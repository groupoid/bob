(*
   Synonymical Names:

   * Interaction Networks Calculus
   * Linear Symmetric Interaction Combinators
   * Internal Parallel Language of Symmetric Monoidal Categories

   Semantics: https://lipn.univ-paris13.fr/~mazza/papers/CombSem-MSCS.pdf
   Reference Implementation: https://github.com/HigherOrderCO/ICVM/

   $ opam install domainslib
   $ ocamlfind ocamlopt -thread -package domainslib -linkpkg -o bob bob.ml
*)

type term =
  | Var of string
  | Con of term
  | Dup of term
  | Era of term
  | Pair of term * term
  | Swap of term
  | Let of string * term * term
  | Unit

type env = (string * term) list
let rec is_bound var env = List.exists (fun (v, _) -> v = var) env

let rec subst env var term = function
  | Var v ->
      if v = var then
        if is_bound var env then failwith "Affine violation: variable used twice"
        else term
      else Var v
  | Con t -> Con (subst env var term t)
  | Dup t -> Dup (subst env var term t)
  | Era t -> Era (subst env var term t)
  | Pair (t, u) -> Pair (subst env var term t, subst env var term u)
  | Swap t -> Swap (subst env var term t)
  | Let (x, t1, t2) ->
      let t1' = subst env var term t1 in
      if x = var then Let (x, t1', t2)
      else Let (x, t1', subst env var term t2)
  | Unit -> Unit

let reduce env term =
  match term with
  | Con (Con x) -> Pair (x, x)           (* ζ-ζ annihilation: two wires *)
  | Dup (Dup x) -> Pair (x, x)           (* δ-δ annihilation: two wires *)
  | Era (Era x) -> Unit                  (* ε-ε annihilation: empty net *)
  | Con (Dup x) -> Dup (Con x)           (* ζ-δ commutation:  reorder *)
  | Con (Era x) -> Pair (Era x, Era x)   (* ζ-ε commutation:  two ε cells *)
  | Dup (Era x) -> Pair (Era x, Era x)   (* δ-ε commutation:  two ε cells *)
  | Swap (Pair (t, u)) -> Pair (u, t)    (* δ-ζ commutation:  port swap *)
  | Let (x, t, u) -> subst env x t u     (* Substitution *)
  | _ -> term

(* Find all reducible subterms (active pairs) *)
let rec find_redexes env term acc =
  match term with
  (* Annihilation rules *)
  | Con (Con x) -> (term, Pair (x, x)) :: acc
  | Dup (Dup x) -> (term, Pair (x, x)) :: acc
  | Era (Era x) -> (term, Unit) :: acc
  (* Commutation rules *)
  | Con (Dup x) -> (term, Dup (Con x)) :: acc
  | Con (Era x) -> (term, Pair (Era x, Era x)) :: acc
  | Dup (Era x) -> (term, Pair (Era x, Era x)) :: acc
  (* SMC operations *)
  | Swap (Pair (t, u)) -> (term, Pair (u, t)) :: acc
  | Let (x, t, u) -> (term, subst env x t u) :: find_redexes env t (find_redexes env u acc)
  (* Recurse into subterms *)
  | Con t ->
      (match t with
       | Dup _ | Era _ -> acc
       | Con x -> find_redexes env t ((term, reduce env term) :: acc)
       | _ -> find_redexes env t acc)
  | Dup t -> find_redexes env t acc
  | Era t -> find_redexes env t acc
  | Pair (t, u) ->
      let acc' = find_redexes env t acc in
      find_redexes env u acc'
  | Swap t -> find_redexes env t acc
  | Var _ | Unit -> acc

(* Replace a subterm in a term *)
let rec replace_subterm old_term new_term = function
  | t when t = old_term -> new_term
  | Con t -> Con (replace_subterm old_term new_term t)
  | Dup t -> Dup (replace_subterm old_term new_term t)
  | Era t -> Era (replace_subterm old_term new_term t)
  | Pair (t, u) ->
      Pair (replace_subterm old_term new_term t, replace_subterm old_term new_term u)
  | Swap t -> Swap (replace_subterm old_term new_term t)
  | Let (x, t, u) ->
      Let (x, replace_subterm old_term new_term t, replace_subterm old_term new_term u)
  | Var x -> Var x
  | Unit -> Unit

(* Parallel evaluation using Domainslib *)
open Domainslib

let eval_parallel pool env term =
  let rec loop term =
    let redexes = find_redexes env term [] in
    if redexes = [] then term
    else
      let new_term = Task.run pool (fun () ->
        List.fold_left
          (fun acc (old_t, new_t) -> replace_subterm old_t new_t acc)
          term redexes
      ) in
      loop new_term
  in
  loop term

(* Pretty-print terms *)
let rec pp_term = function
  | Var x -> x
  | Con t -> "con(" ^ pp_term t ^ ")"
  | Dup t -> "dup(" ^ pp_term t ^ ")"
  | Era t -> "era(" ^ pp_term t ^ ")"
  | Pair (t, u) -> "(" ^ pp_term t ^ ", " ^ pp_term u ^ ")"
  | Swap t -> "swap(" ^ pp_term t ^ ")"
  | Let (x, t, u) -> "let " ^ x ^ " = " ^ pp_term t ^ " in " ^ pp_term u
  | Unit -> "()"

(* Test the parallel evaluator *)
let () =
  let pool = Task.setup_pool ~num_domains:(Domain.recommended_domain_count ()) () in
  let env = [] in
  (* Test 1: ζ-ζ annihilation and δ-ζ simplification *)
  let test1 = Pair (Con (Con (Var "x")), Swap (Pair (Var "t", Var "u"))) in
  Printf.printf "Test 1: %s -> %s\n" (pp_term test1) (pp_term (eval_parallel pool env test1));
  (* Test 2: ζ-δ commutation *)
  let test2 = Con (Dup (Con (Var "x"))) in
  Printf.printf "Test 2: %s -> %s\n" (pp_term test2) (pp_term (eval_parallel pool env test2));
  (* Test 3: Substitution *)
  let test3 = Let ("x", Con (Var "y"), Pair (Var "x", Var "u")) in
  Printf.printf "Test 3: %s -> %s\n" (pp_term test3) (pp_term (eval_parallel pool env test3));
  (* Test 4: ε-ε annihilation *)
  let test4 = Era (Era (Var "x")) in
  Printf.printf "Test 4: %s -> %s\n" (pp_term test4) (pp_term (eval_parallel pool env test4));
  (* Test 5: δ-ε commutation *)
  let test5 = Dup (Era (Var "x")) in
  Printf.printf "Test 5: %s -> %s\n" (pp_term test5) (pp_term (eval_parallel pool env test5));
  (* Test 6: ζ-ε commutation *)
  let test6 = Con (Era (Var "x")) in
  Printf.printf "Test 6: %s -> %s\n" (pp_term test6) (pp_term (eval_parallel pool env test6));
  (* Test 7: δ-δ annihilation *)
  let test7 = Dup (Dup (Var "x")) in
  Printf.printf "Test 7: %s -> %s\n" (pp_term test7) (pp_term (eval_parallel pool env test7));
  (* Test 8: Cyclic net, no reduction expected *)
  let test8 = Pair (Var "x", Pair (Var "y", Var "x")) in
  Printf.printf "Test 8: %s -> %s\n" (pp_term test8) (pp_term (eval_parallel pool env test8));
  Task.teardown_pool pool
