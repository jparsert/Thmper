(****************************)
(* Variables/Terms/Formulas *)
(****************************)

type 'a var = 'a

type 'a term =
  | Var of 'a var
  | Fun of 'a * 'a term list;;

type 'a formula =
  | BOT
  | Atom of 'a * 'a term list
  | Neg of 'a formula
  | Disj of 'a formula * 'a formula
  | Conj of 'a formula * 'a formula
  | Imp of 'a formula * 'a formula
  | Exists of 'a var * 'a formula
  | Forall of 'a var * 'a formula



(**********************************)
(*  Functions for Formulas, etc.  *)
(**********************************)

let rec term_equals t1 t2 = match (t1, t2) with
  | (Var v, Var w) when v = w -> true
  | (Fun (f, args1), Fun (g, args2)) when f = g -> List.for_all2 (fun a b -> term_equals a b) args1 args2
  | _ -> false

let rec formula_equals fm1 fm2 = match (fm1, fm2) with
  | (BOT, BOT) -> true
  | (Atom (a, tl1), Atom (b, tl2)) when a = b -> List.for_all2 (fun a b -> term_equals a b) tl1 tl2
  | (Neg f, Neg f2) -> formula_equals f f2
  | (Disj (a,b), Disj (c,d)) -> formula_equals a c && formula_equals b d
  | (Conj (a,b), Conj (c,d)) -> formula_equals a c && formula_equals b d
  | (Imp (a,b), Imp (c,d)) -> formula_equals a c && formula_equals b d
  | (Exists (a, formula), Exists (b, form2)) when a = b -> formula_equals fm1 fm2
  | (Forall (a, formula), Forall (b, form2)) when a = b -> formula_equals fm1 fm2
  | _ -> false

let rec vars_in_term = function
  | Var v -> [v]
  | Fun (_, tms) -> List.concat (List.map vars_in_term tms)

let rec all_vars_in = function
  | BOT -> []
  | Atom (_, tms) -> List.concat @@ List.map vars_in_term tms
  | Neg fm -> all_vars_in fm
  | Disj (a, b) -> all_vars_in a @ all_vars_in b
  | Conj (a, b) -> all_vars_in a @ all_vars_in b
  | Imp (a, b) -> all_vars_in a @ all_vars_in b
  | Exists (v, fm) -> all_vars_in fm
  | Forall (v, fm) -> all_vars_in fm

let rec all_free_vars_in = function
  | BOT -> []
  | Atom (_, tms) -> List.concat @@ List.map vars_in_term tms
  | Neg fm -> all_vars_in fm
  | Disj (a, b) -> all_vars_in a @ all_vars_in b
  | Conj (a, b) -> all_vars_in a @ all_vars_in b
  | Imp (a, b) -> all_vars_in a @ all_vars_in b
  | Exists (v, fm) -> List.filter (fun x -> not (x = v)) @@ all_vars_in fm
  | Forall (v, fm) -> List.filter (fun x -> not (x = v)) @@ all_vars_in fm

let rec substitute_in_term (v, t) = function
  | Var w when v = w -> t
  | Fun (f, tms) -> Fun (f, List.map (substitute_in_term (v, t)) tms)
  | x -> x

let rec substitute_in_formula (v, t) = function
  | BOT -> BOT
  | Atom (a, tms) -> Atom (a, List.map (substitute_in_term (v, t)) tms)
  | Neg fm -> substitute_in_formula (v, t) fm
  | Disj (a, b) ->  Disj (substitute_in_formula (v, t) a, substitute_in_formula (v, t) b)
  | Conj (a, b) -> Conj (substitute_in_formula (v, t) a, substitute_in_formula (v, t) b)
  | Imp (a, b) -> Imp (substitute_in_formula (v, t) a, substitute_in_formula (v, t) b)
  | Exists (w, fm) as e -> if w = v then e else Exists (w , substitute_in_formula (v, t) fm)
  | Forall (w, fm) as e -> if w = v then e else Forall (w , substitute_in_formula (v, t) fm)

let remove_formula fm lst = List.filter (fun x -> not (formula_equals x fm)) lst



(*********************************)
(* Theorem or Sequent definition *)
(*********************************)

type 'a theorem = 'a formula list * 'a formula  (* ([a,b,c], d) = a; b; c |- d *)



(****************************************)
(* Inference rules of First-order Logic *)
(****************************************)

(***  Intuitionistic rules  ***)
let trivial (fm:'a formula) : 'a theorem = ([fm], fm)

let assume (fm:'a formula) ((fms, c):'a theorem):'a theorem = (fm::fms, c)

let neg_intro ((fms, Imp (a, BOT)):'a theorem) :'a theorem = (fms, Neg a)

let neg_elim ((fms, Neg a):'a theorem) :'a theorem = (fms, Imp (a, BOT))

let bottom_elim ((fms, BOT):'a theorem) fm = ((fms, fm):'a theorem)

let true_introduction :'a theorem = ([], Neg BOT)

let conj_intro ((fms1, c):'a theorem) ((fms2, d):'a theorem) = (fms1 @ fms2, Conj (c,d))

let conj_elim1 (fms, Conj (_, d)) = ((fms, d):'a theorem)

let conj_elim2 (fms, Conj (c, _)) = ((fms, c):'a theorem)

let disj_intro1 (fm:'a formula) ((fms, c):'a theorem) = (fms, Disj (c, fm))

let disj_intro2 (fm:'a formula) ((fms, c):'a theorem) = (fms, Disj (fm, c))

let modus_ponens ((fms1, Imp (c, d)):'a theorem) ((fms2, c):'a theorem) = ((fms1@fms2, d):'a theorem)

let disj_elim_cases ((fms, Disj (a, b)):'a theorem) ((fms1, q):'a theorem) ((fms2, p):'a theorem) =
  if formula_equals p q (* Does a need to be in fms1 and b in fms2? *) then
    (fms @ (remove_formula q fms1) @ (remove_formula p fms2), p)
  else
    failwith "Disjunction elimination failure"

(* also known as GEN *)
let all_intro ((fms, c):'a theorem) (v:'a var) =
  let all_frees_in_fms = List.concat (List.map all_free_vars_in fms) in
  if (List.exists (fun x -> x = v) all_frees_in_fms) then
    failwith "All_intro failure: Variable occurs free in formula"
  else
    (fms, Forall (v,c))

let all_elim ((fms, Forall (v, fm)):'a theorem) u = (fms, substitute_in_formula (v, u) fm)

(* existential E/I missing for now *)


(*** Non-constructive rule  ***)
let lem (fm:'a formula) = ([], Disj (fm, Neg fm))



(**********************)
(* Deduction Theorems *)
(**********************)

let deduction_thm1 ((x::fms, c):'a theorem) :'a theorem = (fms, Imp (x, c))

let deduction_thm2 ((fms, Imp (x, c)):'a theorem) :'a theorem = (x::fms, c)
