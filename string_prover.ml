open Kernel



(****************************)
(*    Printing functions    *)
(****************************)

let rec string_of_term alpha_str = function
  | Var v -> alpha_str v
  | Fun (f, args) -> if List.length args = 0 then alpha_str f else
                       alpha_str f ^ "(" ^ (String.concat "," (List.map (string_of_term alpha_str) args)) ^ ")"

let rec string_of_formula alpha_str = function
  | BOT -> "F"
  | Atom (a, args) -> if List.length args = 0 then alpha_str a else
                       alpha_str a ^ "(" ^ (String.concat "," (List.map (string_of_term alpha_str) args)) ^ ")"
  | Neg fm -> "~"^ string_of_formula alpha_str fm
  | Disj (a, b) -> string_of_formula alpha_str a ^ " \\/ " ^ string_of_formula alpha_str b
  | Conj (a, b) -> string_of_formula alpha_str a ^ " /\\ " ^ string_of_formula alpha_str b
  | Imp (a, b) -> string_of_formula alpha_str a ^ " --> " ^ string_of_formula alpha_str b
  | Exists (w, fm) -> "?" ^ alpha_str w ^ ". " ^ string_of_formula alpha_str fm
  | Forall (w, fm) -> "!" ^ alpha_str w ^ ". " ^ string_of_formula alpha_str fm

let string_of_theorem alpha_str ((fms, c):'a theorem) =
  let assms = if List.length fms = 0 then "" else (String.concat "," (List.map (string_of_formula alpha_str) fms)) in
  let concl = string_of_formula alpha_str c in
  "{ " ^ assms ^ " } |- " ^ concl

let print_theorem alpha_str thm = print_string (string_of_theorem alpha_str thm)



(****************************)
(*         Theorems         *)
(****************************)

(* !x. P(x) --> P(x) *)
let thm_IMP_REFL =
  let l1 = trivial (Atom ("p", [Var "x"])) in
  let l2 = deduction_thm1 l1 in
  all_intro l2 "x"



(****************************)
(*          Tactics         *)
(****************************)


(** Given a Theorem that has a toplevel double negation we return the theorem without double negation **)

let tactic_NNEG_ELIM (a1, (Neg (Neg fm)))=
  let (a2, Disj (a, b)) = lem fm in
  let b1 = conj_elim2 @@ conj_intro (trivial fm) (assume a (true_introduction)) in
  let l1 = assume b (true_introduction) in
  let l2 = neg_elim (a1, (Neg (Neg fm))) in
  let l3 = deduction_thm1 l1 in
  let l4 = modus_ponens l2 l3 in
  let b2 = bottom_elim l4 fm in
  print_theorem (fun x -> x) b1; print_newline();
  print_theorem (fun x -> x) b2; print_newline();
  disj_elim_cases (a2, Disj (a, b)) b1 b2
