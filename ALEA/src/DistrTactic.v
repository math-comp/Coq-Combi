(** * DistrTactic.v: tactics for reasoning on distributions. *)
(** Contributed by Pierre Courtieu CNAM *)

(* begin hide *)
Require Export List.
Require Export Bool.
Require Export Streams.
Require Export Decidable.
Require Export Arith.
Require Export Prog.
Require Export Bernoulli.
Require Import Omega.
Require Import Compare.
Require Export Misc.
Open Local Scope U_scope.
Open Local Scope O_scope.
(* end hide *)


(** The tactics to use are
- [simplmu] for one step simplification, 
- [rsimplmu]  for repeated simplifications. 
- These two tactics can be cloned and extended using [simplmu_arg]. 
*)

Hint Extern 2 => Usimpl.


Ltac simpl_mu_rewrite tacsubgoals := first [
progress setoid_rewrite Umult_sym_cst|rewrite Umult_sym_cst|
progress setoid_rewrite Mif_eq2|rewrite Mif_eq2|
progress setoid_rewrite Bern_true|rewrite Bern_true|
progress setoid_rewrite Bern_false|rewrite Bern_false|
progress setoid_rewrite Mlet_simpl|rewrite Mlet_simpl|
progress setoid_rewrite Munit_simpl|rewrite Munit_simpl|
(* should be applied soon: *)
progress setoid_rewrite bary_refl_feq;[|progress auto]|rewrite bary_refl_feq;[|progress auto]|
(* should be applied soon *)
progress setoid_rewrite Uinv_inv|rewrite Uinv_inv|
progress setoid_rewrite bernoulli_eq|rewrite bernoulli_eq|
progress setoid_rewrite binomial_lt_S|rewrite binomial_lt_S|
progress setoid_rewrite carac_lt_S|rewrite carac_lt_S|
(* progress setoid_rewrite carac_lt_0| *)
(* progress setoid_rewrite carac_lt_zero| *)
progress setoid_rewrite mu_stable_mult2|rewrite mu_stable_mult2|
progress setoid_rewrite mon_simpl|rewrite mon_simpl|
(* progress setoid_rewrite prod_distr| *)
progress setoid_rewrite im_distr_simpl|rewrite im_distr_simpl|
progress setoid_rewrite Mchoice_simpl|rewrite Mchoice_simpl|
progress setoid_rewrite Random_total|rewrite Random_total|
progress setoid_rewrite discrete_simpl|rewrite discrete_simpl|
progress setoid_rewrite Discrete_simpl|rewrite Discrete_simpl|
progress setoid_rewrite Flip_simpl|rewrite Flip_simpl|
(* "dependent function"? *)
progress setoid_rewrite (@mu_fzero_eq _ _) | rewrite (@mu_fzero_eq _ _) | 
progress setoid_rewrite mu_fzero_eq |rewrite mu_fzero_eq |
progress setoid_rewrite Mlet_unit|rewrite Mlet_unit|
progress setoid_rewrite Mlet_assoc|rewrite Mlet_assoc|
(* generates a fplusok subgoal (put in last to avoid loops) *)
progress setoid_rewrite mu_stable_plus2;[|solve [tacsubgoals] ] | rewrite mu_stable_plus2;[|solve [tacsubgoals] ]|
(* This lifts "if then else", so it should applied after anything else fails,
   because otherwise it may put rewrite redexes inside branches of an if, which
   makes them unrewritable. *)
progress setoid_rewrite carac_lt_if_compat | rewrite carac_lt_if_compat
].
(* progress setoid_rewrite random_simpl| *)



(** Try simplification of Oeq and Ole at top level. *)
Ltac simplmu_aux :=
  match goal with
    | |- (Ole (fmont (mu ?d1) ?f)  (fmont (mu ?d2) ?g)) => apply (mu_le_compat (m1:=d1) (m2:=d2) (Ole_refl d1) (f:=f) (g:=g)); intro
    | |- (Oeq (fmont (mu ?d1) ?f)  (fmont (mu ?d2) ?g)) => apply (mu_eq_compat (m1:=d1) (m2:=d2) (Oeq_refl d1) (f:=f) (g:=g)); unfold Oeq;intro
    | |- (Oeq (Munit ?x)  (Munit ?y)) => apply (Munit_eq_compat x y)
    | |- (Oeq (Mlet ?x1 ?f)  (Mlet ?x2 ?g)) 
      => apply (Mlet_eq_compat (m1:=x1) (m2:=x2) (M1:=f) (M2:=g) (Oeq_refl x1)); intro
    | |- (Ole (Mlet ?x1 ?f)  (Mlet ?x2 ?g)) 
      => apply (Mlet_le_compat (m1:=x1) (m2:=x2) (M1:=f) (M2:=g) (Ole_refl x1)); intro
  end.

Ltac simplmu_arg tacsidecond := 
  Usimpl || simplmu_aux || simpl_mu_rewrite ltac:tacsidecond.
Ltac simplmu := simplmu_arg idtac.
Ltac rsimplmu := (repeat progress (simplmu;simpl)).



(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** buffer-file-coding-system: utf-8-unix ***
*** fill-column: 80 ***
*** coq-prog-args: ("-emacs-U" "-I" "." "-I" "../branches/classes-v8.2/ALEA/src")  ***
*** End: ***
*)
 
