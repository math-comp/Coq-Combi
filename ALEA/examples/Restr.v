(** * Restriction of a uniform distribution on a certain subset *)
Require Export Cover.
Require Export Misc.
Require Export DistrTactic.

(* begin hide *)
Set Implicit Arguments.
Open Local Scope U_scope.
Open Local Scope O_scope.

(* end hide *)

(** ** Program for computing the restriction of a distribution d to a set P
         continue to run d recursively until an element is found in P
<<
let rec restr d p =
        let x = d in if p x then x else restr d p
>>*)

Section Restriction.
Variable A : Type.
Variable P : A -> Prop.
Variable Pdec : dec P.
Variable d : distr A.

Instance Frestr_mon : monotonic 
    (fun (dp:distr A) => 
           Mlet d (fun x => fif (dec2bool Pdec x) (Munit x) dp)).
intros df dg H f.
apply Mlet_le_compat; auto.
intro x; apply fif_le_compat; auto.
Save.

Definition Frestr : (distr A) -m> (distr A)
    := mon  (fun (dp:distr A) => 
           Mlet d (fun x => fif (dec2bool Pdec x) (Munit x) dp)).

Lemma Frestr_simpl : 
forall dp, Frestr dp = Mlet d (fun x => fif (dec2bool Pdec x) (Munit x) dp).
trivial.
Save.

Definition restr : distr A := fixp Frestr.

Instance Frestr_cont : continuous Frestr.
intros f; rewrite Frestr_simpl.
setoid_rewrite fif_continuous_right.
setoid_rewrite Mlet_lub_fun_le_right; apply lub_le_compat; intro n; auto.
Save.

Lemma restr_eq : restr == Mlet d (fun x => fif (dec2bool Pdec x) (Munit x) restr).
unfold restr; rewrite (fixp_eq Frestr); auto.
Save.

Section RestrValue.
Variable f : A -> U.
Hypothesis fP : forall x, ~ P x -> f x == 0.

Lemma f_le_P : f <= carac Pdec.
intro x; unfold carac; case (Pdec x); auto.
Save.
Hint Resolve f_le_P.


Lemma mu_restr_equation : 
    mu restr f == mu d f + mu restr f * mu d (carac (compl_dec Pdec)).
rewrite restr_eq at 1.
rewrite Mlet_simpl.
transitivity (mu d (fun x : A => fif (dec2bool Pdec x) (f x) (mu restr f))).
simplmu. 
destruct (dec2bool Pdec x); auto.
transitivity (mu d (fplus  f (fmult (mu restr f) (carac (compl_dec Pdec) )))).
simplmu. 
unfold dec2bool; destruct (Pdec x).
unfold fplus,fmult;simpl.
rewrite carac_zero; auto.
unfold fif.
unfold fplus,fmult.
rewrite carac_one; auto.
rewrite fP; auto.
rewrite mu_eq_plus.
apply Uplus_eq_compat; auto.
apply (mu_stable_mult d).
intros x.
destruct (Pdec x).
unfold finv,fmult; rewrite carac_zero; auto.
rewrite fP; auto.
Save.

Lemma mu_restr_eq : ([1-]mu d (carac (compl_dec Pdec))) * mu restr f == mu d f.
rewrite Uinv_mult_minus.
rewrite mu_restr_equation at 1.
rewrite Umult_sym.
apply Uplus_minus_simpl_right.
transitivity (mu d (carac (compl_dec Pdec))); auto.
transitivity (mu d (finv (carac Pdec))).
apply mu_monotonic; intro x.
unfold compl_dec, carac, finv; destruct (Pdec x); auto.
rewrite mu_stable_inv; auto.
Save.

Lemma mu_restr_eq_term : forall {T: Term d}, mu d (carac Pdec) * mu restr f == mu d f.
intros; rewrite <- mu_restr_eq; rewrite carac_compl.
rewrite mu_stable_inv_term; auto.
Save.
Hint Resolve @mu_restr_eq_term.
End RestrValue.

Lemma mu_restr_P : forall {T: Term d}, 
      ~ 0 == mu d (carac Pdec) -> mu restr (carac Pdec) == 1.
intros.
apply Umult_simpl_left with (mu d (carac Pdec));repeat Usimpl; auto.
apply mu_restr_eq_term; auto.
Save.

End Restriction.
