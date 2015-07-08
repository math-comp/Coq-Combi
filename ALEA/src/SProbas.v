(** * SProbas.v: Definition of the monad for sub-distributions *)
Add Rec LoadPath "." as ALEA.

Require Export Probas.

(* begin hide *)
Set Implicit Arguments.
Open Local Scope U_scope.
Open Local Scope O_scope.
(* end hide *)

(*
Module Proba (Univ:Universe).
Module MP := (Monad Univ).

(* begin hide *)
Import Univ.
Import MP.
Import MP.UP.
(* end hide *)
*)

(** ** Definition of (sub)distribution
Subdistributions are measure functions $\mu$ such that
    - [ mu (1-f) <= 1 - mu f ]
    - [ f <= 1-g -> mu f + mu g <= mu (f+g) ]
    - [ mu f & mu g <= mu (f & g) ]
    - [ mu (f+k) <= mu f + k ]
    - [ mu (k * f) = k * mu (f) ]
    - [ mu (lub f_n) <= lub mu (f_n) ]
*)
Record sdistr (A:Type) : Type := 
  {smu : M A;
   smu_stable_inv : stable_inv smu;  
   smu_le_plus : le_plus smu;
   smu_le_esp : le_esp smu;
   smu_le_plus_cte : le_plus_cte smu;
   smu_stable_mult : stable_mult smu;
   smu_continuous : continuous smu}.

Hint Resolve smu_le_plus smu_stable_inv  smu_le_esp smu_stable_mult 
smu_continuous.

(** ** Properties of sub-measures *)

Lemma smu_monotonic : forall (A : Type)(m: sdistr A), monotonic (smu m).
intros; apply fmonotonic; auto.
Save.
Hint Resolve smu_monotonic.
Implicit Arguments smu_monotonic [A].

Lemma smu_stable : forall (A : Type)(m: sdistr A), stable (smu m).
intros; apply monotonic_stable; auto.
Save.
Hint Resolve smu_stable.
Implicit Arguments smu_stable [A].

Lemma smu_zero : forall (A : Type)(m: sdistr A), smu m (fzero A) == 0.
intros.
transitivity (smu m (fmult 0 (fzero A))); auto.
transitivity (0 * (smu m (fzero A))); auto.
apply smu_stable_mult; auto.
Save.
Hint Resolve smu_zero.

Lemma smu_stable_mult_right : forall (A : Type)(m:(sdistr A)) (c:U) (f : A -> U),
   smu m (fun x => (f x) * c) == (smu m f) * c.
intros; transitivity (smu m (fun x => c * (f x))).
apply smu_stable; auto.
transitivity (c * smu m f); auto.
exact (smu_stable_mult m c f).
Save.

(*
Lemma smu_one_inv : forall (A : Type)(m:sdistr A),
   smu m (f_one A) == 1 -> forall f, smu m (finv f) == [1-] (smu m f).
intros; apply Ule_antisym.
apply (smu_stable_inv m f).
apply Uplus_le_simpl_left with (smu m f); auto.
setoid_rewrite (Uinv_opp_right (smu m f)).
apply Ule_trans with (smu m (fun x => (f x) + [1-] (f x))).
setoid_rewrite <- H; apply (smu_monotonic m); auto.
apply (smu_le_plus m f (finv f)); auto.
Save.
Hint Resolve smu_one_inv.
*)

Lemma smu_le_minus_left : forall (A : Type)(m:sdistr A) (f g:A -> U),
     smu m (fminus f g) <= smu m f.
intros; auto.
Save.
Hint Resolve smu_le_minus_left.



Lemma smu_le_minus : forall (A:Type) (m:sdistr A)(f g: A -> U),
 g <= f  ->  smu m (fminus f g) <= smu m f - smu m g.
intros.
assert (smu m g <= smu m f). 
apply smu_monotonic; auto.
apply Uplus_le_perm_right; auto.
apply Uinv_le_perm_right.
transitivity (smu m (finv g)); auto.
apply (smu_monotonic m); unfold fminus,finv; auto.
apply (smu_stable_inv m).
transitivity (smu m (fplus (fminus f g) g)).
apply (smu_le_plus m).
unfold fplusok,fminus,finv; auto.
apply (smu_monotonic m); unfold fplus,fminus; intros; auto.
Save.
Hint Resolve smu_le_minus.

Lemma smu_cte : forall (A : Type)(m:(sdistr A)) (c:U),
   smu m (fcte A c) == c * smu m (fone A).
intros.
transitivity (smu m (fun x => c * 1)).
apply (smu_stable m); auto.
unfold fone; setoid_rewrite <- (smu_stable_mult m c (fun x => 1)); auto.
Save.
Hint Resolve smu_cte.

Lemma smu_cte_le :   forall (A : Type)(m:(sdistr A)) (c:U),
   smu m (fcte A c) <= c.
intros; transitivity (c * smu m (fone A)); auto.
Save.


Lemma smu_cte_eq : forall (A : Type)(m:(sdistr A)) (c:U),
   smu m (fone A) == 1 -> smu m (fcte A c) == c.
intros; transitivity (c * smu m (fone A)); auto.
Save.

Hint Resolve smu_cte_le smu_cte_eq.

Lemma smu_le_minus_cte : forall (A:Type) (m:sdistr A)(f: A -> U) (k:U),
     smu m f - k  <= smu m (fminus f (fcte A k)).
intros; apply (Ule_total (smu m f) k); auto; intros.
rewrite Uminus_le_zero; auto.
apply Uplus_le_perm_left; auto.
transitivity (smu m (fplus (fminus f (fcte A k)) (fcte A k))).
apply (smu_monotonic m); unfold fplus, fminus,fcte.
intro x; apply (Ule_total (f x) k); auto.
transitivity (smu m (fminus f (fcte A k)) +k); auto.
apply (smu_le_plus_cte m); auto.
Save.

Lemma smu_inv_le_minus : 
forall (A:Type) (m:sdistr A)(f: A -> U),  smu m (finv f) <= smu m (fone A) - smu m f.
intros; transitivity (smu m (fminus (fone A) f)).
apply (smu_monotonic m); unfold finv,fminus,fone; intros; auto.
apply smu_le_minus; auto.
Save.


Lemma smu_inv_minus_inv : forall (A:Type) (m:sdistr A)(f: A -> U), 
     smu m (finv f) + [1-](smu m (fone A)) <= [1-](smu m f).
intros; apply Uminus_le_perm_right.
apply Uinv_le_compat.
apply (smu_monotonic m); unfold fone; auto.
unfold Uminus; Usimpl.
transitivity (smu m (fone A) - smu m f).
apply smu_inv_le_minus.
unfold Uminus.
apply Uinv_le_compat; auto.
Save.

Definition stable_plus_sdistr : forall A (m:M A),
  stable_plus m -> stable_inv m -> stable_mult m -> continuous m -> sdistr A.
intros; exists m; auto.
intros f g okfg.
rewrite H; auto.
apply le_esp_distr; auto.
intros f k.
rewrite le_plus_distr; repeat Usimpl; auto.
transitivity (m (fmult k (fone A))).
apply (fmonotonic m); unfold fcte,fmult,fone; auto.
rewrite H1.
transitivity (k*1); auto.
Defined.

Definition distr_sdistr : forall A, distr A -> sdistr A.
intros A d; apply (stable_plus_sdistr (m:=mu d)); auto.
Defined.
 
Definition Sunit A (x:A) : sdistr A := distr_sdistr (Munit x).


Lemma Sunit_unit : forall A (x:A), smu (Sunit x) = unit x. 
trivial.
Save.

Lemma Sunit_simpl : forall A (x:A) (f : MF A), smu (Sunit x) f = f x. 
trivial.
Save.

Definition Slet : forall A B:Type, (sdistr A) -> (A -> sdistr B) -> sdistr B.
intros A B mA mB.
exists (star (smu mA) (fun x => (smu (mB x)))).
apply star_stable_inv; auto.
apply star_le_plus; auto.
intros a f g Hfg.
transitivity (smu (mB a) (finv g)); auto.
apply smu_stable_inv.
intros f g.
repeat rewrite star_simpl.
rewrite (smu_le_esp mA).
apply (fmonotonic (smu mA)); auto.
intro x; unfold fesp; apply (smu_le_esp (mB x)).
intros f k.
repeat rewrite star_simpl.
rewrite <- (smu_le_plus_cte mA).
apply (fmonotonic (smu mA)); auto.
intro x; unfold fplus,fcte; apply (smu_le_plus_cte (mB x)).
apply star_stable_mult; trivial.
apply star_continuous; trivial.
Defined.

Lemma Slet_star : forall (A B:Type) (m:sdistr A) (M : A -> sdistr B),
      smu (Slet m M) = star (smu m) (fun x => smu (M x)).
trivial.
Save.


Lemma Slet_simpl : forall A B (m:sdistr A) (M : A -> sdistr B) (f:MF B),
                   smu (Slet m M) f = smu m (fun x => smu (M x) f).
trivial.
Save.

(** Non deterministic choice *)

Definition Smin (A:Type)(m1 m2 : sdistr A) : sdistr A.
intros; exists ((Min @2 smu m1) (smu m2)).
intro f; repeat rewrite app2_simpl, Min_simpl.
rewrite Uinv_min_max.
transitivity (smu m1 (finv f)); auto.
rewrite smu_stable_inv; auto.
intros f g Hfg; repeat rewrite app2_simpl, Min_simpl.
transitivity (min (smu m1 f + smu m1 g) (smu m2 f+smu m2 g)); auto.
apply min_le_compat; apply smu_le_plus; auto.
intros f g; repeat rewrite app2_simpl, Min_simpl.
rewrite Uesp_min.
apply min_le_compat; apply smu_le_esp.
intros f k; repeat rewrite app2_simpl, Min_simpl.
rewrite <- min_plus_cte.
apply min_le_compat; apply smu_le_plus_cte.
intros k f; repeat rewrite app2_simpl, Min_simpl.
rewrite (smu_stable_mult m1 k f); rewrite (smu_stable_mult m2 k f); auto.
apply continuous2_app2; auto; apply smu_continuous.
Save.


(** ** Operations on sub-distributions *)

Instance Osdistr (A : Type) : ord (sdistr A) :=
     { Ole := fun f g => smu f <= smu g;
       Oeq := fun f g => smu f == smu g}.
split; auto; intros.
intuition.
intros f g h; transitivity (smu g); auto.
Defined.

Lemma Sunit_compat : forall A (x y : A), x = y -> Sunit x == Sunit y.
intros; subst; auto.
Save.

Lemma Slet_compat : forall (A B : Type) (m1 m2:sdistr A) (M1 M2 : A-> sdistr B), 
  m1 == m2 -> M1 == M2 -> Slet m1 M1 == Slet m2 M2.
intros; intro f; repeat rewrite Slet_simpl.
transitivity (smu m2 (fun x : A => smu (M1 x) f)); auto.
apply smu_stable; intro x; auto.
apply (H0 x f).
Save.

Lemma le_sdistr_gen : forall (A:Type) (m1 m2:sdistr A),
  m1 <= m2 -> forall f g,  f <= g -> smu m1 f <= smu m2 g.
intros; transitivity (smu m2 f); auto.
Save.

(** ** Properties of monadic operators *)
Lemma Slet_unit : forall (A B:Type) (x:A) (m:A -> sdistr B), Slet (Sunit x) m == m x.
intros; intro f.
repeat (rewrite Slet_star).
rewrite Sunit_unit; rewrite law1; trivial.
Save.

Lemma M_ext : forall (A:Type) (m:sdistr A), Slet m (fun x => Sunit x) == m.
intros; intros f; rewrite Slet_star.
rewrite law2; trivial.
Save.

Lemma Mcomp : forall (A B C:Type) (m1:(sdistr A)) (m2:A -> sdistr B) (m3:B -> sdistr C),
     Slet (Slet m1 m2) m3 == Slet m1 (fun x:A => (Slet (m2 x) m3)).
intros; intros f; repeat rewrite Slet_star.
rewrite law3; trivial.
Save.

Lemma Slet_le_compat : forall (A B:Type) (m1 m2: sdistr A) (f1 f2 : A -> sdistr B),
  m1 <= m2 -> f1 <= f2 -> Slet m1 f1 <= Slet m2 f2.
intros; intros f; repeat rewrite Slet_star.
apply star_le_compat; auto.
Save.

(** ** A specific subdistribution *)
Definition sdistr_null : forall A : Type, sdistr A.
intro A; exists (mon (cte (MF A) (0:U))); try red; auto.
Defined.

Lemma le_sdistr_null : forall (A:Type) (m : sdistr A), sdistr_null A <= m.
red; intros.
unfold sdistr_null; simpl; auto.
Save.
Hint Resolve le_sdistr_null.


(** ** Least upper bound of increasing sequences of sdistributions *)
Section Lubs.
Variable A : Type.

Definition Smu : sdistr A -m> M A.
exists (smu (A:=A)); auto.
Defined.

Lemma Smu_simpl : forall d f, Smu d f = smu d f.
trivial.
Save.

Variable smuf : nat -m> sdistr A.


Definition smu_lub: sdistr A.
exists (lub (Smu @ smuf)).

red; intros; simpl; apply lub_inv; intros; simpl.
apply (smu_stable_inv (smuf n)).

red; intros; repeat rewrite M_lub_simpl.
rewrite Uplus_lub_eq.
apply lub_le_compat; intro n; simpl; auto.
exact (smu_le_plus (smuf n) H).

red; intros; repeat rewrite M_lub_simpl.
rewrite Uesp_lub_eq.
apply lub_le_compat; intro n; simpl; auto.
exact (smu_le_esp (smuf n) f g).

red; intros; repeat rewrite M_lub_simpl.
rewrite <- lub_eq_plus_cte_right.
apply lub_le_compat; intro n; simpl; auto.
exact (smu_le_plus_cte (smuf n) f k).

red; intros; repeat rewrite M_lub_simpl.
rewrite <- lub_eq_mult.
apply lub_eq_compat; intro n; simpl; auto.
exact (smu_stable_mult (smuf n) k f).

unfold M; apply lub_continuous; intros.
apply (smu_continuous (smuf n)).
Defined.

Lemma smu_lub_simpl : smu smu_lub = lub (Smu @ smuf).
trivial.
Save.

Lemma smu_lub_le : forall n:nat, smuf n <= smu_lub.
intros n f.
rewrite smu_lub_simpl.
exact (le_lub (Smu @ smuf) n f).
Save.

Lemma smu_lub_sup : forall m:sdistr A, (forall n:nat, smuf n <= m) -> smu_lub <= m.
intros m H f; exact (lub_le (Smu @ smuf) (smu m) H f).
Save.

End Lubs.

(** ** Sub-distribution for [flip]
The distribution associated to [flip ()] is 
       $f \mapsto \frac{1}{2}f(true)+\frac{1}{2}f(false)$ *)
Definition Sflip : sdistr bool := distr_sdistr Flip.

Lemma Sflip_simpl : smu Sflip = flip.
trivial.
Save.

(** ** Uniform sub-distribution beween 0 and n *)
Require Arith.


(** *** Distribution for [Srandom n]
The sdistribution associated to [Srandom n] is 
       $f \mapsto \Sigma_{i=0}^n \frac{f(i)}{n+1}$
       we cannot factorize $\frac{1}{n+1}$ because of possible overflow *)

Definition Srandom (n:nat): sdistr nat:= distr_sdistr (Random n).

Lemma Srandom_simpl : forall n, smu (Srandom n) = random n.
trivial.
Save.
