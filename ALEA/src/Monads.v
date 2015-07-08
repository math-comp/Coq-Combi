(** * Monads.v: Monads for randomized constructions *)

Require Export Frac.
(*
Module Monad (Univ:Universe).
Module UP := (Univ_prop Univ).
*)
(* begin hide *)
Set Implicit Arguments.
Open Local Scope U_scope.
Open Local Scope O_scope.
(* end hide *)

(** ** Definition of monadic operators as the cpo of monotonic oerators *)
Definition M (A:Type) := MF A -m> U.

Instance app_mon (A:Type) (x:A) : monotonic (fun (f:MF A) => f x).
red; auto.
Save.

Definition unit (A:Type) (x:A) : M A := mon (fun (f:MF A) => f x).

Definition star : forall (A B:Type), M A -> (A -> M B) -> M B.
intros A B a F; exists (fun f => a (fun x => F x f)).
red; intros.
apply (fmonotonic a); intro z; simpl; auto.
Defined.

Lemma star_simpl : forall (A B:Type) (a:M A) (F:A -> M B)(f:MF B),
        star a F f =  a (fun x => F x f).
trivial.
Save.

(** ** Properties of monadic operators *)
Lemma law1 : forall (A B:Type) (x:A) (F:A -> M B) (f:MF B), star (unit x) F f == F x f.
trivial.
Qed.

Lemma law2 :
 forall (A:Type) (a:M A) (f:MF A), star a (fun x:A => unit x) f == a (fun x:A => f x).
trivial.
Qed.

Lemma law3 :
 forall (A B C:Type) (a:M A) (F:A -> M B) (G:B -> M C)
   (f:MF C), star (star a F) G f == star a (fun x:A => star (F x) G) f.
trivial.
Qed.

(** ** Properties of distributions *)
(** *** Expected properties of measures *)

Definition stable_inv (A:Type) (m:M A) : Prop := forall f :MF A, m (finv f) <= [1-] (m f).

Definition stable_plus (A:Type) (m:M A) : Prop :=
  forall f g:MF A, fplusok f g -> m (fplus f g) == (m f) + (m g).

Definition le_plus (A:Type) (m:M A) : Prop :=
  forall f g:MF A,  fplusok f g -> (m f) + (m g) <= m (fplus f g).

Definition le_esp (A:Type) (m:M A) : Prop :=
  forall f g: MF A,  (m f) & (m g) <= m (fesp f g).

Definition le_plus_cte (A:Type) (m:M A) : Prop :=
  forall (f : MF A) (k:U),  m (fplus f (fcte A k))  <= m f + k.

Definition stable_mult (A:Type) (m:M A) : Prop :=
  forall (k:U) (f:MF A), m (fmult k f) == k * (m f).

(** *** Stability for equality *)

Lemma stable_minus_distr : forall (A:Type) (m:M A),
     stable_plus m -> stable_inv m ->
     forall (f g : MF A), g <= f -> m (fminus f g) == m f - m g.
intros A m splus sinv; intros.
assert (m g <= m f); auto.
assert (fminus f g <= finv g).
intros; intro x; unfold fminus,Uminus,fplus, finv; auto.
rewrite (fstable m f (fplus (fminus f g) g)).
rewrite (splus (fminus f g) g); auto.
symmetry; apply Uplus_minus_simpl_right; auto.
transitivity ([1-] m (finv g)); auto.
unfold fplus,fminus; intro x; auto.
Save.

Hint Resolve stable_minus_distr.

Lemma inv_minus_distr : forall (A:Type) (m:M A),
     stable_plus m -> stable_inv m ->
     forall (f : MF A), m (finv f) == m (fone A) - m f.
intros A m splus sinv; intros.
transitivity (m (fminus (fone A) f)); auto.
apply (fstable m).
intro x; unfold fminus,finv,fone,fplus; intros; auto.
Save.
Hint Resolve inv_minus_distr.

Lemma le_minus_distr : forall (A : Type)(m:M A),
    forall  (f g:A -> U), m (fminus f g) <= m f.
intros A m; intros.
apply (fmonotonic m); intro x; rewrite fminus_simpl; auto.
Save.
Hint Resolve le_minus_distr.

Lemma le_plus_distr : forall (A : Type)(m:M A),
    stable_plus m -> stable_inv m -> forall (f g:MF A), m (fplus f g) <= m f + m g.
intros A m splus sinv; intros.
transitivity (m (fplus (fminus f (fesp f g)) g)).
apply (fmonotonic m); intro x; unfold fminus,fesp,fplus,finv; intros; auto. 
rewrite (splus (fminus f (fesp f g)) g).
auto.
intro x; unfold fminus,fesp,finv; auto.
Save.
Hint Resolve le_plus_distr.

Lemma le_esp_distr : forall (A : Type) (m:M A), 
     stable_plus m -> stable_inv m -> le_esp m.
intros A m splus sinv; unfold le_esp,fesp,Uesp; intros.
transitivity (m (finv (fplus (finv f) (finv g)))); auto.
rewrite inv_minus_distr; auto.
transitivity 
  (m (fone A) -  (m (finv f) + m (finv g))); auto.
transitivity (m f - [1-] m g) ; repeat Usimpl; auto.
rewrite inv_minus_distr; auto.
transitivity (m f - m (finv g)) ; repeat Usimpl; trivial.
rewrite <- Uminus_assoc_left.
rewrite Uminus_assoc_right; repeat Usimpl; auto.
Save.


Lemma unit_stable_eq : forall (A:Type) (x:A), stable (unit x).
auto.
Qed.

Lemma star_stable_eq : forall (A B:Type) (m:M A) (F:A -> M B), stable (star m F).
auto.
Qed.

Lemma unit_monotonic : forall (A:Type) (x:A) (f g : MF A), 
   f <= g -> unit x f <= unit x g.
auto.
Qed.

Lemma star_monotonic : forall (A B:Type) (m:M A) (F:A -> M B) (f g : MF B),
      f <= g -> star m F f <= star m F g.
auto.
Qed.

Lemma star_le_compat : forall (A B:Type) (m1 m2:M A) (F1 F2:A -> M B),
       m1 <= m2 -> F1 <= F2 -> star m1 F1 <= star m2 F2.
intros; intro f; repeat rewrite star_simpl.
transitivity (m1 (fun x : A => (F2 x) f)); auto.
apply (fmonotonic m1); intro x.
apply (H0 x f).
Save.
Hint Resolve star_le_compat.

(** *** Stability for inversion *)
Lemma unit_stable_inv : forall (A:Type) (x:A), stable_inv (unit x).
red in |- *; intros.
unfold unit in |- *.
auto.
Qed.

Lemma star_stable_inv : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_inv m -> (forall a:A, stable_inv (F a)) -> stable_inv (star m F).
unfold stable_inv in |- *; intros.
unfold star in |- *; simpl.
transitivity (m (finv (fun x:A => F x f))); trivial.
apply (fmonotonic m); intro x.
apply (H0 x f).
Save.

(** *** Stability for addition *)
Lemma unit_stable_plus : forall (A:Type) (x:A), stable_plus (unit x).
red in |- *; intros.
unfold unit in |- *; auto.
Qed.

Lemma star_stable_plus : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_plus m ->
   (forall a:A, forall f g, fplusok f g -> (F a f) <= Uinv (F a g))
   -> (forall a:A, stable_plus (F a)) -> stable_plus (star m F).
unfold stable_plus in |- *; intros.
unfold star in |- *; simpl.
transitivity (m (fplus (fun x:A => F x f) (fun x:A => F x g))); trivial.
apply (fstable m).
intro x; apply (H1 x f g H2).
apply H.
intro x; unfold finv; intros; auto.
Qed.

Lemma unit_le_plus : forall (A:Type) (x:A), le_plus (unit x).
red in |- *; intros.
unfold unit in |- *.
auto.
Qed.

Lemma star_le_plus : forall (A B:Type) (m:M A) (F:A -> M B),
   le_plus m ->
   (forall a:A, forall f g, fplusok f g -> (F a f) <= Uinv (F a g))
   -> (forall a:A, le_plus (F a)) -> le_plus  (star m F).
unfold le_plus in |- *; intros.
unfold star in |- *; simpl.
transitivity (m (fplus (fun x:A => F x f) (fun x:A => F x g))); trivial.
apply H.
red;intro x; unfold finv; intros; auto.
apply (fmonotonic m).
intro x.
rewrite fplus_simpl; auto.
Qed.

(** *** Stability for product *)
Lemma unit_stable_mult : forall (A:Type) (x:A), stable_mult (unit x).
red in |- *; intros.
unfold unit in |- *; auto.
Qed.

Lemma star_stable_mult : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_mult m -> (forall a:A, stable_mult (F a)) -> stable_mult (star m F).
unfold stable_mult in |- *; intros.
unfold star in |- *; simpl.
transitivity (m (fmult k (fun x:A => F x f))); trivial.
apply (fstable m).
intro x; rewrite fmult_simpl; auto.
Qed.

(** *** Continuity *)

Lemma unit_continuous : forall (A:Type) (x:A), continuous  (unit x).
red; unfold unit; intros.
transitivity (lub h x); auto.
transitivity (lub (h <o> x)); auto.
apply lub_le_compat; intro n; auto.
Save.

Lemma star_continuous : forall (A B : Type) (m : M A)(F: A -> M B),
    continuous m -> (forall x, continuous (F x)) -> continuous (star m F).
red; intros; simpl.
transitivity (m (fun x => lub (F x @ h))).
apply (fmonotonic m); intro x.
apply (H0 x h); auto.
transitivity (m (lub (ishift F @ h))).
apply (fmonotonic m); intro x.
rewrite (fcpo_lub_simpl (ishift F @ h) x).
apply lub_le_compat; intro n; auto.
apply Ole_trans with (1:=H (ishift F @ h)); auto.
apply lub_le_compat; intro x; simpl; auto.
Save.


(* End Monad. *)
