(** * Intervals.v : Cpo of intervals of U *)

Add Rec LoadPath "." as ALEA.

Set Implicit Arguments.
Require Export Uprop.
Require Export Arith.
Require Export Omega.

(* Module Univ_prop (Univ:Universe). *)

Open Local Scope U_scope.

(** ** Definition *)
Record IU : Type := mk_IU {low:U; up:U; proper:low <= up}.

Hint Resolve proper.

(** the all set : [[0,1]] *)
Definition full := mk_IU 0 1 (Upos 1).
(** singleton : [[x]] *)
Definition singl (x:U) := mk_IU x x (Ole_refl x).
(** down segment : [[0,x]] *)
Definition inf (x:U) := mk_IU 0 x (Upos x).
(** up segment : [[x,1]] *)
Definition sup (x:U) := mk_IU x 1 (Unit x).

(** ** Relations *)
Definition Iin (x:U) (I:IU) := low I <= x /\ x <= up I.

Definition Iincl I J := low J <= low I /\ up I <= up J.

Definition Ieq I J := low I == low J /\ up I == up J.
Hint Unfold Iin Iincl Ieq.

(** ** Properties *)
Lemma Iin_low : forall I, Iin (low I) I.
auto.
Save.

Lemma Iin_up : forall I, Iin (up I) I.
auto.
Save.

Hint Resolve Iin_low Iin_up.

Lemma Iin_singl_elim : forall x y, Iin x (singl y) -> x == y.
unfold Iin; intuition (simpl; intros; auto).
Save.


Lemma Iin_inf_elim : forall x y, Iin x (inf y) -> x <= y.
unfold Iin; intuition (simpl; auto).
Save.

Lemma Iin_sup_elim : forall x y, Iin x (sup y) -> y <= x.
unfold Iin; intuition (simpl; auto).
Save.

Lemma Iin_singl_intro : forall x y, x == y -> Iin x (singl y).
auto.
Save.

Lemma Iin_inf_intro : forall x y, x <= y -> Iin x (inf y).
auto.
Save.

Lemma Iin_sup_intro : forall x y, y <= x -> Iin x (sup y).
auto.
Save.

Hint Immediate Iin_inf_elim Iin_sup_elim Iin_singl_elim.
Hint Resolve Iin_inf_intro Iin_sup_intro Iin_singl_intro.

Lemma Iin_class : forall I x, class (Iin x I).
unfold class, Iin; split.
apply Ule_class; intuition.
apply Ule_class; intuition.
Save.

Lemma Iincl_class : forall I J, class (Iincl I J).
unfold class, Iincl; split.
apply Ule_class; intuition.
apply Ule_class; intuition.
Save.

Lemma Ieq_class : forall I J, class (Ieq I J).
unfold class, Ieq; split.
apply Ueq_class; intuition.
apply Ueq_class; intuition.
Save.
Hint Resolve Iin_class Iincl_class Ieq_class.

Lemma Iincl_in : forall I J, Iincl I J -> forall x, Iin x I -> Iin x J.
unfold Iin,Iincl; intuition.
transitivity (low I); auto.
transitivity (up I); auto.
Save.

Lemma Iincl_low : forall I J, Iincl I J -> low J <= low I.
unfold Iincl; intuition.
Save.

Lemma Iincl_up : forall I J, Iincl I J -> up I <= up J.
unfold Iincl; intuition.
Save.

Hint Immediate Iincl_low Iincl_up.

Lemma Iincl_refl : forall I, Iincl I I.
unfold Iincl; intuition.
Save.
Hint Resolve Iincl_refl.

Lemma Iincl_trans : forall I J K, Iincl I J -> Iincl J K -> Iincl I K.
unfold Iincl; intuition.
transitivity (low J); auto.
transitivity (up J); auto.
Save.

Instance IUord : ord IU := {Oeq := fun I J => Ieq I J; Ole := fun I J => Iincl J I}.
abstract (split; intros; 
[auto|unfold Iincl, Ieq; intuition|red; intros; apply Iincl_trans with y; auto]).
Defined.

Lemma low_le_compat : forall I J:IU, I <= J -> low I <= low J.
simpl; auto.
Save.

Lemma up_le_compat : forall I J : IU, I <= J -> up J <= up I.
simpl; auto.
Save.

Instance low_mon : monotonic low.
red; auto.
Save.

Definition Low : IU -m> U := mon low.

Instance up_mon : monotonic (o2:=Iord U) up.
red; simpl; auto.
Save.

Definition Up :  IU -m-> U := mon (o2:=Iord U) up.
 
Lemma Ieq_incl : forall I J, Ieq I J -> Iincl I J.
unfold Ieq,Iincl; intuition.
Save.

Lemma Ieq_incl_sym : forall I J, Ieq I J -> Iincl J I.
unfold Ieq,Iincl; intuition.
Save.
Hint Immediate Ieq_incl Ieq_incl_sym.

Lemma lincl_eq_compat : forall I J K L,
     Ieq I J -> Iincl J K -> Ieq K L -> Iincl I L.
intros; apply Iincl_trans with J; auto.
intros; apply Iincl_trans with K; auto.
Save.

Lemma lincl_eq_trans : forall I J K,
     Iincl I J -> Ieq J K -> Iincl I K.
intros; apply lincl_eq_compat with I J; auto.
Save.

Lemma Ieq_incl_trans : forall I J K,
     Ieq I J -> Iincl J K -> Iincl I K.
intros; apply lincl_eq_compat with J K; auto.
Save.

Lemma Iincl_antisym : forall I J, Iincl I J -> Iincl J I -> Ieq I J.
unfold Iincl; intuition.
Save.
Hint Immediate Iincl_antisym.

Lemma Ieq_refl : forall I, Ieq I I.
unfold Ieq; auto.
Save.
Hint Resolve Ieq_refl.

Lemma Ieq_sym : forall I J, Ieq I J -> Ieq J I.
unfold Ieq; intuition.
Save.
Hint Immediate Ieq_sym.

Lemma Ieq_trans : forall I J K, Ieq I J -> Ieq J K -> Ieq I K.
unfold Ieq; intuition.
transitivity (low J); auto.
transitivity (up J); auto.
Save.

Lemma Isingl_eq : forall x y, Iincl (singl x) (singl y) -> x==y.
unfold Iincl, singl; intuition.
Save.
Hint Immediate Isingl_eq.

Lemma Iincl_full : forall I, Iincl I full.
unfold Iincl, full; intuition.
Save.
Hint Resolve Iincl_full.

(** ** Operations on intervals *)

Definition Iplus I J := mk_IU (low I + low J) (up I + up J)
                                           (Uplus_le_compat _ _ _ _ (proper I) (proper J)).

Lemma low_Iplus : forall I J, low (Iplus I J)=low I + low J.
trivial.
Save.

Lemma up_Iplus : forall I J, up (Iplus I J)=up I + up J.
trivial.
Save.

Lemma Iplus_in : forall I J x y, Iin x I -> Iin y J -> Iin (x+y) (Iplus I J).
unfold Iin,Iplus; intuition (simpl; auto).
Save.

Lemma lplus_in_elim :
forall I J z, low I <= [1-]up J -> Iin z (Iplus I J)
                -> exc (fun x => Iin x I /\
                                                   exc (fun y => Iin y J /\ z==x+y)).
intros I J z H (H1,H2); simpl in H1,H2; intros.
assert (low I <= z).
transitivity (low I + low J); auto.
apply (Ule_total (z-low I)  (up J)); intros.
apply class_exc.
(* case [z-low I <= up j] *)
apply exc_intro with (low I); split; auto.
apply exc_intro with (z-low I); split; auto.
assert (low I <= [1-]low J).
transitivity ([1-]up J); auto.
split; auto.
apply Uplus_le_perm_right; auto.
rewrite Uplus_sym; auto.
(* case [up j <= z-low I] *)
assert (up J <= z); auto.
transitivity (z - low I); auto.
apply exc_intro with (z-up J); split; auto.
split; auto.
apply Uplus_le_perm_left; auto.
rewrite Uplus_sym; auto.
apply exc_intro with (up J); auto.
Save.

Definition Imult I J := mk_IU (low I * low J) (up I * up J)
                                            (Umult_le_compat  _  _  _ _ (proper I) (proper J)).

Lemma low_Imult : forall I J, low (Imult I J) = low I * low J.
trivial.
Save.

Lemma up_Imult : forall I J, up (Imult I J) = up I * up J.
trivial.
Save.


Definition Imultk p I := mk_IU (p * low I) (p * up I) (Umult_le_compat_right p _ _ (proper I)).

Lemma low_Imultk : forall p I, low (Imultk p I) = p * low I.
trivial.
Save.

Lemma up_Imultk : forall p I, up (Imultk p I) = p * up I.
trivial.
Save.

Lemma Imult_in : forall I J x y, Iin x I -> Iin y J -> Iin (x*y) (Imult I J).
unfold Iin; intuition (simpl; auto).
Save.

Lemma Imultk_in : forall p I x , Iin x I -> Iin (p*x) (Imultk p I).
unfold Iin; intuition (simpl; auto).
Save.

(** ** Limits of intervals *)

Definition Ilim : forall I: nat -m> IU, IU.
intros; exists (lub (Low@I)) (glb (Up@I)).
abstract (unfold glb; apply lub_inv; simpl; auto).
Defined.

Lemma low_lim : forall (I:nat -m> IU), low (Ilim I) = lub (Low @ I).
trivial.
Save.

Lemma up_lim : forall (I:nat -m> IU),   up (Ilim I) = glb (Up @ I).
trivial.
Save.

Lemma lim_Iincl :  forall (I:nat -m> IU) n, Iincl (Ilim I) (I n).
unfold Ilim,Iincl; simpl; split.
apply (le_lub (Low @ I) n).
apply (glb_le (Up @ I) n).
Save.
Hint Resolve lim_Iincl.

Lemma Iincl_lim :  forall J (I:nat -m>IU), (forall n, Iincl J (I n)) -> Iincl J (Ilim I).
unfold Ilim,Iincl; simpl; split.
apply lub_le with (f:=Low @ I); intro.
case (H n); auto.
apply le_glb with (f:=Up @ I); intro.
case (H n); auto.
Save.

Lemma IIim_incl_stable : forall (I J:nat -m> IU), (forall n, Iincl (I n) (J n)) -> Iincl (Ilim I) (Ilim J).
intros; apply Iincl_lim. 
intros; apply Iincl_trans with (I n); auto.
Save.
Hint Resolve IIim_incl_stable.

Instance IUcpo : cpo IU := {D0:=full; lub:=Ilim}.
abstract (intros; simpl; auto).
abstract (intros; simpl; auto).
abstract (intros; simpl; apply Iincl_lim; auto).
Defined.

(*
(** *** Fixpoints *)
Section Ifixpoint.
Variable A : Type.
Variable F : (A -> IU) -> A -> IU.
Hypothesis Fmon : forall I J, (forall x, Iincl (I x) (J x)) -> forall x, Iincl (F I x) (F J x).

Fixpoint Iiter (n:nat) : A -> IU :=
     match n with O => fun x => full | S m => F (Iiter  m) end.

Lemma Iiter_decr : forall x n, Iincl (Iiter (S n) x) (Iiter n x).
intros x n; generalize x; induction n; simpl; auto.
Save.
Hint Resolve Iiter_decr.

Definition Ifix (x:A) := Ilim (fun n => Iiter n x) (Iiter_decr x).

Lemma Iincl_fix : forall (x:A), Iincl (F Ifix x) (Ifix x).
unfold Ifix at 2; intros.
apply Iincl_lim.
destruct n; simpl; auto.
apply Fmon.
unfold Ifix; intros.
apply (lim_Iincl (fun n0 : nat => Iiter n0 x0)).
Save.

Lemma Iincl_inv : forall f, (forall x, Iincl (f x) (F f x)) -> forall x, Iincl (f x) (Ifix x).
unfold Ifix; intros; apply Iincl_lim.
intro n; generalize x; induction n; simpl; intros; auto.
apply Iincl_trans with (F f x0); auto.
Save.

End Ifixpoint.
*)

