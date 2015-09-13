Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq ssrint tuple ssralg ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module Why3Type.

Section ClassDef.

Record mixin_of T := Mixin { x : T }.

Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >-> Equality.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Notation why3Type := type.
Notation why3Mixin := mixin_of.
Notation Why3Type T m := (@pack T m _ _ id).
Notation "[ 'why3Type' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'why3Type'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'why3Type' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'why3Type'  'of'  T ]") : form_scope.

End Exports.

End Why3Type.
Export Why3Type.Exports.


Definition witness (T : why3Type) : T :=
  match T return T with
      Why3Type.Pack sort cls _ => Why3Type.x (Why3Type.mixin cls)
  end.


Definition nat_why3Mixin := Why3Type.Mixin (T:=nat) 0.
Canonical nat_why3Type := Eval hnf in Why3Type nat nat_why3Mixin.
Lemma witness_nat_why3Type : witness nat_why3Type = 0.
Proof. by []. Qed.


Definition int_why3Mixin := Why3Type.Mixin (T:=int) 0.
Canonical int_why3Type := Eval hnf in Why3Type int int_why3Mixin.
Lemma witness_int_why3Type : witness int_why3Type = 0.
Proof. by []. Qed.

(*Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.*)

Definition array (T : Type) := seq T.
Definition length (T : Type) (a : array T) := (size a : int).

Section Array.

Variable (T:why3Type).

Definition get (a : array T) (i : int) :=
  match i with
    | Posz p => nth (witness T) a p
    | Negz _ => (witness T)
  end.

Definition array_why3Mixin := Why3Type.Mixin (T:= array T) [::].
Canonical array_why3Type := Eval hnf in Why3Type (array T) array_why3Mixin.
(* TODO: set, const *)

End Array.

Import GRing.Theory Num.Theory.

Structure matrix (T : Type) : predArgType :=
  Matrix {matrixval :> seq (seq T);
          nrows : int;
          ncols : int;
          _ : (0 <= nrows)%R;
          _ : (0 <= ncols)%R;
          _ : size matrixval == `|nrows|;
          _ : all [pred r | size r == `|ncols|] matrixval
         }.

Section Matrix.

Variable (T:why3Type).

Definition matrix_get (m : matrix T) (r: int) (c : int) :=
  match (r, c) with
    | (Posz rr, Posz cc) => nth (witness T) (nth [::] m rr) cc
    | _ => (witness T)
  end.

Definition eq_matrix (m1 m2 : matrix T) :=
  [&& (m1 == m2 :> seq (seq T)),
      (nrows m1 == nrows m2) &
      (ncols m1 == ncols m2)].

Lemma eq_matrixP : Equality.axiom eq_matrix.
Proof.
  rewrite /eq_matrix => m1 m2.
  apply (iffP idP).
  - case: m1; rewrite /is_true => [m1 r1 c1 pr1 pc1 Hzs1 Hall1].
    case: m2; rewrite /is_true => [m2 r2 c2 pr2 pc2 Hzs2 Hall2].
    move=> /= /and3P [] /eqP Hm /eqP Hr /eqP Hc.
    subst m1 r1 c1; congr Matrix; by apply eq_irrelevance.
  - move ->; case: m2 => [m2 r2 c2 pr2 pc2 Hzs2 Hall2] /=.
    by rewrite !eq_refl.
Qed.

Definition matrix_eqMixin := EqMixin eq_matrixP.
Canonical matrix_eqType := Eval hnf in EqType (matrix T) matrix_eqMixin.

Lemma empty_matrix : matrix T.
  by apply (@Matrix T [::] 0 0).
Defined.

Definition matrix_why3Mixin := Why3Type.Mixin (T:= matrix T) empty_matrix.
Canonical matrix_why3Type := Eval hnf in Why3Type (matrix T) matrix_why3Mixin.

End Matrix.


