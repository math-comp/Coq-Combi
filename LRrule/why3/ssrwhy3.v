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


Lemma witness (T : why3Type) : T.
Proof.
  case: T => sort [] base [] x _ /=; by apply: x.
Qed.



Definition nat_why3Mixin := Why3Type.Mixin (T:=nat) 0.
Canonical nat_why3Type := Eval hnf in Why3Type nat nat_why3Mixin.

Definition int_why3Mixin := Why3Type.Mixin (T:=int) 0.
Canonical int_why3Type := Eval hnf in Why3Type int int_why3Mixin.

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

End Array.
