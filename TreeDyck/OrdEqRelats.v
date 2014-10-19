Require Export Relations.


Section Tools.
  Variable A : Set.
  Variable eqA : relation A.
  Variable eqA_dec : forall x y : A, {eqA x y} + {~ eqA x y}.
  Variable leA : relation A.
  Variable leA_total_dec : forall x y : A, {leA x y} + {leA y x}.
  Variable leA_refl :      forall x y : A, eqA x y -> leA x y.
  Variable leA_antisym :   forall x y : A, leA x y -> leA y x -> eqA x y.

  Definition leA_dec_from_total : forall x y : A, {leA x y} + {~ leA x y}.
  intros.
  elim leA_total_dec with x y.
   intro; left; trivial.
   elim eqA_dec with x y; intros.
    left; apply leA_refl; trivial.
    right; red; intros; red in b; apply b.
      apply leA_antisym; auto.
  Defined.
End Tools.

Module Type EqRelatA.
  Parameter A : Set.
  Parameter eqA : relation A.

  Parameter eqA_equiv : equivalence A eqA.
  Parameter eqA_dec : forall x y : A, {eqA x y} + {~ eqA x y}.
End EqRelatA.


Module Type OrdEqRelatA.
  Declare Module eqrelat : EqRelatA.
  Export eqrelat.
  Parameter leA : relation A.
  Parameter leA_total_dec : forall x y : A, {leA x y} + {leA y x}.
  Parameter leA_refl :      forall x y : A, eqA x y -> leA x y.
  Parameter leA_antisym :   forall x y : A, leA x y -> leA y x -> eqA x y.
  Parameter leA_trans   :   transitive A leA.

  Definition gtA (x y:A) := ~ leA x y.
  Definition leA_dec : forall x y : A, {leA x y} + {~ leA x y}
    := leA_dec_from_total A eqA eqA_dec leA leA_total_dec
        leA_refl leA_antisym.
End OrdEqRelatA.

Require Import Peano_dec.

Module EqRelatInt.
  Definition A   := nat.
  Definition eqA := eq (A := A).
  Hint Unfold eqA.

  Lemma eqA_equiv : equivalence A eqA.
  Proof.
    apply Build_equivalence; red; auto.
    unfold eqA; intros; rewrite H; auto.
  Qed.

  Lemma eqA_dec : forall x y : A, {eqA x y} + {~ eqA x y}.
  Proof.
    unfold eqA; apply eq_nat_dec.
  Qed.
End EqRelatInt.

Module EqRelatIntA : EqRelatA := EqRelatInt.

Require Import Le.
Require Import Lt.
Require Import Bool_nat.

Module OrdEqRelatInt.
  Module eqrelat := EqRelatInt.
  Export eqrelat.

  Definition leA := le.
  Lemma leA_total_dec : forall x y : A, {leA x y} + {leA y x}.
    unfold leA; intros.
    elim lt_ge_dec with x y; intros.
     left; apply le_trans with (S x).
      auto.
      apply lt_le_S; trivial.
     right; auto with arith.
  Qed.

  Lemma leA_refl :      forall x y : A, eqA x y -> leA x y.
    unfold eqA, leA in |- *; intros.
    rewrite H; auto with arith.
  Qed.

  Lemma leA_antisym :   forall x y : A, leA x y -> leA y x -> eqA x y.
    unfold eqA, leA; intros.
    apply le_antisym; auto.
  Qed.

  Lemma leA_trans   :   transitive A leA.
    unfold leA, transitive; apply le_trans.
  Qed.

  Definition gtA (x y:A) := ~ leA x y.
  Definition leA_dec : forall x y : A, {leA x y} + {~ leA x y}
    := leA_dec_from_total A eqA eqA_dec leA leA_total_dec
        leA_refl leA_antisym.

End OrdEqRelatInt.

Module OrdEqRelatIntA : OrdEqRelatA := OrdEqRelatInt.
