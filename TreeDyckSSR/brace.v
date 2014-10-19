Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Braces.

  Inductive Brace : Set :=
    | Open : Brace | Close : Brace.

  Definition eq_brace b1 b2 :=
    match b1, b2 with
      | Open, Open | Close, Close => true
      | _, _ => false
    end.

  Lemma eq_braceP : Equality.axiom eq_brace.
  Proof.
    move=> n m; apply: (iffP idP) => [|<-]; last by elim n.
    elim: n; elim m; by [].
  Qed.

  Canonical brace_eqMixin := EqMixin eq_braceP.
  Canonical brace_eqType := Eval hnf in EqType Brace brace_eqMixin.

  Definition encode_Brace b := if b is Close then 0 else 1.
  Definition decode_Brace n := if n is 0 then Close else Open.

  Lemma decodeBraceK : cancel encode_Brace decode_Brace. Proof. by case. Qed.

  Definition brace_choiceMixin := CanChoiceMixin decodeBraceK.
  Canonical brace_choiceType := Eval hnf in ChoiceType Brace brace_choiceMixin.
  Definition brace_countMixin := CanCountMixin decodeBraceK.
  Canonical brace_countType := Eval hnf in CountType Brace brace_countMixin.

  Lemma brace_enumP : Finite.axiom [:: Open; Close]. Proof. by case. Qed.

  Definition brace_finMixin := FinMixin brace_enumP.
  Canonical brace_finType := Eval hnf in FinType Brace brace_finMixin.

  Lemma card_Brace : #|{: Brace }| = 2. Proof. by rewrite cardT enumT unlock. Qed.

End Braces.
