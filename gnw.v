Add Rec LoadPath "../Combi/LRrule".

Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop ssralg ssrnum.
Require Import subseq.

Set Implicit Arguments.
Unset Strict Implicit.

Local Open Scope ring_scope.
Import GRing.Theory.

Section Formule.

  Variable T : countType.
  Variable R : comRingType.
  Variable alpha : T -> R.


  Lemma expand_prod_add1_seq (S : seq T) :
    \prod_(i <- S) (1 + alpha i) =
    \sum_(s <- enum_subseqs S) \prod_(i <- s) alpha i.
  Proof.
    elim: S => [| n S IHs] //=.
      rewrite /= big_nil.
      by rewrite big_cons 2! big_nil addr0.
    rewrite big_cons IHs {IHs}.
    set sub := (enum_subseqs _).
    rewrite big_cat /=.
    rewrite mulrDl mul1r addrC.
    congr ( _ + _ ).
    rewrite big_distrr /=.
    rewrite big_map.
    apply eq_bigr => i _.
    by rewrite big_cons.
  Qed.

End Formule.

Section Formule2.

  Variable T U : countType.
  Variable R : comRingType.
  Variable alpha : T -> R.
  Variable beta : U -> R.

Definition delta


  Lemma expand_prod_add1_seq2 (S : seq T) (V : seq U):
    \prod_(i <- S) (1 + alpha i) * \prod_(i <- V) (1 + beta i) =
    \sum_(s <- enum_subseqs S) \sum_(v <- enum_subseqs V) 
       (\prod_(i <- s) alpha i * (\prod_(i <- v) beta i)) .
  Proof.
    elim: S => [| n S IHs] //=.
      rewrite /= big_nil.
      by rewrite big_cons 2! big_nil addr0.
    rewrite big_cons IHs {IHs}.
    set sub := (enum_subseqs _).
    rewrite big_cat /=.
    rewrite mulrDl mul1r addrC.
    congr ( _ + _ ).
    rewrite big_distrr /=.
    rewrite big_map.
    apply eq_bigr => i _.
    by rewrite big_cons.
  Qed.

End Formule.

Section Formule.

  Variable R : comRingType.
  Variable alpha : nat -> R.


  Lemma expand_prod_add1_seq (S : seq nat) :
    \prod_(i <- S) (1 + alpha i) =
    \sum_(s <- enum_subseqs S) \prod_(i <- s) alpha i.
  Proof.
    elim: S => [| n S IHs] //=.
      rewrite /= big_nil.
      by rewrite big_cons 2! big_nil addr0.
    rewrite big_cons IHs {IHs}.
    set sub := (enum_subseqs _).
    rewrite big_cat /=.
    rewrite mulrDl mul1r addrC.
    congr ( _ + _ ).
    rewrite big_distrr /=.
    rewrite big_map.
    apply eq_bigr => i _.
    by rewrite big_cons.
  Qed.

End Formule.

Section Formule2.

  Variable R : comRingType.
  Variable alpha beta: nat -> R.

