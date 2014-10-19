Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq tuple.

Set Implicit Arguments.
Unset Strict Implicit.


Import Coq.Init.Logic.EqNotations.
Require Import Coq.Logic.ProofIrrelevance.
Import EqdepTheory.

Section RewFacts.

  Variable N : Set.
  Variable T : N -> Set.

  Implicit Type n : N.

  Lemma rewR n (x : T n) : rew (Logic.eq_refl n) in x = x.
  Proof. by rewrite /eq_rec_r. Qed.

  Lemma rewRH n (x : T n) (H : n = n) : x = rew H in x.
  Proof. by apply eq_rect_eq. Qed.

  Lemma rewT n0 n1 n2 (x : T n0) (H0 : n0 = n1) (H1 : n1 = n2) :
    rew H1 in (rew H0 in x) = rew (eq_trans H0 H1) in x.
  Proof. rewrite /eq_rec_r /eq_rec /eq_rect /=; subst n2; by []. Qed.

  Lemma rewK n m (x : T n) (Hn : n = m) (Hm : m = n) :
    x = rew Hm in (rew Hn in x).
  Proof. by rewrite rewT -rewRH. Qed.

End RewFacts.
