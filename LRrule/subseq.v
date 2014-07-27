Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype seq.

Section RCons.

  Variable (T : eqType).
  Implicit Type s w : seq T.
  Implicit Type a b l : T.

  Lemma nth_any s a b i : i < size s -> nth a s i = nth b s i.
  Proof. elim: s i => //= s0 s IHs [//=|i] Hsize /=. by apply IHs. Qed.

  Lemma rcons_non_nil s l : ((rcons s l) == [::]) = false.
  Proof.
    case: (altP (rcons s l =P [::])) => //= H.
    have := eq_refl (size (rcons s l)). by rewrite {2}H size_rcons.
  Qed.

  Lemma subseq_rcons_eq s w l : subseq s w <-> subseq (rcons s l) (rcons w l).
  Proof.
    split.
    - by rewrite -!cats1 => H; apply cat_subseq => //=; rewrite (eq_refl _).
    - elim: w s => [|w0 w IHw s] /=.
      case=> //= s0 s; case: (altP (s0 =P l)) => _ //=; by rewrite rcons_non_nil.
    - case: s IHw => //= s0 s; case: (altP (s0 =P w0)) => _ //= H1 H2; first by apply H1.
      rewrite -rcons_cons in H2; by apply H1.
  Qed.

  Lemma subseq_rcons_neq s si w wn :
    si != wn -> subseq (rcons s si) (rcons w wn) -> subseq (rcons s si) w.
  Proof.
    elim: w s si=> [/=| w0 w IHw] s si H.
    - case: s => [| s0 s] /=; first by case: (altP (si =P wn)) H.
      case: (altP (s0 =P wn)) => //= ->; by rewrite rcons_non_nil.
    - case: s => [/=| s0 s].
      * case: (altP (si =P w0)) => [_ _|Hneq]; first by apply sub0seq.
        rewrite -[ [:: si] ]/(rcons [::] si); exact (IHw _ _ H).
      * rewrite !rcons_cons => /=; case: (altP (s0 =P w0)) => _; first by exact (IHw _ _ H).
        rewrite -rcons_cons; by exact (IHw _ _ H).
  Qed.

End RCons.
