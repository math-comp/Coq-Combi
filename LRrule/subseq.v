Require Import ssreflect ssrbool ssrfun ssrnat eqtype choice fintype seq.

Set Implicit Arguments.
Unset Strict Implicit.

Section RCons.

  Variable (T : eqType).
  Implicit Type s w : seq T.
  Implicit Type a b l : T.

  Lemma nth_any s a b i : i < size s -> nth a s i = nth b s i.
  Proof. elim: s i => //= s0 s IHs [//=|i] Hsize /=. by apply IHs. Qed.

  Lemma set_nth_non_nil d s n y : set_nth d s n y != [::].
  Proof. elim: s => [|s0 s]; by case n. Qed.

  Lemma rcons_set_nth a s l : set_nth a s (size s) l = rcons s l.
  Proof. elim: s => [//=| l0 s IHs]. by rewrite rcons_cons -IHs /=. Qed.

  Lemma cons_in_map_cons a b s w :
    forall l : seq (seq T), a :: s \in [seq b :: s1 | s1 <- l] -> a == b.
  Proof.
    elim=> [//=| l0 l H]; rewrite map_cons in_cons; move/orP => []; last by exact H.
    by move=> /eqP [] ->.
  Qed.

  Lemma rcons_nilF s l : ((rcons s l) == [::]) = false.
  Proof.
    case (altP (rcons s l =P [::])) => //= H.
    have:= eq_refl (size (rcons s l)). by rewrite {2}H size_rcons.
  Qed.

  Lemma subseq_rcons_eq s w l : subseq s w <-> subseq (rcons s l) (rcons w l).
  Proof.
    split.
    - by rewrite -!cats1 => H; apply cat_subseq => //=; rewrite (eq_refl _).
    - elim: w s => [|w0 w IHw s] /=.
      case=> //= s0 s; case (altP (s0 =P l)) => _ //=; by rewrite rcons_nilF.
    - case: s IHw => //= s0 s; case (altP (s0 =P w0)) => _ //= H1 H2; first by apply H1.
      rewrite -rcons_cons in H2; by apply H1.
  Qed.

  Lemma subseq_rcons_neq s si w wn :
    si != wn -> subseq (rcons s si) (rcons w wn) -> subseq (rcons s si) w.
  Proof.
    elim: w s si=> [/=| w0 w IHw] s si H.
    - case: s => [| s0 s] /=; first by case: (altP (si =P wn)) H.
      case (altP (s0 =P wn)) => //= ->; by rewrite rcons_nilF.
    - case: s => [/=| s0 s].
      * case (altP (si =P w0)) => [_ _|Hneq]; first by apply sub0seq.
        rewrite -[ [:: si] ]/(rcons [::] si); exact (IHw _ _ H).
      * rewrite !rcons_cons /=; case (altP (s0 =P w0)) => _; first exact (IHw _ _ H).
        rewrite -rcons_cons; exact (IHw _ _ H).
  Qed.

  Lemma count_mem_rcons w l i : count_mem i (rcons w l) = count_mem i w + (l == i).
  Proof. by rewrite -count_rev rev_rcons /= count_rev addnC. Qed.

End RCons.

Section Fintype.
  (* We define SubSeq w as a finType *)

  Variable (T : countType).
  Implicit Type s w : seq T.
  Implicit Type a b l : T.

  Fixpoint subseqs w :=
    if w is w0 :: w' then
      [seq w0 :: s | s <- subseqs w' ] ++ subseqs w'
    else [:: [::] ].

  Lemma subseqs_all s w : subseq s w <-> s \in subseqs w.
  Proof.
    split; elim: w s => [H| w0 w IHw].
    * by move=> /eqP ->.
    * have Hinjcons: injective (cons w0) by move=> x1 x2 [].
      case=> [_|s0 s]; simpl; first by rewrite mem_cat (IHw _ (sub0seq w)); apply orbT.
      case (altP (s0 =P w0)) => [-> | _] H; move: {H} (IHw _ H); rewrite mem_cat.
      - by rewrite -[s \in _](mem_map Hinjcons) => ->.
      - by move->; apply orbT.

    * by rewrite mem_seq1.
    * have Hinjcons: injective (cons w0) by move=> x1 x2 [].
      case=> [_|s0 s /=]; first by apply sub0seq.
      case (altP (s0 =P w0)) => [->|Hneq]; rewrite mem_cat => /orP [].
      - rewrite (mem_map Hinjcons); by apply IHw.
      - move/IHw => H; by apply (subseq_trans (subseq_cons _ _) H).
      - move/cons_in_map_cons => H; rewrite (eqP (H s)) in Hneq.
        by rewrite (eq_refl w0) in Hneq.
      - by apply IHw.
  Qed.

  Definition SubSeq w := seq_sub (subseqs w).
  Coercion seq_of_SubSeq w (s : (SubSeq w)) : seq T := ssval s.

  Definition Sub_of_subseq w s : subseq s w -> SubSeq w.
  Proof. move => H; apply (SeqSub (ssval := s)); by rewrite -subseqs_all. Defined.

  Definition sub_nil  w : (SubSeq w) := Sub_of_subseq (sub0seq w).
  Definition sub_full w : (SubSeq w) := Sub_of_subseq (subseq_refl w).

  Lemma size_le w (s : (SubSeq w)) : size s <= size w.
  Proof. case: s => s Ps /=; apply size_subseq; by rewrite subseqs_all. Qed.

End Fintype.

Section MaxSize.

  Variable w : seq nat.
  Definition PSeq := [fun i : nat => [exists s : SubSeq w, size s == i]].

  Lemma ex0 : PSeq 0.
  Proof. apply /existsP. by exists (sub_nil w). Qed.

  Lemma max_len : forall i : nat, PSeq i -> i <= size w.
  Proof. rewrite /PSeq => i /= /existsP [[s Hs]] /eqP <-; by apply size_le. Qed.

  Definition max_subseq_size := ex_maxn (P := PSeq) (ex_intro _ 0 ex0) max_len.

  Lemma size_max_subseq : max_subseq_size == size w.
  Proof.
    rewrite /max_subseq_size; case (ex_maxnP (ex_intro _ 0 ex0) max_len) => i Hi Hleqi.
    apply/eqP/anti_leq/andP; split; first by apply max_len.
    suff: PSeq (size w); first by apply Hleqi.
    rewrite /PSeq /=; apply /existsP.
    by exists (sub_full w).
  Qed.

End MaxSize.
