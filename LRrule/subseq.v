Require Import ssreflect ssrbool ssrfun ssrnat eqtype choice fintype seq.

Section RCons.

  Variable (T : eqType).
  Implicit Type s w : seq T.
  Implicit Type a b l : T.

  Lemma nth_any s a b i : i < size s -> nth a s i = nth b s i.
  Proof. elim: s i => //= s0 s IHs [//=|i] Hsize /=. by apply IHs. Qed.

  Lemma cons_in_map_cons a b s w :
    forall l : seq (seq T), a :: s \in [seq b :: s1 | s1 <- l] -> a == b.
  Proof.
    elim=> [//=| l0 l H]; rewrite map_cons in_cons; move/orP => []; last by exact H.
    by move=> /eqP [] ->.
  Qed.

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

Section Fintype.

  Variable (T : countType).
  Implicit Type s w : seq T.
  Implicit Type a b l : T.

  Fixpoint subseqs_dup w :=
    if w is w0 :: w' then
      [seq w0 :: s | s <- subseqs_dup w' ] ++ subseqs_dup w'
    else [:: [::] ].

  Definition subseqs w := undup (subseqs_dup w).

  Lemma subseqs_all s w : subseq s w <-> s \in subseqs w.
  Proof.
    rewrite mem_undup; split.
    elim: w s => [H /eqP -> //=| w0 w IHw].
    have Hinjcons: injective (cons w0) by move=> x1 x2 [].
    case=> [_|s0 s]; simpl; first by rewrite mem_cat (IHw _ (sub0seq w)); apply orbT.
    case: (altP (s0 =P w0)) => [-> | _] H; move: {H} (IHw _ H); rewrite mem_cat.
    - by rewrite -[s \in _](mem_map Hinjcons) => ->.
    - by move->; apply orbT.
    elim: w s => [H | w0 w IHw]; first by rewrite mem_seq1.
    have Hinjcons: injective (cons w0) by move=> x1 x2 [].
    case=> [_|s0 s /=]; first by apply sub0seq.
    case: (altP (s0 =P w0)) => [->|Hneq]; rewrite mem_cat => /orP [].
    * rewrite (mem_map Hinjcons); by apply IHw.
    * move/IHw => H; by apply (subseq_trans (subseq_cons _ _) H).
    * move/cons_in_map_cons => H; rewrite (eqP (H s)) in Hneq.
      by rewrite (eq_refl w0) in Hneq.
    * by apply IHw.
  Qed.

  Definition is_subseq w := fun s => subseq s w.

  Definition SubSeq w := {s | is_subseq w s}.

  Definition sub_eqMixin w := sig_eqMixin (is_subseq w).
  Canonical sub_eqType w := sig_eqType (is_subseq w).

  Definition sub_nil w : (SubSeq w) :=
    (exist (is_subseq w) [::] (sub0seq (T := T) w)).

  Definition sub_full w : (SubSeq w) :=
    (exist (is_subseq w) w (subseq_refl w)).

  Definition sub_extend (w0 : T) w (s : SubSeq w) : SubSeq (w0 :: w).
  case: s => s Ps; exists s; apply (subseq_trans Ps); by apply subseq_cons. Defined.

  Lemma sub_extend_eq (w0 : T) w : val \o (sub_extend w0 w) =1 val.
  Proof. by case=> s Ps /=. Qed.

  Definition sub_cons (w0 : T) w (s : SubSeq w) : SubSeq (w0 :: w).
  case: s => s Ps; exists (w0 :: s); by rewrite /= (eq_refl w0). Defined.

  Lemma sub_cons_eq (w0 : T) w : [eta val] \o [eta sub_cons w0 w] =1 (cons w0) \o val.
  Proof. by case=> s Ps /=. Qed.

  Fixpoint SubSeqs_dup w : seq (SubSeq w) :=
    match w as w return seq (SubSeq w) with
      | [::] => [:: sub_nil [::]]
      | w0 :: w =>
        [seq sub_cons  w0 w s | s <- SubSeqs_dup w ] ++
        [seq sub_extend w0 w s | s <- SubSeqs_dup w ]
    end.
  Definition SubSeqs w := undup (SubSeqs_dup w).

  Lemma val_SubSeqs w : subseqs_dup w == [seq val s | s <- SubSeqs_dup w].
  Proof.
    elim: w => [//=|w0 w IHw /=].
    rewrite map_cat -!map_comp (eq_map (sub_cons_eq w0 w)) (eq_map (sub_extend_eq w0 w)).
    by rewrite (eqP IHw) -map_comp.
  Qed.

  Lemma mem_val_SubSeqs w (s : (SubSeq w)) :
    (s \in SubSeqs_dup w) = (val s \in subseqs_dup w).
  Proof. rewrite (eqP (val_SubSeqs w)) mem_map //=; by apply val_inj. Qed.

  Lemma SubSeqs_enumP w : Finite.axiom (SubSeqs w).
  Proof.
    rewrite /Finite.axiom /SubSeqs => S.
    rewrite count_uniq_mem; last by apply undup_uniq.
    rewrite mem_undup mem_val_SubSeqs /= -mem_undup.
    case: S => s /=; rewrite subseqs_all; by move ->.
  Qed.

  Definition SubSeq_finMixin w := Eval hnf in FinMixin (SubSeqs_enumP w).
  Canonical SubSeq_finType w := Eval hnf in FinType (SubSeq w) (SubSeq_finMixin w).
  Coercion seq_of_SubSeq w (s : (SubSeq w)) := val s.

  Lemma size_le w (s : (SubSeq w)) : size s <= size w.
  Proof. case: s => s Ps; by apply size_subseq. Qed.

End Fintype.

Section MaxLen.

  Variable w : seq nat.
  Definition PSeq := [fun i : nat => [exists s : SubSeq nat_countType w, size s == i]].

  Lemma ex0 : PSeq 0.
  Proof. apply /existsP. by exists (sub_nil _ w). Qed.

  Lemma max_len : forall i : nat, PSeq i -> i <= size w.
  Proof. rewrite /PSeq => i /= /existsP [[s Hs]] /eqP <-; by apply size_le. Qed.

  Definition max_subseq_size := ex_maxn (P := PSeq) (ex_intro _ 0 ex0) max_len.

  Lemma size_max_subseq : max_subseq_size == size w.
  Proof.
    rewrite /max_subseq_size; case (ex_maxnP (ex_intro _ 0 ex0) max_len) => i Hi Hleqi.
    apply/eqP/anti_leq/andP; split; first by apply max_len.
    suff: PSeq (size w); first by apply Hleqi.
    rewrite /PSeq /=; apply /existsP.
    by exists (sub_full _ w).
  Qed.

End MaxLen.

