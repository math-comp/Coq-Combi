Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import subseq.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma ieqi1F i : (i == i.+1) = false.
Proof. apply negbTE; by elim i. Qed.

Section Shape.

  Variable T : Type.

  Implicit Type s : seq nat.
  Implicit Type t : seq (seq T).

  Definition shape t := map size t.
  Fixpoint is_part sh :=
    if sh is sh0 :: sh'
    then (sh0 >= head 1 sh') && (is_part sh')
    else true.
  Definition is_out_corner sh i := nth 0 sh i > nth 0 sh i.+1.

  Lemma is_part_tl l0 sh : is_part (l0 :: sh) -> is_part sh.
  Proof. by move=> /= /andP []. Qed.

  Lemma is_partP sh :
    reflect (last 1 sh != 0 /\ forall i, (nth 0 sh i) >= nth 0 sh i.+1) (is_part sh).
  Proof.
    apply (iffP idP).
    - elim: sh => [ //= | sh0 sh IHsh] /= /andP [] Hhead Hpart.
      have:= IHsh Hpart => [] {IHsh} [] Hlast Hi.
      split; first by case: sh Hhead Hpart Hlast Hi => [/= | sh1 sh //=]; case sh0.
      case => [|i] /=; first by move: Hhead; case sh.
      exact (Hi i).
    - elim: sh => [ //= | sh0 sh IHsh] /= [] Hlast Hpart.
      apply/andP; split.
      * move: Hlast; have:= Hpart 0 => /=; case sh => //=.
        by rewrite /head ltn_neqAle eq_sym => -> ->.
      * apply IHsh; split; last by move=> i; apply (Hpart i.+1).
        move: Hlast; by case sh.
  Qed.

  Lemma part_head0F sh : head 1 sh == 0 -> is_part sh = false.
  Proof.
    elim: sh => [//= | sh0 sh IHsh] /= /eqP ->.
    rewrite leqn0; by case (boolP (head 1 sh == 0)).
  Qed.

  Lemma part_head_non0 sh : is_part sh -> head 1 sh != 0.
  Proof.
    elim: sh => [//= | sh0 sh IHsh] /= /andP [] Head.
    move/IHsh; apply contraLR; rewrite !negbK => /eqP Hsh0.
    by move: Head; rewrite Hsh0 leqn0.
  Qed.

  (* unused lemma *)
  Lemma del_out_corner sh i :
    last 1 sh != 0 -> is_part (incr_nth sh i) ->
    is_out_corner (incr_nth sh i) i = is_part sh.
  Proof.
    move=> Hn0 /is_partP [] _ Hpart1.
    apply (sameP (@idP (is_out_corner _ i))); apply (equivP (@idP (is_part _))).
    rewrite /is_out_corner; split.
    - move=> /is_partP => [] [] _ Hpart; have {Hpart} := Hpart i.
      by rewrite !nth_incr_nth ieqi1F eq_refl add0n add1n ltnS.
    - move=> Hcorn; apply /is_partP; split; first exact Hn0.
      move=> j; move: Hcorn (Hpart1 j).
      rewrite !nth_incr_nth ieqi1F eq_refl add0n add1n ltnS => Hcorn.
      case (altP (i =P j)) => [<- //=|_].
      case (altP (i =P j.+1)) => [Hi |_].
      * rewrite add0n add1n; apply ltnW.
      * by rewrite !add0n.
  Qed.

  Fixpoint shape_rowseq s :=
    if s is s0 :: s'
    then incr_nth (shape_rowseq s') s0
    else [::].

  (* Unused old definition *)
  Definition shape_rowseq_count :=
    [fun s => [seq (count_mem i) s | i <- iota 0 (foldr maxn 0 (map S s))]].

  Lemma shape_rowseq_countE : shape_rowseq_count =1 shape_rowseq.
  Proof.
    elim=>[//= | l0 s /= <-]; apply (@eq_from_nth _ 0).
    - rewrite size_incr_nth !size_map !size_iota /= {1}maxnC {1}/maxn.
      set m := foldr _ _ _; case (ltngtP l0.+1 m) => [H||->].
      * by rewrite (leq_ltn_trans (leqnSn l0) H).
      * by rewrite ltnNge => /negbTE ->.
      * by rewrite leqnn.
    - move=> i; rewrite nth_incr_nth size_map => Hsz.
      rewrite (nth_map 0 _ _ Hsz); rewrite size_iota in Hsz; rewrite (nth_iota _ Hsz).
      rewrite add0n.
      case (ltnP i (foldr maxn 0 [seq i.+1 | i <- s])) => Hi.
      * rewrite (nth_map 0 _ _); last by rewrite size_iota.
        by rewrite (nth_iota _ Hi) /= add0n.
      * rewrite (nth_default 0) /=; last by rewrite size_map size_iota.
        congr ((l0 == i) + _).
        elim: s Hi {Hsz} => [//=| s0 s /=].
        set m := foldr _ _ _ => IHs; rewrite /maxn.
        case (ltnP s0.+1 m) => Hs Hi.
        - by rewrite (IHs Hi) (ltn_eqF (leq_ltn_trans (leqnSn s0) (leq_trans Hs Hi))).
        - by rewrite (IHs (leq_trans Hs Hi)) (ltn_eqF Hi).
  Qed.

  Lemma shape_rowshape_cons l s : shape_rowseq (l :: s) = incr_nth (shape_rowseq s) l.
  Proof. by []. Qed.

  (* Yamanouchi word:                                                            *)
  (*   sequence of rows of the corners for an increasing sequence of partitions. *)
  (*   they are in bijection with standard tableaux                              *)
  Fixpoint is_yam s :=
    if s is s0 :: s'
    then is_part (shape_rowseq s) && is_yam s'
    else true.

  Lemma is_part_shyam s : is_yam s -> is_part (shape_rowseq s).
  Proof. by case: s => [//= | s0 s] /= /andP []. Qed.

  Lemma is_yam_tl l0 s : is_yam (l0 :: s) -> is_yam s.
  Proof. by move=> /= /andP []. Qed.

  Fixpoint shift_yam s :=
    if s is s0 :: s'
    then if s0 is s0'.+1
         then s0' :: (shift_yam s')
         else (shift_yam s')
    else [::].

  Lemma shape_shift s : shape_rowseq (shift_yam s) = behead (shape_rowseq s).
  Proof.
    elim: s => [//= | s0 s /= IHs].
    case s0 => [ | s0' /=].
    - rewrite IHs /=; by case (shape_rowseq s).
    - rewrite IHs /=; case (shape_rowseq s) => [|sh0 sh //=].
      by case: s0'.
  Qed.

  Lemma is_yam_shift s : is_yam s -> (is_yam (shift_yam s)).
  Proof.
    elim: s => [//= | s0 s IHs] /= /andP [] Hpart.
    move/IHs {IHs} => Hyam; case: s0 Hpart=> [//= | s0'] /=.
    rewrite Hyam andbT shape_shift.
    case H : (shape_rowseq s) => [| sh0 sh] /= /andP [] _ //=.
    by case s0'.
  Qed.

  Lemma is_out_corner_yam l0 s :
    is_yam (l0 :: s) -> is_out_corner (shape_rowseq (l0 :: s)) l0.
  Proof.
    move=> Hyam; have:= is_part_shyam (is_yam_tl Hyam) => /is_partP [] _ Hpart.
    rewrite /is_out_corner !nth_incr_nth ieqi1F eq_refl add0n add1n ltnS.
    by apply Hpart.
  Qed.

End Shape.
