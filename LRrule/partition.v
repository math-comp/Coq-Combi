(******************************************************************************)
(*       Copyright (C) 2014 Florent Hivert <florent.hivert@lri.fr>            *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop.
Require Import subseq.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma ieqi1F i : (i == i.+1) = false.
Proof. apply negbTE; by elim i. Qed.

Section Partition.

  Implicit Type s : seq nat.

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

  Lemma part0 sh : is_part sh -> sumn sh = 0 -> sh = [::].
  Proof. move/part_head_non0; by case: sh => //= [] [|s0]. Qed.

  Lemma is_part_rconsK sh sn : is_part (rcons sh sn) -> is_part sh.
  Proof.
    case: sn => [/= | sn].
      move/is_partP => []; by rewrite last_rcons.
    elim: sh => [//= | s0 sh IHsh].
    rewrite rcons_cons /= => /andP [] Hhead /IHsh {IHsh} ->.
    rewrite andbT; case: sh Hhead => [//= | s1 sh]; first by apply leq_ltn_trans.
    by rewrite rcons_cons.
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
      case (eqP (y:=j)) => [<- //=|_].
      case eqP => [Hi |_].
      * rewrite add0n add1n; apply ltnW.
      * by rewrite !add0n.
  Qed.

  Fixpoint incr_n sh n :=
    if sh is s0 :: s then
      if n is n.+1 then s0.+1 :: incr_n s n
      else sh
    else nseq n 1.
  Fixpoint conj_part sh :=
    if sh is s0 :: sh then incr_n (conj_part sh) s0
    else [::].

  Lemma is_part_n1 n : is_part (nseq n 1).
  Proof. elim: n => [//= | n /= ->]; rewrite andbT; by case n. Qed.

  Lemma is_part_incr_n sh n :
    is_part sh -> is_part (incr_n sh n).
  Proof.
    elim: sh n => [//= n _| s0 sh IHsh] /=; first by apply is_part_n1.
    case=> [//= | n] /andP [] Hhead /IHsh {IHsh} /= ->; rewrite andbT.
    case: sh Hhead => [_ | s1 sh] /=; first by case n.
    case: n => [| n] /=; last by apply.
    by move/leq_trans; apply.
  Qed.

  Lemma is_part_conj sh : is_part sh -> is_part (conj_part sh).
  Proof.
    elim: sh => [//= | s0 sh IHsh] /= /andP [] _ /IHsh {IHsh}.
    by apply is_part_incr_n.
  Qed.

  Lemma conj_nseq n : 0 < n -> conj_part (nseq n 1) = [:: n].
  Proof.
    elim: n => [//= | n IHn] /= _.
    case: n IHn => [//= | n] IHn.
    by rewrite (IHn (ltn0Sn n)).
  Qed.

  Lemma size_incr_n sh n :
    size sh <= n -> size (incr_n sh n) = n.
  Proof.
    elim: sh n => [| s0 sh IHsh] /= n; first by rewrite size_nseq.
    case: n => [//= | n]; by rewrite /= ltnS => /IHsh ->.
  Qed.

  Lemma size_conj sh : is_part sh -> size (conj_part sh) = head 0 sh.
  Proof.
    elim: sh => [//= | s0 [| s1 sh] IHsh] /= /andP [] Hhead /IHsh {IHsh} /= IHsh.
    + by rewrite size_nseq.
    + move: Hhead; by rewrite -{1}IHsh => /size_incr_n.
  Qed.

  Lemma sumn_incr_n sh n : sumn (incr_n sh n) = sumn sh + n.
  Proof.
    elim: n sh => [//= | n IHn]; first by case.
    case => [/= | s0 s /=].
    + have -> : sumn (nseq n 1) = n.
        elim: n {IHn} => //= n ->; by rewrite add1n.
      by rewrite add0n add1n.
    + by rewrite IHn addnA addnS !addSn.
  Qed.

  Lemma sumn_part_cons sh : sumn (conj_part sh) = sumn sh.
  Proof. elim: sh => [//= | s0 s IHs] /=; by rewrite sumn_incr_n IHs addnC. Qed.

  Lemma conj_part_ind sh l :
    sh != [::] -> is_part sh -> l >= size sh -> conj_part (incr_n sh l) = l :: conj_part sh.
  Proof.
    elim: sh l => [//= | s0 s IHs l] _ /=.
    move=> /andP [] _ Hpart Hs0.
    case: l Hs0 => [//= | l] /=; rewrite ltnS => Hs0.
    case: s IHs Hpart Hs0 => [//= _ _| s1 s IHs].
    + case: l => [//=| l ]; by rewrite conj_nseq; last by apply ltn0Sn.
    + have: s1 :: s != [::] by [].
      move=> Hneq Hpart Hsize /=.
      have{IHs Hneq Hpart} := IHs l Hneq Hpart Hsize.
      by case: l Hsize => [//= | l /=] _ ->.
  Qed.

  Lemma conj_partK sh : is_part sh -> conj_part (conj_part sh) = sh.
  Proof.
    elim: sh => [//=| s0 sh IHsh] /= /andP [] Hhead Hpart.
    case (altP (sh =P [::])) => Hsh.
    + move: Hhead; rewrite Hsh /=; by apply conj_nseq.
    + rewrite conj_part_ind //=; first by rewrite IHsh.
      * move: Hsh; apply contra => /eqP.
        case: sh Hpart {IHsh Hhead} => [//= | s1 s] /=.
        case: s1 => [/andP []| s1 _]; first by rewrite leqn0 => /part_head0F ->.
        by case: (conj_part s).
      * by apply is_part_conj.
      * rewrite size_conj //=.
        move: Hhead Hsh; by case sh.
  Qed.

  Lemma minn0 k : minn k 0 = 0.
  Proof. by rewrite /minn ltn0. Qed.
  Lemma minSS i j : minn i.+1 j.+1 = (minn i j).+1.
  Proof. by rewrite /minn ltnS; case ltnP. Qed.

  Definition part_sum s k := (\sum_(l <- (take k s)) l).

  Lemma sum_conj sh k : \sum_(l <- sh) minn l k = part_sum (conj_part sh) k.
  Proof.
    rewrite /part_sum.
    elim: sh => [//= | s0 sh]; first by rewrite !big_nil.
    rewrite big_cons /= => ->; move: (conj_part sh) => c.
    elim: c s0 k => [//= | c0 c IHc] s0 k /=.
    - rewrite big_nil addn0.
      elim: s0 k => [| s IHs] k /=; first by rewrite minnC minn0 big_nil.
      case: k IHs => [_| k IHs]; first by rewrite minn0 big_nil.
      by rewrite minSS big_cons -IHs add1n.
    - case: s0 => [| s0]; first by rewrite minnC minn0 add0n; case: k IHc.
      case: k => [//=| k] /=.
      rewrite !big_cons -IHc !addnA minSS.
      congr (_ + part_sum c k).
      by rewrite !addSn addnC.
  Qed.

  Lemma part_sum_inj s t :
    is_part s -> is_part t -> (forall k, part_sum s k = part_sum t k) -> s = t.
  Proof.
    rewrite /part_sum.
    elim: s t => [//= t _ | s0 s IHs t].
    + move/part_head_non0; case: t => [//= | t0 t] /= Hto IHs.
      exfalso; have:= (IHs 1); rewrite big_cons take0 big_nil addn0 => H.
      move: Hto; by rewrite H eq_refl.
    + case: t s IHs => [s _ Hs _ Heq | t0 t].
      * have := Heq 1; rewrite /= big_nil big_cons.
        have /= Hs0 := (part_head_non0 Hs).
        move/eqP; rewrite addn_eq0 => /andP [] /eqP H.
        move: Hs0; by rewrite H eq_refl.
      * move=> s IHs /is_part_tl Hps /is_part_tl Hpt /= Heq.
        have := Heq 1; rewrite !take0 !big_cons !big_nil !addn0 => Ht0; subst t0.
        congr (s0 :: _); apply (IHs _ Hps Hpt).
        move=> k; have:= Heq k.+1.
        by rewrite !big_cons => /eqP; rewrite eqn_add2l => /eqP.
  Qed.

  (* Shape of a sequence of row index (mostly Yamanouchi word) *)
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

  Lemma sum_incr_nth s i : sumn (incr_nth s i) = (sumn s).+1.
  Proof.
    elim: i s => [/= | i IHi]; first by case=> [| s0 s].
    case=> [/= | s0 s /=]; first by rewrite /sumn add0n; elim i.
    by rewrite (IHi s) addnS.
  Qed.

  Lemma shape_rowseq_eq_size y : sumn (shape_rowseq y) = size y.
  Proof. elim: y => [//= | y0 y] /=; by rewrite sum_incr_nth => ->. Qed.

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

  (* Remove the zeroes from a yam and decrease all the other entries by 1 *)
  Fixpoint decr_yam s :=
    if s is s0 :: s'
    then if s0 is s0'.+1
         then s0' :: (decr_yam s')
         else (decr_yam s')
    else [::].

  Lemma shape_decr_yam s : shape_rowseq (decr_yam s) = behead (shape_rowseq s).
  Proof.
    elim: s => [//= | s0 s /= IHs].
    case s0 => [ | s0' /=].
    - rewrite IHs /=; by case (shape_rowseq s).
    - rewrite IHs /=; case (shape_rowseq s) => [|sh0 sh //=].
      by case: s0'.
  Qed.

  Lemma is_yam_decr s : is_yam s -> (is_yam (decr_yam s)).
  Proof.
    elim: s => [//= | s0 s IHs] /= /andP [] Hpart.
    move/IHs {IHs} => Hyam; case: s0 Hpart=> [//= | s0'] /=.
    rewrite Hyam andbT shape_decr_yam.
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

  (* Hyperstandard Yamanouchi word : 33 2222 11111 0000000 *)
  Fixpoint hyper_yam_rev sh :=
    if sh is s0 :: s then
      nseq s0 (size s) ++ hyper_yam_rev s
    else [::].
  Definition hyper_yam sh := hyper_yam_rev (rev sh).

  Lemma incr_nth_size s : incr_nth s (size s) = rcons s 1.
  Proof.  by elim: s => [| s0 s /= ->]. Qed.

  Lemma part_rcons_ind s sn : is_part (rcons s sn.+2) -> is_part (rcons s sn.+1).
  Proof.
    elim: s => [//= | s0 s IHs] /=.
    move => /andP [] Hhead /IHs {IHs} ->; rewrite andbT.
    case: s Hhead => [//= | s1 s]; first by apply ltn_trans.
    by rewrite !rcons_cons.
  Qed.

  Lemma shape_rowseq_hyper_yam sh : is_part sh -> shape_rowseq (hyper_yam sh) = sh.
  Proof.
    rewrite /hyper_yam; elim/last_ind: sh => [//= | s sn IHs].
    rewrite rev_rcons /=; case: sn => [/= | sn].
      move/is_partP; by rewrite last_rcons /= => [] [].
    elim: sn => [/= | sn /= IHsn].
      move/is_part_rconsK/IHs ->; by rewrite size_rev incr_nth_size.
    move=> Hpart; rewrite IHsn {IHsn IHs}.
    - rewrite size_rev {Hpart}; elim: s => [//= | s0 s IHs] /=.
      by rewrite IHs.
    - by apply part_rcons_ind.
  Qed.

  Lemma hyper_yamP sh : is_part sh -> is_yam (hyper_yam sh).
  Proof.
    elim/last_ind: sh => [//= | s sn IHs].
    rewrite /hyper_yam rev_rcons /=; case: sn => [//= | sn].
      move/is_partP; by rewrite last_rcons /= => [] [].
    elim: sn => [/= | sn /= IHsn].
      move=> Hpart1; have Hpart := is_part_rconsK Hpart1.
      by rewrite (IHs Hpart) size_rev (shape_rowseq_hyper_yam Hpart) incr_nth_size Hpart1.
    move=> Hpart2; have {IHsn} /andP [] := IHsn (part_rcons_ind Hpart2).
    move=> -> ->; rewrite !andbT.
    have:= Hpart2; by rewrite -{1}(shape_rowseq_hyper_yam Hpart2) /hyper_yam rev_rcons.
  Qed.

End Partition.
