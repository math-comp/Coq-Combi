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
Require Import vectNK. (* for count_flatten *)

Set Implicit Arguments.
Unset Strict Implicit.

Lemma ieqi1F i : (i == i.+1) = false.
Proof. apply: negbTE; by elim i. Qed.

Lemma sumn_count (T : eqType) (l : seq T) (P : pred T) :
  sumn [seq nat_of_bool (P i) | i <- l] = count P l.
Proof. by elim: l => //= l0 l /= ->. Qed.

Lemma countEP (T : eqType) (P : pred T) (l : list T) e :
  (P e -> count_mem e l = 1) -> (P e -> e \in l).
Proof.
  move=> H/H{H}H. have : (count_mem e) l != 0 by rewrite H.
  by apply: contraR => /count_memPn ->.
Qed.

Lemma shape_rev T (s : seq (seq T)) : shape (rev s) = rev (shape s).
Proof. rewrite /shape; elim: s => [//= | s0 s IHs] /=; by rewrite map_rev. Qed.

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
    apply: (iffP idP).
    - elim: sh => [ //= | sh0 sh IHsh] /= /andP [] Hhead Hpart.
      have:= IHsh Hpart => [] {IHsh} [] Hlast Hi.
      split; first by case: sh Hhead Hpart Hlast Hi => [/= | sh1 sh //=]; case sh0.
      case => [|i] /=; first by move: Hhead; case sh.
      exact (Hi i).
    - elim: sh => [ //= | sh0 sh IHsh] /= [] Hlast Hpart.
      apply/andP; split.
      * move: Hlast; have:= Hpart 0 => /=; case sh => //=.
        by rewrite /head ltn_neqAle eq_sym => -> ->.
      * apply: IHsh; split; last by move=> i; apply: (Hpart i.+1).
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
    move/IHsh; apply: contraLR; rewrite !negbK => /eqP Hsh0.
    by move: Head; rewrite Hsh0 leqn0.
  Qed.

  Lemma part0 sh : is_part sh -> sumn sh = 0 -> sh = [::].
  Proof. move/part_head_non0; by case: sh => //= [] [|s0]. Qed.

  Lemma size_part sh : is_part sh -> size sh <= sumn sh.
  Proof.
    elim: sh => [//= | s0 sh IHsh] /= /andP [] Hhead Hpart.
    apply: (leq_ltn_trans (IHsh Hpart)).
    rewrite -{1}[sumn sh]add0n ltn_add2r.
    have /part_head_non0 /= : is_part (s0 :: sh) by rewrite /= Hhead Hpart.
    by rewrite lt0n.
  Qed.

  Lemma part_sumn_rectangle (sh : seq nat) :
    is_part sh -> sumn sh <= (head 0 sh) * (size sh).
  Proof.
    elim: sh => [//= | s0 s IHs] /= /andP [] Hhead /IHs {IHs} Hsum.
    rewrite mulnS leq_add2l.
    apply (leq_trans Hsum).
    rewrite {Hsum} leq_mul2r.
    by case: s Hhead => [//= | s1 s].
  Qed.

  Lemma is_part_rconsK sh sn : is_part (rcons sh sn) -> is_part sh.
  Proof.
    case: sn => [/= | sn].
      move/is_partP => []; by rewrite last_rcons.
    elim: sh => [//= | s0 sh IHsh].
    rewrite rcons_cons /= => /andP [] Hhead /IHsh {IHsh} ->.
    rewrite andbT; case: sh Hhead => [//= | s1 sh]; first by apply: leq_ltn_trans.
    by rewrite rcons_cons.
  Qed.

(*
  Definition is_in_corner sh i := (i == 0) || (nth 0 sh i > nth 0 sh i.-1).

  Lemma last_incr_nth_non0 sh i : last 1 sh != 0 -> last 1 (incr_nth sh i) != 0.
  Proof.
  Qed.

  Lemma is_part_incr_nth sh i : is_part sh -> is_in_corner sh i -> is_part (incr_nth sh i).
  Proof.
    rewrite /is_in_corner; move=> /is_partP [] Hhead Hpart.
    case (altP (i =P 0)) => [-> _ {i} | Hi /= H]; apply/is_partP.
    - case: sh Hhead Hpart => [//= _ _ | s0 sh /=]; first by split => //= [] [].
      move=> Hlast Hi; split; first by move: Hlast; case sh.
      case=> [| i]; first by apply: (leq_trans (Hi 0)) => //=.
      by have /= := Hi i.+1.
    - case: i Hi H => [//= | i] _; split.
      + by apply: last_incr_nth_non0.
      + move: H => /= H j.
        case: sh Hhead Hpart H => [//= | s0 sh] /= Hlast Hpart Hcorn.
        rewrite !nth_incr_nth; case (altP (i =P j)) => Hi /=.
        * rewrite add1n; subst i; have:= Hpart j.
          move /(leq_trans Hcorn); by rewrite ltnn.
        * rewrite add0n; have := Hpart j; case: j Hi => [//= _ | j] /= _.
          move/leq_trans; apply; rewrite nth_incr_nth.
          by apply: leq_addl.
  Qed.

  Lemma in_corner_leq_size sh i : is_in_corner sh i -> i <= size sh.
  Proof.
    rewrite /is_in_corner => /orP [/eqP -> //= | ].
    case (ltnP i (size sh)) => [/ltnW -> //= | Hi].
    by rewrite (nth_default _ Hi).
  Qed.
*)

  (* unused lemma *)
  Lemma del_out_corner sh i :
    last 1 sh != 0 -> is_part (incr_nth sh i) ->
    is_out_corner (incr_nth sh i) i = is_part sh.
  Proof.
    move=> Hn0 /is_partP [] _ Hpart1.
    apply: (sameP (@idP (is_out_corner _ i))); apply: (equivP (@idP (is_part _))).
    rewrite /is_out_corner; split.
    - move=> /is_partP => [] [] _ Hpart; have {Hpart} := Hpart i.
      by rewrite !nth_incr_nth ieqi1F eq_refl add0n add1n ltnS.
    - move=> Hcorn; apply/is_partP; split; first exact Hn0.
      move=> j; move: Hcorn (Hpart1 j).
      rewrite !nth_incr_nth ieqi1F eq_refl add0n add1n ltnS => Hcorn.
      case (eqP (y:=j)) => [<- //=|_].
      case eqP => [Hi |_].
      * rewrite add0n add1n; apply: ltnW.
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
    elim: sh n => [//= n _| s0 sh IHsh] /=; first by apply: is_part_n1.
    case=> [//= | n] /andP [] Hhead /IHsh {IHsh} /= ->; rewrite andbT.
    case: sh Hhead => [_ | s1 sh] /=; first by case n.
    case: n => [| n] /=; last by apply.
    by move/leq_trans; apply.
  Qed.

  Lemma is_part_conj sh : is_part sh -> is_part (conj_part sh).
  Proof.
    elim: sh => [//= | s0 sh IHsh] /= /andP [] _ /IHsh {IHsh}.
    by apply: is_part_incr_n.
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
    + case: l => [//=| l ]; by rewrite conj_nseq; last by apply: ltn0Sn.
    + have: s1 :: s != [::] by [].
      move=> Hneq Hpart Hsize /=.
      have{IHs Hneq Hpart} := IHs l Hneq Hpart Hsize.
      by case: l Hsize => [//= | l /=] _ ->.
  Qed.

  Lemma conj_partK sh : is_part sh -> conj_part (conj_part sh) = sh.
  Proof.
    elim: sh => [//=| s0 sh IHsh] /= /andP [] Hhead Hpart.
    case (altP (sh =P [::])) => Hsh.
    + move: Hhead; rewrite Hsh /=; by apply: conj_nseq.
    + rewrite conj_part_ind //=; first by rewrite IHsh.
      * move: Hsh; apply: contra => /eqP.
        case: sh Hpart {IHsh Hhead} => [//= | s1 s] /=.
        case: s1 => [/andP []| s1 _]; first by rewrite leqn0 => /part_head0F ->.
        by case: (conj_part s).
      * by apply: is_part_conj.
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
        congr (s0 :: _); apply: (IHs _ Hps Hpt).
        move=> k; have:= Heq k.+1.
        by rewrite !big_cons => /eqP; rewrite eqn_add2l => /eqP.
  Qed.

  (* Shape of a sequence of row index (mostly Yamanouchi word) *)
  Fixpoint shape_rowseq s :=
    if s is s0 :: s'
    then incr_nth (shape_rowseq s') s0
    else [::].

  (* equivalent definition *)
  Definition shape_rowseq_count :=
    [fun s => [seq (count_mem i) s | i <- iota 0 (foldr maxn 0 (map S s))]].

  Lemma shape_rowseq_countE : shape_rowseq_count =1 shape_rowseq.
  Proof.
    elim=>[//= | l0 s /= <-]; apply: (@eq_from_nth _ 0).
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

  Lemma sumn_incr_nth s i : sumn (incr_nth s i) = (sumn s).+1.
  Proof.
    elim: i s => [/= | i IHi]; first by case=> [| s0 s].
    case=> [/= | s0 s /=]; first by rewrite /sumn add0n; elim i.
    by rewrite (IHi s) addnS.
  Qed.

  Lemma shape_rowseq_eq_size y : sumn (shape_rowseq y) = size y.
  Proof. elim: y => [//= | y0 y] /=; by rewrite sumn_incr_nth => ->. Qed.

  (* Yamanouchi word:                                                            *)
  (*   sequence of rows of the corners for an increasing sequence of partitions. *)
  (*   they are in bijection with standard tableaux                              *)
  Fixpoint is_yam s :=
    if s is s0 :: s'
    then is_part (shape_rowseq s) && is_yam s'
    else true.

  Lemma is_part_shyam s : is_yam s -> is_part (shape_rowseq s).
  Proof. by case: s => [//= | s0 s] /= /andP []. Qed.

  Lemma yam0 y : is_yam y -> shape_rowseq y = [::] -> y = [::].
  Proof.
    case: y => [//= | y0 y] /= _.
    case: y0 => [| y0] /=; by case (shape_rowseq y).
  Qed.

  Lemma is_yam_tl l0 s : is_yam (l0 :: s) -> is_yam s.
  Proof. by move=> /= /andP []. Qed.

  Lemma is_yam_suffix s t : is_yam (s ++ t) -> is_yam t.
  Proof. by elim: s => [//= | s0 s IHs] /= /andP [] _ /IHs. Qed.

  Lemma last_yam y : is_yam y -> last 0 y = 0.
  Proof.
    case/lastP: y => [//= | y yn].
    rewrite last_rcons.
    elim: y => [//= | y0 y IHy] /=.
      case: yn => [//= | y] /= /andP [] H _.
      by elim: y H => [//= | yn IHy] /= /IHy.
    move=> /andP [] _; exact IHy.
  Qed.

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
    by apply: Hpart.
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
    case: s Hhead => [//= | s1 s]; first by apply: ltn_trans.
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
    - by apply: part_rcons_ind.
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




Section PartCombClass.

Structure intpart : Type := IntPart {pval :> seq nat; _ : is_part pval}.
Canonical intpart_subType := Eval hnf in [subType for pval].
Definition intpart_eqMixin := Eval hnf in [eqMixin of intpart by <:].
Canonical intpart_eqType := Eval hnf in EqType intpart intpart_eqMixin.
Definition intpart_choiceMixin := Eval hnf in [choiceMixin of intpart by <:].
Canonical intpart_choiceType := Eval hnf in ChoiceType intpart intpart_choiceMixin.
Definition intpart_countMixin := Eval hnf in [countMixin of intpart by <:].
Canonical intpart_countType := Eval hnf in CountType intpart intpart_countMixin.

Lemma intpartP (p : intpart) : is_part p.
Proof. by case: p. Qed.

Definition intpart_conj p := IntPart (is_part_conj (intpartP p)).

Lemma intpart_conjK : involutive intpart_conj.
Proof.  move=> p; apply: val_inj => /=; by rewrite conj_partK; last by apply: intpartP. Qed.

Lemma intpart_sum_inj (s t : intpart) :
  (forall k, part_sum s k = part_sum t k) -> s = t.
Proof.
  move=> H; apply: val_inj => /=.
  apply: part_sum_inj; last exact H; by apply: intpartP.
Qed.


Fixpoint list_partnsk sm sz mx : (seq (seq nat)) :=
  if sz is sz.+1 then
    flatten [seq [seq i :: p | p <- list_partnsk (sm - i) sz i] | i <- iota 1 (minn sm mx)]
  else if sm is sm.+1 then [::] else [:: [::]].
Definition list_partns sm sz := list_partnsk sm sz sm.
Definition list_partn sm := flatten [seq list_partns sm sz | sz <- iota 0 sm.+1 ].

Definition is_part_of_n   sm       := [pred p | (sumn p == sm)   & is_part p ].
Definition is_part_of_ns  sm sz    := [pred p | (size p == sz)   & is_part_of_n sm p].
Definition is_part_of_nsk sm sz mx := [pred p | (head 1 p <= mx) & is_part_of_ns sm sz p].

Lemma list_partnsk_allP sm sz mx :
  mx >= 1 -> all (is_part_of_nsk sm sz mx) (list_partnsk sm sz mx).
Proof.
  move=> Hmx; apply/allP => /=.
  elim: sz sm mx Hmx => [/= [] //= | sz IHsz sm] /= mx Hmx p.
    rewrite mem_seq1 => /eqP -> /=; by rewrite Hmx.
  move/flatten_mapP => [] i.
  rewrite mem_iota ltnS => /andP [] Hposi Himin /mapP [] recp.
  move/(IHsz _ _ Hposi)/and4P => [] Hp Hsum Hsz Hhead -> /= {IHsz}.
  rewrite Hp (eqP Hsum) (eqP Hsz) Hhead {Hp Hsum Hsz Hhead} /=.
  move: Himin; rewrite leq_min => /andP [] /subnKC -> ->.
  by rewrite !eq_refl.
Qed.

Lemma list_partnsk_countE sm sz mx :
  mx >= 1 ->
  forall p, is_part_of_nsk sm sz mx p -> count_mem p (list_partnsk sm sz mx) = 1.
Proof.
  elim: sz sm mx => [//= | sz IHsz] /= sm mx Hmx.
    by move=> p /and4P [] Hhead/nilP -> /= /eqP <-.
  case=> [| p0 p] //=; first by rewrite andbF.
  move=> /and5P [] Hp0; rewrite eqSS=> /eqP Hsz /eqP Hsm Hhead Hpart.
  rewrite count_flatten -map_comp; set ci := (X in map X _).
  have {ci} /eq_map -> : ci =1 fun i => i == p0.
    rewrite /ci {ci} => i /=; rewrite count_map /=.
    case (altP (i =P p0)) => [Heq | /negbTE Hneq].
    - subst p0; rewrite (eq_count (a2 := pred_of_simpl (pred1 p))); first last.
        move=> s; by rewrite /= -eqseqE /= eq_refl /=.
      rewrite IHsz //=.
      + have /part_head_non0 /= : is_part (i :: p) by rewrite /= Hhead Hpart.
        by rewrite lt0n.
      + by rewrite Hhead Hsz -Hsm addKn !eq_refl Hpart.
    - rewrite (eq_count (a2 := pred0)); first by rewrite count_pred0.
      move=> s; by rewrite /= -eqseqE /= Hneq.
  rewrite sum_iota //= add1n ltnS leq_min Hp0 -Hsm leq_addr !andbT.
  have /part_head_non0 /= : is_part (p0 :: p) by rewrite /= Hhead Hpart.
  by rewrite lt0n.
Qed.

Lemma list_partnskE sm sz mx :
  mx >= 1 ->
  forall p, count_mem p (list_partnsk sm sz mx) = is_part_of_nsk sm sz mx p.
Proof.
  move=> Hx p. case (boolP ((is_part_of_nsk sm sz mx) p)) => H /=.
  - by rewrite list_partnsk_countE.
  - apply/count_memPn; move: H; apply: contra.
    by apply: (allP (list_partnsk_allP _ _ Hx)).
Qed.

Lemma list_partns_allP sm sz : all (is_part_of_ns sm sz) (list_partns sm sz).
Proof.
  apply/allP; rewrite /list_partns => /= p.
  case: sm => [/= | sm]; first by case: sz; rewrite //= mem_seq1 => /eqP ->.
  have /list_partnsk_allP/allP Hall : sm.+1 >= 1 by [].
  by move=> /Hall /= /andP [] _.
Qed.

Lemma list_partns_countE sm sz p :
  is_part_of_ns sm sz p -> count_mem p (list_partns sm sz) = 1.
Proof.
  rewrite /list_partns.
  case: p => /= [ /and3P [] /eqP <- /eqP <- //= | p0 p] /and4P [] Hsz Hsum Hhead Hpart.
  rewrite list_partnsk_countE //=.
  - rewrite -(eqP Hsum); apply: (@leq_trans p0); last by apply: leq_addr.
    have /part_head_non0 /= : is_part (p0 :: p) by rewrite /= Hhead Hpart.
    by rewrite lt0n.
  - by rewrite Hsz Hsum Hhead Hpart -(eqP Hsum) leq_addr.
Qed.

Lemma list_partnsE sm sz p :
  count_mem p (list_partns sm sz) = is_part_of_ns sm sz p.
Proof.
  case (boolP ((is_part_of_ns sm sz) p)) => H /=.
  - by rewrite list_partns_countE.
  - apply/count_memPn; move: H; apply: contra.
    by apply: (allP (list_partns_allP _ _)).
Qed.

Lemma list_partn_allP sm : all (is_part_of_n sm) (list_partn sm).
Proof.
  apply/allP; rewrite /list_partn => /= p.
  case: sm => [/= | sm]; first by rewrite mem_seq1 => /eqP ->.
  rewrite cat0s => /flatten_mapP [] i.
  rewrite mem_iota ltnS => /andP [] Hposi Hi.
  have /list_partnsk_allP/allP Hall : sm.+1 >= 1 by [].
  by move=> /Hall /= /and3P [].
Qed.

Lemma list_partn_countE sm p :
  is_part_of_n sm p -> count_mem p (list_partn sm) = 1.
Proof.
  rewrite /list_partn /= => /andP [] Hsum Hpart.
  rewrite count_cat list_partnsE /= Hsum Hpart !andbT.
  case: (altP (size p =P 0)) => Hsize.
  - rewrite count_flatten -map_comp.
    set empty := map _ _.
    have {empty} -> : empty = [seq 0 | i <- iota 1 sm].
      rewrite /empty {empty} -eq_in_map => i /=.
      rewrite mem_iota add1n ltnS => /andP [] /lt0n_neq0 Hi _.
      apply/count_memPn => /=; move: Hi; apply: contra.
      move/(allP (list_partns_allP _ _)) => /= /andP [] /eqP <- _.
      by rewrite Hsize.
    have -> : sumn (map (fun _ => 0) _) = 0.
      move=> T; by elim => [//= |l0 l /= ->].
    by rewrite addn0.
  - rewrite /= add0n count_flatten -map_comp; set ci := (X in map X _).
    have {ci} /eq_map -> : ci =1 fun i => i == size p.
      rewrite /ci {ci} => i /=; rewrite list_partnsE /=.
      by rewrite Hsum Hpart !andbT eq_sym.
    rewrite sum_iota //= add1n ltnS lt0n Hsize /= -(eqP Hsum).
    by apply: size_part.
Qed.

Lemma list_partnP n p : (is_part_of_n n p) = (p \in list_partn n).
Proof.
  apply/(sameP idP); apply(iffP idP).
  - by move/(allP (list_partn_allP n)).
  - rewrite -has_pred1 has_count; by move/list_partn_countE ->.
Qed.

Section PartOfn.

Variable n : nat.

Structure intpartn : Type :=
  IntPartN {pnval :> seq nat; _ : is_part_of_n n pnval}.
Canonical intpartn_subType := Eval hnf in [subType for pnval].
Definition intpartn_eqMixin := Eval hnf in [eqMixin of intpartn by <:].
Canonical intpartn_eqType := Eval hnf in EqType intpartn intpartn_eqMixin.
Definition intpartn_choiceMixin := Eval hnf in [choiceMixin of intpartn by <:].
Canonical intpartn_choiceType := Eval hnf in ChoiceType intpartn intpartn_choiceMixin.
Definition intpartn_countMixin := Eval hnf in [countMixin of intpartn by <:].
Canonical intpartn_countType := Eval hnf in CountType intpartn intpartn_countMixin.
Canonical intpartn_subCountType := Eval hnf in [subCountType of intpartn].

Definition intpartn_enum : seq intpartn := pmap insub (list_partn n).

Lemma finite_intpartn : Finite.axiom intpartn_enum.
Proof.
  case=> /= p Hp; rewrite -(count_map _ (pred1 p)) (pmap_filter (@insubK _ _ _)).
  rewrite count_filter -(@eq_count _ (pred1 p)) => [|s /=]; last first.
    by rewrite isSome_insub; case: eqP=> // ->.
  by apply: list_partn_countE.
Qed.

Canonical intpartn_finMixin := Eval hnf in FinMixin finite_intpartn.
Canonical intpartn_finType := Eval hnf in FinType intpartn intpartn_finMixin.
Canonical intpartn_subFinType := Eval hnf in [subFinType of intpartn_countType].

Lemma intpartnP (p : intpartn) : is_part p.
Proof. by case: p => /= p /andP []. Qed.

Lemma intpartn_sumn (p : intpartn) : sumn p = n.
Proof. by case: p => /= p /andP [] /eqP. Qed.

Definition to_intpart (p : intpartn) := IntPart (intpartnP p).
Coercion to_intpart : intpartn >-> intpart.

End PartOfn.

Fixpoint intpartnsk_nb sm sz mx : nat :=
  if sz is sz.+1 then
    (* \sum_(1 <= i <= (minn sm mx)) intpartnsk_nb (sm - i) sz i *)
    iteri (minn sm mx) (fun i s => s + intpartnsk_nb (sm - i.+1) sz i.+1) 0
  else if sm is sm.+1 then 0 else 1.
Definition intpartns_nb sm sz := intpartnsk_nb sm sz sm.
Definition intpartn_nb sm := iteri (sm.+1) (fun sz s => s + intpartns_nb sm sz) 0.

Lemma size_list_partnsk sm sz mx :
  size (list_partnsk sm sz mx) = (intpartnsk_nb sm sz mx).
Proof.
  elim: sz sm mx => [ [] | sz IHsz] //= sm mx.
  rewrite size_flatten /shape -[1]addn0 iota_addl -!map_comp.
  rewrite (eq_map (f2 := fun i => intpartnsk_nb (sm - i.+1) sz i.+1)); first last.
    by move=> i /=; rewrite size_map IHsz.
  elim: (minn sm mx) => [//= | n IHn].
  by rewrite -{1}[n.+1]addn1 iota_add add0n map_cat sumn_cat IHn /= addn0.
Qed.

Lemma size_list_partns sm sz :
  size (list_partns sm sz) = (intpartns_nb sm sz).
Proof. by rewrite size_list_partnsk. Qed.

Lemma size_list_partn sm :
  size (list_partn sm) = intpartn_nb sm.
Proof.
  rewrite /intpartn_nb /list_partn size_flatten /shape.
  elim: (sm.+1) => [//= | n IHn].
  rewrite -{1}[n.+1]addn1 iota_add add0n !map_cat sumn_cat IHn /= addn0.
  by rewrite size_list_partns.
Qed.

Lemma card_intpartn sm : #|{:intpartn sm}| = intpartn_nb sm.
Proof.
  rewrite [#|_|]cardT enumT unlock /= /intpartn_enum size_pmap_sub -size_list_partn.
  have := list_partn_allP sm; by rewrite all_count => /eqP.
Qed.

End PartCombClass.


Fixpoint decr_nth v i {struct i} :=
  if v is n :: v' then
    if i is i'.+1 then n :: decr_nth v' i'
    else if n is n'.+1 then
           if n' is _.+1 then
             n' :: v'
           else [::]
         else [::]
  else [::].

Lemma incr_nthK sh i :
  is_part sh -> is_part (incr_nth sh i) -> decr_nth (incr_nth sh i) i = sh.
Proof.
  elim: sh i => [| s0 sh IHsh] /=.
    case=> [| i] //= _ /andP []; by rewrite leqn0 => /part_head0F ->.
  case=> [| i] //=.
    case: s0 => //= /andP []; by rewrite leqn0 => /part_head0F ->.
  move=> /andP [] Head Hpart /andP [] Headincr Hpartincr.
  by rewrite IHsh.
Qed.

Lemma decr_nthK sh i :
  is_part sh -> is_out_corner sh i -> incr_nth (decr_nth sh i) i = sh.
Proof.
  rewrite /is_out_corner.
  elim: sh i => [| s0 sh IHsh] /=; first by case.
  case=> [| i] /=; case: s0 => [| s0] //= /andP [].
    - move=> {IHsh} Hs0 /part_head_non0 Hhead H ; case: s0 Hs0 H Hhead => //= _.
      case: sh => //= s1 sh; by rewrite ltnS leqn0 => /eqP ->.
    - by rewrite leqn0 => /part_head0F ->.
  move=> Hhead Hpart Hnth; by rewrite IHsh.
Qed.

Lemma is_part_decr_nth sh i :
  is_part sh -> is_out_corner sh i -> is_part (decr_nth sh i).
Proof.
  rewrite /is_out_corner.
  elim: sh i => [| s0 sh IHsh] /=; first by case.
  case=> [| i] /=.
  - case: s0 => [| [| s0]] //= /andP [] _ ->.
    case sh => //= s1 _; by rewrite ltnS => ->.
  move=> /andP [] Hhead Hpart Hnth.
  apply/andP; split; last by apply: IHsh.
  apply: (@leq_trans (head 1 sh)); last exact Hhead.
  case: sh {IHsh Hhead Hnth s0} Hpart => [//= | s1 s]; first by case i.
  case i => //= /andP [].
  case: s1 => [| [| s1]] //=.
  by rewrite leqn0 => /part_head0F ->.
Qed.

Lemma sumn_decr_nth sh i :
  is_part sh -> is_out_corner sh i -> (sumn (decr_nth sh i)) = (sumn sh).-1.
Proof.
  move=> Hpart Hcorn. rewrite -{2}[sh](decr_nthK Hpart Hcorn).
  by rewrite sumn_incr_nth /=.
Qed.

Definition out_corners sh := filter (is_out_corner sh) (iota 0 (size sh)).

Fixpoint list_yamshn n sh :=
  if n is n'.+1 then
    flatten [seq [seq i :: y | y <- list_yamshn n' (decr_nth sh i)] |
                  i <- iota 0 (size sh) & is_out_corner sh i]
  else [:: [::]].
Definition list_yamsh sh := list_yamshn (sumn sh) sh.
Definition is_yam_of_shape sh y := (is_yam y) && (shape_rowseq y == sh).
Definition is_yam_of_size n y := (is_yam y) && (size y == n).

Lemma list_yamshP sh:
  is_part sh -> all (is_yam_of_shape sh) (list_yamsh sh).
Proof.
  move=> Hpart; apply/allP => y.
  rewrite /list_yamsh /is_yam_of_shape; move Hn: (sumn sh) => n.
  elim: n sh Hpart Hn y => [| n IHn] /= .
    by move=> sh Hsh /part0 H0 y; rewrite mem_seq1 H0 //= => /eqP ->.
  move=> sh Hpart Hsh [/= | y0 y] /=.
  - have -> : [::] == sh = false by move: Hsh; case sh.
    by move=> /flattenP [] ltmp /mapP [] i _ -> /mapP [].
  - move/flatten_mapP => [] i; rewrite mem_filter mem_iota add0n => /and3P [] Hcorn _ Hi.
    move/mapP => [] x Hx [] Hitmp Hxtmp; subst i x.
    have Hsum : sumn (decr_nth sh y0) = n by rewrite sumn_decr_nth //= Hsh.
    have:= IHn _ (is_part_decr_nth Hpart Hcorn) Hsum _ Hx =>  /andP [] -> /eqP ->.
    by rewrite decr_nthK //= Hpart /=.
Qed.

Lemma list_yamsh_countE sh y :
  is_part sh -> is_yam_of_shape sh y -> count_mem y (list_yamsh sh) = 1.
Proof.
  rewrite /list_yamsh /is_yam_of_shape; move Hn: (sumn sh) => n.
  elim: n sh Hn y => [| n IHn] /= .
    move=> sh Hsh y /part0 H0.
    by rewrite (H0 Hsh) => /andP [] /yam0 H /eqP /H{H} ->.
  move=> sh Hsh [/= | y0 y] /= Hpart.
  - by have -> : [::] == sh = false by move: Hsh; case sh.
  - move => /andP [] /andP [] _ Hyam /eqP Htmp; subst sh.
    rewrite count_flatten -map_comp; set ci := (X in map X _).
    have {ci} /eq_map -> : ci =1 fun i => i == y0.
      rewrite /ci {ci} => i /=; rewrite count_map /=.
      case (altP (i =P y0)) => [Heq | /negbTE Hneq].
      + subst i; rewrite (eq_count (a2 := pred_of_simpl (pred1 y))); first last.
          move=> s; by rewrite /= -eqseqE /= eq_refl /=.
        rewrite (incr_nthK (is_part_shyam Hyam) Hpart) IHn //=.
        * move: Hsh; rewrite sumn_incr_nth => /eqP; by rewrite eqSS => /eqP.
        * by apply: is_part_shyam.
        * by rewrite Hyam eq_refl.
      + rewrite (eq_count (a2 := pred0)); first by rewrite count_pred0.
        move=> s; by rewrite /= -eqseqE /= Hneq.
    rewrite sumn_count count_filter.
    rewrite (eq_count (a2 := pred_of_simpl (pred1 y0))); first last.
      move=> i /=; case (altP (i =P y0)) => //= ->.
      apply: is_out_corner_yam; by rewrite /= Hpart Hyam.
    rewrite -sumn_count /=.
    rewrite sum_iota //= add0n size_incr_nth.
    by case: (ltnP y0 (size (shape_rowseq y))).
Qed.

(* TESTS:
Eval compute in list_yamsh [:: 3; 2; 1; 1].
Eval compute in out_corners [:: 2; 1].
Eval compute in [seq decr_nth [:: 2; 1] i | i <- out_corners [:: 2; 1]].
*)

Definition list_yamn n : seq (seq nat) :=
  flatten [seq list_yamsh sh | sh <- list_partn n].

Lemma list_yamnP n :
  all (is_yam_of_size n) (list_yamn n).
Proof.
  rewrite /is_yam_of_size /list_yamn; apply/allP => y.
  - move/flatten_mapP => [] p.
    move /(allP (list_partn_allP n)) => /= /andP [] /eqP <- /list_yamshP /allP H/H{H}.
    rewrite /is_yam_of_shape => /andP [] -> /eqP <- /=.
    by rewrite shape_rowseq_eq_size.
Qed.

Lemma list_yamn_countE n y :
  is_yam_of_size n y -> count_mem y (list_yamn n) = 1.
Proof.
  rewrite /is_yam_of_size => /andP [] Hyam /eqP Hsz.
  rewrite /list_yamn count_flatten -map_comp.
  set ci := (X in map X _).
  have {ci} /eq_in_map -> : {in list_partn n, ci =1 fun i => i == (shape_rowseq y)}.
    rewrite /ci {ci} => i /=.
    case (altP (i =P shape_rowseq y)) => [-> | Hneq].
    - rewrite list_yamsh_countE //=; first by apply: is_part_shyam.
      by rewrite /is_yam_of_shape Hyam eq_refl.
    - rewrite -list_partnP /= => /andP [] /eqP Hsum Hpart.
      apply/count_memPn; move: Hneq; apply: contra.
      move/(allP (list_yamshP Hpart)).
      by rewrite /is_yam_of_shape => /andP [] _ /eqP ->.
  rewrite sumn_count /=.
  rewrite (eq_count (a2 := (pred1 (shape_rowseq y)))); last by [].
  apply: list_partn_countE.
  by rewrite /= -Hsz shape_rowseq_eq_size eq_refl is_part_shyam.
Qed.

Section YamOfShape.

Variable sh : seq nat.
Hypothesis Hpart : is_part sh.

Structure yamsh : Type :=
  YamSh {yamshval :> seq nat; _ : is_yam_of_shape sh yamshval}.
Canonical yamsh_subType := Eval hnf in [subType for yamshval].
Definition yamsh_eqMixin := Eval hnf in [eqMixin of yamsh by <:].
Canonical yamsh_eqType := Eval hnf in EqType yamsh yamsh_eqMixin.
Definition yamsh_choiceMixin := Eval hnf in [choiceMixin of yamsh by <:].
Canonical yamsh_choiceType := Eval hnf in ChoiceType yamsh yamsh_choiceMixin.
Definition yamsh_countMixin := Eval hnf in [countMixin of yamsh by <:].
Canonical yamsh_countType := Eval hnf in CountType yamsh yamsh_countMixin.
Canonical yamsh_subCountType := Eval hnf in [subCountType of yamsh].

Definition yamsh_enum : seq yamsh := pmap insub (list_yamsh sh).

Lemma finite_yamsh : Finite.axiom yamsh_enum.
Proof.
  case=> /= p Hp; rewrite -(count_map _ (pred1 p)) (pmap_filter (@insubK _ _ _)).
  rewrite count_filter -(@eq_count _ (pred1 p)) => [|s /=]; last first.
    by rewrite isSome_insub; case: eqP=> // ->.
  by apply: list_yamsh_countE.
Qed.

Canonical yamsh_finMixin := Eval hnf in FinMixin finite_yamsh.
Canonical yamsh_finType := Eval hnf in FinType yamsh yamsh_finMixin.
Canonical yamsh_subFinType := Eval hnf in [subFinType of yamsh_countType].

Lemma yamshP (y : yamsh) : is_yam y.
Proof. by case: y => /= y /andP []. Qed.

Lemma yamsh_sumn (y : yamsh) : shape_rowseq y = sh.
Proof. by case: y => /= y /andP [] _ /eqP. Qed.

End YamOfShape.


Section YamOfSize.

Variable n : nat.

Structure yamn : Type :=
  Yamn {yamnval :> seq nat; _ : is_yam_of_size n yamnval}.
Canonical yamn_subType := Eval hnf in [subType for yamnval].
Definition yamn_eqMixin := Eval hnf in [eqMixin of yamn by <:].
Canonical yamn_eqType := Eval hnf in EqType yamn yamn_eqMixin.
Definition yamn_choiceMixin := Eval hnf in [choiceMixin of yamn by <:].
Canonical yamn_choiceType := Eval hnf in ChoiceType yamn yamn_choiceMixin.
Definition yamn_countMixin := Eval hnf in [countMixin of yamn by <:].
Canonical yamn_countType := Eval hnf in CountType yamn yamn_countMixin.
Canonical yamn_subCountType := Eval hnf in [subCountType of yamn].


Definition yamn_enum : seq yamn := pmap insub (list_yamn n).

Lemma finite_yamn : Finite.axiom yamn_enum.
Proof.
  case=> /= y Hy; rewrite -(count_map _ (pred1 y)) (pmap_filter (@insubK _ _ _)).
  rewrite count_filter -(@eq_count _ (pred1 y)) => [|s /=]; last first.
    by rewrite isSome_insub; case: eqP=> // ->.
  by apply: list_yamn_countE.
Qed.

Canonical yamn_finMixin := Eval hnf in FinMixin finite_yamn.
Canonical yamn_finType := Eval hnf in FinType yamn yamn_finMixin.
Canonical yamn_subFinType := Eval hnf in [subFinType of yamn_countType].

Lemma yamnP (y : yamn) : is_yam y.
Proof. by case: y => /= y /andP []. Qed.

Lemma yamn_sumn (y : yamn) : size y = n.
Proof. by case: y => /= y /andP [] _ /eqP. Qed.

End YamOfSize.
