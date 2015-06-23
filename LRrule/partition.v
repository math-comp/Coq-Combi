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
Require Import tools combclass.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma ieqi1F i : (i == i.+1) = false.
Proof. apply: negbTE; by elim i. Qed.

Section Partition.

  Implicit Type s : seq nat.

  Fixpoint is_part sh :=
    if sh is sh0 :: sh'
    then (sh0 >= head 1 sh') && (is_part sh')
    else true.
  Definition is_out_corner sh i := nth 0 sh i > nth 0 sh i.+1.

  Lemma is_part_tl l0 sh : is_part (l0 :: sh) -> is_part sh.
  Proof. by move=> /= /andP []. Qed.

  Lemma is_part_behead sh : is_part sh -> is_part (behead sh).
  Proof. case: sh => [//| l0 sh] /=; exact: is_part_tl. Qed.

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

  Lemma is_part_ijP sh :
    reflect (last 1 sh != 0 /\ forall i j, i <= j -> (nth 0 sh i) >= nth 0 sh j) (is_part sh).
  Proof.
    apply: (iffP idP).
    - move/is_partP => [] H0 H; split; first exact H0.
      move=> i {H0} j /subnKC <-.
      elim: (j - i) => [|n IHn] {j}; first by rewrite addn0.
      rewrite addnS.
      exact: (leq_trans (H _) IHn).
    - move=> [] H0 H; apply/is_partP; split; first exact H0.
      move=> {H0} i.
      exact: H.
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

  Lemma last_incr_nth_non0 sh i : last 1 sh != 0 -> last 1 (incr_nth sh i) != 0.
  Proof.
    rewrite -!nth_last size_incr_nth.
    case (ltnP i (size sh)) => Hi.
    - have Hsz : (size sh).-1 < size sh by move: Hi; case: (size sh).
      rewrite (nth_any 1 0 (s := (incr_nth sh i))); last by rewrite size_incr_nth Hi Hsz.
      rewrite nth_incr_nth; apply contra.
      rewrite addn_eq0 => /andP [] _ H.
      by rewrite (nth_any 1 0).
   - move=> _ /=.
     rewrite (nth_any 1 0); last by rewrite size_incr_nth [i < size sh]ltnNge Hi /=.
     by rewrite nth_incr_nth eq_refl.
  Qed.

  Lemma is_part_incr_nth_size sh l :
    is_part sh -> is_part (incr_nth sh l) -> l <= size sh.
  Proof.
    elim: sh l => [//= | sh0 sh IHsh] /= l.
      move => _.
      case: l => [| i] //= /andP []; by rewrite leqn0 => /part_head0F ->.
    case: l => [//= | l].
    by rewrite ltnS /= => /andP [] _ /IHsh H /andP [] _ /H.
  Qed.

  Definition is_in_corner sh := [pred i | (i == 0) || (nth 0 sh i < nth 0 sh i.-1)].

  Lemma is_part_incr_nth sh i : is_part sh -> is_in_corner sh i -> is_part (incr_nth sh i).
  Proof.
    rewrite /is_in_corner; move=> /is_partP [] Hhead Hpart.
    case (altP (i =P 0)) => [-> _ {i} | Hi /= H]; apply/is_partP.
    - case: sh Hhead Hpart => [//= _ _ | s0 sh /=]; first by split => //= [] [].
      move=> Hlast Hi; split; first by move: Hlast; case sh.
      case=> [| i]; first by apply: (leq_trans (Hi 0)) => //=.
      by have /= := Hi i.+1.
    - case: i Hi H => [//= | i] _; split; first by apply: last_incr_nth_non0.
      move: H => /= H j.
      case: sh Hhead Hpart H => [//= | s0 sh] /= Hlast Hpart Hcorn.
      + exfalso; move: Hcorn; by rewrite nth_nil.
      + rewrite !nth_incr_nth; case (altP (i =P j)) => Hi /=.
        * rewrite add1n; subst i.
          apply (leq_trans Hcorn).
          elim: j s0 sh {Hcorn Hlast Hpart} => [//= | j IHj] s0 sh /=.
          case sh => [//= | s1 sh']; first by rewrite nth_nil.
          by apply IHj.
        * rewrite add0n.
          case: j Hi => [//= | j] Hj /=; first exact (Hpart 0).
          rewrite nth_incr_nth; case (altP (i =P j)) => Hi.
          case: sh Hpart {Hlast Hcorn} => [//= | s1 sh] /= Hpart.
            by apply (leq_trans (Hpart j.+1)).
          rewrite add0n.
          case: sh Hpart {Hlast Hcorn} => [//= | s1 sh] /= Hpart.
            exact (Hpart j.+1).
  Qed.

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

  Lemma sumn_incr_nth s i : sumn (incr_nth s i) = (sumn s).+1.
  Proof.
    elim: i s => [/= | i IHi]; first by case=> [| s0 s].
    case=> [/= | s0 s /=]; first by rewrite /sumn add0n; elim i.
    by rewrite (IHi s) addnS.
  Qed.

  Lemma sumn_decr_nth sh i :
    is_part sh -> is_out_corner sh i -> (sumn (decr_nth sh i)) = (sumn sh).-1.
  Proof.
    move=> Hpart Hcorn. rewrite -{2}[sh](decr_nthK Hpart Hcorn).
    by rewrite sumn_incr_nth /=.
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

  Definition out_corners sh := filter (is_out_corner sh) (iota 0 (size sh)).

End Partition.


Section SkewShape.

  Fixpoint included inner outer :=
    if inner is inn0 :: inn then
      if outer is out0 :: out then
        (inn0 <= out0) && (included inn out)
      else false
    else true.

  Lemma includedP inner outer :
    reflect (size inner <= size outer /\ forall i, nth 0 inner i <= nth 0 outer i)
            (included inner outer).
  Proof.
    apply (iffP idP).
    - elim: inner outer => [//= | inn0 inn IHinn] /=.
        move=> outer _; by split; last by move=> i; rewrite nth_nil.
      case=> [//= | out0 out] /= /andP [] H0 /IHinn{IHinn} [] Hsize H.
      split; first by rewrite ltnS.
      by case.
    - elim: inner outer => [//= | inn0 inn IHinn] /=.
      case=> [ [] //= | out0 out] [] /=.
      rewrite ltnS => Hsize H.
      apply/andP; split; first by apply (H 0).
      apply: IHinn; split; first exact Hsize.
      move=> i; by apply (H i.+1).
  Qed.

  Lemma included_refl sh : included sh sh.
  Proof. elim: sh => [//= | s0 sh /= -> ]; by rewrite leqnn. Qed.

  Lemma included_trans sha shb shc :
    included sha shb -> included shb shc -> included sha shc.
  Proof.
    move=> /includedP [] Hsza Hincla /includedP [] Hszb Hinclb.
    apply/includedP; split; first exact (leq_trans Hsza Hszb).
    move=> i; by apply (leq_trans (Hincla i) (Hinclb i)).
  Qed.

  Lemma included_incr_nth sh i :
    included sh (incr_nth sh i).
  Proof.
    apply/includedP; split.
    - rewrite size_incr_nth; case ltnP => Hi //=.
      by apply (leq_trans Hi).
    - move=> j; rewrite nth_incr_nth.
      by apply leq_addl.
  Qed.

  Lemma included_decr_nth u i : included (decr_nth u i) u.
  Proof.
    elim: u i => [| u0 u IHu] [| i] //=.
      case: u0 => [| [| u0]] //=.
      by rewrite ltnS (leqnSn u0) (included_refl u).
    by rewrite (leqnn u0) (IHu i).
  Qed.

  Lemma included_incr_nth_inner inner outer i :
    nth 0 inner i < nth 0 outer i ->
    included inner outer -> included (incr_nth inner i) outer.
  Proof.
    move=> Hnth /includedP [] Hsize Hincl.
    apply/includedP; split.
    - rewrite size_incr_nth; case ltnP => _; first exact Hsize.
      rewrite ltnNge; apply (introN idP) => Hout.
      move: Hnth; by rewrite (nth_default _ Hout).
    - move=> j; rewrite nth_incr_nth.
      case eqP => [<- | _].
      - by rewrite add1n.
      - by rewrite add0n.
  Qed.

  Lemma size_included inner outer : included inner outer -> size inner <= size outer.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] /=.
    case=> [//= | outer0 outer] /= /andP [] _ /IHinn.
    by rewrite ltnS.
  Qed.

  Lemma sumn_included inner outer : included inner outer -> sumn inner <= sumn outer.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] /=.
    case=> [//= | outer0 outer] /= /andP [] H0 /IHinn.
    by apply: leq_add.
  Qed.

  Lemma included_sumnE inner outer :
    is_part outer ->
    included inner outer ->
    sumn inner = sumn outer ->
    inner = outer.
  Proof.
    elim: inner outer => [| inn0 inn IHinn] /=.
      by move=> outer Houter _ /esym/(part0 Houter) ->.
    case=> [//= | outer0 out] /= /andP [] _ /IHinn{IHinn}Hrec /andP [] H0 Hincl Heq.
    have {H0} H0 : inn0 = outer0.
      apply anti_leq; rewrite H0 /=.
      have := leq_sub2l (inn0 + sumn inn) (sumn_included Hincl).
      by rewrite {1}Heq !addnK.
    move: Heq => /eqP; by rewrite H0 eqn_add2l => /eqP/(Hrec Hincl) ->.
  Qed.

  Fixpoint diff_shape inner outer :=
    if inner is inn0 :: inn then
      if outer is out0 :: out then
        out0 - inn0 :: diff_shape inn out
      else [::] (* Unused case *)
    else outer.

  Definition pad (T : Type) (x : T) sz := [fun s => s ++ nseq (sz - size s) x].

  Definition outer_shape inner size_seq :=
    [seq p.1 + p.2 | p <- zip (pad 0 (size (size_seq)) inner) size_seq].

  Lemma size_diff_shape inner outer : size (diff_shape inner outer) = size outer.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] /= [//= | out0 out] /=.
    by rewrite IHinn.
  Qed.

  Lemma sumn_diff_shape inner outer :
    included inner outer -> sumn (diff_shape inner outer) = sumn outer - sumn inner.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] /= [//= | out0 out] /=.
      by rewrite subn0.
    move/andP => [] Hleq Hincl.
    rewrite (IHinn _ Hincl) {IHinn}.
    have Hsumn : sumn inn <= sumn out.
      elim: inn out Hincl => [//= | inn1 inn IHinn] /= [//= | out1 out] /=.
      move/andP => [] H1 /IHinn; by apply leq_add.
    by rewrite subnDA (addnBA _ Hsumn) addnC (addnBA _ Hleq) [out0 + _]addnC.
  Qed.

  Lemma diff_shape_pad0 inner outer :
    diff_shape ((pad 0 (size outer)) inner) outer = diff_shape inner outer.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] //=.
      elim=> [//= | out0 out] /=; by rewrite !subn0 => ->.
    case=> [//= | out0 out] /=.
    by rewrite subSS IHinn.
  Qed.

  Lemma diff_shapeK inner outer :
    included inner outer ->
    outer_shape inner (diff_shape inner outer) = outer.
  Proof.
    rewrite /outer_shape.
    elim: inner outer => [//= | inn0 inn IHinn] /= outer.
      rewrite subn0 => _; elim: outer => [//= | out0 out /= ->].
      by rewrite add0n.
   case: outer => [//= | out0 out] /= /andP [] Hin /IHinn{IHinn} ->.
   by rewrite addnC subnK.
  Qed.

  Lemma outer_shapeK inner diff :
    size inner <= size diff ->
    diff_shape inner (outer_shape inner diff) = diff.
  Proof.
    rewrite /outer_shape.
    elim: inner diff => [//= | inn0 inn IHinn] /= diff.
      rewrite subn0 => _; elim: diff => [//= | d0 diff /= ->].
      by rewrite add0n.
    case: diff => [//=| t0 t] /=; rewrite ltnS subSS => /IHinn /= ->.
    by rewrite addKn.
  Qed.


  Lemma outer_shape_pad0 inner sz :
    outer_shape (pad 0 (size sz) inner) sz = outer_shape inner sz.
  Proof.
    rewrite /outer_shape; congr map; congr zip.
    rewrite /= size_cat size_nseq.
    set n := (X in (_++ _) ++ nseq X _).
    suff -> : n = 0 by rewrite /= cats0.
    rewrite /n{n}.
    move: (size sz) (size inner) => a b.
    case: (ltnP a b) => [/ltnW | ] H.
    - move: H; rewrite /leq => /eqP H; by rewrite H addn0 H.
    - by rewrite (subnKC H) subnn.
  Qed.

  Lemma head_pad0 (T : Type) n (p : T) s : head p (pad p n s) = head p s.
  Proof. elim: s => [| s0 s IHs] //=; rewrite subn0; by case: n. Qed.

  Lemma included_pad0 inner outer :
    included inner outer = included (pad 0 (size outer) inner) outer.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] /= outer /=.
     rewrite subn0; by elim: outer.
    case: outer => [//= | out0 out] /=.
    by rewrite subSS IHinn.
Qed.

End SkewShape.


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


Fixpoint enum_partnsk sm sz mx : (seq (seq nat)) :=
  if sz is sz.+1 then
    flatten [seq [seq i :: p | p <- enum_partnsk (sm - i) sz i] | i <- iota 1 (minn sm mx)]
  else if sm is sm.+1 then [::] else [:: [::]].
Definition enum_partns sm sz := enum_partnsk sm sz sm.
Definition enum_partn sm := flatten [seq enum_partns sm sz | sz <- iota 0 sm.+1 ].

Definition is_part_of_n   sm       := [pred p | (sumn p == sm)   & is_part p ].
Definition is_part_of_ns  sm sz    := [pred p | (size p == sz)   & is_part_of_n sm p].
Definition is_part_of_nsk sm sz mx := [pred p | (head 1 p <= mx) & is_part_of_ns sm sz p].

Lemma enum_partnsk_allP sm sz mx :
  mx >= 1 -> all (is_part_of_nsk sm sz mx) (enum_partnsk sm sz mx).
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

Lemma enum_partnsk_countE sm sz mx :
  mx >= 1 ->
  forall p, is_part_of_nsk sm sz mx p -> count_mem p (enum_partnsk sm sz mx) = 1.
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
  rewrite sumn_iota //= add1n ltnS leq_min Hp0 -Hsm leq_addr !andbT.
  have /part_head_non0 /= : is_part (p0 :: p) by rewrite /= Hhead Hpart.
  by rewrite lt0n.
Qed.

Lemma enum_partnskE sm sz mx :
  mx >= 1 ->
  forall p, count_mem p (enum_partnsk sm sz mx) = is_part_of_nsk sm sz mx p.
Proof.
  move=> Hx p. case (boolP ((is_part_of_nsk sm sz mx) p)) => H /=.
  - by rewrite enum_partnsk_countE.
  - apply/count_memPn; move: H; apply: contra.
    by apply: (allP (enum_partnsk_allP _ _ Hx)).
Qed.

Lemma enum_partns_allP sm sz : all (is_part_of_ns sm sz) (enum_partns sm sz).
Proof.
  apply/allP; rewrite /enum_partns => /= p.
  case: sm => [/= | sm]; first by case: sz; rewrite //= mem_seq1 => /eqP ->.
  have /enum_partnsk_allP/allP Hall : sm.+1 >= 1 by [].
  by move=> /Hall /= /andP [] _.
Qed.

Lemma enum_partns_countE sm sz p :
  is_part_of_ns sm sz p -> count_mem p (enum_partns sm sz) = 1.
Proof.
  rewrite /enum_partns.
  case: p => /= [ /and3P [] /eqP <- /eqP <- //= | p0 p] /and4P [] Hsz Hsum Hhead Hpart.
  rewrite enum_partnsk_countE //=.
  - rewrite -(eqP Hsum); apply: (@leq_trans p0); last by apply: leq_addr.
    have /part_head_non0 /= : is_part (p0 :: p) by rewrite /= Hhead Hpart.
    by rewrite lt0n.
  - by rewrite Hsz Hsum Hhead Hpart -(eqP Hsum) leq_addr.
Qed.

Lemma enum_partnsE sm sz p :
  count_mem p (enum_partns sm sz) = is_part_of_ns sm sz p.
Proof.
  case (boolP ((is_part_of_ns sm sz) p)) => H /=.
  - by rewrite enum_partns_countE.
  - apply/count_memPn; move: H; apply: contra.
    by apply: (allP (enum_partns_allP _ _)).
Qed.

Lemma enum_partn_allP sm : all (is_part_of_n sm) (enum_partn sm).
Proof.
  apply/allP; rewrite /enum_partn => /= p.
  case: sm => [/= | sm]; first by rewrite mem_seq1 => /eqP ->.
  rewrite cat0s => /flatten_mapP [] i.
  rewrite mem_iota ltnS => /andP [] Hposi Hi.
  have /enum_partnsk_allP/allP Hall : sm.+1 >= 1 by [].
  by move=> /Hall /= /and3P [].
Qed.

Lemma enum_partn_countE sm p :
  is_part_of_n sm p -> count_mem p (enum_partn sm) = 1.
Proof.
  rewrite /enum_partn /= => /andP [] Hsum Hpart.
  rewrite count_cat enum_partnsE /= Hsum Hpart !andbT.
  case: (altP (size p =P 0)) => Hsize.
  - rewrite count_flatten -map_comp.
    set empty := map _ _.
    have {empty} -> : empty = [seq 0 | i <- iota 1 sm].
      rewrite /empty {empty} -eq_in_map => i /=.
      rewrite mem_iota add1n ltnS => /andP [] /lt0n_neq0 Hi _.
      apply/count_memPn => /=; move: Hi; apply: contra.
      move/(allP (enum_partns_allP _ _)) => /= /andP [] /eqP <- _.
      by rewrite Hsize.
    have -> : sumn (map (fun _ => 0) _) = 0.
      move=> T; by elim => [//= |l0 l /= ->].
    by rewrite addn0.
  - rewrite /= add0n count_flatten -map_comp; set ci := (X in map X _).
    have {ci} /eq_map -> : ci =1 fun i => i == size p.
      rewrite /ci {ci} => i /=; rewrite enum_partnsE /=.
      by rewrite Hsum Hpart !andbT eq_sym.
    rewrite sumn_iota //= add1n ltnS lt0n Hsize /= -(eqP Hsum).
    by apply: size_part.
Qed.

Lemma enum_partnP n p : (is_part_of_n n p) = (p \in enum_partn n).
Proof.
  apply/(sameP idP); apply(iffP idP).
  - by move/(allP (enum_partn_allP n)).
  - rewrite -has_pred1 has_count; by move/enum_partn_countE ->.
Qed.

Section PartOfn.

Variable n : nat.

Structure intpartn : predArgType :=
  IntPartN {pnval :> seq nat; _ : is_part_of_n n pnval}.
Canonical intpartn_subType := Eval hnf in [subType for pnval].
Definition intpartn_eqMixin := Eval hnf in [eqMixin of intpartn by <:].
Canonical intpartn_eqType := Eval hnf in EqType intpartn intpartn_eqMixin.
Definition intpartn_choiceMixin := Eval hnf in [choiceMixin of intpartn by <:].
Canonical intpartn_choiceType := Eval hnf in ChoiceType intpartn intpartn_choiceMixin.
Definition intpartn_countMixin := Eval hnf in [countMixin of intpartn by <:].
Canonical intpartn_countType := Eval hnf in CountType intpartn intpartn_countMixin.
Canonical intpartn_subCountType := Eval hnf in [subCountType of intpartn].

Let type := sub_finType intpartn_subCountType (enum_partn_allP n) (@enum_partn_countE n).
Canonical intpartn_finType := Eval hnf in [finType of intpartn for type].
Canonical intpartn_subFinType := Eval hnf in [subFinType of intpartn].

Lemma intpartnP (p : intpartn) : is_part p.
Proof. by case: p => /= p /andP []. Qed.

Lemma intpartn_sumn (p : intpartn) : sumn p = n.
Proof. by case: p => /= p /andP [] /eqP. Qed.

Lemma enum_intpartnE : map val (enum intpartn) = enum_partn n.
Proof. rewrite /=; by apply enum_subP. Qed.

End PartOfn.

Fixpoint intpartnsk_nb sm sz mx : nat :=
  if sz is sz.+1 then
    (* \sum_(1 <= i <= (minn sm mx)) intpartnsk_nb (sm - i) sz i *)
    iteri (minn sm mx) (fun i s => s + intpartnsk_nb (sm - i.+1) sz i.+1) 0
  else if sm is sm.+1 then 0 else 1.
Definition intpartns_nb sm sz := intpartnsk_nb sm sz sm.
Definition intpartn_nb sm := iteri (sm.+1) (fun sz s => s + intpartns_nb sm sz) 0.

Lemma size_enum_partnsk sm sz mx :
  size (enum_partnsk sm sz mx) = (intpartnsk_nb sm sz mx).
Proof.
  elim: sz sm mx => [ [] | sz IHsz] //= sm mx.
  rewrite size_flatten /shape -[1]addn0 iota_addl -!map_comp.
  rewrite (eq_map (f2 := fun i => intpartnsk_nb (sm - i.+1) sz i.+1)); first last.
    by move=> i /=; rewrite size_map IHsz.
  elim: (minn sm mx) => [//= | n IHn].
  by rewrite -{1}[n.+1]addn1 iota_add add0n map_cat sumn_cat IHn /= addn0.
Qed.

Lemma size_enum_partns sm sz :
  size (enum_partns sm sz) = (intpartns_nb sm sz).
Proof. by rewrite size_enum_partnsk. Qed.

Lemma size_enum_partn sm :
  size (enum_partn sm) = intpartn_nb sm.
Proof.
  rewrite /intpartn_nb /enum_partn size_flatten /shape.
  elim: (sm.+1) => [//= | n IHn].
  rewrite -{1}[n.+1]addn1 iota_add add0n !map_cat sumn_cat IHn /= addn0.
  by rewrite size_enum_partns.
Qed.

Lemma card_intpartn sm : #|intpartn sm| = intpartn_nb sm.
Proof.
  rewrite [#|_|]cardT enumT unlock /=.
  by rewrite -(size_map val) subType_seqP -size_enum_partn.
Qed.

End PartCombClass.
