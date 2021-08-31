(** * Combi.Combi.skewpart : Skew Partitions *)
(******************************************************************************)
(*      Copyright (C) 2021-2021 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * Skew partitions:

- [hb_strip inn out] == [inn/out] is an horizontal border strip.
- [vb_strip inn out] == [inn/out] is a vertical border strip.
******)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple finfun finset bigop path.

Require Import tools partition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Horizontal and vertical border strips *)
Fixpoint hb_strip inner outer :=
  if inner is inn0 :: inn then
    if outer is out0 :: out then
      (head 0 out <= inn0 <= out0) && (hb_strip inn out)
    else false
  else if outer is out0 :: out then out == [::]
       else true.

Fixpoint vb_strip inner outer :=
  if outer is out0 :: out then
    if inner is inn0 :: inn then
      (inn0 <= out0 <= inn0.+1) && (vb_strip inn out)
    else (out0 == 1) && (vb_strip [::] out)
  else inner == [::].

Lemma hb_strip_included inner outer :
  hb_strip inner outer -> included inner outer.
Proof using.
elim: inner outer => [| inn0 inn IHinn] [| out0 out] //=.
by move=> /andP [] /andP [] _ -> /IHinn ->.
Qed.

Lemma hb_strip_size inner outer :
  hb_strip inner outer -> size inner <= size outer <= (size inner).+1.
Proof using.
elim: inner outer => [| inn0 inn IHinn] [| out0 out] //=.
  by move=> /eqP ->.
by move=> /andP [_ /IHinn]; rewrite !ltnS.
Qed.

Lemma vb_strip_included inner outer :
  vb_strip inner outer -> included inner outer.
Proof using.
elim: inner outer => [| inn0 inn IHinn] [| out0 out] //=.
by move=> /andP [] /andP [] -> _ /IHinn ->.
Qed.

Lemma hb_stripP inner outer :
  is_part inner -> is_part outer ->
  reflect
    (forall i, nth 0 outer i.+1 <= nth 0 inner i <= nth 0 outer i)
    (hb_strip inner outer).
Proof using.
move=> Hinn Hout; apply (iffP idP).
- elim: inner outer {Hinn Hout} => [| inn0 inn IHinn] /= [| out0 out] //=.
    by move=> /eqP -> i; rewrite leqnn /= nth_default.
  by move=> /andP [H0 /IHinn{IHinn}Hrec] [//= | i]; exact: Hrec.
- elim: inner Hinn outer Hout => [| inn0 inn IHinn] Hinn /=
                                 [| out0 out] Hout //= H.
  + have:= H 0 => /andP []; rewrite nth_nil leqn0 => /eqP {}H _.
    have:= part_head_non0 (is_part_consK Hout).
    by rewrite -nth0; case: out H {Hout} => //= out1 out' ->.
  + move/part_head_non0 : Hinn; move/(_ 0) : H.
    by rewrite /= leqn0 => ->.
  + have:= H 0; rewrite nth0 /= => -> /=.
    apply (IHinn (is_part_consK Hinn) _ (is_part_consK Hout)) => i.
    exact: H i.+1.
Qed.

Lemma vb_stripP inner outer :
  is_part inner -> is_part outer ->
  reflect
    (forall i, nth 0 inner i <= nth 0 outer i <= (nth 0 inner i).+1)
    (vb_strip inner outer).
Proof using.
move=> Hinn Hout; apply (iffP idP) => [Hstrip|].
- elim: outer inner Hstrip Hout Hinn => [| out0 out IHout] //= [| inn0 inn].
  + by move=> _ _ _ i; rewrite nth_default.
  + by move => /eqP.
  + move=> /andP [] /eqP -> {out0 IHout} H _ _ [|i] //=.
    elim: out H i => [_ i| out1 out IHout] /=.
      by rewrite nth_default.
    by move=> /andP [] /eqP -> /IHout{IHout} Hrec; case.
  + by move=> /andP [H0 {}/IHout Hrec]
              /andP [Hout {}/Hrec Hrec]
              /andP [Hinn {}/Hrec Hrec] [|i] //=.
- elim: outer inner Hout Hinn => [| out0 out IHout].
  + case => //= inn0 inn _ /= /andP [Habs Hinn] H; exfalso.
    move/(_ 0) : H => /= /andP []; rewrite leqn0 => /eqP Hinn0 _.
    by subst inn0; move: Habs Hinn; rewrite leqn0 => /part_head0F ->.
  + move=> inner Hpart; have:= part_head_non0 Hpart => /=.
    rewrite -lt0n eqn_leq => H0out.
    case: inner => [_ {IHout} H | inn0 inn]/=.
    * rewrite H0out.
      have:= H 0 => /= -> /=.
      have {H} /= Hout i := H i.+1.
      move: Hpart => /= /andP [] _.
      elim: out Hout => [//= | out1 out IHout] H Hpart.
      have:= part_head_non0 Hpart => /=.
      rewrite -lt0n eqn_leq => ->.
      have:= H 0 => /= -> /=.
      apply: IHout; last exact: (is_part_consK Hpart).
      by move=> i; exact: H i.+1.
    * move: Hpart => /andP [] H0 {}/IHout Hrec
                      /andP [] _ {}/Hrec Hrec H.
      have := H 0 => /= -> /=.
      apply Hrec => i.
      exact: H i.+1.
Qed.

Lemma vb_strip_conj inner outer :
  is_part inner -> is_part outer ->
  vb_strip inner outer -> hb_strip (conj_part inner) (conj_part outer).
Proof using.
move=> Hinn Hout.
have Hcinn := is_part_conj Hinn; have Hcout := is_part_conj Hout.
move => /(vb_stripP Hinn Hout) H.
apply/(hb_stripP Hcinn Hcout) => i; rewrite -!conj_leqE //.
apply/andP; split.
+ move/(_ (nth 0 (conj_part inner) i)) : H => /andP [] _ /leq_trans.
  by apply; rewrite ltnS conj_leqE.
+ move/(_ (nth 0 (conj_part outer) i)) : H => /andP [] /leq_trans H _.
  by apply H; rewrite conj_leqE.
Qed.

Lemma hb_strip_conj inner outer :
  is_part inner -> is_part outer ->
  hb_strip inner outer -> vb_strip (conj_part inner) (conj_part outer).
Proof using.
move=> Hinn Hout.
have Hcinn := is_part_conj Hinn; have Hcout := is_part_conj Hout.
move => /(hb_stripP Hinn Hout) H.
apply/(vb_stripP Hcinn Hcout) => i; rewrite -!conj_leqE //.
apply/andP; split.
+ move/(_ (nth 0 (conj_part outer) i)) : H => /andP [] _ /leq_trans.
  by apply; rewrite conj_leqE.
+ move/(_ (nth 0 (conj_part inner) i)) : H => /andP [] /leq_trans H _.
  by apply H; rewrite conj_leqE.
Qed.

Lemma hb_strip_conjE inner outer :
  is_part inner -> is_part outer ->
  hb_strip (conj_part inner) (conj_part outer) = vb_strip inner outer.
Proof using.
move=> Hinn Hout; apply/idP/idP; last exact: vb_strip_conj.
rewrite -{2}(conj_partK Hinn) -{2}(conj_partK Hout).
exact: hb_strip_conj (is_part_conj Hinn) (is_part_conj Hout).
Qed.

Lemma vb_strip_conjE inner outer :
  is_part inner -> is_part outer ->
  vb_strip (conj_part inner) (conj_part outer) = hb_strip inner outer.
Proof using.
move=> Hinn Hout; apply/idP/idP; last exact: hb_strip_conj.
rewrite -{2}(conj_partK Hinn) -{2}(conj_partK Hout).
exact: vb_strip_conj (is_part_conj Hinn) (is_part_conj Hout).
Qed.


(** ** Ribbon border strips *)
Fixpoint ribbon_in inner outer :=
  if inner is inn0 :: inn then
    if outer is out0 :: out then
      (inn0 < out0) &&
      ((inn == out) || ((head 0 out == inn0.+1) && (ribbon_in inn out)))
    else false
  else if outer is out0 :: out then head 0 out <= 1
       else false.
Fixpoint ribbon inner outer :=
  ribbon_in inner outer ||
  if inner is inn0 :: inn then
    if outer is out0 :: out then
      (inn0 == out0) && (ribbon inn out)
    else false
  else false.

Section Test.
(*
Goal ~~ ribbon_in [::] [::].
Proof. by []. Qed.
Goal ~~ ribbon_in [:: 2] [:: 2].
Proof. by []. Qed.
Goal ribbon_in [::] [:: 4].
Proof. by []. Qed.
Goal ribbon_in [:: 2] [:: 4].
Proof. by []. Qed.
Goal ~~ ribbon_in [:: 2] [:: 4; 2].
Proof. by []. Qed.
Goal ribbon_in [:: 2] [:: 3].
Proof. by []. Qed.
Goal ribbon_in [:: 2] [:: 4; 3].
Proof. by []. Qed.
Goal ribbon_in [:: 3; 2] [:: 4; 4].
Proof. by []. Qed.
Goal ~~ ribbon_in [:: 3; 2] [:: 4; 4; 1].
Proof. by []. Qed.
Goal ~~ ribbon_in [:: 3; 2] [:: 4; 4; 2].
Proof. by []. Qed.
Goal ribbon_in [:: 3; 2; 2] [:: 4; 4; 2].
Proof. by []. Qed.
Goal ~~ ribbon_in [:: 2; 2] [:: 4; 4].
Proof. by []. Qed.

Goal ribbon [:: 2] [:: 3].
Proof. by []. Qed.
Goal ribbon [:: 2; 2] [:: 3; 2].
Proof. by []. Qed.
Goal ribbon [:: 2; 2] [:: 3; 3].
Proof. by []. Qed.
Goal ribbon [:: 5; 3; 2; 2] [:: 5; 4; 4; 2].
Proof. by []. Qed.
Goal ~~ ribbon [:: 5; 3; 2; 2] [:: 5; 4; 4; 2; 1].
Proof. by []. Qed.
Goal ~~ ribbon [::] [::].
Proof. by []. Qed.
Goal ~~ ribbon [:: 2; 1] [:: 2; 1].
Proof. by []. Qed.
*)
End Test.

Lemma ribbon_in_impl inn out : ribbon_in inn out -> ribbon inn out.
Proof. by case: inn => /= [->| _ _ ->] //. Qed.

Lemma ribbon_consK inn0 inn out0 out :
  ribbon (inn0 :: inn) (out0 :: out) -> (inn == out) || ribbon inn out.
Proof.
by move=>/=/orP[/andP[_ /orP[-> //| /andP[_ /ribbon_in_impl->]]] | /andP[_ ->]];
  rewrite orbT.
Qed.
Lemma ribbonE inn0 inn out0 out :
  inn0 < out0 ->
  ribbon (inn0 :: inn) (out0 :: out) = ribbon_in (inn0 :: inn) (out0 :: out).
Proof. by rewrite /= => H; rewrite H /= (ltn_eqF H) /= orbF. Qed.

Lemma ribbon_in_noneq inner outer : ribbon_in inner outer -> inner != outer.
Proof.
case: inner outer => [| inn0 inn] [| out0 out] //=.
by rewrite eqseq_cons => /andP[/ltn_eqF ->].
Qed.
Lemma ribbon_noneq inner outer : ribbon inner outer -> inner != outer.
Proof.
elim: inner outer => [| inn0 inn IHinn] [| out0 out] //=.
by rewrite eqseq_cons => /orP [/andP[/ltn_eqF ->] // | /andP [-> /IHinn]].
Qed.

Lemma ribbon_in_included inner outer :
  ribbon_in inner outer -> included inner outer.
Proof.
elim: inner outer => [| inn0 inn IHinn] [| out0 out] //=.
move=> /andP [/ltnW ->] /orP [/eqP -> /=| /andP [_/IHinn//]].
exact: included_refl.
Qed.
Lemma ribbon_included inner outer :
  ribbon inner outer -> included inner outer.
Proof.
elim: inner outer => [| inn0 inn IHinn] [| out0 out] //=.
move=> /orP[/andP [lt0] | /andP[/eqP-> /IHinn->//]]; last by rewrite andbT.
move=> /orP[/eqP->|]; first by rewrite (ltnW lt0) included_refl.
by move=> /andP [_ /ribbon_in_included ->]; rewrite (ltnW lt0).
Qed.

(*
Fixpoint add_ribbon sh nbox pos :=
  if pos is i.+1 then
    if nbox + nth 0 sh i.+1 <= nth 0 sh i then
      Some ((set_nth 0 sh i.+1 (nbox + nth 0 sh i.+1)), i.+1)
    else if nbox + nth 0 sh i.+1 == (nth 0 sh i).+1 then
           None
         else
           let newsh := set_nth 0 sh i.+1 (nth 0 sh i).+1 in
           add_ribbon newsh (nbox + (nth 0 sh i.+1) - (nth 0 sh i).+1) i
  else
    Some ((set_nth 0 sh 0 (nbox + nth 0 sh 0)), 0).
 *)

(** Return a triple (shape, height, remaining ) *)
Definition add_col base s0 shres h rem :=
  if rem == 0 then Some (s0 :: shres, h, 0)
  else if rem == base.+1 - s0 then None
       else let: p := minn rem (base.+1 - s0) in
            Some (s0 + p :: shres, h.+1, rem - p).
Fixpoint add_ribbon_base base sh nbox pos :=
  if sh is s0 :: s' then
    if pos is i.+1 then
      if add_ribbon_base s0 s' nbox i is Some (shres, h, rem) then
        add_col base s0 shres h rem
      else None
    else add_col base s0 s' 0 nbox
  else if nbox <= pos then None
       else add_col base 0 (nseq pos 1) pos (nbox - pos).

Definition add_ribbon sh nbox pos :=
  omap fst (* assert snd == 0 *) (add_ribbon_base (nbox + sumn sh) sh nbox pos).

Section Tests.
(*
(** Tests :
[
sage: s[2, 2] * p[1]
s[2, 2, 1] + s[3, 2]
]
 *****)
Goal pmap (add_ribbon [:: 2; 2] 1) (iota 0 10) =
  [:: ([:: 3; 2], 1); ([:: 2; 2; 1], 1)].
Proof. by []. Qed.

(** Tests :
[
sage: s[2, 2] * p[2]
-s[2, 2, 1, 1] + s[2, 2, 2] - s[3, 3] + s[4, 2]
]
 *****)
Goal pmap (add_ribbon [:: 2; 2] 2) (iota 0 10) =
  [:: ([:: 4; 2], 1); ([:: 3; 3], 2); ([:: 2; 2; 2], 1); ([:: 2; 2; 1; 1], 2)].
Proof. by []. Qed.

(** Tests :
[
sage: s[3, 2, 1, 1] * p[4]
-s[3, 2, 1, 1, 1, 1, 1, 1] + s[3, 2, 2, 2, 2] + s[3, 3, 3, 2] - s[5, 4, 1, 1]
  + s[7, 2, 1, 1]
]
*****)
Goal pmap (add_ribbon [:: 3; 2; 1; 1] 4) (iota 0 10) =
  [:: ([:: 7; 2; 1; 1], 1);
      ([:: 5; 4; 1; 1], 2);
      ([:: 3; 3; 3; 2], 3);
      ([:: 3; 2; 2; 2; 2], 3);
      ([:: 3; 2; 1; 1; 1; 1; 1; 1], 4)].
Proof. by []. Qed.

(** Tests :
[
sage: s[2, 2] * p[5]
s[2, 2, 1, 1, 1, 1, 1] - s[2, 2, 2, 1, 1, 1] + s[3, 3, 3] - s[6, 3] + s[7, 2]
]
*****)
Goal pmap (add_ribbon [:: 2; 2] 5) (iota 0 8) =
  [:: ([:: 7; 2], 1); ([:: 6; 3], 2); ([:: 3; 3; 3], 3);
      ([:: 2; 2; 2; 1; 1; 1], 4); ([:: 2; 2; 1; 1; 1; 1; 1], 5)].
Proof. by []. Qed.

(** Tests :
[
sage: s[2, 2, 1] * p[5]
s[2, 2, 1, 1, 1, 1, 1, 1] - s[2, 2, 2, 2, 1, 1] + s[4, 3, 3] - s[6, 3, 1] + s[7, 2, 1]
]
*****)
Goal pmap (add_ribbon [:: 2; 2; 1] 5) (iota 0 8) =
  [:: ([:: 7; 2; 1], 1); ([:: 6; 3; 1], 2); ([:: 4; 3; 3], 3);
      ([:: 2; 2; 2; 2; 1; 1], 4); ([:: 2; 2; 1; 1; 1; 1; 1; 1], 5)].
Proof. by []. Qed.

(** Tests :
[
s[5, 5, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1] - s[5, 5, 2, 2, 2, 2, 1, 1, 1] + s[5, 5, 3, 3, 2, 2, 1] - s[5, 5, 4, 3, 2, 2] + s[7, 6, 6, 1, 1] - s[11, 6, 2, 1, 1] + s[12, 5, 2, 1, 1]
]
*****)
Goal pmap (add_ribbon [:: 5; 5; 2; 1; 1] 7) (iota 0 15) =
  [:: ([:: 12; 5; 2; 1; 1], 1); ([:: 11; 6; 2; 1; 1], 2);
     ([:: 7; 6; 6; 1; 1], 3); ([:: 5; 5; 4; 3; 2; 2], 4);
      ([:: 5; 5; 3; 3; 2; 2; 1], 5); ([:: 5; 5; 2; 2; 2; 2; 1; 1; 1], 6);
      ([:: 5; 5; 2; 1; 1; 1; 1; 1; 1; 1; 1; 1], 7)].
Proof. by []. Qed.

Goal let sh := [:: 2; 2] in
     all (fun p => ribbon sh p.1) (pmap (add_ribbon sh 1) (iota 0 8)).
Proof. by []. Qed.
Goal let sh := [:: 2; 2] in
     all (fun p => ribbon sh p.1) (pmap (add_ribbon sh 5) (iota 0 8)).
Proof. by []. Qed.
Goal let sh := [:: 2; 2; 1] in
     all (fun p => ribbon sh p.1) (pmap (add_ribbon sh 5) (iota 0 8)).
Proof. by []. Qed.
Goal let sh := [:: 5; 5; 2; 1; 1] in
     all (fun p => ribbon sh p.1) (pmap (add_ribbon sh 7) (iota 0 15)).
Proof. by []. Qed.
*)
End Tests.


Section SpecBase.

Variables (base : nat) (sh : seq nat).
Hypothesis partsh : is_part (base :: sh).
Variable  nbox pos : nat.
Variables (res : seq nat) (hgt rem : nat).
Hypothesis Hret : add_ribbon_base base sh nbox.+1 pos = Some (res, hgt, rem).

Lemma rem_add_ribbon_base_lt : rem <= nbox.
Proof.
have add_col_rem bs s0 rm r :
    s0 <= bs -> add_col bs s0 _ _ rm = Some (_, _, r) -> r <= rm.-1.
  rewrite /add_col /= => lts0bs; case: rm => //= [[_ _ <-]// | rm].
  case: eqP => // _ [_ _ <-].
  by rewrite (subSn lts0bs) minSS subSS leq_subr.
move: partsh => /= /andP [Hbase Hpart].
elim: sh Hpart base Hbase nbox pos res hgt rem Hret
  => /= [_|s0 s' IHs /andP [{}/IHs H{}/H Hrec]] bs lts0bs l p rs h rm.
  case: (ltnP l p) => // lepl.
  rewrite subSn //= => /add_col_rem-/(_ (ltnW lts0bs))/leq_trans; apply.
  exact: leq_subr.
case: p => [/add_col_rem -> // | p].
move/(_ l p): Hrec; case: add_ribbon_base=> // [[[shres hres] remres]].
move=> /(_ _ _ _ erefl) H /add_col_rem-/(_ lts0bs)/leq_trans; apply.
exact: (leq_trans (leq_pred _) H).
Qed.

Lemma add_col_part bs s0 s h rm rs hs rms :
  s0 <= bs -> is_part (s0 + (rm != 0) :: s) ->
  add_col bs s0 s h rm = Some (rs, hs , rms) ->
  is_part (bs + (rms != 0) :: rs).
Proof.
rewrite /add_col /= => Hlt /andP [Hhead Hpart].
case: rm Hhead => /= [|rm]; rewrite ?addn0 ?addn1 => Hhead.
  by move=> [<- _ <-] /=; rewrite addn0 Hlt Hpart Hhead.
rewrite subSn // eqSS; case: (altP (_ =P _)) => //.
rewrite /minn ltnS neq_ltn => /orP [] ibs [<- _ <-{rs hs rms}] /=.
  rewrite ibs /= subnn addn0 -leq_subRL //= ibs Hpart andbT /=.
  by rewrite -addSnnS (leq_trans Hhead (leq_addr _ _)).
rewrite (ltnNge rm _) (ltnW ibs) /= Hpart andbT.
rewrite addnS subnKC // -lt0n subn_gt0 !ltnS ibs addn1 ltnS leqnn /=.
by rewrite (leq_trans Hhead).
Qed.

Lemma is_part_add_ribbon_base : is_part (base + (rem != 0) :: res).
Proof.
move: partsh => /= /andP [Hbase Hpart].
elim: sh Hpart base Hbase nbox pos res hgt rem Hret
  => /= [_|s0 s' IHs /andP[Hhead Hpart]] bs lts0bs l p rs h rm.
  case: (ltnP l p) => // lepl /(add_col_part (ltnW lts0bs)); apply.
  by rewrite add0n subSn //= is_part_nseq1 andbT; case p.
case: p => [/(add_col_part lts0bs)/= | p].
  by apply; rewrite Hpart andbT addn1 (leq_trans Hhead).
case: add_ribbon_base (IHs Hpart s0 Hhead l p) => {IHs}//.
move=> [[shres hres] remres] /(_ _ _ _ erefl) /andP[headres Hpartres].
move/add_col_part => /(_ lts0bs) /=; apply.
by rewrite headres Hpartres.
Qed.

Lemma add_col_eq bs s0 s h rm rs hs rms :
  s0 <= bs ->
  add_col bs s0 s h rm = Some (rs, hs, rms) ->
  sumn rs + rms = sumn (s0 :: s) + rm.
Proof.
rewrite /add_col /=.
case: rm => /= [_ [<- _ <- //] | rm lts0bs].
rewrite subSn // eqSS; case: (altP (_ =P _)) => //.
rewrite /minn ltnS neq_ltn => /orP [] ibs [<- _ <-{rs hs rms}] /=.
  by rewrite ibs /= subnn addn0 -!addnA [rm.+1 + _]addnC.
rewrite (ltnNge rm _) (ltnW ibs) /=.
rewrite addnS subnKC // subSS !(addSn, addnS) addnC addnA.
rewrite subnBA // subnK; first by rewrite -!addnA addnC addnA.
by rewrite addnC -leq_subLR ltnW.
Qed.

Lemma sumn_add_ribbon_base : sumn res + rem = nbox.+1 + sumn sh.
Proof.
move: partsh => /= /andP [Hbase Hpart].
elim: sh Hpart base Hbase nbox pos res hgt rem Hret
    => /= [_|s0 s' IHs /andP[Hhead Hpart]] bs lts0bs l p rs h rm.
  case: (ltnP l p) => // lepl /(add_col_eq (ltnW lts0bs)) ->.
  by rewrite /= addn0 add0n sumn_nseq mul1n subnKC // (leq_trans lepl).
case: p => [/(add_col_eq lts0bs)/= ->| p].
  by rewrite addnC addnA.
case: add_ribbon_base (IHs Hpart s0 Hhead l p) => {IHs}//.
move=> [[shres hres] remres] /(_ _ _ _ erefl) Heq /(add_col_eq lts0bs) -> /=.
by rewrite -addnA {}Heq !addnA [s0 + _]addnC.
Qed.

Lemma add_ribbon_base_neq : sh != res.
Proof.
apply/negP=> /eqP Heq; move: sumn_add_ribbon_base rem_add_ribbon_base_lt.
rewrite {}Heq addnC => /eqP; rewrite eqn_add2r => /eqP ->.
by rewrite ltnn.
Qed.

Lemma add_col_ribbon_in bs inn s0 s h rm rs hs rms :
  s0 <= bs ->
  ribbon_in (s0 :: inn) (s0.+1 :: s) ->
  add_col bs s0 s h rm.+1 = Some (rs, hs, rms.+1) ->
  ribbon_in (bs :: s0 :: inn) (bs.+1 :: rs) && (head 0 rs != 0).
Proof.
rewrite /add_col /= !ltnSn /= => lts0bs Hrib.
rewrite subSn // eqSS; case: (altP (_ =P _)) => // Heq [<- _ /eqP].
move: Heq; rewrite minSS subSS /minn.
rewrite neq_ltn => /orP [->| Hbs]; first by rewrite subnn.
rewrite (ltnNge rm _) (ltnW Hbs) /= => _.
by rewrite Hrib /= andbT addnS subnKC // eqxx ltnS lts0bs orbT.
Qed.
Lemma add_ribbon_base_inP :
  rem != 0 -> ribbon_in (base :: sh) (base.+1 :: res).
Proof.
case: rem Hret => // rm Hrm _.
move: partsh => /= /andP [Hbase Hpart].
elim: sh Hpart base Hbase nbox pos res hgt rm Hrm
  => [_ /= |s0 s' IHs Hpart] bs lts0bs l p rs h rm.
  case: (ltnP l p) => // lepl.
  rewrite (subSn lepl) => /(add_col_ribbon_in (ltnW lts0bs))-/(_ [::]) H.
  have {}/H /= : ribbon_in [:: 0] (1 :: nseq p 1).
    by rewrite /=; case p => //= [[|]].
  rewrite !ltnSn /= => /andP [].
  case: rs => //= r0 rs /orP [/eqP[<-]//|].
  by move=> /and3P[/eqP ->] _ /orP [/eqP <- _ /=| /andP[/eqP ->]]; rewrite eqxx.
case: p => [/(add_col_ribbon_in lts0bs)-/(_ s') | p /=] H.
  by have /H/andP [] : ribbon_in (s0 :: s') (s0.+1 :: s')
    by rewrite /ribbon /= ltnSn eqxx.
move: Hpart; rewrite ltnSn /= => /andP [Hhead Hpart].
case: add_ribbon_base (IHs Hpart s0 Hhead l p) H => {IHs}//.
move=> [[shres hres] [|remres]] // /(_ _ _ _ erefl) Hrib.
move/add_col_ribbon_in => /(_ s' lts0bs) H.
have {Hrib}/H /= : ribbon_in (s0 :: s') (s0.+1 :: shres) by move: Hrib => /= ->.
by rewrite ltnSn /= => /andP [-> _].
Qed.

Lemma add_ribbon_base_height : hgt = count (ltn 0) (res / sh).
Proof.
move: partsh => /= /andP [Hbase Hpart].
elim: sh Hpart base Hbase nbox pos res hgt rem Hret
    => /= [_|s0 s' IHs /andP[Hhead Hpart]] bs lts0bs l p rs h rm.
  case: (ltnP l p) => // lepl.
  rewrite /add_col; case: eqP => [_ [<- <- _] | _] /=.
    by rewrite add0n count_nseq /= mul1n.
  case: eqP => // _ [<- <- _] /=.
  by rewrite add0n count_nseq /= mul1n subn0 subSn // minSS /= add1n.
case: p => [|p].
  rewrite /add_col /=; case: eqP => // _ [<- <- _] /=.
  rewrite addKn subSn // minSS /=.
  suff -> : count (ltn 0) (s' / s') = 0 by rewrite addn0.
  elim: s' {IHs Hhead Hpart} => //= s1 s ->.
  by rewrite subnn add0n.
case: add_ribbon_base (IHs Hpart s0 Hhead l p) => {IHs}//.
move=> [[shres hres] remres] // /(_ _ _ _ erefl) Hres.
rewrite /add_col /=; case: (altP (_ =P _)) => [_ [<- <- _] | Hrem] /=.
  by rewrite subnn add0n.
case: eqP => // _ [<- <- _] /=; rewrite -{}Hres addKn subSn //.
by case: remres Hrem => // r _; rewrite minSS /= add1n.
Qed.

End SpecBase.


Section Assert.

Variables (base : nat) (sh : seq nat).
Hypothesis partsh : is_part (base :: sh).
Variable  nbox pos : nat.
Variables (res : seq nat) (hgt rem : nat).
Hypothesis Hret : add_ribbon_base base sh nbox.+1 pos = Some (res, hgt, rem).

Lemma add_ribbon_base_rem0 : base = nbox.+1 + sumn sh -> rem = 0.
Proof.
have add_col_eq0 bs s0 rm r :
    s0 <= bs -> rm <= (bs - s0) ->
    add_col bs s0 _ _ rm = Some (_, _ , r) -> r = 0.
  rewrite /add_col /= => lts0bs; case: rm => //= [_ [_ _ <-]// | rm ltrm].
  case: eqP => // _ [_ _ <-].
  rewrite (subSn lts0bs) minSS subSS.
  by move: ltrm => /ltnW/minn_idPl ->; rewrite subnn.
move=> Heq.
move: partsh => /= /andP [Hbase Hpart].
case: sh Hpart Heq Hbase Hret => /= [_|s0 s' Hpart -> lts0bs]/=.
  case: (ltnP nbox pos) => // lelpos -> _ /add_col_eq0; apply => //.
  by rewrite subn0 addn0 leq_subr.
case: pos => [/add_col_eq0-/(_ lts0bs)/= -> //| p].
  by rewrite -addnBA ?leq_addr.
case Hrib: add_ribbon_base => // [[[rs h] rm]].
move/add_col_eq0 => /(_ lts0bs) -> //.
have := rem_add_ribbon_base_lt Hpart Hrib => /leq_trans; apply.
by rewrite -addnBA ?leq_addr // addKn addSnnS leq_addr.
Qed.

Lemma add_ribbon_baseP : ribbon sh res.
Proof.
case: (altP (rem =P 0)) => [Hrem|]; first last.
  move/(add_ribbon_base_inP partsh Hret)/ribbon_in_impl/ribbon_consK.
  by have:= (add_ribbon_base_neq partsh Hret) => /negbTE ->.
move: Hret; rewrite {}Hrem => Hret0.
move: partsh => /= /andP [Hbase Hpart].
elim: sh Hpart base Hbase nbox pos res hgt Hret0
  => /= [ _ |s0 s' IHs Hpart] bs lts0bs l p rs h.
  case: (ltnP l p) => // lepl; rewrite /add_col /=.
  rewrite subn_eq0 ltnNge lepl /= subn0.
  case: (altP (_ =P _)) => // _; rewrite add0n => [][<- _ _].
  by case p.
case: p => [|p].
  rewrite /add_col /=; case: (altP (_ =P _)) => // _ [<- _ _].
  by rewrite (subSn lts0bs) minSS addnS ltnS leq_addr eqxx.
move tr : (add_ribbon_base s0 s' l.+1 p) => [] //.
move: tr => [[shres hres] [|remres]].
  move: Hpart => /andP [{}/IHs H{}/H H{}/H Hrib].
  by rewrite /add_col /= => [] [<- _]; rewrite eqxx Hrib /= orbT.
move=> /(add_ribbon_base_inP Hpart)/(_ is_true_true) /= /andP [_] Hrib.
rewrite /add_col /=; case: (altP (_ =P _)) => // Heq [<-{rs} _{h hres}] _.
by rewrite (subSn lts0bs) minSS addnS ltnS leq_addr Hrib.
Qed.

Lemma included_add_ribbon_base : included sh res.
Proof. exact: ribbon_included (add_ribbon_baseP). Qed.

End Assert.


Section Spec.

Variables (sh : seq nat).
Hypothesis (partsh : is_part sh).
Variable  (nbox pos : nat).
Variables (res : seq nat) (hgt : nat).
Hypothesis (Hret : add_ribbon sh nbox.+1 pos = Some (res, hgt)).

Local Lemma is_part_base : is_part (nbox.+1 + sumn sh :: sh).
Proof.
rewrite /= partsh andbT addSnnS; apply: (leq_trans _ (leq_addl _ _)).
by case: sh => //= s0 s; rewrite -addnS leq_addr.
Qed.

Lemma is_part_of_ribbon_base : is_part_of_n (nbox.+1 + sumn sh) res.
Proof.
move: Hret; rewrite /add_ribbon.
case Hrib: add_ribbon_base => // [[[x y] z]] [Hx Hy]; subst x y.
rewrite /is_part_of_n /=; apply/andP; split.
  have:= sumn_add_ribbon_base is_part_base Hrib.
  by rewrite (add_ribbon_base_rem0 is_part_base Hrib erefl) addn0 => ->.
by have /= /andP [] := is_part_add_ribbon_base is_part_base Hrib.
Qed.

Lemma add_ribbonP : ribbon sh res.
Proof.
move: Hret; rewrite /add_ribbon.
case Hrib: add_ribbon_base => // [[[x y] rem]] [Hx Hy]; subst x y.
exact: (add_ribbon_baseP is_part_base Hrib).
Qed.

Lemma included_add_ribbon : included sh res.
Proof. exact: ribbon_included (add_ribbonP). Qed.

Lemma add_ribbon_height : hgt = count (ltn 0) (res / sh).
Proof.
move: Hret; rewrite /add_ribbon.
case Hrib: add_ribbon_base => // [[[x y] rem]] [Hx Hy]; subst x y.
exact: (add_ribbon_base_height is_part_base Hrib).
Qed.

End Spec.

Lemma ribbon_in_exP inner outer :
  is_part inner -> is_part outer -> ribbon_in inner outer ->
  exists pos, forall nbox, (* base = (head 0 outer).-1 *)
      nbox.+1 + sumn inner > sumn outer ->
      add_ribbon_base (head 0 outer).-1 inner nbox.+1 pos =
      Some (outer, pos.+1, nbox.+1 + sumn inner - sumn outer).
Proof.
elim: inner outer => [|inn0 inn IHinn] [|out0 out]//.
  move=> _ /= /andP[leout0 /part_nseq1P] H{}/H.
  move: (sumn out) => arm => Hout; subst out.
  have {leout0} : 1 <= out0 by move: leout0; case arm.
  case: out0 => // out0 _; exists arm => nbox.
  rewrite addn0 addSn ltnS => Harm.
  have learmnbox : arm <= nbox by exact: leq_trans (leq_addl _ _) (ltnW Harm).
  rewrite -addnC -ltn_subRL in Harm.
  rewrite ltnNge learmnbox /= subSS subSn //.
  rewrite /add_col /= subn0 eqSS (gtn_eqF Harm) add0n minSS subSS.
  move/ltnW/minn_idPr: Harm => ->.
  by rewrite addnC subnDA.
move=> /[swap]/[dup]/part_head_non0.
case: out0 => //= out0 _ /andP[headout partout] /andP[headinn partinn].
rewrite ltnS => /andP [le0] /orP [/eqP Heq | /andP[/eqP Hout Hrib]].
  rewrite {partinn inn IHinn}Heq in headinn *.
  exists 0 => nbox; nat_norm; rewrite addnA ltnS ltn_add2r => Hlt.
  rewrite /add_col //= subSn // eqSS.
  rewrite addnC -ltn_subLR // in Hlt.
  rewrite (gtn_eqF Hlt) minSS !subSS.
  move/ltnW/minn_idPr: Hlt => ->.
  by rewrite addnS subnKC // subnDr subnBA.
move/(_ _ partinn partout Hrib) : IHinn => [pos Hpos].
exists pos.+1 => nbox.
rewrite !addSn ltnS addnA addnAC => Hlt.
have {}Hlt1 : sumn out < nbox.+1 + sumn inn.
  move: Hlt; rewrite addSn ltnS [_ + inn0]addnC.
  rewrite -ltn_subLR; last exact: (leq_trans le0 (leq_addr _ _)).
  move/(leq_trans _); apply; apply: (leq_trans _ (leqnSn _)).
  by rewrite addnC -addnBA // leq_addr.
move/(_ _ Hlt1) : Hpos; rewrite {}Hout => ->.
rewrite /add_col /= subn_eq0 leqNgt Hlt1 /=.
have Hlt2 : nbox.+1 + sumn inn - sumn out > out0.+1 - inn0.
  rewrite addSn !subSn // ltnS.
  by rewrite ltn_subLR // addnBA // ltn_subRL addnC [inn0 + _]addnC.
rewrite (gtn_eqF Hlt2).
move/ltnW/minn_idPr: Hlt2 => ->.
have le01 := (leq_trans le0 (leqnSn _)).
rewrite subnKC //; congr (Some (_ :: _, _, _)).
rewrite subSS subnBA // addSn subSn // addSn subSS.
by rewrite [out0 + _]addnC subnDA addnBAC.
Qed.

Lemma ribbon_exP inner outer :
  is_part inner -> is_part outer -> ribbon inner outer ->
  exists pos h, forall nbox base,
      nbox.+1 + sumn inner = sumn outer ->
      base >= head 0 outer ->
      add_ribbon_base base inner nbox.+1 pos = Some (outer, h, 0).
Proof.
elim: inner outer => [|inn0 inn IHinn] [|out0 out]//.
  rewrite /= orbF=> _ /= /andP[leout0 /part_nseq1P] H{}/H.
  move: (sumn out) => arm => Hout; subst out.
  have {leout0} : 1 <= out0 by move: leout0; case arm.
  case: out0 => // out0 _; exists arm; exists arm.+1 => nbox base.
  rewrite addn0 addSn => [] [->] Hout0.
  rewrite ltnNge leq_addl /= subSn ?leq_addl // addnK.
  rewrite /add_col /= subn0 eqSS (ltn_eqF Hout0) add0n minSS subSS.
  move/ltnW/minn_idPl: Hout0 => ->.
  by rewrite subnn.
move=> /[swap]/[dup]/part_head_non0.
case: out0 => //= out0 _ /andP[headout partout] /andP[headinn partinn].
rewrite ltnS => /orP [/andP[le0] /orP [/eqP Heq |]| ].
  rewrite {partinn inn IHinn}Heq in headinn *.
  exists 0; exists 1 => nbox base.
  rewrite /add_col !addSn addnA => [[]]/eqP.
  rewrite eqn_add2r => /eqP eqout0 ltout0 /=.
  have ltinn0 := leq_ltn_trans le0 ltout0.
  rewrite subSn ?(ltnW ltinn0) // eqSS.
  rewrite -(eqn_add2r inn0) subnK ?(ltnW ltinn0) // eqout0 (ltn_eqF ltout0).
  rewrite minSS subSS.
  suff /minn_idPl-> : nbox <= (base - inn0) by rewrite addnS addnC eqout0 subnn.
  by apply: ltnW; rewrite ltn_subRL addnC eqout0.
move => {IHinn} /andP[/eqP Hout Hrib].
  have [pos Hrec] := ribbon_in_exP partinn partout Hrib.
  exists pos.+1; exists pos.+2 => nbox base Heq Hbase.
  have Hlt : sumn out < nbox.+1 + sumn inn.
    by rewrite -(ltn_add2l out0.+1) -Heq addnCA ltn_add2r ltnS.
  move/(_ _ Hlt): Hrec; rewrite Hout /= => ->.
  rewrite /add_col subn_eq0 leqNgt Hlt /=.
  have Hlt1 : nbox.+1 + sumn inn - sumn out < base.+1 - inn0.
    rewrite -(ltn_add2l (inn0 + sumn out)) -addnA subnKC ?(ltnW Hlt) //.
    rewrite addnA [inn0 + _]addnC -addnA Heq.
    rewrite ![_ + sumn out]addnC -addnA ltn_add2l subnKC //.
    exact: leq_trans le0 (leq_trans (ltnW Hbase) _).
  rewrite (ltn_eqF Hlt1) (minn_idPl (ltnW Hlt1)) subnn.
  congr (Some (_ :: _, _, _)).
  by rewrite addnBA ?(ltnW Hlt) // addnA [inn0 + _]addnC -addnA Heq addnK.
move=> /andP[/eqP eq0 Hrib].
move/(_ _ partinn partout Hrib) : IHinn => [pos] [h] Hrec.
rewrite -{out0}eq0 in headout *.
exists pos.+1; exists h => nbox base.
rewrite ![inn0 + _]addnC addnA => /eqP; rewrite eqn_add2r => /eqP Heq Hbase.
move/(_ _ _ Heq) : Hrec.
suff -> : head 0 out = head 1 out by move=> /(_ _ headout) ->.
have := sumn_included (ribbon_included Hrib).
by move: Heq; case out.
Qed.

Lemma ribbonP inner outer :
  is_part inner -> is_part outer ->
  reflect
    (exists nbox pos h, add_ribbon inner nbox.+1 pos = Some (outer, h))
    (ribbon inner outer).
Proof.
move=> partinn partout.
apply (iffP idP) => [Hrib | [pos][nbox][h] /add_ribbonP -> //].
have ltsum : sumn inner < sumn outer.
  rewrite ltn_neqAle (sumn_included (ribbon_included Hrib)) andbT.
  have:= ribbon_noneq Hrib; apply contra => /eqP.
  by move/(included_sumnE partout (ribbon_included Hrib)) ->.
have:= ribbon_exP partinn partout Hrib => [][pos][h].
case Hsout : (sumn outer) ltsum => [//|sout] ltsum.
rewrite /add_ribbon =>/(_ (sout - sumn inner)).
rewrite addSn subnK // => /(_ _ erefl) Hres.
have {}/Hres Hres : head 0 outer <= sout.+1.
  rewrite -ltnS -Hsout; move: Hsout; case outer => //= s0 s _.
  by rewrite ltnS leq_addr.
exists (sout - sumn inner); exists pos; exists h.
by rewrite -{1}subSn // subnK ?(ltnW ltsum) // {}Hres.
Qed.

