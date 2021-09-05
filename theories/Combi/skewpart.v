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

- [hb_strip inn out] == [out/inn] is an horizontal border strip.
- [vb_strip inn out] == [out/inn] is a vertical border strip.

Ribbon border strip:

- [add_ribbon sh nbox pos] == tries to add a ribbon with nbox ending at row
               [pos] to the shape [sh]. Returns [Some (sh, hgt)] where [sh] is
               the outer shape of the result and [hgt] its height on success,
               or [error] if not
- [ribbon_from inn out] == [out/inn] is a ribbon shape starting at row 0
- [ribbon inn out] == [out/inn] is a ribbon shape

******)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple finfun finset bigop path.

Require Import tools sorted partition.

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

Lemma vb_strip_diffP inner outer :
  is_part inner -> is_part outer ->
  reflect
    (included inner outer /\ all (geq 1) (outer / inner))
    (vb_strip inner outer).
Proof.
move=> Hinn Hout; apply (iffP (vb_stripP Hinn Hout)) => [H | [Hincl H] i].
- split; first by apply/part_includedP => // i; have /andP[]:= H i.
  apply/(all_nthP 0) => i _ /=; rewrite nth_diff_shape.
  by move/(_ i): H => /andP [_]; rewrite leq_subLR addn1.
- have := Hincl => /includedP [_ /(_ i) -> /=].
  case: (ltnP i (size outer)) => [| {H} Hsz].
    move: H => /(all_nthP 0)/(_ i) /=.
    by rewrite size_diff_shape nth_diff_shape leq_subLR addn1 => H{}/H.
  by rewrite nth_default.
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

Fixpoint ribbon_from inner outer :=
  if inner is inn0 :: inn then
    if outer is out0 :: out then
      (inn0 < out0) &&
      ((out == inn) || ((head 0 out == inn0.+1) && (ribbon_from inn out)))
    else false
  else if outer is out0 :: out then head 0 out <= 1
       else false.
Fixpoint ribbon inner outer :=
  ribbon_from inner outer ||
  if (inner, outer) is (inn0 :: inn, out0 :: out) then
    (out0 == inn0) && (ribbon inn out)
  else false.

Definition ribbon_on start stop inner outer :=
  [/\ forall i, i > stop -> nth 0 outer i = nth 0 inner i,
     forall i, start <= i < stop -> nth 0 outer i.+1 = (nth 0 inner i).+1,
     nth 0 inner start < nth 0 outer start &
     forall i, i < start -> nth 0 outer i = nth 0 inner i].

Lemma ribbon_on_start_stop start stop inner outer :
  ribbon_on start stop inner outer -> start <= stop.
Proof.
move=> [Hsi _ Hs _]; rewrite leqNgt; apply/negP => /Hsi Habs.
by rewrite Habs ltnn in Hs.
Qed.

Lemma ribbon_on_start_le start stop inner outer :
  is_part outer -> ribbon_on start stop inner outer -> start <= size inner.
Proof.
case: start=> [//|start] Hout [_ _ Hs His].
rewrite leqNgt; apply/negP => Habs.
move/(_ _ Habs) : His; rewrite (nth_default _ (leqnn _)) => Hszinn.
case: (ltnP (size inner) (size outer)) => Hsz.
  by have := nth_part_non0 Hout Hsz; rewrite Hszinn.
move: Hs; rewrite !nth_default //; apply ltnW => //.
exact: (leq_ltn_trans Hsz).
Qed.

Lemma ribbon_on_stop_lt start stop inner outer :
  is_part outer -> ribbon_on start stop inner outer -> stop < size outer.
Proof.
case: outer => [_ |out0 out Hpart] [Hsi Hsis Hs His].
  by rewrite nth_nil in Hs.
rewrite ltnNge; apply/negP => /= Hos.
case: (leqP start (size out)) => Hso.
  have /Hsis : start <= size out < stop by rewrite Hso Hos.
  by rewrite nth_default.
by rewrite [X in _ < X]nth_default in Hs.
Qed.

Lemma ribbon_onSS start stop inn0 inn out0 out :
  ribbon_on start.+1 stop.+1 (inn0 :: inn) (out0 :: out)
  <-> inn0 == out0 /\ ribbon_on start stop inn out.
Proof.
rewrite /ribbon_on; split => [ |[/eqP ->]] [Hsi Hsis Hs His].
- split; first exact/eqP/esym/(His _ (ltn0Sn _)).
  split=> // i Hi; [exact: (Hsi i.+1) | exact: (Hsis i.+1) | exact: (His i.+1)].
- split=> //-[|i] Hi//=; [exact: Hsi | exact: Hsis | exact: His].
Qed.

Lemma ribbon_on_inj inner outer start1 stop1 start2 stop2 :
  is_part inner ->
  ribbon_on start1 stop1 inner outer ->
  ribbon_on start2 stop2 inner outer ->
  (start1, stop1) = (start2, stop2).
Proof.
move=> partinn H1 H2; congr (_, _).
- wlog leq12: start1 start2 stop1 stop2 H1 H2 / start1 <= start2.
    move=> Hwlog; case: (leqP start1 start2) => [H12 | /ltnW H21].
    + exact/(Hwlog _ _ _ _ H1 H2).
    + exact/esym/(Hwlog _ _ _ _ H2 H1).
  apply anti_leq; rewrite {}leq12 /=.
  move: H1 H2 => [_ _ Hs1 _] [_ _ _ His2].
  case: leqP => // /His2 Heq.
  by rewrite Heq ltnn in Hs1.
- wlog leq12: start1 start2 stop1 stop2 H1 H2 / stop1 <= stop2.
    move=> Hwlog; case: (leqP stop1 stop2) => [H12 | /ltnW H21].
    + exact/(Hwlog _ _ _ _ H1 H2).
    + exact/esym/(Hwlog _ _ _ _ H2 H1).
  apply anti_leq; rewrite {}leq12 /=.
  move: H1 => [Hsi1 _ _ _].
  case: leqP => // {start1 stop1}/Hsi1 => Heq.
  have:= ribbon_on_start_stop H2.
  rewrite leq_eqVlt => /orP [/eqP eqss| ltss].
  + by move: H2 => [_ _]; rewrite eqss Heq ltnn.
  + case: stop2 H2 Heq ltss => // stop2 [_ Hsis2 _ _] Heq /ltnSE less.
    have {}/Hsis2 : start2 <= stop2 < stop2.+1 by rewrite less ltnS /=.
    rewrite {}Heq => Habs.
    by move/is_partP : partinn => [_ /(_ stop2)]; rewrite Habs ltnn.
Qed.

Lemma ribbon_fromP inner outer :
  is_part inner -> is_part outer ->
  reflect (exists stop, ribbon_on 0 stop inner outer)
          (ribbon_from inner outer).
Proof.
rewrite /ribbon_on=> Hinn Hout; apply (iffP idP);
elim: inner Hinn outer Hout => [| inn0 inn IHinn] Hinn [|out0 out] Hout //=.
- move=> H; exists (size out) => /=.
  move/(part_nseq1P (is_part_consK Hout)) : H ->; rewrite size_nseq.
  split => //[i Hi | i Hi | ].
  + by rewrite nth_nil nth_default //= size_nseq.
  + by rewrite nth_nil nth_nseq Hi.
  + by move/part_head_non0 : Hout => /=; rewrite lt0n.
- move=> /andP [lt0 /orP [/eqP -> | /andP[/eqP Hhead Hrib]]]/=.
  + by exists 0; split=> //; case.
  + move: Hinn Hout => /=/andP[headinn Hinn] /=/andP[headout Hout].
    move/(_ Hinn _ Hout Hrib): IHinn => [stop [Hsi His H0 _]].
    by exists stop.+1; split=> []// [|i] Hi //=; [exact: Hsi| exact: His].
- by move=> [stop []].
- move=> [[|stop] [His Hsi _]].
    by have:= His 1 (ltnSn _); rewrite /= nth0 => ->.
  by have:= Hsi 0 (ltn0Sn _); rewrite /= nth0 => ->.
- by move=> [stop []].
- move=> [stop [Hsi His H0 _]]; rewrite H0 /=.
  case (altP (out =P inn)) => //= Hneq.
  move: Hinn Hout => /=/andP[headinn Hinn] /=/andP[headout Hout].
  case: stop => [|stop] in Hsi His.
    exfalso => {His}; move: Hneq; suff -> : out = inn by rewrite eqxx.
    by apply/eqP/part_eqP => // i; apply: Hsi i.+1 (ltn0Sn _).
  have /= <- := His 0 (ltn0Sn _); rewrite nth0 eqxx /=.
  apply: IHinn => //; exists stop; split => // [i Hi|i Hi|].
  + exact: (Hsi i.+1 Hi).
  + exact: (His i.+1 Hi).
  + have /= -> := His 0 (ltn0Sn _); rewrite nth0 ltnS.
    by move: headinn; case inn.
Qed.

Lemma ribbonP inner outer :
  is_part inner -> is_part outer ->
  reflect (exists start stop, ribbon_on start stop inner outer)
          (ribbon inner outer).
Proof.
elim: inner outer=> [/= outer | inn0 inn IHinn].
  rewrite orbF => Hinn Hout.
  apply: (equivP (@ribbon_fromP [::] outer Hinn Hout)).
  split => [[stop] H | [start] [stop] []]; first by exists 0; exists stop.
  case: start => [Hsi Hsis Hs _| start _ _ Hs His]; first last.
    exfalso; move/(_ 0 (ltn0Sn _)) : His => /= H0.
    by case: outer H0 Hout Hs => // out0 out +/part_head_non0 => /= ->.
  by exists stop.
case=> [/part_head_non0 /= H0 _| out0 out].
  apply (iffP idP) => [] // [start] [stop].
  by move=> /ribbon_on_stop_lt; rewrite /= ltn0; apply.
move=> partinn partout.
have:= partinn => /= /andP[hinn Hinn].
have:= partout => /= /andP[hout Hout].
apply (iffP orP) => [[/andP[lt0]/orP[/eqP Heq|] | /andP[/eqP eq0 Hrib]] | ].
- by exists 0; exists 0; split => // [][//|i]/=; rewrite Heq.
- move=> {IHinn} /=/andP[/eqP eqhout].
  move/(ribbon_fromP Hinn Hout) => [stop] [Hsi Hsis Hs His]/=.
  exists 0; exists stop.+1.
  split => //= [] [|i]//=; rewrite ltnS; [exact: Hsi | exact: Hsis].
- move/(_ _ Hinn Hout Hrib) : IHinn => [start] [stop] [Hsi Hsis Hs His].
  exists start.+1; exists stop.+1.
  split => //= [] [|i]//=; rewrite ltnS; [exact: Hsi | exact: Hsis| exact: His].
- move=> [[/(ribbon_fromP partinn partout) /= ->|start]]; first by left.
  move=> [stop] Hrib.
  have := ribbon_on_start_stop Hrib; case: stop Hrib => // stop.
  rewrite ribbon_onSS  => [[/eqP ->]] Hrib _.
  rewrite ltnn eqxx /=; right.
  by apply/IHinn => //; exists start; exists stop.
Qed.

Section Test.
(*
Goal ~~ ribbon_from [::] [::].
Proof. by []. Qed.
Goal ~~ ribbon_from [:: 2] [:: 2].
Proof. by []. Qed.
Goal ribbon_from [::] [:: 4].
Proof. by []. Qed.
Goal ribbon_from [:: 2] [:: 4].
Proof. by []. Qed.
Goal ~~ ribbon_from [:: 2] [:: 4; 2].
Proof. by []. Qed.
Goal ribbon_from [:: 2] [:: 3].
Proof. by []. Qed.
Goal ribbon_from [:: 2] [:: 4; 3].
Proof. by []. Qed.
Goal ribbon_from [:: 3; 2] [:: 4; 4].
Proof. by []. Qed.
Goal ~~ ribbon_from [:: 3; 2] [:: 4; 4; 1].
Proof. by []. Qed.
Goal ~~ ribbon_from [:: 3; 2] [:: 4; 4; 2].
Proof. by []. Qed.
Goal ribbon_from [:: 3; 2; 2] [:: 4; 4; 2].
Proof. by []. Qed.
Goal ~~ ribbon_from [:: 2; 2] [:: 4; 4].
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

Lemma ribbon_from_impl inn out : ribbon_from inn out -> ribbon inn out.
Proof. by case: inn => /= [->| _ _ ->] //. Qed.

Lemma ribbon_consK inn0 inn out0 out :
  ribbon (inn0 :: inn) (out0 :: out) -> (out == inn) || ribbon inn out.
Proof.
by move=>/=/orP[/andP[_ /orP[-> //| /andP[_ /ribbon_from_impl->]]] | /andP[_ ->]];
  rewrite orbT.
Qed.
Lemma ribbonE inn0 inn out0 out :
  inn0 < out0 ->
  ribbon (inn0 :: inn) (out0 :: out) = ribbon_from (inn0 :: inn) (out0 :: out).
Proof. by rewrite /= => H; rewrite H /= (gtn_eqF H) /= orbF. Qed.

Lemma ribbon_from_noneq inner outer : ribbon_from inner outer -> inner != outer.
Proof.
case: inner outer => [| inn0 inn] [| out0 out] //=.
by rewrite eqseq_cons => /andP[/ltn_eqF ->].
Qed.
Lemma ribbon_noneq inner outer : ribbon inner outer -> outer != inner.
Proof.
elim: inner outer => [| inn0 inn IHinn] [| out0 out] //=.
by rewrite eqseq_cons => /orP [/andP [/gtn_eqF ->] // | /andP [-> /IHinn]].
Qed.

Lemma ribbon_from_included inner outer :
  ribbon_from inner outer -> included inner outer.
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
by move=> /andP [_ /ribbon_from_included ->]; rewrite (ltnW lt0).
Qed.


Fixpoint startrem acc sh nbox pos :=
  if (pos, sh) is (p.+1, s0 :: s) then
    let c := nbox + nth 0 s p in
    let cpos := s0 + pos in
    if c >= cpos then (acc, c - cpos)  (* c == cpos -> error *)
    else startrem acc.+1 s nbox p
  else (acc + (pos - nbox), nbox - pos).  (* nbox <= pos -> error *)

(* Spec : nth 0 sh start + rem <= nth 0 sh start.-1 *)

Lemma startrem_acc_geq acc sh nbox pos : acc <= (startrem acc sh nbox pos).1.
Proof.
elim: pos sh acc => [|p IHpos] [|s0 s] acc /=; rewrite ?leqnn ?leq_addr //.
case: startrem (IHpos s acc.+1) => [start rem] /= /ltnW Has /=.
by case: (leqP (s0 + _) _).
Qed.

Lemma startrem_accE acc sh nbox pos :
  let (start, rem) := startrem acc sh nbox pos in
  nth 0 sh (start - acc) + pos + rem = nth 0 sh pos + (start - acc) + nbox.
Proof.
elim: pos sh acc => [|p IHpos] [|s0 s] acc /=;
    rewrite /= ?sub0n ?addn0 ?subnn /= ?add0n ?subn0 ?addn0 //.
  rewrite addKn nth_nil /= add0n.
  by rewrite [RHS]addnC -!maxnE maxnC.
move/(_ s acc.+1): IHpos.
case: startrem (startrem_acc_geq acc.+1 s nbox p) => [start rem] /= Hstart.
case: (leqP (s0 + _) _) => [Hle _| Hgt].
  by rewrite subnn /= subnKC // addn0 addnC.
case: start Hstart => // start /ltnSE Hstart.
by rewrite subSS (subSn Hstart) /= !(addnS, addSn) => ->.
Qed.
Lemma startremE sh nbox pos :
  let (start, rem) := startrem 0 sh nbox pos in
  nth 0 sh start + pos + rem = nth 0 sh pos + start + nbox.
Proof.
case: startrem (startrem_accE 0 sh nbox pos) => start rem.
by rewrite subn0; apply.
Qed.

Lemma startrem_acc_leq acc sh nbox pos :
  let (start, rem) := startrem acc sh nbox pos in
  0 < rem -> (* Success *)
  start <= (minn pos (size sh)) + acc.
Proof.
elim: pos sh acc => [|p IHpos] [|s0 s] acc /=;
    rewrite /= ?sub0n ?addn0 ?subn0 ?min0n ?addn0 //.
  rewrite subn_gt0 => /ltnW; rewrite -subn_eq0 => /eqP ->.
  by rewrite minn0 addn0 add0n.
case: startrem (IHpos s acc.+1) => [start rem] /=.
case: (leqP (s0 + _) _) => [_ _ _ |H] /=; first by rewrite leq_addl.
by rewrite minSS addSnnS.
Qed.
Lemma startrem_leq sh nbox pos :
  let (start, rem) := startrem 0 sh nbox pos in
  0 < rem -> (* Success *)
  start <= (minn pos (size sh)).
Proof. by have:= startrem_acc_leq 0 sh nbox pos => /=; rewrite addn0. Qed.

Lemma startremP acc sh nbox pos :
  is_part sh ->
  let (start, rem) := startrem acc sh nbox pos in
  0 < rem -> (* Success *)
  (start == acc) || (nth 0 sh (start - acc) + rem <= nth 0 sh (start - acc).-1).
Proof.
elim: pos sh acc => [|p IHpos] [|s0 s] acc; rewrite /= ?sub0n ?addn0 ?eqxx //.
  rewrite subn_gt0 => _ /ltnW; rewrite -subn_eq0 => /eqP ->.
  by rewrite addn0 eqxx.
move=> /andP[Hhead Hpart].
move/(_ s acc.+1 Hpart): IHpos => /=.
have Heq := startrem_accE acc.+1 s nbox p.
have:= startrem_acc_geq acc.+1 s nbox p => Hstart.
case: startrem  => [start rem]/= in Heq Hstart * => Hrec.
case (ltnP 0 rem) => [Hok | {Heq Hrec}].
  move/(_ Hok) : Hrec => /orP[/eqP eqstart | Hleq {Heq}]/=.
    case: (leqP (s0 + _) _) => [_ | Hlt _]; first by rewrite eqxx.
    apply/orP; right; rewrite eqstart subSn // subnn /=.
    rewrite eqstart subnn addn0 in Heq.
    by move: Hlt; rewrite addnC -{}Heq addnS ltnS addnAC leq_add2r.
  case: (leqP (s0 + _) _) => [_ | _ _]; first by rewrite eqxx.
  apply/orP; right.
  move: Hstart Hleq; rewrite subnS.
  rewrite -subn_gt0 => []; case: (start - acc) => //= [[|n]]// _ /=.
  by move/leq_trans; apply; case: s Hhead Hpart.
rewrite leqn0 => /eqP ->.
case: (leqP (s0 + _) _) => [_ | _ _]; first by rewrite eqxx.
rewrite addn0; apply/orP; right.
move: Hstart; rewrite -subn_gt0 => [].
case: (start - acc) => // [[|i]] _ /=; first by case: s Hhead {Hpart}.
by move/is_partP: Hpart => [_]; apply.
Qed.


Definition add_ribbon_start_stop sh start stop rem :=
  (take start sh)
    ++ (nth 0 sh start + rem :: map S (drop start (take stop sh)))
            ++ drop stop.+1 sh ++ nseq (stop - size sh) 1.
Definition add_ribbon sh nbox pos :=
  let: (start, rem) := startrem 0 sh nbox pos in
  if rem > 0 then
    Some (add_ribbon_start_stop sh start pos rem, (pos - start).+1)
  else error.

Section NTh.

Variable (sh : seq nat) (start stop rem : nat).
Hypothesis (lesmin : start <= minn stop (size sh)).

Local Notation res := (add_ribbon_start_stop sh start stop rem).

Let less : start <= stop.
Proof. by move: lesmin; rewrite leq_min=>/andP[]. Qed.
Let lessz : start <= size sh.
Proof. by move: lesmin; rewrite leq_min=>/andP[]. Qed.
Let sztd :
  size (drop start (take stop sh)) = minn stop (size sh) - start.
Proof. by rewrite size_drop size_take /minn. Qed.

Lemma nth_add_ribbon_lt_start i : i < start -> nth 0 res i = nth 0 sh i.
Proof.
move=> Hi; rewrite /add_ribbon_start_stop nth_cat size_take.
by rewrite -/(minn _ _) (minn_idPl lessz) Hi nth_take.
Qed.

Lemma nth_add_ribbon_start : nth 0 res start = nth 0 sh start + rem.
Proof.
rewrite /add_ribbon_start_stop nth_cat size_take.
by rewrite -/(minn _ _) (minn_idPl lessz) ltnn subnn.
Qed.

Lemma nth_add_ribbon_in i :
  start < i.+1 <= stop -> nth 0 res i.+1 = (nth 0 sh i).+1.
Proof.
move=> /andP[ltsi leis].
rewrite /add_ribbon_start_stop nth_cat size_take.
rewrite -/(minn _ _) (minn_idPl lessz) ltnNge (ltnW ltsi) /=.
rewrite subSn //= nth_cat size_map sztd.
rewrite ltn_subRL subnKC // leq_min leis /=.
case: ltnP => [ltisz | leszi].
- rewrite (nth_map 0); first last.
    by rewrite sztd ltn_subRL subnKC // leq_min leis.
  by rewrite nth_drop subnKC // nth_take.
have ltszs := leq_ltn_trans leszi leis.
rewrite nth_cat (minn_idPr (ltnW ltszs)).
rewrite subnBA // subnK // size_drop ltn_subLR //.
have:= ltnW ltszs; rewrite -ltnS => /ltnW; rewrite -subn_eq0 => /eqP ->.
rewrite addn0 (leq_gtF leszi) nth_nseq subn0.
rewrite ltn_subRL subnKC // leis.
by rewrite nth_default.
Qed.

Lemma nth_add_ribbon_stop_lt i : stop < i -> nth 0 res i = nth 0 sh i.
Proof.
move=> ltsi.
rewrite /add_ribbon_start_stop nth_cat size_take.
have ltszs := leq_ltn_trans less ltsi.
rewrite -/(minn _ _) (minn_idPl lessz) (leq_gtF (ltnW ltszs)).
rewrite nth_cat /= size_map sztd ltnS.
rewrite leq_subLR subnKC //.
rewrite leq_min (ltn_geF ltsi) //=.
rewrite nth_cat size_drop -(subSn lesmin) subnBA; last exact: ltnW.
rewrite (subnK (ltnW ltszs)) /minn.
case: (ltnP stop (size sh)) => [ltstsz | leszst].
  rewrite ltn_subRL subnKC //.
  have := ltnW ltstsz; rewrite -subn_eq0 => /eqP -> /=.
  rewrite nth_nil nth_drop subnKC //.
  by case: ltnP => // /(nth_default 0) ->.
have:=leszst; rewrite -ltnS => /ltnW; rewrite -subn_eq0 => /eqP -> /=.
rewrite subn0 nth_nseq.
case: i ltsi {ltszs} => // j /ltnSE ltsj.
rewrite subSS ltn_subRL (subnKC (leq_trans leszst ltsj)).
rewrite (leq_gtF ltsj) nth_default //.
by apply/ltnW; rewrite ltnS (leq_trans leszst ltsj).
Qed.

Lemma add_ribbon_start_stopP : rem > 0 -> ribbon_on start stop sh res.
Proof.
rewrite /ribbon_on => Hrem; split => [i Hsi | i Hsis || i His].
- exact: nth_add_ribbon_stop_lt.
- exact: nth_add_ribbon_in.
- by rewrite nth_add_ribbon_start -{1}(addn0 (nth 0 sh start)) ltn_add2l.
- exact: nth_add_ribbon_lt_start.
Qed.

Lemma is_part_add_ribbon_start_stop nbox :
  is_part sh -> rem > 0 ->
  startrem 0 sh nbox stop = (start, rem) -> is_part res.
Proof.
move=> Hpart Hrem Hstartrem.
have:= startremP 0 nbox stop Hpart; rewrite {}Hstartrem => /(_ Hrem) Hs.
have:= Hpart; rewrite !is_part_sortedE => /andP[/(sorted1P 0) /= _ H0].
move: Hpart => /is_partP => [[_ Hsort]].
apply/andP; split; first last.
  move: H0; apply contra; rewrite /add_ribbon_start_stop !mem_cat inE.
  repeat move=> /orP [].
  - exact: mem_take.
  - by case: rem Hrem => // r _; rewrite addnS.
  - by move=> /mapP [x _ /eqP].
  - exact: mem_drop.
  - by rewrite mem_nseq => /andP [].
apply/(sorted1P 0) => /= i ltiszres.
case: (ltnP i.+1 start) => [lti1start | lestarti1].
  by rewrite !nth_add_ribbon_lt_start // ?Hsort // (ltn_trans (ltnSn _)).
move: lestarti1; rewrite leq_eqVlt => /orP[/eqP Hi|ltstarti1].
  rewrite -Hi nth_add_ribbon_start nth_add_ribbon_lt_start ?Hi //.
  by move: Hs; rewrite Hi /= subn0.
move: ltstarti1; rewrite ltnS leq_eqVlt => /orP[/eqP Hi| ltstarti].
  rewrite -Hi nth_add_ribbon_start.
  move: less; rewrite leq_eqVlt => /orP[/eqP|] Hss.
  - rewrite {2}Hss nth_add_ribbon_stop_lt // Hss.
    exact: (leq_trans (Hsort stop) (leq_addr _ _)).
  - rewrite nth_add_ribbon_in ?ltnSn ?Hss //.
    by case: rem Hrem => // r _; rewrite addnS ltnS leq_addr.
case: i ltstarti => // i /ltnSE ltstarti in ltiszres *.
case: (ltnP i.+1 stop) => [lti1s | lesi1].
  rewrite !nth_add_ribbon_in ?ltnS ?Hsort //.
  + by rewrite ltstarti (ltn_trans _ lti1s).
  + by rewrite (leq_trans ltstarti _).
rewrite nth_add_ribbon_stop_lt //.
move: lesi1; rewrite leq_eqVlt => /orP[/eqP|] ltsi.
  rewrite nth_add_ribbon_in; last by rewrite ltnS ltstarti ltsi /=.
  by do 2 apply: (leq_trans (Hsort _)).
by rewrite nth_add_ribbon_stop_lt.
Qed.

End NTh.


Section Tests.
(*
(** Tests :
[
sage: s[2, 2] * p[1]
s[2, 2, 1] + s[3, 2]
]
 *****)
Compute add_ribbon_start_stop [:: 2; 2; 1; 1] 2 2 1.

Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 0 0 2 = [:: 4; 2; 1; 1].
Proof. by []. Qed.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 1 1 2 = [:: 2; 4; 1; 1].
Proof. by []. Qed. (* Not a ribbon. just for testing *)
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 0 1 2 = [:: 4; 3; 1; 1].
Proof. by []. Qed.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 0 2 2 = [:: 4; 3; 3; 1].
Proof. by []. Qed.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 2 2 1 = [:: 2; 2; 2; 1].
Proof. by []. Qed.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 2 3 1 = [:: 2; 2; 2; 2].
Proof. by []. Qed.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 2 4 1 = [:: 2; 2; 2; 2; 2].
Proof. by []. Qed.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 2 5 1 = [:: 2; 2; 2; 2; 2; 1].
Proof. by []. Qed.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 2 6 1 = [:: 2; 2; 2; 2; 2; 1; 1].
Proof. by []. Qed.

Compute startrem 0 [:: 2; 2; 1; 1] 2 1.
Compute add_ribbon [:: 2; 2; 1; 1] 2 1.

Goal startrem 0 [:: 2; 2; 1; 1] 2 0 = (0, 2).
Proof. by []. Qed.
Goal add_ribbon [:: 2; 2; 1; 1] 2 0 = Some ([:: 4; 2; 1; 1], 1).
Proof. by []. Qed.
Goal startrem 0 [:: 2; 2; 1; 1] 2 1 = (0, 1).
Proof. by []. Qed.
Goal add_ribbon [:: 2; 2; 1; 1] 2 1 = Some ([:: 3; 3; 1; 1], 2).
Proof. by []. Qed.

Compute pmap (add_ribbon [:: 2; 2] 1) (iota 0 10).
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


Section FirstAllEq.

Variable (T : eqType).
Implicit Types (s t : seq T).
Fixpoint first_alleq s t : nat :=
  if s is s0 :: s' then
    if t is t0 :: t' then
      if s' != t' then (first_alleq s' t').+1
      else s0 != t0
    else size s
  else size t.

Lemma drop_first_alleqE s t :
  drop (first_alleq s t) s = drop (first_alleq s t) t.
Proof.
elim: s t => [| s0 s IHs] [|t0 t]//=; try by rewrite drop_size.
by case: eqP => [->|_] //=; case: eqP => [->|].
Qed.

Lemma first_alleq0 s t : first_alleq s t = 0 -> s = t.
Proof.
by case: s t => [| s0 s] [|t0 t]//=; case: eqP => //= ->; case: eqP => // ->.
Qed.

Lemma first_alleq_eq s : first_alleq s s = 0.
Proof. by case: s => [| s0 s]//=; rewrite !eqxx. Qed.

Lemma first_alleq_neq s t : s != t -> first_alleq s t > 0.
Proof.
elim: t s => [| s0 s IHs] [|t0 t]//=.
rewrite eqseq_cons negb_and; case: (altP (t =P s)) => //= _.
by rewrite orbF => ->.
Qed.

End FirstAllEq.



Section Spec.

Variables (sh : seq nat).
Hypothesis (partsh : is_part sh).
Variable  (nbox pos : nat).
Variables (res : seq nat) (hgt : nat).
Hypothesis (Hret : add_ribbon sh nbox.+1 pos = Some (res, hgt)).

Lemma sumn_mapS s : sumn [seq i.+1 | i <- s] = sumn s + size s.
Proof. by elim: s => // s0 s /= ->; rewrite addSnnS -addnS addnA. Qed.

Lemma sumn_add_ribbon : sumn res = nbox.+1 + sumn sh.
Proof.
move: Hret; rewrite /add_ribbon.
move: (startremE sh nbox.+1 pos) (startrem_leq sh nbox.+1 pos).
case: startrem => start [|rem]// Heq /(_ (ltn0Sn _)) lesmin [<- _].
have:= lesmin; rewrite leq_min => /andP [lespos lessz].
rewrite /add_ribbon_start_stop !sumn_cat /= sumn_mapS.
rewrite size_drop size_take -/(minn _ _).
rewrite sumn_nseq mul1n -(take_take lespos) !addnA.
rewrite ![_ + sumn (drop start _)]addnAC -sumn_cat cat_take_drop.
rewrite ![_ + (_ - start) + _]addnAC addnBA //.
rewrite minnE -addnA (subnKC (leq_subr _ _)) // 2![_ + pos]addnAC.
rewrite [sumn (take _ _) + _ ]addnC 2![_ + sumn (take _ _) + _]addnAC Heq.
rewrite ![_ + start + _]addnAC addnK [_ + nbox.+1]addnC -!addnA; congr (_ + _).
rewrite addnCA sumn_take addnA -big_nat_recr //= -sumn_take.
by rewrite -sumn_cat cat_take_drop.
Qed.
Lemma is_part_add_ribbon : is_part res.
Proof.
move: Hret; rewrite /add_ribbon.
move: (startrem_leq sh nbox.+1 pos).
case Hstartrem : startrem => [start [|rem]]//=  /(_ (ltn0Sn _)) lesmin [<- _].
exact: (is_part_add_ribbon_start_stop _ _ _ Hstartrem).
Qed.
Lemma is_part_of_add_ribbon : is_part_of_n (nbox.+1 + sumn sh) res.
Proof.
by rewrite /is_part_of_n /= sumn_add_ribbon eqxx is_part_add_ribbon.
Qed.

Lemma size_add_ribbon : size res = maxn (size sh) pos.+1.
Proof.
move: Hret; rewrite /add_ribbon.
move: (startrem_leq sh nbox.+1 pos).
case: startrem => start [|rem]//= /(_ (ltn0Sn _)) lesmin [<- _].
have:= lesmin; rewrite leq_min => /andP [lespos lessz].
rewrite /add_ribbon_start_stop !size_cat /= size_map size_nseq.
rewrite !size_drop !size_take.
rewrite addSnnS -addSn -!/(minn _ _) (minn_idPl lessz).
rewrite addnA subnKC //.
case: (ltnP pos (size sh)) => [Hlt|Hge].
  have:= ltnW Hlt; rewrite -subn_eq0 => /eqP ->.
  by rewrite addn0 -subSn // subSS (subnKC (ltnW Hlt)) (maxn_idPl Hlt).
have:= Hge; rewrite -ltnS => /ltnW; rewrite -subn_eq0 => /eqP -> /=.
by rewrite add1n -subSn // maxnE.
Qed.

Lemma add_ribbonP : ribbon sh res.
Proof.
move: Hret; rewrite /add_ribbon => H.
apply/(ribbonP partsh is_part_add_ribbon).
move: (startrem_leq sh nbox.+1 pos) H.
case: startrem => start [|rem]//= /(_ (ltn0Sn _)) lesmin [<- _].
exists start; exists pos.
exact: add_ribbon_start_stopP.
Qed.

Lemma included_add_ribbon : included sh res.
Proof. exact: ribbon_included (add_ribbonP). Qed.

(*
Lemma add_ribbon_height : hgt = count (ltn 0) (res / sh).
Proof.
move: Hret; rewrite /add_ribbon.
case Hrib: add_ribbon_base => // [[[x y] rem]] [Hx Hy]; subst x y.
exact: (add_ribbon_base_height is_part_base_init Hrib).
Qed.

Lemma add_ribbon_pos : pos = (first_alleq sh res).-1.
Proof.
move: Hret; rewrite /add_ribbon.
case Hrib: add_ribbon_base => // [[[x y] rem]] [Hx Hy]; subst x y.
exact: (add_ribbon_base_pos is_part_base_init Hrib).
Qed.
*)
End Spec.



(*


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
Definition add_ribcol base s0 shres h rem :=
  if rem == 0 then Some (s0 :: shres, h, 0)
  else if rem == base.+1 - s0 then None
       else let: p := minn rem (base.+1 - s0) in
            Some (s0 + p :: shres, h.+1, rem - p).
Fixpoint add_ribbon_base base sh nbox pos :=
  if sh is s0 :: s' then
    if pos is i.+1 then
      if add_ribbon_base s0 s' nbox i is Some (shres, h, rem) then
        add_ribcol base s0 shres h rem
      else None
    else add_ribcol base s0 s' 0 nbox
  else if nbox <= pos then None
       else add_ribcol base 0 (nseq pos 1) pos (nbox - pos).

Definition add_ribbon sh nbox pos :=
  omap fst (* assert snd == 0 *) (add_ribbon_base (nbox + sumn sh) sh nbox pos).



Section SpecBase.

Variables (base : nat) (sh : seq nat).
Hypothesis partsh : is_part (base :: sh).
Variable  nbox pos : nat.
Variables (res : seq nat) (hgt rem : nat).
Hypothesis Hret : add_ribbon_base base sh nbox.+1 pos = Some (res, hgt, rem).

Lemma rem_add_ribbon_base_lt : rem <= nbox.
Proof.
have add_ribcol_rem bs s0 rm r :
    s0 <= bs -> add_ribcol bs s0 _ _ rm = Some (_, _, r) -> r <= rm.-1.
  rewrite /add_ribcol /= => lts0bs; case: rm => //= [[_ _ <-]// | rm].
  case: eqP => // _ [_ _ <-].
  by rewrite (subSn lts0bs) minSS subSS leq_subr.
move: partsh => /= /andP [Hbase Hpart].
elim: sh Hpart base Hbase nbox pos res hgt rem Hret
  => /= [_|s0 s' IHs /andP [{}/IHs H{}/H Hrec]] bs lts0bs l p rs h rm.
  case: (ltnP l p) => // lepl.
  rewrite subSn //= => /add_ribcol_rem-/(_ (ltnW lts0bs))/leq_trans; apply.
  exact: leq_subr.
case: p => [/add_ribcol_rem -> // | p].
move/(_ l p): Hrec; case: add_ribbon_base=> // [[[shres hres] remres]].
move=> /(_ _ _ _ erefl) H /add_ribcol_rem-/(_ lts0bs)/leq_trans; apply.
exact: (leq_trans (leq_pred _) H).
Qed.

Lemma add_ribcol_part bs s0 s h rm rs hs rms :
  s0 <= bs -> is_part (s0 + (rm != 0) :: s) ->
  add_ribcol bs s0 s h rm = Some (rs, hs , rms) ->
  is_part (bs + (rms != 0) :: rs).
Proof.
rewrite /add_ribcol /= => Hlt /andP [Hhead Hpart].
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
  case: (ltnP l p) => // lepl /(add_ribcol_part (ltnW lts0bs)); apply.
  by rewrite add0n subSn //= is_part_nseq1 andbT; case p.
case: p => [/(add_ribcol_part lts0bs)/= | p].
  by apply; rewrite Hpart andbT addn1 (leq_trans Hhead).
case: add_ribbon_base (IHs Hpart s0 Hhead l p) => {IHs}//.
move=> [[shres hres] remres] /(_ _ _ _ erefl) /andP[headres Hpartres].
move/add_ribcol_part => /(_ lts0bs) /=; apply.
by rewrite headres Hpartres.
Qed.

Lemma add_ribcol_eq bs s0 s h rm rs hs rms :
  s0 <= bs ->
  add_ribcol bs s0 s h rm = Some (rs, hs, rms) ->
  sumn rs + rms = sumn (s0 :: s) + rm.
Proof.
rewrite /add_ribcol /=.
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
  case: (ltnP l p) => // lepl /(add_ribcol_eq (ltnW lts0bs)) ->.
  by rewrite /= addn0 add0n sumn_nseq mul1n subnKC // (leq_trans lepl).
case: p => [/(add_ribcol_eq lts0bs)/= ->| p].
  by rewrite addnC addnA.
case: add_ribbon_base (IHs Hpart s0 Hhead l p) => {IHs}//.
move=> [[shres hres] remres] /(_ _ _ _ erefl) Heq /(add_ribcol_eq lts0bs) -> /=.
by rewrite -addnA {}Heq !addnA [s0 + _]addnC.
Qed.

Lemma add_ribbon_base_neq : sh != res.
Proof.
apply/negP=> /eqP Heq; move: sumn_add_ribbon_base rem_add_ribbon_base_lt.
rewrite {}Heq addnC => /eqP; rewrite eqn_add2r => /eqP ->.
by rewrite ltnn.
Qed.

Lemma size_add_ribbon_base : size res = maxn (size sh) pos.+1.
Proof.
move: partsh => /= /andP [Hbase Hpart].
elim: sh Hpart base Hbase nbox pos res hgt rem Hret
    => /= [_|s0 s' IHs /andP[Hhead Hpart]] bs lts0bs l p rs h rm.
  case: (ltnP l p) => // lepl.
  rewrite /add_ribcol; case: eqP => [_ [<- _ _] | _] /=.
    by rewrite size_nseq.
  by case: eqP => // _ [<- _ _] /=; rewrite size_nseq.
case: p => [|p].
  rewrite /add_ribcol /=; case: eqP => // _ [<- _ _] /=.
  by rewrite maxnSS maxn0.
case: add_ribbon_base (IHs Hpart s0 Hhead l p) => {IHs}//.
move=> [[shres hres] remres] // /(_ _ _ _ erefl) Hres.
rewrite /add_ribcol /=; case: (altP (_ =P _)) => [_ [<- _ _] | Hrem] /=.
  by rewrite Hres maxnSS.
by case: eqP => // _ [<- _ _] /=; rewrite Hres maxnSS.
Qed.

Lemma add_ribcol_ribbon_from bs inn s0 s h rm rs hs rms :
  s0 <= bs ->
  ribbon_from (s0 :: inn) (s0.+1 :: s) ->
  add_ribcol bs s0 s h rm.+1 = Some (rs, hs, rms.+1) ->
  ribbon_from (bs :: s0 :: inn) (bs.+1 :: rs) && (head 0 rs != 0).
Proof.
rewrite /add_ribcol /= !ltnSn /= => lts0bs Hrib.
rewrite subSn // eqSS; case: (altP (_ =P _)) => // Heq [<- _ /eqP].
move: Heq; rewrite minSS subSS /minn.
rewrite neq_ltn => /orP [->| Hbs]; first by rewrite subnn.
rewrite (ltnNge rm _) (ltnW Hbs) /= => _.
by rewrite Hrib /= andbT addnS subnKC // eqxx ltnS lts0bs orbT.
Qed.
Lemma add_ribbon_base_inP :
  rem != 0 -> ribbon_from (base :: sh) (base.+1 :: res).
Proof.
case: rem Hret => // rm Hrm _.
move: partsh => /= /andP [Hbase Hpart].
elim: sh Hpart base Hbase nbox pos res hgt rm Hrm
  => [_ /= |s0 s' IHs Hpart] bs lts0bs l p rs h rm.
  case: (ltnP l p) => // lepl.
  rewrite (subSn lepl) => /(add_ribcol_ribbon_from (ltnW lts0bs))-/(_ [::]) H.
  have {}/H /= : ribbon_from [:: 0] (1 :: nseq p 1).
    by rewrite /=; case p => //= [[|]].
  rewrite !ltnSn /= => /andP [].
  case: rs => //= r0 rs /orP [/eqP[<-]//|].
  by move=> /and3P[/eqP ->] _ /orP [/eqP <- _ /=| /andP[/eqP ->]]; rewrite eqxx.
case: p => [/(add_ribcol_ribbon_from lts0bs)-/(_ s') | p /=] H.
  by have /H/andP [] : ribbon_from (s0 :: s') (s0.+1 :: s')
    by rewrite /ribbon /= ltnSn eqxx.
move: Hpart; rewrite ltnSn /= => /andP [Hhead Hpart].
case: add_ribbon_base (IHs Hpart s0 Hhead l p) H => {IHs}//.
move=> [[shres hres] [|remres]] // /(_ _ _ _ erefl) Hrib.
move/add_ribcol_ribbon_from => /(_ s' lts0bs) H.
have {Hrib}/H /= : ribbon_from (s0 :: s') (s0.+1 :: shres) by move: Hrib => /= ->.
by rewrite ltnSn /= => /andP [-> _].
Qed.

Lemma add_ribbon_base_height : hgt = count (ltn 0) (res / sh).
Proof.
move: partsh => /= /andP [Hbase Hpart].
elim: sh Hpart base Hbase nbox pos res hgt rem Hret
    => /= [_|s0 s' IHs /andP[Hhead Hpart]] bs lts0bs l p rs h rm.
  case: (ltnP l p) => // lepl.
  rewrite /add_ribcol; case: eqP => [_ [<- <- _] | _] /=.
    by rewrite add0n count_nseq /= mul1n.
  case: eqP => // _ [<- <- _] /=.
  by rewrite add0n count_nseq /= mul1n subn0 subSn // minSS /= add1n.
case: p => [|p].
  rewrite /add_ribcol /=; case: eqP => // _ [<- <- _] /=.
  rewrite addKn subSn // minSS /=.
  suff -> : count (ltn 0) (s' / s') = 0 by rewrite addn0.
  elim: s' {IHs Hhead Hpart} => //= s1 s ->.
  by rewrite subnn add0n.
case: add_ribbon_base (IHs Hpart s0 Hhead l p) => {IHs}//.
move=> [[shres hres] remres] // /(_ _ _ _ erefl) Hres.
rewrite /add_ribcol /=; case: (altP (_ =P _)) => [_ [<- <- _] | Hrem] /=.
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
have add_ribcol_eq0 bs s0 rm r :
    s0 <= bs -> rm <= (bs - s0) ->
    add_ribcol bs s0 _ _ rm = Some (_, _ , r) -> r = 0.
  rewrite /add_ribcol /= => lts0bs; case: rm => //= [_ [_ _ <-]// | rm ltrm].
  case: eqP => // _ [_ _ <-].
  rewrite (subSn lts0bs) minSS subSS.
  by move: ltrm => /ltnW/minn_idPl ->; rewrite subnn.
move=> Heq.
move: partsh => /= /andP [Hbase Hpart].
case: sh Hpart Heq Hbase Hret => /= [_|s0 s' Hpart -> lts0bs]/=.
  case: (ltnP nbox pos) => // lelpos -> _ /add_ribcol_eq0; apply => //.
  by rewrite subn0 addn0 leq_subr.
case: pos => [/add_ribcol_eq0-/(_ lts0bs)/= -> //| p].
  by rewrite -addnBA ?leq_addr.
case Hrib: add_ribbon_base => // [[[rs h] rm]].
move/add_ribcol_eq0 => /(_ lts0bs) -> //.
have := rem_add_ribbon_base_lt Hpart Hrib => /leq_trans; apply.
by rewrite -addnBA ?leq_addr // addKn addSnnS leq_addr.
Qed.

Lemma add_ribbon_base_pos : pos = (first_alleq sh res).-1.
Proof.
move: partsh => /= /andP [Hbase Hpart].
elim: sh Hpart base Hbase nbox pos res hgt rem Hret
    => /= [_|s0 s' IHs /andP[Hhead Hpart]] bs lts0bs l p rs h rm.
  case: (ltnP l p) => // lepl.
  rewrite /add_ribcol; case: eqP => [_ [<- _ _] | _] /=.
    by rewrite size_nseq.
  case: eqP => // _ [<- _ _] /=.
  by rewrite size_nseq.
case: p => [|p].
  rewrite /add_ribcol /=; case: eqP => // _ [<- _ _].
  by rewrite eqxx /= subSn // minSS ltn_eqF // addnS ltnS leq_addr.
case Hrib: add_ribbon_base => // [[[rs1 h1] rm1]].
move: IHs => /(_ Hpart s0 Hhead l p _ _ _ Hrib) ->.
have /add_ribbon_base_neq : is_part (s0 :: s') by rewrite /= Hhead Hpart.
move=> /(_ _ _ _ _ _ Hrib) Hneq.
rewrite /add_ribcol; case: (altP (rm1 =P _)) => Hrm1.
  move=> [<-{rs}] _ _ /=; rewrite Hneq /=.
  by move/first_alleq_neq: Hneq; case: first_alleq.
case: (altP (rm1 =P _)) => // eqrm1 [<- _ _]; rewrite Hneq.
by move/first_alleq_neq: Hneq; case: first_alleq.
Qed.

Lemma add_ribbon_baseP : ribbon sh res.
Proof.
case: (altP (rem =P 0)) => [Hrem|]; first last.
  move/(add_ribbon_base_inP partsh Hret)/ribbon_from_impl/ribbon_consK.
  by have:= (add_ribbon_base_neq partsh Hret) => /negbTE ->.
move: Hret; rewrite {}Hrem => Hret0.
move: partsh => /= /andP [Hbase Hpart].
elim: sh Hpart base Hbase nbox pos res hgt Hret0
  => /= [ _ |s0 s' IHs Hpart] bs lts0bs l p rs h.
  case: (ltnP l p) => // lepl; rewrite /add_ribcol /=.
  rewrite subn_eq0 ltnNge lepl /= subn0.
  case: (altP (_ =P _)) => // _; rewrite add0n => [][<- _ _].
  by case p.
case: p => [|p].
  rewrite /add_ribcol /=; case: (altP (_ =P _)) => // _ [<- _ _].
  by rewrite (subSn lts0bs) minSS addnS ltnS leq_addr eqxx.
move tr : (add_ribbon_base s0 s' l.+1 p) => [] //.
move: tr => [[shres hres] [|remres]].
  move: Hpart => /andP [{}/IHs H{}/H H{}/H Hrib].
  by rewrite /add_ribcol /= => [] [<- _]; rewrite eqxx Hrib /= orbT.
move=> /(add_ribbon_base_inP Hpart)/(_ is_true_true) /= /andP [_] Hrib.
rewrite /add_ribcol /=; case: (altP (_ =P _)) => // Heq [<-{rs} _{h hres}] _.
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

Lemma is_part_base_init : is_part (nbox.+1 + sumn sh :: sh).
Proof.
rewrite /= partsh andbT addSnnS; apply: (leq_trans _ (leq_addl _ _)).
by case: sh => //= s0 s; rewrite -addnS leq_addr.
Qed.

Lemma sumn_add_ribbon : sumn res = nbox.+1 + sumn sh.
Proof.
move: Hret; rewrite /add_ribbon.
case Hrib: add_ribbon_base => // [[[x y] z]] [Hx Hy]; subst x y.
have:= sumn_add_ribbon_base is_part_base_init Hrib.
by rewrite (add_ribbon_base_rem0 is_part_base_init Hrib erefl) addn0 => ->.
Qed.

Lemma size_add_ribbon : size res = maxn (size sh) pos.+1.
Proof.
move: Hret; rewrite /add_ribbon.
case Hrib: add_ribbon_base => // [[[x y] z]] [Hx Hy]; subst x y.
exact: (size_add_ribbon_base is_part_base_init Hrib).
Qed.

Lemma is_part_of_add_ribbon : is_part_of_n (nbox.+1 + sumn sh) res.
Proof.
rewrite /is_part_of_n /= sumn_add_ribbon eqxx /=.
move: Hret; rewrite /add_ribbon.
case Hrib: add_ribbon_base => // [[[x y] z]] [Hx Hy]; subst x y.
by have /= /andP [] := is_part_add_ribbon_base is_part_base_init Hrib.
Qed.

Lemma add_ribbonP : ribbon sh res.
Proof.
move: Hret; rewrite /add_ribbon.
case Hrib: add_ribbon_base => // [[[x y] rem]] [Hx Hy]; subst x y.
exact: (add_ribbon_baseP is_part_base_init Hrib).
Qed.

Lemma included_add_ribbon : included sh res.
Proof. exact: ribbon_included (add_ribbonP). Qed.

Lemma add_ribbon_height : hgt = count (ltn 0) (res / sh).
Proof.
move: Hret; rewrite /add_ribbon.
case Hrib: add_ribbon_base => // [[[x y] rem]] [Hx Hy]; subst x y.
exact: (add_ribbon_base_height is_part_base_init Hrib).
Qed.

Lemma add_ribbon_pos : pos = (first_alleq sh res).-1.
Proof.
move: Hret; rewrite /add_ribbon.
case Hrib: add_ribbon_base => // [[[x y] rem]] [Hx Hy]; subst x y.
exact: (add_ribbon_base_pos is_part_base_init Hrib).
Qed.

End Spec.

Lemma ribbon_from_exP inner outer :
  is_part inner -> is_part outer -> ribbon_from inner outer ->
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
  rewrite /add_ribcol /= subn0 eqSS (gtn_eqF Harm) add0n minSS subSS.
  move/ltnW/minn_idPr: Harm => ->.
  by rewrite addnC subnDA.
move=> /[swap]/[dup]/part_head_non0.
case: out0 => //= out0 _ /andP[headout partout] /andP[headinn partinn].
rewrite ltnS => /andP [le0] /orP [/eqP Heq | /andP[/eqP Hout Hrib]].
  rewrite {partinn inn IHinn}Heq in headinn *.
  exists 0 => nbox; nat_norm; rewrite addnA ltnS ltn_add2r => Hlt.
  rewrite /add_ribcol //= subSn // eqSS.
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
rewrite /add_ribcol /= subn_eq0 leqNgt Hlt1 /=.
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
  rewrite /add_ribcol /= subn0 eqSS (ltn_eqF Hout0) add0n minSS subSS.
  move/ltnW/minn_idPl: Hout0 => ->.
  by rewrite subnn.
move=> /[swap]/[dup]/part_head_non0.
case: out0 => //= out0 _ /andP[headout partout] /andP[headinn partinn].
rewrite ltnS => /orP [/andP[le0] /orP [/eqP Heq |]| ].
  rewrite {partinn inn IHinn}Heq in headinn *.
  exists 0; exists 1 => nbox base.
  rewrite /add_ribcol !addSn addnA => [[]]/eqP.
  rewrite eqn_add2r => /eqP eqout0 ltout0 /=.
  have ltinn0 := leq_ltn_trans le0 ltout0.
  rewrite subSn ?(ltnW ltinn0) // eqSS.
  rewrite -(eqn_add2r inn0) subnK ?(ltnW ltinn0) // eqout0 (ltn_eqF ltout0).
  rewrite minSS subSS.
  suff /minn_idPl-> : nbox <= (base - inn0) by rewrite addnS addnC eqout0 subnn.
  by apply: ltnW; rewrite ltn_subRL addnC eqout0.
move => {IHinn} /andP[/eqP Hout Hrib].
  have [pos Hrec] := ribbon_from_exP partinn partout Hrib.
  exists pos.+1; exists pos.+2 => nbox base Heq Hbase.
  have Hlt : sumn out < nbox.+1 + sumn inn.
    by rewrite -(ltn_add2l out0.+1) -Heq addnCA ltn_add2r ltnS.
  move/(_ _ Hlt): Hrec; rewrite Hout /= => ->.
  rewrite /add_ribcol subn_eq0 leqNgt Hlt /=.
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

Lemma add_ribbon_eq inner outer :
  is_part inner -> is_part outer -> ribbon inner outer ->
  add_ribbon inner (sumn outer - sumn inner) (first_alleq inner outer).-1 =
  Some (outer, count (ltn 0) (outer / inner)).
Proof.
move=> partinn partout Hrib.
have/(ribbonP partinn partout) := Hrib => [[nbox][pos][H]Heq].
rewrite -(add_ribbon_height partinn Heq) -(add_ribbon_pos partinn Heq) -Heq.
by rewrite (sumn_add_ribbon partinn Heq) addnK.
Qed.

Lemma fst_add_ribbon_inj inner nbox :
  is_part inner ->
  {on [pred x : option _ | x], injective (omap fst \o add_ribbon inner nbox.+1)}.
Proof.
move=> Hpart pos1; rewrite inE => /= Hrib1 pos2.
case Hrib1 : add_ribbon Hrib1 => [[outer1 h1]|//] _ /esym /= Hrib2.
rewrite (add_ribbon_pos Hpart Hrib1).
case Hrib2 : add_ribbon Hrib2 => [[outer2 h2]|//] /= [] <-.
by rewrite (add_ribbon_pos Hpart Hrib2).
Qed.

Lemma add_ribbon_inj inner nbox :
  is_part inner ->
  {on [pred x : option _ | x], injective (add_ribbon inner nbox.+1)}.
Proof.
move=> /fst_add_ribbon_inj H r1; rewrite inE => H1 r2 Heq.
apply: (H nbox); last by rewrite /= Heq.
by rewrite inE /=; case: add_ribbon H1.
Qed.

*)
