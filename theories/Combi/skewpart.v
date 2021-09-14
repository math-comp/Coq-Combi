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

- [ribbon_from inn out] == [out/inn] is a ribbon shape starting at row 0
- [ribbon inn out] == [out/inn] is a ribbon shape
- [ribbon_on start stop inn out] <-> [out/inn] is a ribbon shape starting and
               ending at rows start and stop.
- [add_ribbon sh nbox pos] == tries to add a ribbon with nbox ending at row
               [pos] to the shape [sh]. Returns [Some (sh, hgt)] where [sh] is
               the outer shape of the result and [hgt] its height on success,
               or [error] if not
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
    by rewrite size_diff_shape nth_diff_shape leq_subLR addn1 => /[apply].
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

Lemma vb_strip_countP inner outer :
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


Section MinDropEq.

Variable (T : eqType).
Implicit Types (s : seq T).

Fact ex_dropeq s1 s2 : exists n, drop n s1 == drop n s2.
Proof.
exists (maxn (size s1) (size s2)).
by rewrite !drop_oversize ?leq_maxr ?leq_maxl.
Qed.
Definition mindropeq s1 s2 := ex_minn (ex_dropeq s1 s2).

Lemma mindropeqC s1 s2 : mindropeq s1 s2 = mindropeq s2 s1.
Proof. by apply: eq_ex_minn => n; rewrite eq_sym. Qed.

Lemma mindropeq0 s1 s2 : mindropeq s1 s2 = 0 -> s1 = s2.
Proof.
rewrite /mindropeq; case: ex_minnP => m /eqP eqdrop _ meq0.
by move: eqdrop; rewrite meq0 !drop0.
Qed.

Lemma mindropeq_eq s : mindropeq s s = 0.
Proof.
rewrite /mindropeq; case: ex_minnP => m _ /(_ 0 (eqxx _)).
by rewrite leqn0 => /eqP ->.
Qed.

Lemma mindropeq_nil s : mindropeq [::] s = size s.
Proof.
rewrite /mindropeq; case: ex_minnP => m /= /eqP/esym dropm Hmin.
apply anti_leq.
have /esym/eqP/Hmin -> /= := drop_size s.
by rewrite -drop_nilE dropm.
Qed.

Lemma mindropeq_cons_eq a b s : a != b -> mindropeq (a :: s) (b :: s) = 1.
Proof.
rewrite /mindropeq; case: ex_minnP => m /= /eqP/esym dropm Hmin Hneq.
apply anti_leq; rewrite {}Hmin //=.
by case: m dropm => // /eqP; rewrite !drop0 eqseq_cons eq_sym (negbTE Hneq).
Qed.

Lemma mindropeq_cons_neq a b s1 s2 :
  s1 != s2 -> mindropeq (a :: s1) (b :: s2) = (mindropeq s1 s2).+1.
Proof.
rewrite /mindropeq => Hneq; case: ex_minnP => m dropm Hminm.
case: ex_minnP => n dropn Hminn; apply anti_leq.
rewrite {}Hminm //=.
case: m dropm => [|m {}/Hminn]/=; last by rewrite ltnS.
by rewrite eqseq_cons (negbTE Hneq) andbF.
Qed.

Lemma mindropeq_nthP x0 s t p :
  x0 \notin s -> x0 \notin t ->
  reflect
    (nth x0 s p != nth x0 t p /\ (forall i, i > p -> nth x0 s i = nth x0 t i))
    (mindropeq s t == p.+1).
Proof.
rewrite /mindropeq => x0notins x0notint.
apply (iffP eqP); case: ex_minnP => m eqdrop mmin.
- move=> eqmp1; split.
  + move/(_ p)/contra: mmin; rewrite eqmp1 -leqNgt => /(_ (leqnn _)) Hneq.
    rewrite {}eqmp1 -add1n -!drop_drop in eqdrop.
    apply/contra: Hneq => /eqP; rewrite -{1 2}(addn0 p) -!nth_drop => Heq.
    have {x0notins} : x0 \notin (drop p s).
      by apply/contra/mem_drop: x0notins.
    have {x0notint} : x0 \notin (drop p t).
      by apply/contra/mem_drop: x0notint.
    case: (drop p s) (drop p t) Heq eqdrop => [|s0 s'] [|t0 t'] //= <-;
      try by rewrite inE eqxx /=.
    by rewrite !drop0 => /eqP ->.
  + rewrite -eqmp1 => i lemi.
    by rewrite -(subnKC lemi) -!nth_drop (eqP eqdrop).
- move=> [Hneq Heq].
  apply anti_leq; apply/andP; split.
  + apply: mmin; apply/eqP/(eq_from_nth_notin (x0 := x0)); first last.
      by move=> i; rewrite !nth_drop addSn; apply: Heq; rewrite ltnS leq_addr.
    * by apply/contra: x0notint => /mem_drop.
    * by apply/contra: x0notins => /mem_drop.
  + apply/contraR: Hneq; rewrite -leqNgt => lemp.
    by rewrite -(subnKC lemp) -!nth_drop (eqP eqdrop).
Qed.

End MinDropEq.


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
Definition ribbon_height inner outer := count (ltn 0) (outer / inner).


Section Test.

Goal ~~ ribbon_from [::] [::].
Proof. by []. Abort.
Goal ~~ ribbon_from [:: 2] [:: 2].
Proof. by []. Abort.
Goal ribbon_from [::] [:: 4].
Proof. by []. Abort.
Goal ribbon_from [:: 2] [:: 4].
Proof. by []. Abort.
Goal ~~ ribbon_from [:: 2] [:: 4; 2].
Proof. by []. Abort.
Goal ribbon_from [:: 2] [:: 3].
Proof. by []. Abort.
Goal ribbon_from [:: 2] [:: 4; 3].
Proof. by []. Abort.
Goal ribbon_from [:: 3; 2] [:: 4; 4].
Proof. by []. Abort.
Goal ~~ ribbon_from [:: 3; 2] [:: 4; 4; 1].
Proof. by []. Abort.
Goal ~~ ribbon_from [:: 3; 2] [:: 4; 4; 2].
Proof. by []. Abort.
Goal ribbon_from [:: 3; 2; 2] [:: 4; 4; 2].
Proof. by []. Abort.
Goal ~~ ribbon_from [:: 2; 2] [:: 4; 4].
Proof. by []. Abort.

Goal ribbon [:: 2] [:: 3].
Proof. by []. Abort.
Goal ribbon [:: 2; 2] [:: 3; 2].
Proof. by []. Abort.
Goal ribbon [:: 2; 2] [:: 3; 3].
Proof. by []. Abort.
Goal ribbon [:: 5; 3; 2; 2] [:: 5; 4; 4; 2].
Proof. by []. Abort.
Goal ~~ ribbon [:: 5; 3; 2; 2] [:: 5; 4; 4; 2; 1].
Proof. by []. Abort.
Goal ~~ ribbon [::] [::].
Proof. by []. Abort.
Goal ~~ ribbon [:: 2; 1] [:: 2; 1].
Proof. by []. Abort.

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

Lemma ribbon_on_height start stop inner outer :
  is_part inner -> is_part outer ->
  ribbon_on start stop inner outer ->
  (stop - start).+1 = ribbon_height inner outer.
Proof.
elim: start => [|start IHst] in stop inner outer * => partinn partout Hrib.
  rewrite /ribbon_height subn0.
  have /(ribbon_on_stop_lt partout) := Hrib => ltszsout.
  move: Hrib => [Hsi Hsis H0 _].
  rewrite -(cat_take_drop stop.+1 (outer / inner)) count_cat.
  rewrite (eq_in_count (a2 := xpredT)); first last.
    move=> x Hin /=; rewrite -(nth_index 0 (mem_take Hin)).
    move: (index _ _) (index_ltn Hin) => i; rewrite ltnS => ltis.
    rewrite nth_diff_shape subn_gt0.
    case: i ltis => [|i ltis]; first by rewrite H0.
    rewrite Hsis // ltnS.
    by move: partinn => /is_partP [_ ->].
  rewrite count_predT (eq_in_count (a2 := xpred0)); first last.
    move=> x /(nth_index 0) <- /=; move: (index _ _) => i.
    rewrite nth_drop addSn nth_diff_shape subn_gt0.
    by rewrite Hsi ?ltnn // ltnS leq_addr.
  rewrite count_pred0 addn0 size_take size_diff_shape.
  by rewrite -/(minn _ _) (minn_idPl ltszsout).
have := (ribbon_on_start_stop Hrib).
case: stop IHst Hrib => // stop IHst Hrib Htss.
have := ribbon_on_start_le partout Hrib.
case: inner => // inn0 inn in partinn Hrib * => _.
move/is_part_consK in partinn.
have := ribbon_on_stop_lt partout Hrib.
case: outer => // out0 out in partout Hrib * => _.
move/is_part_consK in partout.
move: Hrib; rewrite /ribbon_height ribbon_onSS => [[/eqP eq0 Hrib]] /=.
rewrite {}eq0 subnn ltnn add0n subSS.
exact: IHst.
Qed.

Lemma ribbon_on_mindropeq start stop inner outer :
  is_part inner -> is_part outer -> ribbon_on start stop inner outer ->
  mindropeq inner outer = stop.+1.
Proof.
move=> /[dup]/is_partP[_ sortinn].
rewrite !is_part_sortedE => /andP[_ inn0] /andP[_ out0] Hrib.
apply/eqP/(mindropeq_nthP _ inn0 out0) => {inn0 out0}.
split => [|i]; last by move: Hrib => [Hsi _ _ _] /Hsi ->.
have less := ribbon_on_start_stop Hrib.
move: Hrib => [_ Hsis Hs _].
move: less; rewrite leq_eqVlt => /orP[/eqP <-|ltss]; first by rewrite ltn_eqF.
case: stop Hsis ltss {Hs} => // stop Hsis /ltnSE less.
have {less}/Hsis-> : start <= stop < stop.+1 by rewrite less ltnSn.
by rewrite ltn_eqF // ltnS.
Qed.

Lemma ribbon_on_stopE start stop inner outer :
  is_part inner -> is_part outer -> ribbon_on start stop inner outer ->
  stop = (mindropeq inner outer).-1.
Proof. by move=>/ribbon_on_mindropeq/[apply]/[apply]->. Qed.

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

Lemma ribbon_from_mindropeq inner outer :
  is_part inner -> is_part outer -> ribbon_from inner outer ->
  ribbon_on 0 (mindropeq inner outer).-1 inner outer.
Proof.
move=> pinn pout /(ribbon_fromP pinn pout) [stop] Hrib.
by rewrite -(ribbon_on_stopE pinn pout Hrib).
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

Lemma ribbon_mindropeq inner outer :
  is_part inner -> is_part outer -> ribbon inner outer ->
  let min := mindropeq inner outer in
  let height := ribbon_height inner outer in
  ribbon_on (min - height) min.-1 inner outer.
Proof.
move=> pinn pout /(ribbonP pinn pout) [start][stop] Hrib /=.
rewrite -(ribbon_on_height pinn pout Hrib).
rewrite (ribbon_on_mindropeq pinn pout Hrib) /=.
by rewrite subSS subKn // (ribbon_on_start_stop Hrib).
Qed.

Lemma ribbon_on_sumn start stop inner outer :
  is_part inner -> is_part outer ->
  ribbon_on start stop inner outer ->
  sumn (outer / inner) = (stop - start) + (nth 0 outer start - nth 0 inner stop).
Proof.
move=> partinn partout Hrib.
have Hincl : included inner outer.
  by apply/ribbon_included/ribbonP => //; exists start; exists stop.
rewrite (sumn_diff_shape Hincl).
have /sumn_nth_le -> := size_included Hincl.
rewrite (sumn_nth_le (leqnn (size outer))).
have [Hsi Hsis Hs His] := Hrib.
have lt_stop := ribbon_on_stop_lt partout Hrib.
rewrite (big_cat_nat _ (n := stop.+1)) //= addnC.
rewrite big_nat (eq_bigr (fun i => nth 0 inner i)) -?big_nat; first last.
  by move=> i /andP[+ _]; apply: Hsi.
rewrite {Hsi} [X in _ - X](big_cat_nat _ (n := stop.+1)) //=.
rewrite addnC [X in _ - X]addnC subnDA addnK.
have less := ribbon_on_start_stop Hrib.
have := less; rewrite -ltnS => /ltnW less1.
rewrite (big_cat_nat _ (n := start)) //=.
rewrite big_nat (eq_bigr _ His) {His} -big_nat.
rewrite [X in _ - X](big_cat_nat _ (n := start)) //=.
rewrite addnC subnDA addnK.
move: less; rewrite leq_eqVlt => /orP [/eqP Hss|ltss].
  by rewrite Hss !big_nat1 subnn add0n.
rewrite big_nat_recl ?(ltnW ltss) //.
rewrite big_nat (eq_bigr _ Hsis) -big_nat.
rewrite (eq_bigr (fun i => 1 + nth 0 inner i)); last by move=> i _; rewrite add1n.
rewrite big_split /= big_nat_recr ?(ltnW ltss) //= addnA subnDA addnK.
rewrite addnC sum_nat_const_nat muln1.
move/is_part_ijP : partinn => [_ /(_ _ _ (ltnW ltss))].
by move=> /leq_trans/(_ (ltnW Hs))/addnBA ->.
Qed.


Fixpoint startrem acc sh nbox pos :=
  if (pos, sh) is (p.+1, s0 :: s) then
    let c := nth 0 s p + nbox in
    let cpos := s0 + pos in
    if c >= cpos then (acc, c - cpos)  (* c == cpos -> error *)
    else startrem acc.+1 s nbox p
  else (acc + (pos - nbox), nbox - pos).  (* nbox <= pos -> error *)

(* Spec :                                    *)
(* 0 < rem == Success                        *)

Lemma startrem_acc_geq acc sh nbox pos : acc <= (startrem acc sh nbox pos).1.
Proof.
elim: pos sh acc => [|p IHpos] [|s0 s] acc /=; rewrite ?leqnn ?leq_addr //.
case: startrem (IHpos s acc.+1) => [start rem] /= /ltnW Has /=.
by case: (leqP (s0 + _) _).
Qed.

Lemma startrem_leq_pos sh nbox pos : (startrem 0 sh nbox pos).1 <= pos.
Proof.
rewrite -{2}(addn0 pos).
elim: pos sh (0) => [|p IHpos] [|s0 s] acc /=; rewrite /= ?addn0 ?add0n //.
  by rewrite addnC leq_add2r leq_subr.
case: startrem (IHpos s acc.+1) => [start rem] /=.
case: (leqP (s0 + _) _) => [_ _ | H] /=; first by rewrite leq_addl.
by rewrite addSnnS.
Qed.
Lemma startrem_leq_size sh nbox pos :
  let (start, rem) := startrem 0 sh nbox pos in
  0 < rem -> start <= size sh.
Proof.
rewrite -(addn0 (size sh)).
elim: pos sh {1 3}(0) => [|p IHpos] [|s0 s] acc /=;
  rewrite /= ?addn0 ?add0n ?leq_addl//.
  move=> /(leq_ltn_trans (leq0n _)).
  rewrite subn_gt0 => /ltnW; rewrite -subn_eq0 => /eqP ->.
  by rewrite addn0.
case: startrem (IHpos s acc.+1) => [start rem] /=.
case: (leqP (s0 + _) _) => [_ _ H | _] /=; first by rewrite leq_addl.
by rewrite addSnnS.
Qed.
Lemma startrem_leq sh nbox pos :
  let (start, rem) := startrem 0 sh nbox pos in
  0 < rem -> start <= minn pos (size sh).
Proof.
move: (startrem_leq_pos sh nbox pos) (startrem_leq_size sh nbox pos).
case: startrem => [start rem]// lespos /[apply].
by rewrite leq_min {}lespos => ->.
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

Lemma eq_interv_part sh st1 st2 v :
  is_part sh ->
  nth 0 sh st1.+1 <= st1 + v <= nth 0 sh st1 ->
  nth 0 sh st2.+1 <= st2 + v <= nth 0 sh st2 ->
  st1 = st2.
Proof.
wlog H12 : st1 st2 / st1 <= st2.
  move=> Hwlog; case: (leqP st1 st2); first exact: Hwlog.
  by move=> /ltnW/Hwlog H +{}/H => +H => {}/H /(_ _)/esym.
move=> /is_part_ijP[_ psh] /andP[Hs1 _] /andP[_ H2s].
apply anti_leq; rewrite H12 /= -(leq_add2r v).
move: H12; rewrite leq_eqVlt => /orP[/eqP -> // | lt12].
exact: (leq_trans H2s (leq_trans (psh _ _ lt12) Hs1)).
Qed.

Lemma startrem_accP acc sh nbox pos :
  is_part sh ->
  let (start, rem) := startrem acc sh nbox pos in
  0 < rem -> (* Success *)
  (start == acc) || (nth 0 sh (start - acc) + rem <= nth 0 sh (start - acc).-1).
Proof.
elim: pos sh => [|p IHpos] [|s0 s] in acc *; rewrite /= ?sub0n ?addn0 ?eqxx //.
  rewrite subn_gt0 => _ /ltnW; rewrite -subn_eq0 => /eqP ->.
  by rewrite addn0 eqxx.
move=> /andP[Hhead Hpart].
move/(_ s acc.+1 Hpart): IHpos => /=.
have:= startrem_acc_geq acc.+1 s nbox p.
have:= startrem_accE acc.+1 s nbox p.
case: startrem => [start rem]/= Heq Hstart Hrec.
case (ltnP 0 rem) => [Hok | {Heq Hrec}].
  move/(_ Hok): Hrec => /orP[/eqP eqstart | Hleq {Heq}]/=.
    case: (leqP (s0 + _) _) => [_ | Hlt _]; first by rewrite eqxx.
    apply/orP; right; rewrite eqstart subSn // subnn /=.
    rewrite eqstart subnn addn0 in Heq.
    by move: Hlt; rewrite -{}Heq addnS ltnS addnAC leq_add2r.
  case: (leqP (s0 + _) _) => [_ | _ _]; first by rewrite eqxx.
  apply/orP; right.
  move: Hstart Hleq; rewrite subnS.
  rewrite -subn_gt0 => []; case: (start - acc) => //= [[|n]] //= _.
  by move/leq_trans; apply; case: s Hhead Hpart.
rewrite leqn0 => /eqP ->.
case: (leqP (s0 + _) _) => [_ | _ _]; first by rewrite eqxx.
rewrite addn0; apply/orP; right.
move: Hstart; rewrite -subn_gt0 => [].
case: (start - acc) => // [[|i]] _ /=; first by case: s Hhead {Hpart}.
by move/is_partP: Hpart => [_]; apply.
Qed.

Lemma startrem0P acc sh nbox pos :
  nth 0 sh 0 + pos <= nth 0 sh pos + nbox ->
  startrem acc sh nbox pos = (acc, nth 0 sh pos + nbox - (nth 0 sh 0 + pos)).
Proof.
case: sh pos => [|s0 sh] [|pos]//=; nat_norm => //.
- by rewrite -subn_eq0 => /eqP ->; rewrite addn0.
- by rewrite subn0 addKn.
- by move=> ->.
Qed.

Lemma ribbon_on0_startrem stop inner outer acc :
  is_part inner ->
  is_part outer ->
  ribbon_on 0 stop inner outer ->
  startrem acc inner (sumn (outer / inner)) stop =
  (acc, nth 0 outer 0 - nth 0 inner 0).
Proof.
move=> partinn partout Hrib.
case: outer partout Hrib => [_ [_ _] | out0 out]; first by rewrite nth_nil.
case: inner partinn => [|inn0 inn].
  move => _ /=/andP[Hout0 partout] [Hsi His].
  rewrite nth_nil /= => H0 _; rewrite !subn0.
  case: stop Hsi His => [|st /= Hsi His].
    case: out partout {Hout0} => [|out1 out].
      by move=> _ _ _; rewrite !(sub0n, addn0, subn0).
    move=> /part_head_non0 /= /negbTE Hout1 /(_ 1 (ltnSn 0)) /= /eqP.
    by rewrite Hout1.
  suff -> : out = nseq st.+1 1.
    rewrite sumn_nseq mul1n; have := leq_addl out0 st.+1.
    by rewrite -subn_eq0 => /eqP ->; rewrite addn0 addnK.
  apply/eqP/(part_eqP partout (is_part_nseq1 _)) => i.
  rewrite nth_nseq; case: ltnP => [/His ->|]; first by rewrite nth_nil.
  by rewrite -ltnS => /Hsi /=.
move=> partinn partout Hrib.
rewrite (ribbon_on_sumn partinn partout Hrib) subn0 /=.
case: stop Hrib => [|st] [Hsi Hsis /= H0 _].
  by rewrite sub0n addn0 subn0 add0n.
rewrite [st.+1 + _]addnC !addnA leq_add2r subnKC ?(ltnW H0) /=; first last.
  apply: (leq_trans _ (ltnW H0)).
  by move: partinn => /is_part_ijP [_] /(_ _ _ (leq0n st.+1)) /=.
by rewrite subnDr.
Qed.

Lemma ribbon_on_startrem_acc start stop inner outer acc :
  is_part inner ->
  is_part outer ->
  ribbon_on start stop inner outer ->
  startrem acc inner (sumn (outer / inner)) stop =
  (acc + start, nth 0 outer start - nth 0 inner start).
Proof.
elim: start stop inner outer acc => [|start IHstart] stop inner outer acc.
  by rewrite addn0; apply: ribbon_on0_startrem.
case: outer => [|out0 out].
  by move=> _ _ [_ _]; rewrite nth_nil.
case: inner => [|inn0 inn].
  move=> _ /part_head_non0 => /= Hout0 [_ _ _] /(_ 0 (ltn0Sn _)) /= /eqP.
  by rewrite (negbTE Hout0).
move=> partinn partout.
have:= (is_part_ijP _ partout) => [][_ /(_ 0 start.+1 (leq0n _)) /= Hstout0].
move: partinn partout => /=/andP[Hinn0 partinn] /andP[Hout0 partout] Hrib.
case: stop Hrib (ribbon_on_start_stop Hrib) => [//|stop].
rewrite ribbon_onSS => [[/eqP H0 Hrib]] _.
rewrite H0 subnn add0n {1}(ribbon_on_sumn partinn partout Hrib).
have lest : nth 0 out start >= nth 0 inn stop.
  have:= is_part_ijP _ partinn => [][_].
  move=> /(_ _ _ (ribbon_on_start_stop Hrib))/leq_trans; apply.
  have : included inn out.
    by apply/ribbon_included/ribbonP => //; exists start; exists stop.
  by move/includedP => [_]; apply.
rewrite (addnBA _ lest) subnKC; last exact: (leq_trans lest (leq_addl _ _)).
rewrite leqNgt addnS ltnS addnC leq_add /= ?leq_subr //.
by rewrite IHstart // !(addSn, addnS).
Qed.

Lemma ribbon_on_startrem start stop inner outer :
  is_part inner ->
  is_part outer ->
  ribbon_on start stop inner outer ->
  startrem 0 inner (sumn (outer / inner)) stop =
  (start, nth 0 outer start - nth 0 inner start).
Proof.
move/ribbon_on_startrem_acc => H{}/H H{}/H ->.
by rewrite add0n.
Qed.

Lemma ribbon_startrem inner outer :
  is_part inner -> is_part outer -> ribbon inner outer ->
  let min := mindropeq inner outer in
  let height := ribbon_height inner outer in
  startrem 0 inner (sumn (outer / inner)) (mindropeq inner outer).-1 =
  (min - height, nth 0 outer (min - height) - nth 0 inner (min - height)).
Proof.
move=> partinn partout Hrib.
have /= := ribbon_mindropeq partinn partout Hrib.
by move/(ribbon_on_startrem partinn partout) ->.
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


Section NThAddRibbon.

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
have:= startrem_accP 0 nbox stop Hpart; rewrite {}Hstartrem => /(_ Hrem) Hs.
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

End NThAddRibbon.


Section Tests.

Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 0 0 2 = [:: 4; 2; 1; 1].
Proof. by []. Abort.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 1 1 2 = [:: 2; 4; 1; 1].
Proof. by []. Abort. (* Not a ribbon. just for testing *)
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 0 1 2 = [:: 4; 3; 1; 1].
Proof. by []. Abort.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 0 2 2 = [:: 4; 3; 3; 1].
Proof. by []. Abort.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 2 2 1 = [:: 2; 2; 2; 1].
Proof. by []. Abort.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 2 3 1 = [:: 2; 2; 2; 2].
Proof. by []. Abort.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 2 4 1 = [:: 2; 2; 2; 2; 2].
Proof. by []. Abort.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 2 5 1 = [:: 2; 2; 2; 2; 2; 1].
Proof. by []. Abort.
Goal add_ribbon_start_stop [:: 2; 2; 1; 1] 2 6 1 = [:: 2; 2; 2; 2; 2; 1; 1].
Proof. by []. Abort.

Goal startrem 0 [:: 2; 2; 1; 1] 2 0 = (0, 2).
Proof. by []. Abort.
Goal add_ribbon [:: 2; 2; 1; 1] 2 0 = Some ([:: 4; 2; 1; 1], 1).
Proof. by []. Abort.
Goal startrem 0 [:: 2; 2; 1; 1] 2 1 = (0, 1).
Proof. by []. Abort.
Goal add_ribbon [:: 2; 2; 1; 1] 2 1 = Some ([:: 3; 3; 1; 1], 2).
Proof. by []. Abort.

(** Tests :
[
sage: s[2, 2] * p[1]
s[2, 2, 1] + s[3, 2]
]
 *****)
Goal pmap (add_ribbon [:: 2; 2] 1) (iota 0 10) =
  [:: ([:: 3; 2], 1); ([:: 2; 2; 1], 1)].
Proof. by []. Abort.
(** Tests :
[
sage: s[2, 2] * p[2]
-s[2, 2, 1, 1] + s[2, 2, 2] - s[3, 3] + s[4, 2]
]
 *****)
Goal pmap (add_ribbon [:: 2; 2] 2) (iota 0 10) =
  [:: ([:: 4; 2], 1); ([:: 3; 3], 2); ([:: 2; 2; 2], 1); ([:: 2; 2; 1; 1], 2)].
Proof. by []. Abort.
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
Proof. by []. Abort.
(** Tests :
[
sage: s[2, 2] * p[5]
s[2, 2, 1, 1, 1, 1, 1] - s[2, 2, 2, 1, 1, 1] + s[3, 3, 3] - s[6, 3] + s[7, 2]
]
*****)
Goal pmap (add_ribbon [:: 2; 2] 5) (iota 0 8) =
  [:: ([:: 7; 2], 1); ([:: 6; 3], 2); ([:: 3; 3; 3], 3);
      ([:: 2; 2; 2; 1; 1; 1], 4); ([:: 2; 2; 1; 1; 1; 1; 1], 5)].
Proof. by []. Abort.
(** Tests :
[
sage: s[2, 2, 1] * p[5]
s[2, 2, 1, 1, 1, 1, 1, 1] - s[2, 2, 2, 2, 1, 1] + s[4, 3, 3] - s[6, 3, 1] + s[7, 2, 1]
]
*****)
Goal pmap (add_ribbon [:: 2; 2; 1] 5) (iota 0 8) =
  [:: ([:: 7; 2; 1], 1); ([:: 6; 3; 1], 2); ([:: 4; 3; 3], 3);
      ([:: 2; 2; 2; 2; 1; 1], 4); ([:: 2; 2; 1; 1; 1; 1; 1; 1], 5)].
Proof. by []. Abort.
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
Proof. by []. Abort.

Goal let sh := [:: 2; 2] in
     all (fun p => ribbon sh p.1) (pmap (add_ribbon sh 1) (iota 0 8)).
Proof. by []. Abort.
Goal let sh := [:: 2; 2] in
     all (fun p => ribbon sh p.1) (pmap (add_ribbon sh 5) (iota 0 8)).
Proof. by []. Abort.
Goal let sh := [:: 2; 2; 1] in
     all (fun p => ribbon sh p.1) (pmap (add_ribbon sh 5) (iota 0 8)).
Proof. by []. Abort.
Goal let sh := [:: 5; 5; 2; 1; 1] in
     all (fun p => ribbon sh p.1) (pmap (add_ribbon sh 7) (iota 0 15)).
Proof. by []. Abort.

End Tests.


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

Lemma add_ribbon_height : hgt = ribbon_height sh res.
Proof.
move: is_part_add_ribbon.
move: Hret (startrem_leq sh nbox.+1 pos); rewrite /add_ribbon.
case: startrem => start [|rem]//= [<- <-] /(_ (lt0n _)) Hstart Hpart.
apply: ribbon_on_height => //.
exact: add_ribbon_start_stopP.
Qed.

End Spec.


Lemma ribbon_on_addE start stop inner outer :
  is_part inner -> is_part outer -> ribbon_on start stop inner outer ->
  add_ribbon_start_stop inner start stop (nth 0 outer start - nth 0 inner start) =
  outer.
Proof.
move=> partinn partout Hrib.
have Hstartrem := ribbon_on_startrem partinn partout Hrib.
have := Hrib => [[_ _ Hs _]]; rewrite -subn_gt0 in Hs.
have := startrem_leq inner (sumn (outer / inner)) stop.
rewrite Hstartrem => /(_ Hs) lesmin.
apply/eqP/(part_eqP (is_part_add_ribbon_start_stop lesmin partinn Hs Hstartrem)
                    partout) => i.
move: Hrib => [Hsi Hsis {}Hs His].
case: (ltnP i start) => [ltistart | lestarti].
  by rewrite !nth_add_ribbon_lt_start // His.
move: lestarti; rewrite leq_eqVlt => /orP[/eqP Hi|ltstarti].
  by rewrite -Hi nth_add_ribbon_start // subnKC // (ltnW Hs).
case: i ltstarti => // i /ltnSE ltstarti.
case: (ltnP i stop) => [ltis | lesi].
  have {ltstarti} Hi : start <= i < stop by rewrite ltstarti ltis.
  by rewrite !nth_add_ribbon_in // Hsis.
by rewrite nth_add_ribbon_stop_lt // Hsi.
Qed.

Lemma ribbon_addE inner outer :
  is_part inner -> is_part outer -> ribbon inner outer ->
  add_ribbon inner (sumn (outer / inner)) (mindropeq inner outer).-1 =
  Some (outer, ribbon_height inner outer).
Proof.
move=> partinn partout /(ribbonP partinn partout) [start][stop] Hrib.
rewrite -(ribbon_on_stopE partinn partout Hrib).
rewrite /add_ribbon (ribbon_on_startrem partinn partout Hrib) subn_gt0.
have := Hrib => [][_ _ -> _]; congr (Some (_, _)); first last.
  by rewrite (ribbon_on_height partinn partout).
exact: ribbon_on_addE.
Qed.
