(** * Combi.Combi.skewtab : Skew Tableaux *)
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
(** * Skew tableau and yamanouchi words:

- [is_skew_yam inn out y] == [y ++ y0] is Yamanouchi of evaluation [out] for
         any [y0] of evaluation [inn].
- [skew_dominate s u v] == the row [u] dominate the row [v] when shifted by [s].
- [is_skew_tableau inn t] == [t] is a skew tableau with inner shape [t].
- [skew_reshape inn out s] == reshape the sequence [s] by the skew shape [out/inn].
- [filter_leqX_tab n t] == keeps only the entries greater than [n] in [t].
- [join_tab t st] == join the tableau [t] with the skew tableau [st].
       this gives a tableau if the inner shape of [st] is the shape of [t] and
       the entries of [t] are smaller than the entries of [st].
- [hb_strip inn out] == [inn/out] is an horizontal border strip.
- [vb_strip inn out] == [inn/out] is a vertical border strip.
- [std_of_tab t] == the standardized tableau of [t].
******)


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple finfun finset bigop path.

Require Import tools partition Yamanouchi ordtype tableau std stdtab.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N.

Definition is_skew_yam innev outev sy :=
  (forall y, is_yam_of_eval innev y -> is_yam_of_eval outev (sy ++ y)).

Lemma skew_yam_nil sh : is_skew_yam sh sh [::].
Proof. by rewrite /is_skew_yam => y; rewrite cat0s. Qed.

Lemma skew_nil_yamE eval y : is_yam_of_eval eval y -> is_skew_yam [::] eval y.
Proof.
move=> Hy z; rewrite {1}/is_yam_of_eval => /andP [] _ /eqP Hz.
have:= evalseq_eq_size z; rewrite Hz /= => /esym/eqP/nilP ->.
by rewrite cats0.
Qed.

Lemma skew_yam_cat sha shb shc y z :
  is_skew_yam sha shb y -> is_skew_yam shb shc z -> is_skew_yam sha shc (z ++ y).
Proof. by rewrite /is_skew_yam => Hy Hz x /Hy /Hz; rewrite catA. Qed.

Lemma is_skew_yamE innev outev z y0 :
  is_yam_of_eval innev y0 ->
  is_yam_of_eval outev (z ++ y0) ->
  is_skew_yam innev outev z.
Proof.
move=> Hy0 Hcat y Hy.
move: Hy0 Hy Hcat.
rewrite /is_yam_of_eval => /andP [] Hy0 /eqP <- /andP [] Hy /eqP Hsh /andP [].
elim: z outev => [| z0 z IHz /=] outev Hcat Hshcat.
  by rewrite Hy Hsh Hshcat.
move: Hcat => /andP [] Hincr0 Hcat0.
move/(_ _ Hcat0 (eq_refl _)) : IHz => /andP [] -> /eqP ->.
by rewrite Hincr0 Hshcat.
Qed.

Lemma is_part_skew_yam sha shb y :
  is_part sha -> is_skew_yam sha shb y -> is_part shb.
Proof.
move=> /hyper_yam_of_eval Ha /(_ _ Ha).
by rewrite /is_yam_of_eval => /andP [] /is_part_eval_yam H /eqP <-.
Qed.

Lemma skew_yam_catrK sha shb shc y z :
  is_part sha ->
  is_skew_yam sha shb y ->
  is_skew_yam sha shc (z ++ y) ->
  is_skew_yam shb shc z.
Proof.
move=> /hyper_yam_of_eval Ha Hy Hcat.
apply (is_skew_yamE (Hy _ Ha)).
rewrite catA; exact: Hcat.
Qed.

Lemma skew_yam_consK sha shc i y :
  is_part sha -> is_skew_yam sha shc (i :: y) ->
  is_skew_yam sha (decr_nth shc i) y.
Proof.
move=> Hpart /(_ _ (hyper_yam_of_eval Hpart)) /=.
rewrite /is_yam_of_eval /= => /andP [] /andP [] Hincr Hyam /eqP Hc.
apply (is_skew_yamE (hyper_yam_of_eval Hpart)).
rewrite /is_yam_of_eval Hyam /= -Hc.
by rewrite (incr_nthK (is_part_eval_yam Hyam) Hincr).
Qed.

Lemma skew_yam_catK sha shc y z :
  is_part sha -> is_skew_yam sha shc (y ++ z) ->
  { shb | is_skew_yam sha shb z & is_skew_yam shb shc y }.
Proof.
move=> Hpart.
elim: y z shc => [| y0 y IHy ] z shc Hz /=.
  exists shc; first exact: Hz.
  exact: skew_yam_nil.
move/(_ _ _ (skew_yam_consK Hpart Hz)) : IHy => [shb] Hskz Hy.
exists shb; first exact: Hskz.
exact: (skew_yam_catrK Hpart Hskz Hz).
Qed.

Lemma skew_yam_included sha shb y :
  is_part sha -> is_skew_yam sha shb y -> included sha shb.
Proof.
move=> Hpart.
elim: y shb => [| y0 y IHy] shb /= Hskew.
  move/(_ _ (hyper_yam_of_eval Hpart)) : Hskew.
  rewrite cat0s /is_yam_of_eval (evalseq_hyper_yam Hpart) => /andP [] _ /eqP ->.
  exact: included_refl.
move/(_ _ (skew_yam_consK Hpart Hskew)) : IHy => Hrec.
have/(_ _ (hyper_yam_of_eval Hpart)) := Hskew.
rewrite /is_yam_of_eval => /andP [] /is_rem_corner_yam Hcorn /eqP Hb.
rewrite Hb in Hcorn.
have:= included_incr_nth (decr_nth shb y0) y0.
rewrite (decr_nthK (is_part_skew_yam Hpart Hskew) Hcorn).
exact: included_trans.
Qed.

Section Dominate.

Variable T : inhOrdType.
Notation Z := (inhabitant T).

Implicit Type u v : seq T.

Definition skew_dominate sh u v := dominate (drop sh u) v.

Lemma skew_dominate0 : skew_dominate 0 =2 (@dominate T).
Proof using. by move=> u v /=; rewrite /skew_dominate drop0. Qed.

Lemma skew_dominate_take n sh u v :
  skew_dominate sh u (take n v) -> skew_dominate sh u v.
Proof using.
move/dominateP => [].
rewrite size_take -/(minn _ _) => Hsize Hdom.
apply/dominateP; split.
- by apply (leq_trans Hsize); exact: geq_minr.
- move=> i Hi; move/(_ i Hi) : Hdom.
  rewrite nth_take //.
  by have:= leq_trans Hi Hsize; rewrite leq_min => /andP [].
Qed.

Lemma skew_dominate_no_overlap sh u v :
  size u <= sh -> skew_dominate sh u v.
Proof using.
by rewrite /skew_dominate => /drop_oversize ->; exact: dominate_nil.
Qed.

Lemma skew_dominate_consl sh l u v :
  skew_dominate sh u v -> skew_dominate sh.+1 (l :: u) v.
Proof using.
move/dominateP => [] Hsize Hdom.
apply/dominateP; split; first by move: Hsize; rewrite !size_drop.
by move=> i /= /Hdom.
Qed.

Lemma skew_dominate_cut sh u v :
  skew_dominate sh u v = skew_dominate sh u (take (size u - sh) v).
Proof using.
rewrite /skew_dominate /dominate; congr (_ &&_ ).
- rewrite size_drop size_take -/(minn _ _).
  case: leqP => [/minn_idPl -> | H]; first by rewrite leqnn.
  have /minn_idPr -> := ltnW H.
  by rewrite leqNgt H.
- apply eq_in_all => i; rewrite mem_iota add0n /= size_drop => Hi.
  by rewrite nth_take.
Qed.

Fixpoint is_skew_tableau inner t :=
  if t is t0 :: t'
  then [&& head 0 inner + size t0 != 0, (* forbid empty rows *)
        is_row t0,
        skew_dominate ((head 0 inner) - (head 0 (behead inner)))
                      (head [::] t') t0 & is_skew_tableau (behead inner) t']
  else inner == [::].

Lemma is_skew_tableauP inner t :
  reflect
    [/\ size inner <= size t,
     forall i, i < size t -> nth 0 inner i + size (nth [::] t i) != 0,
     forall i, is_row (nth [::] t i) &
     forall i, skew_dominate ((nth 0 inner i) - (nth 0 inner i.+1))
                             (nth [::] t i.+1) (nth [::] t i)]
    (is_skew_tableau inner t).
Proof using.
apply (iffP idP).
- elim: t inner => [| t0 t IHt] /= inner.
    by move=> /eqP ->; split=> // i; rewrite !nth_default.
  case: inner => [| inn0 inn] /and4P [] Ht0 Hrow0 Hdom0 /=
                              /IHt [] Hsz Hnnil Hrow Hdom.
  + split.
    * by [].
    * case=> [_| i] /=; first exact: Ht0.
      by rewrite ltnS => /Hnnil; rewrite nth_default.
    * by case.
    * case=> [| i] /=; first by move: Hdom0; rewrite /= subn0.
      by move/(_ i) : Hdom => /=; rewrite nth_default // subn0.
  + split.
    * exact: Hsz.
    * case=> [_| i] /=; last by rewrite ltnS; exact: Hnnil.
      by move: Ht0.
    * by case.
    * case=> [| i] /=; first exact: Hdom0.
      by move/(_ i) : Hdom => /=; case inn; rewrite // nth_default.
- elim: t inner => [| t0 t IHt] inner //= [] Hsz Hnnil Hrow Hdom.
    by move: Hsz; rewrite leqn0 => /nilP ->.
  apply/and4P; split.
  + by have /Hnnil := ltn0Sn (size t); case inner.
  + by rewrite -/(nth [::] (t0 :: t) 0); exact: Hrow.
  + by move: Hdom; case t => //= t1 tt /(_ 0); case inner.
  + apply IHt; split => [| i Hi | i | i].
    * by move: Hsz; case inner.
    * move: Hi; rewrite -ltnS => /Hnnil.
      by case inner; rewrite //= [nth 0 [::] i]nth_default.
    * exact: (Hrow i.+1).
    * move/(_ i.+1) : Hdom.
      by case inner => [|_ [| inn]] //=; rewrite [nth 0 [::] i]nth_default.
Qed.

Lemma is_skew_tableau0 : is_skew_tableau [::] =1 is_tableau.
Proof using.
elim => //= t0 t IHt; rewrite add0n subn0 skew_dominate0 IHt.
by case t0.
Qed.

Lemma is_skew_tableau_pad0 inner t :
  is_skew_tableau inner t = is_skew_tableau (pad 0 (size t) inner) t.
Proof using.
elim: t inner => [| t0 t IHt] /= inner; first by rewrite cats0.
case: inner => [| inn0 inn] /=.
  rewrite (IHt [::]) /= add0n.
  by rewrite !subn0.
rewrite (IHt inn) subSS /=.
suff -> : head 0 (inn ++ nseq (size t - size inn) 0) = head 0 inn by [].
by case: inn => //=; case: (size t - 0).
Qed.

Definition skew_reshape (inner outer : seq nat) (s : seq T) :=
  rev (reshape (rev (diff_shape inner outer)) s).

Lemma size_skew_reshape inner outer s :
  size (skew_reshape inner outer s) = size outer.
Proof using.
by rewrite /skew_reshape size_rev size_reshape size_rev size_diff_shape.
Qed.

Lemma shape_skew_reshape inner outer s :
  included inner outer ->
  size s = sumn (diff_shape inner outer) ->
  shape (skew_reshape inner outer s) = diff_shape inner outer.
Proof using.
rewrite /shape /skew_reshape.
elim: inner outer s => [| inn0 inn IHinn] /= outer s.
  move=> _; elim: outer s => [s /eqP/nilP -> //= | out0 out IHout] /= s Hsz.
  rewrite rev_cons reshape_rcons; last by rewrite sumn_rev addnC -Hsz.
  rewrite rev_rcons /= IHout.
  - by rewrite size_drop sumn_rev Hsz addnK.
  - by rewrite sumn_rev size_take_leq Hsz leq_addl.
case: outer s => [//= | out0 out] /= s /andP [] H0 Hincl Hsz.
rewrite rev_cons reshape_rcons; last by rewrite sumn_rev addnC -Hsz.
rewrite rev_rcons /= size_drop sumn_rev.
rewrite (IHinn _ _ Hincl); first by rewrite Hsz addnK.
by rewrite size_take_leq Hsz leq_addl.
Qed.

Lemma to_word_skew_reshape inner outer s :
  included inner outer ->
  size s = sumn (diff_shape inner outer) ->
  to_word (skew_reshape inner outer s) = s.
Proof using.
rewrite /skew_reshape /to_word revK.
elim: inner outer s => [| inn0 inn IHinn] /= outer s.
  move=> _; elim: outer s => [s /eqP/nilP -> // | out0 out IHout] /= s Hsz.
  rewrite rev_cons reshape_rcons; last by rewrite sumn_rev addnC -Hsz.
  rewrite flatten_rcons IHout; first by rewrite cat_take_drop.
  by rewrite sumn_rev size_take_leq Hsz leq_addl.
case: outer s => //= out0 out s /andP [] H0 Hincl Hsz.
rewrite rev_cons reshape_rcons; last by rewrite sumn_rev addnC -Hsz.
rewrite flatten_rcons IHinn.
- by rewrite cat_take_drop.
- exact: Hincl.
- by rewrite sumn_rev size_take_leq Hsz leq_addl.
Qed.

Lemma skew_reshapeK inner t :
  size inner <= size t ->
  skew_reshape inner (outer_shape inner (shape t)) (to_word t) = t.
Proof using.
rewrite -(size_map size) => H.
by rewrite /skew_reshape (outer_shapeK H) -shape_rev flattenK revK.
Qed.

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
  + have:= H 0 => /andP []; rewrite nth_nil leqn0 => /eqP {H} H _.
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
  + by move=> /andP [H0 /IHout{IHout}Hrec]
               /andP [Hout /Hrec{Hrec}Hrec]
               /andP [Hinn /Hrec{Hrec}Hrec] [|i] //=.
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
    * move: Hpart => /andP [] H0 /IHout{IHout}Hrec
                      /andP [] _  /Hrec{Hrec}Hrec H.
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

Lemma row_dominate u v :
  is_row (u ++ v) -> dominate u v -> u = [::].
Proof using.
case: u => [//= | u0 u] /=.
case: v => [//= | v0 v] /= /order_path_min Hpath.
have {Hpath} /Hpath /allP Hall : transitive (@leqX_op T)
  by move=> i j k; apply leqX_trans.
move=> /dominateP [] /=.
rewrite ltnS => Hsize /(_ _ (ltn0Sn (size u))) /= H0; exfalso.
have /Hall : v0 \in u ++ v0 :: v by rewrite mem_cat in_cons eq_refl /= orbT.
by rewrite leqXNgtnX H0.
Qed.

Lemma row_hb_strip inner t :
  is_part inner ->
  is_skew_tableau inner t -> is_row (to_word t) ->
  hb_strip inner (outer_shape inner (shape t)).
Proof using.
rewrite /outer_shape.
elim: t inner => [| t0 t IHt] /= inner Hpart.
  by rewrite cats0 => /eqP -> _ /=.
case: inner Hpart => [_ | inn0 inn] /=.
  rewrite subn0 add0n to_word_cons => /and4P [] Ht0 _.
  case: t {IHt} => //= t1 t.
  rewrite to_word_cons add0n subn0.
  rewrite /skew_dominate drop0 => Hdom /and4P [] Ht1 _ _ _.
  rewrite -catA => /is_row_catR Hrow.
  by exfalso; move: Ht1; rewrite (row_dominate Hrow Hdom).
move=> /andP [Hhead Hpart].
rewrite to_word_cons subSS => /and4P [_ _ Hdom /IHt{IHt}Hrec] Hrow.
move/(_ Hpart (is_row_catL Hrow)) : Hrec => -> {Hpart}.
rewrite leq_addr !andbT.
case: t Hdom Hrow => [| t1 t]/=; first by case: inn {Hhead}.
case: inn Hhead => [_ | inn1 inn] /=.
  rewrite add0n subn0 to_word_cons -catA.
  rewrite /skew_dominate => Hdom /is_row_catR.
  rewrite -(cat_take_drop inn0 t1) -catA => /is_row_catR /row_dominate H1.
  rewrite (H1 Hdom) cats0 size_take.
  by case ltnP => [/ltnW|].
rewrite /skew_dominate to_word_cons -catA => Hhead Hdom.
rewrite -(cat_take_drop (inn0 - inn1) t1) -catA => /is_row_catR.
move=> /is_row_catR/row_dominate H1.
rewrite (H1 Hdom) cats0 size_take.
case ltnP => [_|]; first by rewrite subnKC.
by rewrite -(leq_add2l inn1) subnKC.
Qed.

Lemma hb_strip_rowE inner outer u :
  is_part inner -> is_part outer ->
  is_row u -> size u = sumn (diff_shape inner outer) ->
  included inner outer &&
           is_skew_tableau inner (skew_reshape inner outer u) =
  hb_strip inner outer.
Proof using.
move=> Hpartin Hpartout Hrow Hsize.
apply/andP/idP => [[] Hincl /(row_hb_strip Hpartin) | Hstrip].
- rewrite (to_word_skew_reshape Hincl Hsize) => /(_ Hrow).
  by rewrite (shape_skew_reshape Hincl Hsize) (diff_shapeK Hincl).
- split; first exact: hb_strip_included.
  elim: inner outer Hpartout u Hsize Hrow Hstrip {Hpartin} =>
         [| inn0 inn IHinn] /= [//=| out0 out].
    move=> Hpart u Hsize Hrow Hout.
    move: Hout Hsize Hpart => /eqP -> /=.
    rewrite addn0 add0n => Hsize.
    rewrite -Hsize take_size => /andP [] /lt0n_neq0 -> _.
    by rewrite Hrow eq_refl.
  set dsh := diff_shape inn out.
  move=> Hpartout /= u Hsize Hrow /andP [] /andP [] Hhead0 H0 Hstrip.
  rewrite /skew_reshape /= rev_cons reshape_rcons; first last.
    by rewrite sumn_rev Hsize /= addnC.
  rewrite rev_rcons -/dsh /=.
  apply/and4P; split.
  - rewrite size_drop sumn_rev Hsize /= addnK (subnKC H0).
    exact: part_head_non0 Hpartout.
  - exact: is_row_drop.
  - apply skew_dominate_no_overlap.
    rewrite -/(skew_reshape _ _ _) sumn_rev.
    have : size (take (sumn dsh) u) = sumn dsh.
      by rewrite size_take_leq Hsize leq_addl.
    move/(shape_skew_reshape (hb_strip_included Hstrip)).
    set sh := skew_reshape _ _ _ => Hshape.
    have -> : size (head [::] sh) = head 0 (shape sh).
      by rewrite /shape; case sh.
    rewrite Hshape {IHinn Hsize Hrow sh Hshape Hstrip dsh}.
    case: inn => [| inn1 inn] /=; first by rewrite subn0.
    case: out Hhead0 {Hpartout} => //= out1 out H.
    exact: leq_sub2r.
  - rewrite -/(skew_reshape _ _ _); apply IHinn.
    + by move: Hpartout => /= /andP [].
    + by rewrite sumn_rev size_take_leq Hsize leq_addl.
    + exact: is_row_take.
    + exact: Hstrip.
Qed.

End Dominate.

Section FilterLeqGeq.

Variable T : inhOrdType.
Notation Z := (inhabitant T).

Implicit Type l : T.
Implicit Type r w : seq T.
Implicit Type t : seq (seq T).

Lemma filter_leqX_row n r :
  is_row r -> filter (leqX n) r = drop (count (gtnX n) r) r.
Proof using.
elim: r => //= r0 r IHr Hrow /=.
case: (leqXP n r0) => Hr0.
- rewrite add0n; have Hcount : count (gtnX n) r = 0.
  elim: r r0 Hr0 Hrow {IHr} => //= r1 r IHr r0 Hr0 /andP [] Hr0r1 Hpath.
  have Hr1 := leqX_trans Hr0 Hr0r1.
    by rewrite ltnXNgeqX Hr1 (IHr r1 Hr1 Hpath).
  by rewrite Hcount (IHr (is_row_consK Hrow)) Hcount drop0.
- by rewrite add1n (IHr (is_row_consK Hrow)).
Qed.

Lemma filter_leqX_dominate n r1 r0 :
  is_row r0 -> is_row r1 -> dominate r1 r0 ->
  skew_dominate ((count (gtnX n) r0) - (count (gtnX n) r1))
                (filter (leqX n) r1) (filter (leqX n) r0).
Proof using.
move=> Hrow0 Hrow1 Hdom.
have Hsize := count_gtnX_dominate n Hdom.
move: Hdom => /dominateP [Hsz Hdom].
have /eq_count Hcount : (gtnX n) =1 predC (leqX n).
  by move=> i /=; exact: ltnXNgeqX.
apply/dominateP; split.
- rewrite size_drop !size_filter.
  rewrite (subnBA _ Hsize) leq_subLR [count _ r0 + _]addnC.
  by rewrite !Hcount !count_predC.
- rewrite size_drop !size_filter => i.
  rewrite (subnBA _ Hsize) Hcount !count_predC ltn_subRL => /Hdom.
  rewrite (filter_leqX_row _ Hrow0) (filter_leqX_row _ Hrow1) !nth_drop.
  by rewrite -Hcount addnA (subnKC Hsize).
Qed.

Definition filter_leqX_tab n :=
  [fun t : (seq (seq T)) => [seq [seq x <- i | leqX n x] | i <- t]].

Lemma is_skew_tableau_filter_leqX_tmp n t :
  is_tableau t -> is_skew_tableau
                    (shape ([seq [seq x <- i | (x < n)%Ord] | i <- t]))
                    (filter_leqX_tab n t).
Proof using.
elim: t => //= t0 t IHt /and4P [Hnnil Hrow Hdom Htab].
apply/and4P; split.
- rewrite !size_filter /=.
  set p1 := (X in count X); set p2 := (X in _ + count X _).
  have /eq_count -> : p2 =1 predC p1 by move=> i /=; rewrite -leqXNgtnX.
  rewrite count_predC.
  by move: Hnnil; apply contra => /nilP ->.
- apply sorted_filter; last exact Hrow.
  by move=> a b c; exact: leqX_trans.
- case: t Hdom Htab {IHt} => //= t1 t /= Hdom /and4P [_ Hrow1 _ _] {t}.
  rewrite !size_filter.
  exact: filter_leqX_dominate.
- exact: IHt.
Qed.

Lemma filter_gtnX_first_row0 n r t :
  is_tableau t ->
  dominate (head [::] t) r ->
  [seq x <- r | (x < n)%Ord] = [::] ->
  [seq [seq x <- i | (n <= x)%Ord] | i <- t] = t.
Proof using.
elim: t r => //= t0 t IHt r.
move=> /and4P [_ Hrow Hdom Htab] Hdomr Hr.
move/(count_gtnX_dominate n) : Hdomr.
rewrite -!size_filter Hr /= leqn0 => /nilP Ht0.
rewrite (IHt t0 Htab Hdom Ht0).
rewrite (filter_leqX_row n Hrow).
by rewrite -!size_filter Ht0 /= drop0.
Qed.

Lemma filter_leqX_first_row0 n r t :
  is_tableau t ->
  dominate (head [::] t) r ->
  [seq x <- r | (x < n)%Ord] = [::] ->
  [seq [seq x <- i | (x < n)%Ord] | i <- t] = nseq (size t) [::].
Proof using.
elim: t r => //= t0 t IHt r.
move=> /and4P [_ Hrow Hdom Htab] Hdomr Hr.
move/(count_gtnX_dominate n) : Hdomr.
rewrite -!size_filter Hr /= leqn0 => /nilP Ht0.
by rewrite Ht0 (IHt t0 Htab Hdom).
Qed.

Lemma included_shape_filter_gtnX c (t : seq (seq T)) :
  is_tableau t -> included (shape (filter_gtnX_tab c t)) (shape t).
Proof.
move=> Ht; rewrite /filter_gtnX_tab.
elim: t Ht => [//= | t0 t IHt] /and4P [Hnnil Hrow Hdom Htab] /=.
case: (altP ([seq x <- t0 | (x < c)%Ord] =P [::])) => Hhead /=.
- rewrite (filter_leqX_first_row0 Htab Hdom Hhead).
  suff -> : [seq r <- nseq (size t) [::] | r != [::]] = [::] by [].
  by move=> T0; elim: (size t).
- rewrite (IHt Htab) andbT.
  by rewrite size_filter; apply: (leq_trans (count_size _ _)).
Qed.

Lemma shape_inner_filter_leqX n t :
  is_tableau t ->
  shape ([seq [seq x <- i | (x < n)%Ord] | i <- t]) =
  pad 0 (size t) (shape (filter_gtnX_tab n t)).
Proof using.
rewrite /pad /=.
elim: t => //= t0 t IHt /and4P [Hnnil0 Hrow0 Hdom Htab].
case/altP: ([seq x <- t0 | (x < n)%Ord] =P [::]) => Ht0 /=; first last.
  by rewrite subSS -(IHt Htab).
rewrite Ht0 /= {IHt}.
rewrite (filter_leqX_first_row0 Htab Hdom Ht0).
rewrite [filter _ _ ](_ : _ = [::]); last by elim: (size t).
by rewrite /= /shape map_nseq.
Qed.

Lemma is_skew_tableau_filter_leqX n t:
  is_tableau t ->
  is_skew_tableau (shape (filter_gtnX_tab n t)) (filter_leqX_tab n t).
Proof using.
move=> Htab.
rewrite is_skew_tableau_pad0 /filter_leqX_tab size_map.
rewrite -(shape_inner_filter_leqX n Htab).
exact: is_skew_tableau_filter_leqX_tmp.
Qed.

Definition join_tab s t :=
  [seq r.1 ++ r.2 | r <- zip (pad [::] (size t) s) t].

Lemma size_join_tab s t :
  size s <= size t ->
  size_tab (join_tab s t) = size_tab s + size_tab t.
Proof using.
rewrite /join_tab /size_tab.
elim: s t => [| s0 s IHs] /= t.
  by rewrite add0n subn0; elim: t => //= t0 t /= ->.
case: t => //= t0 t.
rewrite ltnS subSS => /IHs -> {IHs}.
rewrite size_cat -!addnA; congr (_ + _).
by rewrite addnA addnAC addnC.
Qed.

Lemma shape_join_tab s t :
  shape (join_tab s t) =
  ([seq r.1 + r.2 | r <- zip (pad 0 (size t) (shape s)) (shape t)])%N.
Proof using .
rewrite /shape /join_tab -map_comp.
rewrite (eq_map (f2 := (fun p => p.1 + p.2) \o
                         (fun p => (size p.1, size p.2)))); first last.
  by move=> [a b] /=; rewrite size_cat.
rewrite map_comp; congr map.
elim: t s => [| t0 t IHt] [| s0 s] //=.
  by have /= := (IHt [::]); rewrite subn0 => ->.
by rewrite IHt /= subSS.
Qed.

Lemma perm_eq_join_tab s t :
  size s <= size t ->
  perm_eq (to_word (join_tab s t)) (to_word s ++ to_word t).
Proof using.
rewrite /join_tab /=.
elim: t s => [//= | t0 t IHt] /= s; first by rewrite leqn0 => /nilP -> /=.
case: s => [_ | s0 s] /=.
  rewrite !to_word_cons {IHt}.
  rewrite [map _ _](_ : _ = t); first by exact: perm_eq_refl.
  by elim: t {t0} => //= t0 t /= ->.
rewrite ltnS subSS => /IHt{IHt}.
rewrite !to_word_cons -!/(to_word _) !catA perm_cat2r.
move: (map _ _) => m.
rewrite -(perm_cat2r s0) => /perm_eq_trans; apply.
rewrite -!catA perm_cat2l.
apply/perm_eqlP; exact: perm_catC.
Qed.

Lemma join_tab_filter n t :
  is_tableau t -> join_tab (filter_gtnX_tab n t) (filter_leqX_tab n t) = t.
Proof using.
rewrite /join_tab.
elim: t => //= t0 t IHt /and4P [Hnnil Hrow0 Hdom Htab].
case H: [seq x <- t0 | (x < n)%Ord] => [| f0 f] /=.
- rewrite {IHt} (filter_leqX_first_row0 Htab Hdom H).
  rewrite [filter _ _](_ : _ = [::]); last by elim: (size t).
  rewrite cat0s /= (filter_leqX_row n Hrow0) -!size_filter /= H /= drop0.
  congr (_ :: _).
  rewrite (filter_gtnX_first_row0 Htab Hdom H).
  by elim: t {Hdom Htab H Hrow0 Hnnil} => //= t1 t ->.
- rewrite (IHt Htab) (filter_leqX_row _ Hrow0).
  rewrite -[f0 :: _ ++ _]cat1s catA cat1s -H.
  by rewrite (filter_gtnX_row _ Hrow0) cat_take_drop.
Qed.

Lemma all_allLtn_cat (s0 s1 s : seq T) :
  all (allLtn (s0 ++ s1)) s -> all (allLtn s0) s /\ all (allLtn s1) s.
Proof using.
rewrite (eq_all (a2 := predI (allLtn s0) (allLtn s1))); first last.
  by rewrite /allLtn => i /=; rewrite all_cat.
by rewrite all_predI => /andP [].
Qed.

Lemma shape_join_tab_skew_reshape t sh w :
  included (shape t) sh ->
  size w = sumn (diff_shape (shape t) sh) ->
  shape (join_tab t (skew_reshape (shape t) sh w)) = sh.
Proof using.
move=> Hincl Hsz.
rewrite shape_join_tab size_skew_reshape shape_skew_reshape // {Hsz w}.
move: (shape t) Hincl => inner {t}.
elim: sh inner => [| s0 sh IHsh] [|in0 inn] //=.
  rewrite add0n => _ {IHsh}; congr (_ :: _) => {s0}.
  by elim: sh => //= s0 sh ->.
move=> /andP [Hin0 /IHsh {IHsh}]; rewrite /pad /= => Hrec.
by rewrite subSS (subnKC Hin0) Hrec.
Qed.

Lemma shape_join_tab_skew_reshape t sh w :
  included (shape t) sh ->
  size w = sumn (diff_shape (shape t) sh) ->
  shape (join_tab t (skew_reshape (shape t) sh w)) = sh.
Proof using.
  move=> Hincl Hsz.
  rewrite shape_join_tab size_skew_reshape shape_skew_reshape // {Hsz w}.
  move: (shape t) Hincl => inner {t}.
  elim: sh inner => [| s0 sh IHsh] [|in0 inn] //=.
    rewrite add0n => _ {IHsh}; congr (_ :: _) => {s0}.
    by elim: sh => //= s0 sh ->.
  move=> /andP [Hin0 /IHsh {IHsh}]; rewrite /pad /= => Hrec.
  by rewrite subSS (subnKC Hin0) Hrec.
Qed.

Lemma join_tab_skew s t :
  all (allLtn (to_word s)) (to_word t) ->
  is_tableau s -> is_skew_tableau (shape s) t ->
  is_tableau (join_tab s t).
Proof using.
rewrite /join_tab.
elim: s t => [| s0 s IHs] /= t.
  move => _ _ Ht; rewrite subn0 /=.
  rewrite [map _ _](_ : _ = t); last by elim: t {Ht} => //= r t ->.
  by rewrite -is_skew_tableau0.
rewrite to_word_cons => /all_allLtn_cat [Halls Halls0].
move/and4P => [Hnnils0 Hrows0 Hdoms Htabs].
case: t Halls0 Halls => //= t0 t Halls0 Halls.
move=>/and4P [Hszt0 Hrowt0 Hdomt Htabt].
apply/and4P; rewrite subSS; split.
- by move: Hnnils0; apply contra; case s0.
- move: Halls0; rewrite to_word_cons all_cat => /andP [] _.
  move=> {s Hdoms Hszt0 Hdomt IHs Htabs Htabt Halls}.
  case: s0 Hnnils0 Hrows0 => //= l0 s0 _ Hpath /allP.
  rewrite cat_path Hpath {Hpath} /=.
  case: t0 Hrowt0 => //= m0 t0 /= Hpath Hall.
  apply/andP; split; last exact Hpath.
  have {Hall} /Hall /andP [] : m0 \in m0 :: t0 by rewrite in_cons eq_refl.
  case/lastP: s0 => [/ltnXW //= | s0 sn] /= _.
  by rewrite last_rcons /allLtn all_rcons /= => /andP [] /ltnXW.
- move=> {IHs Hrows0 Hrowt0 Hnnils0 Hszt0 Halls}.
  case: s Hdoms Htabs Hdomt Htabt => [_ _| s1 s] /=.
  + rewrite subn0.
    case: t Halls0 => //= t1 t Halls0 /dominateP [Hszt Hdomt] _.
    apply/dominateP; split.
    * by move: Hszt; rewrite size_cat size_drop leq_subLR.
    * move: Halls0; rewrite !to_word_cons.
      rewrite !all_cat => /andP [/andP [_ Hallt1] Hallt0] i Hi.
      rewrite nth_cat; case ltnP => His0.
      * move: Hallt1 => /allP /(_ _ (mem_nth Z Hi)).
        by rewrite /allLtn => /allP/(_ _ (mem_nth Z His0)) /=.
      * have /Hdomt : (i - size s0) < size (drop (size s0) t1).
          by rewrite size_drop ltn_subRL (subnKC His0).
        by rewrite nth_drop (subnKC His0).
  + case: t Halls0 => //= t1 t Halls0 /dominateP [] Hszs Hdoms _.
    move: Halls0; rewrite !to_word_cons.
    rewrite !all_cat => /andP [/andP [_ Hallt1] Hallt0].
    move/dominateP => [Hszt Hdomt] _ {s t}.
    have {Hszt} Hszt : size s1 + size t1 <= size s0 + size t0.
      by move: Hszt; rewrite size_drop (subnBA _ Hszs) leq_subLR addnC.
    apply/dominateP; split; first by rewrite !size_cat.
    rewrite size_cat => i Hi.
    rewrite !nth_cat.
    case: (ltnP i (size s1)) => Hi1.
      by rewrite (leq_trans Hi1 Hszs); apply Hdoms.
    case: (ltnP i (size s0)) => Hi0.
    * move: Hallt1 => /allP Hallt1; move: Hi.
      rewrite -{1}(subnKC Hi1) ltn_add2l => /(mem_nth Z) /Hallt1 {Hallt1}.
      by rewrite /allLtn => /allP/(_ _ (mem_nth Z Hi0)).
    * have /Hdomt : i - size s0 < size (drop (size s0 - size s1) t1).
        rewrite size_drop -(ltn_add2l (size s0)) (subnKC Hi0).
        rewrite (subnBA _ Hszs) subnKC addnC //=.
        by apply (leq_trans Hi0); exact: ltnW.
      by rewrite nth_drop addnC (addnBA _ Hszs) (subnK Hi0).
- apply: (IHs _ _ Htabs Htabt).
  by move: Halls; rewrite to_word_cons all_cat => /andP [].
Qed.

End FilterLeqGeq.

Section EqInvSkewTab.

Implicit Type T : inhOrdType.

Lemma eq_inv_skew_dominate T1 T2 (u1 v1 : seq T1) (u2 v2 : seq T2) s :
  eq_inv (u1 ++ v1) (u2 ++ v2) ->
  size u1 = size u2 ->
  skew_dominate s u1 v1 -> skew_dominate s u2 v2.
Proof.
move/eq_invP; rewrite !size_cat => [] [Hsz Hinv] Hszu /dominateP [Hsz1 Hdom].
apply/dominateP; split => [| i Hi1].
  move: Hsz Hsz1; rewrite !size_drop !leq_subLR Hszu => /eqP.
  by rewrite eqn_add2l => /eqP ->.
have Hi2 : i < size (drop s u1) by move: Hi1; rewrite !size_drop Hszu.
move/(_ _ Hi2) : Hdom.
set Z1 := inhabitant T1; set Z2 := inhabitant T2.
rewrite -/Z1 -/Z2 in Hinv.
rewrite !nth_drop !ltnXNgeqX; apply contra.
move : Hi1 Hi2; rewrite !size_drop !ltn_subRL => Hi2 Hi1.
have -> : nth Z1 u1 (s + i) = nth Z1 (u1 ++ v1) (s + i) by rewrite nth_cat Hi1.
have -> : nth Z2 u2 (s + i) = nth Z2 (u2 ++ v2) (s + i) by rewrite nth_cat Hi2.
have -> : nth Z1 v1 i = nth Z1 (u1 ++ v1) (size u1 + i)
  by rewrite nth_cat ltnNge leq_addr /= addKn.
have -> : nth Z2 v2 i = nth Z2 (u2 ++ v2) (size u2 + i)
  by rewrite nth_cat ltnNge leq_addr /= addKn.
rewrite Hinv Hszu // {Hinv Z1 Z2}.
rewrite leq_add2r ltn_add2l; apply/andP; split.
- by apply ltnW; apply: (leq_ltn_trans _ Hi2); exact: leq_addr.
- by move: Hi1 Hsz1; rewrite size_drop -ltn_subRL => /leq_trans H/H{H}.
Qed.

Lemma eq_inv_is_skew_tableau_reshape_size
      inner outer T1 T2 (u1 : seq T1) (u2 : seq T2) :
  size inner = size outer -> (* complete with 0 if needed *)
  eq_inv u1 u2 -> size u1 = sumn (diff_shape inner outer) ->
  is_skew_tableau inner (skew_reshape inner outer u1) ->
  is_skew_tableau inner (skew_reshape inner outer u2).
Proof.
rewrite /skew_reshape.
elim: inner outer u1 u2 => [| inn0 inn IHinn] /=; first by case.
case=> //= out0 out u1 u2 /eqP.
move out0 after inn0; move out after inn.
set shres := diff_shape inn out.
rewrite eqSS => /eqP Hsz Hinv Hszeq /=.
have Hszres : sumn shres <= size u1 by rewrite Hszeq; apply leq_addl.
have:= Hinv => /eq_invP [Hszu _]; move Hszu after Hinv.
set r1 := take (sumn shres) u1; set r2 := take (sumn shres) u2.
have Hinvr : eq_inv r1 r2.
  move: Hinv; rewrite -{1}(cat_take_drop (sumn shres) u1)
                      -{1}(cat_take_drop (sumn shres) u2).
  by move/eq_inv_catl; apply; rewrite !size_take -Hszu.
have Hszr1 : size r1 = sumn shres by rewrite size_take_leq Hszres.
have {IHinn Hsz Hinvr Hszr1} IH := IHinn _ r1 r2 Hsz Hinvr Hszr1.
rewrite !rev_cons !reshape_rcons; first last.
- by rewrite sumn_rev addnC Hszeq.
- by rewrite -Hszu sumn_rev addnC Hszeq.
rewrite sumn_rev !rev_rcons /= !size_drop.
move/and4P => [Hnnil /= Hrow Hdom /IH -> {IH r1 r2}].
rewrite -Hszu Hnnil andbT /=.
set r1 := drop (sumn shres) u1; set r2 := drop (sumn shres) u2.
have /eq_inv_is_row -> //= : eq_inv r1 r2.
  move: Hinv; rewrite -{1}(cat_take_drop (sumn shres) u1)
                      -{1}(cat_take_drop (sumn shres) u2).
  by move/eq_inv_catr; apply; rewrite !size_take -Hszu.
rewrite {r1}/r2.
move: Hdom; case/lastP Hd : (rev (diff_shape inn out)) => [//= | d dl] /=.
have Hsumn : sumn d + dl = sumn shres.
  rewrite -(sumn_rev (diff_shape _ _)) Hd.
  by rewrite -(sumn_rev (rcons _ _)) rev_rcons /= sumn_rev addnC.
rewrite !reshape_rcons ?size_take_leq -?Hszu ?Hszres // !rev_rcons /=.
apply: eq_inv_skew_dominate; last by rewrite !size_drop !size_take Hszu.
have {Hsumn} Hsum : sumn d <= sumn shres by rewrite -Hsumn; apply leq_addr.
have HH n m u : n <= m -> m <= size u ->
                drop n (take m u) ++ (drop m u) = drop n u.
  move=> Hnm Hu; have := erefl (drop n u).
  rewrite -{1}(cat_take_drop m u) drop_cat size_take_leq Hu.
  move: Hnm; rewrite leq_eqVlt => /orP [/eqP -> _| -> //=].
  by rewrite drop_oversize ?cat0s // size_take_leq Hu.
rewrite HH // HH -?Hszu //.
apply (eq_inv_catr (u1 := take (sumn d) u1) (u2 := take (sumn d) u2) ).
- by rewrite !cat_take_drop.
- by rewrite !size_take -Hszu.
Qed.

Lemma is_skew_tableau_skew_reshape_pad0 inner outer T (u : seq T) :
  is_skew_tableau inner (skew_reshape inner outer u) =
  is_skew_tableau ((pad 0 (size outer)) inner)
                  (skew_reshape ((pad 0 (size outer)) inner) outer u).
Proof.
rewrite is_skew_tableau_pad0 {1}/skew_reshape
        size_rev size_reshape size_rev size_diff_shape.
congr (is_skew_tableau _ _).
by rewrite /skew_reshape diff_shape_pad0.
Qed.

Theorem eq_inv_is_skew_tableau_reshape
        inner outer T1 T2 (u1 : seq T1) (u2 : seq T2) :
  size inner <= size outer ->
  eq_inv u1 u2 ->
  size u1 = sumn (diff_shape inner outer) ->
  is_skew_tableau inner (skew_reshape inner outer u1) ->
  is_skew_tableau inner (skew_reshape inner outer u2).
Proof.
rewrite (is_skew_tableau_skew_reshape_pad0 _ _ u1).
rewrite (is_skew_tableau_skew_reshape_pad0 _ _ u2).
move=> Hleq Hinv Hsz.
apply eq_inv_is_skew_tableau_reshape_size.
- elim: outer inner Hleq {Hsz} => [//= | out0 out IHout] [| inn0 inn] //=.
  + by rewrite size_nseq.
  + by rewrite ltnS subSS => /IHout /= ->.
- exact Hinv.
- by rewrite diff_shape_pad0.
Qed.

Theorem is_skew_tableau_reshape_std inner outer T (u : seq T) :
  size inner <= size outer ->
  size u = sumn (diff_shape inner outer) ->
  is_skew_tableau inner (skew_reshape inner outer u) =
  is_skew_tableau inner (skew_reshape inner outer (std u)).
Proof.
move=> Hin Hsize.
apply/idP/idP; apply eq_inv_is_skew_tableau_reshape => //=.
- exact: eq_inv_std.
- by apply eq_inv_sym; exact: eq_inv_std.
- by rewrite size_std.
Qed.

Theorem is_tableau_reshape_std sh T (u : seq T) :
  size u = sumn sh ->
  is_tableau (rev (reshape (rev sh) u)) =
  is_tableau (rev (reshape (rev sh) (std u))).
Proof.
move=> Hsz.
rewrite -!is_skew_tableau0 -[sh]/(diff_shape [::] sh) -!/(skew_reshape _ _ _).
by apply is_skew_tableau_reshape_std.
Qed.

End EqInvSkewTab.
Section StdOfTab.

Variable T : inhOrdType.
Implicit Type t : seq (seq T).

Definition std_of_tab t := skew_reshape [::] (shape t) (std (to_word t)).

Theorem std_of_tabE t : is_tableau t = is_tableau (std_of_tab t).
Proof.
rewrite -{1}(to_wordK t); apply is_tableau_reshape_std.
by rewrite size_to_word.
Qed.

Lemma shape_std_of_tab t : shape (std_of_tab t) = shape t.
Proof.
  rewrite /std_of_tab shape_skew_reshape //.
  by rewrite size_std size_to_word sumn_diff_shape //= subn0.
Qed.

Lemma to_word_std_of_tab t : to_word (std_of_tab t) = std (to_word t).
Proof.
  rewrite /std_of_tab to_word_skew_reshape //.
  by rewrite size_std size_to_word sumn_diff_shape //= subn0.
Qed.

Lemma std_of_tabP t s :
  shape s = shape t -> to_word s = std (to_word t) -> s = std_of_tab t.
Proof.
  rewrite /std_of_tab => Hword Hsh.
  rewrite -(skew_reshapeK (inner := [::]) (t := s)) //.
  by rewrite Hword diff_shapeK // -Hsh.
Qed.

End StdOfTab.
