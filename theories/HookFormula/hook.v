(** * Combi.HookFormula.hook : A proof of the Hook-Lenght formula *)
(******************************************************************************)
(*      Copyright (C) 2015-2018 Florent Hivert <florent.hivert@lri.fr>        *)
(*      Copyright (C) 2015      Chritine Paulin <christine.paulin@lri.fr>     *)
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
(** * A proof of the Hook-Lenght formula

This file contains a proof of the Frame-Robinson-Thrall (see [[FRT]]) hook-Length
formula for the number of standard Young tableau. It follows
closely the probabilistic proof of [[GNW]].

  - [[FRT]] -- J. S. Frame, G. de B. Robinson and R. M. Thrall,
    _The hook graphs of the symmetric group_, Canad. J. Math. 6 (1954), 316-324.

  - [[GNW]] -- Greene, C., Nijenhuis, A. and Wilf, H. S., _A probabilistic
    proof of a formula for the number of Young tableaux of a given
    shape_, Adv. in Math. 31 (1979), 104–109.

Here are the contents of the file:

Basic notions: boxes, hook, corners...

- [corner_box sh (r, c)] == [(r, c)] are the coordinate of a corner of [sh]
- [arm_length sh (r, c)] == the arm length of [sh] of the box [(r, c)]
- [leg_length sh (r, c)] == the leg length of [sh] of the box [(r, c)]
- [hook_length sh (r, c)] == the hook length of [sh] of the box [(r, c)]

- [in_hook (r, c) (k, l)] == the box [(k, l)] is in the hook of the box [(r, c)]
- [hook_box_indices (r, c)] == a sequence of indexes for boxes in the hook of
        [(r, c)]: leg boxes are [inl k], arm boxes are [inr]
- [hook_box (r, c) n] == the coordinate of the box of index [n]
- [hook_boxes (r, c)] == sequence of the boxes in the hool of [(r, c)]

The probabilistic algorithm:

- [is_trace p A B] == the trace of a trial path in the partition [p], that is
        the pair of the vertical and horizontal projection (see GNW).
        Specifically [A] and [B] are two non-empty strictly increasing
        sequences of naturals ending at a corner of [p].

- [trace_seq last] == all stricly increasing sequences ending by [last]
- [enum_trace Alpha Beta] == all trace ending at [(Alpha, Beta)]

- [walk_to_corner m (i, j)] == the probabilistic distribution of traces of a
        hook path of length at most [m] starting at [(i, j)]
- [choose_corner p] == the probalistic distribution of a trace starting at
        a uniformly chosen box

- [starts_at (r, c) t] == the trace [t] starts as [(r, c)]
- [starts_at (r, c) t] == the trace [t] ends as [(r, c)]

Formulas:

- [RHSL3 p a b A B] == the right hand side of Lemma 3 for a path starting
       at [(a, b)] with projections [A] and [B]
- [RHSL3_trace p t] == the right hand side of Lemma 3 for trace [t] in [p]

- [hook_length_prod sh] == the product of the hook length of [sh]

Finally the main Theorem is stated as:

[[
Theorem HookLengthFormula (p : intpart) :
  #|{:stdtabsh p}| = (sumn p)`! %/ (hook_length_prod p).
]]

 **********)


Require Import Misc Ccpo.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype choice ssrnat seq
        ssrint div rat fintype bigop path ssralg ssrnum.
(* Import bigop before ssralg/ssrnum to get correct printing of \sum \prod*)

Require Import tools subseq partition Yamanouchi stdtab Qmeasure.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope nat_scope.

(** * Recursion for the number of Yamanouchi words and standard tableaux *)
Lemma card_yama_rec (p : intpart) :
  p != empty_intpart ->
  #|{:yameval p}| =
      \sum_(i <- rem_corners p) #|{:yameval (decr_nth_intpart p i)}|.
Proof.
move=> H.
rewrite cardE -(size_map val) enum_yamevalE /enum_yameval.
move Hn : (sumn p) => n.
case: n Hn => [| n'] Hn' /=.
  by rewrite (empty_intpartP Hn') in H.
rewrite size_flatten /shape -sumn_map_condE.
rewrite /rem_corners -!map_comp.
congr sumn; apply eq_in_map => i /=.
rewrite mem_filter => /andP [Hcorn _].
rewrite size_map cardE -(size_map val) enum_yamevalE.
rewrite /enum_yameval /= /= Hcorn.
by rewrite (sumn_decr_nth (intpartP p) Hcorn) Hn' /=.
Qed.

Lemma card_yama0 : #|{:yameval empty_intpart}| = 1.
Proof. by rewrite cardE -(size_map val) enum_yamevalE. Qed.

Lemma card_yam_stdtabE (p : intpart) :
  #|{:yameval p}| = #|{:stdtabsh p}|.
Proof.
by rewrite !cardE -!(size_map val) enum_yamevalE enum_stdtabshE size_map.
Qed.

Local Open Scope ring_scope.

Lemma card_stdtabsh_rat_rec (F : intpart -> rat) :
  F empty_intpart = 1 ->
  ( forall p : intpart,
      p != empty_intpart ->
      F p = \sum_(i <- rem_corners p) F (decr_nth_intpart p i) ) ->
  forall p : intpart, F p = #|{:stdtabsh p}|%:Q.
Proof.
move=> H0 Hrec.
elim/intpart_rem_corner_ind => [//= | p IHp] /=.
  by rewrite H0 -card_yam_stdtabE card_yama0.
case: (altP (p =P empty_intpart)) => [-> |/= Hnnil].
  by rewrite H0 -card_yam_stdtabE card_yama0.
rewrite (Hrec _ Hnnil) -card_yam_stdtabE (card_yama_rec Hnnil).
rewrite (big_morph Posz PoszD (id1 := Posz O%N)) //.
rewrite (big_morph intr (@intrD _) (id1 := 0)) //.
rewrite /rem_corners !big_filter; apply eq_bigr => i Hi.
by rewrite card_yam_stdtabE IHp //=.
Qed.

Close Scope ring_scope.


(** * Boxes, Hooks and corners *)

(** Corner Boxes *)

Definition corner_box sh rc :=
  is_rem_corner sh rc.1 && (rc.2 == (nth 0 sh rc.1).-1).

Lemma corner_box_in_part sh rc :
  corner_box sh rc -> in_shape sh rc.
Proof.
move: rc => [r c].
rewrite /corner_box /in_shape /is_rem_corner /= => /andP [Hr /eqP ->].
by move: Hr; case (nth 0 sh r).
Qed.

Lemma corner_box_conj_part sh u v :
  is_part sh -> corner_box sh (u, v) -> corner_box (conj_part sh) (v, u).
Proof.
rewrite /corner_box {1}/is_rem_corner => Hpart /= /andP[Hcorn /eqP->{v}].
rewrite (rem_corner_conj_part Hpart Hcorn) /= eq_sym.
have : nth 0 sh u.+1 <= (nth 0 sh u).-1 < (nth 0 sh u).
  move: Hcorn; case: (nth 0 sh u) => [//= | shu].
  by rewrite ltnS [shu.+1.-1]/= => -> /=.
by rewrite -nth_conjE // => /eqP -> /=.
Qed.

(** Arm Leg and Hook lengths *)

Definition arm_length  sh rc:= ((nth 0 sh rc.1) - rc.2).-1.
Definition leg_length  sh rc := (arm_length (conj_part sh) (rc.2, rc.1)).
Definition hook_length sh rc := (arm_length sh rc + leg_length sh rc).+1.

(** The hook length product *)
Definition hook_length_prod (sh : seq nat) :=
  (\prod_(b : box_in sh) hook_length sh b)%N.
Local Notation HLF sh :=  (((sumn sh)`!)%:Q / (hook_length_prod sh)%:Q)%R.


Lemma hook_length_geq1 sh rc : hook_length sh rc >= 1.
Proof. by rewrite /hook_length. Qed.
#[local] Hint Resolve hook_length_geq1 : core.

Lemma hook_length_conj_part sh r c :
  is_part sh -> hook_length (conj_part sh) (r, c) = hook_length sh (c, r).
Proof. by rewrite /hook_length /leg_length addnC => /conj_partK ->. Qed.

Lemma arm_length_ler sh r c j :
  is_part sh -> r < j -> in_shape sh (j, c) ->
  arm_length sh (j, c) <= arm_length sh (r, c).
Proof.
rewrite /in_shape /arm_length => /is_part_ijP [_ Hpart] Hr Hc.
move/(_ _ _ (ltnW Hr)): Hpart => Hshjr.
rewrite -ltnS !prednK; first exact: leq_sub2r.
- by rewrite subn_gt0; apply: leq_trans Hc Hshjr.
- by rewrite subn_gt0; apply: Hc.
Qed.

Lemma arm_length_ltl sh r c j :
  is_part sh -> c < j -> in_shape sh (r, j) ->
  arm_length sh (r, j) < arm_length sh (r, c).
Proof.
rewrite /in_shape /arm_length => /is_part_ijP [_ Hpart] Hc Hr.
move/(_ _ _ (ltnW Hr)): Hpart => Hshjr.
have Hcr := ltn_trans Hc Hr.
rewrite -ltnS !prednK; first exact: ltn_sub2l.
- by rewrite subn_gt0; apply: Hcr.
- by rewrite subn_gt0; apply: Hr.
Qed.

Lemma leg_length_ltr sh r c j :
  is_part sh -> r < j -> in_shape sh (j, c) ->
  leg_length sh (j, c) < leg_length sh (r, c).
Proof.
rewrite /leg_length => Hpart Hr.
rewrite (in_conj_part Hpart).
exact: (arm_length_ltl (is_part_conj _)).
Qed.

Lemma leg_length_lel sh r c j :
  is_part sh -> c < j -> in_shape sh (r, j) ->
  leg_length sh (r, j) <= leg_length sh (r, c).
Proof.
rewrite /leg_length => Hpart Hr.
rewrite (in_conj_part Hpart).
exact: (arm_length_ler (is_part_conj _)).
Qed.

Lemma hook_length_ltl sh r c j :
  is_part sh -> c < j -> in_shape sh (r, j) ->
  hook_length sh (r, j) < hook_length sh (r, c).
Proof.
rewrite /hook_length ltnS => Hpart Hr Hc.
rewrite -addSn; apply leq_add.
exact: arm_length_ltl.
exact: leg_length_lel.
Qed.

Lemma hook_length_ltr sh r c j :
  is_part sh -> r < j -> in_shape sh (j, c) ->
  hook_length sh (j, c) < hook_length sh (r, c).
Proof.
rewrite /hook_length ltnS => Hpart Hr Hc.
rewrite -addnS; apply leq_add.
exact: arm_length_ler.
exact: leg_length_ltr.
Qed.

Lemma hook_length1_corner sh rc :
  is_part sh -> in_shape sh rc ->
  hook_length sh rc = 1 -> corner_box sh rc.
Proof.
move: rc => [r c] Hpart.
rewrite /in_shape /= => Hin_part /eqP.
rewrite /hook_length eqSS addn_eq0 => /andP [Hnth Hhaut].
apply /andP; split.
- rewrite /is_rem_corner/=.
  apply: (leq_trans _ Hin_part).
  rewrite ltnS (conj_leqE Hpart).
  by rewrite -subn_eq0 subnS.
- rewrite eqn_leq; apply /andP; split.
  + rewrite -ltnS; apply (leq_trans Hin_part).
    exact: leqSpred.
  + by rewrite -subn_eq0 -subn1 -subnAC subn1.
Qed.

Lemma corner_arm_length0 sh rc :
  is_part sh -> corner_box sh rc -> arm_length sh rc = 0.
Proof.
move: rc => [r c].
rewrite /corner_box /is_rem_corner /arm_length => Hpart /=/andP[_ /eqP ->].
by case: (nth 0 sh r) => [//= | n]; rewrite subSn //= subnn.
Qed.

Lemma corner_leg_length0 sh rc :
  is_part sh -> corner_box sh rc -> leg_length sh rc = 0.
Proof.
move: rc => [r c]; rewrite /leg_length => Hpart Hcorn.
apply (corner_arm_length0 (is_part_conj Hpart)).
exact: corner_box_conj_part.
Qed.

Lemma corner_hook_length1 sh rc :
  is_part sh -> corner_box sh rc -> hook_length sh rc = 1.
Proof.
rewrite /hook_length => Hpart Hcorn.
by rewrite corner_arm_length0 // corner_leg_length0.
Qed.

Lemma arm_length_corner_box sh r c u v :
  is_part sh ->
  r <= u -> c <= v -> corner_box sh (u, v) ->
  arm_length sh (r, c) = arm_length sh (u, c) + arm_length sh (r, v).
Proof.
move=> /is_part_ijP [_ Hpart].
rewrite /corner_box /is_rem_corner => Hr Hc /=/andP[Hcorn /eqP Hv].
subst v.
rewrite /arm_length.
move/(_ _ _ Hr): Hpart => {Hr}.
move: Hc Hcorn; case: (nth 0 sh u) => [//= | pu].
rewrite [_.+1.-1]/= => Hcpu; rewrite (subSn Hcpu) => _ Hpu.
have:= leq_ltn_trans Hcpu Hpu.
case: (nth 0 sh r) Hpu => [//= | pr].
rewrite !ltnS => Hpu Hcpr.
by rewrite !subSn //= addnC addnBA // subnK.
Qed.

Lemma leg_length_corner_box sh r c u v :
  is_part sh ->
  r <= u -> c <= v -> corner_box sh (u, v) ->
  leg_length sh (r, c) = leg_length sh (u, c) + leg_length sh (r, v).
Proof.
rewrite /leg_length addnC => Hpart Hru Hcv Hcorn.
apply: (arm_length_corner_box (is_part_conj Hpart) Hcv Hru).
exact: corner_box_conj_part.
Qed.

Lemma hook_length_corner_box sh r c u v :
  is_part sh -> r <= u -> c <= v -> corner_box sh (u, v) ->
  hook_length sh (r, c) = hook_length sh (u, c) + hook_length sh (r, v) - 1.
Proof.
move=> Hpart Hru Hcv Hcorn.
rewrite /hook_length (arm_length_corner_box Hpart Hru Hcv Hcorn).
rewrite (leg_length_corner_box Hpart Hru Hcv Hcorn).
rewrite addSn subn1 /= !addnS !addnA; congr (_ + _).+1.
by rewrite -!addnA; congr (_ + _); rewrite addnC.
Qed.

Lemma arm_length_incr_nth_row sh r c :
  in_shape sh (r, c) ->
  arm_length (incr_nth sh r) (r, c) = (arm_length sh (r, c)).+1.
Proof.
rewrite /in_shape /arm_length nth_incr_nth eq_refl add1n => Hc.
rewrite prednK; last by rewrite subn_gt0.
by rewrite subSn; last exact: ltnW.
Qed.

Lemma arm_length_incr_nth_nrow sh r c i :
  i != r -> arm_length (incr_nth sh i) (r, c) = arm_length sh (r, c).
Proof.
rewrite /arm_length nth_incr_nth => /negbTE ->.
by rewrite add0n.
Qed.

Lemma hook_length_incr_nth_row sh r c :
  is_part sh -> is_add_corner sh r -> in_shape sh (r, c) ->
  hook_length (incr_nth sh r) (r, c) = (hook_length sh (r, c)).+1.
Proof.
rewrite /hook_length => Hpart Hcrn Hin; apply eq_S.
rewrite (arm_length_incr_nth_row Hin) addSn.
congr (_ + _).+1.
rewrite /leg_length /arm_length (conj_part_incr_nth Hpart Hcrn) nth_incr_nth.
move: Hin; rewrite /in_shape eq_sym ltn_neqAle => /andP [/negbTE -> _].
by rewrite add0n.
Qed.

Lemma hook_length_incr_nth_col sh r i :
  is_part sh -> is_add_corner sh r ->
  in_shape sh (i, (nth 0 sh r)) ->
  hook_length (incr_nth sh r) (i, nth 0 sh r)
  = (hook_length sh (i, nth 0 sh r)).+1.
Proof.
move=> Hpart Hcorn Hin.
rewrite -hook_length_conj_part; last exact: is_part_incr_nth.
rewrite conj_part_incr_nth // hook_length_incr_nth_row; first last.
  - by rewrite -in_conj_part.
  - exact: is_add_corner_conj_part.
  - exact: is_part_conj.
by rewrite hook_length_conj_part.
Qed.

Lemma hook_length_incr_nth sh i r c :
  is_part sh -> is_add_corner sh i ->
  in_shape sh (r, c) ->
  i != r -> nth 0 sh i != c ->
  hook_length (incr_nth sh i) (r, c) = hook_length sh (r, c).
Proof.
rewrite /hook_length => Hpart Hcorn Hin Hr Hc; apply eq_S.
congr (_ + _).
- exact: arm_length_incr_nth_nrow.
- rewrite /leg_length conj_part_incr_nth //.
  exact: arm_length_incr_nth_nrow.
Qed.

Open Scope ring_scope.

Lemma hook_length_pred sh rc :
  (hook_length sh rc)%:~R - 1 = ((hook_length sh rc).-1)%:~R :> rat.
Proof. by rewrite predn_int // !mulrzDl. Qed.

Lemma prod_hook_length_quot_row p Alpha Beta :
  is_part p -> corner_box p (Alpha, Beta) ->
  \prod_(i <- enum_box_in (decr_nth p Alpha) | i.1 == Alpha)
     (  (hook_length p i)%:Q /
        (hook_length (decr_nth p Alpha) i)%:Q  ) =
  \prod_(0 <= j < Beta) (1 + ((hook_length p (Alpha, j))%:Q - 1)^-1).
Proof.
move=> Hpart Hcorn.
have:= Hcorn => /andP/=[Hcrn/eqP HBeta].
have:= decr_nthK Hpart Hcrn; set p' := decr_nth p Alpha => Hp.
set F := (F in _ = \prod_(i <- _) F i).
rewrite big_seq_cond (eq_bigr (fun i => F i.2)) -?big_seq_cond; first last.
  move=> [r c] /= /andP []; rewrite mem_enum_box_in unfold_in /= => Hin /eqP Hr.
  subst r.
  rewrite /F{F} -Hp hook_length_pred hook_length_incr_nth_row /=; first last.
  - exact: Hin.
  - rewrite /p'.
    exact: add_corner_decr_nth.
  - exact: is_part_decr_nth.
  have: (hook_length p' (Alpha, c))%:Q != 0 by rewrite intr_eq0.
  move: (hook_length p' (Alpha, c)) => h Hn.
  rewrite -addn1; rewrite PoszD intrD.
  by rewrite -{4}(divff Hn) -{3}div1r -mulrDl.
transitivity (\prod_(i <- [seq i.2 | i <- enum_box_in p' & i.1 == Alpha]) F i).
  by rewrite big_map big_filter; apply: eq_bigr.
rewrite big_map /enum_box_skew filter_flatten big_flatten /= -map_comp big_map.
case: (ltnP Alpha (size p')) => Halpha.
- rewrite (bigD1_seq Alpha) /=; first last.
  + exact: iota_uniq.
  + rewrite mem_iota add0n.
    by rewrite Halpha.
  rewrite big_filter big_map /=.
  under eq_bigl do rewrite /= eq_refl.
  rewrite nth_nil subn0.
  rewrite /p' nth_decr_nth -HBeta (eq_bigr F) //.
  rewrite /index_iota subn0 mulrC.
  rewrite big1 ?mul1r // => i /negbTE Hi.
  by rewrite big_filter big_map big_pred0.
- move: HBeta; rewrite -nth_decr_nth (nth_default _ Halpha) => ->.
  rewrite /index_iota /= big_nil.
  rewrite big_seq_cond.
  apply big1 => i; rewrite andbT mem_iota /= add0n => Hi.
  rewrite big_filter big_map big_pred0 // => j /=.
  exact: ltn_eqF (leq_trans Hi Halpha).
Qed.

Close Scope ring_scope.

Section FindCorner.

Variable p : intpart.
Implicit Types (r c k l : nat) (rc kl : nat * nat).

(** ** Hook boxes *)

Local Notation conj := (conj_part p).

Definition in_hook rc kl :=
  let: (r, c) := rc in let: (k, l) := kl in
  ((r == k) && (c < l < nth 0 p r)) ||
  ((c == l) && (r < k < nth 0 conj c)).

Lemma in_hook_shape rc kl :
   in_shape p rc -> in_hook rc kl -> in_shape p kl.
Proof using.
move: rc kl => [r c][k l].
rewrite /in_shape /in_hook => /= Hj /orP [] /and3P [/eqP <- //= H1 H2].
by rewrite conj_ltnE.
Qed.

Definition hook_box_indices rc : seq (nat+nat) :=
  [seq inl k | k <- iota rc.1.+1 ((nth 0 conj rc.2).-1 - rc.1)] ++
  [seq inr k | k <- iota rc.2.+1 ((nth 0 p rc.1).-1 - rc.2)].
Definition hook_box rc n : nat * nat :=
  match n with inl k => (k,rc.2) | inr k => (rc.1,k) end.
Definition hook_boxes rc := [seq hook_box rc n | n <- hook_box_indices rc].

Lemma size_hook_box_indices rc :
  size (hook_box_indices rc) = (hook_length p rc).-1.
Proof.
move: rc => [r c]; rewrite /= size_cat !size_map !size_iota.
rewrite /hook_length /leg_length /arm_length /=.
by rewrite -!subn1 -!subnDA !add1n !addn1 addnC.
Qed.

Local Lemma ltnPred a b : a < b -> (a <= b.-1).
Proof using. by case: b. Qed.

Local Lemma iota_hookE a b c : a < b -> b < a.+1 + (c.-1 - a) = (b < c).
Proof using.
move => Hab; rewrite addSn.
case: (ltnP b c) => Hbc.
- have:= ltn_trans Hab Hbc => /ltnPred/subnKC ->.
  exact: (leq_trans Hbc (leqSpred _)).
- case: c Hbc => [_ | c Hbc] /=.
  + by rewrite sub0n addn0 ltnS leqNgt Hab.
  + rewrite ltnS; case: (leqP a c).
    * by move/subnKC ->; rewrite leqNgt Hbc.
    * move=> /ltnW; rewrite {1}/leq => /eqP ->.
      by rewrite addn0 leqNgt Hab.
Qed.

Lemma in_hook_boxesP rc kl : (kl \in hook_boxes rc) = (in_hook rc kl).
Proof using.
move: rc kl => [r c] [k l] /=.
apply/mapP/idP.
- move=> /= [] [] x; rewrite mem_cat => /orP [] /=.
  + rewrite mem_map; last by move=> u v [].
    rewrite mem_iota => /andP [Hrx Hxr] /= [-> -> {k l}].
    rewrite /in_hook; apply/orP; right.
    by rewrite eq_refl Hrx /= -(iota_hookE _ Hrx).
  + by move=> /mapP [y] _.
  + by move=> /mapP [y] _.
  + rewrite mem_map; last by move=> u v [].
    rewrite mem_iota => /andP [Hcx Hxc] /= [-> -> {k l}].
    rewrite /in_hook; apply/orP; left.
    by rewrite eq_refl Hcx /= -(iota_hookE _ Hcx).
- rewrite /in_hook => /orP [] /and3P [/eqP <-].
  + move=> {k} Hc Hr.
    exists (inr l); last by [].
    rewrite mem_cat; apply/orP; right; rewrite mem_map; last by move=> u v [].
    by rewrite mem_iota Hc /= iota_hookE.
  + move=> {l} Hr Hc.
    exists (inl k); last by [].
    rewrite mem_cat; apply/orP; left; rewrite mem_map; last by move=> u v [].
    by rewrite mem_iota Hr /= iota_hookE.
Qed.

Lemma hook_boxes_empty rc :
  in_shape p rc -> hook_boxes rc = [::] -> corner_box p rc.
Proof using.
move=> Hpart Hhl. apply hook_length1_corner => //.
suff -> : hook_length p rc = (size (hook_boxes rc)).+1 by rewrite Hhl.
by rewrite size_map size_hook_box_indices.
Qed.


(** ** Traces *)
Definition is_trace (A B : seq nat) :=
  [&& (A != [::]), (B != [::]),
    sorted ltn A, sorted ltn B &
    corner_box p (last 0 A, last 0 B) ].

Lemma is_trace_tll a A B : A != [::] -> is_trace (a :: A) B -> is_trace A B.
Proof using.
rewrite /is_trace => HA /and5P [_ -> /path_sorted -> ->].
by rewrite HA /=; case: A HA.
Qed.

Lemma is_trace_tlr b A B : B != [::] -> is_trace A (b :: B) -> is_trace A B.
Proof using.
rewrite /is_trace => HB /and5P [-> _ -> /path_sorted ->].
by rewrite HB /=; case: B HB.
Qed.

Lemma is_trace_lastr (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> is_trace (a :: A) [:: last b B].
Proof using.
elim: B b => [//= | B0 B IHB] b /= /is_trace_tlr H.
have {}/H : B0 :: B != [::] by [].
exact: IHB.
Qed.

Lemma is_trace_lastl (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> is_trace [:: last a A] (b :: B).
Proof using.
elim: A a => [//= | A0 A IHA] a /= /is_trace_tll H.
have {}/H : A0 :: A != [::] by [].
exact: IHA.
Qed.

Lemma sorted_in_leq_last A a : sorted ltn A -> a \in A -> a <= last 0 A.
Proof using.
elim: A a => [//= | A0 A IHA] a /= Hpart.
rewrite inE => /orP [/eqP |] Ha.
- subst a => {IHA}.
  elim: A A0 Hpart => [//= | A1 A IHA] A0 /= /andP [/ltnW H01 /IHA{IHA}].
  exact: leq_trans H01.
- move/(_ _ (path_sorted Hpart) Ha): IHA => {Hpart}.
  by case: A Ha.
Qed.

Lemma sorted_leq_last A a : sorted ltn (a :: A) -> a <= last a A.
Proof using.
move=> /sorted_in_leq_last H.
by have /H /= : a \in (a :: A) by rewrite inE eq_refl.
Qed.

Lemma is_trace_in_in_shape (A B : seq nat) : is_trace A B ->
  forall a b, a \in A -> b \in B -> in_shape p (a, b).
Proof using.
rewrite /is_trace => /and5P [_ _ HltnA HltnB
                      /corner_box_in_part Hpart] a b Ha Hb.
by apply: (@in_part_le p (last 0 A) (last 0 B) _ _ (intpartP p) Hpart);
  exact: sorted_in_leq_last.
Qed.

Lemma is_trace_in_shape (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> in_shape p (a, b).
Proof using. by move/is_trace_in_in_shape; apply; rewrite inE eq_refl. Qed.

Lemma trace_size_arm_length (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> size B <= arm_length p (a, b).
Proof using.
elim: B b => [//= | B0 B IHB] b /= Htrace.
apply: (leq_ltn_trans (IHB _ (is_trace_tlr _ Htrace))); first by [].
have:= Htrace => /and5P [_ _ _ /= /andP [Hb _] _].
rewrite {IHB} /arm_length.
suff HB0 : B0 < nth 0 p a.
  rewrite -ltnS prednK; last by rewrite subn_gt0.
  rewrite -ltnS prednK //; last by rewrite subn_gt0; exact: (ltn_trans Hb HB0).
  rewrite ltnS; apply ltn_sub2l; last exact Hb.
  exact: (ltn_trans Hb HB0).
rewrite -/(in_shape _ (_, _)).
by apply (is_trace_in_in_shape Htrace); rewrite !inE eq_refl /= ?orbT.
Qed.

Lemma trace_size_leg_length (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> size A <= leg_length p (a, b).
Proof using.
elim: A a => [//= | A0 A IHA] a /= Htrace.
apply: (leq_ltn_trans (IHA _ (is_trace_tll _ Htrace))); first by [].
have:= Htrace => /and5P [_ _ /= /andP [Ha _] _ _].
rewrite {IHA} /leg_length.
suff HA0 : A0 < nth 0 conj b.
  rewrite -ltnS prednK; last by rewrite subn_gt0.
  rewrite -ltnS prednK //; last by rewrite subn_gt0; exact: (ltn_trans Ha HA0).
  rewrite ltnS; apply ltn_sub2l; last exact Ha.
  exact: (ltn_trans Ha HA0).
rewrite -/(in_shape _ (_, _)).
rewrite -in_conj_part //.
by apply (is_trace_in_in_shape Htrace); rewrite !inE eq_refl /= ?orbT.
Qed.

Lemma size_tracer (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> size B < hook_length p (a, b).
Proof using.
move=> /trace_size_arm_length/leq_trans; apply.
by rewrite leq_addr.
Qed.

Lemma size_tracel (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> size A < hook_length p (a, b).
Proof using.
move=> /trace_size_leg_length/leq_trans; apply.
by rewrite leq_addl.
Qed.

Lemma is_trace_corner_nil (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) ->
  (size (hook_box_indices (a, b)) == 0) = (A == [::]) && (B == [::]).
Proof using.
rewrite size_hook_box_indices.
move=> Htrace; apply/idP/idP.
- move=> /eqP Hal.
  have:= size_tracel Htrace; have:= size_tracer Htrace.
  move: Hal; rewrite /hook_length /= => ->.
  by rewrite !ltnS !leqn0 => /nilP -> /nilP ->.
- move=> /andP/=[/eqP HA /eqP HB]; subst.
  move: Htrace => /and5P [_ _ _ _ /=].
  rewrite /corner_box /hook_length /leg_length /arm_length /is_rem_corner.
  move => /andP/=[Ha /eqP Hb]; subst.
  have -> : (nth 0 p a - (nth 0 p a).-1) = 1.
    move: Ha; case: (nth 0 p a) => [//= | pa] _.
    by rewrite /= subSn // subnn.
  rewrite /= add0n.
  suff -> : nth 0 conj (nth 0 p a).-1 = a.+1 by rewrite subSn // subnn.
  apply/eqP; rewrite nth_conjE //.
  move: Ha; case: (nth 0 p a) => [//= | pa].
  by rewrite !ltnS => -> /=.
Qed.

Lemma hook_length_last_rectangle (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) ->
  hook_length p (a, b)
  = hook_length p (last a A, b) + hook_length p (a, (last b B)) - 1.
Proof using.
rewrite /is_trace => /and5P [_ _ HA HB /=].
exact: hook_length_corner_box (sorted_leq_last HA) (sorted_leq_last HB).
Qed.


Definition trace_seq (last : nat) : seq (seq nat) :=
  [seq rcons tr last | tr : subseqs (iota 0 last)].

Definition enum_trace (Alpha Beta : nat) : seq ((seq nat) * (seq nat)) :=
  [seq (A, B) | A <- trace_seq Alpha, B <- trace_seq Beta].

Lemma trace_seq_uniq l : uniq (trace_seq l).
Proof using.
rewrite map_inj_uniq; first exact: enum_uniq.
by move=> i j /rconsK/val_inj ->.
Qed.

Lemma enum_trace_uniq (Alpha Beta : nat) : uniq (enum_trace Alpha Beta).
Proof using.
rewrite /enum_trace; apply allpairs_uniq.
- exact: trace_seq_uniq.
- exact: trace_seq_uniq.
- by move=> [i1 i2] [j1 j2].
Qed.

Lemma trace_corner_box (Alpha Beta : nat) :
  corner_box p (Alpha, Beta) ->
  forall A B, A \in trace_seq Alpha -> B \in trace_seq Beta -> is_trace A B.
Proof using.
move=> Hcorn A B /mapP[[A' /= subA _ ->{A}]] /mapP[[B' /= subB _ ->{B}]].
by rewrite /is_trace !rcons_nilF /=
           -!sorted_subseq_iota_rcons subA subB !last_rcons.
Qed.

Lemma trace_seqlP (A B : seq nat) :
  is_trace A B -> A \in trace_seq (last 0 A).
Proof using.
move=> /and5P [].
case/lastP: A => [//= | A lA] _ _ Hsort _ /= _.
rewrite last_rcons /trace_seq; apply/mapP => /=.
have subA : subseq A (iota 0 lA) by rewrite sorted_subseq_iota_rcons.
by exists (Subseqs subA); first exact: mem_enum.
Qed.

Lemma trace_seqrP (A B : seq nat) :
  is_trace A B -> B \in trace_seq (last 0 B).
Proof using.
move=> /and5P [].
case/lastP: B => [//= | B lB] _ _ _ Hsort /= _.
rewrite last_rcons /trace_seq; apply/mapP => /=.
have subB : subseq B (iota 0 lB) by rewrite sorted_subseq_iota_rcons.
by exists (Subseqs subB); first exact: mem_enum.
Qed.

Lemma enum_traceP (Alpha Beta : nat) :
  corner_box p (Alpha, Beta) ->
  forall A B,
    (A, B) \in enum_trace Alpha Beta =
    [&& (is_trace A B), (last 0 A == Alpha) & (last 0 B == Beta)].
Proof using.
move=> Hcorn A B.
apply/idP/idP.
- move=> /allpairsP [[eA eB] /= [HA HB [H1 H2]]]; subst eA eB.
  apply/and3P; split.
  + exact: (trace_corner_box Hcorn).
  + by move: HA => /mapP [A' _ ->]; rewrite last_rcons.
  + by move: HB => /mapP [B' _ ->]; rewrite last_rcons.
- move=> /and3P [Htrace /eqP HlA /eqP HlB].
  apply/allpairsP; exists (A, B) => /=; split.
  + by rewrite -HlA; exact: (trace_seqlP Htrace).
  + by rewrite -HlB; exact: (trace_seqrP Htrace).
  + by [].
Qed.


(** * The probabilistic algorithm *)

Fixpoint walk_to_corner_rec (m : nat) (i j : nat) : distr (seq nat * seq nat) :=
  if m is m'.+1 then
    let s := hook_box_indices (i, j) in
    (if size s is _.+1
     then Mlet (Uniform (unif_def (inl 0%N) s))
       (fun n => match n with
        | inl k => Mlet (walk_to_corner_rec m' k j) (fun X => Munit (i::X.1, X.2))
        | inr k => Mlet (walk_to_corner_rec m' i k) (fun X => Munit (X.1, j::X.2))
        end)
      else Munit ([::i],[::j]))
   else Munit ([::i],[::j]).
Definition walk_to_corner m ij := walk_to_corner_rec m ij.1 ij.2.
Lemma walk_to_corner0_simpl r c :
  walk_to_corner 0 (r, c) = Munit ([:: r], [:: c]).
Proof using. by []. Qed.

Lemma walk_to_corner_end_simpl m r c :
  size (hook_box_indices (r, c)) = 0 ->
  walk_to_corner m (r, c) = Munit ([:: r], [:: c]).
Proof using. by rewrite /walk_to_corner; case m => [| n] //= ->. Qed.

Lemma walk_to_corner_simpl m r c :
  forall (Hs : (size (hook_box_indices (r, c)) != 0)),
    walk_to_corner m.+1 (r, c) =
    Mlet (Uniform (mkunif (hook_box_indices (r, c)) Hs))
      (fun n => match n with
       | inl k => Mlet (walk_to_corner m (k, c)) (fun X => Munit (r::X.1, X.2))
       | inr k => Mlet (walk_to_corner m (r, k)) (fun X => Munit (X.1, c::X.2))
       end).
Proof using. by rewrite /walk_to_corner /=; case: hook_box_indices. Qed.

Open Scope ring_scope.

Lemma walk_to_corner_inv m r c :
  mu (walk_to_corner m (r, c))
     (fun HS => [&& size   HS.1 != 0, size   HS.2 != 0,
                    head 0 HS.1 == r& head 0 HS.2 == c]%N%:Q)
      = 1.
Proof using.
elim: m r c => [| n Hn] r c.
  by rewrite /= 2!eq_refl.
case (altP (size (hook_box_indices (r, c)) =P 0%N)) => [H0|Hs].
- by rewrite walk_to_corner_end_simpl //= !eq_refl.
- rewrite (walk_to_corner_simpl _ Hs).
  rewrite Mlet_simpl mu_one_eq //.
  move => [] k /=.
  + apply: (mu_bool_impl1 _ _ _ _ (Hn k c)) => [] [A B] /=.
    apply /implyP => /and4P [H1 H2 H3 H4].
    by rewrite H2 H4 eq_refl.
  + apply: (mu_bool_impl1 _ _ _ _ (Hn r k)) => [] [A B] /=.
    apply /implyP => /and4P [H1 H2 H3 H4].
    by rewrite H1 H3 eq_refl.
Qed.

Local Definition charfun A B := fun x : seq nat * seq nat => (x == (A, B))%:Q.

Lemma walk_to_corner_emptyl m rc (A B : seq nat) :
  (A == [::])%B -> mu (walk_to_corner m rc) (charfun A B) = 0.
Proof using.
move => HA.
apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv _ _ _)) => [] [X Y] /=.
apply /implyP => /and4P [SX SY _ _].
move: SX; apply contra.
by rewrite /charfun size_eq0 xpair_eqE (eqP HA); move => /andP [].
Qed.

Lemma walk_to_corner_emptyr m rc (A B : seq nat) :
  (B == [::])%B -> mu (walk_to_corner m rc) (charfun A B) = 0.
Proof using.
move: rc => [r c] HB /=.
apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m r c)) => [] [X Y] /=.
apply /implyP => /and4P [SX SY _ _].
move: SY; apply contra.
by rewrite /charfun size_eq0 xpair_eqE (eqP HB); move => /andP [].
Qed.

Lemma charfun_simpll a A B :
  (fun x => charfun (a :: A) B (a :: x.1, x.2)) == charfun A B.
Proof using.
move => [X Y] /=.
by rewrite /charfun /eq_op /= {1}/eq_op /= eq_refl.
Qed.

Lemma charfun_simplr b A B :
  (fun x => charfun A (b :: B) (x.1, b :: x.2)) == charfun A B.
Proof using.
move => [X Y] /=.
by rewrite /charfun /eq_op /= {2}/eq_op /= eq_refl.
Qed.


Lemma walk_to_corner_decomp m a b (A B : seq nat) :
  (size (hook_box_indices (a, b)) != 0)%N ->
  is_trace (a::A) (b::B) ->
  mu (walk_to_corner m.+1 (a, b)) (charfun (a :: A) (b :: B))
  =
  ( mu (walk_to_corner m  (a, head O B)) (charfun (a :: A) B) +
    mu (walk_to_corner m  (head O A, b)) (charfun A (b :: B))
  ) / (size (hook_box_indices (a, b)))%:Q.
Proof using.
move => Hs Ht.
rewrite (walk_to_corner_simpl _ Hs) Mlet_simpl.
rewrite mu_uniform_sum /=.
congr (_ / _).
rewrite /hook_box_indices big_cat /= !big_map /= addrC.
congr (_ + _).
- case (boolP (size B == 0%N)) => HB.
  + rewrite big1.
    * apply esym.
      apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m a (head O B))) =>
          [] [X Y] /=.
      apply/implyP => /and4P [_ SY _ _].
      by move: SY; apply contra => /eqP [_ ->].
    * move => i _; rewrite charfun_simplr.
      apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m a i)) => [] [X Y] /=.
      apply/implyP => /and4P [_ SY _ _].
      by move: SY; apply contra => /eqP [_ ->].
  + rewrite (bigD1_seq (head O B) _ (iota_uniq _ _)) /=.
    * rewrite -{1}(@charfun_simplr b (a :: A) B) -[RHS]addr0.
      congr (_ + _).
      apply: big1 => i Hi.
      rewrite charfun_simplr.
      apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m a i)) => [] [X Y] /=.
      apply/implyP => /and4P [_ _ _ SH].
      move: Hi; apply contra => /eqP [_ <-].
      by rewrite eq_sym.
    * have:= Ht => /and5P [_ _ _ HsortB _].
      have Hb : (b < head 0 B)%N.
        by move: HsortB HB; case B => [//= | b0 B'] /= /andP [].
      rewrite mem_iota (iota_hookE _ Hb) Hb /=.
      have Hh : (head O B \in b :: B).
        by move: HB; case B => [//= | n l] _; rewrite !inE eq_refl orbT.
      exact: (is_trace_in_in_shape Ht (mem_head _ _) Hh).
- case (boolP (size A == O)) => HA.
  + rewrite big1.
    * apply esym.
      apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m (head O A) b)) =>
          [] [X Y] /=.
      apply /implyP => /andP [SX _].
      by move: SX; apply contra => /eqP [-> _].
    * move => i _; rewrite charfun_simpll.
      apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m i b)) => [] [X Y] /=.
      apply /implyP => /andP [SX _].
      by move: SX; apply contra => /eqP [-> _].
  + rewrite (bigD1_seq (head O A) _ (iota_uniq _ _)) /=.
    * rewrite -{1}(@charfun_simpll a A (b :: B)) -[RHS]addr0.
      congr (_ + _).
      apply: big1 => i Hi.
      rewrite charfun_simpll.
      apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m i b)) => [] [X Y] /=.
      apply /implyP => /and4P [_ _ HX _].
      move: Hi; apply contra => /eqP [<- _].
      by rewrite eq_sym.
    * have:= Ht => /and5P [_ _ HsortA _ _].
      have Ha : (a < head 0 A)%N.
        by move: HsortA HA; case A => [//= | a0 A'] /= /andP [].
      rewrite mem_iota (iota_hookE _ Ha) Ha /=.
      have Hh : (head O A \in a :: A).
        by move: HA; case A => [//= | n l] _; rewrite !inE eq_refl orbT.
      have:= is_trace_in_in_shape Ht Hh (mem_head _ _).
      case: p => /= part Hpart.
      by rewrite in_conj_part.
Qed.

Lemma mu_walk_to_corner_is_trace rc m :
  in_shape p rc ->
  ((hook_length p rc) <= m.+1)%N ->
  mu (walk_to_corner m rc) (fun X => (is_trace X.1 X.2)%:Q) = 1.
Proof using.
elim: m rc => [| m IHm] [r c] Hrc /= Hal.
  have {}Hal : hook_length p (r, c) = 1%N.
    by move: Hal; rewrite /hook_length ltnS leqn0 => /eqP ->.
  by rewrite /is_trace hook_length1_corner.
case H : (hook_length p (r, c)).-1 => [/= | n].
  rewrite walk_to_corner_end_simpl // ?size_hook_box_indices //.
  rewrite Munit_simpl /= /is_trace /=.
  by rewrite hook_length1_corner // /hook_length H.
have Hsz : size (hook_box_indices (r, c)) != 0%N.
  by rewrite size_hook_box_indices H.
rewrite (walk_to_corner_simpl _ Hsz) Mlet_simpl mu_uniform_sum.
have : upoints (unif_def (inl O) (hook_box_indices (r, c))) =
          (hook_box_indices (r, c)).
  rewrite /unif_def.
  move: H; rewrite -size_hook_box_indices.
  by case: (hook_box_indices (r, c)).
rewrite -weight1_size /weight; rat_to_ring.
rewrite [X in (_ / X)](eq_bigl predT) //=.
set num := (X in (X / _)); set den := (X in (_ / X)).
suff -> : num = den.
  rewrite divff // /den {num den}.
  rewrite big_const_seq count_predT size_hook_box_indices H iter_addr addr0.
  by rewrite pnatr_eq0.
rewrite /num /den {num den}.
apply eq_big_seq => /= i.
rewrite mem_cat => /orP [] /mapP [j]; rewrite mem_iota => /andP/=[H1 H2] -> {i};
  move: H2; rewrite (iota_hookE _ H1) Mlet_simpl.
- rewrite -/(in_shape _ (_, _)) -(in_conj_part (intpartP p)) => Hj.
  have Hlen : (hook_length p (j, c) <= m.+1)%N.
    rewrite -ltnS; apply: (leq_trans _ Hal).
    exact: hook_length_ltr.
  rewrite -[RHS](IHm _ Hj Hlen).
  rewrite (mu_pos_cond _ (walk_to_corner_inv m j c)); first last.
    by move=> [A B]; apply/andP; split; [exact: mu_bool_0le | exact: mu_bool_le1].
  rewrite [RHS](mu_pos_cond _ (walk_to_corner_inv m j c)); first last.
    by move=> [A B]; case: (is_trace _ _).
  apply Mstable_eq => [] [A B] /=.
  do 2 (case: eqP => /=; first by rewrite !mul0r).
  do 2 (case: eqP => /=; last by rewrite !mul0r).
  rewrite !mul1r /is_trace /=.
  case: A B => [//= | a0 A] [//= | b0 B] /= _ -> _ _.
  by rewrite H1.
- rewrite -/(in_shape _ (_, _)) => Hj.
  have Hlen : (hook_length p (r, j) <= m.+1)%N.
    rewrite -ltnS; apply: (leq_trans _ Hal).
    exact: hook_length_ltl.
  rewrite -[RHS](IHm _ Hj Hlen).
  rewrite (mu_pos_cond _ (walk_to_corner_inv m r j)); first last.
    by move=> [A B]; apply/andP; split; [exact: mu_bool_0le | exact: mu_bool_le1].
  rewrite [RHS](mu_pos_cond _ (walk_to_corner_inv m r j)); first last.
    by move=> [A B]; case: (is_trace _ _).
  apply Mstable_eq => [] [A B].
  do 2 (case: eqP => /=; first by rewrite !mul0r).
  do 2 (case: eqP => /=; last by rewrite !mul0r).
  rewrite !mul1r /is_trace /=.
  case: A B => [//= | a0 A] [//= | b0 B] /= -> _ _ _.
  by rewrite H1.
Qed.


(** Right hand size formula of Lemma 3. *)
Definition RHSL3 (a b : nat) (A B : seq nat) : rat :=
  \prod_(i <- belast a A) (1 / ((hook_length p (i, last b (b :: B)))%:Q - 1)) *
  \prod_(j <- belast b B) (1 / ((hook_length p (last a (a :: A), j))%:Q - 1)).

Lemma Lemma3 m a b (A B : seq nat) :
  (size A + size B <= m)%N -> is_trace (a :: A) (b :: B) ->
  mu (walk_to_corner m (a, b)) (charfun (a :: A) (b :: B)) = RHSL3 a b A B.
Proof using.
elim: m a b A B => [/= | m IHm] /= a b A B.
  rewrite leqn0 addn_eq0 size_eq0 size_eq0 => /andP [/eqP HA /eqP HB]; subst.
  by move => HT; rewrite /charfun eq_refl /= /RHSL3 /belast /= !big_nil.
case: (altP (size (hook_box_indices (a, b)) =P O)) => [HO|Hn0].
  move=> _ Htrace; rewrite walk_to_corner_end_simpl //.
  move: HO => /eqP; rewrite (is_trace_corner_nil Htrace) => /andP [/eqP Ha /eqP Hb].
  by subst A B; rewrite /charfun /= eq_refl /= /RHSL3 /= !big_nil.
move=> Hs Ht; rewrite walk_to_corner_decomp //.
have:= Hn0; rewrite (is_trace_corner_nil Ht) negb_and.
have -> (u v : bool) : ~~u || ~~v = [|| (~~u && ~~v), (u && ~~v) | (~~ u && v)].
  by case: u; case: v.
move=> /or3P [] /andP [HA HB].
- case: A B HA HB Hs Ht => [//= | A0 A] [//= | B0 B] _ _ Hsize Htrace /=.
  rewrite (IHm a B0 (A0 :: A) B); first last.
    * exact: (is_trace_tlr _ Htrace).
    * by move: Hsize => /=; rewrite addnS ltnS.
  rewrite (IHm A0 b A (B0 :: B)); first last.
    * exact: (is_trace_tll _ Htrace).
    * by move: Hsize => /=; rewrite addSn ltnS.
  rewrite {IHm Hsize Hn0} size_hook_box_indices -subn1.
  rewrite /RHSL3 /= !big_cons.
  set lA := (last A0 A); set lB := (last B0 B).
  move: (belast A0 A) => A'; move: (belast B0 B) => B'.
  move: (\prod_(j <- A') (1 / ((hook_length p (j, lB))%:Q - 1))) => /= PjlB.
  move: (\prod_(j <- B') (1 / ((hook_length p (lA, j))%:Q - 1))) => /= PlAj.
  rewrite !div1r.
  rewrite -![(_ * PjlB)]mulrC mulrA -![(_ * PlAj)%R]mulrC.
  rewrite ![PlAj * (_ * _)]mulrA -mulrDr -[LHS]mulrA.
  rewrite -[RHS]mulrA ![_ * (PlAj * _)]mulrCA [RHS]mulrA; congr *%R.
  have /= := hook_length_last_rectangle Htrace.
  rewrite -/lA -/lB => ->; rewrite -addnBA // addnC -addnBA //.
  rewrite PoszD !subn1 !hook_length_pred intrD.
  set Alen := (hook_length p (lA, b)).-1.
  set Blen := (hook_length p (a, lB)).-1.
  have Alen0 : Alen != O.
    rewrite /Alen /lA -size_hook_box_indices.
    by rewrite (is_trace_corner_nil (is_trace_lastl Htrace)).
  have Blen0 : Blen != O.
    rewrite /Blen /lB -size_hook_box_indices.
    by rewrite (is_trace_corner_nil (is_trace_lastr Htrace)).
  have:= @addf_div rat_fieldType 1 Alen%:Q 1 Blen%:Q.
  rewrite addrC !div1r !mul1r => ->; rewrite ?intr_eq0 ?eqz_nat //.
  rewrite addrC [LHS]mulrC mulrA mulVf; first by rewrite mul1r invfM mulrC.
  rewrite -mulrzDl /= intr_eq0 eqz_nat.
  by rewrite addn_eq0 negb_and Alen0 Blen0.
- move: HA => /eqP HA; subst A.
  rewrite [X in (_ + X)]walk_to_corner_emptyl // addr0.
  have HBd := esym (cons_head_behead O HB).
  rewrite {2}HBd.
  rewrite (IHm a (head O B) [::] (behead B)); first last.
    * by rewrite -HBd; apply: (is_trace_tlr HB Ht).
    * rewrite size_behead; move: HB Hs.
      case B => [//= | B0 B'] _ /=.
      by rewrite !add0n.
  rewrite /RHSL3 !big_nil /=.
  rewrite {3}HBd (belast_cat b [:: head O B] (behead B)) big_cat big_seq1 /=.
  rewrite size_hook_box_indices.
  by rewrite hook_length_pred !mul1r mulrC.
- move: HB => /eqP HB; subst B.
  rewrite walk_to_corner_emptyr  // add0r.
  have HAd := esym (cons_head_behead O HA).
  rewrite {2}HAd.
  rewrite (IHm (head O A) b (behead A) [::]); first last.
    * by rewrite -HAd; apply: (is_trace_tll HA Ht).
    * rewrite size_behead; move: HA Hs.
      case A => [//= | A0 A'] _ /=.
      by rewrite !addn0.
  rewrite /RHSL3 !big_nil /=.
  rewrite {3}HAd (belast_cat a [:: head O A] (behead A)) big_cat big_seq1 /=.
  rewrite size_hook_box_indices.
  by rewrite hook_length_pred !mulr1 mulrC div1r.
Qed.


(** Choose a box in [p] *)

Definition choose_corner : distr ((seq nat) * (seq nat)) :=
  Mlet (Random (sumn p).-1)
       (fun n => let (r, c) := (reshape_index p n, reshape_offset p n) in
                 walk_to_corner (hook_length p (r, c)).-1 (r, c)).

Section EndsAt.

Definition starts_at rc t := (head O t.1 == rc.1) && (head O t.2 == rc.2).
Definition ends_at   rc t := (last O t.1 == rc.1) && (last O t.2 == rc.2).
Definition RHSL3_trace t :=
  (RHSL3 (head O t.1) (head O t.2) (behead t.1) (behead t.2)).

Variable (Alpha Beta : nat).
Hypothesis Hcorn : corner_box p (Alpha, Beta).

Lemma sumnpSPE : (sumn p).-1.+1 = sumn p.
Proof using Hcorn.
have Hszp : (Alpha < size p)%N.
  move: Hcorn; rewrite /corner_box /is_rem_corner => /andP [H _].
  move: H; apply contraLR; rewrite -!ltnNge ltnS => H.
  by rewrite (nth_default _ H).
move: Hszp; case: p => /= [] [//= | p0 p'].
move=> /part_head_non0 /= => Hp0 _.
case: p0 Hp0 => [//= | p0] _.
by rewrite !addSn.
Qed.


Lemma reshape_index_walk_to i (r := reshape_index p i) (c := reshape_offset p i) :
  (i < sumn p)%N ->
  mu (walk_to_corner (hook_length p (r, c)).-1 (r, c))
     (fun pair => (ends_at (Alpha, Beta) pair)%:Q) =
  \sum_(X <- enum_trace Alpha Beta | starts_at (r, c) X) RHSL3_trace X.
Proof using Hcorn.
rewrite /= => /reshape_offsetP; rewrite -/r -/c.
rewrite -/(in_shape p (_, _)) => Hin.
rewrite big_seq_cond.
pose F := (fun X => mu (walk_to_corner (hook_length p (r, c)).-1 (r, c))
                       (charfun X.1 X.2)).
rewrite (eq_bigr F); first last.
  move=> /= [A B] /and3P/= [].
  rewrite /F (enum_traceP Hcorn).
  move => /and3P [Htrace HAlpha HBeta] /eqP <- /eqP <- {F r c Hin}.
  rewrite /RHSL3_trace /=.
  rewrite -(Lemma3 (m := (hook_length p (head O A, head O B)).-1)) /=;
      first last.
  - by have:= Htrace => /and3P [HA HB _]; rewrite !cons_head_behead.
  - have:= Htrace => /and3P [HA HB _].
    case: A B HA HB Htrace {HAlpha HBeta} => [//= | a A] [//= | b B] /= _ _ Htrace.
    rewrite addnC.
    exact: (leq_add (trace_size_arm_length Htrace) (trace_size_leg_length Htrace)).
  apply: Mstable_eq => [] [X1 X2].
  by have:= Htrace => /and3P [HA HB _]; rewrite !cons_head_behead.
rewrite -big_seq_cond.
transitivity (\sum_(i0 <- enum_trace Alpha Beta) F i0).
- rewrite /F {F} -mu_stable_sum /ends_at.
  have H := mu_walk_to_corner_is_trace Hin (leqnn _).
  rewrite (mu_bool_cond _ H).
  apply Mstable_eq => [[A B]] /=.
  rewrite /charfun -in_seq_sum; last exact: enum_trace_uniq.
  by rewrite enum_traceP.
- rewrite (bigID (starts_at (r, c))) /= -[RHS]addr0; congr (_ + _).
  apply big1 => [[A B]]; rewrite /starts_at /F {F} /= => H.
  apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv _ _ _)) => [] [X Y] /=.
  apply /implyP => /and4P [_ _ /eqP Hr /eqP Hc].
  move: H; apply contra => /eqP [ <- <-].
  by rewrite Hr Hc !eq_refl.
Qed.

Lemma prob_choose_corner_ends_at :
  mu choose_corner (fun pair => (ends_at (Alpha, Beta) pair)%:Q) =
  1 / (sumn p)%:Q * \sum_(X <- enum_trace Alpha Beta) RHSL3_trace X.
Proof using Hcorn.
rewrite /choose_corner MLet_simpl mu_random_sum sumnpSPE.
rewrite mulrC mul1r; congr (_ * _).
rewrite big_nat /= (eq_bigr _ reshape_index_walk_to) -big_nat.
rewrite (exchange_big_dep (@predT _)) //=.
apply eq_big_seq => [[A B]].
rewrite (enum_traceP Hcorn) => /and3P [Htrace HA HB].
have Hin : (head O B < nth O p (head O A))%N.
  have:= Htrace => /and3P [HA0 HB0 _].
  case: A B HA0 HB0 Htrace {HA HB} => [//= | a A] [//= | b B] /= _ _ Htrace.
  exact: (is_trace_in_shape Htrace).
rewrite -big_filter (bigD1_seq (flatten_index p (head O A) (head O B))) /=;
    first last.
- by apply filter_uniq; apply: iota_uniq.
- rewrite mem_filter (flatten_indexKr Hin) (flatten_indexKl Hin).
  rewrite /starts_at !eq_refl /= mem_iota add0n subn0 /=.
  exact: flatten_indexP.
rewrite -[RHS]addr0; congr (_ + _).
rewrite big_filter_cond; apply big_pred0 => i.
rewrite /starts_at /=.
case: eqP => //= ->; case: eqP => //= ->.
by rewrite reshape_indexK eq_refl.
Qed.

End EndsAt.


(** * The proof *)
Section Formula.

Variable T : countType.
Variable R : comRingType.
Variable alpha : T -> R.

Lemma expand_prod_add1_seq (S : seq T) :
  uniq S ->
  \prod_(i <- S) (1 + alpha i) = \sum_(s : subseqs S) \prod_(i <- s) alpha i.
Proof using.
elim: S => [| a S IHs] aS_uniq //=.
  by rewrite (big_subseqs0 (fun s => \prod_(i <- s) alpha i)) !big_nil.
have /= /andP[_ S_uniq] :=  aS_uniq.
rewrite (big_subseqs_cons (fun s => \prod_(i <- s) alpha i) aS_uniq) /=.
rewrite big_cons {}IHs // addrC mulrDl mul1r; congr (_ + _).
rewrite mulr_sumr; apply eq_bigr => /= [[s subs] _] /=.
by rewrite big_cons.
Qed.

End Formula.


Section Theorem2.

Variable (Alpha Beta : nat).
Hypothesis Hcorn : corner_box p (Alpha, Beta).

Let p' := decr_nth p Alpha.

Fact Hcrn : is_rem_corner p Alpha.
Proof using Hcorn. by have:= Hcorn => /andP [Hcrn /eqP HBeta]. Qed.
Hint Resolve Hcrn : core.

Fact Hp : incr_nth p' Alpha = p. Proof using Hcorn. exact: decr_nthK. Qed.
Fact Hpart' : is_part p'. Proof using Hcorn. exact: is_part_decr_nth. Qed.
Let Hpartc' : is_part (conj_part p') := is_part_conj Hpart'.
Hint Resolve Hpart' Hpartc' : core.

Fact HBeta : Beta = (nth O p Alpha).-1.
Proof using Hcorn. by have:= Hcorn => /andP [Hcrn /eqP HBeta]. Qed.
Fact HBeta' : Beta = (nth O p' Alpha).
Proof using Hcorn. by rewrite HBeta -Hp nth_incr_nth eq_refl add1n. Qed.

Lemma Formula1 :
  (hook_length_prod p)%:Q / (hook_length_prod p')%:Q =
  ( \prod_(0 <= i < Alpha) (1 + ((hook_length p (i, Beta) )%:Q - 1)^-1) ) *
  ( \prod_(0 <= j < Beta)  (1 + ((hook_length p (Alpha, j))%:Q - 1)^-1) ).
Proof using Hpartc'.
rewrite /hook_length_prod /= !big_box_skew /= (* /hook_length *).
rewrite -{1}Hp -(perm_big _ (box_in_incr_nth _ _)) /= big_cons.
rewrite !PoszM /= !intrM /=.
rewrite !(big_morph Posz PoszM (id1 := Posz 1%N)) //=.
rewrite !(big_morph intr (@intrM _) (id1 := 1)) //=.
rewrite -mulrA.
rewrite -HBeta' (corner_hook_length1 (intpartP p) Hcorn) mul1r.
rewrite -prodf_div /=.
rewrite (bigID (fun i => i.1 == Alpha)) /=.
rewrite mulrC (bigID (fun i => i.2 == Beta)) /= mulrC mulrA.
rewrite [RHS]mulrC -[RHS]mulr1; congr (_ * _ * _).

(* Hooks on the row of (Alpha, Beta) *)
- exact: prod_hook_length_quot_row.

(* Hooks on the column of (Alpha, Beta) *)
- have Hpartconj := is_part_conj (intpartP p).
  have Hcornconj := corner_box_conj_part (intpartP p) Hcorn.
  have Hconj' : (decr_nth (conj_part p) Beta) = conj_part p'.
    rewrite -Hp conj_part_incr_nth //; last exact: add_corner_decr_nth.
    rewrite -HBeta' incr_nthK //.
    apply (is_part_incr_nth Hpartc').
    rewrite HBeta'; apply (is_add_corner_conj_part Hpart').
    exact: add_corner_decr_nth.

  transitivity (\prod_(0 <= j < Alpha)
                 (1 + ((hook_length (conj_part p) (Beta, j))%:Q - 1)^-1)); first last.
    by apply eq_bigr => i _; rewrite hook_length_conj_part.
  rewrite  -(prod_hook_length_quot_row Hpartconj Hcornconj) Hconj'.
  pose swap i : nat * nat := (i.2, i.1).
  have swap_inj : injective swap by apply (can_inj (g := swap)) => [] [r c].
  rewrite -[RHS]big_filter; set F := (X in \prod_(i <- _) X i).
  rewrite -[X in \prod_(i <- X) _]map_id.
  rewrite (eq_map (f2 := swap \o swap)); last by move=> [r c].
  rewrite map_comp big_map.
  transitivity (\prod_(i <- enum_box_in p' |
                       (i.1 != Alpha) && (i.2 == Beta))  F (swap i)).
    apply eq_bigr => [[r c]] _.
    by rewrite /swap /F {F} /= !hook_length_conj_part.
  rewrite -big_filter; apply: perm_big => {F}.
  apply uniq_perm.
  + by apply filter_uniq; apply: enum_box_in_uniq.
  + rewrite (map_inj_uniq swap_inj).
    by apply filter_uniq; apply: enum_box_in_uniq.
  + move=> [r c] /=.
    rewrite -/(swap (c, r)) (mem_map swap_inj) !mem_filter /=.
    rewrite !mem_enum_box_in !unfold_in /= -!/(in_shape _ (_, _)).
    rewrite -in_conj_part //.
    case: (boolP (in_shape p' (r, c))) => Hrc; last by rewrite !andbF.
    case: (altP (c =P Beta)) => /= Hc; last by rewrite !andbF.
    rewrite !andbT.
    move: Hrc; rewrite /in_shape Hc HBeta'.
    by rewrite ltnNge; apply contra => /eqP ->.

(* Hooks neither on the row or column of (Alpha, Beta) *)
- rewrite big_seq_cond; apply big1 => [[r c]] /= /and3P [].
  rewrite mem_enum_box_in unfold_in => Hrc Hr Hc.
  rewrite -Hp hook_length_incr_nth.
  + by rewrite divff // intr_eq0.
  + exact: is_part_decr_nth.
  + exact: add_corner_decr_nth.
  + exact: Hrc.
  + by rewrite eq_sym.
  + move: Hc; rewrite eq_sym HBeta -Hp.
    by rewrite nth_incr_nth eq_refl add1n.
Qed.

Lemma SimpleCalculation :
  \sum_(X <- enum_trace Alpha Beta) RHSL3_trace X =
  (hook_length_prod p)%:Q / (hook_length_prod p')%:Q.
Proof using Hpartc'.
rewrite /enum_trace /trace_seq /RHSL3_trace /RHSL3 big_allpairs /=.
rewrite Formula1 !expand_prod_add1_seq /index_iota ?iota_uniq //.
rewrite /index_iota subn0 big_map big_distrl big_enum; apply eq_bigr=> A _.
rewrite /index_iota subn0 big_map big_distrr big_enum; apply eq_bigr=> B _.
rewrite /= !belast_behead_rcons !last_behead_rcons.
by congr (_ * _); apply eq_big_seq => L _; rewrite mul1r.
Qed.

Theorem Theorem2 :
  mu choose_corner (fun pair => (ends_at (Alpha, Beta) pair)%:Q) =
  (HLF p') / (HLF p).
Proof using Hpartc'.
rewrite prob_choose_corner_ends_at // -{1 2}Hp sumn_incr_nth.
rewrite factS PoszM -!ratzE ratzM !ratzE.
rat_to_ring.
set Rhs := (RHS).
have -> : Rhs = ((1 / (sumn p').+1%:Q) *
                 (hook_length_prod p)%:Q / (hook_length_prod p')%:Q).
  rewrite /Rhs -!mulrA [(((hook_length_prod p')%:Q)^-1 / _)%R]mulrC !invfM !mul1r.
  rewrite !mulrA [X in (X / _ / _ / _)]mulrC.
  congr (_ * _); rewrite -!mulrA; congr (_ * _).
  rewrite mulrA divff; first by rewrite invrK mul1r.
  rewrite intr_eq0 eqz_nat -lt0n.
  exact: fact_gt0.
rewrite {Rhs} !mul1r -[RHS]mulrA; congr (_ * _).
exact: SimpleCalculation.
Qed.

End Theorem2.

Open Scope ring_scope.

Lemma ends_at_rem_cornerE :
  (fun X : seq nat * seq nat =>
     \sum_(i0 <- rem_corners p) (ends_at (i0, (nth O p i0).-1) X)%:Q)
    == (fun X => (corner_box p (last O X.1, last O X.2))%:Q).
Proof using.
rewrite /ends_at => [] [A B] /=.
case (boolP (corner_box p (last O A, last O B))) => Hcorn.
- rewrite (bigD1_seq (last O A) _ (rem_corners_uniq p)) /=; first last.
    move: Hcorn; rewrite /rem_corners /corner_box => /andP [Hcorn _].
    rewrite mem_filter Hcorn mem_iota add0n leq0n /=.
    move: Hcorn; rewrite /is_rem_corner.
    by apply contraLR; rewrite -!ltnNge ltnS => /(nth_default O) ->.
  move: Hcorn; rewrite /corner_box eq_refl => /andP [_ ->] /=.
  by rewrite big1 // => i; rewrite eq_sym => /negbTE ->.
- rewrite big_seq_cond big1 // => i.
  rewrite mem_filter andbT => /andP [Hout _].
  suff /negbTE -> : ~~ ((last O A == i) && (last O B == (nth O p i).-1)) by [].
  move: Hcorn; rewrite /corner_box; apply contra => /andP [/eqP Hi].
  by subst i => ->; rewrite Hout.
Qed.

Corollary Corollary4 :
  p != empty_intpart ->
  \sum_(i <- rem_corners p) (HLF (decr_nth p i)) / (HLF p) = 1.
Proof using.
rewrite big_seq_cond => Hp.
under eq_bigr => i /andP[].
  rewrite /rem_corners mem_filter => /andP[Hcorn _] _.
  rewrite -(Theorem2 (Beta := (nth O p i).-1)); first last.
    by rewrite /corner_box Hcorn eqxx.
over.
rewrite -big_seq_cond -mu_stable_sum.
rewrite /choose_corner Mlet_simpl mu_random_sum.
have Hsum : (sumn p) != 0%N.
  by move: Hp; apply contra => /eqP/empty_intpartP ->.
rewrite prednK ?lt0n // big_nat /=.
rewrite (eq_bigr (fun => 1)).
  rewrite -big_nat big_const_seq count_predT size_iota subn0 iter_addr addr0.
  by rat_to_ring; rewrite divff // pnatr_eq0.
move=> i Hi; have:= reshape_offsetP Hi; move/reshape_indexP: Hi.
rewrite -/(in_shape p (_, _)) => Hind Hoff.
rewrite (Mstable_eq _ ends_at_rem_cornerE).
apply: (mu_bool_impl1 _ (fun X => is_trace X.1 X.2)).
  by move=> [A B] /=; apply/implyP => /and5P [].
exact: mu_walk_to_corner_is_trace.
Qed.

Corollary Corollary4_eq :
  p != empty_intpart ->
  \sum_(i <- rem_corners p) (HLF (decr_nth_intpart p i)) = HLF p.
Proof using.
move=> /Corollary4; rewrite -mulr_suml => /divr1_eq <-.
apply eq_big_seq => i; rewrite mem_filter => /andP [Hi _].
by rewrite /= Hi.
Qed.

End FindCorner.

Theorem HookLengthFormula_rat (p : intpart) :
  ( (#|{:stdtabsh p}|)%:Q = HLF p )%R.
Proof.
apply esym; move: p; apply card_stdtabsh_rat_rec.
- by rewrite /= /hook_length_prod /= big_box_skew /= big_nil factE.
- move=> p Hp; apply esym.
  exact: Corollary4_eq.
Qed.


Lemma hook_length_prod_non0 (p : intpart) : (hook_length_prod p) != 0.
Proof.
rewrite /hook_length_prod -eqz_nat !(big_morph Posz PoszM (id1 := Posz 1%N)) //.
by apply/prodf_neq0 => [] [] [r c].
Qed.

Lemma hook_length_prod_nat (p : intpart) :
  #|{:stdtabsh p}| * (hook_length_prod p) = (sumn p)`!.
Proof.
apply /eqP; rewrite -eqz_nat PoszM.
rewrite -(@eqr_int rat_numDomainType) intrM /=.
have /= -> := HookLengthFormula_rat p.
apply/eqP; rewrite -mulrA -[RHS]mulr1; congr (_ * _)%R.
rewrite mulrC divff // intr_eq0.
by rewrite eqz_nat; apply: hook_length_prod_non0.
Qed.

Lemma hook_length_prod_div (p : intpart) : (hook_length_prod p) %| (sumn p)`!.
Proof.
by apply/dvdnP; exists #|{:stdtabsh p}|; rewrite hook_length_prod_nat.
Qed.

Theorem HookLengthFormula (p : intpart) :
  #|{:stdtabsh p}| = (sumn p)`! %/ (hook_length_prod p).
Proof.
by rewrite -hook_length_prod_nat mulnK // lt0n; exact: hook_length_prod_non0.
Qed.
