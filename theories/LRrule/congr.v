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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
Require Import Recdef path.
Require Import permuted vectNK.


Set Implicit Arguments.
Unset Strict Implicit.

(******************************************************************************)
(* Equivalence and congruence closure of a rewriting rule on words            *)
(*                                                                            *)
(* The rewriting rule is given as a map 'rule : word -> seq word'             *)
(* The closure is a relation (type : rel word)                                *)
(*                                                                            *)
(* We suppose that equivalence classes are *finite*, this is sufficient for   *)
(* out purpose here that is the construction of the plactic monoid. This also *)
(* ensure that the generated equivalence relation is decidable by bounding    *)
(* the lenght of the rewriting paths. Concretely this is done by requiring    *)
(* that rule is included in a refexive relation invar which is invariant by   *)
(* rewriting rule, that is:                                                   *)
(*   Hypothesis Hinvar : forall x0 x, invar x0 x -> all (invar x0) (rule x).  *)
(*                                                                            *)
(* We show that this is true for homogeneous rules (ie: that permutes words   *)
(*   Hypothesis Hhomog : forall u : word, all (perm_eq u) (rule u).           *)
(*                                                                            *)
(* Also to simplify the code, we assume that the rule are symmetric, that is  *)
(*   Hypothesis Hsym : forall x y, x \in rule y -> y \in rule x.              *)
(*                                                                            *)
(* Assuming the two latter hypothesis, we define a relation gencongr which is *)
(* the congruence transitive closure of rule. The main results here are       *)
(* - gencongrP    : gencongr is the smallest transitive congruence relation   *)
(*                  contaning rule.                                           *)
(* - gencongr_ind : induction principle on classes for gencongr, any property *)
(*                  preserved along the rewriting rule holds for classes.     *)
(******************************************************************************)

(* Basic facts on congruences:                                                *)
(* equivalence of various definitions and immediate consequences              *)
Section CongruenceFacts.

Variable Alph : eqType.
Notation word := (seq_eqType Alph).

Definition congruence_rel (r : rel word) :=
  forall a b1 c b2, r b1 b2 -> r (a ++ b1 ++ c) (a ++ b2 ++ c).

Variable r : rel word.
Hypothesis Hcongr : congruence_rel r.
Hypothesis Hequiv : equivalence_rel r.

Lemma congr_cons w1 w2 a : r w1 w2 -> r (a :: w1) (a :: w2).
Proof.
  rewrite -[a :: w1]cat1s -[[:: a] ++ w1]cats0 -catA.
  rewrite -[a :: w2]cat1s -[[:: a] ++ w2]cats0 -catA.
  by apply: Hcongr.
Qed.

Lemma congr_rcons w1 w2 a : r w1 w2 -> r (rcons w1 a) (rcons w2 a).
Proof.
  rewrite -[rcons w1 a]cats1 -[w1 ++ [:: a]]cat0s.
  rewrite -[rcons w2 a]cats1 -[w2 ++ [:: a]]cat0s.
  by apply: Hcongr.
Qed.

Lemma congr_catl u1 u2 v : r u1 u2 -> r (u1 ++ v) (u2 ++ v).
Proof. rewrite -[u1 ++ v]cat0s -[u2 ++ v]cat0s; by apply: Hcongr. Qed.

Lemma congr_catr u v1 v2 : r v1 v2 -> r (u ++ v1) (u ++ v2).
Proof. rewrite -[u ++ v1]cats0 -[u ++ v2]cats0 -!catA; by apply: Hcongr. Qed.

Lemma congr_cat u1 u2 v1 v2 : r u1 u2 -> r v1 v2 -> r (u1 ++ v1) (u2 ++ v2).
Proof.
  have:= Hequiv => /equivalence_relP [] Hrefl Htrans.
  move=> Hu Hv; rewrite (Htrans _ (u1 ++ v2)).
  - by apply: congr_catl.
  - by apply: congr_catr.
Qed.

End CongruenceFacts.

(* Transitive closure of a rule with finite classes                           *)
(* Since we only need to contruct it and not to compute with it, we use a     *)
(* simple but extremely inefficient algorithm                                 *)
Section Transitive.

Variable T : eqType.
Variable rule : T -> seq T.
Variable invar : pred T.
Hypothesis Hinvar : forall x, invar x -> all invar (rule x).

Section FullKnown.

Variable full : seq T.
Hypothesis Hfull : forall x, invar x -> x \in full.

Theorem full_bound :
  forall s : seq T, all invar s -> uniq s -> size s <= size full.
Proof.
  move=> s /allP Hall Huniq; apply: uniq_leq_size; first exact Huniq.
  move=> l Hl. by apply: (Hfull (Hall _ Hl)).
Qed.

End FullKnown.

Variable bound : nat.
Hypothesis Hbound: forall s : seq T, all invar s -> uniq s -> size s <= bound.

Lemma invar_undupE s : all invar (undup s) = all invar s.
Proof.
  apply/(sameP idP); apply(iffP idP); move/allP => H; apply/allP => x Hx; apply: H;
    move: Hx; by rewrite mem_undup.
Qed.

Definition step s := undup (s ++ flatten (map rule s)).

Lemma step_mem s x y : y \in rule x -> x \in s -> y \in step s.
Proof.
  move=> Hrule Hx.
  rewrite /step mem_undup mem_cat; apply/orP; right.
  apply/flattenP; exists (rule x); last by [].
  by apply: map_f.
Qed.

Lemma uniq_step s : uniq (step s).
Proof. by rewrite /step; apply: undup_uniq. Qed.

Lemma undup_step s : undup (step s) = step s.
Proof. by rewrite /step [undup (undup _)]undup_id; last by apply: undup_uniq. Qed.

Lemma invar_step s : all invar s -> all invar (step s).
Proof.
  rewrite /step => /allP H; apply/allP => x.
  rewrite mem_undup mem_cat => /orP []; first by apply: H.
  move=> /flattenP [] tmp /mapP [] y Hyins -> {tmp} Hxy.
  have:= Hinvar (H _ Hyins) => /allP; by apply.
Qed.

Lemma subset_step s : {subset s <= step s}.
Proof. rewrite /step => x Hx; by rewrite mem_undup mem_cat Hx. Qed.

Lemma subset_undup_step s : {subset undup s <= step s}.
Proof. rewrite /step => x; rewrite mem_undup => Hx; by rewrite mem_undup mem_cat Hx. Qed.

(* This is a very unefficient transitive closure algorithm *)
Function trans (s : seq T) {measure (fun s => bound - size (undup s))} : seq T :=
  let us := undup s in
  if all invar us then
    let news := step s in
    if size news > size us then trans news
    else us
  else us.
Proof.
  move=> s Hinv H; rewrite undup_step; apply/ltP.
  have Hszus:= Hbound Hinv (undup_uniq s).
  rewrite invar_undupE in Hinv.
  have Hszn:= Hbound (invar_step Hinv) (uniq_step s).
  by apply: ltn_sub2l; first by apply: (leq_trans H).
Qed.

Lemma subset_s_trans_s s : {subset s <= trans s}.
Proof.
  apply trans_ind => //= {s}.
  * move=> s _ _ H x Hx; exact (H _ (subset_step Hx)).
  * move=> s _ tmp _ {tmp} _ x; by rewrite mem_undup.
  * move=> s _ tmp _ {tmp} x; by rewrite mem_undup.
Qed.

CoInductive rewrite_path x y : Prop :=
  Rew : forall l, path [rel of rule] x l -> y = last x l -> rewrite_path x y.

Lemma invar_rewrite_path x y : invar x -> rewrite_path x y -> invar y.
Proof.
  move=> Hx [] l.
  elim: l x Hx => [x Hx _ -> //= | l0 l IHl] x Hx /= /andP [] Hrule /IHl; apply.
  have:= Hinvar Hx => /allP; by apply.
Qed.

Lemma step_closed x s y :
  undup s =i step s -> x \in s -> rewrite_path x y -> y \in s.
Proof.
  move=> H Hx [] l.
  elim: l x Hx => [x Hx _ -> //= | l0 l IHl] x Hx /= /andP [] Hrule /IHl; apply.
  have:= H l0; rewrite mem_undup => ->.
  exact (step_mem Hrule Hx).
Qed.

Lemma transP y l:
  all invar l -> reflect (exists x, x \in l /\ rewrite_path x y) (y \in trans l).
Proof.
  move=> Hl; apply: (iffP idP).
  + move: Hl; apply trans_ind => //=.
    * move=> s _ Hsz IH Hall Hy.
      case (IH (invar_step Hall) Hy) => x [] Hx Hrew.
      move: Hx; rewrite /step mem_undup mem_cat => /orP []; first by exists x.
      move=> /flattenP [] tmp /mapP [] z Hyins -> {tmp} Hxy.
      exists z; split; first exact Hyins.
      move: Hrew => [] path Hpath Hlast.
      by apply: (Rew (l := x :: path)); first by rewrite /= Hxy Hpath.
    * move=> s _ x <-; case (ltnP (size (undup s)) (size (step s))) => //= Hsz _.
      have:= leq_size_perm (undup_uniq s) (subset_undup_step (s:= s)) Hsz.
      move=> [] Heq _ _; rewrite mem_undup => Hy.
      exists y; split => //=; by apply: (Rew (l := [::])).
    * move=> s x <-; rewrite invar_undupE; by case (all invar s).
  + move: Hl y; apply trans_ind => //=.
    * move=> s _ Hsz IH Hinv y [] x [] Hxins [].
      case.
      - move=> Hpath /= ->; by apply: subset_s_trans_s; apply: subset_step.
      - move=> z pat /= /andP [] Hz Hpath ->.
        apply: IH; first by apply: invar_step.
        exists z; split; first by apply: (step_mem Hz).
        by apply: (Rew Hpath).
    * move=> s _ x <-; case (ltnP (size (undup s)) (size (step s))) => //= Hsz _.
      have:= leq_size_perm (undup_uniq s) (subset_undup_step (s:= s)) Hsz.
      move=> [] Heq _ _ y {x} [] x [] Hx Hrew.
      rewrite mem_undup; by apply: (step_closed Heq Hx).
    * move=> s x <-; rewrite invar_undupE; by case (all invar s).
Qed.

Lemma rewrite_path_trans x y z : rewrite_path x y -> rewrite_path y z -> rewrite_path x z.
Proof.
  move=> [] pathxy Hxy Hy [] pathyz Hyz Hz.
  apply: (Rew (l := pathxy ++ pathyz)).
  + by rewrite cat_path Hxy -Hy Hyz.
  + by rewrite last_cat -Hy.
Qed.

Lemma rewrite_path_sym x y :
  (forall x y, x \in rule y -> y \in rule x) ->
  rewrite_path x y -> rewrite_path y x.
Proof.
  move=> Hsym [] pathxy; rewrite -rev_path => Hxy Hy.
  move: Hxy; rewrite -Hy.
  case/lastP: pathxy Hy => [/= -> _ | pathxz z]; first by apply: (Rew (l := [::])).
  rewrite last_rcons belast_rcons rev_cons => -> {y} Hpath.
  apply: (Rew (l := rcons (rev pathxz) x)).
  + set rel := (X in path X _ _) in Hpath; set rel2 := (X in path X _ _).
    have /eq_path -> : rel2 =2 rel; last exact Hpath.
    move=> i j; rewrite /rel /rel2.
    apply/(sameP idP); apply(iffP idP); by apply: Hsym.
  + by rewrite last_rcons.
Qed.

End Transitive.

(* Deals with the dependance of invar on x *)
Section Depend.

Variable T : eqType.
Variable rule : T -> seq T.

Record invariant_context :=
  InvariantContext {
      invar : T -> pred T;
      Hinvar_all : forall x, invar x x;
      Hinvar : forall x0 x, invar x0 x -> all (invar x0) (rule x);
      bound : T -> nat;
      Hbound: forall x s, all (invar x) s -> uniq s -> size s <= bound x
    }.
Variable inv : invariant_context.
Hypothesis Hsym : forall x y, x \in rule y -> y \in rule x.

Definition rclass x := trans (@Hinvar inv x) (@Hbound inv x) [:: x].
Definition rtrans : rel T := fun x y => y \in rclass x.

Lemma rtransP x y : reflect (rewrite_path rule y x) (rtrans y x).
Proof.
  rewrite /rtrans /rclass.
  apply: (iffP idP).
  - move/transP => H.
    have: (all (invar inv y) [:: y]).
      apply/allP=> z; rewrite mem_seq1 => /eqP ->.
      by apply Hinvar_all.
    by move/H => [] z []; rewrite mem_seq1 => /eqP ->.
  - move=> H; apply/transP.
    + apply/allP=> x0; rewrite mem_seq1 => /eqP ->.
      by apply Hinvar_all.
    + by exists y; rewrite mem_seq1.
Qed.

Theorem equiv_rtrans : equivalence_rel rtrans.
Proof.
  rewrite equivalence_relP; split.
  - rewrite /reflexive /rtrans /rclass => x.
    by apply: subset_s_trans_s; rewrite mem_seq1.
  - rewrite /left_transitive => x y Hrxy z.
    apply/(sameP idP); apply(iffP idP); move: Hrxy.
    * move=> /rtransP Hryx /rtransP Hrzy; apply/rtransP.
      by apply: (rewrite_path_trans (y := y)).
    * move=> /rtransP Hryx /rtransP Hrzx; apply/rtransP.
      have:= rewrite_path_sym Hsym Hryx => Hrzy; by apply: (rewrite_path_trans (y := x)).
Qed.

Lemma rtrans_ind (P : T -> Prop) x :
  P x -> (forall y z, P y -> z \in rule y -> P z) -> forall t, rtrans x t -> P t.
Proof.
  move=> Hx IHr t /rtransP [] l; elim: l x Hx t => [|l0 l IHl] x Hx t /= Hpath -> //=.
  move: Hpath => /andP [] Hl0 Hpath.
  by apply: (@IHl l0); first by apply: (@IHr x).
Qed.

Lemma rule_rtrans x y : y \in rule x -> rtrans x y.
Proof.
  move=> Hrule; apply/rtransP.
    by apply: (Rew (l := [:: y])); first rewrite /= Hrule.
Qed.

Lemma rewrite_path_min (r : rel T) :
  equivalence_rel r -> (forall x y, y \in rule x -> r x y) ->
  forall x y, rewrite_path rule x y -> r x y.
Proof.
  rewrite equivalence_relP => [] [] Hrefl Htr Hin x y [] l.
  elim: l x => [/= x _ -> | l0 l IHl] /=; first by apply: Hrefl.
  move=> x /andP [] /Hin Hl0 /IHl H/H {IHl H} Hl0y.
  by rewrite (Htr _ _ Hl0 y).
Qed.

Lemma rtrans_min (r : rel T) :
  equivalence_rel r -> (forall x y, y \in rule x -> r x y) ->
  forall x y, rtrans x y -> r x y.
Proof. move/rewrite_path_min=> H/H{H} H x y /rtransP Hrew; by apply: H. Qed.

End Depend.


Section CongruenceClosure.

Variable Alph : eqType.
Notation word := (seq_eqType Alph).

Definition congruence_rule (rule : word -> seq word) :=
  forall a b1 c b2, b2 \in rule b1 -> (a ++ b2 ++ c) \in rule (a ++ b1 ++ c).

Variable rule : word -> seq word.
Hypothesis Hsym : forall u v : word, v \in rule u -> u \in rule v.
Hypothesis Hhomog : forall u : word, all (perm_eq u) (rule u).
Hypothesis Hcongr : congruence_rule rule.

Lemma perm_eq_bound (x : word) (s : seq word) :
  all (perm_eq x) s -> uniq s -> size s <= (size x)`!.
Proof. rewrite -(size_permuted x); apply: full_bound; by apply: eq_seqE. Qed.

Lemma Hinvar_perm (x0 x : word) : perm_eq x0 x -> all (perm_eq x0) (rule x).
Proof.
  have:= perm_eq_trans; rewrite /transitive => Ptrans.
  move=> H; apply/allP => x1 Hx1; apply: (@Ptrans _ x _ _ H).
  have:= Hhomog x => /allP; by apply.
Qed.

Let inv := InvariantContext (@perm_eq_refl _) Hinvar_perm perm_eq_bound.
Definition congr := rtrans inv.
Definition congr_class := rclass inv.

Lemma rule_congr x y : y \in rule x -> congr x y.
Proof. by apply: rule_rtrans. Qed.

Lemma congr_ind (P : word -> Prop) x :
  P x -> (forall y z, P y -> z \in rule y -> P z) -> forall t, congr x t -> P t.
Proof. by apply: rtrans_ind. Qed.

Lemma equiv_congr : equivalence_rel congr.
Proof.
  apply: equiv_rtrans; last by move=> x y H; apply: Hsym.
Qed.

Lemma congr_is_congr : congruence_rel congr.
Proof.
  have:= equiv_congr => /equivalence_relP [] Hrefl Htrans.
  move=> a b1 c; apply: congr_ind.
  + by apply: Hrefl.
  + move=> x y Hx Hrule.
    rewrite (@Htrans _ (a ++ x ++ c)); last apply: Hx.
    by apply: rule_congr; apply: Hcongr.
Qed.

Lemma congr_classP x y : congr x y = (y \in congr_class x).
Proof. by rewrite /congr /congr_class /rtrans. Qed.

End CongruenceClosure.


Section CongruenceRule.

Variable Alph : eqType.
Notation word := (seq_eqType Alph).

Variable rule : word -> seq word.
Hypothesis Hhomog : forall u : word, all (perm_eq u) (rule u).
Hypothesis Hsym : forall u v : word, v \in rule u -> u \in rule v.

Definition congrrule s :=
  flatten [seq
             [seq (triple.1.1) ++ b1 ++ (triple.2) | b1 <- rule triple.1.2]
          | triple <- cut3 s ].

Lemma congrruleP u1 u2 :
  reflect (exists a v1 b v2, [/\ u1 = a ++ v1 ++ b, u2 = a ++ v2 ++ b & v1 \in rule v2])
          (u1 \in congrrule u2).
Proof.
  apply: (iffP idP).
  + move/flatten_mapP => [] [] [] a v2 b /=.
    rewrite -cat3_equiv_cut3 => /eqP H2 /mapP [] v1 Hrule H1.
    by exists a; exists v1; exists b; exists v2.
  + move=> [] a [] v1 [] b [] v2 [] H1 H2 Hrule.
    apply/flatten_mapP. exists (a, v2, b); first by rewrite -cat3_equiv_cut3 H2.
    rewrite H1 /=; apply/mapP; by exists v1.
Qed.

Lemma rule_congrrule u v : v \in rule u -> v \in congrrule u.
Proof.
  move=> H; apply/flatten_mapP.
  exists ([::], u, [::]); first by rewrite -cat3_equiv_cut3 cat0s cats0.
  apply/mapP; by exists v; last by rewrite cat0s cats0.
Qed.

Lemma congrrule_is_congr : congruence_rule congrrule.
Proof.
  move=> a b1 c b2 /flatten_mapP [] [[i j1] k].
  rewrite -cat3_equiv_cut3 /= => /eqP -> {b1} /mapP [] j2 Hj2 -> {b2}.
  rewrite !catA [a ++ i]lock -!catA; unlock. set a1 := a ++ i; set c1 := k ++ c.
  apply/flatten_mapP; exists (a1, j1, c1); first by rewrite -cat3_equiv_cut3.
  apply/mapP; by exists j2; first by apply: Hj2.
Qed.

Lemma congrrule_homog u : all (perm_eq u) (congrrule u).
Proof.
  apply/allP => v /flatten_mapP [] [[i j1] k] /=.
  rewrite -cat3_equiv_cut3 /= => /eqP -> /mapP [] j2 Hj2 ->.
  rewrite perm_cat2l perm_cat2r.
  have:= Hhomog j1 => /allP; by apply.
Qed.

Lemma congrrule_sym u v : v \in congrrule u -> u \in congrrule v.
Proof.
  move/flatten_mapP => [] [[i j1] k].
  rewrite -cat3_equiv_cut3 /= => /eqP -> /mapP [] j2 Hj2 ->.
  have {Hj2} Hj2 := (Hsym Hj2); apply: congrrule_is_congr.
  by apply: rule_congrrule.
Qed.

End CongruenceRule.

(* Main results                                                               *)
Section Final.

Variable Alph : eqType.
Notation word := (seq_eqType Alph).

Variable rule : word -> seq word.
Hypothesis Hsym : forall u v : word, v \in rule u -> u \in rule v.
Hypothesis Hhomog : forall u : word, all (perm_eq u) (rule u).

Definition gencongr := (congr (congrrule_homog Hhomog)).
Definition genclass := (congr_class (congrrule_homog Hhomog)).

Lemma genclassP x y : gencongr x y = (y \in genclass x).
Proof. rewrite /gencongr /gencongr. by apply: congr_classP. Qed.

Lemma gencongr_equiv : equivalence_rel gencongr.
Proof. apply: equiv_congr; by apply: congrrule_sym. Qed.

Lemma gencongr_is_congr : congruence_rel gencongr.
Proof.
  apply: congr_is_congr; first by apply: congrrule_sym.
  by apply: congrrule_is_congr.
Qed.

Lemma rule_gencongr u v : v \in rule u -> v \in gencongr u.
Proof. move=> H; apply: rule_congr; by apply: rule_congrrule. Qed.

Lemma gencongr_min (r : rel word) :
  equivalence_rel r -> congruence_rel r ->
  (forall x y, y \in rule x -> r x y) ->
  forall x y, gencongr x y -> r x y.
Proof.
  move=> /equivalence_relP [] Hrefl Htrans Hcongr Hrule x y /rtransP => H.
  have:= H => {H} [] [] l.
  elim: l x => [/= x _ ->| l0 l IHl] ; first by apply: Hrefl.
  move=> x /= /andP [] /flatten_mapP [] [[i j1] k].
  rewrite -cat3_equiv_cut3 /= => /eqP -> {x} /mapP [] j2 Hj2 ->.
  move=> /IHl H/H{H}; rewrite (@Htrans _ (i ++ j2 ++ k)) //=.
  apply: Hcongr; by apply: Hrule.
Qed.

Theorem gencongr_ind (P : word -> Prop) x :
  P x ->
  (forall a b1 c b2, P (a ++ b1 ++ c) -> b2 \in rule b1 -> P (a ++ b2 ++ c)) ->
  forall y, gencongr x y -> P y.
Proof.
  move=> Hx IH; apply: (rtrans_ind Hx).
  move=> y z Hy /flatten_mapP [] [[i j1] k].
  rewrite -cat3_equiv_cut3 /= => /eqP Heqy; subst y.
  move=> /mapP [] j2 Hj2 Hz; subst z.
  by apply: (@IH _ j1).
Qed.

Lemma gencongr_homog u v : v \in gencongr u -> perm_eq u v.
Proof.
  move: v; apply: gencongr_ind; first by apply: perm_eq_refl.
  move=> a b1 c b2 => H Hrule.
  rewrite (perm_eq_trans H); first by [].
  rewrite perm_cat2l perm_cat2r.
  move: (Hhomog b1) => /allP; by apply.
Qed.

CoInductive Generated_EquivCongruence (grel : rel word) :=
  GenCongr : equivalence_rel grel ->
             congruence_rel grel ->
             ( forall u v, v \in rule u -> grel u v ) ->
             ( forall r : rel word,
                      equivalence_rel r -> congruence_rel r ->
                      (forall x y, y \in rule x -> r x y) ->
                      forall x y, grel x y -> r x y
             ) -> Generated_EquivCongruence grel.

Theorem gencongrP : Generated_EquivCongruence gencongr.
Proof.
  constructor.
  + exact gencongr_equiv.
  + exact gencongr_is_congr.
  + exact rule_gencongr.
  + exact gencongr_min.
Qed.

Lemma gencongr_imply r1 r2 :
  Generated_EquivCongruence r1 -> Generated_EquivCongruence r2 ->
  forall x y, r1 x y -> r2 x y.
Proof. case=> Heq1 Hc1 Hr1 Hmin1; case=> Heq2 Hc2 Hr2 _; by apply: Hmin1. Qed.

Theorem gencongr_unique grel :
  Generated_EquivCongruence grel -> grel =2 gencongr.
Proof.
  move=> Hgrel x y; apply/(sameP idP); apply(iffP idP).
  - by apply: gencongr_imply; first exact gencongrP.
  - by apply: gencongr_imply; last  exact gencongrP.
Qed.

End Final.
