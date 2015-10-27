(** * Combi.Basic.congr : Rewriting rule and congruencies of words *)
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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype seq.
Require Import Recdef path tuple.
Require Import permuted vectNK.
(******************************************************************************)
(** * Equivalence and congruence closure of a rewriting rule on words

- The rewriting rule is given as a map [rule : word -> seq word]
- The closure is a relation (type : [rel word])

We suppose that equivalence classes are _finite_, this is sufficient for
our purpose here, that is the construction of the plactic monoid. This also
ensure that the generated equivalence relation is decidable by bounding
the length of the rewriting paths. Concretely, this is done by requiring
that [rule] is included in a refexive relation [invar] which is invariant by
rewriting rule, that is:

  [Hypothesis Hinvar : forall x0 x, invar x0 x -> all (invar x0) (rule x).]

We show that this is true for multi-homogeneous rules (ie: that permutes words):

  [Hypothesis Hmulthom : forall u : word, all (perm_eq u) (rule u).]

Also to simplify the code, we assume that the rule are symmetric, that is

  [Hypothesis Hsym : forall x y, x \in rule y -> y \in rule x.]

Assuming the two latter hypothesis, we define a relation [gencongr] which is
the congruence transitive closure of rule. The main results here are
- [gencongrP]       : gencongr is the smallest transitive congruence relation
                      contaning rule.
- [gencongr_unique] : gencongr is uniquely characterized by the property above
- [gencongr_ind] : induction principle on classes for gencongr, any property
                   preserved along the rewriting rule holds for classes.      *)
(******************************************************************************)


Set Implicit Arguments.
Unset Strict Implicit.


(** ** Transitive closure of a rule with finite classes                          *)
(**  Since we only need to contruct it and not to compute with it, we use a     *)
(**  simple but extremely inefficient algorithm                                 *)
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
  move=> l Hl. exact: (Hfull (Hall _ Hl)).
Qed.

End FullKnown.

Variable bound : nat.
Hypothesis Hbound: forall s : seq T, all invar s -> uniq s -> size s <= bound.

Lemma invar_undupE s : all invar (undup s) = all invar s.
Proof.
  apply/idP/idP => /allP H; apply/allP => x Hx; apply: H;
    move: Hx; by rewrite mem_undup.
Qed.

Definition step s := undup (s ++ flatten (map rule s)).

Lemma step_mem s x y : y \in rule x -> x \in s -> y \in step s.
Proof.
  move=> Hrule Hx.
  rewrite /step mem_undup mem_cat; apply/orP; right.
  apply/flattenP; exists (rule x); last by [].
  exact: map_f.
Qed.

Lemma uniq_step s : uniq (step s).
Proof. by rewrite /step; apply: undup_uniq. Qed.

Lemma undup_step s : undup (step s) = step s.
Proof. by rewrite /step [undup (undup _)]undup_id; last exact: undup_uniq. Qed.

Lemma invar_step s : all invar s -> all invar (step s).
Proof.
  rewrite /step => /allP H; apply/allP => x.
  rewrite mem_undup mem_cat => /orP []; first exact: H.
  move=> /flattenP [] tmp /mapP [] y Hyins -> {tmp} Hxy.
  move/(_ _ (H _ Hyins))/allP : Hinvar; by apply.
Qed.

Lemma subset_step s : {subset s <= step s}.
Proof. rewrite /step => x Hx; by rewrite mem_undup mem_cat Hx. Qed.

Lemma subset_undup_step s : {subset undup s <= step s}.
Proof. rewrite /step => x; rewrite mem_undup => Hx; by rewrite mem_undup mem_cat Hx. Qed.

(** This is a very unefficient transitive closure algorithm *)
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
  by apply: ltn_sub2l; first exact: (leq_trans H).
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
  move/(_ _ Hx)/allP : Hinvar; by apply.
Qed.

Lemma step_closed x s y :
  undup s =i step s -> x \in s -> rewrite_path x y -> y \in s.
Proof.
  move=> H Hx [] l.
  elim: l x Hx => [x Hx _ -> //= | l0 l IHl] x Hx /= /andP [] Hrule /IHl; apply.
  move/(_ l0) : H; rewrite mem_undup => ->.
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
      exists y; split => //=; exact: (Rew (l := [::])).
    * move=> s x <-; rewrite invar_undupE; by case (all invar s).
  + move: Hl y; apply trans_ind => //=.
    * move=> s _ Hsz IH Hinv y [] x [] Hxins [].
      case.
      - move=> Hpath /= ->; by apply: subset_s_trans_s; apply: subset_step.
      - move=> z pat /= /andP [] Hz Hpath ->.
        apply: IH; first exact: invar_step.
        exists z; split; first exact: (step_mem Hz).
        exact: (Rew Hpath).
    * move=> s _ x <-; case (ltnP (size (undup s)) (size (step s))) => //= Hsz _.
      have:= leq_size_perm (undup_uniq s) (subset_undup_step (s:= s)) Hsz.
      move=> [] Heq _ _ y {x} [] x [] Hx Hrew.
      rewrite mem_undup; exact: (step_closed Heq Hx).
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
  case/lastP: pathxy Hy => [/= -> _ | pathxz z]; first exact: (Rew (l := [::])).
  rewrite last_rcons belast_rcons rev_cons => -> {y} Hpath.
  apply: (Rew (l := rcons (rev pathxz) x)).
  + set rel := (X in path X _ _) in Hpath.
    rewrite (eq_path (e' := rel)); first exact: Hpath.
    move=> i j; rewrite /rel; apply/idP/idP; exact: Hsym.
  + by rewrite last_rcons.
Qed.

End Transitive.


(** ** Deals with the dependance of invar on x *)
Section Depend.

Variable T : eqType.
Variable rule : T -> seq T.

Record invariant_context :=
  InvariantContext {
      invar : T -> pred T;
      Hinvar_refl : forall x, invar x x;
      Hinvar_all : forall x0 x, invar x0 x -> all (invar x0) (rule x);
      bound : T -> nat;
      Hbound: forall x s, all (invar x) s -> uniq s -> size s <= bound x
    }.
Variable inv : invariant_context.
Hypothesis Hsym : forall x y, x \in rule y -> y \in rule x.

Definition rclass x := trans (@Hinvar_all inv x) (@Hbound inv x) [:: x].
Definition rtrans : rel T := fun x y => y \in rclass x.

Lemma rtransP x y : reflect (rewrite_path rule y x) (rtrans y x).
Proof.
  rewrite /rtrans /rclass.
  apply: (iffP idP).
  - move/transP => H.
    have: (all (invar inv y) [:: y]).
      apply/allP=> z; rewrite mem_seq1 => /eqP ->.
      exact: Hinvar_refl.
    by move/H => [] z []; rewrite mem_seq1 => /eqP ->.
  - move=> H; apply/transP.
    + apply/allP=> x0; rewrite mem_seq1 => /eqP ->.
      exact: Hinvar_refl.
    + by exists y; rewrite mem_seq1.
Qed.

Theorem equiv_rtrans : equivalence_rel rtrans.
Proof.
  rewrite equivalence_relP; split.
  - rewrite /reflexive /rtrans /rclass => x.
    by apply: subset_s_trans_s; rewrite mem_seq1.
  - rewrite /left_transitive => x y Hrxy z.
    apply/idP/idP; move: Hrxy.
    * move=> /rtransP Hryx /rtransP Hrzx; apply/rtransP.
      by move/(rewrite_path_sym Hsym) : Hryx => /rewrite_path_trans/(_ Hrzx).
    * move=> /rtransP Hryx /rtransP Hrzy; apply/rtransP.
      exact: (rewrite_path_trans (y := y)).
Qed.

Lemma rtrans_ind (P : T -> Prop) x :
  P x -> (forall y z, P y -> z \in rule y -> P z) -> forall t, rtrans x t -> P t.
Proof.
  move=> Hx IHr t /rtransP [] l; elim: l x Hx t => [|l0 l IHl] x Hx t /= Hpath -> //=.
  move: Hpath => /andP [] Hl0 Hpath.
  by apply: (@IHl l0); first exact: (@IHr x).
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
  elim: l x => [/= x _ -> | l0 l IHl] /=; first exact: Hrefl.
  move=> x /andP [] /Hin Hl0 /IHl H/H {IHl H} Hl0y.
  by rewrite (Htr _ _ Hl0 y).
Qed.

Lemma rtrans_min (r : rel T) :
  equivalence_rel r -> (forall x y, y \in rule x -> r x y) ->
  forall x y, rtrans x y -> r x y.
Proof. move/rewrite_path_min=> H/H{H} H x y /rtransP Hrew; exact: H. Qed.

End Depend.


Definition congruence_rel (T : eqType) (r : rel (seq T)) :=
  forall a b1 c b2, r b1 b2 -> r (a ++ b1 ++ c) (a ++ b2 ++ c).

Definition congruence_rule (T : eqType) (rule : seq T -> seq (seq T)) :=
  congruence_rel (fun a b => a \in rule b).


(** ** Basic facts on congruences:                                            *)
(** equivalence of various definitions and immediate consequences             *)
Section CongruenceFacts.

Variable Alph : eqType.
Notation word := (seq Alph).


Variable r : rel word.
Hypothesis Hcongr : congruence_rel r.
Hypothesis Hequiv : equivalence_rel r.

Lemma congr_cons w1 w2 a : r w1 w2 -> r (a :: w1) (a :: w2).
Proof.
  rewrite -[a :: w1]cat1s -[[:: a] ++ w1]cats0 -catA.
  rewrite -[a :: w2]cat1s -[[:: a] ++ w2]cats0 -catA.
  exact: Hcongr.
Qed.

Lemma congr_rcons w1 w2 a : r w1 w2 -> r (rcons w1 a) (rcons w2 a).
Proof.
  rewrite -[rcons w1 a]cats1 -[w1 ++ [:: a]]cat0s.
  rewrite -[rcons w2 a]cats1 -[w2 ++ [:: a]]cat0s.
  exact: Hcongr.
Qed.

Lemma congr_catl u1 u2 v : r u1 u2 -> r (u1 ++ v) (u2 ++ v).
Proof. rewrite -[u1 ++ v]cat0s -[u2 ++ v]cat0s; exact: Hcongr. Qed.

Lemma congr_catr u v1 v2 : r v1 v2 -> r (u ++ v1) (u ++ v2).
Proof. rewrite -[u ++ v1]cats0 -[u ++ v2]cats0 -!catA; exact: Hcongr. Qed.

Lemma congr_cat u1 u2 v1 v2 : r u1 u2 -> r v1 v2 -> r (u1 ++ v1) (u2 ++ v2).
Proof.
  move: Hequiv => /equivalence_relP [] Hrefl Htrans.
  move=> Hu Hv; rewrite (Htrans _ (u1 ++ v2)).
  - exact: congr_catl.
  - exact: congr_catr.
Qed.

End CongruenceFacts.


(** ** Congruence closure of a bounded rule *)
Section CongruenceClosure.

Variable Alph : eqType.
Notation word := (seq_eqType Alph).

Variable rule : word -> seq word.

Hypothesis Hsym : forall u v : word, v \in rule u -> u \in rule v.
Variable inv : invariant_context rule.

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
  apply/mapP; by exists j2; first exact: Hj2.
Qed.

Hypothesis Hinvar_congr :
  forall u a b1 b2 c,
    invar inv b1 b2 -> invar inv u (a ++ b1 ++ c) -> invar inv u (a ++ b2 ++ c).

Lemma congrrule_invar u v :
 invar inv u v -> all (invar inv u) (congrrule v).
Proof.
  move=> Huv.
  apply/allP => w /flatten_mapP [] [[i j1] k] /=.
  rewrite -cat3_equiv_cut3 /= => /eqP Hv; subst v.
  move=> /mapP [] j2 Hj2 ->.
  apply: (Hinvar_congr _ Huv).
  exact: (allP (Hinvar_all (Hinvar_refl inv j1)) _ Hj2).
Qed.

Lemma congrrule_sym u v : v \in congrrule u -> u \in congrrule v.
Proof.
  move/flatten_mapP => [] [[i j1] k].
  rewrite -cat3_equiv_cut3 /= => /eqP -> /mapP [] j2 /Hsym Hj2 ->.
  apply: congrrule_is_congr; exact: rule_congrrule.
Qed.

Definition invcont_congr :=
  InvariantContext (Hinvar_refl inv) congrrule_invar (@Hbound _ _ inv).

Definition gencongr := rtrans invcont_congr.
Definition genclass := rclass invcont_congr.

Lemma genclassE u v : (u \in genclass v) = (u \in gencongr v).
Proof. by rewrite unfold_in. Qed.

Lemma gencongr_equiv : equivalence_rel gencongr.
Proof. apply: equiv_rtrans => x y; exact: congrrule_sym. Qed.

Lemma gencongr_is_congr : congruence_rel gencongr.
Proof.
  move: gencongr_equiv => /equivalence_relP [] Hrefl Htrans.
  move=> a b1 c; apply: rtrans_ind.
  + exact: Hrefl.
  + move=> x y Hx Hrule.
    rewrite (@Htrans _ (a ++ x ++ c)); last apply: Hx.
    rewrite {Hx}; apply rule_rtrans.
    exact: congrrule_is_congr.
Qed.

Lemma rule_gencongr u v : v \in rule u -> v \in gencongr u.
Proof. move=> H; apply rule_rtrans; exact: rule_congrrule. Qed.

Lemma gencongr_min (r : rel word) :
  equivalence_rel r -> congruence_rel r ->
  (forall x y, y \in rule x -> r x y) ->
  forall x y, gencongr x y -> r x y.
Proof.
  move=> /equivalence_relP [] Hrefl Htrans Hcongr Hrule x y /rtransP [] l.
  elim: l x => [/= x _ ->| l0 l IHl] /=; first exact: Hrefl.
  move=> x /andP [] /flatten_mapP [] [[i j1] k].
  rewrite -cat3_equiv_cut3 /= => /eqP -> {x} /mapP [] j2 Hj2 ->.
  move=> /IHl H/H{H}; rewrite (@Htrans _ (i ++ j2 ++ k)) //=.
  apply: Hcongr; exact: Hrule.
Qed.

Theorem gencongr_ind (P : word -> Prop) x :
  P x ->
  (forall a b1 c b2, P (a ++ b1 ++ c) -> b2 \in rule b1 -> P (a ++ b2 ++ c)) ->
  forall y, gencongr x y -> P y.
Proof.
  move=> Hx IH; apply: (rtrans_ind Hx) => y z Hy /flatten_mapP [] [[i j1] k].
  rewrite -cat3_equiv_cut3 /= => /eqP Heqy; subst y.
  move=> /mapP [] j2 Hj2 Hz; subst z.
  exact: (@IH _ j1).
Qed.

Lemma gencongr_invar u v : gencongr u v-> invar inv u v.
Proof.
  move: v; apply rtrans_ind; first exact: Hinvar_refl.
  move=> v w /congrrule_invar /allP; by apply.
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
Proof. case=> Heq1 Hc1 Hr1 Hmin1; case=> Heq2 Hc2 Hr2 _; exact: Hmin1. Qed.

Theorem gencongr_unique grel :
  Generated_EquivCongruence grel -> grel =2 gencongr.
Proof.
  move=> Hgrel x y; apply/idP/idP; apply: gencongr_imply => //; exact gencongrP.
Qed.

Theorem gencongr_generic_ind grel (P : word -> Prop) x :
  Generated_EquivCongruence grel ->
  P x ->
  (forall a b1 c b2, P (a ++ b1 ++ c) -> b2 \in rule b1 -> P (a ++ b2 ++ c)) ->
  forall y, grel x y -> P y.
Proof.
  move=> /gencongr_unique Heq Hinit Hind y.
  rewrite Heq; move: y; exact: gencongr_ind.
Qed.


End CongruenceClosure.



(** ** Invariant contect for multi-homgeneous congruence rules *)
Section InvarContMultHom.

Variable Alph : eqType.
Notation word := (seq_eqType Alph).

Variable rule : word -> seq word.
Hypothesis Hmulthom : forall u : word, all (perm_eq u) (rule u).

Lemma perm_eq_bound (x : word) (s : seq word) :
  all (perm_eq x) s -> uniq s -> size s <= (size x)`!.
Proof. rewrite -(size_permuted x); apply: full_bound; exact: eq_seqE. Qed.

Lemma perm_invar (x0 x : word) : perm_eq x0 x -> all (perm_eq x0) (rule x).
Proof.
  move: perm_eq_trans; rewrite /transitive => Ptrans.
  move=> H; apply/allP => x1 Hx1; apply: (@Ptrans _ x _ _ H).
  move/(_ x)/allP : Hmulthom; by apply.
Qed.

Definition invcont_perm := InvariantContext (@perm_eq_refl _) perm_invar perm_eq_bound.

Hypothesis Hsym : forall u v : word, v \in rule u -> u \in rule v.
Hypothesis Hcongr : congruence_rule rule.

Lemma perm_invar_congr u (a b1 b2 c : word) :
  invar invcont_perm b1 b2 ->
  invar invcont_perm u (a ++ b1 ++ c) -> invar invcont_perm u (a ++ b2 ++ c).
Proof. rewrite /= => Hb1b2 /perm_eqlP ->; by rewrite perm_cat2l perm_cat2r. Qed.

Definition gencongr_multhom := gencongr perm_invar_congr.
Definition genclass_multhom := genclass perm_invar_congr.

End InvarContMultHom.


(** ** Invariant contect for homogeneous congruence rules on a finite type *)
Section InvarContHom.

Variable Alph : finType.
Notation word := (seq_eqType Alph).

Variable rule : word -> seq word.
Let szinvar (u : word) := [pred v : word | size v == size u].
Hypothesis Hhom : forall u : word, all (szinvar u) (rule u).

Lemma size_bound (x : word) (s : seq word) :
  all (szinvar x) s -> uniq s -> size s <= #|Alph|^(size x).
Proof.
  pose T := tuple_subType (size x) Alph.
  rewrite -card_tuple cardE all_count => /eqP Hall /(pmap_sub_uniq T).
  have := size_pmap_sub T s; rewrite Hall => <-.
  apply: (full_bound _ (all_predT _)) => u _; by rewrite mem_enum.
Qed.

Lemma size_invar (x0 x : word) : szinvar x0 x -> all (szinvar x0) (rule x).
Proof. rewrite /szinvar /= => /eqP <-. exact: Hhom. Qed.

Lemma size_invar_refl (x : word) : szinvar x x.
Proof. by rewrite /=. Qed.

Definition invcont_size := InvariantContext size_invar_refl size_invar size_bound.

Hypothesis Hcongr : congruence_rule rule.

Lemma size_invar_congr u (a b1 b2 c : word) :
  invar invcont_size b1 b2 ->
  invar invcont_size u (a ++ b1 ++ c) -> invar invcont_size u (a ++ b2 ++ c).
Proof. by rewrite /= !size_cat => /eqP ->. Qed.

Definition gencongr_hom := gencongr size_invar_congr.
Definition genclass_hom := genclass size_invar_congr.

End InvarContHom.

