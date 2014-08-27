Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
Require Import permuted.

Set Implicit Arguments.
Unset Strict Implicit.

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
  move=> s /allP Hall Huniq; apply uniq_leq_size; first exact Huniq.
  move=> l Hl. by apply (Hfull (Hall _ Hl)).
Qed.

End FullKnown.

Variable bound : nat.
Hypothesis Hbound: forall s : seq T, all invar s -> uniq s -> size s <= bound.

Require Import Recdef.

Lemma invar_undupE s : all invar (undup s) = all invar s.
Proof.
  apply/(sameP idP); apply(iffP idP); move/allP => H; apply /allP => x Hx; apply H;
    move: Hx; by rewrite mem_undup.
Qed.

Definition step s := undup (s ++ flatten (map rule s)).

Lemma step_mem s x y : y \in rule x -> x \in s -> y \in step s.
Proof.
  move=> Hrule Hx.
  rewrite /step mem_undup mem_cat; apply/orP; right.
  apply/flattenP; exists (rule x); last by [].
  by apply map_f.
Qed.

Lemma uniq_step s : uniq (step s).
Proof. by rewrite /step; apply undup_uniq. Qed.

Lemma undup_step s : undup (step s) = step s.
Proof. by rewrite /step [undup (undup _)]undup_id; last by apply undup_uniq. Qed.

Lemma invar_step s : all invar s -> all invar (step s).
Proof.
  rewrite /step => /allP H; apply /allP => x.
  rewrite mem_undup mem_cat => /orP []; first by apply H.
  move=> /flattenP [] tmp /mapP [] y Hyins -> {tmp} Hxy.
  have:= (Hinvar (H _ Hyins)) => /allP; by apply.
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
  move=> s Hinv H; rewrite undup_step; apply /ltP.
  have Hszus:= Hbound Hinv (undup_uniq s).
  rewrite invar_undupE in Hinv.
  have Hszn:= Hbound (invar_step Hinv) (uniq_step s).
  by apply ltn_sub2l; first by apply (leq_trans H).
Qed.

Lemma subset_trans s : {subset s <= trans s}.
Proof.
  apply trans_ind => //= {s}.
  * move=> s _ _ H x Hx; exact (H _ (subset_step Hx)).
  * move=> s _ tmp _ {tmp} _ x; by rewrite mem_undup.
  * move=> s _ tmp _ {tmp} x; by rewrite mem_undup.
Qed.

Inductive rewseq x : T -> Prop :=
  | NilRew : rewseq x x
  | ConsRew : forall y z, rewseq z y -> z \in rule x -> rewseq x y.

Lemma invar_rewseq x y : invar x -> rewseq x y -> invar y.
Proof.
  move=> Hx Hrew; elim: Hrew Hx => [//=|{x y} x y z] Hrew Hinv Hrule Hinvx.
  apply Hinv => {Hinv}; have := Hinvar Hinvx => /allP; by apply.
Qed.

Lemma step_closed x s y :
  undup s =i step s -> x \in s -> rewseq x y -> y \in s.
Proof.
  move=> H Hx Hrew; elim: Hrew Hx; first by [].
  move{x y}=> x y z Hrew IH Hrule Hx.
  apply IH; move: (H z); rewrite mem_undup => ->.
  exact (step_mem Hrule Hx).
Qed.

Lemma transP y l:
  all invar l -> reflect (exists x, x \in l /\ rewseq x y) (y \in trans l).
Proof.
  move=> Hl; apply (iffP idP).
  + move: Hl; apply trans_ind => //=.
    * move=> s _ Hsz IH Hall Hy.
      case: (IH (invar_step Hall) Hy) => x [] Hx Hrew.
      move: Hx; rewrite /step mem_undup mem_cat => /orP []; first by exists x.
      move=> /flattenP [] tmp /mapP [] z Hyins -> {tmp} Hxy.
      exists z; split; first exact Hyins.
      apply (ConsRew Hrew Hxy).
    * move=> s _ x <-; case (ltnP (size (undup s)) (size (step s))) => //= Hsz _.
      have:= leq_size_perm (undup_uniq s) (subset_undup_step (s:= s)) Hsz.
      move=> [] Heq _ _; rewrite mem_undup => Hy.
      exists y; split => //=; by apply NilRew.
    * move=> s x <-; rewrite invar_undupE; by case (all invar s).
  + move: Hl y; apply trans_ind => //=.
    * move=> s _ Hsz IH Hinv y [] x [] Hxins.
      case.
      - by apply subset_trans; apply subset_step.
      - move=> {y} y z Hrew Hrule; apply IH; first by apply invar_step.
        exists z; split; last exact Hrew.
        by apply (step_mem Hrule).
    * move=> s _ x <-; case (ltnP (size (undup s)) (size (step s))) => //= Hsz _.
      have:= leq_size_perm (undup_uniq s) (subset_undup_step (s:= s)) Hsz.
      move=> [] Heq _ _ y {x} [] x [] Hx Hrew.
      rewrite mem_undup; by apply (step_closed Heq Hx).
    * move=> s x <-; rewrite invar_undupE; by case (all invar s).
Qed.

Definition tclass x := trans [:: x].

Lemma tclassP x y :
  invar x -> reflect (rewseq x y) (y \in tclass x).
Proof.
  move=> Hinv; rewrite /tclass; apply (iffP idP).
  + move/transP => H.
    have: (all invar [:: x]) by apply/allP=> z; rewrite mem_seq1 => /eqP ->.
    by move/H => [] z []; rewrite mem_seq1 => /eqP ->.
  + move=> H; apply/transP; last by exists x; rewrite mem_seq1.
    apply/allP=> x0; by rewrite mem_seq1 => /eqP ->.
Qed.

Lemma rewseq_trans x y z : rewseq x y -> rewseq y z -> rewseq x z.
Proof.
  move=> H. elim: H z => [//= | {x y} x y z] Hzy IH Hrule z0 Hyz0.
  apply (ConsRew (z := z)); last exact Hrule.
  by apply IH.
Qed.

Lemma in_tclass_trans x y z :
  invar x -> y \in tclass x -> z \in tclass y -> z \in tclass x.
Proof.
  move=> Hinvx /(tclassP _ Hinvx) => Hrewxy; have:= (invar_rewseq Hinvx Hrewxy).
  move=> Hinvy /(tclassP _ Hinvy) => Hrewyz.
  apply /(tclassP _ Hinvx); by apply (rewseq_trans (y := y)).
Qed.

Lemma in_tclass_refl x : x \in tclass x.
Proof. by rewrite /tclass; apply subset_trans; rewrite mem_seq1. Qed.

Hypothesis Hsym : forall x y, x \in rule y -> y \in rule x.

Lemma rewseq_sym x y : rewseq x y -> rewseq y x.
Proof.
  elim; first by apply NilRew.
  move=> {x y} x y z Hzy Hyz Hrule.
  have {Hrule} Hrule := (Hsym Hrule).
  have:= (ConsRew (NilRew _) Hrule) => Hzx.
  apply (rewseq_trans Hyz Hzx).
Qed.

Lemma in_tclass_sym x y : invar x -> y \in tclass x -> x \in tclass y.
Proof.
  move=> Hinvx /(tclassP _ Hinvx) => Hrewxy.
  have:= (invar_rewseq Hinvx Hrewxy) => Hinvy.
  apply /(tclassP _ Hinvy); by apply rewseq_sym.
Qed.

End Transitive.

Section Depend.

Variable T : eqType.
Variable rule : T -> seq T.
Variable invar : T -> pred T.
Hypothesis invar_all : forall x, invar x x.
Hypothesis Hinvar : forall x0 x, invar x0 x -> all (invar x0) (rule x).
Variable bound : T -> nat.
Hypothesis Hbound: forall x s, all (invar x) s -> uniq s -> size s <= bound x.
Hypothesis Hsym : forall x y, x \in rule y -> y \in rule x.


Definition rclass x := tclass (@Hinvar x) (@Hbound x) x.
Definition rtrans : rel T := fun x y => y \in rclass x.

Lemma rtransP x y : reflect (rewseq rule y x) (rtrans y x).
Proof. rewrite /rtrans /rclass; by apply tclassP. Qed.

Theorem equiv_rtrans : equivalence_rel rtrans.
Proof.
  rewrite equivalence_relP; split.
  - rewrite /reflexive /rtrans /rclass => x; apply in_tclass_refl.
  - rewrite /left_transitive => x y Hrxy z.
    apply/(sameP idP); apply(iffP idP); move: Hrxy.
    * move=> /rtransP Hryx /rtransP Hrzy; apply /rtransP.
      by apply (rewseq_trans (y := y)).
    * move=> /rtransP Hryx /rtransP Hrzx; apply /rtransP.
      have:= (rewseq_sym Hsym Hryx) => Hrzy; by apply (rewseq_trans (y := x)).
Qed.

Lemma rtrans_ind (P : T -> Prop) x :
  P x -> (forall y z, P y -> z \in rule y -> P z) -> forall t, rtrans x t -> P t.
Proof.
  move=> Hx IHr t /rtransP Hrew; elim: Hrew Hx => [//=|].
  move=> {x} x y z Hrew Hzy Hrule Hx.
  apply Hzy; by apply (IHr x); last exact Hrule.
Qed.

Lemma rule_rtrans x y : y \in rule x -> rtrans x y.
Proof. move=> Hrule; apply /rtransP; exact (ConsRew (NilRew _ _) Hrule). Qed.

Lemma rewseq_min (r : rel T) :
  equivalence_rel r -> (forall x y, y \in rule x -> r x y) ->
  forall x y, rewseq rule x y -> r x y.
Proof.
  rewrite equivalence_relP => [] [] Hrefl Htr Hin x y; elim => [x0|]; first by apply Hrefl.
  move=> {x y} x y z _ Hzy /(Hin _ _) Hxz; by rewrite (Htr _ _ Hxz).
Qed.

Lemma rtrans_min (r : rel T) :
  equivalence_rel r -> (forall x y, y \in rule x -> r x y) ->
  forall x y, rtrans x y -> r x y.
Proof. move/rewseq_min=> H/H{H} H x y /rtransP Hrew; by apply H. Qed.

End Depend.

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
  by apply Hcongr.
Qed.

Lemma congr_rcons w1 w2 a : r w1 w2 -> r (rcons w1 a) (rcons w2 a).
Proof.
  rewrite -[rcons w1 a]cats1 -[w1 ++ [:: a]]cat0s.
  rewrite -[rcons w2 a]cats1 -[w2 ++ [:: a]]cat0s.
  by apply Hcongr.
Qed.

Lemma congr_catl u1 u2 v : r u1 u2 -> r (u1 ++ v) (u2 ++ v).
Proof. rewrite -[u1 ++ v]cat0s -[u2 ++ v]cat0s; by apply Hcongr. Qed.

Lemma congr_catr u v1 v2 : r v1 v2 -> r (u ++ v1) (u ++ v2).
Proof. rewrite -[u ++ v1]cats0 -[u ++ v2]cats0 -!catA; by apply Hcongr. Qed.

Lemma congr_cat u1 u2 v1 v2 : r u1 u2 -> r v1 v2 -> r (u1 ++ v1) (u2 ++ v2).
Proof.
  have:= Hequiv => /equivalence_relP [] Hrefl Htrans.
  move=> Hu Hv; rewrite (Htrans _ (u1 ++ v2)).
  - by apply congr_catl.
  - by apply congr_catr.
Qed.

End CongruenceFacts.


(* congruence closure of an homogeneous congruence rewriting rule *)
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
Proof. rewrite -(size_permuted x); apply full_bound; by apply eq_seqE. Qed.

Lemma Hinvar (x0 x : word) : perm_eq x0 x -> all (perm_eq x0) (rule x).
Proof.
  have:= (perm_eq_trans); rewrite /transitive => Ptrans.
  move=> H; apply /allP => x1 Hx1; apply (@Ptrans _ x _ _ H).
  have:= (Hhomog x) => /allP; by apply.
Qed.

Definition congr := (rtrans Hinvar perm_eq_bound).

Lemma rule_congr x y : y \in rule x -> congr x y.
Proof. apply rule_rtrans. apply perm_eq_refl. Qed.

Lemma congr_ind (P : word -> Prop) x :
  P x -> (forall y z, P y -> z \in rule y -> P z) -> forall t, congr x t -> P t.
Proof. apply rtrans_ind. apply perm_eq_refl. Qed.

Lemma equiv_congr : equivalence_rel congr.
Proof.
  apply equiv_rtrans; last by move=> x y H; apply Hsym.
  by apply perm_eq_refl.
Qed.

Lemma congr_is_congr : congruence_rel congr.
Proof.
  have:= equiv_congr => /equivalence_relP [] Hrefl Htrans.
  move=> a b1 c; apply congr_ind.
  + by apply Hrefl.
  + move=> x y Hx Hrule.
    rewrite (@Htrans _ (a ++ x ++ c)); last apply Hx.
    by apply rule_congr; apply Hcongr.
Qed.

End CongruenceClosure.

Require Import vectNK.

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
  apply/mapP; by exists j2; first by apply Hj2.
Qed.

Lemma congrrule_homog u : all (perm_eq u) (congrrule u).
Proof.
  apply/allP => v /flatten_mapP [] [[i j1] k] /=.
  rewrite -cat3_equiv_cut3 /= => /eqP -> /mapP [] j2 Hj2 ->.
  rewrite perm_cat2l perm_cat2r.
  have:= (Hhomog j1) => /allP; by apply.
Qed.

Lemma congrrule_sym u v : v \in congrrule u -> u \in congrrule v.
Proof.
  move/flatten_mapP => [] [[i j1] k].
  rewrite -cat3_equiv_cut3 /= => /eqP -> /mapP [] j2 Hj2 ->.
  have {Hj2} Hj2 := (Hsym Hj2); apply congrrule_is_congr.
  by apply rule_congrrule.
Qed.

End CongruenceRule.


Section Final.

Variable Alph : eqType.
Notation word := (seq_eqType Alph).

Variable rule : word -> seq word.
Hypothesis Hsym : forall u v : word, v \in rule u -> u \in rule v.
Hypothesis Hhomog : forall u : word, all (perm_eq u) (rule u).

Definition gencongr := (congr (congrrule_homog Hhomog)).

Lemma gencongr_equiv : equivalence_rel gencongr.
Proof. apply equiv_congr; by apply congrrule_sym. Qed.

Lemma gencongr_is_congr : congruence_rel gencongr.
Proof.
  apply congr_is_congr; first by apply congrrule_sym.
  by apply congrrule_is_congr.
Qed.

Lemma rule_gencongr u v : v \in rule u -> v \in gencongr u.
Proof. move=> H; apply rule_congr; by apply rule_congrrule. Qed.

Lemma gencongr_min (r : rel word) :
  equivalence_rel r -> congruence_rel r ->
  (forall x y, y \in rule x -> r x y) ->
  forall x y, gencongr x y -> r x y.
Proof.
  move=> /equivalence_relP [] Hrefl Htrans Hcongr Hrule x y /rtransP => H.
  elim: (H (@perm_eq_refl Alph)) => {H}; first by apply Hrefl.
  move=> {x y} x y z _ Hrzy /flatten_mapP [] [[i j1] k] /=.
  rewrite -cat3_equiv_cut3 /= => /eqP -> {x} /mapP [] j2 Hj2 Hz.
  rewrite Hz in Hrzy => {z Hz}.
  rewrite (@Htrans _ (i ++ j2 ++ k)); first exact Hrzy.
  apply Hcongr; by  apply Hrule.
Qed.

Lemma gencongr_ind (P : word -> Prop) x :
  P x ->
  (forall a b1 c b2, P (a ++ b1 ++ c) -> b2 \in rule b1 -> P (a ++ b2 ++ c)) ->
  forall y, gencongr x y -> P y.
Proof.
  move=> Hx IH; apply (rtrans_ind (@perm_eq_refl Alph) Hx).
  move=> y z Hy /flatten_mapP [] [[i j1] k].
  rewrite -cat3_equiv_cut3 /= => /eqP Heqy; subst y.
  move=> /mapP [] j2 Hj2 Hz; subst z.
  by apply (@IH _ j1).
Qed.

End Final.
