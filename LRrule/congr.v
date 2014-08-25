Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import subseq partition ordtype schensted.

Require Import finset perm.

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
  forall s : seq T, all invar s -> uniq s -> size s <= size (full).
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

Definition class x := trans [:: x].

Lemma classP x y :
  invar x -> reflect (rewseq x y) (y \in class x).
Proof.
  move=> Hinv; rewrite /class; apply (iffP idP).
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

Lemma in_class_trans x y z :
  invar x -> y \in class x -> z \in class y -> z \in class x.
Proof.
  move=> Hinvx /(classP _ Hinvx) => Hrewxy; have:= (invar_rewseq Hinvx Hrewxy).
  move=> Hinvy /(classP _ Hinvy) => Hrewyz.
  apply /(classP _ Hinvx); by apply (rewseq_trans (y := y)).
Qed.

Lemma in_class_refl x : x \in class x.
Proof. by rewrite /class; apply subset_trans; rewrite mem_seq1. Qed.

Hypothesis Hsym : forall x y, x \in rule y -> y \in rule x.

Lemma rewseq_sym x y : rewseq x y -> rewseq y x.
Proof.
  elim; first by apply NilRew.
  move=> {x y} x y z Hzy Hyz Hrule.
  have {Hrule} Hrule := (Hsym Hrule).
  have:= (ConsRew (NilRew _) Hrule) => Hzx.
  apply (rewseq_trans Hyz Hzx).
Qed.

Lemma in_class_sym x y : invar x -> y \in class x -> x \in class y.
Proof.
  move=> Hinvx /(classP _ Hinvx) => Hrewxy.
  have:= (invar_rewseq Hinvx Hrewxy) => Hinvy.
  apply /(classP _ Hinvy); by apply rewseq_sym.
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


Definition rclass x := class (@Hinvar x) (@Hbound x) x.
Definition rtrans : rel T := fun x y => y \in rclass x.

Lemma rtransP x y : reflect (rewseq rule y x) (rtrans y x).
Proof. rewrite /rtrans /rclass; by apply classP. Qed.

Theorem equiv_rtrans : equivalence_rel rtrans.
Proof.
  rewrite equivalence_relP; split.
  - rewrite /reflexive /rtrans /rclass => x; apply in_class_refl.
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

(* congruence closure of an homogeneous rewriting rule *)
Section Congruence.

Variable Alph : eqType.
Notation word := (seq_eqType Alph).

Variable rule : word -> seq word.
Hypothesis Hsym : forall u v : word, v \in rule u -> u \in rule v.
Hypothesis Hhomog : forall u : word, all (perm_eq u) (rule u).
Hypothesis Hcongr :
  forall u v1 v2 w : word , v2 \in rule v1 -> (u ++ v2 ++ w) \in rule (u ++ v1 ++ w).

Lemma perm_eq_bound (x : word) (s : seq word) :
  all (perm_eq x) s -> uniq s -> size s <= (size x)`!.
Proof.
  admit.
Qed.

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

Lemma congr_is_congr (u v1 w : word) :
  forall v2, congr v1 v2 -> congr (u ++ v2 ++ w) (u ++ v1 ++ w).
Proof.
  have:= equiv_congr => /equivalence_relP [] Hrefl Htrans.
  apply congr_ind.
  + by apply Hrefl.
  + move=> x y Hx Hrule.
    rewrite (@Htrans _ (u ++ x ++ w)); first exact Hx.
    apply rule_congr; apply Hcongr; by apply Hsym.
Qed.

End Congruence.


