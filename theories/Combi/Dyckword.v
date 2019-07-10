(** * Combi.Combi.DyckWord : Dyck Words *)
(******************************************************************************)
(*      Copyright (C) 2014-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * Dyck Words
 *********************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun bigop ssrnat eqtype fintype choice seq.
From mathcomp Require Import fingraph path finset.

Require Import tools combclass bintree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




Lemma take_take (T : eqType) i j (s : seq T) :
  i <= j -> take i (take j s) = take i s.
Proof.
elim: s i j => [// | s0 s IHs] [|i] [|j] //=.
by rewrite ltnS => /IHs ->.
Qed.



Inductive brace : Set := | Open : brace | Close : brace.

Definition bool_of_brace b :=
  match b with
  | Open => true
  | Close => false
  end.

Definition brace_of_bool b :=
  match b with
  | true => Open
  | false => Close
  end.

Lemma bool_of_braceK : cancel bool_of_brace brace_of_bool.
Proof. by case=> []. Qed.
Lemma brace_of_boolK : cancel brace_of_bool bool_of_brace.
Proof. by case=> []. Qed.

Definition brace_eqMixin := InjEqMixin (can_inj bool_of_braceK).
Canonical brace_eqType := Eval hnf in EqType brace brace_eqMixin.
Definition brace_choiceMixin := CanChoiceMixin bool_of_braceK.
Canonical brace_choiceType := Eval hnf in ChoiceType brace brace_choiceMixin.
Definition brace_countMixin := CanCountMixin bool_of_braceK.
Canonical brace_countType := Eval hnf in CountType brace brace_countMixin.
Definition brace_finMixin := CanFinMixin bool_of_braceK.
Canonical brace_finType := Eval hnf in FinType brace brace_finMixin.

Local Notation "#Open" := (count_mem Open).
Local Notation "#Close" := (count_mem Close).


Section Defs.

Implicit Type h n : nat.
Implicit Type w : seq brace.
Implicit Type l : seq (seq brace).


Definition prefixes w := [seq take n w | n <- iota 0 ((size w).+1)].

Lemma take_prefixes w i : take i w \in prefixes w.
Proof.
apply/mapP; case (leqP i (size w)) => Hi.
- by exists i; first by rewrite mem_iota add0n ltnS Hi.
- exists (size w); first by rewrite mem_iota add0n ltnS leqnn.
  rewrite take_size take_oversize //.
  exact: ltnW.
Qed.
Lemma mem_prefixesP w p : reflect (exists i, p = take i w) (p \in prefixes w).
Proof.
rewrite /prefixes; apply (iffP idP) => [/mapP [i _ ->] | [i ->]].
- by exists i.
- exact: take_prefixes.
Qed.


Definition Dyck_prefix :=
  [qualify a w | all (fun p => #Open p >= #Close p) (prefixes w)].
Definition Dyck_word :=
  [qualify a w | (w \is a Dyck_prefix) && (#Open w == #Close w)].

Lemma Dyck_prefixP w :
  reflect
    (forall n, #Open (take n w) >= #Close (take n w))
    (w \is a Dyck_prefix).
Proof.
rewrite unfold_in.
apply (iffP allP) => /= H.
- by move=> i; apply H; apply take_prefixes.
- by move=> p /mem_prefixesP [i -> {p}].
Qed.

Lemma Dyck_wordP w :
  reflect
    ((forall n, #Open (take n w) >= #Close (take n w)) /\ (#Open w == #Close w))
    (w \is a Dyck_word).
Proof.
rewrite unfold_in.
by apply (iffP andP) => /= [] [H1 H2]; split => //; apply/Dyck_prefixP.
Qed.

Lemma Dyck_word_OwC w :
  w \is a Dyck_word -> Open :: w ++ [:: Close ] \is a Dyck_word.
Proof.
move/Dyck_wordP => [Hpos /eqP Hbal]; apply/Dyck_wordP; split => [n|].
- case: n => [|n /=]; first by rewrite take0.
  rewrite add0n add1n take_cat.
  case: ltnP => Hn; first exact: leqW.
  case: (_ - _) => [|m /=]; first by rewrite take0 cats0 Hbal.
  by rewrite !count_cat /= !addn0 addn1 ltnS Hbal.
- by rewrite /= !count_cat /= !addn0 !add0n !addn1 !add1n Hbal.
Qed.
Lemma Dyck_word_cat w1 w2 :
  w1 \is a Dyck_word -> w2 \is a Dyck_word -> w1 ++ w2 \is a Dyck_word.
Proof.
move/Dyck_wordP => [Hpos1 /eqP Hbal1].
move/Dyck_wordP => [Hpos2 /eqP Hbal2].
apply/Dyck_wordP; split => [n|].
- rewrite take_cat; case ltnP => _; first exact: Hpos1.
  by rewrite !count_cat Hbal1 leq_add2l.
- by rewrite !count_cat Hbal1 Hbal2.
Qed.
Lemma Dyck_word_OwCw w1 w2 :
  w1 \is a Dyck_word -> w2 \is a Dyck_word ->
  Open :: w1 ++ Close :: w2 \is a Dyck_word.
Proof.
move=> Hw1 Hw2.
rewrite -cat1s -[Close :: _]cat1s !catA; apply Dyck_word_cat => //=.
exact: Dyck_word_OwC.
Qed.

End Defs.


Section FactorDef.

Variable w : seq brace.

Definition is_Dyck_fact (dfact : seq brace * seq brace) :=
  [&& dfact.1 \is a Dyck_word, dfact.2 \is a Dyck_word &
    (w == (Open :: dfact.1) ++ (Close :: dfact.2))].

Inductive Dyck_fact : Set :=
  DyckFact { dfact : seq brace * seq brace; _ : is_Dyck_fact dfact }.

Canonical dyckFact_subType := Eval hnf in [subType for dfact].
Definition dyckFact_eqMixin := Eval hnf in [eqMixin of Dyck_fact by <:].
Canonical dyckFact_eqType := Eval hnf in EqType Dyck_fact dyckFact_eqMixin.
Definition dyckFact_choiceMixin :=
  Eval hnf in [choiceMixin of Dyck_fact by <:].
Canonical dyckFact_choiceType :=
  Eval hnf in ChoiceType Dyck_fact dyckFact_choiceMixin.
Definition dyckFact_countMixin :=
  Eval hnf in [countMixin of Dyck_fact by <:].
Canonical dyckFact_countType :=
  Eval hnf in CountType Dyck_fact dyckFact_countMixin.
Canonical dyckFact_subCountType := Eval hnf in [subCountType of Dyck_fact].

End FactorDef.



Section Factor.

Lemma Dyck_fact_nnil w (f : Dyck_fact w) : w != [::].
Proof. by case: f => [[a b] /= /and3P [_ _ /eqP ->]]. Qed.

Lemma Dyck_factP w (f : Dyck_fact w) : w \is a Dyck_word.
Proof.
case: f => [[a b] /= /and3P [Ha Hb /eqP ->]].
exact: Dyck_word_OwCw.
Qed.


Lemma Dyck_cut_ex w :
  w != [::] -> w \is a Dyck_word ->
  exists i, (i != 0) && (#Open (take i w) == #Close (take i w)).
Proof.
move=> Hnnil /Dyck_wordP [_ Heq].
exists (size w); apply/andP; split; first by case: w Hnnil {Heq}.
by rewrite take_size.
Qed.

Theorem factorizeP w :
  w != [::] -> w \is a Dyck_word -> Dyck_fact w.
Proof.
move=> Hnnil HD.
case: (ex_minnP (Dyck_cut_ex Hnnil HD)) => cut /andP [Hcut /eqP Heq Hmin].
case: w Hnnil HD Heq Hmin => // w0 tl _.
case: w0; first last.
  rewrite unfold_in => /andP [/Dyck_prefixP/(_ 1)/=].
  by rewrite take0 /= !addn0.
move=> /Dyck_wordP [Hpos /eqP Hbal].
case: cut Hcut => // [][|cut] _; rewrite [X in X -> _]/= add1n add0n.
  by rewrite take0.
move=> Heq Hmin.
have Hcut : cut < size tl.
  rewrite -ltnS; apply Hmin.
  by rewrite -[(size tl).+1]/(size (Open :: tl)) take_size Hbal /=.
have Hf1 : take cut.+1 tl = rcons (take cut tl) Close.
  move: Heq (Hpos cut.+1).
  rewrite /= (take_nth Open Hcut) add0n add1n.
  rewrite !count_mem_rcons.
  case: (nth Open tl cut) => []; rewrite eq_refl /= !addn1 !addn0 //.
  by move=> <-; rewrite ltnn.
move: Heq; rewrite Hf1 !count_mem_rcons /= addn0 addn1.
move=> /eqP; rewrite eqSS => /eqP Hbalcut.
have {Hmin} Hmin n : n <= cut -> #Open (take n tl) >= #Close (take n tl).
  apply contraLR; rewrite -!ltnNge.
  case: cut Hbalcut Hmin {Hcut Hf1} => [ _ _ | cut Hbalcut Hmin Hlt].
    by case: n; first by rewrite take0.
  apply: (Hmin (n.+1)); rewrite /= add1n add0n.
  apply/eqP/anti_leq.
  rewrite Hlt /=.
  by have:= Hpos (n.+1); rewrite /= add1n add0n.
exists (take cut tl, drop cut.+1 tl).
apply/and3P; split => /=.
- apply/Dyck_wordP; split => [n|].
  + case: (leqP n cut) => Hncut.
    * by rewrite take_take // Hmin.
    * rewrite take_oversize; last by rewrite size_take Hcut; apply ltnW.
      by rewrite Hbalcut.
  + by rewrite Hbalcut.
- apply/Dyck_wordP; split => [n|].
  + have := Hpos (cut.+1 + n.+1).
    rewrite -{1 2}(cat_take_drop cut.+1 tl).
    have Hsz : size (take cut.+1 tl) = cut.+1 by rewrite size_take_leq Hcut.
    rewrite addSn /= take_cat Hsz ltnS.
    rewrite addnS ltnNge leq_addr /=.
    rewrite -addSn addKn !count_cat Hf1 !count_mem_rcons /=.
    by rewrite !addn0 !add0n addn1 addnA add1n Hbalcut leq_add2l.
  + move: Hbal; rewrite  -{1 2}(cat_take_drop cut.+1 tl).
    have Hsz : size (take cut.+1 tl) = cut.+1 by rewrite size_take_leq Hcut.
    rewrite /= !count_cat Hf1 !count_mem_rcons /=.
    rewrite !addn0 !add0n addn1 addnA add1n Hbalcut.
    by move=> /eqP; rewrite eqn_add2l.
- by rewrite -{1}(cat_take_drop cut.+1 tl) Hf1 cat_rcons.
Qed.

Lemma Dyck_fact_size w (f : Dyck_fact w) :
  (size (dfact f).1).+2 =
  ex_minn (Dyck_cut_ex (Dyck_fact_nnil f) (Dyck_factP f)).
Proof.
case: ex_minnP => cut /andP [Hcut /eqP Heq Hmin].
case: f => [[f1 f2] /= /and3P [Hf1 Hf2 /eqP Hw]].
apply/anti_leq/andP; split.
- move: Heq => /eqP {Hmin}; rewrite leqNgt; apply contraL; rewrite ltnS.
  case: cut Hcut => [// | cut _]; rewrite ltnS => Hcut.
  rewrite Hw /= take_cat.
  move: Hcut; rewrite leq_eqVlt => /orP [/eqP ->|->].
  + rewrite ltnn subnn take0 add0n cats0.
    move: Hf1 => /Dyck_wordP [_ /eqP ->]; rewrite add1n.
    by rewrite neq_ltn ltnSn orbT.
  + rewrite add1n add0n neq_ltn ltnS.
    move: Hf1 => /Dyck_wordP [-> _].
    by rewrite orbT.
- apply: Hmin; rewrite /= {}Hw.
  rewrite -cat1s -[Close :: f2]cat1s !catA take_size_cat ?size_cat /= ?addn1 //.
  rewrite !count_cat /= !addn0 add0n add1n addn1.
  by move: Hf1 => /Dyck_wordP [_ /eqP ->].
Qed.

Theorem Dyck_fact_uniq w (f1 f2 : Dyck_fact w) : f1 = f2.
Proof.
have Hnnil := Dyck_fact_nnil f1.
have Hw := Dyck_factP f1.
apply val_inj => /=.
move: (Dyck_fact_size f1).
rewrite (eq_ex_minn _ (Dyck_cut_ex (Dyck_fact_nnil f2) (Dyck_factP f2))) //.
rewrite -(Dyck_fact_size f2) => /eqP; rewrite !eqSS.
case: f1 f2 => [[f1 f2] /= /and3P [] Hf1 Hf2 /eqP ->] [[g1 g2] /= /and3P [] Hg1 Hg2].
move=> Heq /eqP Hsz; move: Heq => /=.
rewrite -[Open :: _ ++ _]cat1s -[Close :: f2]cat1s !catA.
rewrite -[Open :: _ ++ _]cat1s -[Close :: g2]cat1s !catA.
by rewrite !eqseq_cat /= ?size_cat ?Hsz //= => /andP [/andP [/eqP -> _] /eqP ->].
Qed.

End Factor.



Section DyckSet.

Record Dyck := DyckWord {dyckword :> seq brace; is_dyckword :> dyckword \is a Dyck_word}.

Canonical Dyck_subType := Eval hnf in [subType for dyckword].
Definition Dyck_eqMixin := Eval hnf in [eqMixin of Dyck by <:].
Canonical Dyck_eqType := Eval hnf in EqType Dyck Dyck_eqMixin.
Definition Dyck_choiceMixin := [choiceMixin of Dyck by <:].
Canonical Dyck_choiceType :=
  Eval hnf in ChoiceType Dyck Dyck_choiceMixin.

Lemma dyck_inj : injective dyckword. Proof. exact: val_inj. Qed.

Implicit Type d : Dyck.

Canonical emptyDyck := (@DyckWord [::] is_true_true).

Lemma DyckP d : (dyckword d) \is a Dyck_word.
Proof. exact: d. Qed.
Hint Resolve DyckP.

Definition cat_Dyck d1 d2 := DyckWord (Dyck_word_cat d1 d2).
Definition join_Dyck d1 d2 := DyckWord (Dyck_word_OwCw d1 d2).

Theorem factor_Dyck D :
  D != emptyDyck -> { DyckPair : Dyck * Dyck | D == join_Dyck DyckPair.1 DyckPair.2 }.
Proof.
case: D => [w Hw] H /=.
case: (factorizeP H Hw) => [[w1 w2] /= /and3P [Hw1 Hw2 /eqP Heq]].
exists (DyckWord Hw1, DyckWord Hw2) => /=.
exact/eqP/val_inj.
Qed.

Theorem factor_Dyck_unique D1 D2 E1 E2:
  join_Dyck D1 D2 = join_Dyck E1 E2 -> (D1, D2) = (E1, E2).
Proof.
move=> /(congr1 val)/=.
set w := Open :: D1 ++ Close :: D2 => H.
have factD : is_Dyck_fact w (val D1, val D2).
  by apply/and3P => /=; split.
have factE : is_Dyck_fact w (val E1, val E2).
  by apply/and3P => /=; split; last by rewrite H.
have := (Dyck_fact_uniq (DyckFact factD) (DyckFact factE)).
by move/(congr1 val) => /= [/val_inj -> /val_inj ->].
Qed.

End DyckSet.


Section DyckSetInd.

Implicit Type D : Dyck.


Variable P : Dyck -> Type.
Hypothesis (Pnil : P emptyDyck)
           (Pcons : forall D1 D2, P D1 -> P D2 -> P (join_Dyck D1 D2)).

Theorem Dyck_ind D : P D.
Proof.
move: {2}(size D) (leqnn (size D)) => n.
elim: n D => [|n IHn] D.
  rewrite leqn0 => /nilP H.
  suff -> : D = emptyDyck by [].
  exact: val_inj.
case (altP (D =P emptyDyck)) => [-> //| /factor_Dyck [[D1 D2] /= /eqP ->]].
rewrite /= ltnS size_cat /= addnS => /ltnW Hsz.
apply: Pcons; apply IHn.
- exact: (leq_trans (leq_addr (size D2) (size D1))).
- exact: (leq_trans (leq_addl (size D1) (size D2))).
Qed.

End DyckSetInd.

(** Example of application of the induction principle *)
Lemma Dyck_size_even (D : Dyck) : ~~ odd (size D).
Proof.
elim/Dyck_ind: D => //= D1 D2 /negbTE HD1 /negbTE HD2.
by rewrite size_cat /= addnS /= negbK odd_add negb_add HD1 HD2.
Qed.




Section Bij.

Fixpoint Dyck_of_bintree t :=
  if t is BinNode l r then
    (Open :: Dyck_of_bintree l) ++ (Close :: Dyck_of_bintree r)
  else [::].

Fixpoint bintree_of_Dyck_rec (n : nat) (w : seq brace) :=
  if n is n.+1 then
    if w is w0 :: tl then
      match boolP (w0 :: tl \is a Dyck_word) with
      | @AltTrue _ _ Pf =>
        let fact := factorizeP (is_true_true : w0 :: tl != [::]) Pf in
        BinNode (bintree_of_Dyck_rec n (dfact fact).1)
                (bintree_of_Dyck_rec n (dfact fact).2)
      | @AltFalse _ _ _ => BinLeaf
      end
    else BinLeaf
  else BinLeaf.
Definition bintree_of_Dyck w := bintree_of_Dyck_rec (size w) w.


Lemma bintree_of_Dyck_recE w n :
  w \is a Dyck_word -> n >= size w -> bintree_of_Dyck_rec n w = bintree_of_Dyck w.
Proof.
rewrite /bintree_of_Dyck.
elim: n {1 3 4}n w (leqnn n) => [|n IHn] n' w.
  by rewrite leqn0 => /eqP -> _; rewrite leqn0 => /nilP ->.
case: w n' => [|w0 tl] [|n'] //=.
rewrite !ltnS => Hn' HD Hsz.
case (boolP (w0 :: tl \is a Dyck_word)) => // HD' /=.
case: factorizeP => {HD HD'} [[w1 w2] /= /and3P [Hw1 Hw2 /eqP Heq]].
have := leqnn (size (w0 :: tl)); rewrite {1}Heq /= size_cat /= ltnS addnS => /ltnW Hsz12.
have Hsz1 : size w1 <= size tl.
  exact: (leq_trans (leq_addr (size w2) (size w1))).
have Hsz2 : size w2 <= size tl.
  exact: (leq_trans (leq_addl (size w1) (size w2))).
have Hszn := leq_trans Hsz Hn'.
rewrite !IHn //; [exact: (leq_trans Hsz2) | exact: (leq_trans Hsz1)].
Qed.

Lemma bintree_of_DyckE w1 w2 :
  w1 \is a Dyck_word -> w2 \is a Dyck_word ->
  bintree_of_Dyck (Open :: w1 ++ Close :: w2) =
    BinNode (bintree_of_Dyck w1) (bintree_of_Dyck w2).
Proof.
rewrite {1}/bintree_of_Dyck /= => HD1 HD2.
set w := (Open :: w1 ++ Close :: w2).
case (boolP (w \is a Dyck_word)) => // [HD | ]; last by rewrite Dyck_word_OwCw.
have fact_spec : is_Dyck_fact w (w1, w2).
  by apply/and3P => /=; split.
rewrite (Dyck_fact_uniq (factorizeP _ _) (DyckFact fact_spec)) /= {fact_spec HD}.
rewrite !bintree_of_Dyck_recE // size_cat /=.
- by rewrite -addSnnS; apply leq_addl.
- exact: leq_addr.
Qed.


Lemma Dyck_of_bintreeP t : (Dyck_of_bintree t) \is a Dyck_word.
Proof.
elim: t => //= [l IHl r IHr].
rewrite -cat1s -[Close :: _]cat1s !catA; apply Dyck_word_cat => //=.
exact: Dyck_word_OwC.
Qed.

Theorem Dyck_of_bintreeK t : bintree_of_Dyck (Dyck_of_bintree t) = t.
Proof.
elim: t => //= [l IHl r IHr].
by rewrite bintree_of_DyckE ?Dyck_of_bintreeP // IHl IHr.
Qed.

Theorem bintree_of_DyckK w :
  w \is a Dyck_word -> Dyck_of_bintree (bintree_of_Dyck w) = w.
Proof.
move: {2}(size w) (leqnn (size w)) => n.
elim: n w => [|n IHn] w; first by rewrite leqn0 => /nilP ->.
case: (altP (w =P [::])) => [->|] //= Hnnil Hsz HD.
case: (factorizeP Hnnil HD) => {Hnnil HD} [[w1 w2] /and3P /= [Hw1 Hw2 /eqP Hw]].
rewrite Hw bintree_of_DyckE //=.
have := leqnn (size w); rewrite {1}Hw /= size_cat /= addnS => /ltnW Hsz12.
have {Hsz12} := leq_trans Hsz12 Hsz; rewrite ltnS => Hsz12.
rewrite !IHn => //.
- exact: (leq_trans (leq_addl (size w1) (size w2))).
- exact: (leq_trans (leq_addr (size w2) (size w1))).
Qed.


Lemma size_Dyck_of_bintree t :
  size (Dyck_of_bintree t) = 2 * (size_tree t).
Proof.
elim: t => //= l Hl r Hr.
rewrite size_cat /= {}Hl Hr.
by rewrite !mulnDr muln1 -addn1 -addnA addSnnS addnA addnC addnA.
Qed.

Lemma size_bintree_of_Dyck w :
  w \is a Dyck_word -> 2 * size_tree (bintree_of_Dyck w) = size w.
Proof. by move=> /bintree_of_DyckK {2}<-; rewrite size_Dyck_of_bintree. Qed.

