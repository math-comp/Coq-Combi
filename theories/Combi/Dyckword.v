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
    ((forall n, #Open (take n w) >= #Close (take n w)) /\ (#Open w = #Close w))
    (w \is a Dyck_word).
Proof.
rewrite unfold_in.
by apply (iffP andP) => /= [] [H1 /eqP H2]; split => //; apply/Dyck_prefixP.
Qed.

Lemma Dyck_word_OwC w :
  w \is a Dyck_word -> Open :: w ++ [:: Close ] \is a Dyck_word.
Proof.
move/Dyck_wordP => [Hpos Hbal]; apply/Dyck_wordP; split => [n|].
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
move/Dyck_wordP => [Hpos1 Hbal1].
move/Dyck_wordP => [Hpos2 Hbal2].
apply/Dyck_wordP; split => [n|].
- rewrite take_cat; case ltnP => _; first exact: Hpos1.
  by rewrite !count_cat Hbal1 leq_add2l.
- by rewrite !count_cat Hbal1 Hbal2.
Qed.
Lemma Dyck_word_flatten l :
  all (mem Dyck_word) l -> flatten l \is a Dyck_word.
Proof. elim: l => [| w l IHl] //= /andP [Hd /IHl]. exact: Dyck_word_cat. Qed.

Lemma Dyck_word_OwCw w1 w2 :
  w1 \is a Dyck_word -> w2 \is a Dyck_word ->
  Open :: w1 ++ Close :: w2 \is a Dyck_word.
Proof.
move=> Hw1 Hw2.
rewrite -cat1s -[Close :: _]cat1s !catA; apply Dyck_word_cat => //=.
exact: Dyck_word_OwC.
Qed.

End Defs.



Section DyckSet.

Record Dyck := DyckWord {dyckword :> seq brace;
                         is_dyckword :> dyckword \is a Dyck_word}.

Canonical Dyck_subType := Eval hnf in [subType for dyckword].
Definition Dyck_eqMixin := Eval hnf in [eqMixin of Dyck by <:].
Canonical Dyck_eqType := Eval hnf in EqType Dyck Dyck_eqMixin.
Definition Dyck_choiceMixin := [choiceMixin of Dyck by <:].
Canonical Dyck_choiceType :=
  Eval hnf in ChoiceType Dyck Dyck_choiceMixin.
Definition Dyck_countMixin := [countMixin of Dyck by <:].
Canonical Dyck_countType :=
  Eval hnf in CountType Dyck Dyck_countMixin.


Implicit Type D : Dyck.

Canonical nil_Dyck := (@DyckWord [::] is_true_true).

Lemma DyckP D : (dyckword D) \is a Dyck_word.
Proof. exact: D. Qed.
Hint Resolve DyckP.

Definition cat_Dyck D1 D2 := DyckWord (Dyck_word_cat D1 D2).
Definition join_Dyck D1 D2 := DyckWord (Dyck_word_OwCw D1 D2).


Lemma join_Dyck_nnil D1 D2 : dyckword (join_Dyck D1 D2) != [::].
Proof. by []. Qed.


Lemma Dyck_cut_ex w :
  w != [::] -> w \is a Dyck_word ->
  exists i, (i != 0) && (#Open (take i w) == #Close (take i w)).
Proof.
move=> Hnnil /Dyck_wordP [_ Heq].
exists (size w); apply/andP; split; first by case: w Hnnil {Heq}.
by rewrite take_size Heq.
Qed.

Theorem factor_Dyck D :
  D != nil_Dyck -> { DD : Dyck * Dyck | D = join_Dyck DD.1 DD.2 }.
Proof.
case: D => [w HD] H /=.
have {H} Hnnil : w != [::].
  by move: H; apply contra => /eqP H; apply/eqP/val_inj => /=.
case: (ex_minnP (Dyck_cut_ex Hnnil HD)) => cut /andP [Hcut /eqP Heq Hmin].
case: w Hnnil HD Heq Hmin => // w0 tl _.
case: w0 => HD; first last.
  have:= HD; rewrite unfold_in => /andP [/Dyck_prefixP/(_ 1)/=].
  by rewrite take0 /= !addn0.
have:= (Dyck_wordP _ HD) => [[Hpos /eqP Hbal]].
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
have HDL : (take cut tl) \is a Dyck_word.
  apply/Dyck_wordP; split => [n|].
  - case: (leqP n cut) => Hncut.
    + by rewrite take_take // Hmin.
    + rewrite take_oversize; last by rewrite size_take Hcut; apply ltnW.
      by rewrite Hbalcut.
  - by rewrite Hbalcut.
have HDR : (drop cut.+1 tl) \is a Dyck_word.
  apply/Dyck_wordP; split => [n|].
  - have := Hpos (cut.+1 + n.+1).
    rewrite -{1 2}(cat_take_drop cut.+1 tl).
    have Hsz : size (take cut.+1 tl) = cut.+1 by rewrite size_take_leq Hcut.
    rewrite addSn /= take_cat Hsz ltnS.
    rewrite addnS ltnNge leq_addr /=.
    rewrite -addSn addKn !count_cat Hf1 !count_mem_rcons /=.
    by rewrite !addn0 !add0n addn1 addnA add1n Hbalcut leq_add2l.
  - move: Hbal; rewrite  -{1 2}(cat_take_drop cut.+1 tl).
    have Hsz : size (take cut.+1 tl) = cut.+1 by rewrite size_take_leq Hcut.
    rewrite /= !count_cat Hf1 !count_mem_rcons /=.
    rewrite !addn0 !add0n addn1 addnA add1n Hbalcut.
    by rewrite eqn_add2l => /eqP.

exists (DyckWord HDL, DyckWord HDR).

apply/val_inj => /=.
by rewrite -{1}(cat_take_drop cut.+1 tl) Hf1 cat_rcons.
Qed.

Lemma Dyck_fact_size D1 D2 :
  (size D1).+2 = ex_minn (Dyck_cut_ex (join_Dyck_nnil D1 D2) (join_Dyck D1 D2)).
Proof.
case: ex_minnP => cut /andP [Hcut /eqP Heq Hmin].
apply/anti_leq/andP; split.
- move: Heq => /eqP {Hmin}; rewrite leqNgt; apply contraL; rewrite ltnS.
  case: cut Hcut => [// | cut _]; rewrite ltnS => Hcut.
  rewrite /= take_cat.
  move: Hcut; rewrite leq_eqVlt => /orP [/eqP ->|->].
  + rewrite ltnn subnn take0 add0n cats0.
    case: D1 => /= [d1 /Dyck_wordP [_ ->]]; rewrite add1n.
    by rewrite neq_ltn ltnSn orbT.
  + rewrite add1n add0n neq_ltn ltnS.
    case: D1 => /= [d1 /Dyck_wordP [-> _]].
    by rewrite orbT.
- apply: Hmin; rewrite /= {Heq}.
  rewrite -cat1s -[Close :: _]cat1s !catA take_size_cat ?size_cat /= ?addn1 //.
  rewrite !count_cat /= !addn0 add0n add1n addn1.
  by case: D1 => /= [d1 /Dyck_wordP [_ ->]].
Qed.

Theorem join_Dyck_inj D1 D2 E1 E2:
  join_Dyck D1 D2 = join_Dyck E1 E2 -> (D1, D2) = (E1, E2).
Proof.
move=> Heq.
have Hnnil := join_Dyck_nnil D1 D2.
move: (Dyck_fact_size D1 D2).
rewrite (eq_ex_minn _ (Dyck_cut_ex (join_Dyck_nnil E1 E2) (join_Dyck E1 E2)));
  last by move=> i; rewrite Heq.
rewrite -(Dyck_fact_size E1 E2) => /eqP; rewrite !eqSS => /eqP Hsz.
move: Heq => /(congr1 val)/= /eqP.
rewrite -[Open :: _ ++ _]cat1s -[Close :: D2]cat1s !catA.
rewrite -[Open :: _ ++ _]cat1s -[Close :: E2]cat1s !catA.
rewrite !eqseq_cat /= ?size_cat ?Hsz //=.
by move=> /andP [/andP [/eqP /val_inj -> _] /eqP /val_inj ->].
Qed.

End DyckSet.



Section DyckSetInd.

Implicit Type D : Dyck.


Variable P : Dyck -> Type.
Hypothesis (Pnil : P nil_Dyck)
           (Pcons : forall D1 D2, P D1 -> P D2 -> P (join_Dyck D1 D2)).

Theorem Dyck_ind D : P D.
Proof.
move: {2}(size D) (leqnn (size D)) => n.
elim: n D => [|n IHn] D.
  rewrite leqn0 => /nilP H.
  suff -> : D = nil_Dyck by [].
  exact: val_inj.
case (altP (D =P nil_Dyck)) => [-> //| /factor_Dyck [[D1 D2] /= ->]].
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



Lemma factor_Dyck_seq D :
  { DS : seq Dyck | D = foldr join_Dyck nil_Dyck DS }.
Proof.
elim/Dyck_ind: D => [|D1 D2 _ [DS IHD]]; first by exists [::].
by exists (D1 :: DS); rewrite IHD.
Qed.

Lemma foldr_join_Dyck_inj : injective (foldr join_Dyck nil_Dyck).
Proof.
by elim => [|D1 DS1 IHDS1] [|D2 DS2] // /join_Dyck_inj [-> /IHDS1 ->].
Qed.

Lemma size_foldr_join_Dyck DS :
  size (foldr join_Dyck nil_Dyck DS) =
  sumn (map (size \o dyckword) DS) + 2 * size DS.
Proof.
elim: DS => [|D DS IHDS] //=; rewrite size_cat /= IHDS.
by rewrite -!addnS addnA mulnS [2+_]addnC mul2n -addnn !addnA.
Qed.

Section Bij.

Fixpoint Dyck_of_bintree t :=
  if t is BinNode l r then
    join_Dyck (Dyck_of_bintree l) (Dyck_of_bintree r)
  else nil_Dyck.

Lemma bintree_of_Dyck_spec D :
  { t : bintree | Dyck_of_bintree t = D /\
                  forall t', Dyck_of_bintree t' = D -> t = t' }.
Proof.
elim/Dyck_ind: D => [|D1 D2 [t1 [PF1 Uniq1]] [t2 [PF2 Uniq2]]].
  by exists BinLeaf; split; last by case.
exists (BinNode t1 t2); split => /=; first by rewrite PF1 PF2.
by case => //= t'1 t'2 /join_Dyck_inj => [[/Uniq1 -> /Uniq2 ->]].
Qed.
Definition bintree_of_Dyck D := proj1_sig (bintree_of_Dyck_spec D).

Lemma bintree_of_DyckK D : Dyck_of_bintree (bintree_of_Dyck D) = D.
Proof.
by rewrite /bintree_of_Dyck; case: (bintree_of_Dyck_spec _) => /= [t []].
Qed.

Lemma bintree_of_nil_Dyck : bintree_of_Dyck nil_Dyck = BinLeaf.
Proof.
rewrite /bintree_of_Dyck.
by case: (bintree_of_Dyck_spec _) => [[|t1 t2] [Pf Uniq]].
Qed.

Lemma bintree_of_join_Dyck D1 D2 :
  bintree_of_Dyck (join_Dyck D1 D2) =
  BinNode (bintree_of_Dyck D1) (bintree_of_Dyck D2).
Proof.
rewrite {1}/bintree_of_Dyck.
case: (bintree_of_Dyck_spec _) => /= [[|t1 t2 /=] []]; first by move/eqP.
move/join_Dyck_inj => [H1 H2]; apply.
by rewrite /= !bintree_of_DyckK.
Qed.

Theorem Dyck_of_bintreeK t : bintree_of_Dyck (Dyck_of_bintree t) = t.
Proof.
elim: t => [|l IHl r IHr] /=; first exact: bintree_of_nil_Dyck.
by rewrite bintree_of_join_Dyck IHl IHr.
Qed.

Lemma size_Dyck_of_bintree t :
  size (Dyck_of_bintree t) = 2 * (size_tree t).
Proof.
elim: t => //= l Hl r Hr.
rewrite size_cat /= {}Hl Hr.
by rewrite !mulnDr muln1 -addn1 -addnA addSnnS addnA addnC addnA.
Qed.

Lemma size_bintree_of_Dyck D :
  2 * size_tree (bintree_of_Dyck D) = size D.
Proof. by rewrite -{2}(bintree_of_DyckK D) size_Dyck_of_bintree. Qed.

End Bij.
