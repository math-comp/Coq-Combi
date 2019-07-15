(** * Combi.Combi.DyckWord : Dyck Words *)
(******************************************************************************)
(*      Copyright (C) 2018-2019 Florent Hivert <florent.hivert@lri.fr>        *)
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



Lemma take_take (T : Type) i j (s : seq T) :
  i <= j -> take i (take j s) = take i s.
Proof.
elim: s i j => [// | a s IH] [|i] [|j] //=.
by rewrite ltnS => /IH ->.
Qed.

Lemma take_drop (T : Type) i j (s : seq T) :
  take i (drop j s) = drop j (take (i + j) s).
Proof.
elim: j s => [|j IH] s /=; first by rewrite !drop0 addn0.
by case: s => [// | a s]; rewrite addnS /=.
Qed.

Lemma take_addn (T : Type) (s : seq T) n m :
  take (n + m) s = take n s ++ take m (drop n s).
Proof.
elim: n m s => [|n IH] [|m] [|a s] //; first by rewrite take0 addn0 cats0.
by rewrite drop_cons addSn !take_cons /= IH.
Qed.

Lemma addnBAC m n p : n <= m -> m - n + p = m + p - n.
Proof. by move=> le_nm; rewrite addnC addnBA // addnC. Qed.


Inductive brace : Set := | Open : brace | Close : brace.

Local Notation "{{" := Open.
Local Notation "}}" := Close.

Definition bool_of_brace b := if b is {{ then true else false.
Definition brace_of_bool b := if b then {{ else }}.

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

Local Notation "#{{| a |" := (count_mem {{ a) (format "#{{| a |").
Local Notation "#}}| a |" := (count_mem }} a) (format "#}}| a |").


Section Defs.

Implicit Type n : nat.
Implicit Type w : seq brace.


Definition prefixes w := [seq take n w | n <- iota 0 (size w).+1].

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
  [qualify a w | all (fun p => #{{|p| >= #}}|p|) (prefixes w)].
Definition Dyck_word :=
  [qualify a w | (w \is a Dyck_prefix) && (#{{|w| == #}}|w|)].

Lemma Dyck_prefixP w :
  reflect (forall n, #{{|take n w| >= #}}|take n w|) (w \is a Dyck_prefix).
Proof.
rewrite unfold_in; apply (iffP allP) => /= H.
- by move=> i; apply H; apply take_prefixes.
- by move=> p /mem_prefixesP [i -> {p}].
Qed.

Lemma Dyck_wordP w :
  reflect
    ((forall n, #{{|take n w| >= #}}|take n w|) /\ (#{{|w| = #}}|w|))
    (w \is a Dyck_word).
Proof.
rewrite unfold_in.
by apply (iffP andP) => /= [] [H1 /eqP H2]; split => //; apply/Dyck_prefixP.
Qed.

Lemma Dyck_word_leqP w :
  reflect
    ((forall n, n <= size w -> #{{|take n w| >= #}}|take n w|) /\ (#{{|w| = #}}|w|))
    (w \is a Dyck_word).
Proof.
apply (iffP (Dyck_wordP w)) => [] [H1 H2]; split => // n.
case: (leqP n (size w)) => [|H]; first exact: H1.
by rewrite take_oversize ?H2 //; exact: ltnW.
Qed.

Lemma Dyck_word_OwC w :
  w \is a Dyck_word -> {{ :: w ++ [:: }}] \is a Dyck_word.
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
move=> /Dyck_wordP [Hpos1 Hbal1] /Dyck_wordP [Hpos2 Hbal2].
apply/Dyck_wordP; split => [n|].
- rewrite take_cat; case ltnP => _ //.
  by rewrite !count_cat Hbal1 leq_add2l.
- by rewrite !count_cat Hbal1 Hbal2.
Qed.
Lemma Dyck_word_flatten l :
  all (mem Dyck_word) l -> flatten l \is a Dyck_word.
Proof. elim: l => [| w l IHl] //= /andP [Hd /IHl]. exact: Dyck_word_cat. Qed.

Lemma Dyck_word_OwCw w1 w2 :
  w1 \is a Dyck_word -> w2 \is a Dyck_word ->
  {{ :: w1 ++ }} :: w2 \is a Dyck_word.
Proof.
move=> Hw1 Hw2.
rewrite -cat1s -[ }} :: _ ]cat1s !catA; apply Dyck_word_cat => //=.
exact: Dyck_word_OwC.
Qed.

End Defs.


Section DyckType.

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

Lemma DyckP D : (dyckword D) \is a Dyck_word.
Proof. exact: D. Qed.
Hint Resolve DyckP.

Definition dyck D mkD : Dyck :=
  mkD (let: DyckWord _ DP := D return dyckword D \is a Dyck_word in DP).

Lemma dyckE D : dyck (fun sP => @DyckWord D sP) = D.
Proof. by case: D. Qed.

Canonical nil_Dyck := (@DyckWord [::] is_true_true).
Canonical cat_Dyck D1 D2 := DyckWord (Dyck_word_cat D1 D2).
Canonical join_Dyck D1 D2 := DyckWord (Dyck_word_OwCw D1 D2).

End DyckType.

Notation "[ 'Dyck' 'of' s ]" := (dyck (fun sP => @DyckWord s sP))
  (at level 9, format "[ 'Dyck'  'of'  s ]") : form_scope.

Notation "[ 'Dyck' 'of' s 'by' pf ]" := (@DyckWord s pf)
  (at level 9, format "[ 'Dyck'  'of'  s  'by'  pf ]") : form_scope.

Notation "[ 'Dyck' {{ D1 }} D2 ]" := (join_Dyck D1 D2)
  (at level 8, format "[ 'Dyck'  {{  D1  }}  D2 ]",
   D1 at next level) : form_scope.


Section DyckFactor.

Implicit Type D : Dyck.


Lemma join_Dyck_nnil D1 D2 : [Dyck {{ D1 }} D2] != [Dyck of [::]].
Proof. by []. Qed.

Lemma Dyck_cut_ex D :
  D != [Dyck of [::]] -> exists i, (i != 0) && (#{{|take i D| == #}}|take i D|).
Proof.
move=> Hnnil; have:= DyckP D => /Dyck_wordP [_ Heq].
exists (size D); apply/andP; split; first by case: D Hnnil {Heq} => [[]].
- by rewrite take_size Heq.
Qed.

Theorem factor_Dyck D :
  D != [Dyck of [::]] -> { DD : Dyck * Dyck | D = [Dyck {{ DD.1 }} DD.2] }.
Proof.
move=> Hnnil.
case: (ex_minnP (Dyck_cut_ex Hnnil)) => cut /andP [Hcut /eqP Heq Hmin].
case: D Hnnil Heq Hmin => [[|w0 tl]] // HD _; rewrite [dyckword _]/=.
case: w0 HD => HD; first last.
  have:= HD; rewrite unfold_in => /andP [/Dyck_prefixP/(_ 1)].
  by rewrite /= take0 /= !addn0.
have:= (Dyck_wordP _ HD) => [[Hpos /eqP Hbal]].
case: cut Hcut => // [][|cut] _; rewrite [X in X -> _]/= add1n add0n.
  by rewrite take0.
move=> Heq Hmin.
have Hcut : cut < size tl.
  rewrite -ltnS; apply Hmin.
  by rewrite -[(size tl).+1]/(size ( {{ :: tl)) take_size Hbal /=.
have Hf1 : take cut.+1 tl = rcons (take cut tl) }}.
  move: Heq (Hpos cut.+1).
  rewrite /= (take_nth {{ Hcut) add0n add1n.
  rewrite !count_mem_rcons.
  case: (nth {{ tl cut) => []; rewrite eq_refl /= !addn1 !addn0 //.
  by move=> <-; rewrite ltnn.
move: Heq; rewrite Hf1 !count_mem_rcons /= addn0 addn1.
move=> /eqP; rewrite eqSS => /eqP Hbalcut.
have {Hmin} Hmin n : n <= cut -> #{{|take n tl| >= #}}|take n tl|.
  apply contraLR; rewrite -!ltnNge.
  case: cut Hbalcut Hmin {Hcut Hf1} => [ _ _ | cut Hbalcut Hmin Hlt].
    by case: n; first by rewrite take0.
  apply: (Hmin (n.+1)); rewrite /= add1n add0n.
  apply/eqP/anti_leq.
  rewrite Hlt /=.
  by have:= Hpos (n.+1); rewrite /= add1n add0n.
have HDL : (take cut tl) \is a Dyck_word.
  apply/Dyck_word_leqP; split => [n |]; last by rewrite Hbalcut.
  by rewrite size_take Hcut => Hncut; rewrite take_take // Hmin.
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

by apply/val_inj; rewrite /= -{1}(cat_take_drop cut.+1 tl) Hf1 cat_rcons.
Qed.

Lemma Dyck_fact_size D1 D2 :
  (size D1).+2 = ex_minn (Dyck_cut_ex (join_Dyck_nnil D1 D2)).
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
  rewrite -cat1s -[}} :: _]cat1s !catA take_size_cat ?size_cat /= ?addn1 //.
  rewrite !count_cat /= !addn0 add0n add1n addn1.
  by case: D1 => /= [d1 /Dyck_wordP [_ ->]].
Qed.

Theorem join_Dyck_inj D1 D2 E1 E2 :
  [Dyck {{D1}}D2] = [Dyck {{E1}}E2] -> (D1, D2) = (E1, E2).
Proof.
move=> Heq.
have Hnnil := join_Dyck_nnil D1 D2.
move: (Dyck_fact_size D1 D2).
rewrite (eq_ex_minn _ (Dyck_cut_ex (join_Dyck_nnil E1 E2)));
  last by move=> i; rewrite Heq.
rewrite -(Dyck_fact_size E1 E2) => /eqP; rewrite !eqSS => /eqP Hsz.
move: Heq => /(congr1 val)/= /eqP.
rewrite -[{{ :: _ ++ _]cat1s -[}} :: D2]cat1s !catA.
rewrite -[{{ :: _ ++ _]cat1s -[}} :: E2]cat1s !catA.
rewrite !eqseq_cat /= ?size_cat ?Hsz //=.
by move=> /andP [/andP [/eqP /val_inj -> _] /eqP /val_inj ->].
Qed.

End DyckFactor.


Section DyckSetInd.

Implicit Type D : Dyck.


Variable P : Dyck -> Type.
Hypotheses (Pnil : P nil_Dyck)
           (Pcons : forall D1 D2, P D1 -> P D2 -> P ([Dyck {{ D1 }} D2])).

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
    [Dyck {{ (Dyck_of_bintree l) }} Dyck_of_bintree r]
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
  bintree_of_Dyck ([Dyck {{ D1 }} D2]) =
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



Section BalToDyck.

Variable w : seq brace.


Definition maxd := \max_(s <- prefixes w) (#}}|s| - #{{|s|).

Lemma maxdE : maxd = \max_(i < (size w).+1) (#}}|take i w| - #{{|take i w|).
Proof.
rewrite /maxd /prefixes.
by rewrite big_map -{1}[(size w).+1]subn0 -/(index_iota _ _) big_mkord.
Qed.

Lemma maxdP : forall i : nat, #}}|take i w| - #{{|take i w| <= maxd.
Proof.
rewrite maxdE => i.
wlog ilt : i / i < (size w).+1.
  move=> Hlog; case: (ltnP i (size w).+1) => [| szi]; first exact: Hlog.
  rewrite (take_oversize (ltnW szi)) -{1 2}(take_size w).
  exact: Hlog.
rewrite -[i]/(nat_of_ord (Ordinal ilt)).
exact: leq_bigmax.
Qed.

Lemma exists_maxd : exists i : nat, #}}|take i w| - #{{|take i w| == maxd.
Proof.
rewrite maxdE.
have : #|'I_(size w).+1| > 0 by rewrite card_ord.
set F := BIG_F; case/(eq_bigmax F) => [[i Hi]]; rewrite {}/F /= => H.
by exists i; rewrite H.
Qed.

Definition pfmaxd := ex_minn exists_maxd.

Lemma pfmaxdP : #}}|take pfmaxd w| - #{{|take pfmaxd w| = maxd.
Proof. by rewrite /pfmaxd; case: ex_minnP => pfmd /eqP ->. Qed.

Lemma pfmaxd_size : pfmaxd <= size w.
Proof.
rewrite /pfmaxd; case: ex_minnP => pfmd /eqP Hpfmd pfmd_min.
rewrite leqNgt; apply/(introN idP) => Habs.
move: Hpfmd; rewrite (take_oversize (ltnW Habs)) -{1 2}(take_size w).
move=> /eqP/pfmd_min/leq_ltn_trans/(_ Habs).
by rewrite ltnn.
Qed.

Lemma pfmaxd_min :
  forall i : nat, i < pfmaxd -> #}}|take i w| - #{{|take i w| < maxd.
Proof.
rewrite /pfmaxd.
case: ex_minnP => pfmd /eqP Hpfmd pfmd_min i Hi.
rewrite ltn_neqAle maxdP andbT.
apply/(introN idP) => /(pfmd_min i)/(leq_trans Hi).
by rewrite ltnn.
Qed.


Hypothesis bal1 : #}}|w| = #{{|w|.+1.

Lemma maxd_pos : maxd > 0.
Proof.
move: bal1 => /eqP; rewrite leqNgt; apply contraL; rewrite ltnS leqn0 => /eqP.
rewrite maxdE /= => Hmax.
rewrite eq_sym neq_ltn ltnS; apply/orP; right.
pose sz := (Ordinal (ltnSn (size w))).
rewrite -(take_size w) -[size w]/(nat_of_ord sz) -subn_eq0 -leqn0 -Hmax.
exact: leq_bigmax.
Qed.

Lemma take_pfmaxd_leq : #{{|take pfmaxd w| <= #}}|take pfmaxd w|.
Proof. by apply ltnW; rewrite ltnNge -subn_eq0 pfmaxdP -lt0n maxd_pos. Qed.

Lemma pfmaxd_pos : pfmaxd > 0.
Proof. by case: pfmaxd maxd_pos pfmaxdP; first by rewrite take0; case maxd. Qed.

Lemma nth_pfmaxd : nth {{ w pfmaxd.-1 = }}.
Proof.
move: pfmaxdP pfmaxd_min pfmaxd_size.
case: pfmaxd pfmaxd_pos => //= pfmd _ Hpfmd pfmd_min pfmd_sz.
move/(_ _ (ltnSn pfmd)): pfmd_min => /=.
move: Hpfmd; rewrite (take_nth {{ pfmd_sz) !count_mem_rcons /= {pfmd_sz}.
case: nth => //=; rewrite addn0 addn1 => <-.
by rewrite subnS leqNgt ltnS leq_pred.
Qed.

Lemma last_rot_pfmaxd : last {{ (rot pfmaxd w) = }}.
Proof.
rewrite /rot last_cat -nth_pfmaxd -nth_last size_take_leq pfmaxd_size.
rewrite nth_take; last by case: pfmaxd pfmaxd_pos.
apply: set_nth_default.
by case: pfmaxd pfmaxd_pos pfmaxd_size.
Qed.

Lemma rot_pfmaxdE :
  rot pfmaxd w = rcons (take (size w).-1 (rot pfmaxd w)) }}.
Proof.
rewrite -{1}(cat_take_drop (size w).-1 (rot pfmaxd w)).
suff -> : drop (size w).-1 (rot pfmaxd w) = [:: }}] by rewrite cats1.
have hsz : size (drop (size w).-1 (rot pfmaxd w)) = 1.
  rewrite size_drop size_rot /=.
  by case: w bal1 => //= w0 tlw _; rewrite subSn // subnn.
apply (eq_from_nth (x0 := {{)) => [// | n].
rewrite hsz ltnS leqn0 => /eqP ->.
rewrite nth_drop addn0 /= -(size_rot pfmaxd) nth_last.
exact: last_rot_pfmaxd.
Qed.

Theorem rot_is_Dyck : take (size w).-1 (rot pfmaxd w) \is a Dyck_word.
Proof.
apply/Dyck_word_leqP; split => [n|].
- have -> : size (take (size w).-1 (rot pfmaxd w)) = (size w).-1.
    rewrite size_take size_rot /=.
    by case: w bal1 => //= w0 tlw _; rewrite ltnSn.
  move => Hn; rewrite take_take // /rot take_cat size_drop.
  case: ltnP => [{Hn} Hn| Hnpf].
  + have ctd p : count_mem p (take n (drop pfmaxd w)) =
                 count_mem p (take (pfmaxd + n) w) - count_mem p (take pfmaxd w).
      by rewrite take_addn count_cat addnC addnK.
    rewrite !ctd leq_subLR addnBA; first last.
      by rewrite take_addn count_cat leq_addr.
    rewrite [count _ _ + count _ _ ]addnC -addnBA ?take_pfmaxd_leq //.
    rewrite -leq_subLR pfmaxdP.
    exact: maxdP.
  + have {Hnpf} : n - (size w - pfmaxd) < pfmaxd.
      rewrite subnBA ?pfmaxd_size // addnC -subnBA ?leq_subr; first last.
        exact: (leq_trans Hn (leq_pred _)).
      case: w bal1 Hn Hnpf => // w0 wtl _ /= Hn.
      case: pfmaxd pfmaxd_pos => // pfm _; rewrite subSS => Hsz.
      rewrite [(_ - n)]subSn // subSS ltnS.
      exact: leq_subr.
    move: (n - (size w - pfmaxd)) => {n Hn} n Hn.
    rewrite !count_cat take_take; last exact: ltnW.
    rewrite -ltnS.
    have : #}}|take n w| < #{{|take n w| + maxd.
      move/pfmaxd_min: Hn; rewrite -leq_subLR.
      case: (leqP #{{|take n w| #}}|take n w|) => H; first by rewrite subSn.
      move=> _; move: H; rewrite /leq => /eqP ->.
      by rewrite sub0n.
    rewrite -(ltn_add2l #}}|drop pfmaxd w|) => /leq_trans; apply.
    rewrite addnC [X in X.+1]addnC -addnS -addnA leq_add2l.
    rewrite -pfmaxdP addnBAC ?take_pfmaxd_leq //.
    rewrite -count_cat cat_take_drop bal1.
    rewrite -{1}(cat_take_drop pfmaxd w) count_cat.
    by rewrite subSn  ?leq_addr // addnC addnK.
- move: bal1; have /perm_eqlP/perm_eqP Hperm := (perm_rot pfmaxd w).
  by rewrite -!{}Hperm {1 2}rot_pfmaxdE !count_mem_rcons /= addn0 addn1 => [[]].
Qed.

End BalToDyck.


Section DyckToBal.

Variables (w : seq brace) (rt : nat).
Hypothesis HDyck : w \is a Dyck_word.
Hypothesis Hrt: rt <= size w.

Definition rrw := rot rt (rcons w }}).

Lemma rrw_bal1 : #}}|rrw| = #{{|rrw|.+1.
Proof.
have /perm_eqlP/perm_eqP Hperm := (perm_rot rt (rcons w }})).
rewrite !Hperm !count_mem_rcons /= addn1 addn0.
by move: HDyck => /Dyck_wordP [_ ->].
Qed.

Let d := [:: {{; }}; {{; {{; }}; }}; {{; }}].
Eval compute in size d.
                                   (* 012345678 *)
Eval compute in rot 0 (rcons d }}).  (* ()(())()) maxd = 1, pfmaxd = 9 *)
Eval compute in rot 1 (rcons d }}).  (* )(())())( maxd = 2, pfmaxd = 8 *)
Eval compute in rot 2 (rcons d }}).  (* (())())() maxd = 1, pfmaxd = 7 *)
Eval compute in rot 3 (rcons d }}).  (* ())())()( maxd = 2, pfmaxd = 6 *)
Eval compute in rot 4 (rcons d }}).  (* ))())()(( maxd = 3, pfmaxd = 5 *)
Eval compute in rot 5 (rcons d }}).  (* )())()(() maxd = 2, pfmaxd = 4 *)
Eval compute in rot 6 (rcons d }}).  (* ())()(()) maxd = 1, pfmaxd = 3 *)
Eval compute in rot 7 (rcons d }}).  (* ))()(())( maxd = 2, pfmaxd = 2 *)
Eval compute in rot 8 (rcons d }}).  (* )()(())() maxd = 1, pfmaxd = 1 *)


Lemma maxd_rrw : maxd rrw = (#{{|take rt w| - #}}|take rt w|).+1.
Proof.
rewrite maxdE /rrw size_rot size_rcons.
apply/anti_leq/andP; split.
- apply/bigmax_leqP => /= [[i Hi]] /= _.
  rewrite /rot take_cat size_drop size_rcons subSn // ltnS.
  case: (leqP i _) => Hirt.
  + rewrite {Hi} take_drop.
    set dr := drop _ _.
    case: (leqP #}}|dr| #{{|dr|); first by rewrite -subn_eq0 => /eqP ->.
    rewrite {}/dr => /ltnW Hit.
    rewrite -(leq_add2l #}}|take rt (take (i + rt) (rcons w }}))|) addnBA //.
    rewrite -count_cat cat_take_drop take_take ?leq_addl //.
    rewrite -cats1 !take_cat.
    move: Hrt; rewrite leq_eqVlt => [/orP [/eqP|] Hrt1].
    * subst rt; move: Hirt; rewrite ltnn subnn take0 leqn0 => /eqP ->.
      rewrite add0n ltnn subnn take0 take_size cats0 drop_size /=.
      by rewrite subn0 leq_addr.
    move: Hirt; rewrite leq_eqVlt => [/orP [/eqP|] Hirt].
    * subst i; rewrite Hrt1 subnK; last exact: ltnW.
      rewrite ltnn subnn take0 cats0.
      rewrite addnS subnKC; last by move: HDyck => /Dyck_wordP [] ->.
      move: HDyck => /Dyck_wordP [] _ <-.
      by rewrite -{1}(cat_take_drop rt w) count_cat addnK.
    * rewrite ltn_subRL addnC in Hirt.
      rewrite Hirt Hrt1.
      rewrite addnS subnKC; last by move: HDyck => /Dyck_wordP [] ->.
      rewrite -take_drop.
      admit.
  + 
Admitted.

  
    
Lemma rrw_pfmaxd : pfmaxd rrw = (size w).+1 - rt.
Proof.
rewrite /pfmaxd; case: ex_minnP => m /eqP; rewrite maxdE => Hmaxd Hmin.
have hsrt : (size w).+1 - rt < (size rrw).+1.
  by rewrite /rrw size_rot size_rcons ltnS subSn // ltnS leq_subr.
apply/anti_leq/andP; split.
apply/Hmin/eqP/anti_leq/andP; split.
- by rewrite -/(nat_of_ord (Ordinal hsrt)) leq_bigmax.
- apply/bigmax_leqP => /= [[i Hi] _] /=.
  rewrite /rrw /rot !take_cat !size_drop size_rcons ltnn subnn take0 cats0.
  case: ltnP => Hi1.
  + set dr := drop _ _.
    case: (leqP #}}|take i dr| #{{|take i dr|).
      by rewrite -subn_eq0 => /eqP ->.
    rewrite {}/dr  => Hit]; rewrite take_drop.
    rewrite -(leq_add2l #}}|take rt (rcons w }})|).
    rewrite addnBA.
  admit.
- 
End DyckToBal.

End Balanced.
