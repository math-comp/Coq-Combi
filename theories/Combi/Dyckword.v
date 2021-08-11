(** * Combi.Combi.Dyckword : Dyck Words *)
(******************************************************************************)
(*      Copyright (C) 2019-2020 Florent Hivert <florent.hivert@lri.fr>        *)
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

A _Dyck word_ is a word on the two letter alphabet "(" and ")" which is well
parentesized. More formally

- for all prefix, the number of "(" is larger that the number of ")";
- the total number of "(" is equal to those of ")".

We encode those words using:

- [brace]      == a type with two values [Open] and [Close] and locally use
       the notations "[{{]" and "[}}]"
- [height w]   == the difference between the number of "[{{]" and "[}}]"
- [prefixes w] == the list of all the prefix of [w]

- [w is a Dyck_prefix] <=> for all prefix, the number of "[{{]" is larger than
       the number of "[}}]"
- [w is a Dyck_word] <=> [w] is a Dyck word, that is a Dyck_prefix of height 0

- [Dyck]       == a Sigma-type for Dyck words. It is canonically a [countType]
- [[Dyck of s]] == a Dyck word for the sequence [s]; the proof is canonically
       infered.
- [[Dyck of s by pf]] == a Dyck word for the sequence [s] using the proof [pf]
- [[Dyck {{ D1 }} D2]] == the term of type [Dyck] corresponding to the word
       "(D1)D2", assuming that [D1] and [D2] are of type [Dyck]

Dyck words are in bijection with binary trees:

- [Dyck_of_bintree t] == the image of the binary tree [t] by the standard
       bijection from trees to Dyck words.
- [bintree_of_Dyck D] == the converse bijection

The main result of this file is to show that the number of Dyck word is the
so-called Catalan numbers defined below:

- [Catalan n]  == the [n]-th Catalan number ['C(n.*2, n) %/ n.+1]
- [Dyck_hsz n] == the set of tuple of half size n which are Dyck words
- [bal_hsz n]  == the set of tuple of half size n which are balanced words

We prove bijectively the equality with catalan binomial formula, using the
rotation trick: there is a (n+1) to 1 map from balanced words to Dyck words.

- [minh w]     == the minimal height of prefixes of [w]
- [pfminh w]   == the first position where the minimal height is reached
- [Dyck_of_bal w] == given a balanced word [w] returns the unique Dyck word
       [D] such that [D)] is a rotation of [w)]
- [bal_of_Dyck rt w] == the word obtained by rotating [w)] by [rt] and
       removing the last letter.

- [bal_part n] == the partition of balanced words given by the fiber of the
       [Dyck_of_bal] map. The main argument is to show that all the fibers
       have the same cardinality n+1.
 *********************)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun bigop ssrnat eqtype fintype choice.
From mathcomp Require Import seq tuple path fingraph finset order.
From mathcomp Require Import div ssralg ssrint ssrnum binomial.

Require Import tools combclass bintree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Section PreimPartition.

Variables (T rT : finType) (f : T -> rT) (D : {set T}).

Lemma mem_preim_partition (B : {set T}) :
  B \in preim_partition f D ->
  exists x0 : T, (x0 \in B) /\ (B = D :&: f @^-1: [set f x0]).
Proof.
move=> HB.
have /and3P [/eqP Hcov Htriv notP0] := preim_partitionP f D.
have /set0Pn [x Bx] : B != set0 := memPn notP0 B HB.
have Hx : x \in D by rewrite -Hcov; apply/bigcupP; exists B.
have Bblock : pblock (preim_partition f D) x = B by apply def_pblock.
exists x; split => //; apply/setP => y; rewrite inE -Bblock.
case: (boolP (y \in D)) => /= Hy; first last.
- apply negbTE; move: Hy; apply contra => Hy.
  rewrite -Hcov; apply/bigcupP; exists B => //.
  by rewrite -Bblock.
- by rewrite inE pblock_equivalence_partition ?inE //; split => // /eqP ->.
Qed.

Lemma imset_transversal_preim :
  f @: (transversal (preim_partition f D) D) = f @: D.
Proof.
have /and3P [/eqP Hcover Htriv _] := preim_partitionP f D.
have Htr := transversalP (preim_partitionP f D).
have /subsetP := transversal_sub Htr.
move: Htr; set tr := transversal _ _ => Htr Hsub.
apply/setP => y.
apply/imsetP/imsetP => [] [x Hx -> {y}]; first by exists x; first apply Hsub.
have := Hx; rewrite -{1}Hcover => HxD.
exists (transversal_repr x tr (pblock (preim_partition f D) x)).
- by apply: (repr_mem_transversal Htr); apply: pblock_mem.
- apply/esym/eqP.
  move: HxD => /pblock_mem/(transversal_reprK Htr x)/eqP.
  rewrite eq_pblock //; first last.
    rewrite Hcover; apply/Hsub/(repr_mem_transversal Htr).
    by apply pblock_mem; rewrite Hcover.
  rewrite pblock_equivalence_partition //.
  + by split => // /eqP ->.
  + apply/Hsub/(repr_mem_transversal Htr).
    by apply pblock_mem; rewrite Hcover.
Qed.

Lemma card_preim_partition : #|preim_partition f D| = #|f @: D|.
Proof.
have Htr := transversalP (preim_partitionP f D).
have /subsetP := transversal_sub Htr.
rewrite -(card_transversal Htr) -imset_transversal_preim.
move: (transversal _ _ ) Htr => tr Htr Hsub.
apply/esym/card_in_imset => x y Hx Hy Heq.
apply: (pblock_inj Htr Hx Hy); apply same_pblock.
  by have /and3P [] := preim_partitionP f D.
rewrite pblock_equivalence_partition ?Heq //; try exact: Hsub.
by split => // /eqP ->.
Qed.

End PreimPartition.


Lemma card_preim_nth (m : nat) (T : eqType) (s : seq T) (P : pred T) (u : T):
  size s = m -> #|[set i : 'I_m | preim (nth u s) P i]| = count P s.
Proof.
move=> Hsz.
rewrite cardsE cardE /enum_mem -enumT /=.
rewrite (eq_filter (a2 := (fun i : 'I_m => preim (nth u s) P i))); first last.
  by move=> i; rewrite inE unfold_in.
rewrite -(size_map nat_of_ord) -filter_map val_enum_ord.
have:= mkseq_nth u s; rewrite /mkseq.
move=> /(congr1 (filter P))/(congr1 size).
by rewrite [X in _ = X]size_filter filter_map size_map Hsz.
Qed.



(** * Braces and Dyck words *)
Inductive brace : Set := | Open : brace | Close : brace.

Local Notation "{{" := Open.
Local Notation "}}" := Close.

Definition bool_of_brace b := if b is {{ then true else false.
Definition brace_of_bool b := if b then {{ else }}.

Lemma bool_of_braceK : cancel bool_of_brace brace_of_bool. Proof. by case. Qed.
Lemma brace_of_boolK : cancel brace_of_bool bool_of_brace. Proof. by case. Qed.

Definition brace_eqMixin := InjEqMixin (can_inj bool_of_braceK).
Canonical brace_eqType := Eval hnf in EqType brace brace_eqMixin.
Definition brace_choiceMixin := CanChoiceMixin bool_of_braceK.
Canonical brace_choiceType := Eval hnf in ChoiceType brace brace_choiceMixin.
Definition brace_countMixin := CanCountMixin bool_of_braceK.
Canonical brace_countType := Eval hnf in CountType brace brace_countMixin.
Definition brace_finMixin := CanFinMixin bool_of_braceK.
Canonical brace_finType := Eval hnf in FinType brace brace_finMixin.


Lemma size_count_braceE (w : seq brace) :
  size w = count_mem {{ w + count_mem }} w.
Proof.
elim: w => //= w0 w IHw.
rewrite [(_ + count_mem }} w)%N]addnC !addnA.
rewrite -[((w0 == {{) + count_mem _ _ + _)%N]addnA -IHw.
by case: w0 => /=; rewrite ?addn0 ?add0n ?addn1 ?add1n.
Qed.


Import GRing.Theory Num.Theory.
Open Scope int_scope.
Open Scope ring_scope.


(** ** Height of a word *)
Section Defs.

Implicit Type n : nat.
Implicit Type u v w : seq brace.

Definition height w : int := Posz (count_mem {{ w) - Posz (count_mem }} w).

Lemma height_nil : height [::] = 0.
Proof. by []. Qed.

Lemma height_cons l v :
  height (l :: v) = (if l == {{ then 1 else -1) + height v.
Proof.
rewrite /height /=; case: l; rewrite /= add0n !PoszD !addrA //.
by rewrite opprD /= addrA.
Qed.

Lemma height_rcons v l :
  height (rcons v l) = height v + (if l == {{ then 1 else -1).
Proof.
rewrite /height /= !count_rcons.
case: l; rewrite /= addn0 PoszD ?opprD ? addrA //.
by rewrite -addrA [1 - _]addrC addrA.
Qed.

Lemma height_cat u v : height (u ++ v) = height u + height v.
Proof.
rewrite /height !count_cat !PoszD [X in -X]addrC opprD -!addrA; congr (_ + _).
by rewrite [RHS]addrC addrA.
Qed.

Definition height_simpl := (height_cons, height_rcons, height_cat, height_nil).

Lemma height_drop n u : height (drop n u) = height u - height (take n u).
Proof.
rewrite -{2}(cat_take_drop n u) height_cat.
by rewrite addrC addrA [-_ + _]addrC subrr add0r.
Qed.

Lemma height_rev u : height (rev u) = height u.
Proof. by rewrite /height !count_rev. Qed.

Lemma height_nseq n b :
  height (nseq n b) = Posz n * (if b == {{ then 1 else -1).
Proof.
elim: n => [|n IHn] /=; rewrite !height_simpl ?mul0r // IHn.
by rewrite -[X in X + _]mul1r -mulrDl -PoszD add1n.
Qed.


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


(** ** Definitions *)
Definition Dyck_prefix :=
  [qualify a w : seq brace |
   all (fun p : seq brace => height p >= 0) (prefixes w)].
Definition Dyck_word :=
  [qualify a w : seq brace | (w \is a Dyck_prefix) && (height w == 0)].

Lemma Dyck_prefixP w :
  reflect (forall n, height (take n w) >= 0) (w \is a Dyck_prefix).
Proof.
rewrite unfold_in; apply (iffP allP) => /= H.
- by move=> i; apply H; apply take_prefixes.
- by move=> p /mem_prefixesP [i -> {p}].
Qed.

Lemma Dyck_wordP w :
  reflect
    ((forall n, height (take n w) >= 0) /\ (height w = 0))
    (w \is a Dyck_word).
Proof.
rewrite unfold_in.
by apply (iffP andP) => /= [] [H1 /eqP H2]; split => //; apply/Dyck_prefixP.
Qed.

Lemma height_take_leq (h : int) w :
  (forall n : nat, h <= height (take n w)) <->
  (forall n : nat, (n <= size w)%N -> h <= height (take n w)).
Proof.
split => H n //; case (leqP n (size w)); first exact: H.
move=> /ltnW/take_oversize ->.
by rewrite -[w](take_oversize (leqnn _)); apply H.
Qed.

Lemma Dyck_word_OwC w :
  w \is a Dyck_word -> {{ :: w ++ [:: }}] \is a Dyck_word.
Proof.
move/Dyck_wordP => [Hpos Hbal]; apply/Dyck_wordP; split => [n|].
- case: n => [|n /=]; first by rewrite take0.
  rewrite height_cons /=.
  case: (leqP n (size w)) => [/takel_cat -> | Hsz].
  + by apply: (le_trans (Hpos n)); rewrite -subr_ge0 addrK.
  + rewrite take_oversize ?size_cat /= ?addn1 //.
    by rewrite !height_simpl /= addr0 addrC subrK -(take_size w).
- by rewrite !height_simpl /= Hbal addr0 add0r subrr.
Qed.

Lemma Dyck_word_cat w1 w2 :
  w1 \is a Dyck_word -> w2 \is a Dyck_word -> w1 ++ w2 \is a Dyck_word.
Proof.
move=> /Dyck_wordP [Hpos1 Hbal1] /Dyck_wordP [Hpos2 Hbal2].
apply/Dyck_wordP; split => [n|].
- rewrite take_cat; case ltnP => _ //.
  by rewrite height_cat Hbal1 add0r.
- by rewrite height_cat Hbal1 Hbal2.
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


(** ** Sigma type for Dyck words *)
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
Hint Resolve DyckP : core.

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


(** * Standard factorization of Dyck words *)
Section DyckFactor.

Implicit Type D : Dyck.


Lemma Dyck_cut_ex D :
  D != [Dyck of [::]] -> exists i, (i != 0)%N && (height (take i D) == 0).
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
  have:= HD; rewrite unfold_in => /andP [/Dyck_prefixP/(_ 1%N)].
  by rewrite /= take0 !height_simpl /= addr0.
have:= (Dyck_wordP _ HD) => [[Hpos /eqP Hbal]].
case: cut Hcut => // [][|cut] _;
  rewrite [X in X -> _]/= !height_simpl [X in X -> _]/= ?take0 ?height_simpl //.
move=> Heq Hmin.
have Hcut : (cut < size tl)%N.
  rewrite -ltnS; apply Hmin.
  by rewrite -[(size tl).+1]/(size ( {{ :: tl)) take_size Hbal /=.
have Hf1 : take cut.+1 tl = rcons (take cut tl) }}.
  move: Heq (Hpos cut.+1).
  rewrite /= (take_nth {{ Hcut) !height_simpl /=.
  case: (nth {{ tl cut) => //=.
  by rewrite addrC -addrA => /eqP; rewrite addr_eq0 => /eqP ->.
move: Heq; rewrite Hf1 !height_simpl! /= addrC subrK => Hbalcut.
have {}Hmin n : (n <= cut)%N -> height (take n tl) >= 0.
  apply contraLR; rewrite -ltnNge -ltNge.
  case: cut Hbalcut Hmin {Hcut Hf1} => [ _ _ | cut Hbalcut Hmin Hlt].
    by case: n; first by rewrite take0.
  apply: (Hmin (n.+1)); rewrite /= height_simpl /= eq_le.
  apply/andP; split; first by rewrite lez_add1r.
  by have:= Hpos (n.+1); rewrite /= !height_simpl /=.
have HDL : (take cut tl) \is a Dyck_word.
  apply/Dyck_wordP; split; last by rewrite Hbalcut.
  rewrite height_take_leq => n.
  by rewrite size_take Hcut => Hncut; rewrite take_take // Hmin.
have HDR : (drop cut.+1 tl) \is a Dyck_word.
  apply/Dyck_wordP; split => [n|].
  - rewrite take_drop height_drop.
    rewrite take_take ?ltnS ?leq_addl //.
    rewrite Hf1 height_rcons /= Hbalcut sub0r /=.
    have := Hpos ((n + cut.+1).+1)%N.
    by rewrite /= height_simpl /= addrC.
  - move: Hbal; rewrite -{1}(cat_take_drop cut.+1 tl) => /eqP.
    by rewrite Hf1 /= !height_simpl /= Hbalcut add0r addrA subrr add0r.
exists (DyckWord HDL, DyckWord HDR).
by apply/val_inj; rewrite /= -{1}(cat_take_drop cut.+1 tl) Hf1 cat_rcons.
Qed.

Theorem join_Dyck_inj D1 D2 E1 E2 :
  [Dyck {{D1}}D2] = [Dyck {{E1}}E2] -> (D1, D2) = (E1, E2).
Proof.
have join_Dyck_nnil d1 d2 : [Dyck {{ d1 }} d2] != [Dyck of [::]] by [].
have Dyck_fact_size (d1 d2 : Dyck) :
  (size d1).+2 = ex_minn (Dyck_cut_ex (join_Dyck_nnil d1 d2)).
  case: ex_minnP => cut /andP [Hcut /eqP Heq Hmin].
  apply/anti_leq/andP; split.
  - move: Heq => /eqP {Hmin}; rewrite leqNgt; apply contraL; rewrite ltnS.
    case: cut Hcut => [// | cut _]; rewrite ltnS => Hcut.
    rewrite /= take_cat.
    move: Hcut; rewrite leq_eqVlt => /orP [/eqP -> | ->].
    + rewrite ltnn subnn  /= !height_simpl /= addr0.
      by case: d1 => /= [d1 /Dyck_wordP [_ ->]]; rewrite addr0.
    + rewrite !height_simpl /=.
      case: d1 => /= [d1 /Dyck_wordP [/(_ cut) H _]].
      by apply lt0r_neq0; rewrite ltz_add1r.
  - apply: Hmin; rewrite /= {Heq}.
    rewrite -cat1s -[}} :: _]cat1s !catA take_size_cat ?size_cat /= ?addn1 //.
    rewrite !height_simpl /= addr0 addrC subrK.
    by case: d1 => /= [d1 /Dyck_wordP [_ ->]].
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


(** ** Induction on Dyck words following the standard factorization *)
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
  by have -> : D = nil_Dyck by apply: val_inj.
case (altP (D =P nil_Dyck)) => [-> //| /factor_Dyck [[D1 D2] /= ->]].
rewrite /= ltnS size_cat /= addnS => /ltnW Hsz.
apply: Pcons; apply IHn.
- exact: (leq_trans (leq_addr (size D2) (size D1))).
- exact: (leq_trans (leq_addl (size D1) (size D2))).
Qed.

End DyckSetInd.


(** ** Examples of application of the induction principle *)
Lemma Dyck_size_even (D : Dyck) : ~~ odd (size D).
Proof.
elim/Dyck_ind: D => //= D1 D2 /negbTE HD1 /negbTE HD2.
by rewrite size_cat /= addnS /= negbK oddD negb_add HD1 HD2.
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
  (size (foldr join_Dyck nil_Dyck DS) =
   sumn (map (size \o dyckword) DS) + 2 * size DS)%N.
Proof.
elim: DS => [|D DS IHDS] //=; rewrite size_cat /= IHDS.
by rewrite -!addnS addnA mulnS [(2 + _)%N]addnC mul2n -addnn !addnA.
Qed.


(** ** Bijection with binary trees *)
Section BijBinTrees.

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
  size (Dyck_of_bintree t) = (size_tree t).*2.
Proof.
elim: t => //= l Hl r Hr.
by rewrite size_cat /= {}Hl Hr addnS -doubleD -doubleS -addnA add1n.
Qed.

Lemma size_bintree_of_Dyck D :
  (size_tree (bintree_of_Dyck D)).*2 = size D.
Proof. by rewrite -{2}(bintree_of_DyckK D) size_Dyck_of_bintree. Qed.

End BijBinTrees.


(** * Dyck and balanced words *)
(** ** Rotation map from balanced words to a Dyck words *)
Section BalToDyck.

Variable w : seq brace.

Definition minh :=
  - Posz (\max_(s <- prefixes w) (count_mem }} s - count_mem {{ s)).

Lemma minhE :
  minh = - Posz (\max_(i < (size w).+1)
                  (count_mem }} (take i w) - count_mem {{ (take i w))).
Proof.
rewrite /minh /prefixes.
by rewrite big_map -{1}[(size w).+1]subn0 -/(index_iota _ _) big_mkord.
Qed.

Lemma minhP : forall i : nat, height (take i w) >= minh.
Proof.
rewrite /height minhE => i.
wlog ilt : i / (i < (size w).+1)%N.
  move=> Hlog; case: (ltnP i (size w).+1) => [| szi]; first exact: Hlog.
  rewrite (take_oversize (ltnW szi)) -{9 10}(take_size w).
  exact: Hlog.
case: (leqP (count_mem {{ (take i w)) (count_mem }} (take i w))) => [H|].
- rewrite -[i]/(nat_of_ord (Ordinal ilt)).
  rewrite ler_oppl opprB subzn // lez_nat.
  exact: leq_bigmax.
- move=> /ltnW.
  rewrite -lez_nat -[in X in X -> _]subr_ge0 => /(le_trans _); apply.
  by rewrite -oppr_ge0 opprK.
Qed.

Lemma exists_minh : exists i : nat, height (take i w) == minh.
Proof.
rewrite /height minhE.
have : (#|'I_(size w).+1| > 0)%N by rewrite card_ord.
set F := BIG_F; case/(eq_bigmax F) => [[i Hi]]; rewrite {}/F /= => Hmax.
case: (leqP (count_mem {{ (take i w)) (count_mem }} (take i w))) => [Hle |/ltnW].
- by exists i; rewrite -eqr_opp opprK opprB (subzn Hle) Hmax.
- rewrite -subn_eq0 => /eqP Heq; move: Hmax; rewrite Heq => ->.
  by exists 0%N; rewrite take0.
Qed.

Definition pfminh := ex_minn exists_minh.

Lemma pfminhP : height (take pfminh w) = minh.
Proof. by rewrite /pfminh; case: ex_minnP => pfmd /eqP ->. Qed.

Lemma pfminh_size : (pfminh <= size w)%N.
Proof.
rewrite /pfminh; case: ex_minnP => pfmd /eqP Hpfmd pfmd_min.
rewrite leqNgt; apply/negP => Habs.
move: Hpfmd; rewrite (take_oversize (ltnW Habs)) -(take_size w).
move=> /eqP/pfmd_min/leq_ltn_trans/(_ Habs).
by rewrite ltnn.
Qed.

Lemma pfminh_min :
  forall i : nat, (i < pfminh)%N -> height (take i w) > minh.
Proof.
rewrite /pfminh.
case: ex_minnP => pfmd /eqP Hpfmd pfmd_min i.
rewrite ltnNge ltNge; apply contra => H.
by apply pfmd_min; rewrite eq_le H minhP.
Qed.

Lemma pfminhE n :
  (n <= size w)%N ->
  (forall i : nat, height (take i w) >= height (take n w)) ->
  (forall i : nat, (i < n)%N -> height (take i w) > height (take n w)) ->
  n = pfminh.
Proof.
move=> Hnsz Hleq Hltn.
have Hnsz1 : (n < (size w).+1)%N by rewrite ltnS.
have Hminh : height (take n w) = minh.
  by apply/eqP; rewrite eq_le minhP -pfminhP Hleq.
rewrite Hminh in Hleq, Hltn.
rewrite /pfminh; case: ex_minnP => pfmd /eqP Hpfmd pfmd_min.
apply/anti_leq/andP; split.
- move: Hpfmd => /eqP; rewrite eq_le => /andP [H _].
  move: H; rewrite leNgt leqNgt; apply contra.
  exact: Hltn.
- by apply pfmd_min; rewrite Hminh.
Qed.


Hypothesis Hbal1 : height w = -1.

Lemma minh_neg : minh < 0.
Proof.
rewrite oppr_lt0 gtz0_ge1 -ler_opp2 -Hbal1.
rewrite -{2}(take_size w).
exact: minhP.
Qed.

Lemma pfminh_pos : (pfminh > 0)%N.
Proof.
rewrite lt0n; apply/negP => /eqP H.
by have:= minh_neg; rewrite -pfminhP H take0 height_simpl.
Qed.

Lemma nth_pfminh : nth {{ w pfminh.-1 = }}.
Proof.
move: pfminhP pfminh_min pfminh_size.
case: pfminh pfminh_pos => //= pfmh _ Hpfmh pfmh_min pfmh_sz.
move/(_ _ (ltnSn pfmh)): pfmh_min => /=.
move: Hpfmh; rewrite (take_nth {{ pfmh_sz) height_simpl /=.
by case: nth => //= <- /ltW; rewrite lez_addr1 ltxx.
Qed.

Lemma last_rot_pfminh : last {{ (rot pfminh w) = }}.
Proof.
rewrite /rot last_cat -nth_pfminh -nth_last size_takel ?pfminh_size //.
rewrite nth_take; last by case: pfminh pfminh_pos.
apply: set_nth_default.
by case: pfminh pfminh_pos pfminh_size.
Qed.

Lemma rot_pfminhE :
  rcons (take (size w).-1 (rot pfminh w)) }} = rot pfminh w.
Proof.
rewrite -{2}(cat_take_drop (size w).-1 (rot pfminh w)).
suff -> : drop (size w).-1 (rot pfminh w) = [:: }}] by rewrite cats1.
have hsz : size (drop (size w).-1 (rot pfminh w)) = 1%N.
  rewrite size_drop size_rot /=.
  by case: w Hbal1 => //= w0 tlw _; rewrite subSn // subnn.
apply (eq_from_nth (x0 := {{)) => [// | n].
rewrite hsz ltnS leqn0 => /eqP ->.
rewrite nth_drop addn0 /= -(size_rot pfminh) nth_last.
exact: last_rot_pfminh.
Qed.

Theorem rot_is_Dyck : take (size w).-1 (rot pfminh w) \is a Dyck_word.
Proof.
apply/Dyck_wordP; rewrite height_take_leq; split => [n|].
- have -> : size (take (size w).-1 (rot pfminh w)) = (size w).-1.
    rewrite size_take size_rot /=.
    by case: w Hbal1 => //= w0 tlw _; rewrite ltnSn.
  move => Hn; rewrite take_take // /rot take_cat size_drop.
  case: ltnP => [{}Hn| Hnpf].
  + rewrite take_drop height_drop take_take ?leq_addl // subr_ge0.
    by rewrite pfminhP minhP.
  + have {Hnpf} : (n - (size w - pfminh) < pfminh)%N.
      rewrite subnBA ?pfminh_size // addnC -subnBA ?leq_subr; first last.
        exact: (leq_trans Hn (leq_pred _)).
      case: w Hbal1 Hn Hnpf => // w0 wtl _ /= Hn.
      case: pfminh pfminh_pos => // pfm _; rewrite subSS => Hsz.
      rewrite [(_ - n)%N]subSn // subSS ltnS.
      exact: leq_subr.
    move: (n - (size w - pfminh))%N => {}n {}Hn.
    rewrite height_simpl take_take; last exact: ltnW.
    move: Hbal1; rewrite -{1}(cat_take_drop pfminh w) height_simpl => /eqP.
    rewrite -subr_eq0 opprK [height _ + _]addrC -addrA addr_eq0 => /eqP ->.
    rewrite addrC subr_ge0 lez_addr1.
    by rewrite pfminhP pfminh_min.
- have : height (rot pfminh w) = -1.
    by rewrite /rot height_cat addrC -height_cat cat_take_drop.
  rewrite -{1}rot_pfminhE height_simpl /= => /eqP.
  by rewrite subr_eq => /eqP ->.
Qed.

End BalToDyck.


Section DyckToBal.

Variables (w : seq brace) (rt : nat).
Hypothesis HDyck : w \is a Dyck_word.
Hypothesis Hrt: (rt <= (size w))%N.

Lemma rrw_bal1 : height (rot rt (rcons w }})) = -1.
Proof.
rewrite /rot height_cat addrC -height_cat cat_take_drop.
apply/eqP; rewrite height_simpl /= subr_eq.
by move: HDyck => /Dyck_wordP [_ ->].
Qed.

Lemma pfminh_rrw :
  pfminh (rot rt (rcons w }})) = ((size w).+1 - rt)%N.
Proof.
apply/esym/pfminhE => [|i|i].
- by rewrite size_rot size_rcons subSn // ltnS leq_subr.
- rewrite /rot !take_cat !size_drop !size_rcons.
  rewrite subSn // ltnS ltnn subnn take0 cats0 ltnS.
  rewrite -(leq_add2r rt) subnK //.
  case: leqP => Hi.
  + rewrite take_drop !height_drop take_take ?leq_addl //.
    rewrite ler_sub_addr subrK -cats1 takel_cat //.
    rewrite !height_simpl /= addr0.
    move: HDyck => /Dyck_wordP [H1 ->].
    rewrite add0r; apply: (le_trans _ (H1 _)).
    by rewrite -oppr_ge0 opprK.
  + rewrite height_simpl addrC -ler_subl_addr subrr.
    case: (leqP (i - (size w - rt).+1) rt) => [H | /ltnW H].
    * rewrite take_take // -cats1 takel_cat; last exact: leq_trans H Hrt.
      by move: HDyck => /Dyck_wordP [->].
    * rewrite take_oversize ?size_take ?size_rcons ?ltnS ?Hrt //.
      rewrite -cats1 takel_cat //.
      by move: HDyck => /Dyck_wordP [->].
- rewrite subSn // ltnS => Hi.
  rewrite /rot !take_cat !size_drop !size_rcons.
  rewrite subSn // ltnS ltnn subnn take0 cats0 ltnS Hi.
  rewrite take_drop !height_drop take_take ?leq_addl //.
  rewrite ltr_subl_addl addrC subrK.
  rewrite height_rcons /=; move: HDyck => /Dyck_wordP [_ ->].
  move: Hi; rewrite -(leq_add2r rt) subnK // => Hi.
  rewrite add0r -cats1 takel_cat //.
  rewrite -subr_gt0 opprK ltz_addr1.
  by move: HDyck => /Dyck_wordP [H1 _].
Qed.

Lemma minh_rrw : minh (rot rt (rcons w }})) = - height (take rt w) - 1.
Proof.
rewrite -pfminhP pfminh_rrw.
rewrite /rot !take_cat !size_drop !size_rcons.
rewrite subSn // ltnS ltnn subnn take0 cats0.
rewrite height_drop height_simpl /=.
move: HDyck => /Dyck_wordP [_ ->]; rewrite add0r addrC.
by rewrite -cats1 takel_cat.
Qed.

End DyckToBal.


Close Scope ring_scope.

(** * Catalan numbers *)
Definition Catalan n := 'C(n.*2, n) %/ n.+1.

Definition Dyck_hsz n : {set n.*2.-tuple brace} :=
  [set w : n.*2.-tuple brace | tval w \is a Dyck_word].
Definition bal_hsz n : {set n.*2.-tuple brace} :=
  [set w : n.*2.-tuple brace | height w == 0].



Theorem card_bintreesz_dyck n : #|bintreesz n| = #|Dyck_hsz n|.
Proof.
have trdP (tr : bintreesz n) : size (Dyck_of_bintree tr) == n.*2.
  by rewrite size_Dyck_of_bintree bintreeszP.
pose trd (tr : bintreesz n) := Tuple (trdP tr).
rewrite -(card_imset (f := trd)); first last.
  move=> tr1 tr2 /(congr1 val) /= /val_inj /(congr1 (bintree_of_Dyck)).
  by rewrite !Dyck_of_bintreeK => /val_inj.
congr (#|pred_of_set _|).
apply/setP => /= S; rewrite inE; apply/imsetP/idP => /= [[tr Htr -> {S}] | HS].
- by rewrite /=; case: (Dyck_of_bintree _).
- pose tr := bintree_of_Dyck (DyckWord HS).
  have := size_bintree_of_Dyck (DyckWord HS).
  rewrite /= size_tuple => /double_inj/eqP sztr.
  exists (BinTreeSZ sztr); first by rewrite inE.
  by apply val_inj; rewrite /= bintree_of_DyckK.
Qed.

Lemma count_mem_height0 n (w : n.*2.-tuple brace) b :
  height w = 0 -> count_mem b w = n.
Proof.
move=> /eqP; rewrite /height subr_eq0 eqz_nat => /eqP Heq.
have:= size_count_braceE w.
rewrite size_tuple Heq addnn => /double_inj {-1}->.
by case b.
Qed.

Lemma card_bal_hsz n : #|bal_hsz n| = 'C(n.*2, n).
Proof.
have := card_draws [finType of 'I_(n.*2)] n; rewrite card_ord => <-.
have /card_imset <- : injective
    (fun w => [set r : 'I_(n.*2) | preim (tnth w) (pred1 }}) r]).
  move => u v Huv; apply: eq_from_tnth => i.
  move: Huv => /(congr1 (fun s => i \in pred_of_set s)); rewrite !inE.
  by case: (tnth u i) (tnth v i) => [] [].
congr #|pred_of_set _|; apply/setP => /= S.
rewrite inE; apply/imsetP/idP => /= [[w Hw -> {S}] | /eqP HS].
- move: Hw; rewrite inE => /eqP Hw; apply/eqP.
  rewrite -[RHS](count_mem_height0 }} Hw).
  rewrite -(@card_preim_nth n.*2 _ _ _ {{) ?size_tuple //.
  by congr (#|pred_of_set _|); apply/setP => /= i; rewrite /= !inE -tnth_nth.
- exists (mktuple (fun i => if i \in S then }} else {{)); first last.
    by apply/setP => /= i; rewrite inE tnth_mktuple /=; case: (i \in S).
  rewrite inE /height /=.
  do 2 rewrite -size_filter filter_map size_map.
  rewrite [X in (Posz (size X) - _)%R](eq_filter (a2 := mem (~: S))); first last.
    by move=> i; rewrite /= in_setC; case: (i \in S).
  rewrite [X in (_ - Posz (size X))%R](eq_filter (a2 := mem S)); first last.
    by move=> i /=; case: (i \in S).
  rewrite !enumT -/enum_mem -!cardE cardsCs.
  have -> :  ~: ~: S = S by apply/setP => i; rewrite !inE negbK.
  by rewrite HS card_ord -addnn addnK subrr.
Qed.


(** ** The rotation bijection *)
Section DyckWordRotationBijection.

Variable n : nat.
Implicit Types u v w D : n.*2.-tuple brace.

Lemma size_UnDn : size (nseq n {{ ++ nseq n }}) == n.*2.
Proof. by rewrite size_cat !size_nseq addnn. Qed.
Definition UnDn := Tuple size_UnDn.

Lemma UnDn_Dyck : tval UnDn \is a Dyck_word.
Proof.
apply/Dyck_wordP; rewrite height_take_leq; split => [i|].
- rewrite (eqP size_UnDn) take_cat !size_nseq => Hi2.
  case: leqP => [Hi | /ltnW Hi {Hi2}].
  + rewrite height_simpl take_nseq /=; last by rewrite leq_subLR addnn.
    by rewrite !height_nseq mulrN1 mulr1 subr_ge0 lez_nat leq_subLR addnn.
  + by rewrite take_nseq // height_nseq /= mulr1 lez_nat.
- by rewrite height_cat !height_nseq /= mulrN1 mulr1 subrr.
Qed.

Lemma size_UDn : size (flatten (nseq n [:: {{; }}])) == n.*2.
Proof. by elim: n. Qed.
Definition UDn := Tuple size_UDn.

Lemma UDn_Dyck : tval UDn \is a Dyck_word.
Proof.
rewrite /=; apply/Dyck_wordP; rewrite height_take_leq; split => [i|].
- rewrite (eqP size_UDn).
  elim: n i => //= m IHm [|[|i]] //.
  rewrite doubleS ltnS ltnS !height_simpl /= addrA subrr add0r.
  exact: IHm.
- by elim: n => //= m; rewrite !height_simpl /= addrA subrr add0r.
Qed.


Lemma size_Dyck_of_bal w :
  size (take (size w) (rot (pfminh (rcons w }})) (rcons w }}))) == n.*2.
Proof. by rewrite size_take size_rot size_rcons ltnS leqnn size_tuple. Qed.
Definition Dyck_of_bal w := Tuple (size_Dyck_of_bal w).

Lemma Dyck_of_balP w : height w = 0 -> tval (Dyck_of_bal w) \is a Dyck_word.
Proof.
rewrite /Dyck_of_bal /= => Hw.
rewrite -[size w]/(size w).+1.-1 -(size_rcons w }}).
by apply rot_is_Dyck; rewrite height_simpl /= Hw add0r.
Qed.

Lemma Dyck_of_Dyck_hsz D : tval D \is a Dyck_word -> Dyck_of_bal D = D.
Proof.
move => HD; apply val_inj => /=.
suff -> : pfminh (rcons D }}) = size (rcons D }}).
  by rewrite rot_size -cats1 take_size_cat.
apply/esym/pfminhE => //; rewrite take_size.
- rewrite height_take_leq => i.
  rewrite leq_eqVlt => /orP [/eqP -> {i} |]; first by rewrite take_size.
  rewrite size_rcons ltnS => Hi.
  rewrite -cats1 (takel_cat _ Hi) !height_simpl /=.
  move: HD => /Dyck_wordP [Hpos ->].
  rewrite addr0 add0r.
  apply: (le_trans _ (Hpos _)).
  by rewrite -oppr_ge0 opprK.
- move=> i; rewrite size_rcons ltnS => Hi.
  rewrite -cats1 (takel_cat _ Hi) !height_simpl /=.
  move: HD => /Dyck_wordP [Hpos ->].
  by rewrite addr0 add0r -subr_gt0 opprK ltz_addr1.
Qed.

Lemma size_bal_of_Dyck rt w :
  size (take (size w) (rotr rt (rcons w }}))) == n.*2.
Proof. by rewrite size_take size_rot size_rcons ltnS leqnn size_tuple. Qed.
Definition bal_of_Dyck rt w := Tuple (size_bal_of_Dyck rt w).

Lemma bal_of_DyckP rt w :
  (rt <= size w)%N ->
  nth {{ (rcons w }}) (size w - rt) = }} ->
  height w = 0 -> height (bal_of_Dyck rt w) = 0.
Proof.
case: w => [w _] /= Hsz H H0.
rewrite /rot take_cat size_drop size_rcons subKn; last exact: (leq_trans Hsz).
rewrite ltnNge Hsz !height_simpl /= take_take subSn // addrC.
have : (size w - rt < size (rcons w }}))%N by rewrite size_rcons ltnS leq_subr.
move=>/(take_nth {{)/(congr1 height); rewrite !height_simpl => /eqP.
rewrite H /= -subr_eq opprK => /eqP <-.
rewrite -addrA [(1 + _)%R]addrC addrA -height_cat cat_take_drop.
by rewrite height_simpl! /= subrK.
Qed.

Lemma rcons_bal_of_Dyck w k :
  (k <= size w)%N ->
  nth {{ (rcons w }}) (size w - k) = }} ->
  rcons (bal_of_Dyck k w) }} = rotr k (rcons w }}).
Proof.
move=> Hsz Hk; rewrite -cats1 -[RHS](cat_take_drop (size w)); congr (_ ++ _).
apply (eq_from_nth (x0 := {{)) => [|i].
  by rewrite size_drop /= size_rotr size_rcons subSn // subnn.
rewrite /= ltnS leqn0 => /eqP -> {i}.
rewrite [LHS]/= nth_drop addn0 /rotr/rot nth_cat.
rewrite !size_drop subKn; last by apply: (leq_trans Hsz); rewrite size_rcons.
rewrite ltnNge Hsz /= nth_take; last by rewrite size_rcons subSn.
by rewrite Hk.
Qed.

Lemma bal_of_DyckK D rt :
  (rt <= size D)%N ->
  nth {{ (rcons D }}) (size D - rt) = }} ->
  tval D \is a Dyck_word ->
  Dyck_of_bal (bal_of_Dyck rt D) = D.
Proof.
move => Hsz Hnth Hw; apply val_inj; apply (@rconsK _ }} }}) => /=.
set bD := take (size D) _.
have -> : size bD = (size (rcons bD }})).-1 by rewrite size_rcons.
rewrite (@rot_pfminhE (rcons bD }})); first last.
  rewrite /bD height_simpl /=.
  move: Hw => /Dyck_wordP [_] /(bal_of_DyckP Hsz Hnth) /= ->.
  by rewrite add0r.
have {bD Hnth} -> : rcons bD }} = rotr rt (rcons D }}).
  rewrite {}/bD /rotr/rot take_cat size_drop subKn; first last.
    by rewrite size_rcons; apply: (leq_trans Hsz).
  rewrite ltnNge Hsz /= rcons_cat; congr (_ ++ _).
  rewrite size_rcons take_take ?subSn //.
  by rewrite (take_nth {{) ?size_rcons ?ltnS ?leq_subr // Hnth.
case: rt Hsz => [_ | rt Hsz].
  rewrite /rotr subn0 rot_size -{1}(rot0 (rcons D }})) pfminh_rrw //.
  by rewrite subn0 -(size_rcons D }}) rot_size.
rewrite pfminh_rrw // size_rcons; last by rewrite subSS leq_subr.
rewrite subKn; last exact: (leq_trans Hsz).
by rewrite rotrK.
Qed.

Lemma Dyck_of_balK w :
  height w = 0 -> w = bal_of_Dyck (pfminh (rcons w }})) (Dyck_of_bal w).
Proof.
move=> Hbal; apply val_inj => /=.
have -> : size w = (size (rcons w }})).-1 by rewrite size_rcons.
rewrite (@rot_pfminhE (rcons w }})); last by rewrite height_simpl /= Hbal add0r.
rewrite rotK size_take size_rot size_rcons /= ltnSn.
by rewrite -cats1 take_size_cat.
Qed.

Lemma preim_Dyck_of_balE D :
  tval D \is a Dyck_word ->
  (bal_hsz n) :&: (Dyck_of_bal @^-1: [set D]) =
  [ set bal_of_Dyck (nat_of_ord rt) D |
    rt : 'I_((size D).+1) & nth {{ (rcons D }}) (size D - rt) == }} ].
Proof.
move=> HD; apply/setP => /= u; rewrite !inE.
apply/andP/imsetP => /= [[/eqP ubal /eqP Huw] | [v /=]].
- have := Dyck_of_balK ubal; rewrite Huw => ->.
  have := pfminh_size (rcons u }}).
  rewrite size_rcons size_tuple -{2}(size_tuple D).
  rewrite leq_eqVlt => /orP [/eqP ->| Hpfminh].
  + exists (Ordinal (ltn0Sn (size D))).
    * by rewrite inE /= subn0 nth_rcons ltnn eq_refl.
    * apply val_inj => /=.
      by rewrite -(size_rcons D }}) /rotr subnn subn0 rot0 rot_size.
  + exists (Ordinal (Hpfminh)); last by [].
    rewrite inE /=.
    have := Dyck_of_balK ubal; rewrite Huw.
    move=> /(congr1 val)/=; rewrite /rotr/rot.
    rewrite take_cat size_drop subKn ?size_rcons //; last exact: ltnW.
    rewrite ltnNge -ltnS Hpfminh /= take_take ?subSn //.
    move/(congr1 height)/esym; rewrite ubal height_simpl height_drop.
    rewrite (take_nth {{) ?size_rcons ?ltnS ?leq_subr //.
    rewrite !height_simpl /= opprD [(- _ + _)%R]addrC.
    move: (height (take _ _)) => H; rewrite !addrA subrK {H}.
    move: HD => /Dyck_wordP [_ ->]; rewrite add0r.
    by case: (nth _ _ _).
- rewrite inE => /eqP Hnth -> {u}; split.
  + rewrite bal_of_DyckP //; first by case: v {Hnth}.
    by move: HD => /Dyck_wordP [].
  + by apply/eqP/bal_of_DyckK => //; case: v {Hnth}.
Qed.

Lemma card_preim_Dyck_of_bal D :
  tval D \is a Dyck_word ->
  #|(bal_hsz n) :&: (Dyck_of_bal @^-1: [set D])| = n.+1.
Proof.
move=> HD.
rewrite (preim_Dyck_of_balE HD).
rewrite card_in_imset; first last.
  move=> [i Hi] [j Hj]; rewrite !inE /= => /eqP Hnthi /eqP Hnthj Heq.
  wlog ilt : i j Hi Hj Hnthi Hnthj Heq / (i <= j)%N.
    move=> ileqj; case: (leqP i j); first exact: ileqj.
    by move=> /ltnW/ileqj ->.
  apply val_inj => /=; move: Hi Hj; rewrite !ltnS => Hi Hj.
  move: Heq => /(congr1 (fun x => rcons (val x) }})).
  rewrite !rcons_bal_of_Dyck // /rotr => /(congr1 pfminh).
  case: i Hi Hnthi ilt => [|i] //=; rewrite ?subn0.
  - move=> _ Hnth _; case: j Hj Hnthj => // j Hj Hnthj.
    rewrite rot_size -{1}(rot0 (rcons D }})).
    rewrite !pfminh_rrw //= size_rcons; last by rewrite subSS leq_subr.
    rewrite subn0 subKn ?ltnS; last exact: ltnW.
    by move=> [] Heq; move: Hj; rewrite Heq ltnn.
  - case: j Hj Hnthj => // j Hj Hnthj Hi Hnthi.
    rewrite ltnS => Hij.
    rewrite !pfminh_rrw //= size_rcons ?subSS ?leq_subr //.
    rewrite !subSn ?leq_subr //.
    by rewrite !subKn ?ltnS; try exact: ltnW.
rewrite -(card_imset _ rev_ord_inj).
have -> : n.+1 = count_mem }} (rcons D }}).
  rewrite count_rcons /= addn1 count_mem_height0 //.
  by move: HD => /Dyck_wordP [].
rewrite -(@card_preim_nth (size D).+1 _ _ _ {{); last by rewrite size_rcons.
congr (#|pred_of_set _|).
apply/setP => /= i; apply/imsetP/idP => /= [[j] |].
- rewrite inE => /eqP Hnthj -> {i} /=.
  by rewrite inE /= subSS Hnthj.
- rewrite inE => Hnth.
  exists (rev_ord i); last by rewrite rev_ordK.
  by rewrite inE /= subSS subKn // -ltnS.
Qed.

End DyckWordRotationBijection.

Arguments Dyck_of_bal {n}.
Arguments bal_of_Dyck {n}.

(** ** Main theorem for catalan numbers *)
Theorem card_bal_Dyck_hsz n : #|bal_hsz n| = #|Dyck_hsz n| * n.+1.
Proof.
have -> : #|Dyck_hsz n| = #|preim_partition Dyck_of_bal (bal_hsz n)|.
  rewrite card_preim_partition; congr #|pred_of_set _|.
  apply/setP => /= w; apply/idP/imsetP => /= [|[u Hu ->{w}]].
  - rewrite inE => HD.
    exists w; first by move: HD; rewrite !inE => /Dyck_wordP [_ ->].
    by rewrite Dyck_of_Dyck_hsz.
  - by move: Hu; rewrite !inE /= => /eqP/Dyck_of_balP.
apply: (card_uniform_partition _ (preim_partitionP Dyck_of_bal (bal_hsz n))).
move=> /= B HB.
have:= HB => /mem_preim_partition [/= w [Hw Heq]].
have {HB Hw} : w \in (bal_hsz n).
  have /and3P [/eqP Hcov _ _] := preim_partitionP Dyck_of_bal (bal_hsz n).
  by rewrite -Hcov; apply/bigcupP; exists B.
rewrite inE => /eqP Hw.
move: (Dyck_of_bal w) Heq (Dyck_of_balP Hw) => D Heq HD {w Hw}.
by subst B; rewrite (card_preim_Dyck_of_bal HD).
Qed.

Lemma div_central_binomial n : n.+1 %| 'C(n.*2, n).
Proof.
by apply/dvdnP; exists #|Dyck_hsz n|; rewrite -card_bal_Dyck_hsz card_bal_hsz.
Qed.

Theorem card_Dyck_hsz n : #|Dyck_hsz n| = Catalan n.
Proof. by rewrite /Catalan -card_bal_hsz card_bal_Dyck_hsz mulnK. Qed.

Theorem Catalan_binE n : Catalan_bin n = Catalan n.
Proof. by rewrite -card_bintreesz card_bintreesz_dyck card_Dyck_hsz. Qed.
