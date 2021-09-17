(** * Combi.LRrule.freeSchur : Free Schur functions *)
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
(** * Free Schur functions

This file is the second step of the proof of the Littewood-Richardson rule.
We translate theorem [LRtriple_cat_equiv] in a algebraic setting. Specifically,
the main goal of this file is to lift the multiplication of Schur multivariate
polynomials to the non commutative setting.

- [commword n R w] == the commutative image of the word [w] as a multivariate
                      polynomial (of type [{mpoly R[n]}]).
- [homlang n d] == the type of homogenous langage over ['I_n.+1] of degre [d].
                      that is [{set d.-tuple 'I_n}].
- [polylang n R s] == the commutative image of the langage [s] where s is of
                      type [homlang n d].
- [catlang l1 l2] == the concatenation of homogeneous language: given
                      [s1] of degree [d1] and [s2] of degree [d2] return an
                      homogeneous language of degree [d1 + d2].
- [tabwordshape n sh] == the set of reading of tableaux over ['I_n.+1] of
                      shape [sh], where [sh] is of type ['P_d]
- [freeSchur n t] == the set of words whose recording tableau over ['I_n.+1]
                      is [t], where [t] is of type [stdtabn]
- [tabword_of_tuple w] == the bijection freeSchur -> tabwordshape as stated
                      in Theorem [tabword_of_tuple_freeSchur]:

  [
    forall Q : stdtabn d,
      [set tabword_of_tuple x | x in freeSchur n0 Q] = tabwordshape n0 (shape_deg Q)
  ]

The free Littlewood-Richardson rule:

- [LRsupport Q1 Q2] == the set of standard Littlewood-Richardson Q-tableau in
                      the product of the free Schur function indexed by [Q1]
                      and [Q2], that is the set of [Q] which forms a [LRtriple]
                      with [Q1] and [Q2].

The main result here is the free LR rule [free_LR_rule]:

  [
      catlang (freeSchur Q1) (freeSchur Q2) = \bigcup_(Q in LRsupport) freeSchur Q.
  ]

We then go back to commutative Schur polynomials:

- [hyper_stdtab sh] == the hyper standard tableau of shape sh as a [seq (seq nat)].
- [hyper_stdtabn sh] == the hyper standard tableau of shape sh as a
                         [stdtabn d] where sh is a ['P_d].
- [LRtab_set Q1 Q2 Q] == the set of standard Littlewood-Richardson Q-tableau in
                      the product of the free Schur function indexed by [Q1]
                      and [Q2] of shape [Q].
- [LRtab_coeff Q1 Q2] == the Littlewood-Richardson coefficient defined
                      as the cardinality of [LRtab_set Q1 Q2 Q].

Invariance with the choice of Q1 and Q2:

- [bij_LRsupport Q1 Q2] == a bijection from [LRsupport T1 T2] to [LRsupport Q1 Q2]
                      as long as [T1] and [Q1] have the same shape as well as
                      [T2] and [Q2]. It is used to show Theorem
                      [LRtab_coeff_shapeE]:

  [
      shape T1 = P1 -> shape T2 = P2 ->
       LRtab_coeff P = #|[set Q in (LRsupport T1 T2) | (shape Q == P)]|.
  ]

****************************************************************************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import order tuple finfun bigop finset ssralg.
From SsrMultinomials Require Import ssrcomplements freeg mpoly.

Require Import tools ordtype partition Yamanouchi std tableau stdtab.
Require Import Schensted congr plactic stdplact Yam_plact Greene_inv shuffle.
Require Import Schur_mpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.
Local Open Scope ring_scope.
Import GRing.Theory.


(** * Commutative image of an homogeneous langage *)
Section CommutativeImage.

Variable n : nat.
Variable R : comRingType.

Definition commword (w : seq 'I_n) : {mpoly R[n]} := \prod_(i <- w) 'X_i.

Lemma perm_commword (u v : seq 'I_n) :
  perm_eq u v -> commword u = commword v.
Proof using . exact: perm_big. Qed.

Lemma commword_morph (u v : seq 'I_n) :
  commword (u ++ v) = (commword u) * (commword v).
Proof using . by rewrite /commword big_cat. Qed.

Lemma commtuple_morph d1 d2 (u : d1.-tuple 'I_n) (v : d2.-tuple 'I_n) :
  commword (cat_tuple u v) = (commword u) * (commword v).
Proof using . by rewrite commword_morph. Qed.

Definition homlang d := {set d.-tuple 'I_n}.
Definition polylang d (s : homlang d) := \sum_(w in s) commword w.
Definition catlang d1 d2 (s1 : homlang d1) (s2 : homlang d2) :
  homlang (d1 + d2) :=
 [set cat_tuple w1 w2 | w1 in s1, w2 in s2].

Lemma cat_tuple_inj d1 d2 (u x : d1.-tuple 'I_n) (v y : d2.-tuple 'I_n) :
  cat_tuple u v = cat_tuple x y -> (u, v) = (x, y).
Proof using .
rewrite /cat_tuple => [] [/eqP].
rewrite eqseq_cat; last by rewrite !size_tuple.
by move=> /andP [/eqP/val_inj -> /eqP/val_inj ->].
Qed.

Lemma catlangM d1 d2 (s1 : homlang d1) (s2 : homlang d2) :
  polylang s1 * polylang s2 = polylang (catlang s1 s2).
Proof using .
rewrite /polylang /catlang mulr_suml.
under eq_bigr do [rewrite mulr_sumr; under eq_bigr do rewrite -commword_morph].
rewrite pair_big /=.
rewrite -(big_imset (h := fun p => cat_tuple p.1 p.2) commword) /=;
  last by move=> [u v] [x y] /= _ _; apply: cat_tuple_inj.
apply: eq_bigl => w.
apply/idP/idP.
- move/imsetP => [] [u v] /=; rewrite unfold_in /= => /andP [Hu Hv] ->.
  exact: imset2_f.
- move/imset2P => [u v Hu Hv -> {w}].
  by apply/imsetP; exists (u, v) => //=; rewrite unfold_in /= Hu Hv.
Qed.

End CommutativeImage.


(** ** Row reading of tableau *)
Section TableauReading.

Context {disp : unit} {A : inhOrderType disp}.

Definition tabsh_reading_RS (sh : seq nat) (w : seq A) :=
  (to_word (RS w) == w) && (shape (RS (w)) == sh).

Lemma tabsh_reading_RSP (sh : seq nat) (w : seq A) :
  reflect
    (exists tab, [/\ is_tableau tab, shape tab = sh & to_word tab = w])
    (tabsh_reading_RS sh w).
Proof using .
apply (iffP idP).
- move=> /andP [/eqP HRS /eqP Hsh].
  exists (RS w); split => //; exact: is_tableau_RS.
- move=> [tab] [Htab Hsh Hw]; apply/andP.
  have:= RS_tabE Htab; rewrite Hw => ->.
  by rewrite Hw Hsh.
Qed.

Lemma tabsh_reading_RSE sh :
  tabsh_reading sh =1 tabsh_reading_RS sh.
Proof using .
move=> w.
apply/idP/idP.
- by move /tabsh_readingP/tabsh_reading_RSP.
- by move /tabsh_reading_RSP/tabsh_readingP.
Qed.

End TableauReading.


(** * Free Schur function : lifting Schur function is the free algebra *)
Section FreeSchur.

Variable R : comRingType.

Variable n0 : nat.
Local Notation n := (n0.+1).
Local Notation Schur sh := (Schur n0 R sh).
Local Notation homlang d := (homlang n d).

Section Degree.

Variable d : nat.

(* set of tableaux words on 'I_n of a given shape *)
Definition tabwordshape (sh : 'P_d) : homlang d :=
  [set t : d.-tuple 'I_n | tabsh_reading sh t ].
(* set of tableaux words on 'I_n of a given Q-symbol *)
Definition freeSchur (Q : stdtabn d) : homlang d  :=
  [set t : d.-tuple 'I_n | (RStabmap t).2 == Q].

Lemma freeSchurP Q (t : d.-tuple 'I_n) :
  t \in freeSchur Q = (val t \in langQ Q).
Proof using . by rewrite /freeSchur /langQ !inE /=. Qed.

Lemma size_RS_tuple (t : d.-tuple 'I_n) : size (to_word (RS t)) == d.
Proof using . by rewrite size_to_word -{2}(size_tuple t) size_RS. Qed.

(**  Bijection freeSchur -> tabwordshape *)
Definition tabword_of_tuple (t : d.-tuple 'I_n) : d.-tuple 'I_n :=
  Tuple (size_RS_tuple t).

Lemma perm_tabword_of_tuple (t : d.-tuple 'I_n) :
  perm_eq t (tabword_of_tuple t).
Proof using . rewrite /tabword_of_tuple /=; exact: perm_RS. Qed.

Lemma tabword_of_tuple_freeSchur_inj (Q : stdtabn d) :
  {in (freeSchur Q) &, injective tabword_of_tuple}.
Proof using .
move=> /= u v.
rewrite /freeSchur !inE => /eqP Hu /eqP Hv /(congr1 (@tval _ _)) /= H.
case: (bijRStab [inhOrderType of 'I_n]) => RSinv HK _.
apply: val_inj; rewrite -[val u]HK -[val v]HK; congr (RSinv _).
rewrite {RSinv HK} /RStab /=. apply: pqpair_inj => /=.
have:= (is_tableau_RS u). have:= is_tableau_RS v.
move: Hu Hv H; rewrite -!RStabmapE /RStabmap.
case: RSmap => [pu qu] /= ->; case: RSmap => [pv qv] /= -> Heq Hv Hu.
by rewrite -(RS_tabE Hu) -(RS_tabE Hv) Heq.
Qed.

Lemma tabword_of_tuple_freeSchur (Q : stdtabn d) :
  [set tabword_of_tuple x | x in freeSchur Q] = tabwordshape (shape_deg Q).
Proof using .
rewrite /freeSchur /tabwordshape /tabword_of_tuple.
apply/setP/subset_eqP/andP; split; apply/subsetP => w;
    rewrite !inE tabsh_reading_RSE /tabsh_reading_RS.
- move/imsetP => [t]; rewrite inE => /eqP HQ /(congr1 val) /= ->.
  rewrite (RS_tabE (is_tableau_RS t)) eq_refl /= {w}.
  by rewrite -HQ -!RStabmapE shape_RStabmapE.
- move/andP => [/eqP Hw /eqP Hsh]; apply/imsetP.
  have Hpair : is_RStabpair (RS w, val Q).
    by rewrite /is_RStabpair is_tableau_RS stdtabnP Hsh eq_refl.
  have Hpr : is_RSpair (RS w, yam_of_stdtab Q).
    have:= Hpair; rewrite /is_RStabpair /= => /andP [-> /=].
    move=> /andP [/yam_of_stdtabP -> /= /eqP ->].
    by rewrite shape_yam_of_stdtab.
  pose imw := (RStabinv (RSTabPair Hpair)).
  have Hsz : size (imw) == d.
    rewrite /imw /RStabinv /= -size_RS -RSmapE.
    rewrite (RSmapinv2K Hpr) /=.
    by rewrite size_RS size_tuple.
  exists (Tuple Hsz).
  + rewrite inE /= /imw.
    by have/(congr1 val) := RStabinvK (RSTabPair Hpair) => /= ->.
  + apply: val_inj => /=.
    rewrite /imw /RStabinv /= -Hw /=; congr (to_word _).
    by rewrite Hw -[RS (RSmapinv _ _)]RSmapE RSmapinv2K.
Qed.

End Degree.

(** ** Noncommutative lifting of Schur polynomials *)
Lemma SchurE d (Q : stdtabn d) :
  Schur (shape_deg Q) = polylang R (tabwordshape (shape_deg Q)).
Proof using .
rewrite Schur_tabsh_readingE /polylang /commword; apply eq_bigl => i /=.
by rewrite inE.
Qed.

(** ** Commutative image of freeSchur language *)
Lemma Schur_freeSchurE d (Q : stdtabn d) :
  Schur (shape_deg Q) = polylang R (freeSchur Q).
Proof using .
rewrite SchurE -tabword_of_tuple_freeSchur.
rewrite /polylang (big_imset _ (@tabword_of_tuple_freeSchur_inj _ Q)) /=.
apply: eq_bigr => t _; apply: perm_commword.
by rewrite perm_sym; exact: perm_RS.
Qed.


(** * The free Littlewood-Richardson rule *)
Section FreeLRrule.

Variables (d1 d2 : nat).
Variables (Q1 : stdtabn d1) (Q2 : stdtabn d2).

Definition LRsupport :=
  [set Q : stdtabn (d1 + d2) | pred_LRtriple_fast Q1 Q2 Q ].

Lemma free_LR_rule :
  catlang (freeSchur Q1) (freeSchur Q2) = \bigcup_(Q in LRsupport) freeSchur Q.
Proof using .
rewrite /catlang.
apply/setP/subset_eqP/andP; split; apply/subsetP=> t.
- move/imset2P => [w1 w2].
  rewrite !freeSchurP /= => Hw1 Hw2 ->.
  have:= conj Hw1 Hw2.
  rewrite LRtriple_cat_equiv // => [[H1 H2] [Q [Htriple /= Hcat]]].
  have:= is_stdtab_of_n_LRtriple (stdtabnP Q1) (stdtabnP Q2) Htriple.
  rewrite !size_tab_stdtabn => HQ.
  apply/bigcupP; exists (StdtabN HQ).
    rewrite /LRsupport inE -LRtriple_fastE //.
    apply/LRtripleP => //; exact: Htriple.
  by rewrite freeSchurP.
- move/bigcupP => [Q]; rewrite /LRsupport freeSchurP inE => Htriple /= Ht.
  have Hsz1 : size (take d1 t) == d1.
    by rewrite size_takel // size_tuple leq_addr.
  pose t1 := Tuple Hsz1.
  have Hsz2 : size (drop d1 t) == d2.
    by rewrite size_drop size_tuple addKn.
  pose t2 := Tuple Hsz2.
  have Hcat : t = cat_tuple t1 t2.
    by apply: val_inj => /=; rewrite cat_take_drop.
  have : val t1 \in langQ Q1 /\ val t2 \in langQ Q2.
    rewrite LRtriple_cat_equiv // !size_tuple !size_tab_stdtabn //.
    split; try by [].
    exists Q; split.
    + by apply/LRtripleP => //; rewrite LRtriple_fastE.
    + by rewrite /= cat_take_drop.
  move=> [/= Ht1 Ht2].
  apply/imset2P; apply: (Imset2spec (x1 := t1) (x2 := t2)).
  + by rewrite freeSchurP.
  + by rewrite freeSchurP.
  + by apply: val_inj; rewrite /= cat_take_drop.
Qed.

(** Alternative proof from [LRrule_langQ] *)
Lemma free_LR_rule_alternate :
  catlang (freeSchur Q1) (freeSchur Q2) = \bigcup_(Q in LRsupport) freeSchur Q.
Proof using .
rewrite /catlang.
apply/setP/subset_eqP/andP; split; apply/subsetP=> /= t.
- move/imset2P => [/= w1 w2].
  rewrite !freeSchurP /= => Hw1 Hw2 ->.
  have : exists u v, [/\ w1 ++ w2  = u ++ v, u \in langQ Q1 & v \in langQ Q2].
    by exists w1, w2.
  rewrite LRrule_langQ // => [] [w] [Htriple /= Hcat].
  have:= is_stdtab_of_n_LRtriple (stdtabnP Q1) (stdtabnP Q2) Htriple.
  rewrite !size_tab_stdtabn => HQ.
  apply/bigcupP; exists (StdtabN HQ).
    rewrite /LRsupport inE -LRtriple_fastE //.
    apply/LRtripleP => //; exact: Htriple.
  by rewrite freeSchurP.
- move/bigcupP => [/= Q]; rewrite /LRsupport freeSchurP inE -LRtriple_fastE //.
  move=> /(LRtripleP _ (stdtabnP Q1) (stdtabnP Q2)) Htriple /= Ht.
  have : exists Q, LRtriple Q1 Q2 Q /\ val t \in langQ Q by exists Q.
  rewrite -LRrule_langQ_alternate // => [] [/= u1] [/= u2] [Hcat Hu1 Hu2].
  have:= Hu1 => /size_langQ; rewrite size_tab_stdtabn => /eqP Hsz1.
  pose t1 := Tuple Hsz1.
  have:= Hu2 => /size_langQ; rewrite size_tab_stdtabn => /eqP Hsz2.
  pose t2 := Tuple Hsz2.
  apply/imset2P; apply: (Imset2spec (x1 := t1) (x2 := t2)).
  + by rewrite freeSchurP.
  + by rewrite freeSchurP.
  + exact: val_inj.
Qed.

(** Passing to commutative image in the free LR rule *)
Theorem LR_rule_tab :
  Schur (shape_deg Q1) * Schur (shape_deg Q2) =
    \sum_(Q in LRsupport) (Schur (shape_deg Q)).
Proof using .
rewrite !Schur_freeSchurE catlangM free_LR_rule.
rewrite -cover_imset /polylang.
rewrite big_trivIset /=; first last.
  apply/trivIsetP => S1 S2.
  move => /imsetP [/= T1]; rewrite inE => HT1 -> {S1}.
  move => /imsetP [/= T2]; rewrite inE => HT2 -> {S2}.
  rewrite /freeSchur => Hdiff.
  rewrite /disjoint; apply/pred0P => w /=.
  rewrite !inE; apply: negbTE; move: Hdiff; apply: contra.
  by move=> /andP [/eqP -> /eqP ->].
under [RHS]eq_bigr do rewrite Schur_freeSchurE.
rewrite (big_setID [set set0]) /= big1 ?add0r; first last => [i|].
  rewrite inE => /andP [_]; rewrite inE => /eqP ->.
  by rewrite big_set0.
rewrite (big_setID [set x | freeSchur x == set0]) /=.
rewrite [X in X + _]big1 ?add0r; first last => [i|].
  rewrite inE => /andP [_]; rewrite inE => /eqP ->.
  by rewrite /polylang big_set0.
rewrite -big_imset /=; first last => [T1 T2 /=|].
  rewrite inE => /andP []; rewrite inE => /set0Pn [x1 Hx1] _ _.
  move: Hx1; rewrite inE => /eqP Hx1 /setP/(_ x1); rewrite !inE Hx1.
  rewrite eq_refl => /esym/eqP; exact: val_inj.
apply: eq_bigl => s; rewrite !inE; apply/idP/idP.
+ move=> /andP [Hn0 /imsetP [Q HQ Hs]]; subst s.
  by rewrite imset_f //= inE HQ inE Hn0.
+ move/imsetP => [Q]; rewrite 2!inE => /andP [H1 H2] ->.
  by rewrite H1 /= imset_f.
Qed.

End FreeLRrule.


Definition hyper_stdtab sh := RS (std (hyper_yam sh)).
Lemma hyper_stdtabP sh : is_stdtab (hyper_stdtab sh).
Proof using . by rewrite /hyper_stdtab /= RSstdE std_is_std. Qed.

Lemma hyper_stdtabnP d (P : 'P_d) : is_stdtab_of_n d (hyper_stdtab P).
Proof using .
rewrite /is_stdtab_of_n /= hyper_stdtabP /= size_RS.
rewrite size_std -evalseq_eq_size (evalseq_hyper_yam (intpartnP P)).
by rewrite sumn_intpartn.
Qed.
Canonical hyper_stdtabn d (P : 'P_d) := StdtabN (hyper_stdtabnP P).

Lemma shape_hyper_stdtabnP d (P : 'P_d) : shape (hyper_stdtabn P) = P.
Proof using .
  rewrite shape_RS_std (shape_RS_yam (hyper_yamP (intpartnP P))).
  by rewrite (evalseq_hyper_yam (intpartnP P)).
Qed.
Lemma shaped_hyper_stdtabnP d (P : 'P_d) : shape_deg (hyper_stdtabn P) = P.
Proof using . apply: val_inj => /=; exact: shape_hyper_stdtabnP. Qed.


Section Coeffs.

Variables d1 d2 : nat.
Variables (P1 : 'P_d1) (P2 : 'P_d2).

Definition LRtab_set (P : 'P_(d1 + d2)) :=
  [set Q in (LRsupport (hyper_stdtabn P1) (hyper_stdtabn P2)) | (shape Q == P)].
Definition LRtab_coeff (P : 'P_(d1 + d2)) := #|LRtab_set P|.


Theorem LRtab_coeffP :
  Schur P1 * Schur P2 = \sum_P (Schur P) *+ LRtab_coeff P.
Proof using .
rewrite /LRtab_coeff /LRtab_set.
have:= LR_rule_tab (hyper_stdtabn P1) (hyper_stdtabn P2).
rewrite !shaped_hyper_stdtabnP => ->.
move : (LRsupport _ _) => LR.
rewrite (partition_big (@shape_deg (d1 + d2)) predT) //=.
apply: eq_bigr => P _.
under eq_bigr => T /andP [_ /eqP ->] do [].
rewrite sumr_const; congr (_ *+ _).
by apply: eq_card => i /=; rewrite unfold_in inE.
Qed.

Lemma size_RSmapinv2_yam d
      (disp : unit) (Typ : inhOrderType disp)
      (tab : seq (seq Typ)) (T : stdtabn d) :
  size (RSmapinv2 (tab, yam_of_stdtab T)) = d.
Proof using .
rewrite -{2}(size_tab_stdtabn T) -size_yam_of_stdtab // /RSmapinv2 /=.
elim: (yam_of_stdtab _) tab => [//= | w0 w /= IHw] tab.
case: (invinstabnrow _ _) => [tr lr].
by rewrite size_rcons IHw.
Qed.


(** ** Invariance with respect to choice of the Q-Tableau *)
Section Bij_LRsupport.

Section ChangeUT.

Variable (U1 T1 : stdtabn d1) (U2 T2 : stdtabn d2).
Hypothesis Hsh1 : shape U1 = shape T1.
Hypothesis Hsh2 : shape U2 = shape T2.

Section TakeDrop.

Context {disp : unit} {T : inhOrderType disp}.

Lemma RStabE (w : seq T) : (RStab w).1 = (RS w).
Proof using . by rewrite RStabmapE. Qed.

Definition changeUT T1 T2 (w : seq T) : seq T :=
  (RSmapinv2 (RS (take d1 w), yam_of_stdtab T1)) ++
  (RSmapinv2 (RS (drop d1 w), yam_of_stdtab T2)).

Variable w : seq T.
Hypothesis Htake : shape (RS (take d1 w)) = shape U1.
Hypothesis Hdrop : shape (RS (drop d1 w)) = shape U2.

Lemma changeUtakeP : is_RStabpair (RS (take d1 w), val U1).
Proof using Htake.
by rewrite /is_RStabpair is_tableau_RS Htake /= eq_refl andbT.
Qed.
Lemma changeUdropP : is_RStabpair (RS (drop d1 w), val U2).
Proof using Hdrop.
by rewrite /is_RStabpair is_tableau_RS Hdrop /= eq_refl andbT.
Qed.
Lemma changeTtakeP : is_RStabpair (RS (take d1 w), val T1).
Proof using Hsh1 Htake.
by rewrite /is_RStabpair is_tableau_RS Htake /= Hsh1 eq_refl andbT.
Qed.
Lemma changeTdropP : is_RStabpair (RS (drop d1 w), val T2).
Proof using Hdrop Hsh2.
by rewrite /is_RStabpair is_tableau_RS Hdrop /= Hsh2 eq_refl andbT.
Qed.
Lemma toDepRSPair (u : seq T) d (t : stdtabn d) :
  forall H : is_RStabpair (RS u, val t),
  RSmapinv2 (RS u, yam_of_stdtab t) = RStabinv (RSTabPair H).
Proof using . by []. Qed.

Lemma plact_changeUT_take : take d1 (changeUT T1 T2 w) =Pl take d1 w.
Proof using Hsh1 Htake.
rewrite /changeUT take_size_cat; last by rewrite /= size_RSmapinv2_yam.
rewrite (toDepRSPair changeTtakeP).
apply Sch_plact; apply/eqP.
by rewrite -[LHS]RStabE RStabinvK //.
Qed.

Lemma plact_changeUT_drop : drop d1 (changeUT T1 T2 w) =Pl drop d1 w.
Proof using Hdrop Hsh2.
rewrite /changeUT drop_size_cat; last by rewrite /= size_RSmapinv2_yam.
rewrite (toDepRSPair changeTdropP).
apply Sch_plact; apply/eqP.
by rewrite -[LHS]RStabE RStabinvK //.
Qed.

Lemma plact_changeUT : changeUT T1 T2 w =Pl w.
Proof using Hdrop Hsh1 Hsh2 Htake.
rewrite /changeUT -{3}(cat_take_drop d1 w).
apply: plact_cat.
- have:= plact_changeUT_take.
  by rewrite /changeUT take_size_cat // size_RSmapinv2_yam.
- have:= plact_changeUT_drop.
  by rewrite /changeUT drop_size_cat // size_RSmapinv2_yam.
Qed.

End TakeDrop.

Lemma changeUTK (disp : unit) (T : inhOrderType disp) (w : seq T) :
  (take d1 w) \in langQ U1 ->
  (drop d1 w) \in langQ U2 ->
  changeUT U1 U2 (changeUT T1 T2 w) = w.
Proof using Hsh1 Hsh2.
rewrite !inE /= /changeUT => /eqP Htake /eqP Hdrop.
rewrite ?take_size_cat ?drop_size_cat ?size_RSmapinv2_yam //.
have Htk : shape (RS (take d1 w)) = shape U1.
  by rewrite -RStabmapE shape_RStabmapE Htake.
have Hdp : shape (RS (drop d1 w)) = shape U2.
  by rewrite -RStabmapE shape_RStabmapE Hdrop.
have -> : RS (RSmapinv2 (RS (take d1 w), yam_of_stdtab T1)) = RS (take d1 w).
  by rewrite (toDepRSPair (changeTtakeP _)) -RStabE RStabinvK /=.
have -> : RS (RSmapinv2 (RS (drop d1 w), yam_of_stdtab T2)) = RS (drop d1 w).
  by rewrite (toDepRSPair (changeTdropP _)) -RStabE RStabinvK /=.
rewrite -{3}(cat_take_drop d1 w); congr (_ ++ _).
- move: Htake; rewrite /RStabmap /= -!RSmapE.
  case H : (RSmap (take d1 w)) => [Pt Qt] <- /=.
  rewrite stdtab_of_yamK -/((Pt, Qt).2) -H; last exact: is_yam_RSmap2.
  by rewrite RSmapK.
- move: Hdrop; rewrite /RStabmap /= -!RSmapE.
  case H : (RSmap (drop d1 w)) => [Pt Qt] <- /=.
  rewrite stdtab_of_yamK -/((Pt, Qt).2) -H; last exact: is_yam_RSmap2.
  by rewrite RSmapK.
Qed.

Section DefBij.

Variable Q : stdtabn (d1 + d2).
Hypothesis HTriple : pred_LRtriple U1 U2 Q.
Let w := RSmapinv2 (yamtab (shape Q), yam_of_stdtab Q).

Lemma RSpairyamQ : is_RSpair (yamtab (shape Q), yam_of_stdtab Q).
Proof using .
rewrite /= yamtabP /=; last by apply: is_part_sht; exact: stdtabP.
by rewrite yam_of_stdtabP //= shape_yam_of_stdtab // shape_yamtab.
Qed.

Lemma bij_LRsupportP :
  is_stdtab_of_n (d1 + d2)
    (RStab (changeUT T1 T2 (RSmapinv2 (yamtab (shape Q), yam_of_stdtab Q)))).2.
Proof using .
rewrite /is_stdtab_of_n /=.
apply/andP; split; first exact: is_stdtab_RStabmap2.
rewrite /size_tab /= -shape_RStabmapE RStabmapE -/(size_tab _) size_RS size_cat.
by rewrite !size_RSmapinv2_yam.
Qed.
Definition bij_LRsupport := StdtabN bij_LRsupportP.

Lemma take_drop_langQ :
  ((take d1 w) \in langQ U1 /\ (drop d1 w) \in langQ U2).
Proof using HTriple.
have:= HTriple => /LRtripleP-/(_ (stdtabnP _) (stdtabnP _)) Htriple.
have Hszw : size w = (d1 + d2)%N by rewrite /w size_RSmapinv2_yam.
rewrite LRtriple_cat_equiv //; split.
- rewrite size_take size_tab_stdtabn Hszw.
  case: d2 => [| n]; first by rewrite addn0 ltnn.
  by rewrite addnS ltnS leq_addr.
- by rewrite size_drop size_tab_stdtabn Hszw addKn.
- exists (val Q); split; first exact: Htriple.
  rewrite cat_take_drop /w inE /= /RStabmap RSmapinv2K; last exact: RSpairyamQ.
  by rewrite yam_of_stdtabK.
Qed.

Lemma shape_bij_LRsupport : shape bij_LRsupport = shape Q.
Proof using HTriple Hsh1 Hsh2.
have:= take_drop_langQ; rewrite /= -shape_RStabmapE RStabmapE.
rewrite !inE => [] [/eqP HU1 /eqP HU2].
have -> : RS (changeUT T1 T2 w) = RS w.
  apply/eqP; rewrite -plactic_RS;
  by apply: plact_changeUT; rewrite -RStabmapE shape_RStabmapE ?HU1 ?HU2.
rewrite /w -RSmapE shape_RSmap_eq /w RSmapinv2K; last exact: RSpairyamQ.
by rewrite //= shape_yam_of_stdtab.
Qed.

Lemma shape_takeRS : shape (RS (take d1 w)) = shape U1.
Proof using HTriple.
have:= take_drop_langQ; rewrite -/w => /= [] [Htake _].
move: Htake; rewrite inE => /eqP <-.
by rewrite -RStabmapE shape_RStabmapE.
Qed.

Lemma shape_dropRS : shape (RS (drop d1 w)) = shape U2.
Proof using HTriple.
have:= take_drop_langQ; rewrite -/w => /= [] [_ Hdrop].
move: Hdrop; rewrite inE => /eqP <-.
by rewrite -RStabmapE shape_RStabmapE.
Qed.

Lemma predLR_bij_LRsupport : pred_LRtriple T1 T2 bij_LRsupport.
Proof using HTriple Hsh1 Hsh2.
apply/LRtripleP => //=.
have:= take_drop_langQ; rewrite -/w => /= [] [Htake Hdrop].
apply LRtriple_cat_langQ => //.
- have Hpair := changeTtakeP shape_takeRS.
  rewrite (toDepRSPair Hpair) inE.
  by have/(congr1 (fun p => (val p).2)) := RStabinvK (RSTabPair Hpair) => /= ->.
- have Hpair := changeTdropP shape_dropRS.
  rewrite (toDepRSPair Hpair) inE.
  by have/(congr1 (fun p => (val p).2)) := RStabinvK (RSTabPair Hpair) => /= ->.
Qed.

End DefBij.

Lemma card_LRtab_set_leq (P : seq nat) :
  #|[set Q in (LRsupport U1 U2) | (shape Q == P)]| <=
  #|[set Q in (LRsupport T1 T2) | (shape Q == P)]|.
Proof using Hsh1 Hsh2.
rewrite /LRsupport.
have Hsimpl A B C :
    [set Q in (LRsupport A B) | (shape Q == C)] =
    [set Q : stdtabn (d1 + d2) | pred_LRtriple A B Q & (shape Q == C)].
  apply/setP => Q; rewrite /LRsupport 2!inE [RHS]inE.
  by congr (_ && _); rewrite LRtriple_fastE.
rewrite !{}Hsimpl.
rewrite -(card_in_imset (f := bij_LRsupport)).
- apply subset_leqif_cards; apply/subsetP => Qres /imsetP [Q].
  rewrite inE => /andP [Hpred /eqP <-] -> {Qres}.
  rewrite inE; apply/andP; split.
  + exact: predLR_bij_LRsupport.
  + by rewrite shape_bij_LRsupport.
- move=> Q1 Q2; rewrite inE => /andP [HQ1 /eqP HshQ1].
  rewrite inE => /andP [HQ2 /eqP]; rewrite -HshQ1 {HshQ1} => Heqsh.
  move=>/(congr1 (@val _ _ _)); rewrite /=.
  set w1 := (X in changeUT _ _ X).
  set w2 := (X in _ = (RStab (changeUT _ _ X)).2) => Heq1.
  have : RS w1 = RS w2.
    rewrite -!RSmapE /w1 /w2 !RSmapinv2K; first last.
    + rewrite /is_RSpair yamtabP /=; last by apply: is_part_sht; exact: stdtabP.
      by rewrite yam_of_stdtabP //= shape_yamtab shape_yam_of_stdtab.
    + rewrite /is_RSpair yamtabP /=; last by apply: is_part_sht; exact: stdtabP.
      by rewrite yam_of_stdtabP //= shape_yamtab shape_yam_of_stdtab.
    + by rewrite /= Heqsh.
  have:= take_drop_langQ HQ1.
  have:= plact_changeUT (shape_takeRS HQ1) (shape_dropRS HQ1); rewrite -/w1.
  rewrite plactic_RS => /eqP <- [HQ1take HQ1drop].
  have:= take_drop_langQ HQ2.
  have:= plact_changeUT (shape_takeRS HQ2) (shape_dropRS HQ2); rewrite -/w2.
  rewrite plactic_RS => /eqP <- [HQ2take HQ2drop].
  rewrite -!RStabE => Heq2.
  have {Heq1 Heq2 HQ1take HQ1drop HQ2take HQ2drop} Heq : w1 = w2.
    rewrite -(changeUTK HQ1take HQ1drop) -(changeUTK HQ2take HQ2drop).
    congr changeUT.
    rewrite -(RStabK (changeUT T1 T2 w1)) -(RStabK (changeUT T1 T2 w2)).
    congr RStabinv.
    apply val_inj; move: Heq1 Heq2 => /=.
    case: (RStabmap (changeUT T1 T2 w1)) => A1 B1.
    by case: (RStabmap (changeUT T1 T2 w2)) => A2 B2 /= -> ->.
  apply val_inj.
  rewrite /= -(yam_of_stdtabK (stdtabnP Q1)) -(yam_of_stdtabK (stdtabnP Q2)).
  congr stdtab_of_yam.
  have:= RSmapinv2K (RSpairyamQ Q1); rewrite -/w1 Heq /w2.
  by rewrite (RSmapinv2K (RSpairyamQ Q2)) => [] [_ ->].
Qed.

End ChangeUT.

Lemma card_LRtab_set_shapeE P (U1 T1 : stdtabn d1) (U2 T2 : stdtabn d2) :
  shape T1 = shape U1 -> shape T2 = shape U2 ->
  #|[set Q in (LRsupport U1 U2) | (shape Q == P)]| =
  #|[set Q in (LRsupport T1 T2) | (shape Q == P)]|.
Proof using .
by move=> H1 H2; apply anti_leq; rewrite !card_LRtab_set_leq // H1 H2.
Qed.

Theorem LRtab_coeff_shapeE (T1 : stdtabn d1) (T2 : stdtabn d2) P :
  shape T1 = P1 -> shape T2 = P2 ->
  LRtab_coeff P = #|[set Q in (LRsupport T1 T2) | (shape Q == P)]|.
Proof using .
rewrite /LRtab_coeff /LRtab_set => H1 H2.
by apply card_LRtab_set_shapeE; rewrite shape_hyper_stdtabnP ?H1 ?H2.
Qed.

End Bij_LRsupport.

End Coeffs.

End FreeSchur.

(** ** Conjugating tableaux in the free LR rule *)
Section Conj.

Variables d1 d2 : nat.

Lemma LRsupport_conj (T1 : stdtabn d1) (T2 : stdtabn d2):
  LRsupport (conj_stdtabn T1) (conj_stdtabn T2) =
            (@conj_stdtabn _) @: (LRsupport T1 T2).
Proof using .
apply/setP => T; rewrite inE.
apply/idP/idP.
- rewrite -LRtriple_fastE; try exact: is_stdtab_conj => //; last exact: stdtabnP.
  move=> H.
  apply/imsetP; exists (conj_stdtabn T).
  + rewrite inE -LRtriple_fastE //.
    rewrite pred_LRtriple_conj // conj_tabK; first exact H.
    * exact: stdtabP.
    * apply val_inj; rewrite /= conj_tabK //; exact: stdtabP.
- move=> /imsetP [U]; rewrite inE -LRtriple_fastE //.
  rewrite pred_LRtriple_conj // => H -> {T}.
  rewrite -LRtriple_fastE; try exact: is_stdtab_conj.
  exact: H.
Qed.

Theorem LRtab_coeff_conj (P1 : 'P_d1) (P2 : 'P_d2) (P : 'P_(d1 + d2)) :
  LRtab_coeff P1 P2 P =
  LRtab_coeff (conj_intpartn P1) (conj_intpartn P2) (conj_intpartn P).
Proof using .
rewrite [RHS](LRtab_coeff_shapeE
                (T1 := conj_stdtabn (hyper_stdtabn P1))
                (T2 := conj_stdtabn (hyper_stdtabn P2))); first last.
  - by rewrite shape_conj_tab shape_hyper_stdtabnP.
  - by rewrite shape_conj_tab shape_hyper_stdtabnP.
rewrite /LRtab_coeff /LRtab_set LRsupport_conj.
have Hinj : injective (conj_stdtabn (n:=d1 + d2)).
  apply inv_inj => T; apply val_inj; rewrite /= conj_tabK //; exact: stdtabP.
rewrite -(@card_imset _ _ (@conj_stdtabn _)) //.
rewrite !setIdE imsetI; last by move=> a b /= _ _; exact: Hinj.
congr (card (mem (_ :&: _))).
apply/setP => T; rewrite !inE.
apply/idP/idP.
- move/imsetP => [U]; rewrite inE => /eqP HU -> /=.
  by rewrite shape_conj_tab HU.
- move/eqP => H; apply/imsetP; exists (conj_stdtabn T).
  + by rewrite inE /= shape_conj_tab H /= conj_partK.
  + apply val_inj => //=; rewrite conj_tabK //; exact: stdtabP.
Qed.

End Conj.
