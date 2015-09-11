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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import tuple finfun finset bigop ssralg.
Require Import poly.

Require Import tools ordtype partition Yamanouchi std stdtab.
Require Import Schensted stdplact Yam_plact Greene_inv shuffle.

(******************************************************************************)
(* The main goal of this file is to lift the multiplication of multivariate   *)
(* polynomials to the non commutative setting.                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'mpoly' T [ n ] }"
  (at level 0, T, n at level 2, format "{ 'mpoly'  T [ n ] }").
Reserved Notation "''X_' i"
  (at level 8, i at level 2, format "''X_' i").

Local Open Scope ring_scope.
Import GRing.Theory.

Section MPoly.

Variable R : comRingType.

Fixpoint multpoly n :=
  if n is n'.+1 then poly_comRingType (multpoly n') else R.

Fixpoint vari n : 'I_n -> multpoly n :=
  if n is n'.+1 then
    fun i : 'I_n'.+1 =>
      if unliftP ord0 i is UnliftSome j _ then (vari j)%:P
      else 'X
  else fun _ => 1.

End MPoly.

Notation "{ 'mpoly' T [ n ] }" := (multpoly T n).
Notation "'X_ i"        := (vari _ i).


Section Poly.

Variable R : comRingType.
Variable n : nat.

Definition commword (w : seq 'I_n) : {mpoly R[n]} := \prod_(i <- w) 'X_i.

Lemma perm_eq_commword (u v : seq 'I_n) : perm_eq u v -> commword u = commword v.
Proof. by apply: eq_big_perm. Qed.

Lemma commword_morph (u v : seq 'I_n) : commword (u ++ v) = (commword u) * (commword v).
Proof. by rewrite /commword big_cat. Qed.

Lemma commtuple_morph d1 d2 (u : d1.-tuple 'I_n) (v : d2.-tuple 'I_n) :
  commword (cat_tuple u v) = (commword u) * (commword v).
Proof. by rewrite commword_morph. Qed.

Definition polyset d (s : {set d.-tuple 'I_n}) := \sum_(w in s) commword w.

Definition catset d1 d2 (s1 : {set d1.-tuple 'I_n}) (s2 : {set d2.-tuple 'I_n})
           : {set (d1 + d2).-tuple 'I_n} :=
 [set cat_tuple w1 w2 | w1 in s1, w2 in s2].

Lemma cat_tuple_inj d1 d2 (u x : d1.-tuple 'I_n) (v y : d2.-tuple 'I_n) :
  cat_tuple u v = cat_tuple x y -> (u, v) = (x, y).
Proof.
  rewrite /cat_tuple => [] [] /eqP.
  rewrite eqseq_cat; last by rewrite !size_tuple.
  by move=> /andP [] /eqP/val_inj -> /eqP/val_inj ->.
Qed.

Lemma multcatset d1 d2 (s1 : {set d1.-tuple 'I_n}) (s2 : {set d2.-tuple 'I_n}) :
  polyset s1 * polyset s2 = polyset (catset s1 s2).
Proof.
  rewrite /polyset /catset mulr_suml.
  rewrite (@eq_bigr _ _ _ _ _ _ _ (fun u => \sum_(v in s2) commword (cat_tuple u v)));
    last by move=> u _; rewrite mulr_sumr; apply: eq_bigr => t _; by rewrite commword_morph.
  rewrite pair_big /=.
  rewrite (@eq_bigr _ _ _ _ _ _ _ (fun p => commword (cat_tuple p.1 p.2)));
    last by move=> [u v].
  rewrite -(@big_imset _ _ _ _ _ (fun p => cat_tuple p.1 p.2) _ commword) /=;
    last by move=> [u v] [x y] /= _ _; apply: cat_tuple_inj.
  apply: eq_bigl => w.
  apply/(sameP idP); apply(iffP idP).
  - move/imset2P => [] u v Hu Hv -> {w}.
    apply/imsetP; exists (u, v) => //=; by rewrite unfold_in /= Hu Hv.
  - move/imsetP => [] [u v] /=; rewrite unfold_in /= => /andP [] Hu Hv ->.
    by apply: mem_imset2.
Qed.

End Poly.


Section TableauReading.

Variable A : ordType.

Definition is_tableau_of_shape_reading (sh : seq nat) (w : seq A) :=
  (size w == sumn sh) && (is_tableau (rev (reshape (rev sh) w))).
Definition is_tableau_of_shape_reading_RS (sh : seq nat) (w : seq A) :=
  (to_word (RS w) == w) && (shape (RS (w)) == sh).

Lemma is_tableau_of_shape_readingP (sh : seq nat) (w : seq A) :
  reflect
    (exists tab, [/\ is_tableau tab, shape tab = sh & to_word tab = w])
    (is_tableau_of_shape_reading sh w).
Proof.
  apply (iffP idP).
  - move=> /andP [] /eqP Hsz Htab.
    exists (rev (reshape (rev sh) w)); split => //.
    rewrite shape_rev -{2}(revK sh); congr (rev _).
    apply: reshapeKl; by rewrite sumn_rev Hsz.
    rewrite /to_word revK; apply: reshapeKr; by rewrite sumn_rev Hsz.
  - move=> [] tab [] Htab Hsh Hw; apply/andP; split.
    + by rewrite -Hw -size_to_word /size_tab Hsh.
    + rewrite -Hw /to_word -Hsh.
      by rewrite /shape -map_rev -/(shape _) flattenK revK.
Qed.

Lemma is_tableau_of_shape_reading_RSP (sh : seq nat) (w : seq A) :
  reflect
    (exists tab, [/\ is_tableau tab, shape tab = sh & to_word tab = w])
    (is_tableau_of_shape_reading_RS sh w).
Proof.
  apply (iffP idP).
  - move=> /andP [] /eqP HRS /eqP Hsh.
    exists (RS w); split => //; by apply is_tableau_RS.
  - move=> [] tab [] Htab Hsh Hw; apply/andP.
    have:= RS_tabE Htab; rewrite Hw => ->.
    by rewrite Hw Hsh.
Qed.

Lemma is_tableau_of_shape_reading_RSE sh :
  is_tableau_of_shape_reading sh =1 is_tableau_of_shape_reading_RS sh.
Proof.
  move=> w.
  apply (sameP idP); apply (iffP idP).
  - by move /is_tableau_of_shape_reading_RSP/is_tableau_of_shape_readingP.
  - by move /is_tableau_of_shape_readingP/is_tableau_of_shape_reading_RSP.
Qed.

End TableauReading.


Section FinSets.

Variable n : nat.

Hypothesis Hnpos : n != 0%N.

Lemma inhabIn : 'I_n.
Proof. move: Hnpos; rewrite -lt0n; by apply: Ordinal. Qed.

Definition leqOrd (i j : 'I_n) := (i <= j)%N.

Fact leqOrd_order : Order.axiom leqOrd.
Proof.
  split.
  - move=> i; by apply: leqnn.
  - move=> i j; rewrite /leqOrd => H; apply: val_inj; by apply: anti_leq.
  - move=> a b c; by apply: leq_trans.
  - exact leq_total.
Qed.

Definition ord_ordMixin := Order.Mixin inhabIn leqOrd_order.
Canonical ord_ordType := Eval hnf in OrdType 'I_n ord_ordMixin.

Section Size.

Variable d : nat.

(* set of tableaux words on 'I_n of a given shape *)
Definition tabwordshape (sh : intpartn d) :=
  [set t : d.-tuple 'I_n | is_tableau_of_shape_reading sh t ].
(* set of tableaux words on 'I_n of a given Q-symbol *)
Definition freeSchur (Q : stdtabn d) :=
  [set t : d.-tuple 'I_n | (RStabmap t).2 == Q].


Lemma freeSchurP Q t : t \in freeSchur Q = (val t \in langQ Q).
Proof. by rewrite /freeSchur /langQ !inE /=. Qed.

Lemma size_RS_tuple (t : d.-tuple 'I_n) : size (to_word (RS t)) == d.
Proof. by rewrite -size_to_word-{2}(size_tuple t) size_RS. Qed.


(* Bijection freeSchur -> tabwordshape *)
Definition tabword_of_tuple (t : d.-tuple 'I_n) : d.-tuple 'I_n := Tuple (size_RS_tuple t).

Lemma perm_eq_tabword_of_tuple (t : d.-tuple 'I_n) : perm_eq t (tabword_of_tuple t).
Proof. rewrite /tabword_of_tuple /=; by apply: perm_eq_RS. Qed.

Lemma tabword_of_tuple_freeSchur_inj (Q : stdtabn d) :
  {in (freeSchur Q) &, injective tabword_of_tuple}.
Proof.
  move=> /= u v; rewrite /freeSchur !inE => /eqP Hu /eqP Hv H.
  have {H} /= H : tval (tabword_of_tuple u) = tval (tabword_of_tuple v) by rewrite H.
  case: (bijRStab ord_ordType) => RSinv HK _.
  apply: val_inj; rewrite -[val u]HK -[val v]HK; congr (RSinv _).
  rewrite {RSinv HK} /RStab /=. apply: pqpair_inj => /=.
  have := is_tableau_RS u; have := is_tableau_RS v.
  move: Hu Hv H; rewrite -!RStabmapE /RStabmap.
  case RSmap => [pu qu] {u} /= ->; case RSmap => [pv qv] {v} /= -> Heq Hv Hu.
  by rewrite -(RS_tabE Hu) -(RS_tabE Hv) Heq.
Qed.

Lemma sumn_shape_stdtabnE (Q : stdtabn d) : (sumn (shape Q)) = d.
Proof. case: Q => q; by rewrite /is_stdtab_of_n /= => /andP [] H /= /eqP. Qed.

Lemma is_part_shape_deg (Q : stdtabn d) : is_part_of_n d (shape Q).
Proof.
  rewrite /=; apply/andP; split.
  - by rewrite -{2}(stdtabn_size Q).
  - apply: is_part_sht.
    have := stdtabnP Q; by rewrite /is_stdtab => /andP [].
Qed.
Definition shape_deg (Q : stdtabn d) := (IntPartN (is_part_shape_deg Q)).

Lemma tabword_of_tuple_freeSchur (Q : stdtabn d) :
  [set tabword_of_tuple x | x in freeSchur Q] = tabwordshape (shape_deg Q).
Proof.
  rewrite /freeSchur /tabwordshape /tabword_of_tuple.
  apply/setP/subset_eqP/andP; split; apply/subsetP => w;
    rewrite !inE is_tableau_of_shape_reading_RSE /is_tableau_of_shape_reading_RS.
  - move/imsetP => [] t; rewrite inE => /eqP HQ Htmp.
    have /eqP := eq_refl (val w); rewrite {2}Htmp {Htmp} /= => Hw.
    rewrite Hw (RS_tabE (is_tableau_RS t)) eq_refl /= {w Hw}.
    by rewrite -HQ -!RStabmapE shape_RStabmapE.
  - move/andP => [] /eqP Hw /eqP Hsh; apply/imsetP.
    have Hpair : is_RStabpair ((RS w), val Q).
      by rewrite /is_RStabpair is_tableau_RS stdtabnP Hsh eq_refl.
    have Hpr : is_RSpair (RS w, yam_of_stdtab Q).
      have:= Hpair; rewrite /is_RStabpair /= => /andP [] -> /=.
      move=> /andP [] /yam_of_stdtabP -> /= /eqP ->.
      by rewrite shape_yam_of_stdtab.
    pose imw := (RStabinv (RSTabPair Hpair)).
    have Hsz : size (imw) == d.
      rewrite /imw /RStabinv /= -size_RS -RSmapE.
      rewrite (RSmapinv2K Hpr) /=.
      by rewrite size_RS size_tuple.
    exists (Tuple Hsz).
    + rewrite inE /= /imw.
      have := erefl (val (RSTabPair Hpair)).
      by rewrite -{2}(RStabinvK (RSTabPair Hpair)) /= => <-.
    + apply: val_inj => /=.
      rewrite /imw /RStabinv /= -Hw /=.
      congr (to_word _).
      by rewrite Hw -[RS (RSmapinv _ _)]RSmapE RSmapinv2K.
Qed.

End Size.

Variable R : comRingType.

Definition Schur d (sh : intpartn d) : {mpoly R[n]} := polyset R (tabwordshape sh).

Definition rowpart d := if d is _.+1 then [:: d] else [::].
Fact rowpartnP d : is_part_of_n d (rowpart d).
Proof. case: d => [//= | d]; by rewrite /is_part_of_n /= addn0 eq_refl. Qed.
Definition rowpartn d : intpartn d := IntPartN (rowpartnP d).
Definition complete d : {mpoly R[n]} := Schur (rowpartn d).

Definition colpart d := ncons d 1%N [::].
Fact colpartnP d : is_part_of_n d (colpart d).
Proof.
  elim: d => [| d ] //= /andP [] /eqP -> ->.
  rewrite add1n eq_refl andbT /=.
  by case: d.
Qed.
Definition colpartn d : intpartn d := IntPartN (colpartnP d).
Definition elementary d : {mpoly R[n]} := Schur (colpartn d).

(* Noncommutative lifting of Schur *)
Lemma Schur_freeSchurE d (Q : stdtabn d) :
  Schur (shape_deg Q) = polyset R (freeSchur Q).
Proof.
  rewrite /Schur -tabword_of_tuple_freeSchur.
  rewrite /polyset (big_imset _ (@tabword_of_tuple_freeSchur_inj _ Q)) /=.
  apply: eq_bigr => t _; apply: perm_eq_commword.
  rewrite perm_eq_sym; by apply: perm_eq_RS.
Qed.

Section SchurTab.

Variables (d1 d2 : nat).
Variables (Q1 : stdtabn d1) (Q2 : stdtabn d2).

Definition LR_support :=
  [set Q : stdtabn (d1 + d2) | predLRTripleFast Q1 Q2 Q ].

(* Noncommutative LR rule *)
Lemma free_LR_rule :
  catset (freeSchur Q1) (freeSchur Q2) = \bigcup_(Q in LR_support) freeSchur Q.
Proof.
  rewrite /catset.
  apply/setP/subset_eqP/andP; split; apply/subsetP=> t.
  - move/imset2P => [] w1 w2.
    rewrite !freeSchurP /= => Hw1 Hw2 ->.
    have := conj Hw1 Hw2.
    rewrite LRTriple_cat_equiv; try by apply: stdtabnP.
    move => [] H1 H2 [] Q [] Htriple /= Hcat.
    have := is_stdtab_of_n_LRTriple (stdtabnP Q1) (stdtabnP Q2) Htriple.
    rewrite !stdtabn_size => HQ.
    apply/bigcupP; exists (StdtabN HQ).
      rewrite /LR_support inE -LRTripleE; try apply: stdtabnP.
      apply/LRTripleP; try apply: stdtabnP.
      by apply: Htriple.
    by rewrite freeSchurP.
  - move/bigcupP => [] Q; rewrite /LR_support freeSchurP inE => Htriple /= Ht.
    have Hsz1 : size (take d1 t) == d1.
      rewrite size_take size_tuple.
      case: d2 => [| d2']; first by rewrite addn0 ltnn.
      by rewrite addnS ltnS leq_addr.
    pose t1 := Tuple Hsz1.
    have Hsz2 : size (drop d1 t) == d2.
      by rewrite size_drop size_tuple addKn.
    pose t2 := Tuple Hsz2.
    have Hcat : t = cat_tuple t1 t2.
      apply: val_inj => /=; by rewrite cat_take_drop.
    have : (val t1 \in langQ Q1 /\ val t2 \in langQ Q2).
      rewrite LRTriple_cat_equiv; try by apply: stdtabnP.
      rewrite !size_tuple !stdtabn_size; split; try by [].
      exists Q; split.
      + apply/LRTripleP; try apply: stdtabnP.
        by rewrite LRTripleE; try apply: stdtabnP.
      + by rewrite /= cat_take_drop.
    move=> [] /= Ht1 Ht2.
    apply/imset2P; apply: (Imset2spec (x1 := t1) (x2 := t2)).
    + by rewrite freeSchurP.
    + by rewrite freeSchurP.
    + apply: val_inj; by rewrite /= cat_take_drop.
Qed.

(* Commutative image of noncommutative LR rule *)
Theorem LR_rule_tab :
  Schur (shape_deg Q1) * Schur (shape_deg Q2) = \sum_(Q in LR_support) (Schur (shape_deg Q)).
Proof.
  rewrite !Schur_freeSchurE multcatset free_LR_rule.
  rewrite -cover_imset /polyset.
  rewrite big_trivIset /=; first last.
    apply/trivIsetP => S1 S2.
    move => /imsetP [] T1; rewrite inE => HT1 -> {S1}.
    move => /imsetP [] T2; rewrite inE => HT2 -> {S2}.
    rewrite /freeSchur => Hdiff.
    rewrite /disjoint; apply/pred0P => w /=.
    rewrite !inE; apply: negbTE; move: Hdiff; apply: contra.
    by move=> /andP [] /eqP -> /eqP ->.

  rewrite (@eq_bigr _ _ _ _ _ _ _ (fun Q => polyset R (freeSchur Q))) /=;
    last by move=> w _; apply: Schur_freeSchurE.

  rewrite (big_setID [set set0]) /=.
  set A := (X in X + _); have HA : A = 0.
    rewrite /A (eq_bigr (fun x => 0)).
    + rewrite big_const; elim: (card _) => [//=| i IHi] /=; by rewrite IHi add0r.
    + move=> i; rewrite inE => /andP [] _; rewrite inE => /eqP ->.
      by rewrite /polyset big_set0.
  rewrite HA add0r {A HA}.

  rewrite (big_setID [set x | freeSchur x == set0]) /=.
  set A := (X in X + _); have HA : A = 0.
    rewrite /A (eq_bigr (fun x => 0)).
    + rewrite big_const; elim: (card _) => [//=| i IHi] /=; by rewrite IHi add0r.
    + move=> i; rewrite inE => /andP [] _; rewrite inE => /eqP ->.
      by rewrite /polyset big_set0.
  rewrite HA add0r {A HA}.

  rewrite -big_imset /=; first last.
    move=> T1 T2 /=.
    rewrite inE => /andP []; rewrite inE => /set0Pn [] x1 Hx1 _ _.
    move: Hx1; rewrite /freeSchur inE => /eqP Hx1.
    rewrite -setP => H; have := H x1; rewrite !inE Hx1.
    rewrite eq_refl => /esym/eqP.
    move=> Htmp; apply: val_inj; by rewrite /= Htmp.
  rewrite /polyset.

  apply: eq_bigl => s; rewrite !inE.
  apply/(sameP idP); apply(iffP idP).
  + move/imsetP => [] Q; rewrite 2!inE => /andP [] H1 H2 ->.
    by rewrite H1 /= mem_imset.
  + move=> /andP [] Hn0 /imsetP [] Q HQ Hs; subst s.
    by rewrite mem_imset //= inE HQ inE Hn0.
Qed.

End SchurTab.

Definition hyper_tab sh := RS (std (hyper_yam sh)).
Lemma hyper_tabP sh : is_stdtab (hyper_tab sh).
Proof. by rewrite /hyper_tab /= RSstdE std_is_std. Qed.

Lemma hyper_stdtabP d (P : intpartn d) : is_stdtab_of_n d (hyper_tab P).
Proof.
  rewrite /is_stdtab_of_n /= hyper_tabP /= size_RS.
  rewrite size_std -evalseq_eq_size (evalseq_hyper_yam (intpartnP P)).
  by rewrite intpartn_sumn.
Qed.
Definition hyper_stdtab d (P : intpartn d) := StdtabN (hyper_stdtabP P).

Lemma shape_hyper_stdtabP d (P : intpartn d) : shape (hyper_stdtab P) = P.
Proof.
  rewrite shape_RS_std (shape_RS_yam (hyper_yamP (intpartnP P))).
  by rewrite (evalseq_hyper_yam (intpartnP P)).
Qed.
Lemma shaped_hyper_stdtabP d (P : intpartn d) : shape_deg (hyper_stdtab P) = P.
Proof. apply: val_inj => /=; exact: shape_hyper_stdtabP. Qed.

Section Coeffs.

Variables d1 d2 : nat.
Variables (P1 : intpartn d1) (P2 : intpartn d2).

Definition LRtab_set (P : intpartn (d1 + d2)) :=
  [set Q in (LR_support (hyper_stdtab P1) (hyper_stdtab P2)) | (shape Q == P)].
Definition LRtab_coeff (P : intpartn (d1 + d2)) := #|LRtab_set P|.


Theorem LRtab_coeffP :
  Schur P1 * Schur P2 = \sum_P (Schur P) *+ LRtab_coeff P.
Proof.
  rewrite /LRtab_coeff /LRtab_set.
  have := LR_rule_tab (hyper_stdtab P1) (hyper_stdtab P2).
  rewrite !shaped_hyper_stdtabP => ->.
  move : (LR_support _ _) => LR.
  rewrite (partition_big (@shape_deg (d1 + d2)) predT) //=.
  apply: eq_bigr => P _.
  rewrite (eq_bigr (fun i => (Schur P))); last by move=> T /andP [] _ /eqP ->.
  rewrite big_const.
  set c1 := card _; set c2 := card _.
  suff -> : c1 = c2 by elim: c2 => [//= | c IHc] /=; rewrite IHc mulrS.
  rewrite /c1 /c2 {c1 c2}.
  apply: eq_card => i /=.
  by rewrite unfold_in inE.
Qed.

Require Import plactic congr Yam_plact.

Lemma size_RSmapinv2_yam d (Typ : ordType) (tab : seq (seq Typ)) (T : stdtabn d) :
  size (RSmapinv2 (tab, yam_of_stdtab T)) = d.
Proof.
  rewrite -{2}(stdtabn_size T) -size_yam_of_stdtab // /RSmapinv2 /=.
  elim: (yam_of_stdtab _) tab => [//= | w0 w /= IHw] tab.
  case: (invinstabnrow _ _) => [tr lr].
  by rewrite size_rcons IHw.
Qed.


Section Bij_LR_support.

Section ChangeUT.

Variable (U1 T1 : stdtabn d1) (U2 T2 : stdtabn d2).
Hypothesis Hsh1 : shape U1 = shape T1.
Hypothesis Hsh2 : shape U2 = shape T2.

Section TakeDrop.

Variable T : ordType.

Lemma RStabE (w : seq T) : (RStab w).1 = (RS w).
Proof. by rewrite RStabmapE. Qed.

Definition changeUT T1 T2 (w : seq T) : seq T :=
  (RSmapinv2 (RS (take d1 w), yam_of_stdtab T1)) ++
  (RSmapinv2 (RS (drop d1 w), yam_of_stdtab T2)).

Variable w : seq T.
Hypothesis Htake : shape (RS (take d1 w)) = shape U1.
Hypothesis Hdrop : shape (RS (drop d1 w)) = shape U2.

Lemma changeUtakeP : is_RStabpair (RS (take d1 w), val U1).
Proof. by rewrite /is_RStabpair is_tableau_RS Htake /= eq_refl andbT. Qed.
Lemma changeUdropP : is_RStabpair (RS (drop d1 w), val U2).
Proof. by rewrite /is_RStabpair is_tableau_RS Hdrop /= eq_refl andbT. Qed.
Lemma changeTtakeP : is_RStabpair (RS (take d1 w), val T1).
Proof. by rewrite /is_RStabpair is_tableau_RS Htake /= Hsh1 eq_refl andbT. Qed.
Lemma changeTdropP : is_RStabpair (RS (drop d1 w), val T2).
Proof. by rewrite /is_RStabpair is_tableau_RS Hdrop /= Hsh2 eq_refl andbT. Qed.

Lemma toDepRSPair (u : seq T) d (t : stdtabn d) (H : is_RStabpair (RS u, val t)) :
  RSmapinv2 (RS u, yam_of_stdtab t) = RStabinv (RSTabPair H).
Proof. by []. Qed.

Lemma plact_changeUT_take : take d1 (changeUT T1 T2 w) =Pl take d1 w.
Proof.
  rewrite /changeUT take_size_cat; last by rewrite /= size_RSmapinv2_yam.
  rewrite (toDepRSPair changeTtakeP).
  apply Sch_plact; apply/eqP.
  by rewrite -[LHS]RStabE RStabinvK //.
Qed.

Lemma plact_changeUT_drop : drop d1 (changeUT T1 T2 w) =Pl drop d1 w.
Proof.
  rewrite /changeUT drop_size_cat; last by rewrite /= size_RSmapinv2_yam.
  rewrite (toDepRSPair changeTdropP).
  apply Sch_plact; apply/eqP.
  by rewrite -[LHS]RStabE RStabinvK //.
Qed.

Lemma plact_changeUT : changeUT T1 T2 w =Pl w.
Proof.
  rewrite /changeUT -{3}(cat_take_drop d1 w).
  apply: (@congr_cat _ _ (@plactcongr_is_congr _) (@plactcongr_equiv _)).
  - by have:= plact_changeUT_take; rewrite /changeUT take_size_cat // size_RSmapinv2_yam.
  - by have:= plact_changeUT_drop; rewrite /changeUT drop_size_cat // size_RSmapinv2_yam.
Qed.

End TakeDrop.

Lemma changeUTK (T : ordType) (w : seq T) :
  (take d1 w) \in langQ U1 ->
  (drop d1 w) \in langQ U2 ->
  changeUT U1 U2 (changeUT T1 T2 w) = w.
Proof.
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
Hypothesis HTriple : predLRTriple U1 U2 Q.
Let w := RSmapinv2 (yamtab (shape Q), yam_of_stdtab Q).

Lemma RSpairyamQ : is_RSpair (yamtab (shape Q), yam_of_stdtab Q).
Proof.
  rewrite /= yamtabP /=; last by apply: is_part_sht; exact: stdtabP.
  by rewrite yam_of_stdtabP //= shape_yam_of_stdtab // shape_yamtab.
Qed.

Definition fun_LR_support :=
  (RStab (changeUT T1 T2 (RSmapinv2 (yamtab (shape Q), yam_of_stdtab Q)))).2.

Lemma bij_LR_supportP : is_stdtab_of_n (d1 + d2) fun_LR_support.
Proof.
  rewrite /is_stdtab_of_n /= /fun_LR_support.
  apply/andP; split; first exact: is_stdtab_RStabmap2.
  rewrite /size_tab /= -shape_RStabmapE RStabmapE -/(size_tab _) size_RS size_cat.
  by rewrite !size_RSmapinv2_yam.
Qed.
Definition bij_LR_support := StdtabN bij_LR_supportP.

Lemma take_drop_langQ :
  ((take d1 w) \in langQ U1 /\ (drop d1 w) \in langQ U2).
Proof.
  have:= HTriple => /LRTripleP Htriple.
  have {Htriple} Htriple:= (Htriple (stdtabnP _) (stdtabnP _)).
  have Hszw : size w = (d1 + d2)%N by rewrite /w size_RSmapinv2_yam.
  rewrite LRTriple_cat_equiv //; split.
  - rewrite size_take stdtabn_size Hszw bad_if_leq //; exact: leq_addr.
  - by rewrite size_drop stdtabn_size Hszw addKn.
  - exists (val Q); split; first exact: Htriple.
    rewrite cat_take_drop /w inE /= /RStabmap RSmapinv2K; last exact: RSpairyamQ.
    by rewrite yam_of_stdtabK.
Qed.

Lemma shape_bij_LR_support : shape bij_LR_support = shape Q.
Proof.
  have:= take_drop_langQ; rewrite /= /fun_LR_support /= -shape_RStabmapE RStabmapE.
  rewrite !inE => [] [] /eqP HU1 /eqP HU2.
  have -> : RS (changeUT T1 T2 w) = RS w.
    apply/eqP; rewrite -plactic_RS;
    by apply: plact_changeUT; rewrite -RStabmapE shape_RStabmapE ?HU1 ?HU2.
  rewrite /w -RSmapE shape_RSmap_eq /w RSmapinv2K; last exact: RSpairyamQ.
  by rewrite //= shape_yam_of_stdtab.
Qed.

Lemma shape_takeRS : shape (RS (take d1 w)) = shape U1.
Proof.
  have := take_drop_langQ; rewrite -/w => /= [] [] Htake _.
  move: Htake; rewrite inE => /eqP <-.
  by rewrite -RStabmapE shape_RStabmapE.
Qed.

Lemma shape_dropRS : shape (RS (drop d1 w)) = shape U2.
Proof.
  have := take_drop_langQ; rewrite -/w => /= [] [] _ Hdrop.
  move: Hdrop; rewrite inE => /eqP <-.
  by rewrite -RStabmapE shape_RStabmapE.
Qed.

Lemma predLR_bij_LR_support : predLRTriple T1 T2 bij_LR_support.
Proof.
  apply/LRTripleP => //=; rewrite /fun_LR_support.
  have := take_drop_langQ; rewrite -/w => /= [] [] Htake Hdrop.
  apply LRTriple_cat_langQ => //.
  - have Hpair := changeTtakeP shape_takeRS.
    rewrite (toDepRSPair Hpair) inE.
    have := eq_refl (RSTabPair Hpair).2.
    by rewrite -{1}(RStabinvK (RSTabPair Hpair)) => /=.
  - have Hpair := changeTdropP shape_dropRS.
    rewrite (toDepRSPair Hpair) inE.
    have := eq_refl (RSTabPair Hpair).2.
    by rewrite -{1}(RStabinvK (RSTabPair Hpair)) => /=.
Qed.

End DefBij.

Lemma card_LRtab_set_leq P :
  #|[set Q in (LR_support U1 U2) | (shape Q == P)]| <=
  #|[set Q in (LR_support T1 T2) | (shape Q == P)]|.
Proof.
  rewrite /LR_support.
  have Hsimpl A B C :
      [set Q in (LR_support A B) | (shape Q == C)] =
      [set Q : stdtabn (d1 + d2) | predLRTriple A B Q & (shape Q == C)].
    rewrite -setP => Q; rewrite /LR_support 2!inE [RHS]inE.
    congr (_ && _); by rewrite LRTripleE.
  rewrite !Hsimpl {Hsimpl}.
  rewrite -(card_in_imset (f := bij_LR_support)).
  - apply subset_leqif_cards; apply/subsetP => Qres /imsetP [] Q.
    rewrite inE => /andP [] Hpred /eqP <- -> {Qres}.
    rewrite inE; apply/andP; split.
    + exact: predLR_bij_LR_support.
    + by rewrite shape_bij_LR_support.
  - move=> Q1 Q2; rewrite inE => /andP [] HQ1 /eqP HshQ1.
    rewrite inE => /andP [] HQ2 /eqP; rewrite -HshQ1 {HshQ1} => Heqsh Heq.
    have := erefl (val (bij_LR_support Q1)); rewrite {2}Heq{Heq} => /=.
    rewrite /fun_LR_support.
    set w1 := (X in changeUT _ _ X).
    set w2 := (X in _ = (RStab (changeUT _ _ X)).2) => Heq1.
    have : RS w1 = RS w2.
      rewrite -!RSmapE /w1 /w2 !RSmapinv2K; first last.
      - rewrite /is_RSpair yamtabP /=; last by apply: is_part_sht; exact: stdtabP.
        by rewrite yam_of_stdtabP //= shape_yamtab shape_yam_of_stdtab.
      - rewrite /is_RSpair yamtabP /=; last by apply: is_part_sht; exact: stdtabP.
        by rewrite yam_of_stdtabP //= shape_yamtab shape_yam_of_stdtab.
      - by rewrite /= Heqsh.
    have := take_drop_langQ HQ1.
    have := plact_changeUT (shape_takeRS HQ1) (shape_dropRS HQ1); rewrite -/w1.
    rewrite plactic_RS => /eqP <- [] HQ1take HQ1drop.
    have := take_drop_langQ HQ2.
    have := plact_changeUT (shape_takeRS HQ2) (shape_dropRS HQ2); rewrite -/w2.
    rewrite plactic_RS => /eqP <- [] HQ2take HQ2drop.
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
    by rewrite (RSmapinv2K (RSpairyamQ Q2)) => [] [] _ ->.
Qed.

End ChangeUT.

Lemma card_LRtab_setE P (U1 T1 : stdtabn d1) (U2 T2 : stdtabn d2) :
  shape T1 = shape U1 -> shape T2 = shape U2 ->
  #|[set Q in (LR_support U1 U2) | (shape Q == P)]| =
  #|[set Q in (LR_support T1 T2) | (shape Q == P)]|.
Proof. move=> H1 H2; apply anti_leq; rewrite !card_LRtab_set_leq // H1 H2. Qed.

Lemma LRtab_coeffE (T1 : stdtabn d1) (T2 : stdtabn d2) P :
  shape T1 = P1 -> shape T2 = P2 ->
  LRtab_coeff P = #|[set Q in (LR_support T1 T2) | (shape Q == P)]|.
Proof.
  rewrite /LRtab_coeff /LRtab_set => H1 H2.
  apply card_LRtab_setE; by rewrite shape_hyper_stdtabP ?H1 ?H2.
Qed.

End Bij_LR_support.

End Coeffs.

End FinSets.

Section Conj.

Variables d1 d2 : nat.

Lemma LR_support_conj (T1 : stdtabn d1) (T2 : stdtabn d2):
  LR_support (conj_stdtabn T1) (conj_stdtabn T2) = (@conj_stdtabn _) @: (LR_support T1 T2).
Proof.
  rewrite /LR_support -setP => T; rewrite inE.
  apply (sameP idP); apply (iffP idP).
  - move => /imsetP [] U; rewrite inE -LRTripleE //.
    rewrite conj_predLRTriple // => H -> {T}.
    rewrite -LRTripleE; try exact: is_stdtab_conj.
    exact: H.
  - rewrite -LRTripleE; try exact: is_stdtab_conj; last exact: stdtabnP.
    move=> H.
    apply/imsetP; exists (conj_stdtabn T).
    + rewrite inE -LRTripleE //.
      rewrite conj_predLRTriple // conj_tabK; first exact H.
      * by have := stdtabnP T => /andP [].
      * apply val_inj; rewrite /= conj_tabK //.
        by have := stdtabnP T => /andP [].
Qed.

Theorem LRtab_coeff_conj (P1 : intpartn d1) (P2 : intpartn d2) (P : intpartn (d1 + d2)) :
  LRtab_coeff P1 P2 P =
  LRtab_coeff (conj_intpartn P1) (conj_intpartn P2) (conj_intpartn P).
Proof.
  rewrite [RHS](LRtab_coeffE
                  (T1 := conj_stdtabn (hyper_stdtab P1))
                  (T2 := conj_stdtabn (hyper_stdtab P2))); first last.
    - by rewrite shape_conj_tab  shape_hyper_stdtabP.
    - by rewrite shape_conj_tab  shape_hyper_stdtabP.
  rewrite /LRtab_coeff /LRtab_set LR_support_conj.
  have Hinj : injective (conj_stdtabn (n:=d1 + d2)).
    apply inv_inj => T; apply val_inj; rewrite /= conj_tabK //.
    by have := stdtabnP T => /andP [].
  rewrite -(@card_imset _ _ (@conj_stdtabn _)) //.
  rewrite !setIdE imsetI; last by move=> a b /= _ _; exact: Hinj.
  congr (card (mem (_ :&: _))).
  rewrite -setP => T; rewrite !inE.
  apply (sameP idP); apply (iffP idP).
  - move/eqP => H; apply/imsetP; exists (conj_stdtabn T).
    + by rewrite inE /= shape_conj_tab H /= conj_partK.
    + apply val_inj => //=; rewrite conj_tabK //.
      by have := stdtabnP T => /andP [].
  - move/imsetP => [] U; rewrite inE => /eqP HU -> /=.
    by rewrite shape_conj_tab HU.
Qed.

End Conj.




