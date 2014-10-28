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
Require Import tuple finfun finset bigop ssralg zmodp.
Require Import poly ssrint.

Require Import partition schensted ordtype stdtab invseq greeninv.

(******************************************************************************)
(* The main goal of this file is to lift the multiplication of multivariate   *)
(* polynomials to the non commutative setting.                                *)
(******************************************************************************)



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Local Open Scope ring_scope.
Import GRing.Theory.

Section Poly.

Variable R : comRingType.

Fixpoint multpoly n :=
  if n is n'.+1 then poly_comRingType (multpoly n') else R.

Definition vari n (i : 'I_n) : multpoly n.
Proof.
  elim: n i => [//= | n IHn] i; first by apply 1.
  case (unliftP 0 i) => /= [j |] Hi.
  - apply (polyC (IHn j)).
  - apply 'X.
Defined.

Variable n : nat.

Definition commword (w : seq 'I_n) : multpoly n := \prod_(i <- w) vari i.

Lemma perm_eq_commword (u v : seq 'I_n) : perm_eq u v -> commword u = commword v.
Proof. by apply eq_big_perm. Qed.

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
    last by move=> u _; rewrite mulr_sumr; apply eq_bigr => t _; by rewrite commword_morph.
  rewrite pair_big /=.
  rewrite (@eq_bigr _ _ _ _ _ _ _ (fun p => commword (cat_tuple p.1 p.2)));
    last by move=> [u v].
  rewrite -(@big_imset (multpoly n) _ _ _ _ (fun p => cat_tuple p.1 p.2) _ commword) /=;
    last by move=> [u v] [x y] /= _ _; apply cat_tuple_inj.
  apply eq_bigl => w.
  apply/(sameP idP); apply(iffP idP).
  - move/imset2P => [] u v Hu Hv -> {w}.
    apply/imsetP; exists (u, v) => //=; by rewrite unfold_in /= Hu Hv.
  - move/imsetP => [] [u v] /=; rewrite unfold_in /= => /andP [] Hu Hv ->.
    by apply mem_imset2.
Qed.


End Poly.

Section FinSets.

Variable n : nat.

Hypothesis Hpos : n != 0%N.

Lemma inhabIn : 'I_n.
Proof. move: Hpos; rewrite -lt0n; by apply Ordinal. Qed.

Definition leqOrd (i j : 'I_n) := (i <= j)%N.

Fact leqOrd_order : Order.axiom leqOrd.
Proof.
  split.
  - move=> i; by apply leqnn.
  - move=> i j; rewrite /leqOrd => H; apply val_inj; by apply anti_leq.
  - move=> a b c; by apply leq_trans.
  - exact leq_total.
Qed.

Definition ord_ordMixin := Order.Mixin inhabIn leqOrd_order.
Canonical ord_ordType := Eval hnf in OrdType 'I_n ord_ordMixin.


(* set of tableaux on 'I_n of a given size *)
Definition tabwordsize (d : nat) := [set t : d.-tuple 'I_n | to_word (RS t) == t].
(* set of tableaux on 'I_n of a given shape *)
Definition tabwordshape (sh : seq nat) :=
  [set t : (sumn sh).-tuple 'I_n | (to_word (RS t) == t) && (shape (RS (t)) == sh)].

(* set of tableaux on 'I_n of a given Q-symbol *)
Definition freeSchur (Q : seq (seq nat)) :=
  [set t : (size_tab Q).-tuple 'I_n | (RStabmap t).2 == Q].

Lemma size_RS_tuple d (t : d.-tuple 'I_n) : size (to_word (RS t)) == d.
Proof. rewrite -size_to_word-{2}(size_tuple t); by apply size_RS. Qed.
(* Bijection tabwordshape -> freeSchur *)
Definition tabtuple d (t : d.-tuple 'I_n) : d.-tuple 'I_n := Tuple (size_RS_tuple t).

Lemma perm_eq_tabtuple d (t : d.-tuple 'I_n) : perm_eq t (tabtuple t).
Proof. rewrite /tabtuple /=; by apply perm_eq_RS. Qed.

Lemma tabtuple_freeSchur_inj (Q : seq (seq nat)) :
  {in freeSchur Q &, injective (@tabtuple (size_tab Q))}.
Proof.
  move=> /= u v; rewrite /freeSchur !inE => /eqP Hu /eqP Hv H.
  have {H} /= H : tval (tabtuple u) = tval (tabtuple v) by rewrite H.
  case: (bijRStab ord_ordType) => RSinv HK _.
  apply val_inj; rewrite -[val u]HK -[val v]HK; congr (RSinv _).
  rewrite {RSinv HK} /RStab /=; apply pqpair_inj => /=.
  have := is_tableau_RS u; have := is_tableau_RS v.
  move: Hu Hv H; rewrite -!RStabmapE /RStabmap.
  case RSmap => [pu qu] {u} /= ->; case RSmap => [pv qv] {v} /= -> Heq Hv Hu.
  by rewrite -(RS_tabE Hu) -(RS_tabE Hv) Heq.
Qed.

Lemma tabtuple_freeSchur (Q : seq (seq nat)) :
  is_stdtab Q ->
  [set tabtuple x | x in freeSchur Q] = tabwordshape (shape Q).
Proof.
  move=> Htab; rewrite /freeSchur /tabwordshape /tabtuple.
  apply/setP/subset_eqP/andP; split; apply/subsetP => w; rewrite !inE.
  - move/imsetP => [] t; rewrite inE => /eqP HQ Htmp.
    have /eqP := eq_refl (val w); rewrite {2}Htmp {Htmp} /= => Hw.
    rewrite Hw (RS_tabE (is_tableau_RS t)) eq_refl /= {w Hw}.
    move: HQ; rewrite -!RStabmapE /RStabmap.
    have := (shape_RSmap_eq t).
    case H : RSmap => [p q] /= -> <-.
    by rewrite shape_stdtab_of_yam.
  - move/andP => [] /eqP Hw /eqP Hsh; apply/imsetP.
    have Hpair : is_RStabpair ((RS w), Q).
      by rewrite /is_RStabpair is_tableau_RS Htab Hsh eq_refl.
    have Hpr : is_RSpair (RS w, yam_of_stdtab Q).
      have:= Hpair; rewrite /is_RStabpair /= => /andP [] -> /=.
      move=> /andP [] /yam_of_stdtabP -> /= /eqP ->.
      by rewrite shape_yam_of_stdtab.
    pose imw := (RStabinv (RSTabPair Hpair)).
    have Hsz : size (imw) == size_tab Q.
      rewrite /imw /RStabinv /=.
      rewrite -(eqP (size_RS _)) -RSmapE.
      by rewrite (RS_bij_2 Hpr) /= /size_tab Hsh.
    exists (Tuple Hsz).
    + rewrite inE /= /imw.
      case: (bijRStab ord_ordType) => RSinv HK HinvK.
      rewrite /RStabmap /RStabinv /= (RS_bij_2 Hpr) /=.
      by rewrite yam_of_stdtabK.
    + apply val_inj => /=.
      rewrite /imw /RStabinv /= -Hw /=.
      congr (to_word _).
      by rewrite Hw -[RS (RSmapinv _ _)]RSmapE RS_bij_2.
Qed.

Section Schur.

Variable R : comRingType.

Definition Schur_pol (sh : seq nat) := polyset R (tabwordshape sh).

Lemma Schur_freeSchur (Q : seq (seq nat)) :
  is_stdtab Q -> Schur_pol (shape Q) = polyset R (freeSchur Q).
Proof.
  move=> Htab; rewrite /Schur_pol -(tabtuple_freeSchur Htab) {Htab}.
  rewrite /polyset (big_imset _ (@tabtuple_freeSchur_inj Q)) /=.
  apply eq_bigr => t _; apply perm_eq_commword.
  rewrite perm_eq_sym; by apply perm_eq_RS.
Qed.

Lemma LR_lift_to_free (Q1 Q2 : seq (seq nat)) :
  is_stdtab Q1 -> is_stdtab Q2 ->
  Schur_pol (shape Q1) * Schur_pol (shape Q2) =
  polyset R (catset (freeSchur Q1) (freeSchur Q2)).
Proof. move=> /Schur_freeSchur -> /Schur_freeSchur ->; by apply multcatset. Qed.

(* Use partition_big need stdtab (n) to be a fintype *)
(*
Goal forall (Q1 Q2 : seq (seq nat)),
  is_stdtab Q1 -> is_stdtab Q2 ->
  polyset R (catset (freeSchur Q1) (freeSchur Q2)) = 0.
Proof.
  move=> Q1 Q2 HQ1 HQ2.
  rewrite /polyset /catset.
  have:= (partition_big
            (fun w : (size_tab Q1 + size_tab Q2).-tuple 'I_n => (RStabmap w).2)).
End Schur.
 *)

End FinSets.

