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

