Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import finfun fintype tuple finset bigop.
From mathcomp Require Import ssralg fingroup morphism perm gproduct.
From mathcomp Require Import zmodp. (* Defines the coercion nat -> 'I_n.+1 *)
From mathcomp Require Import ssralg matrix vector mxalgebra falgebra ssrnum algC.
From mathcomp Require Import presentation classfun character mxrepresentation.

From Combi Require Import tools ordcast permuted symgroup partition Greene sorted rep1 sympoly.

Require Import ssrcomp slicedbij cycles cycletype reprS2 towerSn.

Import LeqGeqOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Open Scope ring_scope.

Local Notation algCF := [fieldType of algC].
(*

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun eqtype ssrnat seq path choice.
From mathcomp Require Import fintype tuple finfun bigop ssralg finset.
From mathcomp Require Import fingroup morphism perm automorphism quotient finalg action.
From mathcomp Require Import zmodp. (* Defines the coercion nat -> 'I_n.+1 *)
From mathcomp Require Import matrix mxalgebra mxpoly mxrepresentation vector ssrnum algC.
From mathcomp Require Import classfun character.

From SsrMultinomials Require Import ssrcomplements poset freeg bigenough mpoly.

From Combi Require Import symgroup partition Greene tools sorted rep1 sympoly.

Require Import ssrcomp cycles cycletype towerSn.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.
*)

Section Defs.

Variable nvar n : nat.

Local Notation "'z_ p " := (zcoeff p) (at level 2).
Local Notation "''P_[' p ]" := (pbasis p).

Definition frob_iso (f : 'CF([set: 'S_n])) : {sympoly algC[nvar]} :=
  \sum_(l : intpartn n) (f (perm_of_partCT l) / 'z_l) *: 'p[l].

Lemma frob_iso_is_linear : linear frob_iso.
Proof.
move=> a f g; rewrite /frob_iso scaler_sumr -big_split /=.
apply eq_bigr => l _; rewrite !cfunElock.
by rewrite scalerA mulrA -scalerDl mulrDl.
Qed.
Canonical frob_iso_linear := Linear frob_iso_is_linear.

Lemma frob_pbasis l : frob_iso 'P_[l] = 'p[l].
Proof.
rewrite /frob_iso /pbasis (bigD1 l) //= big1 ?addr0; first last.
  move=> m /negbTE Hm /=.
  rewrite cfunElock cfuni_partE /=.
  rewrite /cycle_typeSN perm_of_partCTP.
  rewrite partn_of_partCTE /= !partCT_of_partnK Hm /=.
  by rewrite mulr0 mul0r scale0r.
rewrite cfunElock cfuni_partE /=.
rewrite /cycle_typeSN perm_of_partCTP eq_refl /=.
rewrite mulr1 divff ?scale1r //.
exact: neq0zcoeff.
Qed.

End Defs.

Lemma frob_ind_morph nvar n m (f : 'CF([set: 'S_m])) (g : 'CF([set: 'S_n])) :
  frob_iso nvar ('Ind[[set: 'S_(m + n)]] ((f \ox g)|^)) =
  frob_iso nvar f * frob_iso nvar g.
Proof.
rewrite (pbasis_gen f) (pbasis_gen g).
rewrite cfExtProd_suml !linear_sum [RHS]mulr_suml.
apply eq_bigr => /= l _.
rewrite cfExtProd_sumr !linear_sum [RHS]mulr_sumr.
apply eq_bigr => /= k _.
rewrite cfExtProdZr cfExtProdZl scalerA.
rewrite 3!linearZ /= Ind_pbasis frob_pbasis.
do 2 rewrite linearZ /= frob_pbasis.
by rewrite -scalerAr -scalerAl scalerA prod_genM.
Qed.
