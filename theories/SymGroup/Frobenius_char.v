(** * Combi.SymGroup.Frobenius_char : Frobenius characteristic *)
(******************************************************************************)
(*       Copyright (C) 2016 Florent Hivert <florent.hivert@lri.fr>            *)
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
(** * Frobenius characteristic

- [Fchar f] == the Frobenius characteristic of the class function [f].
               the number of variable is inferred from the context.
 *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import finfun fintype tuple finset bigop.
From mathcomp Require Import ssralg fingroup morphism perm gproduct.
From mathcomp Require Import rat ssralg mxalgebra ssrnum algC.
From mathcomp Require Import classfun character mxrepresentation.

Require Import tools partition sympoly.
Require Import permcomp symgroup cycles cycletype towerSn commutant.

Import LeqGeqOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Open Scope ring_scope.

Local Notation algCF := [fieldType of algC].

Section Defs.

Variable nvar n : nat.

Local Notation "'z_ p " := (zcoeff p) (at level 2).
Local Notation "''P_[' p ]" := (pbasis p).

Definition Fchar (f : 'CF('SG_n)) : {sympoly algC[nvar]} :=
  \sum_(l : intpartn n) (f (perm_of_partCT l) / 'z_l) *: 'p[l].

Lemma Fchar_is_linear : linear Fchar.
Proof using.
move=> a f g; rewrite /Fchar scaler_sumr -big_split /=.
apply eq_bigr => l _; rewrite !cfunElock.
by rewrite scalerA mulrA -scalerDl mulrDl.
Qed.
Canonical Fchar_linear := Linear Fchar_is_linear.

Lemma Fchar_pbasis l : Fchar 'P_[l] = 'p[l].
Proof using.
rewrite /Fchar /pbasis (bigD1 l) //= big1 ?addr0; first last.
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

Lemma Fchar_triv : Fchar 1 = 'h_n.
Proof.
rewrite -decomp_cf_triv linear_sum.
rewrite (eq_bigr (fun i => 'z_i^-1 *: 'p[i])); first last.
  move=> l _; rewrite -Fchar_pbasis /= linearZ scalerA mulrC divff ?scale1r //.
  exact: neq0zcoeff.
rewrite -QtoCcomplete complete_to_power_sum /=.
rewrite rmorph_sum /=; apply eq_bigr => l _.
by rewrite zcoeffE scale_rat_QtoC QtoCpower_sum_prod fmorphV /= ratr_nat.
Qed.

End Defs.
Arguments Fchar [nvar n] f.


Lemma Fchar_ind_morph nv n m (f : 'CF('SG_m)) (g : 'CF('SG_n)) :
  Fchar ('Ind['SG_(m + n)] (f \o^ g)) = Fchar f * Fchar g :> {sympoly algC[nv]}.
Proof using.
rewrite (pbasis_gen f) (pbasis_gen g).
rewrite cfextprod_suml !linear_sum [RHS]mulr_suml.
apply eq_bigr => /= l _.
rewrite cfextprod_sumr !linear_sum [RHS]mulr_sumr.
apply eq_bigr => /= k _.
rewrite cfextprodZr cfextprodZl scalerA.
rewrite 3!linearZ /= Ind_pbasis Fchar_pbasis.
do 2 rewrite linearZ /= Fchar_pbasis.
by rewrite -scalerAr -scalerAl scalerA prod_genM.
Qed.
