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
From mathcomp Require Import rat ssralg ssrnum algC.
From mathcomp Require Import classfun.

From SsrMultinomials Require Import mpoly.
Require Import tools partition sympoly.
Require Import permcomp cycletype towerSn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import LeqGeqOrder.
Import GroupScope GRing.Theory.
Open Scope ring_scope.

Local Notation algCF := [fieldType of algC].

Section Defs.

Variable nvar n : nat.

Local Notation "''z_' p" := (zcoeff p) (at level 2, format "''z_' p").
Local Notation "''1z_[' p ]" := (ncfuniCT p)  (format "''1z_[' p ]").

Definition Fchar (f : 'CF('SG_n)) : {sympoly algC[nvar]} :=
  \sum_(l : intpartn n) (f (permCT l) / 'z_l) *: 'p[l].

Lemma Fchar_is_linear : linear Fchar.
Proof using.
move=> a f g; rewrite /Fchar scaler_sumr -big_split /=.
apply eq_bigr => l _; rewrite !cfunElock.
by rewrite scalerA mulrA -scalerDl mulrDl.
Qed.
Canonical Fchar_linear := Linear Fchar_is_linear.

Lemma Fchar_homog f : sympol (Fchar f) \is n.-homog.
Proof.
rewrite /Fchar !linear_sum  //=.
apply rpred_sum => m _; apply rpredZ.
exact: prod_symp_homog.
Qed.

Lemma Fchar_ncfuniCT l : Fchar '1z_[l] = 'p[l].
Proof using.
rewrite /Fchar (bigD1 l) //= big1 ?addr0; first last.
  move=> m /negbTE Hm /=.
  rewrite cfunElock cfuniCTE /=.
  rewrite /cycle_typeSn permCTP.
  rewrite partnCTE /= !CTpartnK Hm /=.
  by rewrite mulr0 mul0r scale0r.
rewrite cfunElock cfuniCTE /=.
rewrite /cycle_typeSn permCTP eq_refl /=.
by rewrite mulr1 divff ?scale1r.
Qed.

Lemma Fchar_triv : Fchar 1 = 'h_n.
Proof.
rewrite -decomp_cf_triv linear_sum symh_to_symp /=.
rewrite (eq_bigr (fun la => 'z_la^-1 *: 'p[la])); first last.
  move=> la _.
  rewrite -Fchar_ncfuniCT /ncfuniCT /= linearZ /=.
  by rewrite scalerA /= mulrC divff // scale1r.
apply val_inj; rewrite /= /prod_gen /=.
by rewrite !raddf_sum; apply eq_bigr => l _; rewrite zcoeffE.
Qed.

End Defs.
Arguments Fchar [nvar n] f.

(**
This cannot be written as a SSReflect [{morph Fchar : f g / ...  >-> ... }]
because the dependency of Fchar on the degree [n]. The three [Fchar] below are
actually three different functions.

Note: this can be solved using a dependant record [{n; 'CF('S_n)}] with a
dependent equality but I'm not sure this is really needed.

*)

Theorem Fchar_ind_morph nv n m (f : 'CF('SG_m)) (g : 'CF('SG_n)) :
  Fchar ('Ind['SG_(m + n)] (f \o^ g)) = Fchar f * Fchar g :> {sympoly algC[nv]}.
Proof using.
rewrite (ncfuniCT_gen f) (ncfuniCT_gen g).
rewrite cfextprod_suml !linear_sum [RHS]mulr_suml.
apply eq_bigr => /= l _.
rewrite cfextprod_sumr !linear_sum [RHS]mulr_sumr.
apply eq_bigr => /= k _.
rewrite cfextprodZr cfextprodZl scalerA.
rewrite 3!linearZ /= Ind_ncfuniCT Fchar_ncfuniCT.
do 2 rewrite linearZ /= Fchar_ncfuniCT.
by rewrite -scalerAr -scalerAl scalerA prod_genM.
Qed.
