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
Require Import tools partition sympoly homogsym.
Require Import permcomp cycletype towerSn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import LeqGeqOrder.
Import GroupScope GRing.Theory.
Open Scope ring_scope.

Local Notation algCF := [fieldType of algC].

Section Defs.

Variable nvar0 n0 : nat.
Local Notation nvar := nvar0.+1.
Local Notation n := n0.+1.
Local Notation "''z_' p" := (zcoeff p) (at level 2, format "''z_' p").
Local Notation "''1z_[' p ]" := (ncfuniCT p)  (format "''1z_[' p ]").
Local Notation "''p[' k ]" := (homsymp _ _ k)
                              (at level 8, k at level 2, format "''p[' k ]").
Local Notation "''h[' k ]" := (homsymh _ _ k)
                              (at level 8, k at level 2, format "''h[' k ]").

Definition Fchar (f : 'CF('SG_n)) : {homsym algC[nvar, n]} :=
  \sum_(l : intpartn n) (f (permCT l) / 'z_l) *: 'p[l].

Lemma Fchar_is_linear : linear Fchar.
Proof using.
move=> a f g; rewrite /Fchar scaler_sumr -big_split /=.
apply eq_bigr => l _; rewrite !cfunElock.
by rewrite scalerA mulrA -scalerDl mulrDl.
Qed.
Canonical Fchar_linear := Linear Fchar_is_linear.

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

Lemma Fchar_triv : Fchar 1 = 'h[rowpartn n].
Proof.
rewrite -decomp_cf_triv linear_sum.
rewrite (eq_bigr (fun la => 'z_la^-1 *: 'p[la])); first last.
  move=> la _.
  rewrite -Fchar_ncfuniCT /ncfuniCT /= linearZ /=.
  by rewrite scalerA /= mulrC divff // scale1r.
apply val_inj; rewrite /= /prod_gen /= big_seq1.
rewrite raddf_sum symh_to_symp /=.
by apply eq_bigr => l _; rewrite zcoeffE.
Qed.

Lemma Fchar_isometry (f g : 'CF('SG_n)) :
  (n <= nvar)%N -> '[Fchar f | Fchar g] = '[f, g].
Proof.
move=> Hn.
rewrite (ncfuniCT_gen f) (ncfuniCT_gen g) !linear_sum /=.
rewrite homsymdot_suml cfdot_suml; apply eq_bigr => la _.
rewrite homsymdot_sumr cfdot_sumr; apply eq_bigr => mu _.
rewrite ![Fchar (_ *: '1z_[_])]linearZ /= !Fchar_ncfuniCT.
rewrite homsymdotZl homsymdotZr cfdotZl cfdotZr; congr (_ * (_ * _)).
rewrite homsymdotp // cfdotZl cfdotZr cfdot_classfun_part.
case: (altP (la =P mu)) => [<-{mu} | _]; rewrite ?mulr0 ?mulr1 //.
rewrite -zcoeffE -[LHS]mulr1; congr (_ * _).
rewrite /zcoeff rmorphM rmorphV; first last.
  by rewrite unitfE Num.Theory.pnatr_eq0 card_classCT_neq0.
rewrite !conjC_nat -mulrA [X in _ * X]mulrC - mulrA divff; first last.
  by rewrite Num.Theory.pnatr_eq0 card_classCT_neq0.
by rewrite mulr1 divff // Num.Theory.pnatr_eq0 -lt0n cardsT card_Sn fact_gt0.
Qed.

End Defs.
Arguments Fchar [nvar0 n0] f.

(**
This cannot be written as a SSReflect [{morph Fchar : f g / ...  >-> ... }]
because the dependency of Fchar on the degree [n]. The three [Fchar] below are
actually three different functions.

Note: this can be solved using a dependant record [{n; 'CF('S_n)}] with a
dependent equality but I'm not sure this is really needed.

*)

Section IndMorph.

Variables nvar0 n0 m0 : nat.
Local Notation nvar := nvar0.+1.
Local Notation n := n0.+1.
Local Notation m := m0.+1.
Local Notation SF := {sympoly algC[nvar]}.

Theorem Fchar_ind_morph (f : 'CF('SG_m)) (g : 'CF('SG_n)) :
  Fchar ('Ind['SG_(m + n)] (f \o^ g)) =
  (Fchar f : SF) * (Fchar g : SF) :> SF.
Proof using.
rewrite (ncfuniCT_gen f) (ncfuniCT_gen g).
rewrite cfextprod_suml [cfIsom _ _]linear_sum ['Ind[_] _]linear_sum.
rewrite ![Fchar _]linear_sum /= ![homsym _]linear_sum /=.
rewrite mulr_suml /=; apply eq_bigr => /= l _.
rewrite [in RHS]linearZ /= Fchar_ncfuniCT /=.
rewrite cfextprod_sumr [cfIsom _ _]linear_sum ['Ind[_] _]linear_sum.
rewrite ![Fchar _]linear_sum /= ![homsym _]linear_sum /=.
rewrite mulr_sumr /=; apply eq_bigr => /= k _.
rewrite [in RHS]linearZ /= Fchar_ncfuniCT /=.
rewrite -scalerAr -scalerAl scalerA prod_genM.
rewrite cfextprodZr cfextprodZl scalerA.
by rewrite 2!linearZ /= Ind_ncfuniCT linearZ /= Fchar_ncfuniCT /=.
Qed.

End IndMorph.

