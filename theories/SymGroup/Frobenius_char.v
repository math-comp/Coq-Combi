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
(** * Frobenius characteristic associated to a class function of ['SG_n].

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
Require Import permcomp cycletype towerSn permcent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import LeqGeqOrder.
Import GroupScope GRing.Theory.
Open Scope ring_scope.

Local Notation algCF := [fieldType of algC].

Section Defs.

Variable nvar0 : nat.
Local Notation nvar := nvar0.+1.
(* Local Notation n := n0.+1. *)
Local Notation "''z_' p" := (zcoeff p) (at level 2, format "''z_' p").
Local Notation "''1z_[' p ]" := (ncfuniCT p)  (format "''1z_[' p ]").
Local Notation "''p[' k ]" := (homsymp _ _ k)
                              (at level 8, k at level 2, format "''p[' k ]").
Local Notation "''h[' k ]" := (homsymh _ _ k)
                              (at level 8, k at level 2, format "''h[' k ]").

Definition Fchar n (f : 'CF('SG_n)) : {homsym algC[nvar, n]} :=
  locked (\sum_(l : intpartn n) (f (permCT l) / 'z_l) *: 'p[l]).

Lemma FcharE n (f : 'CF('SG_n)) :
  Fchar f = \sum_(l : intpartn n) (f (permCT l) / 'z_l) *: 'p[l].
Proof. by rewrite /Fchar; unlock. Qed.

Lemma Fchar_is_linear n : linear (@Fchar n).
Proof using.
move=> a f g; rewrite !FcharE scaler_sumr -big_split /=.
apply eq_bigr => l _; rewrite !cfunElock.
by rewrite scalerA mulrA -scalerDl mulrDl.
Qed.
Canonical Fchar_linear n := Linear (@Fchar_is_linear n).

Lemma Fchar_ncfuniCT n (l : intpartn n) : Fchar '1z_[l] = 'p[l].
Proof using.
rewrite !FcharE (bigD1 l) //= big1 ?addr0; first last.
  move=> m /negbTE Hm /=.
  rewrite cfunElock cfuniCTE /=.
  rewrite /cycle_typeSn permCTP.
  rewrite partnCTE /= !CTpartnK Hm /=.
  by rewrite mulr0 mul0r scale0r.
rewrite cfunElock cfuniCTE /=.
rewrite /cycle_typeSn permCTP eq_refl /=.
by rewrite mulr1 divff ?scale1r.
Qed.

Lemma Fchar_triv n : Fchar 1 = 'h[rowpartn n].
Proof.
rewrite -decomp_cf_triv linear_sum.
rewrite (eq_bigr (fun la => 'z_la^-1 *: 'p[la])); first last.
  move=> la _.
  rewrite -Fchar_ncfuniCT /ncfuniCT /= linearZ /=.
  by rewrite scalerA /= mulrC divff // scale1r.
apply val_inj; case: n => [|n0]/=.
  rewrite /= prod_gen0.
  rewrite (big_pred1 (rowpartn 0)); first last.
    by move=> la /=; symmetry; apply/eqP/val_inj; rewrite /= intpartn0.
  rewrite linearZ /= prod_gen0.
  rewrite zcoeffE /zcard big_nil mul1n /=.
  rewrite (big_pred1 ord0); first last.
    move=> i /=; symmetry; apply/eqP/val_inj/eqP.
    by rewrite /= -leqn0 -ltnS ltn_ord.
  by rewrite fact0 invr1 scale1r.
rewrite /prod_gen big_seq1 raddf_sum symh_to_symp /=.
by apply eq_bigr => l _; rewrite zcoeffE.
Qed.

Lemma Fchar_isometry n (f g : 'CF('SG_n)) :
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

(**
This cannot be written as a SSReflect [{morph Fchar : f g / ...  >-> ... }]
because the dependency of Fchar on the degree [n]. The three [Fchar] below are
actually three different functions.

Note: this can be solved using a dependant record [{n; 'CF('S_n)}] with a
dependent equality but I'm not sure this is really needed.

*)

Theorem Fchar_ind_morph m n (f : 'CF('SG_m)) (g : 'CF('SG_n)) :
  Fchar ('Ind['SG_(m + n)] (f \o^ g)) = Fchar f *h Fchar g.
Proof using.
rewrite (ncfuniCT_gen f) (ncfuniCT_gen g).
rewrite !linear_sum /=; apply eq_bigr => /= l _.
rewrite homsymprod_suml cfextprod_suml !linear_sum; apply eq_bigr => /= k _.
do 2 rewrite [in RHS]linearZ /= Fchar_ncfuniCT.
rewrite cfextprodZr cfextprodZl scalerA.
rewrite 2!linearZ /= Ind_ncfuniCT linearZ /= Fchar_ncfuniCT /=.
rewrite homsymprodZr homsymprodZl scalerA; congr (_ *: _).
by apply val_inj => /=; rewrite prod_genM.
Qed.

End Defs.
Arguments Fchar [nvar0 n] f.

