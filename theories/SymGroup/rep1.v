(** * Combi.SymGroup.rep1 : Representation of Dimension 1 of the symmetric group *)
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
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun bigop finset binomial fingroup perm.
From mathcomp Require Import fintype tuple finfun bigop prime ssralg poly finset.
From mathcomp Require Import fingroup morphism perm automorphism quotient finalg action.
From mathcomp Require Import matrix vector mxalgebra falgebra ssrnum algC algnum.
From mathcomp Require Import presentation all_character.

Require Import tools permuted combclass congr symgroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Notation reprS n d :=
  (mx_representation [fieldType of algC] [set: 'S_n] d).

Section DefTrivSign.

Variable n d : nat.
Variable rho : reprS n d.

Definition triv_mx_reprf :=
  [fun g : 'S_n => 1 : 'M[algC]_1].
Definition sign_mx_reprf :=
  [fun g : 'S_n => if odd_perm g then -1 else 1 : 'M[algC]_1].
Definition signed_mx_reprf :=
  [fun g : 'S_n => if odd_perm g then -(rho g) else rho g].

Lemma triv_mx_reprP : mx_repr [set: 'S_n] triv_mx_reprf.
Proof.
  split; first by [].
  by move=> g1 g2 _ _; rewrite mul1mx.
Qed.
Definition triv_mx_repr : reprS n 1 := MxRepresentation triv_mx_reprP.

Lemma sign_mx_reprP : mx_repr [set: 'S_n] sign_mx_reprf.
Proof.
  split; first by rewrite /= odd_perm1.
  move=> g1 g2 _ _; rewrite /= odd_permM /=.
  by case: (odd_perm g1); case: (odd_perm g2);
    rewrite /= ?mulNmx ?mulmxN ?opprK mul1mx //.
Qed.
Definition sign_mx_repr : reprS n 1 := MxRepresentation sign_mx_reprP.

Lemma signed_mx_reprP : mx_repr [set: 'S_n] signed_mx_reprf.
Proof.
  split; first by rewrite /= odd_perm1 repr_mx1.
Proof.
  move=> g1 g2 _ _; rewrite /= odd_permM /=.
  by case: (odd_perm g1); case: (odd_perm g2);
    rewrite /=  ?mulNmx ?mulmxN ?opprK repr_mxM // inE.
Qed.
Definition signed_mx_repr : reprS n d := MxRepresentation signed_mx_reprP.

End DefTrivSign.
Arguments triv_mx_repr [n].
Arguments sign_mx_repr [n].

Lemma permS0 (g : 'S_0) : g = 1%g.
Proof. by rewrite -permP => x; case x. Qed.
Lemma permS1 (g : 'S_1) : g = 1%g.
Proof.
rewrite -permP => x; case x => i Hi.
apply val_inj => /=; rewrite permE.
case: (g (Ordinal Hi)) => a Ha /=.
by move: Hi Ha; rewrite !ltnS !leqn0 => /eqP -> /eqP ->.
Qed.

Lemma row_free1 : row_free (1 : 'M[algC]_1).
Proof. by apply/row_freeP; exists 1; rewrite mul1mx. Qed.

Lemma repr1_S0 (rho : reprS 0 1) : mx_rsim rho triv_mx_repr.
Proof.
apply: (MxReprSim (B := 1)) => //; first exact: row_free1.
rewrite /triv_mx_repr /= => g _ /=.
by rewrite mul1mx mulmx1 (permS0 g) repr_mx1.
Qed.

Lemma repr1_S1 (rho : reprS 1 1) : mx_rsim rho triv_mx_repr.
Proof.
apply: (MxReprSim (B := 1)) => //; first exact: row_free1.
rewrite /triv_mx_repr /= => g _ /=.
by rewrite mul1mx mulmx1 (permS1 g) repr_mx1.
Qed.

Lemma triv_sign_not_sim n :
  (n >= 2)%N -> ~ mx_rsim (G := [set: 'S_n]) triv_mx_repr sign_mx_repr.
Proof.
  case: n => // n; rewrite ltnS => Hn [B _].
  rewrite row_free_unit => /mulrI HB Hsim.
  have {Hsim} /Hsim : (eltr n 0) \in [set: 'S_n.+1] by [].
  rewrite /triv_mx_repr /= mul1mx (odd_eltr Hn).
  rewrite -[LHS]mulmx1 => /HB/eqP; rewrite -addr_eq0 -mulr2n => /eqP.
  rewrite -matrixP => /(_ ord0 ord0).
  rewrite !mxE eq_refl /= => /eqP.
  by have := Cchar; rewrite charf0P => /(_ 2) ->.
Qed.

Lemma repr1 n (rho : reprS n 1) :
  mx_rsim rho triv_mx_repr \/ mx_rsim rho sign_mx_repr.
Proof.
  case: n rho => [| n] rho; first by left; exact: repr1_S0.
  have Hs0 : eltr n 0 \in [set: 'S_n.+1] by [].
  have /esym := repr_mxMr rho Hs0 Hs0.
  set M := rho (eltr n 0).
  rewrite tperm2 repr_mx1 (mx11_scalar M).
  rewrite -mulmxE -scalar_mxM -matrixP => /(_ ord0 ord0) /eqP.
  rewrite !mxE eq_refl mulr1n /= -expr2 sqrf_eq1 => /orP [] /eqP HM.
  - left; apply: (MxReprSim (B := 1)) => //; first exact: row_free1.
    rewrite /triv_mx_repr /= => g _; rewrite mul1mx mulmx1.
    have Heltr i : (i < n)%N -> rho (eltr _ i) = 1.
      elim: i => [| i IHi] Hi; first by rewrite -/M (mx11_scalar M) HM.
      have /(congr1 rho) := eltr_braid Hi.
      rewrite !repr_mxMr ?inE //= IHi; last exact: ltnW.
      rewrite !mulr1.
      have: eltr n i.+1 \in [set: 'S_n.+1] by [].
      by move=> /(repr_mx_unit rho)/mulIr H/H <-.
    rewrite (canwordP g); elim: (canword g) => [| w0 w IHw] /=.
      by rewrite big_nil repr_mx1.
    rewrite big_cons repr_mxM ?inE // IHw mulmx1.
    exact: Heltr.
  - right; apply: (MxReprSim (B := 1)) => //; first exact: row_free1.
    rewrite /sign_mx_repr /= => g _; rewrite mul1mx mulmx1.
    have Heltr i : (i < n)%N -> rho (eltr _ i) = -1.
      elim: i => [| i IHi] Hi.
        by rewrite -/M (mx11_scalar M) HM -[RHS]scaleN1r -scalemx1.
      have /(congr1 rho) := eltr_braid Hi.
      rewrite !repr_mxMr ?inE //= IHi; last exact: ltnW.
      rewrite !mulrN1 mulNr => /eqP; rewrite eqr_opp => /eqP.
      have: eltr n i.+1 \in [set: 'S_n.+1] by [].
      by move=> /(repr_mx_unit rho)/mulIr H/H <-.
    rewrite (canwordP g); elim: (canword g) => [| w0 w IHw] /=.
      by rewrite big_nil repr_mx1 odd_perm1.
    rewrite big_cons repr_mxM ?inE // {}IHw odd_permM odd_eltr //= Heltr //.
    case: (odd_perm (\prod_(i <- w) eltr n i)) => /=;
      rewrite mulmxE mulN1r //.
    exact: opprK.
Qed.

