(** * Combi.MPoly.sympoly_def : Definition of Symmetric Polynomials *)
(******************************************************************************)
(*      Copyright (C) 2015-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** This is a technical file whose goal is to mitigate some performance
issues with hierarchy builder compiling the subalgebra structure of symmetric
polynomials. You should'nt import is directly.
 ******)
From HB Require Import structures.
From mathcomp Require Import all_boot ssralg.
From mathcomp Require Import ssrcomplements freeg mpoly.

Set SsrOldRewriteGoalsOrder.  (* change to Unset and remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Open Scope ring_scope.
Import GRing.Theory.

Reserved Notation "{ 'sympoly' T [ n ] }"
  (at level 0, T, n at level 2, format "{ 'sympoly'  T [ n ] }").

Section DefType.

Variable n : nat.
Variable R : nzRingType.

Record sympoly : predArgType :=
  SymPoly {sympol :> {mpoly R[n]}; _ : sympol \is symmetric}.

HB.instance Definition _ := [isSub of sympoly for sympol].
HB.instance Definition _ := [Choice of sympoly by <:].

Lemma sympol_inj : injective sympol. Proof. exact: val_inj. Qed.

End DefType.

(* We need to break off the section here to let the argument scope *)
(* directives take effect.                                         *)
Bind Scope ring_scope with sympoly.
(* Arguments sympol {n}%nat_scope {R}%ring_scope. *)

Notation "{ 'sympoly' T [ n ] }" := (sympoly n T).


Section SymPolyRingType.

Variable n : nat.
Variable R : nzRingType.

HB.instance Definition _ := [SubChoice_isSubLalgebra of {sympoly R[n]} by <:].

Fact sympol_is_linear : linear (@sympol n R).
Proof. by []. Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build
    R {sympoly R[n]} {mpoly R[n]} _ _ sympol_is_linear.
Fact sympol_is_monoid_morphism : monoid_morphism (@sympol n R).
Proof. by []. Qed.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build
    {sympoly R[n]} {mpoly R[n]} _ sympol_is_monoid_morphism.

Lemma sympolP (x : {sympoly R[n]}) : sympol x \is symmetric.
Proof. by case: x. Qed.

End SymPolyRingType.

#[export] Hint Resolve sympolP : core.


Section SymPolyComRingType.

Variable n : nat.
Variable R : comNzRingType.

HB.instance Definition _ :=
  [SubChoice_isSubAlgebra of {sympoly R[n]} by <:].
HB.instance Definition _ :=
  [SubNzRing_isSubComNzRing of {sympoly R[n]} by <:].

End SymPolyComRingType.


Section SymPolyIdomainType.

Variable n : nat.
Variable R : idomainType.

HB.instance Definition _ :=
  [SubNzRing_isSubUnitRing of {sympoly R[n]} by <:].
HB.instance Definition _ :=
  [SubComUnitRing_isSubIntegralDomain of {sympoly R[n]} by <:].

End SymPolyIdomainType.

