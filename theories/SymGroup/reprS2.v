(** * Combi.SymGroup.reprS2 : Representations of the symmetric Group for n=2  *)
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
From mathcomp Require Import ssrbool ssrfun eqtype ssrnat seq path choice.
From mathcomp Require Import fintype tuple finfun bigop ssralg finset.
From mathcomp Require Import fingroup morphism perm automorphism quotient finalg action.
From mathcomp Require Import zmodp. (* Defines the coercion nat -> 'I_n.+1 *)
From mathcomp Require Import matrix mxalgebra mxpoly mxrepresentation vector ssrnum algC.
From mathcomp Require Import classfun character.

Require Import tools sorted reprdim1 partition presentSn.
Require Import permcomp cycles cycletype.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma NirrSn n : Nirr 'SG_n = #|{:intpartn n}|.
Proof using. by rewrite NirrE card_classes_perm card_ord. Qed.

Lemma NirrS2 : Nirr 'SG_2 = 2.
Proof using. by rewrite NirrSn card_intpartn. Qed.

Lemma cfRepr_triv n : cfRepr (triv_repr (n := n)) = 'chi_0.
Proof using.
rewrite -cfunP irr0 => s.
rewrite cfunE cfun1E !inE mulr1n.
rewrite /triv_repr /triv_mx /=.
by rewrite mxtrace1.
Qed.
Lemma triv_Chi n : mx_rsim (triv_repr (n := n)) 'Chi_0.
Proof using. by apply/cfRepr_rsimP; rewrite cfRepr_triv irrRepr. Qed.

Lemma cast_IirrS2 (i : Iirr 'SG_2) :
  i != 0 -> i = cast_ord (esym NirrS2) 1.
Proof using.
move=> Hi; apply val_inj => /=.
by case: i Hi => [[|[|i]]] //=; rewrite NirrS2.
Qed.

Lemma cfRepr_sign2 :
  cfRepr (sign_repr (n := 2)) = 'chi_(cast_ord (esym NirrS2) 1).
Proof using.
have : cfRepr sign_repr \in irr 'SG_2.
  apply/irr_reprP.
  by exists (Representation sign_repr); first exact: sign_irr.
move=> /irrP [j]; rewrite -!irrRepr => /eqP/cfRepr_rsimP/mx_rsim_sym Hj.
apply/eqP/cfRepr_rsimP.
apply (mx_rsim_trans (mx_rsim_sym Hj)).
rewrite (cast_IirrS2 (i := j)); first exact: mx_rsim_refl.
apply/eqP => Hj0; subst j.
apply: (triv_sign_not_sim (n := 2)) => //.
exact: mx_rsim_trans (triv_Chi 2) Hj.
Qed.

Lemma sign_Chi2 : mx_rsim (sign_repr (n := 2)) 'Chi_(cast_ord (esym NirrS2) 1).
Proof using. by apply/cfRepr_rsimP; rewrite cfRepr_sign2 irrRepr. Qed.

Lemma char_S2 :
  irr 'SG_2 = tcast (esym NirrS2) [tuple cfRepr triv_repr; cfRepr sign_repr].
Proof using.
apply eq_from_tnth => i.
case: (altP (i =P 0)) => [-> | Hi].
- by rewrite tcastE {2}/tnth /= cfRepr_triv; congr 'chi_(_); exact: val_inj.
- by rewrite tcastE {2}/tnth /= cfRepr_sign2 (cast_IirrS2 Hi) /=.
Qed.

Lemma perm_eq_char_S2 :
  perm_eq [:: cfRepr triv_repr; cfRepr sign_repr] (irr 'SG_2).
Proof using.
have Huniq : uniq [:: cfRepr (triv_repr (n := 2)); cfRepr sign_repr].
  rewrite /= andbT inE; apply/cfRepr_rsimP.
  exact: triv_sign_not_sim.
apply uniq_perm_eq => //; first by apply free_uniq; exact: irr_free.
apply leq_size_perm => //.
move=> i; rewrite !inE => /orP [] /eqP ->; apply/irr_reprP.
- by exists (Representation triv_repr); first exact: triv_irr.
- by exists (Representation sign_repr); first exact: sign_irr.
- have:= NirrSn 2; rewrite card_intpartn /=.
  have -> : intpartn_nb 2 = 2 by [].
  by rewrite size_tuple /= => ->.
Qed.

Lemma repr_S2 (rho : representation [fieldType of algC] [group of 'SG_2]) :
  mx_irreducible rho -> mx_rsim rho triv_repr \/ mx_rsim rho sign_repr.
Proof using.
move=> Hirr.
have : cfRepr rho \in irr 'SG_2.
  apply/irr_reprP; by exists rho.
by rewrite -(perm_eq_mem perm_eq_char_S2) !inE =>
  /orP [] /cfRepr_rsimP; [left | right].
Qed.

