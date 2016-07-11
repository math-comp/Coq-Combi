Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun bigop finset binomial fingroup perm.
From mathcomp Require Import fintype tuple finfun bigop prime ssralg poly finset.
From mathcomp Require Import fingroup morphism perm automorphism quotient finalg action.
From mathcomp Require Import matrix vector mxalgebra falgebra ssrnum algC algnum.
From mathcomp Require Import presentation all_character.

From Combi Require Import symgroup partition Greene tools sorted rep1.

Require Import ssrcomp bij cycles cycletype.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma NirrSn n : Nirr [set: 'S_n] = #|{:intpartn n}|.
Proof. by rewrite NirrE card_class_perm card_ord. Qed.

Lemma char_S2 :
  perm_eq [:: cfRepr triv_repr; cfRepr sign_repr] (irr [set: 'S_2]).
Proof.
  have Huniq : uniq [:: cfRepr (triv_repr (n := 2)); cfRepr sign_repr].
    rewrite /= andbT inE; apply/cfRepr_rsimP.
    exact: triv_sign_not_sim.
  apply uniq_perm_eq => //; first by apply free_uniq; exact: irr_free.
  apply leq_size_perm => //.
  move=> i; rewrite !inE => /orP [] /eqP ->; apply/irr_reprP.
  - by exists (Representation triv_repr); first exact: triv_irr.
  - by exists (Representation sign_repr); first exact: sign_irr.
    have:= NirrSn 2; rewrite card_intpartn /=.
    have -> : intpartn_nb 2 = 2 by [].
    by rewrite size_tuple /= => ->.
Qed.

Lemma repr_S2 (rho : representation [fieldType of algC] [set: 'S_2]) :
  mx_irreducible rho -> mx_rsim rho triv_repr \/ mx_rsim rho sign_repr.
Proof.
  move=> Hirr.
  have : cfRepr rho \in (irr [set: 'S_2]).
    apply/irr_reprP; by exists rho.
  by rewrite -(perm_eq_mem char_S2) !inE =>
    /orP [] /cfRepr_rsimP; [left | right].
Qed.
