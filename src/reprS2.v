Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun eqtype ssrnat seq path choice.
From mathcomp Require Import fintype tuple finfun bigop ssralg finset.
From mathcomp Require Import fingroup morphism perm automorphism quotient finalg action.
From mathcomp Require Import zmodp. (* Defines the coercion nat -> 'I_n.+1 *)
From mathcomp Require Import matrix mxalgebra mxpoly mxrepresentation vector ssrnum algC.
From mathcomp Require Import classfun character.

From Combi Require Import symgroup partition Greene tools sorted rep1.

Require Import ssrcomp cycles cycletype.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma NirrSn n : Nirr [set: 'S_n] = #|{:intpartn n}|.
Proof. by rewrite NirrE card_classes_perm card_ord. Qed.

Lemma NirrS2 : Nirr [set: 'S_2] = 2.
Proof. by rewrite NirrSn card_intpartn. Qed.

Lemma cfRepr_triv n : cfRepr (triv_repr (n := n)) = 'chi_0.
Proof.
  rewrite -cfunP irr0 => s.
  rewrite cfunE cfun1E !inE mulr1n.
  rewrite /triv_repr /triv_mx /=.
  by rewrite mxtrace1.
Qed.
Lemma triv_Chi n : mx_rsim (triv_repr (n := n)) 'Chi_0.
Proof. by apply/cfRepr_rsimP; rewrite cfRepr_triv irrRepr. Qed.

Lemma IirrS2_non0 (i : Iirr [set: 'S_2]%G) :
  i != 0 -> i = cast_ord (esym NirrS2) 1.
Proof.
  move=> Hi; apply val_inj => /=.
  by case: i Hi => [[|[|i]]] //=; rewrite NirrS2.
Qed.

Lemma cfRepr_sign2 : cfRepr (sign_repr (n := 2)) = 'chi_(cast_ord (esym NirrS2) 1).
Proof.
  have : cfRepr sign_repr \in irr [set: 'S_2].
    apply/irr_reprP.
    by exists (Representation sign_repr); first exact: sign_irr.
  move=> /irrP [j]; rewrite -!irrRepr => /eqP/cfRepr_rsimP/mx_rsim_sym Hj.
  apply/eqP/cfRepr_rsimP.
  apply (mx_rsim_trans (mx_rsim_sym Hj)).
  rewrite (IirrS2_non0 (i := j)); first exact: mx_rsim_refl.
  apply/eqP => Hj0; subst j.
  apply: (triv_sign_not_sim (n := 2)) => //.
  exact: mx_rsim_trans (triv_Chi 2) Hj.
Qed.
Lemma sign_Chi2 : mx_rsim (sign_repr (n := 2)) 'Chi_(cast_ord (esym NirrS2) 1).
Proof. by apply/cfRepr_rsimP; rewrite cfRepr_sign2 irrRepr. Qed.

Lemma char_S2 :
  irr [set: 'S_2] = tcast (esym NirrS2) [tuple cfRepr triv_repr; cfRepr sign_repr].
Proof.
  apply eq_from_tnth => i.
  case: (altP (i =P 0)) => [-> | Hi].
  - by rewrite tcastE {2}/tnth /= cfRepr_triv; congr 'chi_(_); exact: val_inj.
  - by rewrite tcastE {2}/tnth /= cfRepr_sign2 (IirrS2_non0 Hi) /=.
Qed.

Lemma perm_eq_char_S2 :
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
  - have:= NirrSn 2; rewrite card_intpartn /=.
    have -> : intpartn_nb 2 = 2 by [].
    by rewrite size_tuple /= => ->.
Qed.

Lemma repr_S2 (rho : representation [fieldType of algC] [set: 'S_2]) :
  mx_irreducible rho -> mx_rsim rho triv_repr \/ mx_rsim rho sign_repr.
Proof.
  move=> Hirr.
  have : cfRepr rho \in (irr [set: 'S_2]).
    apply/irr_reprP; by exists rho.
  by rewrite -(perm_eq_mem perm_eq_char_S2) !inE =>
    /orP [] /cfRepr_rsimP; [left | right].
Qed.

