Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun eqtype ssrnat seq path choice.
From mathcomp Require Import fintype tuple finfun bigop ssralg finset.
From mathcomp Require Import fingroup morphism perm automorphism quotient finalg action.
From mathcomp Require Import zmodp. (* Defines the coercion nat -> 'I_n.+1 *)
From mathcomp Require Import matrix mxalgebra mxpoly mxrepresentation vector ssrnum algC.
From mathcomp Require Import classfun character.

From SsrMultinomials Require Import ssrcomplements poset freeg bigenough mpoly.

From Combi Require Import symgroup partition Greene tools sorted rep1 sympoly Schur_basis.

Require Import ssrcomp bij cycles cycletype.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Bla.

Notation sympoly := (sympoly _ _ ).

Variable n nvar : nat.

Canonical psum k : sympoly := SymPoly (power_sum_sym nvar [fieldType of algC] k).

Local Notation "''p_' k" := (power_sum nvar [fieldType of algC] k)
                              (at level 8, k at level 2, format "''p_' k").

Let bla : sympoly := 'p_2.

Definition frob_iso (x : 'CF([set: 'S_n])) : {sympoly algC[nvar.+1] } :=
  \sum_(l : intpartn #|'I_n|) (x (perm_of_partn l)) *: \prod_(i <- l) 'p_i.

End Bla.
