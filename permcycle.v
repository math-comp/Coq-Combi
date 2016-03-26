Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial fingroup perm automorphism action.

From Combi Require Import symgroup partition.

Set Implicit Arguments.
Unset Strict Implicit.

Section Definitions.

Variable T : finType.
Implicit Type s : {perm T}.

Definition support s := [set x | s x != x].
Definition is_cycle s :=
  all (fun c : {set T} => #|c| == 1) (enum (pcycles s)).

Definition cyclefun_of s x y : T :=
  if y \in pcycle s x then s y else y.

Lemma cyclefun_ofP s x : injective (finfun (cyclefun_of s x)).
Proof.
Admitted.

Definition cycle_of s x : {perm T} := perm (@cyclefun_ofP s x).

Lemma cycle_of_nsupp s x :
  x \notin (support s) -> cycle_of s x = (perm_one T).
Proof.
Admitted.

Lemma cycle_of_supp s x :
  x \in (support s) -> support s = pcycle s x.
Proof.
Admitted.

Lemma cycle_ofE s x y :
  is_cycle s -> x \in support s -> y \in support s ->
                                         cycle_of s x = cycle_of s y.
Proof.
Admitted.

Lemma cycle_ofP s :
  reflect (exists x, x \in (support s) /\ cycle_of s x = s) (is_cycle s).
Proof.
Admitted.

Lemma perm_cycle_ofK s x :
  support (s * (cycle_of s x)^-1) = support s :\: pcycle s x.
Proof.
Admitted.



End Definitions.

