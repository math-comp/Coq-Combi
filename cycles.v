Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun bigop finset binomial fingroup perm action.

From Combi Require Import symgroup partition.

Set Implicit Arguments.
Unset Strict Implicit.

Section PermCycles.
Variable T: finType.
Implicit Types (s: {perm T}) (x: T).


Definition support s :=
  [set: T] :\: 'Fix_('P)([set s])%g.

Definition is_cycle (s : {perm T}) :=
  #|[set x in pcycles s | #|x| != 1 ]| == 1.

Definition cyclefun_of (s: {perm T}) (x: T) : T :=
  let A := head (set0) (enum ([set y in pcycles s| #|y| != 1])) in if x \in A then s x else x.

Lemma cyclefun_ofP s : injective (cyclefun_of s).
Proof.
Admitted.

Definition cycle_of s : {perm T} := perm (@cyclefun_ofP s).

Lemma cycle_ofE s :
  is_cycle s -> cycle_of s = s.
Proof.
Admitted.

Lemma is_cycleP s :
  reflect (cycle_of s = s) (is_cycle s).
Proof.
Admitted.

Lemma cycle_ofP s: s != 1%g -> is_cycle (cycle_of s).
Proof.
Admitted.

Lemma supp_decr s x :
  s != 1%g -> #|support ((cycle_of s)^-1 * s)| < #|support s|.
Proof.
Admitted.

Lemma perm_cycle_ofK s :
  (support (s * cycle_of s)^-1) = (support s :\: support (cycle_of s)^-1).
Proof.
Admitted.

Lemma support_disjointC s t :
  [disjoint support s & support t] -> (s * t = t * s)%g.
Proof.
Admitted.







End PermCycles.
