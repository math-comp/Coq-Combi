From Corelib Require Import Setoid.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import bigop div.


Fixpoint is_part shape :=
  if shape is shape0 :: shape'
  then (shape0 >= head 1 shape') && (is_part shape')
  else true.

Fixpoint incr_first_n shape n :=
  if shape is s0 :: s then
    if n is n'.+1 then s0.+1 :: incr_first_n s n'
    else shape
  else nseq n 1.
Fixpoint conj_part shape :=
  if shape is s0 :: shape then incr_first_n (conj_part shape) s0
  else [::].

Lemma is_part_nseq1 n : is_part (nseq n 1).
Proof. by elim: n => [//= | n /= ->]; rewrite andbT; case n. Qed.

Lemma is_part_incr_first_n shape n :
  is_part shape -> is_part (incr_first_n shape n).
Proof.
elim: shape n => [// n _| s0 shape IHshape] /=; first exact: is_part_nseq1.
case=> [//= | n] /andP [Hhead /IHshape{IHshape} /= ->]; rewrite andbT.
case: shape Hhead => [_ | s1 shape] /=; first by case n.
case: n => [| n] /=; last by apply.
by move/leq_trans; apply.
Qed.

Lemma is_part_conj shape : is_part shape -> is_part (conj_part shape).
Proof.
elim: shape => [//= | s0 shape IHshape] /= /andP [_ /IHshape{IHshape}].
exact: is_part_incr_first_n.
Qed.



Lemma sum n :
  \sum_(0 <= i < n.+1) i = n * (n + 1) %/ 2.
Proof.
elim : n => [//= | n IHn].
  by rewrite !mul0n div0n big_nat_recl // big_nat big_pred0.
rewrite big_nat_recr //= {}IHn.
rewrite [LHS]addnC -divnMDl //; congr (_ %/ _).
by ring_simplify.
Qed.
