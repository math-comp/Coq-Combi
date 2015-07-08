(** * IterFlip.v: An example of probabilistic termination *)

Add Rec LoadPath "." as ALEA.
Require Export Prog.
Set Implicit Arguments.

(* Module IterFlip (Univ:Universe). *)
(* Module RP := (Rules Univ). *)
(* begin hide *)
(* Import Univ RP PP MP UP. *)
Open Local Scope U_scope.
Open Local Scope O_scope.
(* end hide *)
(** ** Definition of a random walk
We interpret the probabilistic program
<<
let rec iter x = if flip() then iter (x+1) else x
>>*)
Require Import ZArith.

Instance Fiter_mon : 
    monotonic (fun (f:Z -> distr Z) (x:Z) => Mif Flip (f (Zsucc x)) (Munit x)).
red; intros; intro p; apply Mif_le_compat; auto.
Save.

Definition Fiter : (Z -> distr Z) -m> (Z -> distr Z)
:= mon (fun f (x:Z) => Mif Flip (f (Zsucc x)) (Munit x)).

Lemma Fiter_simpl : forall f x, Fiter f x = Mif Flip (f (Zsucc x)) (Munit x).
trivial.
Save.

(*
Lemma Fiter_cont : continuous Fiter.
*)

Definition iterflip : Z -> distr Z := Mfix Fiter.

(** ** Main result
     Probability for [iter] to terminate is [1] *)
(** *** Auxiliary function [p]
   Definition [ p_n = 1 - [1/2] ^ n ] *)

Fixpoint p_ (n : nat) : U := match n with O => 0 | (S n) => [1/2] * p_ n + [1/2] end.

Lemma p_incr : forall n, p_ n <= p_ (S n).
simpl; intros.
transitivity ([1/2]*p_ n + [1/2]*p_ n); auto.
Save.

Hint Resolve p_incr.

Definition p : nat -m> U := fnatO_intro p_ p_incr.

Lemma pS_simpl : forall n, p (S n) = [1/2] * p n + [1/2].
trivial.
Save.

Lemma p_eq : forall n:nat, p n == [1-]([1/2]^n).
induction n; auto; rewrite pS_simpl.
rewrite IHn.
transitivity ([1/2] * [1-]([1/2]^n) + [1-][1/2]);simpl; auto.
Save.
Hint Resolve p_eq.

Lemma p_le : forall n:nat, [1-]([1/]1+n) <= p n.
intro; rewrite (p_eq n).
apply Uinv_le_compat.
induction n; simpl; intros; auto.
transitivity ([1/2] * ([1/]1+n)); auto.
Save.

Hint Resolve p_le.

Lemma lim_p_one : 1 <= lub p.
apply Ule_lt_lim; intros.
assert (exc (fun n : nat => t <= [1-] ([1/]1+n))).
assert (~0 == [1-] t).
red; intro; apply (Olt_notle _ _ H); auto.
transitivity ([1-] 0); auto.
apply (archimedian ([1-]t) H0); auto; intros m H1.
apply exc_intro with m; auto.
apply H0; auto; intros.
transitivity (p x); auto.
transitivity ([1-] ([1/]1+x)); auto.
Save.

Hint Resolve lim_p_one.

(** *** Proof of probabilistic termination  *)
Definition q1 (z1 z2:Z) := 1.

Lemma iterflip_term : okfun (fun k => 1) iterflip q1.
unfold iterflip; intros.
apply okfun_le_compat with (fun (k:Z) => lub p) q1; auto.
intro x; auto.
apply fixrule with (p:= fun (x:Z) => p); auto; intros.
red; simpl; intros.
unfold Fiter.
red.
rewrite (Mif_eq Flip (f (Zsucc x0)) (Munit x0) (q1 x0)); simpl.
repeat Usimpl.
unfold q1 at 2; repeat Usimpl.
transitivity (mu (f (Zsucc x0)) (q1 (Zsucc x0))); auto.
exact (H (Zsucc x0)).
Save.

(* End IterFlip. *)
