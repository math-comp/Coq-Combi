Require Import Arith.
Require Import List.
Require Import Dyck.
Require Import Prefix.
Require Import Multiset.
Require Import Permutation.
Require Import Coq.Sorting.PermutSetoid.
Require Import PermutEq.

Section DyckPrefix.

Notation list_contents := (list_contents _ eq_brace_dec).

Definition mult (w : list Brace) (b : Brace) := multiplicity (list_contents w) b.

Definition mult_prefix (l : nat) (w : list Brace) :=  mult (prefix Brace l w).

Ltac omega_brace :=
  unfold mult_prefix, mult in *;
  simpl in *;
  try rewrite ?if_close_close in *;
  try rewrite ?if_close_open  in *;
  try rewrite ?if_open_close  in *;
  try rewrite ?if_open_open   in *;
  omega.

Definition dyck_prefix_height (h : nat) (w : list Brace) : Prop :=
  (forall l : nat, (mult_prefix l w Open) + h >= (mult_prefix l w Close))
  /\
  (mult w Open) + h = mult w Close.

Lemma dyck_prefix_nil :
  forall h : nat, dyck_prefix_height h nil <-> dyck_height h nil.
Proof.
  unfold dyck_prefix_height, mult_prefix, mult.
  destruct h; simpl.
  split.
  auto with arith.
  intro H; clear H; split; auto.
  destruct l;
  simpl; auto.
  split.
  intro H; decompose [and] H; auto.
  split; auto with arith.
  inversion H.
Qed.

Lemma dyck_impl_prefix :
  forall (w : list Brace) (h : nat), dyck_prefix_height h w -> dyck_height h w.
Proof.
  unfold dyck_prefix_height.
  induction w.
  apply dyck_prefix_nil.
  intro h.
  destruct a.

  simpl.
  intro H; decompose [and] H; clear H.
  apply IHw.
  split.
  clear IHw H1.
  intro l.
  specialize H0 with (S l).
  omega_brace.

  clear IHw H0.
  omega_brace.

  intro H; decompose [and] H; clear H.
  destruct h.
  clear IHw H1.
  specialize H0 with 1.
  unfold mult_prefix, mult in H0.
  simpl in H0.
  rewrite prefix_0 in H0.
  omega_brace.

  simpl.
  apply IHw; clear IHw.
  split.

  intro l.
  specialize H0 with (S l).
  unfold mult_prefix in H0.
  simpl in H0.
  omega_brace.

  omega_brace.
Qed.

Lemma prefix_impl_dyck :
  forall (w : list Brace) (h : nat), dyck_height h w -> dyck_prefix_height h w.
Proof.
  unfold dyck_prefix_height.
  induction w.
  apply dyck_prefix_nil.
  intro h.
  destruct a.
  intro H.
  simpl in H.
  split.

  destruct l.
  simpl.
  unfold mult; auto with arith.

  simpl.
  specialize IHw with (S h).
  elim IHw; auto; clear H IHw; intros IHw IHw1; clear IHw1.
  specialize IHw with l.
  omega_brace.

  specialize IHw with (S h).
  elim IHw; auto; clear H IHw; intros IHw IHw1; clear IHw.
  omega_brace.

  intro H; destruct h.
  simpl in H; contradiction.

  split.

  destruct l.
  simpl.
  unfold mult; auto with arith.

  simpl in H|-*.
  specialize IHw with h.
  elim IHw; auto; clear IHw; intros IHw IHw1; clear IHw1.
  specialize IHw with l.
  omega_brace.

  simpl in H|-*.
  specialize IHw with h.
  elim IHw; auto; clear IHw; intros IHw IHw1; clear IHw.
  omega_brace.
Qed.


Definition dyck_prefix (w : list Brace) : Prop :=
  (forall l : nat, (mult_prefix l w Open) >= (mult_prefix l w Close))
  /\
  mult w Open = mult w Close.

(* Definition dyck_prefix (w : list Brace) : Prop := dyck_prefix_height 0 w. *)

Theorem prefix_dyck_equiv_dyck :
  forall w : list Brace, is_dyck w <-> dyck_prefix w.
Proof.
  unfold dyck_prefix.
  split.
  intro H.
  specialize prefix_impl_dyck with w 0; intros Hd.
  unfold dyck_prefix_height in Hd.
  elim Hd; clear Hd; auto.
  intros H1 H2.
  split.
  intro l; specialize H1 with l.
  rewrite <- plus_n_O in H1; assumption.
  rewrite <- plus_n_O in H2; assumption.
  specialize dyck_impl_prefix with w 0; intro Hd.
  unfold dyck_prefix_height in Hd.
  intros.
  apply Hd; clear Hd.
  decompose [and] H; clear H.
  split.
  intros l.
  rewrite <- plus_n_O; apply H0.
  rewrite <- plus_n_O; assumption.
Qed.


End DyckPrefix.
