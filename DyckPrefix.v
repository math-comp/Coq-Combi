Require Import Arith.
Require Import List.
Require Import Dyck.
Require Import Sublist.
Require Import Multiset.
Require Import Permutation.
Require Import Coq.Sorting.PermutSetoid.
Require Import PermutEq.

Section Prefix.

Notation list_contents := (list_contents _ eq_brace_dec).

Definition mult (l : list Brace) (b : Brace) := multiplicity (list_contents l) b.

Ltac omega_brace :=
  unfold mult in *;
  simpl in *;
  try rewrite ?if_close_close in *;
  try rewrite ?if_close_open  in *;
  try rewrite ?if_open_close  in *;
  try rewrite ?if_open_open   in *;
  omega.

Definition dyck_prefix_height (h : nat) (w : list Brace) : Prop :=
  (forall l : nat, (mult (sublist _ l w) Open) + h >= (mult (sublist _ l w) Close))
  /\
  (mult w Open) + h = mult w Close.

Lemma dyck_prefix_nil :
  forall h : nat, dyck_prefix_height h nil <-> dyck_height h nil.
Proof.
  unfold dyck_prefix_height, mult.
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
  simpl in H0.
  rewrite sublist_0 in H0.
  omega_brace.

  simpl.
  apply IHw; clear IHw.
  split.

  intro l.
  specialize H0 with (S l).
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

Definition dyck_prefix (w : list Brace) : Prop := dyck_prefix_height 0 w.

Theorem prefix_dyck_equiv_dyck :
  forall w : list Brace, is_dyck w <-> dyck_prefix w.
Proof.
  split.
  apply prefix_impl_dyck.
  apply dyck_impl_prefix.
Qed.


End Prefix.
