(** * RandomList.v : pick uniformely an element in a list *)
(** Contributed by David Baelde, 2011 *)

(* begin hide *)
Add Rec LoadPath "." as ALEA.

Set Implicit Arguments.
Require Export Prog.
Require Export List.

Open Scope U_scope.
(* end hide *)

Fixpoint choose A (l : list A) : distr A :=
  match l with
    | nil => distr_null A
    | cons hd tl => Mchoice ([1/](length l)) (Munit hd) (choose tl)
  end.

Lemma choose_uniform : forall A (d : A) (l : list A) f,
  mu (choose l) f == sigma (fun i => ([1/](length l)) * f (nth i l d)) (length l).
Proof.
  intros A d l f; induction l.
  reflexivity.
  simpl choose; rewrite Mchoice_simpl.
  rewrite Munit_simpl.
  simpl nth; simpl length; rewrite sigma_S_lift.
  apply Uplus_eq_compat; auto.
  rewrite IHl.
  rewrite <- sigma_mult; auto.
  apply sigma_eq_compat; intros.
  rewrite Umult_assoc; apply Umult_eq_compat; auto.
  rewrite <- Nmult_n_Unth.
  rewrite <- Nmult_Umult_assoc_left; auto.
  rewrite Nmult_Umult_assoc_right; auto.
  rewrite Nmult_n_Unthp; try omega.
  auto.
Qed.

Lemma In_nth : forall A (x:A) l, In x l -> exists i, (i < length l)%nat /\ nth i l x = x.
Proof.
  induction l; intros.
  destruct H.
  destruct (in_inv H).
  exists 0%nat; split.
  simpl; auto with arith.
  rewrite H0; reflexivity.
  destruct (IHl H0) as (j,(H1,H2)).
  exists (S j); split.
  simpl; auto with arith.
  auto.
Qed.

Lemma choose_le_Nnth :
  forall A (l:list A) x f alpha,
    In x l ->
    alpha <= f x ->
    [1/](length l) * alpha <= mu (choose l) f.
Proof.
  intros.
  rewrite (choose_uniform x).
  destruct (In_nth x l H) as (i,(H1,H2)).
  transitivity ([1/](length l) * f (nth i l x)).
  rewrite H2; auto.
  pose (F := fun i0 : nat => [1/]length l * f (nth i0 l x)).
  change (F i <= sigma F (length l)).
  apply sigma_le.
  assumption.
Qed.

(** ** List containing elements from [0] to [n] *)

Fixpoint lrange n := match n with
  | O => cons O nil
  | S m => cons (S m) (lrange m)
end.

Lemma range_len : forall n, length (lrange n) = S n.
Proof.
  intro n; induction n.
  reflexivity.
  simpl.
  rewrite IHn; reflexivity.
Qed.

Lemma leq_in_range : forall n x, (x<=n)%nat -> In x (lrange n).
Proof.
  intro n; induction n; intros.
  assert (x=O) by omega.
  rewrite H0; simpl; auto.
  assert (x = S n \/ x <= n)%nat by omega.
  destruct H0.
  rewrite H0; simpl; auto.
  change (lrange (S n)) with (cons (S n) (lrange n)).
  apply in_cons.
  apply IHn.
  assumption.
Qed.
