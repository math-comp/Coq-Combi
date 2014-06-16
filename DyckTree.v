(* We proove the bijection between Dyck words and binary trees *)

Require Import Arith.
Require Import List.
Require Import BinTrees.
Require Import Dyck.
Require Import ProofIrrelevance.

Section DyckWordTreeBij.

Inductive tree_is_deriv (t : Tree) (w : list Brace) : Prop :=
  | tree_nil : t = Leaf -> w = nil -> tree_is_deriv t w
  | tree_cons : forall (t1 t2 : Tree) (w1 w2 : list Brace),
      t = Node t1 t2 -> w = Open :: w1 ++ Close :: w2 ->
        tree_is_deriv t1 w1 -> tree_is_deriv t2 w2 -> tree_is_deriv t w.

Theorem tree_deriv_is_dyck :
  forall (t : Tree) (w : list Brace), tree_is_deriv t w -> is_dyck w.
Proof.
  intros t w d; unfold is_dyck.
  induction d.
  rewrite H0; simpl; auto.
  rewrite H0; apply grammar_is_dyck; auto.
Qed.

Definition dyck_has_tree (w : list Brace) :=
  is_dyck w -> { t: Tree | tree_is_deriv t w }.


Lemma dyck_has_tree_rec :
  forall w : list Brace,
    (forall s : list Brace, length s < length w -> dyck_has_tree s) ->
    dyck_has_tree w.
Proof.
  unfold dyck_has_tree.
  intros w Hind.
  destruct w; intros H.
  exists Leaf; apply tree_nil; auto.

  elim dyck_decompose_grammar with (b :: w); auto with datatypes.
  intro x; elim x; clear x; intros w1 w2.
  intro H0; decompose [and] H0; clear H0.
  rewrite H4 in *|-*; clear H H4.
  elim Hind with w1; auto.
  intros t1 Hdev1.
  elim Hind with w2; auto.
  intros t2 Hdev2.
  exists (Node t1 t2).
  apply tree_cons with t1 t2 w1 w2; auto.
  apply dyck_grammar_length_2 with w1; simpl; auto.
  apply dyck_grammar_length_1 with w2; simpl; auto.
Qed.

Definition R (a b:list Brace) := length a < length b.
Lemma Rwf : well_founded R.
  apply Wf_nat.well_founded_ltof.
Qed.

Definition all_dyck_has_tree : forall x : list Brace, dyck_has_tree x
  := Fix Rwf dyck_has_tree dyck_has_tree_rec.


Theorem dyck_tree_unique :
  forall (t u : Tree) (w : list Brace),
    tree_is_deriv t w -> tree_is_deriv u w -> t = u.
Proof.
  induction t.
  induction u.
  auto.
  intros w Hdlw Hdnw.
  destruct Hdlw; destruct Hdnw.
  inversion H1.
  rewrite H0 in H2; inversion H2.
  rewrite H0 in H2; inversion H2.
  inversion H.
  intros u w devNode devu.
  destruct devNode.
  inversion H.
  inversion H.
  destruct devu.
  rewrite H0 in H4; inversion H4.
  assert (w1 = w0 /\ w2 = w3).
  apply dyck_decompose_unique; auto.
  apply tree_deriv_is_dyck with t0; assumption.
  apply tree_deriv_is_dyck with t3; assumption.
  apply tree_deriv_is_dyck with t4; assumption.
  apply tree_deriv_is_dyck with t5; assumption.
  rewrite <- H0, <- H4; auto.
  decompose [and] H5; clear H5.
  subst w1.
  subst w2.
  subst t0.
  subst t3.
  clear H H0.
  rewrite H1; clear H1.
  rewrite IHt1 with t4 w0; auto.
  rewrite IHt2 with t5 w3; auto.
Qed.

Definition dyck_to_tree (w : list Brace) : Tree :=
  match is_dyck_dec w with
     | left proof => let (t, _) := (all_dyck_has_tree w proof) in t
     | right _ => Leaf
  end.

Lemma nil_to_leaf : dyck_to_tree nil = Leaf.
Proof.
  unfold dyck_to_tree; simpl.
  destruct (is_dyck_dec nil); auto.
  elim all_dyck_has_tree with nil.
  clear i.
  intros t H.
  destruct H; auto.
  inversion H0.
Qed.


Fixpoint tree_to_dyck (t : Tree) : list Brace :=
  match t with
  | Leaf => nil
  | Node FG FD => Open :: (tree_to_dyck FG) ++ Close :: (tree_to_dyck FD)
  end.

Lemma tree_to_dyck_deriv_eq :
  forall (t : Tree) (w : list Brace), tree_is_deriv t w -> tree_to_dyck t = w.
Proof.
  induction t; destruct w; auto; intro H; destruct H.
  inversion H0.
  inversion H.
  inversion H.
  inversion H0.
  inversion H0.
  rewrite H0; clear H0 b w.
  inversion H; clear H.
  subst t0.
  subst t3.
  simpl.
  rewrite IHt1 with w1 by apply H1.
  rewrite IHt2 with w2 by apply H2.
  reflexivity.
Qed.

Lemma tree_to_dyck_eq_deriv :
  forall (t : Tree) (w : list Brace), tree_to_dyck t = w -> tree_is_deriv t w.
Proof.
  induction t; auto.
  destruct w.
  simpl; apply tree_nil; auto.
  simpl.
  intro H; inversion H.
  simpl.
  intros t w.
  rewrite <- w; clear w.
  apply tree_cons with t1 t2 (tree_to_dyck t1) (tree_to_dyck t2); auto.
Qed.

Lemma tree_to_dyck_is_dyck :
  forall (t : Tree), is_dyck (tree_to_dyck t).
Proof.
  induction t.
  unfold is_dyck; simpl; auto.
  simpl.
  apply grammar_is_dyck; auto.
Qed.

Theorem bij_dyck :
  forall w : list Brace, is_dyck w -> tree_to_dyck ( dyck_to_tree w ) = w.
Proof.
  intros w Hd.
  unfold dyck_to_tree.
  destruct is_dyck_dec with w; [ | tauto].
  destruct w.
  elim all_dyck_has_tree with nil.
  clear i Hd.
  intros t H.
  destruct t; auto.
  destruct H.
  inversion H.
  inversion H0.
  clear Hd.
  induction all_dyck_has_tree with (b :: w).
  apply tree_to_dyck_deriv_eq; auto.
Qed.


Theorem bij_tree :
  forall t : Tree, dyck_to_tree ( tree_to_dyck t ) = t.
Proof.
  induction t.
  simpl; apply nil_to_leaf.
  simpl.
  specialize tree_to_dyck_is_dyck with t1; intro Hd1.
  specialize tree_to_dyck_is_dyck with t2; intro Hd2.
  remember (tree_to_dyck t1) as d1.
  remember (tree_to_dyck t2) as d2.
  unfold dyck_to_tree.
  elim (is_dyck_dec (Open :: d1 ++ Close :: d2)).
  intro Hd.
  induction all_dyck_has_tree with (Open :: d1 ++ Close :: d2).
  destruct p.
  inversion H0.
  rewrite H; clear H x.
  assert ((w1 = d1) /\ (w2 = d2)) as Heq.
  apply dyck_decompose_unique; auto.
  apply tree_deriv_is_dyck with t0; assumption.
  apply tree_deriv_is_dyck with t3; assumption.
  decompose [and] Heq; clear Heq.
  subst w1.
  subst w2.
  clear H0 Hd Hd1 Hd2.
  replace t0 with t1.
  replace t3 with t2.
  reflexivity.
  apply dyck_tree_unique with d2; auto.
  apply tree_to_dyck_eq_deriv; auto.
  apply dyck_tree_unique with d1; auto.
  apply tree_to_dyck_eq_deriv; auto.
  intro H; contradict H; apply grammar_is_dyck; auto.
Qed.


Theorem bij_tree_size:
  forall t : Tree, 2 * (size t) = length (tree_to_dyck t).
Proof.
  induction t.
  simpl; auto.
  simpl.
  rewrite app_length.
  simpl.
  rewrite <- IHt1, <- IHt2.
  omega.
Qed.

Theorem bij_dyck_deriv_size:
  forall (t : Tree) (w : list Brace), tree_is_deriv t w -> 2 * (size t) = length w.
Proof.
  induction t.
  destruct w.
  intro H; simpl; auto.
  intro H; destruct H.
  inversion H0.
  inversion H.
  intros w H.
  destruct H.
  inversion H.
  inversion H; clear H.
  subst t0 t3.
  rewrite H0; clear H0.
  simpl.
  rewrite app_length; simpl.
  rewrite <- IHt1, <- IHt2; auto.
  omega.
Qed.


Theorem bij_dyck_size:
  forall w : list Brace, is_dyck w -> 2 * (size (dyck_to_tree w)) = length w.
Proof.
  intros w Hdw.
  unfold dyck_to_tree.
  elim (is_dyck_dec w).
  intro pf.
  elim all_dyck_has_tree with w.
  intro t; apply bij_dyck_deriv_size; auto.
  intro H; tauto.
Qed.

End DyckWordTreeBij.


Require Import Wf_nat.
Extraction Inline Wf_nat.lt_wf_rec1 Wf_nat.lt_wf_rec
  Wf_nat.lt_wf_ind Wf_nat.gt_wf_rec Wf_nat.gt_wf_ind.

Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive prod => "(*)"  [ "(,)" ].

Extraction "extract/dycktree.ml" dyck_to_tree tree_to_dyck.
