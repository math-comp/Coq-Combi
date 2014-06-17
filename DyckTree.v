(* We proove the bijection between Dyck words and binary trees *)

Require Import Arith.
Require Import List.
Require Import BinTrees.
Require Import Dyck.
Require Import ProofIrrelevance.

Section DyckWordTreeBij.

Fixpoint tree_to_dyck (t : Tree) : list Brace :=
  match t with
  | Leaf => nil
  | Node FG FD => Open :: (tree_to_dyck FG) ++ Close :: (tree_to_dyck FD)
  end.

Lemma tree_to_dyck_is_dyck :
  forall (t : Tree), is_dyck (tree_to_dyck t).
Proof.
  induction t.
  unfold is_dyck; simpl; auto.
  simpl.
  apply grammar_is_dyck; auto.
Qed.


Definition brace_dyck_has_tree (w : list Brace) :=
  is_dyck w -> { t: Tree | tree_to_dyck t = w }.

Lemma brace_dyck_has_tree_rec :
  forall w : list Brace,
    (forall s : list Brace, length s < length w -> brace_dyck_has_tree s) ->
    brace_dyck_has_tree w.
Proof.
  unfold brace_dyck_has_tree.
  destruct w.
  exists Leaf; auto.

  intros Hind H.
  destruct dyck_decompose_grammar with (b :: w) as (x, H0); auto with datatypes.
  destruct x as (w1, w2).
  decompose [and] H0; clear H0.
  rewrite H4 in *; clear H H4 b w.
  destruct Hind with w1 as (t1, Hdev1); auto.
  apply dyck_grammar_length_1 with w2; simpl; auto.
  destruct Hind with w2 as (t2, Hdev2); auto.
  apply dyck_grammar_length_2 with w1; simpl; auto.
  exists (Node t1 t2).
  simpl; rewrite Hdev1, Hdev2; auto.
Defined.

Definition R (a b:list Brace) := length a < length b.
Lemma Rwf : well_founded R.
  apply Wf_nat.well_founded_ltof.
Qed.

Definition brace_dyck_to_tree : forall x : list Brace, brace_dyck_has_tree x
  := Fix Rwf brace_dyck_has_tree brace_dyck_has_tree_rec.

Theorem tree_to_dyck_inj :
  forall t u : Tree, tree_to_dyck t = tree_to_dyck u -> t = u.
Proof.
  induction t.
  destruct u; auto.
  intro H; simpl in H; inversion H.

  destruct u.
  intro H; simpl in H; inversion H.

  simpl; intro H.
  destruct dyck_decompose_unique with
    (tree_to_dyck t1) (tree_to_dyck t2) (tree_to_dyck u1) (tree_to_dyck u2);
    try apply tree_to_dyck_is_dyck.
  exact H.
  rewrite IHt1 with u1; auto.
  rewrite IHt2 with u2; auto.
Qed.


Definition dyck_to_tree (w : list Brace) : Tree :=
  match is_dyck_dec w with
     | left proof => let (t, _) := (brace_dyck_to_tree w proof) in t
     | right _ => Leaf
  end.

Lemma nil_to_Leaf : dyck_to_tree nil = Leaf.
Proof.
  unfold dyck_to_tree.
  destruct (is_dyck_dec nil) as [Hnil | _]; auto.
  destruct (brace_dyck_to_tree nil Hnil) as (t, H).
  destruct t; auto.
  simpl in H; inversion H.
Qed.

Theorem bij_tree :
  forall t : Tree, dyck_to_tree ( tree_to_dyck t ) = t.
Proof.
  destruct t.
  simpl; rewrite nil_to_Leaf; auto.
  unfold dyck_to_tree.
  destruct (is_dyck_dec (tree_to_dyck (Node t1 t2))) as [Hd | Hnd].
  destruct (brace_dyck_to_tree (tree_to_dyck (Node t1 t2)) Hd).
  apply tree_to_dyck_inj; auto.
  contradict Hnd.
  apply tree_to_dyck_is_dyck.
Qed.

Theorem bij_dyck :
  forall w : list Brace, is_dyck w -> tree_to_dyck ( dyck_to_tree w ) = w.
Proof.
  intros w Hd.
  destruct w.
  rewrite nil_to_Leaf; auto.
  unfold dyck_to_tree.
  destruct is_dyck_dec with (b :: w) as [Hd1 | Hnd1]; [ | exfalso; auto ].
  clear Hd.
  destruct (brace_dyck_to_tree (b :: w) Hd1).
  assumption.
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
  ring.
Qed.

Theorem bij_dyck_size:
  forall w : list Brace, is_dyck w -> 2 * (size (dyck_to_tree w)) = length w.
Proof.
  intros w Hdw.
  unfold dyck_to_tree.
  destruct (is_dyck_dec w) as [Hd | Hnd]; [ | exfalso; auto ].
  clear Hdw.
  destruct (brace_dyck_to_tree w Hd) as (t, Heq).
  rewrite <- Heq.
  apply bij_tree_size.
Qed.

End DyckWordTreeBij.


Require Import Wf_nat.
Extraction Inline Wf_nat.lt_wf_rec1 Wf_nat.lt_wf_rec
  Wf_nat.lt_wf_ind Wf_nat.gt_wf_rec Wf_nat.gt_wf_ind.

Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive prod => "(*)"  [ "(,)" ].

Extraction "extract/dycktree.ml" dyck_to_tree tree_to_dyck.
