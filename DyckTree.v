Require Import Arith.
Require Import List.
Require Import BinTrees.
Require Import Dyck.
Require Import ProofIrrelevance.

Section DyckWordTreeBij.

Fixpoint deriv_to_tree (w : list Brace) (deriv : dyck_deriv w) : Tree :=
  match deriv with
    | grammar_nil _ => Leaf
    | grammar_cons a b ga gb w => Node (deriv_to_tree a ga) (deriv_to_tree b gb)
  end.

Definition dyck_to_tree (w : list Brace) : Tree :=
  match is_dyck_dec w with
     | left proof => deriv_to_tree w (dyck_to_deriv proof)
     | right _ => Leaf
  end.

Lemma nil_to_leaf : dyck_to_tree nil = Leaf.
Proof.
  unfold dyck_to_tree; simpl.
  case (is_dyck_dec nil).
  intro i; simpl.
  unfold deriv_to_tree.
  destruct (dyck_to_deriv i).
  simpl; auto.
  inversion e.
  intro; auto.
Qed.

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

Theorem bij_1_aux :
  forall (w : list Brace), dyck_deriv w -> tree_to_dyck ( dyck_to_tree w ) = w.
Proof.
  intros w deriv.
  induction deriv.
  rewrite e.
  rewrite nil_to_leaf; simpl; auto.
  rewrite e; clear e; clear w.
  unfold dyck_to_tree.
  destruct (is_dyck_dec (Open :: a ++ Close :: b)).
  destruct (dyck_to_deriv i).
  inversion e.
  assert ((a = a0) /\ (b = b0)).
  apply dyck_decompose_unique; auto; apply deriv_to_dyck; assumption.
  decompose [and] H; clear H.
  rewrite e.
  rewrite H0 in IHderiv1.
  rewrite H1 in IHderiv2.
  clear i e deriv1 deriv2 H0 H1 a b.
  simpl.
  unfold dyck_to_tree in IHderiv1.
  destruct (is_dyck_dec a0).
  replace (dyck_to_deriv i) with d1 in IHderiv1.
  rewrite IHderiv1.
  unfold dyck_to_tree in IHderiv2.
  destruct (is_dyck_dec b0).
  replace (dyck_to_deriv i0) with d2 in IHderiv2.
  rewrite IHderiv2.
  auto.
  apply deriv_unique.
  simpl in IHderiv2.
  rewrite <- IHderiv2 in n.
  unfold is_dyck in n; simpl in n; tauto.
  apply deriv_unique.
  simpl in IHderiv1.
  rewrite <- IHderiv1 in n.
  unfold is_dyck in n; simpl in n; tauto.
  contradict n.
  apply grammar_is_dyck; apply deriv_to_dyck; auto.
Qed.

Theorem bij_1 :
  forall (w : list Brace), is_dyck w -> tree_to_dyck ( dyck_to_tree w ) = w.
Proof.
  intros w Hdw.
  apply bij_1_aux.
  apply dyck_to_deriv.
  assumption.
Qed.

Theorem bij_2 :
  forall (t : Tree), dyck_to_tree ( tree_to_dyck t ) = t.
Proof.
  induction t.
  simpl; apply nil_to_leaf.
  simpl.
  specialize tree_to_dyck_is_dyck with t1; intro Hd1.
  remember (tree_to_dyck t1) as d1.
  specialize tree_to_dyck_is_dyck with t2; intro Hd2.
  remember (tree_to_dyck t2) as d2.
  unfold dyck_to_tree.
  elim (is_dyck_dec (Open :: d1 ++ Close :: d2)).
  intro Hd.
  remember (dyck_to_deriv Hd) as deriv.
  destruct deriv.
  inversion e.
  assert ((a = d1) /\ (b = d2)) as H.
  apply dyck_decompose_unique; auto; apply deriv_to_dyck; assumption.
  decompose [and] H; clear H.
  subst a.
  subst b.
  assert (e = refl_equal (Open :: d1 ++ Close :: d2)) by apply proof_irrelevance.
  subst e.
  unfold dyck_to_tree in IHt1, IHt2.
  destruct (is_dyck_dec d1) as [Hisd1 | Hnisd1].
  destruct (is_dyck_dec d2) as [Hisd2 | Hnisd2].
  replace Hisd1 with Hd1 in * |- ; [auto | apply proof_irrelevance] .
  replace Hisd2 with Hd2 in * |- ; [auto | apply proof_irrelevance] .
  clear Hisd1 Hisd2.
  assert (deriv1 = (dyck_to_deriv Hd1)) by apply deriv_unique.
  assert (deriv2 = (dyck_to_deriv Hd2)) by apply deriv_unique.
  subst deriv1; subst deriv2.
  simpl.
  rewrite IHt1, IHt2.
  reflexivity.
  contradiction.
  contradiction.
  intro H; contradict H; apply grammar_is_dyck; auto.
Qed.

End DyckWordTreeBij.
