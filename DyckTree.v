(* We proove the bijection between Dyck words and binary trees *) 

Require Import Arith.
Require Import List.
Require Import BinTrees.
Require Import Dyck.
Require Import ProofIrrelevance.

Section DyckWordTreeBij.

Fixpoint deriv_to_tree (w : list Brace) (deriv : dyck_deriv w) : Tree :=
  match deriv with
    | deriv_nil _ => Leaf
    | deriv_cons a b ga gb w => Node (deriv_to_tree a ga) (deriv_to_tree b gb)
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

Theorem bij_dyck_deriv :
  forall (w : list Brace), dyck_deriv w -> tree_to_dyck ( dyck_to_tree w ) = w.
Proof.
  intros w deriv.
  induction deriv as [ w Hnil | w a b deva Ha devb Hb Hcons ].
  rewrite Hnil.
  rewrite nil_to_leaf; simpl; auto.
  rewrite Hcons; clear Hcons w.
  unfold dyck_to_tree.
  destruct (is_dyck_dec (Open :: a ++ Close :: b)) as [Hd | Hnd].
  destruct (dyck_to_deriv Hd) as [Devnil | a0 b0 deva0 devb0 Hcons0].
  inversion Devnil.
  assert ((a = a0) /\ (b = b0)) as H.
  apply dyck_decompose_unique; auto; apply deriv_to_dyck; assumption.
  decompose [and] H; clear H.
  rewrite Hcons0.
  rewrite H0, H1 in *|-.
  clear Hd Hcons0 deva devb H0 H1 a b.
  simpl.
  unfold dyck_to_tree in Ha.
  destruct (is_dyck_dec a0) as [Hda0 | Hnda0].
  replace (dyck_to_deriv Hda0) with deva0 in Ha.
  rewrite Ha.
  unfold dyck_to_tree in Hb.
  destruct (is_dyck_dec b0) as [Hdb0 | Hndb0].
  replace (dyck_to_deriv Hdb0) with devb0 in Hb.
  rewrite Hb.
  auto.
  apply deriv_unique.
  simpl in Hb.
  rewrite <- Hb in Hndb0.
  unfold is_dyck in Hndb0; simpl in Hndb0; tauto.
  apply deriv_unique.
  simpl in Ha.
  rewrite <- Ha in Hnda0.
  unfold is_dyck in Hnda0; simpl in Hnda0; tauto.
  contradict Hnd.
  apply grammar_is_dyck; apply deriv_to_dyck; auto.
Qed.

Theorem bij_dyck :
  forall (w : list Brace), is_dyck w -> tree_to_dyck ( dyck_to_tree w ) = w.
Proof.
  intros w Hdw.
  apply bij_dyck_deriv.
  apply dyck_to_deriv.
  assumption.
Qed.

Theorem bij_tree :
  forall (t : Tree), dyck_to_tree ( tree_to_dyck t ) = t.
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
  remember (dyck_to_deriv Hd) as deriv.
(*  destruct deriv. *)
  destruct (deriv) as [Devnil | w1 w2 dev1 dev2 Hcons].
  inversion Devnil.
  assert ((w1 = d1) /\ (w2 = d2)) as H.
  apply dyck_decompose_unique; auto; apply deriv_to_dyck; assumption.
  decompose [and] H; clear H.
  subst w1.
  subst w2.
  assert (Hcons = refl_equal (Open :: d1 ++ Close :: d2)) by apply proof_irrelevance.
  subst Hcons.
  unfold dyck_to_tree in IHt1, IHt2.
  destruct (is_dyck_dec d1) as [Hisd1 | Hnisd1].
  destruct (is_dyck_dec d2) as [Hisd2 | Hnisd2].
  replace Hisd1 with Hd1 in * |- ; [auto | apply proof_irrelevance] .
  replace Hisd2 with Hd2 in * |- ; [auto | apply proof_irrelevance] .
  clear Hisd1 Hisd2.
  assert (dev1 = (dyck_to_deriv Hd1)) by apply deriv_unique.
  assert (dev2 = (dyck_to_deriv Hd2)) by apply deriv_unique.
  subst dev1; subst dev2.
  simpl.
  rewrite IHt1, IHt2.
  reflexivity.
  contradiction.
  contradiction.
  intro H; contradict H; apply grammar_is_dyck; auto.
Qed.

Theorem bij_tree_size:
  forall (t : Tree), 2 * (size t) = length (tree_to_dyck t).
Proof.
  induction t.
  simpl; auto.
  simpl.
  rewrite app_length.
  simpl.
  rewrite <- IHt1, <- IHt2.
  omega.
Qed.

Theorem bij_derive_size:
  forall (w : list Brace) (deriv : dyck_deriv w),
    length w = 2* (size (deriv_to_tree w deriv)).
Proof.
  induction deriv.
  rewrite e; simpl; auto.
  rewrite e; simpl.
  rewrite app_length; simpl.
  rewrite IHderiv1, IHderiv2.
  omega.
Qed.

Theorem bij_dyck_size:
  forall (w : list Brace), (is_dyck w) -> 2 * (size (dyck_to_tree w)) = length w.
Proof.
  intros w Hdw.
  unfold dyck_to_tree.
  elim (is_dyck_dec w).
  intro pf.
  symmetry.
  apply bij_derive_size.
  contradiction.
Qed.


End DyckWordTreeBij.


Require Import Wf_nat.
Extraction Inline Wf_nat.lt_wf_rec1 Wf_nat.lt_wf_rec
  Wf_nat.lt_wf_ind Wf_nat.gt_wf_rec Wf_nat.gt_wf_ind.

Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive prod => "(*)"  [ "(,)" ].

Extraction "extract/dycktree.ml" dyck_to_tree tree_to_dyck.
