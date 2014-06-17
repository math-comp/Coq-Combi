Require Import Arith.
Require Import Dyck.
Require Import DyckTree.
Require Import ListOfBinTrees.
Require Import Relation_Definitions.

Section ListOfDyck.

Let eq_list_brace_equiv := {|
                       equiv_refl := fun x : list Brace => eq_refl;
                       equiv_trans := fun x y z : list Brace => eq_trans (z:=z);
                       equiv_sym := fun y y : list Brace => eq_sym (y:=y)
                     |}.

Let eq_list_brace_dec := list_eq_dec eq_brace_dec.

Theorem list_of_dyck :
  forall n : nat,
    list_of_set (list Brace)
                (fun w : list Brace => is_dyck w /\ (length w) = 2*n)
                (eq (A := list Brace))
                eq_list_brace_dec.
Proof.
  intro n.
  apply list_of_image with _ (eq (A := Tree)) eq_tree_dec (fun t : Tree => size t = n)
    tree_to_dyck.
  apply eq_list_brace_equiv.
  intros x y H Heq; rewrite <- Heq; assumption.
  intros t Hsz.
  split.
  apply tree_to_dyck_is_dyck.
  rewrite <- Hsz; symmetry; apply bij_tree_size.
  intros t H; decompose [and] H; clear H.
  assert (2* (size t) = 2 * n).
  rewrite <- H1; apply bij_tree_size.
  omega.
  intros x y H; rewrite H; reflexivity.
  apply tree_to_dyck_inj.
  intros w H; decompose [and] H; clear H H1.
  apply brace_dyck_to_tree; assumption.
  intro b.
  destruct (is_dyck_dec b).
  destruct (eq_nat_dec (length b) (2*n)).
  left; auto.
  right; omega.
  right; tauto.
  apply list_of_trees.
Defined.

End ListOfDyck.
