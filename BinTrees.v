Require Import Arith.

Section BinTrees.
    
Inductive Tree : Set :=
  | Leaf  : Tree
  | Node  : Tree -> Tree -> Tree.

Definition isLeaf (T : Tree) : Prop :=
  match T with
  | Leaf => True
  | Node _ _ => False
  end. 

Lemma leaf_node :
  forall T1 T2 : Tree, Leaf <> Node T1 T2.
Proof.
unfold not; intros; inversion H.
Qed.

  
Inductive included : Tree -> Tree -> Prop :=
  | leaf_is_included : forall T:Tree, included Leaf T
  | node_is_included : forall T1 T'1 T2 T'2: Tree,
    included T1 T'1 -> included T2 T'2 ->
      included (Node T1 T2) (Node T'1 T'2).


Lemma included_refl :
  forall T:Tree, included T T.
Proof.  
induction T.
 apply leaf_is_included; auto.
 apply node_is_included; auto.
Qed.
      
Lemma included_leaf :
  forall T : Tree, included T Leaf ->
    T = Leaf.
Proof.
intros; inversion H; auto.
Qed.    

Lemma invert_included :
  forall T1 T'1 T2 T'2: Tree,
    included (Node T1 T2) (Node T'1 T'2)
      -> included T1 T'1 /\ included T2 T'2.
Proof.
intros; inversion H; auto.
Qed.


Fixpoint size (T : Tree) : nat :=
  match T with
  | Leaf => O
  | Node FG FD => S ((size FG) + (size FD))
  end. 

Lemma zero_size :
  forall T : Tree, (size T) = 0 -> T = Leaf. 
Proof.
intros T; case T.
 auto.
 unfold size; fold size.
   intros; elim O_S with (size t + size t0); auto.
Qed.    
  
Lemma included_size_comp :
  forall T1 T2 : Tree, included T1 T2 ->
    (size T1) <= (size T2).
Proof.
intros T1 T2 inc; elim inc; intros.
 unfold size at 1; auto with arith.
 unfold size; fold size.
   apply le_n_S; apply plus_le_compat; auto.
Qed.      
  
End BinTrees.
