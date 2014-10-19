Require Export Arith.
Require Export List.
Require Export Multiset.
Require Export OrdEqRelats.
Require Export BinTrees.
  
Set Implicit Arguments.
Unset Strict Implicit.


Module LBinTrees (relat : EqRelatA).
Export relat.
Definition eqA_refl  := equiv_refl  A eqA eqA_equiv.
Definition eqA_sym   := equiv_sym   A eqA eqA_equiv.
Definition eqA_trans := equiv_trans A eqA eqA_equiv.

  
Hint Resolve eqA_refl eqA_sym.
Hint Immediate eqA_dec.
      
Inductive Tree : Set :=
  | Leaf  : Tree
  | Node  : A -> Tree -> Tree -> Tree.

Definition isLeaf (T : Tree) : Prop :=
  match T with
  | Leaf => True
  | Node _ _ _ => False
  end. 

  
Definition emptyBag := EmptyBag A.
Definition singletonBag := SingletonBag _ eqA_dec.
  
Fixpoint contents (T : Tree) : multiset A :=
  match T with
  | Leaf => emptyBag
  | Node a T1 T2 =>
      munion (contents T1) (munion (contents T2) (singletonBag a))
  end.

Definition mult_Tree (T : Tree) (a : A) :=
  multiplicity (contents T) a.
  
Lemma mult_Leaf :
  forall (a : A), mult_Tree Leaf a = 0.
Proof.
  intro a; unfold mult_Tree, multiplicity, contents.
  simpl; auto.
Qed.

Lemma mult_Node :
  forall (a b:A) (T1 T2:Tree),
    mult_Tree (Node b T1 T2) a =
      mult_Tree T1 a + mult_Tree T2 a +
      	multiplicity (singletonBag b) a.
Proof.
  intros; unfold mult_Tree, contents, munion, multiplicity.
  auto with arith.
Qed.
  
Lemma mult_is_zero_dec :
  forall (a : A) (T : Tree),
    { mult_Tree T a = 0 } + { mult_Tree T a > 0 }.
Proof.
intro a; induction T.
 left; unfold mult_Tree, multiplicity, contents.
   simpl; auto with arith.
 elim IHT1; intros.
  elim IHT2; intros.
   elim (eqA_dec a a0).
    intro; right; rewrite mult_Node.
      rewrite a1; rewrite a2; rewrite plus_0_l.
      unfold singletonBag, multiplicity; simpl.
      elim eqA_dec; auto with arith.
     intros; elim b; auto.
    intro; left.
      rewrite mult_Node; rewrite a1; rewrite a2; rewrite plus_0_l.
      unfold multiplicity; simpl; elim eqA_dec; intros; auto with arith.
      elim b; auto with arith.
   right; rewrite mult_Node.
     rewrite a1; rewrite plus_0_l.
     apply le_gt_trans with (mult_Tree T2 a); auto with arith.
  right; rewrite mult_Node.
    apply le_gt_trans with (mult_Tree T1 a); auto with arith.
Qed.
  
Lemma contents_case :
    forall (a b : A) (T1 T2:Tree),
      mult_Tree (Node b T1 T2) a > 0 ->
      	eqA a b \/ mult_Tree T1 a > 0 \/ mult_Tree T2 a > 0.
Proof.
intros.
rewrite mult_Node in H.
elim mult_is_zero_dec with a T1; intros.
 elim mult_is_zero_dec with a T2; intros.
  left.
    rewrite a0 in H; rewrite a1 in H; rewrite plus_0_l in H.
    unfold multiplicity in H; simpl in H.
    generalize H; elim eqA_dec; auto with arith.
    intros; elim lt_irrefl with 0; auto with arith.
  right; right; trivial.
 right; left; trivial.
Qed.	
  
  
Inductive included : Tree -> Tree -> Prop :=
  | leaf_is_included : forall T:Tree, included Leaf T
  | node_is_included : forall (a a': A) (T1 T'1 T2 T'2: Tree),
    eqA a a' -> included T1 T'1 -> included T2 T'2 ->
      included (Node a T1 T2) (Node a' T'1 T'2).


Lemma included_refl :
  forall T:Tree, included T T.
Proof.  
induction T.
 apply leaf_is_included; auto.
 apply node_is_included; auto.
Qed.
    
Lemma included_isLeaf_comp :
  forall T1 T2 : Tree, included T1 T2 ->
    isLeaf T2 -> isLeaf T1.
Proof.  
intros T1 T2 H; elim H; intros; trivial.
unfold isLeaf; auto.
Qed.
  
Lemma included_leaf :
  forall T : Tree, included T Leaf ->
    T = Leaf.
Proof.
intros; assert (isLeaf T).
 apply included_isLeaf_comp with Leaf; auto.
   unfold isLeaf; auto.
 generalize H0; induction T; auto.
  unfold isLeaf; tauto.
Qed.    

Lemma invert_included :
  forall (a a': A) (T1 T'1 T2 T'2: Tree),
    included (Node a T1 T2) (Node a' T'1 T'2)
      ->  eqA a a' /\ included T1 T'1 /\ included T2 T'2.
Proof.
intros; inversion H; auto with datatypes.
Qed.

  
Theorem included_mult_Tree :
  forall T1 T2 : Tree, included T1 T2 ->
    forall a, mult_Tree T1 a <= mult_Tree T2 a.
Proof.
intros; elim H; intros.
 rewrite mult_Leaf; auto with arith.
 do 2 rewrite mult_Node.
   apply le_trans with
     (mult_Tree T'1 a + mult_Tree T3 a + multiplicity (singletonBag a0) a).
  apply plus_le_compat_r; apply plus_le_compat_r; trivial.
  apply le_trans with
    (mult_Tree T'1 a + mult_Tree T'2 a + multiplicity (singletonBag a0) a).
   apply plus_le_compat_r; apply plus_le_compat_l; trivial.
   apply plus_le_compat_l.
     unfold multiplicity; unfold singletonBag; simpl.
     elim eqA_dec; intro.
      elim eqA_dec; intro; auto with arith.
      absurd (eqA a' a); trivial.
      apply eqA_trans with a0; auto.
    auto with arith.
Qed.



Fixpoint shape (T : Tree) : (BinTrees.Tree) :=
  match T with
  | Leaf => BinTrees.Leaf
  | Node _ FG FD => BinTrees.Node (shape FG) (shape FD)
  end. 

Theorem shape_included_comp : 
  forall T1 T2 : Tree, included T1 T2 ->
    BinTrees.included (shape T1) (shape T2).
Proof.
intros T1 T2 inc; elim inc; intros.
  unfold shape at 1; apply BinTrees.leaf_is_included.
  unfold shape; fold shape; apply BinTrees.node_is_included; auto.
Qed.      
  
End LBinTrees.

