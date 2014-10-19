Require Export Permutation.
Require Export Sorting.
Require Export OrdEqRelats.
Require Export LBTrees.
Require Export Coq.Sorting.PermutSetoid.

Set Implicit Arguments.
Unset Strict Implicit.

Module BinSearchTrees (relat : OrdEqRelatA).
Module LBinTreeMod := (LBinTrees relat.eqrelat).
Export LBinTreeMod.
Export relat.

Definition gtA (x y:A) := ~ leA x y.


Hint Resolve leA_refl eqA_refl.
Hint Immediate eqA_dec leA_total_dec leA_dec leA_antisym.

Lemma gt_eqA_dec :
  forall a b : A,
    gtA b a ->
      (if eqA_dec a b then 1 else 0) = 0.
Proof.
unfold gtA; intros; elim eqA_dec; intros; auto with arith.
elim H; apply leA_refl; apply eqA_sym; auto.
Qed.



Definition le_Tree (T : Tree) (a:A) :=
  forall (b : A), gtA b a -> mult_Tree T b = 0.

Definition lt_Tree (a:A) (T : Tree) :=
  forall (b : A), leA b a -> mult_Tree T b = 0.


Lemma le_Tree_contrap :
  forall (T : Tree) (a:A),
    le_Tree T a ->
      forall (b : A), mult_Tree T b > 0 -> leA b a.
Proof.
unfold le_Tree; intros.
 elim leA_dec with b a; auto; intros.
   absurd (mult_Tree T b = 0).
  apply sym_not_eq; apply lt_O_neq; auto with arith.
  apply H; unfold gtA; auto.
Qed.

Lemma le_Tree_contrap_rev :
  forall (T : Tree) (a:A),
    (forall (b : A), mult_Tree T b > 0 -> leA b a) ->
      le_Tree T a.
Proof.
unfold le_Tree; intros.
 elim mult_is_zero_dec with b T; intros; auto.
   absurd (leA b a); auto.
Qed.


Lemma lt_Tree_contrap :
  forall (a:A) (T : Tree),
    lt_Tree a T ->
      forall (b : A), mult_Tree T b > 0 -> gtA b a.
Proof.
unfold lt_Tree; intros.
 elim leA_dec with b a; auto; intros.
   absurd (mult_Tree T b = 0).
  apply sym_not_eq; apply lt_O_neq; auto with arith.
  apply H; auto.
Qed.

Lemma lt_Tree_contrap_rev :
  forall (a:A) (T : Tree),
    (forall (b : A), mult_Tree T b > 0 -> gtA b a) ->
      lt_Tree a T.
Proof.
unfold lt_Tree; intros.
 elim mult_is_zero_dec with b T; intros; auto.
   absurd (leA b a); auto.
  apply H; unfold gtA; auto.
Qed.

Lemma le_Tree_comp :
    forall (a b : A) (T : Tree),
      leA a b ->  le_Tree T a -> le_Tree T b.
Proof.
unfold le_Tree, gtA; intros.
apply H0.
red in H1; red; intros; apply H1.
apply leA_trans with a; trivial.
Qed.

Lemma lt_Tree_comp :
    forall (a b : A) (T : Tree),
      leA a b ->  lt_Tree b T  -> lt_Tree a T .
Proof.
unfold lt_Tree; intros.
apply H0.
apply leA_trans with a; trivial.
Qed.



Inductive is_bst : Tree -> Prop :=
  | leaf_is_bst : is_bst Leaf
  | node_is_bst :
    forall (a : A) (T1 T2 : Tree),
      (is_bst T1) -> (is_bst T2) ->
      (le_Tree T1 a) -> (lt_Tree a T2) ->
        is_bst (Node a T1 T2).
Hint Constructors is_bst.


Lemma invert_bst :
  forall (a : A) (T1 T2 : Tree),
    is_bst (Node a T1 T2) ->
    (is_bst T1) /\ (is_bst T2) /\ (le_Tree T1 a) /\ (lt_Tree a T2).
Proof.
intros; inversion H; auto with datatypes.
Qed.

Lemma is_bst_rec :
 forall P:Tree -> Set,
   P Leaf ->
    (forall (a : A) (T1 T2 : Tree),
      (is_bst T1) -> (P T1) ->
      (is_bst T2) -> (P T2) ->
      (le_Tree T1 a) -> (lt_Tree a T2) ->
      	P (Node a T1 T2)) ->
  forall T : Tree, is_bst T -> P T.
Proof.
simple induction T; auto with datatypes.
intros a G PG D PD PN.
elim (invert_bst PN); auto with datatypes.
intros H1 H2; decompose [and] H2.
apply H0; auto with datatypes.
Qed.


(* Fast computation of the multiplicity *)

Inductive mult_bst_spec (T : Tree) (a:A) : Set :=
  mult_exists :
    forall (n : nat), n = mult_Tree T a -> mult_bst_spec T a.

Theorem mult_bst :
  forall (T : Tree) (a:A),
    is_bst T -> mult_bst_spec T a.
Proof.
intros T a bst; elim bst.
 apply mult_exists with 0.
   auto with datatypes.
 unfold mult_Tree; auto.
   intros; elim (leA_dec a a0); intros.
  clear H2; elim H0; intros.
    elim (eqA_dec a a0); intros.
   apply mult_exists with (n + 1).
     rewrite mult_Node; rewrite <- e.
     assert (mult_Tree T2 a = 0); auto.
     rewrite H2; unfold multiplicity; simpl.
     elim (eqA_dec a0 a); auto.
     intro; elim b; auto.
   apply mult_exists with n.
     rewrite mult_Node; rewrite <- e.
     assert (mult_Tree T2 a = 0); auto.
     rewrite H2; unfold multiplicity; simpl.
     elim (eqA_dec a0 a); auto.
    intro; elim b; auto.
    rewrite plus_0_r; rewrite plus_0_r; auto.
  elim H2; intros.
    apply mult_exists with n.
    rewrite mult_Node; rewrite <- e.
    assert (mult_Tree T1 a = 0); auto.
    rewrite H5; unfold multiplicity; simpl.
    elim (eqA_dec a0 a); auto.
    intro; elim b; auto.
Qed.




Lemma compare_roots_l :
  forall (a b: A) (T1 T2 T3:Tree),
    is_bst (Node a (Node b T1 T2) T3) ->
      leA b a.
Proof.
intros; elim (invert_bst H).
intros; decompose [and] H1.
apply le_Tree_contrap with (Node b T1 T2); auto.
rewrite mult_Node.
apply le_gt_trans with (multiplicity (singletonBag b) b); auto with arith.
unfold singletonBag, multiplicity; simpl; auto.
elim eqA_dec with b b; intros; auto.
elim b0; apply eqA_refl.
Qed.

Lemma compare_roots_r :
  forall (a b: A) (T1 T2 T3:Tree),
    is_bst (Node a T1 (Node b T2 T3)) ->
      gtA b a.
Proof.
intros; elim (invert_bst H).
intros; decompose [and] H1.
apply lt_Tree_contrap with (Node b T2 T3); auto.
rewrite mult_Node.
apply le_gt_trans with (multiplicity (singletonBag b) b); auto with arith.
unfold singletonBag, multiplicity; simpl; auto.
elim eqA_dec with b b; intros; auto.
elim b0; apply eqA_refl.
Qed.

Lemma bst_sort_twist1 :
  forall c0 c1 c2 ca0 : multiset A,
    meq c0 (munion c1 ca0) ->
      meq (munion c0 c2)
      	  (munion (munion c1 c2) ca0).
Proof.
intros.
apply meq_trans with (munion (munion c1 ca0) c2).
 apply meq_left; auto.
 apply meq_trans with (munion c1 (munion ca0 c2)).
  apply munion_ass.
  apply meq_trans with (munion c1 (munion c2 ca0)).
   apply meq_right.
     apply munion_comm; auto.
   apply meq_sym; apply munion_ass.
Qed.

Lemma bst_sort_twist2 :
  forall c0 c1 c2 ca ca0 : multiset A,
    meq c0 (munion c2 ca0) ->
      meq (munion c1 (munion c0 ca))
      	  (munion (munion c1 (munion c2 ca)) ca0).
Proof.
intros.
apply meq_trans with (munion c1 (munion (munion c2 ca0) ca)).
 apply meq_right; apply meq_left; auto.
 apply meq_trans with (munion c1 (munion (munion c2 ca) ca0)).
  apply meq_right.
    apply meq_trans with (munion c2 (munion ca ca0)).
   apply meq_trans with (munion c2 (munion ca0 ca)).
    apply munion_ass.
    apply meq_right; apply munion_comm.
   apply meq_sym; apply munion_ass.
  apply meq_sym; apply munion_ass.
Qed.



Inductive insert_spec (a : A) (T : Tree) : Set :=
    insert_exist :
      forall T1 : Tree,
        is_bst T1 -> included T T1 ->
        meq (contents T1) (munion (contents T) (singletonBag a)) ->
          insert_spec a T.

Lemma insert : forall T:Tree,
  is_bst T -> forall a:A, insert_spec a T.
Proof.
simple induction 1; intros.
 apply insert_exist with (Node a Leaf Leaf);
  auto with datatypes.
  apply node_is_bst; auto.
   unfold le_Tree; intros; auto.
   unfold lt_Tree; intros; auto.
  apply leaf_is_included.
 elim (leA_dec a0 a); intro.
  elim H1 with a0; intros.
    apply insert_exist with (Node a T0 T2); auto with datatypes.
   apply node_is_bst; auto.
     unfold le_Tree; intros; unfold mult_Tree.
     unfold meq in m.
     rewrite (m b).
     unfold munion; simpl.
     assert (multiplicity (contents T1) b = 0).
    fold (mult_Tree T1 b); auto.
    rewrite H7; rewrite plus_0_l.
      apply gt_eqA_dec; unfold gtA in H6; unfold gtA, not; intros.
      apply H6; apply leA_trans with a0; auto;
      	apply leA_refl; apply eqA_sym; auto.
   apply node_is_included; auto.
     apply included_refl.
   unfold contents; fold contents.
     apply bst_sort_twist1; auto.
  elim H3 with a0; intros.
    apply insert_exist with (Node a T1 T0); auto with datatypes.
   apply node_is_bst; auto.
     unfold lt_Tree; intros; unfold mult_Tree.
     unfold meq in m.
     rewrite (m b0).
     unfold munion; simpl.
     assert (multiplicity (contents T2) b0 = 0).
    fold (mult_Tree T2 b0); auto.
    rewrite H7; rewrite plus_0_l.
    elim (eqA_dec a0 b0); intros; auto.
    elim b.
    apply leA_trans with b0; auto; apply leA_refl; auto.
  apply node_is_included; auto.
     apply included_refl.
  unfold contents; fold contents.
     apply bst_sort_twist2; auto.
Qed.


(** building a bst from a list *)

Inductive build_bst (l : list A) : Set :=
    bst_exist :
      forall T : Tree,
        is_bst T ->
        meq (list_contents _ eqA_dec l) (contents T) -> build_bst l.

Lemma list_to_bst : forall l:list A, build_bst l.
Proof.
simple induction l.
 apply (bst_exist (l:=nil) leaf_is_bst); auto with datatypes.
 simple induction 1.
   intros T i m; elim (insert i a).
   intros; apply bst_exist with T1; simpl; auto with datatypes.
   apply meq_trans with (munion (contents T) (singletonBag a)).
  apply meq_trans with (munion (singletonBag a) (contents T)).
   apply meq_right; trivial with datatypes.
   apply munion_comm.
  apply meq_sym; trivial with datatypes.
Qed.


(** building the sorted list *)

Inductive flat_spec (T : Tree) : Set :=
    flat_exist :
      forall l:list A,
        sort leA l ->
        meq (contents T) (list_contents _ eqA_dec l) -> flat_spec T.


Lemma le_Tree_list :
  forall (a : A) (T : Tree) (l : list A),
    meq (contents T) (list_contents eqA eqA_dec l) ->
      lt_Tree a T -> lelistA leA a l.
Proof.
intros a T; induction l; intros; auto with datatypes.
assert (leA a a0).
 assert (gtA a0 a).
  apply lt_Tree_contrap with T; auto.
    unfold meq in H.
    unfold mult_Tree; rewrite (H a0).
    unfold list_contents; simpl.
    apply le_gt_trans with (if eqA_dec a0 a0 then 1 else 0).
   auto with arith.
   elim (eqA_dec a0 a0); auto.
    intro; elim b; apply eqA_refl.
  elim (leA_dec a a0); auto.
    intros.
    unfold gtA in H1.
    elim (leA_total_dec a a0); auto.
    intro; elim H1; auto.
 auto with datatypes.
Qed.


Lemma conc_sorted :
  forall (l1 l2 : list A),
    sort leA l1 -> sort leA l2 ->
    (forall x : A,
       multiplicity (list_contents eqA eqA_dec l1) x > 0 ->
       lelistA leA x l2) ->
  sort leA (l1++l2).
Proof.
induction l1; intros; auto.
simpl.
apply cons_sort.
 apply IHl1; trivial.
  elim (sort_inv H); intros; auto.
  intros.
    apply H1.
    unfold list_contents, multiplicity; fold list_contents; simpl.
    apply le_gt_trans with (multiplicity (list_contents eqA eqA_dec l1) x).
   unfold list_contents; fold list_contents; simpl.
     auto with arith.
   trivial.
 induction l1.
  simpl.
    apply H1.
    unfold list_contents; simpl.
    elim eqA_dec; intros; auto.
    elim b; apply eqA_refl; auto.
  simpl; apply cons_leA.
    elim (sort_inv H); intros.
    apply (lelistA_inv H3); intros; auto.
Qed.


Lemma bst_to_list : forall T : Tree, is_bst T -> flat_spec T.
Proof.
  intros T h; elim h; intros.
  apply flat_exist with (nil (A:=A)); auto with datatypes.
  elim H0; intros l1 s1 m1; elim H2; intros l2 s2 m2.
  apply flat_exist with (l1 ++ (a :: l2)); simpl; auto with datatypes.
  apply conc_sorted; auto.
   apply cons_sort; auto.
     apply le_Tree_list with T2; auto.
   intros; apply cons_leA.
     apply le_Tree_contrap with T1; auto.
     unfold meq in m1; unfold mult_Tree; rewrite m1; auto.
  apply meq_trans with
      (munion (list_contents _ eqA_dec l1)
         (munion (singletonBag a) (list_contents _ eqA_dec l2))).
   apply meq_congr; auto with datatypes.
     apply meq_trans with (munion (singletonBag a) (contents T2)).
    apply munion_comm.
    apply meq_right; auto.
   apply meq_trans with
       (munion (list_contents _ eqA_dec l1)
          (list_contents _ eqA_dec (a :: l2))).
    apply meq_right.
      auto with datatypes.
    apply meq_sym; apply list_contents_app.
Qed.


(** specification of bstsort *)

Theorem bstsort :
 forall l : list A, {m : list A | sort leA m &  permutation _ eqA_dec l m}.
Proof.
  intro l; unfold permutation.
  elim (list_to_bst l).
  intros.
  elim (bst_to_list i); auto with datatypes.
  intros.
  exists l0; auto with datatypes.
  apply meq_trans with (contents T); trivial with datatypes.
Qed.

End BinSearchTrees.


(*

   Require Export BSTrees.
   Extraction "bstsort.ml" BinSearchTrees.
*)
