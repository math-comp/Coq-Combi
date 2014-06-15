Require Export Arith.
Require Export ListOf.
Require Export BinTrees.
  
Section Listing.

Lemma eq_tree_equiv :
  equivalence Tree (eq (A := Tree)).
Proof.
apply Build_equivalence; red; auto with datatypes.
intros; rewrite H; auto.
Qed.  
  
Lemma eq_tree_dec :
  forall T1 T2 : Tree, {T1 = T2} + {T1 <> T2}.
Proof.
induction T1; intros; induction T2; intros.
 left; auto.
 right; apply leaf_node.
 right; unfold not; intros.
   elim (leaf_node T1_1 T1_2); auto.
 clear IHT2_1 IHT2_2.
   elim IHT1_1 with T2_1; clear IHT1_1; elim IHT1_2 with T2_2; clear IHT1_2;
    intros.
  left; rewrite a; rewrite a0; auto.
  right; unfold not; intros; inversion H; auto.
  right; unfold not; intros; inversion H; auto.
  right; unfold not; intros; inversion H; auto.
Qed.  

Let list_of_trees_prop prop :=
  list_of_set Tree prop (eq (A := Tree)) eq_tree_dec.

Theorem list_of_trees_size_0 :
  list_of_trees_prop (fun T : Tree => (size T) = 0).
Proof.
  unfold list_of_trees_prop, list_of_set.
apply exist with (Leaf :: nil); intros.
elim eq_tree_dec with a Leaf; intros.
 left; rewrite a0.
   split; auto.
   unfold list_contents, multiplicity; simpl.
   elim eq_tree_dec with Leaf Leaf; auto with datatypes.
   intro b; elim b; auto.
 right; intros; split.
  induction a.
   elim b; auto.
   unfold size; auto with arith.
  unfold list_contents, multiplicity; simpl.
    elim eq_tree_dec with Leaf a; auto.
    intro; elim b; auto.
Qed.

  
Let sizeLeft (T : Tree) : nat :=
    match T with
  | Leaf => O
  | Node FG _ => (size FG)
  end. 


Lemma tree_size_left_le_dec :
  forall (n ng : nat) (T : Tree),
       {size T = n /\ sizeLeft T <= ng} +
       {~ (size T = n /\ sizeLeft T <= ng)}.
Proof.
intros.
elim (eq_nat_dec (size T) n); intros.
 elim (le_lt_dec (sizeLeft T) ng); intros.
  left; auto.
  right; red; intro HH; decompose [and] HH; clear HH.
    elim lt_irrefl with ng.
    apply lt_le_trans with (sizeLeft T); auto.
 right; tauto.
Qed.  
  
Lemma tree_size_left_eq_dec :
  forall (n ng : nat) (T : Tree),
       {size T = n /\ sizeLeft T = ng} +
       {~ (size T = n /\ sizeLeft T = ng)}.
Proof.
intros.
elim (eq_nat_dec (size T) n); intros.
 elim (eq_nat_dec (sizeLeft T) ng); intros.
  left; auto.
  right; red; intro HH; decompose [and] HH; clear HH.
    contradiction.
 right; tauto.
Qed.  

  
Theorem list_of_trees_loop_sizeLeft :
  forall n0 : nat,
    (forall n : nat, n <= n0 ->
      list_of_trees_prop (fun T : Tree => (size T) = n))
  -> forall nG : nat,
    list_of_trees_prop (fun T : Tree => (size T) = (S n0) /\ (sizeLeft T) <= nG).
Proof.
intros n0 ltn; induction nG.

   (* Cas initial *) 

  unfold list_of_trees_prop.
   apply
    (list_of_image
       (PA:=fun T : Tree => size T = n0)
       (PB:=fun T : Tree => size T = S n0 /\ sizeLeft T <= 0)
       (eqA_dec:=eq_tree_dec) eq_tree_equiv eq_tree_dec)
     with (fun T : Tree => Node Leaf T).
  intros.
    rewrite H0 in H; trivial.
  intro; simpl; auto.
  intro; simpl.
    intro HH; decompose [and] HH; clear HH.
    auto with arith.
  intros x y eqxy; rewrite eqxy; auto.
  intros; inversion H; auto.
  intro b; case b.
   intros HH; simpl in HH; decompose [and] HH; elim (O_S n0); auto.
   intros.
     exists t0; decompose [and] H; simpl in H1.
     assert (t = Leaf).
    apply zero_size; apply le_antisym; auto with arith.
    rewrite H2; auto.
  intro b.
    apply tree_size_left_le_dec.
  apply ltn; auto with arith.

 elim le_lt_dec with (S nG) n0; intros.

(* Le cas courant de la boucle *)

  assert (list_of_set Tree
    (fun T : Tree => size T = S n0 /\ sizeLeft T = S nG)
     (eq (A:=Tree)) eq_tree_dec).
  unfold list_of_trees_prop.

(* Liste des arbres *)
  
  apply
   (list_of_image
      (eqA     := eqAB (eq (A:=Tree)) (eq (A:=Tree)))
      (eqA_dec := eqAB_dec eq_tree_equiv eq_tree_dec
      	       	       	   eq_tree_equiv eq_tree_dec)
      (PA := PAB (fun T: Tree => size T = S nG)
               	 (fun T: Tree => size T = n0 - S nG))
    eq_tree_equiv eq_tree_dec)
   with 
      (fun TT : Tree*Tree => match TT with | (t1,t2) => Node t1 t2 end).
    intros; rewrite <- H0; auto.
    induction a0.
      unfold PAB; intros; decompose [and] H.
      simpl in H0, H1 |- *; rewrite H0; rewrite H1; split; auto with arith.
    induction a0.
      unfold PAB; intros; decompose [and] H.
      simpl in H0, H1 |- *.
      split; auto with arith.
      rewrite H1 in H0.
      assert (S nG + size b = n0); auto with arith.
      rewrite <- H2; auto with arith.
    induction x; induction y; intros.
      simpl in H |- *; decompose [and] H; rewrite H0; rewrite H1; auto.
    induction x; induction y; intros.
      simpl in H |- *; split; inversion H; auto.
    induction b.
     intros; decompose [and] H; clear H.
       simpl in H0; elim O_S with n0; auto with arith.
     intros; exists (b1, b2); auto.
    apply tree_size_left_eq_dec.

(* Liste des paires des sous-arbres *)
  
    apply list_of_pairs.
     apply ltn; exact a.
     apply ltn.
       apply le_minus.

(* Reunion des listes selon la taille de l'arbre gauche *)
  
   elim IHnG; intros lst_le_nG H_le_nG; clear IHnG.
     elim H; intros lst_eq_nG H_eq_nG; clear H.
     unfold list_of_trees_prop, list_of_set;
      apply exist with (lst_le_nG ++ lst_eq_nG).
     intros T.
     elim (eq_nat_dec (size T) (S n0)); intros.
    elim (le_lt_dec (sizeLeft T) nG); intros.
     left; split; auto.
       rewrite list_contents_app; simpl.
       elim H_le_nG with T; intros Hle; decompose [and] Hle;
        clear Hle H_le_nG; intros.
      rewrite H0.
        elim H_eq_nG with T; intros Heq; decompose [and] Heq;
         clear Heq H_eq_nG; intros.
       rewrite H5 in H2.
         elim (le_Sn_n nG); auto.
       rewrite H3; auto.
      elim H; tauto.
     elim H_eq_nG with T; intros H; decompose [and] H; clear H H_eq_nG;
      intros.
      elim H_le_nG with T; intros H; decompose [and] H; clear H H_le_nG;
       intros.
       rewrite H3 in H6; elim (le_Sn_n nG); auto.
       left; split; auto.
        split; auto.
          rewrite H3; apply le_refl; auto.
        rewrite list_contents_app; simpl.
          rewrite H1; rewrite H4; auto.
      elim H_le_nG with T; intros Hle; decompose [and] Hle; clear Hle H_le_nG;
       intros.
       elim lt_irrefl with nG; apply lt_le_trans with (sizeLeft T); auto.
       right; simpl; split; auto.
        assert (sizeLeft T <> S nG).
         unfold not.
           intros; apply H0; tauto.
         clear H0.
           elim (lt_eq_lt_dec (sizeLeft T) (S nG)); intro; auto.
          elim a1; clear a1; intros; auto.
            unfold not; intros.
            decompose [and] H0; apply lt_irrefl with nG.
            red; apply lt_le_trans with (sizeLeft T); auto.
            apply lt_n_Sm_le; auto.
          unfold not; intros.
            decompose [and] H0; apply lt_irrefl with (S nG).
            apply lt_le_trans with (sizeLeft T); auto.
        rewrite list_contents_app; simpl.
          rewrite H1; rewrite H2; auto.
    right; split.
     unfold not in b |- *; intros; apply b; tauto.
     rewrite list_contents_app; simpl.
       elim H_eq_nG with T; intros H; decompose [and] H; clear H H_eq_nG.
        contradiction.
      elim H_le_nG with T; intros H; decompose [and] H; clear H H_le_nG.
       contradiction.
       rewrite H1; rewrite H3; auto.
   
(* On a fini la boucle : preuve que le resultat est atteint *)
  
  unfold list_of_trees_prop in IHnG.
    elim IHnG; intros.
    unfold list_of_trees_prop, list_of_set; apply exist with x; intros.
    elim (p a); clear p; intros.
   decompose [and] H; left; split; auto.
   decompose [and] H; right; split; auto.
     red in H0 |- *; intros; apply H0.
     decompose [and] H2; split; auto.
     apply le_trans with n0.
    generalize H3.
      case a; simpl; intros; auto with arith.
      apply le_trans with (size t + size t0); auto with arith.
      apply le_S_n; rewrite H5; auto with arith.
    auto with arith.
Qed.

  
Theorem list_of_trees_rec :
  forall n0 : nat,
    (forall n : nat, n <= n0 ->
      list_of_trees_prop (fun T : Tree => (size T) = n)) ->
    list_of_trees_prop (fun T : Tree => (size T) = (S n0)).
Proof.
intros.
elim (list_of_trees_loop_sizeLeft n0 H n0); intros lst Plst.
unfold list_of_trees_prop, list_of_set; apply exist with lst; intros.
elim (Plst a); clear Plst; intros.
 left; tauto.
 right; decompose [and] H0; clear H0.
   split.
  unfold not in H1 |- *; intros; apply H1; intros.
    split; auto.
    generalize H0; case a; intros.
   unfold sizeLeft; auto with arith.
   unfold sizeLeft; simpl in H3.
     apply le_trans with (size t + size t0); auto with arith.
     assert (size t + size t0 = n0); auto with arith.
     rewrite H4; auto.
  exact H2.
Qed.  


(* This short version leads to a very slow ML program
   due to recalculation during the recursive calls. *)
Theorem list_of_trees_le :
  forall n0 n : nat, n <= n0 ->
    list_of_trees_prop (fun T : Tree => (size T) = n).
Proof.
induction n0; intros.
 rewrite <- (le_n_O_eq n H).
   apply list_of_trees_size_0.
 elim (le_lt_eq_dec n (S n0) H); intros.
  apply IHn0; apply lt_n_Sm_le; trivial.
  rewrite b; apply list_of_trees_rec.
    exact IHn0.
Qed.  
  

Let mult_list (l : list Tree) (T : Tree) :=
  multiplicity (list_contents (eq (A:=Tree)) eq_tree_dec l) T.

  
Inductive list_of_list_tree : nat -> Set :=
  exists_list_of_list_tree : forall (n0 : nat) (llt : list (list Tree)),
    (length llt) = S n0 -> 
       (forall (n : nat), n <= n0 ->
       	 forall (T : Tree),
      	     (size T = n) /\ mult_list (nth n llt nil) T = 1 \/
      	   ~ (size T = n) /\ mult_list (nth n llt nil) T = 0)
	 -> list_of_list_tree n0.

      
Theorem list_of_list_tree_list_of :
  forall n0 : nat, list_of_list_tree n0 ->
    forall n : nat, n <= n0 ->
      list_of_trees_prop (fun T : Tree => (size T) = n).
Proof.
unfold list_of_trees_prop, list_of_set.
intros n0 H; elim H; clear H; intros.
apply exist with (nth n llt nil); intros.
unfold mult_list in o.  
elim (eq_nat_dec (size a) n); [left | right]; intros; split; auto.
 elim o with n a; intros; auto.
  decompose [and] H0; trivial.
  decompose [and] H0; contradiction.
 elim o with n a; intros; auto.
  decompose [and] H0; contradiction.
  decompose [and] H0; trivial.
Qed.

Lemma length_app :
  forall (A : Set) (l1 l2 : list A),
    length (l1++l2) = (length l1) + (length l2).
Proof.
intro; induction l1; intros.
 simpl; auto.
 simpl; rewrite <- (IHl1 l2); trivial.
Qed.

Lemma nth_length_app :
  forall (A : Set) (a : A) (l1 l2 : list A),
    nth (length l1) (l1++l2) a = nth 0 l2 a.
Proof.
intros a A; induction l1; intros.
 unfold length, app; auto.
 simpl; rewrite (IHl1 l2); auto.
Qed.

Lemma nth_length_le_app :
  forall (A : Set) (a : A) (l1 l2 : list A) (n : nat),
    n < length l1 -> nth n (l1++l2) a = nth n l1 a.
Proof.
intros a A; induction l1; intros.
 unfold length in H; elim (lt_n_O n); auto.
 generalize H; clear H; case n; auto.
   intros; simpl.
   rewrite IHl1; auto.
   simpl in H; auto with arith.
Qed.

Lemma S_plus_1 :
  forall n : nat, n + 1 = S n.
induction n; auto.
rewrite <- plus_n_Sm; auto.
Qed.


      
Theorem list_of_list_tree_le :
  forall n0 : nat, list_of_list_tree n0.
Proof.
induction n0; intros.
 elim list_of_trees_size_0; intros.
   apply exists_list_of_list_tree with (x :: nil); intros; auto.
   unfold mult_list; rewrite <- (le_n_O_eq n H).
   elim (eq_nat_dec (size T) 0); [ left | right ]; intros; split; auto.
  unfold nth.
    elim (p T); intros; tauto.
  elim (p T); intros; tauto.
 elim IHn0; clear n0 IHn0; intros.
   elim (list_of_trees_rec n0); intros.
  apply exists_list_of_list_tree with (llt ++ x :: nil); intros; auto.
   rewrite length_app; rewrite e; simpl.
    rewrite (S_plus_1 n0); auto.
   elim (eq_nat_dec (size T) n); [ left | right ]; intros; split; auto.
    elim le_lt_eq_dec with n (S n0); auto; intros.
     rewrite nth_length_le_app.
      elim o with n T; intros; auto.
       decompose [and] H0; auto.
       decompose [and] H0; contradiction.
       red in a0; auto with arith.
      rewrite e; auto.
     unfold mult_list; elim p with T; intros; auto.
      decompose [and] H0; clear H0.
        rewrite a in H1; rewrite <- H1 in e; rewrite <- e.
        rewrite nth_length_app; simpl; trivial.
      decompose [and] H0; clear H0.
        rewrite a in H1; contradiction.
    elim le_lt_eq_dec with n (S n0); auto; intros.
     rewrite nth_length_le_app.
      elim o with n T; intros; auto.
       decompose [and] H0; contradiction.
       decompose [and] H0; auto.
       red in a; auto with arith.
      rewrite e; auto.
     unfold mult_list; elim p with T; intros; auto.
      decompose [and] H0; clear H0.
        rewrite b0 in b; contradiction.
      decompose [and] H0; clear H0.
        rewrite b0; rewrite <- e.
        rewrite nth_length_app; simpl; trivial.
  apply (list_of_list_tree_list_of n0); auto.
    apply exists_list_of_list_tree with llt; auto.
Qed.    

  
Theorem list_of_trees :
  forall n : nat, list_of_trees_prop (fun T : Tree => (size T) = n).
Proof.
intro; apply list_of_list_tree_list_of with n; auto.
 apply list_of_list_tree_le.
Qed.  

  
Theorem list_of_trees_slow :
  forall n : nat, list_of_trees_prop (fun T : Tree => (size T) = n).
Proof.
intros; apply list_of_trees_le with n; auto.
Qed.  

  
End Listing.

Require Import Wf_nat.  
Extraction Inline Wf_nat.lt_wf_rec1 Wf_nat.lt_wf_rec
  Wf_nat.lt_wf_ind Wf_nat.gt_wf_rec Wf_nat.gt_wf_ind.

Extract Inductive sumbool => "bool" [ "true" "false" ].
  
Extraction "extract/listTree.ml" list_of_trees list_of_trees_slow.
