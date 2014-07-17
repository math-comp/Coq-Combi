Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
Require Import Coq.Arith.Wf_nat Recdef.
Require Import brace mDyck seqn.

Set Implicit Arguments.
Unset Strict Implicit.

Module MTree (Param : M_PARAM).

  Import Param.

  Implicit Type n : nat.

  Inductive tree : Set :=
  | mLeaf  : tree
  | mNode  : forest -> tree
  with forest : Set := mF : seqn tree m -> forest.

  Implicit Type t : tree.
  Implicit Type f : forest.

  Local Notation seqt := (seqn tree).

  (* Find a syntactically easier way to do this induction *)

  Module Type INDUCTION_DATA.

    Parameter Inline Pt : tree -> Type.
    Parameter Inline Pf : forest -> Type.
    Parameter Inline Ps : forall n, seqt n -> Type.

    Axiom Inline HLeaf : Pt mLeaf.
    Axiom Inline HNode : forall f : forest, Pf f -> Pt (mNode f).

    Axiom Inline HF : forall s : seqt m, Ps s -> Pf (mF s).

    Axiom Inline Hnil0 : Ps (nil0 tree).
    Axiom Inline Hconsn :
      forall n (t : tree) (s : seqt n), Pt t -> Ps s -> Ps (consn t s).

  End INDUCTION_DATA.

  Module MTreeInduction (Data : INDUCTION_DATA).

    Definition seq_tree_ind (H : forall t, Data.Pt t) n : forall (s : seqt n), Data.Ps s :=
      (fix F n (s : seqt n) {struct s} : Data.Ps s :=
         match s as s in (seqn _ n) return (Data.Ps s) with
         | nil0 => Data.Hnil0
         | consn n t s0 => Data.Hconsn (H t) (F n s0)
       end) n.

    Fixpoint tree_mut_ind t : Data.Pt t :=
      match t with
        | mLeaf   => Data.HLeaf
        | mNode f => Data.HNode (forest_mut_ind f)
      end
    with forest_mut_ind f :=
           let: mF s := f in Data.HF (seq_tree_ind tree_mut_ind s).

    Definition seq_tree_mut_ind := seq_tree_ind tree_mut_ind.

    Include Data.

  End MTreeInduction.

  Module EqualityData <: INDUCTION_DATA.

    Definition Pt t := tree -> bool.
    Definition Pf f := forest -> bool.
    Definition Ps n (_ : seqt n) := (seqt n) -> bool.

    Definition HLeaf := fun t => if t is mLeaf then true else false.
    Definition HNode f :=
      fun (eqf : forest -> bool) t => if t is mNode f2 then eqf f2 else false.

    Definition HF (s : seqt m) :=
      fun (eqs : seqt m -> bool) f => let: mF s2 := f in eqs s2.
    Definition Hnil0 := fun (f : seqt 0) => true.

    Definition Hconsn n (t : tree) (s : seqt n) :=
      fun (eqt : tree -> bool) (eqs : seqt n -> bool) (s : seqt n.+1) =>
        eqt (headn s) && eqs (tailn s).

  End EqualityData.
  Module MTreeEquality := MTreeInduction EqualityData.

(* Import MTreeEquality. *)

  Section Equality.
    Definition eq_tree := MTreeEquality.tree_mut_ind.
    Definition eq_forest := MTreeEquality.forest_mut_ind.
    Definition eq_seq_tree := MTreeEquality.seq_tree_mut_ind.
  End Equality.

  Module EqualityReflexiveData <: INDUCTION_DATA.

    Definition Pt t := is_true (eq_tree t t).
    Definition Pf f := is_true (eq_forest f f).
    Definition Ps n (s : seqt n) := is_true (eq_seq_tree s s).

    Lemma HLeaf : Pt mLeaf. Proof. by []. Qed.
    Lemma HNode : forall f : forest, Pf f -> Pt (mNode f). Proof. by []. Qed.
    Lemma HF : forall s : seqt m, Ps s -> Pf (mF s). Proof. by []. Qed.
    Lemma Hnil0 : Ps (nil0 tree). Proof. by []. Qed.
    Lemma Hconsn : forall n (t : tree) (s : seqt n), Pt t -> Ps s -> Ps (consn t s).
    Proof. by rewrite /Pt /Ps /= /eq_tree => n t s ->. Qed.

  End EqualityReflexiveData.
  Module EqualityReflexive := MTreeInduction EqualityReflexiveData.

  Module EqualityReflectData <: INDUCTION_DATA.

    Definition Pt t := forall t2, eq_tree t t2 -> t = t2.
    Definition Pf f := forall f2, eq_forest f f2 -> f = f2.
    Definition Ps n (s : seqt n) := forall s2, eq_seq_tree s s2 -> s = s2. 

    Lemma HLeaf : Pt mLeaf. Proof. by case. Qed.
    Lemma HNode : forall f : forest, Pf f -> Pt (mNode f).
    Proof.
      rewrite /Pf /Pt /eq_forest => f IHf /=; case => [| f2 Hf2]; first by [].
      by rewrite (IHf _ Hf2).
    Qed.
    Lemma HF : forall s : seqt m, Ps s -> Pf (mF s).
    Proof.
      rewrite /Ps /Pt /Pf /eq_forest => s IHs. case => s2 Hs2.
      by rewrite (IHs _ Hs2).
    Qed.
    Lemma Hnil0 : Ps (nil0 tree).
    Proof.
      rewrite /Ps /eq_seq_tree => s2 _; by rewrite (seq0_nil0 s2).
    Qed.
    Lemma Hconsn : forall n (t : tree) (s : seqt n), Pt t -> Ps s -> Ps (consn t s).
    Proof.
      rewrite /Ps /Pt /Pf /eq_seq_tree => n t s IHt IHs s2.
      apply (seqn_ind_Sn
               (P := fun s2 => MTreeEquality.seq_tree_mut_ind (consn t s) s2
                               -> consn t s = s2)).
      move: s2 => _ t2 s2 /=.
      rewrite /MTreeEquality.seq_tree_mut_ind /= => /andP [] Ht2 Hs2.
      by rewrite (IHt _ Ht2) (IHs _ Hs2).
   Qed.

  End EqualityReflectData.
  Module EqualityReflect := MTreeInduction EqualityReflectData.

  Lemma eq_forestP : Equality.axiom eq_forest.
  Proof.
    move=> f1 f2; apply: (iffP idP) => [|<-].
    apply EqualityReflect.forest_mut_ind.
    apply EqualityReflexive.forest_mut_ind.
  Qed.

  Lemma eq_treeP : Equality.axiom eq_tree.
  Proof.
    move=> f1 f2; apply: (iffP idP) => [|<-].
    apply EqualityReflect.tree_mut_ind.
    apply EqualityReflexive.tree_mut_ind.
  Qed.

  Lemma eq_seq_treeP n : Equality.axiom (@eq_seq_tree n).
  Proof.
    move=> f1 f2; apply: (iffP idP) => [|<-].
    apply EqualityReflect.seq_tree_mut_ind.
    apply EqualityReflexive.seq_tree_mut_ind.
  Qed.
  
  Canonical tree_eqMixin := EqMixin eq_treeP.
  Canonical tree_eqType := Eval hnf in EqType tree tree_eqMixin.

  Canonical forest_eqMixin := EqMixin eq_forestP.
  Canonical forest_eqType := Eval hnf in EqType forest forest_eqMixin.

  Canonical seq_tree_eqMixin n := EqMixin (@eq_seq_treeP n).
  Canonical seq_tree_eqType n := Eval hnf in EqType (seqn tree n) (seq_tree_eqMixin n).

  Fixpoint size_seqn_tree (st : tree -> nat) n (s : seqt n) :=
    match s with
      | nil0 => 0
      | consn _ t s => (st t) + (size_seqn_tree st s)
    end.

  Fixpoint size_tree (t : tree) :=
    match t with
      | mLeaf => 0
      | mNode f => 1 + (size_forest f)
    end
  with size_forest (f : forest) :=
         let: mF s := f in
         ( fix size_seqn_tree n (s : seqt n) :=
             match s with
               | nil0 => 0
               | consn _ t s => (size_tree t) + (size_seqn_tree _ s)
             end ) m s.

End MTree.

Module M. Definition m := 2. End M.
Module MT := MTree M.

Section Tests.

  Import MT.

  Let t1 : tree := mNode (mF (consn mLeaf (consn mLeaf (nil0 tree)))).
  Let t10 : tree := mNode (mF (consn t1 (consn mLeaf (nil0 tree)))).
  Let t01 : tree := mNode (mF (consn mLeaf (consn t1 (nil0 tree)))).
  Let t11 : tree := mNode (mF (consn t1 (consn t1 (nil0 tree)))).

  Eval compute in mLeaf == mLeaf.
  Eval compute in t1 == mLeaf.
  Eval compute in t10 == t10.
  Eval compute in t10 == t01.
  Eval compute in consn mLeaf (consn mLeaf (nil0 tree)) == consn t1 (consn mLeaf (nil0 tree)).

  Eval compute in size_tree t10.
  Eval compute in size_tree t11.

End Tests.
(*  Let eq_tree := tree_mut_ind HLeaf HNode  
    Fixpoint eq_tree (t1 t2 : tree) {struct t1} : bool :=
    match t1, t2 with
      | mLeaf, mLeaf => true
      | mNode f1, mNode f2 => eq_forest f1 f2
      | _, _ => false
    end
  with eq_forest f1 f2 :=
         let: mF s1 := f1 in let: mF s2 := f2 in
          (fix eq_seqt n (f1 : seqt n) : (seqt n) -> bool :=
                 match f1 in seqn _ n return (seqt n) -> bool with
                   | nil0 => fun _ => true
                   | consn n a1 tl1 =>
                     fun f2 => eq_tree a1 (headn f2) && (eq_seqt n tl1 (tailn f2))
                 end) m s1 s2.

  Lemma eq_forest_refl (f : forest) : (eq_forest f f).
  Proof.
    apply (@forest_tree_ind
             (fun t => eq_tree t t)
             (fun t => eq_forest f f)
             (fun n (f : seqt n) => eq_forest f f)) => //=.

    move: n f => _ _ n t f.
    by rewrite /eq_forest /zip_foldnn /= => ->.
  Qed.

  Lemma eq_forestP n : Equality.axiom (@eq_forest n).
  Proof.
    move=> f1 f2; apply: (iffP idP) => [|<-].
    - move: f2.
      apply (@forest_tree_ind
               (fun t => forall t2 : tree, eq_tree t t2 -> t = t2)
               (fun n (f : forest n) => forall f2, eq_forest f f2 -> f = f2)) => //=.
      * move=> f2; by rewrite (seq0_nil0 f2).
      * move=> f H; elim=> //= f2 H2; by have:= (H _ H2) => ->.
      * move=> f _; symmetry; by apply forest0nilf.
      * move=> n' t Heqt f Heqf f2; rewrite [f2]consf_head_tail /eq_forest /= => /andP [].
        by move/Heqt ->; move/Heqf ->.
    - move: f2 => _; by apply eq_forest_refl.
  Qed.

  Lemma eq_treeP : Equality.axiom eq_tree.
  Proof.
    move=> t1 t2; apply: (iffP idP) => [|<-].
    - by case: t1; case t2 => //= f1 f2 /eq_forestP ->.
    - move: t2 => _; case: t1 => //= f; by apply eq_forest_refl.
  Qed.

  Canonical tree_eqMixin := EqMixin eq_treeP.
  Canonical tree_eqType := Eval hnf in EqType tree tree_eqMixin.

  Canonical forest_eqMixin n := EqMixin (@eq_forestP n).
  Canonical forest_eqType n := Eval hnf in EqType (forest n) (forest_eqMixin n).

 
      
End mTree.

End MTree.

Module MBijection (Param : M_PARAM).

  Module MDyckm := MDyck Param.
  Import MDyckm.

  Module Param1. Section One. Definition m := Param.m + 1. End One. End Param1.
  Module MTree := MDyck Param1.
  Import MTree.

  Section MBijection.

  Implicit Type n : nat.
  Implicit Type d : Dyck.
  Implicit Type t : tree.

  Fixpoint dyck_of_tree t 

  End MBijection.

End MBijection.
*)
