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

  Section Induction.

    Variable Pt : tree -> Type.
    Variable Pf : forest -> Type.
    Variable Ps : forall n, seqt n -> Type.
    Hypothesis HLeaf : Pt mLeaf.
    Hypothesis HNode : forall f : forest, Pf f -> Pt (mNode f).
    Hypothesis HF : forall s : seqt m, Ps s -> Pf (mF s).
    Hypothesis Hnil0 : Ps (nil0 tree).
    Hypothesis Hconsn :
      forall n (t : tree) (s : seqt n), Pt t -> Ps s -> Ps (consn t s).

    Definition seq_tree_ind (H : forall t, Pt t) n : forall (s : seqt n), Ps s :=
      (fix F n (s : seqt n) {struct s} : Ps s :=
         match s as s in (seqn _ n) return (Ps s) with
         | nil0 => Hnil0
         | consn n t s0 => Hconsn (H t) (F n s0)
       end) n.

    Fixpoint tree_mut_ind t : Pt t :=
      match t with
        | mLeaf   => HLeaf
        | mNode f => HNode (forest_mut_ind f)
      end
    with forest_mut_ind f :=
           let: mF s := f in HF (seq_tree_ind tree_mut_ind s).

    Definition seq_tree_mut_ind := seq_tree_ind tree_mut_ind.

    CoInductive mut_ind_triple := { get_tree : forall t, Pt t;
                                    get_forest : forall f, Pf f;
                                    get_seq_tree : forall n (s : seqt n), Ps s }.

    Definition mut_ind := Build_mut_ind_triple
                            tree_mut_ind forest_mut_ind seq_tree_mut_ind.

  End Induction.

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
    Include Data.
    Definition def_tree : forall t, Data.Pt t :=
      tree_mut_ind Data.HLeaf Data.HNode Data.HF Data.Hnil0 Data.Hconsn.
    Definition def_forest : forall f, Data.Pf f :=
      forest_mut_ind Data.HLeaf Data.HNode Data.HF Data.Hnil0 Data.Hconsn.
    Definition def_seq_tree : forall n (s : seqt n), Data.Ps s :=
      seq_tree_ind Data.Hnil0 Data.Hconsn def_tree.
  End MTreeInduction.

  Section Equality.

    Section Defs.

      Let eqLeaf := fun t => if t is mLeaf then true else false.
      Let eqNode f :=
        fun (eqf : forest -> bool) t => if t is mNode f2 then eqf f2 else false.
      Let eqF (s : seqt m) :=
        fun (eqs : seqt m -> bool) f => let: mF s2 := f in eqs s2.
      Let eqnil0 := fun (f : seqt 0) => true.
      Let eqconsn n (t : tree) (s : seqt n) :=
        fun (eqt : tree -> bool) (eqs : seqt n -> bool) (s : seqt n.+1) =>
          eqt (headn s) && eqs (tailn s).

      Definition eq_tree : tree -> tree -> bool :=
        tree_mut_ind eqLeaf eqNode eqF eqnil0 eqconsn.
      Definition eq_forest : forest -> forest -> bool :=
        forest_mut_ind eqLeaf eqNode eqF eqnil0 eqconsn.
      Definition eq_seq_tree : forall n, seqt n -> seqt n -> bool :=
        seq_tree_ind eqnil0 eqconsn eq_tree.

    End Defs.

    Lemma eq_tripleR :
      mut_ind_triple (fun t => eq_tree t t)
                     (fun f => eq_forest f f)
                     (fun n (s : seqt n) => eq_seq_tree s s).
    Proof. by apply mut_ind => //= => n t s -> ->. Qed.

    Lemma eq_triple_impl_eq :
      mut_ind_triple (fun t1 => forall t2, eq_tree t1 t2 -> t1 = t2)
                     (fun f1 => forall f2, eq_forest f1 f2 -> f1 = f2)
                     (fun n (s1 : seqt n) => forall s2, eq_seq_tree s1 s2 -> s1 = s2).
    Proof.
      apply mut_ind => //=.
      - by case.
      - move=> f IHf; case => //= f2 Hf2; by rewrite (IHf _ Hf2).
      - move=> s IHs; case => s2 Hs2; by rewrite (IHs _ Hs2).
      - move=> s2 _; by apply seqn_ind_0.
      - move => n t s IHt IHs.
        elim/seqn_ind_Sn => t2 s2 /= /andP [] Ht2 Hs2.
        by rewrite (IHt _ Ht2) (IHs _ Hs2).
    Qed.

    Lemma eq_treeP : Equality.axiom eq_tree.
    Proof.
      move=> t1 t2; apply: (iffP idP) => [|<-].
      by apply (get_tree eq_triple_impl_eq).
      by apply (get_tree eq_tripleR).
    Qed.

    Lemma eq_forestP : Equality.axiom eq_forest.
    Proof.
      move=> f1 f2; apply: (iffP idP) => [|<-].
      by apply (get_forest eq_triple_impl_eq).
      by apply (get_forest eq_tripleR).
    Qed.

    Lemma eq_seq_treeP n : Equality.axiom (@eq_seq_tree n).
    Proof.
      move=> s1 s2; apply: (iffP idP) => [|<-].
      by apply (get_seq_tree eq_triple_impl_eq).
      by apply (get_seq_tree eq_tripleR).
    Qed.

    Canonical tree_eqMixin := EqMixin eq_treeP.
    Canonical tree_eqType := Eval hnf in EqType tree tree_eqMixin.

    Canonical forest_eqMixin := EqMixin eq_forestP.
    Canonical forest_eqType := Eval hnf in EqType forest forest_eqMixin.

    Canonical seq_tree_eqMixin n := EqMixin (@eq_seq_treeP n).
    Canonical seq_tree_eqType n := Eval hnf in EqType (seqn tree n) (seq_tree_eqMixin n).

  End Equality.

  Section Size.

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

  End Size.

End MTree.


(*

Module MBijection (Param : M_PARAM).

  Module MDyckm := MDyck Param.
  Import MDyckm.

  Module Param1. Section One. Definition m := Param.m + 1. End One. End Param1.
  Module MTree := MTree Param1.
  Import MTree.

  Section MBijection.

  Implicit Type n : nat.
  Implicit Type d : Dyck.
  Implicit Type t : tree.

  End MBijection.

End MBijection.

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

*)
