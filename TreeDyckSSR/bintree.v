Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
Require Import Coq.Arith.Wf_nat Recdef.
Require Import brace mDyck.

Set Implicit Arguments.
Unset Strict Implicit.

Section bin_tree.

  Inductive bin_tree : Set :=
  | BinLeaf  : bin_tree
  | BinNode  : bin_tree -> bin_tree -> bin_tree.

  Fixpoint eq_bin_tree (b1 b2 : bin_tree) : bool :=
    match b1, b2 with
      | BinLeaf, BinLeaf => true
      | BinNode l1 r1, BinNode l2 r2 => eq_bin_tree l1 l2 && eq_bin_tree r1 r2
      | _, _ => false
    end.

  Lemma eq_bin_treeP : Equality.axiom eq_bin_tree.
  Proof.
    move=> t1 t2; apply: (iffP idP) => [|<-]; last by elim: t1 => //= r -> l ->.
    elim: t1 t2 => [|l1 IHl r1 IHr]; first by case.
    case => //= [l2 r2] /andP [] Hr Hl; by rewrite (IHl _ Hr)  (IHr _ Hl).
  Qed.

  Canonical bin_tree_eqMixin := EqMixin eq_bin_treeP.
  Canonical bin_tree_eqType := Eval hnf in EqType bin_tree bin_tree_eqMixin.

  Fixpoint size_tree (t : bin_tree) :=
    match t with
      | BinLeaf => 0
      | BinNode l r => 1 + (size_tree l) + (size_tree r)
    end.

End bin_tree.



Section DyckWordTreeBij.

  Import mDyck.MDyck1.

  Implicit Type h n : nat.
  Implicit Type w : seq Brace.
  Implicit Type d : Dyck.
  Implicit Type t : bin_tree.

  Fixpoint word_of_tree t : seq Brace :=
    match t with
      | BinLeaf => nil
      | BinNode l r => Open :: (word_of_tree l) ++ Close :: (word_of_tree r)
    end.

  Lemma word_of_tree_is_dyck t : word_of_tree t \in dyck_rec.
  Proof.
    elim: t => //= l Hl r Hr.
    rewrite -cat_cons -[Close :: _]cat1s catA.
    apply cat_dyck_height; last by apply Hr.
    by rewrite -/cat /mDyck.m1.m -[1]add0n; apply cat_dyck_height.
  Qed.

  Definition Dyck_of_tree t := DyckWord (word_of_tree_is_dyck t).

  Definition tree_of_Dyck_spec d : {t : bin_tree | word_of_tree t == d}.
  Proof.
    elim/Dyck_gram_ind: d; first by exists BinLeaf.
    move=> d [] /= [] [//|] dl /= [] //=.
    rewrite /joinDyck /= => _ dr /eqP -> Hrec.
    have Htriv : dl \in [:: dl] by rewrite inE.
    elim (Hrec _ Htriv) => tl Hl {Hrec Htriv}.
    elim => /= tr Hr.
    exists (BinNode tl tr) => /=.
    by rewrite (eqP Hl) (eqP Hr).
  Defined.

  Definition tree_of_Dyck d := val (tree_of_Dyck_spec d).

(*  Definition tree_of_brace w : bin_tree :=
    (if dyck_rec w as b return (dyck_rec w) = b -> bin_tree
     then fun proof => tree_of_Dyck (DyckWord proof)
     else fun _ => BinLeaf) Logic.eq_refl. *)

  Lemma bij1 d : Dyck_of_tree (tree_of_Dyck d) == d.
  Proof. rewrite /tree_of_Dyck; by elim (tree_of_Dyck_spec d). Qed.

  Lemma bij2 (t : bin_tree) :
    tree_of_Dyck (Dyck_of_tree t) == t.
  Proof.
    rewrite /tree_of_Dyck; elim (tree_of_Dyck_spec _).
    elim t => /= [| l Hl r Hr ]/=; first by case.
    case => //= l0 r0 /eqP Heq.
    have:= (cut_unique (word_of_tree_is_dyck l0) (word_of_tree_is_dyck r0)).
    rewrite Heq => {Heq}.
    rewrite -(eqP (cut_unique (word_of_tree_is_dyck l) (word_of_tree_is_dyck r))).
    move=> /eqP [] /eqP Heql /eqP Heqr.
    by rewrite (eqP (Hl l0 Heql)) (eqP (Hr r0 Heqr)).
  Qed.

  Lemma bij_size_tree t : size (Dyck_of_tree t) == (size_tree t).*2.
  Proof.
    elim: t => //= l /eqP Hl r /eqP Hr.
    by rewrite size_cat /= Hl Hr addnS -addnA add1n doubleS -doubleD.
  Qed.

  Lemma bij_size_Dyck d : size d == (size_tree (tree_of_Dyck d)).*2.
  Proof.
    rewrite -{1}(eqP (bij1 d)); by apply bij_size_tree.
  Qed.

  Lemma tree_of_emptyDyck : tree_of_Dyck emptyDyck = BinLeaf.
  Proof.
    rewrite /tree_of_Dyck.
    elim (tree_of_Dyck_spec emptyDyck); by case.
  Qed.

  Lemma tree_of_gram_Dyck d :
    d != emptyDyck -> { pair : bin_tree * bin_tree
                      | let (t1, t2) := pair in d = Dyck_of_tree (BinNode t1 t2) }.
  Proof.
    rewrite -(eqP (bij1 d)); move Ht : (tree_of_Dyck d) => t; case: t Ht => //= t1 t2 Ht _.
    by exists (t1, t2).
  Qed.

End DyckWordTreeBij.


Import mDyck.MDyck1.

(*
Let w := [:: Open; Close ].
Let d := DyckWord (is_true_true : w \in dyck_rec).
*)
Let t := (BinNode BinLeaf BinLeaf).
Let d := DyckWord (is_true_true : [:: Open; Close] \in dyck_rec).
Let dnnil : d != emptyDyck := is_true_true.

(* Eval compute in tree_of_Dyck_spec d. *)

Lemma checkbij : tree_of_Dyck (d) = t.
Proof.
  have Hnil : d != emptyDyck by []; elim (tree_of_gram_Dyck Hnil) => [[t1 t2]] {Hnil}.
  rewrite /d /t => H. rewrite H (eqP (bij2 _)) /Dyck_of_tree /word_of_tree; move: H.
  case: t1; case: t2 => //=.
Qed.

(* Eval compute in (tree_of_Dyck (DyckWord d)). *)
