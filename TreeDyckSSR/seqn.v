Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq tuple.

Require Import rewfacts.

Set Implicit Arguments.
Unset Strict Implicit.

Section Sequences.

  Variable T : Set.

  Inductive seqn : nat -> Set :=
  | nil0 : seqn 0
  | consn : forall (n : nat), T -> seqn n -> seqn (S n).

  Definition seqn_case_n_type (n : nat) : (seqn n) -> Type :=
    match n with
      | 0    => fun f : seqn 0 => forall (P : seqn 0 -> Type), P nil0 -> P f
      | n.+1 => fun f : seqn n.+1 => forall (P : seqn n.+1 -> Type),
                (forall (t : T) (f : seqn n), P (consn t f)) -> P f
    end.

  (*
  Definition seqn_case (n : nat) (f : seqn n) : seqn_rect_n_type f :=
    match f as ff in seqn n return seqn_rect_n_type ff
    with
      | nil0 => fun (P : seqn 0 -> Type) (H : P nil0) => H
      | consn k t f => fun (P : seqn (S k) -> Type)
                      (H : (forall (t : T) (f : seqn k), P (consn t f))) =>
                        H t f
  end.
   *)

  Lemma seqn_case n (f : seqn n) : seqn_case_n_type f.
  Proof. case f; by rewrite /seqn_case_n_type. Defined.
  Lemma seqn_ind_0 : forall (P : seqn 0 -> Prop), P nil0 -> forall f : seqn 0, P f.
  Proof. move=> P H f; apply (seqn_case f P H). Qed.

  Lemma seqn_ind_Sn n : forall (P : seqn n.+1 -> Prop),
                          (forall (t : T) (f : seqn n), P (consn t f)) ->
                            forall f : seqn n.+1, P f.
  Proof. move=> P H f; apply (seqn_case f P H). Qed.


  Definition headn_internal n (s : seqn n) :=
    match s in seqn n return (match n with 0 => unit | _ => T end) with
      | nil0 => tt
      | consn _ h _ => h
    end.
  Definition headn n (s : seqn (S n)) : T := headn_internal s.

  Definition tailn_internal n (s : seqn n) :=
    match s in seqn n return (match n with 0 => unit | n.+1 => seqn n end) with
      | nil0 => tt
      | consn _ _ t => t
    end.
  Definition tailn n (s : seqn (S n)) : seqn n := tailn_internal s.

  Lemma seq0_nil0 (f : seqn 0) : f = nil0.
  Proof. by elim/seqn_ind_0: f. Qed.

  Lemma head_consn n t (f : seqn n) : t = headn (consn t f).
  Proof. by rewrite /head /=. Qed.

  Lemma tail_consn n t (f : seqn n) : f = tailn (consn t f).
  Proof. by rewrite /tailn /=. Qed.

  Lemma consn_head_tail n (f : seqn n.+1) : f = consn (headn f) (tailn f).
  Proof.
    elim/seqn_ind_Sn: f => t f0; by rewrite -head_consn -tail_consn.
  Qed.

  Fixpoint seqn_of_seq (s : seq T) : seqn (size s) :=
    match s with
      | [::] => nil0
      | h :: t => consn h (seqn_of_seq t)
    end.

  Fixpoint seq_of_seqn n (sn : seqn n) : seq T :=
    match sn with
      | nil0 => [::]
      | consn _ h t => h :: seq_of_seqn t
    end.

  Theorem seq_seqnK s : seq_of_seqn (seqn_of_seq s) = s.
  Proof. by elim: s => //= a l ->. Qed.

  Theorem seq_ofI n (s1 s2 : seqn n) : seq_of_seqn s1 = seq_of_seqn s2 <-> s1 = s2.
  Proof.
    split; last by move ->.
    move: s1 s2; elim n.
    by elim/seqn_ind_0; elim/seqn_ind_0.
    move: n => _ n IHn; elim/seqn_ind_Sn => t1 ts1; elim/seqn_ind_Sn => t2 ts2 /=.
    by move=> [] -> /IHn ->.
  Qed.

  Fixpoint catn n1 (s1 : seqn n1) n2 (s2 : seqn n2) : seqn (n1 + n2) :=
    match s1 with
      | nil0 => s2
      | consn _ x s1' => consn x (catn s1' s2)
    end.

  Import Coq.Init.Logic.EqNotations.


  Lemma rewseq n (s : seqn n) m (H : n = m) : seq_of_seqn s = seq_of_seqn (rew H in s).
  Proof. by subst m. Qed.

  (* Set Printing All. *)
  Notation "[ :0: ]" := nil0 (at level 0, format "[ :0: ]") : seq_scope.
  Infix ":n:" := consn (at level 60, right associativity) : seq_scope.
  Infix "+n+" := catn  (at level 60, right associativity) : seq_scope.

  Lemma cat0s n (s : seqn n) : [:0:] +n+ s = s. Proof. by []. Qed.
  Lemma cat1s x n (s : seqn n) : (x :n: [:0:]) +n+ s = x :n: s. Proof. by []. Qed.
  Lemma cat_cons x n1 (s1 : seqn n1) n2 (s2 : seqn n2) :
    (x :n: s1) +n+ s2 = x :n: s1 +n+ s2. Proof. by []. Qed.
  Lemma eqplus0 n : n = n+0. Proof. by rewrite /eqP addn0. Defined.
  Lemma plus0eq n : n+0 = n. Proof. by rewrite -eqplus0. Defined.

  Lemma cats0 n (s : seqn n) : s +n+ [:0:] = rew (eqplus0 n) in s.
  Proof.
    elim: s => /=; move: n => _; first by rewrite -seq_ofI -rewseq.
    move=> n t s ->; by rewrite -seq_ofI -rewseq /= -rewseq.
  Qed.

  Section Fold.

    Variable Rn : nat -> Type.
    Variable f : forall n, T -> Rn n -> Rn n.+1.
    Variable fNil: Rn 0.

    Fixpoint foldn (n : nat) (s : seqn n) : Rn n :=
      match s in seqn n return Rn n with
        | nil0 => fNil
        | consn _ a tl => f a (foldn tl)
      end.

  End Fold.

  Section ZipFold.

    Variable R : Type.
    Variable f : T -> T -> R -> R.
    Variable fNil : R.

    Fixpoint zip_foldn (n : nat) (f1 : seqn n) : (seqn n) -> R :=
      match f1 in seqn n return (seqn n) -> R with
        | nil0 => fun _ => fNil
        | consn n a1 tl1 => fun f2 => f a1 (headn f2) (zip_foldn tl1 (tailn f2))
      end.

    Fixpoint zip_foldn_ht (n : nat) : (seqn n) -> (seqn n) -> R :=
      match n with
        | 0 => fun _ _ => fNil
        | n.+1 => fun f1 f2 => f (headn f1) (headn f2) (zip_foldn_ht (tailn f1) (tailn f2))
      end.

    Fixpoint zip_foldmn (fMiss : R) (m n : nat) (f1 : seqn m) (f2 : seqn n) : R :=
      match f1, f2 with
        | nil0, nil0 => fNil
        | consn _ a1 tl1, consn _ a2 tl2 => f a1 a2 (zip_foldmn fMiss tl1 tl2)
        | _, _ => fMiss
      end.

    Definition zip_foldnn (n : nat) (f1 : seqn n) (f2 : seqn n) : R :=
      zip_foldmn fNil f1 f2.

  End ZipFold.

End Sequences.

Section Map.

  Variable T1 T2 : Set.
  Variable f : T1 -> T2.

  Fixpoint mapn n (s : seqn T1 n) :=
    match s with
      | nil0 => nil0 T2
      | consn _ a tl => consn (f a) (mapn tl)
    end.

End Map.

Section Zip.

  Variable T1 T2 : Set.

  Fixpoint zipn (n : nat) : (seqn T1 n) -> (seqn T2 n) -> seqn (T1*T2) n :=
    match n with
      | 0 => fun _ _ => nil0 (T1*T2)
      | n.+1 => fun f1 f2 => consn (headn f1, headn f2) (zipn (tailn f1) (tailn f2))
    end.

End Zip.

Section BiZip.

  Variable T1 T2 : Set.
  Variable Rn : nat -> Type.
  Variable f : forall n : nat, T1 -> T2 -> Rn n -> Rn n.+1.
  Variable fnil0 : Rn 0.

  Fixpoint bizip (n : nat) : (seqn T1 n) -> (seqn T2 n) -> Rn n :=
    match n with
      | 0 => fun _ _ => fnil0
      | n.+1 => fun f1 f2 => f (headn f1) (headn f2) (bizip (tailn f1) (tailn f2))
    end.

End BiZip.
