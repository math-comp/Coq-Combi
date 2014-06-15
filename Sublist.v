Require Import Arith.
Require Import List.

Section SubList.

Variable A : Set.

Lemma length_0_nil :
  forall (l : list A), length l = 0 -> l = nil.
intro l; case l; auto.
intros; simpl in H.
elim O_S with (length l0); auto.
Qed.

Lemma length_1 :
  forall (l : list A), length l = 1 ->
    { a : A | l = a::nil }.
Proof.
destruct l.
 simpl; intro; elim O_S with 0; auto.
 simpl; intros.
   exists a; auto.
   assert (l = nil).
  apply length_0_nil; auto with arith.
  rewrite H0; auto.

Qed.

Lemma length_app :
  forall l0 l1 : list A,
    length (l0 ++ l1) = length l0 + length l1.
Proof.
induction l0; intros.
simpl; auto.
simpl; rewrite IHl0; auto.
Qed.


Lemma equal_length_app :
  forall l0 l1 m0 m1 : list A,
    l0 ++ l1 = m0 ++ m1 -> length l0 = length m0 ->
      l0 = m0 /\ l1 = m1.
Proof.
induction l0; intros.
 assert (m0 = nil).
  simpl in H0; apply length_0_nil; auto.
  split; auto.
    rewrite H1 in H; simpl in H; auto.
 generalize H0 H; clear H0 H; case m0; intros.
  simpl in H0; elim O_S with (length l0); auto.
  elim IHl0 with l1 l m1.
   intros; rewrite H1; rewrite H2.
     split; auto.
     rewrite <- app_comm_cons in H; rewrite <- app_comm_cons in H.
     inversion H.
     rewrite <- H4; auto.
   rewrite <- app_comm_cons in H; rewrite <- app_comm_cons in H.
     inversion H; auto.
   simpl in H0; auto with arith.
Qed.


Fixpoint sublist (n:nat) (l:list A) {struct l} : list A :=
  match n, l with
   | 0, _        => nil
   | S m, nil    => nil
   | S m, x :: t => x :: (sublist m t)
end.

Lemma sublist_0 :
  forall (l : list A), sublist 0 l = nil.
intro l; case l; auto.
Qed.

Lemma sublist_nil :
  forall (n:nat), sublist n nil = nil.
intro n; case n; auto.
Qed.

Lemma sublist_length_le :
  forall (n:nat) (l:list A),
    length (sublist n l) <= length l.
double induction n l; intros; simpl; auto with arith.
Qed.

Lemma sublist_full :
  forall (l:list A),
    sublist (length l) l = l.
Proof.
induction l; intros; simpl; auto.
rewrite IHl; auto.
Qed.

Lemma sublist_gt :
  forall (n:nat) (l:list A), (length l) <= n  ->
    (sublist n l) = l.
Proof.
induction n.
 intros; assert (l = nil).
  apply length_0_nil; auto with arith.
  rewrite H0; simpl; auto.
 intros l; case l; intros; simpl; auto.
   rewrite IHn with l0; auto.
   simpl in H; auto with arith.
Qed.

Lemma sublist_length_ok :
  forall (n:nat) (l:list A), n <= (length l) ->
    length (sublist n l) = n.
Proof.
double induction n l; intros; simpl; auto with arith.
Qed.

Lemma sublist_app :
  forall (n:nat) (l:list A),
    { l1 : list A | l = (sublist n l) ++ l1 }.
Proof.
induction n; intros.
 exists l; case l; simpl; auto.
 case l; intros.
  exists (nil (A:=A)); simpl; auto.
  elim IHn with l0; intros.
    exists x; simpl.
    rewrite <- p; auto.
Qed.

Lemma sublist_app_rev :
  forall (l l0 : list A),
    (exists l1 : list A, l = l0 ++ l1)
      -> l0 = sublist (length l0) l.
Proof.
intros l l0; generalize l; clear l.
induction l0; intros.
 simpl; rewrite sublist_0; auto.
 elim H; clear H; intros.
   rewrite H; clear H; simpl.
   rewrite <- IHl0; auto.
   exists x; auto.
Qed.

Lemma subsublist_le :
  forall (l : list A) (n0 n1 : nat),
    n0 <= n1 -> sublist n0 (sublist n1 l) = sublist n0 l.
Proof.
induction l.
 intros; rewrite sublist_nil; rewrite sublist_nil; auto.
 intros n0 n1; case n1; intros.
  assert (n0 = 0); auto with arith.
    rewrite H0; rewrite sublist_0; rewrite sublist_0; auto.
  generalize H.
    case n0; intros.
   rewrite sublist_0; auto.
   simpl; rewrite IHl; auto with arith.
Qed.

Lemma subsublist_gt :
  forall (l : list A) (n0 n1 : nat),
    n0 > n1 -> sublist n0 (sublist n1 l) = sublist n1 l.
Proof.
induction l.
 intros; rewrite sublist_nil; rewrite sublist_nil; auto.
 intros n0 n1; case n1; intros.
  intros; rewrite sublist_nil; auto.
  generalize H; clear H; case n0; intros.
   absurd (0 > S n); auto with arith.
   simpl; rewrite IHl; auto with arith.
Qed.


Lemma sublist_cons :
  forall (a: A) (l : list A) (n : nat), 
    sublist (S n) (a::l) = a::(sublist n l).
Proof.
intros.
auto.
Qed.

End SubList.
