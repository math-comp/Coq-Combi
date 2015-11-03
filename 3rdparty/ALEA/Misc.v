(** printing ~ $\neg$ #&not;# *)
(** printing -> $\ra$ #&rarr;# *)
(** printing => $\Ra$ #&rArr;# *)
(** printing ==> $\Ra$ #&rArr;# *)
(** printing <-> $\lra$ #&harr;# *)
(** printing /\ $\wedge$ #&and;# *)
(** printing \/ $\vee$ #&or;# *)
(** printing forall $\forall$ #&forall;# *)
(** printing exist $\exists$ #&exists;# *)

(** * Misc.v: Preliminaries *)

Set Implicit Arguments.
(* Require Export Setoid. *)
Require Export Arith.
Require Import Coq.Classes.SetoidTactics.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Classes.Morphisms.

Open Local Scope signature_scope.


(* Should be in standard library Arith.EqNat.beq_nat. *)
Lemma beq_nat_neq: forall x y : nat, x <> y -> false = beq_nat x y.
Proof.
  induction x;induction y;simpl;auto.
Qed.

Lemma if_beq_nat_nat_eq_dec : forall A (x y:nat) (a b:A),
  (if beq_nat x y then a else b) = if eq_nat_dec x y then a else b.
Proof.
  intros A x y a b.
  destruct (eq_nat_dec x y);intros;subst.
  rewrite <- beq_nat_refl;trivial.
  rewrite <- beq_nat_neq;auto.
Qed.

Definition ifte A (test:bool) (thn els:A) := if test then thn else els.

Add Parametric Morphism (A:Type) : (@ifte A)
  with signature (eq ==>eq ==> eq ==> eq) as ifte_morphism1.
Proof.
  trivial.
Qed.  

Add Parametric Morphism (A:Type) x : (@ifte A x)
  with signature (eq ==> eq ==> eq) as ifte_morphism2.
Proof.
  trivial.
Qed.  

Add Parametric Morphism (A:Type) x y : (@ifte A x y)
  with signature (eq ==> eq) as ifte_morphism3.
Proof.
  trivial.
Qed.  

(** ** Definition of iterator [compn]
   [compn f u n x] is defined as (f (u (n-1)).. (f (u 0) x)) *)

Fixpoint compn (A:Type)(f:A -> A -> A) (x:A) (u:nat -> A) (n:nat) {struct n}: A := 
   match n with O => x | (S p) => f (u p) (compn f x u p) end.
      
Lemma comp0 : forall (A:Type) (f:A -> A -> A) (x:A) (u:nat -> A), compn f x u 0 = x.
trivial.
Save.

Lemma compS : forall (A:Type) (f:A -> A -> A) (x:A) (u:nat -> A) (n:nat),
              compn f x u (S n) = f (u n) (compn f x u n).
trivial.
Save.

(** ** Reducing if constructs *)

Lemma if_then : forall (P:Prop) (b:{ P }+{ ~ P })(A:Type)(p q:A), 
      P -> (if b then p else q) = p.
destruct b; simpl; intuition.
Save.

Lemma if_else : forall (P :Prop) (b:{ P }+{ ~ P })(A:Type)(p q:A), 
      ~P -> (if b then p else q) = q.
destruct b; simpl; intuition.
Save.

Lemma if_then_not : forall (P Q:Prop) (b:{ P }+{ Q })(A:Type)(p q:A), 
      ~ Q -> (if b then p else q) = p.
destruct b; simpl; intuition.
Save.

Lemma if_else_not : forall (P Q:Prop) (b:{ P }+{ Q })(A:Type)(p q:A), 
      ~P -> (if b then p else q) = q.
destruct b; simpl; intuition.
Save.


(** ** Classical reasoning *)

Definition class (A:Prop) := ~ ~ A -> A.

Lemma class_neg : forall A:Prop, class ( ~ A).
unfold class; intuition.
Save.

Lemma class_false : class False.
unfold class; intuition.
Save.
Hint Resolve class_neg class_false.

Definition orc (A B:Prop) := forall C:Prop, class C -> (A -> C) -> (B -> C) -> C.

Lemma orc_left : forall A B:Prop, A -> orc A B.
red;intuition.
Save.

Lemma orc_right : forall A B:Prop, B -> orc A B.
red;intuition.
Save.

Hint Resolve orc_left orc_right.

Lemma class_orc : forall A B, class (orc A B).
repeat red; intros.
apply H0; red; intro.
apply H; red; intro. 
apply H3; apply H4; auto.
Save.

Implicit Arguments class_orc [].

Lemma orc_intro : forall A B, ( ~ A -> ~ B -> False) -> orc A B.
intros; apply class_orc; red; intros.
apply H; red; auto.
Save.

Lemma class_and : forall A B, class A -> class B -> class (A /\ B).
unfold class; intuition.
Save.

Lemma excluded_middle : forall A, orc A ( ~ A).
red; intros.
apply H; red; intro.
intuition.
Save.

Definition exc (A :Type)(P:A -> Prop) := 
   forall C:Prop, class C -> (forall x:A, P x -> C) -> C.

Lemma exc_intro : forall (A :Type)(P:A -> Prop) (x:A), P x -> exc P.
red;firstorder.
Save.

Lemma class_exc : forall (A :Type)(P:A -> Prop), class (exc P).
repeat red; intros.
apply H0; clear H0; red; intro.
apply H; clear H; red; intro H2. 
apply H2; intros; auto.
apply H0; apply (H1 x); auto.
Save.

Lemma exc_intro_class : forall (A:Type) (P:A -> Prop), ((forall x, ~ P x) -> False) -> exc P.
intros; apply class_exc; red; intros.
apply H; red; intros; auto.
apply H0; apply exc_intro with (x:=x);auto.
Save.

Lemma not_and_elim_left : forall A B, ~ (A /\ B) -> A -> ~B.
intuition.
Save.

Lemma not_and_elim_right : forall A B, ~ (A /\ B) -> B -> ~A.
intuition.
Save.

Hint Resolve class_orc class_and class_exc excluded_middle.

Lemma class_double_neg : forall P Q: Prop, class Q -> (P -> Q) -> ~ ~ P -> Q.
intros.
apply (excluded_middle (A:=P)); auto.
Save.

(** ** Extensional equality *)

Definition feq A B (f g : A -> B) := forall x, f x = g x.

Lemma feq_refl : forall A B (f:A->B), feq f f.
red; trivial.
Save.

Lemma feq_sym : forall A B (f g : A -> B), feq f g -> feq g f.
unfold feq; auto.
Save.

Lemma feq_trans : forall A B (f g h: A -> B), feq f g -> feq g h -> feq f h.
unfold feq; intros.
transitivity (g x); auto.
Save.

Hint Resolve feq_refl.
Hint Immediate feq_sym.
Hint Unfold feq.

Add Parametric Relation (A B : Type) : (A -> B) (feq (A:=A) (B:=B)) 
  reflexivity proved by (feq_refl (A:=A) (B:=B))
  symmetry proved by (feq_sym (A:=A) (B:=B))
  transitivity proved by (feq_trans (A:=A) (B:=B))
as feq_rel.

(** Computational version of elimination on CompSpec *)

Lemma CompSpec_rect : forall (A : Type) (eq lt : A -> A -> Prop) (x y : A)
       (P : comparison -> Type),
       (eq x y -> P Eq) ->
       (lt x y -> P Lt) ->
       (lt y x -> P Gt) 
    -> forall c : comparison, CompSpec eq lt x y c -> P c.
intros A eq lt x y P Peq Plt1 Plt2; destruct c; intro.
apply Peq; inversion H; auto.
apply Plt1; inversion H; auto.
apply Plt2; inversion H; auto.
Defined.

(** Decidability *)
Require Omega.

Lemma dec_sig_lt : forall P : nat -> Prop, (forall x, {P x}+{ ~ P x})
  -> forall n, {i | i < n /\ P i}+{forall i, i < n -> ~ P i}.
intros P Pdec.
induction n.
right; intros; exfalso; omega.
destruct IHn as [(i,(He1,He2))|Hn]; auto.
left; exists i; auto.
destruct (Pdec n) as [HP|HnP].
left; exists n; auto.
right; intros; assert (i < n \/ i = n) as [H1|H2]; subst; auto; try omega.
Defined.

Lemma dec_exists_lt : forall P : nat -> Prop, (forall x, {P x}+{ ~ P x})
  -> forall n, {exists i, i < n /\ P i}+{~ exists i, i < n /\ P i}.
intros P decP n; destruct (dec_sig_lt P decP n) as [(i,(H1,H2))|H].
left; exists i; auto.
right; intros (i,(H1,H2)); apply (H i H1 H2).
Save.

Definition eq_nat2_dec : forall p q : nat*nat, { p=q }+{~ p=q }.
intros (p1,p2) (q1,q2).
destruct (eq_nat_dec p1 q1) as [H1|H1]; subst.
destruct (eq_nat_dec p2 q2) as [H2|H2]; subst; auto with zarith.
right; intro Heq; apply H2.
injection Heq; trivial.
right; intro Heq; apply H1.
injection Heq; trivial.
Defined.

Lemma nat_compare_specT 
   : forall x y : nat, CompareSpecT (x = y) (x < y)%nat (y < x)%nat (nat_compare x y).
intros; apply CompareSpec2Type.
apply nat_compare_spec.
Save.


(** * Preliminary lemmas relating the ordre on nat and N *)

Require Export NArith.

Lemma N2Nat_lt_mono : forall n m, (n < m)%N <-> (N.to_nat n < N.to_nat m)%nat.
unfold N.lt; intros n m; rewrite N2Nat.inj_compare.
rewrite <- nat_compare_lt; split; auto.
Save.

Lemma N2Nat_le_mono : forall n m, (n <= m)%N <-> (N.to_nat n <= N.to_nat m)%nat.
unfold N.le; intros n m; rewrite N2Nat.inj_compare.
rewrite <- nat_compare_le; split; trivial.
Save.

Lemma N2Nat_inj_lt : forall n m, (n < m)%N -> (N.to_nat n < N.to_nat m)%nat.
intros; rewrite <- N2Nat_lt_mono; trivial.
Save.

Lemma N2Nat_inj_le : forall n m, (n <= m)%N -> (N.to_nat n <= N.to_nat m)%nat.
intros; rewrite <- N2Nat_le_mono; trivial.
Save.

Lemma N2Nat_inj_pos : forall n, (0 < n)%N -> (0 < N.to_nat n)%nat.
unfold N.lt; intros n; rewrite N2Nat.inj_compare.
rewrite <- nat_compare_lt; trivial.
Save.
Hint Resolve N2Nat_inj_lt N2Nat_inj_pos N2Nat_inj_le.

Lemma Nsucc_pred_pos: forall n : N, (0 < n)%N -> N.succ (N.pred n) = n.
intros; apply N.lt_succ_pred with (0%N); trivial.
Save.
Hint Resolve Nsucc_pred_pos.

Lemma Npos : forall n, (0 <= n)%N.
destruct n; discriminate.
Save.
Hint Resolve Npos.

Lemma Neq_lt_0 : forall n, (n=0)%N \/ (0<n)%N.
intros; destruct (N.lt_eq_cases 0 n) as (Heq,_); intros.
destruct Heq; auto.
Save.
Hint Resolve Neq_lt_0.

Lemma Nlt0_le1 : forall n, (0<n)%N -> (1<=n)%N.
intros; change (N.succ 0 <= n)%N; rewrite N.le_succ_l; auto.
Save.
Hint Immediate Nlt0_le1.

(* Tactic to deal with closed inequalities on N *)
Ltac Nineq :=
     match goal with 
      |- (N.le ?n ?m) => compute; discriminate
    | |- (N.lt ?n ?m) => compute; reflexivity
    | |- ~ (eq (A:=N) ?n ?m) => rewrite <- N.compare_eq_iff; compute; discriminate
    end.




