Require Import ssreflect ssrbool ssrfun ssrnat eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Order.

Definition axiom T (r : rel T) := [/\ reflexive r, antisymmetric r, transitive r &
                                   (forall m n : T, (r m n) || (r n m))].

Section ClassDef.

Record mixin_of T := Mixin { r : rel T; _ : axiom r }.

Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Equality.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Notation ordType := type.
Notation ordMixin := mixin_of.
Notation OrdType T m := (@pack T m _ _ id).
Notation "[ 'ordType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'ordType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ordType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ordType'  'of'  T ]") : form_scope.

End Exports.

End Order.
Export Order.Exports.

Definition leqX_op T := Order.r (Order.mixin (Order.class T)).

Lemma leqXE T x : leqX_op x = Order.r (Order.mixin (Order.class T)) x.
Proof. by []. Qed.

Lemma leqXordP T : Order.axiom (@leqX_op T).
Proof. by case: T => ? [] /= base []. Qed.
Implicit Arguments leqXordP [T].

Prenex Implicits leqX_op leqXordP.

(* Declare legacy Arith operators in new scope. *)

Delimit Scope ssr_nat_scope with ssr_nat.

Notation "m <= n" := (le m n) : ssr_nat_scope.
Notation "m < n" := (lt m n) : ssr_nat_scope.
Notation "m >= n" := (ge m n) : ssr_nat_scope.
Notation "m > n" := (gt m n) : ssr_nat_scope.

(* Rebind scope delimiters, reserving a scope for the "recursive",     *)
(* i.e., unprotected version of operators.                             *)

Delimit Scope ord_scope with Ord.
Open Scope ord_scope.

Notation "m <= n" := (leqX_op m n) : ord_scope.
Notation "m < n"  := ((m != n) && (m <= n)) : ord_scope.
Notation "m >= n" := (n <= m) (only parsing) : ord_scope.
Notation "m > n"  := (n < m) (only parsing)  : ord_scope.

Notation "m <= n <= p" := ((m <= n) && (n <= p)) : ord_scope.
Notation "m < n <= p" := ((m < n) && (n <= p)) : ord_scope.
Notation "m <= n < p" := ((m <= n) && (n < p)) : ord_scope.
Notation "m < n < p" := ((m < n) && (n < p)) : ord_scope.


Section POrderTheory.

Variable T : ordType.
Implicit Type n m : T.

(* For sorting, etc. *)
Definition geqX := [rel m n | (m:T) >= n].
Definition ltnX := [rel m n | (m:T) < n].
Definition gtnX := [rel m n | (m:T) > n].

Lemma leqXnn n : n <= n.
Proof. have:= (@leqXordP T); by rewrite /Order.axiom /reflexive => [] [] refl _ _. Qed.
Hint Resolve leqXnn.

Lemma ltnXn n : n < n = false.
Proof. by rewrite eq_refl. Qed.

Lemma eq_leqX n m : n = m -> n <= m.
Proof. by move->. Qed.

Lemma ltnX_eqF m n : m < n -> m == n = false.
Proof. by move/andP => [] /negbTE. Qed.

Lemma gtnX_eqF m n : m < n -> n == m = false.
Proof. rewrite [(n == m)]eq_sym. by apply ltnX_eqF. Qed.

Lemma leqX_eqVltnX m n : (m <= n) = (m == n) || (m < n).
Proof. by case: (altP (m =P n)) => [/= -> | /= _]; first by rewrite (leqXnn n). Qed.

Lemma ltnX_neqAleqX m n : (m < n) = (m != n) && (m <= n).
Proof. by []. Qed.

Lemma anti_leqX : antisymmetric (@leqX_op T).
Proof. have:= (@leqXordP T); by rewrite /Order.axiom => [] []. Qed.

Lemma eqn_leqX m n : (m == n) = (m <= n <= m).
Proof.
  apply/(sameP idP); apply(iffP idP).
  - move=> H; have:= anti_leqX; rewrite /antisymmetric => Ha; by rewrite (Ha _ _ H).
  - move/eqP => ->; by rewrite leqXnn.
Qed.

Lemma leqX_trans n m p : m <= n -> n <= p -> m <= p.
Proof.
  have:= (@leqXordP T); rewrite /Order.axiom /transitive => [] [] _ _ H _; by apply H.
Qed.

Lemma leqX_ltnX_trans n m p : m <= n -> n < p -> m < p.
Proof.
  move=> H1 /andP [] Hneq H2; rewrite (leqX_trans H1 H2) andbT.
  move: Hneq; apply contraLR => /=.
  rewrite !negbK [n == p]eqn_leqX => /eqP Heq; rewrite Heq in H1.
  by rewrite H1 H2.
Qed.

Lemma ltnX_leqX_trans n m p : m < n -> n <= p -> m < p.
Proof.
  move=> /andP [] Hneq H1 H2; rewrite (leqX_trans H1 H2) andbT.
  move: Hneq; apply contraLR => /=.
  rewrite !negbK [m == n]eqn_leqX => /eqP Heq; rewrite Heq; rewrite Heq in H1.
  by rewrite H1 H2.
Qed.

Lemma ltnXW m n : m < n -> m <= n.
Proof. by move/andP => []. Qed.

Lemma ltnX_trans n m p : m < n -> n < p -> m < p.
Proof. move=> lt_mn /ltnXW. exact: ltnX_leqX_trans. Qed.

End POrderTheory.


(* Needs total ordering *)
Section OrdTheory.

Variable T : ordType.
Implicit Type n m : T.

Lemma leqX_total m n : (m <= n) || (m >= n).
Proof. have:= (@leqXordP T); rewrite /Order.axiom => [] [] _ _ _; by apply. Qed.

Lemma leqXNgtnX n m : (m <= n) = ~~ (n < m).
Proof.
  case: (orP (leqX_total m n)) => H.
  - rewrite H negb_and negbK; case (boolP (n <= m)) => //=.
    * by rewrite eqn_leqX H => ->.
    * by rewrite orbT.
  - by rewrite eqn_leqX H /= negb_and negbK /= orbF.
Qed.

Lemma ltnXNgeqX m n : (m < n) = ~~ (n <= m).
Proof. by rewrite [n <= m]leqXNgtnX negbK. Qed.


(* Comparison predicates. *)

CoInductive leqX_xor_gtnX m n : bool -> bool -> Set :=
  | LeqXNotGtnX of m <= n : leqX_xor_gtnX m n true false
  | GtnXNotLeqX of n < m  : leqX_xor_gtnX m n false true.

Lemma leqXP m n : leqX_xor_gtnX m n (m <= n) (n < m).
Proof.
  by rewrite ltnXNgeqX; case le_mn: (m <= n); constructor; rewrite // ltnXNgeqX le_mn.
Qed.

CoInductive ltnX_xor_geqX m n : bool -> bool -> Set :=
  | LtnXNotGeqX of m < n  : ltnX_xor_geqX m n false true
  | GeqXNotLtnX of n <= m : ltnX_xor_geqX m n true false.

Lemma ltnXP m n : ltnX_xor_geqX m n (n <= m) (m < n).
Proof. by case: leqXP; constructor. Qed.

CoInductive compareX m n : bool -> bool -> bool -> Set :=
  | CompareXLt of m < n : compareX m n true false false
  | CompareXGt of m > n : compareX m n false true false
  | CompareXEq of m = n : compareX m n false false true.

Lemma compareP m n : compareX m n (m < n) (n < m) (m == n).
Proof.
  rewrite eqn_leqX; case: ltnXP; first by constructor.
  by rewrite leqX_eqVltnX orbC; case: leqXP => /=; constructor; first by apply/eqP.
Qed.

End OrdTheory.

Fact leq_order : Order.axiom leq.
Proof.
  split.
  - move=> n; by apply leqnn.
  - exact anti_leq.
  - move=> m n p; by apply leq_trans.
  - exact leq_total.
Qed.

Definition nat_ordMixin := Order.Mixin leq_order.
Canonical nat_ordType := Eval hnf in OrdType nat nat_ordMixin.

Lemma leqXnatE m n : (n <= m)%Ord = (n <= m)%N.
Proof. by rewrite leqXE /=. Qed.

Lemma ltnXnatE m n : (n < m)%Ord = (n < m)%N.
Proof. by rewrite leqXE ltn_neqAle. Qed.

Hint Resolve leqXnn ltnX ltnXW.
