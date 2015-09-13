Set Implicit Arguments.
Set Strict Implicit.
Require Export Setoid.
Require Omega.

(** * Sets.v: Definition of sets as predicates over a type A *)

Section sets.
Variable A : Type.
Variable decA : forall x y :A, {x=y}+{x<>y}. 

Definition set := A -> Prop.
Definition full : set := fun (x:A) => True.
Definition empty : set := fun (x:A) => False.
Definition add (a:A) (P:set) : set := fun (x:A) => x=a \/ (P x).
Definition singl (a:A) :set := fun (x:A) => x=a.
Definition union (P Q:set) :set := fun (x:A) => (P x) \/ (Q x).
Definition compl (P:set) :set := fun (x:A) => ~P x.
Definition inter (P Q:set) :set := fun (x:A) => (P x) /\ (Q x).
Definition rem (a:A) (P:set) :set := fun (x:A) => x<>a /\ (P x).

(** ** Equivalence *)
Definition eqset (P Q:set) := forall (x:A), P x <-> Q x.

Implicit Arguments full [].
Implicit Arguments empty [].

Lemma eqset_refl : forall P:set, eqset P P.
unfold eqset; intuition.
Save.

Lemma eqset_sym : forall P Q:set, eqset P Q -> eqset Q P.
unfold eqset; firstorder.
Save.

Lemma eqset_trans : forall P Q R:set, 
   eqset P Q -> eqset Q R -> eqset P R.
unfold eqset; firstorder.
Save.

Hint Resolve eqset_refl.
Hint Immediate eqset_sym.

(** ** Setoid structure *)
Lemma set_setoid : Setoid_Theory set eqset.
split; red; auto.
exact eqset_trans.
Qed.

Add Setoid set eqset set_setoid as Set_setoid.

Add Morphism add : eqset_add.
unfold eqset,add; firstorder.
Save.

Add Morphism rem : eqset_rem.
unfold eqset,rem; firstorder.
Save.
Hint Resolve eqset_add eqset_rem.

Add Morphism union : eqset_union.
unfold eqset,union; firstorder.
Save.
Hint Immediate eqset_union.

Lemma eqset_union_left : 
  forall P1 Q P2,
   eqset P1 P2 -> eqset (union P1 Q) (union P2 Q).
auto.
Save.

Lemma eqset_union_right : 
  forall P Q1 Q2 ,
   eqset Q1 Q2 -> eqset (union P Q1) (union P Q2).
auto.
Save.

Hint Resolve eqset_union_left eqset_union_right.

Add Morphism inter : eqset_inter.
unfold eqset,inter; firstorder.
Save.
Hint Immediate eqset_inter.

Add Morphism compl : eqset_compl.
unfold eqset,compl; firstorder.
Save.
Hint Resolve eqset_compl.

Lemma eqset_add_empty : forall (a:A) (P:set), ~eqset (add a P) empty.
red; unfold eqset,empty,add; intros a P eqH; assert (H:=eqH a);  intuition.
Save.

(** ** Finite sets given as an enumeration of elements *)

Inductive finite (P: set) : Type := 
   fin_eq_empty : eqset P empty -> finite P
 | fin_eq_add : forall (x:A)(Q:set),
             ~ Q x-> finite Q -> eqset P (add x Q) -> finite P.
Hint Constructors finite.

Lemma fin_empty : (finite empty).
auto.
Defined.

Lemma fin_add : forall (x:A)(P:set),
             ~ P x -> finite P -> finite (add x P).
eauto.
Defined.

Lemma fin_eqset: forall (P Q : set), (eqset P Q)->(finite P)->(finite Q).
induction 2.
apply fin_eq_empty.
apply eqset_trans with P; auto.
apply fin_eq_add with x Q0; auto.
apply eqset_trans with P; auto.
Defined.

Hint Resolve fin_empty fin_add.

(** *** Emptyness is decidable for finite sets *)
Definition isempty (P:set) := eqset P empty.
Definition notempty (P:set) := not (eqset P empty).

Lemma isempty_dec : forall P, finite P -> {isempty P}+{notempty P}.
unfold isempty,notempty; destruct 1; auto.
right; red; intros.
apply (@eqset_add_empty x Q); auto.
apply eqset_trans with P; auto.
Save.

(** *** Size of a finite set *)
Fixpoint size (P:set) (f:finite P) {struct f}: nat :=
   match f with fin_eq_empty _ => 0%nat
              | fin_eq_add _ Q _ f' _ => S (size f')
   end.

Lemma size_eqset : forall P Q  (f:finite P) (e:eqset P Q),
    (size (fin_eqset e f)) = (size f).
induction f; simpl; intros; auto.
Save.

(** ** Inclusion *)
Definition incl (P Q:set) := forall x, P x -> Q x.

Lemma incl_refl : forall (P:set), incl P P.
unfold incl; intuition.
Save.

Lemma incl_trans : forall (P Q R:set), 
incl P Q -> incl Q R -> incl P R.
unfold incl; intuition.
Save.

Lemma eqset_incl : forall (P Q : set),  eqset P Q -> incl P Q.
unfold eqset, incl; firstorder.
Save.

Lemma eqset_incl_sym : forall (P Q : set), eqset P Q -> incl Q P.
unfold eqset, incl; firstorder.
Save.

Lemma eqset_incl_intro : 
forall (P Q : set), incl P Q -> incl Q P -> eqset P Q.
unfold eqset, incl; firstorder.
Save.

Hint Resolve incl_refl incl_trans eqset_incl_intro. 
Hint Immediate eqset_incl eqset_incl_sym. 

(** ** Properties of operations on sets *)

Lemma incl_empty : forall P, incl empty P.
unfold incl,empty; intuition.
Save.


Lemma incl_empty_false : forall P a, incl P empty -> ~ P a.
unfold incl; firstorder.
Save.

Lemma incl_add_empty : forall (a:A) (P:set), ~ incl (add a P) empty.
red; unfold incl,empty,add; intros a P eqH; assert (H:=eqH a);  intuition.
Save.

Lemma eqset_empty_false : forall P a, eqset P empty -> P a -> False.
unfold eqset; firstorder.
Save.

Hint Immediate incl_empty_false eqset_empty_false incl_add_empty.

Lemma incl_rem_stable :   forall a P Q, incl P Q -> incl (rem a P) (rem a Q).
unfold incl,rem;intuition.
Save.

Lemma incl_add_stable :   forall a P Q, incl P Q -> incl (add a P) (add a Q).
unfold incl,add;intuition.
Save.

Lemma incl_rem_add_iff : 
  forall a P Q, incl (rem a P) Q <-> incl P (add a Q).
unfold rem, add, incl; intuition.
case (decA x a); auto.
case (H x); intuition.
Save.

Lemma incl_rem_add: 
  forall (a:A) (P Q:set), 
     (P a) -> incl Q (rem a P) -> incl (add a Q) P.
unfold rem, add, incl; intros; auto.
case H1; intro; subst; auto.
case (H0 x); auto.
Save.

Lemma incl_add_rem : 
  forall (a:A) (P Q:set), 
     ~ Q a -> incl (add a Q) P -> incl Q (rem a P) .
unfold rem, add, incl; intros; auto.
case (decA x a); intros; auto.
subst; case H; auto.
Save.

Hint Immediate incl_rem_add incl_add_rem.

Lemma eqset_rem_add : 
 forall (a:A) (P Q:set), 
     (P a) -> eqset Q (rem a P)  -> eqset (add a Q) P.
intros; assert (incl Q (rem a P)); auto.
assert (incl (rem a P) Q); auto.
case (incl_rem_add_iff a P Q); auto.
Save.

Lemma eqset_add_rem : 
 forall (a:A) (P Q:set), 
     ~ Q a -> eqset (add a Q) P -> eqset Q (rem a P).
intros; assert (incl (add a Q) P); auto.
assert (incl P (add a Q)); auto.
case (incl_rem_add_iff a P Q); auto.
Save.

Hint Immediate eqset_rem_add eqset_add_rem.

Lemma add_rem_eq_eqset : 
  forall x (P:set), eqset (add x (rem x P)) (add x P).
unfold eqset, add, rem; intuition.
case (decA x0 x); intuition.
Save.

Lemma add_rem_diff_eqset : 
  forall x y (P:set), 
  x<>y -> eqset (add x (rem y P)) (rem y (add x P)).
unfold eqset, add, rem; intuition.
subst; auto.
Save.

Lemma add_eqset_in : 
  forall x (P:set), P x -> eqset (add x P) P.
unfold eqset, add; intuition.
subst;auto.
Save.

Hint Resolve add_rem_eq_eqset add_rem_diff_eqset add_eqset_in.


Lemma add_rem_eqset_in : 
  forall x (P:set), P x -> eqset (add x (rem x P)) P.
intros; apply eqset_trans with (add x P); auto.
Save.

Hint Resolve add_rem_eqset_in.

Lemma rem_add_eq_eqset : 
  forall x (P:set), eqset (rem x (add x P)) (rem x P).
unfold eqset, add, rem; intuition.
Save.

Lemma rem_add_diff_eqset : 
  forall x y (P:set), 
  x<>y -> eqset (rem x (add y P)) (add y (rem x P)).
intros; apply eqset_sym; auto.
Save.

Lemma rem_eqset_notin : 
  forall x (P:set), ~P x -> eqset (rem x P) P.
unfold eqset, rem; intuition.
subst;auto.
Save.

Hint Resolve rem_add_eq_eqset rem_add_diff_eqset rem_eqset_notin.

Lemma rem_add_eqset_notin : 
  forall x (P:set), ~P x -> eqset (rem x (add x P)) P.
intros; apply eqset_trans with (rem x P); auto.
Save.

Hint Resolve rem_add_eqset_notin.


Lemma rem_not_in : forall x (P:set), ~ rem x P x.
unfold rem; intuition.
Save.

Lemma add_in : forall x (P:set), add x P x.
unfold add; intuition.
Save.

Lemma add_in_eq : forall x y P, x=y -> add x P y.
unfold add; intuition.
Save.

Lemma add_intro : forall x (P:set) y, P y -> add x P y.
unfold add; intuition.
Save.

Lemma add_incl : forall x (P:set), incl P (add x P).
unfold incl,add; intuition.
Save.

Lemma add_incl_intro : forall x (P Q:set), (Q x) -> (incl P Q) -> (incl (add x P) Q).
unfold incl,add; intuition; subst; intuition.
Save.

Lemma rem_incl : forall x (P:set), incl (rem x P) P.
unfold incl, rem; intuition.
Save.

Hint Resolve rem_not_in add_in rem_incl add_incl.

Lemma union_sym : forall P Q : set,
      eqset (union P Q) (union Q P).
unfold eqset, union; intuition.
Save.

Lemma union_empty_left : forall P : set,
      eqset P (union P empty).
unfold eqset, union, empty; intuition.
Save.

Lemma union_empty_right : forall P : set,
      eqset P (union empty P).
unfold eqset, union, empty; intuition.
Save.

Lemma union_add_left : forall (a:A) (P Q: set),
      eqset (add a (union P Q)) (union P (add a Q)).
unfold eqset, union, add; intuition.
Save.

Lemma union_add_right : forall (a:A) (P Q: set),
      eqset (add a (union P Q)) (union (add a P) Q).
unfold eqset, union, add; intuition.
Save.

Hint Resolve union_sym union_empty_left union_empty_right
union_add_left union_add_right.

Lemma union_incl_left : forall P Q, incl P (union P Q).
unfold incl,union; intuition.
Save.

Lemma union_incl_right : forall P Q, incl Q (union P Q).
unfold incl,union; intuition.
Save.

Lemma union_incl_intro : forall P Q R, incl P R -> incl Q R -> incl (union P Q) R.
unfold incl,union; intuition.
Save.

Hint Resolve union_incl_left union_incl_right union_incl_intro.

Lemma incl_union_stable : forall P1 P2 Q1 Q2,
	incl P1 P2 -> incl Q1 Q2 -> incl (union P1 Q1) (union P2 Q2).
intros; apply union_incl_intro; unfold incl,union; intuition.
Save.
Hint Immediate incl_union_stable.

Lemma inter_sym : forall P Q : set,
      eqset (inter P Q) (inter Q P).
unfold eqset, inter; intuition.
Save.

Lemma inter_empty_left : forall P : set,
      eqset empty (inter P empty).
unfold eqset, inter, empty; intuition.
Save.

Lemma inter_empty_right : forall P : set,
      eqset empty (inter empty P).
unfold eqset, inter, empty; intuition.
Save.

Lemma inter_add_left_in : forall (a:A) (P Q: set),
      (P a) -> eqset (add a (inter P Q)) (inter P (add a Q)).
unfold eqset, inter, add; split; intuition.
subst; auto.
Save.

Lemma inter_add_left_out : forall (a:A) (P Q: set),
      ~ P a -> eqset (inter P Q) (inter P (add a Q)).
unfold eqset, inter, add; split; intuition.
subst; case H; auto.
Save.

Lemma inter_add_right_in : forall (a:A) (P Q: set),
      Q a -> eqset (add a (inter P Q)) (inter (add a P) Q).
unfold eqset, inter, add; split; intuition.
subst; auto.
Save.

Lemma inter_add_right_out : forall (a:A) (P Q: set),
      ~ Q a -> eqset (inter P Q) (inter (add a P) Q).
unfold eqset, inter, add; split; intuition.
subst; case H; auto.
Save.

Hint Resolve inter_sym inter_empty_left inter_empty_right
inter_add_left_in inter_add_left_out inter_add_right_in inter_add_right_out.

(** ** Generalized union *)
Definition gunion (I:Type)(F:I->set) : set := fun z => exists i, F i z.

Lemma gunion_intro : forall I (F:I->set) i, incl (F i) (gunion F). 
red; intros; exists i; auto.
Save.

Lemma gunion_elim : forall I (F:I->set) (P:set), (forall i, incl (F i) P) -> incl (gunion F) P.
red; intros I F P H x (i,Hi).
apply (H i x); auto.
Save.

Lemma gunion_monotonic : forall I (F G : I -> set), 
      (forall i, incl (F i) (G i))-> incl (gunion F) (gunion G).
intros I F G H x (i,Hi).
exists i; apply (H i x); trivial.
Save.

(** ** Decidable sets *)
Definition dec (P:set) := forall x, {P x}+{ ~ P x}.

Definition dec2bool (P:set) : dec P -> A -> bool := 
   fun p x => if p x then true else false.

Lemma compl_dec : forall P, dec P -> dec (compl P).
intros P dP x; destruct (dP x); auto.
Defined.

Lemma inter_dec : forall P Q, dec P -> dec Q -> dec (inter P Q).
intros P Q dP dQ x; unfold inter; destruct (dP x).
destruct (dQ x); intuition.
right; intuition.
Defined.

Lemma union_dec : forall P Q, dec P -> dec Q -> dec (union P Q).
intros P Q dP dQ x; unfold union; destruct (dP x); auto.
destruct (dQ x); intuition.
Defined.

Hint Resolve compl_dec inter_dec union_dec.

(** ** Removing an element from a finite set *)

Lemma finite_rem :  forall (P:set) (a:A),
   finite P -> finite (rem a P).
induction 1; intuition.
apply fin_eq_empty.
unfold rem,empty,eqset; intuition.
apply (eqset_empty_false x e); auto.
case (decA x a); intros.
apply fin_eqset with Q; subst; auto.
apply eqset_add_rem; auto.
apply fin_eq_add with x (rem a Q); auto.
subst; unfold rem; intuition.
apply eqset_trans with (rem a (add x Q)); auto.
Defined.

Lemma size_finite_rem: 
   forall (P:set) (a:A) (f:finite P), 
    (P a) -> size f = S (size (finite_rem a f)).
induction f;  intros.
case (eqset_empty_false a e H).
simpl; case (decA x a); simpl; intros.
case e0; unfold eq_rect_r;simpl; auto.
rewrite size_eqset; auto.
rewrite IHf; auto.
case (e a); unfold add; intuition.
case n0; auto.
Save.



(* bug lie a intuition
Lemma size_finite_rem: 
   forall (P:set) (a:A) (f:finite P), 
    (P a) -> size f = S (size (finite_rem a f)).
induction f;  intuition.
case (eqset_empty_false a e H).
simpl; case (decA x a); simpl; intros.
case e0; unfold eq_rect_r;simpl; auto.
rewrite size_eqset; auto.
rewrite IHf; auto.
case (e a); unfold add; intuition.
case f0; auto.
Save.
*)
Require Import Arith.

Lemma size_incl : 
  forall (P:set)(f:finite P) (Q:set)(g:finite Q), 
  (incl P Q)-> size f <= size g.
induction f; simpl; intros; auto with arith.
apply le_trans with (S (size (finite_rem x g))).
apply le_n_S.
apply IHf with (g:= finite_rem x g); auto.
apply incl_trans with (rem x P); auto.
apply incl_add_rem; auto.
apply incl_rem_stable; auto.
rewrite <- size_finite_rem; auto.
case (e x); intuition.
Save.

Lemma size_unique : 
  forall (P:set)(f:finite P) (Q:set)(g:finite Q), 
  (eqset P Q)-> size f = size g.
intros; apply le_antisym; apply size_incl; auto.
Save.



Lemma finite_incl : forall P:set,
   finite P -> forall Q:set, dec Q -> incl Q P -> finite Q.
intros P FP; elim FP; intros; auto.
apply fin_eq_empty.
unfold empty,eqset in *|-*; intuition.
case (e x); auto.
case (X0 x); intros.
apply fin_eq_add with (x:=x) (Q:=(rem x Q0)); auto.
apply X.
unfold dec,rem.
intro y; case (decA x y); intro.
case (X0 y); subst; intuition.
case (X0 y); intuition.
case (incl_rem_add_iff x Q0 Q); intuition.
apply H1; apply incl_trans with P0; auto.
apply eqset_sym; auto.
apply X; auto.
red; intros.
case (e x0); intuition.
case H1; intuition; subst; auto.
case n0; auto.
Save.

Lemma finite_dec : forall P:set, finite P -> dec P.
red; intros P FP; elim FP; intros.
right; intro; apply (eqset_empty_false x e); auto.
case (e x0); unfold add; intuition.
case (X x0); intuition.
case (decA x0 x); intuition.
Save.

Lemma fin_add_in : forall (a:A) (P:set), finite P -> finite (add a P).
intros a P FP; case (finite_dec FP a); intro.
apply fin_eqset with P; auto.
apply eqset_sym; auto.
apply fin_add; auto.
Defined.

Lemma finite_union : 
     forall P Q, finite P -> finite Q -> finite (union P Q).
intros P Q FP FQ; elim FP; intros.
apply fin_eqset with Q; auto.
apply eqset_trans with (union empty Q); auto.
apply fin_eqset with (add x (union Q0 Q)); auto.
apply eqset_trans with (union (add x Q0) Q); auto. 
apply fin_add_in; auto.
Defined.
 
Lemma finite_full_dec : forall P:set, finite full -> dec P -> finite P.
intros; apply finite_incl with full; auto.
unfold full,incl; auto.
Save.

Require Import Lt.

(** *** Filter operation *)

Lemma finite_inter : forall P Q, dec P -> finite Q -> finite (inter P Q).
intros P Q decP FQ.
induction FQ.
constructor 1.
apply eqset_trans with (inter P empty); auto.
case (decP x); intro.
constructor 2 with x (inter P Q); auto.
unfold inter; intuition.
rewrite e.
unfold add,inter; red; intuition.
subst; auto.
apply fin_eqset with (inter P Q); auto.
rewrite e.
unfold add,inter; red; intuition.
subst; intuition.
Defined.

Lemma size_inter_empty : forall P Q (decP:dec P) (e:eqset Q empty), 
   size (finite_inter decP (fin_eq_empty e))=O.
trivial.
Save.

Lemma size_inter_add_in : 
     forall P Q R (decP:dec P)(x:A)(nq:~Q x)(FQ:finite Q)(e:eqset R (add x Q)),
      P x ->size (finite_inter decP (fin_eq_add nq FQ e))=S (size (finite_inter decP FQ)).
intros; simpl.
case (decP x); intro; trivial; contradiction.
Save.

Lemma size_inter_add_notin : 
     forall P Q R (decP:dec P)(x:A)(nq:~Q x)(FQ:finite Q)(e:eqset R (add x Q)),
   ~ P x -> size (finite_inter decP (fin_eq_add nq FQ e))=size (finite_inter decP FQ).
intros; simpl.
case (decP x); intro; try contradiction.
rewrite size_eqset; trivial.
Save.

Lemma size_inter_incl : forall P Q (decP:dec P)(FP:finite P)(FQ:finite Q), 
    (incl P Q) -> size (finite_inter decP FQ)=size FP.
intros; apply size_unique.
unfold inter; intro.
generalize (H x); intuition.
Save.

(** *** Selecting elements in a finite set *)

Fixpoint nth_finite (P:set) (k:nat) (PF : finite P) {struct PF}: (k < size PF) -> A := 
  match PF as F return (k < size F) -> A with 
       fin_eq_empty H => (fun (e : k<0) => match lt_n_O k e with end)
     | fin_eq_add x Q nqx fq eqq => 
           match k as k0 return k0<S (size fq)->A with 
                O => fun e => x
         | (S k1) => fun (e:S k1<S (size fq)) => nth_finite fq (lt_S_n k1 (size fq) e)
           end
  end.


(** A set with size > 1 contains at least 2 different elements **)

Lemma select_non_empty : forall (P:set), finite P -> notempty P -> sigT P.
destruct 1; intros.
case H; auto.
exists x; case (e x); intuition.
Defined.

Lemma select_diff : forall (P:set) (FP:finite P),
     (1 < size FP)%nat -> sigT (fun x => sigT (fun y => P x /\ P y /\ x<>y)).
destruct FP; simpl; intros.
absurd (1<0); omega.
exists x; destruct FP; simpl in H.
absurd (1<1); omega.
exists x0; intuition.
case (e x); auto.
case (e0 x0); case (e x0); unfold add; intuition.
subst; case (e0 x0); intuition.
Save.

End sets.

Hint Resolve eqset_refl.
Hint Resolve eqset_add eqset_rem.
Hint Immediate eqset_sym finite_dec finite_full_dec eqset_incl eqset_incl_sym eqset_incl_intro.

Hint Resolve incl_refl.
Hint Immediate incl_union_stable.
Hint Resolve union_incl_left union_incl_right union_incl_intro incl_empty rem_incl
incl_rem_stable incl_add_stable.

Hint Constructors finite.
Hint Resolve add_in add_in_eq add_intro add_incl add_incl_intro union_sym union_empty_left union_empty_right
union_add_left union_add_right finite_union eqset_union_left 
eqset_union_right.
Implicit Arguments full [].
Implicit Arguments empty [].

Add Parametric Relation (A:Type) : (set A) (eqset (A:=A))
      reflexivity proved by (eqset_refl (A:=A))
      symmetry proved by (eqset_sym (A:=A))
      transitivity proved by (eqset_trans (A:=A))
as eqset_rel.

Add Parametric Relation (A:Type) : (set A) (incl (A:=A))
      reflexivity proved by (incl_refl (A:=A))
      transitivity proved by (incl_trans (A:=A))
as incl_rel.
