(** * Ccpo.v: Specification and properties of a cpo *)

Require Export Arith.
Require Export Omega.

Require Export Coq.Classes.SetoidTactics.
Require Export Coq.Classes.SetoidClass.
Require Export Coq.Classes.Morphisms.

Open Local Scope signature_scope.
Delimit Scope O_scope with O.
Local Open Scope O_scope.

(** ** Ordered type *)

Definition eq_rel {A} (E1 E2:relation A) := forall x y, E1 x y <-> E2 x y.

Class Order {A} (E:relation A)  (R:relation A) := 
  {reflexive :> Reflexive R;
   order_eq : forall x y, R x y /\ R y x <-> E x y;
   transitive :> Transitive R }.

Generalizable Variables A E R.

Instance OrderEqRefl `{Order A E R} : Reflexive E.
destruct H as  (rO,aO,tO).
intros x.
rewrite <- aO; intuition.
Save.

Instance OrderEqSym `{Order A E R} : Symmetric E.
destruct H as (rO,aO,tO).
intros x y e.
pose (aO x y); pose (aO y x); intuition.
Save.

Instance OrderEqTrans `{Order A E R} : Transitive E.
destruct H as (rO,aO,tO).
intros x y z e1 e2.
pose (aO x y); pose (aO y z); pose (aO x z); pose (tO x y z); pose (tO z y x); intuition.
Save.

Instance OrderEquiv `{Order A E R} : Equivalence E.
split; auto with *.
apply OrderEqTrans.
Save.
Opaque OrderEquiv.

Class ord A := 
   {  Oeq : relation A;
      Ole : relation A;
      order_rel :> Order Oeq Ole }.


Lemma OrdSetoid `(o:ord A) : Setoid A.
intros. split with Oeq. apply OrderEquiv. 
(* compatibility with Jan's version *)
(*try (split; [apply OrderEqRefl| apply OrderEqSym| apply OrderEqTrans]).*)
Defined.

(*
Typeclasses Opaque equiv.

Instance OrdEquiv `(o:ord A) : Equivalence (equiv (A:=A)).
intros A (E,R,O); apply OrderEquiv.
Save.
*)

Add Parametric Relation {A} {o:ord A} : A (@Oeq _ o) 
reflexivity proved  by OrderEqRefl
symmetry proved  by OrderEqSym
transitivity proved by OrderEqTrans
as Oeq_setoid. 

(** printing <= $\le$ # &le; # *)
(** printing == $\equiv$ # &asymp; # *)

Infix "<=" := Ole : O_scope.
Infix "==" := Oeq : type_scope.

Definition Oge {O} {o:ord O} := fun (x y:O) => y <= x.
Infix ">=" := Oge : O_scope.


Lemma Ole_refl_eq : forall {O} {o:ord O} (x y:O), x == y -> x <= y.
intros O (oeq,ole,(rO,aO,tO)) x y; simpl; pose (aO x y); intuition.
Save.

Hint Immediate @Ole_refl_eq.

Lemma Ole_refl_eq_inv : forall {O} {o:ord O} (x y:O), x == y -> y <= x.
intros O (oeq,ole,(rO,aO,tO)) x y; simpl; pose (aO x y); intuition.
Save.

Hint Immediate @Ole_refl_eq_inv.

Lemma Ole_trans : forall {O} {o:ord O} (x y z:O), x <= y -> y <= z -> x <= z.
intros O (oeq,ole,(rO,aO,tO)) x y z H1 H2; simpl; apply tO with y; auto.
Save.

Lemma Ole_refl : forall {O} {o:ord O} (x:O), x <= x.
intros O (oeq,ole,(rO,aO,tO)) x; simpl; auto.
Save.

Hint Resolve @Ole_refl.

Add Parametric Relation {A} {o:ord A} : A (@Ole _ o) 
reflexivity proved  by Ole_refl
transitivity proved by Ole_trans
as Ole_setoid. 

Lemma Ole_antisym : forall {O} {o:ord O} (x y:O), x <= y -> y <= x -> x == y.
intros O (oeq,ole,(rO,aO,tO)) x y; simpl; pose (aO x y); intuition.
Save.
Hint Immediate @Ole_antisym.

Lemma Oeq_refl : forall {O} {o:ord O} (x:O), x == x.
intros; apply OrderEqRefl.
Save.
Hint Resolve @Oeq_refl.

Lemma Oeq_refl_eq : forall {O} {o:ord O} (x y:O), x = y -> x == y.
intros O o x y H; rewrite H; auto.
Save.
Hint Resolve @Oeq_refl_eq.

Lemma Oeq_sym : forall {O} {o:ord O} (x y:O), x == y -> y == x.
intros; apply OrderEqSym; trivial.
Save.

Lemma Oeq_le : forall {O} {o:ord O} (x y:O), x == y -> x <= y.
intros O (oeq,ole,(rO,aO,tO)) x y; simpl; pose (aO x y); intuition.
Save.

Lemma Oeq_le_sym : forall {O} {o:ord O} (x y:O), x == y -> y <= x.
intros O (oeq,ole,(rO,aO,tO)) x y; simpl; pose (aO x y); intuition.
Save.

Hint Resolve @Oeq_le.
Hint Immediate @Oeq_sym @Oeq_le_sym.

Lemma Oeq_trans 
   : forall {O} {o:ord O} (x y z:O), x == y -> y == z -> x == z.
intros; apply OrderEqTrans with y; trivial.
Save.
Hint Resolve @Oeq_trans.



Add Parametric Morphism `(o:ord A): (Ole (ord:=o)) 
with signature (Oeq (A:=A) ==> Oeq (A:=A) ==> iff) as Ole_eq_compat_iff.
intros x1 y1 e1 x2 y2 e2.
split; intros.
transitivity x1; auto.
transitivity x2; auto.
transitivity y1; auto.
transitivity y2; auto.
Save.

(** Equivalence of orders *)

Definition eq_ord {O} (o1 o2:ord O) := eq_rel (Ole (ord:=o1)) (Ole (ord:=o2)).

Lemma eq_ord_equiv : forall {O} (o1 o2:ord O), eq_ord o1 o2 ->
      eq_rel (Oeq (ord:=o1)) (Oeq (ord:=o2)).
intros O (eq1,le1,(r1,as1,t1)) (eq2,le2,(r2,as2,t2)); unfold eq_ord, eq_rel; simpl; intros.
transitivity (le2 x y /\ le2 y x); auto.
rewrite <- as1; auto.
repeat rewrite H; reflexivity.
Save.

(** printing ==> %\ensuremath\Longrightarrow% #&#8702;# *)

Lemma Ole_eq_compat : 
     forall {O} {o:ord O} (x1 x2 : O),
       x1 == x2 -> forall x3 x4 : O, x3 == x4 -> x1 <= x3 -> x2 <= x4.
intros o x1 x2 H1 x3 x4 H2 H3; case (Ole_eq_compat_iff o x1 x2 H1 x3 x4 H2); auto.
Save.

Lemma Ole_eq_right : forall {O} {o:ord O} (x y z: O),
             x <= y -> y == z -> x <= z.
intros; apply Ole_eq_compat with x y; auto.
Save.

Lemma Ole_eq_left : forall {O} {o:ord O} (x y z: O),
             x == y -> y <= z -> x <= z.
intros; apply Ole_eq_compat with y z; auto.
Save.

Add Parametric Morphism `{o:ord A} : (Oeq (A:=A)) 
       with signature Oeq ==> Oeq ==>  iff as Oeq_iff_morphism.
intros.
rewrite H.
rewrite H0.
intuition.
Qed.

Add Parametric Morphism `{o:ord A} : (Ole (A:=A)) 
       with signature Oeq ==> Oeq ==>  iff as Ole_iff_morphism.
intros.
rewrite H.
rewrite H0.
intuition.
Qed.

Add Parametric Morphism `{o:ord A} : (Ole (A:=A)) 
       with signature Ole --> Ole ==>  Basics.impl as Ole_impl_morphism.
red; intros.
transitivity x; trivial.
transitivity x0; trivial.
Qed.

(** ** Definition and properties of [ x < y ] *)
Definition Olt `{o:ord A} (r1 r2:A) : Prop := (r1 <= r2) /\ ~ (r1 == r2).

Infix "<" := Olt : O_scope.

Lemma Olt_eq_compat `{o:ord A} :
forall x1 x2 : A, x1 == x2 -> forall x3 x4 : A, x3 == x4 -> x1 < x3 -> x2 < x4.
unfold Olt; intros x1 x2 eq1 x3 x4 eq2 (Hle,Hne).
rewrite <- eq1; rewrite <- eq2; auto.
Save.

Add Parametric Morphism `{o:ord A} : (Olt (A:=A))
with signature Oeq ==> Oeq ==> iff as Olt_iff_morphism.
intros x1 x2 eq1 x3 x4 eq2; split.
exact (Olt_eq_compat _ _ eq1 _ _ eq2).
intros; apply Olt_eq_compat with x2 x4; auto.
Save.

Lemma Olt_neq `{o:ord A} : forall x y:A, x < y -> ~ x == y.
unfold Olt; intuition.
Save.

Lemma Olt_neq_rev `{o:ord A} : forall x y:A, x < y -> ~ y == x.
intros x y (Hle,Hne) H; auto.
Save.

Lemma Olt_le `{o:ord A} : forall x y, x < y -> x <= y.
intros x y (Hle,Hne); auto.
Save.

Lemma Olt_notle `{o:ord A} : forall x y, x < y -> ~ y <= x.
intros x y (Hle,Hne) H; auto.
Save.

Lemma Olt_trans `{o:ord A} : forall x y z:A, x < y -> y < z -> x < z.
intros x y z (Hle1,Hne1) (Hle2,Hne2); split.
transitivity y; trivial.
intro Heq; apply Hne2.
apply Ole_antisym; auto.
rewrite <- Heq; trivial.
Save.

Lemma Ole_diff_lt `{o:ord A} : forall x y : A,  x <= y -> ~ x == y -> x < y.
red; intuition.
Save.

Lemma Ole_notle_lt `{o:ord A} : forall x y : A,  x <= y -> ~ y <= x -> x < y.
red; intuition.
Save.

Hint Immediate @Olt_neq @Olt_neq_rev @Olt_le @Olt_notle.
Hint Resolve @Ole_diff_lt.

Lemma Olt_antirefl `{o:ord A} : forall x:A, ~ x < x.
unfold Olt; intuition.
Save.


Lemma Ole_lt_trans `{o:ord A} : forall x y z:A, x <= y -> y < z -> x < z.
intros x y z H (Hle,Hne); split.
transitivity y; trivial.
intro Heq; apply Hne; apply Ole_antisym; auto.
rewrite <- Heq; trivial.
Save.

Lemma Olt_le_trans `{o:ord A} : forall x y z:A, x < y -> y <= z -> x < z.
intros x y z (Hle,Hne) H; split.
transitivity y; trivial.
intro Heq; apply Hne; apply Ole_antisym; auto.
rewrite Heq; trivial.
Save.

Hint Resolve @Olt_antirefl.

Lemma Ole_not_lt `{o:ord A} : forall x y:A, x <= y -> ~ y < x.
intros x y H (Hle,Hne).
apply Hne; auto.
Save.
Hint Resolve @Ole_not_lt.

Add Parametric Morphism `{o:ord A} : (Olt (A:=A)) 
       with signature Ole --> Ole ==>  Basics.impl as Olt_le_compat.
red; intros.
apply Ole_lt_trans with x; trivial.
apply Olt_le_trans with x0; trivial.
Qed.

(** *** Dual order *)

(** - [ Iord x y =  y <= x ]  *)
Definition Iord : forall O {o:ord O}, ord O.
intros O o; exists (Oeq (A:=O)) (fun x y => y <=x).
abstract (split; intuition; red; intros; transitivity y; auto).
Defined.

Implicit Arguments Iord [[o]].

(** *** Order on functions *)

Definition fun_ext A B (R:relation B) : relation (A -> B) := 
                fun f g => forall x, R (f x) (g x).
Implicit Arguments fun_ext [B].

(** - [ ford f g ] := [ forall x, f x <= g x ] *)
Instance ford A O {o:ord O} : ord (A -> O) := 
  {Oeq:=fun_ext A (Oeq (A:=O));Ole:=fun_ext A (Ole (A:=O))}.
abstract (split; unfold fun_ext; intros; intuition;
               red; intros;transitivity (y x0); auto).
Defined.

Lemma ford_le_elim : forall A O (o:ord O) (f g:A -> O), f <= g -> forall n, f n <= g n.
auto.
Save.
Hint Immediate ford_le_elim.


Lemma ford_le_intro : forall A O (o:ord O) (f g:A -> O), ( forall n, f n <= g n ) -> f <= g.
auto.
Save.
Hint Resolve ford_le_intro.

Lemma ford_eq_elim : forall A O (o:ord O) (f g:A -> O), f == g -> forall n, f n == g n.
auto.
Save.
Hint Immediate ford_eq_elim.

Lemma ford_eq_intro : forall A O (o:ord O) (f g:A -> O), ( forall n, f n == g n ) -> f == g.
auto.
Save.
Hint Resolve ford_eq_intro.

(** ** Monotonicity *)

(** *** Definition and properties *)

Generalizable Variables Oa Ob Oc Od.

Class monotonic `{o1:ord Oa} `{o2:ord Ob} (f : Oa -> Ob) :=
      monotonic_def : forall x y, x <= y -> f x <= f y.

Lemma monotonic_intro : forall  `{o1:ord Oa} `{o2:ord Ob} (f : Oa -> Ob),
  (forall x y, x <= y -> f x <= f y) -> monotonic f.
red; auto.
Save.
Hint Resolve @monotonic_intro.


(* 
Instance monotonic_morphism `{o1:ord Oa} `{o2:ord Ob} (f : Oa -> Ob) {m:monotonic f} :
  Morphism (Ole (A:=Oa) ==> Ole (A:=Ob)) f.
 *)

Add Parametric Morphism `{o1:ord Oa} `{o2:ord Ob} (f : Oa -> Ob) {m:monotonic f} : f
with signature (Ole (A:=Oa) ==> Ole (A:=Ob))
as monotonic_morphism.
auto.
Save.

Class stable `{o1:ord Oa} `{o2:ord Ob} (f : Oa -> Ob) :=
      stable_def : forall x y, x == y -> f x == f y.
Hint Unfold stable.

Lemma stable_intro : forall  `{o1:ord Oa} `{o2:ord Ob} (f : Oa -> Ob),
  (forall x y, x == y -> f x == f y) -> stable f.
red; auto.
Save.
Hint Resolve @stable_intro.

Add Parametric Morphism `{o1:ord Oa} `{o2:ord Ob} (f : Oa -> Ob) {s:stable f} : f
with signature (Oeq (A:=Oa) ==> Oeq (A:=Ob))
as stable_morphism.
auto.
Save.

Typeclasses Opaque monotonic stable.

Instance monotonic_stable `{o1:ord Oa} `{o2:ord Ob} (f : Oa -> Ob) {m:monotonic f}
         :  stable  f.
unfold monotonic, stable; simpl; intros.
apply Ole_antisym; auto.
Save.

(** *** Type of monotonic functions *)

Record fmon `{o1:ord Oa} `{o2:ord Ob}:= mon
          {fmont :> Oa -> Ob; 
           fmonotonic: monotonic fmont}.

Existing Instance fmonotonic.

Implicit Arguments mon [[Oa] [o1] [Ob] [o2] [fmonotonic]].
Implicit Arguments fmon [[o1] [o2]].

Hint Resolve @fmonotonic.

(** printing -m> %\ensuremath{\stackrel{m}{\rightarrow}}% #-m>#*)
(** printing -m-> %\ensuremath{\stackrel{m}{\rightarrow}\!\!-}% #-m->#*)
(** printing --m-> %\ensuremath{-\!\!\stackrel{m}{\rightarrow}\!\!-}% #--m->#*)
(** printing --m> %\ensuremath{-\!\!\stackrel{m}{\rightarrow}}% #--m>#*)

Notation "Oa -m> Ob" := (fmon Oa Ob) 
   (right associativity, at level 30) : O_scope.
Notation "Oa --m> Ob" := (fmon Oa (o1:=Iord Oa) Ob ) 
   (right associativity, at level 30) : O_scope.
Notation "Oa --m-> Ob" := (fmon Oa (o1:=Iord Oa) Ob (o2:=Iord Ob)) 
   (right associativity, at level 30) : O_scope.
Notation "Oa -m-> Ob" := (fmon Oa Ob  (o2:=Iord Ob)) 
   (right associativity, at level 30) : O_scope.

Open Scope O_scope.


Lemma mon_simpl : forall `{o1:ord Oa} `{o2:ord Ob} (f:Oa -> Ob){mf: monotonic f} x,
      mon f x = f x.
trivial.
Save.
Hint Resolve @mon_simpl.


Instance fstable `{o1:ord Oa} `{o2:ord Ob} (f:Oa -m> Ob) : stable f.
intros; apply monotonic_stable; auto.
Save.

Hint Resolve @fstable.

Lemma fmon_le : forall `{o1:ord Oa} `{o2:ord Ob} (f:Oa -m> Ob) x y, 
                x <= y -> f x <= f y.
intros; apply (fmonotonic f); auto.
Save.
Hint Resolve @fmon_le.

Lemma fmon_eq : forall `{o1:ord Oa} `{o2:ord Ob} (f:Oa -m> Ob) x y, 
                x == y -> f x == f y.
intros; apply (fstable f); auto.
Save.
Hint Resolve @fmon_eq.

Instance fmono Oa Ob {o1:ord Oa} {o2:ord Ob} : ord (Oa -m> Ob) 
   := {Oeq := fun (f g : Oa-m> Ob)=> forall x, f x == g x;
       Ole := fun (f g : Oa-m> Ob)=> forall x, f x <= g x}.
abstract (split; unfold fun_ext; intros; intuition;
               red; intros; transitivity (y x0); auto).
Defined.

Lemma mon_le_compat : forall `{o1:ord Oa} `{o2:ord Ob} (f g:Oa -> Ob)
      {mf:monotonic f} {mg:monotonic g}, f <= g -> mon f <= mon g.
red; intros; auto.
Save.
Hint Resolve @ mon_le_compat.

Lemma mon_eq_compat : forall `{o1:ord Oa} `{o2:ord Ob} (f g:Oa-> Ob)
      {mf:monotonic f} {mg:monotonic g}, f == g -> mon f == mon g.
red; intros; auto.
Save.
Hint Resolve @ mon_eq_compat.

Add Parametric Morphism `{o1:ord Oa} `{o2:ord Ob} 
       : (fmont (Oa:=Oa) (Ob:=Ob)) 
       with signature Oeq ==> Oeq ==> Oeq as fmont_eq_morphism.
intros [f] [g] H x y h.
simpl.
rewrite (H x).
rewrite h.
simpl.
auto.
Qed.

(** *** Monotonicity and dual order *)

Lemma Imonotonic `{o1:ord Oa} `{o2:ord Ob} (f:Oa -> Ob) {m:monotonic f} 
         : monotonic (o1:=Iord Oa) (o2:=Iord Ob) f.
red; simpl; intros.
apply m; auto.
Save.

Hint Extern 2 (@monotonic _ (Iord _) _ (Iord _) _) => apply @Imonotonic
  : typeclass_instances.

Definition imon `{o1:ord Oa} `{o2:ord Ob} (f:Oa -> Ob) {m:monotonic f} 
   : Oa --m-> Ob := mon (o1:=Iord Oa) (o2:=Iord Ob) f.

Lemma imon_simpl : forall `{o1:ord Oa} `{o2:ord Ob} (f:Oa -> Ob) {m:monotonic f} (x:Oa),
     imon f x = f x.
trivial.
Save.

(** - [Iord (A -> U)] corresponds to [A -> Iord U] *)

Lemma Iord_app {A} `{o1:ord Oa} (x: A) : ((A -> Oa) --m-> Oa).
intros; exists (fun f => f x).
abstract(red; auto).
Defined.

(** - [Imon f] uses f as monotonic function over the dual order. *)

Definition Imon : forall `{o1:ord Oa} `{o2:ord Ob}, (Oa -m> Ob) -> (Oa --m-> Ob).
intros Oa o1 Ob o2 f.
exists (fmont f); abstract (apply Imonotonic; auto).
Defined.

Lemma Imon_simpl : forall `{o1:ord Oa} `{o2:ord Ob} (f:Oa -m> Ob)(x:Oa),
                   Imon f x = f x.
trivial.
Save.

(** *** Monotonicity and equality *)

Lemma mon_fun_eq_monotonic 
  : forall `{o1:ord Oa} `{o2:ord Ob} (f:Oa -> Ob) (g:Oa -m> Ob),
            f == g -> monotonic f.
red; intros.
rewrite (H x); rewrite (H y); auto.
Save.

Definition mon_fun_subst `{o1:ord Oa} `{o2:ord Ob} (f:Oa -> Ob) (g:Oa -m> Ob) (H:f == g)
   : Oa -m> Ob := mon f (fmonotonic:= mon_fun_eq_monotonic _ _ H).

Lemma mon_fun_eq
  : forall `{o1:ord Oa} `{o2:ord Ob} (f:Oa -> Ob) (g:Oa -m> Ob)
            (H:f == g), g == mon_fun_subst f g H.
intros; intro x; unfold mon_fun_subst.
symmetry; apply (H x).
Save.

(** *** Monotonic functions with 2 arguments *)

Class monotonic2 `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} (f:Oa -> Ob -> Oc) := 
    monotonic2_intro : forall (x y:Oa) (z t:Ob), x <= y -> z <= t -> f x z <= f y t.


Instance mon2_intro `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} (f:Oa -> Ob -> Oc) 
    {m1:monotonic f} {m2: forall x, monotonic (f x)} : monotonic2 f | 10.
red; intros.
transitivity (f y z).
apply (m1 x); trivial.
apply (m2 y); trivial.
Save.

Lemma mon2_elim1 `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} (f:Oa -> Ob -> Oc) 
    {m:monotonic2 f} : monotonic f.
red; intros; intro z.
apply m; auto.
Save.

Lemma mon2_elim2 `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} (f:Oa -> Ob -> Oc) 
    {m:monotonic2 f} : forall x, monotonic (f x).
red; intros.
apply m; auto.
Save.
Hint Immediate @mon2_elim1 @mon2_elim2: typeclass_instances.

Definition mon_comp {A} `{o1: ord Oa} `{o2: ord Ob} 
         (f:A -> Oa -> Ob) {mf:forall x, monotonic (f x)} : A -> Oa -m> Ob 
         := fun x => mon (f x).

Instance mon_fun_mon `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} (f:Oa -> Ob -> Oc) 
    {m:monotonic2 f} : monotonic (fun x => mon (f x)).
red; intros; unfold mon_comp.
intro z; apply m; auto.
Save.

Class stable2 `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} (f:Oa -> Ob -> Oc) := 
    stable2_intro : forall (x y:Oa) (z t:Ob), x==y -> z == t -> f x z == f y t.

Instance monotonic2_stable2 `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} 
    (f:Oa -> Ob -> Oc) {m:monotonic2 f} : stable2 f.
red; intros; apply Ole_antisym; auto.
Save.

Typeclasses Opaque monotonic2 stable2.

Definition mon2 `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} (f:Oa -> Ob -> Oc)
     {mf:monotonic2 f} : Oa -m> Ob -m> Oc := mon (fun x => mon (f x)).

Lemma mon2_simpl : forall `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} (f:Oa -> Ob -> Oc)
     {mf:monotonic2 f} x y, mon2 f x y = f x y.
trivial.
Save.
Hint Resolve @mon2_simpl.

Lemma mon2_le_compat :  forall `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} 
     (f g:Oa -> Ob -> Oc) {mf: monotonic2 f} {mg:monotonic2 g}, 
     f <= g -> mon2 f <= mon2 g.
red; simpl; intros.
apply H; trivial.
Save.

Definition fun2 `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} (f:Oa -> Ob -m> Oc) 
     : Oa -> Ob -> Oc := fun x => f x.

Instance fmon2_mon `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} (f:Oa -> Ob -m> Oc) :
       forall x:Oa, monotonic (fun2 f x).
intros; unfold fun2; auto.
Save.

Instance fun2_monotonic `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} 
         (f:Oa -> Ob -m> Oc) {mf:monotonic f} : monotonic (fun2 f).
intros;unfold fun2; auto.
Save.
Hint Resolve @fun2_monotonic.

Instance fmonotonic2 `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} (f:Oa -m> Ob -m> Oc) 
         : monotonic2 (fun2 f).
intros;unfold fun2;  apply mon2_intro; auto.
red; intros.
apply (fmonotonic f x y); trivial .
Save.
Hint Resolve @fmonotonic2.

Definition mfun2 `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} (f:Oa -m> Ob -m> Oc) 
   : Oa-m> (Ob -> Oc) := mon (fun2 f).

Lemma mfun2_simpl : forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} (f:Oa -m> Ob -m> Oc) x y,
     mfun2 f x y = f x y.
trivial.
Save.

Instance mfun2_mon `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} 
         (f:Oa -m> Ob -m> Oc) x : monotonic (mfun2 f x).
red; simpl; unfold fun2; intros; auto.
Save.

Lemma mon2_fun2 : forall `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} 
     (f:Oa -m> Ob -m> Oc), mon2 (fun2 f) == f.
intros; unfold fun2,mon2; intros x y; auto.
Save.

Lemma fun2_mon2 : forall `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} 
      (f:Oa -> Ob -> Oc) {mf:monotonic2 f} , fun2 (mon2 f) == f.
intros; unfold fun2,mon2; intros x y; auto.
Save.
Hint Resolve @mon2_fun2 @fun2_mon2.

Instance fstable2 `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} (f:Oa -m> Ob -m> Oc) 
                : stable2 (fun2 f).
intros; apply monotonic2_stable2; auto.
Save.
Hint Resolve @fstable2.

Definition Imon2 : forall `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc}, 
     (Oa -m> Ob -m> Oc) -> (Oa --m> Ob --m-> Oc).
intros  Oa o1 Ob o2 Oc o3 f.
exists (fun (x:Oa) => Imon (f x)); 
abstract (red; simpl; intros; apply (fmonotonic f); auto).
Defined.

Lemma Imon2_simpl : forall `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} 
      (f:Oa -m> Ob -m> Oc) (x:Oa) (y: Ob),
      Imon2 f x y = f x y.
trivial.
Save.

Lemma Imonotonic2 `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} 
      (f:Oa -> Ob -> Oc){mf : monotonic2 f} 
      : monotonic2 (o1:=Iord Oa) (o2:=Iord Ob) (o3:=Iord Oc) f.
red; simpl; intros; auto.
Save.

Hint Extern 2 (@monotonic2 _ (Iord _) _ (Iord _) _ (Iord _)  _) => apply @Imonotonic2
  : typeclass_instances.

Definition imon2 `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} 
      (f:Oa -> Ob -> Oc){mf : monotonic2 f} : Oa --m> Ob --m-> Oc := 
      mon2 (o1:=Iord Oa) (o2:=Iord Ob) (o3:=Iord Oc) f.

Lemma imon2_simpl : forall `{o1: ord Oa} `{o2: ord Ob} `{o3:ord Oc} 
      (f:Oa -> Ob -> Oc){mf : monotonic2 f} (x:Oa) (y:Ob),
      imon2 f x y = f x y.
trivial.
Save.

(** *** Strict monotonicity *)

Lemma inj_strict_mon : forall `{o1: ord Oa} `{o2: ord Ob} (f:Oa -> Ob) {mf:monotonic f},
      (forall x y, f x == f y -> x == y) -> forall x y, x < y -> f x < f y.
intros Oa o1 Ob o2 f mf Hinj x y (Hle,Hne); split; auto.
Save.


(** ** Sequences *)
(** *** Usual order on natural numbers *)

Instance natO : ord nat := 
    { Oeq := fun n m : nat => n = m;
       Ole := fun n m : nat => (n <= m)%nat}.
      abstract (apply Build_Order; intros; try omega; auto with arith;
                     red; intros; apply le_trans with y; auto).
Defined.

Lemma le_Ole : forall n m, ((n <= m)%nat)-> n <= m.
simpl; auto.
Save.
Hint Resolve le_Ole.

Lemma nat_monotonic : forall {O} {o:ord O} 
               (f:nat -> O), (forall n, f n <= f (S n)) -> monotonic f.
red; simpl; intros.
elim H0; intros; auto.
transitivity (f m); trivial.
Save.
Hint Resolve @nat_monotonic.

Lemma nat_monotonic_inv : forall {O} {o:ord O} 
               (f:nat -> O), (forall n, f (S n) <= f n) -> monotonic (o2:=Iord O) f.
red; simpl; intros.
elim H0; intros; auto.
transitivity (f m); trivial.
Save.
Hint Resolve @nat_monotonic_inv.

Definition fnatO_intro : forall {O} {o:ord O} (f:nat -> O), (forall n, f n <= f (S n)) -> nat -m> O.
intros; exists f; abstract auto.
Defined.


Lemma fnatO_elim : forall {O} {o:ord O} (f:nat -m> O) (n:nat), f n <= f (S n).
intros; apply (fmonotonic f); simpl; auto with arith.
Save.
Hint Resolve @fnatO_elim.


(** - (mseq_lift_left f n) k = f (n+k) *)

Definition seq_lift_left {O} (f:nat -> O) n := fun k => f (n+k)%nat.

(* d'où venait le n avant que je le mette en forall?? *)
Instance mon_seq_lift_left 
  : forall n {O} {o:ord O} (f:nat -> O) {m:monotonic f}, monotonic (seq_lift_left f n).
red; intros; apply m ; simpl; auto with arith.
Save.

Definition mseq_lift_left : forall {O} {o:ord O} (f:nat -m> O) (n:nat), nat -m> O.
intros; exists (fun k => f (n+k)%nat).
abstract (red; intros; apply (fmonotonic f); simpl; auto with arith).
Defined.

Lemma mseq_lift_left_simpl : forall {O} {o:ord O} (f:nat -m> O) (n k:nat), 
    mseq_lift_left f n  k = f (n+k)%nat.
trivial.
Save.

Lemma mseq_lift_left_le_compat : forall {O} {o:ord O} (f g:nat -m> O) (n:nat), 
             f <= g -> mseq_lift_left f n <= mseq_lift_left g n.
intros; intro; simpl; auto.
Save.
Hint Resolve @mseq_lift_left_le_compat.

Add Parametric Morphism {O} {o:ord O} : (@mseq_lift_left _ o) 
  with signature Oeq  ==> eq ==> Oeq
  as mseq_lift_left_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve @mseq_lift_left_eq_compat.

Add Parametric Morphism {O} {o:ord O}: (@seq_lift_left O) 
  with signature Oeq  ==> eq ==> Oeq
  as seq_lift_left_eq_compat.
simpl; intros; intro.
simpl; apply H; auto.
Save.
Hint Resolve @seq_lift_left_eq_compat.


(** - (mseq_lift_right f n) k = f (k+n) *)

Definition seq_lift_right {O} (f:nat -> O) n := fun k => f (k+n)%nat.

Instance mon_seq_lift_right 
   : forall n {O} {o:ord O} (f:nat -> O) {m:monotonic f}, monotonic (seq_lift_right f n).
red; intros; apply m ; simpl; auto with arith.
Save.

Definition mseq_lift_right : forall {O} {o:ord O} (f:nat -m> O) (n:nat), nat -m> O.
intros; exists (fun k => f (k+n)%nat).
abstract (red; intros; apply (fmonotonic f); simpl; auto with arith).
Defined.

Lemma mseq_lift_right_simpl : forall {O} {o:ord O} (f:nat -m> O) (n k:nat), 
    mseq_lift_right f n  k = f (k+n)%nat.
trivial.
Save.

Lemma mseq_lift_right_le_compat : forall {O} {o:ord O} (f g:nat -m> O) (n:nat), 
             f <= g -> mseq_lift_right f n <= mseq_lift_right g n.
intros; intro; simpl; auto.
Save.
Hint Resolve @mseq_lift_right_le_compat.

Add Parametric Morphism {O} {o:ord O} : (mseq_lift_right (o:=o)) 
   with signature Oeq ==> eq ==> Oeq 
   as mseq_lift_right_eq_compat.
intros; apply Ole_antisym; auto.
Save.

Add Parametric Morphism {O} {o:ord O}: (@seq_lift_right O) 
  with signature Oeq  ==> eq ==> Oeq
  as seq_lift_right_eq_compat.
simpl; intros; intro.
simpl; apply H; auto.
Save.
Hint Resolve @seq_lift_right_eq_compat.

Lemma mseq_lift_right_left : forall {O} {o:ord O} (f:nat -m> O) n, 
       mseq_lift_left f n  == mseq_lift_right f n.
unfold mseq_lift_left,mseq_lift_right; intros.
intro x.
unfold fmont; replace (n+x)%nat with (x+n)%nat; auto with arith.
Save.

(** *** Monotonicity and functions *)
(** -  (shift f x) n = f n x *) 

Instance shift_mon_fun {A} `{o1:ord Oa} `{o2:ord Ob} (f:Oa -m> (A -> Ob)) : 
       forall x:A, monotonic (fun (y:Oa) => f y x).
red; intros; apply (fmonotonic f); auto.
Save.

Definition shift {A} `{o1:ord Oa} `{o2:ord Ob} (f:Oa -m> (A -> Ob)) : A -> Oa -m> Ob 
   := fun x => (mon (fun y => f y x)).

(** printing <o> %\ensuremath{\diamond}% # &loz;# *)
Infix "<o>" := shift (at level 30, no associativity) : O_scope.

Lemma shift_simpl : forall {A} `{o1:ord Oa} `{o2:ord Ob} (f:Oa -m> (A -> Ob)) x y,
      (f <o> x) y = f y x.
trivial.
Save. 

Lemma shift_le_compat : forall {A} `{o1:ord Oa} `{o2:ord Ob} (f g:Oa -m> (A -> Ob)), 
             f <= g -> shift f <= shift g.
intros; intros x y.
repeat rewrite shift_simpl.
apply (H y x); trivial.
Save.
Hint Resolve @shift_le_compat.

Add Parametric Morphism {A} `{o1:ord Oa} `{o2:ord Ob}
    : (shift (A:=A) (Oa:=Oa) (Ob:=Ob)) with signature Oeq ==> eq ==> Oeq
as shift_eq_compat.
intros f g H x y.
repeat rewrite shift_simpl; auto.
Save.

Instance ishift_mon {A} `{o1:ord Oa} `{o2:ord Ob} (f:A -> (Oa -m> Ob)) : 
       monotonic (fun (y:Oa) (x:A) => f x y).
red; intros; intro z.
apply (fmonotonic (f z)); auto.
Save.

Definition ishift {A} `{o1:ord Oa} `{o2:ord Ob} (f:A -> (Oa -m> Ob)) : Oa -m> (A -> Ob)
   := mon (fun (y:Oa) (x:A) => f x y) (fmonotonic:=ishift_mon f).

Lemma ishift_simpl : forall {A} `{o1:ord Oa} `{o2:ord Ob} (f:A -> (Oa -m> Ob)) x y,
      ishift f x y = f y x.
trivial.
Save. 

Lemma ishift_le_compat : forall {A} `{o1:ord Oa} `{o2:ord Ob} (f g:A -> (Oa -m> Ob)), 
             f <= g -> ishift f <= ishift g.
intros; intros x y.
repeat rewrite ishift_simpl.
apply (H y x); trivial.
Save.
Hint Resolve @ishift_le_compat.

Add Parametric Morphism {A} `{o1:ord Oa} `{o2:ord Ob}
    : (ishift (A:=A) (Oa:=Oa) (Ob:=Ob)) with signature Oeq ==> eq ==> Oeq
as ishift_eq_compat.
intros f g H x y.
repeat rewrite ishift_simpl.
apply H.
Save.

(*
Instance shift_mon_mon `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} (f:Oa -m> (Ob -m> Oc))
     {mf:forall x, monotonic (f x)}, monotonic (f <o> x).
red; unfold shift; intros; apply m; trivial.
Defined.
*)

Instance shift_fun_mon `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} (f:Oa -m> (Ob -> Oc))
     {m:forall x, monotonic (f x)} : monotonic (shift f).
intros x y H z.
repeat (rewrite shift_simpl); apply m; trivial.
Save.

Instance shift_mon2 `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} (f:Oa -m> Ob -m> Oc)
     : monotonic2 (fun x y => f y x).
apply mon2_intro.
intros x y H z; auto.
intros x z t H; apply (fmonotonic f); trivial.
Save.
Hint Resolve @shift_mon_fun @shift_fun_mon @shift_mon2.

Definition mshift `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} (f:Oa -m> Ob -m> Oc) 
    : Ob -m> Oa -m> Oc := mon2 (fun x y => f y x).

(** - id c = c *)

Definition id O {o:ord O} : O -> O := fun x => x.

Instance mon_id : forall {O:Type} {o:ord O}, monotonic (id O).
auto.
Save.


(**  - (cte c) n = c *) 

Definition cte A  `{o1:ord Oa} (c:Oa) : A -> Oa := fun x => c.

Instance mon_cte : forall `{o1:ord Oa} `{o2:ord Ob} (c:Ob), monotonic (cte Oa c).
auto.
Save.

Definition mseq_cte {O} {o:ord O} (c:O) : nat -m> O := mon (cte nat c).

Add Parametric Morphism `{o1:ord Oa} `{o2:ord Ob} : (@cte Oa  Ob _) 
  with signature Ole  ==>  Ole as cte_le_compat.
intros c1 c2 H x; simpl; auto.
Save.

Add Parametric Morphism `{o1:ord Oa} `{o2:ord Ob} : (@cte Oa  Ob _) 
  with signature Oeq  ==>  Oeq as cte_eq_compat.
intros c1 c2 H x; simpl; auto.
Save.

Instance mon_diag `{o1:ord Oa} `{o2:ord Ob}(f:Oa -m> (Oa -m> Ob)) 
     : monotonic (fun x => f x x).
intros x y H; apply (fmonotonic2 f); auto.
Save.
Hint Resolve @mon_diag.

Definition diag `{o1:ord Oa} `{o2:ord Ob}(f:Oa -m> (Oa -m> Ob)) : Oa-m> Ob
     := mon (fun x => f x x).

Lemma fmon_diag_simpl : forall `{o1:ord Oa} `{o2:ord Ob} (f:Oa -m> (Oa -m> Ob)) (x:Oa), 
             diag f x = f x x.
trivial.
Save.

Lemma diag_le_compat :  forall `{o1:ord Oa} `{o2:ord Ob} (f g:Oa -m> (Oa -m> Ob)), 
             f <= g -> diag f <= diag g.
intros; intro; simpl; auto.
apply H.
Save.
Hint Resolve @diag_le_compat.


Add Parametric Morphism `{o1:ord Oa} `{o2:ord Ob} : (diag (Oa:=Oa) (Ob:=Ob)) 
   with signature Oeq ==> Oeq as diag_eq_compat.
intros; intro; simpl; auto.
apply H.
Save.

Lemma diag_shift : forall `{o1:ord Oa} `{o2:ord Ob} (f: Oa -m> Oa -m> Ob),
                   diag f == diag (mshift f).
intros; intro x; unfold mshift,diag; auto.
Save.

Hint Resolve @diag_shift.

Lemma mshift_simpl : forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc}
      (h:Oa -m> Ob -m>  Oc) (x : Ob) (y:Oa), mshift h x y = h y x.
trivial.
Save.

Lemma mshift_le_compat :  forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} 
      (f g:Oa -m>  Ob -m>  Oc), f <= g -> mshift f <= mshift g.
intros; intros x y; simpl; unfold mshift; intros.
apply H; auto.
Save.
Hint Resolve @mshift_le_compat.

Add Parametric Morphism `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} : (@mshift Oa _ Ob _ Oc _)
     with signature Oeq  ==> Oeq as mshift_eq_compat.
intros f g H x y; simpl; unfold mshift; intros.
apply H; auto.
Save.

Lemma mshift2_eq :  forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} (h : Oa -m> Ob -m>  Oc),
             mshift (mshift h) == h.
intros; intros x y; unfold mshift; auto.
Save.

(** - (f@g) x = f (g x) *)

Instance monotonic_comp `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} 
   (f:Ob -> Oc){mf : monotonic f} (g:Oa -> Ob){mg:monotonic g} : monotonic (fun x => f (g x)).
intros x y H; auto.
Save.
Hint Resolve @monotonic_comp.

Instance monotonic_comp_mon `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} 
   (f:Ob -m> Oc)(g:Oa -m> Ob) : monotonic (fun x => f (g x)).
intros x y H; auto.
Save.
Hint Resolve @monotonic_comp_mon.

Definition comp `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} (f:Ob -m> Oc) (g:Oa -m> Ob) 
       : Oa -m> Oc := mon (fun x => f (g x)).

Infix "@" := comp (at level 35) : O_scope.

Lemma comp_simpl : forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} 
      (f:Ob -m> Oc) (g:Oa -m> Ob) (x:Oa), (f@g) x = f (g x).
trivial.
Save.

Add Parametric Morphism `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc}: (@comp Oa _ Ob _ Oc _)
    with signature Ole ++> Ole  ++> Ole 
    as comp_le_compat.
intros f1 f2 H g1 g2 H1 x; unfold comp; simpl; auto.
transitivity (f2 (g1 x)); auto.
Save.

Hint Immediate @comp_le_compat.

Add Parametric Morphism `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} : (@comp Oa _ Ob _ Oc _)
    with signature Oeq ==> Oeq ==> Oeq
    as comp_eq_compat.
intros f1 f2 H g1 g2 H1 x.
repeat (rewrite comp_simpl); transitivity (f2 (g1 x)); auto.
Save.

Hint Immediate @comp_eq_compat.


(** - (f@2 g) h x = f (g x) (h x) *)

Instance mon_app2 `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} `{o4:ord Od} 
      (f:Ob -> Oc -> Od) (g:Oa -> Ob) (h:Oa -> Oc) 
      {mf:monotonic2 f}{mg:monotonic g} {mh:monotonic h} 
      : monotonic (fun x => f (g x) (h x)).
intros x y H; auto.
Save.

Instance mon_app2_mon `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} `{o4:ord Od} 
      (f:Ob -m> Oc -m> Od) (g:Oa -m> Ob) (h:Oa -m> Oc) 
      : monotonic (fun x => f (g x) (h x)).
intros x y H.
apply (fmonotonic2 f); auto.
Save.

Definition app2 `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} `{o4:ord Od} 
        (f:Ob -m> Oc -m> Od) (g:Oa -m> Ob) (h:Oa -m> Oc) : Oa -m> Od 
        := mon (fun x => f (g x) (h x)).

(** printing @2 %\ensuremath{@^2}% #@&sup2;#*)
Infix "@2" := app2 (at level 70) : O_scope.

Add Parametric Morphism `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} `{o4:ord Od}: 
        (@app2 Oa _ Ob _ Oc _ Od _)
    with signature Ole ++> Ole  ++> Ole ++> Ole 
    as app2_le_compat.
intros f1 f2 H g1 g2 H1 h1 h2 H2 x; unfold app2; simpl; auto.
transitivity (f2 (g1 x) (h1 x)).
apply H.
apply (fmonotonic2 f2); auto.
Save.

Hint Immediate @app2_le_compat.

Add Parametric Morphism `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} `{o4:ord Od}: 
        (@app2 Oa _ Ob _ Oc _ Od _)
    with signature Oeq ==> Oeq  ==> Oeq ==> Oeq 
    as app2_eq_compat.
intros f1 f2 H g1 g2 H1 h1 h2 H2 x; unfold app2; simpl; auto.
transitivity (f2 (g1 x) (h1 x)).
apply H.
apply (fstable2 f2); auto.
Save.

Hint Immediate @app2_eq_compat.


Lemma app2_simpl : 
    forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} `{o4:ord Od} 
            (f:Ob -m> Oc -m> Od) (g:Oa -m> Ob) (h:Oa -m> Oc) (x:Oa), 
    (f@2 g) h x = f (g x) (h x).
trivial.
Save.


Lemma comp_monotonic_right : 
      forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} (f: Ob -m> Oc) (g1 g2:Oa -m> Ob),
               g1<= g2 -> f @ g1 <= f @ g2.
auto.
Save.
Hint Resolve @comp_monotonic_right.

Lemma comp_monotonic_left : 
      forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} (f1 f2: Ob -m> Oc) (g:Oa -m> Ob),
               f1<= f2 -> f1 @ g <= f2 @ g.
auto.
Save.
Hint Resolve @comp_monotonic_left.

Instance comp_monotonic2 : forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc}, 
             monotonic2 (@comp Oa _ Ob _ Oc _).
red; intros.
apply comp_le_compat; auto.
Save.
Hint Resolve @comp_monotonic2.

Definition fcomp `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} :
   (Ob -m> Oc) -m> (Oa -m> Ob) -m> (Oa -m> Oc) := mon2 (@comp Oa _ Ob _ Oc _).

Implicit Arguments fcomp [[o1] [o2] [o3]].

Lemma fcomp_simpl : forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} 
      (f:Ob -m> Oc) (g:Oa -m> Ob), fcomp _ _ _ f g = f@g.
trivial.
Save.


Definition fcomp2  `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} `{o4:ord Od} :
        (Oc -m> Od) -m> (Oa -m> Ob -m> Oc) -m> (Oa -m> Ob -m> Od):=
        (fcomp Oa (Ob -m> Oc) (Ob -m> Od))@(fcomp Ob Oc Od).


Implicit Arguments fcomp2 [[o1] [o2] [o3] [o4]].

Lemma fcomp2_simpl : forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} `{o4:ord Od}
      (f:Oc -m> Od) (g:Oa -m> Ob -m> Oc) (x:Oa)(y:Ob), fcomp2 _ _ _ _ f g x y = f (g x y).
trivial.
Save.

Lemma fmon_le_compat2 : forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} 
      (f: Oa -m> Ob -m> Oc) (x y:Oa) (z t:Ob), x<=y -> z <=t -> f x z <= f y t.
intros; transitivity (f x t).
apply (fmonotonic (f x)); auto.
apply (fmonotonic f); auto.
Save.
Hint Resolve fmon_le_compat2.

Lemma fmon_cte_comp : forall `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc}
      (c:Oc)(f:Oa -m> Ob), (mon (cte Ob c)) @ f == mon (cte Oa c).
intros; intro x; auto.
Save.

(** ** Abstract relational notion of lubs *)
Record islub O (o:ord O) I (f:I -> O) (x:O) : Prop := mk_islub
     { le_islub : forall i,  f i <= x;
       islub_le : forall y, (forall  i,  f i <= y) -> x <= y}.
Implicit Arguments islub [O o I].
Implicit Arguments le_islub [O o I f x].
Implicit Arguments islub_le [O o I f x].

Definition isglb O (o:ord O) I (f:I -> O) (x:O) : Prop
     := islub (o:=Iord O) f x.
Implicit Arguments isglb [O o I].

Lemma le_isglb O (o:ord O) I (f:I -> O) (x:O) :
         isglb f x -> forall i,  x <= f i.
intros; exact (le_islub H i).
Save.

Lemma isglb_le O (o:ord O) I (f:I -> O) (x:O) :
         isglb f x -> forall y, (forall i,  y <= f i) -> y <= x.
intros; exact (islub_le H y H0).
Save.
Implicit Arguments le_isglb [O o I f x].
Implicit Arguments isglb_le [O o I f x].

Lemma mk_isglb O (o:ord O) I (f:I -> O) (x:O) : 
      (forall i,  x <= f i) -> (forall y, (forall i,  y <= f i) -> y <= x)
      -> isglb f x.
red; intros; apply mk_islub; auto.
Save.

Lemma islub_eq_compat O (o:ord O) I (f g:I -> O) (x y:O):
      f==g -> x == y -> islub f x -> islub g y.
intros; destruct H1; split; intros; rewrite <- H0.
rewrite <- (H i); auto.
apply islub_le0; intros.
rewrite (H i); auto.
Save.

Lemma islub_eq_compat_left O (o:ord O) I (f g:I -> O) (x:O):
      f==g -> islub f x -> islub g x.
intros; apply islub_eq_compat with f x; auto.
Save.

Lemma islub_eq_compat_right O (o:ord O) I (f:I -> O) (x y:O):
       x == y -> islub f x -> islub f y.
intros; apply islub_eq_compat with f x; auto.
Save.

Lemma isglb_eq_compat O (o:ord O) I (f g:I -> O) (x y:O):
      f==g -> x == y -> isglb f x -> isglb g y.
intros.
apply (islub_eq_compat O (Iord O)) with f x; auto.
Save.

Lemma isglb_eq_compat_left O (o:ord O) I (f g:I -> O) (x:O):
      f==g -> isglb f x -> isglb g x.
intros; apply isglb_eq_compat with f x; auto.
Save.

Lemma isglb_eq_compat_right O (o:ord O) I (f:I -> O) (x y:O):
       x == y -> isglb f x -> isglb f y.
intros; apply isglb_eq_compat with f x; auto.
Save.

Add Parametric Morphism {O} {o:ord O} I : (@islub _ o I) 
with signature Oeq ==> Oeq ==> iff
as islub_morphism.
split; eapply islub_eq_compat; auto.
Save. 

Add Parametric Morphism {O} {o:ord O} I : (@isglb _ o I) 
with signature Oeq ==> Oeq ==> iff
as isglb_morphism.
split; eapply isglb_eq_compat; auto.
Save. 

Add Parametric Morphism {O} {o:ord O} I : (@islub _ o I) 
with signature (@pointwise_relation I O (@Oeq _ _)) ==> Oeq ==> iff
as islub_morphism_ext.
split; eapply islub_eq_compat; auto.
Save. 

Add Parametric Morphism {O} {o:ord O} I : (@isglb _ o I) 
with signature (@pointwise_relation I O (@Oeq _ _)) ==> Oeq ==> iff
as isglb_morphism_ext.
split; eapply isglb_eq_compat; auto.
Save. 

Lemma islub_incr_ext {O} {o:ord O} (f :nat -> O) (x:O) (n:nat):
      (forall k, f k <= f (S k)) -> islub f x -> islub (fun k => f (n + k)) x.
intros HS (H1,H2); split; auto with arith; intros.
apply H2; intros; transitivity (f (n+i)); auto with arith.
elim n; simpl; auto; intros.
transitivity (f (n0 + i)); auto.
Save.

Lemma islub_incr_lift {O} {o:ord O} (f :nat -> O) (x:O) (n:nat):
      (forall k, f k <= f (S k)) -> islub (fun k => f (n + k)) x -> islub f x.
intros HS (H1,H2); split; auto with arith; intros.
transitivity (f (n+i)); auto with arith.
elim n; simpl; auto; intros.
transitivity (f (n0 + i)); auto.
Save.

Lemma isglb_decr_ext {O} {o:ord O} (f :nat -> O) (x:O) (n:nat):
      (forall k, f (S k) <= f k) -> isglb f x -> isglb (fun k => f (n + k)) x.
intros HS (H1,H2); split; auto with arith; intros.
apply H2; intros; transitivity (f (n+i)); auto with arith.
elim n; simpl; auto; intros.
transitivity (f (n0 + i)); auto.
Save.

Lemma isglb_decr_lift {O} {o:ord O} (f :nat -> O) (x:O) (n:nat):
      (forall k, f (S k) <= f k) -> isglb (fun k => f (n + k)) x -> isglb f x.
intros HS (H1,H2); split; auto with arith; intros.
transitivity (f (n+i)); auto with arith.
elim n; simpl; auto; intros.
transitivity (f (n0 + i)); auto.
Save.

Hint Resolve islub_incr_ext isglb_decr_ext.

Lemma islub_exch {O} {o:ord O} (F :nat -> nat -> O) (f g : nat -> O)(x:O) : 
      (forall m, islub (fun n => F n m) (f m)) 
       -> (forall n, islub (F n) (g n)) -> islub f x -> islub g x.
intros Lf Lg (Lx1,Lx2); split; intros.
apply (islub_le (Lg i)); intros.
transitivity (f i0); auto.
apply (le_islub (Lf i0) i); auto.
apply Lx2; intros.
apply (islub_le (Lf i)); intros.
transitivity (g i0); auto.
apply (le_islub (Lg i0) i); auto.
Save.

Lemma islub_decr {O} {o:ord O} {I} (f g : I -> O) (x y : O) :
      (f <= g) -> islub f x -> islub g y -> x <= y.
intros H (Hf1,Hf2) (Hg1,Hg2).
apply Hf2; intros.
transitivity (g i); auto.
Save.

Lemma islub_unique_eq {O} {o:ord O} {I} (f g : I -> O) (x y : O) :
      (f == g) -> islub f x -> islub g y -> x == y.
intros; apply Ole_antisym.
apply islub_decr with f g; auto.
apply islub_decr with g f; auto.
Save.

Lemma islub_unique {O} {o:ord O} {I} (f : I -> O) (x y : O) :
           islub f x -> islub f y -> x == y.
intros; apply islub_unique_eq with f f; auto.
Save.

Lemma islub_fun_intro O (o:ord O) {I A} (F : I -> A -> O) (f : A -> O) :
           (forall x, islub (fun i => F i x) (f x)) -> islub F f.
split; intros; intro x.
apply (H x); auto.
apply (H x); auto.
Save.

(** ** Basic operators of omega-cpos *)
(** - Constant : [0] 
     - lub : limit of monotonic sequences
*)

Generalizable Variables D.

(** *** Definition of cpos *)
Class cpo  `{o:ord D} : Type := mk_cpo 
  {D0 : D; lub: forall (f:nat -m> D), D;
   Dbot : forall x:D, D0 <= x; 
   le_lub : forall (f : nat -m> D) (n:nat), f n <= lub f;
   lub_le : forall (f : nat -m> D) (x:D), (forall n, f n <= x) -> lub f <= x}.

Implicit Arguments cpo [[o]].

Notation "0" := D0 : O_scope.

Hint Resolve @Dbot @le_lub @lub_le.

Definition mon_ord_equiv : forall `{o:ord D1} `{o1:ord D2} {o2:ord D2},
      eq_ord o1 o2 -> fmon D1 D2 (o2:=o2) -> fmon D1 D2 (o2:=o1).
unfold eq_ord, eq_rel; intros D1 o D2 o1 o2 H f; exists (fun x => f x).
abstract (red; intros; rewrite H; apply (fmonotonic f); auto).
Defined.

Lemma mon_ord_equiv_simpl : forall `{o:ord D1} `{o1:ord D2} {o2:ord D2}
      (H:eq_ord o1 o2) (f:fmon D1 D2 (o2:=o2)) (x:D1), 
      mon_ord_equiv H f x = f x.
trivial.
Save.

Definition cpo_ord_equiv `{o1:ord D} (o2:ord D) 
       : eq_ord o1 o2 -> cpo (o:=o1) D -> cpo (o:=o2) D.
unfold eq_ord, eq_rel; intros H c.
exists (D0 (cpo:=c)) (fun f : nat -m> D => lub (cpo:=c) (mon_ord_equiv H f)).
abstract (intros; rewrite <- H; auto).
abstract (intros; rewrite <- H; apply (le_lub (mon_ord_equiv H f) n)).
abstract (intros; rewrite <- H; apply lub_le; intros; simpl; rewrite H; auto).
Defined.

(** *** Least upper bounds *)

Add Parametric Morphism `{c:cpo D} : (lub (cpo:=c)) 
             with signature Ole ++> Ole as lub_le_compat.
intros f g H; apply lub_le; intros.
transitivity (g n); auto.
Save.
Hint Resolve @lub_le_compat.

Add Parametric Morphism `{c:cpo D}: (lub (cpo:=c)) 
      with signature Oeq ==> Oeq as lub_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve @lub_eq_compat.


Notation "'mlub' f" := (lub (mon f)) (at level 60) : O_scope .

Lemma mlub_le_compat : forall `{c:cpo D} (f g:nat -> D) {mf:monotonic f} {mg:monotonic g}, 
                f <= g -> mlub f <= mlub g.
auto.
Save.
Hint Resolve @mlub_le_compat.

Lemma mlub_eq_compat : forall `{c:cpo D} (f g:nat -> D) {mf:monotonic f} {mg:monotonic g}, 
                f == g -> mlub f == mlub g.
auto.
Save.
Hint Resolve @mlub_eq_compat.

Lemma   le_mlub : forall `{c:cpo D} (f:nat -> D) {m:monotonic f} (n:nat), f n <= mlub f.
intros; apply (le_lub (mon f)); auto.
Save.

Lemma   mlub_le : forall `{c:cpo D}(f:nat -> D) {m:monotonic f}(x:D), (forall n, f n <= x) -> mlub f <= x.
intros; auto.
Save.
Hint Resolve @le_mlub @mlub_le.

Lemma islub_mlub : forall `{c:cpo D}(f:nat -> D) {m:monotonic f},
            islub f (mlub f).
split; auto.
Save.

Lemma islub_lub : forall `{c:cpo D}(f:nat -m> D),
            islub f (lub f).
split; auto.
Save.

Hint Resolve @islub_mlub @islub_lub.

Instance lub_mon `{c:cpo D} : monotonic lub.
intros; exact (lub_le_compat D o c). 
Save.

Definition Lub `{c:cpo D} : (nat -m> D) -m> D := mon lub.

Instance monotonic_lub_comp {O} {o:ord O} `{c:cpo D} (f:O -> nat -> D){mf:monotonic2 f}:
         monotonic (fun x => mlub (f x)).
intros; auto.
Save.

Lemma lub_cte : forall `{c:cpo D} (d:D), mlub (cte nat d) == d.
intros; apply Ole_antisym; auto.
apply le_lub with (f:=mon (fun _ => d)) (n:=O); auto.
Save.

Hint Resolve @lub_cte.

Lemma mlub_lift_right : forall `{c:cpo D} (f:nat -m> D) n, 
      lub f == mlub (seq_lift_right f n).
intros; apply Ole_antisym.
apply lub_le_compat; intro.
unfold seq_lift_right; simpl; auto with arith.
unfold seq_lift_right; simpl; auto.
Save.
Hint Resolve @mlub_lift_right.

Lemma mlub_lift_left : forall `{c:cpo D} (f:nat -m> D) n, 
      lub f == mlub (seq_lift_left f n).
intros; apply Ole_antisym.
apply lub_le_compat; intro.
unfold seq_lift_left; simpl; auto with arith.
unfold seq_lift_left; auto.
Save.
Hint Resolve @mlub_lift_left.

Lemma lub_lift_right : forall `{c:cpo D} (f:nat -m> D) n, 
      lub f == lub (mseq_lift_right f n).
intros; transitivity (mlub (seq_lift_right f n)); auto.
apply lub_eq_compat; intro m; auto.
Save.
Hint Resolve @lub_lift_right.

Lemma lub_lift_left : forall `{c:cpo D} (f:nat -m> D) n, 
      lub f == lub (mseq_lift_left f n).
intros; transitivity (mlub (seq_lift_left f n)); auto.
apply lub_eq_compat; intro m; auto.
Save.
Hint Resolve @lub_lift_left.

Lemma lub_le_lift : forall `{c:cpo D} (f g:nat -m> D)
      (n:nat), (forall k, n <= k -> f k <= g k) -> lub f <= lub g.
intros; apply lub_le; intros.
transitivity (f (n+n0)); auto with arith.
transitivity (g (n+n0)); auto with arith.
Save.

Lemma lub_eq_lift : forall `{c:cpo D} (f g:nat -m> D) {m:monotonic f} {m':monotonic g} 
      (n:nat), (forall k, n <= k -> f k == g k) -> lub f == lub g.
intros; apply Ole_antisym; apply lub_le_lift with n; intros; auto.
apply Oeq_le_sym; auto.
Save.

Lemma lub_seq_eq : forall `{c:cpo D} (f:nat -> D) (g: nat-m> D) (H:f == g),
      lub g == lub (mon_fun_subst f g H).
intros.
apply lub_eq_compat.
apply (mon_fun_eq f g H).
Save.

Lemma lub_Olt : forall `{c:cpo D} (f:nat -m> D) (k:D), 
      k < lub f -> ~ (forall n, f n <= k).
red; intros.
apply (Ole_not_lt (lub f) k); auto.
Save.

(** - (lub_fun h) x = lub_n (h n x) *)
Definition lub_fun {A} `{c:cpo D} (h : nat -m> (A -> D)) : A -> D
               := fun x => mlub (h <o> x).

(*
Instance lub_fun_mon  {O} {o:ord O} `{c:cpo D} (h : nat -m> (O -> D)) 
       {m:forall x, monotonic (h x)} : monotonic (lub_fun h).
red; unfold lub_fun; intros.
apply mlub_le_compat.
apply (shift_fun_mon h x y); trivial.
Save.
Hint Resolve @lub_fun_mon.
*)

Instance lub_shift_mon  {O} {o:ord O} `{c:cpo D} (h : nat -m> (O -m> D)) 
          : monotonic (fun (x:O) => lub (mshift h x)).
red; auto.
Save.
Hint Resolve @lub_shift_mon.


(** *** Functional cpos *)

Instance fcpo {A: Type} `(c:cpo D) : cpo (A -> D) :=
   {D0 := fun x:A => (0:D);
    lub :=  fun f => lub_fun f}.
abstract (intros f x; auto).
abstract (intros f n x; unfold lub_fun; apply (le_mlub  (shift f x) n); auto).
abstract (intros h f H x; unfold lub_fun; apply mlub_le; intro n; rewrite shift_simpl; auto).
Defined.


Lemma fcpo_lub_simpl : forall {A} `{c:cpo D} (h:nat -m> (A -> D))(x:A),
      (lub h) x = lub (h <o> x).
trivial.
Save.

Lemma lub_ishift : forall {A} `{c:cpo D} (h:A -> (nat -m> D)),
       lub (ishift h) == fun x => lub (h x).
intros; intro x.
rewrite fcpo_lub_simpl; apply lub_eq_compat; intro n; auto.
Save.

(** ** Cpo of monotonic functions *)


Instance fmon_cpo {O} {o:ord O} `{c:cpo D} : cpo (O -m> D) := 
     { D0  := mon (cte O (0:D));
       lub := fun h:nat -m> (O -m> D) => mon (fun (x:O) => lub (cpo:=c) (mshift h x))}.
abstract (intros f x; unfold cte; simpl; auto).
abstract (intros h n x; simpl; apply (le_mlub (fun y => h y x) n); auto).
abstract (intros h f H x; simpl; apply mlub_le; intro; apply H; auto).
Defined.

Lemma fmon_lub_simpl : forall {O} {o:ord O} `{c:cpo D} 
      (h:nat -m> (O -m> D))(x:O), (lub h) x = lub (mshift h x).
trivial.
Save.
Hint Resolve @fmon_lub_simpl.

Instance mon_fun_lub : forall {O} {o:ord O} `{c:cpo D} 
         (h:nat -m> (O -> D)) {mh:forall n, monotonic (h n)}, monotonic (lub h).
red; intros; simpl; auto.
unfold lub_fun; apply mlub_le_compat.
apply (shift_fun_mon h x y); trivial.
Save.

(*
Instance mon_lub : forall {O} {o:ord O} `{c:cpo D} 
         (h:nat -m> (O -m> D)), monotonic (mlub h).
intros; simpl; auto.
Save.
*)

(** Link between lubs on ordinary functions and monotonic functions **)

Lemma lub_mon_fcpo : forall {O} {o:ord O} `{c:cpo D} (h:nat -m> (O -m> D)), 
      lub h == mon (lub (mfun2 h)).
intros; intros x.
rewrite fmon_lub_simpl; rewrite mon_simpl; rewrite fcpo_lub_simpl.
apply lub_eq_compat; intro y; auto.
Save.

Lemma lub_fcpo_mon : forall {O} {o:ord O} `{c:cpo D} (h:nat -m> (O -> D)) 
     {mh:forall x, monotonic (h x)}, lub h == lub (mon2 h).
intros; intro x.
rewrite fmon_lub_simpl; rewrite fcpo_lub_simpl.
apply lub_eq_compat; intro y; auto.
Save.

Lemma double_lub_diag : forall `{c:cpo D} (h : nat -m> nat -m>  D),
        lub (lub h) == lub (diag h). 
intros; apply Ole_antisym.
apply lub_le; intros; simpl; apply lub_le; simpl; intros.
transitivity (h n0 (n+n0)); auto with arith.
transitivity (h (n+n0) (n+n0)).
apply (fmonotonic2 h); simpl; auto with arith.
apply (le_lub (diag h) (n + n0)%nat).
apply lub_le_compat.
intro n; simpl; unfold diag.
apply (le_mlub (fun y => h y n) n); auto.
Save.
Hint Resolve @double_lub_diag.


Lemma double_lub_shift : forall `{c:cpo D} (h : nat -m> nat -m>  D),
        lub (lub h) == lub (lub (mshift h)).
intros; transitivity (lub (diag h)); auto.
transitivity (lub (diag (mshift h))); auto.
Save.
Hint Resolve @double_lub_shift.

(*
Instance mlub_monotonic `{c:cpo D} (h : nat -> nat ->  D) {m:monotonic2 h}:
       monotonic (fun m => mlub (h m)).
red; intros.
apply mlub_le_compat; intro z; auto.
Save.

Lemma doubl_lub_simpl_exch : forall `{c:cpo D} (h : nat -m> nat -m>  D),
        lub (lub h) == mlub (mon (fun n => mlub (h n))
                                   (fmonotonic:=mlub_monotonic h)).
intros.
apply Oeq_trans with (1:= diag h).

Save.

Instance mlub_shift_monotonic `{c:cpo D} (h : nat -> nat ->  D) {m:monotonic2 h}:
       monotonic (fun m => mlub (h <o> m)).
red; intros.
apply mlub_le_compat; intro z.
unfold shift; auto.
Save.

Lemma doubl_lub_simpl : forall `{c:cpo D} (h : nat -> nat ->  D) {m:monotonic2 h},
        mlub (mlub h) == 
        lub (mon (fun m => mlub (h <o> m)) (fmonotonic:=mlub_shift_monotonic h)).
intros; apply mlub_eq_compat; auto.
Save.

Lemma doubl_lub_simpl : forall `{c:cpo D} (h : nat -> nat ->  D) {m:monotonic2 h},
        mlub (mlub h) == 
        lub (mon (fun m => mlub (h <o> m)) (fmonotonic:=mlub_shift_monotonic h)).
intros; apply mlub_eq_compat; auto.
Save.


Lemma double_lub_simpl : forall `{c:cpo D} (h : nat -> nat ->  D) {m:monotonic2 h},
        mlub (Lub @ (mon_comp h)) == mlub (diag h). 
intros; apply Ole_antisym.
apply mlub_le; simpl; intros.
apply mlub_le; unfold shift; intros.
transitivity (h n (n+n0)).
apply m; simpl; auto with arith.
transitivity (h (n+n0) (n+n0)).
apply m; simpl; auto with arith.
apply (le_mlub (diag h) (n + n0)%nat).
apply mlub_le_compat; simpl.
intro x; unfold diag, lub_fun, mon_comp, comp; simpl; auto.
Save.
Hint Resolve @double_lub_simpl.



Lemma lub_exch_eq : forall `{c:cpo D} (h : nat -> (nat ->  D)) {m:monotonic2 h},
 mlub (Lub @ mon_comp h) == mlub (mlub h).
intros; transitivity (mlub (diag h)); auto.
Save.

Hint Resolve @lub_exch_eq.
*)

(** ** Continuity *)

Lemma lub_comp_le : 
    forall `{c1:cpo D1} `{c2:cpo D2} (f:D1 -m> D2) (h : nat -m> D1), 
                lub (f @ h) <= f (lub h).
intros; apply lub_le; unfold comp; intros.
apply (fmonotonic f); auto.
Save.
Hint Resolve @lub_comp_le.

Lemma lub_app2_le : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} 
        (F:D1 -m> D2 -m> D3) (f : nat -m> D1) (g: nat -m> D2),
        lub ((F @2 f) g) <= F (lub f) (lub g).
intros; apply mlub_le; unfold app2; auto.
intros; apply (fmonotonic2 F); auto.
Save.
Hint Resolve @lub_app2_le.

Class continuous `{c1:cpo D1} `{c2:cpo D2} (f:D1 -m> D2) :=  
    cont_intro : forall (h : nat -m> D1), f (lub h) <= lub (f @ h).

Typeclasses Opaque continuous.

Lemma continuous_eq_compat : forall `{c1:cpo D1} `{c2:cpo D2}(f g:D1 -m> D2), 
                  f == g -> continuous f -> continuous g.
red; intros.
transitivity (f (lub h)).
assert (g <= f); auto.
transitivity (lub (f @ h)); auto.
Save. 

Add Parametric Morphism `{c1:cpo D1} `{c2:cpo D2} : (@continuous D1 _ _ D2 _ _)
     with signature Oeq ==> iff 
as continuous_eq_compat_iff.
split; intros.
apply continuous_eq_compat with x; trivial.
apply continuous_eq_compat with y; auto.
Save.

Lemma lub_comp_eq : 
    forall `{c1:cpo D1} `{c2:cpo D2} (f:D1 -m> D2) (h : nat -m> D1),  
             continuous f -> f (lub h) == lub (f @ h).
intros; apply Ole_antisym; auto.
Save.
Hint Resolve @lub_comp_eq.


(** - mon0 x == 0 *)
Instance cont0  `{c1:cpo D1} `{c2:cpo D2} : continuous (mon (cte D1 (0:D2))).
red; simpl; intros; unfold cte; auto.
Save.
Implicit Arguments cont0 [].

(** - double_app f g n m = f m (g n) *)
Definition double_app `{o1:ord Oa} `{o2:ord Ob} `{o3:ord Oc} `{o4: ord Od} 
      (f:Oa -m> Oc -m> Od) (g:Ob -m> Oc) 
        : Ob -m> (Oa -m> Od) := mon ((mshift f) @ g).
 
(*
Lemma double_lub_diag : forall `{c:cpo D} (h:nat -> nat -> D) {mh:monotonic2 h},
             mlub (mlub (fun x => mon (h x))) == mlub (diag h).
intros; apply Ole_antisym.
apply mlub_le; intros; simpl; apply mlub_le; unfold shift, fun2; simpl; intros.
transitivity (h (n+n0) (n+n0)); simpl; auto with arith.
apply (le_mlub (diag h) (n + n0)%nat).
apply mlub_le_compat.
unfold diag; intro x; simpl; unfold lub_fun, shift; auto.
apply (le_mlub (h <o> x) x); auto.
Save.
*)

(** *** Continuity *)

Class continuous2 `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}  (F:D1 -m> D2 -m> D3)  := 
continuous2_intro : forall (f : nat -m> D1) (g :nat -m> D2),
                 F (lub f) (lub g) <= lub ((F @2 f) g).

Lemma continuous2_app : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
            (F : D1 -m> D2 -m> D3) {cF:continuous2 F} (k:D1), continuous (F k).
red; intros.
transitivity  (F (mlub (cte nat k))  (lub h)); auto.
apply (fmonotonic2 F); auto.
transitivity (lub ((F @2 (mon (cte nat k))) h)); auto.
apply lub_le_compat; simpl; auto.
Save.

Typeclasses Opaque continuous2.

Lemma continuous2_eq_compat : 
   forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} (f g : D1 -m> D2 -m> D3),
   f == g -> continuous2 f -> continuous2 g.
red; intros.
transitivity (f (lub f0) (lub g0)).
generalize (H (lub f0) (lub (g0))); auto.
transitivity (lub ((f @2 f0) g0)); auto.
Save.

Lemma continuous2_continuous : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
           (F : D1 -m> D2 -m> D3), continuous2 F -> continuous F.
red; intros; intro k.
transitivity (F (lub h) (mlub (cte nat k)) ); auto.
transitivity (lub ((F @2 h) (mon (cte nat k)))); auto.
rewrite fmon_lub_simpl.
apply lub_le_compat; simpl; auto.
Save.
Hint Immediate @continuous2_continuous.

Lemma continuous2_left : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
             (F : D1 -m> D2 -m> D3) (h:nat -m> D1) (x:D2),
             continuous F ->  F (lub h) x <= lub (mshift (F @ h) x).
intros.
transitivity ((mlub (F @ h)) x); auto.
exact (H h x).
Save.

Lemma continuous2_right : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
             (F : D1 -m> D2 -m> D3) (x:D1)(h:nat -m> D2),
             continuous2 F ->  F x (lub h) <= lub (F x @ h).
intros; apply (continuous2_app F x).
Save.

Lemma continuous_continuous2 : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
      (F : D1 -m> D2 -m> D3) (cFr: forall k:D1, continuous (F k)) (cF: continuous F),
      continuous2 F.
red; intros.
transitivity (lub (F (lub f) @ g)); auto.
apply lub_le; unfold comp; simpl; intros.
transitivity ((lub (F@f)) (g n)).
apply cF.
transitivity (lub (mshift (F@f) (g n))); auto.
rewrite (lub_lift_right ((F @2 f) g) n).
apply lub_le_compat.
unfold seq_lift_right; simpl.
intro; apply (fmonotonic2 F); auto with arith.
Save.

Hint Resolve @continuous2_app @continuous2_continuous @continuous_continuous2.

Lemma lub_app2_eq : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
      (F : D1 -m> D2 -m> D3) {cFr:forall k:D1, continuous (F k)} {cF : continuous F}, 
      forall (f:nat -m> D1) (g:nat -m> D2),
      F (lub f) (lub g) == lub ((F@2 f) g).
intros; apply Ole_antisym; auto.
apply (continuous_continuous2 F); trivial.
Save.

Lemma lub_cont2_app2_eq : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
      (F : D1 -m> D2 -m> D3){cF : continuous2 F},
      forall (f:nat -m> D1) (g:nat -m> D2), 
      F (lub f) (lub g) == lub ((F@2 f) g).
intros; apply lub_app2_eq; auto.
intro; apply (continuous2_app F).
apply continuous2_continuous; trivial.
Save.

Lemma mshift_continuous2 : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
             (F : D1 -m> D2 -m> D3), continuous2 F -> continuous2 (mshift F).
red; intros; repeat rewrite mshift_simpl; auto.
rewrite (H g f); auto.
apply lub_le_compat; intro n; auto.
Save.
Hint Resolve @mshift_continuous2.

Lemma monotonic_sym : forall `{o1:ord D1} `{o2:ord D2} (F : D1 -> D1 -> D2),
      (forall x y, F x y == F y x) -> (forall k:D1, monotonic (F k)) -> monotonic F.
red; intros; intro k.
transitivity (F k x); auto.
transitivity (F k y); auto.
apply H0; trivial.
Save.
Hint Immediate @monotonic_sym.

Lemma monotonic2_sym : forall `{o1:ord D1} `{o2:ord D2} (F : D1 -> D1 -> D2),
      (forall x y, F x y == F y x) -> (forall k:D1, monotonic (F k)) -> monotonic2 F.
intros; apply mon2_intro; auto.
Save.
Hint Immediate @monotonic2_sym.

Lemma continuous_sym : forall `{c1:cpo D1} `{c2:cpo D2} (F : D1 -m> D1 -m> D2),
      (forall x y, F x y == F y x) -> (forall k:D1, continuous (F k)) -> continuous F.
red; intros; intro k.
transitivity (F k (lub h)); auto.
transitivity (lub ((F k) @ h)); auto.
simpl.
unfold comp, fun_ext, lub_fun, shift, fun2; simpl; auto.
Save.

Lemma continuous2_sym : forall `{c1:cpo D1} `{c2:cpo D2} (F : D1 -m>D1 -m>D2),
      (forall x y, F x y == F y x) -> (forall k, continuous (F k)) -> continuous2 F.
intros; apply continuous_continuous2; auto.
apply continuous_sym; auto.
Save.
Hint Resolve @continuous2_sym.

(** - continuity is preserved by composition *)

Lemma continuous_comp : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} 
   (f:D2 -m> D3)(g:D1 -m> D2), continuous f -> continuous g -> continuous (mon (f@g)).
red; intros.
simpl; unfold comp at 1; simpl.
transitivity (f (lub (g@h))).
apply (fmonotonic f); auto.
transitivity (lub (f@(g@h))); auto.
Save.
Hint Resolve @continuous_comp.

Lemma continuous2_comp : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} `{c4:cpo D4}
  (f:D1 -m> D2)(g:D2 -m> D3 -m> D4),
  continuous f -> continuous2 g -> continuous2 (g @ f).
intros; apply continuous_continuous2.
red; intros.
unfold comp at 1; simpl.
apply (continuous2_right g (f k) h); trivial.
apply (continuous_comp g f); auto.
apply continuous2_continuous; trivial.
Save.
Hint Resolve @continuous2_comp.

Lemma continuous2_comp2 : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} `{c4:cpo D4}
    (f:D3 -m> D4)(g:D1 -m> D2 -m> D3),
    continuous f -> continuous2 g -> continuous2 (fcomp2 D1 D2 D3 D4 f g).
red; intros.
rewrite fcomp2_simpl.
transitivity (f (lub ((g@2 f0) g0))); auto.
transitivity (lub (f@((g@2 f0) g0))); auto.
apply lub_le_compat.
intros x; trivial.
Save.
Hint Resolve @continuous2_comp2.

Lemma continuous2_app2 : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} `{c4:cpo D4}
    (F : D1 -m> D2 -m> D3) (f:D4 -m> D1)(g:D4 -m> D2), continuous2 F ->
    continuous f -> continuous g -> continuous ((F @2 f) g).
red; intros.
rewrite app2_simpl.
transitivity (F (lub (f@h)) (lub (g@h))).
apply monotonic2_intro; auto.
rewrite H.
apply lub_le_compat.
intros x; trivial.
Save.
Hint Resolve @continuous2_app2.


(** ** Cpo of continuous functions *)

Instance lub_continuous `{c1:cpo D1} `{c2:cpo D2}
     (f:nat -m> (D1 -m> D2)) {cf:forall n, continuous (f n)}
     : continuous  (lub f).
red; intros.
transitivity (lub (mshift f (lub h))); auto.
apply lub_le; intros.
rewrite mshift_simpl.
transitivity (lub ((f n) @ h)); auto.
Save.

Record fcont `{c1:cpo D1} `{c2:cpo D2}: Type 
     := cont {fcontm :> D1 -m> D2; fcontinuous : continuous fcontm}.
Existing Instance fcontinuous.

Hint Resolve @fcontinuous.
Implicit Arguments fcont [[o][c1] [o0][c2]].
Implicit Arguments cont [[D1][o][c1] [D2][o0][c2] [fcontinuous]].

(** printing -c> %\ensuremath{\stackrel{c}{\leftarrow}}% #->#*)

Infix "-c>" := fcont (at level 30, right associativity) : O_scope.

Definition fcont_fun `{c1:cpo D1} `{c2:cpo D2} (f:D1 -c> D2) : D1 -> D2 := fun x => f x.

Instance fcont_ord `{c1:cpo D1} `{c2:cpo D2} : ord (D1 -c> D2)
  := {Oeq := fun f g => forall x, f x == g x; Ole := fun f g =>  forall x, f x <= g x}.
abstract (split; intuition; red; intros; transitivity (y x0); auto).
Defined.

Lemma fcont_le_intro : forall `{c1:cpo D1} `{c2:cpo D2} (f g : D1 -c> D2), 
    (forall x, f x <= g x) -> f <= g.
trivial.
Save.

Lemma fcont_le_elim : forall `{c1:cpo D1} `{c2:cpo D2} (f g : D1 -c> D2), 
     f <= g -> forall x, f x <= g x.
trivial.
Save.

Lemma fcont_eq_intro : forall `{c1:cpo D1} `{c2:cpo D2} (f g : D1 -c> D2), 
      (forall x, f x == g x) -> f == g.
intros; apply Ole_antisym; apply fcont_le_intro; auto.
Save.

Lemma fcont_eq_elim : forall `{c1:cpo D1} `{c2:cpo D2} (f g : D1 -c> D2), 
       f == g -> forall x, f x == g x.
intros; apply Ole_antisym; apply fcont_le_elim; auto.
Save.

Lemma fcont_le : forall `{c1:cpo D1} `{c2:cpo D2} (f : D1 -c> D2) (x y : D1),
            x <= y -> f x <= f y.
intros; apply (fmonotonic (fcontm f) x y H).
Save.
Hint Resolve @fcont_le.

Lemma fcont_eq : forall `{c1:cpo D1} `{c2:cpo D2} (f : D1 -c> D2) (x y : D1),
            x == y -> f x == f y.
intros; apply (fmon_eq (fcontm f) x y H).
Save.
Hint Resolve @fcont_eq.

Definition fcont0 D1 `{c1:cpo D1} D2 `{c2:cpo D2} : D1 -c> D2 := cont (mon (cte D1 (0:D2))).

Instance fcontm_monotonic : forall `{c1:cpo D1} `{c2:cpo D2}, 
         monotonic (fcontm (D1:=D1) (D2:=D2)).
intros; auto.
Save.

Definition Fcontm D1 `{c1:cpo D1} D2 `{c2:cpo D2} : (D1 -c> D2) -m> (D1 -m> D2) := 
     mon (fcontm (D1:=D1) (D2:=D2)).

Instance fcont_lub_continuous : 
    forall `{c1:cpo D1} `{c2:cpo D2} (f:nat -m> (D1 -c> D2)),
    continuous (lub (D:=D1 -m> D2) (Fcontm D1 D2 @ f)).
intros; apply lub_continuous.
intro; simpl; auto.
Save.

Definition fcont_lub `{c1:cpo D1} `{c2:cpo D2} : (nat -m> (D1 -c> D2)) -> D1 -c> D2 := 
     fun f => cont (lub (D:=D1 -m> D2) (Fcontm D1 D2 @ f)).

Instance fcont_cpo `{c1:cpo D1} `{c2:cpo D2} : cpo (D1-c> D2) :=
      {D0:=fcont0 D1 D2; lub:=fcont_lub (D1:=D1) (D2:=D2)}.
abstract (intros; simpl; unfold cte; auto).
abstract (intros; simpl; intros; apply (le_mlub (fun y : nat => f y x))).
abstract (intros; simpl; intros; apply mlub_le; intro n; apply (H n x0)).
Defined.


Definition fcont_app {O} {o:ord O} `{c1:cpo D1} `{c2:cpo D2} (f: O -m> D1 -c> D2) (x:D1) : O -m> D2
         := mshift (Fcontm D1 D2 @ f) x.

(** printing <_> %\ensuremath{<\!\_\!>}% #&lt;_&gt;# *)
Infix "<_>" := fcont_app (at level 70) : O_scope.

Lemma fcont_app_simpl : forall {O} {o:ord O} `{c1:cpo D1} `{c2:cpo D2} (f: O -m> D1 -c> D2)(x:D1)(y:O),
            (f <_> x) y = f y x.
trivial.
Save.

Instance ishift_continuous : 
   forall {A:Type} `{c1:cpo D1} `{c2:cpo D2} (f: A -> (D1 -c> D2)), 
          continuous (ishift f).
red; intros; intro x.
simpl.
transitivity (lub ((f x) @ h)); auto.
apply lub_le_compat; simpl; trivial.
Qed.

Definition fcont_ishift {A:Type} `{c1:cpo D1} `{c2:cpo D2} (f: A -> (D1 -c> D2)) 
        : D1 -c> (A -> D2) := cont _ (fcontinuous:=ishift_continuous f).

Instance mshift_continuous : forall {O} {o:ord O} `{c1:cpo D1} `{c2:cpo D2} (f: O -m> (D1 -c> D2)),
         continuous (mshift (Fcontm D1 D2 @ f)).
red; intros; intro x.
simpl.
rewrite (fcontinuous (f x) h); auto.
Save.

Definition fcont_mshift {O} {o:ord O} `{c1:cpo D1} `{c2:cpo D2} (f: O -m> (D1 -c> D2)) 
   : D1 -c> O -m> D2 := cont (mshift (Fcontm D1 D2 @ f)).


Lemma fcont_app_continuous : 
       forall {O} {o:ord O} `{c1:cpo D1} `{c2:cpo D2} (f: O -m> D1 -c> D2) (h:nat -m> D1),
            f <_> (lub h) <= lub (D:=O -m> D2) ((fcont_mshift f) @ h).
intros; intro x.
rewrite fcont_app_simpl.
rewrite (fcontinuous (f x) h); simpl; auto.
Save.

Lemma fcont_lub_simpl : forall `{c1:cpo D1} `{c2:cpo D2} (h:nat -m> D1 -c> D2)(x:D1),
            lub h x = lub (h <_> x).
trivial.
Save.

Instance cont_app_monotonic : forall `{o1:ord D1} `{c2:cpo D2} `{c3:cpo D3} (f:D1 -m> D2 -m> D3)
            (p:forall k, continuous (f k)), 
            monotonic (Ob:=D2 -c> D3) (fun (k:D1) => cont _ (fcontinuous:=p k)).
red; simpl; intros.
apply (fmonotonic f); trivial.
Qed.

Definition cont_app `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} (f:D1 -m> D2 -m> D3)
            (p:forall k, continuous (f k)) : D1 -m> (D2 -c> D3)
    := mon (fun k => cont (f k) (fcontinuous:=p k)).
            
Lemma cont_app_simpl : 
forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}(f:D1 -m> D2 -m> D3)(p:forall k, continuous (f k))
        (k:D1),  cont_app f p k = cont (f k).
trivial.
Save.

Instance cont2_continuous `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} (f:D1 -m> D2 -m> D3)
           (p:continuous2 f) : continuous (cont_app f (continuous2_app f)).
red; intros; rewrite cont_app_simpl; intro k; simpl.
transitivity (lub (D:=D2 -m> D3) (f@h) k).
assert (continuous f).
apply continuous2_continuous; trivial.
apply H.
simpl; auto.
Qed.

Definition cont2 `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} (f:D1 -m> D2 -m> D3)
           {p:continuous2 f} : D1 -c> (D2 -c> D3)
:= cont (cont_app f (continuous2_app f)).


Instance Fcontm_continuous `{c1:cpo D1} `{c2:cpo D2} : continuous (Fcontm D1 D2).
red; intros; auto.
Save.
Hint Resolve @Fcontm_continuous.

Instance fcont_comp_continuous : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} 
    (f:D2 -c> D3) (g:D1 -c> D2), continuous (f @ g).
intros; apply (continuous_comp (fcontm f) (fcontm g)); auto.
Save.

Definition fcont_comp `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} (f:D2 -c> D3) (g:D1 -c> D2) 
   : D1 -c> D3 := cont (f @ g).

Infix "@_" := fcont_comp (at level 35) : O_scope.

Lemma fcont_comp_simpl : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
       (f:D2 -c> D3)(g:D1 -c> D2) (x:D1), (f @_ g) x = f (g x).
trivial.
Save.

Lemma fcontm_fcont_comp_simpl : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
       (f:D2 -c> D3)(g:D1 -c> D2), fcontm (f @_ g) = f @ g.
trivial.
Save.

Lemma fcont_comp_le_compat : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
      (f g : D2 -c> D3) (k l :D1 -c> D2),
      f <= g -> k <= l -> f @_ k <= g @_ l.
intros; apply fcont_le_intro; intro x.
repeat (rewrite fcont_comp_simpl).
transitivity (g (k x)); auto.
Save.
Hint Resolve @fcont_comp_le_compat.

Add Parametric Morphism `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
    : (@fcont_comp _ _ c1 _ _ c2 _ _ c3) 
      with signature Ole ++> Ole ++> Ole as fcont_comp_le_morph.
intros.
apply fcont_comp_le_compat; trivial.
Save.

Add Parametric Morphism `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
    : (@fcont_comp _ _ c1 _ _ c2 _ _ c3) 
      with signature Oeq ==> Oeq ==> Oeq as fcont_comp_eq_compat.
intros.
apply Ole_antisym; auto.
Save.


Definition fcont_Comp D1 `{c1:cpo D1} D2 `{c2:cpo D2} D3 `{c3:cpo D3} 
      : (D2 -c> D3) -m> (D1 -c> D2) -m> D1 -c> D3 
      := mon2 _ (mf:=fcont_comp_le_compat (D1:=D1) (D2:=D2) (D3:=D3)).

Lemma fcont_Comp_simpl : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
                        (f:D2 -c> D3) (g:D1 -c> D2), fcont_Comp D1 D2 D3 f g = f @_ g.
trivial.
Save.

Instance fcont_Comp_continuous2 
   : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}, continuous2 (fcont_Comp D1 D2 D3).
red; intros.
change ((lub  f) @_ (lub g) <= lub (D:=D1 -c> D3) ((fcont_Comp D1 D2 D3 @2 f) g)).
apply fcont_le_intro; intro x; rewrite fcont_comp_simpl.
repeat (rewrite fcont_lub_simpl).
rewrite fcont_app_continuous.
rewrite double_lub_diag.
apply lub_le_compat; simpl; auto.
Save.

Definition fcont_COMP  D1 `{c1:cpo D1} D2 `{c2:cpo D2} D3 `{c3:cpo D3}
      : (D2 -c> D3) -c> (D1 -c> D2) -c> D1 -c> D3 
      := cont2 (fcont_Comp D1 D2 D3).

Lemma fcont_COMP_simpl : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
        (f: D2 -c> D3) (g:D1 -c> D2),
	fcont_COMP D1 D2 D3 f g = f @_ g.
trivial.
Save.

Definition fcont2_COMP D1 `{c1:cpo D1} D2 `{c2:cpo D2} D3 `{c3:cpo D3} D4 `{c4:cpo D4}
   : (D3 -c> D4) -c> (D1 -c> D2 -c> D3) -c> D1 -c> D2 -c> D4 := 
     (fcont_COMP D1 (D2 -c> D3) (D2 -c> D4)) @_ (fcont_COMP D2 D3 D4).

Definition fcont2_comp `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} `{c4:cpo D4}
           (f:D3 -c> D4)(F:D1 -c> D2 -c> D3) := fcont2_COMP D1 D2 D3 D4 f F.

Infix "@@_" := fcont2_comp (at level 35) : O_scope.

Lemma fcont2_comp_simpl : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} `{c4:cpo D4}
       (f:D3 -c> D4)(F:D1 -c> D2 -c> D3)(x:D1)(y:D2), (f @@_ F) x y = f (F x y).
trivial.
Save.
            
Lemma fcont_le_compat2 : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} (f : D1 -c> D2 -c> D3)
    (x y : D1) (z t : D2), x <= y -> z <= t -> f x z <= f y t.
intros; transitivity (f y z); auto.
assert (f x <= f y); auto.
Save.
Hint Resolve @fcont_le_compat2.

Lemma fcont_eq_compat2 : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} (f : D1 -c> D2 -c> D3)
    (x y : D1) (z t : D2), x == y -> z == t -> f x z == f y t.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve @fcont_eq_compat2.

Lemma fcont_continuous : forall `{c1:cpo D1} `{c2:cpo D2} (f:D1 -c> D2)(h:nat -m> D1),
            f (lub h) <= lub (f @ h).
intros; apply (fcontinuous f h).
Save.
Hint Resolve @fcont_continuous.

Instance fcont_continuous2 : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
         (f:D1 -c> D2 -c> D3), continuous2 (Fcontm D2 D3 @ f).
intros; apply continuous_continuous2; intros.
change (continuous (f k)); auto.
apply (continuous_comp (Fcontm D2 D3) (fcontm f)); auto.
Save.
Hint Resolve @fcont_continuous2.

Instance cshift_continuous2 : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
         (f:D1 -c> D2 -c> D3), continuous2 (mshift (Fcontm D2 D3 @ f)).
intros; auto.
Save.
Hint Resolve @cshift_continuous2.

Definition cshift `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} (f:D1 -c> D2 -c> D3) 
   : D2 -c> D1 -c> D3 := cont2 (mshift (Fcontm D2 D3 @ f)).

Lemma cshift_simpl : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
           (f:D1 -c> D2 -c> D3) (x:D2) (y:D1), cshift f x y = f y x.
trivial.
Save.

Definition fcont_SEQ  D1 `{c1:cpo D1} D2 `{c2:cpo D2} D3 `{c3:cpo D3}
   : (D1 -c> D2) -c> (D2 -c> D3) -c> D1 -c> D3 := cshift (fcont_COMP D1 D2 D3).

Lemma fcont_SEQ_simpl : forall `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3}
       (f: D1 -c> D2) (g:D2 -c> D3), fcont_SEQ D1 D2 D3 f g = g @_ f.
trivial.
Save.

(*
Instance fcont_comp2_continuous `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} `{c4:cpo D4}
                (f: D2 -c> D3 -c> D4) (g:D1 -c> D2) (h:D1 -c> D3) 
     : continuous (((Fcontm D3 D4 @ f) @2 g) h).
red; intros; simpl.
change (f (g (lub h0)) (h (lub h0)) <= lub ((Fcontm D3 D4 @ f @2 g) h @ h0)).
transitivity (f (lub (g @ h0)) (lub (h @ h0))); auto.
apply (fcont_continuous2 f (g @ h0) (h @ h0)).


Definition fcont_comp2 `{c1:cpo D1} `{c2:cpo D2} `{c3:cpo D3} `{c4:cpo D4}
                (f: D2 -c> D3 -c> D4) (g:D1 -c> D2) (h:D1 -c> D3) : D1 -c> D4
                := cont (((Fcontm D3 D4 @ f) @2 g) h).

intros D1 D2 D3 D4 f g h.
exists (((Fcontit D3 D4 @fcontit f) @2 fcontit g) (fcontit h)).
red; intros; simpl.
change (f (g (lub h0)) (h (lub h0)) <= lub (c:=D4) ((Fcontit D3 D4 @ fcontit f @2 fcontit g) (fcontit h) @ h0)).
transitivity (f (lub (c:=D2) (fcontit g @ h0)) (lub (c:=D3) (fcontit h @ h0))); auto.
apply (fcont_continuous2 f (fcontit g @ h0) (fcontit h @ h0)).
Defined.

Infix "@2_" := fcont_comp2 (at level 35, right associativity) : O_scope.

Lemma fcont_comp2_simpl : forall (D1 D2 D3 D4:cpo)
                (F:D2 -c> D3 -c>D4) (f:D1 -c> D2) (g:D1 -c> D3) (x:D1), (F@2_ f) g x = F (f x) (g x).
trivial.
Save.

Add Morphism fcont_comp2 with signature Ole++>Ole ++> Ole ++> Ole 
as fcont_comp2_le_morph.
intros D1 D2 D3 D4 F G HF f1 f2 Hf g1 g2 Hg x.
transitivity (fcontit (fcontit G (fcontit f1 x)) (fcontit g1 x)); auto.
change (Fcontit D3 D4 (fcontit G (fcontit f1 x)) (fcontit g1 x) <=
              Fcontit D3 D4 (fcontit G (fcontit f2 x)) (fcontit g2 x)).
apply (fmon_le_compat2 (Fcontit D3 D4)); auto.
Save.

Add Morphism fcont_comp2 with signature Oeq ==> Oeq ==> Oeq ==> Oeq as fcont_comp2_eq_compat.
intros D1 D2 D3 D4 F G (HF1,HF2) f1 f2 (Hf1,Hf2) g1 g2 (Hg1,Hg2).
apply Ole_antisym.
exact (fcont_comp2_le_morph HF1 Hf1 Hg1).
exact (fcont_comp2_le_morph HF2 Hf2 Hg2).
Save.


(** - Identity function is continuous *)
*)

Instance Id_mon : forall `{o1:ord Oa}, monotonic (fun x:Oa => x).
red; trivial.
Save.

Definition Id Oa {o1:ord Oa} : Oa -m> Oa := mon (fun x => x).

Lemma Id_simpl : forall `{o1:ord Oa} (x:Oa), Id Oa x = x.
trivial.
Save.

(*
Definition ID : forall D:cpo, D-c>D.
intros; exists (Id D); red; auto.
Defined.


Lemma ID_simpl : forall D x, ID D x = Id D x.
trivial.
Save.

Definition AP (D1 D2:cpo) : (D1 -c>D2)-c>D1 -c>D2:=ID (D1 -c>D2).

Lemma AP_simpl : forall (D1 D2:cpo) (f : D1 -c>D2) (x:D1), AP D1 D2 f x = f x.
trivial.
Save.

Definition fcont_comp3 (D1 D2 D3 D4 D5:cpo)
                (F:D2 -c> D3 -c>D4-c>D5)(f:D1 -c> D2)(g:D1 -c> D3)(h:D1 -c>D4): D1 -c>D5
  := (AP D4 D5 @2_ ((F @2_ f) g)) h.

Infix "@3_" := fcont_comp3 (at level 35, right associativity) : O_scope.

Lemma fcont_comp3_simpl : forall (D1 D2 D3 D4 D5:cpo)
                (F:D2 -c> D3 -c>D4-c>D5) (f:D1 -c> D2) (g:D1 -c> D3) (h:D1 -c>D4) (x:D1), 
                (F@3_ f) g h x = F (f x) (g x) (h x).
trivial.
Save.

(** ** Product of two cpos *)

Definition Oprod : ord -> ord -> ord.
intros Oa Ob; exists (Oa * Ob)%type (fun (x y:Oa*Ob) => fst x <= fst y /\ snd x <= snd y); intuition.
transitivity a0; trivial.
transitivity b0; trivial.
Defined.

Definition Fst (Oa Ob : ord) : Oprod Oa Ob -m> Oa.
intros Oa Ob; exists (fst (A:=Oa) (B:=Ob)); red; simpl; intuition.
Defined.

Definition Snd (Oa Ob : ord) : Oprod Oa Ob -m> Ob.
intros Oa Ob; exists (snd (A:=Oa) (B:=Ob)); red; simpl; intuition.
Defined.

Definition Pairr (Oa Ob : ord) : Oa -> Ob -m> Oprod Oa Ob.
intros Oa Ob x; exists (fun y:Ob => (x,y)); red; auto.
Defined.

Definition Pair (Oa Ob : ord) : Oa -m> Ob -m> Oprod Oa Ob.
intros Oa Ob; exists (Pairr (Oa:=Oa) Ob); red; auto.
Defined.

Lemma Fst_simpl : forall (Oa Ob : ord) (p:Oprod Oa Ob), Fst Oa Ob p = fst p.
trivial.
Save.

Lemma Snd_simpl : forall (Oa Ob : ord) (p:Oprod Oa Ob), Snd Oa Ob p = snd p.
trivial.
Save.

Lemma Pair_simpl : forall (Oa Ob : ord) (x:Oa)(y:Ob), Pair Oa Ob x y = (x,y).
trivial.
Save.


Definition prod0 (D1 D2:cpo) : Oprod D1 D2 := (0: D1,0: D2).
Definition prod_lub (D1 D2:cpo) (f : nat -m> Oprod D1 D2) := (lub (Fst D1 D2@f), lub (Snd D1 D2@f)).

Definition Dprod : cpo -> cpo -> cpo.
intros D1 D2; exists (Oprod D1 D2) (prod0 D1 D2) (prod_lub (D1:=D1) (D2:=D2)); unfold prod_lub; intuition.
transitivity (fst (fmonot f n), snd (fmonot f n)); simpl; intuition.
apply le_lub with (f:=Fst D1 D2 @ f) (n:=n).
apply le_lub with (f:=Snd D1 D2 @ f) (n:=n).
transitivity (fst x, snd x); simpl; intuition.
apply lub_le; simpl; intros.
case (H n); auto.
apply lub_le; simpl; intros.
case (H n); auto.
Defined.

Lemma Dprod_eq_intro : forall (D1 D2:cpo) (p1 p2: Dprod D1 D2),
             fst p1 == fst p2 -> snd p1 == snd p2 -> p1 == p2.
split; simpl; auto.  
Save.
Hint Resolve Dprod_eq_intro.

Lemma Dprod_eq_pair : forall (D1 D2:cpo) (x1 y1:D1) (x2 y2:D2),
             x1==y1 -> x2==y2 -> ((x1,x2):Dprod D1 D2) == (y1,y2).
auto.  
Save.
Hint Resolve Dprod_eq_pair.

Lemma Dprod_eq_elim_fst : forall (D1 D2:cpo) (p1 p2: Dprod D1 D2),
             p1==p2 -> fst p1 == fst p2.
split; case H; simpl; intuition.  
Save.
Hint Immediate Dprod_eq_elim_fst.

Lemma Dprod_eq_elim_snd : forall (D1 D2:cpo) (p1 p2: Dprod D1 D2),
             p1==p2 -> snd p1 == snd p2.
split; case H; simpl; intuition.  
Save.
Hint Immediate Dprod_eq_elim_snd.

Definition FST (D1 D2:cpo) : Dprod D1 D2 -c> D1.
intros; exists (Fst D1 D2); red; intros; auto.
Defined.

Definition SND (D1 D2:cpo) : Dprod D1 D2 -c> D2.
intros; exists (Snd D1 D2); red; intros; auto.
Defined.

Lemma Pair_continuous2 : forall (D1 D2:cpo), continuous2 (D3:=Dprod D1 D2) (Pair D1 D2).
red; intros; auto.
Save.

Definition PAIR (D1 D2:cpo) : D1 -c> D2 -c> Dprod D1 D2 
                := continuous2_cont (Pair_continuous2 (D1:=D1) (D2:=D2)).

Lemma FST_simpl : forall (D1 D2 :cpo) (p:Dprod D1 D2), FST D1 D2 p = Fst D1 D2 p.
trivial.
Save.

Lemma SND_simpl : forall (D1 D2 :cpo) (p:Dprod D1 D2), SND D1 D2 p = Snd D1 D2 p.
trivial.
Save.

Lemma PAIR_simpl : forall (D1 D2 :cpo) (p1:D1) (p2:D2), PAIR D1 D2 p1 p2 = Pair D1 D2 p1 p2.
trivial.
Save.

Lemma FST_PAIR_simpl : forall (D1 D2 :cpo) (p1:D1) (p2:D2), 
            FST D1 D2 (PAIR D1 D2 p1 p2) = p1.
trivial.
Save.

Lemma SND_PAIR_simpl : forall (D1 D2 :cpo) (p1:D1) (p2:D2), 
            SND D1 D2 (PAIR D1 D2 p1 p2) = p2.
trivial.
Save.

Definition Prod_map :  forall (D1 D2 D3 D4:cpo)(f:D1 -m>D3)(g:D2 -m>D4) , 
      Dprod D1 D2 -m> Dprod D3 D4.
intros; exists (fun p => pair (f (fst p)) (g (snd p))); red; intros.
split; simpl fst; simpl snd; apply fmonotonic.
apply (fmonotonic (Fst D1 D2) H).
apply (fmonotonic (Snd D1 D2) H).
Defined.


Lemma Prod_map_simpl : forall (D1 D2 D3 D4:cpo)(f:D1 -m>D3)(g:D2 -m>D4) (p:Dprod D1 D2),
      Prod_map f g p =  pair (f (fst p)) (g (snd p)).
trivial.
Save.

Definition PROD_map :  forall (D1 D2 D3 D4:cpo)(f:D1 -c>D3)(g:D2 -c>D4) , 
      Dprod D1 D2 -c> Dprod D3 D4.
intros; exists (Prod_map (fcontit f) (fcontit g)); red; intros; rewrite Prod_map_simpl.
split; simpl.
transitivity (f (lub (Fst D1 D2 @ h))); trivial.
rewrite (fcont_continuous f).
apply lub_le_compat; intros; intro; simpl; auto.
transitivity (g (lub (Snd D1 D2 @ h))); trivial.
rewrite (fcont_continuous g).
apply lub_le_compat; intros; intro; simpl; auto.
Defined.

Lemma PROD_map_simpl :  forall (D1 D2 D3 D4:cpo)(f:D1 -c>D3)(g:D2 -c>D4)(p:Dprod D1 D2), 
      PROD_map f g p = pair (f (fst p)) (g (snd p)).
trivial.
Save.

Definition curry (D1 D2 D3 : cpo) (f:Dprod D1 D2 -c> D3) : D1 -c> (D2 -c>D3) :=
fcont_COMP D1 (D2 -c>Dprod D1 D2) (D2 -c>D3) 
                          (fcont_COMP D2 (Dprod D1 D2) D3 f) (PAIR D1 D2).

Definition Curry : forall (D1 D2 D3 : cpo), (Dprod D1 D2 -c> D3) -m> D1 -c> (D2 -c>D3).
       intros; exists (curry (D1:=D1)(D2:=D2)(D3:=D3)); red; intros; auto.
Defined.

Lemma Curry_simpl : forall (D1 D2 D3 : cpo) (f:Dprod D1 D2 -c> D3) (x:D1) (y:D2), 
       Curry D1 D2 D3 f x y = f (x,y).
trivial.
Save.

Definition CURRY : forall (D1 D2 D3 : cpo), (Dprod D1 D2 -c> D3) -c> D1 -c> (D2 -c>D3).
       intros; exists (Curry D1 D2 D3); red; intros; auto.
Defined.

Lemma CURRY_simpl : forall (D1 D2 D3 : cpo) (f:Dprod D1 D2 -c> D3), 
       CURRY D1 D2 D3 f = Curry D1 D2 D3 f.
trivial.
Save.

Definition uncurry (D1 D2 D3 : cpo) (f:D1 -c> (D2 -c>D3)) : Dprod D1 D2 -c> D3
      :=  (f @2_ (FST D1 D2)) (SND D1 D2).

Definition Uncurry : forall (D1 D2 D3 : cpo), (D1 -c> (D2 -c>D3)) -m> Dprod D1 D2 -c> D3.
       intros; exists (uncurry (D1:=D1)(D2:=D2)(D3:=D3)).
red; intros.
apply fcont_le_intro; intro z; unfold uncurry.
repeat (rewrite fcont_comp2_simpl); auto.
apply (H (FST D1 D2 z) (SND D1 D2 z)).
Defined.

Lemma Uncurry_simpl : forall (D1 D2 D3 : cpo) (f:D1 -c> (D2 -c>D3)) (p:Dprod D1 D2), 
       Uncurry D1 D2 D3 f p = f (fst p) (snd p).
trivial.
Save.

Definition UNCURRY : forall (D1 D2 D3 : cpo), (D1 -c> (D2 -c>D3)) -c> Dprod D1 D2 -c> D3.
       intros; exists (Uncurry D1 D2 D3); red; intros; auto.
Defined.

Lemma UNCURRY_simpl : forall (D1 D2 D3 : cpo)  (f:D1 -c> (D2 -c>D3)),
       UNCURRY D1 D2 D3 f = Uncurry D1 D2 D3 f.
trivial.
Save.

(** ** Indexed product of cpo's *)

Definition Oprodi (I:Type)(O:I->ord) : ord.
intros; exists (forall i:I, O i) (fun p1 p2:forall i:I, O i => forall i:I, p1 i <= p2 i); intros; auto.
transitivity (y i); trivial.
Defined.

Lemma Oprodi_eq_intro : forall (I:Type)(O:I->ord) (p q : Oprodi O), (forall i, p i == q i) -> p==q.
intros; apply Ole_antisym; intro i; auto.
Save.

Lemma Oprodi_eq_elim : forall (I:Type)(O:I->ord) (p q : Oprodi O), p==q -> forall i, p i == q i.
intros; apply Ole_antisym; case H; auto.
Save.

Definition Proj (I:Type)(O:I->ord) (i:I) : Oprodi O -m> O i.
intros; exists (fun x: Oprodi O=> x i); red; intuition.
Defined.

Lemma Proj_simpl : forall  (I:Type)(O:I->ord) (i:I) (x:Oprodi O),
            Proj O i x = x i.
trivial.
Save.

Definition Dprodi (I:Type)(D:I->cpo) : cpo.
intros; exists (Oprodi D) (fun i=>(0:D i)) (fun (f : nat -m> Oprodi D) (i:I) => lub (Proj D i @ f));
intros; simpl; intros; auto.
apply le_lub with (f:= Proj (fun x : I => D x) i @ f) (n:=n).
apply lub_le; simpl; intros.
apply (H n i).
Defined.

Lemma Dprodi_lub_simpl : forall (I:Type)(Di:I->cpo)(h:nat-m>Dprodi Di)(i:I),
            lub h i = lub (c:=Di i) (Proj Di i @ h).
trivial.
Save.

Lemma Dprodi_continuous : forall `{c:cpo D}(I:Type)(Di:I->cpo)
    (f:D -m> Dprodi Di), (forall i, continuous (Proj Di i @ f)) -> 
    continuous f.
red; intros; intro i.
transitivity (lub (c:=Di i) ((Proj Di i @ f) @ h)); auto.
exact (H i h).
Save.

Definition Dprodi_lift : forall (I J:Type)(Di:I->cpo)(f:J->I),
             Dprodi Di -m> Dprodi (fun j => Di (f j)).
intros; exists (fun (p: Dprodi Di) j => p (f j)); red; auto.
Defined.

Lemma Dprodi_lift_simpl : forall (I J:Type)(Di:I->cpo)(f:J->I)(p:Dprodi Di),
             Dprodi_lift Di f p = fun j => p (f j).
trivial.
Save.

Lemma Dprodi_lift_cont : forall (I J:Type)(Di:I->cpo)(f:J->I),
             continuous (Dprodi_lift Di f).
intros; apply Dprodi_continuous; red; simpl; intros; auto.
Save.

Definition DLIFTi (I J:Type)(Di:I->cpo)(f:J->I) : Dprodi Di -c> Dprodi (fun j => Di (f j)) 
             := mk_fconti (Dprodi_lift_cont (Di:=Di) f).

Definition Dmapi : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Di i -m> Dj i), 
            Dprodi Di -m> Dprodi Dj.
intros; exists (fun p i => f i (p i)); red; auto.
Defined.

Lemma Dmapi_simpl : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Di i -m> Dj i) (p:Dprodi Di) (i:I),
Dmapi f p i = f i (p i).
trivial.
Save.

Lemma DMAPi : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Di i -c> Dj i), 
            Dprodi Di -c> Dprodi Dj.
intros; exists (Dmapi (fun i => fcontit (f i))).
red; intros; intro i; rewrite Dmapi_simpl.
repeat (rewrite Dprodi_lub_simpl).
transitivity (lub (c:=Dj i) (Fcontit (Di i) (Dj i) (f i) @ (Proj (fun x : I => Di x) i @ h))); auto.
Defined.

Lemma DMAPi_simpl : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Di i -c> Dj i) (p:Dprodi Di) (i:I),
DMAPi f p i = f i (p i).
trivial.
Save.

Lemma Proj_cont : forall (I:Type)(Di:I->cpo) (i:I), 
                    continuous (D1:=Dprodi Di) (D2:=Di i) (Proj Di i).
red; intros; simpl; trivial.
Save.

Definition PROJ (I:Type)(Di:I->cpo) (i:I) : Dprodi Di -c> Di i := 
      mk_fconti (Proj_cont (Di:=Di) i).

Lemma PROJ_simpl : forall (I:Type)(Di:I->cpo) (i:I)(d:Dprodi Di),
               PROJ Di i d = d i.
trivial.
Save.

(** *** Particular cases with one or two elements *)

Section Product2.

Definition I2 := bool.
Variable DI2 : bool -> cpo.

Definition DP1 := DI2 true.
Definition DP2 := DI2 false.

Definition PI1 : Dprodi DI2 -c> DP1 := PROJ DI2 true.
Definition pi1 (d:Dprodi DI2) := PI1 d.

Definition PI2 : Dprodi DI2 -c> DP2 := PROJ DI2 false.
Definition pi2 (d:Dprodi DI2) := PI2 d.

Definition pair2 (d1:DP1) (d2:DP2) : Dprodi DI2 := bool_rect DI2 d1 d2.

Lemma pair2_le_compat : forall (d1 d'1:DP1) (d2 d'2:DP2), d1 <= d'1 -> d2 <= d'2 
            -> pair2 d1 d2 <= pair2 d'1 d'2.
intros; intro b; case b; simpl; auto.
Save.

Definition Pair2 : DP1 -m> DP2 -m> Dprodi DI2 := le_compat2_mon pair2_le_compat.

Definition PAIR2 : DP1 -c> DP2 -c> Dprodi DI2.
apply continuous2_cont with (D1:=DP1) (D2:=DP2) (D3:=Dprodi DI2) (f:=Pair2).
red; intros; intro b.
case b; simpl; apply lub_le_compat; auto.
Defined.

Lemma PAIR2_simpl : forall (d1:DP1) (d2:DP2), PAIR2 d1 d2 = Pair2 d1 d2.
trivial.
Save.

Lemma Pair2_simpl : forall (d1:DP1) (d2:DP2), Pair2 d1 d2 = pair2 d1 d2.
trivial.
Save.

Lemma pi1_simpl : forall  (d1: DP1) (d2:DP2), pi1 (pair2 d1 d2) = d1.
trivial.
Save.

Lemma pi2_simpl : forall  (d1: DP1) (d2:DP2), pi2 (pair2 d1 d2) = d2.
trivial.
Save.

Definition DI2_map (f1 : DP1 -c> DP1) (f2:DP2 -c> DP2) 
               : Dprodi DI2 -c> Dprodi DI2 :=
                 DMAPi (bool_rect (fun b:bool => DI2 b -c>DI2 b) f1 f2).

Lemma Dl2_map_eq : forall (f1 : DP1 -c> DP1) (f2:DP2 -c> DP2) (d:Dprodi DI2),
               DI2_map f1 f2 d == pair2 (f1 (pi1 d)) (f2 (pi2 d)).
intros; simpl; apply Oprodi_eq_intro; intro b; case b; trivial.
Save.
End Product2.
Hint Resolve Dl2_map_eq.

Section Product1.
Definition I1 := unit.
Variable D : cpo.

Definition DI1 (_:unit) := D.
Definition PI : Dprodi DI1 -c> D := PROJ DI1 tt.
Definition pi (d:Dprodi DI1) := PI d.

Definition pair1 (d:D) : Dprodi DI1 := unit_rect DI1 d.

Definition pair1_simpl : forall (d:D) (x:unit), pair1 d x = d.
destruct x; trivial.
Defined.

Definition Pair1 : D -m> Dprodi DI1.
exists pair1; red; intros; intro d.
repeat (rewrite pair1_simpl);trivial.
Defined.


Lemma Pair1_simpl : forall (d:D), Pair1 d = pair1 d.
trivial.
Save.

Definition PAIR1 : D -c> Dprodi DI1.
exists Pair1; red; intros; repeat (rewrite Pair1_simpl).
intro d; rewrite pair1_simpl.
rewrite (Dprodi_lub_simpl (Di:=DI1)).
apply lub_le_compat; intros.
intro x; simpl; rewrite pair1_simpl; auto.
Defined.

Lemma pi_simpl : forall  (d:D), pi (pair1 d) = d.
trivial.
Save.

Definition DI1_map (f : D -c> D) 
               : Dprodi DI1 -c> Dprodi DI1 :=
                 DMAPi (fun t:unit => f).

Lemma DI1_map_eq : forall (f : D -c> D) (d:Dprodi DI1),
               DI1_map f d == pair1 (f (pi d)).
intros; simpl; apply Oprodi_eq_intro; intro b; case b; trivial.
Save.
End Product1.

Hint Resolve DI1_map_eq.
*)

(** ** Fixpoints *)

Fixpoint iter_ {D} {o} `{c: @cpo D o} (f : D -m> D) n {struct n} : D 
    := match n with O => 0 | S m => f (iter_ f m) end.

Lemma iter_incr : forall `{c: cpo D} (f : D -m> D) n, iter_ f n <= f (iter_ f n).
induction n; simpl; auto.
Save.
Hint Resolve @iter_incr.

Instance iter_mon : forall `{c: cpo D} (f : D -m> D), monotonic (iter_ f).
red; intros.
induction H; simpl; auto.
transitivity (iter_ f m); auto.
Save.

Definition iter `{c: cpo D} (f : D -m> D) : nat -m> D := mon (iter_ f).

Definition fixp `{c: cpo D} (f : D -m> D) : D := mlub (iter_ f).

Lemma fixp_le : forall `{c: cpo D} (f : D -m> D), fixp f <= f (fixp f).
intros; unfold fixp.
transitivity (lub (f @ (iter f))); auto.
apply lub_le_compat; intro n; simpl.
apply iter_incr.
Save.
Hint Resolve @fixp_le.

Lemma fixp_eq : forall `{c: cpo D} (f : D -m> D) {mf:continuous f}, 
      fixp f == f (fixp f).
intros; apply Ole_antisym; auto.
unfold fixp.
transitivity (lub (f@ (iter f))); auto.
rewrite (mlub_lift_left (mon (iter_ f)) (S O)); auto.
Save.

Lemma fixp_inv : forall `{c: cpo D} (f : D -m> D) g, f g <= g -> fixp f <= g.
unfold fixp; intros.
apply lub_le.
induction n; intros; simpl; auto.
simpl; transitivity (f g); auto.
Save.



Definition fixp_cte : forall `{c:cpo D} (d:D), fixp (mon (cte D d)) == d.
intros.
apply fixp_eq with (f:=mon (cte D d)); red; intros; simpl; auto.
apply (le_mlub (mon (cte D d) @ h) O).
Save.
Hint Resolve @fixp_cte.


Lemma fixp_le_compat : forall `{c:cpo D} (f g : D -m> D), 
      f <= g -> fixp f <= fixp g.
intros; unfold fixp.
apply mlub_le_compat.
intro n; induction n; simpl; auto.
transitivity (g (iter_ (D:=D) f n)); auto.
Save.
Hint Resolve @fixp_le_compat.

Instance fixp_monotonic `{c:cpo D} : monotonic fixp.
red; auto.
Save.

Add Parametric Morphism `{c:cpo D} : (fixp (c:=c))
    with signature Oeq ==> Oeq as fixp_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve @fixp_eq_compat.

Definition Fixp D `{c:cpo D} : (D -m> D) -m> D := mon fixp.

Lemma Fixp_simpl : forall `{c:cpo D} (f:D-m>D), Fixp D f = fixp f.
trivial.
Save.

Instance iter_monotonic `{c:cpo D} : monotonic iter.
red; intros f g H.
intro n; induction n; simpl; intros; auto.
transitivity (g (iter_ f n)); auto.
Save.

Definition Iter D `{c:cpo D} : (D -m> D) -m> (nat -m> D) := mon iter.

Lemma IterS_simpl : forall `{c:cpo D} f n, Iter D f (S n) = f (Iter D f n).
trivial.
Save.

Lemma iterO_simpl : forall `{c:cpo D} (f: D-m> D), iter f O = (0:D).
trivial.
Save.

Lemma iterS_simpl : forall `{c:cpo D} f n, iter f (S n) = f (iter f n).
trivial.
Save.

Lemma iter_continuous : forall `{c:cpo D} (h : nat -m> (D -m> D)),
       (forall n, continuous (h n)) -> iter (lub h) <= lub (mon iter @ h).
red; intros; intro k.
induction k.
rewrite iterO_simpl; auto.
rewrite iterS_simpl.
transitivity ((lub h) ((lub (mon iter @ h)) k)); auto.
transitivity ((lub h) (lub (mshift (mon iter @ h) k))); auto.
transitivity (lub ((lub h) @ (mshift (mon iter @ h) k))).
apply lub_continuous; trivial.
pose (hh:=fun n m: nat => h n (iter (h m) k)).
assert (monotonic2 hh).
unfold hh; red; intros n1 n2 m1 m2 H1 H2.
apply (fmonotonic2 h); trivial. 
apply iter_monotonic; auto.
transitivity (lub (lub (mon2 hh))).
apply lub_le_compat; intro n; unfold hh; simpl; auto.
transitivity (lub (diag (mon2 hh))); auto.
transitivity (lub (mshift (mon iter @ h) (S k))); auto.
apply lub_le_compat; intro n; simpl; auto.
Save.

Hint Resolve @iter_continuous.

Lemma iter_continuous_eq : forall `{c:cpo D} (h : nat -m> (D -m> D)),
    (forall n, continuous (h n)) -> iter (lub h) == lub (mon iter @ h).
intros; apply Ole_antisym; auto.
exact (lub_comp_le (mon iter) h).
Save.


Lemma fixp_continuous : forall `{c:cpo D} (h : nat -m> (D -m> D)), 
       (forall n, continuous (h n)) -> fixp (lub h) <= lub (mon fixp @ h).
intros; unfold fixp.
transitivity (lub (lub (mon iter @ h))); auto.
apply lub_le_compat; auto.
exact (iter_continuous h H).
transitivity (lub (lub (mshift (mon iter @ h)))); auto.
apply lub_le_compat; intro n; simpl; auto.
Save.
Hint Resolve @fixp_continuous.

Lemma fixp_continuous_eq : forall `{c:cpo D} (h : nat -m> (D -m> D)), 
       (forall n, continuous (h n)) -> fixp (lub h) == lub (mon fixp @ h).
intros; apply Ole_antisym; auto.
exact (lub_comp_le (mon fixp) h).
Save.

Definition Fixp_cont D `{c:cpo D} : (D -c> D) -m> D := Fixp D @ (Fcontm D D).

Lemma Fixp_cont_simpl : forall `{c:cpo D} (f:D -c> D), Fixp_cont D f = fixp (fcontm f).
trivial.
Save.


Instance Fixp_cont_continuous :  forall D `{c:cpo D}, continuous (Fixp_cont D).
red; intros.
rewrite Fixp_cont_simpl.
transitivity (fixp (lub (Fcontm D D@h))); auto.
transitivity  (lub (Fixp D @ (Fcontm D D@h))); auto.
apply fixp_continuous; intros.
change (continuous (D1:=D) (D2:=D) (fcontm (h n))); auto.
apply lub_le_compat; intro n; auto.
Save.

Definition FIXP D `{c:cpo D} : (D -c> D) -c> D := cont (Fixp_cont D).

Lemma FIXP_simpl : forall `{c:cpo D} (f:D -c> D), FIXP D f = Fixp D (fcontm f).
trivial.
Save.

Lemma FIXP_le_compat : forall `{c:cpo D} (f g : D -c> D),
            f <= g -> FIXP D f <= FIXP D g.
intros; repeat (rewrite FIXP_simpl); repeat (rewrite Fixp_simpl).
apply fixp_le_compat; auto.
Save.
Hint Resolve @FIXP_le_compat.

Lemma FIXP_eq_compat : forall `{c:cpo D} (f g : D -c> D),
            f == g -> FIXP D f == FIXP D g.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve @FIXP_eq_compat.

Lemma FIXP_eq : forall `{c:cpo D} (f:D -c> D), FIXP D f == f (FIXP D f).
intros; rewrite FIXP_simpl; rewrite Fixp_simpl.
apply (fixp_eq (fcontm f)).
Save.
Hint Resolve @FIXP_eq.

Lemma FIXP_inv : forall `{c:cpo D} (f:D -c> D) (g : D), f g <= g -> FIXP D f <= g.
intros; rewrite FIXP_simpl; rewrite Fixp_simpl; apply fixp_inv; auto.
Save.

(** *** Iteration of functional *)
Lemma FIXP_comp_com : forall `{c:cpo D} (f g:D-c>D),
       g @_ f <= f @_ g-> FIXP D g <= f (FIXP D g).
intros; apply FIXP_inv.
transitivity (f (g (FIXP D g))).
apply (fcont_le_elim _ _ H (FIXP D g)).
apply (fcont_le f).
rewrite (FIXP_eq g) at 2; trivial.
Save.

Lemma FIXP_comp : forall `{c:cpo D} (f g:D-c>D),
       g @_ f <= f @_ g -> f (FIXP D g) <= FIXP D g -> FIXP D (f @_ g) == FIXP D g.
intros; apply Ole_antisym.
(* fix f @_ g <= fix g *)
apply FIXP_inv.
rewrite fcont_comp_simpl.
transitivity (f (FIXP D g)); auto.
(* fix g <= fix f @_ g *)
apply FIXP_inv.
assert (g (f (FIXP D (f @_ g))) <= f (g (FIXP D (f @_ g)))).
apply (H (FIXP D (f @_ g))).
rewrite (FIXP_eq (f@_g)) at 2.
rewrite <- H1.
apply fcont_le.
apply FIXP_inv.
rewrite fcont_comp_simpl.
apply fcont_le.
rewrite H1; auto.
rewrite (FIXP_eq (f@_g)) at 2; auto.
Save.

Fixpoint fcont_compn {D} {o} `{c:@cpo D o}(f:D -c> D) (n:nat) {struct n} : D -c> D := 
             match n with O => f | S p => fcont_compn f p @_ f end.

Lemma fcont_compn_Sn_simpl : 
     forall `{c:cpo D}(f:D -c> D) (n:nat), fcont_compn f (S n) = fcont_compn f n @_ f.
trivial.
Save.

Lemma fcont_compn_com : forall `{c:cpo D}(f:D-c>D) (n:nat), 
            f @_ (fcont_compn f n) <= fcont_compn f n @_ f.
induction n; auto.
rewrite fcont_compn_Sn_simpl.
transitivity ((f @_ fcont_compn (D:=D) f n) @_ f); auto.
intro k; simpl; auto.
Save.

Lemma FIXP_compn : 
     forall `{c:cpo D} (f:D-c>D) (n:nat), FIXP D (fcont_compn f n) == FIXP D f.
induction n; auto.
simpl fcont_compn.
apply FIXP_comp.
apply fcont_compn_com.
transitivity (fcont_compn (D:=D) f n (FIXP D (fcont_compn (D:=D) f n))); auto.
transitivity (FIXP D (fcont_compn (D:=D) f n)); auto.
Save.

Lemma fixp_double : forall `{c:cpo D} (f:D-c>D), FIXP D (f @_ f) == FIXP D f.
intros; exact (FIXP_compn f (S O)).
Save.

(*
Lemma FIXP_proj : forall (I:Type)(DI: I -> cpo) (F:Dprodi DI -c> Dprodi DI) (i:I) (fi : DI i -c> DI i), 
                              (forall X : Dprodi DI, F X i == fi (X i)) -> FIXP (Dprodi DI) F i == FIXP (DI i) fi.
intros; apply Ole_antisym.
(* fix F i <= fix fi *)
rewrite FIXP_simpl.
rewrite Fixp_simpl.
unfold fixp.
rewrite Dprodi_lub_simpl.
apply lub_le .
induction n; auto.
rewrite fmon_comp_simpl.
rewrite (iterS_simpl (fcontit F)).
rewrite (Proj_simpl (O:=DI) i).
transitivity (fi (iter (D:=Dprodi DI) (fcontit F) n i)).
case (H (iter (D:=Dprodi DI) (fcontit F) n)); trivial.
transitivity (fi (FIXP (DI i) fi)); auto.
(* fix fi <= fix F i *)
apply FIXP_inv.
case (H (FIXP (Dprodi DI) F)); intros.
transitivity (1:=H1).
case (FIXP_eq F); auto.
Save.
*)

(** *** Induction principle *)
Definition admissible `{c:cpo D}(P:D->Type) := 
          forall f : nat -m> D, (forall n, P (f n)) -> P (lub f).

Lemma fixp_ind : forall  `{c:cpo D}(F:D -m> D)(P:D->Type),
       admissible P -> P 0 -> (forall x, P x -> P (F x)) -> P (fixp F).
intros; unfold fixp.
apply X; intros.
induction n; simpl; auto.
Defined.

Definition admissible2 `{c1:cpo D1}`{c2:cpo D2}(R:D1 -> D2 -> Type) := 
    forall (f : nat -m> D1) (g:nat -m> D2), (forall n, R (f n) (g n)) -> R (lub f) (lub g).

Lemma fixp_ind_rel : forall  `{c1:cpo D1}`{c2:cpo D2}(F:D1 -m> D1) (G:D2-m> D2)
       (R:D1 -> D2 -> Type),
       admissible2 R -> R 0 0 -> (forall x y, R x y -> R (F x) (G y)) -> R (fixp F) (fixp G).
intros; unfold fixp.
apply X; intros.
induction n; simpl; auto.
Defined.

Lemma lub_le_fixp : forall `{c1:cpo D1}`{c2:cpo D2}  (f:D1-m>D2)  (F:D1 -m> D1)
                                         (s:nat-m> D2),
          s O <= f 0 -> (forall x n, s n <= f x -> s (S n) <= f (F x))
          -> lub s <= f (fixp F).
intros; apply lub_le; intro n.
transitivity (f (iter_ F n)); auto.
induction n; simpl; auto.
apply fmonotonic; auto.
unfold fixp; auto.
Save.

Lemma fixp_le_lub : forall `{c1:cpo D1}`{c2:cpo D2}  (f:D1-m>D2)  (F:D1 -m> D1)
                                         (s:nat-m> D2) {fc:continuous f},
          f 0 <= s O -> (forall x n, f x <= s n ->  f (F x) <= s (S n)) -> f (fixp F) <= lub s.
intros; unfold fixp; rewrite fc.
apply lub_le_compat; intro n.
induction n; simpl; auto.
Save.
  
(*
(** ** Directed complete partial orders without minimal element *)

Record dcpo : Type := mk_dcpo 
  {tdcpo:> ord; dlub: (nat -m> tdcpo) -> tdcpo;
   le_dlub : forall (f : nat -m> tdcpo) (n:nat), f n <= dlub f;
   dlub_le : forall (f : nat -m> tdcpo) (x:tdcpo), (forall n, f n <= x) -> dlub f <= x}.

Hint Resolve le_dlub dlub_le.

Lemma dlub_le_compat : forall (D:dcpo)(f1 f2 : nat -m> D), f1 <= f2 -> dlub f1 <= dlub f2.
intros; apply dlub_le; intros.
transitivity (f2 n); auto.
Save.
Hint Resolve dlub_le_compat.

Lemma dlub_eq_compat : forall (D:dcpo)(f1 f2 : nat -m> D), f1 == f2 -> dlub f1 == dlub f2.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve dlub_eq_compat.

Lemma dlub_lift_right : forall (D:dcpo) (f:nat-m>D) n, dlub f == dlub (mseq_lift_right f n).
intros; apply Ole_antisym; auto.
apply dlub_le_compat; intro.
unfold mseq_lift_right; simpl.
apply (fmonotonic f); auto with arith.
Save.
Hint Resolve dlub_lift_right.

Lemma dlub_cte : forall (D:dcpo) (c:D), dlub (mseq_cte c) == c.
intros; apply Ole_antisym; auto.
apply le_dlub with (f:=fmon_cte nat c) (n:=O); auto.
Save.


(** *** A cpo is a dcpo *)

Definition cpo_dcpo : cpo -> dcpo.
intro D; exists D (lub (c:=D)); auto.
Defined.

(** ** Setoid type *)

Record setoid : Type := mk_setoid
  {tset:>Type; Seq:tset->tset->Prop; Seq_refl : forall x :tset, Seq x x; 
   Seq_sym : forall x y:tset, Seq x y -> Seq y x;
   Seq_trans : forall x y z:tset, Seq x y -> Seq y z -> Seq x z}.

Hint Resolve Seq_refl.
Hint Immediate Seq_sym.

(** *** A setoid is an ordered set *)

Definition setoid_ord : setoid -> ord.
intro S; exists S (Seq (s:=S)); auto.
intros; apply Seq_trans with y; trivial.
Defined.

Definition ord_setoid : ord -> setoid.
intro O; exists O (Oeq (O:=O)); auto.
intros; apply Oeq_trans with y; trivial.
Defined.

(** *** A Type is an ordered set and a setoid with Leibniz equality *)

Definition type_ord (X:Type) : ord.
intro X; exists X (fun x y:X => x = y); intros; auto.
transitivity y; trivial.
Defined.

Definition type_setoid (X:Type) : setoid.
intro X; exists X (fun x y:X => x = y); intros; auto.
transitivity y; trivial.
Defined.

(** *** A setoid is a dcpo *)

Definition lub_eq (S:setoid) (f:nat-m>setoid_ord S) := f O.

Lemma le_lub_eq  : forall (S:setoid) (f:nat-m>setoid_ord S) (n:nat), f n <= lub_eq f.
intros; unfold lub_eq; simpl.
apply Seq_sym; apply (fmonotonic f); simpl; auto with arith.
Save.

Lemma lub_eq_le  : forall (S:setoid) (f:nat-m>setoid_ord S)(x:setoid_ord S), 
                (forall (n:nat), f n <= x) -> lub_eq f <= x.
intros; unfold lub_eq; simpl; intros.
exact (H O).
Save.

Hint Resolve le_lub_eq lub_eq_le.

Definition setoid_dcpo : setoid -> dcpo.
intro S; exists (setoid_ord S) (lub_eq (S:=S)); intros; auto.
Defined.

(** Cpo of arrays seen as functions from nat to D with a bound n *)

Definition lek {O} {o:ord O} (k:nat) (f g : nat -> O) := forall n, n < k -> f n <= g n.
Hint Unfold lek.

Lemma lek_refl : forall {O} {o:ord O} k (f:nat -> O), lek k f f.
auto.
Save.
Hint Resolve lek_refl.

Lemma lek_trans : forall {O} {o:ord O} (k:nat) (f g h: nat -> O), lek k f g -> lek k g h -> lek k f h.
red; intros.
transitivity (g n); auto.
Save.

Definition natk_ord : ord -> nat -> ord.
intros O k; exists (nat->O) (lek (O:=O) k); auto.
exact (lek_trans (O:=O) (k:=k)).
Defined.

Definition norm {O} {o:ord O} (x:O) (k:nat) (f: natk_ord O k) : natk_ord O k := 
        fun n => if le_lt_dec k n then x else f n.

Lemma norm_simpl_lt : forall {O} {o:ord O} (x:O) (k:nat) (f: natk_ord O k) (n:nat),
       n < k -> norm x f n = f n.
unfold norm; intros; case (le_lt_dec k n); auto.
intros; casetype False; omega.
Save.

Lemma norm_simpl_le : forall {O} {o:ord O} (x:O) (k:nat) (f: natk_ord O k) (n:nat),
       (k <= n)%nat -> norm x f n = x.
unfold norm; intros; case (le_lt_dec k n); auto.
intros; casetype False; omega.
Save. 

Definition natk_mon_shift : forall (Oa Ob : ord)(x:Ob) (k:nat),
         (Oa -m> natk_ord Ob k) -> natk_ord (Oa -m> Ob) k.
intros Oa Ob x k f n; exists (fun (y:Oa) => norm x (f y) n).
red; intros.
case (le_lt_dec k n); intro.
repeat rewrite norm_simpl_le; auto.
repeat rewrite norm_simpl_lt; auto.
apply (fmonotonic f H n); trivial.
Defined.

Lemma natk_mon_shift_simpl 
     : forall (Oa Ob : ord)(x:Ob) (k:nat)(f:Oa -m> natk_ord Ob k) (n:nat) (y:Oa),
     natk_mon_shift x f n y = norm x (f y) n.
trivial.
Save.

Definition natk_shift_mon : forall (Oa Ob : ord)(k:nat),
         (natk_ord (Oa -m> Ob) k) -> Oa -m> natk_ord Ob k.
intros Oa Ob k f; exists (fun (y:Oa) n => f n y). 
red; intros; intros n H1.
apply (fmonotonic (f n)); auto.
Defined.

Lemma natk_shift_mon_simpl 
     : forall (Oa Ob : ord)(k:nat)(f:natk_ord (Oa -m> Ob) k) (x:Oa)(n:nat),
     natk_shift_mon f x n = f n x.
trivial.
Save.

Definition natk0 `{c:cpo D} (k:nat) : natk_ord D k := fun n : nat => (0:D).

Definition natklub `{c:cpo D} (k:nat) (h:nat-m>natk_ord D k) : natk_ord D k := 
                            fun n => lub (natk_mon_shift (0:D) h n).

Lemma natklub_less : forall `{c:cpo D} (k:nat) (h:nat-m>natk_ord D k) (n:nat),
                       h n <= natklub h.
simpl; red; unfold natklub; intros.
transitivity (natk_mon_shift (Oa:=nat) (Ob:=D) 0 (k:=k) h n0 n); auto.
rewrite natk_mon_shift_simpl.
rewrite norm_simpl_lt; auto.
Save.

Lemma natklub_least : forall `{c:cpo D} (k:nat) (h:nat-m>natk_ord D k) (p:natk_ord D k),
                       (forall n:nat, h n <= p) -> natklub h <= p.
simpl; red; unfold natklub; intros.
apply lub_le; intros.
rewrite natk_mon_shift_simpl.
rewrite norm_simpl_lt; auto.
apply (H n0 n H0).
Save.

Definition Dnatk : forall `{c:cpo D} (k:nat), cpo.
intros; exists (natk_ord D k) (natk0 D k) (natklub (D:=D) (k:=k)).
unfold natk0; auto.
exact (natklub_less (D:=D) (k:=k)).
exact (natklub_least (D:=D) (k:=k)).
Defined.

Notation "k --> D" := (Dnatk D k) (at level 30, right associativity) : O_scope.

Definition natk_shift_cont : forall (D1 D2 : cpo)(k:nat),
         (k --> (D1 -c>D2)) -> D1 -c> (k --> D2).
intros D1 D2 k f; exists (natk_shift_mon (k:=k) (fun n => fcontit (f n))).
red; intros; intros n H.
rewrite (natk_shift_mon_simpl (Oa:=D1) (Ob:=D2) (k:=k)).
simpl; unfold natklub.
transitivity (lub (fcontit (f n) @ h)); auto.
apply lub_le_compat; intro m.
rewrite fmon_comp_simpl.
rewrite natk_mon_shift_simpl.
rewrite norm_simpl_lt; trivial.
Defined.

Lemma natk_shift_cont_simpl 
     : forall (D1 D2:cpo)(k:nat)(f:k --> (D1 -c>D2)) (n:nat) (x:D1),
     natk_shift_cont f x n = f n x.
trivial.
Save.

Lemma natklub_simpl : forall `{c:cpo D} (k:nat) (h:nat -m> k --> D) (n:nat), 
                    lub h n = lub (natk_mon_shift (0:D) h n).
trivial.
Save.
*)

Ltac continuity cont Cont Hcont:= 
  match goal with 
 | |- (Ole ?x1 (lub (mon (fun (n:nat) => cont (@?g n))))) => 
      let f := fresh "f" in (
           pose (f:=g); assert (monotonic f) ;
                               [auto |  (transitivity (lub (Cont@(mon f))); [rewrite <- Hcont | auto])]
           )
end.

Ltac gen_monotonic := 
match goal with |- context [(@mon _ _ _ _ ?f ?mf)] => generalize (mf:monotonic f)
end.

Ltac gen_monotonic1 f := 
match goal with |- context [(@mon _ _ _ _ f ?mf)] => generalize (mf:monotonic f)
end.

(** *** Function for conditionnal choice defined as a morphism *)

Definition fif {A} (b:bool) : A -> A -> A := fun e1 e2 => if b then e1 else e2.

Instance fif_mon2 `{o:ord A} (b:bool) : monotonic2 (@fif _ b).
red; intros; case b; auto.
Save.

Definition Fif `{o:ord A} (b:bool) : A -m> A -m> A := mon2 (@fif _ b).

Lemma Fif_simpl : forall `{o:ord A} (b:bool) (x y:A), Fif b x y = fif b x y.
trivial.
Save.

Lemma Fif_continuous_right `{c:cpo A} (b:bool) (e:A) : continuous (Fif b e).
red; intros; simpl.
case b; simpl @fif.
rewrite <- (lub_cte e) at 1; auto.
apply mlub_le_compat; auto. 
apply lub_le_compat; intro n; auto.
Save.

Lemma  Fif_continuous_left `{c:cpo A} (b:bool) : continuous (Fif (A:=A) b).
red; intros h e.
transitivity (Fif (negb b) e (lub h)).
destruct b; trivial.
rewrite (Fif_continuous_right (negb b) e h).
rewrite fmon_lub_simpl.
apply lub_le_compat; intro n; case b; auto.
Save.
Hint Resolve @Fif_continuous_right @Fif_continuous_left.

Lemma fif_continuous_left `{c:cpo A} (b:bool) (f:nat-m> A):
    fif b (lub f) == lub (Fif b@f).
intros; rewrite <- lub_comp_eq; auto.
Save.

Lemma fif_continuous_left2 :
forall (A : Type) (o : ord A) (c : cpo A) (b : bool) (f : nat -m> A) (g:A),
fif b (lub f) g == lub (Fif b @ f) g.
intros; apply fif_continuous_left.
Save.


Lemma fif_continuous_right `{c:cpo A} (b:bool) e (f:nat-m> A):
    fif b e (lub f) == lub (Fif b e@f).
intros; rewrite <- lub_comp_eq; auto.
Save.

Hint Resolve @fif_continuous_right @fif_continuous_left @fif_continuous_left2.

Instance Fif_continuous2 `{c:cpo A} (b:bool) : continuous2 (Fif (A:=A) b).
apply continuous_continuous2; auto.
Save.

Lemma fif_continuous2 `{c:cpo A} (b:bool) (f g : nat-m> A):
      fif b (lub f) (lub g) == lub ((Fif b@2 f) g).
rewrite <- lub_cont2_app2_eq; auto.
Save.


Add Parametric Morphism `{o:ord A} (b:bool) : (@fif A b) 
with signature Ole ==> Ole ==> Ole
as fif_le_compat.
intros; apply fif_mon2; auto.
Save.

Add Parametric Morphism `{o:ord A} (b:bool) : (@fif A b) 
with signature Oeq ==> Oeq ==> Oeq
as fif_eq_compat.
intros; apply (monotonic2_stable2 (@fif A b)); auto.
Save.




