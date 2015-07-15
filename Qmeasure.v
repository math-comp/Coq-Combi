(** * Qmeasure.v: Definition of finite probabilities as measures with values in rational numbers *)

Add Rec LoadPath "ALEA/src" as ALEA.

Require Export Misc.
Require Export Ccpo.
Set Implicit Arguments.
Local Open Scope O_scope.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype rat 
               finfun ssrnum ssralg ssrint bigop.
Import GRing.
Local Open Scope ring_scope.

Instance ratO : ord rat := 
     { Oeq := fun n m : rat => n = m;
       Ole := fun n m : rat => (n <= m)%R}.
apply Build_Order.
red.
apply Num.Theory.lerr.
split.
move /andP => H; apply (Num.Theory.ler_asym (R:=rat_numDomainType)).
by [].
move => H; by rewrite H Num.Theory.lerr.
red; move => x y z; apply Num.Theory.ler_trans.
Defined.

(** Functions to be measured *)

Definition MF (A:Type) := A -> rat.

Instance MFO (A:Type) : ord (MF A) := ford A rat.

Canonical rat_lmodType : lmodType rat := Eval hnf in regular_lmodType rat_Ring.

(** Type of measures on [A] *)

Definition M A := MF A -m> rat.

Instance MO (A:Type) : ord (M A) := fmono (MF A) rat.

Instance app_mon (A:Type) (x:A) : monotonic (fun (f:MF A) => f x).
red; auto.
Save.
Hint Resolve app_mon.

(** Monadic operators on M A *)

Definition munit (A:Type) (x:A) : M A := mon (fun (f:MF A) => f x).

Definition mstar : forall (A B:Type), M A -> (A -> M B) -> M B.
intros A B a F; exists (fun f => a (fun x => F x f)).
red; intros.
apply (fmonotonic a); intro z; simpl.
apply (fmonotonic (F z)); trivial.
Defined.

Lemma star_simpl : forall (A B:Type) (a:M A) (F:A -> M B)(f:MF B),
        mstar a F f =  a (fun x => F x f).
trivial.
Save.

(** ** Properties of monadic operators *)
Lemma law1 : forall (A B:Type) (x:A) (F:A -> M B) (f:MF B), mstar (munit x) F f == F x f.
trivial.
Qed.

Lemma law2 :
 forall (A:Type) (a:M A) (f:MF A), mstar a (fun x:A => munit x) f == a (fun x:A => f x).
trivial.
Qed.

Lemma law3 :
 forall (A B C:Type) (a:M A) (F:A -> M B) (G:B -> M C)
   (f:MF C), mstar (mstar a F) G f == mstar a (fun x:A => mstar (F x) G) f.
trivial.
Qed.

(** ** Properties of distributions *)
(** *** Expected properties of measures *)

Definition stable_add (A:Type) (m:M A) : Prop :=
  forall f g:MF A, m (f \+ g) = (m f) + (m g).

Definition stable_sub (A:Type) (m:M A) : Prop :=
  forall f g:MF A, m (f \- g) = (m f) - (m g).

Definition stable_mull (A:Type) (m:M A) : Prop :=
  forall (k:rat) (f:MF A), m (k \*o f) = k * (m f).

Definition stable_opp (A:Type) (m:M A) : Prop :=
  forall (f:MF A), m (fun x => - (f x)) = - (m f).

(** Linearity on rational is deduced from stability with respect to substraction *)

Section StabilityProperties.

Variable A : Type.
Variable m : M A.
Hypothesis Mstable_sub : stable_sub m.

Lemma Mstable_eq : stable m.
apply monotonic_stable; trivial.
Save.
Hint Resolve Mstable_eq.

Lemma Mstable0 : m \0 = 0.
transitivity (m \0 - m \0).
transitivity (m (\0 \- \0)).
apply Mstable_eq; auto.
apply Mstable_sub.
rewrite (GRing.addrN (m \0)); trivial.
Save.
Hint Resolve Mstable0.

Lemma Mstable_opp : stable_opp m.
move => f; transitivity (m \0 - m f).
rewrite -Mstable_sub.
apply Mstable_eq; intro x.
rewrite /null_fun_head /= sub0r; auto.
rewrite Mstable0 /null_fun_head /= sub0r; auto.
Save.
Hint Resolve Mstable_opp.

Lemma Mstable_add : stable_add m.
move => f g; transitivity (m f - m (fun x => - g x)).
transitivity (m (f \- (fun x => - g x))).
apply Mstable_eq; intro x.
rewrite /= opprK; auto.
apply Mstable_sub.
rewrite Mstable_opp opprK; trivial.
Save.
Hint Resolve Mstable_add.

Lemma Mstable_addn (f : MF A) (n : nat) : m (fun x => f x *+ n) = (m f) *+ n.
move:n; elim => [|n].
rewrite mulr0n.
transitivity (m \0); auto.
move => IHn; rewrite mulrSr.
transitivity (m (fun x : A => f x *+ n) + m f).
rewrite -Mstable_add.
apply Mstable_eq; move => x /=; rewrite mulrSr //=.
by congr +%R.
Save.

Lemma Mstable_subn (f : MF A) (n : nat) : m (fun x => f x *- n) = (m f) *- n.
rewrite Mstable_opp.
by rewrite Mstable_addn.
Save.

Lemma Mstable_divn (f : MF A) (n : nat) : m (fun x => f x / n%:Q) = (m f) / (n%:Q).
case :n => [|n].
rewrite rat0 invr0 mulr0.
rewrite -{2}Mstable0.
apply Mstable_eq; move=> x /=.
apply mulr0.
have Hu:((n.+1)%:Q \in unit).
apply Num.Theory.unitf_gt0.
by rewrite ltr0z /=.
apply (@mulrI _ (n.+1)%:Q); trivial.
rewrite mulr_natl.
rewrite -Mstable_addn.
rewrite mulrC mulrVK; trivial.
apply Mstable_eq; move=> x /=.
rewrite -mulr_natr.
rewrite mulrVK; trivial.
Save.

Lemma Mstable_addi (f : MF A) (n : int) : m (fun x => f x *~ n) = (m f) *~ n.
move:n => [np|nn].
rewrite -pmulrn.
apply Mstable_addn.
rewrite NegzE -nmulrn.
apply Mstable_subn.
Save.

Lemma Mstable_muli (f : MF A) (n : int) : m (fun x => n%:Q * f x) = (n%:Q) * (m f).
rewrite mulrzl -Mstable_addi.
apply Mstable_eq; move=> x /=.
apply mulrzl.
Save.

Lemma Mstable_divi (f : MF A) (n : int) : m (fun x => f x / n%:Q) = (m f) / (n%:Q).
move:n => [np|nn].
rewrite -pmulrn.
apply Mstable_divn.
rewrite NegzE -nmulrn.
rewrite invrN mulrN.
rewrite -Mstable_divn.
rewrite -Mstable_opp.
apply Mstable_eq; move=> x /=.
by rewrite mulrN.
Save.

Lemma Mstable_mull : stable_mull m.
rewrite /stable_mull; move => n f.
rewrite -{2}(divq_num_den n).
rewrite -mulrA.
rewrite (mulrC _ (m f)).
rewrite -Mstable_divi.
rewrite -Mstable_muli.
apply Mstable_eq; move=> x /=.
by rewrite (mulrC (f x)) mulrA (divq_num_den n).
Save.

Lemma Mstable_linear : forall (p q : rat) (f g : MF A), 
    m ((p \*o f) \+ (q \*o g)) = p * (m f) + q * (m g).
by intros; rewrite Mstable_add !Mstable_mull.
Save.

End StabilityProperties.


Lemma unit_stable_eq : forall (A:Type) (x:A), stable (munit x).
auto.
Qed.

Lemma star_stable_eq : forall (A B:Type) (m:M A) (F:A -> M B), stable (mstar m F).
auto.
Qed.

Lemma unit_monotonic A (x:A) (f g : MF A):(f <= g)%O -> munit x f <= munit x g.
by rewrite /unit /=.
Qed.

Lemma star_monotonic A B (m:M A) (F:A -> M B) (f g : MF B) : (f <= g)%O -> mstar m F f <= mstar m F g.
move => H; rewrite /mstar /=.
apply (fmonotonic m); intro x.
by apply (fmonotonic (F x)).
Qed.

Lemma star_le_compat A B (m1 m2:M A) (F1 F2:A -> M B):
       (m1 <= m2)%O -> (F1 <= F2)%O -> (mstar m1 F1 <= mstar m2 F2)%O.
intros; intro f; repeat rewrite star_simpl.
transitivity (m1 (fun x : A => (F2 x) f)); auto.
apply (fmonotonic m1); intro x.
apply (H0 x f).
Save.
Hint Resolve star_le_compat.

(** *** Stability for substraction of unit and star *)
Lemma unit_stable_sub : forall (A:Type) (x:A), stable_sub (munit x).
red in |- *; intros.
unfold unit in |- *.
auto.
Qed.

Lemma star_stable_sub : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_sub m -> (forall a:A, stable_sub (F a)) -> stable_sub (mstar m F).
unfold stable_sub in |- *; intros.
unfold mstar in |- *; simpl.
transitivity (m (fun x:A => F x f - F x g)).
apply (Mstable_eq m); intro x; auto.
apply (H (fun x : A => (F x) f) (fun x : A => (F x) g)).
Save.


(** ** Definition of distribution
Finite distributions are monotonic measure functions such that
    - [ mu (f - g) = mu f - mu g]
    - [ mu 1 = 1]
*)

Record distr (A:Type) : Type := 
  {mu : M A;
   mu_stable_sub : stable_sub mu; 
   mu_prob : mu (fun x => 1%:Q) = 1}.

Hint Resolve mu_stable_sub mu_prob.

(** ** Properties of measures *)

Lemma mu_monotonic A (m: distr A) : monotonic (mu m).
apply fmonotonic; auto.
Save.
Hint Resolve mu_monotonic.
Implicit Arguments mu_monotonic [A].

Lemma mu_stable_eq A (m: distr A) : stable (mu m).
apply fstable; auto.
Save.
Hint Resolve mu_stable_eq.
Implicit Arguments mu_stable_eq [A].

Lemma mu_zero A (m: distr A) : mu m \0 = 0.
apply Mstable0; auto.
Save.
Hint Resolve mu_zero.

Lemma mu_zero_eq A (m: distr A) f : (forall x, f x = 0) -> mu m f = 0.
transitivity (mu m \0); auto.
apply Mstable_eq; intro x; auto.
Save.
Hint Immediate mu_zero_eq.

Lemma mu_one_eq A (m: distr A) f : (forall x, f x = 1) -> mu m f = 1.
transitivity (mu m (fun x => 1)); auto.
apply Mstable_eq; intro x; auto.
Save.
Hint Immediate mu_one_eq.

Lemma mu_stable_inv A (m: distr A) f : mu m (fun x => 1 - f x) = 1 - (mu m f).
transitivity (mu m (fun x => 1) - mu m f).
rewrite mu_stable_sub; trivial.
rewrite mu_prob; trivial.
Save.
Hint Resolve mu_stable_inv.

Lemma mu_stable_add A (m: distr A) f g: mu m (f \+ g) = mu m f + mu m g.
rewrite Mstable_add; auto.
Save.
Hint Resolve mu_stable_add.

Lemma mu_stable_mull A (m: distr A) q f : mu m (q \*o f) = q * mu m f.
rewrite Mstable_mull; auto.
Save.
Hint Resolve mu_stable_mull.

Lemma mu_add_zero A (m: distr A) f g : mu m f = 0 -> mu m g = 0 -> mu m (f \+ g) = 0.
intros Hf Hg; rewrite mu_stable_add Hf Hg; auto.
Save.
Hint Resolve mu_add_zero.

Lemma mu_non_neg A (m: distr A) f : (\0 <= f)%O -> 0 <= mu m f.
move => Hf; rewrite -(mu_zero m).
apply (fmonotonic (mu m)); auto.
Save.

Lemma mu_cte A (m: distr A) (c:rat) : mu m (fun x => c) = c.
intros.
transitivity (mu m (fun x => c * 1)).
apply (mu_stable_eq m); intro x; auto.
rewrite (mulr1 c); auto.
by rewrite mu_stable_mull mu_prob mulr1.
Save.
Hint Resolve mu_cte.

Lemma mu_stable_mulr A (m: distr A) (c:rat) f : mu m (c \o* f) = (mu m f) * c.
intros; rewrite mulrC -mu_stable_mull.
apply mu_stable_eq; intro x.
by rewrite /= mulrC /=.
Save.

Lemma mu_stable_inv_inv A (m: distr A) f : mu m f = 1 - mu m (fun x => 1 - f x).
rewrite -mu_stable_inv.
apply mu_stable_eq; intro x; rewrite opprB /=.
by rewrite addrCA subrr addr0.
Save.
Hint Resolve  mu_stable_inv_inv.

Instance Odistr (A:Type) : ord (distr A) := 
    {Ole := fun (f g : distr A) => (mu f <= mu g)%O;
     Oeq := fun (f g : distr A) => Oeq (mu f) (mu g)}.
split; intuition.
intros f g h; transitivity (mu g); auto.
Defined.


(** ** Monadic operators for distributions *)
Definition Munit : forall A:Type, A -> distr A.
intros A x.
exists (munit x).
apply unit_stable_sub.
rewrite /unit /=; auto.
Defined.

Definition Mlet : forall A B:Type, distr A -> (A -> distr B) -> distr B.
intros A B mA mB.
exists (mstar (mu mA) (fun x => (mu (mB x)))).
apply star_stable_sub; auto.
rewrite /mstar /=; apply mu_one_eq; auto.
Defined.

Lemma Munit_simpl : forall (A:Type) (q:A -> rat) x, mu (Munit x) q = q x.
trivial.
Save.

Lemma Munit_simpl_eq : forall (A:Type) (q:A -> rat) x, mu (Munit x) q == q x.
trivial.
Save.

Lemma Mlet_simpl : forall (A B:Type) (m:distr A) (M:A -> distr B) (f:B -> rat),
     mu (Mlet m M) f = mu m (fun x => (mu (M x) f)).
trivial.
Save.

Lemma Mlet_simpl_eq : forall (A B:Type) (m:distr A) (M:A -> distr B) (f:B -> rat),
     mu (Mlet m M) f == mu m (fun x => (mu (M x) f)).
trivial.
Save.


(** ** Operations on distributions *)


Lemma Munit_eq_compat : forall A (x y : A), x = y -> Munit x == Munit y.
intros; subst; auto.
Save.

Lemma Mlet_le_compat : forall (A B : Type) (m1 m2:distr A) (M1 M2 : A -> distr B), 
  (m1 <= m2 -> M1 <= M2 -> Mlet m1 M1 <= Mlet m2 M2)%O.
intros A B m1 m2 M1 M2 Hm HM f.
repeat rewrite Mlet_simpl.
transitivity (mu m2 (fun x : A => mu (M1 x) f)); auto.
apply (fmonotonic (mu m2)); intro; auto.
apply (HM x f).
Save.
Hint Resolve Mlet_le_compat.

Add Parametric Morphism (A B : Type) : (Mlet (A:=A) (B:=B))
  with signature Ole ==> Ole ==> Ole 
  as Mlet_le_morphism.
auto.
Save.

Add Parametric Morphism (A B : Type) : (Mlet (A:=A) (B:=B))
  with signature  Ole ==> (@pointwise_relation A (distr B) (@Ole _ _)) ==> Ole 
  as Mlet_le_pointwise_morphism.
auto.
Save.


Instance Mlet_mon2 : forall (A B : Type), monotonic2 (@Mlet A B).
red; auto.
Save.

Definition MLet (A B : Type) : distr A -m> (A -> distr B) -m> distr B
               := mon2 (@Mlet A B).

Lemma MLet_simpl0 : forall (A B:Type) (m:distr A) (M:A -> distr B),
     MLet A B m M = Mlet m M.
trivial.
Save.

Lemma MLet_simpl : forall (A B:Type) (m:distr A) (M:A -> distr B)(f:B -> rat),
     mu (MLet A B m M) f = mu m (fun x => mu (M x) f).
trivial.
Save.

Lemma Mlet_eq_compat : forall (A B : Type) (m1 m2:distr A) (M1 M2 : A -> distr B), 
  (m1 == m2 -> M1 == M2 -> Mlet m1 M1 == Mlet m2 M2)%type.
intros; apply (monotonic2_stable2 (@Mlet A B)); trivial.
Save.
Hint Resolve Mlet_eq_compat.

Add Parametric Morphism (A B : Type) : (Mlet (A:=A) (B:=B))
  with signature Oeq ==> Oeq ==> Oeq 
  as Mlet_eq_morphism.
auto.
Save.


Add Parametric Morphism (A B : Type) : (Mlet (A:=A) (B:=B))
  with signature  Oeq ==> (@pointwise_relation A (distr B) (@Oeq _ _)) ==> Oeq 
  as Mlet_Oeq_pointwise_morphism.
auto.
Save.


Lemma mu_le_compat : forall (A:Type) (m1 m2:distr A),
  (m1 <= m2 -> forall f g : A -> rat,  f <= g -> mu m1 f <= mu m2 g)%O.
intros; transitivity (mu m2 f); auto.
Save.

Lemma mu_eq_compat : forall (A:Type) (m1 m2:distr A),
  (m1 == m2 -> forall f g : A -> rat,  f == g -> mu m1 f = mu m2 g)%type.
intros; change (mu m1 f == mu m2 g)%type; transitivity (mu m2 f); auto.
Save.
Hint Immediate mu_le_compat mu_eq_compat.

Add Parametric Morphism (A : Type) : (mu (A:=A))
  with signature Ole ==> Ole
  as mu_le_morphism.
auto.
Save.

Add Parametric Morphism (A : Type) : (mu (A:=A))
  with signature Oeq ==> Oeq
  as mu_eq_morphism.
auto.
Save.

(* eq version for Mlet_simpl/Munit_simpl *)
Add Parametric Morphism (A:Type) (a:distr A) : (@mu A a)
  with signature (@pointwise_relation A rat (@eq _) ==> Oeq) as mu_distr_eq_morphism.
intros f g H1.
apply mu_eq_compat; auto.
Save.

(* Utile *)
Add Parametric Morphism (A:Type) (a:distr A) : (@mu A a)
  with signature (@pointwise_relation A rat (@Oeq _ _) ==> Oeq) as mu_distr_Oeq_morphism.
intros f g H1.
apply mu_eq_compat; auto.
Save.

(* Utile? *)
Add Parametric Morphism (A:Type) (a:distr A) : (@mu A a)
  with signature (@pointwise_relation _ _ (@Ole _ _) ==> Ole) as mu_distr_le_morphism.
intros x y H.
apply mu_le_compat; auto.
Save.

Add Parametric Morphism (A B:Type) : (@Mlet A B)
  with signature (Ole ==> @pointwise_relation _ _ (@Ole _ _) ==> Ole) as mlet_distr_le_morphism.
intros x y H F G H2.
apply Mlet_le_compat; auto.
Save.

Add Parametric Morphism (A B:Type) : (@Mlet A B)
  with signature (Oeq ==> @pointwise_relation _ _ (@Oeq _ _) ==> Oeq) as mlet_distr_eq_morphism.
intros x y H F G H2.
apply Mlet_eq_compat; auto.
Save.

(** ** Properties of monadic operators *)
Lemma Mlet_unit : forall A B (x:A) (m:A -> distr B), Mlet (Munit x) m == m x.
intros; intro f; auto.
Save.

Lemma Mlet_ext : forall A (m:distr A), Mlet m (fun x => Munit x) == m.
intros;  intro f.
rewrite Mlet_simpl.
apply (mu_stable_eq m).
intro x; auto.
Save.

Lemma Mlet_assoc : forall A B C (m1: distr A) (m2:A -> distr B) (m3:B -> distr C),
     Mlet (Mlet m1 m2) m3 == Mlet m1 (fun x:A => Mlet (m2 x) m3).
intros;  intro f; simpl; trivial.
Save.

Lemma let_indep : forall (A B:Type) (m1:distr A) (m2: distr B) (f:MF B), 
       mu m1 (fun _ => mu m2 f) = mu m2 f.
intros; rewrite (mu_cte m1 (mu m2 f)); auto.
Save.


Lemma let_indep_distr : forall (A B:Type) (m1:distr A) (m2: distr B), 
       Mlet m1 (fun _ => m2) == m2.
exact let_indep.
Save.

(*
(** ** Conditional probabilities *)

Definition mcond A (m:M A) (f:MF A) : M A.
intros; exists (fun g => (m (fconj f g)) / m f).
red; intros g h legh.
apply Udiv_le_compat_left.
apply (fmonotonic m); unfold fconj; intros; auto.
Defined.

Lemma mcond_simpl : forall A (m:M A) (f g: MF A),
      mcond m f g = m (fconj f g) / m f.
trivial.
Save.

Lemma mcond_stable_plus : forall A (m:distr A) (f: MF A), stable_plus (mcond (mu m) f).
red; intros.
repeat rewrite mcond_simpl.
simpl; rewrite <- Udiv_plus.
apply Udiv_eq_compat_left.
assert (fplusok (fconj f f0) (fconj f g)).
auto.
rewrite <- (mu_stable_plus m H0).
apply (mu_stable_eq m); intro x; unfold fconj,fplus; auto.
apply Udistr_plus_left; auto.
apply (H x).
Save.

Lemma mcond_stable_inv : forall A (m:distr A) (f: MF A), stable_inv (mcond (mu m) f).
red; intros.
repeat rewrite mcond_simpl.
apply (Ueq_orc 0 (mu m f)); intro.
apply Ule_class; auto.
rewrite (Udiv_by_zero (mu m (fconj f (finv f0))) (mu m f)); auto.
transitivity (mu m (fminus f (fconj f f0)) / mu m f).
apply Udiv_le_compat_left.
apply (mu_monotonic m); intro x; unfold fconj,finv,fminus; auto.
rewrite stable_minus_distr; trivial.
rewrite Udiv_minus; trivial.
Save.

Lemma mcond_stable_mult : forall A (m:distr A) (f: MF A), stable_mult (mcond (mu m) f).
red; intros.
repeat rewrite mcond_simpl.
rewrite <- Umult_div_assoc.
apply Udiv_eq_compat_left.
apply Oeq_trans with (mu m (fmult k (fconj f f0))).
apply (mu_stable_eq m).
intro x; unfold fconj, fmult; auto.
apply (mu_stable_mult m).
auto.
Save.

Lemma mcond_continuous : forall A (m:distr A) (f: MF A), continuous (mcond (mu m) f).
red; intros.
repeat rewrite mcond_simpl.
apply (Ueq_orc 0 (mu m f)); intro.
apply Ule_class; auto.
rewrite (Udiv_by_zero (mu m (fconj f (lub h))) (mu m f)); auto.
apply Umult_div_le_right.
transitivity (mu m (lub((Fconj A f)@h))).
apply mu_monotonic.
exact (continuous2_app (Fconj A) f h).
rewrite (mu_continuous m).
transitivity (mshift UMult (mu m f) (lub (mcond (mu m) f @ h))); auto.
rewrite <- (lub_comp_le (mshift UMult (mu m f)) (mcond (mu m) f @ h) ).
apply lub_le_compat; intro x; simpl.
rewrite Udiv_mult; auto.
Save.

Definition Mcond A (m:distr A) (f:MF A) : distr A :=
   Build_distr (mcond_stable_inv m f) (mcond_stable_plus m f)
               (mcond_stable_mult m f) (mcond_continuous m f).

Lemma Mcond_total : forall A (m:distr A) (f:MF A), 
          ~ 0 == mu m f -> mu (Mcond m f) (fone A) == 1.
intros; simpl.
transitivity (mu m f /mu m f); auto.
apply Udiv_eq_compat; apply (mu_stable_eq m); intro x; unfold fconj, fone; auto.
Save.

Lemma Mcond_simpl : forall A (m:distr A) (f g:MF A), 
      mu (Mcond m f) g = mu m (fconj f g) / mu m f.
trivial.
Save.
Hint Resolve Mcond_simpl.

Lemma Mcond_zero_stable : forall A (m:distr A) (f g:MF A), 
      mu m g == 0 -> mu (Mcond m f) g == 0.
intros; rewrite  Mcond_simpl. 
apply Ule_zero_eq; transitivity (mu m g / mu m f); auto.
Save.

Lemma Mcond_null : forall A (m:distr A) (f g:MF A), 
      mu m f == 0 -> mu (Mcond m f) g == 0.
intros; rewrite  Mcond_simpl; auto. 
Save.

Lemma Mcond_conj : forall A (m:distr A) (f g:MF A), 
          mu m (fconj f g) == mu (Mcond m f) g * mu m f.
intros; rewrite Mcond_simpl.
apply (Ueq_orc 0 (mu m f)); intros; auto.
rewrite <- H; repeat Usimpl.
apply Ule_zero_eq.
transitivity (mu m f); auto.
symmetry; apply Udiv_mult; auto.
Save.

Lemma Mcond_decomp : 
    forall A (m:distr A) (f g:MF A), 
          mu m g == mu (Mcond m f) g * mu m f + mu (Mcond m (finv f)) g * mu m (finv f).
intros; transitivity (mu m (fplus (fconj f g) (fconj (finv f) g))).
apply mu_stable_eq; intro x; unfold fplus,finv,fconj; simpl; auto.
rewrite mu_stable_plus.
repeat rewrite Mcond_conj; auto.
apply fplusok_le_compat with f (finv f); auto.
Save.

Lemma Mcond_bayes : forall A (m:distr A) (f g:MF A), 
          mu (Mcond m f) g == (mu (Mcond m g) f * mu m g) / (mu m f).
intros; repeat rewrite Mcond_simpl.
apply Udiv_eq_compat; trivial.
apply (Ueq_orc (mu m g) 0); intros; trivial.
rewrite H; Usimpl.
apply Ule_zero_eq.
transitivity (mu m g); auto.
rewrite Udiv_mult; auto.
Save.

Lemma Mcond_mult : forall A (m:distr A) (f g h:MF A), 
            mu (Mcond m h) (fconj f g) == mu (Mcond m (fconj g h)) f * mu (Mcond m h) g.
intros; repeat rewrite Mcond_simpl.
apply (Ueq_orc 0 (mu m (fconj g h))); auto; intros.
rewrite Udiv_by_zero with (y:=mu m (fconj g h)); auto.
rewrite Udiv_zero_eq with (x:=mu m (fconj h (fconj f g))); auto.
symmetry; apply Ule_zero_eq; transitivity (mu m (fconj g h)); auto.
apply mu_le_compat; auto; intro x; repeat rewrite fconj_simpl.
rewrite Umult_sym; auto.
rewrite <- Umult_div_assoc; auto.
rewrite (fconj_sym h g); rewrite Udiv_mult; auto.
apply Udiv_eq_compat; auto.
apply mu_eq_compat; auto; intro x; repeat rewrite fconj_simpl.
rewrite (Umult_sym (g x) (h x)).
rewrite <- Umult_assoc.
Usimpl; auto.
Save.

Lemma Mcond_conj_simpl : forall A (m:distr A) (f g h:MF A), 
            (fconj f f == f) -> mu (Mcond m f) (fconj f g) == mu (Mcond m f) g.
intros; repeat rewrite Mcond_simpl.
apply Udiv_eq_compat; auto.
apply mu_eq_compat; auto; intro x; auto.
repeat rewrite fconj_simpl.
rewrite Umult_assoc.
rewrite (H x); auto.
Save.

Hint Resolve Mcond_mult Mcond_conj_simpl.
*)


(** ** Distribution for [flip]
The distribution associated to [flip ()] is 
       [f --> [1/2] (f true) + [1/2] (f false) ] *)

Notation "[1/2]" := (2%:Q)^-1.

Instance flip_mon : monotonic (fun (f : bool -> rat) => [1/2] * (f true) + [1/2] * (f false)).
intros f g Hfg.
apply Num.Theory.ler_add.
rewrite (Num.Theory.ler_pmul2l (x:=2%:~R^-1) _ (f true) (g true)); auto.
apply Hfg.
rewrite (Num.Theory.ler_pmul2l (x:=2%:~R^-1) _ (f false) (g false)); auto.
apply Hfg.
Save.

Definition flip : M bool := mon (fun (f : bool -> rat) => [1/2] * (f true) + [1/2] * (f false)).

Lemma flip_stable_sub : stable_sub flip.
unfold flip, stable_sub; intros f g; simpl.
ring_to_rat; ring.
Save.

Lemma flip_prob : flip (fun x => 1) = 1.
rewrite /flip /= !mulr1 -div1r addf_div /=; auto.
rewrite mul1r.
rewrite -intrD -intrM.
change ((4)%:Q / (4)%:Q = 1).
apply divrr.
auto.
Save.

Lemma flip_true : flip (fun b => (b%:Q)) = [1/2].
rewrite /flip /= mulr1 mulr0.
auto.
Save.

Lemma flip_false : flip (fun b => (~~b)%:Q) = [1/2].
rewrite /flip /= mulr1 mulr0.
auto.
Save.

Hint Resolve flip_true flip_false.

Definition Flip  : distr bool.
exists flip.
apply flip_stable_sub.
apply flip_prob.
Defined.

Lemma Flip_simpl : forall f, mu Flip f = [1/2] * (f true) + [1/2] * (f false).
trivial.
Save.


(** ** Finite distributions given by points and rational coefficients *)

Require Arith.

Local Open Scope rat_scope.

Section FiniteDistributions.

Variable A : Type.
Variable p : seq A.

(** We use a finite sequent of points, give a rational coefficient 
    to each point but only consider positive ones *)

Definition weight (c : A -> rat) : rat := \sum_(i <- p | 0 < c i) (c i).

Lemma weight_nonneg c : 0 <= weight c.
apply Num.Theory.sumr_ge0.
auto.
Save.
Hint Resolve weight_nonneg.

Lemma weight_case c : (weight c = 0) \/ 0 < (weight c)^-1.
have Hc:((weight c == 0) || (0 < weight c)).
rewrite -(Num.Theory.le0r (weight c)); auto.
move:Hc; case /orP => Hc.
move:Hc; case /eqP; auto.
by rewrite Num.Theory.invr_gt0; auto.
Save.


Instance finite_mon (c : A -> rat) : 
   monotonic (fun f => (\sum_(i <- p | 0 < c i) (c i * f i))/weight c).
intros f g Hfg.
rewrite /Ole /=.
case (weight_case c) => [Hci|Hci].
rewrite Hci.
rat_to_ring.
by rewrite invr0 mulr0 mulr0.
rat_to_ring.
rewrite (Num.Theory.ler_pmul2r Hci).
apply Num.Theory.ler_sum.
move => i Hi.
rewrite (Num.Theory.ler_pmul2l Hi).
apply Hfg.
Save.

Definition mfinite (c : A -> rat) : M A := 
       mon (fun f => (\sum_(i <- p | 0 < c i) (c i * f i))/weight c).

Lemma finite_simpl (c : A -> rat) f : 
     mfinite c f = (\sum_(i <- p | 0 < c i) (c i * f i))/weight c.
trivial.
Save.

Lemma finite_stable_sub (c : A -> rat) : stable_sub (mfinite c).
red; intros.
rewrite !finite_simpl.
case (weight_case c) => [Hci|Hci].
rewrite Hci.
rat_to_ring.
by rewrite invr0 !mulr0 subr0.
rewrite -mulrBl.
rat_to_ring.
congr *%R.
rewrite -sumrB.
apply eq_bigr => i Hi.
rewrite mulrDr.
congr (+%R).
by rewrite mulrN.
Save.

End FiniteDistributions.

(** We have a distribution when the total weight is positive *)

Record fin (A:Type) : Type := mkfin
     {points : seq A; coeff : A -> rat; weight_pos : 0 < weight points coeff}.
Hint Resolve weight_pos.

Lemma inv_weight_pos A (d:fin A) : 0 < (weight (points d) (coeff d))^-1.
by rewrite Num.Theory.invr_gt0; auto.
Save.
Hint Resolve inv_weight_pos.

Definition fprob A (d:fin A) (a : A) : rat := coeff d a / weight (points d) (coeff d).

Definition Finite : forall A,  fin A -> distr A.
intros A d ; exists (mfinite (points d) (coeff d)).
apply finite_stable_sub; trivial.
rewrite finite_simpl.
rewrite -{2}(divrr (x:=weight (points d) (coeff d))).
congr *%R.
apply eq_bigr => i Hi.
apply mulr1.
apply Num.Theory.unitf_gt0.
auto.
Defined.

Lemma Finite_simpl : forall A (d:fin A), 
     mu (Finite d) = mfinite (points d) (coeff d).
trivial.
Save.


Lemma Finite_eq_in (A:eqType) (d:fin A) (a:A) : 
     uniq (points d) -> (a \in points d)%SEQ -> 0 < coeff d a -> 
     mu (Finite d) (fun x => (x==a)%:Q) = fprob d a.
move => Hu Hain Hap.
rewrite Finite_simpl finite_simpl /fprob.
congr *%R.
rewrite -big_filter.
rewrite (bigD1_seq a) /=.
rewrite (eq_refl a) mulr1.
transitivity (coeff d a + 0)%R.
congr +%R.
apply big1.
move => i Hi.
move: Hi; case (i == a); rewrite /=.
by [].
by rewrite mulr0.
by rewrite addr0.
rewrite mem_filter.
by rewrite Hain Hap.
by rewrite filter_uniq.
Save.


Lemma Finite_eq_out (A:eqType) (d:fin A) (a:A) : 
     (a \notin points d)%SEQ \/ (coeff d a <= 0)%Q -> 
     mu (Finite d) (fun x => (x==a)%:Q) = 0.
move => Ha.
rewrite Finite_simpl finite_simpl.
rewrite big1_seq.
apply mul0r.
move => i Hi.
case (@eqP _ i a).
move => H; move :Hi; rewrite H /=.
move => Ha1.
case (andP Ha1) => H1 H2 //=.
destruct Ha.
by move: H0 H2; case (a \in points d).
move: H0 H1; rewrite Num.Theory.ltrNge /=.
change ((coeff d a <= 0)%B -> ~~(coeff d a <= 0)%B -> (coeff d a * 1%:~R)%R = 0%R).
by case (coeff d a <= 0)%B.
by move => _; rewrite /= mulr0.
Save.


(** ** Uniform distribution beween 0 and n *)

Record unif (A:Type) : Type := mkunif 
   {upoints :> seq A; _ : upoints<>[::]}.

Definition unif2fin A (p:unif A) : fin A.
   exists (upoints p) (fun A => 1%Q).
case: p.
case => [|a s] /=.
by move => H; exfalso.
move => _.
rewrite /weight.
rewrite big_cons /=.
apply Num.Theory.ltr_le_trans with 1; auto.
rewrite Num.Theory.ler_addl.
apply weight_nonneg.
Save.


Definition Uniform A (d:unif A) : distr A := Finite (unif2fin d).
     
(*
Definition is_discrete (A:Type) (m: distr A) := 
      exists d : discr A, m == Discrete d.

(** *** Distribution for [random n]
The distribution associated to [random n] is 
       [ f  --> sigma (i=0..n) [1]1+n (f i) ]
       we cannot factorize [ [1/]1+n ] because of possible overflow *)

Instance random_mon : forall n, monotonic (fun (f:MF nat) => sigma (fun k => Unth n *  f k) (S n)).
red; intros; auto.
Save.

Definition random (n:nat):M nat := mon (fun (f:MF nat) => sigma (fun k => Unth n *  f k) (S n)).

Lemma random_simpl : forall n (f : MF nat), 
           random n f = sigma (fun k => Unth n *  f k) (S n).
trivial.
Save.

(** *** Properties of [random] *)

Lemma random_stable_inv : forall n, stable_inv (random n).
unfold random, stable_inv, finv; intros; simpl.
rewrite (sigma_inv f (fnth_retract n)); auto.
Save.

Lemma random_stable_plus : forall n, stable_plus (random n).
unfold stable_plus, fplus; intros.
repeat (rewrite random_simpl).
unfold fplusok, finv in H.
transitivity 
 (sigma (fun k : nat => ([1/]1+n * f k) + ([1/]1+n  * g k)) (S n)).
apply sigma_eq_compat; intros.
assert (f k <= [1-] (g k)); auto.
apply sigma_plus with (f:=fun k : nat => Unth n * f k)
                      (g:=fun k : nat => Unth n * g k); auto.
Save.

Lemma random_stable_mult : forall n, stable_mult (random n).
unfold stable_mult, fmult; intros; repeat (rewrite random_simpl).
transitivity 
 (sigma (fun l : nat => k * ([1/]1+n * f l)) (S n)).
apply sigma_eq_compat; intros; auto.
apply sigma_mult with (f:=fun k : nat => Unth n * f k).
red; intros.
transitivity ([1/]1+n); auto.
transitivity ([1-] (sigma (fun k1 => Unth n) k0)); auto.
apply (fnth_retract n k0); auto.
Save.


Lemma random_continuous : forall n, continuous (random n).
unfold continuous; intros; rewrite random_simpl.
transitivity 
    (sigma (fun k : nat => lub (UMult ([1/]1+n) @ (h <o> k))) (S n)).
apply sigma_le_compat; intros; simpl.
rewrite (lub_eq_mult ([1/]1+n) (h <o> k)); auto.
transitivity 
(sigma (lub (D:=MF nat) (ishift (fun k : nat => (UMult ([1/]1+n) @ (h <o> k))))) (S n)).
apply sigma_le_compat; intros; auto.
rewrite MF_lub_simpl.
apply lub_le_compat; intro m; simpl; auto.
rewrite sigma_lub1; auto.
apply lub_le_compat; intro m; simpl; auto.
Save.

Definition Random (n:nat) : distr nat.
exists (random n).
apply random_stable_inv.
apply random_stable_plus.
apply random_stable_mult.
apply random_continuous.
Defined.

Lemma Random_simpl : forall (n:nat), mu (Random n) = random n.  
trivial.
Save.

Instance Random_total : forall n : nat,  Term (Random n).
red; intros; simpl mu;unfold fone; rewrite random_simpl.
transitivity  (sigma (fnth n) (S n)).
apply sigma_eq_compat.
intros; repeat Usimpl; auto.
auto.
Save.
Hint Resolve Random_total.

Lemma Random_inv : forall f n, mu (Random n) (finv f) == [1-] (mu (Random n) f).
intros; apply mu_stable_inv_term; auto.
Save.
Hint Resolve Random_inv.
*)

(** ** Tacticals *)

(*
Ltac mu_plus d := 
  match goal with 
 | |- context [fmont (mu d) (fun x => (Uplus (@?f x) (@?g x)))] => 
      rewrite (mu_stable_plus d (f:=f) (g:=g))
  end.

Ltac mu_mult d := 
  match goal with 
 | |- context [fmont (mu d) (fun x => (Umult ?k (@?f x)))] => 
      rewrite (mu_stable_mult d k f)
  end.
*)
