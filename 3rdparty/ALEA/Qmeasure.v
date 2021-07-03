(** * ALEA.Qmeasure: Finite probabilities *)
(******************************************************************************)
(*      Copyright (C) 2015-2018 Florent Hivert <florent.hivert@lri.fr>        *)
(*      Copyright (C) 2015      Chritine Paulin <christine.paulin@lri.fr>     *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
(** * Definition of finite probabilities as measures with values in rational numbers *)

Require Import Misc Ccpo.

Set Implicit Arguments.

Local Open Scope O_scope.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun eqtype ssrbool ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop ssrint rat ssralg ssrnum.
Import GRing.
Import Num.Theory.
Import mc_1_10.Num.Theory.

Local Open Scope ring_scope.

Program Instance ratO : ord rat :=
     { Oeq := fun n m : rat => n = m;
       Ole := fun n m : rat => (n <= m)%R}.
Next Obligation.
apply Build_Order => /=.
- exact: lerr.
- split => [/andP  H | ->]; first by apply ler_asym.
  by rewrite lerr.
- move=> /= x y z; apply ler_trans.
Defined.

(** Functions to be measured *)

Definition MF (A:Type) := A -> rat.

Instance MFO (A:Type) : ord (MF A) := ford A rat.

(** Type of measures on [A] *)

Definition M A := MF A -m> rat.

Instance MO (A:Type) : ord (M A) := fmono (MF A) rat.

Instance app_mon (A:Type) (x:A) : monotonic (fun (f:MF A) => f x).
Proof. by []. Qed.
#[export] Hint Resolve app_mon : core.

(** Monadic operators on M A *)

Definition munit (A:Type) (x:A) : M A := mon (fun (f:MF A) => f x).

Definition mstar (A B:Type) : M A -> (A -> M B) -> M B.
move=> a F; exists (fun f => a (fun x => F x f)) => /= x y H.
apply (fmonotonic a) => z /=.
by apply (fmonotonic (F z)).
Defined.

Lemma star_simpl (A B:Type) (a:M A) (F:A -> M B) (f:MF B) :
  mstar a F f = a (fun x => F x f).
Proof. by []. Qed.

(** ** Properties of monadic operators *)
Lemma law1 (A B:Type) (x:A) (F:A -> M B) (f:MF B) :
  mstar (munit x) F f == F x f.
Proof. by []. Qed.

Lemma law2 (A:Type) (a:M A) (f:MF A) :
  mstar a (fun x:A => munit x) f == a (fun x:A => f x).
Proof. by []. Qed.

Lemma law3 (A B C:Type) (a:M A) (F:A -> M B) (G:B -> M C) (f:MF C) :
  mstar (mstar a F) G f == mstar a (fun x:A => mstar (F x) G) f.
Proof. by []. Qed.

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

Implicit Types (f g : MF A).

Lemma Mstable_eq : stable m.
Proof using . exact: monotonic_stable. Qed.
Hint Resolve Mstable_eq : core.

Lemma Mstable0 : m \0 = 0.
Proof using Mstable_sub.
transitivity (m \0 - m \0); last by rewrite (GRing.addrN (m \0)).
transitivity (m (\0 \- \0)); first exact: Mstable_eq.
by apply Mstable_sub; rewrite (GRing.addrN (m \0)).
Qed.
Hint Resolve Mstable0 : core.

Lemma Mstable_opp : stable_opp m.
Proof using Mstable_sub.
move => f; transitivity (m \0 - m f); first last.
  by rewrite Mstable0 /null_fun_head /= sub0r.
rewrite -Mstable_sub.
apply Mstable_eq => x.
by rewrite /null_fun_head /= sub0r.
Qed.

Lemma Mstable_add : stable_add m.
Proof using Mstable_sub.
move => f g.
transitivity (m f - m (fun x => - g x)); last by rewrite Mstable_opp opprK.
transitivity (m (f \- (fun x => - g x))); last exact: Mstable_sub.
apply Mstable_eq => x.
by rewrite /= opprK.
Qed.

Lemma Mstable_addn f (n : nat) : m (fun x => f x *+ n) = (m f) *+ n.
Proof using Mstable_sub.
elim: n => [| n IHn]; first by rewrite mulr0n.
rewrite mulrSr.
transitivity (m (fun x : A => f x *+ n) + m f); last by congr +%R.
rewrite -Mstable_add.
by apply Mstable_eq => x /=; rewrite mulrSr.
Qed.

Lemma Mstable_subn f (n : nat) : m (fun x => f x *- n) = (m f) *- n.
Proof using Mstable_sub.
by rewrite Mstable_opp Mstable_addn.
Qed.

Lemma Mstable_divn f (n : nat) :
  m (fun x => f x / n%:~R) = (m f) / (n%:~R).
Proof using Mstable_sub.
case: n => [|n].
  rewrite rat0 invr0 mulr0 -{2}Mstable0.
  apply Mstable_eq => x /=.
  exact: mulr0.
have Hu: ((n.+1)%:~R : rat) \in unit.
  apply Num.Theory.unitf_gt0.
  by rewrite ltr0z.
apply (@mulrI _ (n.+1)%:~R); first by [].
rewrite mulr_natl -Mstable_addn mulrC mulrVK //.
apply Mstable_eq => x /=.
by rewrite -mulr_natr mulrVK.
Qed.

Lemma Mstable_addi f (n : int) : m (fun x => f x *~ n) = (m f) *~ n.
Proof using Mstable_sub.
case:n => [np|nn].
- by rewrite -pmulrn; apply Mstable_addn.
- by rewrite NegzE -nmulrn; apply Mstable_subn.
Qed.

Lemma Mstable_muli f (n : int) : m (fun x => n%:~R * f x) = (n%:~R) * (m f).
Proof using Mstable_sub.
rewrite mulrzl -Mstable_addi.
apply Mstable_eq => x /=.
exact: mulrzl.
Qed.

Lemma Mstable_divi f (n : int) : m (fun x => f x / n%:~R) = (m f) / (n%:~R).
Proof using Mstable_sub.
case:n => [np|nn].
- by rewrite -pmulrn; apply Mstable_divn.
- rewrite NegzE -nmulrn invrN mulrN.
  rewrite -Mstable_divn -Mstable_opp.
  apply Mstable_eq => x /=.
  by rewrite mulrN.
Qed.

Lemma Mstable_mull : stable_mull m.
Proof using Mstable_sub.
rewrite /stable_mull => n f.
rewrite -{2}(divq_num_den n).
rewrite -mulrA (mulrC _ (m f)).
rewrite -Mstable_divi -Mstable_muli.
apply Mstable_eq => x /=.
by rewrite (mulrC (f x)) mulrA (divq_num_den n).
Qed.

Lemma Mstable_linear (p q : rat) f g :
  m ((p \*o f) \+ (q \*o g)) = p * (m f) + q * (m g).
Proof using Mstable_sub.
by rewrite Mstable_add !Mstable_mull.
Qed.

End StabilityProperties.
#[export] Hint Resolve Mstable_eq : core.
#[export] Hint Resolve Mstable0 : core.
#[export] Hint Resolve Mstable_opp : core.
#[export] Hint Resolve Mstable_add : core.


Lemma unit_stable_eq (A:Type) (x:A) : stable (munit x).
Proof. by []. Qed.

Lemma star_stable_eq (A B:Type) (m:M A) (F:A -> M B) : stable (mstar m F).
Proof. by []. Qed.

Lemma unit_monotonic A (x:A) (f g : MF A) :
  (f <= g)%O -> munit x f <= munit x g.
Proof. by rewrite /unit /=. Qed.

Lemma star_monotonic A B (m:M A) (F:A -> M B) (f g : MF B) :
  (f <= g)%O -> mstar m F f <= mstar m F g.
Proof.
move => H; rewrite /mstar /=.
apply (fmonotonic m) => x.
exact: (fmonotonic (F x)).
Qed.

Lemma star_le_compat A B (m1 m2:M A) (F1 F2:A -> M B) :
  (m1 <= m2)%O -> (F1 <= F2)%O -> (mstar m1 F1 <= mstar m2 F2)%O.
Proof.
move=> Hm HF f; rewrite !star_simpl.
transitivity (m1 (fun x : A => (F2 x) f)); last by [].
apply (fmonotonic m1) => x.
exact: (HF x f).
Qed.
#[export] Hint Resolve star_le_compat : core.

(** *** Stability for substraction of unit and star *)
Lemma unit_stable_sub (A:Type) (x:A) : stable_sub (munit x).
Proof. by []. Qed.

Lemma star_stable_sub (A B:Type) (m:M A) (F:A -> M B) :
  stable_sub m -> (forall a:A, stable_sub (F a)) -> stable_sub (mstar m F).
Proof.
rewrite /stable_sub /mstar /= => Hst HstF f g.
transitivity (m (fun x:A => F x f - F x g)).
- by apply: (Mstable_eq m) => x.
- exact: (Hst (fun x : A => (F x) f) (fun x : A => (F x) g)).
Qed.

(** ** Definition of distribution
Finite distributions are monotonic measure functions such that
    - [ mu (f - g) = mu f - mu g]
    - [ mu 1 = 1]
*)

Record distr (A:Type) : Type := {
       mu : M A;
       mu_stable_sub : stable_sub mu;
       mu_prob : mu (fun x => 1) = 1
   }.

#[export] Hint Resolve mu_stable_sub mu_prob : core.

(** ** Properties of measures *)
Section MeasureProp.

Context {A : Type} (m: distr A).
Implicit Types (f g : MF A).

Lemma mu_monotonic : monotonic (mu m).
Proof. exact: fmonotonic. Qed.
Hint Resolve mu_monotonic : core.

Lemma mu_stable_eq : stable (mu m).
Proof. exact: fstable. Qed.
Hint Resolve mu_stable_eq : core.

Lemma mu_zero : mu m \0 = 0.
Proof. exact: Mstable0. Qed.
Hint Resolve mu_zero : core.

Lemma mu_zero_eq f : (forall x, f x = 0) -> mu m f = 0.
Proof.
transitivity (mu m \0); last by [].
exact: Mstable_eq.
Qed.

Lemma mu_one_eq f : (forall x, f x = 1) -> mu m f = 1.
Proof.
transitivity (mu m (fun x => 1)); last by [].
exact: Mstable_eq.
Qed.

Lemma mu_stable_inv f : mu m (fun x => 1 - f x) = 1 - (mu m f).
Proof.
transitivity (mu m (fun x => 1) - mu m f).
- by rewrite mu_stable_sub.
- by rewrite mu_prob.
Qed.

Lemma mu_stable_add f g : mu m (f \+ g) = mu m f + mu m g.
Proof. exact: Mstable_add. Qed.

Lemma mu_stable_mull (q : rat) f : mu m (q \*o f) = q * mu m f.
Proof. exact: Mstable_mull. Qed.

Lemma mu_add_zero f g : mu m f = 0 -> mu m g = 0 -> mu m (f \+ g) = 0.
Proof. by move=> Hf Hg; rewrite mu_stable_add Hf Hg. Qed.

Lemma mu_stable_pos f : (\0 <= f)%O -> 0 <= mu m f.
Proof.
move => Hf; rewrite -mu_zero.
exact: (fmonotonic (mu m)).
Qed.

Lemma mu_stable_le1 f : (forall x, f x <= 1) -> mu m f <= 1.
Proof.
move => Hf; rewrite -(mu_prob m).
exact: mu_monotonic.
Qed.

Lemma mu_cte (c:rat) : mu m (fun x => c) = c.
Proof.
transitivity (mu m (fun x => c * 1)).
- by apply mu_stable_eq => x; rewrite mulr1.
- by rewrite mu_stable_mull mu_prob mulr1.
Qed.

Lemma mu_stable_mulr (c:rat) f : mu m (c \o* f) = (mu m f) * c.
Proof.
rewrite mulrC -mu_stable_mull.
apply mu_stable_eq => x.
by rewrite /= mulrC.
Qed.

Lemma mu_stable_inv_inv f : mu m f = 1 - mu m (fun x => 1 - f x).
Proof.
rewrite -mu_stable_inv.
apply mu_stable_eq => x; rewrite opprB /=.
by rewrite addrCA subrr addr0.
Qed.

End MeasureProp.
#[export] Hint Resolve mu_monotonic : core.
#[export] Hint Resolve mu_stable_eq : core.
#[export] Hint Resolve mu_zero : core.
#[export] Hint Immediate mu_zero_eq : core.
#[export] Hint Immediate mu_one_eq : core.
#[export] Hint Resolve mu_stable_inv : core.
#[export] Hint Resolve mu_stable_add : core.
#[export] Hint Resolve mu_stable_mull : core.
#[export] Hint Resolve mu_add_zero : core.
#[export] Hint Resolve mu_cte : core.
#[export] Hint Resolve mu_stable_inv_inv : core.

Program Instance Odistr (A:Type) : ord (distr A) := 
    {Ole := fun (f g : distr A) => (mu f <= mu g)%O;
     Oeq := fun (f g : distr A) => Oeq (mu f) (mu g)}.
Next Obligation.
split; intuition.
- by apply ler_anti; rewrite H0 H1.
- by rewrite H.
- by rewrite H.
- by move=> f g h H1 H2 x; apply: (ler_trans (H1 x) (H2 x)).
Defined.


(** ** Monadic operators for distributions *)
Section MonDistrib.

Variables (A B : Type).

Definition Munit : A -> distr A.
Proof.
move=> x.
by exists (munit x); first exact: unit_stable_sub.
Defined.

Definition Mlet : distr A -> (A -> distr B) -> distr B.
Proof.
move=> mA mB.
exists (mstar (mu mA) (fun x => (mu (mB x)))).
- exact: star_stable_sub.
- by rewrite /mstar /=; apply mu_one_eq.
Defined.

Lemma Munit_simpl (q : A -> rat) x : mu (Munit x) q = q x.
Proof. by []. Qed.

Lemma Munit_simpl_eq (q : A -> rat) x : mu (Munit x) q == q x.
Proof. by []. Qed.


Lemma Mlet_simpl (m : distr A) (M : A -> distr B) (f : B -> rat) :
  mu (Mlet m M) f = mu m (fun x => (mu (M x) f)).
Proof. by []. Qed.

Lemma Mlet_simpl_eq (m : distr A) (M : A -> distr B) (f : B -> rat) :
mu (Mlet m M) f == mu m (fun x => (mu (M x) f)).
Proof. by []. Qed.

End MonDistrib.


(** * Operations on distributions *)
Section OperDistr.

Variables (A B C : Type).

Lemma Munit_eq_compat (x y : A) : x = y -> Munit x == Munit y.
Proof. by move ->. Qed.

Lemma Mlet_le_compat (m1 m2 : distr A) (M1 M2 : A -> distr B) :
  (m1 <= m2 -> M1 <= M2 -> Mlet m1 M1 <= Mlet m2 M2)%O.
Proof.
move=> Hm HM f; rewrite !Mlet_simpl.
transitivity (mu m2 (fun x : A => mu (M1 x) f)); first by [].
apply (fmonotonic (mu m2)) => x.
exact: (HM x f).
Qed.
Hint Resolve Mlet_le_compat : core.

Add Parametric Morphism : (Mlet (A:=A) (B:=B))
    with signature Ole ==> Ole ==> Ole
      as Mlet_le_morphism.
Proof. by auto. Qed.

Add Parametric Morphism : (Mlet (A:=A) (B:=B))
    with signature Ole ==> (@pointwise_relation A (distr B) (@Ole _ _)) ==> Ole
      as Mlet_le_pointwise_morphism.
Proof. by auto. Qed.

Instance Mlet_mon2 : monotonic2 (@Mlet A B).
Proof. by red; auto. Qed.

Definition MLet : distr A -m> (A -> distr B) -m> distr B
  := mon2 (@Mlet A B).

Lemma MLet_simpl (m : distr A) (M : A -> distr B) (f : B -> rat) :
  mu (MLet m M) f = mu m (fun x => mu (M x) f).
Proof. by []. Qed.

Lemma Mlet_eq_compat (m1 m2 : distr A) (M1 M2 : A -> distr B) :
  (m1 == m2 -> M1 == M2 -> Mlet m1 M1 == Mlet m2 M2)%type.
Proof. by move=> H1 H2; exact: monotonic2_stable2. Qed.
Hint Resolve Mlet_eq_compat : core.

Add Parametric Morphism : (Mlet (A:=A) (B:=B))
    with signature Oeq ==> Oeq ==> Oeq
      as Mlet_eq_morphism.
Proof. by auto. Qed.

Add Parametric Morphism : (Mlet (A:=A) (B:=B))
    with signature  Oeq ==> (@pointwise_relation A (distr B) (@Oeq _ _)) ==> Oeq
      as Mlet_Oeq_pointwise_morphism.
Proof. by auto. Qed.

Lemma mu_le_compat (m1 m2 : distr A) :
  (m1 <= m2 -> forall f g : A -> rat, f <= g -> mu m1 f <= mu m2 g)%O.
Proof. by move=> Hm f g Hfg; transitivity (mu m2 f); auto. Qed.

Lemma mu_eq_compat (m1 m2 : distr A) :
  (m1 == m2 -> forall f g : A -> rat,  f == g -> mu m1 f = mu m2 g)%type.
Proof.
move=> Hm f g Hfg.
by change (mu m1 f == mu m2 g)%type; transitivity (mu m2 f); auto.
Qed.
Hint Immediate mu_le_compat mu_eq_compat : core.

Add Parametric Morphism : (mu (A:=A))
    with signature Ole ==> Ole
      as mu_le_morphism.
Proof. by auto. Qed.

Add Parametric Morphism : (mu (A:=A))
    with signature Oeq ==> Oeq
      as mu_eq_morphism.
Proof. by auto. Qed.

(* eq version for Mlet_simpl/Munit_simpl *)
Add Parametric Morphism (a : distr A) : (@mu A a)
    with signature (@pointwise_relation A rat (@eq _) ==> Oeq)
      as mu_distr_eq_morphism.
Proof. by move=> f g H1; exact: mu_eq_compat. Qed.

(* Utile *)
Add Parametric Morphism (a : distr A) : (@mu A a)
    with signature (@pointwise_relation A rat (@Oeq _ _) ==> Oeq)
      as mu_distr_Oeq_morphism.
Proof. by move=> f g H1; exact: mu_eq_compat. Qed.

(* Utile? *)
Add Parametric Morphism (a : distr A) : (@mu A a)
    with signature (@pointwise_relation _ _ (@Ole _ _) ==> Ole)
      as mu_distr_le_morphism.
Proof. by move=> x y H; exact: mu_le_compat. Qed.

Add Parametric Morphism : (@Mlet A B)
    with signature (Ole ==> @pointwise_relation _ _ (@Ole _ _) ==> Ole)
      as mlet_distr_le_morphism.
Proof. by move=> x y H F G H2; exact: Mlet_le_compat. Qed.

Add Parametric Morphism : (@Mlet A B)
    with signature (Oeq ==> @pointwise_relation _ _ (@Oeq _ _) ==> Oeq)
      as mlet_distr_eq_morphism.
Proof. by move=> x y H F G H2; exact: Mlet_eq_compat. Qed.

(** ** Properties of monadic operators *)
Lemma Mlet_unit (x : A) (m : A -> distr B) : Mlet (Munit x) m == m x.
Proof. by []. Qed.

Lemma Mlet_ext (m : distr A) : Mlet m (fun x => Munit x) == m.
Proof. by []. Qed.

Lemma Mlet_assoc (m1 : distr A) (m2 : A -> distr B) (m3 : B -> distr C) :
  Mlet (Mlet m1 m2) m3 == Mlet m1 (fun x:A => Mlet (m2 x) m3).
Proof. by []. Qed.

Lemma let_indep (m1 : distr A) (m2 : distr B) (f : MF B) :
  mu m1 (fun => mu m2 f) = mu m2 f.
Proof. by rewrite (mu_cte m1 (mu m2 f)). Qed.

Lemma let_indep_distr (m1 : distr A) (m2 : distr B) :
  Mlet m1 (fun => m2) == m2.
Proof. exact: let_indep. Qed.

Implicit Types (m : distr A) (f g : A -> bool).
Lemma mu_bool_le1 m f : mu m (fun x => (f x)%:~R) <= 1%:~R.
Proof.
apply ler_trans with (mu m (fun x => 1)).
- apply mu_monotonic => x.
  by case (f x) => //=.
- by rewrite mu_prob => //=.
Qed.
Hint Resolve mu_bool_le1 : core.

Lemma mu_bool_0le (m : distr A) (f : A -> bool) :
  0%:~R <= mu m (fun x => (f x)%:~R).
Proof. by apply mu_stable_pos => x /=; case (f x). Qed.
Hint Resolve mu_bool_0le : core.

Lemma mu_bool_impl m f g :
  (forall x, (f x) ==> (g x)%B) ->
  (mu m (fun x => (f x)%:~R) <= mu m (fun x => (g x)%:~R)).
Proof.
move=> Hfg; apply mu_monotonic => x.
by move: (Hfg x); case (f x); case (g x).
Qed.

Lemma mu_bool_impl1 m f g :
  (forall x, (f x) ==> (g x)%B) ->
  mu m (fun x => (f x)%:~R) = 1 ->  mu m (fun x => (g x)%:~R) = 1.
Proof.
move=> Hi Hf.
apply ler_anti.
apply /andP; split; first by [].
rewrite -[X in X <= _]Hf.
exact: mu_bool_impl.
Qed.

Lemma mu_bool_negb0 m f g :
  (forall x, (f x) ==> ~~ (g x)%B) ->
  mu m (fun x => (f x)%:~R) = 1 ->
  mu m (fun x => (g x)%:~R) = 0.
Proof.
move => Hi Hf.
apply ler_anti; apply /andP; split.
- apply ler_trans with (mu m (fun x : A => 1 - (f x)%:~R)).
  + apply mu_monotonic => x.
    by case: (f x) (Hi x); case (g x).
  + by rewrite mu_stable_inv Hf subrr.
- apply mu_stable_pos.
  by move => x /=; case (g x).
Qed.

Lemma mu_bool_negb m f :
  mu m (fun x => (~~ f x)%:~R) = 1 - mu m (fun x => (f x)%:~R).
Proof.
rewrite -mu_stable_inv.
by apply mu_stable_eq => x; case (f x).
Qed.

Lemma mu_bool_negb1 m f g :
  (forall x, (~~ (f x) ==> g x)%B) ->
  mu m (fun x => (f x)%:~R) = 0 ->
  mu m (fun x => (g x)%:~R) = 1.
Proof.
move => Hi Hf.
apply ler_anti; apply /andP; split.
- by apply mu_stable_le1 => x /=; case (g x).
  apply ler_trans with (mu m (fun x : A => 1 - (f x)%:~R)).
  + by rewrite mu_stable_inv Hf subr0.
  + apply mu_monotonic => x.
    by move: (Hi x); case (f x); case (g x).
Qed.

End OperDistr.

#[export] Hint Resolve mu_bool_le1 : core.
#[export] Hint Resolve mu_bool_0le : core.

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
Qed.

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
Qed.

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
Qed.

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
Qed.

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
Qed.

Definition Mcond A (m:distr A) (f:MF A) : distr A :=
   Build_distr (mcond_stable_inv m f) (mcond_stable_plus m f)
               (mcond_stable_mult m f) (mcond_continuous m f).

Lemma Mcond_total : forall A (m:distr A) (f:MF A), 
          ~ 0 == mu m f -> mu (Mcond m f) (fone A) == 1.
intros; simpl.
transitivity (mu m f /mu m f); auto.
apply Udiv_eq_compat; apply (mu_stable_eq m); intro x; unfold fconj, fone; auto.
Qed.

Lemma Mcond_simpl : forall A (m:distr A) (f g:MF A), 
      mu (Mcond m f) g = mu m (fconj f g) / mu m f.
trivial.
Qed.
Hint Resolve Mcond_simpl : core.

Lemma Mcond_zero_stable : forall A (m:distr A) (f g:MF A), 
      mu m g == 0 -> mu (Mcond m f) g == 0.
intros; rewrite  Mcond_simpl. 
apply Ule_zero_eq; transitivity (mu m g / mu m f); auto.
Qed.

Lemma Mcond_null : forall A (m:distr A) (f g:MF A), 
      mu m f == 0 -> mu (Mcond m f) g == 0.
intros; rewrite  Mcond_simpl; auto. 
Qed.

Lemma Mcond_conj : forall A (m:distr A) (f g:MF A), 
          mu m (fconj f g) == mu (Mcond m f) g * mu m f.
intros; rewrite Mcond_simpl.
apply (Ueq_orc 0 (mu m f)); intros; auto.
rewrite <- H; repeat Usimpl.
apply Ule_zero_eq.
transitivity (mu m f); auto.
symmetry; apply Udiv_mult; auto.
Qed.

Lemma Mcond_decomp : 
    forall A (m:distr A) (f g:MF A), 
          mu m g == mu (Mcond m f) g * mu m f + mu (Mcond m (finv f)) g * mu m (finv f).
intros; transitivity (mu m (fplus (fconj f g) (fconj (finv f) g))).
apply mu_stable_eq; intro x; unfold fplus,finv,fconj; simpl; auto.
rewrite mu_stable_plus.
repeat rewrite Mcond_conj; auto.
apply fplusok_le_compat with f (finv f); auto.
Qed.

Lemma Mcond_bayes : forall A (m:distr A) (f g:MF A), 
          mu (Mcond m f) g == (mu (Mcond m g) f * mu m g) / (mu m f).
intros; repeat rewrite Mcond_simpl.
apply Udiv_eq_compat; trivial.
apply (Ueq_orc (mu m g) 0); intros; trivial.
rewrite H; Usimpl.
apply Ule_zero_eq.
transitivity (mu m g); auto.
rewrite Udiv_mult; auto.
Qed.

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
Qed.

Lemma Mcond_conj_simpl : forall A (m:distr A) (f g h:MF A), 
            (fconj f f == f) -> mu (Mcond m f) (fconj f g) == mu (Mcond m f) g.
intros; repeat rewrite Mcond_simpl.
apply Udiv_eq_compat; auto.
apply mu_eq_compat; auto; intro x; auto.
repeat rewrite fconj_simpl.
rewrite Umult_assoc.
rewrite (H x); auto.
Qed.

Hint Resolve Mcond_mult Mcond_conj_simpl : core.
*)

(** * Examples of distributions *)

(** ** Flipping a coin:

The distribution associated to [flip ()] is
       [f --> [1/2] (f true) + [1/2] (f false) ] *)

Notation "[1/2]" := (2%:~R)^-1.

Instance flip_mon :
  monotonic (fun (f : bool -> rat) => [1/2] * (f true) + [1/2] * (f false)).
Proof.
move=> f g Hfg.
apply Num.Theory.ler_add.
- rewrite (Num.Theory.ler_pmul2l (x:=2%:~R^-1) _ (f true) (g true)) //.
  exact: Hfg.
- rewrite (Num.Theory.ler_pmul2l (x:=2%:~R^-1) _ (f false) (g false)) //.
  exact: Hfg.
Qed.

Definition flip : M bool :=
  mon (fun (f : bool -> rat) => [1/2] * (f true) + [1/2] * (f false)).

Lemma flip_stable_sub : stable_sub flip.
Proof.
rewrite /flip /stable_sub => /= f g.
rewrite !mulrDr !mulrN [in RHS]opprD.
move: (2%:~R^-1 * f true) => ft.
move: (2%:~R^-1 * g true) => gt.
move: (2%:~R^-1 * f false) => ff.
move: (2%:~R^-1 * g false) => gf.
by ring_to_rat; ring.
Qed.

Lemma flip_prob : flip (fun x => 1) = 1.
Proof.
rewrite /flip /= !mulr1 -div1r addf_div //=.
rewrite mul1r -intrD -intrM.
exact: divrr.
Qed.

Lemma flip_true : flip (fun b => (b%:~R)) = [1/2].
Proof. by rewrite /flip /= mulr1 mulr0. Qed.

Lemma flip_false : flip (fun b => (~~b)%:~R) = [1/2].
Proof. by rewrite /flip /= mulr1 mulr0. Qed.

#[export] Hint Resolve flip_true flip_false : core.

Definition Flip : distr bool.
Proof.
exists flip; [exact: flip_stable_sub | exact: flip_prob].
Defined.

Lemma Flip_simpl f : mu Flip f = [1/2] * (f true) + [1/2] * (f false).
Proof. by []. Qed.


(** ** Finite distributions given by points and rational coefficients *)

Require Arith.

(* Local Open Scope rat_scope. *)

Section FiniteDistributions.

Variable A : Type.
Variable p : seq A.

(** We use a finite sequent of points, give a rational coefficient 
    to each point but only consider positive ones *)

Definition weight (c : A -> rat) : rat := \sum_(i <- p | 0 < c i) (c i).

Lemma weight_nonneg c : 0 <= weight c.
Proof using. by apply: Num.Theory.sumr_ge0; auto. Qed.
Hint Resolve weight_nonneg : core.

Lemma weight_case c : (weight c = 0) \/ 0 < (weight c)^-1.
Proof using.
have: ((weight c == 0) || (0 < weight c)).
  by rewrite -(Num.Theory.le0r (weight c)).
move=> /orP [/eqP ->|]; first by auto.
by rewrite Num.Theory.invr_gt0; auto.
Qed.


Instance finite_mon (c : A -> rat) :
  monotonic (fun f => (\sum_(i <- p | 0 < c i) (c i * f i)) / weight c).
Proof using.
move=> f g Hfg.
rewrite /Ole /=.
case (weight_case c) => [-> |Hci]; rat_to_ring.
- by rewrite invr0 mulr0 mulr0.
- rewrite (Num.Theory.ler_pmul2r Hci).
  apply Num.Theory.ler_sum => i Hi.
  rewrite (Num.Theory.ler_pmul2l Hi).
  exact: Hfg.
Qed.

Definition mfinite (c : A -> rat) : M A :=
  mon (fun f => (\sum_(i <- p | 0 < c i) (c i * f i))/weight c).

Lemma finite_simpl (c : A -> rat) f :
  mfinite c f = (\sum_(i <- p | 0 < c i) (c i * f i))/weight c.
Proof. by []. Qed.

Lemma finite_stable_sub (c : A -> rat) : stable_sub (mfinite c).
Proof using.
red => f g.
rewrite !finite_simpl.
case (weight_case c) => [->|Hci]; rat_to_ring.
- by rewrite invr0 !mulr0 subr0.
- rewrite -mulrBl.
  congr *%R.
  rewrite -sumrB.
  apply eq_bigr => i Hi.
  by rewrite mulrDr mulrN.
Qed.

End FiniteDistributions.

(** We have a distribution when the total weight is positive *)

Record fin (A : Type) : Type :=
  mkfin { points : seq A;
          coeff : A -> rat;
          weight_pos : 0 < weight points coeff
        }.
#[export] Hint Resolve weight_pos : core.

Lemma inv_weight_pos A (d : fin A) : 0 < (weight (points d) (coeff d))^-1.
Proof. by rewrite Num.Theory.invr_gt0. Qed.
#[export] Hint Resolve inv_weight_pos : core.

Lemma weight_is_unit A (d : fin A) : (weight (points d) (coeff d)) \is a unit.
Proof. by apply Num.Theory.unitf_gt0. Qed.
#[export] Hint Resolve weight_is_unit : core.

Definition fprob A (d : fin A) (a : A) : rat :=
  coeff d a / weight (points d) (coeff d).

Definition Finite A : fin A -> distr A.
Proof.
move=> d; exists (mfinite (points d) (coeff d)).
- by apply finite_stable_sub.
  rewrite finite_simpl -{2}(divrr (weight_is_unit d)).
  congr *%R.
  apply eq_bigr => i Hi.
  exact: mulr1.
Defined.

Lemma Finite_simpl A (d : fin A) :
  mu (Finite d) = mfinite (points d) (coeff d).
Proof. by []. Qed.


Lemma Finite_eq_in (A : eqType) (d : fin A) (a : A) :
  uniq (points d) -> (a \in points d)%SEQ -> 0 < coeff d a ->
  mu (Finite d) (fun x => (x==a)%:~R) = fprob d a.
Proof.
move => Hu Hain Hap.
rewrite Finite_simpl finite_simpl /fprob.
congr *%R.
rewrite -big_filter (bigD1_seq a) /=.
- rewrite (eq_refl a) mulr1.
  transitivity (coeff d a + 0)%R; last by rewrite addr0.
  congr +%R; apply big1 => i.
  by case (i == a); rewrite //= ?mulr0 ?addr0.
- by rewrite mem_filter Hain Hap.
- by rewrite filter_uniq.
Qed.


Lemma Finite_eq_out (A : eqType) (d : fin A) (a : A) :
  (a \notin points d)%SEQ \/ (coeff d a <= 0)%R ->
  mu (Finite d) (fun x => (x==a)%:~R) = 0.
Proof.
move => Ha.
rewrite Finite_simpl finite_simpl big1_seq ?mul0r // => i.
case (altP (i =P a)) => [-> /andP [H1 H2] | -].
- move: Ha => [| Hco]; first by case: (a \in points d) H2.
  by move: H1; rewrite ltrNge /= Hco.
- by rewrite mulr0.
Qed.

Lemma Finite_in_seq (A : eqType) (d : fin A) :
  mu (Finite d) (fun x => (x \in points d)%:~R) = 1%R.
Proof.
rewrite Finite_simpl finite_simpl.
rewrite -[in X in _ = X](divrr (weight_is_unit d)).
congr (_ / _).
rewrite /weight.
rewrite [in X in _ = X]big_seq_cond [in X in X = _]big_seq_cond.
apply eq_bigr => i.
case (i \in points d) => //=.
by rewrite mulr1.
Qed.

(** ** Uniform distribution on a non empty sequence of points *)

Record unif (A : Type) : Type :=
  mkunif { upoints :> seq A; _ : size upoints != O }.

Definition usize A (p : unif A) : nat := size (upoints p).

Lemma usize_pos A (p : unif A) : usize p != O.
Proof. by rewrite /usize; case p; case. Qed.

Definition unif2fin A (p:unif A) : fin A.
Proof.
exists (upoints p) (fun A => 1%:~R).
case: p; case => [|a s _] //=.
rewrite /weight big_cons /=.
apply ltr_le_trans with 1; first by [].
rewrite Num.Theory.ler_addl.
exact: weight_nonneg.
Defined.

Definition Uniform A (d : unif A) : distr A := Finite (unif2fin d).

Lemma Uniform_simpl A (d : unif A) :
  mu (Uniform d) = mfinite (upoints d) (fun A => 1%R).
Proof. by []. Qed.

Lemma weight1_size A (d : seq A) : weight d (fun x => 1) = (size d)%:~R.
Proof. by rewrite /weight -sum1_size sumMz. Qed.

Lemma mu_uniform_sum A (d : unif A) (f : A -> rat) :
  mu (Uniform d) f = (\sum_(i <- d) f i) / (size d)%:~R.
Proof.
rewrite Uniform_simpl /mfinite /= weight1_size.
congr (_ / _).
by apply eq_bigr => i _; apply mul1r.
Qed.

Lemma Uniform_eq_in (A : eqType) (d : unif A) (a : A) :
  uniq d -> (a \in upoints d)%SEQ ->
  mu (Uniform d) (fun x => (x==a)%:~R) = 1 / (usize d)%:~R.
Proof.
move => Hu Ha; rewrite /Uniform Finite_eq_in //.
rewrite /fprob /=.
by rat_to_ring; rewrite weight1_size.
Qed.

Lemma Uniform_eq_out (A : eqType) (d : unif A) (a : A) :
  (a \notin upoints d)%SEQ ->
  mu (Uniform d) (fun x => (x==a)%:~R) = 0%:~R.
Proof.
move => Ha; rewrite /Uniform Finite_eq_out //.
by left; exact Ha.
Qed.

Lemma Uniform_in_seq (A : eqType) (d : unif A) :
  mu (Uniform d) (fun x => (x \in upoints d)%:~R) = 1%:~R.
Proof. by rewrite /Uniform; apply Finite_in_seq. Qed.

Fact succ_neq0 (n m : nat) : (n==m.+1)%N -> (n!=0)%N.
Proof. by rewrite -lt0n => H; rewrite (eqP H). Qed.

Lemma Uniform_unif_seq_eq (A : eqType) (d1 d2 : unif A) :
  (d1 == d2 :> seq A) -> Uniform d1 == Uniform d2.
Proof.
move => Heq f.
rewrite 2!mu_uniform_sum.
by rewrite (eqP Heq).
Qed.

(** Uniform distribution on a sequence with a default value *)

Definition unif_def A (d : A) (s : seq A) : unif A.
Proof. by exists (if s is [::] then [::d] else s); case s. Defined.

Lemma Uniform_def_ne A (d : A) (s : seq A) :
  forall (Hs : (size s != 0)%N), Uniform (unif_def d s) = Uniform (mkunif s Hs).
Proof. by case s. Qed.

(** ** Uniform distribution between 0 and n included *)
Section UnifNat.

Implicit Types (n a : nat).

Definition unifnat n : unif nat := mkunif (iota 0 (n.+1)) (eq_refl true).
Definition Random n : distr nat := Uniform (unifnat n).

Lemma Random_simpl n : mu (Random n) = mfinite (iota 0 (n.+1)) (fun x => 1).
Proof. by []. Qed.

Lemma Random_eq_in n a :
  (a <= n)%N -> mu (Random n) (fun x => (x==a)%:~R) = 1 / (n.+1)%:~R.
Proof.
move => Han; rewrite /Random; rewrite Uniform_eq_in.
- by congr (_ / _); rewrite /usize size_iota.
- exact: iota_uniq.
- by rewrite mem_iota.
Qed.

Lemma Random_eq_out n a :
  (n < a)%N ->  mu (Random n) (fun x => (x==a)%:~R) = 0.
Proof.
move => Han; rewrite /Random; rewrite Uniform_eq_out //.
by rewrite mem_iota /= add0n -leqNgt.
Qed.

Lemma mu_random_sum n (f : nat -> rat) :
  mu (Random n) f = (\sum_(0 <= i < n.+1) f i) / (n.+1)%:~R.
Proof. by rewrite /Random mu_uniform_sum size_iota. Qed.

Lemma Random_in_range n :
  mu (Random n) (fun x => (x <= n)%N%:~R) = 1%:~R.
Proof.
rewrite /Random -[in X in _ = X](Uniform_in_seq _ (unifnat n)).
apply Mstable_eq; move => x /=.
congr natmul.
rewrite -[(0%N :: iota 1 n)]/(iota 0%N (n.+1)).
by rewrite mem_iota add0n.
Qed.

End UnifNat.

(* Local Close Scope rat_scope. *)


(** * Distribution and big sums *)

Unset Strict Implicit.

Lemma mu_stable_sum (A : Type) (m : distr A)
      (I : Type) (s : seq I) (f : I -> A -> rat) :
  mu m (fun a => \sum_(i <- s) f i a) = \sum_(i <- s) (mu m (f i)).
Proof.
elim: s => [| s0 s IHs] /=.
  by rewrite big_nil; apply mu_zero_eq => x; rewrite big_nil.
rewrite big_cons -IHs -mu_stable_add.
by apply Mstable_eq => x /=; rewrite big_cons.
Qed.


Section Bigsums.

Variable A : eqType.
Implicit Types (x : A) (s : seq A) (m : distr A).

Lemma in_seq_sum s x :
  uniq s -> (x \in s)%:~R = \sum_(i <- s) (x == i)%:~R :> rat.
Proof.
elim: s => [| s0 s IHs] /=; first by rewrite big_nil.
rewrite inE big_cons => /andP [/negbTE Hs0 /IHs <- {IHs}].
case: (boolP (x == s0)) => [/= /eqP -> | _ ]; last by rewrite /= add0r.
by rewrite Hs0 addr0.
Qed.

Lemma mu_in_seq m s :
  uniq s ->
  mu m (fun x => (x \in s)%:~R) = \sum_(a <- s) mu m (fun x => (x == a)%:~R).
Proof.
rewrite -mu_stable_sum => Hs.
apply Mstable_eq => x /=.
exact: in_seq_sum.
Qed.

Lemma mu_bool_cond m (f g : A -> bool) :
  mu m (fun x => (f x)%:~R) = 1 ->
  mu m (fun x => (g x)%:~R) = mu m (fun x => (f x && g x)%:~R).
Proof.
move=> H; apply ler_asym; apply/andP; split.
- rewrite -[X in (_ <= X)]addr0.
  have <- : (mu m) (fun x : A => (~~ f x && g x)%:~R) = 0.
    by move: H; apply mu_bool_negb0 => x; case: (f x).
  rewrite -Mstable_add //.
  apply mu_monotonic => x /=.
  by case: (f x); rewrite ?addr0 ?add0r.
- by apply mu_bool_impl => x; apply/implyP => /andP [].
Qed.

Lemma mu_pos_cond (m : distr A) (f : A -> bool) (g : A -> rat) :
  (forall x, 0 <= g x <= 1) ->
  mu m (fun x => (f x)%:~R) = 1 ->
  mu m (fun x => (g x)) = mu m (fun x => ((f x)%:~R * g x)).
Proof.
move=> Hg H.
have H0g x : 0 <= g x by have:= Hg x => /andP [].
have Hg1 x : g x <= 1 by have:= Hg x => /andP [].
apply ler_asym; apply/andP; split.
- rewrite -[X in (_ <= X)]addr0.
  have <- : (mu m) (fun x : A => ((~~ f x)%:~R * g x)) = 0.
    apply ler_asym; apply/andP; split.
    + rewrite -(subrr 1) -{3}H -mu_bool_negb.
      apply mu_monotonic => x /=.
      by case: (f x) => /=; rewrite ?mul0r ?mul1r.
    + apply mu_stable_pos => x /=.
      by case: (f x) => /=; rewrite ?mul0r ?mul1r.
  rewrite -Mstable_add //.
  apply mu_monotonic => x /=.
  by case: (f x); rewrite /= ?mul0r ?mul1r ?addr0 ?add0r.
- apply mu_monotonic => x /=.
  by case: (f x) => /=; rewrite ?mul0r ?mul1r.
Qed.

End Bigsums.
