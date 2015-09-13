
(** * Probas.v: The monad for distributions *)

Add Rec LoadPath "." as ALEA.

Require Export Monads.
(* Module Proba (Univ:Universe). *)
(* Module MP := (Monad Univ). *)
(* Import Univ MP UP. *)

(* begin hide *)
Set Implicit Arguments.
Open Local Scope U_scope.
Open Local Scope O_scope.
(* end hide *)

(** printing mu $\mu$ #&mu;# *)

(** ** Definition of distribution
Distributions are monotonic measure functions such that
    - [ mu (1-f) <= 1 - mu f ]
    - [ f <= 1 -g =>  mu (f+g) == mu f + mu g ]
    - [ mu (k * f) = k * mu (f) ]
    - [ mu (lub f_n) <= lub mu (f_n) ]
*)

Record distr (A:Type) : Type := 
  {mu : M A;
   mu_stable_inv : stable_inv mu; 
   mu_stable_plus : stable_plus mu;
   mu_stable_mult : stable_mult mu;
   mu_continuous : continuous mu}.

Hint Resolve mu_stable_plus mu_stable_inv mu_stable_mult mu_continuous.

(** ** Properties of measures *)

Lemma mu_monotonic : forall (A : Type)(m: distr A), monotonic (mu m).
intros; apply fmonotonic; auto.
Save.
Hint Resolve mu_monotonic.
Implicit Arguments mu_monotonic [A].

Lemma mu_stable_eq : forall (A : Type)(m: distr A), stable (mu m).
intros; apply fstable; auto.
Save.
Hint Resolve mu_stable_eq.
Implicit Arguments mu_stable_eq [A].

Lemma mu_zero : forall (A : Type)(m: distr A), mu m (fzero A) == 0.
intros.
transitivity (mu m (fmult 0 (fzero A))); auto.
transitivity (0 * (mu m (fzero A))); auto.
apply mu_stable_mult; auto.
Save.
Hint Resolve mu_zero.

Lemma mu_zero_eq : forall (A : Type)(m: distr A) f, 
   (forall x, f x == 0) -> mu m f == 0.
intros; transitivity (mu m (fzero A)); auto.
Save.

Lemma mu_one_inv : forall (A : Type)(m:distr A),
   mu m (fone A) == 1 -> forall f, mu m (finv f) == [1-] (mu m f).
intros; apply Ole_antisym.
apply (mu_stable_inv m f).
apply Uplus_le_simpl_left with (mu m f); auto.
setoid_rewrite (Uinv_opp_right (mu m f)).
transitivity (mu m (fun x => (f x) + [1-] (f x))).
setoid_rewrite <- H; apply (mu_monotonic m); intro x; simpl; auto.
assert (H1 : fplusok f (finv f)).
red; unfold finv; intro x; auto.
setoid_rewrite <- (mu_stable_plus m H1); auto.
Save.
Hint Resolve mu_one_inv.

Lemma mu_fplusok : forall (A : Type)(m:distr A) f g, fplusok f g -> 
            mu m f <= [1-] mu m g.
intros; transitivity (mu m (finv g)); auto.
apply (mu_stable_inv m g).
Save.
Hint Resolve mu_fplusok.

Lemma mu_le_minus : forall (A : Type)(m:distr A) (f g:MF A),
     mu m (fminus f g) <= mu m f.
intros; apply mu_monotonic; intro x; unfold fminus; auto.
Save.
Hint Resolve mu_le_minus.

Lemma mu_le_plus : forall (A : Type)(m:distr A) (f g:MF A),
     mu m (fplus f g) <= mu m f + mu m g.
auto.
Save.
Hint Resolve mu_le_plus.

Lemma mu_eq_plus : forall (A : Type)(m:distr A) (f g:MF A),
     fplusok f g -> mu m (fplus f g) == mu m f + mu m g.
intros; rewrite mu_stable_plus; auto.
Save.
Hint Resolve mu_eq_plus.

Lemma mu_plus_zero : forall (A : Type)(m:distr A) (f g:MF A),
   mu m f == 0 -> mu m g == 0 -> mu m (fplus f g) == 0.
intros; apply Ule_zero_eq.
transitivity (mu m f + mu m g); auto.
rewrite H,H0; auto.
Save.
Hint Resolve mu_plus_zero.

Lemma mu_plus_pos : forall (A : Type)(m:distr A) (f g:MF A),
   0 < mu m (fplus f g) -> orc (0 < mu m f) (0 < mu m g). 
intros; apply (Ueq_orc 0 (mu m f)); intros; auto.
apply orc_right.
apply Ult_neq_zero.
intro Hg; destruct H as (H1,H2); apply H2; auto.
symmetry; auto.
Save.

Lemma mu_fcte : forall (A : Type)(m:(distr A)) (c:U),
   mu m (fcte A c) == c * mu m (fone A).
intros.
transitivity (mu m (fun x => c * 1)).
apply (mu_stable_eq m); intro x; auto.
unfold fone; rewrite <- (mu_stable_mult m c (fun x => 1)); auto.
Save.
Hint Resolve mu_fcte.

Lemma mu_fcte_le :   forall (A : Type)(m:distr A) (c:U), mu m (fcte A c) <= c.
intros; transitivity (c * mu m (fone A)); auto.
Save.


Lemma mu_fcte_eq : forall (A : Type)(m:distr A) (c:U),
   mu m (fone A) == 1 -> mu m (fcte A c) == c.
intros; transitivity (c * mu m (fone A)); auto.
Save.

Hint Resolve mu_fcte_le mu_fcte_eq.

Lemma mu_cte : forall (A : Type)(m:(distr A)) (c:U),
   mu m (fun _ => c) == c * mu m (fone A).
exact mu_fcte.
Save.
Hint Resolve mu_cte.

Lemma mu_cte_le :   forall (A : Type)(m:distr A) (c:U), mu m (fun _ => c) <= c.
exact mu_fcte_le.
Save.

Lemma mu_cte_eq : forall (A : Type)(m:distr A) (c:U),
   mu m (fone A) == 1 -> mu m (fun _ => c) == c.
exact mu_fcte_eq.
Save.
Hint Resolve mu_cte_le mu_cte_eq.

Lemma mu_stable_mult_right : forall (A : Type)(m:distr A) (c:U) (f : MF A),
   mu m (fun x => (f x) * c) == (mu m f) * c.
intros; transitivity 
   (mu m (fun x => c * (f x))).
apply mu_stable_eq; intro x; auto.
transitivity (c * mu m f); auto.
exact (mu_stable_mult m c f).
Save.

Lemma mu_stable_minus : forall (A:Type) (m:distr A)(f g : MF A),
 g <= f -> mu m (fun x => f x - g x) == mu m f - mu m g.
intros; change (mu m (fminus f g) == mu m f - mu m g).
apply (stable_minus_distr (m:=mu m)); auto.
Save.

Lemma mu_inv_minus : 
forall (A:Type) (m:distr A)(f: MF A), mu m (finv f) == mu m (fone A) - mu m f.
intros; transitivity (mu m (fun x => fone A x - f x)).
apply (mu_stable_eq m); intro x; unfold finv,fone; intros; auto.
apply mu_stable_minus; auto.
Save.


Lemma mu_stable_le_minus : forall (A:Type) (m:distr A)(f g : MF A),
 mu m f - mu m g <= mu m (fun x => f x - g x).
intros; apply Uplus_le_perm_left.
transitivity (mu m (fun x => g x + (f x - g x))).
apply mu_monotonic; intro x; auto.
apply (mu_le_plus m g (fun x => f x - g x)).
Save.

Lemma mu_inv_minus_inv : forall (A:Type) (m:distr A)(f: MF A), 
     mu m (finv f) + [1-](mu m (fone A)) == [1-](mu m f).
intros; apply Uminus_eq_perm_right.
apply Uinv_le_compat.
apply (mu_monotonic m); unfold fone; auto.
unfold Uminus.
rewrite mu_inv_minus; repeat Usimpl.
unfold Uminus.
apply Uinv_eq_compat; auto.
Save.

Lemma mu_le_esp_inv : forall (A:Type) (m:distr A)(f g : MF A),
 ([1-]mu m (finv f)) & mu m g <= mu m (fesp f g).
intros; rewrite Uesp_sym.
apply Uplus_inv_le_esp; Usimpl.
transitivity (mu m (fplus (fesp f g) (finv f))); auto.
apply (mu_monotonic m); unfold fplus, fesp,finv; intro x.
rewrite Uesp_sym; auto.
Save.
Hint Resolve mu_le_esp_inv.

Lemma mu_stable_inv_inv : forall (A:Type) (m:distr A)(f : MF A),
             mu m f <= [1-] mu m (finv f).
intros; transitivity (mu m (finv (finv f))).
apply (mu_monotonic m); auto.
apply (mu_stable_inv m); auto.
Save.
Hint Resolve  mu_stable_inv_inv.

Lemma mu_stable_div : forall (A:Type) (m:distr A)(k:U)(f : MF A),
          ~ 0==k -> f <= fcte A k -> mu m (fdiv k f) == mu m f / k.
intros; apply Umult_div_eq; auto.
rewrite Umult_sym.
rewrite <- (mu_stable_mult m k).
apply mu_stable_eq; intro x.
unfold fmult,fdiv; apply Umult_div; auto.
apply (H0 x).
Save.

Lemma mu_stable_div_le : forall (A:Type) (m:distr A)(k:U)(f : MF A),
          ~ 0==k -> mu m (fdiv k f) <= mu m f / k.
intros; apply Umult_div_le_left; auto.
rewrite Umult_sym.
rewrite <- (mu_stable_mult m k).
apply mu_monotonic; intro x.
unfold fmult,fdiv; apply Umult_div_le; auto.
Save.

Lemma mu_le_esp : forall (A:Type) (m:distr A)(f g : MF A),
 mu m f & mu m g <= mu m (fesp f g).
intros; transitivity (([1-]mu m (finv f)) & mu m g); auto.
Save.
Hint Resolve mu_le_esp.

Lemma mu_esp_one : forall (A:Type)(m:distr A)(f g:MF A),
   1 <= mu m f -> mu m g == mu m (fesp f g).
intros; apply Ole_antisym.
transitivity (mu m f & mu m g).
transitivity (1 & mu m g); auto.
apply mu_le_esp with (f:=f) (g:=g).
apply mu_monotonic; unfold fesp;  intro x; auto.
Save.

Lemma mu_esp_zero : forall (A:Type)(m:distr A)(f g:MF A),
   mu m (finv f) <= 0 -> mu m g == mu m (fesp f g).
intros; apply Ole_antisym.
transitivity (([1-](mu m (finv f))) & mu m g); auto.
transitivity (1 & mu m g); auto.
apply Uesp_le_compat; auto.
transitivity ([1-]0); auto.
apply mu_monotonic; unfold fesp;  intro x; auto.
Save.

(* Lemma suited for rewriting. *)
Lemma mu_stable_mult2: 
  forall (A : Type) (d : distr A), forall (k : U)
  (f : MF A), (mu d) (fun x => k * f x) == k * (mu d) f.
  intros A0 d k f.
  replace (fun x => k * f x) with (fmult k f).
  setoid_rewrite mu_stable_mult;trivial.
  trivial.
Qed.

(* Lemma suited for rewriting. *)
Lemma mu_stable_plus2: 
  forall (A : Type) (d : distr A) (f g: MF A),
    fplusok f g -> (mu d) (fun x => f x + g x) == (mu d) f + (mu d) g.
  intros A d f g H.
  replace (fun x => f x + g x) with (fplus f g).
  setoid_rewrite mu_stable_plus;auto.
  trivial.
Qed.

(* Lemma suited for rewriting. *)
Lemma mu_fzero_eq : forall A m, @mu A m (fun x => 0) == 0.
Proof.
  intros A m.
  setoid_rewrite mu_zero_eq;auto.
Qed.

Lemma fplusok_plus_esp : forall (A : Type) (f g : MF A),
      fplusok f (fminus g (fesp f g)).
intros; intro x; unfold fplus,fminus,fesp,finv,Uminus,Uesp; repeat Usimpl; auto.
rewrite Uplus_sym; rewrite <- Uinv_plus_right_le; auto.
Save.
Hint Resolve fplusok_plus_esp.

Lemma mu_eq_plus_esp : 
forall (A : Type) (m : distr A) (f g : MF A),
  mu m (fplus f g) == mu m f + (mu m g - (mu m (fesp f g))).
intros; transitivity (mu m (fplus f (fminus g (fesp f g)))); auto.
apply mu_stable_eq; intro x; unfold fplus, fminus, fesp; auto.
rewrite mu_stable_plus; auto.
Save.
Hint Resolve mu_eq_plus_esp.

Instance Odistr (A:Type) : ord (distr A) := 
    {Ole := fun (f g : distr A) => mu f <= mu g;
     Oeq := fun (f g : distr A) => mu f == mu g}.
split; intuition.
intros f g h; transitivity (mu g); auto.
Defined.

(** Probability of termination *)

Definition pone A (m:distr A) := mu m (fone A).

Add Parametric Morphism A : (pone (A:=A) )
    with signature Oeq ==> Oeq as pone_eq_compat.
intros; unfold pone; auto.
Save.
Hint Resolve pone_eq_compat.


(** ** Monadic operators for distributions *)
Definition Munit : forall A:Type, A -> distr A.
intros A x.
exists (unit x).
apply unit_stable_inv.
apply unit_stable_plus.
apply unit_stable_mult.
apply unit_continuous.
Defined.

Definition Mlet : forall A B:Type, distr A -> (A -> distr B) -> distr B.
intros A B mA mB.
exists (star (mu mA) (fun x => (mu (mB x)))).
apply star_stable_inv; auto.
apply star_stable_plus; auto.
apply star_stable_mult; auto.
apply star_continuous; auto.
Defined.

Lemma Munit_simpl : forall (A:Type) (q:A -> U) x, mu (Munit x) q = q x.
trivial.
Save.

Lemma Munit_simpl_eq : forall (A:Type) (q:A -> U) x, mu (Munit x) q == q x.
trivial.
Save.

Lemma Mlet_simpl : forall (A B:Type) (m:distr A) (M:A -> distr B) (f:B -> U),
     mu (Mlet m M) f = mu m (fun x => (mu (M x) f)).
trivial.
Save.

Lemma Mlet_simpl_eq : forall (A B:Type) (m:distr A) (M:A -> distr B) (f:B -> U),
     mu (Mlet m M) f == mu m (fun x => (mu (M x) f)).
trivial.
Save.


(** ** Operations on distributions *)


Lemma Munit_eq_compat : forall A (x y : A), x = y -> Munit x == Munit y.
intros; subst; auto.
Save.

Lemma Mlet_le_compat : forall (A B : Type) (m1 m2:distr A) (M1 M2 : A -> distr B), 
  m1 <= m2 -> M1 <= M2 -> Mlet m1 M1 <= Mlet m2 M2.
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

Lemma MLet_simpl : forall (A B:Type) (m:distr A) (M:A -> distr B)(f:B -> U),
     mu (MLet A B m M) f = mu m (fun x => mu (M x) f).
trivial.
Save.

Lemma Mlet_eq_compat : forall (A B : Type) (m1 m2:distr A) (M1 M2 : A -> distr B), 
  m1 == m2 -> M1==M2 -> Mlet m1 M1 == Mlet m2 M2.
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
  m1 <= m2 -> forall f g : A -> U,  f <= g -> mu m1 f <= mu m2 g.
intros; transitivity (mu m2 f); auto.
Save.

Lemma mu_eq_compat : forall (A:Type) (m1 m2:distr A),
  m1 == m2 -> forall f g : A -> U,  f == g -> mu m1 f == mu m2 g.
intros; transitivity (mu m2 f); auto.
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
  with signature (@pointwise_relation A U (@eq _) ==> Oeq) as mu_distr_eq_morphism.
intros f g H1.
apply mu_eq_compat; auto.
Save.

(* Utile *)
Add Parametric Morphism (A:Type) (a:distr A) : (@mu A a)
  with signature (@pointwise_relation A U (@Oeq _ _) ==> Oeq) as mu_distr_Oeq_morphism.
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
Lemma Mlet_unit : forall (A B:Type) (x:A) (m:A -> distr B), Mlet (Munit x) m == m x.
intros; intro f; auto.
Save.

Lemma Mlet_ext : forall (A:Type) (m:distr A), Mlet m (fun x => Munit x) == m.
intros;  intro f.
rewrite Mlet_simpl.
apply (mu_stable_eq m).
intro x; auto.
Save.

Lemma Mlet_assoc : forall (A B C:Type) (m1: distr A) (m2:A -> distr B) (m3:B -> distr C),
     Mlet (Mlet m1 m2) m3 == Mlet m1 (fun x:A => Mlet (m2 x) m3).
intros;  intro f; simpl; trivial.
Save.

Lemma let_indep : forall (A B:Type) (m1:distr A) (m2: distr B) (f:MF B), 
       mu m1 (fun _ => mu m2 f) == pone m1 * (mu m2 f).
intros; rewrite (mu_cte m1 (mu m2 f)); auto.
Save.


(** ** A specific distribution *)
Definition distr_null : forall A : Type, distr A.
intro A; exists (mon (cte (MF A) (0:U))); try red; auto.
Defined.

Lemma le_distr_null : forall (A:Type) (m : distr A), distr_null A <= m.
red; intros.
unfold distr_null; simpl; auto.
Save.
Hint Resolve le_distr_null.

(** ** Scaling a distribution *)

Definition Mmult A (k:MF A) (m:M A) : M A.
intros;  exists (fun f => m (fun x => k x * f x)).
red; intros.
apply fmonotonic; intro z; auto.
Defined.

Lemma Mmult_simpl : forall A (k:MF A) (m:M A) f, Mmult k m f = m (fun x => k x * f x).
trivial.
Save.

Lemma Mmult_stable_inv : forall A (k:MF A) (d:distr A), stable_inv (Mmult k (mu d)).
red; intros; simpl.
transitivity (mu d (finv f)); auto.
Save.

Lemma Mmult_stable_plus : forall A (k:MF A) (d:distr A), stable_plus (Mmult k (mu d)).
red; intros; simpl.
transitivity (mu d (fun x => k x * f x + k x * g x)).
apply (mu_stable_eq d).
simpl; intro x; unfold fplus.
apply Udistr_plus_left; apply (H x).
apply (mu_stable_plus d (f:=fun x=> k x * f x) (g:=fun x => k x * g x)).
intro x; transitivity (f x); auto.
transitivity (finv g x); auto.
unfold finv; repeat Usimpl; auto.
Save.

Lemma Mmult_stable_mult : forall A (k:MF A) (d:distr A), stable_mult (Mmult k (mu d)).
red; intros; simpl.
transitivity (mu d  (fmult k0 (fun x : A => k x * f x))).
apply (mu_stable_eq d).
intro x; unfold fmult; auto.
apply (mu_stable_mult d).
Save.

Lemma Mmult_continuous : forall A (k:MF A) (d:distr A), continuous (Mmult k (mu d)).
red; intros; rewrite Mmult_simpl.
transitivity (mu d (fun (x:A) => lub (UMult (k x) @ (h <o> x)))).
apply (mu_monotonic d); intros x; auto.
rewrite (MF_lub_simpl h); auto.
transitivity (mu d (lub (ishift (fun x : A => (UMult (k x) @ h <o> x)))));auto.
apply (mu_monotonic d); intro x; trivial.
rewrite (MF_lub_simpl (ishift (fun x0 : A => UMult (k x0) @ h <o> x0))); 
apply lub_le_compat; intro n; simpl; auto.
rewrite (mu_continuous d (ishift (fun x => UMult (k x) @ h <o> x))).
apply lub_le_compat; intro n; simpl; auto.
Save.

Definition distr_mult A (k:MF A) (d:distr A) : distr A.
intros; exists (Mmult k (mu d)).
apply Mmult_stable_inv.
apply Mmult_stable_plus.
apply Mmult_stable_mult.
apply Mmult_continuous.
Defined.

Lemma distr_mult_assoc : forall A (k1 k2:MF A) (d:distr A), 
             distr_mult k1 (distr_mult k2 d) == distr_mult (fun x => k1 x * k2 x) d.
intros; intro f; simpl.
apply mu_eq_compat; trivial.
intro x.
rewrite Umult_assoc.
rewrite (Umult_sym (k2 x) (k1 x)); auto.
Save.

Add Parametric Morphism (A B : Type) : (distr_mult (A:=A)) 
     with signature Oeq ==> Oeq ==> Oeq
as distr_mult_eq_compat.
intros; intro f; simpl; apply mu_eq_compat; auto.
Save.

(** Scaling with a constant functions *)

Definition distr_scale A (k:U) (d:distr A) : distr A := distr_mult (fcte A k) d.

Lemma distr_scale_assoc : forall A (k1 k2:U) (d:distr A), 
             distr_scale k1 (distr_scale k2 d) == distr_scale (k1*k2) d.
unfold distr_scale; intros.
rewrite distr_mult_assoc.
apply distr_mult_eq_compat; auto.
Save.

Lemma distr_scale_simpl : forall  A (k:U) (d:distr A)(f:MF A), 
       mu (distr_scale k d) f == k * mu d f.
intros; simpl; rewrite (mu_stable_mult d k f); auto.
Save.

Add Parametric Morphism A : (distr_scale (A:=A)) 
with signature Oeq ==> Oeq ==> Oeq 
as distr_scale_eq_compat.
intros; intro f; repeat rewrite distr_scale_simpl.
auto.
Save.
Hint Resolve distr_scale_eq_compat.

Lemma distr_scale_one : forall A  (d:distr A), distr_scale 1 d == d.
intros; intro f; rewrite distr_scale_simpl; auto.
Save.

Lemma distr_scale_zero : forall A  (d:distr A), distr_scale 0 d == distr_null A.
intros; intro f; rewrite distr_scale_simpl; auto.
Save.

Hint Resolve distr_scale_simpl distr_scale_assoc distr_scale_one distr_scale_zero.


Lemma let_indep_distr : forall (A B:Type) (m1:distr A) (m2: distr B), 
       Mlet m1 (fun _ => m2) == distr_scale (pone m1) m2.
intros; intro f; simpl.
rewrite let_indep.
unfold fcte; rewrite (mu_stable_mult m2 (pone m1) f); trivial.
Save.

Definition Mdiv A (k:U) (m:M A) : M A := UDiv k @ m.

Lemma Mdiv_simpl : forall A k (m:M A) f, Mdiv k m f = m f / k.
trivial.
Save.

Lemma Mdiv_stable_inv : forall A (k:U) (d:distr A)(dk : mu d (fone A) <= k),
                stable_inv (Mdiv k (mu d)).
red; intros; repeat rewrite Mdiv_simpl.
apply (Ueq_orc 0 k); auto; intros.
repeat (rewrite Udiv_by_zero;auto).
assert (forall f, mu d f <= k).
intros; transitivity (mu d (fone A)); auto.
transitivity ((mu d (fone A) - mu d f) / k); auto.
Save.

Lemma Mdiv_stable_plus : forall A (k:U)(d:distr A), stable_plus (Mdiv k (mu d)).
red; intros; repeat rewrite Mdiv_simpl.
transitivity ((mu d f + mu d g)/k); auto.
Save.

Lemma Mdiv_stable_mult : forall A (k:U)(d:distr A)(dk : mu d (fone A) <= k), 
                          stable_mult (Mdiv k (mu d)).
red; intros; repeat rewrite Mdiv_simpl.
apply (Ueq_orc 0 k); auto; intros.
repeat (rewrite Udiv_by_zero;auto).
assert (forall f, mu d f <= k).
intros; transitivity (mu d (fone A)); auto.
transitivity ((k0 * mu d f) / k); auto.
apply Udiv_eq_compat_left; auto.
apply (mu_stable_mult d); trivial.
apply Umult_div_assoc; auto. 
Save.

Lemma Mdiv_continuous : forall A (k:U)(d:distr A), continuous (Mdiv k (mu d)).
red; intros; repeat rewrite Mdiv_simpl.
transitivity (lub (mu d @ h) / k); auto.
transitivity (lub (UDiv k @ (mu d @ h))).
exact (Udiv_continuous k (mu d @ h)).
apply lub_le_compat; intro n; auto.
Save.

Definition distr_div A (k:U) (d:distr A) (dk : mu d (fone A) <= k)
              : distr A.
intros.
exists (Mdiv k (mu d)).
apply Mdiv_stable_inv; auto.
apply Mdiv_stable_plus.
apply Mdiv_stable_mult; auto.
apply Mdiv_continuous.
Defined.

Lemma distr_div_simpl : forall A (k:U) (d:distr A) (dk : mu d (fone A) <= k) f, 
     mu (distr_div _ _ dk) f = mu d f / k.
trivial.
Save.

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

(** ** Least upper bound of increasing sequences of distributions *)

Lemma M_lub_simpl : forall A (h: nat -m> M A) (f:MF A),
     lub h f = lub (mshift h f).
trivial.
Save.

Section Lubs.
Variable A : Type.

Definition Mu : distr A -m> M A.
exists (mu (A:=A)); auto.
Defined.

Lemma Mu_simpl : forall d f, Mu d f = mu d f.
trivial.
Save.

Variable muf : nat -m> distr A.

Definition mu_lub: distr A.
exists (lub (Mu @ muf)).

red; intros; simpl; apply lub_inv; intros; simpl.
apply (mu_stable_inv (muf n)).

red; intros.
transitivity (lub ((UPlus @2 (mshift (Mu @ muf) f)) (mshift (Mu @ muf) g))); auto.
rewrite (M_lub_simpl (Mu @ muf) (fplus f g)).
apply lub_eq_compat; intro n; simpl; auto.
(*exact (mu_stable_plus (muf n) H); auto.*)
rewrite <- (lub_cont2_app2_eq UPlus); auto.

red; intros; simpl.
transitivity (lub (UMult k @ (mshift (Mu @ muf) f))); auto.
apply lub_eq_compat; auto.
intro n; simpl; exact (mu_stable_mult (muf n) k f); auto.

unfold M; apply lub_continuous; intros.
apply (mu_continuous (muf n)).
Defined.

Lemma mu_lub_le : forall n:nat, muf n <= mu_lub.
simpl; intros.
apply (le_lub (mshift (Mu @ muf) x) n).
Save.

Lemma mu_lub_sup : forall m: distr A, (forall n:nat, muf n <= m) -> mu_lub <= m.
simpl; intros.
apply lub_le; simpl; intros; auto.
Save.

End Lubs.
Hint Resolve mu_lub_le mu_lub_sup.

(** *** Distributions seen as a Ccpo *)

Instance cdistr (A:Type) : cpo (distr A) :=
   {D0 := distr_null A; lub:=mu_lub (A:=A)}.
auto.
auto.
auto.
Defined.

Lemma distr_lub_simpl : forall A (h : nat -m> distr A) (f:MF A),
      mu (lub h) f = lub (mshift (Mu A @ h) f).
trivial.
Save.
Hint Resolve distr_lub_simpl. 

(** ** Fixpoints *)

Definition Mfix (A B:Type) (F: (A -> distr B) -m> (A -> distr B))
    : A -> distr B := fixp F.

Definition MFix (A B:Type) : ((A -> distr B) -m> (A -> distr B)) -m> (A -> distr B) 
           := Fixp (A -> distr B).

Lemma Mfix_le : forall  (A B:Type) (F: (A -> distr B) -m> (A -> distr B)) (x:A),
            Mfix F x <= F (Mfix F) x.
intros; unfold Mfix; apply (fixp_le F x).
Save.

Lemma Mfix_eq : forall  (A B:Type) (F: (A -> distr B) -m> (A -> distr B)), 
continuous F -> forall (x:A),  Mfix F x == F (Mfix F) x.
intros A B F H; unfold Mfix.
exact (fixp_eq F).
Save.

Hint Resolve Mfix_le Mfix_eq.

Lemma Mfix_le_compat : forall (A B:Type) (F G : (A -> distr B)-m> (A -> distr B)),
        F <= G -> Mfix F <= Mfix G.
intros; unfold Mfix; auto.
Save.

Definition Miter  (A B:Type) := Ccpo.iter (D:=A -> distr B).

Lemma Mfix_le_iter : forall  (A B:Type) (F:(A -> distr B) -m> (A -> distr B)) (n:nat),
      Miter F n <= Mfix F.
unfold Miter,Mfix,fixp; auto.
Save.

(** ** Continuity *)

Section Continuity.

Variables A B:Type.

Instance Mlet_continuous_right 
    : forall a:distr A, continuous (D1:= A -> distr B) (D2:=distr B) (MLet A B a).
red; intros; intro f.
rewrite (MLet_simpl (A:=A) (B:=B)).
transitivity (mu a (fun x : A => lub (mshift (Mu B @ h <o> x) f)));auto.
transitivity (mu a (lub (ishift (fun x:A => mshift (Mu B @ (h <o> x)) f)))).
apply (mu_monotonic a); intro x; auto.
(* pierre: Top. needed here? *)
rewrite fcpo_lub_simpl; apply lub_le_compat; intro; auto.
rewrite (mu_continuous a).
rewrite distr_lub_simpl; apply lub_le_compat; intro n; simpl; auto.
Save.

Lemma Mlet_continuous_left 
    : continuous (D1:=distr A) (D2:=(A -> distr B) -m> distr B) (MLet A B).
red; intros; intro F; intro f.
rewrite (MLet_simpl (A:=A) (B:=B)).
simpl; auto.
Save.

Hint Resolve Mlet_continuous_right Mlet_continuous_left.

Lemma Mlet_continuous2 : continuous2 (D1:=distr A) (D2:= A->distr B) (D3:=distr B) (MLet A B).
intros; apply continuous_continuous2; auto.
Save.
Hint Resolve Mlet_continuous2.


Lemma Mlet_lub_le : forall (mun:nat -m> distr A) (Mn : nat -m> (A -> distr B)),
            Mlet (lub mun) (lub Mn) <= lub ((MLet A B @2 mun) Mn).
intros; apply Mlet_continuous2 with (f:=mun) (g:=Mn).
Save.

Lemma Mlet_lub_le_left : forall (mun:nat -m> distr A) 
           (M : A -> distr B),
            Mlet (lub mun) M <= lub (mshift (MLet A B @ mun) M).
intros.
apply (Mlet_continuous_left mun M).
Save.

Lemma Mlet_lub_le_right : forall (m:distr A) 
           (Mun : nat -m> (A -> distr B)),
            Mlet m (lub Mun) <= lub ((MLet A B m)@Mun).
intros.
apply (Mlet_continuous_right m Mun).
Save.

Lemma Mlet_lub_fun_le_right : forall (m:distr A) 
           (Mun : A -> nat -m> distr B),
            Mlet m (fun x => lub (Mun x)) <= lub ((MLet A B m)@(ishift Mun)).
intros.
rewrite <- lub_ishift.
apply Mlet_lub_le_right.
Save.

Lemma Mfix_continuous : 
     forall (Fn : nat -m> (A -> distr B) -m> (A -> distr B)),
     (forall n, continuous (Fn n)) -> 
      Mfix (lub Fn) <= lub (MFix A B @ Fn).
unfold Mfix, MFix; intros; apply fixp_continuous; auto.
Save.

End Continuity.

(** ** Exact probability : probability of full space is 1 *)

Class Term A (m:distr A) := term_def : mu m (fone A) == 1.
Hint Resolve @term_def.

Lemma Mlet_indep_term : forall A B (d1:distr A) (d2:distr B) {T:Term d1},
            Mlet d1 (fun _ => d2) == d2.
intros; intro f; simpl.
rewrite  let_indep; unfold pone; rewrite T; auto.
Save.
Hint Resolve Mlet_indep_term.

Lemma mu_stable_inv_term : forall A (d:distr A) {T:Term d} f, mu d (finv f) == [1-](mu d f).
intros; apply mu_one_inv; auto.
Save.

Instance Munit_term : forall A (a:A), Term (Munit a).
red; unfold fone; auto.
Save.
Hint Resolve Munit_term.

Instance Mlet_term : forall A B (d1:distr A) (d2: A -> distr B)
   {T1:Term d1} {T2:forall x, Term (d2 x)}, Term (Mlet d1 d2).
red; unfold fone; intros; simpl.
transitivity (mu d1 (fone _)); auto.
Save.
Hint Resolve Mlet_term.

Lemma fplusok_mu_term : forall (A B:Type) (d:distr B) (f f':A -> MF B) {T:Term d},
  (forall x:A, fplusok (f x) (f' x)) -> 
  fplusok  (fun x : A => mu d (f x))  (fun x : A => mu d (f' x)).
Proof.
  intros A0 B d f f' hok htotal.
  unfold fplusok,finv.
  intro x.
  unfold fun_ext, finv.
  setoid_rewrite <- mu_one_inv.
  apply mu_le_compat; auto.
  apply htotal.
  apply hok.
Qed.

(** ** distribution for [flip]
The distribution associated to [flip ()] is 
       [f --> [1/2] (f true) + [1/2] (f false) ] *)

Definition flip : M bool := mon (fun (f : bool -> U) => [1/2] * (f true) + [1/2] * (f false)).

Lemma flip_stable_inv : stable_inv flip.
unfold flip, stable_inv, finv; intro f; simpl; auto.
Save.

Lemma flip_stable_plus : stable_plus flip.
unfold flip, stable_plus, fplus; intros; simpl.
rewrite (Udistr_plus_left [1/2] _ _ (H true)).
rewrite (Udistr_plus_left [1/2] _ _ (H false)).
repeat norm_assoc_right.
apply Uplus_eq_compat_right.
repeat norm_assoc_left; apply Uplus_eq_compat_left; auto.
Save.

Lemma flip_stable_mult : stable_mult flip.
unfold flip, stable_mult, fmult; intros; simpl.
assert (H:([1/2]* f true) <= ([1-] ([1/2]* f false))); auto.
rewrite (Udistr_plus_left k _ _ H); auto.
Save.

Lemma flip_continuous : continuous flip.
unfold continuous; intros.
unfold flip; rewrite mon_simpl.
repeat rewrite MF_lub_simpl.
do 2 rewrite <- lub_eq_mult.
rewrite <- lub_eq_plus.
apply lub_le_compat; intro n; auto.
Save.

Lemma flip_true : flip B2U == [1/2].
unfold flip, B2U; simpl.
setoid_rewrite (Umult_one_right [1/2]).
setoid_rewrite (Umult_zero_right [1/2]); auto.
Save.

Lemma flip_false : flip NB2U == [1/2].
unfold flip, NB2U; simpl.
setoid_rewrite (Umult_one_right [1/2]).
setoid_rewrite (Umult_zero_right [1/2]); auto.
Save.

Hint Resolve flip_true flip_false.

Definition Flip  : distr bool.
exists flip.
apply flip_stable_inv.
apply flip_stable_plus.
apply flip_stable_mult.
apply flip_continuous.
Defined.

Lemma Flip_simpl : forall f, mu Flip f = [1/2] * (f true) + [1/2] * (f false).
trivial.
Save.

Instance flip_term : Term Flip.
red; rewrite Flip_simpl; unfold fone; Usimpl; auto.
Save.
Hint Resolve flip_term.

(** ** Uniform distribution beween 0 and n *)
Require Arith.

(** *** Definition of [fnth]
        [fnth n k] is defined as [ [1/]1+n ] *)

Definition fnth (n:nat) : nat -> U := fun k => [1/]1+n.           

(** *** Basic properties of [fnth] *)


Lemma Unth_eq : forall n, Unth n == [1-] (sigma (fnth n) n).
intro; exact (Unth_prop n).
Save.
Hint Resolve Unth_eq.

Lemma sigma_fnth_one : forall n, sigma (fnth n) (S n) == 1.
intros; rewrite sigma_S.
unfold fnth at 1.
rewrite (Unth_eq n); auto.
Save.
Hint Resolve sigma_fnth_one.

Lemma Unth_inv_eq : forall n, [1-] ([1/]1+n) == sigma (fnth n) n.
intro; setoid_rewrite (Unth_eq n); auto.
Save.

Lemma sigma_fnth_sup : forall n m, (m > n) -> sigma (fnth n) m == sigma (fnth n) (S n).
intros.
assert ((S n) <= m)%nat; auto with arith.
elim H0; intros; auto.
rewrite sigma_S; auto.
setoid_rewrite H2.
assert (m0 > n); auto with arith.
setoid_rewrite (sigma_fnth_one n); auto.
Save.


Lemma sigma_fnth_le : forall n m, (sigma (fnth n) m) <= (sigma (fnth n) (S n)).
intros; setoid_rewrite (sigma_fnth_one n); auto.
Save.

Hint Resolve sigma_fnth_le.

(** [fnth] is a retract *)
Lemma fnth_retract : forall n:nat,(retract (fnth n) (S n)).
red; intros.
unfold fnth at 1.
transitivity ([1-] (sigma (fnth n) n)); auto with arith.
Save.

Implicit Arguments fnth_retract [].

(** ** Distributions and general summations *)

Definition sigma_fun A (f:nat -> MF A) (n:nat) : MF A := fun x => sigma (fun k => f k x) n.
Definition serie_fun A (f:nat -> MF A) : MF A := fun x => serie (fun k => f k x).

Definition Sigma_fun A (f:nat -> MF A) : nat -m> MF A := 
              ishift (fun x => Sigma (fun k => f k x)).

Lemma Sigma_fun_simpl : forall A (f:nat -> MF A) (n:nat),
    Sigma_fun f n = sigma_fun f n.
trivial.
Save.

Lemma serie_fun_lub_sigma_fun : forall A (f:nat -> MF A), 
     serie_fun f == lub (Sigma_fun f).
intros; unfold serie_fun.
simpl; intro x.
unfold serie; apply lub_eq_compat.
simpl; intro n; trivial.
Save.
Hint Resolve serie_fun_lub_sigma_fun.

Lemma sigma_fun_0 : forall A (f:nat -> MF A), sigma_fun f 0 == fzero A.
intros; unfold fzero; intro x; auto.
Save.

Lemma sigma_fun_S : forall A (f:nat->MF A) (n:nat), 
      sigma_fun f (S n) == fplus (f n) (sigma_fun f n).
intros; unfold fplus; intro x; auto.
Save.


Lemma mu_sigma_le : forall A (d:distr A) (f:nat -> MF A) (n:nat), 
      mu d (sigma_fun f n) <= sigma (fun k => mu d (f k)) n.
induction n; intros.
rewrite sigma_0; transitivity (mu d (fzero A)); auto.
rewrite sigma_S; transitivity (mu d (fplus (f n) (sigma_fun f n))).
auto.
transitivity (mu d (f n) + mu d (sigma_fun f n)); auto.
Save.

Lemma retract_fplusok : forall A (f:nat -> MF A) (n:nat), 
     (forall x, retract (fun k => f k x) n) -> 
     forall k, (k < n)%nat -> fplusok (f k) (sigma_fun f k).
red; intros; intro x.
apply (H x k); auto.
Save.


Lemma mu_sigma_eq : forall A (d:distr A) (f:nat -> MF A) (n:nat), 
     (forall x, retract (fun k => f k x) n) -> 
      mu d (sigma_fun f n) == sigma (fun k => mu d (f k)) n.
induction n; intros.
rewrite sigma_0; transitivity (mu d (fzero A)); auto.
rewrite sigma_S; transitivity (mu d (fplus (f n) (sigma_fun f n))).
auto.
transitivity (mu d (f n) + mu d (sigma_fun f n)); auto.
apply (mu_stable_plus d).
apply retract_fplusok with (S n); auto.
Save.


Lemma mu_serie_le : forall A (d:distr A) (f:nat -> MF A), 
      mu d (serie_fun f) <= serie (fun k => mu d (f k)).
intros; transitivity (mu d (lub (Sigma_fun f))).
apply mu_monotonic; rewrite (serie_fun_lub_sigma_fun f); trivial.
transitivity (lub (mu d @ (Sigma_fun f))).
apply (mu_continuous d).
unfold serie; apply lub_le_compat; intro n.
rewrite comp_simpl.
exact (mu_sigma_le d f n).
Save.

Lemma mu_serie_eq : forall A (d:distr A) (f:nat -> MF A), 
     (forall x, wretract (fun k => f k x)) -> 
      mu d (serie_fun f) == serie (fun k => mu d (f k)).
intros; transitivity (mu d (lub (Sigma_fun f))).
apply mu_stable_eq; apply (serie_fun_lub_sigma_fun f); trivial.
transitivity (lub (mu d @ (Sigma_fun f))).
apply (lub_comp_eq (mu d)).
apply (mu_continuous d).
unfold serie; apply lub_eq_compat; intro n.
rewrite comp_simpl.
apply (mu_sigma_eq d f (n:=n)).
red; intros.
apply (H x k).
Save.

Lemma wretract_fplusok : forall A (f:nat -> MF A), 
     (forall x, wretract (fun k => f k x)) -> 
     forall k, fplusok (f k) (sigma_fun f k).
red; intros; intro x.
apply (H x k); auto.
Save.


(** ** Discrete distributions *)

Instance discrete_mon : forall A (c : nat -> U) (p : nat -> A),
     monotonic (fun f : A -> U => serie (fun k => c k * f (p k))).
red; intros; auto.
Save.

Definition discrete A (c : nat -> U) (p : nat -> A) : M A := 
       mon (fun f : A -> U => serie (fun k => c k * f (p k))).

Lemma discrete_simpl : forall A (c : nat -> U) (p : nat -> A) f, 
     discrete c p f = serie (fun k => c k * f (p k)).
trivial.
Save.

Lemma discrete_stable_inv : forall A (c : nat -> U) (p : nat -> A), 
    wretract c -> stable_inv (discrete c p).
red; intros.
repeat rewrite discrete_simpl.
unfold finv; apply serie_inv_le; auto.
Save.

Lemma discrete_stable_plus : forall A (c : nat -> U) (p : nat -> A), 
    stable_plus (discrete c p).
red; intros.
repeat rewrite discrete_simpl.
transitivity (serie (fun k : nat => c k * f (p k) + c k * g (p k))).
apply serie_eq_compat.
intros; unfold fplus.
apply Udistr_plus_left.
apply (H (p k)).
apply serie_plus; auto.
Save.

Lemma discrete_stable_mult : forall A (c : nat -> U) (p : nat -> A), 
    wretract c -> stable_mult (discrete c p).
red; intros.
repeat rewrite discrete_simpl; unfold fmult.
transitivity (serie (fun k0 : nat => k * (c k0 * f (p k0)))); auto. 
apply serie_mult.
apply wretract_le with c; auto.
Save.

Lemma discrete_continuous : forall A (c : nat -> U) (p : nat -> A), 
    continuous (discrete c p).
red; intros.
rewrite discrete_simpl.
transitivity 
(serie (lub (ishift (fun k => (UMult (c k) @ (h <o> (p k))))))).
apply serie_le_compat; intro k.
repeat rewrite fcpo_lub_simpl.
rewrite (UMult_continuous_right (c k) (h <o> p k)).
apply lub_le_compat; intro n; auto.
rewrite (serie_continuous (ishift (fun k : nat => UMult (c k) @ h <o> p k))).
apply lub_le_compat; intro n; auto.
Save.

Record discr (A:Type) : Type := 
     {coeff : nat -> U; coeff_retr : wretract coeff; points : nat -> A}.
Hint Resolve coeff_retr.

Definition Discrete : forall A,  discr A -> distr A.
intros A d ; exists (discrete (coeff d) (points d)).
apply discrete_stable_inv; trivial.
apply discrete_stable_plus.
apply discrete_stable_mult; trivial.
apply discrete_continuous.
Defined.

Lemma Discrete_simpl : forall A (d:discr A), 
     mu (Discrete d) = discrete (coeff d) (points d).
trivial.
Save.

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

(** ** Tacticals *)

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


(* End Proba. *)
