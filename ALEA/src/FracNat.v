(** * Frac.v : lemmas about rational numbers in U *)

(* begin hide *)
Add Rec LoadPath "." as ALEA.
Require Export Uprop.
Set Implicit Arguments.
Open Local Scope U_scope.
(* end hide *)

Definition frac n p := Nmult n (Unth (pred p)).

Infix "[/]" := frac (left associativity, at level 40) : U_scope.

Lemma frac_le_compat_left : forall n m p, (n<=m)%nat -> n [/] p <= m [/] p.
intros; unfold frac; auto.
Save.
Hint Resolve frac_le_compat_left.

Lemma frac_le_compat_right : forall n p q, (q <= p)%nat -> n [/] p <= n [/] q.
intros; unfold frac; auto.
Save.
Hint Resolve frac_le_compat_right.

Add Morphism frac with signature eq ==> eq ==> Oeq as frac_eq_compat.
auto.
Qed.
Hint Immediate frac_eq_compat.

Add Morphism frac with signature le ==> le --> Ole as frac_le_compat.
intros; transitivity (y[/]x0); auto.
Qed.
Hint Immediate frac_le_compat.

Lemma frac_eq_simpl : forall n, (0<n)%nat -> n [/] n == 1.
unfold frac; auto.
Save.
Hint Resolve frac_eq_simpl.

Lemma frac_ge_simpl : forall n p, (0<n)%nat -> (p <= n)%nat -> n [/] p == 1.
intros; apply Uge_one_eq; transitivity (n[/]n); auto.
rewrite frac_eq_simpl; auto.
Save.
Hint Resolve frac_ge_simpl.

Lemma frac_0_den : forall n, (0<n)%nat -> n [/] 0 == 1.
intros; apply frac_ge_simpl; auto with arith.
Save.
Hint Resolve frac_0_den.

Lemma frac_1_den : forall n, (0<n)%nat -> n [/] 1 == 1.
intros; apply frac_ge_simpl; auto.
Save.
Hint Resolve frac_1_den.

Lemma frac_1_num : forall n, 1 [/] n == [1/]n.
intros; unfold frac; auto.
Save.
Hint Resolve frac_1_num.

Lemma frac_le : forall n m p q, (0<q)%nat -> (n*q <= m*p)%nat -> n [/] p <= m [/] q.
intros; apply Nmult_Unth_le.
rewrite <- S_pred with (n:=q) (m:=O); auto.
transitivity (m*p)%nat; auto.
apply mult_le_compat_l; omega.
Save.

Hint Resolve frac_le.

Lemma frac_eq : forall n m p q, (0<p)%nat -> (0<q)%nat -> (n*q = m*p)%nat -> n [/] p == m [/] q.
intros; apply Ole_antisym; apply frac_le; auto.
rewrite H1; reflexivity.
rewrite H1; reflexivity.
Save.


Lemma frac_lt_succ : forall n p, (n < p)%nat -> n [/] p < (S n) [/] p.
intros; unfold frac; rewrite Nmult_S.
apply Ole_lt_trans with (0 + (n */ [1/]p)); auto.
Save.
Hint Resolve frac_lt_succ.


Lemma frac_lt_compat_left : forall n m p, (n<m)%nat -> (n<p)%nat -> n [/] p < m [/] p.
intros; apply Olt_le_trans with (S n [/]p); auto.
Save.
Hint Resolve frac_lt_compat_left.

Lemma frac_lt1 : forall  n p, (n < p)%nat -> n [/] p < 1.
intros; apply Olt_le_trans with (p[/]p); auto.
Save.
Hint Resolve frac_lt1.

Lemma frac_0_num : forall p, 0 [/] p == 0.
auto.
Save.

Lemma frac_0_num_elim : forall n p, n[/]p == 0 -> (n = 0)%nat.
intros; destruct (NPeano.Nat.eq_0_gt_0_cases n); auto.
assert (0 < n[/]p).
apply Olt_le_trans with (1[/]p).
rewrite frac_1_num; auto.
apply frac_le_compat_left; auto.
absurd (0 < n[/]p); auto.
Save.

Lemma frac_non_eq0 : forall n p, (0<n)%nat -> ~ 0 == n[/]p.
red; intros.
absurd (n=0)%nat.
red; intros; absurd (0 < n)%nat; omega.
apply frac_0_num_elim with p; auto.
Save.
Hint Resolve frac_non_eq0.

Lemma frac_pos : forall n p, (0<n)%nat -> 0 < n[/]p.
intros; apply Ult_neq_zero; auto.
Save.
Hint Resolve frac_pos.

Lemma frac_plus : forall n m p, n [/] p + m [/] p == (n+m) [/] p.
unfold frac; intros; symmetry; auto.
Save.
Hint Resolve frac_plus.


Lemma frac_nmult : forall n m p, n */ (m [/] p) == (n*m) [/] p.
unfold frac; intros; symmetry; auto.
Save.
Hint Resolve frac_nmult.

Lemma frac_inv : forall n p, (0<p)%nat -> [1-] (n [/] p) == (p-n) [/] p.
unfold frac; intros.
rewrite Uinv_Nmult; auto.
rewrite <- S_pred with (m:=O); auto.
Save.
Hint Resolve frac_inv.

Lemma frac_minus : forall n m p, (0<p)%nat -> (n <= p)%nat 
      -> n [/] p - m [/] p == (n-m) [/] p.
intros; destruct (NPeano.Nat.le_ge_cases n m) as [Hnm|Hnm].
assert (n[/]p <= m[/]p); auto.
rewrite Uminus_le_zero; auto.
replace (n-m)%nat with 0%nat; auto.
symmetry; rewrite NPeano.Nat.sub_0_le; auto.
apply Uplus_eq_perm_left.
rewrite frac_inv; auto.
apply frac_le_compat_left; auto.
replace (p - (n - m))%nat with (m+(p-n))%nat; omega.
rewrite frac_plus; intuition.
Save.
Hint Resolve frac_minus.





Lemma frac_mult : forall n m p q, (n<=p)%nat -> (m<=q)%nat
           -> (n [/] p) * (m [/] q) == (n*m) [/] (p*q).
unfold frac; intros.
(* degenerate case n=0 *)
destruct (NPeano.Nat.eq_0_gt_0_cases n).
subst n; repeat Usimpl; auto.
(* degenerate case m=0 *)
destruct (NPeano.Nat.eq_0_gt_0_cases m).
subst m; rewrite NPeano.Nat.mul_0_r; repeat Usimpl; auto.
(* normal case *)
rewrite  <- mult_Nmult_Umult; auto with zarith.
apply Nmult_eq_compat; auto.
rewrite Umult_Unthp; intuition.
Save.
Hint Resolve frac_mult.

Lemma frac_simpl_r : forall n m p, (0<m)%nat -> (0<p)%nat 
       -> (n*m) [/] (p*m) == n [/] p.
intros; apply Nmult_Unth_eq.
repeat (rewrite <- S_pred with (m:=O)); auto.
ring.
apply NPeano.Nat.mul_pos_pos; trivial.
Save.
Hint Resolve frac_simpl_r.

Lemma frac_simpl_l : forall n m p, (0<m)%nat -> (0<p)%nat 
       -> (m*n) [/] (m*p) == n [/] p.
intros; apply Nmult_Unth_eq.
repeat (rewrite <- S_pred with (m:=O)); auto.
ring.
apply NPeano.Nat.mul_pos_pos; trivial.
Save.
Hint Resolve frac_simpl_l.

Lemma frac_simpl_rl : forall n m p, (0<m)%nat -> (0<p)%nat 
       -> (n*m) [/] (m*p) == n [/] p.
intros; rewrite NPeano.Nat.mul_comm; auto.
Save.
Hint Resolve frac_simpl_rl.

Lemma frac_simpl_lr : forall n m p, (0<m)%nat -> (0<p)%nat 
       -> (m*n) [/] (p*m) == n [/] p.
intros; rewrite NPeano.Nat.mul_comm; auto.
Save.
Hint Resolve frac_simpl_lr.

Lemma frac_plus_gen : forall n m p q r s, (0 < p)%nat -> (0 < r)%nat
      -> (p * r = q * s)%nat 
      -> (n [/] p) + (m [/] q) == (n * r + m * s) [/] (p * r).
intros; assert (0 < q /\ 0 < s)%nat.
rewrite <- NPeano.Nat.lt_0_mul'.
rewrite <- H1; rewrite NPeano.Nat.lt_0_mul'; auto.
destruct H2.
rewrite <- frac_simpl_r with (n:=n) (p:=p) (m:= r); auto.
rewrite <- frac_simpl_r with (n:=m) (p:=q) (m:= s); auto.
rewrite <- H1; auto.
Save.

Lemma frac_minus_gen : forall n m p q r s, (0 < p)%nat -> (0 < r)%nat
      -> (p * r = q * s)%nat -> (n <= p)%nat
      -> (n [/] p) - (m [/] q) == (n * r - m * s) [/] (p * r).
intros; assert (0 < q /\ 0 < s)%nat as (Hq,Hs).
rewrite <- NPeano.Nat.lt_0_mul'.
rewrite <- H1; rewrite NPeano.Nat.lt_0_mul'; auto.
rewrite <- frac_simpl_r with (n:=n) (p:=p) (m:= r); auto.
rewrite <- frac_simpl_r with (n:=m) (p:=q) (m:= s); auto.
rewrite <- H1; auto.
apply frac_minus; intuition.
apply NPeano.Nat.mul_pos_pos; auto.
apply NPeano.Nat.mul_le_mono_nonneg_r; intuition.
Save.


Lemma frac_lt : forall n m p q, (0<q)%nat -> (n*q < m*p)%nat -> (n<p)%nat
      -> n [/] p < m [/] q.
intros; assert (0<m*p)%nat.
apply le_lt_trans with (n*q)%nat; auto with arith.
assert (0<m /\ 0<p)%nat as (Hm,Hp).
rewrite <- NPeano.Nat.lt_0_mul'; auto.
destruct (NPeano.Nat.le_ge_cases m q) as [Hmq|Hmq].
apply Uminus_lt0_intro; auto.
rewrite frac_minus_gen with (r:=p) (s:=q); auto.
apply frac_pos; auto.
rewrite <- NPeano.Nat.neq_0_lt_0.
apply NPeano.Nat.sub_gt; auto.
ring.
rewrite frac_ge_simpl with (n:=m); auto.
Save.

Lemma frac_plus_mult : forall n m p q, (0 < p)%nat -> (0 < q)%nat
      -> (n [/] p) + (m [/] q) == (n * q + m * p) [/] (p * q).
intros; apply frac_plus_gen; auto.
apply NPeano.Nat.mul_comm.
Save.

Lemma frac_div : forall n m p q, (0<m)%nat -> (n <= p)%nat -> (m <= q)%nat
      -> (n [/] p) / (m [/] q) == (n*q) [/] (m*p).
intros; destruct (NPeano.Nat.eq_0_gt_0_cases n).
subst n; repeat Usimpl; auto.
assert (0<p/\0<q)%nat as (Hp,Hq); try omega.
destruct (NPeano.Nat.le_ge_cases (m*p) (n*q)).
rewrite frac_ge_simpl with (n:=(n*q)%nat); auto.
rewrite NPeano.Nat.lt_0_mul'; auto.
(* non degenerate case *)
symmetry; apply Umult_div_eq; auto.
rewrite frac_mult; auto.
assert (0 < q * m)%nat.
rewrite NPeano.Nat.lt_0_mul'; auto.
transitivity ((n * (q * m))[/](p * (q * m))); auto.
apply frac_eq_compat; ring.
Save.
Hint Resolve frac_div.

Lemma nmult_frac_right : forall n p x, (n <= p)%nat -> Nmult_def p x
       -> (p */ x) * (n [/] p) == n */ x.
intros.
destruct (NPeano.Nat.eq_0_gt_0_cases n) as [Hn|Hn].
subst; repeat Usimpl; auto.
assert (Nmult_def n x).
apply Nmult_def_le_compat_left with p; auto.
assert (0<p)%nat.
apply lt_le_trans with n; auto.
rewrite <- Nmult_Umult_assoc_left; auto.
rewrite Umult_sym.
unfold frac; rewrite <- Nmult_Umult_assoc_left; auto.
rewrite Nmult_Umult_assoc_right with (n:=n); auto.
rewrite Nmult_Umult_assoc_left; auto.
Save.
Hint Resolve nmult_frac_right.

Lemma Udiv_frac_right : forall n p x, (x <= (n [/] p)) -> (n <= p)%nat 
       -> x / (n [/] p) == p */ (x * [1/]n).
(** introduce a few extra conditions on arguments *)
intros; apply (Ule_orc x 0); intros; auto.
assert (Hx:x==0); auto.
rewrite Hx; repeat Usimpl; auto.
assert (Hx:0<x); auto.
destruct (NPeano.Nat.eq_0_gt_0_cases n).
destruct H1.
replace 0 with (n[/]p); subst; auto.
assert (Hp:(0<p)%nat).
apply lt_le_trans with n; auto.
assert (Hmd:Nmult_def p (x * [1/]n)); auto.
apply Nmult_def_introp.
apply Nmult_le_simpl with (pred n); auto.
rewrite <- S_pred with (m:=O); auto.
rewrite Nmult_Umult_assoc_right; auto.
rewrite Nmult_n_Unthp; repeat Usimpl; auto.
(** main case *)
symmetry; apply Umult_div_eq; auto.
rewrite nmult_frac_right; auto.
rewrite Nmult_Umult_assoc_right; auto.
Save.

(*
Require Import Euclid.

(** get n/p = m/q + r/qp with r < p *)
Definition approx_div n p hp q := eucl_dev p hp (n * q) .

Lemma approx_eucl_eq : forall n p q (hp:(0<p)%nat), (0<q)%nat 
      -> match approx_div n hp q with (divex m r _ _) => n[/]p==m[/]q + r[/](p*q) end.
intros; unfold approx_div.
destruct (eucl_dev p hp (n * q)).
transitivity ((n*q)[/](p*q)).
rewrite frac_simpl_r; auto.
rewrite e.
rewrite <- frac_plus.
Usimpl.
replace (q0*p)%nat with (p*q0)%nat; auto with arith.
Save.

Lemma approx_eucl_spec : forall n p q (hp:(0<p)%nat), 
   (n<=p)%nat -> (0<q)%nat 
  -> let (m,r,_,_):= approx_div n hp q in 
     n[/]p==m[/]q + r[/](p*q) /\ (r[/](p*q) < [1/]q).
intros n p q Hle Hp Hq.
unfold approx_div in *.
destruct (NPeano.Nat.eq_0_gt_0_cases n) as [Hn|Hn].
subst; simpl; auto.
assert (Hp1:(p<>0)%nat).
omega.
assert (Hm:=mod_lt (n * q) p Hp1).
unfold modulo in Hm; destruct (div_eucl (n * q) p).
simpl in Hm.
split; auto.
apply Olt_le_trans with (p[/](p * q)); auto.
apply frac_lt_compat_left; auto.
apply lt_le_trans with p; auto.
transitivity (p * 1)%nat.
rewrite mul_1_r; reflexivity.
apply mul_le_mono_l; auto.
rewrite <- (mul_1_r p) at 1.
rewrite frac_simpl_l; auto.
Save.

Definition approx_down n p q := let (m,r):= approx_div n p q in m[/]q.

Definition approx_near n p q := let (m,r):= approx_div n p q in
    match (r+r ?= p)%nat with Gt => (m+1)[/]q | _ => m [/] q end.

Lemma approx_down_inf : forall n p q, (0<p)%nat -> (0<q)%nat 
      -> approx_down n p q <= n[/]p.
unfold approx_down; intros n p q Hp Hq.
assert (Hs:=approx_eucl_eq n Hp Hq).
destruct (approx_div n p q).
rewrite Hs; auto.
Save.


Lemma approx_down_sup : forall n p q, (n<p)%nat -> (0<p)%nat -> (0<q)%nat 
      -> n[/]p < approx_down n p q + [1/]q.
unfold approx_down; intros n p q Hnp Hp Hq.
assert (Hnp1:(n <= p)%nat).
red; rewrite Hnp; discriminate.
assert (Hs:=approx_eucl_spec Hnp1 Hp Hq).
destruct (approx_div n p q).
destruct Hs.
rewrite H.
apply Uplus_lt_compat_r; auto.
rewrite <- H; auto.
Save.

Lemma approx_near_spec : forall n p q, (n<=p)%nat -> (0<p)%nat -> (0<q)%nat 
      -> diff (n[/]p) (approx_near n p q) <= 1[/](2*q).
intros n p q Hnp Hp Hq.
assert (0<2*q)%nat.
apply lt_le_trans with q; auto.
transitivity (1*q)%nat.
ring_simplify; reflexivity.
apply mul_le_mono_nonneg_r; auto.
Nineq.
assert (0<p*q)%nat.
rewrite lt_0_mul'; auto.
(* starting proof *)
unfold approx_near; assert (Hs:=approx_eucl_spec Hnp Hp Hq).
destruct (approx_div n p q).
destruct Hs as (Heq,Hinf).
rewrite Heq.
destruct (le_gt_cases (n1+n1) p) as [Hc|Hc].
(* Case 2n1 <= p *)
transitivity (diff (n0[/]q + n1[/](p * q)) (n0[/]q)).
red in Hc; destruct (n1 + n1 ?= p)%nat; auto.
contradiction Hc; trivial.
rewrite diff_sym.
rewrite diff_Uminus; auto.
transitivity (n1[/](p * q)); auto.
apply frac_le; auto.
ring_simplify.
transitivity (q * (n1+n1))%nat; auto.
ring_simplify; reflexivity.
apply mul_le_mono_nonneg_l; auto.
(** case (p < 2n1)%nat *)
assert (n1 <= p)%nat.
rewrite <- nlt_ge; intro.
absurd (1[/]q < 1[/]q); auto.
apply Ole_lt_trans with (n1[/](p * q)).
apply frac_le; auto.
rewrite mul_1_l.
apply mul_le_mono_nonneg_r; auto.
apply lt_le_incl; auto.
rewrite frac_1_num;auto.

rewrite <- gt_lt_iff in Hc.
rewrite Hc.
rewrite diff_Uminus; auto.
transitivity (1[/]q - n1[/](p * q)).
rewrite <- frac_plus.
rewrite <- Uminus_assoc_left.
rewrite Uplus_sym; auto.
rewrite <- frac_simpl_l with (m:=p); auto.
rewrite frac_minus; auto.
rewrite mul_1_r.
apply frac_le; auto.
ring_simplify.
rewrite (mul_comm q p).
apply mul_le_mono_r; auto.
transitivity ((p - n1) + (p-n1))%nat.
ring_simplify; reflexivity.
transitivity ((p - n1) + n1)%nat.
rewrite <-  add_le_mono_l.
rewrite le_sub_le_add_r.
apply lt_le_incl.
apply gt_lt; trivial.
rewrite sub_add; auto.
reflexivity.
apply mul_le_mono_l; auto.
rewrite <- frac_plus; auto.
rewrite frac_1_num.
apply Uplus_le_compat_right; auto.
Save.

*)







 