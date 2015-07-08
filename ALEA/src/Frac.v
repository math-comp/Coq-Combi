(** * Frac.v : lemmas about rational numbers in U *)

(* begin hide *)
Add Rec LoadPath "." as ALEA.
Require Export Uprop.
Set Implicit Arguments.
Open Local Scope U_scope.
(* end hide *)

Definition nfrac n p := nmult n (Nnth (N.pred p)).

Infix "[/]" := nfrac (left associativity, at level 40) : U_scope.

Lemma nfrac_le_compat_left : forall n m p, (n<=m)%N -> n [/] p <= m [/] p.
intros; unfold nfrac; auto.
Save.
Hint Resolve nfrac_le_compat_left.

Lemma nfrac_le_compat_right : forall n p q, (q <= p)%N -> n [/] p <= n [/] q.
intros; unfold nfrac; auto.
Save.
Hint Resolve nfrac_le_compat_right.

Add Morphism nfrac with signature eq ==> eq ==> Oeq as nfrac_eq_compat.
auto.
Qed.
Hint Immediate nfrac_eq_compat.

Add Morphism nfrac with signature N.le ==> N.le --> Ole as nfrac_le_compat.
intros; transitivity (y[/]x0); auto.
Qed.
Hint Immediate nfrac_le_compat.

Lemma nfrac_eq_simpl : forall n, (0<n)%N -> n [/] n == 1.
unfold nfrac; auto.
Save.
Hint Resolve nfrac_eq_simpl.

Lemma nfrac_ge_simpl : forall n p, (0<n)%N -> (p <= n)%N -> n [/] p == 1.
intros; apply Uge_one_eq; transitivity (n[/]n); auto.
rewrite nfrac_eq_simpl; auto.
Save.
Hint Resolve nfrac_ge_simpl.

Lemma nfrac_0_den : forall n, (0<n)%N -> n [/] 0 == 1.
intros; apply nfrac_ge_simpl; auto.
Save.
Hint Resolve nfrac_0_den.

Lemma nfrac_1_den : forall n, (0<n)%N -> n [/] 1 == 1.
intros; apply nfrac_ge_simpl; auto.
Save.
Hint Resolve nfrac_1_den.

Lemma nfrac_1_num : forall n, 1 [/] n == [1|]n.
intros; unfold nfrac; auto.
Save.
Hint Resolve nfrac_1_num.

Lemma nfrac_le : forall n m p q, (0<q)%N -> (n*q <= m*p)%N -> n [/] p <= m [/] q.
intros; apply nmult_Nnth_le.
rewrite Nsucc_pred_pos with (n:=q); auto.
transitivity (m*p)%N; auto.
apply N.mul_le_mono_l; auto.
apply N.le_pred_le_succ; reflexivity.
Save.

Hint Resolve nfrac_le.

Lemma nfrac_eq : forall n m p q, (0<p)%N -> (0<q)%N -> (n*q = m*p)%N -> n [/] p == m [/] q.
intros; apply Ole_antisym; apply nfrac_le; auto.
rewrite H1; reflexivity.
rewrite H1; reflexivity.
Save.


Lemma nfrac_lt_succ : forall n p, (n < p)%N -> n [/] p < (N.succ n) [/] p.
intros; unfold nfrac; rewrite nmult_S.
apply Ole_lt_trans with (0 + (n *\ [1|]p)); auto.
apply Uplus_lt_compat_left_lt; auto.
Usimpl.
destruct (Neq_lt_0 n) as [Hn|Hn].
subst n; simpl; auto.
apply Olt_le_trans with (n *\ [1|]n); auto.
apply nmult_def_lt_compat; auto.
unfold Nnth; apply Unth_decr.
apply N2Nat_lt_mono.
rewrite <- N.pred_lt_mono; auto.
intro; subst; discriminate.
Save.
Hint Resolve nfrac_lt_succ.


Lemma nfrac_lt_compat_left : forall n m p, (n<m)%N -> (n<p)%N -> n [/] p < m [/] p.
intros; apply Olt_le_trans with (N.succ n [/]p); auto.
apply nfrac_le_compat_left; auto.
rewrite N.le_succ_l; auto.
Save.
Hint Resolve nfrac_lt_compat_left.

Lemma nfrac_lt1 : forall  n p, (n < p)%N -> n [/] p < 1.
intros; apply Olt_le_trans with (p[/]p); auto.
Save.
Hint Resolve nfrac_lt1.

Lemma nfrac_0_num : forall p, 0 [/] p == 0.
auto.
Save.

Lemma nfrac_0_num_elim : forall n p, n[/]p == 0 -> (n = 0)%N.
intros; destruct (Neq_lt_0 n); auto.
assert (0 < n[/]p).
apply Olt_le_trans with (1[/]p).
rewrite nfrac_1_num; auto.
apply nfrac_le_compat_left; auto.
absurd (0 < n[/]p); auto.
Save.

Lemma nfrac_non_eq0 : forall n p, (0<n)%N -> ~ 0 == n[/]p.
red; intros.
absurd (n=0)%N.
red; intros; absurd (0 < n)%N; auto.
rewrite H1; discriminate.
apply nfrac_0_num_elim with p; auto.
Save.
Hint Resolve nfrac_non_eq0.

Lemma nfrac_pos : forall n p, (0<n)%N -> 0 < n[/]p.
intros; apply Ult_neq_zero; auto.
Save.
Hint Resolve nfrac_pos.

Lemma nfrac_plus : forall n m p, n [/] p + m [/] p == (n+m) [/] p.
unfold nfrac; intros; symmetry; auto.
Save.
Hint Resolve nfrac_plus.


Lemma nfrac_nmult : forall n m p, n *\ (m [/] p) == (n*m) [/] p.
unfold nfrac; intros; symmetry; auto.
Save.
Hint Resolve nfrac_nmult.

Lemma nfrac_inv : forall n p, (0<p)%N -> [1-] (n [/] p) == (p-n) [/] p.
unfold nfrac; intros.
rewrite Uinv_nmult; auto.
rewrite Nsucc_pred_pos; auto.
Save.
Hint Resolve nfrac_inv.

Lemma nfrac_minus : forall n m p, (0<p)%N -> (n <= p)%N 
      -> n [/] p - m [/] p == (n-m) [/] p.
intros; destruct (N.le_ge_cases n m) as [Hnm|Hnm].
assert (n[/]p <= m[/]p); auto.
rewrite Uminus_le_zero; auto.
replace (n-m)%N with 0%N; auto.
symmetry; rewrite N.sub_0_le; auto.
apply Uplus_eq_perm_left.
rewrite nfrac_inv; auto.
apply nfrac_le_compat_left; auto.
replace (p - (n - m))%N with (m+(p-n))%N.
rewrite <- (N.add_0_r m) at 1.
apply N.add_le_mono_l; auto.
symmetry; apply N.add_sub_eq_r.
rewrite N.add_comm.
rewrite N.add_assoc.
rewrite N.sub_add; auto.
rewrite N.add_sub_assoc; auto.
rewrite N.add_comm.
rewrite N.add_sub; auto.
rewrite nfrac_plus.
rewrite N.add_sub_assoc; auto.
rewrite N.add_comm.
rewrite N.add_sub; auto.
Save.
Hint Resolve nfrac_minus.





Lemma nfrac_mult : forall n m p q, (n<=p)%N -> (m<=q)%N
           -> (n [/] p) * (m [/] q) == (n*m) [/] (p*q).
unfold nfrac; intros.
(* degenerate case n=0 *)
destruct (Neq_lt_0 n).
subst n; repeat Usimpl; auto.
(* degenerate case m=0 *)
destruct (Neq_lt_0 m).
subst m; rewrite N.mul_0_r; repeat Usimpl; auto.
(* normal case *)
rewrite  <- mult_nmult_Umult; auto.
apply nmult_eq_compat; auto.
rewrite Umult_Nnthp; auto.
apply N.lt_le_trans with n; auto.
apply N.lt_le_trans with m; auto.
Save.
Hint Resolve nfrac_mult.

Lemma nfrac_simpl_r : forall n m p, (0<m)%N -> (0<p)%N 
       -> (n*m) [/] (p*m) == n [/] p.
intros; apply nmult_Nnth_eq.
repeat (rewrite Nsucc_pred_pos); auto.
ring.
apply N.mul_pos_pos; trivial.
Save.
Hint Resolve nfrac_simpl_r.

Lemma nfrac_simpl_l : forall n m p, (0<m)%N -> (0<p)%N 
       -> (m*n) [/] (m*p) == n [/] p.
intros; apply nmult_Nnth_eq.
repeat (rewrite Nsucc_pred_pos); auto.
ring.
apply N.mul_pos_pos; trivial.
Save.
Hint Resolve nfrac_simpl_l.

Lemma nfrac_simpl_rl : forall n m p, (0<m)%N -> (0<p)%N 
       -> (n*m) [/] (m*p) == n [/] p.
intros; rewrite N.mul_comm; auto.
Save.
Hint Resolve nfrac_simpl_rl.

Lemma nfrac_simpl_lr : forall n m p, (0<m)%N -> (0<p)%N 
       -> (m*n) [/] (p*m) == n [/] p.
intros; rewrite N.mul_comm; auto.
Save.
Hint Resolve nfrac_simpl_lr.

Lemma nfrac_plus_gen : forall n m p q r s, (0 < p)%N -> (0 < r)%N
      -> (p * r = q * s)%N 
      -> (n [/] p) + (m [/] q) == (n * r + m * s) [/] (p * r).
intros; assert (0 < q /\ 0 < s)%N.
rewrite <- N.lt_0_mul'.
rewrite <- H1; rewrite N.lt_0_mul'; auto.
destruct H2.
rewrite <- nfrac_simpl_r with (n:=n) (p:=p) (m:= r); auto.
rewrite <- nfrac_simpl_r with (n:=m) (p:=q) (m:= s); auto.
rewrite <- H1; auto.
Save.

Lemma nfrac_minus_gen : forall n m p q r s, (0 < p)%N -> (0 < r)%N
      -> (p * r = q * s)%N -> (n <= p)%N
      -> (n [/] p) - (m [/] q) == (n * r - m * s) [/] (p * r).
intros; assert (0 < q /\ 0 < s)%N as (Hq,Hs).
rewrite <- N.lt_0_mul'.
rewrite <- H1; rewrite N.lt_0_mul'; auto.
rewrite <- nfrac_simpl_r with (n:=n) (p:=p) (m:= r); auto.
rewrite <- nfrac_simpl_r with (n:=m) (p:=q) (m:= s); auto.
rewrite <- H1; auto.
apply nfrac_minus; auto.
apply N.mul_pos_pos; auto.
apply N.mul_le_mono_nonneg_r; auto.
Save.


Lemma nfrac_lt : forall n m p q, (0<q)%N -> (n*q < m*p)%N -> (n<p)%N
      -> n [/] p < m [/] q.
intros; assert (0<m*p)%N.
apply N.le_lt_trans with (n*q)%N; auto.
assert (0<m /\ 0<p)%N as (Hm,Hp).
rewrite <- N.lt_0_mul'; auto.
destruct (N.le_ge_cases m q) as [Hmq|Hmq].
apply Uminus_lt0_intro; auto.
rewrite nfrac_minus_gen with (r:=p) (s:=q); auto.
apply nfrac_pos; auto.
rewrite <- N.neq_0_lt_0.
apply N.sub_gt; auto.
ring.
rewrite nfrac_ge_simpl with (n:=m); auto.
Save.

Lemma nfrac_plus_mult : forall n m p q, (0 < p)%N -> (0 < q)%N
      -> (n [/] p) + (m [/] q) == (n * q + m * p) [/] (p * q).
intros; apply nfrac_plus_gen; auto.
apply N.mul_comm.
Save.

Lemma nfrac_div : forall n m p q, (0<m)%N -> (n <= p)%N -> (m <= q)%N
      -> (n [/] p) / (m [/] q) == (n*q) [/] (m*p).
intros; destruct (Neq_lt_0 n).
subst n; repeat Usimpl; auto.
assert (0<p/\0<q)%N as (Hp,Hq); auto.
split.
apply N.lt_le_trans with n; auto.
apply N.lt_le_trans with m; auto.
destruct (N.le_ge_cases (m*p) (n*q)).
rewrite nfrac_ge_simpl with (n:=(n*q)%N); auto.
rewrite N.lt_0_mul'; auto.
(* non degenerate case *)
symmetry; apply Umult_div_eq; auto.
rewrite nfrac_mult; auto.
assert (0 < q * m)%N.
rewrite N.lt_0_mul'; auto.
transitivity ((n * (q * m))[/](p * (q * m))); auto.
apply nfrac_eq_compat; ring.
Save.
Hint Resolve nfrac_div.

Lemma nmult_frac_right : forall n p x, (n <= p)%N -> nmult_def p x
       -> (p *\ x) * (n [/] p) == n *\ x.
intros.
destruct (Neq_lt_0 n) as [Hn|Hn].
subst; repeat Usimpl; auto.
assert (nmult_def n x).
apply nmult_def_le_compat_left with p; auto.
assert (0<p)%N.
apply N.lt_le_trans with n; auto.
rewrite <- nmult_Umult_assoc_left; auto.
rewrite Umult_sym.
unfold nfrac; rewrite <- nmult_Umult_assoc_left; auto.
rewrite nmult_Umult_assoc_right with (n:=n); auto.
rewrite nmult_Umult_assoc_left; auto.
Save.
Hint Resolve nmult_frac_right.

Lemma Udiv_frac_right : forall n p x, (x <= (n [/] p)) -> (n <= p)%N 
       -> x / (n [/] p) == p *\ (x * [1|]n).
(** introduce a few extra conditions on arguments *)
intros; apply (Ule_orc x 0); intros; auto.
assert (Hx:x==0); auto.
rewrite Hx; repeat Usimpl; auto.
assert (Hx:0<x); auto.
destruct (Neq_lt_0 n).
destruct H1.
replace 0 with (n[/]p); subst; auto.
assert (Hp:(0<p)%N).
apply N.lt_le_trans with n; auto.
assert (Hmd:nmult_def p (x * [1|]n)); auto.
apply nmult_def_introp.
apply nmult_le_simpl with (N.pred n); auto.
rewrite Nsucc_pred_pos; auto.
rewrite nmult_Umult_assoc_right; auto.
rewrite nmult_n_Nnthp; repeat Usimpl; auto.
(** main case *)
symmetry; apply Umult_div_eq; auto.
rewrite nmult_frac_right; auto.
rewrite nmult_Umult_assoc_right; auto.
Save.

(** get n/p = m/q + r/qp with r < p *)
Definition approx_div n p q := N.div_eucl (n * q) p.

Lemma approx_eucl_eq : forall n p q, (0<p)%N -> (0<q)%N 
      -> let (m,r):= approx_div n p q in n[/]p==m[/]q + r[/](p*q).
intros; unfold approx_div.
assert (Hd:=N.div_eucl_spec (n * q) p).
destruct (N.div_eucl (n * q) p).
transitivity ((n*q)[/](p*q)).
rewrite nfrac_simpl_r; auto.
rewrite Hd.
rewrite <- nfrac_plus.
Usimpl.
rewrite nfrac_simpl_l; auto.
Save.

Lemma approx_eucl_spec : forall n p q, 
   (n<=p)%N -> (0<p)%N -> (0<q)%N 
  -> let (m,r):= approx_div n p q in 
     n[/]p==m[/]q + r[/](p*q) /\ (r[/](p*q) < [1|]q).
intros n p q Hle Hp Hq.
assert (Hd:=approx_eucl_eq n Hp Hq).
unfold approx_div in *.
destruct (Neq_lt_0 n) as [Hn|Hn].
subst; simpl; auto.
assert (Hp1:(p<>0)%N).
intro Ha; subst p; discriminate.
assert (Hm:=N.mod_lt (n * q) p Hp1).
unfold N.modulo in Hm; destruct (N.div_eucl (n * q) p).
simpl in Hm.
split; auto.
apply Olt_le_trans with (p[/](p * q)); auto.
apply nfrac_lt_compat_left; auto.
apply N.lt_le_trans with p; auto.
transitivity (p * 1)%N.
rewrite N.mul_1_r; reflexivity.
apply N.mul_le_mono_l; auto.
rewrite <- (N.mul_1_r p) at 1.
rewrite nfrac_simpl_l; auto.
Save.

Definition approx_down n p q := let (m,r):= approx_div n p q in m[/]q.

Definition approx_near n p q := let (m,r):= approx_div n p q in
    match (r+r ?= p)%N with Gt => (m+1)[/]q | _ => m [/] q end.

Lemma approx_down_inf : forall n p q, (0<p)%N -> (0<q)%N 
      -> approx_down n p q <= n[/]p.
unfold approx_down; intros n p q Hp Hq.
assert (Hs:=approx_eucl_eq n Hp Hq).
destruct (approx_div n p q).
rewrite Hs; auto.
Save.


Lemma approx_down_sup : forall n p q, (n<p)%N -> (0<p)%N -> (0<q)%N 
      -> n[/]p < approx_down n p q + [1|]q.
unfold approx_down; intros n p q Hnp Hp Hq.
assert (Hnp1:(n <= p)%N).
red; rewrite Hnp; discriminate.
assert (Hs:=approx_eucl_spec Hnp1 Hp Hq).
destruct (approx_div n p q).
destruct Hs.
rewrite H.
apply Uplus_lt_compat_r; auto.
rewrite <- H; auto.
Save.

Lemma approx_near_spec : forall n p q, (n<=p)%N -> (0<p)%N -> (0<q)%N 
      -> diff (n[/]p) (approx_near n p q) <= 1[/](2*q).
intros n p q Hnp Hp Hq.
assert (0<2*q)%N.
apply N.lt_le_trans with q; auto.
transitivity (1*q)%N.
ring_simplify; reflexivity.
apply N.mul_le_mono_nonneg_r; auto.
Nineq.
assert (0<p*q)%N.
rewrite N.lt_0_mul'; auto.
(* starting proof *)
unfold approx_near; assert (Hs:=approx_eucl_spec Hnp Hp Hq).
destruct (approx_div n p q).
destruct Hs as (Heq,Hinf).
rewrite Heq.
destruct (N.le_gt_cases (n1+n1) p) as [Hc|Hc].
(* Case 2n1 <= p *)
transitivity (diff (n0[/]q + n1[/](p * q)) (n0[/]q)).
red in Hc; destruct (n1 + n1 ?= p)%N; auto.
contradiction Hc; trivial.
rewrite diff_sym.
rewrite diff_Uminus; auto.
transitivity (n1[/](p * q)); auto.
apply nfrac_le; auto.
ring_simplify.
transitivity (q * (n1+n1))%N; auto.
ring_simplify; reflexivity.
apply N.mul_le_mono_nonneg_l; auto.
(** case (p < 2n1)%N *)
assert (n1 <= p)%N.
rewrite <- N.nlt_ge; intro.
absurd (1[/]q < 1[/]q); auto.
apply Ole_lt_trans with (n1[/](p * q)).
apply nfrac_le; auto.
rewrite N.mul_1_l.
apply N.mul_le_mono_nonneg_r; auto.
apply N.lt_le_incl; auto.
rewrite nfrac_1_num;auto.

rewrite <- N.gt_lt_iff in Hc.
rewrite Hc.
rewrite diff_Uminus; auto.
transitivity (1[/]q - n1[/](p * q)).
rewrite <- nfrac_plus.
rewrite <- Uminus_assoc_left.
rewrite Uplus_sym; auto.
rewrite <- nfrac_simpl_l with (m:=p); auto.
rewrite nfrac_minus; auto.
rewrite N.mul_1_r.
apply nfrac_le; auto.
ring_simplify.
rewrite (N.mul_comm q p).
apply N.mul_le_mono_r; auto.
transitivity ((p - n1) + (p-n1))%N.
ring_simplify; reflexivity.
transitivity ((p - n1) + n1)%N.
rewrite <-  N.add_le_mono_l.
rewrite N.le_sub_le_add_r.
apply N.lt_le_incl.
apply N.gt_lt; trivial.
rewrite N.sub_add; auto.
reflexivity.
apply N.mul_le_mono_l; auto.
rewrite <- nfrac_plus; auto.
rewrite nfrac_1_num.
apply Uplus_le_compat_right; auto.
Save.










 