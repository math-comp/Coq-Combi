(** * Bernoulli.v: Simulating Bernoulli and Binomial distributions *)
Add Rec LoadPath "." as ALEA.

Require Export Cover.
Require Export Misc.
Require Export BinCoeff.

(* begin hide *)
Set Implicit Arguments.

(* Module Bernoulli (Univ:Universe). *)
(* Module CP := (CoverFun Univ). *)
(* Import Univ CP RP PP MP UP. *)
Open Local Scope U_scope.
Open Local Scope O_scope.

(* end hide *)

(** ** Program for computing a Bernoulli distribution
       bernoulli p gives true with probability [p]
       and false with probability [(1-p)]
<<
let rec bernoulli p =
        if flip
        then (if p < 1/2 then false else bernoulli (2 p - 1))
        else (if p < 1/2 then bernoulli (2 p) else true)
>>*)

Hypothesis dec_demi : forall x : U, {x < [1/2]}+{[1/2] <= x}.

Instance Fbern_mon : monotonic 
    (fun (f:U -> distr bool) p => 
     Mif Flip
       (if dec_demi p then Munit false else f (p & p))
       (if dec_demi p then f (p + p) else Munit true)).
intros; intros f g H n.
apply Mif_le_compat; case (dec_demi n); auto.
Save.

Definition Fbern : (U -> distr bool) -m> (U -> distr bool)
    := mon (fun f p => Mif Flip
       (if dec_demi p then Munit false else f (p & p))
       (if dec_demi p then f (p + p) else Munit true)).


Definition bernoulli : U -> distr bool := Mfix Fbern.


(** ** [fc p n k] is defined as [(C(k,n) p^k (1-p)^(n-k)] *)

Definition fc (p:U)(n k:nat) :=  (comb k n) */ (p^k * ([1-]p)^(n-k)).

Lemma fcp_0 : forall p n, fc p n O == ([1-]p)^n.
intros; unfold fc; rewrite comb_0_n; repeat Usimpl.
rewrite <- minus_n_O; auto.
Save.

Lemma fcp_n : forall p n, fc p n n == p^n.
intros; unfold fc; rewrite comb_n_n; repeat Usimpl.
rewrite <- minus_n_n; auto.
Save.

Lemma fcp_not_le : forall p n k, (S n <= k)%nat -> fc p n k == 0.
unfold fc; intros; rewrite comb_not_le; auto.
Save.

Lemma fc0 : forall n k, fc 0 n (S k) == 0.
intros; unfold fc; repeat Usimpl; auto.
Save.
Hint Resolve fc0.

Add Morphism fc with signature Oeq ==> eq ==> eq ==> Oeq
as fc_eq_compat.
unfold fc; intros; rewrite H; auto.
Save.

Hint Resolve fc_eq_compat.

(** *** Sum of [fc] objects *)

Lemma sigma_fc0 : forall n k,  sigma (fc 0 n) (S k) == 1.
intros; rewrite sigma_S_lift.
rewrite fcp_0; rewrite sigma_zero; repeat Usimpl; auto.
Save.

(** Intermediate results for inductive proof of [ [1-]p^n == sigma (fc p n) n ] *)

Lemma fc_retract :
     forall p n, [1-]p^n == sigma (fc p n) n -> retract (fc p n) (S n).
intros; apply (Ueq_orc p 0); intros; auto.
red; intros.
destruct k.
simpl; Usimpl; auto.
rewrite sigma_S; repeat Usimpl; auto.
transitivity (0:U); auto.
rewrite H0; auto.
apply retractS_intro; auto.
apply retract_lt.
apply Ole_lt_trans with ([1-]p^n); auto.
transitivity (p^n); auto.
rewrite fcp_n; auto.
Save.
Hint Resolve fc_retract.

Lemma fc_Nmult_def :
     forall p n k, ([1-]p^n == sigma (fc p n) n) -> 
                    Nmult_def (comb k n) (p^k * ([1-]p) ^(n-k)).
intros p n k Heq; destruct k.
rewrite comb_0_n; auto.
apply (Ueq_orc p 0); intros; auto.
(* case p == 0 *)
rewrite H; repeat Usimpl; auto.
(* case p <> 0 *)
assert (Hk:(S k < n \/n=S k\/ n < S k)%nat); try omega.
decompose sum Hk; clear Hk; intros.
(* S k < n *)
apply Nmult_def_lt.
apply Ole_lt_trans with (sigma (fc p n) n).
apply sigma_le with (k:=S k) (f:=fc p n); auto.
apply Ole_lt_trans with ([1-](p^n)); auto.
(* n=S k *)
subst.
rewrite comb_n_n; auto.
rewrite comb_not_le; auto with arith.
Save.
Hint Resolve fc_Nmult_def.

Lemma fcp_S :
    forall p n k, ([1-]p^n == sigma (fc p n) n) 
         -> fc p (S n) (S k) == p * (fc p n k) + ([1-]p) * (fc p n (S k)).
intros;
assert (Hcase : (k<n \/ n=k \/ (S n)<=k)%nat); try omega.
decompose sum Hcase.
unfold fc; simpl.
rewrite plus_Nmult_distr.
rewrite <- Umult_assoc.
rewrite Nmult_Umult_assoc_right; auto.
repeat Usimpl.
rewrite <- Nmult_Umult_assoc_right; auto.
2:exact (fc_Nmult_def p n (S k) H).
apply Nmult_eq_compat_left; trivial.
repeat rewrite  Umult_assoc.
rewrite (Umult_sym ([1-]p) p).
rewrite <-  (Umult_assoc p ([1-]p)).
rewrite (Umult_sym ([1-]p) (p^k)); auto.
repeat rewrite  <- Umult_assoc; auto.
replace (n-k)%nat with (S (n-S k)); auto; omega.
subst; repeat rewrite fcp_n.
rewrite fcp_not_le; repeat Usimpl; auto.
repeat (rewrite fcp_not_le; auto with arith).
Save.

Lemma sigma_fc_1 
   : forall p n, [1-]p^n == sigma (fc p n) n -> 1 == sigma (fc p n) (S n).
intros; rewrite sigma_S.
rewrite <- H; rewrite fcp_n; auto.
Save.
Hint Resolve sigma_fc_1.

(** Main result : [ [1-](p^n) == sigma (k=0..(n-1)) C(k,n) p^k (1-p)^(n-k) ] *)

Lemma Uinv_exp : forall p n,  [1-](p^n) == sigma (fc p n) n.
induction n; auto.
(* case S n *)
apply (Ueq_orc p 0); intros; auto.
(* case p == 0 *)
rewrite sigma_S_lift.
rewrite fcp_0; rewrite sigma_zero; intros;
rewrite H; repeat Usimpl; auto.
(* case p <> 0 *)
assert (Hr:retract (fc p n) (S n)); auto.
(* main property *)
rewrite sigma_S_lift.
rewrite fcp_0.
transitivity (([1-] p) ^ S n + sigma (fun k : nat => p * fc p n k + ([1-]p) * fc p n (S k)) n).
rewrite (sigma_plus (fun k => p * fc p n k) (fun k => [1-] p * fc p n (S k))).
rewrite sigma_mult; auto.
rewrite <-IHn.
transitivity (p * [1-] p ^ n + (([1-] p) ^ S n + sigma (fun k : nat => [1-] p * fc p n (S k)) n));auto.
transitivity (p * [1-] p ^ n + (sigma (fun k : nat => [1-] p * fc p n k) (S n))).
rewrite sigma_mult; auto.
rewrite <- sigma_fc_1;auto; repeat Usimpl;apply Uexp_inv_S.
rewrite sigma_S_lift; repeat Usimpl; rewrite fcp_0; auto.
repeat Usimpl.
apply sigma_eq_compat; intros.
apply Oeq_sym; apply fcp_S; auto.
Save.

Hint Resolve Uinv_exp.

Lemma Nmult_comb 
   : forall p n k, Nmult_def (comb k n) (p ^ k * ([1-] p) ^ (n - k)).
auto.
Save.
Hint Resolve Nmult_comb.


(** ** Properties of the Bernoulli program *)

Lemma Fbern_simpl : forall f p,
Fbern f p = Mif Flip
       (if dec_demi p then Munit false else f (p & p))
       (if dec_demi p then f (p + p) else Munit true).
trivial.
Save.

(** *** Proofs using fixpoint rules *)

Instance Mubern_mon : forall (q: bool -> U), 
  monotonic 
   (fun bern (p:U) => if dec_demi p then [1/2]*(q false)+[1/2]*(bern (p+p))
                           else  [1/2]*(bern (p&p)) + [1/2]*(q true)).
intros q f g H p.
case (dec_demi p); repeat Usimpl; auto.
Save.

Definition Mubern (q: bool -> U) :  MF U -m> MF U 
  := mon (fun bern (p:U) => if dec_demi p then [1/2]*(q false)+[1/2]*(bern (p+p))
                            else  [1/2]*(bern (p&p)) + [1/2]*(q true)).

Lemma Mubern_simpl : forall (q: bool -> U) f p,
  Mubern q f p = if dec_demi p then [1/2]*(q false)+[1/2]*(f (p+p))
                 else  [1/2]*(f (p&p)) + [1/2]*(q true).
trivial.
Save.

(** Mubern commutes with the measure of Fbern *)

Lemma Mubern_eq : forall (q: bool -> U) (f:U -> distr bool) (p:U),
             mu (Fbern f p) q  == Mubern q (fun y => mu (f y) q) p.
intros; rewrite Mubern_simpl; rewrite Fbern_simpl.
case (dec_demi p).
rewrite Mif_eq; rewrite Flip_true; rewrite Flip_false; rewrite Munit_simpl; auto.
rewrite Mif_eq; rewrite Flip_true; rewrite Flip_false; rewrite Munit_simpl; auto.
Save.
Hint Resolve Mubern_eq.

Lemma Bern_eq :
    forall q : bool -> U, forall p, mu (bernoulli p) q == mufix (Mubern q) p.
intros; apply Oeq_sym.
unfold bernoulli; apply mufix_mu with (muF:=(Mubern q)) (q:=fun (p:U) => q); auto.
Save.
Hint Resolve Bern_eq.

Lemma Bern_commute : forall q : bool -> U,
   mu_muF_commute_le Fbern (fun (x:U) => q) (Mubern q).
red; auto.
Save.
Hint Resolve Bern_commute.

(** bernoulli terminates with probability 1 *)

Lemma Bern_term : forall p, mu (bernoulli p) (fone bool) == 1.
intros; transitivity (mufix (Mubern (fone bool)) p); auto.
transitivity (lub U1min); auto.
unfold mufix, fixp.
simpl; apply lub_eq_compat; intro n.
transitivity (Ccpo.iter (D:=MF U) (Mubern (fone bool)) n p); auto.
generalize p; induction n; auto.
intros; transitivity ([1/2] * U1min n + [1/2]); auto.
rewrite iterS_simpl.
rewrite Mubern_simpl.
unfold fone; repeat Usimpl.
case (dec_demi p0); rewrite IHn; repeat Usimpl; auto.
Save.
Hint Resolve Bern_term.

(** *** p is an invariant of Mubern qtrue *)

Lemma MuBern_true : forall p, Mubern B2U (fun q => q) p == p.
intros; unfold B2U; rewrite Mubern_simpl; case (dec_demi p); intros; repeat Usimpl.
apply half_twice; auto.
apply half_esp; auto.
Save.
Hint Resolve MuBern_true.

Lemma MuBern_false : forall p, Mubern (finv B2U) (finv (fun q => q)) p == [1-]p.
intros; unfold finv, B2U; rewrite Mubern_simpl; case (dec_demi p); intros; repeat Usimpl.
rewrite Uplus_sym; rewrite Uinv_half; repeat Usimpl.
apply half_twice; auto.
rewrite Uinv_esp_plus.
apply half_twice; auto.
Save.
Hint Resolve MuBern_false.

Lemma Mubern_inv : forall (q: bool -> U) (f:U -> U) (p:U),
      Mubern (finv q) (finv f) p == [1-] Mubern q f p.
intros; unfold finv; repeat (rewrite Mubern_simpl).
case (dec_demi p); intro; auto.
Save.

(** [ prob(bernoulli = true) = p ] *)

Lemma Bern_true : forall p, mu (bernoulli p) B2U == p.
intros; unfold bernoulli.
apply muF_eq with
    (muFqinv:= Mubern (qinv (fun (x:U) => B2U) p))
    (muFq:=Mubern B2U)
    (q:=fun (x:U) => (B2U:bool->U))
    (f:=fun (x:U) => x);intros; auto.
unfold qinv; auto.
exact (Bern_term p).
Save.

(** [ prob(bernoulli = false) = 1-p ] *)

Lemma Bern_false : forall p, mu (bernoulli p) NB2U == [1-]p.
intros; transitivity (mu (bernoulli p) (finv B2U)).
apply mu_stable_eq; auto.
rewrite mu_inv_minus.
rewrite Bern_term; rewrite Bern_true; auto.
Save.


(** *** Direct proofs using lubs *)
(**  Invariant [pmin p] with [pmin p n = p - [1/2] ^ n] *)

(** Property : [ forall p, ok p (bernoulli p) chi (.=true) ] *)

Definition qtrue (p:U) := B2U.
Definition qfalse (p:U) := NB2U.

Lemma bernoulli_true :   okfun (fun p => p) bernoulli qtrue.
unfold bernoulli; intros.
apply okfun_le_compat with (fun p => lub (Pmin p)) qtrue; auto.
intro x; auto.
apply fixrule with (p:= Pmin); intros.
simpl; auto.
red; simpl; intros.
red.
rewrite
 (Mif_eq Flip
   (if dec_demi x0 then Munit false else f (x0 & x0))
   (if dec_demi x0 then f (x0 + x0) else Munit true) (qtrue x0)); simpl.
case (dec_demi x0); simpl; intros.
(* Case x0 < 1/2 *)
unfold flip, unit, B2U, NB2U; simpl.
repeat Usimpl.
transitivity ((pmin (x0 + x0) i) * [1/2]).
assert (x0<= [1/2]); auto.
rewrite (pmin_plus_eq x0 i H0).
Usimpl; trivial.
Usimpl; apply (H (x0+x0)); auto.
(* Case 1/2 <= x0 *)
unfold flip, unit, B2U, NB2U; simpl.
repeat Usimpl.
transitivity ((pmin (x0 & x0) i) * [1/2] + [1/2]).
apply Ole_trans with (1:=(pmin_esp_le x0 i)); auto.
repeat Usimpl; apply (H (x0&x0)); auto.
Save.

(** Property : [ forall p, ok (1-p) (bernoulli p) (chi (.=false)) ] *)

Lemma bernoulli_false :  okfun (fun p => [1-] p) bernoulli qfalse.
unfold bernoulli; intros.
apply okfun_le_compat with (fun p => lub (Pmin ([1-]p))) qfalse; auto.
intro x; auto.
apply fixrule with (p:= fun p => Pmin ([1-]p)); auto; intros.
simpl; auto.
red; simpl; intros.
red.
rewrite
 (Mif_eq Flip
   (if dec_demi x0 then Munit false else f (x0 & x0))
   (if dec_demi x0 then f (x0 + x0) else Munit true) (qfalse x0)); simpl.
case (dec_demi x0); simpl; intros.
(* Case x0 < 1/2 *)
unfold flip, unit, B2U, NB2U; simpl.
repeat Usimpl.
transitivity ([1/2] + (pmin ([1-] (x0 + x0)) i) * [1/2]).
apply Ole_trans with (1:=pmin_esp_le ([1-] x0) i).
rewrite (Uinv_plus_esp x0 x0).
Usimpl; auto.
repeat Usimpl; apply (H (x0+x0)); auto.
(* Case 1/2 <= x0 *)
unfold flip, unit, B2U, NB2U; simpl.
repeat Usimpl.
transitivity ((pmin ([1-] (x0 & x0)) i) * [1/2]).
rewrite (Uinv_esp_plus x0 x0).
assert ([1-] x0 <= [1/2]); auto.
rewrite (pmin_plus_eq ([1-]x0) i H0).
repeat Usimpl; trivial.
repeat Usimpl; apply (H (x0&x0)); auto.
Save.

(** Probability for the result of [ (bernoulli p) ] to be true is exactly [p] *)

Lemma qtrue_qfalse_inv : forall (b:bool) (x:U), qtrue x b == [1-] (qfalse x b).
intros; case b; simpl; auto.
Save.

Lemma bernoulli_eq_true :  forall p, mu (bernoulli p) (qtrue p) == p.
intros; apply Ole_antisym.
transitivity (mu (bernoulli p) (fun b => [1-] (qfalse p b))).
apply (mu_monotonic (bernoulli p)).
intro b; rewrite (qtrue_qfalse_inv b); auto.
transitivity ([1-] (mu (bernoulli p) (qfalse p))).
exact (mu_stable_inv (bernoulli p) (qfalse p)).
apply Uinv_le_perm_left.
apply (bernoulli_false p).
apply (bernoulli_true p).
Save.

Lemma bernoulli_eq_false :  forall p, mu (bernoulli p) (qfalse p)== [1-]p.
intros; apply Ole_antisym.
transitivity (mu (bernoulli p) (fun b => [1-] (qtrue p b))).
apply (mu_monotonic (bernoulli p)).
intro b; rewrite (qtrue_qfalse_inv b p); auto.
transitivity ([1-] (mu (bernoulli p) (qtrue p))).
exact (mu_stable_inv (bernoulli p) (qtrue p)).
apply Uinv_le_perm_left; Usimpl.
apply (bernoulli_true p).
apply (bernoulli_false p).
Save.

Lemma bernoulli_eq :  forall p f, 
      mu (bernoulli p) f == p * f true + ([1-]p) * f false.
intros; transitivity (mu (bernoulli p) (fun b => f true * qtrue p b + f false * qfalse p b)).
apply mu_stable_eq.
unfold qtrue,qfalse,B2U,NB2U.
simpl; apply ford_eq_intro; intro x; destruct x; repeat Usimpl; auto.
rewrite (mu_stable_plus (bernoulli p) (f:=fun b => f true * qtrue p b)
                                                          (g:=fun b => f false * qfalse p b)).
(*unfold finv,qtrue,qfalse,B2U,NB2U; intro x.
destruct x; unfold finv; repeat Usimpl; auto.*)
rewrite (mu_stable_mult (bernoulli p) (f true) (qtrue p)).
rewrite (mu_stable_mult (bernoulli p) (f false) (qfalse p)).
rewrite bernoulli_eq_true; rewrite bernoulli_eq_false.
apply Uplus_eq_compat; auto.
unfold finv,qtrue,qfalse,B2U,NB2U; intro x.
destruct x; unfold finv; repeat Usimpl; auto.
Save.

Lemma bernoulli_total : forall p , mu (bernoulli p) (fone bool)==1.
intros; rewrite bernoulli_eq; unfold fone; repeat Usimpl; auto.
Save.

(** Direct version of Bernoulli *)

Lemma bernoulli_choice : forall p, bernoulli p == Mchoice p (Munit true) (Munit false).
intros; intro f.
rewrite Mchoice_simpl.
repeat rewrite Munit_simpl.
apply bernoulli_eq.
Save.

Lemma bernoulli_eq_compat : forall p q, p == q -> bernoulli p == bernoulli q.
intros; repeat rewrite bernoulli_choice; apply Mchoice_eq_compat; auto.
Save.
Hint Resolve bernoulli_eq_compat.

Lemma Mif_bernoulli_choice : forall A p (m1 m2:distr A), 
   Mif (bernoulli p) m1 m2 == Mchoice p m1 m2.
intros; intro f.
rewrite Mchoice_simpl.
rewrite Mif_eq.
rewrite Bern_true; rewrite Bern_false.
auto.
Save.

Lemma Mlet_if_bernoulli : forall A B (m:distr A) (m1 m2:distr B) (cond : A -> bool), 
      mu m (fone A) == 1 ->
      Mlet m (fun a => if cond a then m1 else m2) == Mif (bernoulli (mu m (fun a => B2U (cond a)))) m1 m2.
intros; transitivity (Mif (Mlet m (fun a => Munit (cond a))) m1 m2).
rewrite Mif_simpl.
rewrite Mlet_assoc.
apply Mlet_eq_compat; auto; intro a.
rewrite Mlet_unit; auto.
apply Mif_eq_compat; auto.
intro f; rewrite Mlet_simpl.
rewrite bernoulli_eq.
simpl.
transitivity (mu m (fun x : A => B2U (cond x) * f true + NB2U (cond x) * f false)).
apply mu_stable_eq; intro x; unfold B2U, NB2U; destruct (cond x); repeat Usimpl; auto.
setoid_rewrite mu_stable_plus.
apply Uplus_eq_compat; auto.
setoid_rewrite mu_stable_mult_right; auto.
setoid_rewrite mu_stable_mult_right; auto.
apply Umult_eq_compat_left.
rewrite <- mu_one_inv; auto.
apply mu_stable_eq; intro a; auto.
rewrite (B2Uinv (cond a)); auto.
intro x; unfold finv.
unfold NB2U, B2U; destruct (cond x); repeat Usimpl; auto.
Save.

(** ** Program for computing a binomial distribution *)

(** Recursive definition of binomial distribution using bernoulli *)
(**  [ (binomial p n) ]  gives [k] with probability [ C(k,n) p^k (1-p)^(n-k) ] *)

Fixpoint binomial (p:U)(n:nat) {struct n}: distr nat :=
    match n with O => Munit O
             | S m => Mlet (binomial p m)
                      (fun x => Mif (bernoulli p) (Munit (S x)) (Munit x))
    end.

Lemma binomial_0_simpl : forall p,   binomial p 0 = Munit O.
trivial.
Save.

Lemma binomial_S_simpl : forall p n,
   binomial p (S n) =  Mlet (binomial p n)
                      (fun x => Mif (bernoulli p) (Munit (S x)) (Munit x)).
trivial.
Save.

(** ** Properties of Binomial distribution *)

(** [prob(binomial p n = k) = C(k,n) p ^ k (1-p)^(n-k)] *)

Lemma binomial_eq_k :
   forall p n k, mu (binomial p n) (carac_eq k) == fc p n k.
induction n; intros.
(* case n = 0 *)
simpl; destruct k; unfold unit,carac_eq,carac; auto.
rewrite fcp_0; auto.
(* cas n<>0 *)
simpl binomial.
simpl mu.
transitivity
(star (mu (binomial p n))
  (fun x : nat =>
   star (mu (bernoulli p))
     (fun x0 : bool => mu (if x0 then Munit (S x) else Munit x))) (carac_eq k));
auto.
transitivity
 (mu (binomial p n)
  (fun x : nat => p * (carac_eq k (S x)) + ([1-]p) * (carac_eq k x))).
rewrite star_simpl.
apply mu_stable_eq; intro x; rewrite star_simpl.
rewrite bernoulli_eq; unfold Munit,carac; simpl; auto.
destruct k.
(* case k = 0 *)
transitivity (mu (binomial p n) (fun x => [1-] p * carac_eq 0 x)).
apply mu_stable_eq; unfold carac_eq at 1,carac; intro x; auto.
rewrite if_else; auto; repeat Usimpl; auto.
rewrite (mu_stable_mult (binomial p n) ([1-]p) (carac_eq 0)).
rewrite IHn; simpl; repeat Usimpl; auto.
repeat rewrite fcp_0; auto.
(* Case S k *)
transitivity  (mu (binomial p n) (fun x : nat => p * carac_eq k x + [1-] p * carac_eq (S k) x)).
apply mu_stable_eq; intro; repeat Usimpl.
unfold carac_eq,carac; intros.
case (eq_nat_dec k x); intro.
rewrite if_then; auto.
rewrite if_else; auto.
rewrite (mu_stable_plus (binomial p n) (f:=fun x : nat => p * carac_eq k x) (g:=fun x : nat => [1-] p * carac_eq (S k) x)).
(* *)
rewrite (mu_stable_mult (binomial p n) p (carac_eq k)).
rewrite (mu_stable_mult (binomial p n) ([1-]p) (carac_eq (S k))).
rewrite IHn.
rewrite IHn.
rewrite fcp_S; auto.
(* fplusok *)
intro x; unfold finv,carac_eq; intros.
case (eq_nat_dec k x); intro; auto.
Save.

(** [prob(binomial p n <= n) = 1] *)

Lemma binomial_le_n :
   forall p n, 1 <= mu (binomial p n) (carac_le n).
induction n.
unfold carac_le; simpl; case (le_lt_dec 0 0); intuition.
simpl binomial.
apply cover_let_one with (P:=fun k => k <= n) (cP:=carac_le n); auto.
apply (is_le n).
intros; repeat distrsimpl.
transitivity (mu (bernoulli p) (fone bool)); auto.
repeat distrsimpl.
unfold fone; case x0; unfold carac_le; simpl.
rewrite carac_one; auto with arith.
rewrite carac_one; auto with arith.
Save.

(** [prob(binomial p (S n) <= S k) = 
      p prob(binomial p n <= k) + (1-p) prob(binomial p n <= S k) *)

Lemma binomial_le_S : forall p n k, 
   mu (binomial p (S n)) (carac_le (S k)) ==
   p * (mu (binomial p n) (carac_le k)) + ([1-]p) * (mu (binomial p n) (carac_le (S k))).
Proof.
simpl binomial; intros.
repeat distrsimpl.
rewrite <- (mu_stable_mult (binomial p n) p).
rewrite <- (mu_stable_mult (binomial p n) ([1-]p)).
rewrite <- (mu_stable_plus (binomial p n)); auto.
repeat distrsimpl.
rewrite bernoulli_eq; simpl.
unfold fplus,fmult.
apply  Uplus_eq_compat; repeat Usimpl; auto.
Qed.

(** [prob(binomial p (S n) < S k) = 
      p prob(binomial p n < k) + (1-p) prob(binomial p n < S k) *)

Lemma binomial_lt_S : forall p n k, 
   mu (binomial p (S n)) (carac_lt (S k)) ==
   p * (mu (binomial p n) (carac_lt k)) + ([1-]p) * (mu (binomial p n) (carac_lt (S k))).
Proof.
simpl binomial; intros.
repeat distrsimpl.
rewrite <- (mu_stable_mult (binomial p n) p).
rewrite <- (mu_stable_mult (binomial p n) ([1-]p)).
rewrite <- (mu_stable_plus (binomial p n)); auto.
repeat distrsimpl.
rewrite bernoulli_eq; simpl.
unfold fplus,fmult.
apply  Uplus_eq_compat; repeat Usimpl; auto.
Qed.

Lemma binomial_eq : forall p n f,
   mu (binomial p n) f == sigma (fun k => fc p n k * f k) (S n).
intros; transitivity (mu (binomial p n) (fun x => carac_le n x * f x)).
apply mu_cut with (cP:=carac_le n) (P:=fun k => k <= n).
apply is_le.
intros; rewrite (cover_eq_one x (is_le n)); auto.
apply binomial_le_n.
transitivity (mu (binomial p n) (fun x => sigma (fun k => carac_le n x * carac_eq k x * f k) (S n))).
apply mu_stable_eq; intro x.
apply (cover_elim (is_le n) x); auto.
intros (Hgt,Hc).
rewrite sigma_zero; intros; rewrite Hc; repeat Usimpl; auto.
intros (Hle,Hc); rewrite Hc; repeat Usimpl; auto.
transitivity (sigma (fun k : nat => carac_eq k x * f k) x 
            + sigma (fun k : nat => carac_eq (x+k) x * f (x+k)%nat) (S n - x)%nat).
rewrite sigma_zero.
Usimpl.
rewrite <- minus_Sn_m; auto.
rewrite sigma_S_lift.
repeat rewrite <- plus_n_O.
rewrite (cover_eq_one x (is_eq x)); auto.
Usimpl.
rewrite sigma_zero; auto.
intros; rewrite (cover_eq_zero x (is_eq (x + S k))); auto.
omega.
intros; rewrite (cover_eq_zero x (is_eq k)); auto.
omega.
assert (Hp:(x + (S n - x) = S n)%nat) by omega.
rewrite <- Hp at 2.
rewrite sigma_plus_lift.
apply Uplus_eq_compat.
apply sigma_eq_compat; intros; rewrite Hc; auto.
apply sigma_eq_compat; intros; rewrite Hc; auto.
transitivity (sigma (fun k => mu (binomial p n) (fun x : nat => carac_eq k x * f k)) (S n)).
rewrite <- mu_sigma_eq.
apply mu_stable_eq.
intro x; apply sigma_eq_compat; intros; auto.
apply (cover_elim (is_eq k) x); auto; intros (Hp,Hc).
rewrite Hc; repeat Usimpl; auto.
rewrite Hc; rewrite (cover_eq_one x (is_le n)); repeat Usimpl; auto; try omega.
red; intros; apply (cover_elim (is_eq k) x); auto; intros (Hp,Hc).
rewrite Hc; repeat Usimpl; auto.
rewrite Hc; Usimpl.
rewrite sigma_zero; repeat Usimpl; auto.
intros; rewrite (cover_eq_zero x (is_eq k0)); repeat Usimpl; auto; try omega.
apply sigma_eq_compat; intros.
rewrite <- binomial_eq_k.
rewrite <- mu_stable_mult_right; apply mu_stable_eq; auto.
Save.


(* End Bernoulli. *)
