Require Export Cover.
Set Implicit Arguments.
Require Arith.

(* Module Ycart (Univ:Universe). *)
(* begin hide *)
(* Import Univ.
Module CP := (CoverFun Univ).
Import CP RP PP MP UP. *)
Open Local Scope U_scope.
Open Local Scope O_scope.
(* end hide *)


(** * Ycart.v: An exemple of partial termination  *)

Section YcartExample.
(** ** Program giving an example of partiality
Given a function K : nat ->nat, N:nat
<<
let rec ycart p x = if random p < K x then x else ycart (x+1)
>>
The probability of termination is $1-\prod_{k=x}^{\infty}(1-K(k)/p+1)$
*)
Variable K : nat -> nat.
Variable N : nat.

Instance FYcart_mon : monotonic 
  (fun (f:nat -> distr nat) n => 
       Mlet (Random N) (fun x => if dec_lt (K n) x then Munit n else f (S n))).
intros f g H n.
apply Mlet_le_compat; auto.
intro x; case (dec_lt (K n) x); auto.
Save.

Definition FYcart : (nat -> distr nat) -m> (nat -> distr nat)
    := mon (fun (f:nat -> distr nat) n => 
       Mlet (Random N) (fun x => if dec_lt (K n) x then Munit n else f (S n))).


Lemma FYcart_simpl : forall f n,
   FYcart f n = Mlet (Random N) (fun x => if dec_lt (K n) x then Munit n else f (S n)).
trivial.
Save.

Definition Ycart : nat -> distr nat := Mfix FYcart.

Definition F x := (K x) */ [1/]1+N.

(** ** Properties of Ycart *)

Lemma FYcart_val : forall (q: MF nat) f x,
     mu (FYcart f x) q == F x * q x + [1-](F x) * mu (f (S x)) q.
intros; unfold  F; rewrite FYcart_simpl.
rewrite Mlet_simpl.
transitivity
   (mu (Random N) (fplus (fmult (q x) (carac_lt (K x)))
                                        (fmult (mu (f (S x)) q) (finv (carac_lt (K x)))))).
apply mu_stable_eq.
intro x0.
unfold fplus,fmult,finv,is_lt, carac_lt, carac.
case (dec_lt (K x) x0); simpl; intros; repeat Usimpl; auto.
assert (fok:fplusok (fmult (q x) (carac_lt (K x))) (fmult (mu (f (S x)) q) (finv (carac_lt (K x))))).
intro y; unfold fmult,finv,is_lt, carac_lt, carac.
case (dec_lt (K x) y); repeat Usimpl; auto.
rewrite (mu_stable_plus (Random N) fok).
transitivity
  (q x * mu (Random N) (carac_lt (K x)) +
   mu (f (S x)) q * mu (Random N)  (finv (carac_lt (K x)))).
apply Uplus_eq_compat; apply (mu_stable_mult (Random N)).
rewrite (Random_lt N (K x)).
apply Uplus_eq_compat; auto.
rewrite Random_inv; rewrite Random_lt; auto.
Save.

Definition P (x : nat) : nat -m-> U := Prod (fun i => [1-]F (x+i)).

Definition p (x:nat) : nat -m> U := sigma (fun k => F (x+k) * P x k).

Lemma P_prod : forall x k, F (x+k) * P x k == P x k - P x (S k).
intros; unfold P.
repeat (rewrite Prod_simpl); rewrite prod_minus; auto.
Save.
Hint Resolve P_prod.

Lemma p_diff : forall x n,  (p x n : U) == [1-] P x n.
unfold p; intros.
apply Oeq_trans with (sigma (fun k => P x k - P x (S k)) n).
apply sigma_eq_compat; intros; auto.
rewrite sigma_minus_decr; unfold P; auto.
Save.
Hint Resolve p_diff.

Lemma p_lub : forall x, lub (p x) == [1-] prod_inf (fun i => [1-]F (x+i)).
unfold prod_inf; intros.
apply Oeq_trans with (lub (UInv @ (P x)) : U).
apply lub_eq_compat.
intro n.
apply Oeq_trans with  (1:=p_diff x n); auto.
apply Oeq_trans with ([1-]glb (P x)); auto.
Save.
Hint Resolve p_lub.

Lemma p_equation : forall x n,  p x (S n) == F x + [1-](F x) * p (S x) n.
unfold p; intros.
rewrite sigma_S_lift.
unfold P at 1; rewrite Prod_simpl; rewrite prod_0; Usimpl.
apply Uplus_eq_compat.
replace ((x+0)%nat) with x; auto.
rewrite <- sigma_mult.
(*
red; intros.
apply Ole_trans with (P (S x) k); auto.
change ((P (S x) k : U) <= [1-]p (S x) k).
rewrite p_diff; auto.
*)
apply sigma_eq_compat; intros; auto.
unfold P; rewrite Prod_simpl; rewrite prod_S_lift.
rewrite Umult_assoc.
rewrite (Umult_sym (F (x+S k)) ([1-]F (x+0))).
rewrite <- Umult_assoc.
apply Umult_eq_compat.
replace ((x+0)%nat) with x; auto.
apply Umult_eq_compat.
replace ((x + S k)%nat) with ((S x + k)%nat); auto.
omega.
rewrite Prod_simpl; apply prod_eq_compat; intro; auto.
replace ((x + S k0)%nat) with ((S x + k0)%nat); auto.
omega.
red; intros.
apply Ole_trans with (P (S x) k); auto.
change ((P (S x) k : U) <= [1-]p (S x) k).
rewrite p_diff; auto.
Save.
Hint Resolve p_equation.

Lemma Ycart_term1 : forall x, mu (Ycart x) (fone nat) == [1-] prod_inf (fun i => [1-]F (x+i)).
intros; apply Oeq_trans with (lub (p x)); auto.
apply Ole_antisym.
apply (fixrule_up_lub FYcart) with (p:=p) (q:=fun (x:nat) => fone nat); red; intros.
red; rewrite FYcart_val.
unfold fone; Usimpl.
apply Ole_trans with (F x0 + [1-] F x0 * p (S x0) i).
repeat Usimpl; auto.
apply (H (S x0)).
rewrite p_equation; auto.
apply (fixrule FYcart) with (p:=p) (q:=fun (x:nat) => fone nat); intros.
unfold p; rewrite sigma_0; auto.
intro y; red.
rewrite FYcart_val.
unfold fone; Usimpl.
apply Ole_trans with (F y + [1-] F y * p (S y) i).
rewrite p_equation; auto.
repeat Usimpl; auto.
apply (H (S y)).
Save.

(** A  shorter proof using mu (Ycart x) (f_one nat) = mu h. muYcart h x *)

Instance Ycart_one_mon 
   : monotonic (fun (p:nat -> U) (y:nat) => F y + [1-](F y) * p (S y)).
intros f g H n; repeat Usimpl; auto.
Save.

Definition Ycart_one : (nat -> U) -m> (nat -> U) :=
   mon (fun (p:nat->U) (y:nat) => F y + [1-](F y) * p (S y)).

Lemma Ycart_one_simpl : forall p y, Ycart_one p y = F y + [1-](F y) * p (S y).
trivial.
Save.

Lemma Ycart_term2 : forall x, mu (Ycart x) (fone nat) == [1-] prod_inf (fun i => [1-]F (x+i)).
intros; apply Oeq_trans with (mufix Ycart_one x).
unfold Ycart; apply Oeq_sym.
apply mufix_mu with (q:=fun (y:nat) => (fone nat:nat->U)); intros.
apply Oeq_trans with (1:=FYcart_val (fone nat) f x0).
unfold fone.
transitivity (F x0  + [1-] F x0 * (mu (f (S x0))) (fun _ : nat => 1)); auto.
apply Oeq_trans with (lub (p x)); auto.
unfold mufix,fixp; simpl.
apply lub_eq_compat.
intro n; generalize x; induction n; intros; auto.
change (Ccpo.iter (D:=MF nat) Ycart_one (S n) x0 == p x0 (S n)).
rewrite iterS_simpl.
assert (Ccpo.iter (D:=MF nat) Ycart_one n == fun x => p x n).
change  (forall x : nat, Ccpo.iter (D:=MF nat) Ycart_one n x == p x n) in IHn.
simpl; apply ford_eq_intro; auto.
apply Oeq_trans with (Ycart_one (fun x : nat => p x n) x0); auto.
apply ford_eq_elim with (n:=x0).
apply (monotonic_stable Ycart_one); auto.
rewrite Ycart_one_simpl; auto.
Save.

Instance FYcart_lt_mon : monotonic (fun (p: nat -> U) (y:nat) => [1-](F y) * p (S y)).
red; intros; auto.
Save.

Definition FYcart_lt : (nat -> U) -m> (nat -> U) :=
   mon (fun (p:nat->U) (y:nat) => [1-](F y) * p (S y)).

Lemma FYcart_lt_simpl : forall (p:nat -> U) (y:nat), FYcart_lt p y = [1-](F y) * p (S y).
trivial.
Save.

Lemma Ycart_ltx : forall x, mu (Ycart x) (carac_lt x) <= 0.
intros; apply Ole_trans with (mufix FYcart_lt x).
unfold Ycart; apply mu_mufix_le with (A:=nat) (B:=nat) (q:=carac_lt); intros; auto.
red; intros; rewrite FYcart_lt_simpl.
rewrite FYcart_val; unfold carac_lt.
rewrite carac_zero; auto with arith.
repeat Usimpl.
apply mu_monotonic; intro; apply carac_incl; red; auto with arith.
apply mufix_inv with (f:=fun y:nat => (0:U)); intro n; simpl; auto.
Save.

Lemma Ycart_eqx : forall x, mu (Ycart x) (carac (eq_nat_dec x)) == F x.
intros; apply Oeq_trans with (mufix (mon (cte (nat->U) F)) x).
unfold Ycart; apply Oeq_sym.
apply mufix_mu with (A:=nat) (B:=nat) (q:=fun (y:nat) => carac (eq_nat_dec y)); intros; auto.
apply Oeq_trans with (1:=FYcart_val (carac (eq_nat_dec x0)) f x0).
unfold cte; simpl.
rewrite (carac_one (eq_nat_dec x0) x0); auto; Usimpl.
assert ((mu (f (S x0)) (carac (eq_nat_dec x0)))==0).
apply Ule_zero_eq; apply Ole_trans with (mu (Mfix FYcart (S x0)) (carac (eq_nat_dec x0))).
apply H.
apply Ole_trans with (2:=Ycart_ltx (S x0)).
apply mu_monotonic; intro.
unfold carac_lt; apply carac_monotonic; intuition.
rewrite H0; repeat Usimpl; trivial.
apply ford_eq_elim with (n:=x); exact (mufix_cte F).
Save.

End YcartExample.
(* End Ycart. *)