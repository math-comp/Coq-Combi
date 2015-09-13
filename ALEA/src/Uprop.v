(** * Uprop.v : Properties of operators on [[0,1]] *)

Add Rec LoadPath "." as ALEA.

Set Implicit Arguments.
Require Export Utheory.
Require Export Arith.
Require Export Omega.

(* Module Univ_prop (Univ:Universe). *)

Open Local Scope U_scope.

Notation "[1/] n" := (Unth (pred n)) (at level 35, right associativity).

(** ** Direct consequences of axioms  *)

Lemma Uplus_le_compat_right : forall x y z:U, y <= z -> x + y <= x + z.
intros; apply Uplus_mon_right; trivial.
Save.
Hint Resolve Uplus_le_compat_right.

Instance Uplus_mon2 : monotonic2 Uplus.
intros; apply monotonic2_sym; auto.
Save.
Hint Resolve Uplus_mon2.

Lemma Uplus_le_compat_left : forall x y z:U, x <= y -> x + z <= y + z.
intros; apply Uplus_mon2; trivial.
Save.
Hint Resolve Uplus_le_compat_left.

Lemma Uplus_le_compat : forall x y z t, x <= y -> z <= t -> x + z <= y + t.
intros; apply Uplus_mon2; auto.
Save.
Hint Immediate Uplus_le_compat.

Lemma Uplus_eq_compat_left : forall x y z:U, x == y -> x + z == y + z.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve Uplus_eq_compat_left.

Lemma Uplus_eq_compat_right : forall x y z:U, x == y -> (z + x) == (z + y).
intros; apply Ole_antisym; auto.
Save.

Hint Resolve Uplus_eq_compat_left Uplus_eq_compat_right.

Add Morphism Uplus with signature Oeq ==> Oeq ==> Oeq as Uplus_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; apply Oeq_trans with (x1+x4); auto.
Qed.
Hint Immediate Uplus_eq_compat.

Add Morphism Uinv with signature Oeq ==> Oeq as Uinv_eq_compat.
intros; apply Ole_antisym; auto.
Qed.
Hint Resolve Uinv_eq_compat.

Lemma Uplus_zero_right : forall x:U, x + 0 == x.
intros; rewrite (Uplus_sym x 0); auto.
Save.
Hint Resolve Uplus_zero_right.

Lemma Uinv_opp_left : forall x, [1-] x + x == 1.
unfold U1; intros; transitivity ([1-](x + 0) + x); auto.
Save.
Hint Resolve Uinv_opp_left.

Lemma Uinv_opp_right : forall x, x + [1-] x == 1.
intros; transitivity ([1-] x + x); auto.
Save.
Hint Resolve Uinv_opp_right.

Lemma Uinv_inv : forall x : U, [1-] [1-] x == x.
intros; transitivity ([1-] (x + [1-] x) + x); auto.
apply Oeq_sym; auto.
rewrite (Uinv_opp_right x); rewrite Uinv_one; auto.
Save.
Hint Resolve Uinv_inv.

Lemma Unit : forall x:U, x <= 1.
intro; transitivity ([1-][1-]x); unfold U1; auto.
Save.
Hint Resolve Unit.

Lemma Uinv_zero : [1-] 0 = 1.
trivial.
Save.

Lemma Ueq_class : forall x y:U, class (x==y).
red; intros.
apply Ole_antisym;
apply Ule_class; intuition.
Save.

Lemma Ueq_double_neg : forall x y : U, ~ ~ (x == y) -> x == y.
exact Ueq_class.
Save.
Hint Resolve Ueq_class.
Hint Immediate Ueq_double_neg.

Lemma Ule_orc : forall x y : U, orc (x<=y) (~ x<=y).
auto.
Save.
Implicit Arguments Ule_orc [].

Lemma Ueq_orc : forall x y:U, orc (x==y) (~ x==y).
auto.
Save.
Implicit Arguments Ueq_orc [].

Lemma Upos : forall x:U, 0 <= x.
auto.
Save.

Lemma Ule_0_1 : 0 <= 1.
auto.
Save.

Hint Resolve Upos Ule_0_1.


(** ** Properties of [ == ] derived from properties of [ <= ] *)

Definition UPlus : U -m> U -m> U := mon2 Uplus.

Definition UPlus_simpl : forall x y, UPlus x y = x+y.
trivial.
Save.

Instance Uplus_continuous2 : continuous2 (mon2 Uplus).
apply continuous2_sym.
intros n m; repeat (rewrite mon2_simpl); auto.
intro k; apply continuous_eq_compat with (2:=Uplus_right_continuous k).
intro m; auto.
Save.

Hint Resolve Uplus_continuous2.

Lemma Uplus_lub_eq : forall f g : nat -m> U,
      lub f + lub g == lub ((UPlus @2 f) g).
intros; exact (lub_cont2_app2_eq UPlus f g).
Save.


Lemma Umult_le_compat_right : forall x y z:U, y <= z -> x * y <= x * z.
intros; apply Umult_mon_right; trivial.
Save.
Hint Resolve Umult_le_compat_right.

Instance Umult_mon2 : monotonic2 Umult.
apply monotonic2_sym; auto.
Save.

Lemma Umult_le_compat_left : forall x y z:U, x <= y -> x * z <= y * z.
intros; apply Umult_mon2; trivial.
Save.
Hint Resolve Umult_le_compat_left.

(*
Add Morphism Umult with signature Ole ++> Ole ++> Ole as Umult_le_compat.
intros x1 x2 H1 x3 x4 H2; apply Ole_trans with (x1 * x4); auto.
Save.
Hint Immediate Umult_le_compat.
*)

Lemma Umult_le_compat : forall x y z t, x <= y -> z <= t -> x * z <= y * t.
intros; apply Umult_mon2; trivial.
Save.
Hint Immediate Umult_le_compat.

Definition UMult : U -m> U -m> U := mon2 Umult.

Lemma Umult_eq_compat_left : forall x y z:U, x == y -> (x * z) == (y * z).
intros;  apply Ole_antisym; auto.
Save.
Hint Resolve Umult_eq_compat_left.

Lemma Umult_eq_compat_right :  forall x y z:U, x == y -> (z * x) == (z * y).
intros; transitivity (x * z); auto.
transitivity (y * z); auto.
Save.

Hint Resolve Umult_eq_compat_left Umult_eq_compat_right.


Definition UMult_simpl : forall x y, UMult x y = x*y.
trivial.
Save.

Instance Umult_continuous2 : continuous2 (mon2 Umult).
apply continuous2_sym.
intros; repeat (rewrite mon2_simpl); auto.
intro k; apply continuous_eq_compat with (2:=Umult_right_continuous k).
intro l; auto.
Save.
Hint Resolve Umult_continuous2.

Lemma Umult_lub_eq : forall f g : nat -m> U,
      lub f * lub g == lub ((UMult @2 f) g).
intros; exact (lub_cont2_app2_eq UMult f g).
Save.

Lemma Umultk_lub_eq : forall (k:U) (f : nat -m> U),
      k * lub f == lub (UMult k @ f).
intros; apply (lub_comp_eq (UMult k) f).
apply continuous2_app; auto.
Save.


(** ** [U] is a setoid *)

Add Morphism Umult with signature Oeq ==> Oeq ==> Oeq
   as Umult_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; transitivity (x1 * x4); auto.
Qed.

Hint Immediate Umult_eq_compat.

Instance Uinv_mon : monotonic (o1:=Iord U) Uinv.
red; simpl; intros; auto.
Save.

Definition UInv : U --m> U := mon (o1:=Iord U) Uinv.
 
Definition UInv_simpl : forall x, UInv x = [1-]x.
trivial.
Save.

(*
Add Morphism (Ole (o:=U)) with signature Oeq ==> iff as Ule_eq_compat_iff.
exact (Ole_eq_compat_iff o:=U)).
Save.
*)

Lemma Ule_eq_compat : 
forall x1 x2 : U, x1 == x2 -> forall x3 x4 : U, x3 == x4 -> x1 <= x3 -> x2 <= x4.
intros x1 x2 eq1 x3 x4 eq2; apply (Ole_eq_compat _ _ eq1 _ _ eq2); auto.
Save.

(* begin hide *)
(** Tactic for left normal form with respect to associativity *)
Ltac norm_assoc_left :=
     match goal with
      | |- context [(Uplus ?X1 (Uplus ?X2 ?X3))]
        => (setoid_rewrite (Uplus_assoc X1 X2 X3))
     end.

Ltac norm_assoc_right :=
     match goal with
      | |- context [(Uplus (Uplus ?X1 ?X2) ?X3)]
        => (setoid_rewrite <- (Uplus_assoc X1 X2 X3))
     end.
(* end hide *)


(** ** Properties of [ x < y ] on U *)

Lemma Ult_class : forall x y, class ( x < y ).
unfold Olt; auto.
Save.
Hint Resolve Ult_class.

Lemma Ult_notle_equiv : forall x y:U, x < y <-> ~ (y <= x).
split; auto.
intro; apply (Ule_total x y); intros; auto.
case (H H0).
Save.

Lemma notUle_lt : forall x y:U,  ~ (y <= x) -> x < y.
intros; rewrite Ult_notle_equiv; auto.
Save.

Hint Immediate notUle_lt.

Lemma notUlt_le : forall x y, ~ x < y -> y <= x.
intros; apply (Ule_class y x); auto.
Save.

Hint Immediate notUlt_le.

(** *** Properties of [ x <=  y ] *)

Lemma notUle_le : forall x y:U,  ~ (y <= x) -> x <= y.
intros; apply (Ule_total x y); intros; auto.
case H; trivial.
Save.
Hint Immediate notUle_le.

Lemma Ule_zero_eq :  forall x:U, x <= 0 -> x == 0.
intros; apply Ole_antisym; auto.
Save.

Lemma Uge_one_eq : forall x:U, 1 <= x -> x == 1.
intros; apply Ole_antisym; auto.
Save.

Hint Immediate Ule_zero_eq Uge_one_eq.

(** *** Properties of [ x < y ] *)

Lemma Ult_neq_zero : forall x, ~ 0 == x -> 0 < x.
auto.
Save.

Lemma Ult_neq_one : forall x, ~ 1 == x -> x < 1.
auto.
Save.

Hint Resolve Ule_total Ult_neq_zero Ult_neq_one.

Lemma not_Ult_eq_zero : forall x, ~ 0 < x -> 0 == x.
intros; unfold Olt; apply Ueq_class; intuition.
Save.

Lemma not_Ult_eq_one : forall x, ~ x < 1 -> 1 == x.
intros; unfold Olt; apply Ueq_class; intuition.
Save.

Hint Immediate not_Ult_eq_zero not_Ult_eq_one.

Lemma Ule_lt_orc_eq : forall x y, x <= y -> orc (x < y) (x == y).
intros; apply (Ueq_orc x y); auto.
Save.
Hint Resolve Ule_lt_orc_eq.

Lemma Udiff_lt_orc : forall x y, ~ x == y -> orc (x < y) (y < x).
intros; apply (Ule_total x y); auto.
Save.
Hint Resolve Udiff_lt_orc.


Lemma Uplus_pos_elim : forall x y,
      0 < x + y -> orc (0 < x) (0 < y).
intros; apply (Ueq_orc 0 x); auto.
intros; apply orc_right.
rewrite <- H0 in H; 
rewrite Uplus_zero_left in H; auto.
Save.

(** ** Properties of [ + ] and [ * ]  *)

Lemma Udistr_plus_left :  forall x y z, y <= [1-] z -> x * (y + z) == x * y + x * z.
intros.
rewrite (Umult_sym x (y+z)).
rewrite (Umult_sym x y).
rewrite (Umult_sym x z);auto.
Save.


Lemma Udistr_inv_left :  forall x y, [1-](x * y) == (x * ([1-] y)) + [1-] x.
intros.
setoid_rewrite (Umult_sym x y).
setoid_rewrite (Udistr_inv_right y x); auto.
Save.

Hint Resolve Uinv_eq_compat Udistr_plus_left Udistr_inv_left.

Lemma Uplus_perm2 : forall x y z:U, x + (y + z) == y + (x + z).
intros; setoid_rewrite (Uplus_assoc x y z).
setoid_rewrite (Uplus_sym x y); auto.
Save.

Lemma Umult_perm2 : forall x y z:U, x * (y * z) == y * (x * z).
intros; setoid_rewrite (Umult_assoc x y z).
setoid_rewrite (Umult_sym x y); auto.
Save.

Lemma Uplus_perm3 : forall x y z : U, (x + (y + z)) == z + (x + y).
intros; setoid_rewrite (Uplus_assoc x y z); auto.
Save.

Lemma Umult_perm3 : forall x y z : U, (x * (y * z)) == z * (x * y).
intros; setoid_rewrite (Umult_assoc x y z); auto.
Save.

Hint Resolve Uplus_perm2 Umult_perm2 Uplus_perm3 Umult_perm3.


(* ** Properties of [1-] *)

Lemma Uinv_simpl :  forall x y : U, [1-] x == [1-] y -> x == y.
intros; setoid_rewrite <- (Uinv_inv x);
 setoid_rewrite <- (Uinv_inv y); auto.
Save.

Hint Immediate Uinv_simpl.

Lemma Umult_decomp : forall x y, x == x * y + x * [1-]y.
intros; apply Oeq_trans with (x * (y + [1-]y)); auto.
apply Oeq_trans with (x * 1); auto.
rewrite Umult_sym; auto.
Save.
Hint Resolve Umult_decomp.

(** ** More properties on [+] and [*]  and [Uinv] *)
(*
Lemma Umult_le_compat_right :  forall x y z: U,  x <= y -> (z * x) <= (z * y).
intros; setoid_rewrite (Umult_sym z x); setoid_rewrite (Umult_sym z y).
apply Umult_le_compat_left; trivial.
Save.

Hint Resolve Umult_le_compat_right.
*)


Lemma Umult_one_right : forall x:U, x * 1 == x.
intros; setoid_rewrite (Umult_sym x 1); auto.
Save.
Hint Resolve Umult_one_right.

Lemma Umult_one_right_eq : forall x y:U, y == 1 -> x * y == x.
intros; rewrite H; auto.
Save.
Hint Resolve Umult_one_right_eq.

Lemma Umult_one_left_eq : forall x y:U, x == 1 -> x * y == y.
intros; rewrite H; auto.
Save.
Hint Resolve Umult_one_left_eq.

Lemma Udistr_plus_left_le :  forall x y z : U, x * (y + z) <= x * y + x * z.
intros; apply (Ule_total y ([1-]z)); intros; auto.
apply Ole_trans with (x *  ([1-]z+z)).
rewrite Uinv_opp_left; auto.
rewrite Udistr_plus_left; auto.
Save.

Lemma Uplus_eq_simpl_right :
forall x y z:U, z <= [1-] x -> z <= [1-] y -> (x + z) == (y + z) -> x == y.
intros; apply Ole_antisym.
apply Uplus_le_simpl_right with z; auto.
apply Uplus_le_simpl_right with z; auto.
Save.

Lemma Ule_plus_right : forall x y, x <= x + y.
intros; apply Ule_eq_compat with (x + 0) (x + y); auto.
Save.

Lemma Ule_plus_left : forall x y, y <= x + y.
intros; apply Ule_eq_compat with (0 + y) (x + y); auto.
Save.
Hint Resolve Ule_plus_right Ule_plus_left.

Lemma Ule_mult_right : forall x y, x * y <= x .
intros; apply Ule_eq_compat with (x * y) (x * 1); auto.
Save.

Lemma Ule_mult_left : forall x y, x * y <= y.
intros; apply Ule_eq_compat with (x * y) (1 * y); auto.
Save.
Hint Resolve Ule_mult_right Ule_mult_left.

Lemma Uinv_le_perm_right : forall x y:U, x <= [1-] y -> y <= [1-] x.
intros; apply Ole_trans with ([1-] ([1-] y)); auto.
Save.
Hint Immediate Uinv_le_perm_right.

Lemma Uinv_le_perm_left :  forall x y:U, [1-] x <= y -> [1-] y <= x.
intros; apply Ole_trans with ([1-] ([1-] x)); auto.
Save.
Hint Immediate Uinv_le_perm_left.

Lemma Uinv_le_simpl :  forall x y:U, [1-] x <= [1-] y -> y <= x.
intros; apply Ole_trans with ([1-] ([1-] x)); auto.
Save.
Hint Immediate Uinv_le_simpl.

Lemma Uinv_double_le_simpl_right : forall x y, x<=y -> x <= [1-][1-]y.
intros; apply Uinv_le_perm_right; auto.
Save.
Hint Resolve Uinv_double_le_simpl_right.

Lemma Uinv_double_le_simpl_left : forall x y, x<=y -> [1-][1-]x <= y.
intros; apply Uinv_le_perm_left; auto.
Save.
Hint Resolve Uinv_double_le_simpl_left.

Lemma Uinv_eq_perm_left :  forall x y:U, x == [1-] y -> [1-] x == y.
intros; apply Oeq_trans with ([1-] ([1-] y)); auto.
Save.
Hint Immediate Uinv_eq_perm_left.

Lemma Uinv_eq_perm_right :  forall x y:U, [1-] x == y ->  x == [1-] y.
intros; apply Oeq_trans with ([1-] ([1-] x)); auto.
Save.

Hint Immediate Uinv_eq_perm_right.

Lemma Uinv_eq : forall x y:U, x == [1-] y <-> [1-] x == y.
split; auto.
Save.
Hint Resolve Uinv_eq.

Lemma Uinv_eq_simpl :  forall x y:U, [1-] x == [1-] y -> x == y.
intros; apply Oeq_trans with ([1-] ([1-] x)); auto.
Save.
Hint Immediate Uinv_eq_simpl.

Lemma Uinv_double_eq_simpl_right : forall x y, x==y -> x == [1-][1-]y.
intros; apply Uinv_eq_perm_right; auto.
Save.
Hint Resolve Uinv_double_eq_simpl_right.

Lemma Uinv_double_eq_simpl_left : forall x y, x==y -> [1-][1-]x == y.
intros; apply Uinv_eq_perm_left; auto.
Save.
Hint Resolve Uinv_double_eq_simpl_left.

Lemma Uinv_plus_right : forall x y, y <= [1-] x -> [1-] (x + y) + y == [1-] x.
intros; setoid_rewrite (Uplus_sym x y); auto.
Save.
Hint Resolve Uinv_plus_right.

Lemma Uplus_eq_simpl_left :
forall x y z:U, x <= [1-] y -> x <= [1-] z -> (x + y) == (x + z) -> y == z.
intros x y z H1 H2; setoid_rewrite (Uplus_sym x y); setoid_rewrite (Uplus_sym x z); auto.
intros; apply Uplus_eq_simpl_right with x; auto.
Save.

Lemma Uplus_eq_zero_left : forall x y:U, (x <= [1-] y)-> (x + y) == y -> x == 0.
intros.
apply Uplus_eq_simpl_right with y; auto.
setoid_rewrite H0; auto.
Save.

Lemma Uplus_le_zero_left : forall x y:U, x <= [1-] y -> (x + y) <= y -> x == 0.
intros; apply Uplus_eq_zero_left with y; auto.
Save.

Lemma Uplus_le_zero_right : forall x y:U, x <= [1-] y -> (x + y) <= x -> y == 0.
intros; apply Uplus_le_zero_left with x; auto.
rewrite Uplus_sym; auto.
Save.

Lemma Uinv_le_trans : forall x y z t, x <= [1-] y -> z <= x -> t <= y -> z <= [1-] t.
intros; apply Ole_trans with x; auto.
apply Ole_trans with ([1-] y); auto.
Save.


Lemma Uinv_plus_left_le : forall x y, [1-]y <= [1-](x+y) + x.
intros; apply (Ule_total y ([1-]x)); auto; intros.
rewrite Uinv_plus_left; auto.
apply Ole_trans with x; auto.
Save.

Lemma Uinv_plus_right_le : forall x y, [1-]x <= [1-](x+y) + y.
intros; apply (Ule_total y ([1-]x)); auto; intros.
rewrite Uinv_plus_right; auto.
apply Ole_trans with y; auto.
Save.

Hint Resolve Uinv_plus_left_le Uinv_plus_right_le.

(** ** Disequality *)

Lemma neq_sym : forall x y:U, ~ x==y -> ~ y==x.
red; intros; apply H; auto.
Save.
Hint Immediate neq_sym.

Lemma Uinv_neq_compat : forall x y, ~ x == y -> ~ [1-] x == [1-] y.
red; intros; apply H; auto.
Save.

Lemma Uinv_neq_simpl : forall x y, ~ [1-] x == [1-] y-> ~ x == y.
red; intros; apply H; auto.
Save.

Hint Resolve Uinv_neq_compat.
Hint Immediate Uinv_neq_simpl.

Lemma Uinv_neq_left : forall x y, ~ x == [1-] y -> ~ [1-] x == y.
red; intros; apply H; auto.
Save.

Lemma Uinv_neq_right : forall x y, ~ [1-] x == y -> ~x == [1-] y.
red; intros; apply H; auto.
Save.
Hint Immediate Uinv_neq_left Uinv_neq_right.

(** *** Properties of [<]  *)


Lemma Ult_0_1 : (0 < 1).
red; intuition.
Save.

Hint Resolve Ult_0_1.

Lemma Ule_neq_zero : forall (x y:U), ~ 0 == x -> x <= y -> ~ 0 == y.
red; intros.
apply H.
apply Ole_antisym; auto; rewrite H1; trivial.
Save.

Lemma Uplus_neq_zero_left : forall x y, ~ 0 == x -> ~ 0 == x+y.
intros; apply Olt_neq.
apply Olt_le_trans with x; auto.
Save.

Lemma Uplus_neq_zero_right : forall x y, ~ 0 == y -> ~ 0 == x+y.
intros; apply Olt_neq.
apply Olt_le_trans with y; auto.
Save.



Lemma Uplus_le_simpl_left : forall x y z : U, z <= [1-] x -> z + x <= z + y -> x <= y.
intros.
apply Uplus_le_simpl_right with z; auto.
apply Ole_trans with (z + x); auto.
apply Ole_trans with (z + y); auto.
Save.



Lemma Uplus_lt_compat_left : forall x y z:U, z <= [1-] y -> x < y -> (x + z) < (y + z).
intros x y z H (Hle,Hne); split; auto.
intro H1; apply Hne; apply Uplus_eq_simpl_right with z; auto.
transitivity ([1-] y); auto.
Save.

Lemma Uplus_lt_compat_right : forall x y z:U, z <= [1-] y -> x < y -> (z + x) < (z + y).
intros; setoid_rewrite (Uplus_sym z x).
intros; setoid_rewrite (Uplus_sym z y).
apply Uplus_lt_compat_left; auto.
Save.

Hint Resolve Uplus_lt_compat_right Uplus_lt_compat_left.


Lemma Uplus_one_le : forall x y, x + y == 1 -> [1-] y <= x.
intros; apply Ule_class; red; intros.
assert (x < [1-] y); auto.
assert (x + y < 1).
apply Olt_le_trans with ([1-] y + y); auto.
apply (Olt_antirefl 1).
rewrite <- H at 1; trivial.
Save.
Hint Immediate Uplus_one_le.


Lemma Uplus_one : forall x y, [1-] x <= y -> x + y == 1.
intros; apply Ole_antisym; auto.
transitivity (x + [1-] x); auto.
Save.
Hint Resolve Uplus_one.

Lemma Uplus_lt_Uinv_lt :   forall x y, x + y < 1 -> x < [1-] y.
intros; apply notUle_lt; intro.
apply (Olt_neq (x+y) 1); auto.
Save.
Hint Resolve Uplus_lt_Uinv_lt.

Lemma Uplus_one_lt : forall x y, x < [1-] y -> x + y < 1.
split; auto; intro.
apply Olt_notle with (1:=H); auto.
Save.
Hint Immediate Uplus_one_lt.

Lemma Uplus_lt_Uinv :   forall x y, x + y < 1 -> x <= [1-] y.
intros; apply Uplus_lt_Uinv_lt; auto.
Save.
Hint Immediate Uplus_lt_Uinv_lt.

Lemma Uplus_Uinv_one_lt : forall x y, x < y -> x + [1-]y < 1.
intros; apply Uplus_one_lt; auto.
rewrite Uinv_inv;  auto.
Save.
Hint Immediate Uplus_Uinv_one_lt.

Lemma Uinv_lt_perm_right : forall x y, x < [1-]y -> y < [1-]x.
intros x y (Hle,Hneq); split; auto.
apply Uinv_neq_right; auto.
Save.
Hint Immediate Uinv_lt_perm_right.

Lemma Uinv_lt_perm_left : forall x y, [1-]x < y -> [1-]y < x.
intros x y (Hle,Hneq); split; auto.
apply Uinv_neq_left; auto.
Save.
Hint Immediate Uinv_lt_perm_left.

Lemma Uplus_lt_compat_left_lt : forall x y z:U, z < [1-] x -> x < y -> (x + z) < (y + z).
intros x y z H (Hle,Hne); split; auto.
intro H1; apply Hne; apply Uplus_eq_simpl_right with z; auto.
apply Uplus_lt_Uinv_lt.
rewrite Uplus_sym; rewrite <- H1.
apply Uplus_one_lt; auto.
Save.

Lemma Uplus_lt_compat_right_lt : forall x y z:U, z < [1-] x -> x < y -> (z + x) < (z + y).
intros x y z H (Hle,Hne); split; auto.
intro H1; apply Hne; apply Uplus_eq_simpl_left with z; auto.
apply Uplus_lt_Uinv_lt.
rewrite <- H1.
apply Uplus_one_lt; auto.
Save.

Lemma Uplus_le_lt_compat_lt :
forall x y z t:U, z < [1-] x -> x <= y -> z < t -> (x + z) < (y + t).
intros; apply Olt_le_trans with (x + t); auto.
apply Uplus_lt_compat_right_lt; auto.
Save.

Lemma Uplus_lt_le_compat_lt :
forall x y z t:U, z < [1-] x -> x < y -> z <= t -> (x + z) < (y + t).
intros; apply Olt_le_trans with (y + z); auto.
apply Uplus_lt_compat_left_lt; auto.
Save.

Lemma Uplus_le_lt_compat :
forall x y z t:U, t <= [1-] y -> x <= y -> z < t -> (x + z) < (y + t).
intros; apply Ole_lt_trans with (y + z); auto.
Save.

Lemma Uplus_lt_le_compat :
forall x y z t:U, t <= [1-] y -> x < y -> z <= t -> (x + z) < (y + t).
intros; apply Ole_lt_trans with (x + t); auto.
Save.
Hint Immediate Uplus_le_lt_compat_lt Uplus_lt_le_compat_lt Uplus_le_lt_compat Uplus_lt_le_compat.

Lemma Uplus_lt_compat :
forall x y z t:U, t <= [1-] y -> x < y -> z < t -> (x + z) < (y + t).
intros; apply Olt_trans with (y + z); auto.
apply Uplus_lt_compat_left; auto.
transitivity t; auto.
Save.
Hint Immediate Uplus_lt_compat.

Lemma Uplus_lt_compat_lt :
forall x y z t:U, z < [1-] x -> x < y -> z < t -> (x + z) < (y + t).
intros; apply Uplus_lt_le_compat_lt; auto.
Save.
Hint Immediate Uplus_lt_compat_lt.

Lemma Ult_plus_left : forall x y z : U,  x < y -> x < y + z.
intros; apply Olt_le_trans with y; auto.
Save. 

Lemma Ult_plus_right : forall x y z : U,  x < z -> x < y + z.
intros; apply Olt_le_trans with z; auto.
Save. 
Hint Immediate Ult_plus_left Ult_plus_right.

Lemma Uplus_lt_simpl_left : forall x y z:U, z + x < z + y -> x < y.
intros; rewrite Ult_notle_equiv.
intro H1.
apply (Olt_notle _ _ H); auto.
Save.

Lemma Uplus_lt_simpl_right : forall x y z:U, (x + z) < (y + z) -> x < y.
intros; rewrite Ult_notle_equiv.
intro H1; apply (Olt_notle _ _ H); auto.
Save.



Lemma Uplus_eq_zero : forall x, x < 1 -> (x + x) == x -> x == 0.
intros x H1 H2; assert (x <= [1-]x).
apply Uplus_lt_Uinv; rewrite H2; auto.
apply Uplus_eq_simpl_left with x; auto.
rewrite H2; auto.
Save.

Lemma Umult_zero_left : forall x, 0 * x == 0.
intros; apply Uinv_simpl.
rewrite (Udistr_inv_right 0 x); auto.
Save.
Hint Resolve Umult_zero_left.

Lemma Umult_zero_right : forall x, (x * 0) == 0.
intros; rewrite (Umult_sym x 0); auto.
Save.
Hint Resolve Uplus_eq_zero Umult_zero_right.

Lemma Umult_zero_left_eq : forall x y, x == 0 -> x * y == 0.
intros; rewrite H; auto.
Save.

Lemma Umult_zero_right_eq : forall x y, y == 0 -> x * y == 0.
intros; rewrite H; auto.
Save.

Lemma Umult_zero_eq : forall x y z, x == 0 -> x * y == x * z.
intros; rewrite H.
rewrite Umult_zero_left; auto.
Save.

(** *** Compatibility of operations with respect to order. *)

Lemma Umult_le_simpl_right : forall x y z, ~ 0 == z -> (x * z) <= (y * z) -> x <= y.
intros; apply Umult_le_simpl_left with z; auto.
setoid_rewrite (Umult_sym z x);
setoid_rewrite (Umult_sym z y);trivial.
Save.
Hint Resolve Umult_le_simpl_right.

Lemma Umult_simpl_right : forall x y z, ~ 0 == z -> (x * z) == (y * z) -> x == y.
intros; apply Ole_antisym; auto.
apply Umult_le_simpl_right with z; auto.
apply Umult_le_simpl_right with z; auto.
Save.

Lemma Umult_simpl_left : forall x y z, ~ 0 == x -> (x * y) == (x * z) -> y == z.
intros; apply Ole_antisym; auto.
apply Umult_le_simpl_left with x; auto.
apply Umult_le_simpl_left with x; auto.
Save.

Lemma Umult_lt_compat_left : forall x y z, ~ 0 == z -> x < y -> (x * z) < (y * z).
intros x y z H (Hle,Hne); split; auto.
intro H1; apply Hne; apply Umult_simpl_right with z; auto.
Save.

Lemma Umult_lt_compat_right : forall x y z, ~ 0 == z -> x < y -> (z * x) < (z * y).
intros x y z H (Hle,Hne); split; auto.
intro H1; apply Hne; apply Umult_simpl_left with z; auto.
Save.


Lemma Umult_lt_simpl_right : forall x y z, ~ 0 == z -> (x * z) < (y * z) -> x < y.
intros x y z H (Hle,Hne); split; auto.
apply Umult_le_simpl_right with z; auto.
Save.

Lemma Umult_lt_simpl_left : forall x y z, ~ 0 == z -> (z * x) < (z * y) -> x < y.
intros x y z H (Hle,Hne); split; auto.
apply Umult_le_simpl_left with z; auto.
Save.

Hint Resolve Umult_lt_compat_left Umult_lt_compat_right.

Lemma Umult_zero_simpl_right : forall x y, 0 == x * y -> ~ 0 == x -> 0 == y.
intros.
apply Umult_simpl_left with x; auto.
rewrite (Umult_zero_right x); trivial.
Save.

Lemma Umult_zero_simpl_left : forall x y, 0 == x * y -> ~ 0 == y -> 0 == x.
intros.
apply Umult_simpl_right with y; auto.
rewrite (Umult_zero_left y); trivial.
Save.


Lemma Umult_neq_zero : forall x y, ~ 0 == x -> ~ 0 == y -> ~ 0 == x*y.
red; intros.
apply H0; apply Umult_zero_simpl_right with x; trivial.
Save.
Hint Resolve Umult_neq_zero.

Lemma Umult_lt_zero : forall x y, 0 < x -> 0 < y -> 0 < x*y.
auto.
Save.
Hint Resolve Umult_lt_zero.

Lemma Umult_lt_compat : forall x y z t, x < y -> z < t -> x * z < y * t.
intros.
assert (0<y); auto.
apply Ole_lt_trans with x; auto.
assert (0<t); auto.
apply Ole_lt_trans with z; auto.
apply (Ueq_orc 0 z); auto; intros.
rewrite <- H3.
rewrite Umult_zero_right; auto.
apply Olt_trans with (y * z); auto.
Save.


(** *** More Properties *)

Lemma Uplus_one_right : forall x, x + 1 == 1.
auto.
Save.

Lemma Uplus_one_left : forall x:U, 1 + x == 1.
auto.
Save.
Hint Resolve Uplus_one_right Uplus_one_left.

Lemma Uinv_mult_simpl : forall x y z t, x <= [1-] y -> (x * z) <= [1-] (y * t).
intros; apply Ole_trans with x; auto.
intros; apply Ole_trans with ([1-] y); auto.
Save.
Hint Resolve Uinv_mult_simpl.

Lemma Umult_inv_plus :   forall x y, x * [1-] y + y == x + y * [1-] x.
intros; apply Oeq_trans with (x * [1-] y + y * ([1-] x + x)).
setoid_rewrite (Uinv_opp_left x); auto.
assert (H:[1-] x <= [1-] x); auto.
rewrite (Udistr_plus_left y ([1-]x) x H).
apply Oeq_trans with (x * [1-] y + y * x + y * [1-] x).
norm_assoc_right; auto.
rewrite (Umult_sym y x).
assert (H1:[1-] y <= [1-] y); auto.
rewrite <- (Udistr_plus_left x ([1-]y) y H1).
setoid_rewrite (Uinv_opp_left y); auto.
Save.
Hint Resolve Umult_inv_plus.

Lemma Umult_inv_plus_le : forall x y z, y <= z -> x * [1-] y + y <= x * [1-] z + z.
intros.
setoid_rewrite (Umult_inv_plus x y);
setoid_rewrite (Umult_inv_plus x z); auto.
Save.
Hint Resolve Umult_inv_plus_le.


Lemma Uinv_lt_compat : forall x y : U, x < y -> [1-] y < [1-] x.
intros; apply Uinv_lt_perm_right.
rewrite Uinv_inv; trivial.
Save.
Hint Resolve Uinv_lt_compat.

Lemma Uinv_lt_simpl : forall x y : U, [1-] y < [1-] x -> x < y.
intros; rewrite <- (Uinv_inv x); rewrite <- (Uinv_inv y); auto.
Save.
Hint Immediate Uinv_lt_simpl.

Lemma Ult_inv_Uplus : forall x y, x < [1-] y -> x + y < 1.
intros x y H; apply notUle_lt; intro H1.
apply (Olt_notle _ _ H); auto.
apply Uplus_one_le; auto.
Save.

Hint Immediate Uplus_lt_Uinv Uinv_lt_perm_left Uinv_lt_perm_right Ult_inv_Uplus.

Lemma Uinv_lt_one : forall x, 0 < x -> [1-]x < 1.
intros; assert ([1-]1 < x); auto.
rewrite Uinv_one; auto.
Save.

Lemma Uinv_lt_zero : forall x, x < 1 -> 0 < [1-]x.
intros; assert (x < [1-]0); auto.
Save.

Hint Resolve Uinv_lt_one Uinv_lt_zero.

Lemma orc_inv_plus_one : forall x y, orc (x<=[1-]y) (x+y==1).
intros; apply (Ule_total x ([1-]y)); intro; auto.
apply class_orc; trivial.
Save.

Lemma Umult_lt_right : forall p q, p <1 -> 0 < q -> p * q < q.
intros.
apply Olt_le_trans with (1 * q); auto.
Save.

Lemma Umult_lt_left : forall p q, 0 < p -> q < 1 -> p * q < p.
intros.
apply Olt_le_trans with (p * 1); auto.
Save.

Hint Resolve Umult_lt_right Umult_lt_left.

(** Variant of Uplus_lt_compat_left and right with alternative condition on non overflow *)

Lemma Uplus_lt_compat_l : forall x y z:U, x + z < 1 -> x < y -> (x + z) < (y + z).
intros; apply (orc_inv_plus_one z y); auto.
intros; apply Olt_le_trans with 1; auto.
rewrite <- H1; auto.
Save.

Lemma Uplus_lt_compat_r : forall x y z:U, z + x < 1 -> x < y -> (z + x) < (z + y).
intros x y z; setoid_rewrite (Uplus_sym z x); intros.
intros; setoid_rewrite (Uplus_sym z y).
apply Uplus_lt_compat_l; auto.
Save.

Hint Resolve Uplus_lt_compat_r Uplus_lt_compat_l.

(** ** Definition of [ x ^ n ] *)
Fixpoint Uexp (x:U) (n:nat) {struct n} : U :=
   match n with 0 => 1 | (S p) => x * Uexp x p end.

Infix "^" := Uexp : U_scope.

Lemma Uexp_1 : forall x, x^1 == x.
simpl Uexp; auto.
Save.

Lemma Uexp_0 : forall x, x^0 == 1.
simpl Uexp; auto.
Save.

Lemma Uexp_zero : forall n, (0<n)%nat -> 0^n == 0.
destruct n; simpl Uexp; intro; auto.
casetype False; omega.
Save.

Lemma Uexp_one : forall n, 1^n == 1.
induction n; simpl Uexp; auto.
Save.

Lemma Uexp_le_compat_right :
      forall x n m, (n<=m)%nat -> x^m <= x^n.
induction 1; simpl; auto.
apply Ole_trans with (x^m); auto.
Save.

Lemma Uexp_le_compat_left :  forall x y n,  x <= y -> x^n <= y^n.
induction n; simpl; intros; auto.
apply Ole_trans with (x * (y^n)); auto.
Save.
Hint Resolve Uexp_le_compat_left Uexp_le_compat_right.

Lemma Uexp_le_compat : forall x y (n m:nat), 
	x <= y -> n <= m -> x^m <= y^n.
intros; apply Ole_trans with (x^n); auto.
Save.

Instance Uexp_mon2 : monotonic2 (o1:=Iord U) (o3:=Iord U) Uexp.
red; simpl; intros; apply Uexp_le_compat; trivial.
Save.

Definition UExp : U --m> (nat -m-> U) := mon2 Uexp.


Add Morphism Uexp with signature Oeq ==> eq ==> Oeq as Uexp_eq_compat.
intros; apply Ole_antisym; auto.
Save.

Lemma Uexp_inv_S : forall x n, ([1-]x^(S n)) == x * ([1-]x^n)+[1-]x.
simpl Uexp; auto.
Save.

Lemma Uexp_lt_compat : forall p q n, (O<n)%nat -> p<q -> (p^n<q^n).
induction n; simpl Uexp; intros; auto.
casetype False; omega.
destruct n; auto.
apply Umult_lt_compat; auto with arith.
Save.

Hint Resolve Uexp_lt_compat.

Lemma Uexp_lt_zero : forall p n, (0<p) -> (0<p^n).
destruct n; intros; auto.
rewrite <- (Uexp_zero (n:=S n)); auto with arith.
Save.
Hint Resolve Uexp_lt_zero.

Lemma Uexp_lt_one : forall p n, (0<n)%nat -> p<1 -> (p^n<1).
intros; rewrite <- (Uexp_one n); auto with arith.
Save.
Hint Resolve Uexp_lt_one.

Lemma Uexp_lt_antimon: forall p n m, 
    (n<m)%nat-> 0 < p -> p < 1 -> p^m < p^n.
induction 1; simpl; intros; auto with arith.
apply Olt_trans with (p*p^n); auto with arith.
Save.
Hint Resolve Uexp_lt_antimon.

(** ** Properties of division *)

Lemma Udiv_mult : forall x y, ~ 0 == y -> x <= y -> (x/y) * y == x.
intros; rewrite Umult_sym; auto.
Save.
Hint Resolve Udiv_mult.

Lemma Umult_div_le : forall x y, y * (x / y) <= x.
intros; apply (Ueq_orc 0 y); auto; intros.
apply Ole_trans with (0 * (x/y)); auto.
rewrite Umult_zero_left; auto.
intros; apply (Ule_total x y); auto; intros.
rewrite Udiv_le_one; auto.
rewrite Umult_one_right; auto.
Save.
Hint Resolve Umult_div_le.

Lemma Udiv_mult_le : forall x y, (x/y) * y <= x.
intros; rewrite Umult_sym; auto.
Save.
Hint Resolve Udiv_mult_le.

Lemma Udiv_le_compat_left :  forall x y z, x <= y -> x/z <= y/z.
intros; apply (Ueq_orc 0 z); auto; intros.
rewrite (Udiv_by_zero x); auto.
intros; apply (Ule_total y z); auto; intros.
apply Umult_le_simpl_right with z; auto.
rewrite (Udiv_mult x); auto.
rewrite (Udiv_mult y); auto.
transitivity y; auto.
rewrite (Udiv_le_one y); auto.
Save.
Hint Resolve Udiv_le_compat_left.

Lemma Udiv_eq_compat_left : forall x y z, x == y -> x/z == y/z.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve Udiv_eq_compat_left.


Lemma Umult_div_le_left : forall x y z, ~ 0==y -> x*y <= z -> x <= z/y.
intros; apply (Ule_total y z); auto; intros.
rewrite (Udiv_le_one z); auto.
apply Umult_le_simpl_right with y; auto.
apply Ole_trans with z; auto.
rewrite (Udiv_mult z y H); auto.
Save.

Lemma Udiv_le_compat_right : forall x y z, ~ 0==y -> y <= z ->  x/z <= x/y.
intros; assert (~ 0 == z).
apply Ule_neq_zero with y; auto.
apply (Ule_total z x); auto; intros.
rewrite Udiv_le_one; auto.
rewrite Udiv_le_one; auto.
apply Ole_trans with z; trivial.
apply Umult_div_le_left; auto.
apply Ole_trans with (x/z * z); auto.
Save.
Hint Resolve Udiv_le_compat_right.

Lemma Udiv_eq_compat_right : forall x y z, y == z -> x/z == x/y.
intros; apply (Ueq_orc 0 y); auto; intros.
assert (0==z).
rewrite <- H; auto.
repeat rewrite Udiv_by_zero; auto.
assert (~ 0 == z).
apply Ule_neq_zero with y; auto.
apply Ole_antisym; auto.
Save.
Hint Resolve Udiv_eq_compat_right.

Add Morphism Udiv with signature Oeq ==> Oeq ==> Oeq as Udiv_eq_compat.
intros x1 x2 eq1 x3 x4 eq2.
transitivity (x2/x3); auto.
Save.

Add Morphism Udiv with signature Ole ++> Oeq ==> Ole as Udiv_le_compat.
intros x1 x2 le1 x3 x4 le2; transitivity (x2/x3); auto.
Save.

Lemma Umult_div_eq : forall x y z, ~ 0 == y -> x * y == z -> x == z/y.
intros; apply Umult_simpl_right with y; auto.
assert (z<=y).
transitivity (x*y); auto.
transitivity z; auto.
apply Oeq_sym; auto.
Save.

Lemma Umult_div_le_right : forall x y z,  x <= y * z -> x/z <= y.
intros; apply (Ueq_orc 0 z); auto; intros.
rewrite Udiv_by_zero; auto.
apply Umult_le_simpl_right with z; auto.
assert (x<=z).
transitivity (y*z); auto.
rewrite (Udiv_mult x z H0); auto.
Save.

Lemma Udiv_le : forall x y, ~ 0 == y -> x <= x/y.
intros; apply Umult_div_le_left; auto.
Save.

Lemma Udiv_zero : forall x, 0/x == 0.
intros; apply (Ueq_orc 0 x); auto; intros.
apply Oeq_sym; apply Umult_div_eq; auto.
Save.
Hint Resolve Udiv_zero.

Lemma Udiv_zero_eq : forall x y, 0 == x -> x/y == 0.
intros; rewrite <- H; auto.
Save.
Hint Resolve Udiv_zero_eq.

Lemma Udiv_one : forall x, x/1 == x.
intros; apply Oeq_sym; apply Umult_div_eq; auto.
Save.
Hint Resolve Udiv_one.

Lemma Udiv_refl : forall x, ~ 0 == x -> x/x == 1.
auto.
Save.
Hint Resolve Udiv_refl.

Lemma Umult_div_assoc : forall x y z, y <= z->  (x * y) / z == x * (y/z).
intros; apply (Ueq_orc 0 z); auto; intros.
repeat rewrite Udiv_by_zero; auto.
apply Oeq_sym; apply Umult_div_eq; auto.
transitivity (x * (y / z * z)); auto.
Save.

Lemma Udiv_mult_assoc : forall x y z, x <= y * z ->  x/(y * z) == (x/y)/z.
intros; apply (Ueq_orc 0 z); auto; intros.
rewrite (Udiv_by_zero (x/y)); auto.
rewrite Udiv_by_zero; auto; rewrite <- H0; auto.
intros; apply (Ueq_orc 0 y); auto; intros.
rewrite (Udiv_by_zero x); auto.
rewrite <-H1; auto.
rewrite (Udiv_by_zero x); auto.
transitivity (0*z); auto.
apply Oeq_sym; apply Umult_div_eq; auto.
rewrite (Umult_sym y z).
transitivity (x / y / z * z * y); auto.
assert (x/y <= z).
apply Umult_div_le_right; auto.
transitivity (y*z); auto.
rewrite (Udiv_mult (x/y) z H0); auto.
assert (x<=y); auto.
transitivity (y*z); auto.
Save.

Lemma Udiv_inv : forall x y, ~ 0 == y -> [1-](x/y) <= ([1-]x)/y.
intros; apply (Ule_total x y); auto; intros.
apply Umult_div_le_left; auto.
transitivity ([1-] (x/y * y)); auto.
rewrite Udiv_le_one; auto.
Save.

Lemma Uplus_div_inv : forall x y z, x+y <= z -> x<=[1-]y -> x/z <= [1-](y/z).
intros; apply (Ueq_orc 0 z); auto; intros.
repeat (rewrite Udiv_by_zero; auto).
apply Umult_div_le_right; auto.
apply Uplus_le_simpl_right with ([1-]z).
apply Uinv_le_compat; transitivity (x+y); auto.
rewrite <- Udistr_inv_right.
rewrite Udiv_mult; auto.
transitivity (x+[1-](x+y)); auto.
rewrite Uplus_sym; rewrite Uinv_plus_left; auto.
transitivity (x+y); auto.
Save.
Hint Resolve Uplus_div_inv.

Lemma Udiv_plus_le : forall x y z,  x/z + y/z <= (x+y)/z.
intros; apply (Ueq_orc 0 z); auto; intros.
repeat (rewrite Udiv_by_zero; auto).
intros; apply Umult_div_le_left; auto.
rewrite Umult_sym; rewrite Udistr_plus_left_le.
apply Uplus_le_compat; rewrite Umult_sym; auto.
Save.
Hint Resolve Udiv_plus_le.

Lemma Udiv_plus : forall x y z, (x+y)/z == x/z + y/z.
intros; apply Ole_antisym; auto.
apply (Ueq_orc 0 z); auto; intros.
repeat (rewrite Udiv_by_zero; auto).
apply (Ule_total x z); auto; intros.
apply (Ule_total y z); auto; intros.
apply (Ule_total (x/z) ([1-](y/z))); auto; intros.
apply Umult_div_le_right; auto.
rewrite Udistr_plus_right; auto.
apply Uplus_le_compat; rewrite Udiv_mult; auto.
rewrite (Uplus_one (x/z) (y/z)); auto.
rewrite (Udiv_le_one y z H); auto.
transitivity 1; auto.
rewrite (Udiv_le_one x z H); auto.
transitivity 1; auto.
Save.
Hint Resolve Udiv_plus.

Lemma Umult_div_simpl_r : forall x y, ~ 0 == y -> (x * y) / y == x.
intros; symmetry.
apply Umult_div_eq; auto.
Save.
Hint Resolve Umult_div_simpl_r.

Lemma Umult_div_simpl_l : forall x y, ~ 0 == x -> (x * y) / x == y.
intros; rewrite Umult_sym; auto.
Save.
Hint Resolve Umult_div_simpl_l.

Instance Udiv_mon : forall k, monotonic (fun x => (x/k)).
red; auto.
Save.

Definition UDiv (k:U) : U -m> U := mon (fun x => (x/k)).

Lemma UDiv_simpl : forall (k:U) x, UDiv k x = x/k.
trivial.
Save.

(** printing & %\&% #&amp;# *)
(** ** Definition and properties of [x & y]
   A conjonction operation which coincides with min and mult
   on [0] and [1], see Morgan & McIver *)

Definition Uesp (x y:U) := [1-] ([1-] x + [1-] y).

Infix "&" := Uesp  (left associativity, at level 40) : U_scope.

Lemma Uinv_plus_esp : forall x y, [1-] (x + y) == [1-] x & [1-] y.
unfold Uesp; intros.
setoid_rewrite (Uinv_inv x); setoid_rewrite (Uinv_inv y); auto.
Save.
Hint Resolve Uinv_plus_esp.

Lemma Uinv_esp_plus : forall x y, [1-] (x & y) == [1-] x + [1-] y.
unfold Uesp; intros.
setoid_rewrite (Uinv_inv ([1-] x + [1-] y)); trivial.
Save.
Hint Resolve Uinv_esp_plus.


Lemma Uesp_sym : forall x y : U, x & y == y & x.
intros; unfold Uesp; auto.
Save.

Lemma Uesp_one_right : forall x : U, x & 1 == x.
intro; unfold Uesp.
setoid_rewrite Uinv_one.
setoid_rewrite (Uplus_zero_right ([1-] x)); auto.
Save.

Lemma Uesp_one_left : forall x : U, 1 & x  == x.
intros; rewrite Uesp_sym; apply Uesp_one_right.
Save.

Lemma Uesp_zero : forall x y, x <= [1-] y -> x & y == 0.
intros; unfold Uesp.
setoid_rewrite <- Uinv_one; auto.
Save.

Hint Resolve Uesp_sym Uesp_one_right Uesp_one_left Uesp_zero.

Lemma Uesp_zero_right : forall x : U, x & 0 == 0.
auto.
Save.

Lemma Uesp_zero_left : forall x : U, 0 & x == 0.
auto.
Save.

Hint Resolve Uesp_zero_right Uesp_zero_left.

Add Morphism Uesp with signature Oeq ==> Oeq ==> Oeq as Uesp_eq_compat.
unfold Uesp; intros.
apply Uinv_eq_compat.
rewrite H; rewrite H0; auto.
Save.

Lemma Uesp_le_compat : forall x y z t, x <= y -> z <=t -> x & z <= y &t .
unfold Uesp; intros.
apply Uinv_le_compat.
apply Uplus_le_compat; auto.
Save.

Hint Immediate Uesp_le_compat Uesp_eq_compat.

Lemma Uesp_assoc : forall x y z, x & (y & z) == x & y & z.
unfold Uesp; intros; apply Uinv_eq_compat.
repeat rewrite Uinv_inv; auto.
Save.
Hint Resolve Uesp_assoc.

Lemma Uesp_zero_one_mult_left : forall x y, orc (x == 0) (x == 1) -> x & y == x * y.
intros; apply H; intros; auto.
rewrite H0; rewrite Uesp_zero_left; auto. 
rewrite H0; rewrite Uesp_one_left; auto.
Save.

Lemma Uesp_zero_one_mult_right : forall x y, orc (y == 0) (y == 1) -> x & y == x * y.
intros; apply H; intros; auto.
rewrite H0; rewrite Uesp_zero_right; auto. 
rewrite H0; rewrite Uesp_one_right; auto.
Save.

Hint Resolve Uesp_zero_one_mult_left Uesp_zero_one_mult_right.

Instance Uesp_mon : monotonic2 Uesp.
red; auto.
Save.

Definition UEsp : U -m> U -m> U := mon2 Uesp.
             
Lemma UEsp_simpl : forall x y, UEsp x y = x & y.
trivial.
Save.


Lemma Uesp_le_left : forall x y, x & y <= x.
unfold Uesp; intros.
apply Uinv_le_perm_left; auto.
Save.

Lemma Uesp_le_right : forall x y, x & y <= y.
unfold Uesp; intros.
apply Uinv_le_perm_left; auto.
Save.

Hint Resolve Uesp_le_left Uesp_le_right.

Lemma Uesp_plus_inv : forall x y, [1-] y <= x -> x == x & y + [1-] y.
unfold Uesp; intros.
rewrite Uinv_plus_right; auto.
Save.
Hint Resolve Uesp_plus_inv.

Lemma Uesp_le_plus_inv : forall x y, x <= x & y + [1-] y.
intros; apply (Ule_total ([1-]y) x); intros; auto.
rewrite Uesp_zero; auto.
rewrite Uplus_zero_left; auto.
Save.
Hint Resolve Uesp_le_plus_inv.

Lemma Uplus_inv_le_esp : forall x y z, x <= y + ([1-] z) -> x & z <= y.
intros; unfold Uesp.
apply Uinv_le_perm_left.
transitivity ([1-](y+[1-]z) + [1-]z); auto.
Save.
Hint Immediate Uplus_inv_le_esp.

Lemma Ult_esp_left : forall x y z, x < z -> x & y < z.
intros; apply Ole_lt_trans with x; auto.
Save.

Lemma Ult_esp_right : forall x y z, y < z -> x & y < z.
intros; apply Ole_lt_trans with y; auto.
Save.

Hint Immediate Ult_esp_left Ult_esp_right.

Lemma Uesp_lt_compat_left : forall x y z, [1-]x <= z -> x < y -> x & z < y & z.
intros; unfold Uesp.
apply Uinv_lt_compat.
apply Uplus_lt_compat_left; auto.
Save.
Hint Resolve Uesp_lt_compat_left.

Lemma Uesp_lt_compat_right : forall x y z, [1-]x <= y -> y < z -> x & y < x & z.
intros; rewrite (Uesp_sym x z); rewrite (Uesp_sym x y); auto.
Save.
Hint Resolve Uesp_lt_compat_left.

Lemma Uesp_le_one_right : forall x y, [1-]x <= y -> (x <= x & y) -> y == 1.
intros; rewrite <- Uinv_zero.
apply Uinv_eq_perm_right.
apply Uplus_le_zero_right with ([1-]x); auto.
Save.

Lemma Uesp_eq_one_right : forall x y, [1-]x <= y -> (x == x & y) -> y == 1.
intros; apply Uesp_le_one_right with x; auto.
Save.

Lemma Uesp_le_one_left : forall x y, [1-]x <= y -> y <= x & y -> x == 1.
intros; apply Uesp_le_one_right with y; auto.
rewrite Uesp_sym; auto.
Save.

(** ** Definition and properties of [x - y] *)

Definition Uminus (x y:U) := [1-] ([1-] x + y).

Infix "-" := Uminus : U_scope.

Lemma Uminus_le_compat_left : forall x y z, x <= y -> x - z <= y - z.
unfold Uminus; auto.
Save.

Lemma Uminus_le_compat_right :  forall x y z, y <= z -> x - z <= x - y.
unfold Uminus; auto.
Save.

Hint Resolve Uminus_le_compat_left Uminus_le_compat_right.

Lemma Uminus_le_compat : forall x y z t, x <= y ->  t <= z -> x - z <= y - t.
intros; transitivity (x-t); auto.
Save.

Hint Immediate Uminus_le_compat.

Add Morphism Uminus with signature Oeq ==> Oeq ==> Oeq as Uminus_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; apply Ole_antisym;
transitivity (x1-x4); auto.
Save.
Hint Immediate Uminus_eq_compat.


Lemma Uminus_zero_right : forall x, x - 0 == x.
unfold Uminus; intros.
setoid_rewrite (Uplus_zero_right ([1-] x)); auto.
Save.

Lemma Uminus_one_left : forall x, 1 - x == [1-] x.
unfold Uminus; intros.
setoid_rewrite Uinv_one; auto.
Save.

Lemma Uminus_le_zero : forall x y, x <= y -> x - y == 0.
unfold Uminus; intros.
setoid_rewrite <- Uinv_one.
apply Uinv_eq_compat.
apply Ole_antisym; auto.
transitivity ([1-] y + y); auto.
Save.

Hint Resolve Uminus_zero_right Uminus_one_left Uminus_le_zero.


Lemma Uminus_zero_left :  forall x,  0 - x == 0.
auto.
Save.
Hint Resolve Uminus_zero_left.

Lemma Uminus_one_right :  forall x,  x - 1 == 0.
auto.
Save.
Hint Resolve Uminus_one_right.


Lemma Uminus_eq : forall x, x - x == 0.
auto.
Save.
Hint Resolve Uminus_eq.

Lemma Uminus_le_left : forall x y, x - y <= x.
unfold Uminus; auto.
Save.

Hint Resolve Uminus_le_left.


Lemma Uminus_le_inv : forall x y, x - y <= [1-]y.
intros.
unfold Uminus.
apply Uinv_le_compat; auto.
Save.
Hint Resolve Uminus_le_inv.

Lemma Uminus_plus_simpl : forall x y, y <= x -> (x - y) + y == x.
unfold Uminus; intros.
rewrite (Uinv_plus_right ([1-]x) y); auto.
Save.

Lemma Uminus_plus_zero : forall x y, x <= y -> (x - y) + y == y.
intros; rewrite (Uminus_le_zero x y); auto.
Save.

Hint Resolve Uminus_plus_simpl Uminus_plus_zero.

Lemma Uminus_plus_le : forall x y, x <= (x - y) + y.
intros; apply (Ule_total x y); intros; auto.
transitivity y ; auto.
rewrite (Uminus_plus_simpl x y H); trivial. 
Save.

Hint Resolve Uminus_plus_le.

Lemma Uesp_minus_distr_left : forall x y z, (x & y) - z  == (x - z) & y.
unfold Uesp, Uminus; intros.
apply Uinv_eq_compat.
setoid_rewrite (Uinv_inv ([1-] x + [1-] y)).
setoid_rewrite (Uinv_inv (([1-] x) + z)).
repeat norm_assoc_right; auto.
Save.

Lemma Uesp_minus_distr_right : forall x y z, (x & y) - z  == x & (y - z).
intros; rewrite (Uesp_sym x y).
setoid_rewrite (Uesp_sym x (y - z));
apply Uesp_minus_distr_left.
Save.

Hint Resolve Uesp_minus_distr_left Uesp_minus_distr_right.

Lemma Uesp_minus_distr : forall x y z t, (x & y) - (z + t) == (x - z) & (y - t).
unfold Uesp, Uminus; intros.
apply Uinv_eq_compat.
setoid_rewrite (Uinv_inv ([1-] x + [1-] y)).
setoid_rewrite (Uinv_inv ([1-] x + z)).
setoid_rewrite (Uinv_inv ([1-] y + t)).
repeat norm_assoc_right; auto.
Save.
Hint Resolve Uesp_minus_distr.

Lemma Uminus_esp_simpl_left : forall x y, [1-]x <= y -> x - (x & y) == [1-]y.
unfold Uesp,Uminus; intros.
apply Uinv_eq_compat.
rewrite (Uplus_sym ([1-]x)).
rewrite Uinv_plus_left; auto.
Save.

Lemma Uplus_esp_simpl : forall x y, (x - (x & y)) + y == x + y.
intros; apply (Ule_total ([1-]x) y); auto; intros.
rewrite Uminus_esp_simpl_left; auto.
rewrite (@Uplus_one x y); auto.
rewrite (@Uesp_zero x y); auto.
Save.
Hint Resolve Uminus_esp_simpl_left Uplus_esp_simpl.

Lemma Uplus_esp_simpl_right : forall x y, x + (y - (x & y)) == x + y.
intros; rewrite Uesp_sym; rewrite Uplus_sym.
rewrite (Uplus_sym x y); auto.
Save.
Hint Resolve Uplus_esp_simpl_right.


Lemma Uminus_esp_le_inv  : forall x y, x - (x & y) <= [1-]y.
intros; apply (Ule_total ([1-]x) y); auto; intros.
rewrite (@Uesp_zero x y); auto.
rewrite Uminus_zero_right; auto.
Save.

Hint Resolve Uminus_esp_le_inv.

Lemma Uplus_esp_inv_simpl : forall x y, x <= [1-]y -> (x + y) & [1-]y == x.
unfold Uesp; intros.
apply Uinv_eq_perm_left.
rewrite Uinv_inv; auto.
Save.
Hint Resolve Uplus_esp_inv_simpl.

Lemma Uplus_inv_esp_simpl : forall x y, x <= y -> (x + [1-]y) & y == x.
intros.
transitivity ((x + [1-] y) & [1-][1-]y); auto.
rewrite Uinv_inv; auto.
Save.
Hint Resolve Uplus_inv_esp_simpl.

(** ** Definition and properties of max *)

Definition max (x y : U) : U := (x - y) + y.

Lemma max_eq_left : forall x y : U, y <= x -> max x y == x.
unfold max; auto.
Save.

Lemma max_eq_right : forall x y : U, x <= y -> max x y == y.
unfold max; auto.
Save.

Hint Resolve max_eq_left max_eq_right.

Lemma max_eq_case : forall x y : U, orc (max x y == x) (max x y == y).
intros; apply (Ule_total x y); auto.
Save.

Add Morphism max with signature Oeq ==> Oeq ==> Oeq as max_eq_compat.
unfold max; intros.
apply Uplus_eq_compat; auto.
Save.

Lemma max_le_right : forall x y : U, x <= max x y.
intros; apply (Ule_total x y); intros; auto.
rewrite max_eq_right; auto.
rewrite max_eq_left; auto.
Save.

Lemma max_le_left : forall x y : U, y <= max x y.
intros; apply (Ule_total x y); intros; auto.
rewrite max_eq_right; auto.
rewrite max_eq_left; auto.
Save.

Hint Resolve max_le_right max_le_left.

Lemma max_le : forall x y z : U, x <= z -> y <= z -> max x y <= z.
intros; apply (Ule_total x y); intros; auto.
rewrite max_eq_right; auto.
rewrite max_eq_left; auto.
Save.

Lemma max_le_compat : forall x y z t: U, x <= y -> z <= t -> max x z <= max y t.
intros; apply max_le; auto.
transitivity y; auto.
transitivity t; auto.
Save.
Hint Immediate max_le_compat.

Lemma max_idem : forall x, max x x == x.
intros; unfold max; auto.
Save.
Hint Resolve max_idem.

Lemma max_sym_le : forall x y, max x y <= max y x.
intros; apply max_le; auto.
Save.
Hint Resolve max_sym_le.

Lemma max_sym : forall x y, max x y == max y x.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve max_sym.

Lemma max_assoc : forall x y z, max x (max y z) == max (max x y) z.
intros; apply Ole_antisym; apply max_le; auto.
transitivity (max x y); auto.
transitivity (max y z); auto.
Save.
Hint Resolve max_assoc.

Lemma max_0 : forall x, max 0 x == x.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve max_0.

Instance max_mon : monotonic2 max.
red; auto.
Save.

Definition Max : U -m> U -m> U := mon2 max.

Lemma max_eq_mult : forall k x y, max (k*x) (k*y) == k * max x y.
intros; apply Ole_antisym.
apply max_le; auto.
apply (max_eq_case x y); auto; intro H; rewrite H; auto.
Save.

Lemma max_eq_plus_cte_right : forall x y k, max (x+k) (y+k) == (max x y) + k.
intros; apply Ole_antisym.
apply max_le; auto.
apply (max_eq_case x y); auto; intro H; rewrite H; auto.
Save.

Hint Resolve max_eq_mult max_eq_plus_cte_right.

(** ** Definition and properties of min *)

Definition min (x y : U) : U := [1-] ((y - x) + [1-]y).

Lemma min_eq_left : forall x y : U, x <= y -> min x y == x.
unfold min, Uminus; intros.
apply Uinv_eq_perm_left; auto.
Save.

Lemma min_eq_right : forall x y : U, y <= x -> min x y == y.
unfold min; intros.
rewrite Uminus_le_zero; auto.
Save.

Hint Resolve min_eq_right min_eq_left.

Lemma min_eq_case : forall x y : U, orc (min x y == x) (min x y == y).
intros; apply (Ule_total x y); auto.
Save.

Add Morphism min with signature Oeq ==>  Oeq ==> Oeq as min_eq_compat.
unfold min; intros.
apply Uinv_eq_compat; auto.
apply Uplus_eq_compat; auto.
Save.
Hint Immediate min_eq_compat.

Lemma min_le_right : forall x y : U, min x y <=x.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto.
Save.

Lemma min_le_left : forall x y : U, min x y <= y.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_left; auto.
Save.

Hint Resolve min_le_right min_le_left.

Lemma min_le : forall x y z : U, z <= x -> z <= y -> z <= min x y.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_left; auto.
rewrite min_eq_right; auto.
Save.

Lemma Uinv_min_max : forall x y, [1-](min x y)==max ([1-]x) ([1-]y).
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_left; auto; rewrite max_eq_left; auto.
rewrite min_eq_right; auto; rewrite max_eq_right; auto.
Save.

Lemma Uinv_max_min : forall x y, [1-](max x y)==min ([1-]x) ([1-]y).
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto; rewrite max_eq_right; auto.
rewrite min_eq_left; auto; rewrite max_eq_left; auto.
Save.

Lemma min_idem : forall x, min x x == x.
intros; unfold min.
rewrite Uminus_eq.
apply Uinv_eq_perm_left; trivial.
Save.


Lemma min_mult : forall x y k,
    min (k * x) (k * y) == k * (min x y).
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_left; auto; rewrite min_eq_left; auto.
rewrite min_eq_right; auto; rewrite min_eq_right; auto.
Save.
Hint Resolve min_mult.

Lemma min_plus : forall x1 x2 y1 y2,
    (min x1 x2)  + (min y1 y2) <= min (x1+y1) (x2+y2).
intros; apply min_le; auto.
Save.
Hint Resolve min_plus.

Lemma min_plus_cte : forall x y k, min (x + k) (y + k) == (min x y) + k.
intros; apply (Ule_total x y); intros; auto.
repeat (rewrite min_eq_left; auto).
rewrite min_eq_right; auto; rewrite min_eq_right; auto.
Save.
Hint Resolve min_plus_cte.

Lemma min_le_compat : forall x1 y1 x2 y2,
      x1<=y1 -> x2 <=y2 -> min x1 x2 <= min y1 y2.
intros; apply min_le.
transitivity x1; auto.
transitivity x2; auto.
Save.
Hint Immediate min_le_compat.


Lemma min_sym_le : forall x y, min x y <= min y x.
intros; apply min_le; auto.
Save.
Hint Resolve min_sym_le.

Lemma min_sym : forall x y, min x y == min y x.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve min_sym.

Lemma min_assoc : forall x y z, min x (min y z) == min (min x y) z.
intros; apply Ole_antisym; apply min_le; auto.
transitivity (min y z); auto.
transitivity (min x y); auto.
Save.
Hint Resolve min_assoc.

Lemma min_0 : forall x, min 0 x == 0.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve min_0.


Instance min_mon2 : monotonic2 min.
red; auto.
Save.

Definition Min : U -m> U -m> U := mon2 min.

Lemma Min_simpl : forall x y, Min x y = min x y.
trivial.
Save.

Lemma incr_decomp_aux : forall f g : nat -m>  U, 
     forall n1 n2, (forall m, ~ ((n1<=m)%nat /\ f n1 <= g m))
           -> (forall m, ~((n2<=m)%nat /\ g n2 <= f m)) -> (n1<=n2)%nat -> False.
intros; assert (absurd:~ g n2 < g n2); auto.
assert (~(f n1 <= g n2)).
apply not_and_elim_left with (1:= H n2); auto.
assert (~(g n2 <= f n2)); auto.
apply not_and_elim_left with (1:= H0 n2); auto.
apply absurd; apply Olt_le_trans with (f n1); auto.
transitivity (f n2); auto.
Save.

Lemma incr_decomp : forall f g: nat -m> U,
     orc (forall n, exc (fun m => (n<=m)%nat /\ f n <= g m)) 
           (forall n, exc (fun m => (n<=m)%nat /\ g n <= f m)).
intros f g; apply orc_intro; intros.
apply H; clear H; intros.
apply exc_intro_class; intros.
apply H0; clear H0; intros.
apply exc_intro_class; intros.
case (dec_le n n0); intro.
apply (incr_decomp_aux f g) with (n1:=n) (n2:=n0); auto.
apply (incr_decomp_aux g f) with (n1:=n0) (n2:=n); auto; omega.
Save.



(** ** Other properties *)
Lemma Uplus_minus_simpl_right : forall x y, y <= [1-] x -> (x + y) - y == x.
unfold Uminus; intros.
rewrite (Uinv_plus_right x y); auto.
Save.
Hint Resolve Uplus_minus_simpl_right.

Lemma Uplus_minus_simpl_left : forall x y, y <= [1-] x -> (x + y) - x == y.
intros; setoid_rewrite (Uplus_sym x y); auto.
Save.

Lemma Uminus_assoc_left : forall x y z, (x - y) - z == x - (y + z).
unfold Uminus; intros.
apply Uinv_eq_compat.
setoid_rewrite (Uinv_inv ([1-] x + y)); auto.
Save.

Hint Resolve Uminus_assoc_left.

Lemma Uminus_perm : forall x y z, (x - y) - z == (x - z) - y.
intros; rewrite Uminus_assoc_left.
rewrite (Uplus_sym y z); auto.
Save.
Hint Resolve Uminus_perm.

Lemma Uminus_le_perm_left : forall x y z, y <= x -> x - y <= z -> x <= z + y.
intros; rewrite <- (Uminus_plus_simpl x y); auto.
Save.

Lemma Uplus_le_perm_left : forall x y z, x <= y + z  -> x - y <= z.
intros; apply (Ule_total y x); intros; auto.
apply Uplus_le_simpl_left with y.
unfold Uminus; setoid_rewrite (Uinv_inv ([1-] x + y)); auto.
setoid_rewrite (Uplus_sym y (x-y)); rewrite (Uminus_plus_simpl x y); auto.
transitivity (0:U); auto.
Save.
(*
Lemma Uplus_le_perm_left : forall x y z, y <= x -> x <= y + z  -> x - y <= z.
intros; apply Uplus_le_simpl_left with y.
unfold Uminus; setoid_rewrite (Uinv_inv ([1-] x + y)); auto.
setoid_rewrite (Uplus_sym y (x-y)); rewrite (Uminus_plus_simpl x y); auto.
Save.
*)

Lemma Uminus_eq_perm_left : forall x y z, y <= x -> x - y == z -> x == z + y.
intros; rewrite <- (Uminus_plus_simpl x y); auto.
Save.

Lemma Uplus_eq_perm_left : forall x y z, y <= [1-] z -> x == y + z  -> x - y == z.
intros; setoid_rewrite H0; auto.
setoid_rewrite (Uplus_sym y z); auto.
Save.

Hint Resolve Uminus_le_perm_left Uminus_eq_perm_left.
Hint Resolve Uplus_le_perm_left Uplus_eq_perm_left.

Lemma Uminus_le_perm_right : forall x y z, z <= y -> x <= y - z -> x + z <= y.
intros; rewrite <- (Uminus_plus_simpl y z); auto.
Save.

Lemma Uplus_le_perm_right : forall x y z, z <= [1-] x -> x + z <= y  -> x <= y - z.
intros; apply Uplus_le_simpl_right with z; auto.
Save.
Hint Resolve Uminus_le_perm_right Uplus_le_perm_right.

Lemma Uminus_le_perm : forall x y z, z <= y -> x <= [1-] z -> x <= y - z -> z <= y - x.
intros; apply Uplus_le_perm_right; auto.
setoid_rewrite (Uplus_sym z x); auto.
Save.
Hint Resolve Uminus_le_perm.

Lemma Uminus_eq_perm_right : forall x y z, z <= y -> x == y - z -> x + z == y.
intros; transitivity (y - z + z); auto.
Save.
Hint Resolve Uminus_eq_perm_right.

Lemma Uminus_plus_perm : forall x y z, y <= x -> z <= [1-]x -> (x - y) + z == (x + z) - y.
intros; apply Uminus_eq_perm_right.
transitivity (y + z - y); auto.
rewrite Uplus_minus_simpl_left; auto.
transitivity ([1-]x); auto.
rewrite Uminus_perm.
rewrite Uplus_minus_simpl_right; auto.
Save.


Lemma Uminus_zero_le : forall x y, x - y == 0 -> x <= y.
intros x y; unfold Uminus; intros.
setoid_rewrite <- (Uinv_inv x).
apply Uplus_one_le.
setoid_rewrite <- Uinv_zero; auto.
setoid_rewrite <- H; auto.
Save.

Lemma Uminus_lt_non_zero : forall x y, x < y -> ~ 0 == y - x.
intros x y H1 H2.
apply (Olt_notle _ _ H1); auto.
apply Uminus_zero_le; auto.
Save.
Hint Immediate Uminus_zero_le Uminus_lt_non_zero.

Lemma Ult_le_nth_minus : forall x y, x < y -> exc (fun n => x <= y - [1/]1+n).
intros; apply (archimedian (y - x)); intros; auto.
apply exc_intro with x0.
apply Uminus_le_perm; auto.
transitivity (y - x); auto. 
Save.


Lemma Uinv_plus_minus_left : forall x y, [1-](x + y) == [1-]x - y.
intros; unfold Uminus; apply Uinv_eq_compat; auto.
Save.

Lemma Uinv_plus_minus_right : forall x y, [1-](x + y) == [1-]y - x.
intros; rewrite Uplus_sym; unfold Uminus; apply Uinv_eq_compat; auto.
Save.

Hint Resolve Uinv_plus_minus_left Uinv_plus_minus_right.

Lemma Ult_le_nth_plus : forall x y, x < y -> exc (fun n : nat => x + [1/]1+n <= y).
intros.
assert (not (0==y-x)); auto.
assert (H1:exc (fun n => [1/]1+n <= y - x)).
apply archimedian; auto.
apply H1;auto;  intros n H2.
apply exc_intro with n.
transitivity (x + (y - x)); auto.
Save.

Lemma Uminus_distr_left : forall x y z, (x - y) * z == (x * z) - (y * z).
intros; apply (Ule_total x y); intros; auto.
(* first case x <= y, left and right hand side equal 0 *)
rewrite (Uminus_le_zero x y); trivial.
rewrite (Umult_zero_left z).
assert (x * z <= y * z); auto.
rewrite (Uminus_le_zero _ _ H0); auto.
(* second case y <= x, use simplification *)
unfold Uminus; intros; auto.
apply Uplus_eq_simpl_right with (y * z); auto.
assert ([1-] ([1-] x + y) <= [1-] y); auto.
rewrite <- (Udistr_plus_right _ _ z H0); auto.
assert (y <= [1-] ([1-] x)); auto.
rewrite (Uinv_plus_right _ _ H1).
rewrite (Uinv_inv x); auto.
Save.

Hint Resolve Uminus_distr_left.

Lemma Uminus_distr_right : forall x y z,  x * (y - z) == (x * y) - (x * z).
intros; setoid_rewrite (Umult_sym x y).
setoid_rewrite (Umult_sym x z).
setoid_rewrite (Umult_sym x (y - z)); auto.
Save.

Hint Resolve Uminus_distr_right.


Lemma Uminus_assoc_right :  forall x y z, y <= x -> z <= y -> x - (y - z) == (x - y) + z.
intros.
apply Uplus_eq_perm_left; auto.
unfold Uminus at 1; apply Uinv_le_compat.
transitivity (1 - y + z); auto.
transitivity ((y - z) + z + (x - y)).
rewrite (Uminus_plus_simpl _ _ H0).
rewrite (Uplus_sym y (x - y)); auto.
norm_assoc_right; auto.
Save.

Lemma Uplus_minus_assoc_right : forall x y z, 
      y <= [1-]x -> z <= y -> x + (y - z) == (x + y) - z.
intros; unfold Uminus.
transitivity ([1-] (x + ([1-] (x + y) + z)) + x).
rewrite Uplus_assoc.
rewrite (Uplus_sym x ([1-] (x + y))).
rewrite Uinv_plus_left; auto.
rewrite Uinv_plus_left; auto.
transitivity ([1-] (x + y) + y); auto.
Save.
Hint Resolve Uplus_minus_assoc_right.

Lemma Uplus_minus_assoc_le : forall x y z, (x + y) - z <= x + (y - z).
intros; apply (Ule_total z y); intros; auto.
apply (Ule_total y ([1-]x)); intros; auto.
rewrite Uplus_minus_assoc_right; trivial.
rewrite (Uplus_one x y); auto.
rewrite Uminus_one_left.
transitivity (x + ([1-]x - z)); auto.
rewrite <- Uinv_plus_minus_right.
rewrite Uplus_sym; auto.
Save.
Hint Resolve Uplus_minus_assoc_le.


Lemma Udiv_minus : forall x y z, ~0 == z -> x <= z -> (x - y) / z == x/z - y/z.
intros; apply (Ule_total x y); auto; intros.
transitivity (0/z); auto.
rewrite Uminus_le_zero; auto.
assert (y <= z).
transitivity x; auto.
apply Oeq_sym; apply Umult_div_eq; auto.
rewrite Uminus_distr_left.
rewrite Udiv_mult; auto.
rewrite Udiv_mult; auto.
Save.

Lemma Umult_inv_minus : forall x y, x * [1-]y == x - x * y.
intros; rewrite <- Uminus_one_left.
rewrite Uminus_distr_right; auto.
Save.
Hint Resolve Umult_inv_minus.

Lemma Uinv_mult_minus : forall x y, ([1-]x) * y == y - x * y.
intros; rewrite (Umult_sym ([1-]x) y); rewrite (Umult_sym x y); trivial.
Save.
Hint Resolve Uinv_mult_minus.

Lemma Uminus_plus_perm_right : forall x y z, y <= x -> y <= z -> (x - y) + z == x + (z - y).
intros; apply (Ule_total (x-y) ([1-]z)); trivial; intros.
apply Uminus_eq_perm_left.
transitivity z; auto.
rewrite <- Uplus_minus_assoc_right; auto.
rewrite Uminus_assoc_right; auto.
rewrite Uminus_eq; auto.
rewrite Uplus_zero_left; auto.
(* case with overflow *)
transitivity 1; auto.
rewrite Uplus_one; auto.
Save.
Hint Resolve Uminus_plus_perm_right.

Lemma Uminus_plus_simpl_mid : 
    forall x y z, z <= x -> y <= z -> x - y == (x - z) + (z - y).
intros; assert ((x - z) + (z - y) <= [1-]y).
transitivity ([1-]z + (z - y)); auto.
unfold Uminus; auto.
apply Uplus_eq_perm_left; auto.
rewrite Uplus_sym.
norm_assoc_right.
rewrite Uminus_plus_simpl; auto.
Save.
Hint Resolve Uminus_plus_simpl_mid.

(** - triangular inequality *)

Lemma Uminus_triangular : forall x y z, x - y <= (x - z) + (z - y).
intros; apply (Ule_total z x); intros; trivial.
intros; apply (Ule_total y z); intros; auto.
rewrite (Uminus_le_zero z y); auto.
rewrite Uplus_zero_right; auto.
rewrite (Uminus_le_zero x z); auto.
rewrite Uplus_zero_left; auto.
Save.
Hint Resolve Uminus_triangular.


Lemma Uesp_plus_right_perm : forall x y z,
    x <= [1-] y -> y <= [1-] z -> x & (y + z) == (x + y) & z.
intros; unfold Uesp; apply Uinv_eq_compat.
rewrite Uinv_plus_minus_right.
rewrite Uinv_plus_minus_left.
symmetry; auto.
Save.
Hint Resolve Uesp_plus_right_perm.

Lemma Uplus_esp_assoc : forall x y z,
    x <= [1-]y -> [1-]z <= y -> x + (y & z) == (x + y) & z.
intros; apply Uplus_eq_simpl_right with ([1-]z); auto.
apply Uinv_le_compat; auto.
transitivity ([1-]y + y & z); auto.
rewrite Uplus_sym; rewrite Uesp_sym; rewrite <- Uesp_plus_inv; auto.
rewrite <- Uesp_plus_inv; auto.
norm_assoc_right.
rewrite <- Uesp_plus_inv; auto.
transitivity y; auto.
Save.
Hint Resolve Uplus_esp_assoc.

Lemma Uesp_plus_left_perm : forall x y z,
    [1-]x <= y  ->  [1-]z <= y -> x & y <= [1-] z -> (x & y) + z == x + (y & z).
intros; symmetry; apply Uminus_eq_perm_right.
transitivity z; auto.
rewrite <- Uplus_minus_assoc_right; auto.
rewrite (Uesp_sym y z).
rewrite Uminus_esp_simpl_left; auto.
Save.
Hint Resolve Uesp_plus_left_perm.

Lemma Uesp_plus_left_perm_le : forall x y z,
    [1-]x <= y  ->  [1-]z <= y -> (x & y) + z <= x + (y & z).
intros; apply Uminus_le_perm_left.
transitivity z; auto.
rewrite Uplus_minus_assoc_le.
rewrite (Uesp_sym y z).
rewrite Uminus_esp_simpl_left; auto.
Save.
Hint Resolve Uesp_plus_left_perm_le.

Lemma Uesp_plus_assoc : forall x y z,
    [1-]x <= y  ->  y <= [1-]z -> x & (y + z) == (x & y) + z.
intros; apply Uminus_eq_perm_left.
assert (z <= x).
transitivity ([1-]y); auto.
transitivity (x & ([1-]x + z)); auto.
rewrite Uesp_sym,Uplus_sym.
rewrite Uplus_inv_esp_simpl; auto.
apply Uesp_le_compat; auto.
rewrite Uesp_minus_distr_right.
rewrite Uplus_minus_simpl_right; auto.
Save.
Hint Resolve Uesp_plus_assoc.

Lemma Uminus_assoc_right_perm : forall x y z,
    x <= [1-] z -> z <= y ->  x - (y - z) == x + z - y.
intros; apply (Ule_total (y -z) x); intros; auto.
apply Uplus_eq_simpl_right with y; auto.
apply Uinv_le_perm_right.
transitivity ([1-]z - (y - z)); auto.
rewrite <- Uinv_plus_minus_right; auto.
rewrite Uminus_plus_perm_right; auto.
rewrite Uminus_assoc_right; auto.
rewrite Uminus_plus_simpl; auto.
rewrite (Uminus_le_zero y y); auto.
rewrite (Uminus_le_zero x (y-z)); auto.
rewrite Uminus_le_zero; auto.
Save.
Hint Resolve Uminus_assoc_right_perm.

Lemma Uminus_lt_left : forall x y, ~ 0 == x -> ~ 0 == y -> x - y < x.
split; auto.
intro H1.
apply (Ule_total x y); auto; intro Hle.
apply H; rewrite <- H1; symmetry; auto.
apply H0; transitivity (x - x); auto.
rewrite <- H1 at 2; auto.
Save.
Hint Resolve Uminus_lt_left.

Lemma Uminus_lt0_intro : forall x y, 0 < y - x -> x < y.
intros; apply notUle_lt; intro.
assert (y - x == 0); auto.
rewrite H1 in H; auto.
absurd (0<0); auto.
Save.
Hint Immediate Uminus_lt0_intro.

Lemma Uminus_lt0_elim : forall x y, x < y -> 0 < y - x.
intros; apply Ult_neq_zero; auto.
Save.
Hint Immediate Uminus_lt0_elim.

Lemma Uesp_mult_le : 
  forall x y z, [1-]x <= y -> x * z <= [1-](y * z) 
  -> (x & y) * z == x * z + y * z - z.
intros; unfold Uesp.
rewrite Uinv_mult_minus.
rewrite Udistr_plus_right; auto.
repeat rewrite Uinv_mult_minus.
rewrite <- Uminus_assoc_left.
rewrite (Uminus_assoc_right z); auto.
rewrite (Uminus_le_zero z z); auto.
rewrite Uplus_zero_left.
rewrite Uminus_assoc_right_perm; auto.
Save.
Hint Resolve Uesp_mult_le.

Lemma Uesp_mult_ge : 
  forall x y z, [1-]x <= y -> [1-](x * z) <= y * z 
  -> (x & y) * z == (x * z) & (y * z) + [1-]z.
intros; unfold Uesp.
rewrite Uinv_mult_minus.
rewrite Udistr_plus_right; auto.
repeat rewrite Uinv_mult_minus.
rewrite <- Uminus_assoc_left.
rewrite (Uminus_assoc_right z); auto.
rewrite (Uminus_le_zero z z); auto.
rewrite Uplus_zero_left.
rewrite (Udistr_inv_right y z).
rewrite Uplus_assoc.
rewrite Uinv_plus_right; auto.
unfold Uminus.
apply Uinv_eq_compat.
apply Uplus_eq_compat; auto.
rewrite Uinv_mult_minus.
unfold Uminus; apply Uinv_eq_compat; auto.
apply Uinv_le_compat; auto.
transitivity (y * z + [1-]y * z); auto.
Save.
Hint Resolve Uesp_mult_ge.

(** ** Definition and properties of generalized sums *)

Definition sigma : (nat -> U) -> nat -m> U.
intros alpha; exists (compn Uplus 0 alpha); red; intros.
abstract (induction H; simpl; [auto | transitivity (compn Uplus 0 alpha m); auto]).
Defined.

Lemma sigma_0 : forall (f : nat -> U), sigma f O == 0.
trivial.
Save.

Lemma sigma_S : forall (f :nat -> U) (n:nat), sigma f (S n) = (f n) + (sigma f n).
trivial.
Save.

Lemma sigma_1 : forall (f : nat -> U), sigma f (S 0) == f O.
intros; rewrite sigma_S; auto.
Save.


Lemma sigma_incr : forall (f : nat -> U) (n m:nat), (n <= m)%nat -> sigma f n <= sigma f m.
intros f n m H; apply (fmonotonic (sigma f)); trivial.
Save.

Hint Resolve sigma_incr.

Lemma sigma_eq_compat : forall (f g: nat -> U) (n:nat), 
 (forall k, (k < n)%nat -> f k == g k) -> sigma f n == sigma g n.
induction n; auto.
intros; repeat rewrite sigma_S.
transitivity (g n + sigma f n); auto with arith.
Save.

Lemma sigma_le_compat : forall (f g: nat -> U) (n:nat), 
 (forall k, (k < n)%nat -> f k <= g k) -> sigma f n <= sigma g n.
induction n; auto.
intros; repeat rewrite sigma_S.
transitivity (g n + sigma f n); auto with arith.
Save.

Lemma sigma_S_lift : forall (f :nat -> U) (n:nat), 
          sigma f (S n) == (f O) + (sigma (fun k => f (S k)) n).
intros f n; generalize f; induction n; intros; auto.
rewrite sigma_S.
rewrite IHn.
rewrite sigma_S.
rewrite Uplus_assoc.
rewrite (Uplus_sym (f0 (S n)) (f0 O)); auto.
Save.

Lemma sigma_plus_lift : forall (f :nat -> U) (n m:nat),
          sigma f (n+m)%nat == sigma f n + sigma (fun k => f (n+k)%nat) m.
intros f n m; generalize f; clear f; induction n; intros.
simpl plus.
rewrite sigma_0.
rewrite Uplus_zero_left.
apply sigma_eq_compat; auto.
rewrite sigma_S_lift.
simpl plus.
rewrite sigma_S_lift.
rewrite IHn; auto.
Save.

Lemma sigma_zero : forall f n, 
  (forall k, (k<n)%nat -> f k == 0) -> sigma f n == 0.
induction n; intros; auto.
rewrite sigma_S.
rewrite (H n); auto.
rewrite IHn; auto.
Save.

Lemma sigma_not_zero : forall f n k, (k<n)%nat -> 0 < f k -> 0 < sigma f n.
induction n; intros; auto.
casetype False; omega.
rewrite sigma_S.
assert (k < n \/ k = n)%nat.
omega.
case H1; intros; subst; auto.
apply Olt_le_trans with (sigma f n); auto.
apply (IHn k); auto.
Save.

Lemma sigma_zero_elim : forall f n, 
  (sigma f n) == 0 -> forall k, (k<n)%nat -> f k == 0.
intros; apply Ueq_class; red; intros.
assert (0 < sigma f n); auto.
apply sigma_not_zero with k; auto.
apply (Olt_notle _ _ H2); auto.
Save.

Hint Resolve sigma_eq_compat sigma_le_compat sigma_zero.

Lemma sigma_le : forall f n k, (k<n)%nat -> f k <= sigma f n.
induction n; intros.
casetype False; omega.
rewrite sigma_S.
assert (k < n \/ k = n)%nat.
omega.
case H0; intros; subst; auto.
transitivity (sigma f n); auto.
Save.
Hint Resolve sigma_le.

Lemma sigma_minus_decr : forall f n, (forall k, f (S k) <= f k) ->
         sigma (fun k => f k - f (S k)) n == f O - f n.
intros f n fmon;induction n.
rewrite sigma_0; auto.
rewrite sigma_S; rewrite IHn.
rewrite Uplus_sym.
rewrite Uplus_minus_assoc_right; auto.
rewrite Uminus_plus_simpl; auto.
elim n; intros; auto.
transitivity (f n0); auto.
Save.

Lemma sigma_minus_incr : forall f n, (forall k, f k <= f (S k)) ->
         sigma (fun k => f (S k) - f k) n == f n - f O.
intros f n fmon;induction n.
rewrite sigma_0; auto.
rewrite sigma_S; rewrite IHn.
rewrite Uplus_minus_assoc_right; auto.
rewrite Uminus_plus_simpl; auto.
elim n; intros; auto.
transitivity (f n0); auto.
Save.          
(** ** Definition and properties of generalized products *)

Definition prod (alpha : nat -> U) (n:nat) := compn Umult 1 alpha n.

Lemma prod_0 : forall (f : nat -> U), prod f 0 = 1.
trivial.
Save.

Lemma prod_S : forall (f :nat -> U) (n:nat), prod f (S n) = (f n) * (prod f n).
trivial.
Save.

Lemma prod_1 : forall (f : nat -> U), prod f (S 0) == f O.
intros; rewrite prod_S; auto.
Save.

Lemma prod_S_lift : forall (f :nat -> U) (n:nat),
          prod f (S n) == (f O) * (prod (fun k => f (S k)) n).
intros f n; generalize f; induction n; intros; auto.
rewrite prod_S.
rewrite IHn.
rewrite prod_S.
rewrite Umult_assoc.
rewrite (Umult_sym (f0 (S n)) (f0 O)); auto.
Save.

Lemma prod_decr : forall (f : nat -> U) (n m:nat), (n <= m)%nat -> prod f m <= prod f n.
intros f n m H; induction H; auto.
intros; rewrite prod_S.
transitivity (prod f m); auto.
Save.

Hint Resolve prod_decr.

Lemma prod_eq_compat : forall (f g: nat -> U) (n:nat), 
 (forall k, (k < n)%nat -> f k == g k) -> (prod f n) == (prod g n).
induction n; auto.
intros; repeat rewrite prod_S.
transitivity (g n * prod f n); auto with arith.
Save.

Lemma prod_le_compat : forall (f g: nat -> U) (n:nat), 
 (forall k, (k < n)%nat -> f k <= g k) -> prod f n <= prod g n.
induction n; auto.
intros; repeat rewrite prod_S.
transitivity (g n * prod f n); auto with arith.
Save.

Lemma prod_zero : forall f n k, (k<n)%nat -> f k ==0 -> prod f n==0.
induction n; intros.
absurd ((k < 0)%nat); auto with arith.
rewrite prod_S.
assert (k < n \/ k = n)%nat.
omega.
case H1; intros; subst; auto.
rewrite (IHn k); auto.
rewrite H0; auto.
Save.

Lemma prod_not_zero : forall f n, 
  (forall k, (k<n)%nat -> 0 < f k) -> 0 < prod f n.
induction n; intros; auto.
rewrite prod_S; auto with arith.
Save.

Lemma prod_zero_elim : forall f n, 
  prod f n == 0 -> exc (fun k => (k<n)%nat /\ f k ==0).
intros; apply class_exc; red; intros.
assert (forall k, (k<n)%nat -> 0 < f k); intros.
rewrite Ult_notle_equiv; intro.
apply H0.
apply exc_intro with k; auto.
absurd (0 < prod f n); auto.
apply prod_not_zero; auto.
Save.

Hint Resolve prod_eq_compat prod_le_compat prod_not_zero.

Lemma prod_le : forall f n k, (k<n)%nat -> prod f n <= f k.
induction n; simpl; intros.
casetype False; omega.
rewrite prod_S.
assert (k < n \/ k = n)%nat.
omega.
case H0; intros; subst; auto.
transitivity (prod f n); auto.
Save.

Lemma prod_minus : forall f n, prod f n - prod f (S n) == ([1-]f n)  * prod f n.
intros f n; rewrite prod_S.
transitivity (1 * prod f n - f n * prod f n).
rewrite Umult_one_left; auto.
rewrite <- Uminus_distr_left; auto.
Save.


Definition Prod : (nat -> U) -> nat -m-> U.
intro f; exists (prod f).
abstract (red; intros; simpl; auto).
Defined.

Lemma Prod_simpl : forall f n, Prod f n = prod f n.
trivial.
Save.
Hint Resolve Prod_simpl.

(** ** Properties of [Unth] *)

Lemma Unth_eq_compat : forall n m, n = m -> [1/]1+n == [1/]1+m.
intros n m H; rewrite H; trivial.
Save.
Hint Resolve Unth_eq_compat.

Lemma Unth_zero : [1/]1+0 == 1.
setoid_rewrite (Unth_prop 0); auto.
Save.

(** printing [1/2] $\frac{1}{2}$ #&frac12;# *)
Notation "[1/2]" := (Unth 1).

Lemma Unth_one : [1/2] == [1-] [1/2].
transitivity ([1-] (compn Uplus 0 ( fun _ => [1/2] ) (S O))); auto.
apply Uinv_eq_compat; rewrite compS; rewrite comp0; auto.
Save.

Hint Resolve Unth_zero Unth_one.

Lemma Unth_one_plus : [1/2] + [1/2] == 1.
transitivity  ([1/2] + [1-][1/2]); auto.
Save.
Hint Resolve Unth_one_plus.

Lemma Unth_one_refl : forall t, [1/2] * t + [1/2] * t == t.
intro; rewrite <- Udistr_plus_right; auto.
Save.

Lemma Unth_not_null : forall n, ~ (0 == [1/]1+n).
red; intros.
apply Udiff_0_1.
transitivity ([1/]1+n); auto.
transitivity ([1-] (sigma (fun k => [1/]1+n) n)).
apply (Unth_prop n).
transitivity ([1-] (sigma (fun k => 0) n)).
apply Uinv_eq_compat.
apply sigma_eq_compat; auto.
transitivity ([1-] 0); auto.
Save.
Hint Resolve Unth_not_null.

Lemma Unth_lt_zero : forall n, 0 < [1/]1+n.
auto.
Save.
Hint Resolve Unth_lt_zero.

Lemma Unth_inv_lt_one : forall n, [1-][1/]1+n<1.
intro; rewrite <- Uinv_zero; auto.
Save.
Hint Resolve Unth_inv_lt_one.

Lemma Unth_not_one : forall n, ~ (1 == [1-][1/]1+n).
auto.
Save.
Hint Resolve Unth_not_one.

Lemma Unth_prop_sigma : forall n, [1/]1+n == [1-] (sigma (fun k => [1/]1+n) n).
exact Unth_prop.
Save.
Hint Resolve Unth_prop_sigma.

Lemma Unth_sigma_n : forall n : nat, ~ (1 == sigma (fun k => [1/]1+n) n).
intros; apply Uinv_neq_simpl.
setoid_rewrite Uinv_one.
setoid_rewrite <- (Unth_prop_sigma n); auto.
Save.

Lemma Unth_sigma_Sn : forall n : nat, 1 == sigma (fun k => [1/]1+n) (S n).
intros; rewrite sigma_S.
transitivity 
([1-] (sigma (fun k => [1/]1+n) n) + (sigma (fun k => [1/]1+n) n));auto.
Save.

Hint Resolve Unth_sigma_n Unth_sigma_Sn.

Lemma Unth_decr : forall n m, (n < m)%nat -> [1/]1+m < [1/]1+n.
intros n m H; rewrite Ult_notle_equiv; intro.
apply (Unth_sigma_n m).
apply Ole_antisym; auto.
transitivity (sigma (fun _ : nat => [1/]1+n) (S n)); auto.
transitivity (sigma (fun _ => [1/]1+n) m); auto.
Save.
Hint Resolve Unth_decr.

Lemma Unth_decr_S : forall n, [1/]1+(S n) < [1/]1+n.
intro n; rewrite Ult_notle_equiv; intro.
apply (Unth_sigma_n (S n)).
apply Ole_antisym; auto.
transitivity (sigma (fun _ : nat => [1/]1+n) (S n)); auto.
Save.
Hint Resolve Unth_decr_S.

Lemma Unth_le_compat :
forall n m, (n <= m)%nat -> [1/]1+m <= [1/]1+n.
induction 1; auto.
transitivity ([1/]1+m); auto.
Save.
Hint Resolve Unth_le_compat.

Lemma Unth_le_equiv :
  forall n m, [1/]1+n <= [1/]1+m <-> (m <= n)%nat.
Proof.
  intros; split; intros.
  assert (m<=n \/ n<m)%nat by omega.
  destruct H0; [omega|].
  assert ([1/]1+m < [1/]1+n) by (apply Unth_decr; omega).
  elim (Olt_notle _ _ H1 H).
  apply Unth_le_compat; auto.
Save.

Lemma Unth_eq_equiv :
  forall n m, [1/]1+n == [1/]1+m <-> (m = n)%nat.
Proof.
  intros; split; auto; intro.
  apply le_antisym;
  rewrite <- Unth_le_equiv; auto.
Save.

Lemma Unth_le_half : forall n, [1/]1+(S n) <= [1/2].
auto with arith.
Save.
Hint Resolve Unth_le_half.

Lemma Unth_lt_one : forall n, [1/]1+(S n) < 1.
intros; apply Olt_le_trans with ([1/]1+0); auto with zarith.
Save.
Hint Resolve Unth_lt_one.

(** *** Mean of two numbers : [[1/2] x + [1/2] y]*)
Definition mean (x y:U) := [1/2] * x + [1/2] * y.

Lemma mean_eq : forall x:U, mean x x ==x.
unfold mean; intros.
assert (H : ([1/2] <= [1-] ([1/2]))); auto.
rewrite <- (Udistr_plus_right _ _ x H); auto.
Save.

Lemma mean_le_compat_right : forall x y z, y <= z -> mean x y <= mean x z.
unfold mean; intros.
apply Uplus_le_compat_right; auto.
Save.

Lemma mean_le_compat_left : forall x y z, x <= y -> mean x z <= mean y z.
unfold mean; intros.
apply Uplus_le_compat_left; auto.
Save.

Hint Resolve mean_eq mean_le_compat_left mean_le_compat_right.

Lemma mean_lt_compat_right : forall x y z, y < z -> mean x y < mean x z.
unfold mean; intros.
apply Uplus_lt_compat_right; auto.
Save.

Lemma mean_lt_compat_left : forall x y z, x < y -> mean x z < mean y z.
unfold mean; intros.
apply Uplus_lt_compat_left; auto.
Save.

Hint Resolve mean_eq mean_le_compat_left mean_le_compat_right.
Hint Resolve mean_lt_compat_left mean_lt_compat_right.

Lemma mean_le_up : forall x y, x <= y -> mean x y <= y.
intros; transitivity (mean y y); auto. 
Save.

Lemma mean_le_down : forall x y, x <= y -> x <= mean x y.
intros; transitivity (mean x x); auto. 
Save.

Lemma mean_lt_up : forall x y, x < y -> mean x y < y.
intros; apply Olt_le_trans with (mean y y); auto. 
Save.

Lemma mean_lt_down : forall x y, x < y -> x < mean x y.
intros; apply Ole_lt_trans with (mean x x); auto. 
Save.

Hint Resolve mean_le_up mean_le_down mean_lt_up mean_lt_down.


(** *** Properties of [ [1/2] ] *)

Lemma le_half_inv : forall x, x <= [1/2] -> x <= [1-] x.
intros; transitivity ([1/2]); auto.
setoid_rewrite Unth_one; auto.
Save.

Hint Immediate le_half_inv.

Lemma ge_half_inv : forall x, [1/2] <= x  -> [1-] x <= x.
intros; transitivity ([1/2]); auto.
setoid_rewrite Unth_one; auto.
Save.

Hint Immediate ge_half_inv.

Lemma Uinv_le_half_left : forall x, x <= [1/2] -> [1/2] <= [1-] x.
intros; setoid_rewrite Unth_one; auto.
Save.

Lemma Uinv_le_half_right : forall x, [1/2] <= x -> [1-] x <= [1/2].
intros; setoid_rewrite Unth_one; auto.
Save.

Hint Resolve Uinv_le_half_left Uinv_le_half_right.

Lemma half_twice : forall x,  x <= [1/2] -> [1/2] * (x + x) == x.
intros; assert (H1 : x <= [1-] x); auto.
rewrite (Udistr_plus_left ([1/2]) _ _ H1).
exact (mean_eq x).
Save.

Lemma half_twice_le : forall x, [1/2] * (x + x) <= x.
intros; apply (Ule_total x ([1/2])); intros; auto.
rewrite (half_twice _ H); trivial.
assert (x+x==1); auto.
rewrite H0.
rewrite (Umult_one_right [1/2]); auto.
Save.

Lemma Uinv_half : forall x, [1/2] * ([1-] x)  + [1/2] == [1-] ( [1/2] * x ).
intros; setoid_rewrite (Udistr_inv_left ([1/2]) x).
setoid_rewrite Unth_one; auto.
Save.


Lemma Uinv_half_plus : forall x, [1-]x + [1/2] * x  == [1-] ( [1/2] * x ).
Proof.
intros x. rewrite <- Uinv_half.
setoid_rewrite <- (Unth_one_refl ([1-]x)) at 1.
rewrite <- Uplus_assoc. setoid_rewrite <- Udistr_plus_left;auto.
Qed.


Lemma half_esp :
forall x, ([1/2] <= x) -> ([1/2]) * (x & x) + [1/2] == x.
intros; unfold Uesp.
setoid_rewrite (Uinv_half ([1-] x + [1-] x)).
assert (H1:[1-] x <= [1/2]).
setoid_rewrite Unth_one; auto.
rewrite (half_twice _ H1); auto.
Save.

Lemma half_esp_le : forall x, x <= [1/2] * (x & x) + [1/2].
intros; apply (Ule_total ([1/2]) x); intros; auto.
setoid_rewrite (half_esp _ H); trivial.
assert (x & x == 0); auto.
setoid_rewrite H0.
setoid_rewrite (Umult_zero_right ([1/2])).
setoid_rewrite (Uplus_zero_left ([1/2])); auto.
Save.
Hint Resolve half_esp_le.


Lemma half_le : forall x y, y <= [1-] y -> x <= y + y -> ([1/2]) * x <= y.
intros.
apply notUlt_le; red; intros.
assert (y + y < x).
apply Olt_le_trans with  (mean x x); auto.
unfold mean; apply Uplus_lt_compat; auto.
apply (Olt_notle _ _ H2); auto.
Save.

Lemma half_Unth_le: forall n, [1/2] * ([1/]1+n) <= [1/]1+(S n).
intros; apply half_le; auto.
rewrite (Unth_prop_sigma n).
transitivity ([1-] (sigma (fun _ : nat => [1/]1+(S n)) n)).
apply Uinv_le_compat.
apply sigma_le_compat; auto.
transitivity 
([1-] (sigma (fun _ : nat => [1/]1+(S n)) (S n)) + [1/]1+(S n)); auto.
rewrite sigma_S; auto.
Save.
Hint Resolve half_le half_Unth_le.

Lemma half_exp : forall n, [1/2]^n == [1/2]^(S n) + [1/2]^(S n).
intros; simpl; symmetry; exact (mean_eq ([1/2]^n)).
Save.

(** ** Diff function : [| x - y |] *)

Definition diff (x y:U) := (x - y) + (y - x).

Lemma diff_eq : forall x, diff x x == 0.
unfold diff; intros; rewrite Uminus_eq; auto.
Save.
Hint Resolve diff_eq.

Lemma diff_sym : forall x y, diff x y == diff y x.
unfold diff; intros; auto.
Save.
Hint Resolve diff_sym.

Lemma diff_zero : forall x, diff x 0 == x.
unfold diff; intros.
transitivity (x + 0); auto.
Save.
Hint Resolve diff_zero.

Add Morphism  diff with signature Oeq ==> Oeq ==> Oeq as diff_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; unfold diff.
apply Uplus_eq_compat; auto.
Qed.
Hint Immediate diff_eq_compat.

Lemma diff_plus_ok : forall x y, x - y <= [1-](y - x).
intros; apply (Ule_total x y); intros; trivial.
rewrite (Uminus_le_zero x y H); auto.
rewrite (Uminus_le_zero y x H); auto.
Save.
Hint Resolve diff_plus_ok.

Lemma diff_Uminus : forall x y, x <= y -> diff x y == y - x.
intros; unfold diff; rewrite (Uminus_le_zero x y); auto.
Save.

Lemma diff_Uplus_le : forall x y, x <= diff x y + y.
intros; unfold diff; apply (Ule_total x y); intros; auto.
transitivity y; auto.
Save.
Hint Resolve diff_Uplus_le.

Lemma diff_triangular : forall x y z, diff x y <= diff x z + diff y z.
unfold diff; intros.
transitivity (((x-z)+(z-y)) + ((y-z)+(z-x))).
apply Uplus_le_compat; apply Uminus_triangular.
repeat norm_assoc_right; apply Uplus_le_compat; trivial.
rewrite Uplus_perm3.
apply Uplus_le_compat; auto.
Save.
Hint Resolve diff_triangular.


(** ** Density *)
Lemma Ule_lt_lim : forall x y,  (forall t, t < x -> t <= y) -> x <= y.
intros; apply Ule_class; red; intros.
pose (z:= mean y x).
assert (y < z); unfold z; auto.
apply (Olt_notle _ _ H1); apply H; unfold z; auto.
Save.

Lemma Ule_nth_lim : forall x y, (forall p, x <= y + [1/]1+p) -> x <= y.
intros; apply Ule_lt_lim; intros.
apply (Ult_le_nth_minus H0); auto; intros n H1.
transitivity (x - [1/]1+n); auto.
transitivity (y + [1/]1+n - [1/]1+n); auto.
Save.

(** ** Properties of least upper bounds *)

Lemma lub_un : mlub (cte nat 1) == 1.
apply lub_cte.
Save.
Hint Resolve lub_un.

Lemma UPlusk_eq : forall k, UPlus k == mon (Uplus k).
intros k x; rewrite UPlus_simpl; auto.
Save.

Lemma UMultk_eq : forall k, UMult k == mon (Umult k).
intros k x; rewrite UMult_simpl; auto.
Save.

Lemma UPlus_continuous_right : forall k, continuous (UPlus k).
intros; rewrite UPlusk_eq; auto.
Save.
Hint Resolve UPlus_continuous_right.

Lemma UPlus_continuous_left : continuous UPlus.
apply continuous_sym; auto.
intros; repeat (rewrite UPlus_simpl); auto.
Save.
Hint Resolve UPlus_continuous_left.

Lemma UMult_continuous_right : forall k, continuous (UMult k).
intros; rewrite UMultk_eq; auto.
Save.
Hint Resolve UMult_continuous_right.

Lemma UMult_continuous_left : continuous UMult.
apply continuous_sym; auto.
intros; repeat (rewrite UMult_simpl); auto.
Save.
Hint Resolve UMult_continuous_left.

Lemma lub_eq_plus_cte_left : forall (f:nat -m> U) (k:U), lub ((UPlus k) @ f) == k + lub f.
intros; symmetry; apply (lub_comp_eq (UPlus k) f); red; intros; auto.
Save.
Hint Resolve lub_eq_plus_cte_left.

Lemma lub_eq_mult : forall (k:U) (f:nat -m> U), lub ((UMult k) @ f) ==  k * lub f.
intros; symmetry; apply (lub_comp_eq (UMult k) f); trivial.
Save.
Hint Resolve lub_eq_mult.

Lemma lub_eq_plus_cte_right : forall (f : nat -m> U) (k:U),
           lub ((mshift UPlus k) @ f) == lub f + k.
intros; transitivity (k + lub f); auto.
transitivity (lub (UPlus k @ f)); auto.
apply lub_eq_compat; intro n.
repeat (rewrite comp_simpl).
repeat (rewrite mshift_simpl).
repeat (rewrite UPlus_simpl); auto.
Save.
Hint Resolve lub_eq_plus_cte_right.

Lemma min_lub_le : forall f g : nat -m> U, 
         lub ((Min @2 f) g) <= min (lub f) (lub g).
intros; apply min_le.
apply lub_le.
intro; transitivity (f n); simpl; auto.
apply lub_le.
intro; transitivity (g n); simpl; auto.
Save.

Lemma min_lub_le_incr_aux : forall f g : nat -m> U,
         (forall n, exc (fun m => (n<=m)%nat /\ f n <= g m)) 
         -> min (lub f) (lub g) <= lub ((Min @2 f) g).
intros; transitivity (lub f); auto.
apply lub_le; intros.
apply (H n); auto; intros m (H1,H2).
transitivity (min (f m) (g m)); auto.
apply min_le; auto.
apply (le_lub ((Min @2 f) g) m); simpl; auto.
Save.

Lemma min_lub_le_incr : forall f g : nat -m> U, 
         min (lub f) (lub g) <= lub ((Min @2 f) g).
intros f g; apply (incr_decomp f g); auto; intros.
apply (min_lub_le_incr_aux f g); auto.
rewrite min_sym.
transitivity (lub ((Min @2 g) f)); auto.
apply (min_lub_le_incr_aux g f); auto.
apply lub_le_compat; intro n.
simpl; auto.
Save.

Lemma min_continuous2 : continuous2 Min.
intros f g; exact (min_lub_le_incr f g).
Save.
Hint Resolve min_continuous2.

Lemma lub_eq_esp_right : 
  forall (f : nat -m> U) (k : U), lub ((mshift UEsp k) @ f) == lub f & k.
intros; apply Ole_antisym.
apply lub_le; auto.
intro n; simpl; auto.
apply Uplus_inv_le_esp.
rewrite <- lub_eq_plus_cte_right.
apply lub_le_compat; simpl; auto.
Save.
Hint Resolve lub_eq_esp_right.


Lemma Udiv_continuous : forall (k:U), continuous (UDiv k).
red; intros.
rewrite UDiv_simpl.
apply (Ueq_orc 0 k); auto; intros.
rewrite Udiv_by_zero; auto.
apply (excluded_middle (A:=forall n, h n <= k)); auto; intros.
apply Umult_div_le_right; auto.
rewrite Umult_sym.
transitivity (lub (UMult k @ (UDiv k @ h))); auto.
apply lub_le_compat; intro n; simpl; auto.
rewrite Umult_div; auto.
assert (exc (fun n => k <= h n)).
apply exc_intro_class; intros; apply H0; intros; auto.
apply H1; auto; intros.
rewrite (Udiv_le_one (lub h) k); auto.
transitivity (h x / k); auto.
rewrite (Udiv_le_one (h x) k H); auto.
apply le_lub with (f:=UDiv k @ h) (n:=x).
transitivity (h x); auto.
Save.
Hint Resolve Udiv_continuous.

(** ** Greatest lower bounds *)


Definition glb (f:nat -m-> U) := [1-](lub (UInv @ f)).

Lemma glb_le:   forall (f : nat -m-> U) (n : nat), glb f <= (f n).
unfold glb; intros; apply Uinv_le_perm_left.
apply (le_lub (UInv @ f) n); auto.
Save.

Lemma le_glb: forall (f : nat -m-> U) (x:U), 
      (forall n : nat, x <= f n) -> x <= glb f.
unfold glb; intros; apply Uinv_le_perm_right.
apply (lub_le (UInv @ f)); simpl; auto.
Save.
Hint Resolve glb_le le_glb.

Definition Uopp : cpo (o:=Iord U) U.
   exists 1 glb; abstract (simpl; auto).  
Defined.

Lemma Uopp_lub_simpl 
   : forall h : nat -m-> U, lub (cpo:=Uopp) h = glb h.
trivial.
Save.

Lemma Uopp_mon_seq : forall f:nat -m-> U, 
   forall n m:nat, (n <= m)%nat -> f m <= f n.
intros f n m H; exact (fmonotonic f n m H).
Save.
Hint Resolve Uopp_mon_seq.


(** Infinite product: $\Pi_{i=0}^{\infty} f\,i$ #&Pi;(i=0..&infin;) f i #*) 
Definition prod_inf (f : nat -> U) : U := glb (Prod f).

(** Properties of [glb] *)

Lemma glb_le_compat:
  forall f g :  nat -m-> U, (forall x, f x <= g x) -> glb f <= glb g.
intros f g; exact (lub_le_compat U (Iord U) Uopp g f).
Save.
Hint Resolve glb_le_compat.

Lemma glb_eq_compat:
  forall f g : nat -m-> U, f == g -> glb f == glb g.
intros; apply Ole_antisym; auto.
apply glb_le_compat; intro x; assert (f x == g x); auto.
Save.
Hint Resolve glb_eq_compat.

Lemma glb_cte: forall c : U, glb (mon (cte nat (o1:=(Iord U)) c)) == c.
intros; exact (lub_cte (c:=Uopp) c).
Save.
Hint Resolve glb_cte.

Lemma glb_eq_plus_cte_right:
  forall (f : nat -m-> U) (k : U), glb (Imon (mshift UPlus k) @ f) == glb f + k.
unfold glb; intros.
transitivity ([1-] lub (mshift UEsp ([1-]k) @ (UInv @ f))); auto.
apply Uinv_eq_compat; apply lub_eq_compat; intro x.
repeat (rewrite comp_simpl).
unfold Imon, UEsp, UInv, UPlus, mon2.
repeat (rewrite mon_simpl); repeat (rewrite mshift_simpl); repeat (rewrite mon_simpl); auto.
transitivity ([1-] (lub (UInv @ f) & [1-] k)).
apply Uinv_eq_compat; apply (lub_eq_esp_right (UInv @ f) ([1-]k)).
rewrite Uinv_esp_plus; auto.
Save.
Hint Resolve glb_eq_plus_cte_right.

Lemma glb_eq_plus_cte_left:
  forall (f : nat -m-> U) (k : U), glb (Imon (UPlus k) @ f) == k + glb f.
intros; transitivity (glb f + k); auto.
transitivity (glb (Imon (mshift UPlus k) @ f)); auto.
apply glb_eq_compat; intro x; simpl.
change (k + f x == f x + k); auto.
Save.
Hint Resolve glb_eq_plus_cte_left.

Lemma glb_eq_mult:
  forall (k : U) (f : nat -m-> U), glb (Imon (UMult k) @ f) == k * glb f.
unfold glb; intros; auto.
transitivity ([1-] lub (mshift UPlus ([1-]k) @ (UMult k @ (UInv @ f)))).
apply Uinv_eq_compat; apply lub_eq_compat; intro x; simpl.
change ([1-] (k * f x) == (k * [1-] f x + [1-] k)); auto.
rewrite lub_eq_plus_cte_right.
rewrite (lub_eq_mult k).
apply Uinv_eq_perm_left; auto.
rewrite Udistr_inv_left; auto.
Save.

Lemma Imon2_plus_continuous 
       : continuous2 (c1:=Uopp) (c2:=Uopp) (c3:=Uopp) (imon2 Uplus).
apply continuous2_sym; intros.
repeat (rewrite imon2_simpl); simpl; auto.
red; intros.
rewrite imon2_simpl; simpl.
rewrite <- glb_eq_plus_cte_left; auto.
Save.

Hint Resolve  Imon2_plus_continuous.

Lemma Uinv_continuous : continuous (c1:=Uopp) UInv.
red; intros.
rewrite UInv_simpl; simpl.
unfold glb.
rewrite Uinv_inv; auto.
Save.

Lemma Uinv_lub_eq : forall f : nat -m-> U, [1-](lub (cpo:=Uopp) f) == lub (UInv@f).
intro; apply (lub_comp_eq UInv f Uinv_continuous).
Save.

Lemma Uinvopp_mon : monotonic (o2:= Iord U) Uinv.
red; simpl; intros; auto.
Save.
Hint Resolve Uinvopp_mon.

Definition UInvopp : U -m-> U 
   := mon (o2:= Iord U) Uinv (fmonotonic:=Uinvopp_mon).

Lemma UInvopp_simpl : forall x, UInvopp x = [1-]x.
trivial.
Save.

Lemma Uinvopp_continuous : continuous (c2:=Uopp) UInvopp.
red; intros.
rewrite UInvopp_simpl; simpl.
unfold glb; simpl.
apply Uinv_le_compat; apply lub_le_compat; simpl; auto.
Save.

Lemma Uinvopp_lub_eq 
   : forall f : nat -m> U, [1-](lub f) == lub (cpo:=Uopp) (UInvopp@f).
intro; apply (lub_comp_eq UInvopp f Uinvopp_continuous).
Save.

Hint Resolve Uinv_continuous Uinvopp_continuous.

Instance Uminus_mon2 : monotonic2 (o2:=Iord U) Uminus.
red; intros; auto.
Save.

Definition UMinus : U -m> U --m> U := mon2 Uminus.

Lemma UMinus_simpl : forall x y, UMinus x y = x - y.
trivial.
Save.

Lemma Uminus_continuous2 : continuous2 (c2:=Uopp) UMinus.
apply continuous2_eq_compat with (fcomp2 _ _ _ _ UInv (imon2 Uplus @ UInvopp)).
intros x y; simpl; auto.
apply (continuous2_comp2 (c1:=cpoU) (c2:=Uopp) (c3:=Uopp) (c4:=cpoU)); auto.
apply (continuous2_comp (c1:=cpoU) (c2:=Uopp) (c3:=Uopp)(c4:=Uopp)); auto.
Save.
Hint Resolve Uminus_continuous2.
(*
min_lub_le_incr:
  forall f g : nat -> U,
  incr f ->
  incr g -> min (lub f) (lub g) <= lub (fun n : nat => min (f n) (g n))
min_lub_le_incr_aux:
  forall f g : nat -> U,
  incr f ->
  (forall n : nat, exc (fun m : nat => (n <= m)%nat /\ f n <= g m)) ->
  min (lub f) (lub g) <= lub (fun n : nat => min (f n) (g n))
min_lub_le:
  forall f g : nat -> U,
  lub (fun n : nat => min (f n) (g n)) <= min (lub f) (lub g)
*)

Lemma glb_le_esp :  forall f g :nat -m-> U, (glb f) & (glb g) <= glb ((imon2 Uesp @2 f) g).
intros; apply le_glb; simpl; auto.
Save.
Hint Resolve glb_le_esp.

Lemma Uesp_min : forall a1 a2 b1 b2, min a1 b1 & min a2 b2 <= min (a1 & a2) (b1 & b2).
intros; apply min_le.
apply Uesp_le_compat; auto.
apply Uesp_le_compat; auto.
Save.

(*
Instance Uesp_continuous2 : continuous2 UEsp.
red; intros; rewrite UEsp_simpl; unfold Uesp.
repeat rewrite Uinvopp_lub_eq.
apply Uinv_le_perm_left.
rewrite Uplus_lub_eq.
*)


(** Defining lubs of arbitrary sequences *)

Fixpoint seq_max (f:nat -> U) (n:nat) : U := match n with 
             O => f O | S p => max (seq_max f p) (f (S p)) end.

Lemma seq_max_incr : forall f n, seq_max f n <= seq_max f (S n).
induction n; simpl; intros; auto.
Save.
Hint Resolve seq_max_incr.

Lemma seq_max_le : forall f n, f n <= seq_max f n.
induction n; simpl; intros; auto.
Save.
Hint Resolve seq_max_le.

Instance seq_max_mon : forall (f:nat -> U), monotonic (seq_max f).
intro; apply nat_monotonic; auto.
Save.

Definition sMax (f:nat -> U) : nat -m> U := mon (seq_max f).

Lemma sMax_mult : forall k (f:nat->U),  sMax (fun n => k * f n) == UMult k @ sMax f.
intros; intro n; simpl.
induction n; simpl; intros; auto.
rewrite IHn; auto.
Save.  

Lemma sMax_plus_cte_right : forall k (f:nat-> U),  
    sMax (fun n => f n + k) == mshift UPlus k @ sMax f.
intros; intro n; simpl; intros.
induction n; simpl; intros; auto.
rewrite IHn; auto.
Save.  

Definition Ulub  (f:nat -> U)  := lub (sMax f).

Lemma le_Ulub : forall f n, f n <= Ulub f.
unfold Ulub; intros; transitivity (seq_max f n); auto.
apply (le_lub (sMax f) n).
Save.

Lemma Ulub_le : forall f x, (forall n, f n <= x) -> Ulub f <= x.
unfold Ulub; intros; apply lub_le.
induction n; simpl; intros; auto.
apply max_le; auto.
Save.

Hint Resolve le_Ulub Ulub_le.

Lemma Ulub_le_compat : forall f g : nat->U, f <= g -> Ulub f <= Ulub g.
intros; apply Ulub_le; intros; auto.
transitivity (g n); auto.
Save.
Hint Resolve Ulub_le_compat.

Add Morphism Ulub with signature Oeq ==> Oeq as Ulub_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve Ulub_eq_compat.

Lemma Ulub_eq_mult : forall k (f:nat->U), Ulub (fun n => k * f n)== k * Ulub f.
intros; unfold Ulub.
rewrite sMax_mult; auto.
Save.

Lemma Ulub_eq_plus_cte_right : forall (f:nat->U) k, Ulub (fun n => f n + k)== Ulub f + k.
intros; unfold Ulub.
rewrite sMax_plus_cte_right; auto.
Save.

Hint Resolve Ulub_eq_mult Ulub_eq_plus_cte_right.

Lemma Ulub_eq_esp_right :
  forall (f : nat -> U) (k : U), Ulub (fun n => f n & k) == Ulub f & k.
intros; apply Ole_antisym.
apply Ulub_le; auto.
apply Uplus_inv_le_esp.
transitivity (Ulub (fun n => (f n & k) + ([1-]k))); auto.
Save.
Hint Resolve lub_eq_esp_right.

Lemma Ulub_le_plus : forall f g, Ulub (fun n => f n + g n) <= Ulub f + Ulub g.
intros; apply Ulub_le; auto.
Save.
Hint Resolve Ulub_le_plus.

Definition Uglb (f:nat -> U) :U := [1-]Ulub (fun n => [1-](f n)).

Lemma Uglb_le:   forall (f : nat -> U) (n : nat), Uglb f <= f n.
unfold Uglb; intros; apply Uinv_le_perm_left.
apply le_Ulub with (f:=fun n => [1-]f n) (n:=n); auto.
Save.

Lemma le_Uglb: forall (f : nat -> U) (x:U), 
  (forall n : nat, x <= f n) -> x <= Uglb f.
unfold Uglb; intros; apply Uinv_le_perm_right.
apply Ulub_le with (f:=fun n => [1-]f n); auto.
Save.
Hint Resolve Uglb_le le_Uglb.

Lemma Uglb_le_compat : forall f g : nat -> U, f <= g -> Uglb f <= Uglb g.
intros; apply le_Uglb; intros; auto.
transitivity (f n); auto.
Save.
Hint Resolve Uglb_le_compat.

Add Morphism Uglb with signature Oeq ==> Oeq as Uglb_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve Uglb_eq_compat.

Lemma Uglb_eq_plus_cte_right:
  forall (f : nat -> U) (k : U), Uglb (fun n => f n + k) == Uglb f + k.
unfold Uglb; intros.
transitivity ([1-] Ulub (fun n => ([1-]f n) & [1-]k)); auto.
transitivity ([1-] (Ulub (fun n => [1-]f n) & [1-] k)).
apply Uinv_eq_compat; apply (Ulub_eq_esp_right (fun n => [1-]f n) ([1-]k)).
transitivity ([1-]Ulub (fun n => [1-]f n) + [1-][1-]k); auto.
Save.
Hint Resolve Uglb_eq_plus_cte_right.

Lemma Uglb_eq_mult:
  forall (k : U) (f : nat -> U), Uglb (fun n => k * f n) == k * Uglb f.
unfold Uglb; intros; auto.
transitivity ([1-] Ulub (fun n => (k * [1-]f n) + [1-]k)).
apply Uinv_eq_compat; apply Ulub_eq_compat; intro x; simpl; auto.
transitivity ([1-](Ulub (fun n => k * [1-]f n) + [1-]k)); auto.
transitivity ([1-](k * Ulub (fun n => [1-]f n) + [1-]k)); auto.
apply Uinv_eq_perm_left; auto.
transitivity (k* [1-][1-](Ulub (fun n => [1-]f n)) + [1-]k); auto.
Save.
Hint Resolve Uglb_eq_mult Uglb_eq_plus_cte_right.

Lemma Uglb_le_plus : forall f g, Uglb f + Uglb g <= Uglb (fun n => f n + g n).
intros; apply le_Uglb; auto.
Save.
Hint Resolve Uglb_le_plus.

Lemma Ulub_lub : forall f:nat -m> U, Ulub f == lub f.
intros; unfold Ulub; apply lub_eq_compat; intro n; simpl; intros; auto.
induction n; simpl; intros; auto.
rewrite IHn; apply Ole_antisym; auto.
Save.
Hint Resolve Ulub_lub.

Lemma Uglb_glb : forall f:nat -m-> U, Uglb f == glb f.
intros; unfold Uglb,glb.
apply Uinv_eq_compat; apply (Ulub_lub (UInv @ f)).
Save.
Hint Resolve Uglb_glb.

Lemma Uglb_glb_mon : forall (f:nat -> U) {Hf:monotonic (o2:=Iord U) f}, Uglb f == glb (mon f).
intros; rewrite <- Uglb_glb; reflexivity.
Save.
Hint Resolve @Uglb_glb_mon.

Lemma lub_le_plus : forall (f g : nat -m> U), lub ((UPlus @2 f) g) <= lub f + lub g.
intros; apply lub_le; simpl; auto.
Save.
Hint Resolve lub_le_plus.


Lemma glb_le_plus : forall (f g:nat -m-> U) , glb f + glb g <= glb ((Imon2 UPlus @2 f) g).
intros; apply le_glb; simpl; auto.
Save.
Hint Resolve glb_le_plus.


Lemma lub_eq_plus : forall f g : nat -m> U, lub ((UPlus @2 f) g) == lub f + lub g.
intros; apply Oeq_sym.
apply @lub_app2_eq 
  with (c1:=cpoU) (c2:=cpoU) (c3:=cpoU) (F:=UPlus) (f:=f) (g:=g); auto.
Save.
Hint Resolve lub_eq_plus.

Lemma glb_mon : forall f : nat -m> U, Uglb f == f O.
intros; apply Ole_antisym; auto.
apply le_Uglb; auto with arith.
Save.

Lemma lub_inv : forall (f g : nat -m> U), (forall n, f n <= [1-] g n) -> lub f <= [1-] (lub g).
intros; apply Uinv_le_perm_right.
apply lub_le; intros.
apply Uinv_le_perm_right.
rewrite (lub_lift_left f n). 
apply lub_le; simpl; unfold seq_lift_left; intros.
transitivity ([1-] (g (n+n0)%nat)); auto with arith.
Save.


Lemma glb_lift_left : forall (f:nat -m-> U) n,  
     glb f == glb (mon (seq_lift_left f n)).
intros.
exact (mlub_lift_left (c:=Uopp) f n).
Save.
Hint Resolve glb_lift_left.

Lemma Ulub_mon : forall f : nat -m-> U, Ulub f == f O.
intros; apply Ole_antisym; auto.
apply Ulub_le; intros; auto with arith.
Save.

Lemma lub_glb_le : forall (f:nat -m> U) (g:nat -m-> U), 
      (forall n, f n <= g n) -> lub f <= glb g.
intros; apply lub_le; intros.
rewrite (glb_lift_left g n); auto.
apply le_glb; simpl; unfold seq_lift_left; intros.
transitivity (f (n+n0))%nat; auto with arith.
Save.

Lemma lub_lub_inv_le : forall f g :nat -m> U, 
      (forall n, f n <= [1-]g n) -> lub f <= [1-] lub g.
intros; transitivity (glb (UInvopp @ g)).
apply lub_glb_le; auto.
unfold glb; apply Uinv_le_compat.
apply lub_le_compat; simpl; auto.
Save.

Lemma Uplus_opp_continuous_right : 
     forall k, continuous  (c1:=Uopp) (c2:=Uopp) (Imon (UPlus k)).
red; intros.
change (glb (Imon (UPlus k) @ h) <= k + glb h).
rewrite glb_eq_plus_cte_left; trivial.
Save.

Lemma Uplus_opp_continuous_left : 
     continuous  (c1:=Uopp) (c2:=fmon_cpo (o:=Iord U) (c:=Uopp))(Imon2 UPlus). 
red; intros.
intro k; simpl.
transitivity (glb (Imon (mshift UPlus k) @ h)); auto.
Save.

Hint Resolve Uplus_opp_continuous_right Uplus_opp_continuous_left.

Instance Uplusopp_continuous2 : continuous2 (c1:=Uopp) (c2:=Uopp) (c3:=Uopp) (Imon2 UPlus).
apply continuous_continuous2; auto.
exact (Uplus_opp_continuous_right).
Save.

Lemma Uplusopp_lub_eq : forall (f g : nat -m-> U),
    lub (cpo:=Uopp) f + lub (cpo:=Uopp) g == lub (cpo:=Uopp) ((Imon2 UPlus @2 f)  g).
intros; exact (lub_cont2_app2_eq (Imon2 UPlus) f g).
Save.

Lemma glb_eq_plus : forall (f g : nat -m-> U), glb ((Imon2 UPlus @2 f)  g) == glb f + glb g.
intros; apply Oeq_sym.
apply (lub_app2_eq (c1:=Uopp) (c2:=Uopp) (c3:=Uopp)) 
   with (F:=Imon2 UPlus) (f:=f) (g:=g); intros.
apply continuous_eq_compat with (Imon (UPlus k)); auto.
apply continuous_eq_compat with (Imon2 UPlus); auto.
Save.
Hint Resolve glb_eq_plus.

Instance UEsp_continuous2 : continuous2 UEsp.
red; intros; rewrite UEsp_simpl; unfold Uesp.
repeat rewrite Uinvopp_lub_eq.
rewrite Uplusopp_lub_eq.
rewrite Uinv_lub_eq.
apply lub_le_compat; intro n; auto.
Save.

Lemma Uesp_lub_eq : forall f g : nat -m> U, lub f & lub g == lub ((UEsp @2 f) g).
intros f g.
exact (lub_cont2_app2_eq UEsp f g).
Save.

Instance sigma_mon :monotonic sigma. 
intros f g H n.
apply sigma_le_compat; auto.
Save.

(* BUG V8.2-1
    Definition Sigma : (nat -> U) -m> nat-m> U 
    := mon sigma.
Anomaly: Non-functional construction. Please report.
*)

Definition Sigma : (nat -> U) -m> nat-m> U 
    := mon sigma (fmonotonic:=sigma_mon).

Lemma Sigma_simpl : forall f, Sigma f = sigma f.
trivial.
Save.

Lemma sigma_continuous1 : continuous Sigma.
red; intros; intro n.
induction n; auto.
transitivity (sigma (lub h) (S n)); auto.
rewrite sigma_S.
transitivity (lub h n + lub (Sigma @ h) n); auto.
rewrite fcpo_lub_simpl; repeat (rewrite fmon_lub_simpl).
transitivity (lub ((UPlus @2 (h <o> n)) (mshift (Sigma @ h) n))); auto.
apply lub_le_compat; simpl; auto.
Save.


Lemma sigma_lub1 : forall (f : nat -m> (nat -> U)) n, 
       sigma (lub f) n == lub ((mshift Sigma n) @ f).
intros; assert (Sigma (lub f) == lub (Sigma @ f)).
apply (lub_comp_eq Sigma); apply sigma_continuous1.
transitivity (lub (Sigma @ f) n); auto.
rewrite fmon_lub_simpl; apply lub_eq_compat; intro m; simpl; auto.
Save.

(* A more general type to deal with arbitrary representation of
   spaces of measurable functions
(** ** Type of spaces equiped with measurable functions *)
Record MFS : Type := mk_MF
   {MFA:Type; MF:>Type; fapp: MF -> MFA -> U;
     fplus : MF -> MF -> MF;
     fmult : U -> MF -> MF;
     finv : MF -> MF;
     fzero : MF;
     flub : (nat -> MF) -> MF;
     fplus_eq : forall (f g : MF) (x : MFA),
                             fapp (fplus f g) x == fapp f x + fapp g x;
     fmult_eq : forall (k:U) (f : MF) (x : MFA),
                             fapp (fmult k f) x == k * fapp f x;
     fzero_eq : forall (x : MFA), fapp fzero x == 0;
     finv_eq : forall (f : MF) (x : MFA), fapp (finv f) x == [1-]fapp f x;
     flub_eq : forall (f:nat -> MF) (x:MFA),
                            fapp (flub f) x == lub (fun n => fapp (f n) x)
}.
*)

(* Definition MF (A:Type) := A -> U. *)

Definition MF (A:Type) : Type := A -> U.

Definition MFcpo (A:Type) : cpo (MF A) := fcpo cpoU.

Definition MFopp (A:Type) : cpo (o:=Iord (A -> U)) (MF A).
apply (cpo_ord_equiv (o1:=ford A U (o:=Iord U))).
red; intros f g; simpl; split; intros x  y; auto.
exact (@fcpo A U (Iord U) Uopp).
Defined.

Lemma MFopp_lub_eq : forall (A:Type) (h:nat-m-> MF A),
      lub (cpo:=MFopp A) h == fun x => glb (Iord_app x @ h).
simpl; intros; intro x.
apply glb_eq_compat; intro n; auto.
Save.

Lemma fle_intro : forall (A:Type) (f g : MF A), (forall x, f x <= g x) -> f <= g.
intros; intro x; trivial.
Save.
Hint Resolve fle_intro.

Lemma feq_intro : forall (A:Type) (f g : MF A), (forall x, f x == g x) -> f == g.
intros; intro x; trivial.
Save.
Hint Resolve feq_intro.

Definition fplus (A:Type) (f g : MF A) : MF A := 
               fun x => f x + g x.

Definition fmult (A:Type) (k:U) (f : MF A) : MF A := 
               fun x => k *  f x.

Definition finv (A:Type) (f : MF A) : MF A := 
               fun x => [1-]  f x.

Definition fzero (A:Type) : MF A := 
               fun x => 0.

Definition fdiv  (A:Type) (k:U) (f : MF A) : MF A := 
               fun x => (f x) / k.

Definition flub (A:Type) (f : nat -m> MF A) : MF A := lub f.

Lemma  fplus_simpl : forall (A:Type)(f g : MF A) (x : A), 
                             fplus f g x = f x + g x.
trivial.
Save.

Lemma  fplus_def : forall (A:Type)(f g : MF A), 
                             fplus f g = fun x => f x + g x.
trivial.
Save.

Lemma  fmult_simpl : forall (A:Type)(k:U) (f : MF A) (x : A), 
                             fmult k f x = k * f x.
trivial.
Save.

Lemma  fmult_def : forall (A:Type)(k:U) (f : MF A), 
                             fmult k f = fun x => k * f x.
trivial.
Save.

Lemma  fdiv_simpl : forall (A:Type)(k:U) (f : MF A) (x : A), 
                             fdiv k f x = f x / k.
trivial.
Save.

Lemma  fdiv_def : forall (A:Type)(k:U) (f : MF A), 
                             fdiv k f = fun x => f x / k.
trivial.
Save.

Implicit Arguments fzero [].

Lemma fzero_simpl : forall (A:Type)(x : A), fzero A x = 0.
trivial.
Save.

Lemma fzero_def : forall (A:Type), fzero A = fun x:A => 0.
trivial.
Save.

Lemma finv_simpl : forall (A:Type)(f : MF A) (x : A), finv f x = [1-]f x.
trivial.
Save.

Lemma finv_def : forall (A:Type)(f : MF A), finv f = fun x => [1-](f x).
trivial.
Save.


Lemma flub_simpl : forall (A:Type)(f:nat -m> MF A) (x:A), 
                           (flub f) x = lub (f <o> x).
trivial.
Save.

Lemma flub_def : forall (A:Type)(f:nat -m> MF A), 
                           (flub f) = fun x => lub (f <o> x).
trivial.
Save.


Hint Resolve fplus_simpl fmult_simpl fzero_simpl finv_simpl flub_simpl.


Definition fone (A:Type) : MF A := fun x => 1.
Implicit Arguments fone [].

Lemma fone_simpl : forall (A:Type) (x:A), fone A x = 1.
trivial.
Save.

Lemma fone_def : forall (A:Type), fone A = fun (x:A) => 1.
trivial.
Save.

Definition fcte (A:Type) (k:U): MF A := fun x => k.
Implicit Arguments fcte [].

Lemma fcte_simpl : forall (A:Type) (k:U) (x:A), fcte A k x = k.
trivial.
Save.

Lemma fcte_def : forall (A:Type) (k:U), fcte A k = fun (x:A) => k.
trivial.
Save.

Definition fminus (A:Type) (f g :MF A) : MF A := fun x => f x - g x.

Lemma fminus_simpl : forall (A:Type) (f g: MF A) (x:A), fminus f g x = f x - g x.
trivial.
Save.

Lemma fminus_def : forall (A:Type) (f g: MF A), fminus f g = fun x => f x - g x.
trivial.
Save.


Definition fesp (A:Type) (f g :MF A) : MF A := fun x => f x & g x.

Lemma fesp_simpl : forall (A:Type) (f g: MF A) (x:A), fesp f g x = f x & g x.
trivial.
Save.

Lemma fesp_def : forall (A:Type) (f g: MF A) , fesp f g = fun x => f x & g x.
trivial.
Save.

Definition fconj (A:Type)(f g:MF A) : MF A := fun x => f x * g x.
 
Lemma fconj_simpl : forall (A:Type) (f g: MF A) (x:A), fconj f g x = f x * g x.
trivial.
Save.

Lemma fconj_def : forall (A:Type) (f g: MF A), fconj f g = fun x => f x * g x.
trivial.
Save.

 
Lemma MF_lub_simpl : forall  (A:Type) (f : nat -m> MF A) (x:A), 
             lub f x = lub (f <o>x).
auto.
Save.
Hint Resolve MF_lub_simpl.

Lemma MF_lub_def : forall  (A:Type) (f : nat -m> MF A), 
             lub f = fun x => lub (f <o>x).
auto.
Save.

(*
Definition fglb (A:Type) (f : nat -m-> MF A) : MF A := fun x => glb (f <o> x).

Lemma fglb_simpl : forall (A:Type) (f : nat -m-> MF A)(x:A), 
      fglb f x = glb (f <o> x).
trivial.
Save.
*)

(** *** Defining morphisms *)

Lemma fplus_eq_compat : forall A  (f1 f2 g1 g2:MF A), 
          f1==f2 -> g1==g2 -> fplus f1 g1 == fplus f2 g2.
intros; intro x.
repeat (rewrite fplus_simpl); firstorder.
Save.

Add Parametric Morphism (A:Type) : (@fplus A)
    with signature Oeq ==> Oeq ==> Oeq 
    as fplus_feq_compat_morph.
intros; exact (fplus_eq_compat H H0); auto.
Save.

Instance fplus_mon2 : forall A, monotonic2 (fplus (A:=A)).
unfold monotonic2; intros; intro a.
repeat rewrite fplus_simpl; firstorder.
Save.
Hint Resolve fplus_mon2.

Lemma fplus_le_compat : forall A  (f1 f2 g1 g2:MF A), 
          f1<=f2 -> g1<=g2 -> fplus f1 g1 <= fplus f2 g2.
intros; apply fplus_mon2; auto.
Save.

Add Parametric Morphism A : (@fplus A) with signature Ole ++> Ole ++> Ole 
    as fplus_fle_compat_morph.
intros f1 f2 H g1 g2 H1 x; exact (fplus_le_compat H H1 x); auto.
Save.

Lemma finv_eq_compat : forall A (f g:MF A), f==g -> finv f == finv g.
intros; intro x.
repeat (rewrite finv_simpl); firstorder.
Save.

Add Parametric Morphism A : (@finv A) with signature Oeq ==> Oeq 
    as finv_feq_compat_morph.
intros; exact (finv_eq_compat H). 
Save.

Instance finv_mon : forall A, monotonic (o2:=Iord (MF A)) (finv (A:=A)).
unfold monotonic; intros; intro a.
repeat rewrite finv_simpl; firstorder.
Save.
Hint Resolve finv_mon.

Lemma finv_le_compat : forall A (f g:MF A), f <= g -> finv g <= finv f.
intros; apply finv_mon; trivial.
Save.

Add Parametric Morphism A: (@finv A)
   with signature Ole --> Ole as finv_fle_compat_morph.
intros f g H x; exact (finv_le_compat H x).
Save.

Lemma fmult_eq_compat : forall A  k1 k2 (f1 f2:MF A), 
          k1 == k2 -> f1 == f2 -> fmult k1 f1 == fmult k2 f2.
intros A k1 k2 f1 f2 H H1 x.
repeat (rewrite fmult_simpl); firstorder.
Save.

Add Parametric Morphism A : (@fmult A) 
   with signature Oeq ==> Oeq ==> Oeq as fmult_feq_compat_morph.
intros k1 k2 H f1 f2 H1; exact (fmult_eq_compat k1 k2 H H1); auto.
Save.


Instance fmult_mon2 : forall A, monotonic2 (fmult (A:=A)).
unfold monotonic2; intros; intro a.
repeat rewrite fmult_simpl; firstorder.
Save.
Hint Resolve fmult_mon2.

Lemma fmult_le_compat : forall A  k1 k2 (f1 f2:MF A), 
          k1 <= k2 -> f1 <= f2 -> fmult k1 f1 <= fmult k2 f2.
intros; apply fmult_mon2; auto.
Save.

Add Parametric Morphism A : (@fmult A)
    with signature Ole ++> Ole ++> Ole as fmult_fle_compat_morph.
intros k1 k2 H f1 f2 H1 x; exact (fmult_le_compat k1 k2 H H1 x); auto.
Save.

Lemma fminus_eq_compat : forall A  (f1 f2 g1 g2:MF A), 
          f1 == f2 -> g1 == g2 -> fminus f1 g1 == fminus f2 g2.
intros A f1 f2 g1 g2 H H1 x.
repeat (rewrite fminus_simpl); firstorder.
Save.

Add Parametric Morphism A : (@fminus A)
    with signature Oeq ==> Oeq ==> Oeq as fminus_feq_compat_morph.
intros f1 f2 H g1 g2 H1 x; exact (fminus_eq_compat H H1 x); auto.
Save.

Instance fminus_mon2 : forall A, monotonic2 (o2:=Iord (MF A)) (fminus (A:=A)).
unfold monotonic2; intros; intro a.
repeat rewrite fminus_simpl; firstorder.
Save.
Hint Resolve fminus_mon2.

Lemma fminus_le_compat : forall A  (f1 f2 g1 g2:MF A), 
          f1 <= f2 -> g2 <= g1 -> fminus f1 g1 <= fminus f2 g2.
intros; apply fminus_mon2; auto.
Save.

Add Parametric Morphism A : (@fminus A) 
    with signature Ole ++> Ole --> Ole as fminus_fle_compat_morph.
intros f1 f2 H g1 g2 H1 x; exact (fminus_le_compat H H1 x); auto.
Save.

Lemma fesp_eq_compat : forall A  (f1 f2 g1 g2:MF A), 
          f1==f2 -> g1==g2 -> fesp f1 g1 == fesp f2 g2.
intros; intro x.
repeat (rewrite fesp_simpl); firstorder.
Save.

Add Parametric Morphism A : (@fesp A) with signature Oeq ==> Oeq ==> Oeq as fesp_feq_compat_morph.
intros; exact (fesp_eq_compat H H0); auto.
Save.

Instance fesp_mon2 : forall A, monotonic2 (fesp (A:=A)).
unfold monotonic2; intros; intro a.
repeat rewrite fesp_simpl; firstorder.
Save.
Hint Resolve fesp_mon2.

Lemma fesp_le_compat : forall A  (f1 f2 g1 g2:MF A), 
          f1<=f2 -> g1<=g2 -> fesp f1 g1 <= fesp f2 g2.
intros; apply fesp_mon2; auto.
Save.

Add Parametric Morphism A : (@fesp A)
   with signature Ole ++> Ole ++> Ole as fesp_fle_compat_morph.
intros f1 f2 H g1 g2 H1 x; exact (fesp_le_compat H H1 x); auto.
Save.

Lemma fconj_eq_compat : forall A  (f1 f2 g1 g2:MF A), 
           f1==f2 -> g1==g2 -> fconj f1 g1 == fconj f2 g2.
 intros; intro x.
 repeat (rewrite fconj_simpl); firstorder.
 Save.
 
 Add Parametric Morphism A : (@fconj A)
   with signature Oeq ==> Oeq ==> Oeq
 as fconj_feq_compat_morph.
 intros; exact (fconj_eq_compat H H0); auto.
 Save.

Instance fconj_mon2 : forall A, monotonic2 (fconj (A:=A)).
unfold monotonic2; intros; intro a.
repeat rewrite fconj_simpl.
apply Umult_le_compat; trivial.
Save.
Hint Resolve fconj_mon2.

Lemma fconj_le_compat : forall A  (f1 f2 g1 g2:MF A), 
           f1 <= f2 -> g1 <= g2 -> fconj f1 g1 <= fconj f2 g2.
intros; apply fconj_mon2; auto.
Save.
 
Add Parametric Morphism A : (@fconj A) with signature Ole  ++> Ole  ++> Ole 
as fconj_fle_compat_morph.
intros.
exact (fconj_le_compat H H0); auto.
Save.
 

Hint Immediate fplus_le_compat fplus_eq_compat fesp_le_compat fesp_eq_compat
fmult_le_compat fmult_eq_compat fminus_le_compat fminus_eq_compat
fconj_eq_compat.

Hint Resolve finv_eq_compat.

(** *** Elementary properties *)

Lemma fle_fplus_left : forall (A:Type) (f g : MF A), f <= fplus f g.
intros m f g x; rewrite fplus_simpl; auto.
Save.

Lemma fle_fplus_right : forall (A:Type) (f g : MF A), g <= fplus f g.
intros m f g x; rewrite fplus_simpl; auto.
Save.

Lemma fle_fmult : forall (A:Type) (k:U)(f : MF A), fmult k f <= f.
intros m k f x; rewrite fmult_simpl; auto.
Save.

Lemma fle_zero : forall (A:Type) (f : MF A), fzero A <= f.
intros m f x; rewrite fzero_simpl; auto.
Save.

Lemma fle_one : forall (A:Type) (f : MF A), f <= fone A.
intros m f x; rewrite fone_simpl; auto.
Save.

Lemma feq_finv_finv : forall (A:Type) (f : MF A), finv (finv f) == f.
intros m f x; rewrite finv_simpl; auto.
Save.

Lemma fle_fesp_left : forall (A:Type) (f g : MF A), fesp f g <= f.
intros m f g x; rewrite fesp_simpl; auto.
Save.

Lemma fle_fesp_right : forall (A:Type) (f g : MF A), fesp f g <= g.
intros m f g x; rewrite fesp_simpl; auto.
Save.

Lemma fle_fconj_left : forall (A:Type) (f g : MF A), fconj f g <= f.
intros m f g x; rewrite fconj_simpl; auto.
Save.
 
Lemma fle_fconj_right : forall (A:Type) (f g : MF A), fconj f g <= g.
intros m f g x; rewrite fconj_simpl; auto.
Save.
 
Lemma fconj_decomp : forall A (f g : MF A), 
             f == fplus (fconj f g) (fconj f (finv g)).
intros; simpl; intros x; apply Umult_decomp.
Save.
Hint Resolve fconj_decomp.

(** *** Compatibility of addition of two functions *)

Definition fplusok (A:Type) (f g : MF A) :=  f <= finv g.
Hint Unfold fplusok.

Lemma fplusok_sym : forall (A:Type) (f g : MF A) , fplusok f g -> fplusok g f.
unfold fplusok, finv; intros;  intro; auto.
Save.
Hint Immediate fplusok_sym.

Lemma fplusok_inv : forall (A:Type) (f : MF A) , fplusok f (finv f).
intros; apply fplusok_sym; unfold fplusok; auto.
Save.
Hint Resolve fplusok_inv.

Lemma fplusok_le_compat : forall (A:Type)(f1 f2 g1 g2:MF A), 
      fplusok f2 g2 -> f1 <= f2 -> g1 <= g2 -> fplusok f1 g1.
unfold fplusok; intros.
transitivity f2; trivial.
transitivity (finv g2); trivial.
apply finv_le_compat; auto.
Save.

Hint Resolve fle_fplus_left  fle_fplus_right fle_zero  fle_one feq_finv_finv finv_le_compat
fle_fmult fle_fesp_left fle_fesp_right fle_fconj_left fle_fconj_right.

Lemma fconj_fplusok : forall (A:Type)(f g h:MF A), 
            fplusok g h -> fplusok (fconj f g) (fconj f h).
intros; apply fplusok_le_compat with g h; auto.
Save.
Hint Resolve fconj_fplusok.

Definition Fconj A : MF A -m> MF A -m> MF A := mon2 (fconj (A:=A)).
 
Lemma Fconj_simpl : forall A f g, Fconj A f g = fconj f g.
 trivial.
Save.
 
Lemma fconj_sym : forall A (f g : MF A), fconj f g == fconj g f.
 intros; intro x; unfold fconj; auto.
Save.
Hint Resolve fconj_sym.

Lemma Fconj_sym : forall A (f g : MF A), Fconj A f g == Fconj A g f.
intros; repeat rewrite Fconj_simpl; auto.
Save.
Hint Resolve Fconj_sym.

Lemma lub_MF_simpl : forall A (h : nat -m> MF A) (x:A), lub h x = lub (h <o> x).
intros; exact (fcpo_lub_simpl h x).
Save.

Instance fconj_continuous2 A : continuous2 (Fconj A).
intros; apply continuous2_sym.
intros; apply Fconj_sym.
red; intros.
intro x; rewrite (Fconj_simpl k (lub h)).
unfold fconj.
repeat rewrite fcpo_lub_simpl.
transitivity (lub (UMult (k x) @  (h <o> x))).
apply (UMult_continuous_right (k x)).
apply lub_le_compat; simpl; auto.
Save.
 
Definition Fmult A : U -m> MF A -m> MF A := mon2 (fmult (A:=A)).
 
Lemma Fmult_simpl : forall A k f, Fmult A k f = fmult k f.
 trivial.
Save.
 
Lemma Fmult_simpl2 : forall A k f x, Fmult A k f x = k * (f x).
 trivial.
Save.

Lemma fmult_continuous2 : forall A, continuous2 (Fmult A).
red; intros.
rewrite Fmult_simpl.
intro x; unfold fmult.
repeat rewrite lub_MF_simpl.
rewrite (Umult_continuous2 f (g <o> x)).
apply lub_le_compat; intro y; simpl; auto.
Save.

(* This is a ring like asymetric commutation lemma: put constant on the left. *)
Lemma Umult_sym_cst:
  forall A : Type,
  forall (k : U) (f : MF A), (fun x : A => f x * k) == (fun x : A => k * f x).
Proof.
  intros A d k f.
  setoid_rewrite Umult_sym at 1.
  reflexivity.
Qed.

(*
Instance fplusok_Oeq_compat_iff `(A:Type) : 
  Morphism (pointwise_relation _ Oeq ==> pointwise_relation _ Oeq ==> iff) (@fplusok A).
Proof.
  simpl;red.
  unfold fplusok , Morphism, pointwise_relation, fun_ext, finv;simpl;red.
  unfold fun_ext , finv.
  red.
  intros A0 x y H x0 y0 H0.
  setoid_rewrite <- H.
  setoid_rewrite <- H0.
  reflexivity.
Save.

Instance fplusok_Ole_compat_iff `(A:Type) : 
  Morphism (Oeq ==> Oeq ==> iff) (@fplusok A).
Proof.
  unfold fplusok.
  red.
  intros A0.
  red.
  intros x y H.
  red.
  intros x0 y0 H0.
  rewrite H.
  rewrite H0.
  reflexivity.
Save.
*)
(** ** Fixpoints of functions of type [A -> U] *)
Section FixDef.
Variable A :Type.

Variable F : MF A -m> MF A.

Definition mufix : MF A := fixp F.

Definition G : MF A --m-> MF A := Imon F. 

Definition nufix : MF A := fixp (c:=MFopp A) G.

Lemma mufix_inv : forall f : MF A, F f <= f -> mufix  <= f.
unfold mufix; intros; apply fixp_inv; auto.
Save.
Hint Resolve mufix_inv.

Lemma nufix_inv : forall f :MF A, f  <= F f -> f <= nufix.
unfold nufix; intros.
change (Ole (ord:=Iord (MF A)) (fixp (c:=MFopp A) G) f); apply (fixp_inv (c:=MFopp A)); auto.
Save.
Hint Resolve nufix_inv.

Lemma mufix_le : mufix  <= F mufix.
unfold mufix; auto.
Save.
Hint Resolve mufix_le.

Lemma nufix_sup : F nufix <= nufix.
unfold nufix.
change (Ole (ord:=Iord (MF A)) (fixp (c:=MFopp A) G) (G (fixp (c:=MFopp A) G))); auto.
Save.
Hint Resolve nufix_sup.

(*
Definition Fcontlub := forall (fn : nat -> A -> U), increase fn ->
           fle (F (lub fn)) (lub (fun n => F (fn n))).
Definition Fcontglb := forall (fn : nat -> A -> U), decrease fn ->
           fle (fglb (fun n => F (fn n))) (F (fglb fn)).

Lemma Fcontlub_fle : Fcontlub -> forall (fn : nat -> A -> U), increase fn ->
           fle (F (flub fn)) (flub (fun n => F (fn n))).
auto.
Save.

Lemma Fcontglb_fle : Fcontglb -> forall (fn : nat -> A -> U), decrease fn ->
           fle (fglb (fun n => F (fn n))) (F (fglb fn)).
auto.
Save.


Hypothesis muFcont : forall (fn : nat -> A -> U), increase fn ->
           fle (F (flub fn)) (flub (fun n => F (fn n))).

Hypothesis nuFcont : forall (fn : nat -> A -> U), decrease fn ->
           fle (fglb (fun n => F (fn n))) (F (fglb fn)).

Implicit Arguments muFcont [].
Implicit Arguments nuFcont [].

Lemma incr_muiter : increase muiter.
red; intros; induction n; red; simpl; intros; auto.
Save.

Lemma decr_nuiter : decrease nuiter.
red; intros; induction n; red; simpl; intros; auto.
Save.

Hint Resolve incr_muiter decr_nuiter.
*)

Lemma mufix_eq : continuous F -> mufix  == F mufix.
intros; unfold mufix; apply fixp_eq; auto.
Save.
Hint Resolve mufix_eq.

Lemma nufix_eq : continuous (c1:=MFopp A) (c2:=MFopp A) G -> nufix  == F nufix.
intros; unfold nufix.
assert (Oeq (ord:=Iord (MF A)) (fixp (c:=MFopp A) G) (G (fixp (c:=MFopp A) G))); auto.
apply fixp_eq; auto.
Save.
Hint Resolve nufix_eq.

End FixDef.
Hint Resolve mufix_le mufix_eq nufix_sup nufix_eq.

Definition Fcte (A:Type) (f:MF A) : MF A -m> MF A := mon (cte (MF A) f).

Lemma mufix_cte : forall (A:Type) (f:MF A), mufix (Fcte f) == f.
intros A f; exact (fixp_cte f).
Save.

Lemma nufix_cte : forall (A:Type) (f:MF A), nufix (Fcte f) == f.
intros A f.
change (@Oeq (MF A) (@Iord (MF A) (@ford A U ordU)) (@nufix A (@Fcte A f)) f).
unfold nufix, Fcte.
(* Ceci suffisait en v8.2: *)
(* transitivity (fixp (c:=MFopp A) (mon (o1:=Iord (MF A)) (o2:=Iord (MF A)) (cte (MF A) f)))  *)
transitivity (fixp (c:=MFopp A) (@mon _ (Iord (MF A)) _ (Iord (MF A)) (cte (MF A) f) (@mon_cte (MF A) (@Iord (MF A) (@ford A U ordU)) 
              (MF A) (@Iord (MF A) (@ford A U ordU)) f))).
apply fixp_eq_compat.
intros g x; simpl; auto.
exact (fixp_cte (o:=Iord (MF A)) (c:=MFopp A) f).
Save.

Hint Resolve mufix_cte nufix_cte.

(** ** Properties of (pseudo-)barycenter of two points *)

Lemma Uinv_bary :
   forall a b x y : U, a <= [1-]b -> 
      [1-] (a * x + b * y) == a * [1-] x + b * [1-] y + [1-] (a + b).
intros a b x y sum_le_one.
apply Uplus_eq_simpl_left with (a * x); auto.
apply Uinv_le_perm_right.
rewrite (Udistr_inv_left a x).
repeat norm_assoc_right.
apply Uplus_le_compat_right.
transitivity (b + [1-] (a + b)); auto.
(* transitivity ([1-] (a + b) + b); auto. *)
transitivity ([1-] (b * y)).
transitivity 
   ([1-] (a * x + b * y) + a * x); auto.
setoid_rewrite (Udistr_inv_left b y); auto.
transitivity  
 ((a * x + a * [1-] x) + b * [1-] y + [1-] (a + b)).
assert (x <= ([1-] ([1-] x))); auto.
rewrite <- (Udistr_plus_left a _ _ H); auto.
rewrite (Uinv_opp_right x).
rewrite (Umult_one_right a).
transitivity (b * [1-] y + ([1-] (a + b) + a)).
assert (b <= [1-] a); auto.
(* rewrite (Uinv_plus_left _ _ H0); auto. *)
rewrite (Uplus_sym a (b * [1-] y)); auto.
transitivity 
(b * [1-] y + (a + [1-] (a + b))); auto.
transitivity 
(((a * x + a * [1-] x) + (b * [1-] y + [1-] (a + b)))); auto.
transitivity 
(((a * x + (a * [1-] x + (b * [1-] y + [1-] (a + b)))))); auto.
Save.
Hint Resolve Uinv_bary.

Lemma Uinv_bary_le : 
   forall a b x y : U, a <= [1-]b -> a * [1-] x + b * [1-] y <= [1-] (a * x + b * y).
intros; rewrite Uinv_bary; auto.
Save.
Hint Resolve Uinv_bary_le.

Lemma Uinv_bary_eq : forall a b x y : U, a == [1-]b -> 
      [1-] (a * x + b * y) == a * [1-] x + b * [1-] y.
intros; rewrite H; rewrite Uinv_bary; auto.
rewrite Uinv_opp_left.
rewrite Uinv_one; auto.
Save.
Hint Resolve Uinv_bary_eq.

Lemma bary_refl_eq : forall a b x, a == [1-]b ->  a * x + b * x == x.
intros; rewrite H; auto.
Save.
Hint Resolve bary_refl_eq.

Lemma bary_refl_feq : forall A a b (f:A -> U) , 
      a == [1-]b ->  (fun x => a * f x + b * f x) == f.
intros; intro x; rewrite H; auto.
Save.
Hint Resolve bary_refl_feq.

Lemma bary_le_left : forall a b x y,  [1-]b <= a -> x <= y -> x <= a * x + b * y.
intros; transitivity ([1-]b * x + b * x); auto.
Save.

Lemma bary_le_right : forall a b x y, a <= [1-]b -> x <= y -> a * x + b * y <= y.
intros; transitivity ([1-]b * y + b * y); auto.
Save.

Hint Resolve bary_le_left bary_le_right.

Lemma bary_up_eq : forall a b x y : U, a == [1-]b -> x <= y -> a * x + b * y == x + b * (y - x).
intros.
rewrite H; rewrite Uinv_mult_minus.
rewrite Uminus_plus_perm_right; auto.
Save.

Lemma bary_up_le : forall a b x y : U, a <= [1-]b -> a * x + b * y <= x + b * (y - x).
intros; transitivity (([1-]b) * x + b * y); auto.
apply (Ule_total y x); intros; trivial.
intros; rewrite Uminus_le_zero; trivial.
rewrite Umult_zero_right.
rewrite Uplus_zero_right.
transitivity (([1-] b) * x + b * x); auto. 
rewrite bary_up_eq; trivial.
Save.

Lemma bary_anti_mon : forall a b a' b' x y : U, 
  a == [1-]b -> a' == [1-]b' -> a <= a' -> x <= y -> a' * x + b' * y <= a * x  + b * y.
intros; rewrite bary_up_eq; trivial.
rewrite bary_up_eq; trivial.
apply Uplus_le_compat; auto.
apply Umult_le_compat_left; trivial.
apply Uinv_le_simpl.
rewrite <- H, <- H0; auto.
Save.
Hint Resolve bary_anti_mon.


Lemma bary_Uminus_left : 
   forall a b x y : U, a <= [1-]b -> (a * x + b * y) - x <= b * (y - x).
intros; apply Uplus_le_perm_left.
apply bary_up_le; trivial.
Save.

Lemma bary_Uminus_left_eq :   
    forall a b x y : U, a == [1-]b -> x <= y -> (a * x + b * y) - x == b * (y - x).
intros; apply Uplus_eq_perm_left.
apply Uinv_le_perm_right.
transitivity (y - x); auto.
apply bary_up_eq; trivial.
Save.

Lemma Uminus_bary_left 
   : forall a b x y : U, [1-]a <= b -> x - (a * x + b * y) <= b * (x - y).
intros; rewrite <- Uminus_assoc_left.
transitivity (([1-]a) * x - b * y); auto.
rewrite Uminus_distr_right; auto.
Save.

Lemma Uminus_bary_left_eq
   : forall a b x y : U, a == [1-]b -> y <= x -> x - (a * x + b * y) == b * (x - y).
intros; rewrite H; rewrite <- Uminus_assoc_left.
transitivity (b * x - b * y); auto.
apply Uminus_eq_compat; auto.
Save.

Hint Resolve bary_up_eq bary_up_le bary_Uminus_left Uminus_bary_left bary_Uminus_left_eq Uminus_bary_left_eq.

Lemma bary_le_simpl_right 
     : forall a b x y : U, a == [1-]b -> ~ 0 == a -> a * x + b * y <= y -> x <= y.
intros.
apply (orc_inv_plus_one (a * x) (b * y)); intros; auto.
apply Umult_le_simpl_left with a; auto.
apply Uplus_le_simpl_right with (b * y); auto.
rewrite bary_refl_eq; auto.
transitivity 1; auto.
rewrite <- H2; trivial.
Save.

Lemma bary_le_simpl_left 
     : forall a b x y : U, a == [1-]b -> ~ 0 == b -> x <= a * x + b * y -> x <= y.
intros.
apply Umult_le_simpl_left with b; auto.
apply Uplus_le_simpl_left with (a * x); auto.
rewrite bary_refl_eq; auto.
Save.

Lemma diff_bary_left_eq
   : forall a b x y : U, a == [1-]b -> diff x (a * x + b * y) == b * diff x y.
intros; unfold diff.
apply (Ule_total x y); trivial; intros.
(* case x <= y *)
assert (x <= a * x + b * y); auto.
rewrite (Uminus_le_zero _ _ H0); rewrite (Uminus_le_zero _ _ H1); auto.
repeat rewrite Uplus_zero_left; auto.
(* case y <= x *)
assert (a * x + b * y <= x).
assert (b == [1-] a).
apply Uinv_eq_perm_right; auto.
rewrite (Uplus_sym (a * x)); auto.
rewrite (Uminus_le_zero _ _ H0); rewrite (Uminus_le_zero _ _ H1); auto.
repeat rewrite Uplus_zero_right; auto.
Save.
Hint Resolve diff_bary_left_eq.

Lemma Uinv_half_bary :
   forall x y : U, [1-] ([1/2] * x + [1/2] * y) == [1/2] * [1-] x + [1/2] * [1-] y.
intros; rewrite Uinv_bary; auto.
rewrite Unth_one_plus; rewrite Uinv_one; auto.
Save.
Hint Resolve Uinv_half_bary.

Lemma Uinv_Umult : forall x y, [1-]x * [1-]y == [1-](x-x*y+y).
Proof.
  intros.
  setoid_rewrite Uinv_eq.
  rewrite Udistr_inv_right.
  rewrite 2!Uinv_inv.
  rewrite Umult_sym; rewrite Uinv_mult_minus.
  auto.
Qed.
Hint Resolve Uinv_Umult.

(** ** Properties of generalized sums [sigma] *)

Lemma sigma_plus : forall (f g : nat -> U) (n:nat),
   sigma (fun k => (f k) + (g k)) n == sigma f n + sigma g n.
intros; induction n; simpl; auto.
repeat rewrite sigma_S; setoid_rewrite IHn.
repeat norm_assoc_right; apply Uplus_eq_compat_right.
setoid_rewrite (Uplus_sym (g n) ((sigma f n) + (sigma g n))).
repeat norm_assoc_right; apply Uplus_eq_compat_right; auto.
Save.


Definition retract (f : nat -> U) (n : nat) := forall k, (k < n)%nat -> f k <= [1-] (sigma f k).

Lemma retract_class : forall f n, class (retract f n).
unfold retract; red; intros.
apply Ule_class; red; intros.
apply H; intro; auto.
Save.
Hint Resolve retract_class.

Lemma retract0 : forall (f : nat -> U), retract f 0.
red; intros; absurd (k < O)%nat; auto with arith.
Save.

Lemma retract_pred : forall (f : nat -> U) (n : nat), retract f (S n) -> retract f n.
unfold retract; auto with arith.
Save.

Lemma retractS: forall (f : nat -> U) (n : nat), retract f (S n) -> f n <= [1-] (sigma f n).
unfold retract; auto with arith.
Save.

Hint Immediate retract_pred retractS.

Lemma retractS_inv :
     forall (f : nat -> U) (n : nat), retract f (S n) -> sigma f n <= [1-] f n.
intros; apply Uinv_le_perm_right; auto.
Save.
Hint Immediate retractS_inv.

Lemma retractS_intro: forall (f : nat -> U) (n : nat),
   retract f n -> f n <= [1-] (sigma f n) -> retract f (S n).
unfold retract; intros.
assert ((k<n)%nat \/ k=n); try omega; intuition; subst; auto.
Save.

Hint Resolve retract0 retractS_intro.

Lemma retract_lt : forall (f : nat -> U) (n : nat),  sigma f n < 1 -> retract f n.
induction n; auto.
rewrite sigma_S.
intros;assert ((sigma f n)<1).
apply Ole_lt_trans with (f n + sigma f n); auto.
assert (f n <= [1-](sigma f n)); auto.
Save.

Lemma retract_unif :
    forall (f : nat -> U) (n : nat),
             (forall k, (k<=n)%nat -> f k <= [1/]1+n) -> retract f (S n).
red; intros.
transitivity ([1/]1+n); auto with arith.
apply Uinv_le_perm_right.
transitivity (sigma (fun k => [1/]1+n) n); auto.
transitivity (sigma f n); auto with arith.
apply Uinv_le_perm_right; auto.
Save.

Hint Resolve retract_unif.

Lemma retract_unif_Unthp :
  forall (f : nat -> U) (n : nat),
  (forall k : nat, (k <= n)%nat -> f k <= [1/]n) -> retract f n.
Proof.
  intros; destruct n; auto.
Defined.
Hint Resolve retract_unif_Unthp.

Lemma sigma_mult :
  forall (f : nat -> U) n c, retract f n -> sigma (fun k => c * (f k)) n == c * (sigma f n).
intros; induction n; simpl; auto.
repeat rewrite sigma_S.
assert (H1: retract f n); auto.
rewrite (IHn H1).
rewrite (Udistr_plus_left c _ _ (retractS H)); auto.
Save.
Hint Resolve sigma_mult.

Lemma sigma_mult_perm :
  forall (f : nat -> U) n c1 c2, retract (fun k => c1 * (f k)) n -> retract (fun k => c2 * (f k)) n
  -> c1 * (sigma (fun k => c2 * (f k)) n) == c2 * (sigma (fun k => c1 * (f k)) n).
intros; transitivity (sigma (fun k => c2 * (c1 * (f k))) n); auto.
rewrite <- sigma_mult; auto.
Save.
Hint Resolve sigma_mult_perm.

Lemma sigma_prod_maj :  forall (f g : nat -> U) n,
   sigma (fun k => (f k) * (g k)) n <= sigma f n.
auto.
Save.

Hint Resolve sigma_prod_maj.

Lemma sigma_prod_le :  forall (f g : nat -> U) (c:U), (forall k, (f k) <= c)
   -> forall n, retract g n -> sigma (fun k => (f k) * (g k)) n <= c * (sigma g n).
induction n; simpl; intros; auto.
repeat rewrite sigma_S.
transitivity ((f n) * (g n) + (c * sigma g n)); auto.
transitivity ( c * (g n) + (c * sigma g n)); auto.
setoid_rewrite (Udistr_plus_left c _ _ (retractS H0)); auto.
Save.

Lemma sigma_prod_ge :  forall (f g : nat -> U) (c:U), (forall k, c <= (f k))
   -> forall n, (retract g n) -> c * (sigma g n) <= (sigma (fun k => (f k) * (g k)) n).
induction n; simpl; intros; auto.
repeat rewrite sigma_S.
rewrite (Udistr_plus_left c _ _ (retractS H0)); auto.
Save.

Hint Resolve sigma_prod_maj sigma_prod_le  sigma_prod_ge.

Lemma sigma_inv : forall (f g : nat -> U) (n:nat), (retract f n) ->
  [1-] (sigma (fun k => f k * g k) n) == (sigma (fun k => f k * [1-] (g k)) n) + [1-] (sigma f n).
intros; induction n; repeat rewrite sigma_S; auto.
apply Uplus_eq_simpl_right with ((f n) * (g n)).
rewrite 
 (Uinv_inv (f n * g n + sigma (fun k : nat => f k * g k) n));auto.
apply Uinv_le_perm_right.
rewrite (Udistr_inv_left (f n) (g n)).
repeat norm_assoc_right; apply Uplus_le_compat_right.
transitivity 
  (sigma f n + [1-] (f n + sigma f n)); auto.
(* assert (sigma f n <= [1-] (f n)).
apply Uinv_le_perm_right; auto.
rewrite <- (Uinv_plus_right _ _ H0); auto. *)

assert (sigma (fun k : nat => f k * g k) n <= [1-] (f n * g n)).
transitivity (sigma f n); auto.
transitivity ([1-] (f n)); auto.
rewrite (Uinv_plus_left _ _ H0).
transitivity (sigma (fun k : nat => f k * [1-] g k) n + [1-] sigma f n).
auto.
rewrite (Uplus_sym (f n * [1-] (g n))
                          (sigma (fun k : nat => f k * [1-] (g k)) n)). 
repeat norm_assoc_right; apply Uplus_eq_compat_right.
rewrite (Uplus_sym  ([1-] (f n + sigma f n)) (f n * g n)).
repeat norm_assoc_left.
assert ([1-] (g n) <= [1-] (g n)); auto.

rewrite <- (Udistr_plus_left (f n) _ _ H1).
rewrite (Uinv_opp_left (g n)).
rewrite (Umult_one_right (f n)); auto.
(* rewrite (Uplus_sym (f n) ([1-] (f n + sigma f n))).
apply Oeq_sym; apply Uinv_plus_left; auto. *)
Save.

Lemma sigma_inv_simpl : forall (n:nat) (f: nat -> U),
    sigma (fun i => [1/]1+n * [1-] (f i)) (S n) == [1-] sigma (fun i => [1/]1+n * (f  i)) (S n).
intros.
pose (g:= fun (k:nat) => [1/]1+n).
assert (Rg:retract g (S n)) by auto.
transitivity (sigma (fun i : nat => [1/]1+n * [1-] f i) (S n) + [1-] sigma g (S n)).
cbv delta [g].
rewrite <- Unth_sigma_Sn.
rewrite Uinv_one;auto.
symmetry; apply (sigma_inv f Rg).
Save.

(** ** Product by an integer *)

(** *** Definition of [Nmult n x] written [n */ x] *)
Fixpoint Nmult (n: nat) (x : U) {struct n} : U :=
   match n with O => 0 | (S O) => x | S p => x + (Nmult p x) end.

(** *** Condition for [n */ x] to be exact : [n = 0] or [ x <= 1/n ] *)
Definition Nmult_def (n: nat) (x : U) :=
   match n with O => True | S p => x <= [1/]1+p end.

Lemma Nmult_def_O : forall x, Nmult_def O x.
simpl; auto.
Save.
Hint Resolve Nmult_def_O.

Lemma Nmult_def_1 : forall x, Nmult_def (S O) x.
simpl; intro; rewrite Unth_zero; auto.
Save.
Hint Resolve Nmult_def_1.

Lemma Nmult_def_intro : forall n x , x <= [1/]1+n -> Nmult_def (S n) x.
trivial.
Save.
Hint Resolve Nmult_def_intro.

Lemma Nmult_def_Unth_le : forall n m, (n <= S m)%nat -> Nmult_def n ([1/]1+m).
intros; destruct n; auto with arith.
Save.
Hint Resolve Nmult_def_Unth_le.

Lemma Nmult_def_le : forall n m x, (n <= S m)%nat -> x <= [1/]1+m -> Nmult_def n x.
intros; destruct n; simpl; auto with arith.
transitivity ([1/]1+m); auto with arith.
Save.
Hint Resolve Nmult_def_le.

Lemma Nmult_def_introp : forall n x, x <= [1/]n -> Nmult_def n x.
intros; apply Nmult_def_le with (pred n); intuition.
Save.
Hint Resolve Nmult_def_introp.

Lemma Nmult_def_Unth: forall n , Nmult_def (S n) ([1/]1+n).
auto.
Save.
Hint Resolve Nmult_def_Unth.

Lemma Nmult_def_Unthp : forall n, Nmult_def n ([1/]n).
Proof.
  intros.
  destruct n; auto.
Qed.
Hint Resolve Nmult_def_Unthp.

Lemma Nmult_def_pred : forall n x, Nmult_def (S n) x -> Nmult_def n x.
intros n x; case n; simpl; intros; auto.
transitivity ([1/]1+(S n0)); auto.
Save.

Hint Immediate Nmult_def_pred.

Lemma Nmult_defS : forall n x, Nmult_def (S n) x -> x <= [1/]1+n.
destruct n; simpl; intros; auto.
Save.
Hint Immediate Nmult_defS.

Lemma Nmult_def_class : forall n p, class (Nmult_def n p).
unfold class; destruct n; intuition.
apply Nmult_def_intro.
apply Ule_class; intuition.
Save.
Hint Resolve Nmult_def_class.

Infix "*/" := Nmult (at level 60) : U_scope.

Add Morphism Nmult_def with signature eq ==> Oeq ==> iff as Nmult_def_eq_compat.
unfold Nmult_def; intro n; destruct n; intuition.
transitivity x; auto.
transitivity y0; auto.
Save.

Lemma Nmult_def_zero : forall n, Nmult_def n 0.
destruct n; auto.
Save.
Hint Resolve Nmult_def_zero.


Lemma Nmult_def_elimp : forall n x, Nmult_def n x -> x <= [1/]n.
unfold Nmult_def; intros.
destruct n; auto.
Save.
Hint Immediate Nmult_def_elimp.

Lemma Nmult_def_le_compat_left 
  : forall n m x, (n<=m)%nat -> Nmult_def m x -> Nmult_def n x.
intros; apply Nmult_def_introp.
transitivity ([1/]m); intuition.
Save.

Lemma Nmult_def_le_compat_right 
  : forall n x y, (y <= x) -> Nmult_def n x -> Nmult_def n y.
intros; apply Nmult_def_introp.
transitivity x; auto.
Save.


(** *** Properties of [n */ x] *)

Lemma Nmult_0 : forall (x:U), O */ x = 0.
trivial.
Save.

Lemma Nmult_1 : forall (x:U), (S O) */ x = x.
trivial.
Save.

Lemma Nmult_zero : forall n, n */ 0 == 0.
induction n; simpl; auto.
destruct n; auto.
Save.

Lemma Nmult_SS : forall (n:nat) (x:U), S (S n) */ x = x + (S n */ x).
destruct n; simpl; auto.
Save.

Lemma Nmult_2 : forall (x:U), 2 */ x = x + x.
trivial.
Save.

Lemma Nmult_S : forall (n:nat) (x:U), S n */ x == x + (n */ x).
destruct n; intros; simpl; auto.
Save.

Hint Resolve Nmult_0 Nmult_zero Nmult_1 Nmult_SS Nmult_2 Nmult_S.

Add Morphism Nmult with signature eq ==> Oeq ==> Oeq as Nmult_eq_compat.
intros n x1 x2 eq1; induction n; simpl; intros; auto.
destruct n; repeat rewrite Nmult_SS; trivial.
apply Uplus_eq_compat; auto.
Save.
Hint Immediate Nmult_eq_compat.

Lemma Nmult_eq_compat_left : forall (n:nat) (x y:U), x == y -> n */ x == n */ y.
auto.
Save.

Lemma Nmult_eq_compat_right : forall (n m:nat) (x:U), (n = m)%nat -> n */ x == m */ x.
auto.
Save.
Hint Resolve Nmult_eq_compat_right.

Lemma Nmult_le_compat_right :  forall n x y, x <= y -> n */ x <= n */ y.
intros; induction n; auto.
rewrite (Nmult_S n x); rewrite (Nmult_S n y);auto.
Save.

Lemma Nmult_le_compat_left : forall n m x, (n <= m)%nat -> n */ x <= m */ x.
induction 1; trivial.
rewrite (Nmult_S m x); auto.
transitivity (m */ x); auto.
Save.

Hint Resolve Nmult_eq_compat_right Nmult_le_compat_right Nmult_le_compat_left.

Lemma Nmult_le_compat : forall (n m:nat) x y, n <= m -> x <= y -> n */ x <= m */ y.
intros; transitivity (n */y); auto.
Save.
Hint Immediate Nmult_le_compat.

Instance Nmult_mon2 : monotonic2 Nmult.
red; intros; apply Nmult_le_compat; auto.
Save.

Definition NMult : nat -m> U -m> U :=mon2 Nmult.


Lemma Nmult_sigma : forall (n:nat) (x:U), n */ x == sigma (fun k => x) n.
intros n x; induction n; simpl; intros; auto.
destruct n; auto.
Save.

Hint Resolve Nmult_sigma.

Lemma Nmult_Unth_prop : forall n:nat, [1/]1+n == [1-] (n*/ ([1/]1+n)).
intro.
rewrite (Nmult_sigma n ([1/]1+n)).
exact (Unth_prop n).
Save.
Hint Resolve Nmult_Unth_prop.

Lemma Nmult_n_Unth: forall n:nat, n */ [1/]1+n == [1-] ([1/]1+n).
intro; apply Uinv_eq_perm_right; auto.
Save.

Lemma Nmult_Sn_Unth: forall n:nat, S n */ [1/]1+n == 1.
intro; rewrite (Nmult_S n ([1/]1+n)).
rewrite (Nmult_n_Unth n); auto.
Save.

Hint Resolve Nmult_n_Unth Nmult_Sn_Unth.

Lemma Nmult_ge_Sn_Unth: forall n k, (S n <= k)%nat -> k */ [1/]1+n == 1.
induction 1; auto.
rewrite (Nmult_S m ([1/]1+n)); rewrite IHle; auto.
Save.

Lemma Nmult_n_Unthp : forall n : nat, (0 < n)%nat -> n */ [1/]n == 1.
Proof.
  intros.
  destruct H; auto.
Qed.
Hint Resolve Nmult_n_Unthp.

Lemma Unthp_S : forall n, [1/](S n) == [1/]1+n.
Proof.
  trivial.
Qed.

Lemma Nmult_le_n_Unth: forall n k, (k <= n)%nat -> k */ [1/]1+n <= [1-] ([1/]1+n).
intros; transitivity (n */ [1/]1+n); auto.
Save.

Hint Resolve Nmult_ge_Sn_Unth Nmult_le_n_Unth.

Lemma Nmult_def_inv : forall n x, Nmult_def (S n) x -> n */ x <= [1-] x.
intros; transitivity (n */ [1/]1+n); auto.
rewrite Nmult_n_Unth; auto.
Save.
Hint Resolve Nmult_def_inv.

Lemma Nmult_Umult_assoc_left : forall n x y, Nmult_def n x -> n */ (x*y) == (n */ x) *y.
intros n x y; induction n; auto; intros.
destruct n; auto.
repeat rewrite Nmult_SS.
assert(Nmult_def (S n) x); auto.
setoid_rewrite (IHn H0).
assert (x <= [1-] ((S n) */ x)).
apply Uinv_le_perm_right.
transitivity ([1-] ([1/]1+(S n))); auto.
transitivity ((S n) */ ([1/]1+(S n))); auto.
apply Oeq_sym; auto.
Save.

Hint Resolve Nmult_Umult_assoc_left.

Lemma Nmult_Umult_assoc_right : forall n x y, Nmult_def n y -> n */ (x*y) == x * (n */ y).
intros; rewrite (Umult_sym x y); rewrite (Nmult_Umult_assoc_left n y x H); auto.
Save.

Hint Resolve Nmult_Umult_assoc_right.

Lemma plus_Nmult_distr : forall n m x, (n + m) */ x== (n */ x) + (m */ x).
intros n m x; induction n; auto; intros.
rewrite plus_Sn_m.
rewrite (Nmult_S (n + m) x).
setoid_rewrite IHn.
rewrite (Nmult_S n x); auto.
Save.

Lemma Nmult_Uplus_distr : forall n x y, n */ (x + y) == (n */ x) + (n */ y).
intros n x y; induction n.
simpl; auto.
rewrite (Nmult_S n (x+y)).
rewrite IHn.
norm_assoc_right.
rewrite (Uplus_perm2 y (n */ x) (n */ y)).
rewrite <- (Nmult_S n y).
norm_assoc_left.
apply Uplus_eq_compat; auto.
Save.

Lemma Nmult_mult_assoc : forall n m x, (n * m) */ x == n */ (m */ x).
intros n m x; induction n; intros; auto.
simpl mult.
rewrite (plus_Nmult_distr m (n * m) x).
rewrite IHn; auto.
Save.

Lemma Nmult_Unth_simpl_left : forall n x, (S n) */ ([1/]1+n * x) == x.
intros.
rewrite (Nmult_Umult_assoc_left (S n) ([1/]1+n) x (Nmult_def_Unth n)).
rewrite (Nmult_Sn_Unth n); auto.
Save.

Lemma Nmult_Unth_simpl_right : forall n x, (S n) */ (x * [1/]1+n) == x.
intros.
rewrite (Nmult_Umult_assoc_right (S n) x ([1/]1+n) (Nmult_def_Unth n)).
rewrite (Nmult_Sn_Unth n); auto.
Save.

Hint Resolve Nmult_Umult_assoc_right plus_Nmult_distr Nmult_Uplus_distr
Nmult_mult_assoc Nmult_Unth_simpl_left Nmult_Unth_simpl_right.

Lemma Uinv_Nmult : forall k n, [1-] (k */ [1/]1+n) == ((S n) - k)  */ [1/]1+n.
intros k n; case (le_lt_dec (S n) k); intro.
rewrite (Nmult_ge_Sn_Unth l).
replace (S n - k)%nat with O; auto.
omega.
induction k; intros.
rewrite Nmult_0; rewrite Uinv_zero.
replace (S n - O)%nat with (S n); auto with arith.
rewrite (Nmult_S k ([1/]1+n)).
apply Uplus_eq_simpl_right with ([1/]1+n); auto.
apply Uinv_le_perm_right.
apply Nmult_le_n_Unth.
omega.
transitivity (((S n - S k) + (S O)) */ [1/]1+n).
replace ((S n - S k) + (S O))%nat with (S n - k)%nat.
transitivity ([1-] (k */ [1/]1+n)); auto with arith.
omega.
rewrite (plus_Nmult_distr (S n - S k) (S O) ([1/]1+n)); auto.
Save.

Lemma Nmult_neq_zero : forall n x, ~0==x -> ~0==S n */ x.
intros; rewrite (Nmult_S n x); auto.
apply Uplus_neq_zero_left; trivial.
Save.
Hint Resolve Nmult_neq_zero.


Lemma Nmult_le_simpl :  forall (n:nat) (x y:U),
   Nmult_def (S n) x -> Nmult_def (S n) y -> (S n */ x) <= (S n */ y) -> x <= y.
intros; apply Umult_le_simpl_left with (S n */ [1/]1+n).
auto.
assert (Nmult_def (S n) ([1/]1+n)); auto.
rewrite <- (Nmult_Umult_assoc_left (S n) ([1/]1+n) x H2).
rewrite <- (Nmult_Umult_assoc_left (S n) ([1/]1+n) y H2).
rewrite (Nmult_Umult_assoc_right (S n) ([1/]1+n) y H0).
rewrite (Nmult_Umult_assoc_right (S n) ([1/]1+n) x H).
transitivity ([1/]1+n * (S n */ x)); auto.
Save.

Lemma Nmult_Unth_le : forall (n1 n2 m1 m2:nat),
   (n2 * S n1<= m2 * S m1)%nat -> n2 */ [1/]1+m1 <= m2 */ [1/]1+n1.
intros.
transitivity ((n2 * S n1) */ ([1/]1+m1 * [1/]1+n1)).
rewrite (Nmult_mult_assoc n2 (S n1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_le_compat_right.
rewrite (Nmult_Unth_simpl_right n1 ([1/]1+m1)); auto.
transitivity ((m2 * S m1) */ [1/]1+m1 * [1/]1+n1); auto.
rewrite (Nmult_mult_assoc m2 (S m1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_le_compat_right.
rewrite (Nmult_Unth_simpl_left m1 ([1/]1+n1)); auto.
Save.

Lemma Nmult_Unth_eq :
   forall (n1 n2 m1 m2:nat),
   (n2 * S n1= m2 * S m1)%nat -> n2 */ [1/]1+m1 == m2 */ [1/]1+n1.
intros.
transitivity ((n2 * S n1) */ ([1/]1+m1 * [1/]1+n1)).
rewrite (Nmult_mult_assoc n2 (S n1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_eq_compat_left.
rewrite (Nmult_Unth_simpl_right n1 ([1/]1+m1)); auto.
rewrite H.
rewrite (Nmult_mult_assoc m2 (S m1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_eq_compat_left.
rewrite (Nmult_Unth_simpl_left m1 ([1/]1+n1)); auto.
Save.

Hint Resolve Nmult_Unth_le Nmult_Unth_eq.

Lemma Nmult_Unth_factor :
   forall (n m1 m2:nat),
   (n * S m2= S m1)%nat -> n */ [1/]1+m1 == [1/]1+m2.
intros; transitivity (1 */ [1/]1+m2); trivial.
apply Nmult_Unth_eq; omega.
Save.
Hint Resolve Nmult_Unth_factor.

Lemma Unth_eq : forall n p, n */ p == [1-]p -> p == [1/]1+n.
intros; apply Ole_antisym; apply (Ule_total p ([1/]1+n)); intros; auto.
apply Uinv_le_simpl.
transitivity (n*/[1/]1+n); auto.
transitivity (n*/p); auto.
apply Uinv_le_simpl.
transitivity (n*/p); auto.
transitivity (n*/[1/]1+n); auto.
Save.

Lemma mult_Nmult_Umult : forall n m x y,
  Nmult_def n x -> Nmult_def m y -> (n*m)%nat */ (x*y) == (n*/x)*(m*/y).
Proof.
  intros n m x y Hnx Hmy. 
  rewrite Nmult_mult_assoc.
  rewrite Nmult_Umult_assoc_right; auto.
Qed.

Hint Resolve mult_Nmult_Umult.

Lemma minus_Nmult_distr : forall n m x, 
     Nmult_def n x ->  (n - m) */ x== (n */ x) - (m */ x).
intros n m x; induction n; auto; intros.
assert (m <= n \/ (S n) <= m)%nat; try omega.
destruct H0 as [H1|H1].
rewrite <- minus_Sn_m; trivial.
repeat rewrite Nmult_S.
rewrite IHn; auto.
replace (S n - m)%nat with O by omega.
rewrite Nmult_0.
symmetry; apply Uminus_le_zero; auto.
Save.

Lemma Nmult_Uminus_distr : forall n x y,  
       Nmult_def n x -> n */ (x - y) == (n */ x) - (n */ y).
intros; apply (Ule_total x y); intros; auto.
rewrite Uminus_le_zero; auto.
rewrite Uminus_le_zero; auto.
induction n; auto.
repeat rewrite Nmult_S.
rewrite IHn; auto.
assert (n */ y <= n */ x); auto.
rewrite <- Uminus_assoc_left; auto.
rewrite <- (Uminus_plus_perm  x); auto.
apply Uplus_minus_assoc_right; auto.
transitivity ([1-]x); auto.
Save.
Hint Resolve minus_Nmult_distr Nmult_Uminus_distr.

Lemma Umult_Unth : forall n m, [1/]1+n * [1/]1+m == [1/]1+(n+m+n*m).
  intros.
  apply Unth_eq.
  repeat rewrite plus_Nmult_distr.
  rewrite mult_Nmult_Umult by auto.
  rewrite Nmult_Umult_assoc_left by auto.
  rewrite (Nmult_Umult_assoc_right m) by auto.
  rewrite <- Uplus_assoc.
  rewrite <- Udistr_plus_right by auto.
  rewrite (Nmult_n_Unth n) at 1.
  rewrite Udistr_inv_right.
  apply Uplus_eq_compat; auto.
  rewrite (Nmult_n_Unth m); auto.
Save.
Hint Resolve Umult_Unth.

Lemma Umult_Unthp : forall n m,
  (0 < n)%nat -> (0 < m)%nat -> [1/]n * [1/]m == [1/](n*m)%nat.
Proof.
  intros.
  rewrite Umult_Unth.
  apply Unth_eq_compat.
  destruct n, m; try omega.
  simpl.
  rewrite <- mult_n_Sm.
  omega.
Qed.
Hint Resolve Umult_Unthp.

Lemma Unthp_le_compat : forall n m, (n <= m)%nat -> [1/]m <= [1/]n.
Proof.
  intros; apply Unth_le_compat.
  apply le_pred.
  trivial.
Qed.
Hint Resolve Unthp_le_compat.

Lemma Unthp_le_equiv : forall n m, (0 < n)%nat -> (0 < m)%nat -> ([1/]n <= [1/]m <-> m <= n).
Proof.
  intros.
  rewrite Unth_le_equiv.
  destruct n, m; simpl; omega.
Qed.

Lemma Unth_eqp_equiv : forall n m, (0 < n)%nat -> (0 < m)%nat -> ([1/]n == [1/]m <-> m = n).
Proof.
  intros.
  rewrite Unth_eq_equiv.
  destruct n, m; simpl; omega.
Qed.

Lemma half_Unth_eq : forall n, [1/2] * [1/]1+n == [1/]1+(2*n+1).
intros.
rewrite Umult_Unth.
apply Unth_eq_compat; simpl; omega.
Save.

Lemma twice_half : forall p, [1/]1+(2 * p + 1) + [1/]1+(2 * p + 1) == [1/]1+p.
intros; transitivity (2 */  [1/]1+(2 * p + 1)); auto.
apply Nmult_Unth_factor; simpl; omega.
Save.


Lemma Nmult_def_lt : forall n x, n */ x < 1 -> Nmult_def n x.
red; destruct n; intros; auto.
apply (Ule_total x ([1/]1+n)); intros; auto.
case (Olt_notle _ _ H).
transitivity (S n */ [1/]1+n); auto.
Save.
Hint Immediate Nmult_def_lt.

Lemma Nmult_lt_simpl : forall n x y, n */ x < n */ y -> x < y.
intros n x y H; apply notUle_lt; intro.
assert (n */ y <= n */ x); auto.
apply Ole_not_lt with (1:=H1); auto.
Save.

Lemma Nmult_lt_compat : 
   forall n x y, (0 < n)%nat -> n */ x < 1 -> x < y -> n */ x < n */ y.
induction 1; intros; auto.
repeat rewrite Nmult_S.
assert (m */x < 1).
apply Ole_lt_trans with (S m */ x); auto.
assert (m*/x < [1-]x).
apply Uplus_lt_Uinv_lt; auto.
apply Ole_lt_trans with (S m */ x); auto.
rewrite Nmult_S; auto.
apply Uplus_lt_compat_lt; auto.
Save.
Hint Resolve Nmult_lt_compat.

Lemma Nmult_def_lt_compat : 
   forall n x y, (0 < n)%nat -> Nmult_def n y -> x < y -> n */ x < n */ y.
induction 1; intros; auto.
repeat rewrite Nmult_S.
assert (Nmult_def m y); auto.
assert (m*/y <= [1-]y); auto.
apply Uplus_lt_compat; auto.
Save.
Hint Resolve Nmult_def_lt_compat.

(** ** efficient product with binary integers in N *)

Require Export NArith.

(** Defining Nmult on binary numbers *)

Definition nmult (n:N) (x:U) : U := 
  N.binary_rect (fun _ => U) 
    0 (fun k r => (r + r)%U) (fun k r => (x + (r + r))%U) 
  n.


Infix "*\" := nmult (at level 60) : U_scope.
(* Open Local Scope N_scope.*)

Lemma nmult_0 : forall (x:U), ((0%N) *\ x) = 0%U.
trivial.
Save.

Lemma nmult_1 : forall (x:U), (1%N) *\ x == x.
simpl; intros.
rewrite Uplus_zero_left; trivial.
Save.

Hint Resolve nmult_0 nmult_1.

Lemma nmult_double : 
  forall n (x:U), (N.double n) *\ x == ((n *\ x) + (n *\ x))%U.
intros; destruct n; auto.
Save.

Lemma nmult_succ_double : 
  forall n (x:U), (N.succ_double n) *\ x == (x + ((n *\ x) + (n *\ x)))%U.
intros; destruct n; auto.
Save.

Lemma nmult_Nmult : forall (n:N) (x:U), (n *\ x == N.to_nat n */ x).
intros; pattern n; apply N.binary_ind; intros; simpl; auto.
rewrite N2Nat.inj_double.
rewrite nmult_double.
rewrite H; simpl.
rewrite plus_Nmult_distr.
apply Uplus_eq_compat_right.
rewrite <- plus_n_O; trivial.
rewrite nmult_succ_double.
rewrite N2Nat.inj_succ_double.
rewrite Nmult_S.
rewrite H; simpl.
apply Uplus_eq_compat_right.
rewrite plus_Nmult_distr; auto.
Save.

Lemma Nmult_nmult : forall (n:nat) (x:U), (N.of_nat n *\ x == n */ x).
intros; transitivity (N.to_nat (N.of_nat n) */ x).
apply nmult_Nmult.
rewrite Nat2N.id.
trivial.
Save.

Lemma nmult_zero : forall n, n *\ 0 == 0.
intros; rewrite nmult_Nmult; auto.
Save.

Add Morphism nmult with signature eq ==> Oeq ==> Oeq as nmult_eq_compat.
intros n x1 x2 eq1; rewrite nmult_Nmult; rewrite nmult_Nmult; auto.
Save.

Hint Immediate nmult_eq_compat.



Lemma nmult_S : 
  forall (n:N) (x:U), (N.succ n) *\ x == x + (n *\ x).
intros; repeat rewrite nmult_Nmult; auto.
rewrite N2Nat.inj_succ; auto.
Save.

Lemma nmult_2 : forall (x:U), 2 *\ x == x + x.
intros; rewrite nmult_Nmult; auto.
Save.

Hint Resolve nmult_0 nmult_zero nmult_1 nmult_2 nmult_S.

Lemma nmult_eq_compat_left : forall (n:N) (x y:U), x == y -> n *\ x == n *\ y.
auto.
Save.

Lemma nmult_eq_compat_right : forall (n m:N) (x:U), (n = m)%nat -> n *\ x == m *\ x.
auto.
Save.
Hint Resolve nmult_eq_compat_right.

Lemma nmult_le_compat_right :  forall n x y, x <= y -> n *\ x <= n *\ y.
intros; repeat rewrite nmult_Nmult; auto.
Save.

Lemma nmult_le_compat_left : forall n m x, (n <= m)%N -> n *\ x <= m *\ x.
intros; repeat rewrite nmult_Nmult; apply Nmult_le_compat_left; auto.
Save.

Hint Resolve nmult_eq_compat_right nmult_le_compat_right nmult_le_compat_left.

Lemma nmult_le_compat : forall (n m:N) x y, (n <= m)%N -> x <= y -> n *\ x <= m *\ y.
intros; transitivity (n *\y); auto.
Save.
Hint Immediate nmult_le_compat.

Instance No : ord N  := 
     { Oeq := fun n m : N => n = m;
       Ole := fun n m : N => (n <= m)%N}.
abstract (
apply Build_Order; intros ; [
red; reflexivity |
split ; [destruct 1; intros; apply N.le_antisymm; auto|
         split; subst; reflexivity] |
red; intros x y z; transitivity y; auto
]).
Defined.


Instance nmult_mon2 : monotonic2 nmult.
red; intros; apply nmult_le_compat; auto.
Save.

Definition Nnmult : N -m> U -m> U := mon2 nmult.


Lemma nmult_sigma : forall (n:N) (x:U), n *\ x == sigma (fun k => x) (N.to_nat n).
intros n x; rewrite nmult_Nmult; auto.
Save.

Hint Resolve nmult_sigma.

Definition Nnth (n:N) : U := [1/]1+N.to_nat n.
Notation "[1|]1+ n" := (Nnth n) (at level 35, right associativity) : U_scope.
Notation "[1|2]" := (Nnth 1) (at level 35, right associativity) : U_scope.
Notation "[1|] n" := (Nnth (N.pred n)) (at level 35, right associativity) : U_scope.

Lemma Nnthp_simpl : forall n, [1|]n == [1/](N.to_nat n).
intros; unfold Nnth.
rewrite N2Nat.inj_pred; auto.
Save.
Hint Resolve Nnthp_simpl.

Lemma Nnth_not_null : forall n, ~ 0 == [1|]1+ n.
unfold Nnth; auto.
Save.
Hint Resolve Nnth_not_null.

Lemma nmult_Nnth_prop : 
   forall n:N, [1|]1+n == [1-] (n *\ ([1|]1+n)).
intro.
rewrite (nmult_sigma n ([1|]1+n)).
exact (Unth_prop (N.to_nat n)).
Save.
Hint Resolve nmult_Nnth_prop.

Lemma nmult_n_Nnth: forall n:N, n *\ [1|]1+n == [1-] ([1|]1+n).
intro; apply Uinv_eq_perm_right; auto.
Save.

Lemma nmult_Sn_Nnth: forall n:N, N.succ n *\ [1|]1+n == 1.
intro; rewrite (nmult_S n ([1|]1+n)).
rewrite (nmult_n_Nnth n); auto.
Save.

Hint Resolve nmult_n_Nnth nmult_Sn_Nnth.

Lemma nmult_ge_Sn_Nnth: forall n k, (N.succ n <= k) -> k *\ [1|]1+n == 1.
intros; apply Uge_one_eq.
transitivity (N.succ n *\ [1|]1+n); auto.
Save.

Lemma nmult_n_Nnthp : forall n : N, (0 < n)%N -> n *\ [1|]n == 1.
Proof.
  intros.
  transitivity (N.succ (N.pred n) *\ [1|]n); auto.
  rewrite N.lt_succ_pred with (z:=0%N); auto.
Qed.
Hint Resolve nmult_n_Nnthp.

Lemma Nnth_succ : forall n, [1|](N.succ n) == [1|]1+n.
Proof.
  intros; rewrite N.pred_succ; trivial.
Qed.

Lemma nmult_le_n_Nnth: forall n k, (k <= n)%N -> k *\ [1|]1+n <= [1-] ([1|]1+n).
intros; transitivity (n *\ [1|]1+n); auto.
Save.

Hint Resolve nmult_ge_Sn_Nnth nmult_le_n_Nnth.

Definition nmult_def n x := Nmult_def (N.to_nat n) x.

Lemma nmult_defS : forall n x, nmult_def (N.succ n) x -> x <= [1|]1+n.
unfold nmult_def; intros n x; rewrite N2Nat.inj_succ; auto.
Save.
Hint Immediate nmult_defS.

Lemma nmult_def_inv : forall n x, nmult_def (N.succ n) x -> n *\ x <= [1-] x.
intros; transitivity (n *\ [1|]1+n); auto.
rewrite nmult_n_Nnth; auto.
Save.
Hint Resolve nmult_def_inv.

Lemma nmult_def_pred: forall (n : N) (x : U), nmult_def (N.succ n) x -> nmult_def n x.
unfold nmult_def; intros; apply Nmult_def_pred; auto.
rewrite <- N2Nat.inj_succ; auto.
Save.
Hint Immediate nmult_def_pred.

Lemma nmult_def_intro : forall n x, x <= [1|]1+n -> nmult_def (N.succ n) x.
unfold Nnth, nmult_def; intros.
rewrite N2Nat.inj_succ; auto.
Save.
Hint Resolve nmult_def_intro.


Lemma nmult_def_Nnth_le : forall n m, (n <= N.succ m)%N -> nmult_def n ([1|]1+m).
unfold Nnth, nmult_def; intros.
apply Nmult_def_Unth_le.
rewrite <- N2Nat.inj_succ; auto.
Save.
Hint Resolve nmult_def_Nnth_le.

Lemma nmult_def_le : forall n m x, (n <= N.succ m)%N -> x <= [1|]1+m -> nmult_def n x.
unfold Nnth, nmult_def; intros.
apply Nmult_def_le with (N.to_nat m); auto.
rewrite <- N2Nat.inj_succ; auto.
Save.
Hint Resolve nmult_def_le.

Lemma nmult_def_Nnth: forall n , nmult_def (N.succ n) ([1|]1+n).
auto.
Save.
Hint Resolve nmult_def_Nnth.

Lemma nmult_def_Nnthp : forall n, nmult_def n ([1|]n).
Proof.
  intros; apply nmult_def_le with (N.pred n); auto.
  rewrite <- N.le_pred_le_succ; auto.
  reflexivity.
Qed.
Hint Resolve nmult_def_Nnthp.

Lemma nmult_def_introp : forall n x, x <= [1|]n -> nmult_def n x.
intros; apply nmult_def_le with (N.pred n); auto.
rewrite <- N.le_pred_le_succ; auto.
reflexivity.
Save.
Hint Resolve nmult_def_introp.

Lemma nmult_def_elimp : forall n x, nmult_def n x -> x <= [1|]n.
unfold Nnth, nmult_def; intros.
rewrite N2Nat.inj_pred.
destruct (N.to_nat n); auto.
Save.
Hint Immediate nmult_def_elimp.


Lemma nmult_Umult_assoc_left : forall n x y, nmult_def n x -> n *\ (x*y) == (n *\ x) * y.
intros; repeat rewrite nmult_Nmult; auto.
Save.

Hint Resolve nmult_Umult_assoc_left.

Lemma nmult_Umult_assoc_right : forall n x y, nmult_def n y -> n *\ (x*y) == x * (n *\ y).
intros; repeat rewrite nmult_Nmult; auto.
Save.

Hint Resolve nmult_Umult_assoc_right.

Lemma plus_nmult_distr : forall n m x, (n + m) *\ x== (n *\ x) + (m *\ x).
intros; repeat rewrite nmult_Nmult.
rewrite N2Nat.inj_add; auto.
Save.

Lemma nmult_Uplus_distr : forall n x y, n *\ (x + y) == (n *\ x) + (n *\ y).
intros; repeat rewrite nmult_Nmult; auto.
Save.

Lemma nmult_mult_assoc : forall n m x, (n * m) *\ x == n *\ (m *\ x).
intros; repeat rewrite nmult_Nmult.
rewrite N2Nat.inj_mul; auto.
Save.

Lemma nmult_Unth_simpl_left : forall n x, (N.succ n) *\ ([1|]1+n * x) == x.
intros; repeat rewrite nmult_Nmult.
rewrite N2Nat.inj_succ; auto.
apply Nmult_Unth_simpl_left.
Save.

Lemma nmult_Unth_simpl_right : forall n x, (N.succ n) *\ (x * [1|]1+n) == x.
intros; repeat rewrite nmult_Nmult.
rewrite N2Nat.inj_succ; auto.
apply Nmult_Unth_simpl_right.
Save.

Hint Resolve nmult_Umult_assoc_right plus_nmult_distr nmult_Uplus_distr
nmult_mult_assoc nmult_Unth_simpl_left nmult_Unth_simpl_right.

Lemma Uinv_nmult : forall k n, [1-] (k *\ [1|]1+n) == ((N.succ n) - k)  *\ [1|]1+n.
intros; repeat rewrite nmult_Nmult.
rewrite N2Nat.inj_sub, N2Nat.inj_succ.
apply Uinv_Nmult.
Save.

Lemma nmult_neq_zero : forall n x, ~ 0 == x -> ~ 0 == N.succ n *\ x.
intros; repeat rewrite nmult_Nmult; rewrite N2Nat.inj_succ; auto.
Save.
Hint Resolve nmult_neq_zero.


Lemma nmult_le_simpl :  forall (n:N) (x y:U),
   nmult_def (N.succ n) x -> nmult_def (N.succ n) y 
 -> (N.succ n *\ x) <= (N.succ n *\ y) -> x <= y.
intros n x y; unfold nmult_def; repeat rewrite nmult_Nmult.
repeat rewrite N2Nat.inj_succ; auto.
intros; apply Nmult_le_simpl with (N.to_nat n); auto.
Save.

Lemma nmult_Nnth_le : forall (n1 n2 m1 m2:N),
   (n2 * N.succ n1 <= m2 * N.succ m1)%N -> n2 *\ [1|]1+m1 <= m2 *\ [1|]1+n1.
intros n1 n2 m1 m2; repeat rewrite nmult_Nmult.
repeat rewrite N2Nat.inj_succ.
intros; apply Nmult_Unth_le; auto.
cut (N.to_nat (n2 * N.succ n1) <= N.to_nat (m2 * N.succ m1)); auto.
repeat rewrite N2Nat.inj_mul; repeat rewrite N2Nat.inj_succ; auto.
Save.
Hint Resolve nmult_Nnth_le.

Lemma nmult_Nnth_eq :
   forall (n1 n2 m1 m2:N),
   (n2 * N.succ n1 = m2 * N.succ m1)%N -> n2 *\ [1|]1+m1 == m2 *\ [1|]1+n1.
intros; apply Ole_antisym; apply nmult_Nnth_le; rewrite H; reflexivity.
Save.

Hint Resolve nmult_Nnth_le nmult_Nnth_eq.

Lemma nmult_Nnth_factor :
   forall (n m1 m2:N),
   (n * N.succ m2 = N.succ m1)%N -> n *\ [1|]1+m1 == [1|]1+m2.
intros; transitivity (1 *\ [1|]1+m2); trivial.
apply nmult_Nnth_eq.
rewrite H; ring.
Save.
Hint Resolve nmult_Nnth_factor.

Lemma Nnth_eq : forall n p, n *\ p == [1-]p -> p == [1|]1+n.
intros n p; repeat rewrite nmult_Nmult; unfold Nnth.
intro; apply Unth_eq; auto.
Save.

Lemma mult_nmult_Umult : forall n m x y,
  nmult_def n x -> nmult_def m y -> (n*m)%N *\ (x*y) == (n*\x)*(m*\y).
Proof.
  intros n m x y Hnx Hmy. 
  rewrite nmult_mult_assoc.
  rewrite nmult_Umult_assoc_right; auto.
Qed.

Hint Resolve mult_nmult_Umult.

Lemma minus_nmult_distr : forall n m x, 
     nmult_def n x ->  (n - m) *\ x== (n *\ x) - (m *\ x).
intros n m x; unfold nmult_def; repeat rewrite nmult_Nmult.
rewrite N2Nat.inj_sub; auto.
Save.

Lemma nmult_Uminus_distr : forall n x y,  
       nmult_def n x -> n *\ (x - y) == (n *\ x) - (n *\ y).
intros n m x; unfold nmult_def; repeat rewrite nmult_Nmult; auto.
Save.

Hint Resolve minus_nmult_distr nmult_Uminus_distr.

Lemma Umult_Nnth : forall n m, [1|]1+n * [1|]1+m == [1|]1+(n+m+n*m).
intros n m; unfold Nnth; rewrite Umult_Unth.
repeat rewrite N2Nat.inj_add; repeat rewrite N2Nat.inj_mul; auto.
Save.
Hint Resolve Umult_Unth.


Lemma Umult_Nnthp : forall n m,
  (0 < n)%N -> (0 < m)%N -> [1|]n * [1|]m == [1|](n*m)%N.
Proof.
  intros; repeat rewrite Nnthp_simpl.
  rewrite Umult_Unthp; auto.
  rewrite N2Nat.inj_mul; auto.
Qed.
Hint Resolve Umult_Nnth.

Lemma Nnth_le_compat : forall n m, (n <= m)%N -> [1|]1+m <= [1|]1+n.
Proof.
  intros; unfold Nnth; apply Unth_le_compat; auto.
Qed.
Hint Resolve Nnth_le_compat.

Lemma Nnth_eq_compat : forall n m, n = m -> [1|]1+m == [1|]1+n.
Proof.
  intros; subst; auto.
Qed.
Hint Resolve Nnth_eq_compat.

Lemma Nnthp_le_compat : forall n m, (n <= m)%N -> [1|]m <= [1|]n.
Proof.
  intros; apply Nnth_le_compat.
  apply N.pred_le_mono; auto.
Qed.
Hint Resolve Nnth_le_compat Nnthp_le_compat.

Lemma Nnthp_le_equiv 
   : forall n m, (0 < n)%N -> (0 < m)%N -> ([1|]n <= [1|]m <-> (m <= n)%N).
Proof.
  split; auto.
  unfold Nnth; rewrite Unth_le_equiv.
  rewrite nat_compare_le.
  rewrite <- N2Nat.inj_compare.
  intros; rewrite <- (N.lt_succ_pred 0 m); trivial.
  intros; rewrite <- (N.lt_succ_pred 0 n); auto.
  rewrite <- N.succ_le_mono; auto.
Qed.

Lemma Nnth_eq_equiv 
   : forall n m, (0 < n)%N -> (0 < m)%N -> ([1|]n == [1|]m <-> m = n).
Proof.
  split; auto.
  unfold Nnth; rewrite Unth_eq_equiv.
  repeat rewrite N2Nat.inj_pred.
  intros; assert (N.to_nat n = N.to_nat m); auto.
  apply NPeano.Nat.pred_inj; auto.
  assert (0 < N.to_nat n)%nat; auto; try omega.
  assert (0 < N.to_nat m)%nat; auto; try omega.
  apply N2Nat.inj; auto.
  intro; subst; auto.
Qed.

Lemma nmult_def_le_compat_left 
  : forall n m x, (n<=m)%N -> nmult_def m x -> nmult_def n x.
intros; apply nmult_def_introp.
transitivity ([1|]m); auto.
Save.

Lemma nmult_def_le_compat_right 
  : forall n x y, (y <= x) -> nmult_def n x -> nmult_def n y.
intros; apply nmult_def_introp.
transitivity x; auto.
Save.

Lemma half_Nnth_eq : forall n, [1|2] * [1|]1+n == [1|]1+(2*n+1).
intros.
rewrite Umult_Nnth.
apply Nnth_eq_compat.
ring.
Save.

Lemma Nnth_twice_half 
  : forall p, [1|]1+(2 * p + 1) + [1|]1+(2 * p + 1) == [1|]1+p.
intros; transitivity (2 *\  [1|]1+(2 * p + 1)); auto.
apply nmult_Nnth_factor.
repeat rewrite <- N.add_1_l; ring.
Save.


Lemma nmult_def_lt : forall n x, n *\ x < 1 -> nmult_def n x.
intros n x; rewrite nmult_Nmult; unfold nmult_def; auto.
Save.
Hint Immediate nmult_def_lt.

Lemma nmult_lt_simpl : forall n x y, n *\ x < n *\ y -> x < y.
intros n x y; repeat rewrite nmult_Nmult.
apply Nmult_lt_simpl with (n:=N.to_nat n); trivial.
Save.

Lemma nmult_lt_compat : 
   forall n x y, (0 < n)%N -> n *\ x < 1 -> x < y -> n *\ x < n *\ y.
intros n x y; repeat rewrite nmult_Nmult.
intros; apply Nmult_lt_compat; auto.
Save.

Lemma nmult_def_lt_compat : 
   forall n x y, (0 < n)%N -> nmult_def n y -> x < y -> n *\ x < n *\ y.
intros n x y; repeat rewrite nmult_Nmult.
intros; apply Nmult_def_lt_compat; auto.
Save.
Hint Resolve nmult_def_lt_compat.


Lemma Udiv_Nnth : forall n x, (0<n)%N -> nmult_def n x 
      -> x / [1|]n == n *\ x.
intros; symmetry; apply Umult_div_eq; auto.
rewrite <- nmult_Umult_assoc_left; auto.
rewrite Umult_sym.
rewrite -> nmult_Umult_assoc_left; auto.
Save.
Hint Resolve Udiv_Nnth.

Lemma Udiv_nmult : forall n x y, (0<n)%N -> ~ 0 == y
      -> nmult_def n y
      -> x / (n *\ y) == (x * [1|]n) / y.
intros; assert (Heq:N.succ (N.pred n)=n); auto.
assert (~ 0 == n *\ y); auto.
rewrite <- Heq; auto.
apply (Ule_total (n *\ y) x); auto; intros.
(* degenerate case ny <= x, both sides are 1 *)
rewrite Udiv_le_one; auto.
rewrite Udiv_le_one; auto.
transitivity ((n *\ y) * [1|]n); auto.
rewrite <- nmult_Umult_assoc_left; auto.
rewrite nmult_Umult_assoc_right; auto.
rewrite nmult_n_Nnthp; auto.
(* normal case x <= ny *)
symmetry; apply Umult_div_eq; auto.
rewrite Umult_sym.
rewrite <- nmult_Umult_assoc_left; auto.
rewrite Umult_div; auto.
rewrite nmult_Umult_assoc_right; auto.
transitivity ((n *\ y) * [1|]n); auto.
rewrite <- nmult_Umult_assoc_left; auto.
rewrite nmult_Umult_assoc_right; auto.
Save.
Hint Resolve Udiv_nmult.

(** ** Conversion from booleans to U *)

Definition B2U :MF bool := fun (b:bool) => if b then 1 else 0.

Definition NB2U :MF bool := fun (b:bool) => if b then 0 else 1.

Lemma B2Uinv : NB2U == finv B2U.
unfold NB2U,finv,B2U; intro b; case b; auto.
Save.

Lemma NB2Uinv : B2U == finv NB2U.
unfold NB2U,finv,B2U; intro b; case b; auto.
Save.

Hint Resolve B2Uinv NB2Uinv.

Lemma Umult_B2U_andb : forall x y, (B2U x) * (B2U y) == B2U (andb x y).
Proof.
  intros; unfold B2U; simpl.
  destruct x; destruct y; simpl; auto.
Qed.

Lemma Uplus_B2U_orb : forall x y, (B2U x) + (B2U y) == B2U (orb x y).
Proof.
  intros; unfold B2U; simpl.
  destruct x; destruct y; simpl; auto.
Qed.

(*
(** ** Trivial space of measurable function on A : A -> U *)

Definition MFT : Type -> MFS.
intro A; exists A (A->U) (fun (f:A->U) (x:A) => f x)
            (fun (f g:A->U) (x:A) => f x + g x)
            (fun (k:U) (f:A->U) (x:A) => k * f x)
            (fun (f:A->U) (x:A) => [1-] f x) (fun (x:A) => (0:U))
            (fun (f : nat -> A -> U) (x:A) => lub (fun n => f n x)); auto.
Defined.
*)


(** ** Particular sequences *)
  (**  [pmin p n = p - [1/2] ^ n] *)

Definition pmin (p:U) (n:nat) :=  p - ( [1/2] ^ n ).

Add Morphism pmin with signature Oeq ==> eq ==> Oeq as pmin_eq_compat.
unfold pmin; auto.
Save.

(** *** Properties of [pmin] *)
Lemma pmin_esp_S : forall p n, pmin (p & p) n == pmin p (S n) & pmin p (S n).
unfold pmin at 1; intros.
rewrite (half_exp n).
rewrite (Uesp_minus_distr p p ([1/2]^(S n)) ([1/2]^(S n))); auto.
Save.

Lemma pmin_esp_le : forall p n,  pmin p (S n) <= [1/2] * (pmin (p & p) n) + [1/2].
intros; setoid_rewrite (pmin_esp_S p n); auto.
Save.

Lemma pmin_plus_eq :  forall p n, p <= [1/2] -> pmin p (S n) == [1/2] * (pmin (p + p) n).
intros; unfold pmin at 2.
setoid_rewrite (Uminus_distr_right [1/2] (p + p) ([1/2]^n)).
setoid_rewrite (half_twice _ H); auto.
Save.

Lemma pmin_0 : forall p:U, pmin p O == 0.
unfold pmin; simpl; intros;  auto.
Save.

Lemma pmin_le : forall (p:U) (n:nat), p - ([1/]1+n) <= pmin p n.
unfold pmin; intros.
apply Uminus_le_compat_right.
induction n; simpl; intros; auto.
transitivity ([1/2] * ([1/]1+n)); auto.
Save.

Hint Resolve pmin_0 pmin_le.

Lemma pmin_le_compat : forall p (n m : nat), n <= m -> pmin p n <= pmin p m.
unfold pmin; intros.
apply Uminus_le_compat_right; auto.
Save.
Hint Resolve pmin_le_compat.

Instance pmin_mon : forall p, monotonic (pmin p).
red; auto.
Save.

Definition Pmin (p:U) :nat -m> U := mon (pmin p).

Lemma le_p_lim_pmin : forall p, p <= lub (Pmin p).
intro; apply Ule_lt_lim; intros.
assert (exc (fun n : nat => t <= p - [1/]1+n)).
apply Ult_le_nth_minus; trivial.
apply H0; auto; intros n H1.
transitivity (p - [1/]1+n); auto.
transitivity (pmin p n); auto.
apply (le_lub (Pmin p) n).
Save.

Lemma le_lim_pmin_p : forall p, lub (Pmin p) <= p.
intro; apply lub_le; simpl; unfold pmin; auto.
Save.
Hint Resolve le_p_lim_pmin le_lim_pmin_p.

Lemma eq_lim_pmin_p : forall p, lub (Pmin p) == p.
intros; apply Ole_antisym; auto.
Save.

Hint Resolve eq_lim_pmin_p.

(** Particular case where p = 1 *)

Definition U1min := Pmin 1.

Lemma eq_lim_U1min : lub U1min == 1.
unfold U1min; auto.
Save.

Lemma U1min_S : forall n, U1min (S n) == [1/2]*(U1min n) + [1/2].
intros; unfold U1min at 2,pmin.
rewrite (Uminus_distr_right [1/2] 1 ([1/2]^n)).
rewrite Umult_one_right.
rewrite Uminus_plus_perm; auto.
rewrite Unth_one_plus; auto.
Save.

Lemma U1min_0 : U1min O == 0.
unfold U1min; simpl; auto.
Save.

Hint Resolve eq_lim_U1min U1min_S U1min_0.

Lemma glb_half_exp : glb (UExp [1/2]) == 0.
unfold glb; apply Uinv_eq_perm_left.
transitivity (lub U1min).
apply lub_eq_compat; intro n; simpl; unfold U1min,pmin; auto.
rewrite eq_lim_U1min; auto.
Save.
Hint Resolve glb_half_exp.

Lemma Ule_lt_half_exp : forall x y, (forall p, x <= y + [1/2]^p) -> x <= y.
intros; transitivity (glb (UExp [1/2]) + y).
transitivity (glb (Imon (mshift UPlus  y) @ (UExp [1/2]))).
apply le_glb; intro p.
transitivity (y + [1/2] ^ p); simpl; auto.
rewrite glb_eq_plus_cte_right; auto.
rewrite glb_half_exp; auto.
Save.

Lemma half_exp_le_half : forall p, [1/2]^(S p) <= [1/2].
simpl; auto.
Save.
Hint Resolve half_exp_le_half.

Lemma twice_half_exp : forall p, [1/2]^(S p) + [1/2]^(S p) ==  [1/2]^p.
simpl; intros.
rewrite <- Udistr_plus_right; auto.
Save.
Hint Resolve twice_half_exp.

(** *** Dyadic numbers *)
Fixpoint exp2 (n:nat) : nat :=
   match n with O => (1%nat) | S p => (2 * (exp2 p))%nat end.

Lemma exp2_pos : forall n, (O < exp2 n)%nat.
induction n; simpl; auto with arith.
Save.
Hint Resolve exp2_pos.

Lemma S_pred_exp2 : forall n, S (pred (exp2 n))=exp2 n.
intro; rewrite S_pred with (exp2 n) O; trivial.
Save.
Hint Resolve S_pred_exp2.

Notation "k  /2^ p" := (k */ ([1/2])^p) (at level 35, no associativity).


Lemma Unth_half : forall n, (O<n)%nat -> [1/]1+(pred (n+n)) == [1/2] * [1/]1+pred n.
intros; apply Oeq_sym; apply Unth_eq.
destruct n; intros.
absurd (0<0)%nat; auto with arith.
simpl.
replace (n + S n)%nat with (2 * n + 1)%nat; auto with zarith.
rewrite plus_Nmult_distr.
rewrite Nmult_1.
rewrite Nmult_mult_assoc.
rewrite Nmult_Umult_assoc_right; auto.
rewrite Nmult_Umult_assoc_left; auto.
rewrite Nmult_Sn_Unth.
rewrite Umult_one_left.
rewrite Nmult_n_Unth.
rewrite Udistr_inv_right; auto.
Save.

Lemma Unth_exp2 : forall p, [1/2]^p == [1/]1+pred (exp2 p).
induction p; simpl; intros; auto.
rewrite <- plus_n_O.
rewrite Unth_half; auto.
Save.

Hint Resolve Unth_exp2.



Lemma Nmult_exp2 : forall p, (exp2 p)/2^p == 1.
intros; rewrite Unth_exp2.
replace (exp2 p) with (S (pred (exp2 p))); auto.
Save.
Hint Resolve Nmult_exp2.

Section Sequence.
Variable k : U.
Hypothesis kless1 : k < 1.

Lemma Ult_one_inv_zero : ~ 0 == [1-]k.
red; intro; apply kless1; auto.
transitivity ([1-]0); auto.
apply Uinv_eq_perm_right; auto.
Save.
Hint Resolve Ult_one_inv_zero.

Lemma Umult_simpl_zero : forall x, x <= k * x -> x == 0.
intros; apply Ule_zero_eq.
apply (bary_le_simpl_left k ([1-]k)); auto.
rewrite Umult_zero_right; rewrite Uplus_zero_right; auto.
Save.

Lemma Umult_simpl_one : forall x, k * x + [1-]k <= x -> x == 1.
intros; apply Uge_one_eq.
apply (bary_le_simpl_right ([1-]k) k); auto.
rewrite Umult_one_right; rewrite Uplus_sym; auto.
Save.

Lemma bary_le_compat : forall k' x y, x <= y -> k <= k' -> k' * x + [1-]k' * y <= k * x + [1-]k * y.
intros.
auto.
Save.

Lemma bary_one_le_compat : forall k' x, k <= k' -> k' * x + [1-]k' <= k * x + [1-]k.
intros.
transitivity (k * x + [1-]k * 1); auto.
transitivity (k' * x + [1-]k' * 1); auto.
Save.


Lemma glb_exp_0 : glb (UExp k) == 0.
apply Umult_simpl_zero.
transitivity (glb (mon (seq_lift_left (UExp k) (S 0)))).
rewrite (glb_lift_left (UExp k) 1); auto.
rewrite <- glb_eq_mult.
apply glb_le_compat; intro n; simpl; auto.
Save.

Instance Uinvexp_mon : monotonic (fun n => [1-]k ^ n).
red; intros n m H; auto.
Save.

Lemma lub_inv_exp_1 : mlub (fun n => [1-]k ^ n) == 1.
apply Uinv_eq_simpl.
transitivity (glb (UExp k)).
unfold glb; apply Uinv_eq_compat.
apply mlub_eq_compat; intro n; auto.
rewrite glb_exp_0; auto.
Save.


End Sequence.
Hint Resolve  glb_exp_0 lub_inv_exp_1 bary_one_le_compat bary_le_compat.
Existing Instance Uinvexp_mon.

(** ** Tactic for simplification of goals *)

Ltac Usimpl :=  match goal with
    |- context [(Uplus 0 ?x)]     => setoid_rewrite (Uplus_zero_left x)
 |  |- context [(Uplus ?x 0)]     => setoid_rewrite (Uplus_zero_right x)
 |  |- context [(Uplus 1 ?x)]     => setoid_rewrite (Uplus_one_left x)
 |  |- context [(Uplus ?x 1)]     => setoid_rewrite (Uplus_one_right x)
 |  |- context [(Umult 0 ?x)]     => setoid_rewrite (Umult_zero_left x)
 |  |- context [(Umult ?x 0)]     => setoid_rewrite (Umult_zero_right x)
 |  |- context [(Umult 1 ?x)]     => setoid_rewrite (Umult_one_left x)
 |  |- context [(Umult ?x 1)]     => setoid_rewrite (Umult_one_right x)
 |  |- context [(Uesp 0 ?x)]      => setoid_rewrite (Uesp_zero_left x)
 |  |- context [(Uesp ?x 0)]      => setoid_rewrite (Uesp_zero_right x)
 |  |- context [(Uesp 1 ?x)]      => setoid_rewrite (Uesp_one_left x)
 |  |- context [(Uesp ?x 1)]      => setoid_rewrite (Uesp_one_right x)
 |  |- context [(Uminus 0 ?x)]    => setoid_rewrite (Uminus_zero_left x)
 |  |- context [(Uminus ?x 0)]    => setoid_rewrite (Uminus_zero_right x)
 |  |- context [(Uminus ?x 1)]    => setoid_rewrite (Uminus_one_right x)
 |  |- context [(Uminus ?x ?x)]   => setoid_rewrite (Uminus_eq x)
 |  |- context [[1/2] + [1/2]]  => setoid_rewrite Unth_one_plus
 |  |- context [([1/2] * ?x + [1/2] * ?x)]  => setoid_rewrite (Unth_one_refl x)
 |  |- context [[1-][1/2]]        => setoid_rewrite <- Unth_one
 |  |- context [([1-] ([1-] ?x))] => setoid_rewrite (Uinv_inv x)
 |  |- context [ ?x + ([1-] ?x)]  => setoid_rewrite (Uinv_opp_right x)
 |  |- context [ ([1-]?x) + ?x ]  => setoid_rewrite (Uinv_opp_left x)
 |  |- context [([1-] 1)] => setoid_rewrite Uinv_one
 |  |- context [([1-] 0)] => setoid_rewrite Uinv_zero
 |  |- context [([1/]1+O)]        => setoid_rewrite Unth_zero
 |  |- context [(0/?x)]      => setoid_rewrite (Udiv_zero x)
 |  |- context [(?x/1)]      => setoid_rewrite (Udiv_one x)
 |  |- context [(?x/0)]      => setoid_rewrite (Udiv_by_zero x); [idtac|reflexivity]
 |  |- context [?x^O] => setoid_rewrite (Uexp_0 x)
 |  |- context [?x^(S O)] => setoid_rewrite (Uexp_1 x)
 |  |- context [0^(?n)] => setoid_rewrite Uexp_zero; [idtac|omega]
 |  |- context [U1^(?n)] => setoid_rewrite Uexp_one
 |  |- context [(Nmult 0 ?x)]     => setoid_rewrite Nmult_0
 |  |- context [(Nmult 1 ?x)]     => setoid_rewrite Nmult_1
 |  |- context [(Nmult ?n 0)]     => setoid_rewrite Nmult_zero
 |  |- context [(nmult 0 ?x)]     => setoid_rewrite nmult_0
 |  |- context [(nmult 1 ?x)]     => setoid_rewrite nmult_1
 |  |- context [(nmult ?n 0)]     => setoid_rewrite nmult_zero
 |  |- context [(sigma ?f O)]     => setoid_rewrite sigma_0
 |  |- context [(sigma ?f (S O))]     => setoid_rewrite sigma_1
 |  |- (Ole (Uplus ?x ?y) (Uplus ?x ?z)) => apply Uplus_le_compat_right
 |  |- (Ole (Uplus ?x ?z) (Uplus ?y ?z)) => apply Uplus_le_compat_left
 |  |- (Ole (Uplus ?x ?z) (Uplus ?z ?y)) => setoid_rewrite (Uplus_sym z y);
					      apply Uplus_le_compat_left
 |  |- (Ole (Uplus ?x ?y) (Uplus ?z ?x)) => setoid_rewrite (Uplus_sym x y);
                                              apply Uplus_le_compat_left
 |  |- (Ole (Uinv ?y) (Uinv ?x)) => apply Uinv_le_compat
 |  |- (Ole (Uminus ?x ?y) (Uminus ?x ?z)) => apply Uminus_le_compat_right
 |  |- (Ole (Uminus ?x ?z) (Uminus ?y ?z)) => apply Uminus_le_compat_left
 |  |- (Ole (Nmult ?x ?z) (Nmult ?y ?z)) => apply Nmult_le_compat_left
 |  |- (Ole (Nmult ?x ?y) (Nmult ?x ?z)) => apply Nmult_le_compat_right
 |  |- (Ole (nmult ?x ?z) (nmult ?y ?z)) => apply nmult_le_compat_left
 |  |- (Ole (nmult ?x ?y) (nmult ?x ?z)) => apply nmult_le_compat_right
 |  |- ((Uinv ?x) == (Uinv ?y)) => apply Uinv_eq_compat
 |  |- ((Uplus ?x ?y) == (Uplus ?x ?z)) => apply Uplus_eq_compat_right
 |  |- ((Uplus ?x ?z) == (Uplus ?y ?z)) => apply Uplus_eq_compat_left
 |  |- ((Uplus ?x ?z) == (Uplus ?z ?y)) => setoid_rewrite (Uplus_sym z y);
                                             apply Uplus_eq_compat_left
 |  |- ((Uplus ?x ?y) == (Uplus ?z ?x)) => setoid_rewrite (Uplus_sym x y);
					     apply Uplus_eq_compat_left
 |  |- ((Uminus ?x ?y) == (Uplus ?x ?z)) => apply Uminus_eq_compat;[apply Oeq_refl|idtac]
 |  |- ((Uminus ?x ?z) == (Uplus ?y ?z)) => apply Uminus_eq_compat;[idtac|apply Oeq_refl]
 |  |- ((Nmult ?x ?y) == (Nmult ?x ?z)) => apply Nmult_eq_compat;[apply eq_refl|idtac]
 |  |- ((Nmult ?x ?z) == (Nmult ?y ?z)) => apply Nmult_eq_compat;[idtac|apply Oeq_refl]
 |  |- ((nmult ?x ?y) == (nmult ?x ?z)) => apply nmult_eq_compat;[apply eq_refl|idtac]
 |  |- ((nmult ?x ?z) == (nmult ?y ?z)) => apply nmult_eq_compat;[idtac|apply Oeq_refl]
 |  |- (Ole (Umult ?x ?y) (Umult ?x ?z)) => apply Umult_le_compat_right
 |  |- (Ole (Umult ?x ?z) (Umult ?y ?z)) => apply Umult_le_compat_left
 |  |- (Ole (Umult ?x ?z) (Umult ?z ?y)) => setoid_rewrite (Umult_sym z y);
                                             apply Umult_le_compat_left
 |  |- (Ole (Umult ?x ?y) (Umult ?z ?x)) => setoid_rewrite (Umult_sym x y);
                                             apply Umult_le_compat_left
 |  |- ((Umult ?x ?y) == (Umult ?x ?z)) => apply Umult_eq_compat_right
 |  |- ((Umult ?x ?z) == (Umult ?y ?z)) =>  apply Umult_eq_compat_left
 |  |- ((Umult ?x ?z) == (Umult ?z ?y)) => setoid_rewrite (Umult_sym z y);
                                             apply Umult_eq_compat_left
 |  |- ((Umult ?x ?y) == (Umult ?z ?x)) => setoid_rewrite (Umult_sym x y);
                                             apply Umult_eq_compat_left
end.

Ltac Ucompute1 :=  
 first [rewrite Uplus_zero_left |
        rewrite Uplus_zero_right |
        rewrite Uplus_one_left |
        rewrite Uplus_one_right |
        rewrite Umult_zero_left |
        rewrite Umult_zero_right |
        rewrite Umult_one_left | 
        rewrite Umult_one_right |
        rewrite Uesp_zero_left |
        rewrite Uesp_zero_right |
        rewrite Uesp_one_left |
        rewrite Uesp_one_right |
        rewrite Uminus_zero_left |
        rewrite Uminus_zero_right |
        rewrite Uminus_one_right |
        rewrite Uinv_inv |
        rewrite Uinv_opp_right |
        rewrite Uinv_opp_left |  
        rewrite Uinv_one |
        rewrite Uinv_zero |
        rewrite Unth_zero |
        rewrite Uexp_0 | 
        rewrite Uexp_1 |
        (rewrite Uexp_zero; [idtac|omega]) |
        rewrite Uexp_one |
        rewrite Nmult_0  | 
        rewrite Nmult_1 |
        rewrite Nmult_zero |
        rewrite sigma_0 |
        rewrite sigma_1 
].

Ltac Ucompute :=  
 first [setoid_rewrite Uplus_zero_left |
        setoid_rewrite Uplus_zero_right |
        setoid_rewrite Uplus_one_left |
        setoid_rewrite Uplus_one_right |
        setoid_rewrite Umult_zero_left |
        setoid_rewrite Umult_zero_right |
        setoid_rewrite Umult_one_left | 
        setoid_rewrite Umult_one_right |
        setoid_rewrite Uesp_zero_left |
        setoid_rewrite Uesp_zero_right |
        setoid_rewrite Uesp_one_left |
        setoid_rewrite Uesp_one_right |
        setoid_rewrite Uminus_zero_left |
        setoid_rewrite Uminus_zero_right |
        setoid_rewrite Uminus_one_right |
        setoid_rewrite Uinv_inv |
        setoid_rewrite Uinv_opp_right |
        setoid_rewrite Uinv_opp_left |  
        setoid_rewrite Uinv_one |
        setoid_rewrite Uinv_zero |
        setoid_rewrite Unth_zero |
        setoid_rewrite Uexp_0 | 
        setoid_rewrite Uexp_1 |
        (setoid_rewrite Uexp_zero; [idtac|omega]) |
        setoid_rewrite Uexp_one |
        setoid_rewrite Nmult_0  | 
        setoid_rewrite Nmult_1 |
        setoid_rewrite Nmult_zero |
        setoid_rewrite sigma_0 |
        setoid_rewrite sigma_1 
].

(** printing [1/4] $\frac{1}{4}$ #&frac14;# *)
(** printing [3/4] $\frac{3}{4}$ #&frac34;# *)

(** Properties of common values *)
Notation "[1/3]" := (Unth 2%nat).
Notation "[1/4]" := (Unth 3%nat).
Notation "[1/8]" := (Unth 7).
Notation "[3/4]" := (Uinv [1/4]).

Lemma half_square : [1/2]*[1/2]==[1/4].
rewrite <- (Unth_exp2 2).
simpl; auto.
Save.

Lemma half_cube : [1/2]*[1/2]*[1/2]==[1/8].
rewrite <- (Unth_exp2 3).
simpl; rewrite Umult_one_right; auto.
Save.

Lemma three_quarter_decomp : [3/4]==[1/2]+[1/4].
transitivity ([1/4] + [1/4] + [1/4]).
rewrite <- Nmult_n_Unth; simpl.
norm_assoc_left; trivial.
Usimpl.
transitivity (2 */ [1/4]); auto.
Save.

Hint Resolve half_square half_cube three_quarter_decomp.

Lemma half_dec_mult 
  : forall p, p <= [1/2] -> ([1/2]+p) * ([1/2]-p) == [1/4] - (p * p).
intros.
rewrite Udistr_plus_right; auto.
repeat rewrite Uminus_distr_right.
rewrite (Umult_sym p [1/2]).
rewrite half_square.
rewrite <- Uminus_plus_simpl_mid; auto.
transitivity ([1/2]*[1/2]); auto.
Save.

Lemma half_Ult_Umult_Uinv : 
      forall p, p < [1/2] -> p * [1-]p < [1/4].
intros.
pose (k:=[1/2]-p).
assert (0 < k) by (unfold k; auto).
assert (p == [1/2]-k).
unfold k.
rewrite Uminus_assoc_right; repeat Usimpl; auto.
assert ([1-]p == [1/2]+k).
unfold k.
rewrite Uplus_minus_assoc_right; auto.
rewrite Unth_one_plus; auto.
rewrite Umult_sym.
rewrite H2, H1, half_dec_mult; auto.
unfold k; auto.
Save.
Hint Resolve half_Ult_Umult_Uinv.

Lemma half_Ule_Umult_Uinv : 
      forall p, p <= [1/2] -> p * [1-]p <= [1/4].
intros; apply (Ule_lt_orc_eq H); auto; intros.
apply Olt_le; apply half_Ult_Umult_Uinv; auto.
rewrite H0.
rewrite <- Unth_one; auto.
Save.
Hint Resolve half_Ule_Umult_Uinv.

Lemma Ult_Umult_Uinv : 
      forall p, ~ p == [1/2] -> p * [1-]p < [1/4].
intros; apply (Udiff_lt_orc H); auto; intros.
apply Ole_lt_trans with ([1-]p * p); auto.
rewrite <- (Uinv_inv p) at 2.
assert ([1-]p < [1/2]); auto.
apply Uinv_lt_perm_left; auto.
rewrite <- Unth_one; auto.
Save.  

Lemma Ule_Umult_Uinv : forall p, p * [1-]p <= [1/4].
intros; apply (Ule_total p [1/2]); auto; intros.
transitivity ([1-]p * p); auto.
rewrite <- (Uinv_inv p) at 2.
assert ([1-]p <= [1/2]); auto.
Save.

(** Equality is not true, even for monotonic sequences fot instance n/m *)

Lemma Ulub_Uglb_exch_le : forall f : nat -> nat -> U,
     Ulub (fun n => Uglb (fun m => f n m)) <= Uglb (fun m => Ulub (fun n => f n m)).
intros; apply le_Uglb; intro m.
apply Ulub_le_compat; intro n.
apply Uglb_le with (f:=fun m0 : nat => f n m0) (n:=m).
Save.



(** ** Limits inf and sup *)

Definition fsup (f:nat -> U) (n:nat) := Ulub (fun k => f (n+k)%nat).

Definition finf (f:nat -> U) (n:nat) := Uglb (fun k => f (n+k)%nat).

Lemma fsup_incr : forall (f:nat -> U) n, fsup f (S n) <= fsup f n.
unfold fsup; intros.
apply Ulub_le; intros.
replace (S n+n0)%nat with (n+S n0)%nat; try omega.
apply le_Ulub with (f:=fun k : nat => f (n+k)%nat).
Save.
Hint Resolve fsup_incr.

Lemma finf_incr : forall (f:nat -> U) n, finf f n <= finf f (S n).
unfold finf; intros.
apply le_Uglb; intros.
replace (S n+n0)%nat with (n+S n0)%nat; try omega.
apply Uglb_le with (f:=fun k : nat => f (n+k)%nat).
Save.

Hint Resolve finf_incr.

Instance fsup_mon : forall f, monotonic (o2:=Iord U) (fsup f).
intro; apply nat_monotonic; simpl; auto.
Save.

Instance finf_mon : forall f, monotonic (finf f).
intro; apply nat_monotonic; auto.
Save.


Definition Fsup (f:nat -> U) : nat -m-> U := mon (fsup f).
Definition Finf (f:nat -> U) : nat -m> U := mon (finf f).

Lemma fn_fsup : forall f n, f n <= fsup f n.
unfold fsup; intros.
pattern n at 1; replace n with (n+O)%nat; auto with arith.
apply le_Ulub with (f:=fun k : nat => f (n+k)%nat) (n:=O).
Save.
Hint Resolve fn_fsup.

Lemma finf_fn : forall f n, finf f n <= f n.
unfold finf; intros.
pattern n at 2; replace n with (n+O)%nat; auto with arith.
apply Uglb_le with (f:=fun k : nat => f (n+k)%nat) (n:=O).
Save.
Hint Resolve finf_fn.

Definition limsup f := glb (Fsup f).
Definition liminf f := lub (Finf f).

Lemma le_liminf_sup : forall f, liminf f <= limsup f.
unfold liminf,limsup; simpl; intro.
rewrite <- Uglb_glb.
transitivity (Ulub (Finf f)); auto.
unfold Finf,Fsup,finf,fsup.
transitivity 
    (Uglb (fun m : nat => Ulub (fun n : nat => f (n+m)%nat))).
apply Ulub_Uglb_exch_le with (f:=fun n m => f (n+m)%nat).
apply Uglb_le_compat; simpl; intro.
apply Ulub_le_compat; simpl; intro.
replace ((x0+x)%nat) with ((x+x0)%nat); auto with arith.
Save.

Hint Resolve le_liminf_sup.

Definition has_lim f := limsup f <= liminf f.

Lemma eq_liminf_sup : forall f, has_lim f-> liminf f == limsup f.
intro; unfold has_lim; apply Ole_antisym; auto.
Save.


Definition cauchy f := forall (p:nat), exc (fun M:nat => forall n m,
          (M <= n)%nat -> (M <= m)%nat -> f n <= f m + [1/2]^p).


Definition is_limit f (l:U) := forall (p:nat), exc (fun M:nat => forall n,
          (M <= n)%nat -> f n <= l + [1/2]^p /\ l <= f n + [1/2]^p).

Lemma cauchy_lim : forall f, cauchy f -> is_limit f (limsup f).
unfold cauchy,is_limit; intros.
apply (H p); clear H; auto; intros M H; apply exc_intro with M; intros n H1; unfold limsup; split.
transitivity (glb ((Imon (mshift UPlus ([1/2]^p))) @ (mon (seq_lift_left (Fsup f) M)))).
apply le_glb; simpl; intro k.
transitivity (f (M + k)%nat + [1/2]^p); unfold seq_lift_left; simpl; auto with arith.
rewrite glb_eq_plus_cte_right; Usimpl.
rewrite <- glb_lift_left; auto.
transitivity (Fsup f M); auto; simpl.
unfold fsup; apply Ulub_le; intro k; auto with arith.
Save.


Lemma has_limit_cauchy : forall f l, is_limit f l -> cauchy f.
unfold cauchy,is_limit; intros.
apply (H (S p)); clear H; auto; intros M H; apply exc_intro with M; intros n m H1; unfold limsup.
case (H n); auto with arith; intros.
case (H m); auto with arith; intros.
transitivity (l + [1/2]^(S p)); auto.
transitivity (f m + [1/2]^(S p) + [1/2]^(S p)); auto.
norm_assoc_right; Usimpl; auto.
Save.

Lemma limit_le_unique : forall f l1 l2, is_limit f l1 -> is_limit f l2 -> l1 <= l2.
intros f l1 l2 liml1 liml2; apply Ule_lt_half_exp; intro p2.
intros; apply Ule_lt_half_exp; intro p1.
apply (liml1 p1); auto; intros M1 H1.
apply (liml2 p2); auto; intros M2 H2.
case (H1 (M1+M2)%nat); auto with arith; intros.
case (H2 (M1+M2))%nat; auto with arith; intros.
transitivity (f (M1 + M2)%nat + [1/2]^p1); auto.
Save.


Lemma limit_unique : forall f l1 l2, is_limit f l1 -> is_limit f l2 -> l1 == l2.
intros; apply Ole_antisym; apply (limit_le_unique (f:=f)); auto.
Save.
Hint Resolve limit_unique.

Lemma has_limit_compute : forall f l, is_limit f l -> is_limit f (limsup f).
intros; apply cauchy_lim; auto.
apply has_limit_cauchy with l; trivial.
Save.


Lemma limsup_eq_mult : forall k (f : nat -> U),
        limsup (fun n => k * f n) == k * limsup f.
unfold limsup; intros.
transitivity (glb (Imon (UMult k) @ (Fsup f))); auto.
apply glb_eq_compat; intro n; simpl; unfold fsup; intros; simpl; auto.
rewrite glb_eq_mult; trivial.
Save.

Lemma liminf_eq_mult : forall k (f : nat -> U),
        liminf (fun n => k * f n) == k * liminf f.
unfold liminf; intros.
transitivity (lub ((UMult k) @ (Finf f))); auto.
apply lub_eq_compat; intro n; simpl; unfold finf; intros; auto.
Save.

Lemma limsup_eq_plus_cte_right : forall k (f : nat -> U),
                 limsup (fun n => (f n) + k) == limsup f + k.
unfold limsup; intros.
transitivity (glb (Imon (mshift UPlus k) @ (Fsup f))); auto.
apply glb_eq_compat; intro n; simpl; unfold fsup; intros; auto.
Save.

Lemma liminf_eq_plus_cte_right : forall k (f : nat -> U),
                 liminf (fun n => (f n) + k) == liminf f + k.
unfold liminf; intros.
transitivity (lub (mshift UPlus  k @ (Finf f))); auto.
apply lub_eq_compat; intro n; simpl; unfold finf; intros; auto.
Save.

Lemma limsup_le_plus : forall (f g: nat -> U),
                 limsup (fun x => f x + g x) <= limsup f + limsup g.
intros; unfold limsup,fplus.
transitivity (glb ((Imon2 UPlus @2 (Fsup f)) (Fsup g))).
apply glb_le_compat; simpl; intro.
unfold fsup; auto.
rewrite glb_eq_plus; auto.
Save.

Lemma liminf_le_plus : forall (f g: nat -> U),
                 liminf f + liminf g <= liminf (fun x => f x + g x).
intros; unfold liminf,fplus.
transitivity (lub ((UPlus @2 (Finf f)) (Finf g))); auto.
apply lub_le_compat; simpl; unfold finf; auto.
Save.

Hint Resolve liminf_le_plus limsup_le_plus.

Lemma limsup_le_compat : forall f g : nat -> U, f <= g -> limsup f <= limsup g.
unfold limsup; intros.
apply glb_le_compat; simpl; intros; unfold fsup; apply Ulub_le_compat; auto.
Save.

Lemma liminf_le_compat : forall f g : nat -> U, f <= g -> liminf f <= liminf g.
unfold liminf; intros.
apply lub_le_compat; simpl; intros; unfold finf; apply Uglb_le_compat; auto.
Save.

Hint Resolve limsup_le_compat liminf_le_compat.

Lemma limsup_eq_compat : forall f g : nat -> U, f == g -> limsup f == limsup g.
intros; apply Ole_antisym; auto.
Save.

Lemma liminf_eq_compat : forall f g : nat -> U, f == g -> liminf f == liminf g.
intros; apply Ole_antisym; auto.
Save.

Hint Resolve liminf_eq_compat limsup_eq_compat.

Lemma limsup_inv :  forall f : nat -> U, limsup (fun x => [1-]f x) == [1-] liminf f.
unfold limsup, liminf; intros.
unfold glb; Usimpl.
apply lub_eq_compat; intro n; simpl; unfold finf,fsup,Uglb; simpl; Usimpl.
apply Ulub_eq_compat; intro m; auto.
Save.

Lemma liminf_inv :  forall f : nat -> U, liminf (fun x => [1-]f x) == [1-] limsup f.
unfold limsup, liminf; intros.
unfold glb; Usimpl.
apply lub_eq_compat; intro n; simpl; unfold finf,fsup,Uglb; Usimpl.
apply Ulub_eq_compat;  intro m; auto.
Save.

Hint Resolve limsup_inv liminf_inv.

(** ** Limits of arbitrary sequences *)
Lemma liminf_incr : forall f:nat -m> U, liminf f == lub f.
unfold liminf;intros.
apply lub_eq_compat; intro n; simpl.
unfold finf.
rewrite (glb_mon (mseq_lift_left f n)); simpl.
replace (n+0)%nat with n; auto with arith.
Save.

Lemma limsup_incr : forall f:nat -m> U, limsup f == lub f.
unfold limsup; intros.
transitivity (glb (mon  (o2:=Iord U) (fun _ => (lub f)))); auto.
apply glb_eq_compat; intro n; simpl.
unfold fsup.
transitivity (lub (mseq_lift_left f n)).
transitivity (Ulub (mseq_lift_left f n)); auto.
unfold fcte; transitivity (mlub (seq_lift_left f n)); auto.
apply lub_eq_compat; intro x; simpl; auto.
apply (glb_cte (lub f)).
Save.


Lemma has_limit_incr : forall f:nat -m> U, has_lim f.
red; intros.
rewrite liminf_incr; auto; rewrite limsup_incr; auto.
Save.

Lemma liminf_decr : forall f:nat -m-> U, liminf f == glb f.
unfold liminf; intros.
transitivity (mlub (cte nat (glb f))); auto.
apply lub_eq_compat; intro n; simpl; unfold finf; intros.
transitivity (glb (mseq_lift_left f n)).
transitivity (Uglb (mseq_lift_left f n)); auto.
unfold cte; transitivity (glb (mon (seq_lift_left f n))); auto.
apply glb_eq_compat; intro x; simpl; auto.
Save.


Lemma limsup_decr : forall f:nat -m-> U, limsup f == glb f.
unfold limsup;intros.
apply glb_eq_compat; intro n; simpl; unfold fsup.
transitivity (Ulub (mseq_lift_left f n)); auto.
transitivity (mseq_lift_left f n O); auto.
apply (Ulub_mon (mseq_lift_left f n)).
simpl; replace (n+0)%nat with n; auto with arith.
Save.

Lemma has_limit_decr : forall f:nat -m-> U, has_lim f.
red; intros.
rewrite liminf_decr; auto; rewrite limsup_decr; auto.
Save.

Lemma has_limit_sum : forall f g: nat -> U, has_lim f -> has_lim g -> has_lim (fun x => f x + g x).
unfold has_lim; intros.
transitivity (limsup f + limsup g); auto.
apply  Ole_trans with (liminf f + liminf g); auto.
Save.

Lemma has_limit_inv : forall f : nat -> U, has_lim f -> has_lim (fun x => [1-]f x).
unfold has_lim; intros.
transitivity  ([1-]liminf f); auto.
transitivity  ([1-]limsup f); auto.
Save.

Lemma has_limit_cte : forall c, has_lim (fun n => c).
intros; apply (has_limit_incr (mon (cte nat (c:U)))); red; auto.
Save.


(** ** Definition and properties of series : infinite sums *)

Definition serie (f : nat -> U) : U := lub (sigma f).

Lemma serie_le_compat : forall (f g: nat -> U), 
 (forall k,  f k <= g k) -> serie f  <= serie g.
unfold serie; intros; apply lub_le_compat; intro n; auto.
Save.

Lemma serie_eq_compat : forall (f g: nat -> U), 
 (forall k, f k == g k) -> serie f == serie g.
unfold serie; intros; apply lub_eq_compat; intro n; auto.
Save.

Lemma serie_sigma_lift : forall (f :nat -> U) (n:nat), 
          serie f == sigma f n + serie (fun k => f (n + k)%nat).
intros f n; unfold serie; transitivity 
   (lub (mseq_lift_left (sigma f) n)); auto.
transitivity 
  (lub (UPlus (sigma f n) @  sigma (fun k => f (n+k)%nat))).
apply lub_eq_compat; intro n0.
rewrite mseq_lift_left_simpl.
rewrite comp_simpl.
apply (sigma_plus_lift f n n0).
symmetry.
apply (lub_comp_eq (UPlus (sigma f n)) (sigma (fun k : nat => f (n + k)%nat))  ).
apply continuous2_app; trivial.
Save.

Lemma serie_sigma_decomp : forall (f g:nat -> U) (n:nat), 
          (forall k, g k = f (n + k)%nat) ->
          serie f == sigma f n + serie g.
intros; apply Oeq_trans with (1:=serie_sigma_lift f n).
apply Uplus_eq_compat; trivial.
apply serie_eq_compat; auto.
Save.


Lemma serie_lift_le : forall (f :nat -> U) (n:nat), 
          serie (fun k => f (n + k)%nat)  <= serie f.
intros.
rewrite (serie_sigma_lift f n); auto.
Save.
Hint Resolve serie_lift_le.

Lemma serie_decomp_le : forall (f g:nat -> U) (n:nat), 
          (forall k, g k <= f (n + k)%nat) ->
          serie g <= serie f.
intros.
apply Ole_trans with (2:=serie_lift_le f n).
apply serie_le_compat; auto.
Save.

Lemma serie_S_lift : forall (f :nat -> U),
          serie f == f O + serie (fun k => f (S k)).
intro; rewrite (serie_sigma_lift f (S O)); simpl.
apply Uplus_eq_compat; auto.
Save.

Lemma serie_zero : forall f, (forall k, f k ==0) -> serie f ==0.
unfold serie; intros.
rewrite <- (lub_cte (D:=U) 0).
apply lub_eq_compat; intro n; auto.
Save.

Lemma serie_not_zero : forall f k, 0 < f k ->  0 < serie f.
intros; apply Olt_le_trans with (sigma f (S k)).
apply (sigma_not_zero f) with (k:=k); auto.
unfold serie; apply le_lub; auto.
Save.

Lemma serie_zero_elim : forall f, serie f == 0 -> forall k, f k ==0.
intros; apply Ueq_class; red; intros.
assert (0 < serie f); auto.
apply serie_not_zero with k; auto.
apply (Olt_notle _ _ H1); auto.
Save.

Hint Resolve serie_eq_compat serie_le_compat serie_zero.

Lemma serie_le : forall f k, f k <= serie f.
intros; transitivity (sigma f (S k)); auto.
unfold serie; apply le_lub; auto.
Save.

Lemma serie_minus_incr : forall f :nat -m> U, serie (fun k => f (S k) - f k) == lub f - f O.
intros; transitivity (lub (mshift UMinus (f O) @ f)).
unfold serie; apply lub_eq_compat.
intro n; rewrite comp_simpl; rewrite mshift_simpl.
rewrite UMinus_simpl.
apply (sigma_minus_incr f); auto.
assert (continuous2 (c1:=Uopp) (mshift UMinus)); auto.
assert (continuous (mshift UMinus (f O))); auto.
apply (continuous2_app (c1:=Uopp)); trivial.
rewrite <- (lub_comp_eq (mshift UMinus (f O)) f); trivial.
Save.

Lemma serie_minus_decr : forall f : nat -m-> U,
         serie (fun k => f k - f (S k)) == f O - glb f.
intros; transitivity (lub (UMinus (f O) @ f)).
unfold serie; apply lub_eq_compat.
intro n; rewrite comp_simpl.
rewrite UMinus_simpl.
apply (sigma_minus_decr f); auto.
assert (continuous (c1:=Uopp) (UMinus (f O))).
apply @continuous2_app with (c1:=cpoU) (c2:=Uopp) (F:=UMinus) (k:=f O); trivial.
symmetry; rewrite <- (lub_comp_eq (c1:=Uopp) (UMinus (f O)) f); auto.
Save.

Lemma serie_plus : forall (f g : nat -> U), 
   serie (fun k => (f k) + (g k))  == serie f + serie g.
intros; unfold serie.
transitivity 
  (lub ((UPlus @2 sigma f) (sigma g))); auto.
apply lub_eq_compat; intro n.
exact (sigma_plus f g n).
Save.

(** series and lub *)

Lemma serie_glb_pos : forall f : nat -> U, 0 < Uglb f -> serie f == 1.
intros; apply Ole_antisym; trivial.
apply (archimedian (Uglb f)); intros; auto.
transitivity (S x */ [1/]1+x); auto.
transitivity (sigma f (S x)); auto.
rewrite Nmult_sigma; apply sigma_le_compat; intros.
transitivity (Uglb f); auto.
rewrite (serie_sigma_lift f (S x)); auto.
Save.

Lemma serie_glb_0 : forall f : nat -> U, serie f < 1 -> Uglb f == 0.
intros.
symmetry; apply not_Ult_eq_zero;intro.
apply H.
apply serie_glb_pos; auto.
Save.
Hint Immediate serie_glb_0.

Definition wretract (f : nat -> U) := forall k, f k <= [1-] (sigma f k).

Lemma retract_wretract : forall f, (forall n, retract f n) -> wretract f.
red; intros; auto.
Save.

Lemma wretract_retract : forall f, wretract f -> forall n, retract f n.
red; intros; auto.
Save.

Hint Resolve wretract_retract.

Lemma wretract_lt : forall (f : nat -> U), (forall (n : nat),  sigma f n < 1) -> wretract f.
intros; apply retract_wretract; intros.
apply retract_lt; trivial.
Save.
Hint Immediate wretract_lt.

Lemma wretract_lt_serie : forall (f : nat -> U), serie f < 1 -> wretract f.
intros; apply wretract_lt; intros.
apply Ole_lt_trans with (serie f); auto.
unfold serie; auto.
Save.
Hint Immediate wretract_lt_serie.

Lemma retract_zero_wretract :
       forall f n, retract f n -> (forall k, (n <= k)%nat -> f k == 0) -> wretract f.
red; intros.
assert (k < n \/ n <= k)%nat; intuition.
omega.
rewrite H0; auto.
Save.

Lemma wretract_le : forall f g : nat -> U, f <= g -> wretract g -> wretract f.
red; intros.
transitivity (g k); auto.
transitivity ([1-]sigma g k); auto.
Save.

Lemma wretract_lift : forall f n, wretract f -> 
      sigma f n <= [1-] serie (fun k => f (n + k)%nat).
intros f n Hr; apply Uinv_le_perm_right.
unfold serie.
apply lub_le.
intro k; induction k; auto.
rewrite sigma_S.
transitivity ([1-]sigma f (n+k)%nat + (sigma (fun k0 : nat => f (n + k0)%nat)) k).
auto.
rewrite sigma_plus_lift.
rewrite (Uplus_sym (sigma f n)).
rewrite Uinv_plus_left; auto.
Save.
Hint Resolve wretract_lift.

Lemma serie_mult :
  forall (f : nat -> U) c, wretract f -> serie (fun k => c * f k) == c * serie f.
unfold serie; intros.
transitivity (lub (UMult c @ sigma f)); auto.
apply lub_eq_compat; intro n.
apply (sigma_mult (f:=f) c (n:=n)); auto.
Save.
Hint Resolve serie_mult.

Lemma serie_prod_maj :  forall (f g : nat -> U), 
   serie (fun k => f k * g k) <= serie f.
auto.
Save.

Hint Resolve serie_prod_maj.

Lemma serie_prod_le :  forall (f g : nat -> U) (c:U), (forall k, f k <= c) 
   -> wretract g -> serie (fun k => f k * g k) <= c * serie g.
intros; transitivity (serie (fun k => c * g k)); auto.
Save.

Lemma serie_prod_ge :  forall (f g : nat -> U) (c:U), (forall k, c <= (f k)) 
   -> wretract g -> c * serie g <= serie (fun k => f k * g k).
intros; transitivity (serie (fun k => c * g k)); auto.
rewrite serie_mult; auto.
Save.

Hint Resolve serie_prod_le  serie_prod_ge.

(*
Lemma serie_inv : forall (f g : nat -> U), wretract f ->
  [1-] (serie (fun k => f k * g k)) == serie (fun k => f k * [1-] (g k)) + [1-] (serie f).
unfold serie; intros.
transitivity 
  (glb (UInvopp @ sigma (fun k : nat => f k * g k))).
unfold glb; Usimpl.
apply lub_eq_compat; apply fmon_eq_intro; intro n.
repeat rewrite fmon_comp_simpl; rewrite UInv_simpl.
rewrite (UInvopp_simpl (sigma (fun k : nat => f k * g k) n)); auto.
transitivity (glb (UPlus2 @2 
*)

Lemma serie_inv_le : forall (f g : nat -> U), wretract f ->
  serie (fun k => f k * [1-] (g k)) <= [1-] (serie (fun k => f k * g k)).
unfold serie; intros.
apply lub_lub_inv_le; intros.
rewrite sigma_inv; auto.
Save.

Lemma serie_half : forall f, serie f < 1  
      -> exc (fun n => serie (fun k => f (n + k)%nat) <= [1/2] * serie f).
intros; apply (Ueq_orc 0 (serie f)); auto; intros.
apply exc_intro with O; simpl; rewrite <- H0; repeat Usimpl; auto.
assert ([1/2] * serie f < serie f).
apply Umult_lt_right; auto.
assert (exc (fun n => [1/2] * serie f < sigma f n)).
apply exc_intro_class.
intros; apply (lub_Olt _ _ H1); auto.
apply H2; auto; intros n Hlt.
apply exc_intro with n.
transitivity (serie f - sigma f n).
rewrite (serie_sigma_lift f n); auto.
transitivity (serie f - [1/2] * serie f); auto.
Save.

Lemma serie_half_exp : forall f m, serie f < 1  
      -> exc (fun n => serie (fun k => f (n + k)%nat) <= [1/2]^m).
intros; induction m; simpl.
apply exc_intro with O; auto.
apply IHm; auto; intros n Hn.
apply (serie_half (fun k => f (n+k)%nat)); auto.
apply Ole_lt_trans with (serie f); auto.
intros n0 Hn0.
apply exc_intro with (n+n0)%nat.
transitivity (serie (fun k : nat => f (n + (n0 + k))%nat)); auto with zarith.
rewrite Hn0; auto.
Save.

(*
Lemma serie_lt_lift :  forall f p, serie f < 1 -> ~ 0 == p -> 
      -> exc (fun n => serie (fun k => f (n + k)%nat) <= p).
*)


Definition Serie : (nat -> U) -m> U.
exists serie.
abstract (red; intros; apply serie_le_compat; auto).
Defined.

Lemma Serie_simpl : forall f, Serie f = serie f.
trivial.
Save.

Lemma serie_continuous : continuous Serie.
red; intros; rewrite Serie_simpl; unfold serie.
transitivity (lub (lub (Sigma @ h))).
apply lub_le_compat; intro n; auto.
apply sigma_continuous1.
rewrite  (double_lub_shift (Sigma @ h)).
apply lub_le_compat; intro n.
rewrite comp_simpl; rewrite Serie_simpl.
unfold serie; rewrite fmon_lub_simpl.
apply lub_le_compat; intro m.
repeat rewrite mshift_simpl; auto.
Save.

Definition fun_cte n (a:U) : nat -> U 
      := fun p => if eq_nat_dec p n then a else 0.

Lemma fun_cte_eq : forall n a, fun_cte n a n = a.
unfold fun_cte; intros; rewrite if_then; auto.
Save.

Lemma fun_cte_zero : forall n a p, p <> n -> fun_cte n a p = 0.
unfold fun_cte; intros; rewrite if_else; auto.
Save.

Lemma sigma_cte_eq : forall n a p, (n < p)%nat -> sigma (fun_cte n a) p == a.
induction 1.
rewrite sigma_S.
assert ((sigma (fun_cte n a)) n == 0).
apply sigma_zero.
intros k H; rewrite fun_cte_zero; auto; omega.
rewrite fun_cte_eq; rewrite H; auto.
rewrite sigma_S; rewrite IHle.
rewrite fun_cte_zero; auto; omega.
Save.
Hint Resolve sigma_cte_eq.

Lemma serie_cte_eq : forall n a, serie (fun_cte n a) == a.
intros; apply Ole_antisym; unfold serie.
apply lub_le.
intros p; destruct (le_lt_dec (S n) p) as [Hle|Hle].
rewrite sigma_cte_eq; auto.
transitivity (sigma (fun_cte n a) (S n)); auto.
apply fmon_le; auto with arith.
transitivity (sigma (fun_cte n a) (S n)); auto.
rewrite sigma_cte_eq; auto.
Save.

Section PartialPermutationSerieLe.
Variables f g : nat -> U.

Variable s : nat -> nat -> Prop.
Hypothesis s_dec : forall i j, {s i j}+{~s i j}.

Hypothesis s_inj : forall i j k : nat, s i k -> s j k -> i = j.
Hypothesis s_dom : forall i, ~ f i == 0 -> exists j, s i j.

Hypothesis f_g_perm : forall i j, s i j -> f i == g j.

Lemma serie_perm_rel_le : serie f <= serie g.
unfold serie at 1.
apply lub_le; intro n.
transitivity (serie (fun k => 
                            if dec_exists_lt _  (fun i => s_dec i k) n 
                               then g k else 0)).
induction n; auto.
rewrite sigma_S.
rewrite IHn; clear IHn.
apply (Ueq_orc (f n) 0); auto; intro H.
rewrite H; Usimpl; apply serie_le_compat; intro k.
destruct dec_exists_lt as [(i,(H1,H2))|H']; auto with zarith.
rewrite if_then; auto with zarith.
exists i; auto with zarith.
destruct (s_dom n) as (ni,Hni); auto.
rewrite <- (serie_cte_eq ni (f n)).
rewrite <- serie_plus.
apply serie_le_compat;intro k.
unfold fun_cte; destruct (eq_nat_dec k ni) as [Hkn|Hkn].
rewrite if_else; try omega.
rewrite if_then; try omega.
rewrite Hkn; auto.
exists n; subst; auto with zarith.
intros (i,(H1,H2)). 
subst; absurd (i=n); auto with zarith.
apply s_inj with ni; auto.
Usimpl; destruct dec_exists_lt as [(i,(H1,H2))|Hsknd]; auto.
rewrite if_then; auto.
exists i; auto with zarith.
apply serie_le_compat; intro k.
destruct dec_exists_lt as [(i,(H1,H2))|Hsknd]; auto.
Save.

End PartialPermutationSerieLe.

Section PartialPermutationSerieEq.
Variables f g : nat -> U.

Variable s : nat -> nat -> Prop.
Hypothesis s_dec : forall i j, {s i j}+{~s i j}.
Hypothesis s_fun : forall i j k : nat, s i j -> s i k -> j = k.
Hypothesis s_inj : forall i j k : nat, s i k -> s j k -> i = j.
Hypothesis s_surj : forall j, ~ g j == 0 ->  exists i, s i j.
Hypothesis s_dom : forall i, ~ f i == 0 -> exists j, s i j.
Hypothesis f_g_perm : forall i j, s i j -> f i == g j.

Lemma serie_perm_rel_eq : serie f == serie g.
apply Ole_antisym.
apply serie_perm_rel_le with s; auto.
apply serie_perm_rel_le with (fun i j => s j i); auto.
intros; apply s_fun with k; auto.
intros; symmetry; auto.
Save.

End  PartialPermutationSerieEq.


Section PermutationSerie.
Variable s : nat -> nat.
Hypothesis s_inj : forall i j : nat, s i = s j -> i = j.
Hypothesis s_surj : forall j, exists i, s i = j.

Variable f : nat -> U.

Lemma serie_perm_le : serie (fun i => f (s i)) <= serie f.
apply serie_perm_rel_le with (fun i j => s i = j); auto.
intros; apply (eq_nat_dec (s i) j).
intros; apply s_inj; transitivity k; auto.
intros; exists (s i); auto.
Save.

Lemma serie_perm_eq : serie f == serie (fun i => f (s i)).
apply serie_perm_rel_eq with (fun i j => s j = i); auto with zarith.
intros; apply (eq_nat_dec (s j) i).
intros; exists (s j); auto.
Save.

End PermutationSerie.
Hint Resolve serie_perm_eq serie_perm_le.


Section SerieProdRel.
Variable f : nat -> U.
Variable g : nat -> nat -> U.
Variable s : nat -> nat -> nat -> Prop.
Hypothesis s_dec : forall k n m, {s k n m}+{~ s k n m}.
Hypothesis s_fun1 : forall k n1 m1 n2 m2, s k n1 m1 -> s k n2 m2 -> n1 = n2.
Hypothesis s_fun2 : forall k n1 m1 n2 m2, s k n1 m1 -> s k n2 m2 -> m1 = m2.
Hypothesis s_inj : forall k1 k2 n m, s k1 n m -> s k2 n m -> k1 = k2.
Hypothesis s_surj : forall n m, ~ g n m == 0 -> exists k, s k n m.
Hypothesis f_g_perm : forall k n m, s k n m -> f k == g n m.

Section SPR.

Hypothesis s_dom : forall k, ~ f k == 0 -> exists n, exists m, s k n m.

Lemma serie_le_rel_prod : serie f <= serie (fun n => serie (g n)).
unfold serie at 1.
apply lub_le; intro N.
transitivity (serie (fun n => serie (fun m => 
                                           if dec_exists_lt (fun i => s i n m) (fun i => s_dec i n m) N
                                           then g n m else 0))).
induction N; auto.
rewrite sigma_S.
rewrite IHN; clear IHN.
apply (Ueq_orc (f N) 0); auto; intro H.
rewrite H; Usimpl; apply serie_le_compat; intro n.
apply serie_le_compat; intro m.
destruct dec_exists_lt as [(i,(H1,H2))|H']; auto with zarith.
rewrite if_then; auto with zarith.
exists i; auto with zarith.
destruct (s_dom N) as (Ni,(Mi,HNMi)); auto.
rewrite <- (serie_cte_eq Mi (f N)).
rewrite <- (serie_cte_eq Ni (serie (fun_cte Mi (f N)))).
rewrite <- serie_plus.
apply serie_le_compat;intro n.
unfold fun_cte; destruct (eq_nat_dec n Ni) as [Hkn|Hkn].
rewrite <- serie_plus.
apply serie_le_compat;intro m.
destruct (eq_nat_dec m Mi) as [Hkm|Hkm].
rewrite if_else; try omega.
rewrite if_then; try omega.
Usimpl; subst; auto.
exists N; subst; auto with zarith.
intros (i,(H1,H2)). 
subst; absurd (i=N); auto with zarith.
apply s_inj with Ni Mi; auto.
Usimpl; destruct dec_exists_lt as [(i,(H1,H2))|Hsknd]; auto.
rewrite if_then; auto.
exists i; auto with zarith.
Usimpl; apply serie_le_compat; intro m.
destruct dec_exists_lt as [(i,(H1,H2))|Hsknd]; auto.
rewrite if_then; auto.
exists i; auto.
apply serie_le_compat;intro n.
apply serie_le_compat;intro m.
destruct dec_exists_lt as [(i,(H1,H2))|Hsknd]; auto.
Save.
End SPR.

Variable s_fst : nat -> nat.
Hypothesis s_fst_ex : forall k, exists m, s k (s_fst k) m.

Lemma s_dom : forall k, exists n, exists m, s k n m.
intros; exists (s_fst k); auto.
Save.
Hint Resolve s_dom.

Lemma serie_rel_prod_le : serie (fun n => serie (g n)) <= serie f.
unfold serie at 1.
apply lub_le; intro N.
transitivity (serie (fun k => if lt_dec (s_fst k) N then f k else 0)).
induction N; auto.
rewrite sigma_S.
rewrite IHN; clear IHN.
assert (serie (g N) <= 
            serie (fun k => if eq_nat_dec (s_fst k) N then f k else 0)).
apply serie_perm_rel_le with (fun m k => s k N m); auto.
intros; apply s_fun2 with k N N; auto.
intros; rewrite if_then; auto. 
symmetry; auto.
destruct (s_fst_ex j) as (m,Hsm).
apply s_fun1 with j m i; auto.

(**)
transitivity (serie (fun k : nat => if eq_nat_dec (s_fst k) N then f k else 0)
                  + serie (fun k : nat => if lt_dec (s_fst k) N then f k else 0) ); auto.
rewrite <- serie_plus.
apply serie_le_compat; intro k.
destruct (lt_eq_lt_dec (s_fst k) N) as [[H1|H1]|H1].
rewrite if_else; auto with zarith.
rewrite if_then; auto with zarith.
rewrite if_then; auto with zarith.
rewrite if_then; auto with zarith.
rewrite if_else; auto with zarith.
rewrite if_then; auto with zarith.
rewrite if_else; auto with zarith.
rewrite if_else; auto with zarith.
(**)
apply serie_le_compat; intro k.
destruct lt_dec; auto.
Save.

Lemma serie_rel_prod_eq : serie f == serie (fun n => serie (g n)).
intros; apply Ole_antisym.
apply serie_le_rel_prod; auto.
apply serie_rel_prod_le.
Save.

End SerieProdRel.


Section SerieProd.
Variable f : (nat * nat) -> U.
Variable s : nat -> nat * nat.
Variable s_inj : forall n m, s n = s m -> n = m.
Variable s_surj : forall m, exists n, s n = m.


Lemma serie_enum_prod_eq : serie (fun k => f (s k)) == serie (fun n => serie (fun m => f (n,m))).
intros.
apply serie_rel_prod_eq with (s:=fun k n m => s k = (n,m)) (s_fst := fun k => fst (s k)); intros;
auto.
apply (eq_nat2_dec (s k) (n,m)).
assert (Heq: (n1,m1)=(n2,m2)); try (injection Heq); auto.
transitivity (s k); auto.
assert (Heq: (n1,m1)=(n2,m2)); try (injection Heq); auto.
transitivity (s k); auto.
apply s_inj; transitivity (n,m); auto.
rewrite H; auto.
exists (snd (s k)); destruct (s k); trivial.
Save.

End SerieProd.
Hint Resolve serie_enum_prod_eq.


(* End Univ_prop. *)
