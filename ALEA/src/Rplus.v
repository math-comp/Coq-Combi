(** * Rplus.v: Definition of R+ *)

Add Rec LoadPath "." as ALEA.
Require Export Uprop.
Open Local Scope U_scope.
Require Export Omega.
Require Export Arith.

(** ** Extra axiom on [U] : test of order *)

Variable isle : U -> U -> bool.
Hypothesis isle_true_eq : forall x y, x <= y <-> isle x y = true.

Lemma isle_true : forall x y, x <= y -> isle x y = true.
intros x y; rewrite isle_true_eq; trivial.
Save.

Lemma isle_false_iff : forall x y, ~ (x <= y) <-> isle x y = false.
intros x y; rewrite isle_true_eq.
case (isle x y); intuition.
Save.

Lemma isle_false_nle : forall x y, ~ (x <= y) -> isle x y = false.
intros x y; rewrite isle_false_iff; trivial.
Save.

Lemma isle_false : forall x y, y < x -> isle x y = false.
intros; apply isle_false_nle; auto.
Save.

Hint Resolve isle_true_eq isle_false_iff.

Hint Immediate isle_true isle_false isle_false_nle.

Lemma isle_rec : forall (x y:U) (P : bool -> Type),
      (x <= y -> P true)
   -> (y < x  -> P false)
   -> P (isle x y).
intros; case_eq (isle x y); intro.
apply X; rewrite isle_true_eq; auto.
apply X0; apply notUle_lt; auto.
rewrite isle_false_iff; auto.
Defined.

Lemma isle_lt_dec : forall x y : U, {x <= y} + {y < x}.
intros x y; apply (isle_rec x y (fun _ => {x <= y} + {y < x})); auto.
Defined.

Lemma isle_dec : forall x y : U, {x <= y} + { ~ x <= y}.
intros x y; apply (isle_rec x y (fun _ => {x <= y} + { ~ x <= y})); auto.
Defined.

Lemma iseq_dec : forall x y : U, {x == y} + { ~ x == y}.
intros; case (isle_dec x y); intro; auto.
case (isle_dec y x); intro; auto.
Defined.

Hint Resolve isle_dec iseq_dec.

Add Morphism isle with signature Oeq ==> Oeq ==> eq as isle_eq_compat.
intros; case_eq (isle x x0); intros.
symmetry.
apply isle_true.
rewrite <- H; rewrite <- H0; rewrite isle_true_eq; auto.
symmetry.
apply isle_false_nle.
rewrite <- H; rewrite <- H0; rewrite isle_false_iff; auto.
Save.

Definition is0 (x:U) := isle x 0.

Definition is1 (x:U) := isle 1 x.

(*
Lemma is1_true_eq :  forall x:U, x == 1 <-> is1 x = true.
intros; unfold is1.
rewrite <- is0_true_eq.
intuition.
apply Uinv_simpl; rewrite H; auto.
Save.

Lemma is1_true :  forall x:U, x == 1 -> is1 x = true.
intro; rewrite is1_true_eq; trivial.
Save.


Lemma is1_false_eq :  forall x:U, ~ x == 1 <-> is1 x = false.
intro; rewrite is1_true_eq.
case (is1 x); intuition.
Save.

Lemma is1_false :  forall x:U, ~ x == 1 -> is1 x = false.
intro; rewrite is1_false_eq; trivial.
Save.

Lemma is1_false_lt :  forall x:U, x < 1 -> is1 x = false.
intros; apply is1_false; auto.
Save.

Hint Resolve is1_true_eq is1_false_eq.
Hint Immediate is1_true is1_false is1_false_lt.

Lemma is1_rec : forall (x:U) (P : bool -> Type),
      (x == 1 -> P true)
   -> (x < 1  -> P false)
   -> P (is1 x).
intros; case_eq (is1 x); intro.
apply X; rewrite is1_true_eq; auto.
apply X0; apply Ult_neq_one.
apply neq_sym.
rewrite is1_false_eq; auto.
Defined.

Lemma is1_dec : forall x, {x == 1} + { x < 1 }.
intro; apply (is1_rec x (fun _ => {x == 1} + { x < 1 })); auto.
Defined.
*)

(** ** Definition of [Rp] with integer part and fractional part in [U] *)

Record Rp := mkRp { int:nat; frac:U }.

Bind Scope Rp_scope with Rp.
Delimit Scope Rp_scope with Rp.
Open Local Scope Rp_scope.


Lemma int_simpl : forall n x, int (mkRp n x) = n.
trivial.
Save.

Lemma frac_simpl : forall n x, frac (mkRp n x) = x.
trivial.
Save.

Lemma mkRp_eta : forall r, r = mkRp (int r) (frac r).
destruct r; trivial.
Save.
Hint Resolve mkRp_eta.

(** Avoid two representations of same value (n,1)==(S n,0) *)

Lemma orc_lt_eq1 : forall x, orc (x < 1) (x == 1) .
intros; apply Ule_lt_orc_eq; auto.
Save.

Lemma or_lt_eq1 : forall x, (x < 1) \/ (x == 1) .
intros; destruct (isle_dec U1 x); auto.
Save.

Definition if1 {A} (x:U) (o1 o2:A) : A := if isle_dec U1 x then o1 else o2.

Lemma if1_eq1 : forall {A} (x:U) (o1 o2:A), 1 <= x -> if1 x o1 o2 = o1.
unfold if1; intros; rewrite if_then; auto.
Save.

Lemma if1_lt1 : forall {A} (x:U) (o1 o2:A), x < 1 -> if1 x o1 o2 = o2.
unfold if1; intros; rewrite if_else; auto.
Save.

Hint Resolve @if1_eq1 @if1_lt1.

Lemma if1_elim : forall {A} (x:U) (o1 o2:A) (P:A -> Type),
      (x == 1 -> P o1) -> (x < 1 -> P o2) -> P (if1 x o1 o2).
unfold if1; intros; destruct (isle_dec U1 x); auto.
Defined.

Add Parametric Morphism {A} {o:ord A} : (if1 (A:=A)) with signature 
    Oeq ==> Oeq ==> Oeq ==> Oeq as if1_eq_compat_ord.
intros; apply (if1_elim x); intros.
rewrite if1_eq1; trivial.
transitivity x; auto.
rewrite if1_lt1; trivial.
rewrite <- H; auto.
Save.

Add Parametric Morphism {A} : (if1 (A:=A)) with signature 
    Oeq ==> eq ==> eq ==> eq as if1_eq_compat.
intros; apply (if1_elim x); intros.
rewrite if1_eq1; trivial.
transitivity x; auto.
rewrite if1_lt1; trivial.
rewrite <- H; auto.
Save.

Hint Immediate  if1_eq_compat if1_eq_compat_ord.

Definition floor (r : Rp) : nat := if1 (frac r) (S (int r)) (int r).

Definition decimal (r : Rp) : U := if1 (frac r) 0%U (frac r).

Lemma floor_int : forall x, frac x < 1%U -> floor x = int x.
intros; unfold floor; auto.
Save.
Hint Resolve floor_int.

Lemma floor_int_equiv : forall x, frac x < 1%U <-> floor x = int x.
split; auto.
unfold floor; apply (if1_elim (frac x)); intros; auto with arith.
exfalso; omega.
Save.

Lemma floor_mkRp_int n x : (x < 1)%U -> floor (mkRp n x) = n.
intros; apply floor_int; simpl; auto.
Save.
Hint Resolve floor_mkRp_int.

Lemma decimal_frac : forall x, frac x < 1%U -> decimal x = frac x.
unfold decimal; auto.
Save.
Hint Resolve decimal_frac.

Lemma decimal_frac_equiv : forall x, frac x < 1%U <-> decimal x = frac x.
split; auto.
unfold decimal; apply (if1_elim (frac x)); intros; auto with arith.
rewrite <- H0; auto.
Save.

Lemma decimal_mkRp_frac : forall n x, (x < 1)%U -> decimal (mkRp n x) = x.
intros; apply decimal_frac; auto.
Save.
Hint Resolve decimal_mkRp_frac.

Lemma floor_S_int : forall x, 1%U <= frac x -> floor x = S (int x).
intros; unfold floor; auto.
Save.
Hint Resolve floor_S_int.

Lemma floor_S_int_equiv : forall x, frac x == 1%U <-> floor x = S (int x).
split; auto.
unfold floor; apply (if1_elim (frac x)); intros; auto with arith.
exfalso; omega.
Save.

Lemma floor_mkRp_S_int n x : (x == 1)%U -> floor (mkRp n x) = S n.
intros; apply floor_S_int; simpl; auto.
Save.
Hint Resolve floor_mkRp_S_int.

Lemma decimal_0 : forall x, 1%U <= frac x -> decimal x = 0.
intros; unfold decimal; auto.
Save.
Hint Resolve decimal_0.

Lemma decimal_0_equiv : forall x, (frac x == 0 \/ frac x == 1%U) <-> decimal x == 0.
split.
destruct 1; auto.
rewrite decimal_frac; auto.
apply Ole_lt_trans with 0; auto.
unfold decimal; apply (if1_elim (frac x)); intros; auto with arith.
Save.

Lemma decimal_mkRp_0 : forall n x, (x == 1)%U -> decimal (mkRp n x) = 0.
intros; apply decimal_0; simpl; auto.
Save.
Hint Resolve decimal_mkRp_0.

Lemma decimal_lt1 : forall x, decimal x < 1%U.
unfold decimal; intros.
apply (if1_elim (frac x)); intros; auto with arith.
Save.
Hint Resolve decimal_lt1.

Lemma int_floor_le : forall x, int x <= floor x.
intros; destruct (or_lt_eq1 (frac x)); auto.
rewrite floor_int; auto.
rewrite floor_S_int; auto.
Save.
Hint Resolve int_floor_le.

Lemma decimal_frac_le : forall x, decimal x <= frac x.
intros; destruct (or_lt_eq1 (frac x)); auto.
rewrite decimal_0; auto.
Save.
Hint Resolve decimal_frac_le.


(** Morphism with Leibniz equality on the argument *)

Add Morphism frac  with signature eq ==> Oeq as frac_eq_compat.
auto.
Save.

Add Morphism int with signature eq ==> eq as int_eq_compat.
auto.
Save.

(** ** From [N] and [U] to [Rp] *)

Definition N2Rp n := mkRp n 0.
Definition U2Rp x := mkRp 0 x.

Coercion U2Rp : U >-> Rp.
Coercion N2Rp : nat >-> Rp.

Notation R0 := (N2Rp 0).
Notation R1 := (N2Rp 1).


Lemma floorN2Rp : forall n:nat, floor n = n.
intros; unfold floor; simpl.
rewrite if1_lt1; auto.
Save.

Lemma decimalN2Rp_eq : forall n:nat, decimal n = 0.
intros; unfold decimal; simpl.
rewrite if1_lt1; auto.
Save.

Hint Resolve decimalN2Rp_eq floorN2Rp.

Lemma decimalN2Rp : forall n:nat, decimal n == 0.
auto.
Save.
Hint Resolve decimalN2Rp.


Lemma floorU2Rp : forall x:U, x < 1 -> floor x = O.
intros; unfold floor; simpl.
rewrite if1_lt1; auto.
Save.

Lemma decimalU2Rp_eq : forall x:U, x < 1 -> decimal x = x.
intros; unfold decimal; simpl.
rewrite if1_lt1; auto.
Save.

Hint Resolve floorU2Rp decimalU2Rp_eq.

Lemma decimalU2Rp : forall x:U, x < 1 -> decimal x == x.
auto.
Save.
Hint Resolve decimalU2Rp.

Lemma floorU1_eq : forall x, x==1 -> floor x = 1%nat.
intros; rewrite floor_S_int; auto.
Save.
Hint Resolve floorU1_eq.

Lemma decimalU1_eq : forall x, x==1 -> decimal x = 0%U.
intros; rewrite decimal_0; auto.
Save.
Hint Resolve decimalU1_eq.

Lemma floorU1 : floor U1 = 1%nat.
auto.
Save.

Lemma decimalU1 : decimal U1 = 0%U.
auto.
Save.
Hint Resolve floorU1 decimalU1.


(** ** Order structure on [Rp] *)

Definition Rpeq r1 r2 := floor r1 = floor r2 /\ decimal r1 == decimal r2.

Definition Rple r1 r2 
    := (floor r1 < floor r2)%nat \/ (floor r1 = floor r2 /\ decimal r1 <= decimal r2).

 

Instance Rpord : ord Rp := {Oeq := Rpeq; Ole := Rple}.
split; unfold Rpeq, Rple; auto.
(* x <= y /\ y <= x <-> x == y *)
split.
(* x <= y /\ y <= x -> x == y *)
intros ([H1|(H11,H12)],[H2|(H21,H22)]); auto with arith.
casetype False; omega.
casetype False; omega.
casetype False; omega.
(* x == y -> x <= y /\ y <= x *)
intros (H1,H2).
rewrite H1; rewrite H2; auto.
(* Transitivity *)
intros r1 r2 r3 [H1|(H11,H12)] [H2|(H21,H22)].
left; transitivity (floor r2); auto.
rewrite H21 in H1; auto.
assert (floor r1 <= floor r3)%nat; try omega.
left; omega.
right; split; try omega.
transitivity (decimal r2); auto.
Defined.

Lemma Rpeq_simpl 
   : forall x y : Rp, (x == y) = (floor x = floor y /\ decimal x == decimal y).
trivial.
Save.

Lemma Rpeq_intro 
   : forall x y : Rp, floor x = floor y -> decimal x == decimal y -> x == y.
intros; rewrite Rpeq_simpl; auto.
Save.

Lemma Rple_simpl : forall x y : Rp, 
 (x <= y) = ((floor x < floor y)%nat \/ (floor x = floor y /\ decimal x <= decimal y)).
trivial.
Save.

Lemma Rple_intro_lt : forall x y : Rp, 
     (floor x < floor y)%nat -> x <= y.
intros; rewrite Rple_simpl; auto.
Save.

Lemma Rple_intro_eq : forall x y : Rp, 
     floor x = floor y -> decimal x <= decimal y -> x <= y.
intros; rewrite Rple_simpl; auto.
Save.

Hint Resolve Rpeq_intro Rple_intro_lt Rple_intro_eq.

Lemma Rple_intro_le_floor : forall x y : Rp, 
     (floor x <= floor y)%nat -> decimal x <= decimal y -> x <= y.
intros; case (le_lt_or_eq (floor x) (floor y)); auto.
Save.
Hint Immediate Rple_intro_le_floor.

Lemma Rplt_intro_lt_floor : forall x y : Rp, 
     (floor x < floor y)%nat -> x < y.
split; auto.
intros (H1,_); exfalso; omega.
Save.
Hint Resolve Rplt_intro_lt_floor.

Lemma Rplt_intro_lt_decimal : forall x y : Rp, 
     (floor x = floor y)%nat -> decimal x < decimal y -> x < y.
split; auto.
intros (H1,H2); absurd (decimal x == decimal y); auto.
Save.
Hint Resolve Rplt_intro_lt_decimal.

Add Morphism mkRp with signature eq ==> Oeq ==> Oeq 
as mkRp_eq_compat.
intros.
apply Rpeq_intro; unfold floor,decimal;
repeat rewrite frac_simpl;repeat rewrite int_simpl;
rewrite H; auto.
Save.

Add Morphism mkRp with signature le ==> Ole ==> Ole 
as mkRp_le_compat.
intros.
rewrite Rple_simpl; unfold floor,decimal;
repeat rewrite frac_simpl;repeat rewrite int_simpl.
apply (if1_elim x0); intros; auto with arith.
assert (1 <= y0) by (transitivity x0; auto).
repeat rewrite if1_eq1; auto.
case (le_lt_or_eq x y); intros; auto with arith.
apply (if1_elim y0); intros; auto with arith.
repeat rewrite if1_lt1; auto.
case (le_lt_or_eq x y); intros; auto with arith.
Save.

Hint Resolve mkRp_eq_compat mkRp_le_compat.

Lemma Rpeq_norm : forall n x, (x==1)%U -> mkRp n x == (S n).
intros n x H; rewrite H.
apply Rpeq_intro.
rewrite floorN2Rp; rewrite floor_S_int; auto.
rewrite decimalN2Rp; rewrite decimal_0; auto.
Save.
Hint Resolve Rpeq_norm.

Lemma Rpeq_norm1 : forall n,mkRp n 1 == (S n).
auto.
Save.
Hint Resolve Rpeq_norm1.

Add Morphism floor with signature Oeq ==> eq as floor_eq_compat.
intros x y; rewrite Rpeq_simpl; intuition.
Save.

Add Morphism floor with signature Ole ==> le as floor_le_compat.
intros r1 r2 [H1|(H11,H12)]; auto with arith.
rewrite H11; auto with arith.
Save.

Hint Resolve floor_eq_compat floor_le_compat.

Add Morphism decimal with signature Oeq ==> Oeq as decimal_eq_compat.
intros x y; rewrite Rpeq_simpl; intuition.
Save.

Lemma floor_decimal_mkRp_elim : forall n d (R : Rp -> Prop),
      (forall x, x == mkRp n d -> R x -> R (mkRp n d)) -> 
      (d < 1 -> R (mkRp n d)) -> (d == 1 -> R (S n)) ->  R (mkRp n d).
intros; destruct (or_lt_eq1 d); auto.
apply H with (S n); auto.
rewrite H2; auto.
Save.


Lemma floor_decimal_U2Rp_elim : forall (x:U) (R : nat -> U -> Prop),
      (x < 1 -> R 0%nat x) -> (x == 1 -> R 1%nat 0) ->  R (floor x) (decimal x).
intros; destruct (or_lt_eq1 x).
rewrite floorU2Rp; auto.
rewrite decimalU2Rp_eq; auto.
rewrite floorU1_eq; auto.
rewrite decimalU1_eq; auto.
Save.



Lemma decimal_eq_R0 : forall x, x == R0 -> decimal x == 0.
intros x H; rewrite H; trivial.
Save.

Lemma floor_eq_R0 : forall x, x == R0 -> floor x = O.
intros x H; rewrite H; trivial.
Save.

Hint Immediate floor_eq_R0 decimal_eq_R0.

Lemma floorR0 : floor R0 = O.
auto.
Save.

Lemma decimalR0 : decimal R0 == 0.
auto.
Save.
Hint Resolve floorR0 decimalR0.


Lemma floor_decimal : forall x, x == mkRp (floor x) (decimal x).
intro; apply Rpeq_intro.
rewrite (floor_int (mkRp (floor x) (decimal x))); simpl; auto.
rewrite (decimal_frac (mkRp (floor x) (decimal x))); simpl; auto.
Save.
Hint Resolve floor_decimal.


Add Morphism U2Rp with signature Oeq ==> Oeq 
as U2Rp_eq_compat.
intros; apply Rpeq_intro; unfold floor, decimal; simpl; auto.
Save.

Add Morphism U2Rp with signature Ole ==> Ole 
as U2Rp_le_compat.
intros; rewrite Rple_simpl.
unfold floor, decimal; simpl; auto.
apply (if1_elim x); intros; apply (if1_elim y); intros; auto.
right; split; trivial; rewrite if1_eq1; auto.
absurd (1 <= y); auto.
transitivity x; auto.
repeat rewrite if1_lt1; auto. 
Save.

Hint Resolve U2Rp_eq_compat U2Rp_le_compat.

Lemma eq_U2Rp_intro : forall (r:Rp) (x:U), 
      floor r = O -> decimal r == x -> r == U2Rp x.
intros; assert (x < 1)%U.
rewrite <- H0; trivial.
apply Rpeq_intro.
rewrite floorU2Rp; trivial.
rewrite decimalU2Rp; trivial.
Save.
Hint Resolve eq_U2Rp_intro.

Lemma U2Rp_eq_intro : forall (r:Rp) (x:U), 
      floor r = O -> decimal r == x -> U2Rp x == r.
intros; symmetry; auto.
Save.
Hint Resolve U2Rp_eq_intro.


Lemma U2Rp_le_simpl : forall x y : U, U2Rp x <= U2Rp y -> x <= y.
intros x y; rewrite Rple_simpl.
destruct (or_lt_eq1 y).
repeat rewrite (floorU2Rp y); repeat rewrite (decimalU2Rp y); auto.
destruct (or_lt_eq1 x).
repeat rewrite (floorU2Rp x); repeat rewrite (decimalU2Rp x); intuition.
rewrite H0; repeat rewrite floorU1; repeat rewrite decimalU1.
intuition.
rewrite H; auto.
Save.

Lemma U2Rp_eq_simpl : forall x y : U, U2Rp x == U2Rp y -> x == y.
intros; apply Ole_antisym; apply U2Rp_le_simpl; auto.
Save.

Hint Immediate U2Rp_le_simpl U2Rp_eq_simpl.

Add Morphism U2Rp with signature Olt ==> Olt 
as U2Rp_lt_compat.
intros; apply inj_strict_mon; auto.
Save.
Hint Resolve U2Rp_lt_compat.

Lemma U2Rp_lt_simpl : forall x y : U, U2Rp x < U2Rp y -> x < y.
intros x y (Hle,Hne); split; auto.
Save.
Hint Immediate U2Rp_lt_simpl.

Lemma U2Rp_eq_rewrite : forall x y : U, (x == y) <-> U2Rp x == U2Rp y.
split; auto.
Save.

Lemma U2Rp_le_rewrite : forall x y : U, (x <= y) <-> U2Rp x <= U2Rp y.
split; auto.
Save.

Lemma U2Rp_lt_rewrite : forall x y : U, (x < y) <-> U2Rp x < U2Rp y.
split; auto.
Save.

Add Morphism N2Rp with signature le ==> Ole 
as N2Rp_le_compat.
intros; apply Rple_intro_le_floor; repeat rewrite decimalN2Rp; 
repeat rewrite floorN2Rp; auto.
Save.
Hint Resolve N2Rp_le_compat.

Add Morphism N2Rp with signature eq ==> Oeq 
as N2Rp_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve N2Rp_eq_compat.

Lemma N2Rp_eq_simpl : forall a b, N2Rp a == N2Rp b -> a = b.
intros a b (Hi,Hf); auto.
repeat rewrite floorN2Rp in Hi; auto.
Save.
Hint Immediate N2Rp_eq_simpl.

Lemma N2Rp_eq_rewrite : forall a b, a = b <-> N2Rp a == N2Rp b.
Proof.
split; auto.
Qed.

Lemma decimal_0_eq_floor  : forall x:Rp, decimal x == 0 -> x == floor x.
intros x H; transitivity (mkRp (floor x) (decimal x)); auto.
rewrite H; auto.
Save.
Hint Resolve decimal_0_eq_floor.

Lemma floor_decimal_R0 : forall x:Rp, floor x = O -> decimal x == 0%U -> x == R0.
intros; transitivity (floor x); auto.
Save.
Hint Resolve floor_decimal_R0.


Add Morphism N2Rp with signature lt ==> Olt 
as N2Rp_lt_compat.
split; auto with arith.
intro H1; assert (x=y).
rewrite N2Rp_eq_rewrite; trivial.
auto with zarith.
Save.
Hint Resolve N2Rp_lt_compat.

Lemma N2Rp_le_simpl : forall (x y : nat), N2Rp x <= N2Rp y -> (x<=y)%nat.
intros a b [Hi|(He,Hf)]; repeat rewrite floorN2Rp in *; auto with zarith.
Save.
Hint Immediate N2Rp_le_simpl.

Lemma N2Rp_le_rewrite : forall (x y : nat), (x<=y)%nat <-> N2Rp x <= N2Rp y.
split; auto.
Save.

Lemma N2Rp_lt_simpl : forall (x y : nat), N2Rp x < N2Rp y -> (x<y)%nat.
intros a b (Hle,Hne).
rewrite <- N2Rp_eq_rewrite in Hne; rewrite <- N2Rp_le_rewrite in Hle; auto with zarith.
Save.
Hint Immediate N2Rp_lt_simpl.

Lemma N2Rp_lt_rewrite : forall (x y : nat), (x<y)%nat <-> N2Rp x < N2Rp y.
split; auto.
Save.

Lemma Rple_eq_floor_le_decimal 
   : forall r1 r2, r1 <= r2 -> (floor r1 = floor r2) -> decimal r1 <= decimal r2.
intros r1 r2; rewrite (Rple_simpl r1 r2); intuition.
Save.

Hint Immediate Rple_eq_floor_le_decimal.

Lemma Rple_N2Rp_mkRp : forall n m x, (n<=m)%nat -> N2Rp n <= mkRp m x.
intros; apply Rple_intro_le_floor; auto.
rewrite floorN2Rp; auto.
apply le_trans with (int {| int := m; frac := x |}); auto.
apply int_floor_le; auto.
rewrite decimalN2Rp; auto.
Save.
Hint Resolve Rple_N2Rp_mkRp.

Lemma U2Rp1_R1 : U2Rp 1 == R1.
apply Rpeq_intro.
rewrite floorU1;auto.
rewrite decimalU1;auto.
Save.
Hint Resolve U2Rp1_R1.

Lemma U2Rp_le_R1 : forall x:U, U2Rp x <= R1.
intros; transitivity (U2Rp 1); auto.
Save.
Hint Resolve U2Rp_le_R1.

(** ** Basic relations are classical *)

Lemma le_class : forall x y:nat, class (x <= y)%nat.
red; intros; omega.
Save.

Lemma eq_nat_class : forall x y:nat, class (x = y).
red; intros; case (eq_nat_dec x y); intros; auto with arith.
absurd (x <> y); auto with arith.
Save.

Hint Resolve le_class eq_nat_class.


Lemma Rple_class : forall x y: Rp, class (x <= y).
red; intros.
case (le_or_lt (floor x) (floor y)); intro.
case (le_lt_or_eq (floor x) (floor y)); intros; auto.
right.
apply (Ule_orc (decimal x) (decimal y)); intros; auto.
absurd (~ (x <= y)); auto.
absurd (~ (x <= y)); auto.
intro Hle.
absurd (floor x <= floor y)%nat; auto with zarith.
Save.
Hint Resolve Rple_class.

Lemma Rple_total : forall x y : Rp, orc (x <= y) (y <= x).
intros.
case (le_or_lt (floor x) (floor y)); intros; auto.
case (le_lt_or_eq (floor x) (floor y)); intros; auto.
apply (Ule_orc (decimal x) (decimal y)); intros; auto.
Save.
Hint Resolve Rple_total.

Lemma Rpeq_class : forall x y:Rp, class (x == y).
red; intros.
apply Ole_antisym; apply Rple_class; intuition.
Save.
Hint Resolve Rpeq_class.

Lemma Rple_zero : forall (x:Rp), R0 <= x.
intro; apply Rple_intro_le_floor.
rewrite floorN2Rp; auto with arith.
rewrite decimalN2Rp; auto.
Save.
Hint Resolve Rple_zero.


Lemma Rple_dec : forall x y: Rp, {x <= y} + { ~ x <= y}.
intros; case (le_lt_dec (floor x) (floor y)); intro.
case (le_lt_eq_dec _ _ l); intro; auto.
case (isle_lt_dec (decimal x) (decimal y)); intro; auto.
right; rewrite Rple_simpl; intuition.
case o; intuition.
right; rewrite Rple_simpl; intuition.
Defined.

Lemma Rpeq_dec : forall x y: Rp, {x == y} + { ~ x == y}.
intros; case (Rple_dec x y); intro; auto.
case (Rple_dec y x); intro; auto.
Defined.

Lemma Rple_lt_eq_dec : forall x y: Rp, x <= y -> {x < y} + {x == y}.
intros; case (Rpeq_dec x y); intro; auto.
Defined.

Lemma Rple_lt_dec : forall x y: Rp, {x <= y} + {y < x}.
intros; case (Rple_dec x y); intro; auto.
right; split; auto.
apply (Rple_total y x); intros; auto.
case n; trivial.
Defined.

Hint Resolve Rple_dec Rpeq_dec Rple_lt_eq_dec Rple_lt_dec.

Lemma Rp_lt_eq_lt_dec : forall x y:Rp, {x < y} + {x==y} + {y < x}.
intros; case (Rple_lt_dec x y); intro; auto.
Defined.
Hint Resolve Rp_lt_eq_lt_dec.

Lemma Rplt_neq_zero: forall x : Rp, ~ R0 == x -> R0 < x.
auto.
Save.

Lemma notRple_lt: forall x y : Rp, ~ y <= x -> x < y.
intros; case (Rple_lt_dec y x); intros; auto.
exfalso; auto.
Save.
Hint Immediate notRple_lt.

Lemma notRplt_le: forall x y : Rp, ~ x < y -> y <= x.
intros; case (Rple_lt_dec y x); intros; auto.
exfalso; auto.
Save.
Hint Immediate notRplt_le.

Lemma floor_le : forall x, N2Rp (floor x) <= x.
Proof.
  intros; apply Rple_intro_le_floor.
  rewrite floorN2Rp; auto.
  rewrite decimalN2Rp; auto.
Qed.
Hint Resolve floor_le.

Lemma floor_gt_S : forall x, x < S (floor x).
Proof.
  intros.
  apply Rplt_intro_lt_floor; rewrite floorN2Rp; auto with arith.
Qed.
Hint Resolve floor_gt_S.

Lemma Rplt_nat_floor : forall (x : Rp) (n:nat), x < n -> (floor x < n)%nat.
intros x n H; apply N2Rp_lt_simpl.
apply Ole_lt_trans with x; auto.
Save.
Hint Resolve Rplt_nat_floor.

Lemma Rplt1_floor : forall x:Rp, x < R1 -> floor x = O.
intros; assert (floor x < 1)%nat; auto with zarith.
Save.
Hint Resolve Rplt1_floor.

Lemma Rplt1_decimal : forall x:Rp, x < R1 -> x == decimal x.
intros; apply Rpeq_intro.
rewrite floorU2Rp; auto.
rewrite decimalU2Rp; auto.
Save.
Hint Resolve Rplt1_decimal.

Lemma Rplt_nat_floor_le : forall (x : Rp) (n:nat), N2Rp n <= x ->  (n <= floor x)%nat.
intros x n H; rewrite <- (floorN2Rp n); auto.
Save.
Hint Resolve Rplt_nat_floor_le.

Lemma Rplt_nat_floor_lt : forall (x : Rp) (n:nat), N2Rp (S n) < x ->  (n < floor x)%nat.
auto.
Save.
Hint Resolve Rplt_nat_floor_lt.

(** ** Addition [Rpplus] *)

(** *** Definition and basic properties *)
Definition Rpplus r1 r2 := 
    if isle ([1-](decimal r2)) (decimal r1) then mkRp (S (floor r1 + floor r2)) (decimal r1 & decimal r2)
    else mkRp (floor r1 + floor r2)%nat (decimal r1 + decimal r2).

Infix "+" := Rpplus : Rp_scope.

Lemma Rpplus_simpl : forall r1 r2 : Rp,
   r1 + r2 = if isle ([1-](decimal r2)) (decimal r1) then mkRp (S (floor r1 + floor r2)) (decimal r1 & decimal r2)
    else mkRp (floor r1 + floor r2)%nat (decimal r1 + decimal r2).
trivial.
Save.


Lemma Rpplus_rec : forall (r1 r2:Rp) (P : Rp -> Type),
   (decimal r1  < [1-]decimal r2 -> P (mkRp (floor r1 + floor r2)  (decimal r1 + decimal r2)))
-> ([1-]decimal r2 <= decimal r1  -> P (mkRp (S (floor r1 + floor r2))  (decimal r1 & decimal r2)))
-> P (r1 + r2).
intros; unfold Rpplus.
apply (isle_rec ([1-]decimal r2) (decimal r1)); intros; auto.
Defined.

Lemma Rpplus_simpl_ok : forall (r1 r2:Rp),
      decimal r1 < [1-]decimal r2 -> r1 + r2 = mkRp (floor r1 + floor r2)  (decimal r1 + decimal r2).
intros; unfold Rpplus.
rewrite (isle_false ([1-]decimal r2) (decimal r1)); auto.
Save.

Lemma Rpplus_simpl_over : forall (r1 r2:Rp),
     [1-]decimal r2 <= decimal r1 -> r1 + r2 = mkRp (1 + (floor r1 + floor r2))  (decimal r1 & decimal r2).
intros; unfold Rpplus.
rewrite (isle_true ([1-]decimal r2) (decimal r1)); auto.
Save.

Lemma Rpplus_simpl_ok2 : forall (r1 r2:Rp),
      decimal r1 <= [1-]decimal r2 -> r1 + r2 == mkRp (floor r1 + floor r2)  (decimal r1 + decimal r2).
intros r1 r2 H; apply (Ule_lt_orc_eq H); intros; auto.
rewrite Rpplus_simpl_ok; auto.
rewrite Rpplus_simpl_over.
rewrite H0.
rewrite Uinv_opp_left.
rewrite Rpeq_norm1.
assert ([1-] decimal r2 & decimal r2 == 0); auto.
rewrite H1.
apply Rpeq_intro.
rewrite floorN2Rp.
rewrite floor_int; auto.
repeat rewrite decimal_frac; auto.
rewrite H0; auto.
Save.

Lemma floor_Rpplus_simpl_ok : forall (r1 r2:Rp),
      decimal r1 < [1-]decimal r2 -> floor (r1 + r2) = (floor r1 + floor r2)%nat.
intros; rewrite Rpplus_simpl_ok; auto.
Save.

Lemma floor_Rpplus_simpl_over : forall (r1 r2:Rp),
      [1-]decimal r2 <= decimal r1 -> floor (r1 + r2) = (1 + (floor r1 + floor r2))%nat.
intros; rewrite Rpplus_simpl_over; auto.
Save.

Lemma decimal_Rpplus_simpl_ok : forall (r1 r2:Rp),
      decimal r1 < [1-]decimal r2 -> decimal (r1 + r2) == (decimal r1 + decimal r2)%U.
intros; rewrite Rpplus_simpl_ok; auto.
Save.

Lemma decimal_Rpplus_simpl_over : forall (r1 r2:Rp),
      [1-]decimal r2 <= decimal r1 -> decimal (r1 + r2) = (decimal r1 & decimal r2)%U.
intros; rewrite Rpplus_simpl_over; auto.
Save.

(** *** Properties of addition *)

Lemma Rpdiff_0_1 : ~ (R0 == R1).
intro; assert (0=1)%nat; auto with arith.
omega.
Save.
Hint Resolve Rpdiff_0_1.


Lemma Rpplus_sym : forall r1 r2 : Rp, r1 + r2 == r2 + r1.
intros x y.
apply (Rpplus_rec x y); intros.
rewrite Rpplus_simpl_ok; auto.
rewrite Uplus_sym; rewrite plus_comm; auto.
rewrite Rpplus_simpl_over; auto.
rewrite Uesp_sym; rewrite plus_comm; auto.
Save.
Hint Resolve Rpplus_sym.

Lemma Rpplus_zero_left : forall r : Rp, R0 + r == r.
intros; rewrite Rpplus_simpl_ok2; auto.
rewrite floorN2Rp; rewrite decimalN2Rp.
Usimpl; simpl plus; auto.
rewrite decimalN2Rp; auto.
Save.
Hint Resolve Rpplus_zero_left.

Lemma Rpplus_zero_right : forall r : Rp, r + R0 == r.
intros; rewrite Rpplus_sym; auto.
Save.
Hint Resolve Rpplus_zero_right.

Lemma Rpplus_assoc : forall r1 r2 r3 : Rp, r1 + (r2 + r3) == (r1 + r2) + r3.
intros; apply (Rpplus_rec r1 r2); intros; 
apply (Rpplus_rec r2 r3); intros.
apply (Ule_orc ([1-](decimal r2 + decimal r3)) (decimal r1)); intros; auto.
assert ([1-] decimal r3 <= decimal r1 + decimal r2)%U; auto.
transitivity ([1-] (decimal r2 + decimal r3) + decimal r2)%U; auto.
rewrite Rpplus_simpl_over.
rewrite Rpplus_simpl_over; auto.
repeat rewrite floor_mkRp_int; auto.
repeat rewrite decimal_mkRp_frac; auto.
apply mkRp_eq_compat; auto with arith.
rewrite decimal_mkRp_frac; auto.
rewrite decimal_mkRp_frac; auto.
rewrite Rpplus_simpl_ok.
rewrite Rpplus_simpl_ok; auto.
repeat rewrite decimal_mkRp_frac; auto.
repeat rewrite floor_mkRp_int; auto.
apply mkRp_eq_compat; auto with arith.
rewrite decimal_mkRp_frac; auto.
apply Olt_le_trans with ([1-] (decimal r2 + decimal r3) + decimal r2)%U; auto.
rewrite decimal_mkRp_frac; auto.
rewrite Rpplus_simpl_ok.
rewrite Rpplus_simpl_over.
repeat rewrite floor_mkRp_int; auto.
repeat rewrite decimal_mkRp_frac; auto.
apply mkRp_eq_compat; auto with arith.
omega.
rewrite decimal_mkRp_frac; auto.
transitivity (decimal r2); auto.
rewrite decimal_mkRp_frac; auto.
apply Olt_le_trans with ([1-] decimal r2); auto.
rewrite Rpplus_simpl_over.
rewrite Rpplus_simpl_ok.
repeat rewrite floor_mkRp_int; auto.
repeat rewrite decimal_mkRp_frac; auto.
apply mkRp_eq_compat; auto with arith.
omega.
rewrite decimal_mkRp_frac; auto.
rewrite decimal_mkRp_frac; auto.
transitivity ([1-]decimal r2); auto.
apply (Ule_orc ([1-](decimal r3)) (decimal r1 & decimal r2)); intros; auto.
assert ([1-](decimal r2 & decimal r3) <= decimal r1)%U; auto.
rewrite Uinv_esp_plus.
transitivity ([1-] decimal r2 + (decimal r1 & decimal r2))%U; auto.
rewrite Rpplus_simpl_over.
rewrite Rpplus_simpl_over.
repeat rewrite floor_mkRp_int; auto.
repeat rewrite decimal_mkRp_frac; auto.
apply mkRp_eq_compat; auto.
omega.
rewrite decimal_mkRp_frac; auto.
rewrite decimal_mkRp_frac; auto.
rewrite Rpplus_simpl_ok.
rewrite Rpplus_simpl_ok.
repeat rewrite floor_mkRp_int; auto.
repeat rewrite decimal_mkRp_frac; auto.
apply mkRp_eq_compat; auto.
omega.
symmetry; apply Uesp_plus_left_perm; auto.
rewrite decimal_mkRp_frac; auto.
rewrite decimal_mkRp_frac; auto.
apply Ole_lt_trans with ((decimal r1 & decimal r2) + [1-]decimal r2)%U; auto.
apply Olt_le_trans with ([1-] decimal r3 + [1-] decimal r2)%U; auto.
Save.
Hint Resolve Rpplus_assoc.

(** *** Link with operations on [nat] and [U] *)

Lemma N2Rp_plus : forall n m : nat, N2Rp n + N2Rp m == N2Rp (n+m)%nat.
intros; rewrite Rpplus_simpl_ok; repeat rewrite decimalN2Rp; auto.
apply mkRp_eq_compat; auto.
Save.

Lemma N2Rp_S_plus_1 : forall n, N2Rp (S n) == R1 + n.
intros; rewrite N2Rp_plus; auto.
Save.
Hint Resolve N2Rp_plus N2Rp_S_plus_1.

Lemma N2Rp_plus_left : forall (n:nat) (r:Rp), 
   N2Rp n + r == mkRp (n + floor r)%nat (decimal r).
intros; rewrite Rpplus_simpl_ok; repeat rewrite decimalN2Rp; 
repeat rewrite floorN2Rp; auto.
Save.

Lemma U2Rp_plus_0_1 : forall x y:U, x == 0 -> y == 1 -> U2Rp x + U2Rp y == U2Rp 1.
intros x y H0 H1; rewrite Rpplus_simpl_ok2; rewrite H0; rewrite H1.
transitivity R1; auto.
apply mkRp_eq_compat.
rewrite floorU1; rewrite floorU2Rp; auto.
rewrite decimalU1; rewrite decimalU2Rp; auto.
rewrite decimalU1; rewrite decimalU2Rp; auto.
Save.
Hint Immediate U2Rp_plus_0_1.

Lemma decimal_le : forall x:U, decimal x <= x.
intros; apply (orc_lt_eq1 x); auto; intros.
rewrite H; rewrite decimalU1; auto.
Save.
Hint Resolve decimal_le.

Lemma Uinv_decimal : forall x y : U, x <= [1-]y -> decimal x <= [1-]decimal y.
intros; apply (orc_lt_eq1 x); auto; intros.
rewrite decimalU2Rp; auto.
transitivity ([1-]y); auto.
rewrite H0; rewrite decimalU1; auto.
Save.
Hint Resolve Uinv_decimal.


Lemma U2Rp_plus_le : forall x y : U, x <= [1-]y ->
      U2Rp x + U2Rp y == U2Rp (x+y).
intros.
rewrite Rpplus_simpl_ok2; auto.
apply (floor_decimal_U2Rp_elim x); auto; intros.
apply (floor_decimal_U2Rp_elim y); auto; intros.
assert (x==0).
apply Ule_zero_eq; rewrite H; rewrite H1; auto.
rewrite H2; rewrite H1; repeat Usimpl; auto.
assert (y==0).
apply Ule_zero_eq; transitivity ([1-]x); auto.
rewrite H1; rewrite H0; repeat Usimpl; 
rewrite decimalU2Rp; auto.
rewrite floorU2Rp; auto.
Save.
Hint Resolve U2Rp_plus_le.

Lemma U2Rp_plus_ge : forall x y : U, [1-]y <= x ->
      U2Rp x + U2Rp y == mkRp 1%nat (x&y).
intros; apply (orc_lt_eq1 x); auto; intros.
apply (orc_lt_eq1 y); auto; intros.
rewrite Rpplus_simpl_over; auto.
repeat rewrite decimalU2Rp; auto.
repeat rewrite floorU2Rp; auto.
repeat rewrite decimalU2Rp; auto.
rewrite Rpplus_simpl_ok; auto.
rewrite H1; rewrite floorU1; rewrite decimalU1.
rewrite floorU2Rp; auto.
rewrite decimalU2Rp; repeat Usimpl; auto.
rewrite H1; rewrite decimalU1; auto.
rewrite Rpplus_simpl_ok2; auto.
rewrite H0; rewrite floorU1; rewrite decimalU1.
repeat Usimpl.
apply (orc_lt_eq1 y); auto; intros.
rewrite H1, floorU1, decimalU1; auto.
rewrite Rpeq_norm1; auto.
rewrite H0; rewrite decimalU1; auto.
Save.

Lemma Rpplus_floor_decimal : forall r:Rp, r == N2Rp (floor r) + U2Rp (decimal r).
intros; rewrite Rpplus_simpl_ok2.
repeat rewrite floorN2Rp;repeat rewrite decimalN2Rp.
repeat rewrite floorU2Rp; auto.
repeat rewrite decimalU2Rp; auto.
Usimpl.
transitivity (mkRp (floor r) (decimal r)); auto.
rewrite decimalU2Rp; auto.
rewrite decimalN2Rp; auto.
Save.

Lemma Rpplus_NU2Rp : forall n x, N2Rp n + U2Rp x == mkRp n x.
intros; rewrite Rpplus_simpl_ok2;
repeat rewrite floorN2Rp;repeat rewrite decimalN2Rp; repeat Usimpl; auto.
apply (floor_decimal_U2Rp_elim x); intros; repeat Usimpl; auto.
rewrite H; rewrite Rpeq_norm1.
apply mkRp_eq_compat; auto.
omega.
Save.
Hint Resolve N2Rp_plus N2Rp_plus_left U2Rp_plus_ge Rpplus_floor_decimal
 Rpplus_NU2Rp.

Lemma U2Rp_ge_R1 : forall x y:U, [1-]x <= y -> R1 <= U2Rp x + U2Rp y.
intros; rewrite U2Rp_plus_ge; auto.
Save.
Hint Resolve U2Rp_ge_R1.

Lemma Rple1_U2Rp : forall x:Rp, x <= R1 -> {y : U | x == U2Rp y}.
intros.
case (Rple_lt_eq_dec _ _ H); intro.
exists (decimal x); symmetry.
apply Rpeq_intro.
rewrite floorU2Rp; auto.
assert (floor x < 1)%nat; auto.
omega.
rewrite decimalU2Rp; auto.
exists 1%U; rewrite o; auto.
Defined.

Lemma U2Rp_plus : forall x y, U2Rp (x+y) <= x+y.
Proof.
  intros.
  apply (Ule_total x ([1-]y)); intros; auto. 
  rewrite U2Rp_plus_le; auto.
  transitivity R1; auto.
Qed.

Lemma Rple_floor : forall x : Rp, N2Rp (floor x) <= x.
intros; apply Rple_intro_eq; auto.
Save.
Hint Resolve Rple_floor.

Lemma Rple_S_N2Rp : forall (r:Rp) (n:nat), r <= n -> r <= S n.
intros; transitivity (N2Rp n); auto.
Save.
Hint Immediate Rple_S_N2Rp.

Lemma Rplt_S_N2Rp: forall (r:Rp) (n:nat), r <= n -> r < S n.
intros; apply Ole_lt_trans with (N2Rp n); auto.
Save.
Hint Immediate Rplt_S_N2Rp.

(** *** Monotonicity ans stability *)

Instance Rpplus_mon_right : forall r, monotonic (Rpplus r).
red; intros.
apply (Rpplus_rec r x); intros; apply (Rpplus_rec r y); intros.
destruct H as [Hlt|(Heq,Hle)].
apply Rple_intro_lt.
repeat rewrite floor_mkRp_int; auto with arith.
apply Rple_intro_eq; repeat rewrite floor_mkRp_int; auto.
repeat rewrite decimal_mkRp_frac; auto.
transitivity (S (floor r + floor y)); auto.
apply Rple_intro_lt; rewrite floor_mkRp_int, floorN2Rp; auto with arith.
assert (decimal y < decimal x).
apply Uinv_lt_simpl; apply Ole_lt_trans with (decimal r); auto.
assert (floor x < floor y)%nat.
destruct H as [Hlt|(Heq,Hle)]; auto.
absurd (decimal x <= decimal y); auto.
apply Rple_intro_le_floor; auto.
repeat rewrite floor_mkRp_int; auto.
omega.
repeat rewrite decimal_mkRp_frac; auto.
transitivity (decimal r); auto.
destruct H as [Hlt|(Heq,Hle)]; auto.
apply Rple_intro_lt; auto.
repeat rewrite floor_mkRp_int; auto.
omega.
rewrite Heq; apply Rple_intro_eq; auto.
repeat rewrite floor_mkRp_int; auto.
repeat rewrite decimal_mkRp_frac; auto.
Save.
Hint Resolve Rpplus_mon_right.

Instance Rpplus_monotonic2 : monotonic2 Rpplus.
apply monotonic2_sym; auto.
Save.
Hint Resolve Rpplus_monotonic2.

Add Morphism Rpplus with signature Oeq ==> Oeq ==> Oeq
as Rpplus_eq_compat.
intros; apply (monotonic2_stable2 Rpplus); auto.
Save.

Add Morphism Rpplus with signature Ole ==> Ole ==> Ole
as Rpplus_le_compat.
intros; apply Rpplus_monotonic2; auto.
Save.
Hint Immediate Rpplus_eq_compat Rpplus_le_compat.

Lemma Rpplus_le_compat_left 
   : forall x y z : Rp, x <= y -> x + z <= y + z.
auto.
Save.

Lemma Rpplus_le_compat_right 
   : forall x y z : Rp, y <= z -> x + y <= x + z.
auto.
Save.
Hint Resolve Rpplus_le_compat_left Rpplus_le_compat_right.

Lemma Rpplus_eq_compat_left 
   : forall x y z : Rp, x == y -> x + z == y + z.
auto.
Save.

Lemma Rpplus_eq_compat_right 
   : forall x y z : Rp, y == z -> x + y == x + z.
auto.
Save.
Hint Resolve Rpplus_eq_compat_left Rpplus_eq_compat_right.

Instance Rpplus_mon2 : monotonic2 Rpplus.
red; intros; apply Rpplus_le_compat; auto.
Save.

Definition RpPlus : Rp -m> Rp -m> Rp := mon2 Rpplus.

Lemma Rple_plus_right : forall r1 r2, r1 <= r1 + r2.
intros; transitivity (r1 + R0); auto.
Save.
Hint Resolve Rple_plus_right.

Lemma Rple_plus_left : forall r1 r2, r2 <= r1 + r2.
intros; rewrite Rpplus_sym; auto.
Save.
Hint Resolve Rple_plus_left.

Lemma Rpplus_perm3: forall x y z : Rp, x + (y + z) == z + (x + y).
intros; rewrite Rpplus_assoc; auto.
Save.

Lemma Rpplus_perm2: forall x y z : Rp, x + (y + z) == y + (x + z).
intros; repeat rewrite Rpplus_assoc; apply Rpplus_eq_compat; auto.
Save.
Hint Resolve Rpplus_perm2 Rpplus_perm3.


(** ** Substraction [Rpminus] *)

(** *** Definition and basic properties *)
Definition Rpminus r1 r2 := 
   match nat_compare (floor r1) (floor r2) with
    Lt => R0
  | Eq => mkRp 0 (decimal r1 - decimal r2)
  | Gt => if isle (decimal r2) (decimal r1) 
          then mkRp (floor r1 - floor r2) (decimal r1 - decimal r2) 
          else mkRp (pred (floor r1 - floor r2)) (decimal r1 + [1-]decimal r2) 
   end.

Infix "-" := Rpminus : Rp_scope.

Lemma Rpminus_rec : forall (r1 r2:Rp) (P : Rp -> Type),
   ( (floor r1 < floor r2)%nat -> P R0 )
-> ( floor r1 = floor r2 -> P (mkRp 0 (decimal r1 - decimal r2)))
-> ( (floor r2 < floor r1)%nat -> decimal r2 <= decimal r1 
      -> P (mkRp (floor r1 - floor r2)  (decimal r1 - decimal r2)))
-> ( (floor r2 < floor r1)%nat -> decimal r1 < decimal r2  
      -> P (mkRp (pred (floor r1 - floor r2)) (decimal r1 + [1-]decimal r2)))
-> P (r1 - r2).
intros; unfold Rpminus.
elim (nat_compare_specT (floor r1) (floor r2)); intros; auto.
apply (isle_rec (decimal r2) (decimal r1)); intros; auto.
Defined.

(** Useful lemma *)
Lemma decimal_minus_lt1 : forall (x:Rp) (y:U), ((decimal x) - y < 1)%U.
intros; apply Ole_lt_trans with (decimal x); auto.
Save.
Hint Resolve decimal_minus_lt1.

Lemma Rpminus_simpl_lt : forall (r1 r2:Rp),
      (floor r1 < floor r2)%nat -> r1 - r2 = R0.
intros r1 r2; rewrite nat_compare_lt; unfold Rpminus; intro.
rewrite H; auto.
Save.

Lemma Rpminus_simpl_eq : forall (r1 r2:Rp),
      floor r1 = floor r2 -> r1 - r2 = U2Rp (decimal r1 - decimal r2).
intros r1 r2; rewrite <- nat_compare_eq_iff; unfold Rpminus; intro.
rewrite H; auto.
Save.

Lemma Rpminus_simpl_gt : forall (r1 r2:Rp),
   decimal r2 <= decimal r1  -> (floor r2 < floor r1)%nat -> 
   r1 - r2 = mkRp (floor r1 - floor r2) (decimal r1 - decimal r2).
intros r1 r2 H1 H2.
assert (nat_compare (floor r1) (floor r2) = Gt).
rewrite <- nat_compare_gt; auto with arith.
unfold Rpminus; rewrite H; auto.
rewrite (isle_true (decimal r2) (decimal r1)); auto.
Save.

Lemma Rpminus_simpl_gt2 : forall (r1 r2:Rp),
   decimal r2 <= decimal r1  -> (floor r2 <= floor r1)%nat -> 
   r1 - r2 = mkRp (floor r1 - floor r2) (decimal r1 - decimal r2).
intros r1 r2 H1 H2.
destruct (le_lt_or_eq _ _ H2).
apply Rpminus_simpl_gt; auto.
rewrite Rpminus_simpl_eq; auto.
replace (floor r1 - floor r2)%nat with O; try omega; auto.
Save.


Lemma Rpminus_simpl_gtc : forall (r1 r2:Rp),
   decimal r1 < decimal r2 -> (floor r2 < floor r1)%nat -> 
   r1 - r2 = mkRp (pred (floor r1 - floor r2)) (decimal r1 + [1-]decimal r2).
intros r1 r2 H1 H2.
assert (nat_compare (floor r1) (floor r2) = Gt).
rewrite <- nat_compare_gt; auto with arith.
unfold Rpminus; rewrite H; auto.
rewrite (isle_false (decimal r2) (decimal r1)); auto.
Save.

Lemma Rpminus_simpl_gtc2 : forall (r1 r2:Rp),
   decimal r1 <= decimal r2 -> (floor r2 < floor r1)%nat -> 
   r1 - r2 == mkRp (pred (floor r1 - floor r2)) (decimal r1 + [1-]decimal r2).
intros r1 r2 H1 H2.
apply (Ueq_orc (decimal r1) (decimal r2)); intros; auto.
rewrite Rpminus_simpl_gt; auto.
rewrite H; repeat Usimpl.
rewrite (Rpeq_norm1 (pred (floor r1 - floor r2))); auto.
apply mkRp_eq_compat; auto with arith.
omega.
rewrite Rpminus_simpl_gtc; auto.
Save.

Hint Resolve Rpminus_simpl_lt Rpminus_simpl_eq Rpminus_simpl_gt Rpminus_simpl_gt2 Rpminus_simpl_gtc Rpminus_simpl_gtc2.

(** *** Algebraic properties of [Rpminus] *)

Lemma Rpminus_le_zero: forall r1 r2 : Rp, r1 <= r2 -> (r1 - r2) == R0.
intros x y [Hlt|(Heq,Hf)]; auto.
rewrite Rpminus_simpl_eq; unfold U2Rp; auto.
apply mkRp_eq_compat; auto.
Save.


Lemma Rpminus_zero_right: forall x : Rp, x - R0 == x.
intros; unfold N2Rp.
case (zerop (floor x)); intro.
rewrite Rpminus_simpl_eq; repeat rewrite floor_mkRp_int; auto.
repeat rewrite decimal_mkRp_frac; auto.
rewrite Rpminus_simpl_gt; repeat rewrite floor_mkRp_int; auto.
repeat rewrite decimal_mkRp_frac; auto.
Usimpl; apply Rpeq_intro; auto.
rewrite floor_mkRp_int; auto.
omega.
rewrite decimal_mkRp_frac; auto.
Save.
Hint Resolve Rpminus_zero_right Rpminus_le_zero.

(** *** Monotonicity *)

Lemma Rpminus_le_compat_left: forall x y z : Rp, x <= y -> (x - z) <= (y - z).
intros x y z [Hlt|(Heq,Hle)].
apply (Rpminus_rec x z); intros; auto.
case (isle_dec (decimal z) (decimal y)); intro.
rewrite Rpminus_simpl_gt; auto; try omega.
apply Rple_intro_lt; repeat rewrite floor_mkRp_int; auto; try omega.
assert (decimal y < decimal z); auto.
rewrite Rpminus_simpl_gtc; auto; try omega.
apply Rple_intro_le_floor; repeat rewrite floor_mkRp_int; auto.
repeat rewrite decimal_mkRp_frac; auto.
transitivity ([1-]decimal z); auto.
case (isle_dec (decimal z) (decimal y)); intro.
rewrite Rpminus_simpl_gt; auto; try omega.
repeat rewrite decimal_mkRp_frac; auto.
apply Rple_intro_lt; repeat rewrite floor_mkRp_int; auto; try omega.
assert (decimal y < decimal z); auto.
rewrite Rpminus_simpl_gtc; auto; try omega.
apply Rple_intro_le_floor; repeat rewrite floor_mkRp_int; auto; try omega.
repeat rewrite decimal_mkRp_frac; auto.
transitivity ([1-] decimal z); auto.
case (isle_dec (decimal z) (decimal y)); intro.
rewrite Rpminus_simpl_gt; auto; try omega.
apply Rple_intro_lt; repeat rewrite floor_mkRp_int; auto; try omega.
assert (decimal y < decimal z); auto.
rewrite Rpminus_simpl_gtc; auto; try omega.
apply Rple_intro_lt; repeat rewrite floor_mkRp_int; auto; try omega.
apply (Rpminus_rec x z); intros; auto.
rewrite Rpminus_simpl_eq; try omega; auto.
(* change (U2Rp (decimal x - decimal z) <= (decimal y - decimal z)%U); auto.*)
rewrite Rpminus_simpl_gt; auto; try omega.
apply Rple_intro_eq; repeat rewrite floor_mkRp_int; auto; try omega.
repeat rewrite decimal_mkRp_frac; auto.
transitivity (decimal x); auto.
case (isle_dec (decimal z) (decimal y)); intro.
rewrite Rpminus_simpl_gt; auto; try omega.
apply Rple_intro_lt; repeat rewrite floor_mkRp_int; auto; try omega.
rewrite Rpminus_simpl_gtc; auto; try omega.
assert (decimal y < decimal z); auto.
apply Rple_intro_eq; repeat rewrite floor_mkRp_int; auto; try omega.
repeat rewrite decimal_mkRp_frac; auto.
Save.
Hint Resolve Rpminus_le_compat_left.

Lemma Rpminus_eq_compat_left:
  forall x y z : Rp, x == y -> (x - z) == (y - z).
intros; apply Ole_antisym; auto.
Save.


Lemma Rpminus_le_compat_right: forall x y z : Rp, y <= z -> (x - z) <= (x - y).
intros x y z [Hlt|(Heq,Hle)].
apply (Rpminus_rec x y); intros; auto.
rewrite Rpminus_simpl_lt; auto; try omega.
rewrite Rpminus_simpl_lt; auto; try omega.
apply (Rpminus_rec x z); intros; auto.
apply Rple_intro_lt; repeat rewrite floor_mkRp_int; auto; try omega.
apply Rple_intro_lt; repeat rewrite floor_mkRp_int; auto; try omega.
apply Rple_intro_lt; repeat rewrite floor_mkRp_int; auto; try omega.
apply (Rpminus_rec x z); intros; auto.
apply Rple_intro_le_floor; repeat rewrite floor_mkRp_int; auto; try omega.
repeat rewrite decimal_mkRp_frac; auto.
transitivity (decimal x); auto.
apply Rple_intro_le_floor; repeat rewrite floor_mkRp_int; auto; try omega.
repeat rewrite decimal_mkRp_frac; auto.
transitivity (decimal x); auto.
apply Rple_intro_lt; repeat rewrite floor_mkRp_int; auto; try omega.
apply (Rpminus_rec x y); intros; auto.
rewrite Rpminus_simpl_lt; auto; try omega.
rewrite Rpminus_simpl_eq; repeat rewrite floor_mkRp_int; auto; try omega.
case (isle_dec (decimal z) (decimal x)); intro.
rewrite Rpminus_simpl_gt; auto; try omega.
apply Rple_intro_eq; repeat rewrite floor_mkRp_int; auto; try omega.
repeat rewrite decimal_mkRp_frac; auto.
assert (decimal x < decimal z); auto.
rewrite Rpminus_simpl_gtc; auto; try omega.
apply Rple_intro_lt; repeat rewrite floor_mkRp_int; auto; try omega.
assert (decimal x < decimal z).
apply Olt_le_trans with (decimal y); auto.
rewrite Rpminus_simpl_gtc; auto; try omega.
apply Rple_intro_eq; repeat rewrite floor_mkRp_int; auto; try omega.
repeat rewrite decimal_mkRp_frac; auto.
Save.
Hint Resolve Rpminus_le_compat_right.

Lemma Rpminus_eq_compat_right:
  forall x y z : Rp, y == z -> (x - y) == (x - z).
intros; apply Ole_antisym; auto.
Save.

Hint Resolve Rpminus_eq_compat_left Rpminus_eq_compat_right.

Lemma Rpminus_eq_compat:
  forall x y z t : Rp, x == y -> z == t -> (x - z) == (y - t).
intros; transitivity (y - z); auto.
Save.

Lemma Rpminus_le_compat:
  forall x y z t : Rp, x <= y -> t <= z  -> (x - z) <= (y - t).
intros; transitivity (y - z); auto.
Save.

Hint Immediate Rpminus_eq_compat Rpminus_le_compat.

Add Morphism Rpminus with signature Oeq ==> Oeq ==> Oeq
   as Rpminus_eq_morphism.
auto.
Save.

Add Morphism Rpminus with signature Ole ==> Ole --> Ole
   as Rpminus_le_morphism.
auto.
Save.

Instance Rpminus_mon2 : monotonic2 (o2:=Iord Rp) Rpminus.
red; intros; auto.
Save.
Hint Resolve Rpminus_mon2.

Definition RpMinus : Rp -m> Rp --m> Rp := mon2 (o2:=Iord Rp) Rpminus.

Lemma U2Rp_minus : forall x y:U, U2Rp x - U2Rp y == U2Rp (x - y).
intros; apply (Ule_orc x y); auto; intros.
rewrite Uminus_le_zero; auto.
assert (y < x); auto.
assert (y < 1); auto.
apply Olt_le_trans with x; auto.
apply (floor_decimal_U2Rp_elim x (fun f d => U2Rp x - U2Rp y == U2Rp (x - y))); intros.
rewrite Rpminus_simpl_eq.
repeat rewrite decimalU2Rp; auto.
repeat rewrite floorU2Rp; auto.
rewrite H2.
rewrite Rpminus_simpl_gtc2; auto.
rewrite floorU1; rewrite decimalU1.
rewrite decimalU2Rp; auto.
rewrite floorU2Rp; auto.
simpl minus; simpl pred; Usimpl.
apply U2Rp_eq_compat; auto.
rewrite decimalU1; auto.
rewrite floorU1; rewrite floorU2Rp; auto.
Save.

Lemma N2Rp_minus : forall x y:nat, N2Rp x - N2Rp y == N2Rp (x - y).
intros; destruct (le_or_lt x y).
rewrite Rpminus_le_zero; auto.
apply N2Rp_eq_compat; omega.
rewrite Rpminus_simpl_gt2; repeat rewrite floorN2Rp; repeat rewrite decimalN2Rp; auto.
Usimpl.
apply N2Rp_eq_compat; omega.
omega.
Save.

(** *** More algebraic properties *)

Lemma Rpminus_zero_left: forall r : Rp, (R0 - r) == R0.
auto.
Save.
Hint Resolve Rpminus_zero_left.

Lemma Rpminus_eq: forall r : Rp, (r - r) == R0.
auto.
Save.
Hint Resolve Rpminus_eq.

Lemma Rpplus_minus_simpl_right : forall r1 r2 : Rp, (r1 + r2 - r2) == r1.
intros; transitivity (mkRp (floor r1) (decimal r1)); auto.
apply (Rpplus_rec r1 r2); intros.
rewrite Rpminus_simpl_gt2; repeat rewrite floor_mkRp_int; repeat rewrite decimal_mkRp_frac; auto with arith.
apply mkRp_eq_compat; try omega; auto.
rewrite <- Uplus_minus_assoc_right; auto.
rewrite Uminus_le_zero; auto.
apply Uinv_le_perm_right; auto.
rewrite Rpminus_simpl_gtc2; repeat rewrite floor_mkRp_int; repeat rewrite decimal_mkRp_frac; auto with arith.
apply mkRp_eq_compat; try omega; auto.
Save.
Hint Resolve Rpplus_minus_simpl_right.

Lemma Rpplus_minus_simpl_left : forall r1 r2 : Rp, (r1 + r2 - r1) == r2.
intros; rewrite Rpplus_sym; auto.
Save.
Hint Resolve Rpplus_minus_simpl_left.

Lemma Rpminus_plus_simpl : forall r1 r2 : Rp, r2 <= r1 -> (r1 - r2 + r2) == r1.
intros; apply (Rpminus_rec r1 r2); intros.
rewrite Rpplus_zero_left; apply Ole_antisym; auto.
assert (decimal r2 <= decimal r1).
apply Rple_eq_floor_le_decimal; auto.
rewrite Rpplus_simpl_ok2; repeat rewrite floor_mkRp_int; repeat rewrite decimal_mkRp_frac; try omega; auto.
transitivity (mkRp (floor r1) (decimal r1)); auto.
rewrite Rpplus_simpl_ok2; repeat rewrite floor_mkRp_int; repeat rewrite decimal_mkRp_frac; try omega; auto.
transitivity (mkRp (floor r1) (decimal r1)); auto.
apply mkRp_eq_compat; try omega; auto.
rewrite Rpplus_simpl_over; repeat rewrite floor_mkRp_int; repeat rewrite decimal_mkRp_frac; try omega; auto.
transitivity (mkRp (floor r1) (decimal r1)); auto.
apply mkRp_eq_compat; try omega; auto.
Save.
Hint Resolve Rpminus_plus_simpl.

Lemma Rpminus_plus_simpl_le : forall r1 r2 : Rp, r1 <= r1 - r2 + r2.
intros; apply (Rple_total r1 r2); intros; auto.
setoid_replace (r1 - r2) with R0; auto.
transitivity r2; auto.
rewrite Rpminus_plus_simpl; auto.
Save.
Hint Resolve Rpminus_plus_simpl_le.

Lemma Rpplus_le_simpl_right:
  forall x y z : Rp, (x + z) <= (y + z) -> x <= y.
intros; rewrite <- (Rpplus_minus_simpl_right x z); rewrite <- (Rpplus_minus_simpl_right y z).
rewrite H; auto.
Save.

Lemma Rpplus_le_simpl_left:
  forall x y z : Rp, (x + y) <= (x + z) -> y <= z.
intros x y z; rewrite (Rpplus_sym x y); rewrite (Rpplus_sym x z).
intros; apply Rpplus_le_simpl_right with x; auto.
Save.

Lemma Rpplus_eq_simpl_right:
  forall x y z : Rp, (x + z) == (y + z) -> x == y.
intros; rewrite <- (Rpplus_minus_simpl_right x z); rewrite <- (Rpplus_minus_simpl_right y z).
rewrite H; auto.
Save.

Lemma Rpplus_eq_simpl_left:
  forall x y z : Rp, (x + y) == (x + z) -> y == z.
intros x y z; rewrite (Rpplus_sym x y); rewrite (Rpplus_sym x z).
intros; apply Rpplus_eq_simpl_right with x; auto.
Save.

Lemma Rpplus_eq_perm_left: forall x y z : Rp, x == y + z -> x - y == z.
intros; assert (y <= x).
rewrite H; auto.
apply Rpplus_eq_simpl_right with y.
rewrite Rpminus_plus_simpl; auto.
rewrite H; trivial.
Save.
Hint Immediate Rpplus_eq_perm_left.

Lemma Rpplus_eq_perm_right: forall x y z : Rp, x + z == y  -> x == y - z.
intros; symmetry ; apply Rpplus_eq_perm_left; auto.
rewrite <- H; trivial.
Save.
Hint Immediate Rpplus_eq_perm_right.

Lemma Rpplus_le_perm_left: forall x y z : Rp, x <= y + z -> x - y <= z.
intros; rewrite H; auto.
Save.
Hint Immediate Rpplus_le_perm_left.

Lemma Rpplus_le_perm_right: forall x y z : Rp, x + z <= y -> x <= y - z.
intros; rewrite <- H; auto.
Save.
Hint Immediate Rpplus_le_perm_right.

Lemma Rpminus_plus_perm_right:
  forall x y z : Rp, y <= x -> y <= z -> x - y + z == x + (z - y).
intros; apply Rpplus_eq_simpl_right with y; auto.
transitivity (x + z).
rewrite Rpplus_sym.
repeat rewrite Rpplus_assoc.
apply Rpplus_eq_compat; auto.
rewrite Rpplus_sym; auto.
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; auto.
symmetry; auto.
Save.
Hint Resolve Rpminus_plus_perm_right.

Lemma Rpminus_plus_perm : forall x y z : Rp, y <= x -> x - y + z == (x + z) - y.
intros; apply Rpplus_eq_simpl_right with y; auto.
transitivity (x + z).
rewrite Rpplus_sym.
repeat rewrite Rpplus_assoc.
apply Rpplus_eq_compat; auto.
rewrite Rpplus_sym; auto.
rewrite Rpminus_plus_simpl; auto.
transitivity x; auto.
Save.
Hint Resolve Rpminus_plus_perm.

Lemma Rpminus_assoc_right : forall x y z, y <= x -> z <= y -> x - (y - z) == x - y + z.
intros; apply Rpplus_eq_perm_left.
rewrite Rpminus_plus_perm; auto.
rewrite Rpplus_assoc.
rewrite (Rpplus_sym y (x-y)); auto.
rewrite Rpminus_plus_simpl; auto.
Save.
Hint Resolve Rpminus_assoc_right.

Lemma Rpplus_minus_assoc : forall x y z, z <= y -> x + y - z == x + (y - z).
intros; rewrite (Rpplus_sym x (y - z)).
rewrite (Rpplus_sym x y); auto.
symmetry; auto.
Save.
Hint Resolve Rpplus_minus_assoc.

Lemma Rpminus_zero_le: forall r1 r2 : Rp, (r1 - r2) == R0 -> r1 <= r2.
intros; transitivity (r1 - r2 + r2); auto.
rewrite H; auto.
Save.
Hint Immediate Rpminus_zero_le.


Lemma U2Rp_Uesp : forall x y, [1-]x <= y -> U2Rp (x & y) == U2Rp x + U2Rp y - R1.
intros; rewrite  U2Rp_plus_ge; auto.
rewrite <- Rpplus_NU2Rp; auto.
Save.
Hint Resolve U2Rp_Uesp.

Lemma Rpminus_le_perm_right:
  forall x y z : Rp, z <= y -> x <= y - z -> x + z <= y.
intros.
rewrite H0; auto.
Save.
Hint Resolve Rpminus_le_perm_right.

Lemma Rpminus_le_perm_left:
  forall x y z : Rp, x - y <= z -> x <= z + y.
intros.
rewrite <- H; auto.
Save.
Hint Resolve Rpminus_le_perm_left.

Lemma Rpminus_eq_perm_right:
  forall x y z : Rp, z <= y -> x == y - z -> x + z == y.
intros.
rewrite H0; auto.
Save.
Hint Resolve Rpminus_eq_perm_right.

Lemma Rpminus_eq_perm_left:
  forall x y z : Rp, y <= x -> x - y == z -> x == z + y.
intros.
rewrite <- H0; symmetry; auto.
Save.
Hint Resolve Rpminus_eq_perm_left.

Lemma Rpplus_lt_compat_left : forall x y z : Rp, x < y -> x + z < y + z.
intros x y z (H1,H2); split; auto.
intro H; apply H2.
apply Rpplus_eq_simpl_right with z; auto.
Save.

Lemma Rpplus_lt_compat_right : forall x y z : Rp, y < z -> x + y < x + z.
intros x y z (H1,H2); split; auto.
intro H; apply H2.
apply Rpplus_eq_simpl_left with x; auto.
Save.

Lemma U2Rp_Uinv : forall x, U2Rp ([1-]x) == R1 - U2Rp x.
Proof.
  intro x.
  apply Rpplus_eq_perm_right.
  rewrite <- U2Rp1_R1; rewrite U2Rp_plus_le; auto.
Qed.
Hint Resolve U2Rp_Uinv.

Lemma Rpplus_Uinv_le : forall x y : U, x + y <= R1 -> x <= [1-]y.
intros; apply U2Rp_le_simpl.
rewrite U2Rp_Uinv; auto.
Save.
Hint Immediate Rpplus_Uinv_le.

Lemma Rpminus_lt_compat_right: 
    forall x y z : Rp, z <= x -> y < z -> x - z < x - y.
intros; split; auto.
intro.
assert (x-z == (x-z)+(z-y)).
rewrite <- Rpminus_assoc_right; auto.
rewrite (Rpminus_assoc_right z); auto.
rewrite Rpminus_eq.
rewrite Rpplus_zero_left; auto.
assert (R0 == z - y).
apply Rpplus_eq_simpl_left with (x-z); auto.
rewrite Rpplus_zero_right; auto.
assert (z <= y).
apply Rpminus_zero_le; auto.
apply (Olt_notle y z);auto.
Save.
Hint Resolve Rpminus_lt_compat_right.


Lemma Rpminus_lt_compat_left: forall x y z : Rp, z <= x -> x < y -> x - z < y - z.
intros; split; auto.
intro.
assert (x == y).
rewrite <- (Rpminus_plus_simpl x z); auto.
rewrite <- (Rpminus_plus_simpl y z); auto.
transitivity x; auto.
destruct H0; auto.
Save.
Hint Resolve Rpminus_lt_compat_left.

Lemma Rpminus_lt_0 : forall x y : Rp, x < y -> R0 < y - x.
intros; apply Olt_eq_compat with (x-x) (y-x); auto.
Save.
Hint Immediate Rpminus_lt_0.


Lemma Rpminus_Sn_R1 : forall (n:nat), N2Rp (S n) - R1 == n.
intros; rewrite N2Rp_minus; auto with arith.
apply N2Rp_eq_compat; auto with zarith.
Save.
Hint Resolve Rpminus_Sn_R1.

Lemma Rpminus_Sn_1 : forall (n:nat), N2Rp (S n) - 1%U == n.
intros; transitivity (N2Rp (S n) - R1); auto.
Save.
Hint Resolve Rpminus_Sn_1.

Lemma Rpminus_assoc_left : forall x y z : Rp, x - y - z == x - (y + z).
intros; apply (Rple_total x (y+z)); auto; intros.
rewrite Rpminus_le_zero; auto.
rewrite Rpminus_le_zero; auto.
apply Rpplus_eq_perm_left.
rewrite Rpplus_sym.
rewrite <- Rpminus_assoc_right; auto.
Save.
Hint Resolve Rpminus_assoc_left.

Lemma Rpminus_perm : forall x y z : Rp, x - y - z == x - z - y.
intros; transitivity (x - (y + z)); auto.
rewrite Rpplus_sym; auto.
Save.
Hint Resolve Rpminus_perm.


(** ** Multiplications [Rpmult] *)
(** *** Multiplication by an integer [NRpmult] *)

Fixpoint NRpmult p r {struct p} : Rp := 
  match p with O => R0
             | S n =>  r + (NRpmult n r)
  end.

Infix "*/" := NRpmult (at level 60) : Rp_scope.

Lemma NRpmult_0 : forall r : Rp, 0 */ r = R0.
trivial.
Save.

Lemma NRpmult_S : forall (n:nat) (r : Rp), (S n) */ r = r + (n */ r).
trivial.
Save.
Hint Resolve NRpmult_0 NRpmult_S.

Lemma NRpmult_zero : forall n : nat, n */ R0 == R0.
induction n; auto.
rewrite NRpmult_S; rewrite IHn; auto.
Save.

Lemma NRpmult_1: forall x : Rp, (1 */ x) == x.
intros; rewrite NRpmult_S; auto.
Save.
Hint Resolve NRpmult_1.

Lemma plus_NRpmult_distr:
  forall (n m : nat) (r : Rp), (n + m */ r) == ((n */ r) + (m */ r)).
intros; induction n; auto.
rewrite plus_Sn_m; rewrite NRpmult_S.
rewrite IHn; rewrite NRpmult_S; auto.
Save.

Lemma NRpmult_plus_distr:
  forall (n : nat) (r1 r2 : Rp), (n */ r1 + r2) == ((n */ r1) + (n */ r2)).
intros; induction n; auto.
repeat rewrite NRpmult_S.
rewrite IHn; auto.
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; trivial.
Save.

Hint Resolve plus_NRpmult_distr NRpmult_plus_distr.

Lemma NRpmult_le_compat_right :  
    forall (n : nat) (r1 r2 : Rp), r1 <= r2 -> (n */ r1) <= (n */ r2).
intros; induction n; trivial.
repeat rewrite NRpmult_S; auto.
Save.
Hint Resolve NRpmult_le_compat_right.

Lemma NRpmult_le_compat_left:
  forall (n m : nat) (r : Rp), (n <= m)%nat -> (n */ r) <= (m */ r).
induction 1; trivial.
transitivity (m */ r); trivial.
rewrite NRpmult_S; auto.
Save.
Hint Resolve NRpmult_le_compat_left.

Add Morphism NRpmult with signature le ==> Ole ==> Ole 
    as NRpmult_le_compat.
intros; transitivity (y */ x0); auto.
Save. 
Hint Immediate NRpmult_le_compat.

Add Morphism NRpmult with signature eq ==> Oeq ==> Oeq 
    as NRpmult_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Immediate NRpmult_eq_compat.

Lemma NRpmult_mult_assoc: forall (n m : nat) (r:Rp), n * m */ r == n */ (m */ r).
intros; induction n.
rewrite mult_0_l; auto.
rewrite mult_succ_l.
rewrite plus_NRpmult_distr.
rewrite NRpmult_S,IHn; auto.
Save.
Hint Resolve NRpmult_mult_assoc.

Lemma NRpmult_N2Rp : forall n m, n */ N2Rp m == N2Rp (n*m).
intros; induction n; intros; auto.
rewrite NRpmult_S, IHn,N2Rp_plus; auto.
Save.
Hint Resolve NRpmult_N2Rp.

Lemma NRpmult_floor_decimal : forall n (r:Rp), n */  r == N2Rp (n * floor r) + (n */  U2Rp (decimal r)).
intros; rewrite (Rpplus_floor_decimal r) at 1.
rewrite NRpmult_plus_distr,NRpmult_N2Rp; auto.
Save.
Hint Resolve NRpmult_floor_decimal.

Lemma NRpmult_minus_distr : forall n r1 r2, n */ (r1 - r2) == (n */ r1) - (n */ r2).
intros; apply (Rple_total r1 r2); intros; auto.
rewrite Rpminus_le_zero; auto.
rewrite NRpmult_zero.
rewrite Rpminus_le_zero; auto.
apply Rpplus_eq_perm_right.
rewrite <- NRpmult_plus_distr.
rewrite Rpminus_plus_simpl; trivial.
Save.
Hint Resolve NRpmult_minus_distr.


Lemma NRpmult_R1 : forall n, n */ R1 == N2Rp n.
intros; rewrite (NRpmult_N2Rp n 1).
rewrite mult_1_r; trivial.
Save.
Hint Resolve NRpmult_R1.

(** *** Multiplication between positive reals *)

Definition Rpmult (r1 r2 : Rp) : Rp := 
     (floor r1 */ r2) + (floor r2 */ U2Rp (decimal r1)) + U2Rp (decimal r1 * decimal r2)%U.

Infix "*" := Rpmult : Rp_scope.

Lemma Rpmult_zero_left: forall r : Rp, R0 * r == R0.
intros; unfold Rpmult; repeat rewrite floorR0; repeat rewrite decimalR0.
rewrite NRpmult_zero, Umult_zero_left, NRpmult_0; auto.
repeat rewrite Rpplus_zero_left; auto.
Save.
Hint Resolve Rpmult_zero_left.


Lemma Rpmult_sym : forall r1 r2 : Rp, r1 * r2  == r2 * r1.
intros; unfold Rpmult; apply Rpplus_eq_compat; auto.
rewrite (NRpmult_floor_decimal (floor r1) r2).
rewrite (NRpmult_floor_decimal (floor r2) r1).
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; auto with arith.
Save.
Hint Resolve Rpmult_sym.

Lemma Rpmult_zero_right: forall r : Rp, r * R0 == R0.
intros; rewrite Rpmult_sym; auto.
Save.
Hint Resolve Rpmult_zero_right.

Lemma NRpmult_mult : forall n r, N2Rp n * r == n */ r.
intros; unfold Rpmult; repeat rewrite decimalN2Rp; repeat rewrite floorN2Rp.
rewrite Umult_zero_left.
rewrite Rpplus_zero_right.
rewrite NRpmult_zero; auto.
Save.
Hint Resolve NRpmult_mult.

Lemma Rpmult_one_left: forall x : Rp, (R1 * x) == x.
intro; rewrite (NRpmult_mult 1 x); auto.
Save.
Hint Resolve Rpmult_one_left.


Lemma NRp_Nmult_eq : forall n (x:U), (n */ x < 1)%U -> (n */ x)%Rp == (n */ x)%U.
intros n x. 
induction n; auto.
rewrite Nmult_S.
rewrite NRpmult_S.
intros; rewrite IHn; auto.
apply Ole_lt_trans with (2:=H); auto.
Save.
Hint Resolve NRp_Nmult_eq.

Lemma NRp_Nmult_eq_le1 
   : forall n (x:U), (n */ x <= R1)%Rp -> (n */ x)%Rp == (n */ x)%U.
intros n x. 
induction n; auto.
rewrite Nmult_S.
rewrite NRpmult_S.
intros; assert (n */ x <= R1).
transitivity (x + (n */ x)); auto.
rewrite IHn; auto.
apply U2Rp_plus_le; auto.
apply Rpplus_Uinv_le; auto.
rewrite <- IHn; auto.
Save.

Lemma U2Rp_Nmult_NRpmult : forall n x, U2Rp (n */ x) <= n */ x.
Proof.
  induction n; intros.
  auto.
  rewrite Nmult_S.
  rewrite U2Rp_plus.
  rewrite NRpmult_S; auto.
Qed.

Lemma U2Rp_Nmult_le : forall n x, U2Rp (n */ x) <= n * x.
Proof.
  intros; rewrite U2Rp_Nmult_NRpmult; auto.
Qed.
Hint Resolve U2Rp_Nmult_NRpmult U2Rp_Nmult_le.

Lemma N2Rp_mult : forall x y, N2Rp (x * y) == N2Rp x * N2Rp y.
intros; unfold Rpmult; repeat rewrite floorN2Rp; repeat rewrite decimalN2Rp; auto.
rewrite Umult_zero_left; repeat rewrite NRpmult_zero.
repeat rewrite Rpplus_zero_right; auto.
Save.
Hint Resolve N2Rp_mult.

Lemma U2Rp_mult : forall x y, U2Rp (x * y) == U2Rp x * U2Rp y.
intros; apply (orc_lt_eq1 x); auto; intros.
intros; apply (orc_lt_eq1 y); auto; intros.
unfold Rpmult; repeat rewrite floor_mkRp_int; repeat rewrite decimal_mkRp_frac; auto.
repeat rewrite floorU2Rp; repeat rewrite decimalU2Rp; auto.
unfold Rpmult; repeat rewrite floor_mkRp_int; repeat rewrite decimal_mkRp_frac; auto.
rewrite H0; rewrite floorU1; rewrite decimalU1.
repeat Usimpl.
rewrite U2Rp1_R1, NRpmult_R1, NRpmult_1, Rpplus_zero_right; auto.
unfold Rpmult; rewrite H; rewrite floorU1; rewrite decimalU1.
repeat Usimpl.
rewrite NRpmult_1, NRpmult_zero, Rpplus_zero_right; auto.
Save.
Hint Resolve U2Rp_mult.

Lemma U2Rp_esp_mult 
  : forall x y z, [1-]x <= y -> U2Rp ((x & y) * z) == U2Rp (x * z) + U2Rp (y * z) - U2Rp z.
intros.
apply (Ule_total (x * z) ([1-](y * z))); intros; auto.
rewrite Uesp_mult_le; auto.
rewrite <- U2Rp_minus.
apply Rpminus_eq_compat; auto.
symmetry; auto.
rewrite Uesp_mult_ge; auto.
rewrite <- (U2Rp_plus_le (x * z & (y * z))); auto.
rewrite U2Rp_Uesp; auto.
rewrite <- Rpminus_assoc_right;  auto.
apply Rpminus_eq_compat; auto.
rewrite <- Uminus_one_left.
rewrite <- U2Rp_minus.
rewrite Rpminus_assoc_right; auto.
rewrite Rpminus_le_zero; auto.
rewrite Uinv_inv.
apply Uplus_inv_le_esp.
transitivity z; auto.
Save.
Hint Resolve U2Rp_esp_mult.

Instance Rpmult_mon_right : forall x, monotonic (Rpmult x).
intros x y z; unfold Rpmult; intros.
repeat rewrite <- Rpplus_assoc.
apply Rpplus_le_compat; auto.
destruct H as [Hlt|(Hle,Hne)].
(* case floor y < floor z *)
transitivity (floor z */ U2Rp (decimal x)); auto.
transitivity (S (floor y) */ U2Rp (decimal x)); auto with zarith.
rewrite NRpmult_S; auto.
rewrite Rpplus_sym; apply Rpplus_le_compat; auto with arith.
(* case floor y = floor z & decimal x <= decimal x0 *)
auto.
Save.
Hint Resolve Rpmult_mon_right.

Instance Rpmult_monotonic2 : monotonic2 Rpmult.
intros; apply monotonic2_sym; auto.
Save.
Hint Resolve Rpmult_monotonic2.

Instance Rpmult_stable2 : stable2 Rpmult.
apply monotonic2_stable2; trivial.
Save.
Hint Resolve Rpmult_stable2.

Add Morphism Rpmult with signature Ole ==> Ole ==> Ole
as Rpmult_le_compat.
intros; apply Rpmult_monotonic2; auto.
Save.
Hint Immediate Rpmult_le_compat.

Add Morphism Rpmult with signature Oeq ==> Oeq ==> Oeq
as Rpmult_eq_compat.
intros; apply Rpmult_stable2; auto.
Save.
Hint Immediate Rpmult_eq_compat.

Lemma Rpmult_le_compat_left : forall x y z : Rp, x <= y -> x * z <= y * z.
auto.
Save.

Lemma Rpmult_le_compat_right : forall x y z : Rp, y <= z -> x * y <= x * z.
auto.
Save.

Lemma Rpmult_eq_compat_left : forall x y z : Rp, x == y -> x * z == y * z.
auto.
Save.

Lemma Rpmult_eq_compat_right : forall x y z : Rp, y == z -> x * y == x * z.
auto.
Save.
Hint Resolve Rpmult_le_compat_left Rpmult_le_compat_right Rpmult_eq_compat_left Rpmult_eq_compat_right.

Instance Rpmult_mon2 : monotonic2 Rpmult.
red; intros; auto.
Save.

Definition RpMult : Rp -m> Rp -m> Rp := mon2 Rpmult.

Lemma Rpdistr_plus_right 
   : forall r1 r2 r3 : Rp, (r1 + r2) * r3 == r1 * r3 + r2 * r3.
intros; unfold Rpmult; apply (Rpplus_rec r1 r2); intros;
repeat rewrite decimal_mkRp_frac; repeat rewrite floor_mkRp_int; auto.
rewrite plus_NRpmult_distr.
rewrite <- U2Rp_plus_le; auto.
rewrite NRpmult_plus_distr.
rewrite Udistr_plus_right; auto.
rewrite <- U2Rp_plus_le; auto.
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; trivial.
repeat rewrite Rpplus_assoc.
apply Rpplus_eq_compat; trivial.
repeat rewrite <- Rpplus_assoc.
rewrite Rpplus_sym.
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; trivial.
rewrite Rpplus_sym.
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; trivial.
(* case [1- decimal r2 < decimal r1] *)
rewrite NRpmult_S, plus_NRpmult_distr.
repeat rewrite <- Rpplus_assoc.
rewrite Rpplus_sym.
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; trivial.
transitivity ((floor r2 */ r3)  + (floor r3 */ U2Rp (decimal r1)) + (U2Rp (decimal r1 * decimal r3) 
             + ((floor r3 */ U2Rp (decimal r2)) + U2Rp (decimal r2 * decimal r3)))).
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; trivial.
rewrite U2Rp_Uesp; auto.
rewrite NRpmult_minus_distr.
rewrite Rpminus_plus_perm_right; auto.
rewrite NRpmult_plus_distr.
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; trivial.
repeat rewrite Rpplus_assoc.
rewrite (Rpplus_sym (U2Rp (decimal r1 * decimal r3))).
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; trivial.
rewrite U2Rp_esp_mult; auto.
rewrite (Rpplus_floor_decimal r3) at 4.
rewrite NRpmult_R1.
rewrite Rpplus_minus_assoc with (z:=N2Rp (floor r3)); auto.
rewrite Rpplus_minus_simpl_left.
rewrite Rpminus_plus_simpl; auto.
transitivity (U2Rp (([1-]decimal r2) * decimal r3 + decimal r2 * decimal r3)); auto.
rewrite <- U2Rp_plus_le; auto.
transitivity r3; auto.
rewrite NRpmult_R1.
apply Rple_intro_eq; repeat rewrite int_simpl; repeat rewrite frac_simpl; auto.
rewrite (Rpplus_sym (floor r2 */ r3)).
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; trivial.
Save.

Lemma Rpdistr_plus_left : forall r1 r2 r3 : Rp, r1 * (r2 + r3) == r1 * r2 + r1 * r3.
intros; rewrite Rpmult_sym, Rpdistr_plus_right.
apply Rpplus_eq_compat; auto.
Save.

Hint Resolve Rpdistr_plus_right Rpdistr_plus_left.

Lemma Rpmult_NRpmult_perm : forall n x y, x * (n */ y) == n */ (x * y).
intros; induction n.
repeat rewrite NRpmult_0; auto.
repeat rewrite NRpmult_S.
rewrite Rpdistr_plus_left.
rewrite IHn; auto.
Save.
Hint Resolve Rpmult_NRpmult_perm.

Lemma Rpmult_decomp : forall r1 r2 : Rp,
   r1 * r2 == (N2Rp (floor r1 * floor r2))
            + (floor r1 */ U2Rp (decimal r2)) + (floor r2 */ U2Rp (decimal r1))
            + U2Rp (decimal r1 * decimal r2).
intros; unfold Rpmult.
rewrite (NRpmult_floor_decimal (floor r1)); auto.
Save.

Lemma Rpmult2_decomp : forall r1 r2 r3: Rp,
   r1 * (r2 * r3) == (N2Rp (floor r1 * floor r2 * floor r3))
            + ((floor r1 * floor r2) */ U2Rp (decimal r3)) 
            + ((floor r1 * floor r3) */ U2Rp (decimal r2))
            + ((floor r2 * floor r3) */ U2Rp (decimal r1))
            + (floor r1 */ U2Rp (decimal r2 * decimal r3))
            + (floor r2 */ U2Rp (decimal r1 * decimal r3))
            + (floor r3 */ U2Rp (decimal r1 * decimal r2))
            + U2Rp (decimal r1 * decimal r2 * decimal r3).
intros; rewrite (Rpmult_decomp r2 r3).
rewrite (Rpplus_floor_decimal r1) at 1.
rewrite Rpdistr_plus_right.
repeat rewrite Rpdistr_plus_left.
rewrite <- N2Rp_mult.
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; auto with arith.
repeat rewrite NRpmult_mult.
repeat rewrite <- NRpmult_mult_assoc.
apply Rpplus_eq_compat; auto with arith.
apply Rpplus_eq_compat; auto with arith.
repeat rewrite Rpplus_assoc.
rewrite <- U2Rp_mult.
apply Rpplus_eq_compat; auto.
rewrite (Rpplus_sym (floor r2 * floor r3 */ U2Rp (decimal r1))).
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; auto.
rewrite (Rpmult_sym (U2Rp (decimal r1))).
rewrite NRpmult_mult.
apply Rpplus_eq_compat; auto.
repeat rewrite Rpmult_NRpmult_perm.
repeat rewrite <- U2Rp_mult.
apply Rpplus_eq_compat; auto.
Save.

Lemma Rpmult_assoc : forall  r1 r2 r3 : Rp, r1 * (r2 * r3) == r1 * r2 * r3.
intros; rewrite (Rpmult_sym (r1 * r2)).
repeat rewrite Rpmult2_decomp.
apply Rpplus_eq_compat.
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat.
apply N2Rp_eq_compat; ring.
repeat rewrite Rpplus_assoc.
rewrite (Rpplus_sym (floor r1 * floor r2 */ U2Rp (decimal r3))).
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; auto with arith.
repeat rewrite Rpplus_assoc.
rewrite (Rpplus_sym (floor r1 * floor r2 */ U2Rp (decimal r3))).
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; auto with arith.
apply Rpplus_eq_compat; auto with arith.
rewrite (Rpplus_sym (floor r3 */ U2Rp (decimal r1 * decimal r2))).
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat.
apply NRpmult_eq_compat; auto.
apply Rpplus_eq_compat; auto.
apply NRpmult_eq_compat; auto.
apply U2Rp_eq_compat; auto.
rewrite Umult_sym; auto.
Save.
Hint Resolve Rpmult_assoc.

Lemma Rpmult_one_right: forall x : Rp, (x * R1) == x.
intro; rewrite Rpmult_sym; auto.
Save.
Hint Resolve Rpmult_one_right.

Lemma Rpmult_not0_left : forall x y : Rp, ~ R0 == x * y -> ~ R0 == x.
intros; intro xis0.
apply H; rewrite <- xis0; auto.
Save.
Hint Resolve Rpmult_not0_left.

Lemma Rpmult_not0_right : forall x y : Rp, ~ R0 == x * y -> ~ R0 == y.
intros x y; rewrite Rpmult_sym.
intro; apply Rpmult_not0_left with x; trivial.
Save.
Hint Resolve Rpmult_not0_right.

Lemma U2Rp_0_simpl : forall x : U, R0 == U2Rp x -> 0 == x.
intros; apply U2Rp_eq_simpl.
rewrite <- H; auto.
Save.
Hint Immediate U2Rp_0_simpl.

Lemma U2Rp_not_0 : forall x : U, ~ R0 == x -> ~ 0 == x.
intros; intro xis0.
apply H.
rewrite <- xis0; auto.
Save.
Hint Resolve U2Rp_not_0.

Lemma U2Rp_not_0_equiv : forall x : U, ~ R0 == x <-> ~ 0 == x.
intros; split; auto.
Save.

Lemma U2Rp_lt_0 : forall x:U, R0 < x -> 0 < x.
auto.
Save.
Hint Resolve U2Rp_lt_0.

Lemma U2Rp_0_lt : forall x:U, 0 < x -> R0 < x.
intros.
apply U2Rp_lt_compat.
assumption.
Save.
Hint Resolve U2Rp_0_lt.

Lemma Rpplus_lt_simpl_left: forall x y z : Rp, x + z < y + z -> x < y.
intros; rewrite <- (Rpplus_minus_simpl_right x z).
rewrite <- (Rpplus_minus_simpl_right y z); auto.
Save.

Lemma Rpplus_lt_simpl_right: forall x y z : Rp, x + y < x + z -> y < z.
intros; rewrite <- (Rpplus_minus_simpl_left x z).
rewrite <- (Rpplus_minus_simpl_left x y); auto.
Save.

Lemma plus_lt_1_decimal : forall x y:Rp, x + y < R1 -> decimal x < [1-] decimal y.
intros; apply U2Rp_lt_simpl.
rewrite U2Rp_Uinv.
assert (y < R1).
apply Ole_lt_trans with (x+y); auto.
assert (x < R1).
apply Ole_lt_trans with (x+y); auto.
repeat (rewrite <- Rplt1_decimal; trivial).
apply Rpplus_lt_simpl_left with y.
apply Olt_le_trans with R1; auto.
Save.
Hint Immediate plus_lt_1_decimal.

Lemma plus_lt_1_decimal_plus : forall x y, x + y < R1 -> decimal (x+y) == (decimal x + decimal y)%U.
intros; apply decimal_Rpplus_simpl_ok; auto.
Save.
Hint Immediate plus_lt_1_decimal_plus.


Lemma Rpplus_0_simpl_left : forall x y : Rp, R0 == x + y -> R0 == x.
intros; transitivity (x + y - y); auto.
rewrite <- H; auto.
Save.

Lemma Rpplus_0_simpl_right : forall x y : Rp, R0 == x + y -> R0 == y.
intros x y; rewrite Rpplus_sym; intro.
apply Rpplus_0_simpl_left with x; trivial.
Save.

Lemma Rpplus_0_simpl : forall x y : Rp, R0 == x + y -> R0 == x /\ R0 == y.
split.
apply Rpplus_0_simpl_left with y; trivial.
apply Rpplus_0_simpl_right with x; trivial.
Save.

Lemma NRpmult_0_simpl : forall (n:nat) (x : Rp), R0 == n */ x -> n = O \/ R0 == x.
intros n x; destruct n; auto.
rewrite NRpmult_S; intro.
right; apply Rpplus_0_simpl_left with (n */ x); auto.
Save. 

Lemma Rpmult_0_simpl : forall x y : Rp, R0 == x * y -> R0 == x \/ R0 == y.
intros x y; unfold Rpmult; intros. 
destruct (Rpplus_0_simpl _ _ H); clear H.
destruct (Rpplus_0_simpl _ _ H0); clear H0.
destruct (NRpmult_0_simpl _ _ H); clear H; auto.
destruct (NRpmult_0_simpl _ _ H2); clear H2; auto.
assert (H2:=U2Rp_0_simpl _ H1); clear H1.
(*assert (decimal x * decimal y == 0)%U; auto.*)
destruct (iseq_dec 0 (decimal x)); auto.
left; transitivity (floor x); auto.
symmetry; auto.
assert (0 == decimal y)%U; auto.
apply Umult_zero_simpl_right with (decimal x); auto.
right; symmetry; auto.
assert (0==decimal x)%U; auto.
left; symmetry; auto.
Save.

Lemma Rpmult_not_0 : forall x y : Rp, ~ R0 == x -> ~ R0 == y -> ~ R0 == x * y.
intros; intro M0.
destruct (Rpmult_0_simpl _ _ M0); auto.
Save.
Hint Resolve Rpmult_not_0.

Lemma Rpdistr_minus_right : forall r1 r2 r3 : Rp, (r1 - r2) * r3 == r1 * r3 - r2 * r3.
intros.
apply (Rple_total r1 r2); intros; auto.
rewrite (Rpminus_le_zero r1 r2); auto.
rewrite (Rpminus_le_zero (r1 * r3) (r2 * r3)); auto.
apply Rpplus_eq_perm_right.
rewrite <- Rpdistr_plus_right; auto.
Save.
Hint Resolve Rpdistr_minus_right.

Lemma Rpdistr_minus_left : forall r1 r2 r3 : Rp, r1 * (r2 - r3) == r1 * r2 - r1 * r3.
intros; rewrite (Rpmult_sym r1 (r2 - r3)).
rewrite Rpdistr_minus_right; auto.
Save.
Hint Resolve Rpdistr_minus_left.


Lemma U2Rp_mult_le_left : forall (x:U) (y:Rp), x * y <= y.
intros; transitivity (R1 * y); auto.
Save.
Hint Resolve U2Rp_mult_le_left.

Lemma U2Rp_mult_le_right : forall (x:Rp) (y:U), x * y <= x.
intros; transitivity (x * R1); auto.
Save.
Hint Resolve U2Rp_mult_le_right.

(** ** Division [Rpdiv] *) 

(** *** Inverse [U1div] of elements of [U] *)

(** A stronger formulation of the Archimedian property to be able to compute [n] *)

Hypothesis archimedian2: forall x : U, ~ 0 == x -> exists n : nat, [1/]1+n <= x.


Require Export Markov.

(** Definition [1/x] for [x] in [U] *)

Section U1div_def.
Variable x : U.
Hypothesis x_not0 : ~ 0 == x.

Definition P (n:nat) := ([1-](n */ x) < x)%U.

Lemma Pdec : dec P.
intros n.
case (isle_dec x ([1-](n*/x))); unfold P; auto.
Defined.

Definition DP : Dec := mk_Dec Pdec.

Lemma Pacc : exists n : nat, P n.
intros; elim (archimedian2 x); auto.
intro n; exists (S n); unfold P.
apply Ole_lt_trans with 0; auto.
transitivity ([1-]((S n) */ [1/]1+n))%U; auto.
Save.

Let n := minimize DP Pacc.

Lemma Olt_Uinv_Nmult_nx_x : [1-](n */ x) < x.
change (P n).
apply (minimize_P DP Pacc).
Save.
Hint Resolve Olt_Uinv_Nmult_nx_x.

Lemma Nmult_nx_1 : (n */ x) <= R1.
assert (forall m, (m <= n)%nat -> (m */ x) <= R1); auto.
induction m; auto.
intros H.
assert (~ [1-](m */ x) < x).
apply (minimize_min DP Pacc (m:=m)); auto.
rewrite NRpmult_S.
assert (x <= [1-](m*/x)); auto.
setoid_replace (m */ x) with (U2Rp (m */ x)); auto.
rewrite U2Rp_plus_le; auto.
apply NRp_Nmult_eq_le1; apply IHm; try omega.
Save.
Hint Resolve Nmult_nx_1.


Definition U1div0 : Rp := mkRp n (([1-] (n */ x))/x).

Lemma Olt_frac_U1div0_1 : (([1-] (n */ x))/x) < 1.
apply Ult_neq_one; intro.
absurd ([1-](n */ x) == x); auto.
transitivity (1 * x)%U; auto.
rewrite H; auto.
rewrite Udiv_mult; auto.
Save.
Hint Resolve Olt_frac_U1div0_1.

Lemma floor_U1div0 : floor U1div0 = n.
unfold U1div0; auto.
Save.

Lemma decimal_U1div0 : decimal U1div0 = ([1-] (n */ x)) /x.
unfold U1div0; auto.
Save.

Lemma U1div0_left : U2Rp x * U1div0 == R1.
rewrite Rpmult_decomp.
rewrite floor_U1div0,decimal_U1div0.
apply (floor_decimal_U2Rp_elim x); intros.
-simpl mult; rewrite NRpmult_0; repeat rewrite Rpplus_zero_left.
 rewrite Umult_div; auto.
 repeat (rewrite NRp_Nmult_eq_le1; auto).
 rewrite U2Rp_plus_le; auto.
 rewrite <- U2Rp1_R1; auto.
-assert (n=1)%nat.
* case_eq n; intros.
absurd ([1-](n */ x) < x); auto.
rewrite H0; auto.
destruct n0; auto.
absurd ((n */ x) <= R1); auto.
rewrite H,H0.
rewrite U2Rp1_R1; auto.
rewrite NRpmult_R1; auto.
intro; absurd (S (S n0) <= 1)%nat; auto with arith.
* rewrite H,H0.
rewrite NRpmult_1,NRpmult_zero,Umult_zero_left,Rpplus_zero_right,
        Rpplus_zero_right,Nmult_1,Uinv_one,Udiv_zero,Rpplus_zero_right.
auto.
Save.

Lemma U1div0_right : U1div0 * U2Rp x == R1.
rewrite Rpmult_sym; apply U1div0_left.
Save.

End U1div_def.
Hint Resolve U1div0_right U1div0_left.

Definition U1div (x:U) := match iseq_dec 0 x with 
    left _ => R0 | right H => U1div0 x H end.

Lemma U1div_left : forall x, ~ 0 == x -> U2Rp x * U1div x == R1.
unfold U1div; intros; destruct (iseq_dec 0 x); auto.
case H; trivial.
Save.
Hint Resolve U1div_left.

Lemma U1div_right : forall x, ~ 0 == x ->  U1div x * U2Rp x == R1.
intros; rewrite Rpmult_sym; auto.
Save.
Hint Resolve U1div_right.

Lemma U1div_zero : forall x, 0 == x ->  U1div x == R0.
unfold U1div; intros; destruct (iseq_dec 0 x); auto.
exfalso; auto.
Save.
Hint Resolve U1div_zero.

Lemma Unth_mult_le1 : forall x:Rp, U2Rp ([1/]1+(floor x)) * x <= R1.
intros; transitivity (U2Rp ([1/]1+(floor x)) * (S (floor x))); auto.
rewrite Rpmult_sym.
rewrite NRpmult_mult.
rewrite NRpmult_S.
rewrite NRp_Nmult_eq.
rewrite U2Rp_plus_le; auto.
rewrite Nmult_n_Unth.
apply Uinv_lt_one; auto.
Save.
Hint Resolve Unth_mult_le1.

(** *** Non-zero elements *)

Class notz (x:Rp) := notz_def : ~ R0 == x.

Lemma notz_le_compat : forall x y, notz x -> x <= y -> notz y.
intros x y nx Hle Hy; apply nx.
apply Ole_antisym; auto.
rewrite Hle; auto.
Save.

Add Morphism notz with signature Ole ++> Basics.impl as notz_le_compat_morph.
red; intros; apply notz_le_compat with x; auto.
Save.

Lemma notz_eq_compat : forall x y, notz x -> x == y -> notz y.
intros; apply notz_le_compat with x; auto.
Save.

Add Morphism notz with signature Oeq ==> Basics.impl as notz_eq_compat_morph.
red; intros; apply notz_eq_compat with x; auto.
Save.

Instance notz_mult : forall x y, notz x -> notz y -> notz (x * y).
unfold notz; auto.
Save.
Hint Resolve notz_mult.

Instance notz_plus_left : forall x y, notz x -> notz (x + y).
unfold notz; intros; intro H1.
apply H.
apply Rpplus_0_simpl_left with y; auto.
Save.
Hint Immediate notz_plus_left.

Instance notz_plus_right : forall x y, notz y -> notz (x + y).
unfold notz; intros; intro H1.
apply H.
apply Rpplus_0_simpl_right with x; auto.
Save.
Hint Immediate notz_plus_right.

Lemma notz_mult_inv_left : forall x y, notz (x * y) -> notz x.
unfold notz; intros x y H nx.
apply H; rewrite <- nx; auto.
Save.

Lemma notz_mult_inv_right : forall x y, notz (x * y) -> notz y.
unfold notz; intros x y H nx.
apply H; rewrite <- nx; auto.
Save.

Instance notz_1 : notz R1.
exact Rpdiff_0_1.
Save.
Hint Resolve notz_1.

(** *** Inverse of elements in Rp [Rp1div] *)

Section Rp1div_def.
Variable x : Rp.

Let a := U2Rp ([1/]1+(floor x)) * x.

Lemma a_le_1 : a <= R1.
apply  (Unth_mult_le1 x).
Save.

Lemma a_not_0 : notz x -> notz a.
intro x_not0; apply Rpmult_not_0; auto.
intro H; assert (e:=U2Rp_0_simpl _ H); auto.
apply (Unth_not_null (floor x)); trivial.
Save.

Lemma a_is_0 : R0 == x -> R0 == a.
intro eqx0; unfold a.
rewrite <- eqx0 at 2; auto.
Save.

Lemma U2Rp_eq_not_0 : notz x -> forall y, a == U2Rp y -> ~ 0 == y.
intro x_not0; intros; apply U2Rp_not_0.
rewrite <- H; apply a_not_0; trivial.
Save.

Lemma U2Rp_eq_is_0 : R0 == x -> forall y, a == U2Rp y -> 0 == y.
intro eqx0; intros; apply U2Rp_0_simpl.
rewrite <- H; apply a_is_0; trivial.
Save.

Definition Rp1div : Rp :=  
   let (y,H) := Rple1_U2Rp a a_le_1 in  U2Rp ([1/]1+(floor x)) * U1div y.

Lemma Rp1div_left : notz x -> x * Rp1div == R1.
intro x_not0;unfold Rp1div; destruct (Rple1_U2Rp a a_le_1).
rewrite Rpmult_assoc.
rewrite (Rpmult_sym x).
fold a.
rewrite o; auto.
apply U1div_left; apply U2Rp_eq_not_0; auto.
Save.
Hint Resolve Rp1div_left.

Lemma Rp1div_right : notz x -> Rp1div * x == R1.
intro x_not0;rewrite Rpmult_sym; auto.
Save.
Hint Resolve Rp1div_right.

Lemma Rp1div_zero : R0 == x -> Rp1div == R0.
intro x_not0;unfold Rp1div; destruct (Rple1_U2Rp a a_le_1).
setoid_replace (U1div x0) with R0; auto.
apply U1div_zero.
apply U2Rp_eq_is_0; auto.
Save.

End Rp1div_def.

Notation "[1/] x" := (Rp1div x) (at level 35, right associativity) : Rp_scope.
Hint Resolve Rp1div_left Rp1div_right Rp1div_zero.

Lemma Rp1div_0 : [1/]R0 == R0.
auto.
Save.
Hint Resolve Rp1div_0.

Instance notz_1div : forall x {nx:notz x}, notz ([1/]x).
intros; intro H1.
apply Rpdiff_0_1.
transitivity ([1/]x * x); auto.
rewrite <- H1; auto.
Save.
Hint Resolve notz_1div.

Lemma notz_dec : forall x, {notz x} + {R0 == x}.
intros; case (Rpeq_dec R0 x); auto.
Defined.

Lemma Rpmult_le_simpl_left : forall (x y z : Rp) {nx : notz x},
      x * y <= x * z -> y <= z.
intros; transitivity ([1/]x * (x * z)).
transitivity ([1/]x * (x * y)); auto.
rewrite Rpmult_assoc.
rewrite Rp1div_right; auto.
rewrite Rpmult_assoc.
rewrite Rp1div_right; auto.
Save.
Hint Resolve Rpmult_le_simpl_left.

Lemma Rpmult_le_simpl_right : forall (x y z : Rp) {nz : notz z}, 
   x * z <= y * z -> x <= y.
intros; apply Rpmult_le_simpl_left with z; auto.
transitivity (x * z); auto.
transitivity (y * z); auto.
Save.
Hint Resolve Rpmult_le_simpl_right.


Lemma Rpmult_eq_simpl_left : forall (x y z : Rp) {nx : notz x}, 
   x * y == x * z -> y == z.
intros; apply Ole_antisym.
apply Rpmult_le_simpl_left with x; auto.
apply Rpmult_le_simpl_left with x; auto.
Save.
Hint Resolve Rpmult_eq_simpl_left.

Lemma Rpmult_eq_simpl_right : forall (x y z : Rp) {nz : notz z}, 
   x * z == y * z -> x == y.
intros; apply Rpmult_eq_simpl_left with z; auto.
transitivity (x * z); auto.
transitivity (y * z); auto.
Save.
Hint Resolve Rpmult_eq_simpl_right.

Lemma Rpmult_le_perm_right :
forall (x y z : Rp) {nz: notz z}, x * z <= y -> x <= y * [1/]z.
intros; rewrite <- H.
rewrite <- Rpmult_assoc, Rp1div_left; auto.
Save.
Hint Resolve Rpmult_le_perm_right.

Lemma Rpmult_eq_perm_right :
forall (x y z : Rp) {nz: notz z}, x * z == y -> x == y * [1/]z.
intros; rewrite <- H.
rewrite <- Rpmult_assoc, Rp1div_left; auto.
Save.
Hint Resolve Rpmult_eq_perm_right.

Lemma Rpmult_le_perm_left :
forall (x y z : Rp), x <= y * z -> x * [1/]y <= z.
intros; rewrite H.
destruct (notz_dec y).
rewrite Rpmult_sym, Rpmult_assoc, Rp1div_right; auto.
rewrite Rp1div_zero; auto.
rewrite Rpmult_zero_right; auto.
Save.
Hint Resolve Rpmult_le_perm_left.

Lemma Rpmult_eq_perm_left :
forall (x y z : Rp) {ny: notz y}, x == y * z -> x * [1/]y == z.
intros; rewrite H.
rewrite Rpmult_sym, Rpmult_assoc, Rp1div_right; auto.
Save.
Hint Resolve Rpmult_eq_perm_left.

Lemma Rpmult_lt_zero: forall x y : Rp, R0 < x -> R0 < y -> R0 < x * y.
intros; apply Rplt_neq_zero; apply Rpmult_not_0; auto.
Save.
Hint Resolve Rpmult_lt_zero.

Lemma Rp1div_le_perm_left :
forall (x y z : Rp) {ny:notz y}, x * [1/]y <= z -> x <= z * y.
intros; rewrite <- H.
rewrite <- Rpmult_assoc, Rp1div_right; auto.
Save.
Hint Resolve Rp1div_le_perm_left.

Lemma Rp1div_eq_perm_left :
forall (x y z : Rp) {ny:notz y}, x * [1/]y == z -> x == z * y.
intros; rewrite <- H.
rewrite <- Rpmult_assoc, Rp1div_right; auto.
Save.
Hint Resolve Rp1div_eq_perm_left.

Lemma Rp1div_le_perm_right :
forall (x y z : Rp) {nz:notz z}, x <= y * [1/]z -> x * z <= y.
intros; rewrite H.
rewrite <- Rpmult_assoc, Rp1div_right; auto.
Save.
Hint Resolve Rp1div_le_perm_right.

Lemma Rp1div_eq_perm_right :
forall (x y z : Rp) {nz:notz z}, x == y * [1/]z -> x * z == y.
intros; rewrite H.
rewrite <- Rpmult_assoc, Rp1div_right; auto.
Save.
Hint Resolve Rp1div_eq_perm_right.

Lemma Rp1div_le_compat : forall (x y : Rp) {nx:notz x}, x <= y -> ([1/]y) <= ([1/]x).
intros; assert (ny:notz y).
apply notz_le_compat with x; trivial.
apply Rpmult_le_simpl_right with (x * y); auto.
rewrite (Rpmult_assoc ([1/]x)).
rewrite Rp1div_right, Rpmult_one_left; auto.
transitivity x; trivial.
rewrite (Rpmult_sym x).
rewrite Rpmult_assoc, Rp1div_right, Rpmult_one_left; auto.
Save.
Hint Resolve Rp1div_le_compat.

Add Morphism Rp1div with signature Oeq ==> Oeq
as Rp1div_eq_compat.
intros; destruct (notz_dec x).
assert (ny:notz y).
apply notz_le_compat with x; auto.
apply Ole_antisym; auto.
rewrite Rp1div_zero; auto.
rewrite Rp1div_zero; auto.
rewrite o; auto.
Save.
Hint Resolve Rp1div_eq_compat.

Lemma is_Rp1div : forall x y, x * y == R1 -> x == [1/]y.
Proof.
  intros.
  transitivity (R1 * [1/]y); auto.
  rewrite <- H.
  rewrite <- Rpmult_assoc.
  rewrite Rp1div_left; auto.
  apply Rpmult_not0_right with x; auto.
  rewrite H; auto.
Qed.
  
Lemma Rp1div_1 : [1/]R1 == R1.
symmetry; apply is_Rp1div; auto.
Save.
Hint Resolve Rp1div_1.

Lemma Rp1div_Rp1div : forall r, [1/][1/]r == r.
Proof.
  intro.
  destruct (notz_dec r) as [nr|nr].
  symmetry; apply is_Rp1div.
  auto.
  rewrite <- nr; rewrite Rp1div_zero; auto.
Qed.

Lemma Rp1div_le_simpl : forall x y : Rp, notz y -> [1/]y <= [1/]x -> x <= y.
Proof.
  intros x y ny H.
  rewrite <- (Rp1div_Rp1div x); trivial.
  rewrite <- (Rp1div_Rp1div y); auto.
Save.
Hint Immediate Rp1div_le_simpl.

Lemma Rp1div_eq_simpl : forall x y : Rp, [1/]y == [1/]x -> x == y.
  intros x y H.
  rewrite <- (Rp1div_Rp1div x); trivial.
  rewrite <- (Rp1div_Rp1div y); auto.
Save.
Hint Immediate Rp1div_eq_simpl.


Lemma Rp1div_lt_compat : forall x y : Rp, notz x -> x < y -> [1/]y < [1/]x.
Proof.
  intros x y H (Hle,Hneq).
  split; auto.
Qed.
Hint Resolve Rp1div_lt_compat.

Lemma Rpmult_Rp1div : forall r1 r2, [1/](r1*r2) == ([1/]r1)*([1/]r2).
Proof.
  intros.
  destruct (notz_dec (r1 * r2)) as [nz|nz].
  assert (notz r1).
  intro nz1; apply nz; rewrite <- nz1; auto.
  assert (notz r2).
  intro nz2; apply nz; rewrite <- nz2; auto.
  symmetry; apply is_Rp1div.
  rewrite (Rpmult_sym r1 r2).
  rewrite <- Rpmult_assoc.
  rewrite (Rpmult_assoc ([1/]r2)).
  rewrite Rp1div_right; auto.
  rewrite Rpmult_one_left; auto.
  rewrite Rp1div_zero; auto.
  destruct (Rpmult_0_simpl r1 r2) as [nr|nr]; auto.
  rewrite Rp1div_zero; auto.
  rewrite (Rp1div_zero r2); auto.
Qed.

(** *** Definition of general division *)

Definition Rpdiv r1 r2 := r1 * [1/] r2.
Notation "x / y" := (Rpdiv x y) : Rp_scope.

Add Morphism Rpdiv with signature Oeq ==> Oeq ==> Oeq
as Rpdiv_eq_compat.
intros.
unfold Rpdiv.
rewrite H.
rewrite H0.
reflexivity.
Save.

Lemma Rpdiv_le_compat : forall x y x' y',
  notz y' -> x <= y -> y' <= x' -> x/x' <= y/y'.
Proof.
  intros; unfold Rpdiv; auto.
Qed.

Lemma Rpdiv_Rp1div : forall r1 r2, [1/](r1/r2) == r2/r1.
Proof.
  intros; unfold Rpdiv.
  destruct (notz_dec r2) as [nz|nz].
  rewrite Rpmult_Rp1div.
  rewrite Rp1div_Rp1div; auto.
  rewrite <- nz.
  rewrite Rp1div_zero; auto.
  rewrite Rp1div_zero; auto.
Qed.
Hint Resolve Rpdiv_Rp1div.

(** ** Exponential function *)

Fixpoint Rpexp x (n:nat) {struct n} : Rp := 
    match n with O => R1 | S p => x * Rpexp x p end.

Infix "^" := Rpexp : Rp_scope.

Lemma Rpexp_simpl : forall x n, x ^ n = match n with O => R1 | S p => x * (x ^ p) end.
destruct n; trivial.
Save.

Lemma U2Rp_exp: forall (x:U) n, U2Rp (x ^ n) == (U2Rp x) ^ n.
induction n; auto.
rewrite Rpexp_simpl.
simpl Uexp.
rewrite U2Rp_mult; auto.
Save.

Lemma Rpexp_le1_mon : forall x n, x <= R1 -> x ^ (S n) <= x ^ n.
intros; rewrite Rpexp_simpl at 1.
transitivity (R1 * x ^ n); auto.
Save.
Hint Resolve Rpexp_le1_mon.

Lemma Rpexp_le1 : forall x n, x <= R1 -> x ^ n <= R1.
intros; induction n; auto.
transitivity (x ^ n); auto.
Save.
Hint Resolve Rpexp_le1.

Lemma Rpexp_le_compat : forall x y n, x <= y -> x ^ n <= y ^ n.
intros; induction n; auto.
rewrite (Rpexp_simpl x); rewrite (Rpexp_simpl y); auto.
Save.
Hint Resolve Rpexp_le_compat.

Lemma Rpexp_ge1_mon : forall x n, R1 <= x -> x ^ n <= x ^ (S n).
intros; rewrite (Rpexp_simpl x (S n)).
transitivity (R1 * x ^ n); auto.
Save.
Hint Resolve Rpexp_ge1_mon.

Add Morphism Rpexp with signature Oeq ==> eq ==> Oeq as Rpexp_eq_compat.
intros.
apply Ole_antisym; auto.
Save.

Hint Immediate Rpexp_eq_compat.

Instance Rpexp_mon : forall x, x <= R1 -> monotonic (o2:=Iord Rp) (Rpexp x).
red; intros.
induction H0; auto.
transitivity (x ^ m);auto.
change (x ^ S m <= x ^ m); auto.
Save.

Lemma Rpexp_0 : forall x, x ^ O == R1.
trivial.
Save.

Lemma Rpexp_1 : forall x, x ^ (S O) == x.
intro; rewrite Rpexp_simpl; auto.
Save.
Hint Resolve Rpexp_0 Rpexp_1.

Lemma Rpexp_zero : forall n, (0 < n)%nat -> R0 ^ n == R0.
induction 1; rewrite Rpexp_simpl; auto.
Save.

Lemma Rpexp_one : forall n, R1 ^ n == R1.
induction n; rewrite Rpexp_simpl; auto.
rewrite IHn; auto.
Save.

Lemma Rpexp_Rp1div_right 
 : forall r n, notz r -> ([1/]r) ^ n * r ^ n == R1.
intros; induction n; simpl Rpexp; auto.
rewrite (Rpmult_sym r).
rewrite <- Rpmult_assoc.
rewrite (Rpmult_assoc (([1/]r) ^ n)).
rewrite IHn.
rewrite Rpmult_one_left; auto.
Save.
Hint Resolve Rpexp_Rp1div_right.

Lemma Rpexp_Rp1div_left 
 : forall r n, notz r -> r ^ n  * ([1/]r) ^ n == R1.
intros; rewrite Rpmult_sym; auto.
Save.
Hint Resolve Rpexp_Rp1div_left.


Lemma Rpexp_Rp1div : forall r n, ([1/]r)^n == [1/](r^n).
Proof.
  intros.
  destruct (notz_dec r) as [nr|nr].
  apply is_Rp1div; auto.
  rewrite <- nr.
  rewrite (Rp1div_zero R0); auto.
  destruct n; auto.
  rewrite Rpexp_zero; auto with arith.
Qed.
Hint Resolve Rpexp_Rp1div.

Lemma Rpexp_Rpmult : forall r m n, r ^ m * r ^ n == r ^ (m+n).
Proof.
  intros r m n.
  induction m; simpl Rpexp; simpl plus; auto.
  rewrite <- Rpmult_assoc; rewrite IHm; auto.
Qed.


(** ** Compatibility of lubs and operations *)

Lemma islub_Rpplus : forall (f g:nat -> Rp) {mf:monotonic f} {mg:monotonic g} lf lg, 
      islub f lf -> islub g lg -> islub (fun n => f n + g n) (lf + lg).
intros f g Mf Mg lf lg (Hf,Lf) (Hg,Lg); split; intros.
transitivity (f i + lg); auto.
apply Rpminus_le_perm_right.
apply Lg; intros.
transitivity (f i + g i); auto.
apply Lf; intros.
apply Rpplus_le_perm_right.
rewrite Rpplus_sym.
apply Rpminus_le_perm_right.
transitivity (f i + g i); auto.
apply Lg; intros.
apply Rpplus_le_perm_right.
rewrite Rpplus_sym.
transitivity (f (i + i0)%nat + g (i + i0)%nat); auto.
apply Rpplus_le_compat; auto with arith.
Save.


Lemma islub_Rpminus : forall (f g:nat -> Rp) {mf:monotonic f} {mg:monotonic (o2:=Iord Rp) g} lf lg, 
      islub f lf -> isglb g lg -> islub (fun n => f n - g n) (lf - lg).
intros f g Mf Mg lf lg (Hf,Lf) (Hg,Lg); split; intros.
transitivity (f i - lg); auto.
apply Rpplus_le_perm_left.
apply Lf; intros.
apply Rpminus_le_perm_left.
apply (Lg (f i - y)); intros.
change (f i - y <= g i0).
apply Rpplus_le_perm_left.
apply Rpminus_le_perm_left.
transitivity (f (i + i0)%nat - g (i + i0)%nat); auto.
apply Rpminus_le_compat; auto with arith.
apply (Mg i0 (i+i0)%nat); auto with arith. 
Save.

Lemma islub_cte : forall c : Rp, islub (fun n:nat => c) c.
split; intros; auto.
apply (H O).
Save.

Lemma islub_fcte : forall f (c:Rp), (forall n:nat, f n == c) -> islub f c.
intros; apply islub_eq_compat with (fun n:nat => c) c; auto.
apply (islub_cte c).
Save.

Lemma islub_zero : forall (f:nat -> Rp), islub f R0 -> forall n, f n == R0.
intros f (Hf,Lf) n; apply Ole_antisym; auto.
Save.

Lemma islub_Rpplus_cte_left (f :nat -> Rp)  lf c :
      islub f lf ->  islub (fun n => c + f n) (c + lf).
intros (H1,H2); split; auto.
intros y H3.
assert (c <= y).
transitivity (c + f O); auto.
rewrite Rpplus_sym; apply Rpminus_le_perm_right; auto.
apply H2; intros.
apply Rpplus_le_perm_right; auto.
rewrite Rpplus_sym;auto.
Save.
Hint Resolve islub_Rpplus_cte_left.

Lemma islub_Rpplus_cte_right (f :nat -> Rp)  lf c :
      islub f lf ->  islub (fun n => f n + c) (lf + c).
intros; apply islub_eq_compat with  (fun n => c + f n) (c + lf); auto.
Save.
Hint Resolve islub_Rpplus_cte_right.
 

Lemma islub_Rpmult : forall (f g:nat -> Rp) {mf: monotonic f} {mg:monotonic g} lf lg, 
      islub f lf -> islub g lg -> islub (fun n => f n * g n) (lf * lg).
intros f g Mf Mg lf lg (Hf,Lf) (Hg,Lg); split; intros; auto.
case (notz_dec lg); intro.
apply Rp1div_le_perm_right; trivial.
apply Lf; intros.
apply Rpmult_le_perm_right; trivial.
case (notz_dec (f i)); intro.
rewrite Rpmult_sym.
apply Rp1div_le_perm_right; trivial.
apply Lg; intros.
apply Rpmult_le_perm_right; trivial.
rewrite Rpmult_sym.
transitivity (f (i+i0)%nat * g (i+i0)%nat); auto.
apply Rpmult_le_compat; auto with arith.
rewrite <- o,Rpmult_zero_left; auto.
rewrite <- o,Rpmult_zero_right; auto.
Save.

Lemma islub_lub_U : forall (f:nat -m> U), islub (fun n => U2Rp (f n)) (U2Rp (lub f)).
split; intros; auto.
case (Rple_lt_dec R1 y); intro.
transitivity R1; auto.
assert (Uy := Rplt1_decimal y o).
rewrite Uy.
apply U2Rp_le_compat.
apply lub_le; intros.
apply U2Rp_le_simpl; transitivity y; auto.
Save.

Lemma isglb_glb_U : forall (f:nat -m-> U), isglb (fun n => U2Rp (f n)) (U2Rp (glb f)).
split; intros; auto.
change (U2Rp (glb f) <= U2Rp (f i)); apply U2Rp_le_compat; auto.
change (y <= U2Rp (glb f)).
assert (y <= R1).
transitivity (U2Rp (f O)); auto.
apply (H O).
case (Rple_lt_eq_dec y R1); auto; intro.
assert (Uy := Rplt1_decimal y o).
rewrite Uy.
apply U2Rp_le_compat.
apply le_glb; intros.
apply U2Rp_le_simpl; transitivity y; auto.
apply (H n).
assert (forall i, 1 <= f i); intros.
apply U2Rp_le_simpl.
transitivity R1; auto.
transitivity y; auto.
apply (H i).
assert (1 <= glb f).
apply le_glb; auto.
rewrite <- H2,o; auto.
Save.


(** ** Sum of first [n] values of a function *)

Instance Rpcompplus_mon (a:nat -> Rp) : monotonic (compn Rpplus R0 a).
red; intros.
induction H; auto.
transitivity (compn Rpplus R0 a m); auto.
rewrite compS; auto.
Save.

Definition Rpsigma (a: nat -> Rp) : nat -m> Rp := mon (compn Rpplus R0 a).

Lemma Rpsigma_0: forall f : nat -> Rp, Rpsigma f O == R0.
trivial.
Save.
Hint Resolve Rpsigma_0.

Lemma Rpsigma_S:
  forall (f : nat -> Rp) (n : nat), Rpsigma f (S n) = f n + Rpsigma f n.
trivial.
Save.
Hint Resolve Rpsigma_S.

Lemma Rpsigma_1 : forall f : nat -> Rp, Rpsigma f 1%nat == f O.
intros; rewrite Rpsigma_S.
rewrite Rpsigma_0; auto.
Save.
Hint Resolve Rpsigma_1.

Lemma Rpsigma_incr:
  forall (f : nat -> Rp) (n m : nat), n <= m -> (Rpsigma f) n <= (Rpsigma f) m.
intros; apply (Rpcompplus_mon f n m); auto.
Save.
Hint Resolve Rpsigma_incr.

Lemma Rpsigma_le_compat:
  forall (f g : nat -> Rp) (n : nat),
  (forall k : nat, (k < n)%nat -> f k <= g k) -> Rpsigma f n <= Rpsigma g n.
induction n; intros; auto.
repeat rewrite Rpsigma_S.
rewrite H; auto with arith.
Save.
Hint Resolve Rpsigma_le_compat.

Lemma Rpsigma_eq_compat:
  forall (f g : nat -> Rp) (n : nat),
  (forall k : nat, (k < n)%nat -> f k == g k) -> Rpsigma f n == Rpsigma g n.
intros; apply Ole_antisym; auto.
apply Rpsigma_le_compat; intros; rewrite H; trivial.
Save.
Hint Resolve Rpsigma_eq_compat.

Lemma Rpsigma_eq_compat_index:
  forall (f g : nat -> Rp) (n m: nat), n=m ->
  (forall k : nat, (k < n)%nat -> f k == g k) -> (Rpsigma f) n == (Rpsigma g) m.
intros; rewrite <- H; auto.
Save.


Lemma Rpsigma_S_lift:
  forall (f : nat -> Rp) (n : nat),
  Rpsigma f (S n) == f O + Rpsigma (fun k : nat => f (S k)) n.
induction n; intros; auto.
rewrite Rpsigma_S.
rewrite IHn.
rewrite Rpplus_assoc.
rewrite (Rpplus_sym (f (S n))).
rewrite <- Rpplus_assoc; auto.
Save.

Lemma Rpsigma_plus_lift:
  forall (f : nat -> Rp) (n m : nat),
  (Rpsigma f) (n + m)%nat ==
  Rpsigma f n + Rpsigma (fun k : nat => f (n + k)%nat) m.
intros f n m; generalize f; clear f; induction n; intros.
simpl plus.
rewrite Rpsigma_0.
rewrite Rpplus_zero_left.
apply Rpsigma_eq_compat; auto.
rewrite Rpsigma_S_lift.
simpl plus.
rewrite Rpsigma_S_lift.
rewrite IHn; auto.
Save.

Lemma Rpsigma_zero : forall f n, 
  (forall k, (k<n)%nat -> f k == R0) -> Rpsigma f n == R0.
induction n; intros; auto.
rewrite Rpsigma_S.
rewrite (H n); auto.
rewrite IHn; auto.
Save.
Hint Resolve Rpsigma_zero.

Lemma Rpsigma_le : forall f n k, (k<n)%nat -> f k <= Rpsigma f n.
induction n; intros.
casetype False; omega.
rewrite Rpsigma_S.
assert (k < n \/ k = n)%nat.
omega.
case H0; intros.
transitivity (Rpsigma f n); auto.
subst; auto.
Save.
Hint Resolve Rpsigma_le.

Lemma Rpsigma_not_zero : forall f n k, (k<n)%nat -> R0 < f k -> R0 < Rpsigma f n.
intros; apply Olt_le_trans with (f k); auto.
Save.

Lemma Rpsigma_zero_elim : forall f n, 
  Rpsigma f n == R0 -> forall k, (k<n)%nat -> f k == R0.
intros; apply Rpeq_class; red; intros.
assert (R0 < Rpsigma f n); auto.
apply Rpsigma_not_zero with k; auto.
apply (Olt_notle _ _ H2); auto.
Save.


Lemma Rpsigma_minus_decr : forall f n, (forall k, f (S k) <= f k) ->
         Rpsigma (fun k => f k - f (S k)) n == f O - f n.
intros f n fmon;induction n.
rewrite Rpsigma_0; auto.
rewrite Rpsigma_S; rewrite IHn.
rewrite Rpplus_sym.
rewrite <- Rpplus_minus_assoc; auto.
rewrite Rpminus_plus_simpl; auto.
elim n; intros; auto.
transitivity (f n0); auto.
Save.

Lemma Rpsigma_minus_incr : forall f n, (forall k, f k <= f (S k)) ->
         Rpsigma (fun k => f (S k) - f k) n == f n - f O.
intros f n fmon;induction n.
rewrite Rpsigma_0; auto.
rewrite Rpsigma_S; rewrite IHn.
rewrite <-  Rpplus_minus_assoc; auto.
elim n; intros; auto.
transitivity (f n0); auto.
Save.         

Instance Rpsigma_mon: monotonic Rpsigma.
red; intros.
intro n; auto.
Save.

Lemma Rpsigma_plus:
  forall (f g : nat -> Rp) (n : nat),
  Rpsigma (fun k : nat => f k + g k) n == Rpsigma f n + Rpsigma g n.
intros; induction n.
repeat rewrite Rpsigma_0; auto.
repeat rewrite Rpsigma_S; rewrite IHn.
repeat rewrite <- Rpplus_assoc.
apply Rpplus_eq_compat; trivial.
Save.

Lemma Rpsigma_mult:
  forall (f : nat -> Rp) (n : nat) (c : Rp),
  Rpsigma (fun k : nat => c * f k) n == c * Rpsigma f n.
intros; induction n.
repeat rewrite Rpsigma_0; auto.
repeat rewrite Rpsigma_S; rewrite IHn.
rewrite Rpdistr_plus_left; apply Rpplus_eq_compat; auto.
Save.

Lemma Rpsigma_U2Rp : forall (f : nat -> U) n, retract f n 
    -> Rpsigma f n == sigma f n.
induction n; intros.
rewrite Rpsigma_0, sigma_0; auto.
rewrite Rpsigma_S, sigma_S.
rewrite <- U2Rp_plus_le; auto.
Save.
Hint Resolve Rpsigma_U2Rp.

Lemma Rpsigma_U2Rp_bound : forall (f : nat -> U) n, Rpsigma f n <= n.
induction n; auto.
rewrite Rpsigma_S; transitivity (R1+n); auto.
Save.
Hint Resolve Rpsigma_U2Rp_bound.

Lemma islub_Rpsigma : forall (F : nat -> nat -> Rp) {M:monotonic F} (n:nat) (f:nat -> Rp),
     (forall k, islub (fun p => F p k) (f k)) -> islub (fun p => Rpsigma (F p) n) (Rpsigma f n).
intros; induction n.
rewrite Rpsigma_0; apply islub_fcte; auto.
rewrite Rpsigma_S.
apply islub_Rpplus with (f:=fun p => F p n) (g:= fun p => Rpsigma (F p) n); auto.
intros p q Hpq; apply M; auto.
intros p q Hpq; apply Rpsigma_le_compat; intros; auto.
apply M; auto.
Save.

Lemma islub_U2Rp : forall (f:nat -> U) (x:U), islub f x -> islub (fun n => U2Rp (f n)) (U2Rp x).
intros f x (Hl1,Hl2); split; intros; auto.
destruct (Rple_lt_dec R1 y) as [H1|H1].
transitivity R1; auto.
assert (Hf:=Rplt1_decimal y H1); auto.
rewrite Hf; apply U2Rp_le_compat; apply Hl2; auto.
intros; apply U2Rp_le_simpl; rewrite <- Hf; auto.
Save.

(** *** Geometrical sum : sigma_0^n x^i *)

Section GeometricalSum.
Variable x : Rp.
Hypothesis xone : x < R1.

Definition sumg (n:nat) : Rp := Rpsigma (Rpexp x) n.

Lemma sumg_0 : sumg 0 = R0.
trivial.
Save.

Lemma sumg_S : forall n, sumg (S n) = (x ^ n) + sumg n.
trivial.
Save.

Instance invx_not0 : notz (R1 - x).
intro; destruct xone.
apply H1.
apply Ole_antisym; auto.
apply Rpminus_zero_le; auto.
Save.
Hint Resolve invx_not0.

Lemma sumg_eq : forall n, sumg n == [1/](R1 - x) * (R1 - x ^ n).
induction n.
rewrite sumg_0, Rpexp_simpl; auto.
rewrite Rpminus_eq; auto.
rewrite sumg_S.
rewrite IHn.
transitivity ([1/](R1 - x) * (R1 - x) * x ^ n + [1/](R1 - x) * (R1 - x ^ n)).
rewrite Rp1div_right; trivial.
rewrite Rpmult_one_left; auto.
rewrite <- Rpmult_assoc.
rewrite <- Rpdistr_plus_left.
apply Rpmult_eq_compat; auto.
rewrite Rpdistr_minus_right.
rewrite Rpmult_one_left.
apply Rpplus_eq_perm_right.
rewrite <- Rpplus_assoc.
rewrite (Rpplus_sym (R1 - x ^ n)), Rpplus_assoc.
rewrite Rpminus_plus_simpl.
rewrite Rpplus_sym; auto.
auto.
Save.

Lemma glb_exp_0 : isglb (fun n => x ^ n) R0.
apply isglb_eq_compat with (fun n => U2Rp (UExp (decimal x) n)) (U2Rp 0); auto.
intro n.
rewrite (Rplt1_decimal x) at 2; trivial.
rewrite <- U2Rp_exp; auto.
rewrite <- (glb_exp_0 (k:=decimal x)); auto.
apply isglb_glb_U; auto.
Save.

Instance mon_Rpexp_lt : monotonic (o2:=Iord Rp) (Rpexp x).
apply Rpexp_mon; auto.
Save.

Definition RpExp : nat -m-> Rp := mon (o2:=Iord Rp) (Rpexp x).

Lemma sumg_lim : islub sumg ([1/](R1 - x)).
apply islub_eq_compat with (fun n => cte nat ([1/](R1 - x)) n *
                                    (cte nat R1 n - x ^ n))
                           ([1/](R1 - x) * (R1 - R0)); auto.
intro n; rewrite sumg_eq; auto.
rewrite Rpminus_zero_right; auto.
apply islub_Rpmult; auto.
apply islub_fcte; auto.
apply (islub_Rpminus (cte nat R1) (fun n => x ^ n)); auto.
apply islub_fcte; auto.
apply glb_exp_0.
Save.

End GeometricalSum.

(** ** Miscelaneous lemmas *)

Lemma U2Rp_half : forall x y:U, 
  U2Rp ([1/2] * x + [1/2]*y) == ([1/2] * U2Rp x) + [1/2] * U2Rp y.
intros; rewrite <- U2Rp_plus_le; auto.
Save.
 

Lemma Rphalf_plus: ([1/2] + [1/2])%Rp == R1.
rewrite U2Rp_plus_le; auto.
rewrite Unth_one_plus; auto.
Save.
Hint Resolve Rphalf_plus.

Lemma Rphalf_refl: forall t : Rp, ([1/2] * t + [1/2] * t)%Rp == t.
intros; rewrite <- Rpdistr_plus_right.
rewrite Rphalf_plus; auto.
Save.
Hint Resolve Rphalf_refl.

Lemma Rple_lt_eps 
  : forall x y:Rp, (forall eps:Rp, R0 < eps -> x <= y + eps) -> x <= y.
intros; destruct (Rple_lt_dec x y) as [H1|H1]; trivial.
exfalso; pose (eps := [1/2] * (x-y)).
assert (R0 < x - y); auto.
assert (R0 < eps).
unfold eps; auto.
assert (y + eps < x).
apply Olt_eq_compat with (y+eps+R0) (y+eps+eps); auto.
rewrite <- Rpplus_assoc; unfold eps.
rewrite Rphalf_refl.
rewrite <- Rpminus_plus_perm_right; auto.
rewrite Rpminus_le_zero; auto.
apply Rpplus_lt_compat_right; auto.
apply (Olt_notle (y+eps) x); auto.
Save.

(** ** Min Max *)

Definition Rpmin r1 r2 := 
   match lt_eq_lt_dec (floor r1) (floor r2) with 
      inleft (left _) => r1 
    | inleft (right _) => mkRp (floor r1) (min (decimal r1) (decimal r2))
    | inright _ => r2
   end.

Lemma min_decimal_lt1 : forall x y, min (decimal x) (decimal y) < 1.
intros; apply Ole_lt_trans with (decimal x); auto.
Save.
Hint Resolve min_decimal_lt1.

Lemma Rpmin_le_right: forall x y : Rp, Rpmin x y <= x.
unfold Rpmin; intros.
destruct (lt_eq_lt_dec (floor x) (floor y)) as [[Hlt|Heq]|Hgt]; auto.
apply Rple_intro_le_floor.
rewrite floor_mkRp_int; auto.
rewrite decimal_mkRp_frac; auto.
Save.

Lemma Rpmin_le_left: forall x y : Rp, Rpmin x y <= y.
unfold Rpmin; intros.
destruct (lt_eq_lt_dec (floor x) (floor y)) as [[Hlt|Heq]|Hgt]; auto.
rewrite Heq; apply Rple_intro_le_floor.
rewrite floor_mkRp_int; auto.
rewrite decimal_mkRp_frac; auto.
Save.
Hint Resolve Rpmin_le_right Rpmin_le_left.

Lemma Rpmin_le: forall x y z : Rp, z <= x -> z <= y -> z <= Rpmin x y.
unfold Rpmin; intros.
destruct (lt_eq_lt_dec (floor x) (floor y)) as [[Hlt|Heq]|Hgt]; auto.
apply (Ule_total (decimal x) (decimal y)); intros; auto.
transitivity x; auto.
rewrite (floor_decimal x) at 1; auto.
apply Rple_intro_le_floor; auto.
repeat (rewrite decimal_mkRp_frac; auto).
rewrite min_eq_left; auto.
transitivity y; auto.
rewrite (floor_decimal y) at 1; auto.
rewrite Heq.
apply Rple_intro_le_floor; auto.
repeat (rewrite decimal_mkRp_frac; auto).
rewrite min_eq_right; auto.
Save.
Hint Immediate Rpmin_le.

Lemma Rpmin_le_sym : forall x y, Rpmin x y <= Rpmin y x.
intros; apply Rpmin_le; auto.
Save.
Hint Resolve Rpmin_le_sym.

Lemma Rpmin_sym : forall x y, Rpmin x y == Rpmin y x.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve Rpmin_sym.

Lemma Rpmin_le_compat_left : forall x y z, x <= y -> Rpmin x z <= Rpmin y z.
intros; apply Rpmin_le; auto.
transitivity x; auto.
Save.
Hint Resolve Rpmin_le_compat_left.

Lemma Rpmin_le_compat_right : forall x y z, y <= z -> Rpmin x y <= Rpmin x z.
intros; rewrite (Rpmin_sym x y); rewrite (Rpmin_sym x z); auto.
Save.
Hint Resolve Rpmin_le_compat_right.

Add Morphism Rpmin  with signature Ole ==> Ole ==> Ole as Rpmin_le_compat.
intros; transitivity (Rpmin y x0); auto.
Save.
Hint Immediate Rpmin_le_compat.

Add Morphism Rpmin  with signature Oeq ==> Oeq ==> Oeq as Rpmin_eq_compat.
intros; apply Ole_antisym; apply Rpmin_le_compat; auto.
Save.
Hint Immediate Rpmin_eq_compat.

Lemma Rpmin_idem: forall x : Rp, Rpmin x x == x.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve Rpmin_idem.

Lemma Rpmin_eq_right : forall x y : Rp, x <= y -> Rpmin x y == x.
intros; apply Ole_antisym; auto.
Save.

Lemma Rpmin_eq_left : forall x y : Rp, y <= x -> Rpmin x y == y.
intros; apply Ole_antisym; auto.
Save.

Hint Resolve Rpmin_eq_right Rpmin_eq_left.

(** ** A simplification tactic *)
Ltac my_rewrite t := setoid_rewrite t || rewrite t.

Ltac Rpsimpl :=  match goal with
    |- context [(Rpplus R0 ?x)]    => my_rewrite (Rpplus_zero_left x)
 |  |- context [(Rpplus ?x R0)]    => my_rewrite (Rpplus_zero_right x)
 |  |- context [(U2Rp U1)]         => my_rewrite U2Rp1_R1
 |  |- context [(U2Rp ?x)]         => Usimpl
 |  |- context [(Rpmult R0 ?x)]     => my_rewrite (Rpmult_zero_left x)
 |  |- context [(Rpmult ?x R0)]     => my_rewrite (Rpmult_zero_right x)
 |  |- context [(Rpmult R1 ?x)]     => my_rewrite (Rpmult_one_left x)
 |  |- context [(Rpmult ?x R1)]     => my_rewrite (Rpmult_one_right x)
 |  |- context [(Rpminus 0 ?x)]    => my_rewrite (Rpminus_zero_left x)
 |  |- context [(Rpminus ?x 0)]    => my_rewrite (Rpminus_zero_right x)
 |  |- context [(Rpmult ?x (Rp1div ?x))] => my_rewrite (Rp1div_right x)
 |  |- context [(Rpmult (Rp1div ?x) ?x)] => my_rewrite (Rp1div_left x)
 (*|  |- context [(0/?x)]      => my_rewrite (Udiv_zero x)
 |  |- context [(?x/1)]      => my_rewrite (Udiv_one x)
 |  |- context [(?x/0)]      => my_rewrite (Udiv_by_zero x); [idtac|reflexivity]
*)
 |  |- context [?x^O] => my_rewrite (Rpexp_0 x)
 |  |- context [?x^(S O)] => my_rewrite (Rpexp_1 x)
 |  |- context [0^(?n)] => my_rewrite Rpexp_zero; [idtac|omega]
 |  |- context [R1^(?n)] => my_rewrite Rpexp_one
 |  |- context [(NRpmult 0 ?x)]     => my_rewrite NRpmult_0
 |  |- context [(NRpmult 1 ?x)]     => my_rewrite NRpmult_1
 |  |- context [(NRpmult ?n 0)]     => my_rewrite NRpmult_zero
 |  |- context [(Rpsigma ?f O)]     => my_rewrite Rpsigma_0
 |  |- context [(Rpsigma ?f (S O))]     => my_rewrite Rpsigma_1
 |  |- (Ole (Rpplus ?x ?y) (Rpplus ?x ?z)) => apply Rpplus_le_compat_right
 |  |- (Ole (Rpplus ?x ?z) (Rpplus ?y ?z)) => apply Rpplus_le_compat_left
 |  |- (Ole (Rpplus ?x ?z) (Rpplus ?z ?y)) => my_rewrite (Rpplus_sym z y);
					      apply Rpplus_le_compat_left
 |  |- (Ole (Rpplus ?x ?y) (Rpplus ?z ?x)) => my_rewrite (Rpplus_sym x y);
                                              apply Rpplus_le_compat_left
 |  |- (Ole (Rpminus ?x ?y) (Rpminus ?x ?z)) => apply Rpminus_le_compat_right
 |  |- (Ole (Rpminus ?x ?z) (Rpminus ?y ?z)) => apply Rpminus_le_compat_left
 |  |- ((Rpplus ?x ?y) == (Rpplus ?x ?z)) => apply Rpplus_eq_compat_right
 |  |- ((Rpplus ?x ?z) == (Rpplus ?y ?z)) => apply Rpplus_eq_compat_left
 |  |- ((Rpplus ?x ?z) == (Rpplus ?z ?y)) => my_rewrite (Rpplus_sym z y);
                                             apply Rpplus_eq_compat_left
 |  |- ((Rpplus ?x ?y) == (Rpplus ?z ?x)) => my_rewrite (Rpplus_sym x y);
					     apply Rpplus_eq_compat_left
 |  |- ((Rpminus ?x ?y) == (Rpminus ?x ?z)) => apply Rpminus_eq_compat_right
 |  |- ((Rpminus ?x ?z) == (Rpminus ?y ?z)) => apply Rpminus_eq_compat_left
 |  |- (Ole (Rpmult ?x ?y) (Rpmult ?x ?z)) => apply Rpmult_le_compat_right
 |  |- (Ole (Rpmult ?x ?z) (Rpmult ?y ?z)) => apply Rpmult_le_compat_left
 |  |- (Ole (Rpmult ?x ?z) (Rpmult ?z ?y)) => my_rewrite (Rpmult_sym z y);
                                             apply Rpmult_le_compat_left
 |  |- (Ole (Rpmult ?x ?y) (Rpmult ?z ?x)) => my_rewrite (Rpmult_sym x y);
                                             apply Rpmult_le_compat_left
 |  |- ((Rpmult ?x ?y) == (Rpmult ?x ?z)) => apply Rpmult_eq_compat_right
 |  |- ((Rpmult ?x ?z) == (Rpmult ?y ?z)) =>  apply Rpmult_eq_compat_left
 |  |- ((Rpmult ?x ?z) == (Rpmult ?z ?y)) => my_rewrite (Rpmult_sym z y);
                                             apply Rpmult_eq_compat_left
 |  |- ((Rpmult ?x ?y) == (Rpmult ?z ?x)) => my_rewrite (Rpmult_sym x y);
                                             apply Rpmult_eq_compat_left
end.

(** ** More lemmas on [notz] *)

Instance notz_S : forall k, notz (N2Rp (S k)).
Proof.
  intros k H.
  rewrite <- N2Rp_eq_rewrite in H.
  discriminate H.
Qed.
Hint Resolve notz_S.

Instance notz_Rpexp : forall r n, notz r -> notz (r^n).
Proof.
  intros; induction n.
  simpl; auto.
  simpl Rpexp; auto.
Qed.
Hint Resolve notz_Rpexp.

Instance notz_square : forall r, notz r -> notz (r^2).
Proof.
  auto.
Qed.
Hint Resolve notz_square.

(*
Lemma norm_from_O_false : forall x : Rp, norm R0 x -> False.
Proof.
  intros x (_,(H,_)).
  auto.
Qed.

Lemma norm_to_O_false : forall x : Rp, norm x R0 -> False.
Proof.
  intros x (H,(_,_)).
  discriminate H.
Qed.
*)

Lemma notz_Unth : forall n, notz ([1/]1+n)%U.
Proof.
  intros n; unfold notz.
  rewrite U2Rp_not_0_equiv.
  apply Unth_not_null with (n := n).
Qed.
Hint Resolve notz_Unth.

Lemma notz_lt_0 : forall x, R0 < x -> notz x.
Proof.
  intros x Hlt.
  apply Olt_neq.
  assumption.
Qed.
Hint Resolve notz_lt_0.

Lemma notz_lt : forall x y, x < y -> notz y.
Proof.
  intros.
  assert (R0 < y); [|auto].
  apply (Ole_lt_trans R0 x y); auto.
Qed.

Lemma notz_lt_minus : forall x y, x < y -> notz (y-x).
Proof.
  intros x y Hlt.
  auto.
Qed.
Hint Resolve notz_lt_minus.

Lemma notz_N2Rp_lt_0 : forall n:nat, (0 < n)%nat -> notz n.
Proof.
  intros [|n] Hn.
  inversion Hn.
  auto.
Qed.
Hint Resolve notz_N2Rp_lt_0.

Lemma notz_Rpdiv : forall x y, notz x -> notz y -> notz (x / y).
Proof.
  unfold Rpdiv; auto.
Qed.
Hint Resolve notz_Rpdiv.


(** ** Compatibility of operations on [U] and [R+] *)

Lemma U2Rp_Nmult_eq : forall (n:nat) (u:U), n * u <= R1 ->
  U2Rp (n */ u) == N2Rp n * U2Rp u.
Proof.
  induction n; intros.
  auto.
  rewrite Nmult_S.
  replace (S n) with (1+n)%nat by omega.
  rewrite <- N2Rp_plus;
   rewrite Rpdistr_plus_right;
    rewrite Rpmult_one_left.
  assert (n * u <= N2Rp 1) as H' by (transitivity (S n * u); auto).
  rewrite <- U2Rp_plus_le.
  rewrite IHn; auto.
  assert (U2Rp u <= 1%nat - (n * u)).
    apply Rpplus_le_perm_right.
    apply Ole_trans with (y := S n * u) (2 := H).
    replace (S n) with (1+n)%nat by omega;
     rewrite <- N2Rp_plus;
      rewrite Rpdistr_plus_right;
       rewrite Rpmult_one_left; reflexivity.
  rewrite <- IHn in H0; auto.
(*  setoid_replace (N2Rp 1) with (U2Rp 1) in H0 by auto.*)
  rewrite <- U2Rp_Uinv in H0.
  apply U2Rp_le_simpl.
  assumption.
Qed.
Hint Resolve U2Rp_Nmult_eq.

Lemma Nmult_def_Rp : forall n x, Nmult_def n x -> n * x <= R1.
Proof.
  intros.
  destruct n.
  Rpsimpl; auto.
  simpl in H.
  replace (S n) with (n+1)%nat by omega; rewrite <- N2Rp_plus.
  rewrite Rpdistr_plus_right; Rpsimpl.
  rewrite NRpmult_mult.
  rewrite NRp_Nmult_eq.
  rewrite H.
  rewrite U2Rp_plus_le; auto.
  rewrite H.
  apply Ole_lt_trans with ([1-]([1/]1+n))%U; auto.
Qed.

Lemma U2Rp_Nmult_Nmult_def : forall n x, Nmult_def n x ->
  U2Rp (Nmult n x) == n * x.
Proof.
  intros.
  apply U2Rp_Nmult_eq.
  apply Nmult_def_Rp.
  assumption.
Qed.

Lemma U2Rp_Unth : forall n, U2Rp (Unth n) == Rp1div (N2Rp (S n)).
Proof.
  intros.
  apply Rpmult_eq_simpl_left with (S n); auto.
  rewrite Rp1div_left; auto.
  rewrite <- U2Rp_Nmult_eq.
  setoid_replace (N2Rp 1) with (U2Rp 1); auto.
  apply Nmult_def_Rp; auto.
Qed.

Lemma Rpexp_Rpmult_distr :
  forall r1 r2 k, (r1 * r2) ^ k == r1^k * r2^k.
Proof.
  intros; induction k.
  auto.
  simpl Rpexp.
  rewrite IHk.
  repeat rewrite Rpmult_assoc.
  apply Rpmult_eq_compat; auto.
  rewrite Rpmult_sym.
  repeat rewrite Rpmult_assoc.
  apply Rpmult_eq_compat; auto.
Qed.
Hint Resolve Rpexp_Rpmult_distr.
