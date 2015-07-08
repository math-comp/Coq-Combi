(** * Rlow.v: Definition of lower real numbers *)


Add Rec LoadPath "." as ALEA.

Require Export Misc.
Require Export Ccpo.
Set Implicit Arguments.
Require Export QArith.
Open Local Scope Q_scope.
Open Local Scope O_scope.
Require Export QOrderedType.
Require Export Qminmax.

(** ** lower reals are monotonic sequences of rationals *)

(** *** Extra properties of rational numbers Q *)
Hint Resolve Q.le_max_l Q.le_max_r : qarith.

Lemma Qmult_le_compat_l:
  forall x y z : Q, (x <= y)%Q -> (0 <= z)%Q -> (z * x <= z * y)%Q.
intros; do 2 rewrite (Qmult_comm z); apply Qmult_le_compat_r; auto.
Save.
Hint Resolve Qmult_le_compat_l.

Lemma Qmult_inv_l : forall x : Q, ~ (x == 0)%Q -> (/ x * x == 1)%Q.
intros; rewrite Qmult_comm; apply Qmult_inv_r; auto.
Save.
Hint Resolve Qmult_inv_l.

Lemma Qplus_le_lt_compat:
  forall x y z t : Q, (x <= y)%Q -> (z < t)%Q -> (x + z < y + t)%Q.
intros; rewrite (Qplus_comm x); rewrite (Qplus_comm y); 
 apply Qplus_lt_le_compat; auto.
Save.

Lemma Qplus_lt_compat_r:
  forall x y z : Q, (x < y)%Q -> (x + z < y + z)%Q.
intros; apply Qplus_lt_le_compat; trivial with qarith.
Save.

Lemma Qplus_lt_compat_l:
  forall x y z : Q, (x < y)%Q -> (z + x < z + y)%Q.
intros; apply Qplus_le_lt_compat; trivial with qarith.
Save.

Hint Resolve Qplus_lt_compat_r Qplus_lt_compat_l : qarith.


(** Order on Q *)

Instance QO : ord Q := 
    { Oeq := fun n m : Q => n == m;
      Ole := fun n m : Q => (n <= m)%Q}.
abstract (apply Build_Order; intros; 
[auto with qarith |
split; intros ; [
apply Qle_antisym; destruct H; trivial |
rewrite H; auto with qarith ] |
intros n m p H1 H2; apply Qle_trans with m; trivial]).
Defined.

Lemma Ole_Qle : forall p q : Q, (p <= q) <-> (p <= q)%Q.
split; trivial with qarith.
Save.

Lemma Oeq_Qeq : forall p q : Q, (p == q) <-> (p == q)%Q.
split; trivial with qarith.
Save.

Lemma Olt_Qlt : forall p q : Q, (p < q) <-> (p < q)%Q.
split; intros.
destruct H.
apply Qnot_le_lt; intro.
apply H0; apply Qle_antisym; auto with qarith. 
apply Ole_diff_lt.
apply Ole_Qle; auto with qarith.
rewrite Oeq_Qeq.
intro.
rewrite H0 in H.
apply (Qlt_irrefl q); trivial.
Save.

Hint Immediate Olt_Qlt Ole_Qle Oeq_Qeq.

(** ** Definition of Rlow *)

Definition Rlow := nat -m> Q.

Lemma Rlow_mon : forall (r:Rlow) n m, (n <=m)%nat -> (r n <= r m).
intros r n m H; apply (fmonotonic r); auto.
Save.
Hint Resolve Rlow_mon.

(** ** From Q to Rlow *)

Definition Q_inject (p:Q) : Rlow := mseq_cte p.

Notation "[ n ]" := (Q_inject n) : Rl_scope.

Local Open Scope Rl_scope.
Delimit Scope Rl_scope with Rl.
Bind Scope Rl_scope with Rlow.

(** ** Order and equality on Rlow *)

Definition nat2Q (n:nat) : Q := inject_Z (Z.of_nat n).

Lemma nat2Q_pos : forall n, (0 < nat2Q (S n))%Q.
auto with qarith.
Save.
Hint Resolve nat2Q_pos.

Definition eps (n:nat) : Q := / nat2Q (S n).

Lemma eps_pos : forall n, (0 < eps n)%Q.
unfold eps.
auto with qarith.
Save.
Hint Resolve eps_pos.

Add Parametric Morphism : eps with signature le --> Ole as eps_le_compat.
unfold eps; intros.
apply Qle_shift_inv_r; auto with qarith.
apply Qle_trans with (/ nat2Q (S y) * nat2Q (S y)); auto with qarith.
rewrite
 Qmult_inv_l; auto with qarith.
apply Qmult_le_compat_l; auto with qarith.
unfold nat2Q; rewrite <- Zle_Qle.
apply inj_le; auto with arith.
Save.
Hint Resolve eps_le_compat.

Lemma minus_eps : forall p n, (p - eps n < p)%Q.
intros; apply Qplus_lt_l with (eps n); ring_simplify; auto with qarith.
rewrite Qplus_comm.
apply Qle_lt_trans with (0+p)%Q.
ring_simplify; auto with qarith.
apply Qplus_lt_le_compat; auto with qarith.
Save.
Hint Resolve minus_eps.


(** A lower real r corresponds to a set of rationals : p < r with p in Q *)

Definition QltRl (p:Q) (r:Rlow) := exists n, (p < r n)%Q.

Definition Rlle (r s : Rlow) := forall p, QltRl p r -> QltRl p s.

Definition Rleq r s := Rlle r s /\ Rlle s r.

Lemma Rlle_refl : forall r, Rlle r r.
red; intros; auto.
Save.
Hint Resolve Rlle_refl.

Lemma Rlle_trans : forall r s t, Rlle r s -> Rlle s t -> Rlle r t.
unfold Rlle; intros; auto.
Save.

Lemma Rlle_antisym : forall r s, Rlle r s -> Rlle s r -> Rleq r s.
red; auto.
Save.

Instance Rlow_ord : ord Rlow := { Oeq := Rleq; Ole := Rlle }.
abstract (apply Build_Order; [auto |
unfold Rleq; split; auto |
red; intros x y z Hxy Hyz; apply Rlle_trans with y; auto]).
Defined.

(** A sufficent for proving the relation between two reals *)

Lemma Rlle_intro (r s : Rlow) : (forall n, exists m, r n <= s m) -> r <= s.
simpl; red; intros.
destruct H0 as (n,Hn).
destruct (H n) as (m,Hm).
exists m; apply Qlt_le_trans with (r n); auto.
Save.

Lemma Rlle_intro_triv (r s : Rlow) : (forall n, (r n <= s n)) -> r <= s.
intros; apply Rlle_intro; intro n; exists n; auto.
Save.

Lemma Rleq_intro_triv (r s : Rlow) : (forall n, (r n == s n)) -> r == s.
intros; apply Ole_antisym; apply Rlle_intro_triv; auto with qarith.
Save.

Definition Rllift (r:Rlow) k : Rlow := mseq_lift_left r k.

Lemma Rllift_eq : forall r k n, Rllift r k n = r (k + n)%nat.
trivial.
Save.

Lemma Rleq_lift : forall r k, r == Rllift r k.
intros; apply Rlle_antisym.
apply Rlle_intro_triv; intros; rewrite Rllift_eq; auto with arith.
apply Rlle_intro; intros n; exists (k + n)%nat; auto.
Save.

Lemma Rlle_elim (r s : Rlow) : r <= s -> forall n, exists m, (r n - eps n < s m)%Q.
intros; change (QltRl (r n - eps n) s).
apply (H (r n - eps n)).
exists n; auto with qarith.
Save.

Lemma Rleq_elim_lr (r s : Rlow) 
   : r == s -> forall n, exists m, (r n - eps n < s m)%Q.
intros; apply Rlle_elim; auto.
Save.
 
Lemma Rleq_elim_rl (r s : Rlow) 
   : r == s -> forall n, exists m, (s n - eps n < r m)%Q.
intros; apply Rlle_elim; auto.
Save.

Lemma Qle_Rlle : forall p q, (p <= q) -> [p] <= [q].
intros; apply Rlle_intro_triv; auto.
Save.

Lemma Rllt_intro : forall p r s, QltRl p s -> ~ QltRl p r -> r < s.
intros p r s (n,Hn) H.
assert (forall k, (r k <= p)%Q).
intros; case (Qlt_le_dec p (r k)); intro; trivial.
case H; exists k; trivial.
assert (r <= s).
intros q (k,Hk).
exists n.
apply Qlt_trans with (r k); auto with qarith.
apply Qle_lt_trans with p; auto with qarith.
red; split; auto.
simpl; intros (_,Hle2).
destruct (Hle2 p).
exists n; auto.
absurd (p < r x)%Q; auto with qarith.
Save.

Lemma QltRl_Q : forall p q, p < q <-> QltRl p [q].
split.
exists O.
change (p < q)%Q.
apply Olt_Qlt; trivial.
intros (n,Hn); apply Olt_Qlt; trivial.
Save.

Lemma notQltRl_Q : forall p q, q <= p <-> ~ QltRl p [q].
intros; rewrite <- QltRl_Q.
rewrite Olt_Qlt, Ole_Qle.
rewrite Qgt_alt, Qle_alt; tauto.
Save.

Definition mid p q : Q := ((1#2)*(p+q))%Q.

Lemma mid_l : forall p q, p < q -> p < mid p q.
intros; unfold mid; apply Ole_lt_trans with ((1#2)*(p+p))%Q.
ring_simplify; trivial with qarith.
rewrite Olt_Qlt in *; apply Qmult_lt_l; auto with qarith.
Save.
Hint Resolve mid_l.

Lemma mid_r : forall p q, p < q -> mid p q < q.
intros; unfold mid; apply Olt_le_trans with ((1#2)*(q+q))%Q.
rewrite Olt_Qlt in *; apply Qmult_lt_l; auto with qarith.
ring_simplify; trivial with qarith.
Save.
Hint Resolve mid_r.

Lemma Qlt_Rllt : forall p q, (p < q) -> [p] < [q].
intros; apply Rllt_intro with (mid p q); auto with qarith.
apply QltRl_Q; auto with qarith.
apply notQltRl_Q; auto with qarith.
apply Ole_lt_trans with p; auto with qarith.
Save.


Lemma Rllt_Qlt : forall p q, [p] < [q] -> p < q.
intros; case (Qlt_le_dec p q); intro.
apply Olt_Qlt; trivial.
case (Olt_antirefl [p]).
apply Olt_le_trans with [q]; auto with qarith.
apply Qle_Rlle; auto with qarith.
Save.

Lemma Rlle_Qle : forall p q, [p] <= [q] -> (p <= q).
intros; case (Qlt_le_dec q p); intro; trivial.
case (Olt_antirefl [q]).
apply Olt_le_trans with [p]; auto with qarith.
apply Qlt_Rllt; auto with qarith.
apply Olt_Qlt; trivial.
Save.

Hint Resolve Qle_Rlle Qlt_Rllt.
Hint Immediate Rlle_Qle Rllt_Qlt.

Lemma Qeq_Rleq : forall p q, (p == q) -> [p] == [q].
intros; apply Rlle_antisym; apply Qle_Rlle; rewrite H; auto.
Save.

Lemma Rleq_Qeq : forall p q, [p] == [q] -> (p == q).
intros p q H; apply Qle_antisym; apply Rlle_Qle; rewrite H; auto.
Save.
Hint Resolve Qeq_Rleq.
Hint Immediate Rleq_Qeq.

Lemma QRlle (p:Q) (r:Rlow) : forall k, (p <= r k) -> [p] <= r.
intros; apply Rlle_intro; intros n; exists k; auto.
Save.

Lemma RlQle (p:Q) (r:Rlow) : (forall n, r n <= p) -> r <= [p].
intros; apply Rlle_intro; intros n; exists O; auto.
Save.
Hint Resolve RlQle.


(** ** Operations on Rlow *)

Definition Rl_map (f:Q-m>Q) (r:Rlow) : Rlow := f@r.
Definition Rl_map2 (f:Q-m>Q-m>Q) (r s:Rlow) : Rlow := (f@2 r) s.

Lemma Rl_map_eq : forall f r n, Rl_map f r n = f (r n).
trivial.
Save.
Hint Resolve Rl_map_eq.

Lemma Rl_map2_eq : forall f r s n, Rl_map2 f r s n = f (r n) (s n).
trivial.
Save.
Hint Resolve Rl_map2_eq.

Lemma Rl_map_Q : forall f q, Rl_map f [q] == [f q].
intros; apply Rleq_intro_triv; auto.
Save.

Lemma Rl_map2_Q : forall f p q, Rl_map2 f [p] [q] == [f p q].
intros; apply Rleq_intro_triv; auto.
Save.

(** Addition **)

Instance Qplus_mon : monotonic2 Qplus.
intros x y z t H1 H2; simpl in *; apply Qplus_le_compat; trivial.
Save.

Definition QPlus : Q-m> Q -m> Q := mon2 Qplus.

Definition Rlplus : Rlow -> Rlow -> Rlow := Rl_map2 QPlus.

Infix "+" := Rlplus : Rl_scope. 

Lemma Rlplus_eq : forall x y n, (x + y) n = (x n + y n)%Q.
trivial.
Save.
Hint Resolve Rlplus_eq.

Instance Qminus_mon1 (p:Q) : monotonic (fun q => q - p).
intros x y H1; simpl in *.
apply Qplus_le_l with p.
ring_simplify; trivial.
Save.

Definition QMinus1 (p:Q) : Q -m> Q := mon (fun q => q - p).

Definition RlminusQ (r:Rlow) (p: Q) : Rlow := Rl_map (QMinus1 p) r.

Lemma RlminusQ_eq : forall r p n, RlminusQ r p n = r n - p.
trivial.
Save.
Hint Resolve  RlminusQ_eq.

Class Qpos (p:Q) := ispos : (0 <= p)%Q.

Instance Qmult_mon_l (p:Q) {H:Qpos p} : monotonic (fun q => p * q).
intros x y H1; simpl in *.
setoid_replace (p * x) with (x * p); try ring.
setoid_replace (p * y) with (y * p); try ring.
apply Qmult_le_compat_r; trivial.
Save.

Instance Qmult_mon_r (p:Q) {H:Qpos p} : monotonic (fun q => q * p).
intros x y H1; simpl in *.
apply Qmult_le_compat_r; trivial.
Save.

Definition QMult_l p {H:Qpos p} : Q -m> Q := mon (fun q => p * q).
Definition QMult_r (p:Q) {H:Qpos p} : Q -m> Q := mon (fun q => q * p).

Arguments QMult_l p [H].
Arguments QMult_r p [H].

Definition RlmultQ (r:Rlow) (p : Q) {H:Qpos p} := Rl_map (QMult_r p) r.
Definition QmultRl (p : Q) {H:Qpos p} (r:Rlow) := Rl_map (QMult_l p) r.

Arguments RlmultQ r p [H].
Arguments QmultRl p [H] r.


(** Taking the max of the n first elements of a sequence of rationals *)

Fixpoint Qmaxn (f:nat->Q) n : Q := 
   match n with O => f O
             | S p => Qmax (Qmaxn f p) (f (S p))
   end.

Lemma Qmaxn_le_max : forall f n k, (k <= n)%nat -> (f k <= Qmaxn f n)%Q.
induction n; simpl; intros; auto with qarith.
replace k with O; try omega; auto with qarith.
rewrite NPeano.Nat.le_succ_r in H.
destruct H.
apply Qle_trans with (Qmaxn f n); auto with qarith.
subst; auto with qarith.
Save.

Lemma Qmaxn_eq_max : forall (f:nat -> Q) n, exists2 k:nat, (k <= n)%nat & (f k == Qmaxn f n)%Q.
induction n; simpl.
exists O; auto with qarith.
destruct (Q.max_spec_le (Qmaxn f n) (f (S n))) as [(H1,H2)|(H1,H2)].
exists (S n); auto.
rewrite H2; auto with qarith.
destruct IHn as (k,H3,H4).
exists k; auto with arith.
rewrite H2; auto with qarith.
Save.


Add Parametric Morphism : Qmaxn with signature Ole ==> le ==> Qle as Qmaxn_le_compat.
intros f g H n m Hnm.
destruct (Qmaxn_eq_max f n) as (k,Hk1,Hk2).
rewrite <- Hk2.
apply Qle_trans with (g k).
apply (H k).
apply Qmaxn_le_max; omega.
Save.

Add Parametric Morphism : Qmaxn with signature Oeq ==> eq ==> Qeq as Qmaxn_eq_compat.
intros f g H n.
apply Qle_antisym; apply Qmaxn_le_compat; auto.
Save.

(* build a real from an ordinary sequence of rationals *)
Instance Qmaxn_mon (f : nat -> Q) : monotonic (Qmaxn f).
red; apply Qmaxn_le_compat; auto.
Save.

Definition Rlbuild (f : nat -> Q) : Rlow := mon (Qmaxn f).

(* build a real from a monotonic sequence of sequences of rationals using max and diagonalisation *) 

Instance Qmaxn_diag_mon (f : nat -m> (nat -> Q)) : monotonic (fun n => Qmaxn (f n) n).
apply nat_monotonic.
intros; apply Qmaxn_le_compat; auto with arith.
Save.

Definition Rldiag (f : nat -m> (nat -> Q)) : Rlow := mon (fun n => Qmaxn (f n) n).

Lemma Rldiag_eq : forall (f : nat -m> (nat -> Q)) n, Rldiag f n = Qmaxn (f n) n.
trivial.
Save.
Hint Resolve Rldiag.

(** Least upper bound on Rlow *)

Instance Rlshift_mon (fr : nat -> Rlow) : monotonic (fun n => fun k => fr k n).
intros n m Hnm k; simpl.
apply (fmonotonic (fr k)); auto.
Save.

Definition Rllub (fr : nat -> Rlow) : Rlow := Rldiag (mon (fun n => fun k => fr k n)).

Lemma Rllub_eq : forall (fr : nat -> Rlow) n, Rllub fr n = Qmaxn (fun k => fr k n) n.
trivial.
Save.
Hint Resolve Rllub_eq.

Lemma Rlle_lub : forall (fr : nat -> Rlow) n,  fr n <= Rllub fr.
intros; apply Rlle_intro; intro p.
pose (m:=Max.max n p).
exists m.
assert (n <= m)%nat.
unfold m; apply Max.le_max_l.
assert (p <= m)%nat.
unfold m; apply Max.le_max_r.
transitivity (fr n m); auto.
rewrite Rllub_eq.
simpl; apply (Qmaxn_le_max (fun k : nat => (fr k) m) H).
Save.

Lemma Rllub_le 
  : forall (fr : nat -> Rlow) r, (forall n, fr n <= r) -> Rllub fr <= r.
intros fr r H p (n,Hpn).
rewrite Rllub_eq in Hpn.
destruct (Qmaxn_eq_max (fun k : nat => (fr k) n) n) as (k,H1,H2).
destruct (H k p) as (m,Hm).
exists n.
rewrite H2; auto.
exists m; auto with qarith.
Save.


