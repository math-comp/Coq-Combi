Require Export Arith.
Require Export Omega.
Set Implicit Arguments.

(** * Markov rule *)

(** ** Decidable predicates on natural numbers *)

Definition dec (P:nat -> Prop) := forall n, {P n} + {~ P n}.

Record Dec : Type := mk_Dec {prop :> nat -> Prop; is_dec : dec prop}.

(** ** Definition of a successor function on predicates 
    - PS P n = P (n+1) *)

Definition PS : Dec -> Dec.
intro P; exists (fun n => P (S n)).
intro n; exact (is_dec P (S n)).
Defined.

(** ** Order on predicates 
    - P <= Q iff forall n, Q n -> exists m < n, P m *)

Definition ord (P Q:Dec) := forall n, Q n -> exists m, m < n /\ P m.

Lemma ord_eq_compat : forall (P1 P2 Q1 Q2:Dec), 
        (forall n, P1 n -> P2 n) -> (forall n, Q2 n -> Q1 n) 
        -> ord P1 Q1 -> ord P2 Q2.
red; intros.
case (H1 n); auto.
intros m (H3,H4); exists m; auto.
Save.

Lemma ord_not_0 : forall P Q : Dec, ord P Q -> ~ Q 0.
intros P Q H H1; case (H 0 H1); intros m (H2,H3); casetype False; omega.
Save.

Lemma ord_0 : forall P Q : Dec, P 0 -> ~ Q 0 -> ord P Q.
intros P Q H H1 n; exists 0; destruct n; intuition.
Save.

(** ** Chaining two predicates 
       - PP P Q : first elt of P then Q : PP P Q 0 = P 0, PP P Q (n+1) = Q n *)

Definition PP : Dec -> Dec -> Dec.
 intros P Q; exists (fun n => match n with O => P 0 | S p => Q p end).
intro n; case n.
apply (is_dec P 0).
intro p; apply (is_dec Q p).
Defined.


Lemma PP_PS : forall (P:Dec) n, PP P (PS P) n <-> P n.
intros; case n; simpl; intuition.
Save.

Lemma PS_PP : forall (P Q:Dec) n, PS (PP P Q) n <-> Q n.
unfold PS,PP; simpl; intuition.
Save.

Lemma ord_PS : forall P : Dec, ~ P 0 -> ord (PS P) P.
intros P H n Qn.
destruct n.
case H; trivial.
exists n; auto.
Save.

Lemma ord_PP : forall (P Q: Dec), ~ P 0 -> ord Q (PP P Q).
intros P Q H n Qn.
destruct n.
case H; trivial.
exists n; auto.
Save.

Lemma ord_PS_PS : forall P Q : Dec, ord P Q -> ~ P 0 -> ord (PS P) (PS Q).
red; intros.
case (H (S n)); auto.
intros m Hm.
destruct m; intros.
case H0; intuition.
exists m; intuition.
Save.

(** ** Accessibility of the order relation *)
Lemma Acc_ord_equiv : forall P Q : Dec, 
   (forall n, P n <-> Q n) -> Acc ord P -> Acc ord Q.
intros; destruct H0; intros.
apply Acc_intro; intros R HR.
apply H0.
apply ord_eq_compat with R Q; intuition.
case (H n); auto.
Save.

Lemma Acc_ord_0 : forall P : Dec, P 0 -> Acc ord P.
intros; apply Acc_intro; intros Q H1.
case (ord_not_0 H1 H).
Save.
Hint Immediate Acc_ord_0.

Lemma Acc_ord_PP : forall (P Q:Dec), Acc ord Q -> Acc ord (PP P Q).
intros P Q H; generalize P; clear P; elim H; clear Q H.
intros Q AQ APP P.
apply Acc_intro; intros R H1.
case (is_dec R 0); intro.
auto.
apply Acc_ord_equiv with (PP R (PS R)).
exact (PP_PS R).
apply APP.
apply ord_eq_compat with (PS R) (PS (PP P Q)); auto.
apply ord_PS_PS; auto.
Save.

Lemma Acc_ord_PS : forall (P:Dec), Acc ord (PS P) -> Acc ord P.
intros; apply Acc_ord_equiv with (PP P (PS P)).
exact (PP_PS P).
apply Acc_ord_PP; auto.
Save.

Lemma Acc_ord : forall (P:Dec), (exists n,P n) -> Acc ord P.
intros P (n,H).
generalize P H; elim n; intros.
auto.
apply Acc_ord_PS; auto.
Save.

(** ** Definition of the [minimize] function *)

Fixpoint min_acc (P:Dec) (a:Acc ord P) {struct a} : nat := 
   match is_dec P 0 with
      left _ => 0 | right H => S (min_acc (Acc_inv a (PS P) (ord_PS P H))) 
   end.

Definition minimize (P:Dec) (e:exists n, P n) : nat := min_acc (Acc_ord P e).

Lemma minimize_P : forall (P:Dec) (e:exists n, P n), P (minimize P e).
unfold minimize.
intros; elim (Acc_ord P e) using Acc_inv_dep.
intros Q H H1.
simpl.
case (is_dec Q 0); auto.
intro n; assert (H2:=H1 (PS Q) (ord_PS Q n)); auto.
Save.

Lemma minimize_min : forall (P:Dec) (e:exists n, P n) (m:nat), m < minimize P e -> ~ P m.
unfold minimize.
intros P e; elim (Acc_ord P e) using Acc_inv_dep.
simpl; intros Q H1 H2 m.
case (is_dec Q 0).
red; intros; omega.
intro n; assert (H3:=H2 (PS Q) (ord_PS Q n)).
destruct m; intros; auto.
assert (H4:m < min_acc (H1 (PS Q) (ord_PS Q n))); try omega.
exact (H3 m H4).
Save.

Lemma minimize_incr : forall (P Q:Dec)(e:exists n, P n)(f:exists n, Q n),
            (forall n, P n -> Q n) -> minimize Q f <= minimize P e.
intros; assert (~ minimize P e < minimize Q f); try omega.
red; intro; assert (~ Q (minimize P e)).
apply minimize_min with f; trivial.
apply H1; apply H; apply minimize_P.
Save.
