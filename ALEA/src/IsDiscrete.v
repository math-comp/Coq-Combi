(** * IsDiscrete.v: distributions over discrete domains *)
(** Contributed by David Baelde. This has been adapted from Certicrypt : 
      Santiago Zanella and Benjmain Grégoire. *)

(* begin hide *)
Add Rec LoadPath "." as ALEA.

Require Export List.
Require Export Arith.
Require Export Prog.
Require Export Setoid.
Require Export Cover.

Open Scope U_scope.

Set Implicit Arguments.
(* end hide *)

(** ** Definition of discrete domains and decidable equalities *)

Class Discrete_domain (A:Type) :=
  { points : nat -> A ;
    points_surj : forall x, exists n, points n = x }.

Class DecidEq (A:Type) :=
  { eq_dec : forall x y : A, { x=y }+{ x<>y } }.

(** ** Useful functions on discrete domains *)
Section Discrete.

  Variable A : Type.
  Hypothesis A_discrete : Discrete_domain A.
  Hypothesis A_decidable : DecidEq A.

  Definition uequiv : A -> MF A := fun a => carac (eq_dec a).

  Lemma cover_uequiv : forall a, cover (eq a) (uequiv a).
  Proof.
    intro a.
    unfold uequiv.
    apply cover_dec.
  Qed.

  (** [not_first_repr k] decide if [points k] is not the first point in is class,
     in that case [points k] is not the representant of the class *)

  Definition not_first_repr k := sigma (fun i => uequiv (points k) (points i)) k.

  Lemma cover_not_first_repr :  
   cover (fun k => exc (fun k0 => (k0 < k)%nat /\ (points k) = (points k0))) not_first_repr.
  Proof.
   red; split; intros.
   apply H;[auto | intros k0 (H1, H2)].
   apply Ole_trans with (2:= sigma_le (fun i : nat => uequiv (points x) (points i)) H1).
   rewrite (cover_eq_one _ (cover_uequiv (points x)) H2); trivial.
   unfold not_first_repr; rewrite sigma_zero; trivial; intros.
   apply (cover_elim (cover_uequiv (points x)) (points k)); [auto | | ];
   intros [H4 H5]; trivial.
   elim H; apply exc_intro with k; auto.
  Qed.

  (** [in_classes a] decides if [a] is in relation with one element of [points] *)
  Definition in_classes a := serie (fun k => uequiv a (points k)).

  Definition In_classes a := exc (fun k => a = (points k)).

  Lemma cover_in_classes : cover In_classes in_classes.
  Proof.
   unfold In_classes; red; split; intros.
   apply H;[auto | intros k H1].
   apply Ole_trans with (2:=serie_le (fun k : nat => uequiv x (points k)) k).
   rewrite (cover_eq_one _ (cover_uequiv x) H1); trivial.
   unfold in_classes; rewrite serie_zero; trivial.
   intros k; apply (cover_elim (cover_uequiv x) (points k)); [auto | | ]; intros [H4 H5]; trivial.
    elim H; apply exc_intro with k; trivial.
  Qed.

  (** [in_class a k] decides if [a] is in relation with [points k] and
     [points k] is the representant of it class *)
  Definition in_class a k := [1-] (not_first_repr k) * uequiv (points k) a.

  Definition In_class a k :=
     (points k) = a /\
     (forall k0, (k0 < k)%nat -> ~ (points k = points k0)).
  
  Lemma cover_in_class : forall a, cover (In_class a) (in_class a).
  Proof.
   unfold in_class, In_class;split;intros.
   destruct H.
   rewrite (cover_eq_one _ (cover_uequiv (points x)) H); Usimpl.
   rewrite (cover_eq_zero _ cover_not_first_repr);[auto| ].
   intros Hex;apply Hex;[auto | intros].
   destruct H1;apply (H0 x0);trivial.
   apply (cover_elim (cover_uequiv (points x)) a);[auto | | ];intros [H1 H2].
   rewrite H2;trivial.
   apply (cover_elim cover_not_first_repr x);[auto | | ];intros [H3 H4].
   elim H;split;trivial.
   red;intros;apply H3.
   apply exc_intro with k0;auto.
   rewrite H4;Usimpl;auto.
  Qed.

  Lemma in_class_wretract : forall x, wretract (in_class x).
  Proof.
   red; intros.
   apply (cover_elim (cover_in_class x) k);[auto | | ];intros [H H0];
   rewrite H0;[auto | ].
   rewrite sigma_zero; [auto | intros].
   destruct H;apply (cover_eq_zero _ (cover_in_class x)).
   intros (H3, H4).
   elim (H2 _ H1).
   transitivity x; auto.
  Qed.
 
  Lemma in_classes_refl : forall k, in_classes (points k) == 1.
  Proof.
   intros k; apply (cover_eq_one _ cover_in_classes).
   red; intros; apply exc_intro with k; reflexivity.
  Qed.

  Lemma cover_serie_in_class : cover (fun a => exc (In_class a)) (fun a => serie (in_class a)).
  Proof.
   split; intros.
   apply H;[auto | intros k H1].
   apply Ole_trans with (2:=serie_le (in_class x) k).
   rewrite (cover_eq_one _ (cover_in_class x) H1); trivial.
   rewrite serie_zero; trivial.
   intros k; apply (cover_elim (cover_in_class x) k); [auto | | ]; intros [H4 H5]; trivial.
   elim H; apply exc_intro with k; trivial.
  Qed.

  Lemma in_classes_in_class : forall a, in_classes a == serie (in_class a).
  Proof.
   intros a; apply (cover_elim cover_in_classes a); [ auto | | ]; intros [H1 H2].
   rewrite H2; symmetry; apply serie_zero; intros.
   apply (cover_elim (cover_in_class a) k);[auto | | ];intros (H3, H4);rewrite H4;trivial.
   elim H1;destruct H3;apply exc_intro with k;auto.
   rewrite H2.
   assert (exc (In_class a)).
   Focus 2.
   assert (W:= cover_eq_one a cover_serie_in_class H);simpl in W;rewrite W.
   trivial.
     apply H1;[auto | ].
     induction x using Wf_nat.lt_wf_ind; intros.
     apply (cover_elim cover_not_first_repr x); [ auto | | ]; intros [H3 H4].
     apply exc_intro with x; split.
     symmetry; assumption.
     intros k0 Hk0 HR; elim H3.
     apply exc_intro with k0;auto.
     apply H3;[auto | ].
     intros m (H5, H6);apply (H m);eauto.
     transitivity (points x); assumption.
  Qed.

(** ** Any distribtion on a discrete domain is discrete *)
  Variable d : distr A.

  Lemma range_in_classes : range In_classes d.
  Proof.
    unfold range; intros.
    assert (f == fzero A); [| rewrite H0; symmetry; apply mu_zero ].
    intro x; rewrite <- H.
    reflexivity.
    unfold In_classes.
    destruct (points_surj x) as [y Hy].
    apply exc_intro with (x:=y).
    rewrite Hy; reflexivity.
  Qed.

  Definition coeff k := ([1-] (not_first_repr k)) * mu d (uequiv (points k)).

  Lemma mu_discrete : mu d == discrete coeff points.
  Proof.
   intros f; rewrite discrete_simpl.
   unfold coeff.
   transitivity (serie (fun k => mu d (fun a => f a * (in_class a k)))).
   rewrite <- mu_serie_eq.
   unfold serie_fun.
   transitivity (mu d (fun a : A => in_classes a * f a)).
   apply range_cover with (P:= In_classes); trivial.
   apply range_in_classes.
   apply cover_in_classes.
   apply mu_stable_eq; simpl; apply ford_eq_intro; intro a.
   rewrite Umult_sym, serie_mult; [ | apply in_class_wretract].
   Usimpl; apply in_classes_in_class.
   intros; apply wretract_le with (2:=in_class_wretract x); auto. 
   apply serie_eq_compat; intros.
   assert (W:= mu_stable_mult d (f (points k) * [1-] not_first_repr k )).
   rewrite Umult_sym, Umult_assoc, <- W.
   apply mu_stable_eq; simpl; apply ford_eq_intro; intros; unfold fmult.
   unfold in_class;rewrite Umult_assoc.
   apply (cover_elim (cover_uequiv (points k)) n); [auto | | ]; intros [H5 H6].
   rewrite H6; repeat Usimpl; trivial.
   rewrite H5; trivial.
  Qed.

  Lemma coeff_retract : wretract coeff.
  Proof.
    unfold coeff,wretract; intros.
    apply (cover_elim cover_not_first_repr k);
      [auto | |
       (* There is a k0<k with the same repr as k, and 0<=anything. *)
       intros (H,H0); rewrite H0; repeat Usimpl; auto].
    intros (H,H0).
    rewrite H0; clear H0; repeat Usimpl.
    rewrite mu_stable_inv_inv.
    apply Uinv_le_compat.
    transitivity
      (sigma (fun k0 : nat => (mu d) (fun x => [1-] not_first_repr k0 * uequiv (points k0) x)) k).
      apply sigma_le_compat; intros k0 Hk0; auto.
      rewrite <- mu_stable_mult.
      reflexivity.
    rewrite <- mu_sigma_eq.
    (* Sum over points represented by k0<k <= sum over points not represented by k. *)
    apply mu_le_compat; [reflexivity|].
    intro x; unfold finv, sigma_fun.
    apply (cover_elim (cover_uequiv (points k)) x); auto; intros (Hx,Hx').
      (* points k <> x : anything <= 1 *)
      rewrite Hx'; auto.
      (* points k = x : our left hand-side is 0 *)
      rewrite sigma_zero; [auto|intros k0 Hk0].
      rewrite (cover_eq_zero _ (cover_uequiv (points k0))); auto.
      intro; apply H.
      apply exc_intro with (x:=k0); auto.
      split; [assumption | transitivity x; auto].
    (* Summing points represented by k0<k is well formed. *)
    red; intros x k0 Hk0.
    apply (cover_elim (cover_uequiv (points k0)) x); auto;
      intros (H',H''); rewrite H''; clear H''; repeat Usimpl; auto.
    apply (cover_elim cover_not_first_repr k0); auto;
      intros (H0,H0'); rewrite H0'; clear H0'; [|auto].
    rewrite sigma_zero; [auto|intros].
    rewrite <- H'.
    rewrite (cover_eq_zero _ (cover_uequiv (points k1))); auto.
    intro Heq; apply H0.
    apply exc_intro with (x:=k1); split.
    auto.
    symmetry; assumption.
  Qed.

  Theorem domain_is_discrete : is_discrete d.
  Proof.
    unfold is_discrete.
    exists (Build_discr coeff_retract points).
    intro f; unfold Probas.Discrete; simpl mu.
    apply mu_discrete.
  Qed.

End Discrete.

Implicit Arguments domain_is_discrete [[A] [A_discrete] [A_decidable]].

(** **  Instances for common discrete and decidable domains *)

Instance nat_discrete : Discrete_domain nat.
Proof.
  refine {| points := fun x => x ; points_surj := _ |}.
  intro x; exists x; reflexivity.
Qed.

Instance nat_decid_eq : DecidEq nat := Build_DecidEq eq_nat_dec.

Definition bool_points := beq_nat 0.
Instance bool_discrete : Discrete_domain bool.
Proof.
  apply Build_Discrete_domain with (points := bool_points).
  intros [|]; [exists 0%nat|exists 1%nat]; reflexivity.
Qed.

Require Import Bool.

Instance bool_decid_eq : DecidEq bool := Build_DecidEq bool_dec.

(** ** Building a bijection between [nat] and [nat * nat] *)
Require Import Even.
Require Import Div2.

Lemma bij_n_nxn_aux : forall k, 
 (0 < k)%nat -> sigT (fun (i:nat) => {j : nat | k = (exp2 i * (2 * j + 1))%nat}).
Proof.
 induction k using lt_wf_rec; intros.
 destruct (even_odd_dec k).
 destruct (H (div2 k)) as (i, (j, Heq)).
 apply lt_div2; auto with arith.
 inversion e.
 rewrite <- H1 in H0; inversion H0.
 inversion H1; simpl; auto with arith.
 exists (S i)%nat; exists j.
 rewrite (even_double _ e).
 rewrite Heq; unfold double; simpl exp2; ring.
 exists O; exists (div2 k).
 apply trans_eq with (1:= odd_double _ o).
 unfold double; simpl exp2; ring.
Qed.

Definition bij_n_nxn k :=
 match @bij_n_nxn_aux (S k) (lt_O_Sn k) with
 | existT i (exist j _) => (i, j)
 end.

Lemma mult_eq_reg_l : forall n m p, 
 (0 < p -> p * n = p * m -> n = m)%nat.
Proof.
 intros.
 destruct p;[inversion H | ].
 apply le_antisym;
  apply mult_S_le_reg_l with p; rewrite H0; trivial.
Qed.

Lemma even_exp2 : forall n, even (exp2 (S n)).
Proof.
 induction n; simpl.
 repeat constructor.
 apply even_even_plus.
 exact IHn.
 rewrite plus_0_r; exact IHn.
Qed.

Lemma odd_2p1 : forall n, odd (2 * n + 1).
Proof.
 intros; apply odd_plus_r;[ apply even_mult_l | ];
  repeat constructor.
Qed.

Lemma bij_surj : forall i j, exists k, 
 bij_n_nxn k = (i, j).
Proof.
 intros i j.
 exists (exp2 i * (2 * j + 1) - 1)%nat.
 unfold bij_n_nxn.
 destruct (bij_n_nxn_aux (lt_O_Sn (exp2 i * (2 * j + 1) - 1))) as (i', (j', H)).
 assert (exp2 i * (2 * j + 1) = exp2 i' * (2 * j' + 1))%nat .
 rewrite <- H.
 assert (0 < exp2 i * (2 * j + 1))%nat; [ | omega].
 apply le_lt_trans with (O * (2 * j + 1))%nat; trivial.
 apply mult_lt_compat_r.
 apply exp2_pos.
 rewrite plus_comm; simpl; auto with arith.
 clear H.
 generalize i j i' j' H0; clear H0 i j i' j'.
 induction i; destruct i'; intros.
 apply mult_eq_reg_l in H0; [ | apply exp2_pos].
 rewrite plus_comm, (plus_comm (2 * j')) in H0.
 apply plus_reg_l in H0; apply mult_eq_reg_l in H0.
 rewrite H0; trivial.
 auto with arith.
 elimtype False.
 apply not_even_and_odd with (exp2 0 * (2 * j + 1))%nat.
 rewrite H0.
 apply even_mult_l; apply even_exp2.
 simpl exp2; rewrite mult_1_l; apply odd_2p1.
 elimtype False.
 apply not_even_and_odd with (exp2 0 * (2 * j' + 1))%nat.
 rewrite <- H0.
 apply even_mult_l; apply even_exp2.
 simpl exp2; rewrite mult_1_l; apply odd_2p1.
 assert (forall k, exp2 (S k) = 2 * exp2 k)%nat by trivial.
 repeat rewrite H, <- mult_assoc in H0.
 apply mult_eq_reg_l in H0; [ | auto with arith].
 assert (W:= IHi _ _ _ H0); injection W; intros; subst; trivial.
Qed.

(** ** The product of two discrete domains is discrete *)
Instance prod_discrete : forall A B,
  Discrete_domain A -> Discrete_domain B -> Discrete_domain (A*B).
Proof.
  intros.
  apply Build_Discrete_domain with
    (points := fun n => let (i,j) := bij_n_nxn n in ((points i, points j):A*B)).
  intros (x,y).
  destruct (points_surj x) as (x',Hx').
  destruct (points_surj y) as (y',Hy').
  destruct (bij_surj x' y') as (n,Hn).
  exists n.
  rewrite Hn; simpl; rewrite Hx'; rewrite Hy'; reflexivity.
Qed.
