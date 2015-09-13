(** * BinCoeff.v: Binomial coefficients *)
(** Contributed by David Baelde, 2011 *)

Require Import Arith.
Require Import Omega.

(* begin hide *)
Set Implicit Arguments.

(* end hide *)

(** ** Definition of binomial coefficients *)

Fixpoint comb (k n:nat) {struct n} : nat :=
   match n with O => match k with O => (1%nat) | (S l) => O end
          | (S m) => match k with O => (1%nat)
                            | (S l) => ((comb l m) + (comb k m))%nat 
                     end
   end.

(** ** Properties of binomial coefficients *)

Lemma comb_0_n : forall n, comb 0 n = 1%nat.
destruct n; trivial.
Save.

Lemma comb_not_le : forall n k, (S n <= k)%nat -> comb k n = 0%nat.
induction n; destruct k; simpl; try omega; intros.
rewrite (IHn k); auto with zarith.
rewrite (IHn (S k)); auto with zarith.
Save.

Lemma comb_Sn_n : forall n, comb (S n) n = 0%nat.
intro; apply comb_not_le; auto.
Save.

Lemma comb_n_n : forall n, comb n n = 1%nat.
induction n; simpl; auto.
rewrite comb_Sn_n; auto with zarith.
Save.

Lemma comb_1_Sn : forall n, comb 1 (S n) = S n.
induction n; auto.
replace (comb 1 (S (S n))) with ((comb 0 (S n)+comb 1 (S n))%nat); auto.
Save.

Lemma comb_inv : forall n k, (k<=n)%nat -> comb k n = comb (n-k) n.
induction n; destruct k; simpl; auto with zarith; intros.
rewrite comb_Sn_n; rewrite comb_n_n; auto.
assert (Hle : (k<=n)%nat); auto with zarith.
case (le_lt_or_eq k n Hle); intros.
assert (Heq:(n-k)%nat=(S (n-(S k)))); auto with zarith.
pattern ((n-k)%nat) at 1; rewrite Heq.
rewrite (IHn (S k)); auto.
rewrite (IHn k); auto with zarith.
subst.
rewrite comb_Sn_n; rewrite comb_n_n; rewrite <- minus_n_n; trivial.
Save.

Lemma comb_n_Sn : forall n, comb n (S n) = (S n).
intros; transitivity (comb (S n - n) (S n)).
apply comb_inv; auto.
rewrite <- minus_Sn_m; auto.
rewrite <- minus_n_n.
apply comb_1_Sn.
Save.


(* Shortcuts for horizontal (k-axis) and vertical (n-axis) relationships for (comb k n). *)
Notation H := (fun n k => comb (S k) (S n) * (S k) = comb k (S n) * (S n - k)).
Notation V := (fun n k => comb k (S n) * (S n - k) = comb k n * (S n)).

Lemma comb_relations : forall n k, H n k /\ V n k.
Proof.
  intro n; induction n; intros.

  (* Case split for the base case: k = 0, 1 or >n. *)
  destruct k; [ auto | destruct k; auto ].

  (* We first treat the "illegal" cases where k>=n+2. *)
  destruct (lt_eq_lt_dec k (S (S n))) as [ [ Lt_k_SSn | Eq_k_SSn ] | Gt_k_SSn ].
  (* k=n+2 *)
  Focus 2.
  rewrite Eq_k_SSn.
  rewrite comb_n_n; repeat rewrite comb_Sn_n;
  repeat rewrite minus_diag; auto with arith.
  (* k>n+2 *)
  Focus 2.
  do 3 (rewrite comb_not_le; auto with arith).

  (* First prove V, then use it to derive H. *)
  assert (V (S n) k) as VSnk.
  destruct k.
  rewrite comb_0_n; auto with arith.
  change (comb (S k) (S (S n))) with (comb k (S n) + comb (S k) (S n)).
  rewrite mult_plus_distr_r.
  assert (H n k) as Hnk.
  elim (IHn k); trivial.
  change (S (S n) - S k) with (S n - k).
  rewrite <- Hnk.
  rewrite <- mult_plus_distr_l.
  replace (S k + (S n - k)) with (S (S n)).
  reflexivity.
  rewrite plus_Sn_m.
  rewrite <- (le_plus_minus k (S n)) by (apply lt_le_weak; auto with arith).
  reflexivity.

  split; try exact VSnk.

  change (comb (S k) (S (S n))) with (comb k (S n) + comb (S k) (S n)).
  rewrite mult_plus_distr_r.
  assert (H n k) as Hnk.
  elim (IHn k); trivial.
  rewrite Hnk.
  rewrite <- mult_plus_distr_l.
  replace (S k + (S n - k)) with (S (S n)).
  rewrite <- VSnk.
  reflexivity.
  rewrite plus_Sn_m.
  rewrite <- (le_plus_minus k (S n)) by (auto with arith).
  reflexivity.
Qed.

Lemma comb_incr_n : forall n k, comb k (S n) * (S n - k) = comb k n * (S n).
Proof.
  intros.
  elim (comb_relations n k).
  trivial.
Qed.

Lemma comb_incr_k : forall n k, comb (S k) (S n) * (S k) = comb k (S n) * (S n - k).
Proof.
  intros.
  elim (comb_relations n k).
  trivial.
Qed.

Lemma comb_fact : forall n k, k<=n -> comb k n * fact k * fact (n-k) = fact n.
Proof.
  (* We iterate Sk_k (rather than Sn_n) hence we proceed by induction on k. *)
  intros n k; induction k.
  (* Base case. *)
  intros _.
  rewrite comb_0_n; simpl fact; simpl mult;
  rewrite <- minus_n_O; rewrite <- plus_n_O; reflexivity.
  (* Successor. *)
  intro.
  change (fact (S k)) with (S k * fact k).
  destruct n.
    (* n can't be 0 *)
    elim (le_Sn_O _ H).
    (* n := S n, we can apply Sk_k *)
    rewrite mult_assoc. rewrite comb_incr_k.
    change (S n - S k) with (n-k).
    rewrite <- minus_Sn_m; try omega.
    repeat rewrite <- mult_assoc.
    rewrite (mult_comm (fact k)).
    rewrite (mult_assoc (S (n-k))).
    change ((S (n - k)) * fact (n - k)) with (fact (S (n - k))).
    rewrite minus_Sn_m; try omega.
    rewrite <- IHk; try omega.
    repeat rewrite <- mult_assoc.
    auto with arith.
Qed.

Lemma comb_le_0_lt : forall k n, k <= n -> 0 < comb k n.
Proof.
  intros.
  elim (zerop (comb k n)); intros.
  assert (comb k n * fact k * fact (n-k) = 0)%nat.
  rewrite a; auto with arith.
  rewrite (comb_fact H) in H0.
  assert (0<0).
  rewrite <- H0 at 2.
  exact (lt_O_fact n).
  inversion H1.
  auto.
Qed.

Lemma mult_simpl_right : forall m n p, 0 < p -> m * p = n * p -> m = n.
Proof.
  intros.
  assert (m<n \/ n<m \/ m=n) as [H1|[H1|H1]] by omega.
  exfalso; assert (m * p < n * p);  [|omega].
  apply mult_lt_compat_r; assumption.
  exfalso; assert (m * p > n * p); [|omega].
  apply mult_lt_compat_r; assumption.
  assumption.
Qed.

Corollary comb_symmetric : forall k n, k<=n -> comb k n = comb (n-k) n.
Proof.
  intros.
  assert (comb k n * (fact k * fact (n-k)) =
          comb (n-k) n * (fact (n-(n-k)) * fact (n-k))).
    rewrite mult_assoc. rewrite comb_fact; [ | omega ].
    rewrite (mult_comm (fact (n-(n-k)))). rewrite mult_assoc. rewrite comb_fact; [ | omega ].
    reflexivity.
  replace (n-(n-k)) with k in H0 by omega.
  assert (0 < fact k * fact (n - k)) by
    (change 0 with (0 * fact (n-k)); apply mult_lt_compat_r; apply lt_O_fact).
  apply (mult_simpl_right _ _ H1 H0).
Qed.

Lemma mult_lt_compat_l : forall n m p : nat, n < m -> 0 < p -> p * n < p * m.
Proof.
  intros.
  rewrite <- 2!mult_comm with (m:=p).
  apply mult_lt_compat_r; assumption.
Qed.

Lemma comb_monotonic_k : forall k n k', 0<n -> k<=k' -> 2*k'<=n -> comb k n <= comb k' n.
Proof.
  intros k n k' Hn Hkk'; induction Hkk'; intros.
  auto.
  apply le_trans with (comb m n).
  apply IHHkk'.
  omega.
  assert (comb (S m) n * (S m) = comb m n * (n-m)).
    replace n with (S (pred n)) by omega.
    apply comb_incr_k.
  assert (comb m n <= comb (S m) n \/ comb m n > comb (S m) n) by omega.
  destruct H1.
  assumption.
  assert (comb (S m) n * S m < comb m n * (n-m)); [ | omega ].
  transitivity (comb m n * S m).
  apply mult_lt_compat_r; omega.
  apply mult_lt_compat_l; omega.
Qed.

Lemma comb_monotonic_n : forall k n n', k<=n -> n<=n' -> comb k n <= comb k n'.
Proof.
  intros k n n' Hk Hle; induction Hle.
  auto.
  apply le_trans with (comb k m); [ assumption | clear IHHle ].
  assert (comb k m * S m = comb k (S m) * ((S m) - k)).
    rewrite comb_incr_n; reflexivity.
  (* Ab absurdo *)
  assert (comb k m <= comb k (S m) \/ comb k (S m) < comb k m) by omega;
    destruct H0; try assumption.
  assert (comb k (S m) * (S m - k) < comb k m * S m); [ | omega ].
  apply le_lt_trans with (m:= comb k (S m) * S m).
  apply mult_le_compat_l; omega.
  apply mult_lt_compat_r; omega.
Qed.

Lemma comb_monotonic :
  forall k n k' n', 0<n -> k<=n -> k<=k' -> 2*k'<=n' -> n<=n' -> comb k n <= comb k' n'.
Proof.
  intros.
  apply le_trans with (comb k n').
  apply comb_monotonic_n; omega.
  apply comb_monotonic_k; omega.
Qed.

Lemma comb_max_half : forall k n, comb k n <= comb (Div2.div2 n) n.
Proof.
  intros.
  (* Eliminate the case where n = 0 *)
  destruct n.
    destruct k; simpl; auto.
  (* Eliminate the case where k > n *)
  assert (k > S n \/ k <= S n) by omega.
  destruct H as [ H | H ].
  rewrite comb_not_le by try omega.
  apply lt_le_weak.
  apply comb_le_0_lt.
  apply lt_le_weak.
  apply Div2.lt_div2; omega.
  (* Treat the case where k <= n/2 *)
  assert (forall k, k <= Div2.div2 (S n) -> comb k (S n) <= comb (Div2.div2 (S n)) (S n)).
    intros.
    apply comb_monotonic_k; try omega.
    replace (2 * Div2.div2 (S n)) with (Div2.double (Div2.div2 (S n)))
      by (unfold Div2.double; omega).
    destruct (Even.even_or_odd (S n)) as [ He | Ho ] ;
    [ rewrite <- Div2.even_double with (1:=He); auto |
      apply le_S_n; rewrite <- Div2.odd_double with (1:=Ho); omega ].
  (* By symmetry we can conclude *)
  assert (k <= Div2.div2 (S n) \/ k > Div2.div2 (S n)) by omega.
    (* Immediate if k<=n/2 *)
    destruct H1 as [ H1 | H1 ].
    auto.
    (* Otherwise get back to that case *)
    rewrite comb_inv with (1:=H).
    apply H0.
    assert (S n <= Div2.div2 (S n) + k).
    assert (S n <= S (Div2.double (Div2.div2 (S n)))) by
      (destruct (Even.even_or_odd (S n)) as [ He | Ho ];
       [ apply le_S_n; rewrite <- Div2.even_double with (1:=He); omega |
         apply le_S_n; rewrite <- Div2.odd_double with (1:=Ho); omega ]).
    unfold Div2.double in H2.
    omega.
    omega.
Qed.
