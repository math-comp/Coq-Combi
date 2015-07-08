(** * AbstractWalk.v: An example of probabilistic termination
      Related to Vacid0 example of Maze construction
*)

(* begin hide *)
Add Rec LoadPath "../src" as ALEA.
Require Export DistrTactic.
Set Implicit Arguments.
Open Local Scope U_scope.
Open Local Scope O_scope.
(* end hide *)

Section Walk.

(** ** Abstraction of maze scheme

  If the process is not terminated then a random value is chosen in
  Data, under a certain condition on input and the data, the process
  is iterated on the same input, otherwise the input is changed.  The
  change in the input decreases it strictly and the probability to stay 
  with the same input is bounded by k<1, then the process terminates.  

<< let rec iter u =
  if finished u then output u 
  else let d = dData in 
       if cond u d then iter u else iter (step d u) 
>> 
*)

Variable Data Input Result: Type.

Variable dData : distr Data.

(** Termination is taken using a measure on integer but could be generalized
    to an arbitrary well-founded ordering *)

Variable size : Input -> nat.
Variable finished : Input -> bool.
Axiom finished_size : forall u, size u = O -> finished u = true.

Variable output : Input -> Result.
Variable cond : Input -> Data -> bool.
Variable step : Input -> Data -> Input.

(** When the process is not terminated, the probability to stay in the same state 
    is bounded by k<1 *)

Variable k : U.
Hypothesis knot1 : k < 1.
Hypothesis d_true_bounded 
    : forall x, finished x = false -> mu dData (fun d => B2U (cond x d)) <= k.

(** The random choice of data terminates *)

Hypothesis d_term : mu dData (fun d => 1) == 1.

(** Hypothesis that the size decreases, when a step is taken *)

Hypothesis size_step : forall (u:Input) (x:Data), 
   finished u = false -> cond u x = false -> (size (step u x) < size u)%nat.


Lemma d_if_bound : 
   forall x,  finished x = false -> forall a b, a <= b -> 
    k * a + [1-]k * b 
 <= mu dData (fun d => B2U (cond x d)) * a 
  + mu dData (fun d => NB2U (cond x d)) * b.
intros; 
rewrite (bary_le_compat (mu dData (fun d => B2U (cond x d))) k a b); 
auto.
apply Uplus_le_compat; auto.
apply Umult_le_compat; auto.
rewrite <- mu_one_inv; auto.
unfold finv; rsimplmu.
case (cond x x0); simpl; auto.
Save.

Instance iter_mon : 
    monotonic 
   (fun (f:Input -> distr Result) (u:Input) => 
        if (finished u) then Munit (output u)
        else (Mlet dData 
               (fun d => if (cond u d) then (f u) else (f (step u d))))).
red; intros; intro u.
case (finished u); auto.
apply Mlet_le_compat; auto; intro d; auto.
case (cond u d); auto.
Save.

Lemma mu_if : forall A (b:bool) (dt de : distr A) (f:MF A),
              mu (if b then dt else de) f = if b then (mu dt f) else (mu de f).
destruct b; auto.
Save.

Definition Fiter : (Input -> distr Result) -m> (Input -> distr Result)
:= mon  (fun (f:Input -> distr Result) (u:Input) => 
        fif (finished u) (Munit (output u))
        (Mlet dData 
             (fun d => fif (cond u d) (f u) (f (step u d))))).

Lemma Fiter_simpl : forall f u, 
   Fiter f u = fif (finished u) (Munit (output u))
        (Mlet dData 
             (fun d => fif (cond u d) (f u) (f (step u d)))).
trivial.
Save.

Lemma Fiter_cont : continuous Fiter. 
intros h u.
rewrite Fiter_simpl.
rewrite fcpo_lub_simpl.
setoid_rewrite (fcpo_lub_simpl h).
setoid_rewrite fif_continuous2.
rewrite Mlet_lub_fun_le_right.
rewrite (fif_continuous_right (finished u) (Munit (output u))).
rewrite fcpo_lub_simpl; apply lub_le_compat; intro n; auto.
Save.

Definition iter : Input -> distr Result := Mfix Fiter.

Lemma iter_eq : forall u:Input,
      iter u == fif (finished u) (Munit (output u))
                (Mlet dData (fun d => fif (cond u d) (iter u) (iter (step u d)))).
exact (Mfix_eq Fiter_cont).
Save.
Hint Resolve iter_eq.

(** ** Building the invariant sequence

  [x] is the size of the input and [n] the number of iterations: 

      [pw x 0 = 0]
      [pw 0 n = 1]
      [pw (x+1) (n+1) = k (pw (x+1) n) + (1-k) (pw x n)]
   
*)

Fixpoint pw_ (x n : nat) : U := 
  match n with O => 0 
            | (S n) => match x with 
                         O => 1
                     | S y => k * pw_ x n + ([1-] k) * pw_ y n 
                       end
  end.

Lemma pw_decrS_x : forall n x, pw_ (S x) n <= pw_ x n.
induction n; simpl; intros; auto.
destruct x; auto.
Save.
Hint Resolve pw_decrS_x.

Lemma pw_decr_x : forall n x y, (x <= y)%nat -> pw_ y n <= pw_ x n.
induction 1; simpl; intros; auto.
transitivity (pw_ m n); auto.
Save.
Hint Resolve pw_decr_x.

Lemma pw_incr : forall x n, pw_ x n <= pw_ x (S n).
simpl; intros.
case x; auto.
Save.

Hint Resolve pw_incr.

Definition pw : nat -> nat -m> U 
    := fun x => fnatO_intro (pw_ x) (pw_incr x).

Lemma pw_pw_ : forall x n, pw x n = pw_ x n.
trivial.
Save.

Lemma pw_simpl : forall x n, pw x n = 
    match n with O => 0 
             | (S n) => match x with 
                          O => 1
                        | S y => k * pw x n + ([1-] k) * pw y n
                        end
    end.
destruct n; auto.
Save.

Lemma pwS_simpl : forall x n, pw (S x) (S n) = k * pw (S x) n + [1-]k * (pw x n).
trivial.
Save.


Lemma lim_pw_one : forall x, lub (pw x) == 1.
induction x.
apply Uge_one_eq.
transitivity (pw O (S O)); auto.
apply Umult_simpl_one with k; auto.
transitivity (mlub (seq_lift_left (pw (S x)) (S 0))).
transitivity (k * lub (pw (S x)) + [1-] k * lub (pw x)).
rewrite IHx; auto.
do 2 rewrite <- lub_eq_mult.
rewrite <- lub_eq_plus.
apply mlub_le_compat; intro n; auto.
rewrite <- mlub_lift_left; trivial.
Save.


Lemma iter_term : forall u, 1 <= mu (iter u) (fun r => 1).
assert (okfun (fun x : Input => lub (pw (size x))) (Mfix Fiter) (fun a b => 1)).
apply fixrule; auto.
unfold okfun,ok; intros.
rewrite Fiter_simpl.
case_eq (size x); intros.
rewrite finished_size; auto.
case_eq (finished x); auto.
intro fx; rewrite pwS_simpl; intros.
simpl @fif.
rewrite Mlet_simpl.
rewrite (d_if_bound fx).
transitivity 
 (mu dData
   (fplus
   (fun x0 : Data => B2U (cond x x0) * (mu (f x) (fun _ => 1)))
   (fun x0 => NB2U (cond x x0) * (mu (f (step x x0)) (fun _ => 1))))).
rewrite (mu_stable_plus dData).
apply Uplus_le_compat; auto.
do 4 simplmu.
rewrite <- H0; rewrite <- H; auto.
transitivity (mu dData
  (fun x0 : Data =>
   NB2U (cond x x0) *(pw n i))); auto.
rewrite Umult_sym; rewrite <- (mu_stable_mult dData (pw n i)).
unfold fmult; simplmu; auto.
apply mu_le_compat; auto; intro x0.
case_eq (cond x x0); unfold NB2U; auto.
repeat Usimpl.
intro; rewrite <- H.
assert (size (step x x0) <= n)%nat; auto.
assert (S (size (step x x0)) <= S n)%nat; auto.
rewrite <- H0; apply size_step; auto.
omega.
repeat rewrite pw_pw_; auto.
red; intros; intro d.
transitivity (B2U (cond x d)); auto.
transitivity ([1-](NB2U (cond x d))); try simplmu; auto.
case (cond x d); auto.
(* unfold finv; rsimplmu; auto.*)
apply mu_le_compat; intro d; unfold fplus; auto.
case (cond x d); simpl; auto.
apply (pw_decrS_x i n).
intro u; rewrite <- (lim_pw_one (size u)) at 1.
exact (H u).
Save.

End Walk.
