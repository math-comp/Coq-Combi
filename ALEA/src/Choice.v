(** * Choice.v: An example of probabilistic choice *)
Require Export Prog.
Set Implicit Arguments.

(* Module Choice (Univ:Universe).
Module RP := (Rules Univ). *)
(* begin hide *)
(* Import Univ RP PP MP UP. *)

Open Local Scope U_scope.
Open Local Scope O_scope.

(* end hide *)
(** ** Definition of a probabilistic choice
We interpret the probabilistic program [p] which executes 
two probabilistic programs [p1] and [p2] and then make a choice 
between the two computed results.
<<
let rec p () = let x = p1 () in let y = p2 () in choice x y 
>>*)
Section CHOICE.
Variable A : Type.
Variables p1 p2 : distr A.
Variable choice : A -> A -> A.
Definition p : distr A := Mlet p1 (fun x => Mlet p2 (fun y => Munit (choice x y))).
(** ** Main result 
 We estimate the probability for [p] to satisfy [Q] given estimations for 
both [p1] and [p2]. *)
(** *** Assumptions 
We need extra properties on [p1], [p2] and [choice].
- [p1] and [p2] terminate with probability [1]
- [Q] value on [choice] is not less than the sum of values of [Q] on separate elements. 
If [Q] is a boolean function it means than if one of [x] or [y] satisfies [Q]
then [(choice~x~y)] will also satisfy [Q] *)
Hypothesis p1_terminates : (mu p1 (fone A))==1.
Hypothesis p2_terminates : (mu p2 (fone A))==1.

Variable Q : MF A. 
Hypothesis choiceok : forall x y, Q x + Q y <= Q (choice x y).

(** *** Proof of estimation:
[ ok k1 p1 Q ] and [ ok k2 p2 Q ] implies [ ok (k1(1-k2)+k2) p Q ]
*)

Lemma choicerule : forall k1 k2,  
  k1 <= mu p1 Q -> k2 <= mu p2 Q ->  (k1 * ([1-] k2) + k2) <= mu p Q.
unfold p,Mlet,star; simpl; unfold unit; intros.
apply Ole_trans with 
  (mu p1 (fun x : A => mu p2 (fun y : A => Q x * ([1-] (Q y)) + Q y))).
apply Ole_trans with 
  (mu p1 (fun x : A => 
           ((mu p2 (fun y : A => Q x * ([1-] (Q y))))
           +(mu p2 Q)))).
change 
 (k1 * [1-] k2 + k2 <=
  mu p1 (fplus (fun x : A => mu p2 (fun y : A => Q x * [1-] (Q y)))
               (fun x => mu p2 Q))).
assert (H1 : fplusok (fun x : A => mu p2 (fun y : A => Q x * [1-] (Q y)))
               (fun x => mu p2 Q)).
repeat red; unfold finv; intros.
apply Ole_trans with (mu p2 (fun y : A => [1-] (Q y))).
apply (mu_monotonic p2); auto.
apply (mu_stable_inv p2 Q).
setoid_rewrite (mu_stable_plus p1 H1).
assert (Heq1:mu p1 (fun _ : A => mu p2 Q) == mu p2 Q).
exact (mu_cte_eq p1 (mu p2 Q) p1_terminates).
rewrite Heq1.
apply Ole_trans with  (k1 * [1-] (mu p2 Q) + (mu p2 Q)); auto.
Usimpl.
apply Ole_trans with (mu p1 (fun x : A => (Q x) * mu p2 (finv Q))).
apply Ole_trans with ((mu p1 Q) * (mu p2 (finv Q))).
rewrite (mu_one_inv p2 p2_terminates Q); auto.
rewrite (mu_stable_mult_right p1 (mu p2 (finv Q)) Q); auto.
apply (mu_monotonic p1); intro x.
rewrite <- (mu_stable_mult p2 (Q x) (finv Q)); auto.

apply (mu_monotonic p1); intro x.
assert (fplusok (fun y : A => Q x * [1-] (Q y)) Q).
intro y; unfold finv; auto.
rewrite <- (mu_stable_plus p2 H1); auto.
apply (mu_monotonic p1); intro x.
apply (mu_monotonic p2); intro y.
apply Ole_trans with ((Q x) + (Q y)); auto.
Save.

End CHOICE.
(* End Choice. *)
