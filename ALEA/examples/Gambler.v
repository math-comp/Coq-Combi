(** * Gambler.v : gambler dream to win a little might lead to loose a lot *)
(** Source : Abstraction, refinement and proof for probabilistic systems 
    A. McIver and C. Morgan, Springer *)
Add Rec LoadPath "../src" as ALEA.

Require Export Cover.
Require Export Misc.
Require Export DistrTactic.
Require Export Arith.

(* begin hide *)
Set Implicit Arguments.
Open Local Scope U_scope.
Open Local Scope O_scope.

(* end hide *)

(** ** Strategy
the gambler doubles his bet until he wins or he runs out of money
he starts with enough money to play n-times, ie
   (1 + 2 + ...+ 2^{n-1})b = (2^n-1)b
<<
let rec play n b =
        if n = 0 then 0 
        else if flip then (2^n) b else play n (2b)
>>
*)

Section Gamble.

Fixpoint pow2 (n:nat) : nat := 
   match n with O => 1%nat | S p => (2 * (pow2 p))%nat end.

Fixpoint play (n:nat) (b:nat) : distr nat := 
    match n with 
      O => Munit O
    | S p => Mif Flip (Munit ((pow2 n) * b)%nat) (play p (2*b))
    end.

Lemma pow2not0 : forall n, pow2 n <> O.
induction n; simpl; omega.
Save.
Hint Resolve pow2not0.


Lemma proba_loose : forall n b, ~ b=O -> mu (play n b) (carac_eq O)== [1/2]^n.
induction n; intros.
simpl; auto.
simpl.
replace (pow2 n + (pow2 n + 0))%nat with (pow2 (S n)) by trivial.
rewrite (cover_eq_zero _ (is_eq O)).
repeat Usimpl.
apply IHn.
omega.
apply not_eq_sym.
apply NPeano.Nat.neq_mul_0; auto.
Save.

Lemma proba_win : forall n b, ~ b=O -> mu (play n b) (carac_eq ((pow2 n) * b)%nat)== [1-]([1/2]^n).
induction n; intros.
simpl; repeat Usimpl.
rewrite (cover_eq_zero _ (is_eq (b + 0))); intuition.
simpl.
rewrite (cover_eq_one _ (is_eq (pow2 (S n) * b)%nat)); trivial.
repeat Usimpl.
replace ((pow2 n + (pow2 n + 0)) * b)%nat with (pow2 n * (2*b))%nat.
rewrite IHn.
rewrite <- Uinv_half; repeat Usimpl; auto.
omega.
ring.
Save.

End Gamble.
