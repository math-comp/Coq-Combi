(** * FFact.v : a faulty factorial function *)
(** Source : Abstraction, refinement and proof for probabilistic systems 
    A. McIver and C. Morgan, Springer *)
Add Rec LoadPath "../src" as ALEA.

Require Export Cover.
Require Export Misc.
Require Export DistrTactic.
Require Export Bernoulli.
Require Export Arith.

(* begin hide *)
Set Implicit Arguments.
Open Local Scope U_scope.
Open Local Scope O_scope.

(* end hide *)

(** ** Program trying to compute fact 
but with a faulty decreasing function *)
Section Fact.

Variable p : U.
Hypothesis ppos : 0 < p.

(**
<<
let rec ffact n f =
        match n with O => Munit f 
                 | S p => if bernoulli p then ffact p (f*n) 
                          else ffact (S n) (f*n)
        end
>>*)


Instance Ffact_mon : monotonic 
    (fun (df:(nat*nat)-> distr nat) => 
         fun nf : nat*nat => 
           match nf with (O,f) => Munit f 
                 | (S m,f) => Mif (bernoulli p) (df (m,f*(S m))%nat)
                                  (df (S (S m),f*(S m))%nat)
           end).
intros df dg H (n,f).
destruct n; auto.
Save.

Definition Ffact : ((nat*nat)-> distr nat) -m> ((nat*nat)-> distr nat)
    := mon  (fun (df:(nat*nat)-> distr nat) => 
         fun nf : nat*nat => 
           match nf with (O,f) => Munit f 
                 | (S m,f) => Mif (bernoulli p) (df (m,f*(S m))%nat)
                                  (df (S (S m),f*(S m))%nat)
           end).

Lemma Ffact_simpl : forall df nf, 
Ffact df nf = match nf with (O,f) => Munit f 
                 | (S m,f) => Mif (bernoulli p) (df (m,f*(S m))%nat)
                                  (df (S (S m),f*(S m))%nat)
              end.
trivial.
Save.

Definition ffact : (nat*nat)-> distr nat := Mfix Ffact.

Instance Ffact_cont : continuous Ffact.
intros fn nf.
rewrite Ffact_simpl.
destruct nf; destruct n; auto.
transitivity ((Ffact @ fn) O (O, n0)).
simpl; auto.
apply (le_lub (Ffact @ fn) O (O, n0)).
setoid_rewrite Mif_lub_eq2; 
apply lub_le_compat; intro m; auto.
Save.
Hint Resolve Ffact_cont.

Lemma ffact_eq 
  : forall nf, ffact nf == match nf with (O,f) => Munit f 
                 | (S m,f) => Mif (bernoulli p) (ffact (m,f*(S m))%nat)
                                  (ffact (S (S m),f*(S m))%nat)
              end.
unfold ffact; intro nf; apply Mfix_eq; auto.
Save.

Lemma fact_Sn_mult_simpl : 
forall n f, (fact (S n) * f = fact n * (f * (S n)))%nat.
intros; simpl; ring.
Save.

Lemma ffact_fact : 
    forall n f, p ^ n <= mu (ffact (n,f)) (carac_eq (fact n * f)).
induction n; intros.
rewrite ffact_eq.
simpl.
rewrite carac_eq_one; auto.
rewrite ffact_eq.
rewrite Mif_bernoulli_choice.
rewrite Mchoice_simpl.
transitivity 
  (p * (mu (ffact (n, (f * S n)%nat))) (carac_eq (fact (S n) * f))).
rewrite (fact_Sn_mult_simpl n f).
rewrite <- (IHn (f * S n)%nat); auto.
auto.
Save.
 
End Fact.
