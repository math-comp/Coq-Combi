Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.


(** Term, judgments and computation *)

Check true.
Check (true : bool).
Check 3.
Check (3 : nat).
(** Check (3 : bool). *)
Check [:: 3; 4].
Check ([:: 3; 4] : seq nat).
(** Check ([:: 3; 4; 2] : nat). *)

Check (fun n => n + 1).
Check ((fun n => n + 1) 3).
Eval compute in (fun n => n + 1) 3.

Definition add1 := fun n => n + 1.
Definition add1_bis n := n + 1. (* shortcut *)

Eval compute in add1 3.
Eval compute in add1_bis 3.

(** New data structures and programs *)
Check nat. (** Set is by convention the type of data structure *)
Check bool.
Print bool.

Inductive answer : Set :=
  | yes : answer
  | no : answer
  | dontknow : answer.

Definition is_ok ans :=
  match ans with
  | yes => true
  | no => false
  | dontknow => false
  end.

Check is_ok.
Eval compute in is_ok yes.

Print nat.

Fixpoint pow a n := (* Fixpoint = recursive definition *)
  match n with
  | S n' => a * (pow a n')
  | O => 1
  end.
Print pow.
Eval compute in pow 2 10.


(* Syntactical sugar *)
Fixpoint pow_short a n :=
  if n is n'.+1 then a * pow_short a n' else 1.
Print pow_short.

Print list.
Print size.


(** Statements (ie: terms of type [Prop] *)
Check (2 = 3).
Check (forall n, n = 0).
Check (erefl (A := nat)).

Print eq.
Print and.
Print or.

Check (or_introl (erefl 3) : 3 = 3 \/ 3 = 5).

Print False. (* A proposition which has by definition no proof *)

(** Not to be confused with *)
Print false. (* A boolean constant *)

(** * Proof as program an induction reasoning *)
Fixpoint iterate
         (T : Type)
         (init : T)
         (step : T -> T)
         (n : nat) :=
  if n is n'.+1 then step (iterate T init step n') else init.

Fixpoint iterate_dep
         (T : nat -> Type)
         (init : T 0)
         (step : forall (n : nat), T n -> T n.+1)
         (n : nat) :=
  if n is n'.+1 then step n' (iterate_dep T init step n') else init.


(** The use of tactics *)
Lemma impl_trans (A B C : Prop) :
  (A -> B) -> (B -> C) -> (A -> C).
Proof.
intro A_implies_B.
intro B_implies_C.
intro A_holds.
apply B_implies_C.
apply A_implies_B.
apply A_holds.
Qed.
Check impl_trans.


(** Section *)
Section Composition.

Variables (A B C : Prop).
Hypotheses (AB : A -> B) (BC : B -> C).
Definition impl_trans_sec := fun (a : A) => BC (AB a).

End Composition.

(** Direct definition *)
Definition impl_trans_fun
           (A B C : Prop)
           (AB : A -> B)
           (BC : B -> C) :=
  fun (a : A) => BC (AB a).

(** SSreflect / Mathematical component : a different tactic language *)
Lemma impl_trans_ssr (A B C : Prop) :
  (A -> B) -> (B -> C) -> (A -> C).
Proof.
by move=> HAB HBC HA; apply HBC; apply HAB.
Qed.

Print impl_trans.
Print impl_trans_sec.
Print impl_trans_fun.
Print impl_trans_ssr.

(** Boolean reflection *)

Print and.
Print andb.
Check andP.

Print has.

Eval compute in has (fun x => x == 5) [:: 2; 5; 3; 4].
Eval compute in has (fun x => x == 0) [:: 2; 5; 3; 4].
Check hasP.

