(** * program.v : the probabilistic program finding a corner *)

Add Rec LoadPath "ALEA/src" as ALEA.
Add Rec LoadPath "../Combi/LRrule".

Require Import Misc Ccpo Qmeasure.
Set Implicit Arguments.
Local Open Scope O_scope.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype rat 
               finfun ssrnum ssralg ssrint bigop.
Local Open Scope ring_scope.
Require Import partition.

(* Require Import equerre. *)

Section FindCorner.

Variable p : intpart.

Variable hook' : nat -> nat -> nat.

Definition in_part (i j:nat) := (i < size p)%N && (j < nth 0 p i)%N.

Definition last i := nth O p i.-1.

Definition in_hook (i j:nat) (k l : nat) := 
     ((i == k) && (j < l < nth 0 p i))%N || ((j == l) && (i < k < size p))%N.

Lemma in_hook_part (i j:nat) (k l : nat) :
   in_part i j -> in_hook i j k l -> in_part k l.
admit.
Save.

Definition hook_seq i j := 
    [seq (k,j) | k <- iota (i.+1) ((size p).-1 - i)]++
    [seq (i,k) | k <- iota (j.+1) ((nth O p i).-1 - j)].

Lemma in_hook_seq (i j:nat) (k l : nat) :
   (k,l) \in (hook_seq i j) -> in_hook i j k l.
admit.
Save.

Lemma hook_seq_empty (i j:nat) : 
      in_part i j -> (hook_seq i j == [::])%B -> (j == last i)%B && is_out_corner p i.
admit.
Save.

Lemma in_hook_seq_decr (i j:nat) (k l : nat) :
   (k,l) \in (hook_seq i j) -> (size (hook_seq k l) < size (hook_seq i j))%N.
admit.
Save.

Fact succ_neq0 : forall n m : nat, (n==m.+1)%N -> (n!=0)%N.
move => n m; rewrite -lt0n.
by move => H; rewrite (eqP H).
Save.

Fixpoint choose_corner (i j : nat) (m:nat) := 
   if m is m'.+1 then
     let s := hook_seq i j in
     (if size s is p.+1 as n return (size s==n)%N -> distr (seq nat*seq nat) 
     then fun (Hs: (size s == p.+1)%N)  => 
          Mlet (Uniform (mkunif s (succ_neq0 _ _ Hs)))
          (fun ab => let: (k,l) := ab in 
             Mlet (choose_corner k l m') (fun AB => let: (A,B):=AB in Munit (i::A,j::B)))
     else fun _ => Munit ([::i],[::j]))
     (eq_refl (size s))
   else Munit ([::i],[::j]).


End FindCorner.