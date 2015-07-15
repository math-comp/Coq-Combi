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

Definition last i = nth O p i.-1.

Definition in_hook (i j:nat) (k l : nat) := 
     (i == k && j < l < nth 0 p i)%N || (j == l && i < k < size p)%N.

Lemma in_hook_part (i j:nat) (k l : nat) :
   in_part i j -> in_hook i j k l -> in_part k l.
admit.
Save.

(* Definition choose_in_hook i j := 
*)

End FindCorner.