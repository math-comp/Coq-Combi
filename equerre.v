Add Rec LoadPath "../Coq-Combi/LRrule".

Require Import ssreflect ssrbool eqtype ssrnat seq bigop rat fintype.
Require Import partition .

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Fixpoint haut (L : seq nat) j :=
  match L with
  |[::] => 0
  |b :: reste => if j<b then (haut reste j).+1 else haut reste j
  end.


Definition equerre L i j := (nth 0 L i)-j + (haut L j)-i -1.

Definition tabvide L := fun (i : ordinal (lenght L))(j : ordinal 

Definition F (L : seq nat) 



