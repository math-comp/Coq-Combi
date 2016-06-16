Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
From mathcomp Require Import finset perm fingroup matrix ssralg.
Require Import tools combclass subseq partition Yamanouchi permuted ordtype Schensted plactic Greene_inv std.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Section Hello.
Variable m n: nat.

Definition bimon_of_mat (M : 'M[nat]_(m, n)) : seq (nat * nat) :=
  flatten [seq nseq (M a b) ((a:nat), (b:nat)) | a <- enum 'I_m, b <- enum 'I_n].

Definition M := \matrix_(i<2,j<3) 1%N.

End Hello.

Check @bimon_of_mat 2 3.
Check M (Ordinal (lt0n 2)) (Ordinal (lt0n 3)).
Check bimon_of_mat (m:=2) (n:=3) M.
Compute bimon_of_mat M.


(*Définir:
  ordre lexico +
  passage d'une matrice à un mot
  utiliser la correspondance RSK (cf) Schensted.v en remplacant les 1,2,3... qui apparaissent dans Q, par 1,1,1,2,2,3,3,... et montrer que c'est un tableau*)
