
(*
   here we prove the equivalence between definitions from
   - the Coq proof (in directory ..), and
   - the Why3 proof (in file lrrule.mlw)
*)

Add LoadPath "..".
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
(* Require Import tuple finfun finset bigop path. *)
Require Import tools partition yama ordtype tableau std stdtab.

(* import definitions from Why3 *)
Require Import spec.



