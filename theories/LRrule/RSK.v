(******************************************************************************)
(*       Copyright (C) 2014 Florent Hivert <florent.hivert@lri.fr>            *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm fingroup matrix ssralg.
Require Import tools combclass subseq partition Yamanouchi permuted ordtype Schensted plactic Greene_inv std.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

(* Definition bimon (A B : finType) := {ffun A*B -> nat}. *)
Definition word_of_mat m n (M : 'M[nat]_(m, n)) : seq 'I_n :=
  flatten [seq flatten [seq nseq (M a b) b | a : 'I_m] | b : 'I_n].

Section Defs.

Variables (m n : nat).
Hypothesis Hmpos : m != 0%N.
Hypothesis Hnpos : n != 0%N.

Canonical Im := Eval hnf in OrdType 'I_m (ord_ordMixin Hmpos).
Canonical In := Eval hnf in OrdType 'I_n (ord_ordMixin Hnpos).

Definition bimon_of_mat (M : 'M[nat]_(m, n)) : seq ('I_m * 'I_n) :=
  flatten [seq nseq (M a b) (a, b) | a <- enum 'I_m, b <- enum 'I_n].

Definition RSK (M : 'M[nat]_(m, n)) :=
  (RS (T := In) (word_of_mat M), RS (word_of_mat M^T)).

End Defs.

