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
Set Implicit Arguments.
Unset Strict Implicit.

(** * Setup a coercion [int -> rat] and add a few simple lemmas *)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import  ssrfun ssrbool eqtype choice ssrnat seq ssrint rat
               fintype bigop path ssralg ssrnum.

Import GRing.Theory.
Import Num.Theory.


Definition int_to_rat : int -> rat := intmul (GRing.one rat_Ring).
Coercion int_to_rat : int >-> rat.

Lemma int_to_ratD : {morph int_to_rat : n m / (n + m)%R >-> (n + m)%R}.
Proof. move => m n /=; exact: mulrzDl. Qed.

Lemma int_to_ratM : {morph int_to_rat : n m / (n * m)%R >-> (n * m)%R}.
Proof. move => m n /=; by rewrite -intrM. Qed.

Section FieldLemmas.

Local Open Scope ring_scope.

Lemma iter_plus1 n : (iter n (+%R (1 : rat)) 0 = int_to_rat n)%R.
Proof.
  elim: n => [//= | n IHn] /=.
  by rewrite -add1n PoszD IHn /int_to_rat mulrzDl.
Qed.

Lemma quot_eq1 (R : fieldType) (x y : R) : x / y = 1 -> x = y.
Proof.
  move=> H.
  have := GRing.Field.intro_unit H; rewrite invr_eq0 => Hy.
  rewrite -[y]mul1r -H -mulrA [_ * y]mulrC.
  by rewrite (divff Hy) mulr1.
Qed.

End FieldLemmas.
