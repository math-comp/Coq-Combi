(******************************************************************************)
(*      Copyright (C) 2015-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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

Definition int_to_rat : int -> rat := intr.
Coercion int_to_rat : int >-> rat.

Section FieldLemmas.

Local Open Scope ring_scope.

Lemma iter_plus1 n : (iter n (+%R (1 : rat)) 0 = n%:~R)%R.
Proof.
  elim: n => [//= | n IHn] /=.
  by rewrite -add1n PoszD IHn /int_to_rat mulrzDl.
Qed.

End FieldLemmas.
