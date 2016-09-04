(** * Combi.Combi.Kostka : Kostka numbers *)
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
(** * Kostka numbers
*****)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import path finset bigop tuple.
Require Import tools ordtype sorted combclass partition tableau.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope N.

Section DefsTuple.

Variables (d : nat) (sh : intpartn d) (n : nat).
Implicit Type ev : n.+1.-tuple nat.
Definition KostkaTab ev :=
  [set t : tabsh n sh |
   [forall i : 'I_n.+1, count_mem i (to_word t) == tnth ev i]].
Definition KostkaT ev := #|KostkaTab ev|.

Lemma KostkaT_sumeval ev :
  sumn ev != sumn sh -> KostkaT ev == 0.
Proof.
apply contraR; rewrite cards_eq0 => /set0Pn /= [t]; rewrite inE => /forallP /= Ht.
rewrite -sumnE big_tuple.
rewrite (eq_bigr (fun i => (count_mem i) (to_word t))); first last.
  by move=> i _; rewrite (eqP (Ht i)).
by rewrite sum_count_mem count_predT size_to_word /size_tab shape_tabsh.
Qed.

Lemma perm_KostkaT ev1 ev2 :
  perm_eq ev1 ev2 -> KostkaT ev1 = KostkaT ev2.
Proof.
Admitted.

End DefsTuple.

Require Import Yamanouchi Yam_plact.

Lemma evalseq_eq_shape_unique (t : seq (seq nat)) :
  is_tableau t -> evalseq (to_word t) = (shape t) -> t = yamtab (shape t).
Proof.
Admitted.  
