(** * Combi.Combi.permuted : Listing the Permutations of a seq *)

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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype seq tuple.
Require Import finset perm.

(** * The list of the permuted tuple of a given tuple                        *)
(*
The main goal is to show that, given a sequence [s] over an [eqType] there
are only finitely many sequences [s'] which are a permutation of [s] (that is
[perm_eq s s']
*)

Set Implicit Arguments.
Unset Strict Implicit.

Section Permuted.

Variable T : eqType.

Section SizeN.

Variable n : nat.

Lemma card_Sn : #|'S_(n)| = n`!.
Proof.
  rewrite (eq_card (B := perm_on [set : 'I_n])).
    by rewrite card_perm /= cardsE /= card_ord.
  move=> p; rewrite inE unfold_in /perm_on /=.
  apply/esym/subsetP => i _; by rewrite in_set.
Qed.

Definition permuted_tuple (t : n.-tuple T) :=
  [seq [tuple tnth t (aperm i p) | i < n] | p <- enum 'S_n ].

Lemma size_permuted_tuple (t : n.-tuple T) : size (permuted_tuple t) = n`!.
Proof. rewrite /permuted_tuple size_map -cardE; exact card_Sn. Qed.

Lemma perm_eq_permuted_tuple (s : seq T) (H : size s == n) :
  forall s1, perm_eq s s1 -> s1 \in [seq tval t | t <- permuted_tuple (Tuple H)].
Proof.
  set t := Tuple H; have Ht : perm_eq s t by [].
  move=> s1 Hss1; rewrite perm_eq_sym in Hss1.
  have:= perm_eq_trans Hss1 Ht => /tuple_perm_eqP [] p Hs1.
  apply/mapP; set t1 := (X in _ = tval X) in Hs1; exists t1; last exact Hs1.
  rewrite /permuted_tuple; apply/mapP.
  by exists p; first by rewrite mem_enum.
Qed.

End SizeN.

Definition permuted s :=
  [seq tval t | t <- permuted_tuple (Tuple (eq_refl (size s)))].

Lemma size_permuted s : size (permuted s) = (size s)`!.
Proof. by rewrite /permuted size_map size_permuted_tuple. Qed.

Lemma eq_seqE s s1 : perm_eq s s1 -> s1 \in permuted s.
Proof. exact: perm_eq_permuted_tuple. Qed.

End Permuted.

