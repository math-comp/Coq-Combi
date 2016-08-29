(** * Combi.Combi.permuted : Listing the Permutations of a tuple or seq *)

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
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import tuple bigop path div finset binomial.
From mathcomp Require Import perm.

Require Import tools permcomp.

(** * The list of the permuted tuple of a given tuple

The main goal is to show that, given a sequence [s] over an [eqType] there
are only finitely many sequences [s'] which are a permutation of [s] (that is
[perm_eq s s'])

- [permuted_tuple t] == a sequence of tuples containing (with duplicates) all
             tuple [t'] such that [perm_eq t t']
- [permuted_seq s] == a sequence of seqs containing (with duplicates) all seqs
             [s'] such that [perm_eq s s']
- [permuted t] == sigma typle for tuple [t'] such that [perm_eq t t'].  this
             is canonically a [fintype], provided the typle of the element of
             [t] is a [countType].

 *)

Set Implicit Arguments.
Unset Strict Implicit.

Section Permuted.

Variable T : eqType.

Section SizeN.

Variable n : nat.

Definition permuted_tuple (t : n.-tuple T) :=
  [seq [tuple tnth t (aperm i p) | i < n] | p <- enum 'S_n ].

Lemma size_permuted_tuple (t : n.-tuple T) : size (permuted_tuple t) = n`!.
Proof using . rewrite /permuted_tuple size_map -cardE; exact: card_Sn. Qed.

Lemma perm_eq_permuted_tuple (s : seq T) (H : size s == n) :
  forall s1, perm_eq s s1 -> s1 \in [seq tval t | t <- permuted_tuple (Tuple H)].
Proof using .
  set t := Tuple H; have Ht : perm_eq s t by [].
  move=> s1 Hss1; rewrite perm_eq_sym in Hss1.
  have:= perm_eq_trans Hss1 Ht => /tuple_perm_eqP [] p Hs1.
  apply/mapP; set t1 := (X in _ = tval X) in Hs1; exists t1; last exact Hs1.
  rewrite /permuted_tuple; apply/mapP.
  by exists p; first by rewrite mem_enum.
Qed.

Lemma mem_enum_permuted (s t : n.-tuple T) :
  perm_eq s t -> t \in permuted_tuple s.
Proof.
  rewrite perm_eq_sym => /tuple_perm_eqP [perm Hperm].
  apply/mapP; exists perm; first by rewrite mem_enum.
  by apply val_inj => /=; rewrite Hperm => /=.
Qed.

Lemma all_permuted (s : n.-tuple T) :
  all (fun x : n.-tuple T => perm_eq s x) (permuted_tuple s).
Proof.
  apply/allP => t /mapP /= [perm _] -> {t}.
  by rewrite perm_eq_sym; apply/tuple_perm_eqP; exists perm.
Qed.

End SizeN.

Definition permuted_seq s :=
  [seq tval t | t <- permuted_tuple (Tuple (eq_refl (size s)))].

Lemma size_permuted_seq s : size (permuted_seq s) = (size s)`!.
Proof using . by rewrite /permuted_seq size_map size_permuted_tuple. Qed.

Lemma eq_seqE s s1 : perm_eq s s1 -> s1 \in permuted_seq s.
Proof using . exact: perm_eq_permuted_tuple. Qed.

End Permuted.

Require Import combclass.


Section FinType.

Variable T : countType.
Variable n : nat.
Variable w : n.-tuple T.

Structure permuted : predArgType :=
  Permuted { tpval :> n.-tuple T; _ : perm_eq w tpval }.

Canonical permuted_subType := Eval hnf in [subType for tpval].
Definition permuted_eqMixin := Eval hnf in [eqMixin of permuted by <:].
Canonical permuted_eqType := Eval hnf in EqType permuted permuted_eqMixin.
Definition permuted_choiceMixin := Eval hnf in [choiceMixin of permuted by <:].
Canonical permuted_choiceType :=
  Eval hnf in ChoiceType permuted permuted_choiceMixin.
Definition permuted_countMixin := Eval hnf in [countMixin of permuted by <:].
Canonical permuted_countType :=
  Eval hnf in CountType permuted permuted_countMixin.
Canonical permuted_subCountType := Eval hnf in [subCountType of permuted].

Let type := sub_undup_finType permuted_subCountType
                              (all_permuted w) (mem_enum_permuted (s := w)).
Canonical permuted_finType := [finType of permuted for type].
Canonical permuted_subFinType := Eval hnf in [subFinType of permuted].

Lemma permutedP (p : permuted) : perm_eq w p.
Proof. by case: p. Qed.

End FinType.

Hint Resolve permutedP.
