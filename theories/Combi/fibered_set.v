(** * Combi.Combi.fibered_set : Bijection beetween fibered sets *)
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
(** * Bijection beetween fibered sets

Given a type with equality [I] a fiberedset is a set [fbset] in an ihnabited
fintype [T] equiped with a function [fbfun : fbset -> I]. The preimage of some
[i] under [fbfun] is called the fiber of [i]. The goal of this file is to show
that if two fibered set [S1] [S2] have their fiber of [i] of the same
cardinality for all [i], then there there exists a bijection [fbbij] from [S1]
to [S2] which sends the fiber of [i] to the fiber of [i]. That is [fbbij]
commute with the [fbfun] : [forall x, fbfun2 (fbbij x) = fbfun1 x].

- [fibered_set] == record for fibered sets on a carrier [finType]
- [fiber S i]  == the [i]-fiber of [S]

- [fbbij U V] == a bijection from [U] to [V] provided the two fibered sets [U]
  and [V] have their fiber of [i] of the same cardinality:

  [Hypothesis HcardEq : forall i, #|fiber U i| = #|fiber V i|.]

*)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial.

Set Implicit Arguments.
Unset Strict Implicit.

Section BijFiberedSet.

Variable I : eqType.

Record fibered_set := FiberedSet {
                          carrier : finType;
                          elt     : carrier;
                          fbset   :> {set carrier};
                          fbfun   : carrier -> I }.

Definition fiber (S : fibered_set) v := [set x | x in S & fbfun x == v].

Lemma mem_fiber (S : fibered_set) x : x \in S -> x \in fiber S (fbfun x).
Proof using.
move=> Hx; apply/imsetP; exists x => //.
by rewrite inE Hx /=.
Qed.

Definition fbbij (U V : fibered_set) (x : carrier U) : carrier V :=
  nth (elt V) (enum (fiber V (fbfun x))) (index x (enum (fiber U (fbfun x)))).

Section Defs.

Variable U V : fibered_set.
Hypothesis HcardEq : forall i, #|fiber U i| = #|fiber V i|.

Lemma fbbij_in_fiber x : x \in U -> fbbij V x \in fiber V (fbfun x).
Proof using HcardEq.
move=> Hx; rewrite -mem_enum; apply mem_nth.
by rewrite -cardE -HcardEq cardE index_mem mem_enum; apply: mem_fiber.
Qed.

Lemma fbset_fbbij x : x \in U -> fbbij V x \in V.
Proof using HcardEq.
by move=> /fbbij_in_fiber /imsetP [x0]; rewrite inE => /andP [] Hx0 _ ->.
Qed.

Lemma equi_fbbij x : x \in U -> fbfun (fbbij V x) = fbfun x.
Proof using HcardEq.
move=> /fbbij_in_fiber.
by move=> /imsetP [im0]; rewrite inE => /andP [_ /eqP <- ->].
Qed.

Lemma fbbijK : {in U, cancel (fbbij V) (fbbij U)}.
Proof using HcardEq.
move=> x Hx.
have : index (fbbij V x) (enum (fiber V (fbfun x))) =
       index x         (enum (fiber U (fbfun x))).
  rewrite index_uniq //; last exact: enum_uniq.
  by rewrite -cardE -HcardEq cardE index_mem mem_enum; apply: mem_fiber.
rewrite /fbbij (equi_fbbij Hx) => ->.
apply nth_index.
by rewrite mem_enum; apply: mem_fiber.
Qed.

Lemma inj_fbbij : {in U &, injective (fbbij V)}.
Proof using HcardEq. exact: can_in_inj fbbijK. Qed.

End Defs.

Lemma surj_fbbij (U V : fibered_set) :
  (forall i, #|fiber U i| = #|fiber V i|) -> [set fbbij V x | x in U] = V.
Proof using.
rewrite -setP => HcardEq y.
apply/imsetP/idP => [[x Hx] -> {y} | Hy].
- exact: fbset_fbbij.
- exists (fbbij U y); first exact: fbset_fbbij.
  by rewrite fbbijK //.
Qed.

Lemma fbbijP (U V : fibered_set) :
  (forall i, #|fiber U i| = #|fiber V i|) ->
  [/\ {in U &, injective (fbbij V)},
   [set fbbij V x | x in U] = V &
   {in U, forall x, fbfun (fbbij V x) = fbfun x} ].
Proof using. split; [exact: inj_fbbij | exact: surj_fbbij | exact: equi_fbbij]. Qed.

End BijFiberedSet.
