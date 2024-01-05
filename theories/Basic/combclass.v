(** * Combi.Basic.combclass : Fintypes for Combinatorics *)
(******************************************************************************)
(*      Copyright (C) 2014-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * Fintypes for Combinatorics

The goal of this file is to define various way to easily build finite
subtype of a countable type knowing a lists of its elements. We provide four
ways, three from a list (see [sub_subFinType], [sub_uniq_subFinType] and
[sub_undup_subFinType] below) and one by taking the disjoint union of already
constructed subfintypes (see [union_subFinType] below).  *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Require Import tools.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Summing [count_mem] in a [finType] *)
Lemma sum_count_mem (T : finType) (P : pred T) l :
  \sum_(i | P i) (count_mem i) l = count P l.
Proof.
rewrite uniq_sum_count_mem; last exact: index_enum_uniq.
by apply: eq_count => x /=; rewrite mem_index_enum.
Qed.


(** * Building subtype from a sequence

Here is how to construct a fintype from a list: we are given
- a type [T] which is a [countType]
- a type [TP] which is [subCountType] of [T] for a predicate [P].
- a list [lst] of element from [T] whose element veryfies the predicate [P].

We define three possible ways to provide [TP] with a [subFinType] structure:
- [sub_subFinType] which suppose that any element verifying [P] appears only
  once in [lst];
- [sub_uniq_subFinType] which suppose that any element verifying [P] appears in
  [lst] and that [lst] is duplicate free ([uniq]);
- [sub_undup_subFinType] which suppose that any element verifying [P] appears in
  [lst] and remove the duplicate elements.
 *)


Section EnumFintype.
Context {T : countType} {P : pred T} (TP : subCountType P).
Variable subenum : seq T.
Hypothesis subenumP : all P subenum.
Hypothesis subenum_countE : forall x : T, P x -> count_mem x subenum = 1.

Lemma sub_enumE : subenum =i P.
Proof.
move=> i.
apply/idP/idP; rewrite !unfold_in.
- by move=> /(allP subenumP).
- by move=> /subenum_countE => H; apply/count_memPn; rewrite H.
Qed.

Definition subType_seq : seq TP := pmap insub subenum.
Lemma subType_seqP : map val subType_seq = subenum.
Proof.
rewrite /subType_seq; elim: subenum subenumP => [|l0 l IHl] //=.
by case/andP => /= H0 Hall0; rewrite insubT /= IHl // SubK.
Qed.
Lemma finite_subP : Finite.axiom subType_seq.
Proof.
move=> xP; rewrite (eq_count (a2 := (pred1 (val xP)) \o val)).
- by rewrite -count_map subType_seqP subenum_countE //=; exact: valP.
- by move=> i; apply/idP/idP=> /eqP H; apply/eqP; [rewrite H | apply val_inj].
Qed.
Definition seq_finType : finType :=
  HB.pack TP (isFinite.Build TP finite_subP).

Lemma enum_subE : map val (enum (seq_finType)) = subenum.
Proof. by rewrite enumT unlock /= subType_seqP. Qed.
Lemma card_subE : #|seq_finType| = size subenum.
Proof using. by rewrite cardE -(size_map val) /= enum_subE. Qed.

End EnumFintype.


Module Example1.

Definition is_one n := n == 1.
Record isOne := IsOne { one :> nat; _ : is_one one}.
HB.instance Definition _ := [isSub of isOne for one].
HB.instance Definition _ := [Countable of isOne by <:].
Lemma all_isOne : all is_one [:: 1].
Proof. by []. Qed.
Lemma isOne_count_1 x : is_one x -> count_mem x [:: 1] = 1.
Proof. by rewrite /is_one; case: eqP => [->|]. Qed.
HB.instance Definition _ :=
  Finite.copy isOne (seq_finType isOne all_isOne isOne_count_1).

Lemma enum_isOne : map val (enum (isOne : finType)) = [:: 1].
Proof. exact: enum_subE. Qed.
Lemma card_isOne : #|isOne : finType| = 1.
Proof. exact: card_subE. Qed.

End Example1.



(** ** Method 2 - Each element appears and the lists is uniq *)
Section UniqFinType.
Context {T : countType} {P : pred T} (TP : subCountType P).
Variable subenum : seq T.
Hypothesis subenumE : subenum =i P.
Hypothesis subenum_uniq : uniq subenum.

Lemma all_subenum : all P subenum.
Proof. by apply/allP => x; rewrite subenumE. Qed.
Lemma subenum_countE x : P x -> count_mem x subenum = 1.
Proof.
have:= subenumE x; rewrite !unfold_in => <-.
by rewrite (count_uniq_mem _ subenum_uniq) unfold_in => ->.
Qed.
Definition uniq_finType : finType :=
  seq_finType TP all_subenum subenum_countE.
End UniqFinType.


Module Example2.

Definition is_one n := n == 1.
Record isOne := IsOne { one :> nat; _ : is_one one}.
HB.instance Definition _ := [isSub of isOne for one].
HB.instance Definition _ := [Countable of isOne by <:].
Lemma all_isoneE : [:: 1] =i is_one.
Proof. by move=> n; rewrite inE. Qed.
Lemma isOne_uniq : uniq [:: 1].
Proof. by []. Qed.
HB.instance Definition _ :=
  Finite.copy isOne (uniq_finType isOne all_isoneE isOne_uniq).

Lemma enum_isOne : map val (enum (isOne : finType)) = [:: 1].
Proof. exact: enum_subE. Qed.
Lemma card_isOne : #|isOne : finType| = 1.
Proof. exact: card_subE. Qed.

End Example2.


(** ** Method 3 - Each element appears, we remove the duplicates *)
Section SubUndup.
Context {T : countType} {P : pred T} (TP : subCountType P).
Variable subenum : seq T.
Hypothesis subenumP : all P subenum.
Hypothesis subenum_in : forall x : T, P x -> x \in subenum.

Lemma finite_sub_undupP :
  Finite.axiom (undup (subType_seq TP subenum)).
Proof.
move=> x; rewrite count_uniq_mem; last exact: undup_uniq.
rewrite mem_undup; have /= := subenum_in (valP x).
by rewrite -{1}(subType_seqP TP subenumP) (mem_map val_inj) => ->.
Qed.
Definition undup_finType : finType :=
  HB.pack TP (isFinite.Build TP finite_sub_undupP).

Lemma enum_sub_undupE : map val (enum undup_finType) = undup subenum.
Proof.
rewrite enumT unlock /= -{2}(subType_seqP TP subenumP).
by rewrite (undup_map_inj val_inj).
Qed.

End SubUndup.


Module Example3.

Definition is_one n := n == 1.
Record isOne := IsOne { one :> nat; _ : is_one one}.
HB.instance Definition _ := [isSub of isOne for one].
HB.instance Definition _ := [Countable of isOne by <:].
Lemma all_isOne : all is_one [:: 1; 1].
Proof. by []. Qed.
Lemma isOne_in n : is_one n -> n \in [:: 1; 1].
Proof. by move/eqP => ->. Qed.
HB.instance Definition _ :=
  Finite.copy isOne (undup_finType isOne all_isOne isOne_in).

Lemma enum_isOne : map val (enum (isOne : finType)) = [:: 1].
Proof. exact: enum_sub_undupE. Qed.
Lemma card_isOne : #|isOne : finType| = 1.
Proof. by rewrite cardE -(size_map val) /= enum_isOne. Qed.

End Example3.


(** * Finite subtype obtained as a finite the dijoint union of finite subtypes

Here is how to construct a union of disjoint finite subtype of a countable
type. More precisely, we want to define a type for

    <<U := Union_(i : TI | Pi i) TPi i>>

For the constructed type [U], we need the following data:
- a type [T] which is a [countType].
- a type [TP] which is [subCountType] of [T] for a predicate [P].
The index type must be also countable, it should be given by
- a type [TI] which is a [countType].
- a type [TPI] which is [subCountType] of [TI] for a predicate [PI].
For all index [i : TPI], there must be a finite type, given by
- a type [TPi i] which is a [subFinType (Pi (val i))] for a predicate [Pi i].
Finally the sets <<{ { x | Pi i } | PI i }>> should define a partition
of <<{ x | P x }>>. This is ensured by providing
- a map [FI : T -> TI] which recover the index of an element [x] of [T].
Together with the two following requirements:
- for all index [i : TPi] and [x : T], the statement [Pi i x] must be
  equivalent to [P x && i == FI x].
- forall [x : T], such that [P x] the assertion [PI (FI x)] must holds.
From all these data [union_subFinType] is a [subFinType] of [T] for the
predicate [P] that is a [subFinType] structure for [TP].

See [stpn_subFinType] and [yamn_subFinType] for example of usage.
 *)
Section SubtypesDisjointUnion.

Variable T : countType.
Variable P : pred T.
Variable TP : subCountType P.

Variable TI : countType.
Variable PI : pred TI.
Variable TPI : subFinType PI.

Variable Pi : TI -> pred T.
Variable TPi : forall i : TPI, subFinType (Pi (val i)).

Variable FI : T -> TI.
Hypothesis HPTi : forall i : TPI, (predI P (pred1 (val i) \o FI)) =1 (Pi (val i)).
Hypothesis Hpart : forall x : T, P x -> PI (FI x).

Definition enum_union := flatten [seq map val (enum (TPi i)) | i : TPI].

Lemma all_unionP : all P enum_union.
Proof using HPTi.
rewrite /enum_union.
apply/allP => x /flatten_mapP[i /mapP[ifin Hi ->{i}] /mapP[xfin Hx ->{x}]].
by have:= valP xfin; rewrite -HPTi /= => /andP[].
Qed.

Lemma count_unionP x : P x -> count_mem x enum_union = 1.
Proof using HPTi Hpart.
move=> HPx; have:= HPx; rewrite /enum_union => /Hpart H.
rewrite count_flatten -2!map_comp.
pose ix := @Sub TI PI TPI (FI x) H.
rewrite (eq_map (g := fun i => i == ix : nat)); first last.
  move=> i /=.
  case: eqP => [->{i} | Hneq].
  - rewrite count_map /=.
    have Hix : Pi (val ix) x by rewrite -HPTi /= SubK HPx eq_refl.
    pose xPI := @Sub T _ (TPi ix) x Hix.
    rewrite (eq_count (a2 := pred1 xPI)); first last.
      move=> y /=; apply/eqP/eqP => HH.
      + by apply val_inj; rewrite HH SubK.
      + by rewrite HH SubK.
    by rewrite enumT /=; exact: (@enumP (TPi ix)).
  - apply/count_memPn; apply/contra_notN: Hneq => /mapP[xfin _ Hx].
    apply val_inj; rewrite SubK.
    by have:= valP xfin; rewrite /= -HPTi Hx=> /andP[_ /eqP->].
by rewrite sumn_count /=; exact: (@enumP TPI).
Qed.

Let union_enum := subType_seq TP enum_union.

Lemma subType_unionE : map val union_enum = enum_union.
Proof using HPTi. by rewrite subType_seqP // all_unionP. Qed.
Lemma finite_unionP : Finite.axiom union_enum.
Proof using HPTi Hpart TPi. exact: (finite_subP all_unionP count_unionP). Qed.
Definition union_finType : finType :=
  HB.pack TP (isFinite.Build TP finite_unionP).

Lemma enum_unionE :
  map val (enum union_finType) = enum_union.
Proof using. by rewrite enumT unlock subType_seqP // all_unionP. Qed.

Lemma card_unionE : #|union_finType| = \sum_(i : TPI) #|TPi i|.
Proof using.
rewrite cardE -(size_map val) /= enum_unionE.
rewrite /enum_union size_flatten /shape -map_comp.
rewrite (eq_map (g := fun i => #|TPi i|)); first last.
  by move=> i; rewrite /= size_map cardE.
by rewrite sumn_mapE big_enum.
Qed.

End SubtypesDisjointUnion.
