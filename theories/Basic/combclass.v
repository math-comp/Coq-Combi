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
Context {T : countType} {P : pred T} {TP : subCountType P}.
Context (subenum : seq T)
  (subenumP : all P subenum)
  (subenum_countE : forall x : T, P x -> count_mem x subenum = 1).

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


Module Example.

Definition is_one n := n == 1.
Record isOne := IsOne { one :> nat; _ : is_one one}.
HB.instance Definition _ := [isSub of isOne for one].
HB.instance Definition _ := [Countable of isOne by <:].
Lemma all_isOne : all is_one [:: 1].
Proof. by []. Qed.
Lemma isOne_count_1 x : is_one x -> count_mem x [:: 1] = 1.
Proof. by rewrite /is_one; case: eqP => [->|]. Qed.
HB.instance Definition _ :=
  Finite.copy isOne (seq_finType all_isOne isOne_count_1).

Lemma enum_isOne : map val (enum (isOne : finType)) = [:: 1].
Proof. exact: enum_subE. Qed.
Lemma card_isOne : #|isOne : finType| = 1.
Proof. exact: card_subE. Qed.

End Example.



#[key=TP]
HB.factory Record seq_isFinite
  (T : countType) (P : pred T) (TP : Type) of SubCountable T P TP := {
    lst : seq T;
    all_lst : all P lst;
    lst_count_1 : forall x : T, P x -> count_mem x lst = 1;
  }.
#[key=TP]
HB.builders Context T P TP of seq_isFinite T P TP.

Definition subType_seq : seq TP := pmap insub lst.
Lemma subType_seqP : map val subType_seq = lst.
Proof.
rewrite /subType_seq; have := all_lst; elim: lst => [|l0 l IHl] //=.
by case/andP => /= H0 Hall0; rewrite insubT /= IHl // SubK.
Qed.
Lemma finite_subP : Finite.axiom subType_seq.
Proof using.
move=> xP; rewrite (eq_count (a2 := (pred1 (val xP)) \o val)).
- by rewrite -count_map subType_seqP lst_count_1 //=; exact: valP.
- by move=> i; apply/idP/idP=> /eqP H; apply/eqP; [rewrite H | apply val_inj].
Qed.
HB.instance Definition _ := isFinite.Build TP finite_subP.

(* TODO : get the following lemmas out if the HB context *)
Lemma sub_enumE : lst =i P.
Proof using.
move=> i.
apply/idP/idP; rewrite !unfold_in.
- by move=> /(allP all_lst).
- by move=> /lst_count_1 => H; apply/count_memPn; rewrite H.
Qed.
Lemma enum_subE : map val (enum (TP : finType)) = lst.
Proof using. by rewrite enumT unlock /= subType_seqP. Qed.
Lemma card_subE : #|TP : finType| = size lst.
Proof using. by rewrite cardE -(size_map val) /= enum_subE. Qed.

HB.end.




Fixpoint subType_seq l {struct l} :=
  match l as l1 return all P l1 -> seq TP with
  | [::]     => fun => [::]
  | l0 :: ll => fun Hall =>
                  match elimTF andP Hall with
                  | conj H0 Hl => (Sub l0 H0) :: (subType_seq ll Hl)
                  end
  end.

Lemma subType_seqP : map val (subType_seq all_lst) = lst.
Proof using.
elim: lst all_lst => [| l0 l IHl] //=.
by case/andP => /= H0 Hall0; rewrite IHl SubK.
Qed.

Lemma sub_enumE : lst =i P.
Proof using.
move=> i.
apply/idP/idP; rewrite !unfold_in.
- by move=> /(allP all_lst).
- by move=> /lst_count_1 => H; apply/count_memPn; rewrite H.
Qed.

Lemma finite_subP : Finite.axiom (subType_seq all_lst).
Proof using.
move=> xP; rewrite (eq_count (a2 := (pred1 (val xP)) \o val)).
- by rewrite -count_map subType_seqP lst_count_1 //=; exact: valP.
- by move=> i; apply/idP/idP=> /eqP H; apply/eqP; [rewrite H | apply val_inj].
Qed.

HB.instance Definition _ := isFinite.Build TP finite_subP.

(* TODO : get the two following lemmas out if the HB context *)
Lemma enum_subE : map val (enum (TP : finType)) = lst.
Proof using. by rewrite enumT unlock /= subType_seqP. Qed.

Lemma card_subE : #|TP : finType| = size lst.
Proof using. by rewrite cardE -(size_map val) /= enum_subE. Qed.

HB.end.




#[key=TP]
HB.factory Record seq_isFinite
  (T : countType) (P : pred T) (TP : Type) of SubCountable T P TP := {
    lst : seq T;
    all_lst : all P lst;
    lst_count_1 : forall x : T, P x -> count_mem x lst = 1;
  }.
#[key=TP]
HB.builders Context T P TP of seq_isFinite T P TP.

Fixpoint subType_seq l {struct l} :=
  match l as l1 return all P l1 -> seq TP with
  | [::]     => fun => [::]
  | l0 :: ll => fun Hall =>
                  match elimTF andP Hall with
                  | conj H0 Hl => (Sub l0 H0) :: (subType_seq ll Hl)
                  end
  end.

Lemma subType_seqP : map val (subType_seq all_lst) = lst.
Proof using.
elim: lst all_lst => [| l0 l IHl] //=.
by case/andP => /= H0 Hall0; rewrite IHl SubK.
Qed.

Lemma sub_enumE : lst =i P.
Proof using.
move=> i.
apply/idP/idP; rewrite !unfold_in.
- by move=> /(allP all_lst).
- by move=> /lst_count_1 => H; apply/count_memPn; rewrite H.
Qed.

Lemma finite_subP : Finite.axiom (subType_seq all_lst).
Proof using.
move=> xP; rewrite (eq_count (a2 := (pred1 (val xP)) \o val)).
- by rewrite -count_map subType_seqP lst_count_1 //=; exact: valP.
- by move=> i; apply/idP/idP=> /eqP H; apply/eqP; [rewrite H | apply val_inj].
Qed.

HB.instance Definition _ := isFinite.Build TP finite_subP.

(* TODO : get the two following lemmas out if the HB context *)
Lemma enum_subE : map val (enum (TP : finType)) = lst.
Proof using. by rewrite enumT unlock /= subType_seqP. Qed.

Lemma card_subE : #|TP : finType| = size lst.
Proof using. by rewrite cardE -(size_map val) /= enum_subE. Qed.

HB.end.


#[key=TP]
HB.factory Record uniq_isFinite
  (T : countType) (P : pred T) (TP : Type) of SubCountable T P TP := {
    lst : seq T;
    lst_uniq : uniq lst;
    lst_pred_eq : lst =i P;
  }.
#[key=TP]
HB.builders Context T P TP of uniq_isFinite T P TP.

Lemma all_lst : all P lst.
Proof using. by apply/allP => x; rewrite lst_pred_eq. Qed.

Lemma lst_count_1 x : P x -> count_mem x lst = 1.
Proof using.
have:= lst_pred_eq x; rewrite !unfold_in => <-.
by rewrite (count_uniq_mem _ lst_uniq) unfold_in => ->.
Qed.

HB.instance Definition _ := seq_isFinite.Build T P TP all_lst lst_count_1.
HB.end.



(** ** Method 3 - Each element appears, we remove the duplicates *)
Section SubUndup.

Hypothesis all_lst : all P lst.
Hypothesis HPin : forall x : T, P x -> x \in lst.

Lemma finite_sub_undupP :
  Finite.axiom (undup (subType_seq all_lst)).
Proof using HPin.
move=> x; rewrite count_uniq_mem; last exact: undup_uniq.
rewrite mem_undup.
by have:= HPin (valP x); rewrite -{1}subType_seqP (mem_map val_inj) => ->.
Qed.

Definition sub_undup_finMixin := Eval hnf in FinMixin finite_sub_undupP.
Definition sub_undup_finType := Eval hnf in FinType TP sub_undup_finMixin.
Definition sub_undup_subFinType := Eval hnf in [subFinType of sub_undup_finType].

Lemma enum_sub_undupE : map val (enum sub_undup_finType) = undup lst.
Proof using.
rewrite enumT unlock /= -{2}subType_seqP.
elim: lst all_lst => [//= | l0 l IHl] /=.
case/andP=> /= H0 Hall0.
rewrite mem_map; last exact: val_inj.
by case: (Sub l0 H0 \in subType_seq Hall0); rewrite /= IHl.
Qed.

End SubUndup.

End SubtypeSeq.


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
apply/allP => x /flatten_mapP [] i /mapP [] ifin Hi -> {i} /mapP [] xfin Hx -> {x}.
by have:= valP xfin; rewrite -HPTi /= => /andP [].
Qed.

Lemma count_unionP x : P x -> count_mem x enum_union = 1.
Proof using HPTi Hpart.
move=> HPx; have:= HPx; rewrite /enum_union => /Hpart H.
rewrite count_flatten -2!map_comp.
pose ix := @Sub TI PI TPI (FI x) H.
rewrite (eq_map (f2 := fun i => i == ix : nat)); first last.
  move=> i /=.
  case: (altP (i =P ix)) => [-> {i} | Hneq].
  - rewrite count_map /=.
    have Hix : Pi (val ix) x by rewrite -HPTi /= SubK HPx eq_refl.
    pose xPI := @Sub T _ (TPi ix) x Hix.
    rewrite (eq_count (a2 := pred1 xPI)); first last.
      move=> y /=; apply/idP/idP => /eqP HH; apply /eqP.
      + by apply val_inj; rewrite HH SubK.
      + by rewrite HH SubK.
    by rewrite enumT /=; exact: (@enumP (TPi ix)).
  - apply/count_memPn; move: Hneq; apply contra => /mapP [] xfin _ Hx.
  apply/eqP; apply val_inj; rewrite SubK.
  by have:= valP xfin; rewrite /= -HPTi Hx=> /andP [] _ /eqP ->.
by rewrite sumn_count /=; exact: (@enumP TPI).
Qed.

Let union_enum := subType_seq TP all_unionP.

Lemma subType_unionE : map val union_enum = enum_union.
Proof using HPTi. exact: subType_seqP. Qed.

Lemma finite_unionP : Finite.axiom union_enum.
Proof using HPTi Hpart TPi. apply finite_subP => x; exact: count_unionP. Qed.

Definition union_finMixin := Eval hnf in FinMixin finite_unionP.
Definition union_finType := Eval hnf in FinType TP union_finMixin.
Definition union_subFinType := Eval hnf in [subFinType of union_finType].

Lemma enum_unionE :
  map val (enum union_finType) = enum_union.
Proof using. by rewrite enumT unlock subType_seqP. Qed.

Lemma card_unionE : #|union_finType| = \sum_(i : TPI) #|TPi i|.
Proof using.
rewrite cardE -(size_map val) /= enum_unionE.
rewrite /enum_union size_flatten /shape -map_comp.
rewrite (eq_map (f2 := fun i => #|TPi i|)); first last.
  by move=> i; rewrite /= size_map cardE.
by rewrite sumn_mapE big_enum.
Qed.

End SubtypesDisjointUnion.
