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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.

Require Import tools.

Set Implicit Arguments.
Unset Strict Implicit.

Section SubtypeSeq.

Variable T : eqType.
Variable P : pred T.
Variable TP : subType P.

Fixpoint subType_seq l {struct l} :=
  match l as l1 return all P l1 -> seq TP with
    | [::]     => fun _ : true = true => [::]
    | l0 :: ll => fun Hall =>
                    match elimTF andP Hall with
                      | conj H0 Hl => (Sub l0 H0) :: (subType_seq ll Hl)
                    end
  end.


Variable lst : seq T.
Hypothesis Hall : all P lst.

Lemma subType_seqP : map val (subType_seq Hall) = lst.
Proof.
  elim: lst Hall => [//= | l0 l IHl] /=.
  case/andP => /= H0 Hall0.
  by rewrite IHl SubK.
Qed.

Hypothesis Hcount : forall x : T, P x -> count_mem x lst = 1.

Lemma finite_subP : Finite.axiom (subType_seq Hall).
Proof.
  move=> xP; set p := (X in count X _).
  rewrite (eq_count (a2 := (pred1 (val xP)) \o val)); last first.
    rewrite /p; move=> i /=.
    apply/(sameP idP); apply(iffP idP) => /eqP H; apply /eqP.
    - by apply val_inj.
    - by rewrite H.
  rewrite -count_map subType_seqP Hcount //=.
  by apply valP.
Qed.

End SubtypeSeq.


Section SubtypesDisjointUnion.

Variable T : countType.
Variable TI : countType.
Variable FI : T -> TI.
Variable P : pred T.
Variable Pi : TI -> pred T.
Variable PI : pred TI.

Variable TPI : subFinType PI.
Variable TPi : forall i : TPI, subFinType (Pi (val i)).

Hypothesis HPTi : forall i : TPI, (predI P (pred1 (val i) \o FI)) =1 (Pi (val i)).
Hypothesis Hpart : forall x : T, P x -> PI (FI x).

Definition union_list := flatten [seq map val (enum (TPi i)) | i <- enum TPI].

Lemma all_unionP : all P union_list.
Proof.
  rewrite /union_list.
  apply/allP => x /flatten_mapP [] i /mapP [] ifin Hi -> {i} /mapP [] xfin Hx -> {x}.
  have /= := valP xfin; by rewrite -HPTi /= => /andP [].
Qed.

Lemma count_unionP x : P x -> count_mem x union_list = 1.
Proof.
  move=> HPx; have:= HPx; rewrite /union_list => /Hpart H.
  rewrite count_flatten -2!map_comp; set ci := (X in map X _).
  set ix := @Sub TI PI TPI (FI x) H.
  have {ci} /eq_map -> : ci =1 (pred_of_simpl (pred1 ix)).
    rewrite /ci {ci} => i /=.
    case: (altP (i =P ix)) => [-> {i} | Hneq].
    - rewrite count_map /=.
      have Hix : Pi (val ix) x by rewrite -HPTi /= SubK HPx eq_refl.
      pose xPI := @Sub T _ (TPi ix) x Hix.
      rewrite (eq_count (a2 := pred1 xPI)); first last.
        move=> y /=.
        apply/(sameP idP); apply(iffP idP) => /eqP HH; apply /eqP.
        + by rewrite HH SubK.
        + apply val_inj; by rewrite HH SubK.
      rewrite enumT /=; by apply (@enumP (TPi ix)).
    - apply/count_memPn; move: Hneq; apply contra.
      move=> /mapP [] xfin _ Hx.
      apply/eqP; apply val_inj; rewrite SubK.
      have /= := valP xfin; by rewrite -HPTi Hx=> /andP [] _ /eqP ->.
  rewrite sumn_count /=.
  by apply (@enumP TPI).
Qed.

Variable TP : subCountType P.

Definition union_enum := subType_seq TP all_unionP.

Lemma subType_unionP : map val union_enum = union_list.
Proof. by apply subType_seqP. Qed.

Lemma finite_unionP : Finite.axiom union_enum.
Proof. apply finite_subP => x; by apply count_unionP. Qed.

Definition union_finMixin := Eval hnf in FinMixin finite_unionP.
Definition union_finType := Eval hnf in FinType TP union_finMixin.
(* Canonical union_subFinType := Eval hnf in [subFinType of T]. *)

End SubtypesDisjointUnion.

Require Import partition yama.

Lemma PredEq n (sh : intpartn_subFinType n) :
  predI (is_yam_of_size n) (pred1 (val sh) \o shape_rowseq) =1 is_yam_of_shape (val sh).
Proof.
  move=> y; rewrite /is_yam_of_size /is_yam_of_shape /= -andbA; congr (_ && _).
  case: (altP (shape_rowseq y =P sh)) => /=; last by rewrite andbF.
  rewrite -shape_rowseq_eq_size => ->.
  by rewrite (intpartn_sumn sh) eq_refl.
Qed.

Lemma shape_size n x :
  is_yam_of_size n x -> (is_part_of_n n) (shape_rowseq x).
Proof.
  by rewrite /is_yam_of_size /= shape_rowseq_eq_size => /andP [] /is_part_shyam -> ->.
Qed.


Definition yamsize n := Eval hnf in 
  union_finType
    (fun p : intpartn_subFinType n => (yamsh_subFinType (intpartnP p)))
    (@PredEq n)
    (@shape_size n) (@yamn_subCountType n).

Let bla : yamn 2 := @Yamn 2 [:: 1; 0] is_true_true.
Let blo : yamsize _ := bla.
(* Eval compute in size (Finite.enum (yamn 0)). Doesn't work ! *)
Eval compute in size (Finite.enum (yamn_finType 0)).
Let x := size (Finite.enum (yamsize 2)).

(*
Structure tuple_of : Type := Tuple {tval :> seq T; _ : size tval == n}.

Definition tuple t mkT : tuple_of :=
  mkT (let: Tuple _ tP := t return size t == n in tP).

Notation "[ 'tuple' 'of' s ]" := (tuple (fun sP => @Tuple _ _ s sP))
  (at level 0, format "[ 'tuple'  'of'  s ]") : form_scope.
subFinType_finType

*)

(*
Section SubtypeDisjointUnion.

Variable T : eqType.
Variable TI : eqType.
Variable FI : T -> TI.
Variable P : pred T.
Variable PI : pred TI.

Variable TP : subType P.

Variable lstI : seq TI.
Variable lst_fibers : TI -> seq T.

Hypothesis Hpart : forall x : T, P x <-> PI (FI x).
Hypothesis Hfibers : forall i x, x \in (lst_fibers i) -> FI x = i.

Hypothesis HallI : all PI lstI.
Hypothesis HcountI : forall i, PI i -> count_mem i lstI = 1.

Hypothesis Hall_fibers : forall i : TI, PI i -> all P (lst_fibers i).
Hypothesis Hcount_fibers : forall x, P x -> count_mem x (lst_fibers (FI x)) = 1.

Definition union_list := flatten [seq lst_fibers i | i <- lstI].

Lemma all_unionP : all P union_list.
Proof.
  rewrite /union_list; apply/allP => x /flatten_mapP [] i Hi.
  by apply (allP (Hall_fibers (allP HallI _ Hi))).
Qed.


Lemma count_unionP x : P x -> count_mem x union_list = 1.
Proof.
  rewrite /union_list Hpart => H.
  rewrite count_flatten -map_comp; set ci := (X in map X _).
  have {ci} /eq_map -> : ci =1 fun i => i == FI x.
    rewrite /ci {ci} => i /=.
    case (altP (i =P FI x)) => [-> | Hneq].
    - by rewrite Hcount_fibers //= Hpart.
    - rewrite /=; apply/count_memPn.
      move: Hneq; apply contra.
      by move/Hfibers ->.
  rewrite sumn_count; by apply HcountI.
Qed.

Definition union_enum := subType_seq TP all_unionP.

Lemma subType_unionP : map val union_enum = union_list.
Proof. by apply subType_seqP. Qed.

Lemma finite_unionP : Finite.axiom union_enum.
Proof. apply finite_subP => x; by apply count_unionP. Qed.

End SubtypeDisjointUnion.

*)
