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
Add Rec LoadPath "../Combi/LRrule".

Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop.
Require Import tools combclass.

Set Implicit Arguments.
Unset Strict Implicit.

Definition is_in_shape sh r c := c < nth 0 sh r.

Section BoxIn.

Variable sh : seq nat.

Definition is_box_in_shape b := is_in_shape sh b.1 b.2.

Structure box_in : predArgType :=
  BoxIn {coord :> nat * nat; _ : is_box_in_shape coord}.
Canonical box_in_subType := Eval hnf in [subType for coord].
Definition box_in_eqMixin := Eval hnf in [eqMixin of box_in by <:].
Canonical box_in_eqType := Eval hnf in EqType box_in box_in_eqMixin.
Definition box_in_choiceMixin := Eval hnf in [choiceMixin of box_in by <:].
Canonical box_in_choiceType := Eval hnf in ChoiceType box_in box_in_choiceMixin.
Definition box_in_countMixin := Eval hnf in [countMixin of box_in by <:].
Canonical box_in_countType := Eval hnf in CountType box_in box_in_countMixin.
Canonical box_in_subCountType := Eval hnf in [subCountType of box_in].

Definition enum_box_in :=
  flatten [seq [seq (r, c) | c <- iota 0 (nth 0 sh r) ] | r <- iota 0 (size sh)].

Lemma enum_box_in_uniq : uniq enum_box_in.
Proof.
  rewrite /enum_box_in.
  elim: sh => [//= | s0 s IHs] /=.
  rewrite cat_uniq; apply/and3P; split.
  - rewrite map_inj_uniq; first exact: iota_uniq.
    by move => i j /= [].
  - apply/hasP => [] [] x /flatten_mapP [] r.
    rewrite mem_iota add1n => /andP [] Hr _ /mapP [] c.
    rewrite mem_iota add0n /= => Hc -> {x} /mapP [] r' _ [] Hr1 _.
    move: Hr; by rewrite Hr1.
  - set l0 := (X in uniq X) in IHs; set l1 := (X in uniq X).
    have -> : l1 = [seq (x.1.+1, x.2) | x <- l0].
      rewrite /l0 /l1 {l0 l1 IHs}.
      rewrite map_flatten; congr flatten.
      rewrite -(addn0 1) iota_addl -!map_comp; apply eq_map => r /=.
      rewrite -!map_comp; apply eq_map => c /=.
      by rewrite add1n.
    rewrite map_inj_uniq; first exact IHs.
    by move=> [r1 c1] [r2 c2] /= [] -> ->.
Qed.

Lemma enum_box_inP : all (fun c => is_in_shape sh c.1 c.2) enum_box_in.
Proof.
  apply/allP => [[r c]] /= /flatten_mapP [] r0.
  rewrite mem_iota add0n /= => Hr0 /mapP [] c0.
  by rewrite mem_iota add0n /= => Hc0 [] -> ->.
Qed.

Lemma count_enum_box_inP rc : is_in_shape sh rc.1 rc.2 -> count_mem rc enum_box_in = 1.
Proof.
  case: rc => [r c] /=.
  rewrite /is_in_shape => H.
  rewrite (count_uniq_mem _ enum_box_in_uniq).
  suff -> : (r, c) \in enum_box_in by [].
  apply/flatten_mapP; exists r.
    rewrite mem_iota /= add0n.
    move: H; apply contraLR; by rewrite -!leqNgt => /(nth_default 0) ->.
  apply/mapP; exists c; by rewrite // mem_iota add0n.
Qed.

Let type := sub_finType box_in_subCountType enum_box_inP count_enum_box_inP.
Canonical box_in_finType := Eval hnf in [finType of box_in for type].
Canonical box_in_subFinType := Eval hnf in [subFinType of box_in].

Lemma box_inP (rc : box_in) : is_in_shape sh rc.1 rc.2.
Proof. by case: rc. Qed.

Lemma enum_box_inE : map val (enum box_in) = enum_box_in.
Proof. rewrite /=; by apply enum_subE. Qed.

Lemma mem_enum_box_in : enum_box_in =i is_box_in_shape.
Proof. exact: (sub_enumE enum_box_inP count_enum_box_inP). Qed.

Lemma big_enum_box_in (R : Type) (idx : R) (op : Monoid.law idx) (f : nat -> nat -> R):
  \big[op/idx]_(b <- enum_box_in) f b.1 b.2 =
  \big[op/idx]_(0 <= r < size sh) \big[op/idx]_(0 <= c < nth 0 sh r) f r c.
Proof.
  rewrite /enum_box_in.
  rewrite big_flatten /index_iota big_map !subn0; apply eq_bigr => r _.
  by rewrite big_map !subn0; apply eq_bigr.
Qed.

Lemma big_box_in (R : Type) (idx : R) (op : Monoid.law idx) (f : nat -> nat -> R):
  \big[op/idx]_(b : box_in) f b.1 b.2 = \big[op/idx]_(b <- enum_box_in) f b.1 b.2.
Proof.
  rewrite -enum_box_inE.
  - rewrite /index_enum /= enumT /=.
    elim: (Finite.enum box_in_finType) => [| b0 b] /=; first by rewrite !big_nil.
    by rewrite !big_cons => ->.
Qed.

End BoxIn.

Lemma box_in_incr_nth sh i :
  perm_eq ((i, nth 0 sh i) :: enum_box_in sh) (enum_box_in (incr_nth sh i)).
Proof.
  apply uniq_perm_eq.
  - rewrite /= enum_box_in_uniq andbT.
    apply (introN idP) => /(allP (enum_box_inP sh)) /=.
    by rewrite /is_in_shape ltnn.
  - exact: enum_box_in_uniq.
  - move=> [r c]; rewrite inE !mem_enum_box_in.
    rewrite /is_box_in_shape !unfold_in /is_in_shape /=.
    apply (sameP idP); apply (iffP idP).
    + rewrite nth_incr_nth {2}/eq_op /= eq_sym.
      case: eqP => [-> {r} | Hri] /=; last by rewrite add0n.
      by rewrite add1n ltnS leq_eqVlt.
    + move/orP => [/eqP [] -> ->|].
      * by rewrite nth_incr_nth eq_refl add1n ltnS.
      * move => /leq_trans; apply.
        rewrite nth_incr_nth; by apply leq_addl.
Qed.

