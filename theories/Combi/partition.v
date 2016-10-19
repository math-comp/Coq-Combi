(** * Combi.Combi.partition : Integer Partitions *)
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
(** * Shapes and Integer Partitions

Partitions (and more generally shapes) are stored by terms of type [seq (seq
nat)]. We define the following predicates and operations on [seq (seq nat)]:
[(r, c)] is in [sh] if [r < sh[i]]

- [is_in_shape sh r c] == the box with coordinate (r, c) belongs to the shape
                          sh, that is: [c < sh[r]].
- [is_box_in_shape (r, c)] == uncurried version: same as [is_in_shape sh r c].
- [box_in sh] == a sigma type for boxes in sh : [{ b | is_box_in_shape sh b }]
                 is is canonically a [subFinType].
- [enum_box_in sh] == a full duplicate free list of the boxes in sh.

Integer Partitions:

- [is_part sh] == [sh] is a partition
- [rem_trail0 sh] == remove the trailing zeroes of a shape
- [is_add_corner sh i] == i is the row of an addable corner of sh
- [is_rem_corner sh i] == i is the row of a removable corner of sh
- [incr_nth sh i] == the shape obtained by adding a box at the end of the
                     i-th row. This gives a partition if i is an addable
                     corner of sh (Lemma [is_part_incr_nth])
- [decr_nth sh i] == the shape obtained by removing a box at the end of the
                     i-th row. This gives a partition if i is an removable
                     corner of sh (Lemma [is_part_decr_nth])
- [rem_corners sh] == the list of the rows of the removable corners of sh.
- [incr_first_n sh n] == adding 1 to the n'th first part of sh,
                     always gives a partitions
- [conj_part sh] == the conjugate of a partition
- [included s t] == the Ferrer's diagram of s is included in the
                    Ferrer's diagram of t. This is an order.
- [diff_shape s t] == the difference of the shape s and t
- [outer_shape s t] == add t to the shape s


Enumeration of integer partitions:

- [is_part_of_n sm sh] == sh in a partition of n
- [is_part_of_ns sm sz sh] == sh in a partitionfo n of size sz
- [is_part_of_nsk sm sz mx sh] == sh in a partition of n of size sz
                                    in parts at most mx
- [enum_partn sm] == the lists of all partitions of n
- [enum_partns sm sz] == the lists of all partitions of n of size sz
- [enum_partnsk sm sz mx] == the lists of all partitions of n of size sz
                                    in parts at most mx

- [intpartn_nb sm] == the number of partitions of n
- [intpartns_nb sm sz] == the number of partitions of n of size sz
- [intpartnsk_nb sm sz mx] == the number of partitions of n of size sz
                                    in parts at most mx


Sigma types for integer partitions:

- [intpart] == a type for [seq (seq nat)] which are partitions; it is
               canonically a [subCountType] of [seq (seq nat)]
- [conj_intpart] == the conjugate of a [intpart] as a [intpart]

- [intpart n] == a type for [seq (seq nat)] which are partitions of n;
               it is canonically a [finType]
- [conj_intpartn] == the conjugate of a [intpartn] as a [intpartn]


Operations on partitions:

- [union_intpart l k] == the partition of type [intpart] obtained by
               gathering the parts of [l] and [k]
- [union_intpartn l k] == the partition of type [intpartn] obtained by
               gathering the parts of [l] and [k]

Comparison of partitions:

- [partdom s t] == [s] is dominated by [t], that is the partial sum of [s] are
               smaller that the partial sum of [t].
- [intpartndom d] == a type convertible to [intpart d] which is canonically
               finite and partially ordered by [partdom].
- [(s <= t)%Ord] == [s] is smaller than [t] for the lexicographic order

Relation with set partitions:

- [setpart_shape P] == the shape of a set partition, i.e.
               the sorted list of the cardinal of the parts
******)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import bigop path.
Require Import tools combclass sorted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Shapes *)
Definition is_in_shape sh r c := c < nth 0 sh r.

Lemma is_in_shape_size sh r c : is_in_shape sh r c -> r < size sh.
Proof.
rewrite /is_in_shape; apply contraLR; rewrite -!leqNgt => Hr.
by rewrite (nth_default _ Hr).
Qed.

(** ** A finite type [finType] for coordinate of boxes inside a shape *)
Section BoxIn.

Variable sh : seq nat.

Definition is_box_in_shape b := is_in_shape sh b.1 b.2.

Structure box_in : Set :=
  BoxIn {coordbox :> nat * nat; _ : is_box_in_shape coordbox}.
Canonical box_in_subType := Eval hnf in [subType for coordbox].
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
Proof using.
rewrite /enum_box_in.
elim: sh => [//= | s0 s IHs] /=.
rewrite cat_uniq; apply/and3P; split.
- rewrite map_inj_uniq; first exact: iota_uniq.
  by move => i j /= [].
- apply/hasP => [] [] x /flatten_mapP [] r.
  rewrite mem_iota add1n => /andP [] Hr _ /mapP [] c.
  rewrite mem_iota add0n /= => Hc -> {x} /mapP [] r' _ [] Hr1 _.
  move: Hr; by rewrite Hr1.
- set l0 := (X in uniq X) in IHs.
  rewrite [X in uniq X](_ : _ = [seq (x.1.+1, x.2) | x <- l0]); first last.
    rewrite /l0 {l0 IHs} map_flatten; congr flatten.
    rewrite -(addn0 1) iota_addl -!map_comp; apply eq_map => r /=.
    rewrite -!map_comp; apply eq_map => c /=.
    by rewrite add1n.
  rewrite map_inj_uniq; first exact IHs.
  by move=> [r1 c1] [r2 c2] /= [] -> ->.
Qed.

Lemma enum_box_inP : all (fun c => is_in_shape sh c.1 c.2) enum_box_in.
Proof using.
apply/allP => [[r c]] /= /flatten_mapP [] r0.
rewrite mem_iota add0n /= => Hr0 /mapP [] c0.
by rewrite mem_iota add0n /= => Hc0 [] -> ->.
Qed.

Lemma count_enum_box_inP rc :
  is_in_shape sh rc.1 rc.2 -> count_mem rc enum_box_in = 1.
Proof using.
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
Proof using. by case: rc. Qed.

Lemma enum_box_inE : map val (enum {:box_in}) = enum_box_in.
Proof using. exact: enum_subE. Qed.

Lemma mem_enum_box_in : enum_box_in =i is_box_in_shape.
Proof using. exact: (sub_enumE enum_box_inP count_enum_box_inP). Qed.

(** ** Rewriting bigops running along the boxes of a shape *)
Lemma big_enum_box_in
      (R : Type) (idx : R) (op : Monoid.law idx) (f : nat -> nat -> R):
  \big[op/idx]_(b <- enum_box_in) f b.1 b.2 =
  \big[op/idx]_(0 <= r < size sh) \big[op/idx]_(0 <= c < nth 0 sh r) f r c.
Proof using.
rewrite /enum_box_in.
rewrite big_flatten /index_iota big_map !subn0; apply eq_bigr => r _.
by rewrite big_map !subn0; apply eq_bigr.
Qed.

Lemma big_box_in (R : Type) (idx : R) (op : Monoid.law idx) (f : nat -> nat -> R):
  \big[op/idx]_(b : box_in) f b.1 b.2 = \big[op/idx]_(b <- enum_box_in) f b.1 b.2.
Proof using.
rewrite -enum_box_inE /index_enum /= -enumT /=.
elim: (enum _) => [| b0 b] /=; first by rewrite !big_nil.
by rewrite !big_cons => ->.
Qed.

End BoxIn.

(** ** Adding a box to a shape *)
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
  apply/idP/idP.
  + move/orP => [/eqP [] -> ->|].
    * by rewrite nth_incr_nth eq_refl add1n ltnS.
    * move => /leq_trans; apply.
      rewrite nth_incr_nth; exact: leq_addl.
  + rewrite nth_incr_nth {2}/eq_op /= eq_sym.
    case: eqP => [-> {r} | Hri] /=; last by rewrite add0n.
    by rewrite add1n ltnS leq_eqVlt.
Qed.


(** * Integer Partitions *)
(** ** Definitions and basic properties *)

Implicit Type s : seq nat.

Fixpoint is_part sh :=
  if sh is sh0 :: sh'
  then (sh0 >= head 1 sh') && (is_part sh')
  else true.

(** Partitions don't have 0 parts *)
Lemma part_head0F sh : head 1 sh == 0 -> is_part sh = false.
Proof.
elim: sh => [//= | sh0 sh IHsh] /= /eqP ->.
rewrite leqn0; by case (boolP (head 1 sh == 0)).
Qed.

Lemma part_head_non0 sh : is_part sh -> head 1 sh != 0.
Proof.
elim: sh => [//= | sh0 sh IHsh] /= /andP [] Head.
move/IHsh; apply: contraLR; rewrite !negbK => /eqP Hsh0.
by move: Head; rewrite Hsh0 leqn0.
Qed.

Lemma nth_part_non0 sh i : is_part sh -> i < size sh -> nth 0 sh i != 0.
Proof.
elim: i sh => [//= | i IHi] [//=| s0 s].
  by move=> /part_head_non0.
move=> /= /andP [] _.
exact: IHi.
Qed.

(** Three equivalent definitions *)
Lemma is_partP sh :
  reflect
    (last 1 sh != 0 /\ forall i, (nth 0 sh i) >= nth 0 sh i.+1)
    (is_part sh).
Proof.
apply: (iffP idP).
- elim: sh => [ //= | sh0 sh IHsh] /= /andP [] Hhead Hpart.
  move/(_ Hpart) : IHsh => [] Hlast Hi.
  split; first by case: sh Hhead Hpart Hlast Hi => [/= | sh1 sh //=]; case sh0.
  case => [|i] /=; first by move: Hhead; case sh.
  exact (Hi i).
- elim: sh => [ //= | sh0 sh IHsh] /= [] Hlast Hpart.
  apply/andP; split.
  * move: Hlast; move/(_ 0) : Hpart => /=; case sh => //=.
    by rewrite /head ltn_neqAle eq_sym => -> ->.
  * apply: IHsh; split; last by move=> i; apply: (Hpart i.+1).
    move: Hlast; by case sh.
Qed.

Lemma is_part_ijP sh :
  reflect
    (last 1 sh != 0 /\ forall i j, i <= j -> (nth 0 sh i) >= nth 0 sh j)
    (is_part sh).
Proof.
apply: (iffP idP).
- move/is_partP => [] H0 H; split; first exact H0.
  move=> i {H0} j /subnKC <-.
  elim: (j - i) => [|n IHn] {j}; first by rewrite addn0.
  rewrite addnS.
  exact: (leq_trans (H _) IHn).
- move=> [] H0 H; apply/is_partP; split; first exact H0.
  move=> {H0} i.
  exact: H.
Qed.

Lemma is_part_sortedE sh : (is_part sh) = (sorted geq sh) && (0 \notin sh).
Proof.
apply/idP/andP => [Hpart|].
- split.
  + apply/sorted1P => i _.
    by move: Hpart=> /is_partP [_]; apply.
  + move: Hpart; elim: sh => [// | s0 sh IHsh] Hpart.
    rewrite inE negb_or eq_sym.
    have /= -> /= := (part_head_non0 Hpart).
    by apply IHsh; move: Hpart => /andP [].
- move=> [/sorted1P Hsort Hnotin].
  apply/is_partP; split => [| i].
  + case: sh Hnotin {Hsort} => [// | s0 sh].
    rewrite inE negb_or eq_sym => /andP [Hs0 Hnot] /=.
    elim: sh s0 Hs0 Hnot => [// | s1 sh IHsh] s0 _.
    rewrite inE negb_or eq_sym /= => /andP [].
    exact: IHsh.
  + case: (ltnP i.+1 (size sh)) => Hsz; first exact: Hsort.
    by rewrite (nth_default _ Hsz).
Qed.

(** Sub-partitions *)

Lemma is_part_consK l0 sh : is_part (l0 :: sh) -> is_part sh.
Proof. by move=> /= /andP []. Qed.

Lemma is_part_behead sh : is_part sh -> is_part (behead sh).
Proof. case: sh => [//| l0 sh] /=; exact: is_part_consK. Qed.

Lemma is_part_rconsK sh sn : is_part (rcons sh sn) -> is_part sh.
Proof.
case: sn => [/= | sn].
  move/is_partP => []; by rewrite last_rcons.
elim: sh => [//= | s0 sh IHsh].
rewrite rcons_cons /= => /andP [] Hhead /IHsh {IHsh} ->.
rewrite andbT; case: sh Hhead => [//= | s1 sh]; first exact: leq_ltn_trans.
by rewrite rcons_cons.
Qed.

(** TODO : write the reciprocal *)
Lemma is_in_part_le (sh : seq nat) r c j k :
  is_part sh -> is_in_shape sh r c -> j <= r -> k <= c -> is_in_shape sh j k.
Proof.
rewrite /is_in_shape => /is_part_ijP [] _ Hpart Hcr /Hpart Hrj Hkc.
exact: leq_ltn_trans Hkc (leq_trans Hcr Hrj).
Qed.

(** Equality of partitions *)
Lemma part_nth_len_eq p q :
  (forall i, nth 0 p i = nth 0 q i) -> is_part p -> is_part q -> size p = size q.
Proof.
wlog Hwlog: p q / (size p) <= (size q).
  move=> Hwlog Hnth.
  by case: (leqP (size p) (size q)) => [|/ltnW] /Hwlog H/H{H}H/H{H} ->.
move=> Hnth /is_part_ijP [] Hlastp Hp /is_part_ijP [] Hlastq Hq.
apply anti_leq; rewrite Hwlog {Hwlog} /=.
case: q Hnth Hlastq Hq => [//=|q0 q] Hnth Hlastq Hq.
rewrite leqNgt; apply (introN idP) => Habs.
move: Hlastq.
have:= Habs; rewrite -(ltn_predK Habs) ltnS => /(Hq _ _).
by rewrite nth_last /= -Hnth nth_default // leqn0 => /eqP ->.
Qed.

Lemma part_eqP p q :
  is_part p -> is_part q -> reflect (forall i, nth 0 p i = nth 0 q i) (p == q).
Proof.
move=> Hp Hq.
apply (iffP idP) => [/eqP -> //| H].
apply/eqP; apply (eq_from_nth (x0 := 0)).
- exact: part_nth_len_eq.
- move=> i _; exact: H.
Qed.

(** Partitions and sumn *)
Lemma part0 sh : is_part sh -> sumn sh = 0 -> sh = [::].
Proof. move/part_head_non0; by case: sh => //= [] [|s0]. Qed.

Lemma size_part sh : is_part sh -> size sh <= sumn sh.
Proof.
elim: sh => [//= | s0 sh IHsh] /= /andP [] Hhead Hpart.
apply: (leq_ltn_trans (IHsh Hpart)).
rewrite -{1}[sumn sh]add0n ltn_add2r.
have /part_head_non0 /= : is_part (s0 :: sh) by rewrite /= Hhead Hpart.
by rewrite lt0n.
Qed.

Lemma mem_part sh i : is_part sh -> i \in sh -> 0 < i <= sumn sh.
Proof.
elim: sh i => [//= | s0 sh IHsh] i Hpart.
have /= Hs0 := part_head_non0 Hpart.
move: Hpart => /andP [_ Hpart].
rewrite inE => /orP [/eqP -> | /(IHsh _ Hpart)/andP [-> /=]].
- by rewrite leq_addr andbT; case: s0 Hs0.
- by move/leq_trans; apply; apply leq_addl.
Qed.

Lemma part_sumn_rectangle (sh : seq nat) :
  is_part sh -> sumn sh <= (head 0 sh) * (size sh).
Proof.
elim: sh => [//= | s0 s IHs] /= /andP [] Hhead /IHs {IHs} Hsum.
rewrite mulnS leq_add2l.
apply (leq_trans Hsum).
rewrite {Hsum} leq_mul2r.
by case: s Hhead => [//= | s1 s].
Qed.


(** Removing trailing zeroes *)
Fixpoint rem_trail0 s :=
  if s is s0 :: s' then
    if (rem_trail0 s') is t1 :: t' then s0 :: t1 :: t'
    else if s0 == 0 then [::] else [:: s0]
  else [::].

Lemma size_rem_trail0 s : size (rem_trail0 s) <= size s.
Proof.
elim: s => [//= | s0 s]/=.
case: (rem_trail0 s) => [/= _ | //=].
by case: eqP.
Qed.

Lemma nth_rem_trail0 s i : nth 0 (rem_trail0 s) i = nth 0 s i.
Proof.
elim: s i => [//= | s0 s]/=.
case: (rem_trail0 s) => [/= | t1 t'] IHs i.
- case (altP (s0 =P 0)) => [-> |_].
  + by case: i => [//= | i]; first by rewrite /= -IHs.
  + by case: i => [//= | i] /=; apply: IHs.
- by case: i => [//= | i] /=; apply: IHs.
Qed.

Lemma sumn_rem_trail0 s : sumn (rem_trail0 s) = sumn s.
Proof.
elim: s => [//= | s0 s] /=.
case: (rem_trail0 s) => [/= <- | t1 t' <- //=].
by case: (altP (s0 =P 0%N)) => [-> | _] /=; rewrite ?addn0.
Qed.

Lemma is_part_rem_trail0 s : sorted geq s -> is_part (rem_trail0 s).
Proof.
case: s => [//= | s0 s]; rewrite [sorted _ _]/=.
elim: s s0 => [| s1 s IHs] s0 /=; first by case: s0.
move=> /andP [] H01 /IHs /=.
case: (rem_trail0 s) => [_ | t0 t] /=; last by rewrite H01.
case: (altP (s1 =P 0)) => [_ | Hs1].
- case (altP (s0 =P 0)) => [// | Hs0] /=.
  by rewrite lt0n Hs0.
- by rewrite /= H01 lt0n Hs1.
Qed.


(** ** Corners, adding and removing corners *)
Definition is_rem_corner sh i := nth 0 sh i > nth 0 sh i.+1.
Definition is_add_corner sh i := (i == 0) || (nth 0 sh i < nth 0 sh i.-1).

Lemma last_incr_nth_non0 sh i : last 1 sh != 0 -> last 1 (incr_nth sh i) != 0.
Proof.
rewrite -!nth_last size_incr_nth.
case (ltnP i (size sh)) => Hi.
- have Hsz : (size sh).-1 < size sh by move: Hi; case: (size sh).
  rewrite (set_nth_default 0 1 (s := incr_nth _ _));
    last by rewrite size_incr_nth Hi Hsz.
  rewrite nth_incr_nth; apply contra.
  rewrite addn_eq0 => /andP [] _ H.
  by rewrite (set_nth_default 0 1).
- move=> _; rewrite /= (set_nth_default 0 1).
  + by rewrite nth_incr_nth eq_refl.
  + by rewrite size_incr_nth [i < size sh]ltnNge Hi /=.
Qed.

Lemma is_part_incr_nth_size sh l :
  is_part sh -> is_part (incr_nth sh l) -> l <= size sh.
Proof.
elim: sh l => [//= | sh0 sh IHsh] /= l.
  move => _.
  case: l => [| i] //= /andP []; by rewrite leqn0 => /part_head0F ->.
case: l => [//= | l].
by rewrite ltnS /= => /andP [] _ /IHsh H /andP [] _ /H.
Qed.

Lemma is_part_incr_nth sh i :
  is_part sh -> is_add_corner sh i -> is_part (incr_nth sh i).
Proof.
rewrite /is_add_corner; move=> /is_partP [] Hhead Hpart.
case (altP (i =P 0)) => [-> _ {i} | Hi /= H]; apply/is_partP.
- case: sh Hhead Hpart => [//= _ _ | s0 sh /=]; first by split => //= [] [].
  move=> Hlast Hi; split; first by move: Hlast; case sh.
  case=> [| i]; first by apply: (leq_trans (Hi 0)) => //=.
  by move/(_ i.+1) : Hi.
- case: i Hi H => [//= | i] _; split; first exact: last_incr_nth_non0.
  move: H => /= H j.
  case: sh Hhead Hpart H => [//= | s0 sh] /= Hlast Hpart Hcorn.
  + by exfalso; move: Hcorn; rewrite nth_nil.
  + rewrite !nth_incr_nth; case (altP (i =P j)) => Hi /=.
    * rewrite add1n; subst i.
      apply (leq_trans Hcorn).
      elim: j s0 sh {Hcorn Hlast Hpart} => [//= | j IHj] s0 sh /=.
      case sh => [//= | s1 sh']; first by rewrite nth_nil.
      exact: IHj.
    * rewrite add0n.
      case: j Hi => [//= | j] Hj /=; first exact (Hpart 0).
      rewrite nth_incr_nth; case (altP (i =P j)) => Hi.
      case: sh Hpart {Hlast Hcorn} => [//= | s1 sh] /= Hpart.
        exact: (leq_trans (Hpart j.+1)).
      rewrite add0n.
      case: sh Hpart {Hlast Hcorn} => [//= | s1 sh] /= Hpart.
      exact: (Hpart j.+1).
Qed.

(* unused lemma *)
Lemma del_rem_corner sh i :
  last 1 sh != 0 -> is_part (incr_nth sh i) ->
  is_rem_corner (incr_nth sh i) i = is_part sh.
Proof.
move=> Hn0 /is_partP [] _ Hpart1.
rewrite/is_rem_corner; apply/idP/idP.
- move=> Hcorn; apply/is_partP; split; first exact Hn0.
  move=> j; move: Hcorn (Hpart1 j).
  rewrite !nth_incr_nth (@ltn_eqF i i.+1) // eq_refl add0n add1n ltnS => Hcorn.
  case (eqP (y:=j)) => [<- //=|_].
  by case eqP => [Hi |_]; rewrite !add0n // add1n; apply: ltnW.
- move=> /is_partP => [] [] _ /(_ i).
  by rewrite !nth_incr_nth (@ltn_eqF i i.+1) // eq_refl add0n add1n ltnS.
Qed.

Lemma rem_corner_incr_nth sh i :
  is_part sh -> is_add_corner sh i -> is_rem_corner (incr_nth sh i) i.
Proof.
rewrite /is_add_corner /is_rem_corner /= nth_incr_nth eq_refl add1n.
case: i => [/= | i].
  case: sh => [// | s0 [// | s1 s]] /= /andP [].
  by rewrite ltnS.
move=> Hpart /orP [] //; rewrite [i.+1.-1]/=.
elim: sh i Hpart => [| s0 sh IHsh] i /=; first by rewrite !nth_nil.
move=> /andP [] Hhead Hpart.
case: i => [_|i].
  move: Hhead; case: sh Hpart {IHsh} => [//= | s1 [//= | s2 sh]] /= /andP [].
  by rewrite ltnS.
by move=> /(IHsh i Hpart).
Qed.

Lemma is_rem_cornerP sh i : is_part sh ->
  (i < size sh) && (~~ is_in_shape sh i.+1 (nth 0 sh i).-1) =
  (is_rem_corner sh i).
Proof.
rewrite /is_rem_corner /is_in_shape -ltnNge => Hpart.
apply/idP/idP.
- move=> /andP [] /(nth_part_non0 Hpart).
  by case: (nth 0 sh i).
- case: (ltnP i (size sh)) => Hi; last by rewrite [nth 0 sh i]nth_default.
  have:= nth_part_non0 Hpart Hi.
  by case: (nth 0 sh i) => pi //= _ ->.
Qed.

Lemma minn0 k : minn k 0 = 0.
Proof. by rewrite /minn ltn0. Qed.
Lemma minSS i j : minn i.+1 j.+1 = (minn i j).+1.
Proof. by rewrite /minn ltnS; case ltnP. Qed.

Fixpoint decr_nth v i {struct i} :=
  if v is n :: v' then
    if i is i'.+1 then n :: decr_nth v' i'
    else if n is n'.+1 then
           if n' is _.+1 then
             n' :: v'
           else [::]
         else [::]
  else [::].

Lemma incr_nthK sh i :
  is_part sh -> is_part (incr_nth sh i) -> decr_nth (incr_nth sh i) i = sh.
Proof.
elim: sh i => [| s0 sh IHsh] [| i] //=.
- by move=> _ /andP []; rewrite leqn0 => /part_head0F ->.
- by case: s0 => //= /andP []; rewrite leqn0 => /part_head0F ->.
- move=> /andP [] Head Hpart /andP [] Headincr Hpartincr.
  by rewrite IHsh.
Qed.

Lemma decr_nthK sh i :
  is_part sh -> is_rem_corner sh i -> incr_nth (decr_nth sh i) i = sh.
Proof.
rewrite /is_rem_corner.
elim: sh i => [| s0 sh IHsh] /=; first by case.
case=> [| i] /=; case: s0 => [| s0] //= /andP [].
  - move=> {IHsh} Hs0 /part_head_non0 Hhead H ; case: s0 Hs0 H Hhead => //= _.
    by case: sh => //= s1 sh; rewrite ltnS leqn0 => /eqP ->.
  - by rewrite leqn0 => /part_head0F ->.
by move=> Hhead Hpart Hnth; rewrite IHsh.
Qed.

Lemma sumn_incr_nth s i : sumn (incr_nth s i) = (sumn s).+1.
Proof.
elim: i s => [/= | i IHi]; first by case=> [| s0 s].
case=> [/= | s0 s /=]; first by rewrite /sumn add0n; elim i.
by rewrite (IHi s) addnS.
Qed.

Lemma nth_decr_nth sh i :
  nth 0 (decr_nth sh i) i = (nth 0 sh i).-1.
Proof. by elim: i sh => [| i IHi] [| [|[|s0]] sh] /=. Qed.

Lemma nth_decr_nth_neq sh i j :
  is_part sh -> is_rem_corner sh i -> i != j -> nth 0 (decr_nth sh i) j = nth 0 sh j.
Proof.
move=> Hpart Hcrn /negbTE Hij.
rewrite -{2}(decr_nthK Hpart Hcrn).
by rewrite nth_incr_nth Hij add0n.
Qed.

Lemma sumn_decr_nth sh i :
  is_part sh -> is_rem_corner sh i -> (sumn (decr_nth sh i)) = (sumn sh).-1.
Proof.
move=> Hpart Hcorn. rewrite -{2}[sh](decr_nthK Hpart Hcorn).
by rewrite sumn_incr_nth /=.
Qed.

Lemma is_part_decr_nth sh i :
  is_part sh -> is_rem_corner sh i -> is_part (decr_nth sh i).
Proof.
rewrite /is_rem_corner.
elim: sh i => [| s0 sh IHsh] /=; first by case.
case=> [| i] /=.
  case: s0 => [| [| s0]] //= /andP [] _ ->.
  by case sh => //= s1 _; rewrite ltnS => ->.
move=> /andP [] Hhead Hpart Hnth.
apply/andP; split; last exact: IHsh.
apply: (@leq_trans (head 1 sh)); last exact Hhead.
case: sh {IHsh Hhead Hnth s0} Hpart => [//= | s1 s]; first by case i.
case i => //= /andP [].
case: s1 => [| [| s1]] //=.
by rewrite leqn0 => /part_head0F ->.
Qed.

Lemma add_corner_decr_nth sh i :
  is_part sh -> is_rem_corner sh i -> is_add_corner (decr_nth sh i) i.
Proof.
move=> Hpart Hout; rewrite /is_add_corner /=.
case: i Hout => [//=|i] Hout; rewrite [i.+1.-1]/=.
apply/orP; right.
rewrite nth_decr_nth nth_decr_nth_neq //; last by rewrite eq_sym ltn_eqF.
move: Hout; rewrite /is_rem_corner => Hi2.
move/is_partP : Hpart => [] _ Hdecr.
apply: leq_trans _ (Hdecr i).
by move: Hi2; case: (nth 0 sh i.+1).
Qed.

Definition rem_corners sh := filter (is_rem_corner sh) (iota 0 (size sh)).

Lemma rem_corners_uniq sh : uniq (rem_corners sh).
Proof. rewrite /rem_corners; apply filter_uniq; exact: iota_uniq. Qed.

(** ** Conjugate of a partition *)

Fixpoint incr_first_n sh n :=
  if sh is s0 :: s then
    if n is n.+1 then s0.+1 :: incr_first_n s n
    else sh
  else nseq n 1.
Fixpoint conj_part sh :=
  if sh is s0 :: sh then incr_first_n (conj_part sh) s0
  else [::].

Lemma is_part_n1 n : is_part (nseq n 1).
Proof. elim: n => [//= | n /= ->]; rewrite andbT; by case n. Qed.

Lemma nth_incr_first_n sh n i :
  nth 0 (incr_first_n sh n) i = if i < n then (nth 0 sh i).+1 else nth 0 sh i.
Proof.
elim: sh n i => [| s0 s IHs] n i /=.
  by rewrite nth_nseq nth_default.
case: n i => [| n] //= [| i] //=.
exact: IHs.
Qed.

Lemma incr_first_n_nthC sh i j :
  incr_first_n (incr_nth sh i) j = incr_nth (incr_first_n sh j) i.
Proof.
elim: sh i j => [| s0 sh IHsh].
  elim=> [| i IHi] [|j] //=.
  move/(_ j) : IHi => /= <-; by case: i.
case=> [| i] [| j] //=.
by rewrite IHsh.
Qed.

Lemma is_part_incr_first_n sh n :
  is_part sh -> is_part (incr_first_n sh n).
Proof.
elim: sh n => [//= n _| s0 sh IHsh] /=; first exact: is_part_n1.
case=> [//= | n] /andP [] Hhead /IHsh {IHsh} /= ->; rewrite andbT.
case: sh Hhead => [_ | s1 sh] /=; first by case n.
case: n => [| n] /=; last by apply.
by move/leq_trans; apply.
Qed.

Lemma is_part_conj sh : is_part sh -> is_part (conj_part sh).
Proof.
elim: sh => [//= | s0 sh IHsh] /= /andP [] _ /IHsh {IHsh}.
exact: is_part_incr_first_n.
Qed.

Lemma conj_nseq n : 0 < n -> conj_part (nseq n 1) = [:: n].
Proof.
elim: n => [//= | n IHn] /= _.
case: n IHn => [//= | n] IHn.
by rewrite (IHn (ltn0Sn n)).
Qed.

Lemma size_incr_first_n sh n :
  size sh <= n -> size (incr_first_n sh n) = n.
Proof.
elim: sh n => [| s0 sh IHsh] /= n; first by rewrite size_nseq.
case: n => [//= | n]; by rewrite /= ltnS => /IHsh ->.
Qed.

Lemma size_conj_part sh : is_part sh -> size (conj_part sh) = head 0 sh.
Proof.
elim: sh => [//= | s0 [| s1 sh] IHsh] /= /andP [] Hhead /IHsh {IHsh} /= IHsh.
- by rewrite size_nseq.
- move: Hhead; by rewrite -{1}IHsh => /size_incr_first_n.
Qed.

Lemma sumn_incr_first_n sh n : sumn (incr_first_n sh n) = sumn sh + n.
Proof.
elim: n sh => [//= | n IHn]; first by case.
case => [/= | s0 s /=].
- have -> : sumn (nseq n 1) = n.
    elim: n {IHn} => //= n ->; by rewrite add1n.
  by rewrite add0n add1n.
- by rewrite IHn addnA addnS !addSn.
Qed.

Lemma sumn_conj_part sh : sumn (conj_part sh) = sumn sh.
Proof. elim: sh => [//= | s0 s IHs] /=; by rewrite sumn_incr_first_n IHs addnC. Qed.

Lemma conj_part_ind sh l :
  sh != [::] -> is_part sh -> l >= size sh ->
  conj_part (incr_first_n sh l) = l :: conj_part sh.
Proof.
elim: sh l => [//= | s0 s IHs l] _ /=.
move=> /andP [] _ Hpart Hs0.
case: l Hs0 => [//= | l] /=; rewrite ltnS => Hs0.
case: s IHs Hpart Hs0 => [//= _ _| s1 s IHs].
- case: l => [//=| l ]; by rewrite conj_nseq; last exact: ltn0Sn.
- have Hneq : s1 :: s != [::] by [].
  move=> Hpart Hsize /=.
  move/(_ l Hneq Hpart Hsize) : IHs.
  by case: l Hsize => [//= | l /=] _ ->.
Qed.

Lemma conj_partK sh : is_part sh -> conj_part (conj_part sh) = sh.
Proof.
elim: sh => [//=| s0 sh IHsh] /= /andP [] Hhead Hpart.
case (altP (sh =P [::])) => Hsh.
- move: Hhead; rewrite Hsh /=; exact: conj_nseq.
- rewrite conj_part_ind //=; first by rewrite IHsh.
  + move: Hsh; apply: contra => /eqP.
    case: sh Hpart {IHsh Hhead} => [//= | s1 s] /=.
    case: s1 => [/andP []| s1 _]; first by rewrite leqn0 => /part_head0F ->.
    by case: (conj_part s).
  + exact: is_part_conj.
  + rewrite size_conj_part //=.
    by move: Hhead Hsh; case sh.
Qed.

Lemma conj_part_incr_nth sh i :
  is_part sh -> is_add_corner sh i ->
  conj_part (incr_nth sh i) = incr_nth (conj_part sh) (nth 0 sh i).
Proof.
elim: sh i => [| s0 sh IHsh] i /=.
  by rewrite /is_add_corner /= !nth_nil => _ /orP [] // /eqP ->.
move=> /= /andP [] H0 Hpart.
case: i => [_ | i Hcrn]/=.
  have Hszconj: (size (conj_part sh) <= s0)%N.
    rewrite (size_conj_part Hpart).
    move: H0; case sh => [| n _] //=; exact: ltnW.
  have Hszn : size (incr_first_n (conj_part sh) s0.+1) = s0.+1.
    by rewrite size_incr_first_n; last exact: (leq_trans Hszconj).
  apply (eq_from_nth (x0 := 0)).
  - rewrite Hszn.
    by rewrite size_incr_nth ltnNge (size_incr_first_n Hszconj) leqnn /=.
  - move=> i; rewrite Hszn => Hi.
    rewrite nth_incr_nth !nth_incr_first_n Hi ltn_neqAle.
    move: Hi; rewrite ltnS eq_sym => ->.
    by case: eqP => /= _; rewrite ?add0n ?add1n.
rewrite (IHsh _ Hpart); first exact: incr_first_n_nthC.
by move: Hcrn => /=; case: i.
Qed.

Lemma is_in_conj_part_impl sh:
  is_part sh -> forall r c , is_in_shape sh r c -> is_in_shape (conj_part sh) c r.
Proof.
rewrite /is_in_shape.
elim: sh => [| s0 s IHs] Hpart r c.
  by rewrite /is_rem_corner nth_default // nth_default //.
have:= Hpart => /= /andP [] Hhead Hparts.
rewrite nth_incr_first_n.
case: r => [ -> // | r] /= H.
move/is_part_ijP : Hpart => [] _ /(_ _ _ (leq0n r.+1))/=.
move=> /(leq_trans H) ->.
by rewrite ltnS; exact:  IHs.
Qed.

Lemma is_in_conj_part sh :
  is_part sh -> forall r c, is_in_shape sh r c = is_in_shape (conj_part sh) c r.
Proof.
move=> Hpart r c; apply/idP/idP; first exact: is_in_conj_part_impl.
rewrite -{2}(conj_partK Hpart).
by apply is_in_conj_part_impl; exact: is_part_conj.
Qed.

(* A rephrasing of the preceding lemma *)
Lemma conj_ltnE sh :
  is_part sh -> forall i j, nth 0 sh i > j = (nth 0 (conj_part sh) j > i).
Proof.
move=> Hpart.
rewrite -/(is_in_shape sh _ _) -/(is_in_shape (conj_part sh) _ _).
exact: is_in_conj_part.
Qed.

Lemma conj_leqE sh :
  is_part sh -> forall i j, (nth 0 sh i <= j) = (nth 0 (conj_part sh) j <= i).
Proof. by move=> Hpart i j; rewrite leqNgt [RHS]leqNgt (conj_ltnE Hpart). Qed.

Lemma nth_conjE sh r c :
  is_part sh -> c != 0 ->
  (nth 0 (conj_part sh) r == c) = (nth 0 sh c <= r < nth 0 sh c.-1).
Proof.
move=> Hpart.
case: c => [//= | c _].
rewrite (conj_leqE Hpart) (conj_ltnE Hpart) /=.
apply/idP/idP.
- move/eqP ->; by rewrite !leqnn.
- move=> H; apply/eqP; exact: anti_leq.
Qed.

Lemma rem_corner_incr_first_n sh i :
  is_part sh -> is_rem_corner (incr_first_n sh i.+1) i.
Proof.
rewrite /is_rem_corner.
elim: sh i => [/= i _ | s0 sh IHsh i]; first by elim: i.
move=> /= => /andP [] Hhead /IHsh{IHsh} Hrec.
case: i => [| i] /=; first by case: sh Hhead {Hrec}.
exact: (Hrec i).
Qed.

Lemma rem_corner_incr_first_nE sh n i :
  is_part sh -> is_rem_corner sh i -> is_rem_corner (incr_first_n sh n) i.
Proof.
rewrite /is_rem_corner.
elim: sh i n => [/= i n _ | s0 sh IHsh i n]; first by elim: i.
rewrite [is_part _]/= => /andP [] Hhead Hpart.
case: i => [/= | i].
  case: sh IHsh Hhead Hpart => [//= | s1 sh] IHsh Hhead Hpart H10.
    case: n {IHsh Hhead Hpart} => [//= | n].
    rewrite /nseq; case: n => [//= | n] /=.
    by rewrite ltnS.
  case: n {IHsh Hhead Hpart} => [| [| n]] //=.
  exact: (leq_trans H10).
rewrite [X in (X -> _)]/= => Hcorn.
case: n => [//= | n].
exact: (IHsh _ n Hpart Hcorn).
Qed.

Lemma is_add_corner_conj_part sh r :
  is_part sh -> is_add_corner sh r -> is_add_corner (conj_part sh) (nth 0 sh r).
Proof.
case: (altP ( r =P 0)) => Hr; rewrite /is_add_corner /= => Hpart /orP [].
- move=> /eqP ->.
  case: sh Hpart (part_head_non0 Hpart) => [//= | s0 sh] /= /andP [] Hs0 Hpart Hs0n0.
  apply/orP; right.
  rewrite !nth_incr_first_n ltnn.
  have -> : s0.-1 < s0 by move: Hs0n0; case s0.
  rewrite ltnS {Hs0}.
  case: s0 Hs0n0 => [//= | s0] _.
  by move/is_part_conj/is_partP: Hpart => [] _; apply.
- by rewrite Hr ltnn.
- by rewrite (negbTE Hr).
- move=> Hnthr.
  case: eqP => //= /eqP H.
  have : nth 0 sh r <= nth 0 sh r < nth 0 sh r.-1 by rewrite leqnn Hnthr.
  rewrite -(nth_conjE _ Hpart Hr) => /eqP.
  rewrite -(conj_ltnE Hpart) => ->.
  by move: H; case: (nth 0 sh r).
Qed.

Lemma rem_corner_conj_part sh i :
  is_part sh -> is_rem_corner sh i -> is_rem_corner (conj_part sh) (nth 0 sh i).-1.
Proof.
elim: sh i => [| s0 sh IHsh] i /=.
  by rewrite /is_rem_corner nth_default // nth_default //.
move=> /andP [] H0 Hpart.
case: i => [//= | i] /= H.
  case: s0 H0 H => [//= | s0]/= _ H.
  apply rem_corner_incr_first_n.
  exact: is_part_conj.
apply rem_corner_incr_first_nE; first exact: is_part_conj.
exact: (IHsh _ Hpart).
Qed.

(** ** Partial sum of partitions *)

Lemma sumn_take_leq s k1 k2 :
  k1 <= k2 -> sumn (take k1 s) <= sumn (take k2 s).
Proof.
rewrite !sumn_take; move=> H.
by rewrite (big_cat_nat _ _ _ _ H) //=; apply leq_addr.
Qed.

Lemma sum_conj sh k : \sum_(l <- sh) minn l k = sumn (take k (conj_part sh)).
Proof.
elim: sh => [//= | s0 sh]; first by rewrite big_nil.
rewrite big_cons /= => ->; move: (conj_part sh) => c.
elim: c s0 k => [//= | c0 c IHc] s0 k /=.
- rewrite /= addn0.
  elim: s0 k => [| s IHs] k //=; first by rewrite min0n.
  case: k => [| k] /=; first by rewrite minn0.
  by rewrite minSS IHs add1n.
- case: s0 => [| s0]; first by rewrite min0n add0n.
  case: k => [| k] //=.
  by rewrite -IHc !addnA minSS addSnnS [minn _ _ + _]addnC.
Qed.

Lemma sumn_take_inj s t :
  is_part s -> is_part t ->
  (forall k, sumn (take k s) = sumn (take k t)) -> s = t.
Proof.
elim: s t => [//= t _ | s0 s IHs t].
- move/part_head_non0; case: t => [//= | t0 t] /= Ht0 IHs.
  exfalso; move/(_ 1) : IHs; rewrite take0 /= addn0 => H.
  by rewrite H eq_refl in Ht0.
- case: t s IHs => [s _ Hs _ /(_ 1) | t0 t] /=.
  + rewrite take0 /= addn0 => Hs0.
    by exfalso; move/part_head_non0 : Hs; rewrite Hs0.
  + move=> s IHs /is_part_consK Hps /is_part_consK Hpt /= Heq.
    have:= Heq 1; rewrite !take0 /= !addn0 => Ht0; subst t0.
    congr (s0 :: _); apply: (IHs _ Hps Hpt).
    move=> k; move/(_ k.+1) : Heq.
    by move=> /= /eqP; rewrite eqn_add2l => /eqP.
Qed.

(** * Inclusion of Partitions and Skew Partitions *)

Fixpoint included inner outer :=
  if inner is inn0 :: inn then
    if outer is out0 :: out then
      (inn0 <= out0) && (included inn out)
    else false
  else true.

Lemma includedP inner outer :
  reflect (size inner <= size outer /\ forall i, nth 0 inner i <= nth 0 outer i)
          (included inner outer).
Proof.
apply (iffP idP).
- elim: inner outer => [//= | inn0 inn IHinn] /=.
    move=> outer _; by split; last by move=> i; rewrite nth_nil.
  case=> [//= | out0 out] /= /andP [] H0 /IHinn{IHinn} [] Hsize H.
  split; first by rewrite ltnS.
  by case.
- elim: inner outer => [//= | inn0 inn IHinn] /=.
  case=> [ [] //= | out0 out] [] /=.
  rewrite ltnS => Hsize H.
  apply/andP; split; first exact: (H 0).
  apply: IHinn; split; first exact: Hsize.
  move=> i; exact: (H i.+1).
Qed.

Lemma included_behead p1 p2 :
  included p1 p2 -> included (behead p1) (behead p2).
Proof.
case: p1 => [//=|a l].
  by case: p2 => [//=|b s] /= /andP [].
Qed.

Lemma included_refl sh : included sh sh.
Proof. elim: sh => [//= | s0 sh /= -> ]; by rewrite leqnn. Qed.

Lemma included_trans sha shb shc :
  included sha shb -> included shb shc -> included sha shc.
Proof.
move=> /includedP [] Hsza Hincla /includedP [] Hszb Hinclb.
apply/includedP; split; first exact (leq_trans Hsza Hszb).
move=> i; exact: (leq_trans (Hincla i) (Hinclb i)).
Qed.

Lemma included_incr_nth sh i :
  included sh (incr_nth sh i).
Proof.
apply/includedP; split.
- rewrite size_incr_nth; case ltnP => Hi //=.
  exact: (leq_trans Hi).
- move=> j; rewrite nth_incr_nth.
  exact: leq_addl.
Qed.

Lemma included_decr_nth u i : included (decr_nth u i) u.
Proof.
elim: u i => [| u0 u IHu] [| i] //=.
  case: u0 => [| [| u0]] //=.
  by rewrite ltnS (leqnSn u0) (included_refl u).
by rewrite (leqnn u0) (IHu i).
Qed.

Lemma included_incr_nth_inner inner outer i :
  nth 0 inner i < nth 0 outer i ->
  included inner outer -> included (incr_nth inner i) outer.
Proof.
move=> Hnth /includedP [] Hsize Hincl.
apply/includedP; split.
- rewrite size_incr_nth; case ltnP => _; first exact Hsize.
  rewrite ltnNge; apply (introN idP) => Hout.
  move: Hnth; by rewrite (nth_default _ Hout).
- move=> j; rewrite nth_incr_nth.
  by case eqP => [<- | _]; rewrite ?add1n ?add0n.
Qed.

Lemma size_included inner outer :
  included inner outer -> size inner <= size outer.
Proof.
elim: inner outer => [//= | inn0 inn IHinn] /=.
case=> [//= | outer0 outer] /= /andP [] _ /IHinn.
by rewrite ltnS.
Qed.

Lemma sumn_included inner outer :
  included inner outer -> sumn inner <= sumn outer.
Proof.
elim: inner outer => [//= | inn0 inn IHinn] /=.
case=> [//= | outer0 outer] /= /andP [] H0 /IHinn.
exact: leq_add.
Qed.

Lemma included_sumnE inner outer :
  is_part outer ->
  included inner outer ->
  sumn inner = sumn outer ->
  inner = outer.
Proof.
elim: inner outer => [| inn0 inn IHinn] /=.
  by move=> outer Houter _ /esym/(part0 Houter) ->.
case=> [//= | outer0 out] /= /andP [] _ /IHinn{IHinn}Hrec /andP [] H0 Hincl Heq.
by have:= leq_addE H0 (sumn_included Hincl) Heq => [] [] -> /(Hrec Hincl) ->.
Qed.

Lemma included_conj_part inner outer :
  is_part inner -> is_part outer ->
  included inner outer -> included (conj_part inner) (conj_part outer).
Proof.
move=> Hinn Hout /includedP [] Hsz Hincl.
apply/includedP; split; first by rewrite !size_conj_part // -!nth0; exact: Hincl.
move=> i.
rewrite -conj_leqE //; apply (leq_trans (Hincl _)); by rewrite conj_leqE.
Qed.

Lemma included_conj_partE inner outer :
  is_part inner -> is_part outer ->
  included inner outer = included (conj_part inner) (conj_part outer).
Proof.
move=> Hinn Hout; apply/idP/idP; first exact: included_conj_part.
rewrite -{2}(conj_partK Hinn) -{2}(conj_partK Hout).
apply: included_conj_part; exact: is_part_conj.
Qed.

Fixpoint diff_shape inner outer :=
  if inner is inn0 :: inn then
    if outer is out0 :: out then
      out0 - inn0 :: diff_shape inn out
    else [::] (* Unused case *)
  else outer.

Definition pad (T : Type) (x : T) sz := [fun s => s ++ nseq (sz - size s) x].

Lemma nth_pad (T : Type) n (p : T) (s : seq T) i :
  nth p (pad p n s) i = nth p s i.
Proof.
rewrite /pad /= nth_cat.
case: (ltnP i (size s)) => //= /(nth_default p) ->.
by rewrite nth_nseq if_same.
Qed.

Lemma head_pad (T : Type) n (p : T) (s : seq T) : head p (pad p n s) = head p s.
Proof. elim: s => [| s0 s IHs] //=; rewrite subn0; by case: n. Qed.

Definition outer_shape inner size_seq :=
  [seq p.1 + p.2 | p <- zip (pad 0 (size (size_seq)) inner) size_seq].

Lemma size_diff_shape inner outer : size (diff_shape inner outer) = size outer.
Proof.
elim: inner outer => [//= | inn0 inn IHinn] /= [//= | out0 out] /=.
by rewrite IHinn.
Qed.

Lemma nth_diff_shape inn out i :
  nth 0 (diff_shape inn out) i = nth 0 out i - nth 0 inn i.
Proof.
elim: inn out i => [| inn0 inn IHinn] out i //=.
  by rewrite (@nth_default _ _ [::]) // subn0.
case: out => [| out0 out] /=.
  by rewrite nth_default.
by case: i => [| i] //=.
Qed.

Lemma sumn_diff_shape inner outer :
  included inner outer -> sumn (diff_shape inner outer) = sumn outer - sumn inner.
Proof.
elim: inner outer => [//= | inn0 inn IHinn] /= [//= | out0 out] /=.
  by rewrite subn0.
move/andP => [] Hleq Hincl.
rewrite (IHinn _ Hincl) {IHinn}.
have Hsumn : sumn inn <= sumn out.
  elim: inn out Hincl => [//= | inn1 inn IHinn] /= [//= | out1 out] /=.
  move/andP => [] H1 /IHinn; exact: leq_add.
by rewrite subnDA (addnBA _ Hsumn) addnC (addnBA _ Hleq) [out0 + _]addnC.
Qed.

Lemma diff_shape_pad0 inner outer :
  diff_shape ((pad 0 (size outer)) inner) outer = diff_shape inner outer.
Proof.
elim: inner outer => [//= | inn0 inn IHinn] //=.
  elim=> [//= | out0 out] /=; by rewrite !subn0 => ->.
case=> [//= | out0 out] /=.
by rewrite subSS IHinn.
Qed.

Lemma diff_shapeK inner outer :
  included inner outer ->
  outer_shape inner (diff_shape inner outer) = outer.
Proof.
rewrite /outer_shape.
elim: inner outer => [//= | inn0 inn IHinn] /= outer.
  rewrite subn0 => _; elim: outer => [//= | out0 out /= ->].
  by rewrite add0n.
case: outer => [//= | out0 out] /= /andP [] Hin /IHinn{IHinn} ->.
by rewrite addnC subnK.
Qed.

Lemma outer_shapeK inner diff :
  size inner <= size diff ->
  diff_shape inner (outer_shape inner diff) = diff.
Proof.
rewrite /outer_shape.
elim: inner diff => [//= | inn0 inn IHinn] /= diff.
  rewrite subn0 => _; elim: diff => [//= | d0 diff /= ->].
  by rewrite add0n.
case: diff => [//=| t0 t] /=; rewrite ltnS subSS => /IHinn /= ->.
by rewrite addKn.
Qed.


Lemma outer_shape_pad0 inner sz :
  outer_shape (pad 0 (size sz) inner) sz = outer_shape inner sz.
Proof.
rewrite /outer_shape; congr map; congr zip.
rewrite /= size_cat size_nseq.
set n := (X in (_++ _) ++ nseq X _).
suff -> : n = 0 by rewrite /= cats0.
rewrite /n{n}.
move: (size sz) (size inner) => a b.
case: (ltnP a b) => [/ltnW | ] H.
- move: H; rewrite /leq => /eqP H; by rewrite H addn0 H.
- by rewrite (subnKC H) subnn.
Qed.

Lemma included_pad0 inner outer :
  included inner outer = included (pad 0 (size outer) inner) outer.
Proof.
elim: inner outer => [//= | inn0 inn IHinn] /= outer /=.
 rewrite subn0; by elim: outer.
case: outer => [//= | out0 out] /=.
by rewrite subSS IHinn.
Qed.


(** * Sigma Types for Partitions *)

Structure intpart : Type := IntPart {pval :> seq nat; _ : is_part pval}.
Canonical intpart_subType := Eval hnf in [subType for pval].
Definition intpart_eqMixin := Eval hnf in [eqMixin of intpart by <:].
Canonical intpart_eqType := Eval hnf in EqType intpart intpart_eqMixin.
Definition intpart_choiceMixin := Eval hnf in [choiceMixin of intpart by <:].
Canonical intpart_choiceType := Eval hnf in ChoiceType intpart intpart_choiceMixin.
Definition intpart_countMixin := Eval hnf in [countMixin of intpart by <:].
Canonical intpart_countType := Eval hnf in CountType intpart intpart_countMixin.

Lemma intpartP (p : intpart) : is_part p.
Proof. by case: p. Qed.

Lemma intpart_sorted (p : intpart) : sorted geq p.
Proof. by have:= intpartP p; rewrite is_part_sortedE => /andP []. Qed.

Hint Resolve intpartP intpart_sorted.

Canonical conj_intpart p := IntPart (is_part_conj (intpartP p)).

Lemma conj_intpartK : involutive conj_intpart.
Proof. move=> p; apply: val_inj => /=; by rewrite conj_partK. Qed.

Lemma intpart_sumn_take_inj (s t : intpart) :
  (forall k, sumn (take k s) = sumn (take k t)) -> s = t.
Proof.
move=> H; apply: val_inj => /=.
by apply: sumn_take_inj; last exact H.
Qed.


Fixpoint enum_partnsk sm sz mx : (seq (seq nat)) :=
  if sz is sz.+1 then
    flatten [seq [seq i :: p | p <- enum_partnsk (sm - i) sz i] |
             i <- iota 1 (minn sm mx)]
  else if sm is sm.+1 then [::] else [:: [::]].

Definition enum_partns sm sz := enum_partnsk sm sz sm.
Definition enum_partn sm := flatten [seq enum_partns sm sz | sz <- iota 0 sm.+1 ].

Definition is_part_of_n   sm :=
  [pred p | (sumn p == sm)   & is_part p ].
Definition is_part_of_ns  sm sz :=
  [pred p | (size p == sz)   & is_part_of_n sm p].
Definition is_part_of_nsk sm sz mx :=
  [pred p | (head 1 p <= mx) & is_part_of_ns sm sz p].

Lemma enum_partnsk_allP sm sz mx :
  mx >= 1 -> all (is_part_of_nsk sm sz mx) (enum_partnsk sm sz mx).
Proof.
move=> Hmx; apply/allP => /=.
elim: sz sm mx Hmx => [/= [] //= | sz IHsz sm] /= mx Hmx p.
  rewrite mem_seq1 => /eqP -> /=; by rewrite Hmx.
move/flatten_mapP => [] i.
rewrite mem_iota ltnS => /andP [] Hposi Himin /mapP [] recp.
move/(IHsz _ _ Hposi)/and4P => [] Hp Hsum Hsz Hhead -> /= {IHsz}.
rewrite Hp (eqP Hsum) (eqP Hsz) Hhead {Hp Hsum Hsz Hhead} /=.
move: Himin; rewrite leq_min => /andP [] /subnKC -> ->.
by rewrite !eq_refl.
Qed.

Lemma enum_partnsk_countE sm sz mx :
  mx >= 1 ->
  forall p, is_part_of_nsk sm sz mx p -> count_mem p (enum_partnsk sm sz mx) = 1.
Proof.
elim: sz sm mx => [//= | sz IHsz] /= sm mx Hmx.
  by move=> p /and4P [] Hhead/nilP -> /= /eqP <-.
case=> [| p0 p] //=; first by rewrite andbF.
move=> /and5P [] Hp0; rewrite eqSS=> /eqP Hsz /eqP Hsm Hhead Hpart.
rewrite count_flatten -map_comp (eq_map (f2 := fun i => i == p0 : nat)); first last.
  move=> i /=; rewrite count_map /=.
  case (altP (i =P p0)) => [Heq | /negbTE Hneq].
  - subst p0; rewrite (eq_count (a2 := xpred1 p)); first last.
      move=> s; by rewrite /= -eqseqE /= eq_refl /=.
    rewrite {}IHsz //=.
    + have /part_head_non0 /= : is_part (i :: p) by rewrite /= Hhead Hpart.
      by rewrite lt0n.
    + by rewrite Hhead Hsz -Hsm addKn !eq_refl Hpart.
  - rewrite (eq_count (a2 := pred0)); first by rewrite count_pred0.
    move=> s; by rewrite /= -eqseqE /= Hneq.
rewrite sumn_iota //= add1n ltnS leq_min Hp0 -Hsm leq_addr !andbT.
have /part_head_non0 /= : is_part (p0 :: p) by rewrite /= Hhead Hpart.
by rewrite lt0n.
Qed.

Lemma enum_partnskE sm sz mx :
  mx >= 1 ->
  forall p, count_mem p (enum_partnsk sm sz mx) = is_part_of_nsk sm sz mx p.
Proof.
move=> Hx p. case (boolP ((is_part_of_nsk sm sz mx) p)) => H /=.
- by rewrite enum_partnsk_countE.
- apply/count_memPn; move: H; apply: contra.
  exact: (allP (enum_partnsk_allP _ _ Hx)).
Qed.

Lemma enum_partns_allP sm sz : all (is_part_of_ns sm sz) (enum_partns sm sz).
Proof.
apply/allP; rewrite /enum_partns => /= p.
case: sm => [/= | sm]; first by case: sz; rewrite //= mem_seq1 => /eqP ->.
have /enum_partnsk_allP/allP Hall : sm.+1 >= 1 by [].
by move=> /Hall /= /andP [] _.
Qed.

Lemma enum_partns_countE sm sz p :
  is_part_of_ns sm sz p -> count_mem p (enum_partns sm sz) = 1.
Proof.
rewrite /enum_partns.
case: p => /= [ /and3P [] /eqP <- /eqP <- //= | p0 p] /and4P [] Hsz Hsum Hhead Hpart.
rewrite enum_partnsk_countE //=.
- rewrite -(eqP Hsum); apply: (@leq_trans p0); last exact: leq_addr.
  have /part_head_non0 /= : is_part (p0 :: p) by rewrite /= Hhead Hpart.
  by rewrite lt0n.
- by rewrite Hsz Hsum Hhead Hpart -(eqP Hsum) leq_addr.
Qed.

Lemma enum_partnsE sm sz p :
  count_mem p (enum_partns sm sz) = is_part_of_ns sm sz p.
Proof.
case (boolP ((is_part_of_ns sm sz) p)) => H /=.
- by rewrite enum_partns_countE.
- apply/count_memPn; move: H; apply: contra.
  exact: (allP (enum_partns_allP _ _)).
Qed.

Lemma enum_partn_allP sm : all (is_part_of_n sm) (enum_partn sm).
Proof.
apply/allP; rewrite /enum_partn => /= p.
case: sm => [/= | sm]; first by rewrite mem_seq1 => /eqP ->.
rewrite cat0s => /flatten_mapP [] i.
rewrite mem_iota ltnS => /andP [] Hposi Hi.
have /enum_partnsk_allP/allP Hall : sm.+1 >= 1 by [].
by move=> /Hall /= /and3P [].
Qed.

Lemma enum_partn_countE sm p :
  is_part_of_n sm p -> count_mem p (enum_partn sm) = 1.
Proof.
rewrite /enum_partn /= => /andP [] Hsum Hpart.
rewrite count_cat enum_partnsE /= Hsum Hpart !andbT.
case: (altP (size p =P 0)) => Hsize.
- rewrite count_flatten -map_comp.
  set empty := map _ _; have {empty} -> : empty = [seq 0 | i <- iota 1 sm].
    rewrite /empty {empty} -eq_in_map => i /=.
    rewrite mem_iota add1n ltnS => /andP [] /lt0n_neq0 Hi _.
    apply/count_memPn => /=; move: Hi; apply: contra.
    move/(allP (enum_partns_allP _ _)) => /= /andP [] /eqP <- _.
    by rewrite Hsize.
  suff -> : sumn (map (fun=> 0) _) = 0 by rewrite addn0.
  move=> T; by elim => [//= |l0 l /= ->].
- rewrite /= add0n count_flatten -map_comp.
  rewrite (eq_map (f2 := fun i => i == size p : nat)); first last.
    move=> i /=; rewrite enum_partnsE /=.
    by rewrite Hsum Hpart !andbT eq_sym.
  rewrite sumn_iota //= add1n ltnS lt0n Hsize /= -(eqP Hsum).
  exact: size_part.
Qed.

Lemma enum_partnP n p : (is_part_of_n n p) = (p \in enum_partn n).
Proof.
apply/idP/idP; last by move/(allP (enum_partn_allP n)).
rewrite -has_pred1 has_count; by move/enum_partn_countE ->.
Qed.

Section PartOfn.

Variable n : nat.

Structure intpartn : Set :=
  IntPartN {pnval :> seq nat; _ : is_part_of_n n pnval}.
Canonical intpartn_subType := Eval hnf in [subType for pnval].
Definition intpartn_eqMixin := Eval hnf in [eqMixin of intpartn by <:].
Canonical intpartn_eqType := Eval hnf in EqType intpartn intpartn_eqMixin.
Definition intpartn_choiceMixin := Eval hnf in [choiceMixin of intpartn by <:].
Canonical intpartn_choiceType :=
  Eval hnf in ChoiceType intpartn intpartn_choiceMixin.
Definition intpartn_countMixin := Eval hnf in [countMixin of intpartn by <:].
Canonical intpartn_countType :=
  Eval hnf in CountType intpartn intpartn_countMixin.
Canonical intpartn_subCountType := Eval hnf in [subCountType of intpartn].

Let type := sub_finType
              intpartn_subCountType (enum_partn_allP n) (@enum_partn_countE n).
Canonical intpartn_finType := Eval hnf in [finType of intpartn for type].
Canonical intpartn_subFinType := Eval hnf in [subFinType of intpartn].

Lemma intpartnP (p : intpartn) : is_part p.
Proof using. by case: p => /= p /andP []. Qed.

Lemma intpartn_sorted (p : intpartn) : sorted geq p.
Proof. by have:= intpartnP p; rewrite is_part_sortedE => /andP []. Qed.

Hint Resolve intpartnP intpartn_sorted.

Definition intpart_of_intpartn (p : intpartn) := IntPart (intpartnP p).
Coercion intpart_of_intpartn : intpartn >-> intpart.

Lemma intpartn_sumn (p : intpartn) : sumn p = n.
Proof using. by case: p => /= p /andP [] /eqP. Qed.

Lemma mem_intpartn (p : intpartn) i : i \in pnval p -> 0 < i <= n.
Proof. by rewrite -(intpartn_sumn p); apply mem_part. Qed.

Lemma enum_intpartnE : map val (enum {:intpartn}) = enum_partn n.
Proof using. rewrite /=; exact: enum_subE. Qed.

Lemma conj_intpartnP (sh : intpartn) : is_part_of_n n (conj_part sh).
Proof using.
case: sh => sh /= /andP [] /eqP <- Hpart.
by rewrite is_part_conj // sumn_conj_part /= eq_refl.
Qed.
Canonical conj_intpartn (sh : intpartn) := IntPartN (conj_intpartnP sh).

Lemma conj_intpartnK : involutive conj_intpartn.
Proof using. move=> p; apply: val_inj => /=; by rewrite conj_partK. Qed.

End PartOfn.

Lemma intpartn0 (sh : intpartn 0) : sh = [::] :> seq nat.
Proof.
case: sh => sh Hsh /=; move: Hsh; rewrite enum_partnP.
by rewrite /enum_partn /= inE => /eqP.
Qed.

Lemma intpartn1 (sh : intpartn 1) : sh = [:: 1] :> seq nat.
Proof.
case: sh => sh Hsh /=; move: Hsh; rewrite enum_partnP.
by rewrite /enum_partn /= inE => /eqP.
Qed.

Lemma intpartn2 (sh : intpartn 2) :
  sh = [:: 2]  :> seq nat \/ sh = [:: 1; 1] :> seq nat.
Proof.
case: sh => sh Hsh /=; move: Hsh; rewrite enum_partnP.
by rewrite /enum_partn /= !inE => /orP [] /eqP ->; [left | right].
Qed.

Definition cast_intpartn m n (eq_mn : m = n) p :=
  let: erefl in _ = n := eq_mn return intpartn n in p.

Lemma cast_intpartnE m n (eq_mn : m = n) p :
  val (cast_intpartn eq_mn p) = val p.
Proof. subst m; by case: p. Qed.

Lemma cast_intpartn_id n eq_n (s : intpartn n) : cast_intpartn eq_n s = s.
Proof using. by apply val_inj => /=; rewrite cast_intpartnE. Qed.

Lemma cast_intpartnK m n eq_m_n :
  cancel (@cast_intpartn m n eq_m_n) (cast_intpartn (esym eq_m_n)).
Proof using. by subst m. Qed.

Lemma cast_intpartnKV m n eq_m_n :
  cancel (cast_intpartn (esym eq_m_n)) (@cast_intpartn m n eq_m_n).
Proof using. by subst m. Qed.

Lemma cast_intpartn_inj m n eq_m_n : injective (@cast_intpartn m n eq_m_n).
Proof using. exact: can_inj (cast_intpartnK eq_m_n). Qed.


Definition rowpart d := if d is _.+1 then [:: d] else [::].
Fact rowpartnP d : is_part_of_n d (rowpart d).
Proof. case: d => [//= | d]; by rewrite /is_part_of_n /= addn0 eq_refl. Qed.
Definition rowpartn d : intpartn d := IntPartN (rowpartnP d).

Definition colpart d := nseq d 1%N.
Fact colpartnP d : is_part_of_n d (colpart d).
Proof.
elim: d => [| d ] //= /andP [] /eqP -> ->.
rewrite add1n eq_refl andbT /=.
by case: d.
Qed.
Definition colpartn d : intpartn d := IntPartN (colpartnP d).

Lemma conj_rowpartn d : conj_intpartn (rowpartn d) = colpartn d.
Proof. apply val_inj => /=; rewrite /rowpart /colpart; by case: d. Qed.
Lemma conj_colpartn d : conj_intpartn (colpartn d) = rowpartn d.
Proof. rewrite -[RHS]conj_intpartnK; by rewrite conj_rowpartn. Qed.


Module IntPartNLex.

Require Import ordtype.

Definition intpartnlex := intpartn.

Definition intpartnlex_pordMixin n := [pordMixin of intpartnlex n by <:].
Canonical intpartnlex_pordType n :=
  Eval hnf in POrdType (intpartnlex n) (intpartnlex_pordMixin n).
Definition intpartnlex_ordMixin n := [ordMixin of intpartnlex_pordType n by <:].
Canonical intpartnlex_ordType n :=
  Eval hnf in OrdType (intpartnlex n) (intpartnlex_ordMixin n).
Canonical intpartnlex_finPOrdType n := [finPOrdType of intpartnlex n].

Definition intpartnlex_inhMixin n := Inhabited.Mixin (rowpartn n).
Canonical intpartnlex_inhType n :=
  Eval hnf in InhType (intpartnlex n) (intpartnlex_inhMixin n).
Canonical intpartnlex_inhOrdType n := [inhOrdType of intpartnlex n].
Canonical intpartnlex_inhOrdFinType n := [inhOrdFinType of intpartnlex n].

End IntPartNLex.


(**  * Counting functions *)

Fixpoint intpartnsk_nb sm sz mx : nat :=
  if sz is sz.+1 then
    (* \sum_(1 <= i <= (minn sm mx)) intpartnsk_nb (sm - i) sz i *)
    iteri (minn sm mx) (fun i n => n + intpartnsk_nb (sm - i.+1) sz i.+1) 0
  else if sm is sm.+1 then 0 else 1.
Definition intpartns_nb sm sz := intpartnsk_nb sm sz sm.
Definition intpartn_nb sm := iteri (sm.+1) (fun sz n => n + intpartns_nb sm sz) 0.

Lemma size_enum_partnsk sm sz mx :
  size (enum_partnsk sm sz mx) = (intpartnsk_nb sm sz mx).
Proof.
elim: sz sm mx => [ [] | sz IHsz] //= sm mx.
rewrite size_flatten /shape -[1]addn0 iota_addl -!map_comp.
rewrite (eq_map (f2 := fun i => intpartnsk_nb (sm - i.+1) sz i.+1)); first last.
  by move=> i /=; rewrite size_map IHsz.
elim: (minn sm mx) => [//= | n IHn].
by rewrite -{1}[n.+1]addn1 iota_add add0n map_cat sumn_cat IHn /= addn0.
Qed.

Lemma size_enum_partns sm sz : size (enum_partns sm sz) = (intpartns_nb sm sz).
Proof. by rewrite size_enum_partnsk. Qed.

Lemma size_enum_partn sm : size (enum_partn sm) = intpartn_nb sm.
Proof.
rewrite /intpartn_nb /enum_partn size_flatten /shape.
elim: (sm.+1) => [//= | n IHn].
rewrite -{1}[n.+1]addn1 iota_add add0n !map_cat sumn_cat IHn /= addn0.
by rewrite size_enum_partns.
Qed.

Lemma card_intpartn sm : #|{:intpartn sm}| = intpartn_nb sm.
Proof.
rewrite [#|_|]cardT enumT unlock /=.
by rewrite -(size_map val) subType_seqP -size_enum_partn.
Qed.

Hint Resolve intpartP intpart_sorted intpartnP intpartn_sorted.


(** * The union of two integer partitions *)

Lemma merge_is_part l k :
  is_part l -> is_part k -> is_part (merge geq l k).
Proof.
rewrite !is_part_sortedE => /andP [sortl l0] /andP [sortk k0].
apply/andP; split; first exact: merge_sorted.
by rewrite mem_merge mem_cat negb_or l0 k0.
Qed.

Lemma merge_sortedE l k :
  is_part l -> is_part k -> merge geq l k = sort geq (l ++ k).
Proof.
rewrite !is_part_sortedE => /andP [sortl _] /andP [sortk _].
apply (eq_sorted (leT := geq)) => //.
- apply: merge_sorted => //.
- exact: sort_sorted.
- by rewrite perm_merge perm_eq_sym perm_sort.
Qed.

Lemma sumn_union_part l k : sumn (merge geq l k) = sumn l + sumn k.
Proof.
have:= perm_merge geq l k => /perm_eqlP/perm_sumn ->.
by rewrite sumn_cat.
Qed.

Fact union_intpart_subproof (l : intpart) (k : intpart) :
  is_part (merge geq l k).
Proof. exact: merge_is_part. Qed.
Definition union_intpart (l : intpart) (k : intpart) :=
  IntPart (union_intpart_subproof l k).

Lemma union_intpartE l k : val (union_intpart l k) = sort geq (l ++ k).
Proof. by rewrite /= merge_sortedE. Qed.

Lemma perm_union_intpart l k : perm_eq (union_intpart l k) (l ++ k).
Proof. by rewrite /= perm_merge. Qed.

Lemma union_intpartC l k : union_intpart l k = union_intpart k l.
Proof.
apply val_inj; rewrite !union_intpartE.
by apply/perm_sortP; rewrite // perm_catC.
Qed.

Lemma union_intpartA l k j :
  union_intpart l (union_intpart k j) = union_intpart (union_intpart k l) j.
Proof.
apply val_inj; rewrite !union_intpartE; apply/perm_sortP => //.
apply (perm_eq_trans (y := l ++ (k ++ j))).
- by rewrite perm_cat2l perm_sort.
- apply (perm_eq_trans (y := (k ++ l) ++ j)).
  + by rewrite catA perm_cat2r perm_catC.
  + by rewrite perm_cat2r perm_eq_sym perm_sort.
Qed.

Section UnionPart.

Variables (m n : nat) (l : intpartn m) (k : intpartn n).

Lemma union_intpartn_subproof : is_part_of_n (m + n) (merge geq l k).
Proof.
apply /andP; split.
- by rewrite sumn_union_part !intpartn_sumn.
- exact: merge_is_part.
Qed.
Definition union_intpartn := IntPartN union_intpartn_subproof.

Lemma union_intpartnE : val union_intpartn = sort geq (l ++ k).
Proof. by rewrite /= merge_sortedE. Qed.

Lemma perm_union_intpartn : perm_eq (union_intpart l k) (l ++ k).
Proof. by rewrite /= perm_merge. Qed.

End UnionPart.


(** * Dominance order on partition *)
Definition partdomsh n1 n2 (s1 s2 : seq nat) :=
  all
    (fun i => n1 + sumn (take i s1) <= n2 + sumn (take i s2))
    (iota 0 (size s1).+1).

Definition partdom := partdomsh 0 0.

Lemma partdomshP {n1 n2 s1 s2} :
  reflect (forall i, n1 + sumn (take i s1) <= n2 + sumn (take i s2))
          (partdomsh n1 n2 s1 s2).
Proof.
apply (iffP allP) => H i; last by move=> _; exact: H.
case: (ltnP i (size s1)) => Hi.
- by apply: H; rewrite mem_iota /= add0n ltnS; apply ltnW.
- have /H : (size s1) \in iota 0 (size s1).+1.
    by rewrite mem_iota /= add0n ltnS.
  rewrite take_size (take_oversize Hi) => /leq_trans; apply.
  by rewrite leq_add2l; apply: sumn_take_leq.
Qed.

Lemma partdomP s1 s2 :
  reflect (forall i, sumn (take i s1) <= sumn (take i s2)) (partdom s1 s2).
Proof.
by apply (iffP partdomshP) => H i; have:= H i; rewrite ?add0n.
Qed.

Lemma partdomsh_add y n1 n2 s1 s2 :
  partdomsh (y + n1) (y + n2) s1 s2 = partdomsh n1 n2 s1 s2.
Proof.
rewrite/partdomsh; apply eq_all => i.
by rewrite -!addnA leq_add2l.
Qed.

Lemma partdom_nil s : partdom [::] s.
Proof. by apply/partdomP. Qed.

Lemma partdom_refl : reflexive partdom.
Proof. by move=> s1; apply/partdomP. Qed.

Hint Resolve partdom_nil partdom_refl.

Lemma partdom_trans : transitive partdom.
Proof.
move=> s1 s2 s3 /partdomP H12 /partdomP H23.
by apply/partdomP => i; exact: (leq_trans (H12 i) (H23 i)).
Qed.

Lemma partdom_anti s1 s2 :
  is_part s1 -> is_part s2 -> partdom s1 s2 -> partdom s2 s1 -> s1 = s2.
Proof.
move=> H1 H2 /partdomP H12 /partdomP H21.
apply sumn_take_inj => // k.
by apply anti_leq; rewrite H12 H21.
Qed.

Lemma partdomsh_cons2 y1 y2 s t n1 n2 :
  partdomsh n1 n2 (y1 :: s) (y2 :: t) =
  (n1 <= n2) && (partdomsh (n1 + y1) (n2 + y2) s t).
Proof.
apply/partdomshP/andP => [H | [Hn /partdomshP Hdom] [|i]] /=; first split.
- by have:= H 0; rewrite /= !addn0.
- by apply/partdomshP => i; have:= H i.+1; rewrite /= !addnA.
- by rewrite !addn0.
- by rewrite !addnA.
Qed.

Lemma partdomsh_cons2E y s t n1 n2 :
  partdomsh n1 n2 (y :: s) (y :: t) = partdomsh n1 n2 s t.
Proof.
rewrite partdomsh_cons2 ![_ + y]addnC partdomsh_add andbC.
case: (boolP (partdomsh _ _ _ _)) => //= /partdomshP/(_ 0).
by rewrite !take0 /= !addn0.
Qed.

Lemma sumn_take_merge t x i :
  is_part t ->
  sumn (take i.+1 (merge geq [:: x] t)) =
  maxn (sumn (take i.+1 t)) (x + sumn (take i t)).
Proof.
elim: t i => [i _| t0 t IHt i /andP [Hhead Hpart]] /=.
  by rewrite addn0 max0n.
move/(_ _ Hpart): IHt => /=.
set mrgx := fix mrgx (s : seq nat) := _; move mrgx before x => Hrec.
case: (leqP x t0) => [/maxn_idPl Hxt0 | /ltnW /maxn_idPr Hxt0];
  case: i => [|i]; rewrite /= ?take0 /= ?addn0 ?Hxt0 //.
- by rewrite Hrec [x + (t0 + _)]addnC -addnA -addn_maxr [_ + x]addnC.
- rewrite [x + (t0 + _)]addnC -addnA -addn_maxr [_ + x]addnC.
  congr (t0 + _); apply esym; apply/maxn_idPr.
  move: Hxt0 => /maxn_idPr/(leq_trans Hhead).
  elim: t i Hpart {Hhead Hrec t0} =>
     [i _ _| t0 t IHt [|i] /andP [Hhead Hpart] /= Ht0] //=.
  + by rewrite take0 !addn0.
  + rewrite [x + (t0 + _)]addnC -addnA leq_add2l addnC.
    exact: (IHt i Hpart (leq_trans Hhead Ht0)).
Qed.

Lemma merge_cons x s t :
  is_part (x :: s) -> is_part t ->
  merge geq (x :: s) t = merge geq [:: x] (merge geq s t).
Proof.
move=> Hxs Ht.
have Hs := is_part_consK Hxs.
have Hx : is_part [:: x] by rewrite /= lt0n (part_head_non0 Hxs).
rewrite (merge_sortedE Hxs Ht) (merge_sortedE Hx) ?merge_is_part //=.
apply (eq_sorted (leT := geq)) => //; try exact: sort_sorted.
by rewrite perm_sort perm_eq_sym perm_sort perm_cons perm_merge.
Qed.

Lemma partdomsh_merge1 n1 n2 x t1 t2 :
  is_part t1 -> is_part t2 ->
  partdomsh n1 n2 t1 t2 ->
  partdomsh n1 n2 (merge geq [:: x] t1) (merge geq [:: x] t2).
Proof.
move=> Ht1 Ht2 /partdomshP Hdom; apply/partdomshP => i.
case: i => [|i].
- by move/(_ 0): Hdom; rewrite /= !take0.
- rewrite !sumn_take_merge // !addn_maxr.
  rewrite ![_ + (x + _)]addnC -![x + _ + _]addnA ![sumn _ + _]addnC.
  by rewrite geq_max !leq_max ?leq_add2l !Hdom /= orbT.
Qed.

Lemma partdomsh_merge n1 n2 s t1 t2 :
  is_part s -> is_part t1 -> is_part t2 ->
  partdomsh n1 n2 t1 t2 ->
  partdomsh n1 n2 (merge geq s t1) (merge geq s t2).
Proof.
elim: s => [//| s0 s IHs] Hs0s Ht1 Ht2 Hdom.
have Hs := is_part_consK Hs0s.
rewrite !(merge_cons Hs0s) //.
apply partdomsh_merge1; try exact: merge_is_part.
exact: IHs.
Qed.

Lemma partdom_union_intpartl (s t1 t2 : intpart) :
  partdom t1 t2 -> partdom (union_intpart s t1) (union_intpart s t2).
Proof. exact: partdomsh_merge. Qed.

Lemma partdom_union_intpartr (s t1 t2 : intpart) :
  partdom t1 t2 -> partdom (union_intpart t1 s) (union_intpart t2 s).
Proof. rewrite !(union_intpartC _ s); exact: partdomsh_merge. Qed.

Lemma partdom_union_intpart (s1 s2 t1 t2 : intpart) :
  partdom s1 s2 -> partdom t1 t2 ->
  partdom (union_intpart s1 t1) (union_intpart s2 t2).
Proof.
move=> /partdom_union_intpartr-/(_ t1)/partdom_trans Hs Ht; apply: Hs.
by move: Ht => /partdom_union_intpartl; apply.
Qed.

Module IntPartNDom.

Require Import ordtype.

Definition intpartndom d := intpartn d.

Fact partdom_porder d : PartOrder.axiom (fun x y : intpartndom d => partdom x y).
Proof using.
split.
- exact: partdom_refl.
- by move=> x y /andP [Hxy Hyx]; apply val_inj => /=; apply: partdom_anti.
- exact: partdom_trans.
Qed.

Definition partdom_pordMixin d := PartOrder.Mixin (partdom_porder d).
Canonical partdom_pordType d :=
  Eval hnf in POrdType (intpartndom d) (partdom_pordMixin d).
Canonical intpartndom_finPOrdType d := [finPOrdType of intpartndom d].
Definition intpartndom_inhMixin d := Inhabited.Mixin (rowpartn d).
Canonical intpartndom_inhType d :=
  Eval hnf in InhType (intpartndom d) (intpartndom_inhMixin d).

Lemma partdomE d : @leqX_op (partdom_pordType d) = partdom.
Proof. by rewrite /leqX_op. Qed.

Lemma partdom_rowpartn d (sh : intpartn d) : partdom sh (rowpartn d).
Proof.
case: d sh => [|d] sh; first by rewrite /= !intpartn0.
rewrite /=; apply/partdomP => i.
case: i => [|i] /=; rewrite ?take0 ?addn0 //.
by rewrite -{2}(intpartn_sumn sh) -{2}(cat_take_drop i.+1 sh) sumn_cat leq_addr.
Qed.

Lemma colpartn_partdom d (sh : intpartn d) : partdom (colpartn d) sh.
Proof.
apply/partdomP => i; rewrite /=.
case: (ssrnat.ltnP i (size sh)) => Hi.
- rewrite !sumn_take !big_nat; apply leq_sum => j /= Hj.
  rewrite nth_nseq.
  have:= (leq_trans (ltn_trans Hj Hi) (size_part (intpartnP sh))).
  rewrite intpartn_sumn => ->.
  rewrite lt0n; apply nth_part_non0 => //.
  exact: ltn_trans Hj Hi.
- rewrite (take_oversize Hi) intpartn_sumn.
  rewrite -{2}(intpartn_sumn (colpartn d)) /=.
  by rewrite -{2}(cat_take_drop i (colpart d)) sumn_cat leq_addr.
Qed.

End IntPartNDom.

From mathcomp Require Import binomial finset.

(** * Shape of set partitions and integer partitions *)
Section SetPartitionShape.

Variable T : finType.
Implicit Types (A B X : {set T}) (P Q : {set {set T}}).

Lemma partition0P P : reflect (P = set0) (partition P set0).
Proof using.
apply (iffP and3P) => [[/eqP Hcov _ H0] | ->].
- case: (set_0Vmem P) => [// | [X HXP]].
  exfalso; suff HX : X = set0 by subst X; rewrite HXP in H0.
  by apply/eqP; rewrite -subset0; rewrite -Hcov (bigcup_max X).
- by split; rewrite ?inE // /trivIset /cover !big_set0 ?cards0.
Qed.

Lemma triv_part P X : X \in P -> partition P X -> P = [set X].
Proof using.
move=> HXP /and3P [/eqP Hcov /trivIsetP /(_ X _ HXP) H H0].
apply/setP => Y; rewrite inE; apply/idP/idP => [HYP | /eqP -> //].
rewrite eq_sym; move/(_ Y HYP): H => /contraR; apply.
have /set0Pn [y Hy] : Y != set0
  by apply/negP => /eqP HY; move: H0; rewrite -HY HYP.
apply/negP => /disjoint_setI0/setP/(_ y).
by rewrite !inE Hy -Hcov andbT => /bigcupP; apply; exists Y.
Qed.

Lemma count_set_of_card (p : pred nat) (P : {set {set T}}) :
  count p [seq #{x} | x <- enum P] = #|P :&: [set x | p #{x}]|.
Proof using.
rewrite cardE -size_filter /enum_mem -enumT /=.
rewrite filter_map size_map; congr size.
rewrite -filter_predI; apply eq_filter.
by move=> S; rewrite !inE andbC.
Qed.

Definition setpart_shape P := sort geq [seq #{X} | X <- enum P].

Lemma setpart_shapeP P D :
  partition P D -> is_part_of_n #|D| (setpart_shape P).
Proof using.
rewrite /setpart_shape => /and3P [/eqP Hcov Htriv Hnon0].
rewrite /is_part_of_n /= is_part_sortedE.
apply/and3P; split.
- by rewrite sumn_sort -sumnE big_map -big_enum -Hcov.
- by apply sort_sorted => m n.
- move: Hnon0; apply contra.
  rewrite mem_sort => /mapP [] x.
  by rewrite mem_enum => Hx /esym/cards0_eq <-.
Qed.

Lemma ex_subset_card B k :
 k <= #{B} -> exists2 A : {set T}, A \subset B & #{A} == k.
Proof using.
rewrite -bin_gt0 -(cards_draws B k) card_gt0 => /set0Pn [x].
rewrite inE => /andP [H1 H2]; by exists x.
Qed.

Lemma ex_setpart_shape (s : seq nat) (A : {set T}) :
  sumn s = #|A| -> 0 \notin s ->
  exists P : seq {set T},
    [/\ uniq P, partition [set X in P] A & [seq #{X} | X <- P] = s].
Proof using.
elim: s A => [| i s IHs] A /=.
  move=> /esym/cards0_eq -> _; exists [::]; split => //.
  apply/partition0P; apply/setP => x.
  by rewrite !inE in_nil.
rewrite inE eq_sym => Hi /norP [Bne0 /IHs{IHs} Hrec].
have: i <= #|A| by rewrite -Hi; apply: leq_addr.
move=> /ex_subset_card [B BsubA /eqP cardB]; subst i.
have /Hrec{Hrec} [P [Puniq]] : sumn s = #|A :\: B|.
  by rewrite cardsD (setIidPr BsubA) -Hi addKn.
move=> /and3P [/eqP covP trivP set0P] Ps; rewrite inE in set0P.
have BninP : B \notin P.
  move: Bne0; apply contra => BinP; rewrite cards_eq0.
  have : B \subset A :\: B.
    by rewrite -covP /cover; apply (bigcup_max B); rewrite // inE.
  rewrite setDE => /subsetIP [_].
  by rewrite -disjoints_subset -setI_eq0 setIid.
rewrite -lt0n card_gt0 in Bne0.
have Hcons : [set X in B :: P] = B |: [set X in P].
  by apply/setP => X; rewrite !inE.
exists (B :: P); split => /=; [|apply/and3P; split|].
- by rewrite Puniq BninP.
- rewrite Hcons /cover big_setU1 /= ?inE // -/(cover _) covP.
  by rewrite -{1}(setIidPr BsubA) setID.
- move: trivP; rewrite /trivIset Hcons.
  rewrite /cover !big_setU1 ?inE //= -/(cover _) => /eqP ->.
  rewrite covP cardsU (_ : B :&: (A :\: B) = set0) ?cards0 ?subn0 //.
  by rewrite setDE setIC -setIA [X in A :&: X]setIC setICr setI0.
- by rewrite !inE negb_or eq_sym Bne0.
- by rewrite Ps.
Qed.

Lemma ex_set_setpart_shape A (sh : intpartn #|A|) :
  exists2 P, partition P A & setpart_shape P = sh.
Proof using.
case: sh => sh.
rewrite /is_part_of_n /= is_part_sortedE => /andP [/eqP shsum /andP [shsort]].
move=> /(ex_setpart_shape shsum) [P [Puniq Ppart Psh]].
exists [set X in P]; first exact: Ppart.
apply (eq_sorted (leT := geq)) => //.
- exact: sort_sorted.
- rewrite /setpart_shape -Psh perm_sort; apply: perm_map.
  apply: (uniq_perm_eq (enum_uniq _) Puniq) => x.
  by rewrite mem_enum inE.
Qed.

Lemma setpart_shape_union P Q :
  [disjoint P & Q] ->
  setpart_shape (P :|: Q) = sort geq (setpart_shape P ++ setpart_shape Q).
Proof using.
rewrite /setpart_shape -setI_eq0 => /eqP disj.
apply/perm_sortP/perm_eqP => // Prd.
have count_sort l : count ^~ (sort geq l) =1 count ^~ l.
  by apply/perm_eqP; rewrite perm_sort perm_eq_refl.
rewrite count_cat !count_sort !count_set_of_card.
rewrite setIUl cardsU -[RHS]subn0; congr(_ - _).
apply/eqP; rewrite cards_eq0 -subset0 -disj.
by apply/subsetP => x; rewrite !inE => /andP [/andP [-> _] /andP [-> _]].
Qed.

End SetPartitionShape.

Lemma setpart_shape_inj
      (T1 T2 : finType) (f : T1 -> T2) (A : {set {set T1}}) :
  injective f -> setpart_shape [set f @: (x : {set T1}) | x in A] = setpart_shape A.
Proof using.
rewrite /setpart_shape /= => Hinj.
apply/perm_sortP/perm_eqP => // P.
rewrite !count_set_of_card -(card_imset _ (imset_inj Hinj)).
rewrite imsetI; last by move=> B C _ _; exact: imset_inj.
congr #{_}; apply/setP => S; rewrite !inE.
case: (boolP (S \in (imset _ _))) => //= /imsetP [U _ -> {S}].
rewrite (card_imset _ Hinj).
apply/idP/imsetP => [| [] V].
- by exists U; rewrite // inE.
- by rewrite inE => HP /(imset_inj Hinj) ->.
Qed.
