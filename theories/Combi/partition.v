(** * Combi.Combi.partition : Integer Partitions *)
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
(** * Shapes and Integer Partitions

Partitions (and more generally shapes) are stored by terms of type [seq nat].
We define the following predicates and operations on [seq nat]:

- [in_shape sh (r, c) ] == the box with coordinate (r, c) belongs to the shape
                         [sh], that is: [c < sh[r]].
- [in_skew inn out (r, c) ] == the box with coordinate (r, c) belongs to the
                         [out] but not [inn]
- [box_in sh] == a sigma type for boxes in sh : [{ b | in_shape sh b }]
                         it is canonically a [subFinType].
- [box_skew inn out] == a sigma type for boxes in the skew shape [out / inn]
- [enum_box_in sh] == a full duplicate free list of the boxes in sh.
- [enum_box_skew inn out] == a full duplicate free list of the boxes in
                         the skew shape [out / inn]

Integer Partitions:

- [is_part sh]        == [sh] is a partition
- [rem_trail0 sh]     == remove the trailing zeroes of a shape
- [is_add_corner sh i] == i is the row of an addable corner of sh
- [is_rem_corner sh i] == i is the row of a removable corner of sh
- [incr_nth sh i]     == the shape obtained by adding a box at the end of the
                         i-th row. This gives a partition if i is an addable
                         corner of sh (Lemma [is_part_incr_nth])
- [decr_nth sh i]     == the shape obtained by removing a box at the end of the
                         i-th row. This gives a partition if i is an removable
                         corner of sh (Lemma [is_part_decr_nth])
- [rem_corners sh]    == the list of the rows of the removable corners of sh.
- [incr_first_n sh n] == adding 1 to the n'th first part of sh,
                         always gives a partitions
- [conj_part sh]      == the conjugate of a partition
- [included s t]      == the Ferrer's diagram of s is included in the
                         Ferrer's diagram of t. This is an order.
- [s / t] = [diff_shape s t] == the difference of the shape s and t
- [outer_shape s t]   == add t to the shape s


Enumeration of integer partitions:

- [is_part_of_n sm sh]     == sh in a partition of n
- [is_part_of_ns sm sz sh] == sh in a partitionfo n of size sz
- [is_part_of_nsk sm sz mx sh] == sh in a partition of n of size sz
                              in parts at most mx
- [enum_partn sm]          == the lists of all partitions of n
- [enum_partns sm sz]      == the lists of all partitions of n of size sz
- [enum_partnsk sm sz mx]  == the lists of all partitions of n of size sz
                              in parts at most mx
- [intpartn_nb sm]         == the number of partitions of n
- [intpartns_nb sm sz]     == the number of partitions of n of size sz
- [intpartnsk_nb sm sz mx] == the number of partitions of n of size sz
                              in parts at most mx


Sigma types for integer partitions:

- [intpart]       == a type for [seq nat] which are partitions;
                     canonically a [subCountType] of [seq nat]
- [conj_intpart]  == the conjugate of a [intpart] as a [intpart]
- [empty_intpart] == the empty intpart

- ['P_n]          == a type for [seq nat] which are partitions of [n];
                     canonically a [finType]
- [cast_intpartn m n eq_mn] == the cast from ['P_m] to ['P_n]
- [rowpartn n]    == the one row partition of sum [n] as a ['P_n]
- [colpartn n]    == the one column partition of sum [n] as a ['P_n]
- [conj_intpartn] == the conjugate of a ['P_n] as a ['P_n]
- [hookpartm n k] == then hook shape partition of sum [n.+1] as a ['P_n.+1]
                     whose arm length is [k] (not counting the corner),
                     that is [(k+1, 1, ..., 1)].

- [decr_nth_intpart p i] == the shape obtained by removing a box at the end
               of the [i]-th row if the result is a partition else [p]

Operations on partitions:

- [union_intpart l k] == the partition of type [intpart] obtained by
               gathering the parts of [l] and [k]
- [l +|+ k] = [union_intpartn l k] == the partition of type ['P_(m + n)]
               obtained by gathering the parts of [l : 'P_m] and [k : 'P_n]

Comparison of partitions:

- [partdom s t] == [s] is dominated by [t], that is the partial sum of [s] are
                   smaller that the partial sum of [t].
- ['PDom_d]     == a type convertible to ['P_d] which is canonically
                   a finite lattice partially ordered by [partdom].
- ['PLexi_d]    == a type convertible to ['P_n] which is canonically
                   finite and totally ordered by the lexicographic order.

Relation with set partitions:

- [setpart_shape P] == the shape of a set partition, i.e.
               the sorted list of the cardinal of the parts
******)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import bigop path binomial finset order tuple.
Require Import tools combclass sorted ordtype lattice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import LeqGeqOrder.

Open Scope nat_scope.
Declare Scope Combi_scope.
Delimit Scope Combi_scope with Combi.
Open Scope Combi_scope.

Reserved Notation "''P_' n"
         (at level 8, n at level 2, format "''P_' n").
Reserved Notation "''PDom_' n"
         (at level 8, n at level 2, format "''PDom_' n").
Reserved Notation "''PLexi_' n"
         (at level 8, n at level 2, format "''PLexi_' n").


(** * Shapes *)
Definition in_shape sh b := b.2 < nth 0 sh b.1.
Definition in_skew inn out b := nth 0 inn b.1 <= b.2 < nth 0 out b.1.

Lemma in_skewE inn out b :
  in_skew inn out b =  ~~ in_shape inn b && in_shape out b.
Proof. by rewrite /in_skew /in_shape -leqNgt andbC. Qed.
Lemma in_skew_out inn out b : in_skew inn out b -> in_shape out b.
Proof. by rewrite in_skewE => /andP[]. Qed.
Lemma in_skew_in inn out b : in_skew inn out b -> ~~ in_shape inn b.
Proof. by rewrite in_skewE => /andP[]. Qed.

Lemma in_shape_nil : in_shape [::] =1 pred0.
Proof. by move=> [r c] /=; rewrite /in_shape /= nth_nil ltn0. Qed.
Lemma in_skew_nil : in_skew [::] =2 in_shape.
Proof. by move=> out rc; rewrite in_skewE in_shape_nil. Qed.

Lemma in_shape_size sh r c : in_shape sh (r, c) -> r < size sh.
Proof.
rewrite /in_shape; apply contraLR; rewrite -!leqNgt => Hr.
by rewrite (nth_default _ Hr).
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
elim: sh => [| sh0 sh IHsh] //= /eqP ->.
by rewrite leqn0; case (boolP (head 1 sh == 0)).
Qed.

Lemma part_head_non0 sh : is_part sh -> head 1 sh != 0.
Proof.
elim: sh => [| sh0 sh IHsh] //= /andP[Head].
move/IHsh; apply: contraLR; rewrite !negbK => /eqP Hsh0.
by move: Head; rewrite Hsh0 leqn0.
Qed.

Lemma notin0_part sh : is_part sh -> 0 \notin sh.
Proof.
elim: sh => [//| s0 sh IHsh] Hpart.
rewrite inE negb_or eq_sym.
have /= -> /= := (part_head_non0 Hpart).
by apply: IHsh; move: Hpart => /= /andP[].
Qed.

Lemma in_part_non0 sh i : is_part sh -> i \in sh -> i != 0.
Proof. by move/notin0_part => + Hi; apply/contra => /eqP <-. Qed.

Lemma nth_part_non0 sh i : is_part sh -> i < size sh -> nth 0 sh i != 0.
Proof. by move/in_part_non0 => H le_i_sz; apply/H/mem_nth. Qed.

Lemma leq_head_sumn sh : head 0 sh <= sumn sh.
Proof. by case: sh => //= s0 s; apply: leq_addr. Qed.

Lemma part_leq_head sh i : is_part sh -> i \in sh -> i <= head 0 sh.
Proof.
elim: sh => [| sh0 sh IHsh] // Hpart.
rewrite inE => /orP [/eqP->/= |].
  by case: sh0 {Hpart} (part_head_non0 Hpart) => [|n _]//=.
move: Hpart => /= => /andP[Hhead {}/IHsh H{}/H] /leq_trans; apply.
by case: sh Hhead.
Qed.

(** Three equivalent definitions *)
Lemma is_partP sh :
  reflect
    (last 1 sh != 0 /\ forall i, (nth 0 sh i) >= nth 0 sh i.+1)
    (is_part sh).
Proof.
apply: (iffP idP).
- elim: sh => [| sh0 sh IHsh] //= /andP[Hhead Hpart].
  move/(_ Hpart) : IHsh => [Hlast Hi].
  split; first by case: sh Hhead Hpart Hlast Hi => [| sh1 sh] //=; case sh0.
  case => [|i] /=; first by move: Hhead; case sh.
  exact (Hi i).
- elim: sh => [| sh0 sh IHsh] //= [Hlast Hpart].
  apply/andP; split.
  * move: Hlast; move/(_ 0) : Hpart => /=; case sh => //=.
    by rewrite /head ltn_neqAle eq_sym => -> ->.
  * apply: IHsh; split; last by move=> i; apply: (Hpart i.+1).
    by move: Hlast; case sh.
Qed.

Lemma is_part_ijP sh :
  reflect
    (last 1 sh != 0 /\ forall i j, i <= j -> (nth 0 sh i) >= nth 0 sh j)
    (is_part sh).
Proof.
apply: (iffP idP) => [/is_partP [H0 H] | [H0 H]].
- split=> [| i {H0} j /subnKC <-]; first exact H0.
  elim: (j - i) => [|n IHn] {j}; first by rewrite addn0.
  rewrite addnS.
  exact: (leq_trans (H _) IHn).
- by apply/is_partP; split => [| {H0} i]; [exact H0 | exact: H].
Qed.

Lemma is_part_sortedE sh : (is_part sh) = (sorted geq sh) && (0 \notin sh).
Proof.
apply/idP/andP => [Hpart|].
- split.
  + apply/sorted1P => i _.
    by move: Hpart=> /is_partP [_]; apply.
  + exact: notin0_part.
- move=> [/sorted1P Hsort Hnotin].
  apply/is_partP; split => [| i].
  + case: sh Hnotin {Hsort} => [// | s0 sh].
    by apply contra => /= => /eqP <-; apply: mem_last.
  + case: (ltnP i.+1 (size sh)) => Hsz; first exact: Hsort.
    by rewrite (nth_default _ Hsz).
Qed.

(** Sub-partitions *)

Lemma is_part_consK l0 sh : is_part (l0 :: sh) -> is_part sh.
Proof. by move=> /= /andP[]. Qed.

Lemma is_part_behead sh : is_part sh -> is_part (behead sh).
Proof. case: sh => [//| l0 sh] /=; exact: is_part_consK. Qed.

Lemma is_part_subseq sh1 sh2 : subseq sh1 sh2 -> is_part sh2 -> is_part sh1.
Proof.
rewrite !is_part_sortedE => Hsub /andP[Hsort H0].
rewrite (subseq_sorted _ Hsub Hsort) //=.
by move: H0; apply contra => /(mem_subseq Hsub).
Qed.

Lemma is_part_rconsK sh sn : is_part (rcons sh sn) -> is_part sh.
Proof. exact/is_part_subseq/subseq_rcons. Qed.

Lemma is_part_catl sh1 sh2 : is_part (sh1 ++ sh2) -> is_part sh2.
Proof. exact/is_part_subseq/suffix_subseq. Qed.
Lemma is_part_catr sh1 sh2 : is_part (sh1 ++ sh2) -> is_part sh1.
Proof. exact/is_part_subseq/prefix_subseq. Qed.


(** Boxes in a partitions *)

Lemma in_part_le (sh : seq nat) r c j k :
  is_part sh -> in_shape sh (r, c) -> j <= r -> k <= c -> in_shape sh (j, k).
Proof.
rewrite /in_shape => /is_part_ijP[_ Hpart] Hcr /Hpart Hrj Hkc.
exact: leq_ltn_trans Hkc (leq_trans Hcr Hrj).
Qed.

Lemma in_part_is_part (sh : seq nat) :
  (forall r c j k, j <= r -> k <= c ->
                   in_shape sh (r, c) -> in_shape sh (j, k)) ->
  last 1 sh != 0 -> is_part sh.
Proof.
rewrite /in_shape => H Hlast.
apply/is_partP; split => [|i]; first exact: Hlast.
case Hnth : (nth 0 sh i.+1) => [//|n].
apply: (H i.+1 n i n (leqnSn i) (leqnn n)).
by rewrite Hnth.
Qed.


(** Equality of partitions *)
Lemma part_eqP p q :
  is_part p -> is_part q -> reflect (forall i, nth 0 p i = nth 0 q i) (p == q).
Proof.
move=> Hp Hq.
apply (iffP idP) => [/eqP -> //| H].
apply/eqP; apply (eq_from_nth (x0 := 0)); last by move=> i _; exact: H.
move: H Hp Hq.
wlog Hpq : p q / (size p) <= (size q).
  move=> Hwlog Hnth.
  by case: (leqP (size p) (size q)) => [|/ltnW] /Hwlog H{}/H H{}/H ->.
move=> Hnth /is_part_ijP [Hlastp Hp] /is_part_ijP [Hlastq Hq].
apply anti_leq; rewrite {}Hpq /=.
case: q Hnth Hlastq Hq => [//=|q0 q] Hnth Hlastq Hq.
rewrite leqNgt; apply/negP => Habs.
move: Hlastq.
have:= Habs; rewrite -(ltn_predK Habs) ltnS => /(Hq _ _).
by rewrite nth_last /= -Hnth nth_default // leqn0 => /eqP ->.
Qed.

(** Partitions and sumn *)
Lemma part0 sh : is_part sh -> sumn sh = 0 -> sh = [::].
Proof. by move/part_head_non0; case: sh => //= [] [|s0]. Qed.

Lemma size_part sh : is_part sh -> size sh <= sumn sh.
Proof.
elim: sh => [//= | s0 sh IHsh] /= /andP[Hhead Hpart].
apply: (leq_ltn_trans (IHsh Hpart)).
rewrite -{1}[sumn sh]add0n ltn_add2r.
have /part_head_non0 /= : is_part (s0 :: sh) by rewrite /= Hhead Hpart.
by rewrite lt0n.
Qed.

Lemma part_sumn_rectangle (sh : seq nat) :
  is_part sh -> sumn sh <= (head 0 sh) * (size sh).
Proof.
elim: sh => [//= | s0 s IHs] /= /andP[Hhead /IHs{IHs} Hsum].
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
move=> /andP[H01 /IHs /=].
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
  rewrite addn_eq0 => /andP[_ H].
  by rewrite (set_nth_default 0 1).
- move=> _; rewrite /= (set_nth_default 0 1).
  + by rewrite nth_incr_nth eq_refl.
  + by rewrite size_incr_nth [i < size sh]ltnNge Hi /=.
Qed.

Lemma is_part_incr_nth_size sh l :
  is_part sh -> is_part (incr_nth sh l) -> l <= size sh.
Proof.
elim: sh l => [| sh0 sh IHsh] //= l.
  move => _.
  by case: l => [| i] //= /andP[]; rewrite leqn0 => /part_head0F ->.
case: l => [//= | l].
by rewrite ltnS /= => /andP[_ /IHsh H] /andP[_ /H].
Qed.

Lemma is_part_incr_nth sh i :
  is_part sh -> is_add_corner sh i -> is_part (incr_nth sh i).
Proof.
rewrite /is_add_corner; move=> /is_partP [Hhead Hpart].
case (altP (i =P 0)) => [-> _ {i} | Hi /= H]; apply/is_partP.
- case: sh Hhead Hpart => [//= _ _ | s0 sh /=]; first by split=> //= [] [].
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
move=> Hn0 /is_partP [_ Hpart1].
rewrite/is_rem_corner; apply/idP/idP.
- move=> Hcorn; apply/is_partP; split; first exact Hn0.
  move=> j; move: Hcorn (Hpart1 j).
  rewrite !nth_incr_nth (@ltn_eqF i i.+1) // eq_refl add0n add1n ltnS => Hcorn.
  case (eqP (y:=j)) => [<- //=|_].
  by case eqP => [Hi |_]; rewrite !add0n // add1n; apply: ltnW.
- move=> /is_partP => [] [_ /(_ i)].
  by rewrite !nth_incr_nth (@ltn_eqF i i.+1) // eq_refl add0n add1n ltnS.
Qed.

Lemma rem_corner_incr_nth sh i :
  is_part sh -> is_add_corner sh i -> is_rem_corner (incr_nth sh i) i.
Proof.
rewrite /is_add_corner /is_rem_corner /= nth_incr_nth. 
case: i => [/= | i].
  case: sh => [// | s0 [// | s1 s]] /= /andP[].
  by rewrite ltnS.
move=> Hpart /orP [] //; rewrite [i.+1.-1]/=.
elim: sh i Hpart => [| s0 sh IHsh] i /=; first by rewrite !nth_nil.
move=> /andP[Hhead Hpart].
case: i => [_|i].
  move: Hhead; case: sh Hpart {IHsh} => [//= | s1 [//= | s2 sh]] /= /andP[].
  by rewrite ltnS.
by move=> /(IHsh i Hpart).
Qed.

Lemma is_rem_cornerP sh i : is_part sh ->
  (i < size sh) && (~~ in_shape sh (i.+1, (nth 0 sh i).-1)) =
  (is_rem_corner sh i).
Proof.
rewrite /is_rem_corner /in_shape -ltnNge => Hpart.
apply/idP/idP.
- move=> /andP[/(nth_part_non0 Hpart)].
  by case: (nth 0 sh i).
- case: (ltnP i (size sh)) => Hi; last by rewrite [nth 0 sh i]nth_default.
  have:= nth_part_non0 Hpart Hi.
  by case: (nth 0 sh i) => pi //= _ ->.
Qed.


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
- by move=> _ /andP[]; rewrite leqn0 => /part_head0F ->.
- by case: s0 => //= /andP[]; rewrite leqn0 => /part_head0F ->.
- move=> /andP[Head Hpart] /andP[Headincr Hpartincr].
  by rewrite IHsh.
Qed.

Lemma decr_nthK sh i :
  is_part sh -> is_rem_corner sh i -> incr_nth (decr_nth sh i) i = sh.
Proof.
rewrite /is_rem_corner.
elim: sh i => [| s0 sh IHsh] /=; first by case.
case=> [| i] /=; case: s0 => [| s0] //= /andP[].
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
  is_part sh -> is_rem_corner sh i -> i != j ->
  nth 0 (decr_nth sh i) j = nth 0 sh j.
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
  case: s0 => [| [| s0]] //= /andP[_ ->].
  by case sh => //= s1 _; rewrite ltnS => ->.
move=> /andP[Hhead Hpart] Hnth.
apply/andP; split; last exact: IHsh.
apply: (@leq_trans (head 1 sh)); last exact Hhead.
case: sh {IHsh Hhead Hnth s0} Hpart => [//= | s1 s]; first by case i.
case i => //= /andP[].
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
move/is_partP : Hpart => [_ Hdecr].
apply: leq_trans _ (Hdecr i).
by move: Hi2; case: (nth 0 sh i.+1).
Qed.

Definition rem_corners sh := filter (is_rem_corner sh) (iota 0 (size sh)).

Lemma rem_corners_uniq sh : uniq (rem_corners sh).
Proof. rewrite /rem_corners; apply filter_uniq; exact: iota_uniq. Qed.

(** ** Conjugate of a partition *)

Fixpoint incr_first_n sh n :=
  if sh is s0 :: s then
    if n is n'.+1 then s0.+1 :: incr_first_n s n'
    else sh
  else nseq n 1.
Fixpoint conj_part sh :=
  if sh is s0 :: sh then incr_first_n (conj_part sh) s0
  else [::].

Lemma is_part_nseq1 n : is_part (nseq n 1).
Proof. by elim: n => [//= | n /= ->]; rewrite andbT; case n. Qed.

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
  by move/(_ j) : IHi => /= <-; case: i.
case=> [| i] [| j] //=.
by rewrite IHsh.
Qed.

Lemma is_part_incr_first_n sh n :
  is_part sh -> is_part (incr_first_n sh n).
Proof.
elim: sh n => [// n _| s0 sh IHsh] /=; first exact: is_part_nseq1.
case=> [//= | n] /andP[Hhead /IHsh{IHsh} /= ->]; rewrite andbT.
case: sh Hhead => [_ | s1 sh] /=; first by case n.
case: n => [| n] /=; last by apply.
by move/leq_trans; apply.
Qed.

Lemma is_part_conj sh : is_part sh -> is_part (conj_part sh).
Proof.
elim: sh => [//= | s0 sh IHsh] /= /andP[_ /IHsh{IHsh}].
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
by case: n => [//= | n]; rewrite /= ltnS => /IHsh ->.
Qed.

Lemma size_conj_part sh : is_part sh -> size (conj_part sh) = head 0 sh.
Proof.
elim: sh => [//= | s0 [| s1 sh] IHsh] /= /andP[Hhead /IHsh{IHsh}] /= Hrec.
- by rewrite size_nseq.
- by move: Hhead; rewrite -{1}Hrec => /size_incr_first_n.
Qed.

Lemma sumn_incr_first_n sh n : sumn (incr_first_n sh n) = sumn sh + n.
Proof.
elim: n sh => [/= | n IHn].
case => //=.
case => [/= | s0 s /=].
- have -> : sumn (nseq n 1) = n.
    by elim: n {IHn} => //= n ->; rewrite add1n.
  by rewrite add0n add1n.
- by rewrite IHn addnA addnS !addSn.
Qed.

Lemma sumn_conj_part sh : sumn (conj_part sh) = sumn sh.
Proof.
by elim: sh => [//= | s0 s IHs] /=; rewrite sumn_incr_first_n IHs addnC.
Qed.

Lemma conj_part_ind sh l :
  sh != [::] -> is_part sh -> l >= size sh ->
  conj_part (incr_first_n sh l) = l :: conj_part sh.
Proof.
elim: sh l => [//= | s0 s IHs l] _ /=.
move=> /andP[_ Hpart] Hs0.
case: l Hs0 => [//= | l] /=; rewrite ltnS => Hs0.
case: s IHs Hpart Hs0 => [//= _ _| s1 s IHs].
- by case: l => [//=| l ]; rewrite conj_nseq; last exact: ltn0Sn.
- have Hneq : s1 :: s != [::] by [].
  move=> Hpart Hsize /=.
  move/(_ l Hneq Hpart Hsize) : IHs.
  by case: l Hsize => [//= | l /=] _ ->.
Qed.

Lemma conj_partK sh : is_part sh -> conj_part (conj_part sh) = sh.
Proof.
elim: sh => [//=| s0 sh IHsh] /= /andP[Hhead Hpart].
case (altP (sh =P [::])) => Hsh.
- move: Hhead; rewrite Hsh /=; exact: conj_nseq.
- rewrite conj_part_ind //=; first by rewrite IHsh.
  + move: Hsh; apply: contra => /eqP.
    case: sh Hpart {IHsh Hhead} => [//= | s1 s] /=.
    case: s1 => [/andP[]| s1 _]; first by rewrite leqn0 => /part_head0F ->.
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
move=> /= /andP[H0 Hpart].
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

Lemma in_conj_part_impl sh : is_part sh ->
  forall r c, in_shape sh (r, c) -> in_shape (conj_part sh) (c, r).
Proof.
rewrite /in_shape.
elim: sh => [| s0 s IHs] Hpart r c.
  by rewrite /is_rem_corner nth_default // nth_default //.
have:= Hpart => /= /andP[Hhead Hparts].
rewrite nth_incr_first_n.
case: r => [ -> // | r] /= H.
move/is_part_ijP : Hpart => [_ /(_ _ _ (leq0n r.+1))/=].
move=> /(leq_trans H) ->.
by rewrite ltnS; exact:  IHs.
Qed.

Lemma in_conj_part sh : is_part sh ->
  forall r c, in_shape sh (r, c) = in_shape (conj_part sh) (c, r).
Proof.
move=> Hpart r c; apply/idP/idP; first exact: in_conj_part_impl.
rewrite -{2}(conj_partK Hpart).
by apply in_conj_part_impl; exact: is_part_conj.
Qed.

(* A rephrasing of the preceding lemma *)
Lemma conj_ltnE sh :
  is_part sh -> forall i j, nth 0 sh i > j = (nth 0 (conj_part sh) j > i).
Proof.
move=> Hpart.
rewrite -/(in_shape sh _) -/(in_shape (conj_part sh) _).
exact: in_conj_part.
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
- by move/eqP ->; rewrite !leqnn.
- by move=> H; apply/eqP; exact: anti_leq.
Qed.

Lemma rem_corner_incr_first_n sh i :
  is_part sh -> is_rem_corner (incr_first_n sh i.+1) i.
Proof.
rewrite /is_rem_corner.
elim: sh i => [/= i _ | s0 sh IHsh i]; first by elim: i.
move=> /= => /andP[Hhead /IHsh{IHsh} Hrec].
case: i => [| i] /=; first by case: sh Hhead {Hrec}.
exact: (Hrec i).
Qed.

Lemma rem_corner_incr_first_nE sh n i :
  is_part sh -> is_rem_corner sh i -> is_rem_corner (incr_first_n sh n) i.
Proof.
rewrite /is_rem_corner.
elim: sh i n => [/= i n _ | s0 sh IHsh i n]; first by elim: i.
rewrite [is_part _]/= => /andP[Hhead Hpart].
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
  case: sh Hpart (part_head_non0 Hpart) => [| s0 sh] //= /andP[Hs0 Hpart] Hs0n0.
  apply/orP; right.
  rewrite !nth_incr_first_n ltnn.
  have -> : s0.-1 < s0 by move: Hs0n0; case s0.
  rewrite ltnS {Hs0}.
  case: s0 Hs0n0 => [//= | s0] _.
  by move/is_part_conj/is_partP: Hpart => [_]; apply.
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
  is_part sh -> is_rem_corner sh i ->
  is_rem_corner (conj_part sh) (nth 0 sh i).-1.
Proof.
elim: sh i => [| s0 sh IHsh] i /=.
  by rewrite /is_rem_corner nth_default // nth_default //.
move=> /andP[H0 Hpart].
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
  exfalso; move/(_ 1) : IHs; rewrite /= take0 /= addn0 => H.
  by rewrite H eq_refl in Ht0.
- case: t s IHs => [s _ Hs _ /(_ 1) | t0 t] /=.
  + rewrite take0 /= addn0 => Hs0.
    by exfalso; move/part_head_non0 : Hs; rewrite Hs0.
  + move=> s IHs /is_part_consK Hps /is_part_consK Hpt /= Heq.
    have:= Heq 1; rewrite /= !take0 /= !addn0 => Ht0; subst t0.
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
    by move=> outer _; split; last by move=> i; rewrite nth_nil.
  case=> [//= | out0 out] /= /andP[H0 /IHinn{IHinn} [Hsize H]].
  split; first by rewrite ltnS.
  by case.
- elim: inner outer => [//= | inn0 inn IHinn] /=.
  case=> [ [] //= | out0 out] [] /=.
  rewrite ltnS => Hsize H.
  apply/andP; split; first exact: (H 0).
  apply: IHinn; split; first exact: Hsize.
  by move=> i; exact: (H i.+1).
Qed.

Lemma part_includedP inner outer :
  is_part inner ->
  reflect (forall i, nth 0 inner i <= nth 0 outer i) (included inner outer).
Proof.
move=> Hinn; apply (iffP (includedP _ _)) => [[]//|H]; split; last by [].
case Hsz : (size inner) => [//|n].
have /(nth_part_non0 Hinn) : n < size inner by rewrite Hsz.
rewrite -lt0n => /leq_trans/(_ (H _)).
by apply: contraTltn => /(nth_default 0) ->.
Qed.

Lemma included_behead p1 p2 :
  included p1 p2 -> included (behead p1) (behead p2).
Proof.
case: p1 => [//=|a l].
  by case: p2 => [//=|b s] /= /andP[].
Qed.

Lemma included_refl sh : included sh sh.
Proof. by elim: sh => [//= | s0 sh /= -> ]; rewrite leqnn. Qed.

Lemma included_trans : transitive included.
Proof.
move=> shb sha shc.
move=> /includedP[Hsza Hincla] /includedP[Hszb Hinclb].
apply/includedP; split; first exact (leq_trans Hsza Hszb).
by move=> i; exact: leq_trans (Hincla i) (Hinclb i).
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
move=> Hnth /includedP [Hsize Hincl].
apply/includedP; split.
- rewrite size_incr_nth; case ltnP => _; first exact Hsize.
  rewrite ltnNge; apply/negP => Hout.
  by move: Hnth; rewrite (nth_default _ Hout).
- move=> j; rewrite nth_incr_nth.
  by case eqP => [<- | _]; rewrite ?add1n ?add0n.
Qed.

Lemma size_included inner outer :
  included inner outer -> size inner <= size outer.
Proof.
elim: inner outer => [//= | inn0 inn IHinn] /=.
case=> [//= | outer0 outer] /= /andP[_ /IHinn].
by rewrite ltnS.
Qed.

Lemma sumn_included inner outer :
  included inner outer -> sumn inner <= sumn outer.
Proof.
elim: inner outer => [//= | inn0 inn IHinn] /=.
case=> [//= | outer0 outer] /= /andP[H0 /IHinn].
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
case=> [//= | outer0 out] /= /andP[_ /IHinn{IHinn}Hrec] /andP[H0 Hincl] Heq.
by have:= leq_addE H0 (sumn_included Hincl) Heq => [] [-> /(Hrec Hincl) ->].
Qed.

Lemma included_anti sh1 sh2 :
  is_part sh1 -> is_part sh2 ->
  included sh1 sh2 -> included sh2 sh1 ->
  sh1 = sh2.
Proof.
move=> psh1 psh2 in12 in21; apply included_sumnE => //.
by apply anti_leq; rewrite !sumn_included.
Qed.

Lemma included_conj_part inner outer :
  is_part inner -> is_part outer ->
  included inner outer -> included (conj_part inner) (conj_part outer).
Proof.
move=> Hinn Hout /includedP [Hsz Hincl].
apply/part_includedP => [|i]; first exact: is_part_conj.
by rewrite -conj_leqE //; apply (leq_trans (Hincl _)); rewrite conj_leqE.
Qed.

Lemma included_conj_partE inner outer :
  is_part inner -> is_part outer ->
  included inner outer = included (conj_part inner) (conj_part outer).
Proof.
move=> Hinn Hout; apply/idP/idP; first exact: included_conj_part.
rewrite -{2}(conj_partK Hinn) -{2}(conj_partK Hout).
by apply: included_conj_part; exact: is_part_conj.
Qed.


Fixpoint diff_shape inner outer :=
  if inner is inn0 :: inn then
    if outer is out0 :: out then
      out0 - inn0 :: diff_shape inn out
    else [::] (* Unused case *)
  else outer.

Notation "outer / inner" := (diff_shape inner outer) : Combi_scope.

Definition pad (T : Type) (x : T) sz := [fun s => s ++ nseq (sz - size s) x].

Lemma nth_pad (T : Type) n (p : T) (s : seq T) i :
  nth p (pad p n s) i = nth p s i.
Proof.
rewrite /pad /= nth_cat.
case: (ltnP i (size s)) => //= /(nth_default p) ->.
by rewrite nth_nseq if_same.
Qed.

Lemma head_pad (T : Type) n (p : T) (s : seq T) :
  head p (pad p n s) = head p s.
Proof. by elim: s => [| s0 s IHs] //=; rewrite subn0; case: n. Qed.

Definition outer_shape inner size_seq :=
  [seq p.1 + p.2 | p <- zip (pad 0 (size (size_seq)) inner) size_seq].


Lemma diff_shape_eq s : s / s = nseq (size s) 0.
Proof. by elim: s => [|s0 a IHs] //=; rewrite subnn IHs. Qed.

Lemma sumn_diff_shape_eq s : sumn (s / s) = 0.
Proof. by rewrite diff_shape_eq sumn_nseq mul0n. Qed.

Lemma size_diff_shape inner outer : size (outer / inner) = size outer.
Proof.
elim: inner outer => [//= | inn0 inn IHinn] /= [//= | out0 out] /=.
by rewrite IHinn.
Qed.

Lemma nth_diff_shape inn out i :
  nth 0 (out / inn) i = nth 0 out i - nth 0 inn i.
Proof.
elim: inn out i => [| inn0 inn IHinn] out i //=.
  by rewrite (@nth_default _ _ [::]) // subn0.
case: out => [| out0 out] /=.
  by rewrite nth_default.
by case: i => [| i] //=.
Qed.

Lemma sumn_diff_shape inner outer :
  included inner outer -> sumn (outer / inner) = sumn outer - sumn inner.
Proof.
elim: inner outer => [//= | inn0 inn IHinn] /= [//= | out0 out] /=.
  by rewrite subn0.
move/andP => [Hleq Hincl].
rewrite (IHinn _ Hincl) {IHinn}.
have Hsumn : sumn inn <= sumn out.
  elim: inn out Hincl => [//= | inn1 inn IHinn] /= [//= | out1 out] /=.
  by move/andP => [H1 /IHinn]; exact: leq_add.
by rewrite subnDA (addnBA _ Hsumn) addnC (addnBA _ Hleq) [out0 + _]addnC.
Qed.

Lemma diff_shape_pad0 inner outer :
  outer / ((pad 0 (size outer)) inner) = outer / inner.
Proof.
elim: inner outer => [//= | inn0 inn IHinn] //=.
  by elim=> [//= | out0 out] /=; rewrite !subn0 => ->.
case=> [//= | out0 out] /=.
by rewrite subSS IHinn.
Qed.

Lemma diff_shapeK inner outer :
  included inner outer -> outer_shape inner (outer / inner) = outer.
Proof.
rewrite /outer_shape.
elim: inner outer => [//= | inn0 inn IHinn] /= outer.
  rewrite subn0 => _; elim: outer => [//= | out0 out /= ->].
  by rewrite add0n.
case: outer => [//= | out0 out] /= /andP[Hin /IHinn{IHinn} ->].
by rewrite addnC subnK.
Qed.

Lemma outer_shapeK inner diff :
  size inner <= size diff -> (outer_shape inner diff) / inner = diff.
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
- by move: H; rewrite /leq => /eqP H; rewrite H addn0 H.
- by rewrite (subnKC H) subnn.
Qed.

Lemma included_pad0 inner outer :
  included inner outer = included (pad 0 (size outer) inner) outer.
Proof.
elim: inner outer => [//= | inn0 inn IHinn] /= outer /=.
 by rewrite subn0; elim: outer.
case: outer => [//= | out0 out] /=.
by rewrite subSS IHinn.
Qed.


(** * Sigma Types for Partitions *)

Structure intpart : Type := IntPart {pval :> seq nat; _ : is_part pval}.
Canonical intpart_subType := Eval hnf in [subType for pval].
Definition intpart_eqMixin := Eval hnf in [eqMixin of intpart by <:].
Canonical intpart_eqType := Eval hnf in EqType intpart intpart_eqMixin.
Definition intpart_choiceMixin := Eval hnf in [choiceMixin of intpart by <:].
Canonical intpart_choiceType := ChoiceType intpart intpart_choiceMixin.
Definition intpart_countMixin := Eval hnf in [countMixin of intpart by <:].
Canonical intpart_countType := CountType intpart intpart_countMixin.

Lemma intpartP (p : intpart) : is_part p.
Proof. by case: p. Qed.

Lemma intpart_sorted (p : intpart) : sorted geq p.
Proof. by have:= intpartP p; rewrite is_part_sortedE => /andP[]. Qed.

#[export] Hint Resolve intpartP intpart_sorted : core.

Canonical conj_intpart p := IntPart (is_part_conj (intpartP p)).

Lemma conj_intpartK : involutive conj_intpart.
Proof. by move=> p; apply: val_inj => /=; rewrite conj_partK. Qed.

Lemma intpart_sumn_take_inj (s t : intpart) :
  (forall k, sumn (take k s) = sumn (take k t)) -> s = t.
Proof.
move=> H; apply: val_inj => /=.
by apply: sumn_take_inj; last exact H.
Qed.

Canonical empty_intpart := IntPart (pval := [::]) is_true_true.

Lemma empty_intpartP (p : intpart) : sumn p = 0 -> p = empty_intpart.
Proof. by move=> Hsum; apply val_inj => /=; apply: part0. Qed.

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
elim: sz sm mx Hmx => [/= []| sz IHsz sm] //= mx Hmx p.
  by rewrite mem_seq1 => /eqP -> /=; rewrite Hmx.
move/flatten_mapP => [i].
rewrite mem_iota ltnS => /andP[Hposi Himin] /mapP [recp].
move/(IHsz _ _ Hposi)/and4P => [Hp Hsum Hsz Hhead] -> /= {IHsz}.
rewrite Hp (eqP Hsum) (eqP Hsz) Hhead {Hp Hsum Hsz Hhead} /=.
move: Himin; rewrite leq_min => /andP[/subnKC -> ->].
by rewrite !eq_refl.
Qed.

Lemma enum_partnsk_countE sm sz mx :
  mx >= 1 ->
  forall p, is_part_of_nsk sm sz mx p ->
            count_mem p (enum_partnsk sm sz mx) = 1.
Proof.
elim: sz sm mx => [//= | sz IHsz] /= sm mx Hmx.
  by move=> p /and4P [Hhead/nilP -> /= /eqP <-].
case=> [| p0 p] //=; first by rewrite andbF.
move=> /and5P [Hp0]; rewrite eqSS=> /eqP Hsz /eqP Hsm Hhead Hpart.
rewrite count_flatten -map_comp (eq_map (f2 := fun i => i == p0 : nat)); first last.
  move=> i /=; rewrite count_map /=.
  case (altP (i =P p0)) => [Heq | /negbTE Hneq].
  - subst p0; rewrite (eq_count (a2 := xpred1 p)); first last.
      by move=> s; rewrite /= -eqseqE /= eq_refl /=.
    rewrite {}IHsz //=.
    + have /part_head_non0 /= : is_part (i :: p) by rewrite /= Hhead Hpart.
      by rewrite lt0n.
    + by rewrite Hhead Hsz -Hsm addKn !eq_refl Hpart.
  - rewrite (eq_count (a2 := pred0)); first by rewrite count_pred0.
    by move=> s; rewrite /= -eqseqE /= Hneq.
rewrite sumn_pred1_iota add1n ltnS leq_min Hp0 -Hsm leq_addr !andbT.
have /part_head_non0 /= : is_part (p0 :: p) by rewrite /= Hhead Hpart.
by rewrite lt0n => ->.
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
by move=> /Hall /= /andP[_].
Qed.

Lemma enum_partns_countE sm sz p :
  is_part_of_ns sm sz p -> count_mem p (enum_partns sm sz) = 1.
Proof.
rewrite /enum_partns.
case: p => /= [ /and3P [/eqP <- /eqP <-] //= | p0 p] /and4P [Hsz Hsum Hhead Hpart].
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
rewrite cat0s => /flatten_mapP [i].
rewrite mem_iota ltnS => /andP[Hposi Hi].
have /enum_partnsk_allP/allP Hall : sm.+1 >= 1 by [].
by move=> /Hall /= /and3P [].
Qed.

Lemma enum_partn_countE sm p :
  is_part_of_n sm p -> count_mem p (enum_partn sm) = 1.
Proof.
rewrite /enum_partn /= => /andP[Hsum Hpart].
rewrite count_cat enum_partnsE /= Hsum Hpart !andbT.
case: (altP (size p =P 0)) => Hsize.
- rewrite count_flatten -map_comp.
  set empty := map _ _; have {empty} -> : empty = [seq 0 | i <- iota 1 sm].
    rewrite /empty {empty} -eq_in_map => i /=.
    rewrite mem_iota add1n ltnS => /andP[/lt0n_neq0 Hi _].
    apply/count_memPn => /=; move: Hi; apply: contra.
    move/(allP (enum_partns_allP _ _)) => /= /andP[/eqP <- _].
    by rewrite Hsize.
  suff -> : sumn (map (fun=> 0) _) = 0 by rewrite addn0.
  by move=> T; elim => [//= |l0 l /= ->].
- rewrite /= add0n count_flatten -map_comp.
  rewrite (eq_map (f2 := fun i => i == size p : nat)); first last.
    move=> i /=; rewrite enum_partnsE /=.
    by rewrite Hsum Hpart !andbT eq_sym.
  by rewrite sumn_pred1_iota add1n ltnS lt0n Hsize /= -(eqP Hsum) size_part.
Qed.

Lemma enum_partnP n p : (is_part_of_n n p) = (p \in enum_partn n).
Proof.
apply/idP/idP; last by move/(allP (enum_partn_allP n)).
by rewrite -has_pred1 has_count; move/enum_partn_countE ->.
Qed.


Section PartOfn.

Variable n : nat.

Structure intpartn : Set :=
  IntPartN {pnval :> seq nat; _ : is_part_of_n n pnval}.
Canonical intpartn_subType := Eval hnf in [subType for pnval].
Definition intpartn_eqMixin := Eval hnf in [eqMixin of intpartn by <:].
Canonical intpartn_eqType := EqType intpartn intpartn_eqMixin.
Definition intpartn_choiceMixin := Eval hnf in [choiceMixin of intpartn by <:].
Canonical intpartn_choiceType := ChoiceType intpartn intpartn_choiceMixin.
Definition intpartn_countMixin := Eval hnf in [countMixin of intpartn by <:].
Canonical intpartn_countType := CountType intpartn intpartn_countMixin.
Canonical intpartn_subCountType := Eval hnf in [subCountType of intpartn].

Let type := sub_finType
              intpartn_subCountType (enum_partn_allP n) (@enum_partn_countE n).
Canonical intpartn_finType := Eval hnf in [finType of intpartn for type].
Canonical intpartn_subFinType := Eval hnf in [subFinType of intpartn].

Local Notation "''P'" := intpartn.

Implicit Type (p : 'P).
Lemma intpartnP p : is_part p.
Proof using. by case: p => /= p /andP[]. Qed.

Lemma intpartn_sorted p : sorted geq p.
Proof. by have:= intpartnP p; rewrite is_part_sortedE => /andP[]. Qed.

Hint Resolve intpartnP intpartn_sorted : core.

Definition intpart_of_intpartn p := IntPart (intpartnP p).
Coercion intpart_of_intpartn : intpartn >-> intpart.

Lemma sumn_intpartn p : sumn p = n.
Proof using. by case: p => /= p /andP[/eqP]. Qed.

Lemma intpartn_leq_head p i : i \in pnval p -> i <= head 0 p.
Proof. exact: part_leq_head. Qed.

Lemma intpartn_leq p i : i \in pnval p -> i <= n.
Proof.
move=> /intpartn_leq_head /leq_trans; apply.
by rewrite -(sumn_intpartn p); apply: leq_head_sumn.
Qed.

Lemma enum_intpartnE : map val (enum {:'P}) = enum_partn n.
Proof using. by rewrite /=; exact: enum_subE. Qed.

Lemma conj_intpartnP (sh : 'P) : is_part_of_n n (conj_part sh).
Proof using.
case: sh => sh /= /andP[/eqP <- Hpart].
by rewrite is_part_conj // sumn_conj_part /= eq_refl.
Qed.
Canonical conj_intpartn (sh : 'P) := IntPartN (conj_intpartnP sh).

Lemma conj_intpartnK : involutive conj_intpartn.
Proof using. by move=> p; apply: val_inj => /=; rewrite conj_partK. Qed.

End PartOfn.

Notation "''P_' n" := (intpartn n).

Lemma val_intpartn0 (sh : 'P_0) : sh = [::] :> seq nat.
Proof.
case: sh => sh Hsh /=; move: Hsh; rewrite enum_partnP.
by rewrite /enum_partn /= inE => /eqP.
Qed.

Lemma val_intpartn1 (sh : 'P_1) : sh = [:: 1] :> seq nat.
Proof.
case: sh => sh Hsh /=; move: Hsh; rewrite enum_partnP.
by rewrite /enum_partn /= inE => /eqP.
Qed.

Lemma val_intpartn2 (sh : 'P_2) :
  sh = [:: 2]  :> seq nat \/ sh = [:: 1; 1] :> seq nat.
Proof.
case: sh => sh Hsh /=; move: Hsh; rewrite enum_partnP.
by rewrite /enum_partn /= !inE => /orP [] /eqP ->; [left | right].
Qed.

Lemma val_intpartn3 (sh : 'P_3) :
  [\/ sh = [:: 3] :> seq nat,
      sh = [:: 2; 1] :> seq nat |
      sh = [:: 1; 1; 1] :> seq nat].
Proof.
case: sh => sh Hsh /=; move: Hsh; rewrite enum_partnP.
by rewrite /enum_partn /= !inE => /or3P [] /eqP ->;
  [apply Or31 | apply Or32 | apply Or33].
Qed.

Definition cast_intpartn m n (eq_mn : m = n) p :=
  let: erefl in _ = n := eq_mn return 'P_n in p.

Lemma cast_intpartnE m n (eq_mn : m = n) p :
  val (cast_intpartn eq_mn p) = val p.
Proof. by subst m; case: p. Qed.

Lemma cast_intpartn_id n eq_n (s : 'P_n) : cast_intpartn eq_n s = s.
Proof using. by apply val_inj => /=; rewrite cast_intpartnE. Qed.

Lemma cast_intpartnK m n eq_m_n :
  cancel (@cast_intpartn m n eq_m_n) (cast_intpartn (esym eq_m_n)).
Proof using. by subst m. Qed.

Lemma cast_intpartnKV m n eq_m_n :
  cancel (cast_intpartn (esym eq_m_n)) (@cast_intpartn m n eq_m_n).
Proof using. by subst m. Qed.

Lemma cast_intpartn_inj m n eq_m_n : injective (@cast_intpartn m n eq_m_n).
Proof using. exact: can_inj (cast_intpartnK eq_m_n). Qed.

Lemma cast_intpartn_bij m n eq_m_n : bijective (@cast_intpartn m n eq_m_n).
Proof using. exact: Bijective (cast_intpartnK eq_m_n) (cast_intpartnKV _). Qed.

Lemma cast_conj_inpart m n eq_m_n (s : 'P_m) :
  (@cast_intpartn m n eq_m_n) (conj_intpartn s) =
  conj_intpartn (@cast_intpartn m n eq_m_n s).
Proof. by apply val_inj; rewrite /= !cast_intpartnE. Qed.

Fact rowpartn_subproof d : is_part_of_n d (if d is 0 then [::] else [:: d]).
Proof. by case: d => [//= | d]; rewrite /is_part_of_n /= addn0 eq_refl. Qed.
Definition rowpartn d : 'P_d := locked (IntPartN (rowpartn_subproof d)).

Fact colpartn_subproof d : is_part_of_n d (nseq d 1%N).
Proof.
elim: d => [| d ] //= /andP[/eqP -> ->].
rewrite add1n eq_refl andbT /=.
by case: d.
Qed.
Definition colpartn d : 'P_d := locked (IntPartN (colpartn_subproof d)).

Definition intpartn_inhMixin d := InhMixin (rowpartn d).
Canonical intpartn_inhType d := InhType (intpartn d) (intpartn_inhMixin d).

Lemma rowpartnE d : rowpartn d = (if d is 0 then [::] else [:: d]) :> seq nat.
Proof. by rewrite /rowpartn -lock. Qed.
Lemma colpartnE d : colpartn d = nseq d 1%N :> seq nat.
Proof. by rewrite /colpartn -lock. Qed.

Lemma rowpartn0E : rowpartn 0 = [::] :> seq nat.
Proof. by rewrite rowpartnE. Qed.
Lemma rowpartnSE d : rowpartn d.+1 = [:: d.+1] :> seq nat.
Proof. by rewrite rowpartnE. Qed.

Lemma size_colpartn d : size (colpartn d) = d.
Proof. by rewrite colpartnE size_nseq. Qed.
Lemma size_rowpartn d : size (rowpartn d) = (d != 0).
Proof. by rewrite rowpartnE; case: d. Qed.

Lemma part_nseq1P x0 sh :
  is_part sh -> head x0 sh <= 1 -> sh = nseq (sumn sh) 1.
Proof.
move=> Hpart.
elim: sh Hpart (part_head_non0 Hpart) x0 => [//|s0 s IHs]/=/andP[H Hpart].
rewrite -lt0n => lt0s0 x0 les01; move: H.
have {lt0s0 les01} -> : s0 = 1 by apply anti_leq; rewrite lt0s0 les01.
move=> Hhead; rewrite /= -(IHs _ _ 1) //.
exact: part_head_non0.
Qed.
Lemma colpartnP x0 d (la : 'P_d) : head x0 la <= 1 -> la = colpartn d.
Proof.
move=> /(part_nseq1P (intpartnP _)) Heq.
apply val_inj; rewrite /= colpartnE.
by rewrite (sumn_intpartn la) in Heq.
Qed.

Lemma conj_rowpartn d : conj_intpartn (rowpartn d) = colpartn d.
Proof. by apply val_inj => /=; rewrite rowpartnE colpartnE; case: d. Qed.
Lemma conj_colpartn d : conj_intpartn (colpartn d) = rowpartn d.
Proof. by rewrite -[RHS]conj_intpartnK conj_rowpartn. Qed.

(** ** Hook shaped partitions *)

Definition hookpart d k :=
  if d is d'.+1 then minn d'.+1 k.+1 :: nseq (d' - k) 1%N else [::].
Fact hookpartn_subproof d k : is_part_of_n d (hookpart d k).
Proof.
rewrite /hookpart /=; case: d => [|d]//.
have /= /andP[/eqP -> ->] := colpartn_subproof (d.+1 - k.+1).
rewrite andbT subSS minSS addSn minnE subnK ?leq_subr // eqxx /=.
by case : (d - k).
Qed.
Definition hookpartn d k : 'P_d :=
  locked (IntPartN (hookpartn_subproof d k)).

Lemma hookpartnE d k :
  k < d -> (hookpartn d k) = k.+1 :: nseq (d.-1 - k) 1%N :> seq nat.
Proof.
case: d => // d.
by rewrite ltnS /hookpartn -lock /hookpart /= minSS => /minn_idPr ->.
Qed.

Lemma size_hookpartn d k : k < d -> size (hookpartn d k) = d - k.
Proof.
rewrite /hookpartn -lock /hookpart; case: d => //= d ltkd.
by rewrite size_nseq subSn.
Qed.

Lemma behead_hookpartn d k : behead (hookpartn d k) = nseq (d.-1 - k) 1%N.
Proof. by rewrite /hookpartn -lock /hookpart; case: d => [|d]. Qed.

Lemma hookpartn_col d : hookpartn d 0 = colpartn d.
Proof.
apply val_inj; case: d => [|d]/=.
  by rewrite /hookpartn /colpartn -!lock.
by rewrite /= hookpartnE // subn0 colpartnE.
Qed.
Lemma hookpartn_row d : hookpartn d d.-1 = rowpartn d.
Proof.
apply val_inj; case: d => [|d]/=.
  by rewrite /hookpartn /rowpartn -!lock.
by rewrite /= hookpartnE //= subnn /= rowpartnE.
Qed.
Lemma conj_hookpartn d k :
  k < d -> conj_intpartn (hookpartn d k) = hookpartn d (d.-1 - k).
Proof.
case: d => // d; rewrite ltnS; case: k => [_|k ltkd].
  by rewrite hookpartn_col subn0 hookpartn_row conj_colpartn.
apply val_inj; rewrite /= !hookpartnE ?ltnS ?leq_subr //.
have -> : k.+2 :: nseq (d - k.+1) 1 = incr_first_n [:: k.+1] (d - k).
  move: ltkd; rewrite -subn_gt0 /= subnS.
  by case: (d - k).
by rewrite conj_part_ind ?subn_gt0 // subKn //= -subSn.
Qed.

Lemma sorted_geq_count_leq2E (s : seq nat) :
  sorted geq s -> (count (leq 2) s <= 1) = (nth 0 s 1 <= 1).
Proof.
case: s => [|s0 [|s1 s]]//=; first by rewrite addn0; case: ltnP.
move=> /andP[le10 Hpath]; case: (ltnP 1 s1) => [|les1 {le10}].
  by move/leq_trans/(_ le10) ->; rewrite !add1n.
suff -> : count (leq 2) s = 0 by rewrite !addn0; case: ltnP.
elim: s s1 Hpath les1 => // s2 s IHs s1.
move=> /= /andP[les2 Hpath /(leq_trans les2) {les2}les].
by rewrite (IHs _ Hpath les) addn0 ltnNge les.
Qed.

Lemma sorted_geq_nth0E (s : seq nat) :
  sorted geq s -> nth 0 s 0 = \max_(i <- s) i.
Proof.
case: s => [|s0 s]/= Hpath; first by rewrite big_nil.
rewrite big_cons; apply/esym/maxn_idPl.
elim: s s0 Hpath => [|s1 s IHs] s0 /=; first by rewrite big_nil.
rewrite big_cons geq_max=> /andP[le10 Hpath].
by rewrite le10 /=; apply: (leq_trans _ le10); apply: IHs.
Qed.

Lemma intpartn_count_leq2E d (la : 'P_d) :
  (count (leq 2) la <= 1) = (nth 0 la 1 <= 1).
Proof.
apply: sorted_geq_count_leq2E.
by have:= intpartnP la; rewrite is_part_sortedE => /andP[].
Qed.
Lemma intpartn_nth0 d (la : 'P_d) :
  nth 0 la 0 = \max_(i <- la) i.
Proof.
apply sorted_geq_nth0E.
by have:= intpartnP la; rewrite is_part_sortedE => /andP[].
Qed.

Lemma hookpartnPE x0 x1 d (la : 'P_d) :
  nth x0 la 1 <= 1 -> la = hookpartn d (nth x1 la 0).-1.
Proof.
move=> H; apply val_inj => /=.
case: la H => /= [[//=|l0 la] /andP[/eqP Heq Hpart]] /= H.
  by rewrite -Heq /hookpartn -lock.
case: l0 Heq Hpart (part_head_non0 Hpart) => // l0 /=.
rewrite addSn => [Hd] /andP[_ Hpart] _.
rewrite hookpartnE -?Hd ?leq_addr // addKn.
by rewrite {1}(part_nseq1P Hpart H).
Qed.

Lemma hookpartnP d (la : 'P_d.+1) :
  reflect (exists k, k < d.+1 /\ la = hookpartn d.+1 k) (nth 0 la 1 <= 1).
Proof.
apply (iffP idP) => [H | ].
- exists (nth 0 la 0).-1; split; last exact: (hookpartnPE _ H).
  case: la H => /= [[//=|l0 la] /andP[/eqP Heq /part_head_non0]] /= Hl0 _.
  rewrite -ltnS -{}Heq /=; case: l0 Hl0 => // l0 _ /=.
  by rewrite addSn ltnS leq_addr.
- move=> [k [lekd /(congr1 val) /= ->]]; rewrite hookpartnE // /=.
  by case: (d - k).
Qed.


Lemma intpartn0 : all_equal_to (rowpartn 0).
Proof. by move=> sh /=; apply val_inj; rewrite /= val_intpartn0 rowpartnE. Qed.

Lemma intpartn1 : all_equal_to (rowpartn 1).
Proof. by move=> sh /=; apply val_inj; rewrite /= val_intpartn1 rowpartnE. Qed.

Lemma intpartn2 (sh : 'P_2) : sh = rowpartn 2 \/ sh = colpartn 2.
Proof.
by case: (val_intpartn2 sh) => sheq; [left | right]; apply val_inj;
  rewrite /= {}sheq ?rowpartnE ?colpartnE.
Qed.

Lemma intpartn3 (sh : 'P_3) :
  [\/ sh = rowpartn 3, sh = hookpartn 3 1 | sh = colpartn 3].
Proof.
by case: (val_intpartn3 sh) => sheq;
  [apply Or31 | apply Or32 | apply Or33]; apply val_inj;
  rewrite /= {}sheq ?rowpartnE ?hookpartnE ?colpartnE.
Qed.


(** ** Removing a corner from a partition *)

Lemma is_part_decr_nth_part (p : intpart) i :
  is_part (if is_rem_corner p i then decr_nth p i  else p).
Proof.
case: (boolP (is_rem_corner p i)).
- by apply is_part_decr_nth; apply: intpartP.
- by move=> _; apply: intpartP.
Qed.

Definition decr_nth_intpart (p : intpart) i : intpart :=
  IntPart (is_part_decr_nth_part p i).

Lemma decr_nth_intpartE (p : intpart) i :
  is_rem_corner p i -> decr_nth_intpart p i = decr_nth p i :> seq nat.
Proof.
rewrite /decr_nth_intpart /=.
by case: (is_rem_corner p i).
Qed.

Lemma intpart_rem_corner_ind (F : intpart -> Type) :
  F empty_intpart ->
  (forall p : intpart,
      (forall i, is_rem_corner p i -> F (decr_nth_intpart p i)) -> F p) ->
  forall p : intpart, F p.
Proof.
move=> H0 Hrec p.
move Hp : (sumn p) => n.
elim: n p Hp => [| n IHn] p Hp; first by rewrite (empty_intpartP Hp).
apply: Hrec => i Hi.
apply: IHn; rewrite /decr_nth_intpart /= Hi.
by rewrite (sumn_decr_nth (intpartP p) Hi) Hp.
Qed.

Lemma part_rem_corner_ind (F : seq nat -> Type) :
  F [::] ->
  (forall p, is_part p ->
             (forall i, is_rem_corner p i -> F (decr_nth p i)) -> F p) ->
  forall p, is_part p -> F p.
Proof.
move=> H0 Hrec p Hp; rewrite -[p]/(val (IntPart Hp)).
apply: (intpart_rem_corner_ind (F := fun p => F (val p))) => [//|{Hp}p IHp].
apply (Hrec p (intpartP p)) => i Hi.
by move/(_ i Hi): IHp; rewrite /= Hi.
Qed.


(** ** Lexicographic order on partitions of a fixed sum *)

Import Order.TTheory.

Module IntPartNLexi.
Section IntPartNLexi.
Import DefaultSeqLexiOrder.

Variable d : nat.
Definition intpartnlexi := 'P_d.
Local Notation "'PLexi" := intpartnlexi.
Implicit Type (sh : 'PLexi).

Definition pordMixin := Eval hnf in [porderMixin of 'PLexi by <:].
Canonical porderType := POrderType Order.lexi_display 'PLexi pordMixin.
Definition orderMixin := Eval hnf in [totalOrderMixin of 'PLexi by <:].
Canonical latticeType := LatticeType 'PLexi orderMixin.
Canonical distrLatticeType := DistrLatticeType 'PLexi orderMixin.
Canonical orderType := OrderType 'PLexi orderMixin.
Canonical finPOrderType := [finPOrderType of 'PLexi].

Lemma leEintpartnlexi sh1 sh2 :
  (sh1 <= sh2)%O = (sh1 <= sh2 :> seqlexi nat)%O.
Proof. by []. Qed.
Lemma ltEintpartnlexi sh1 sh2 :
  (sh1 < sh2)%O = (sh1 < sh2 :> seqlexi nat)%O.
Proof. by []. Qed.

Lemma rowpartn_top sh : (sh <= rowpartn d :> 'PLexi)%O.
Proof.
rewrite leEsub leEseqlexi.
case: sh; case: d => [|n] sh Hsh; first by rewrite intpartn0 /= rowpartn0E.
rewrite /= rowpartnSE; case: sh Hsh => [|s0 sh]//= /andP[/eqP<- /andP[_ Hpart]].
rewrite !leEnat leq_addr /=; case: leqP => //=.
rewrite -{2}(addn0 s0) leq_add2l leqn0 => /eqP/(part0 Hpart) ->.
by rewrite leEseqlexi.
Qed.
Lemma colpartn_bot sh : (colpartn d <= sh :> 'PLexi)%O.
Proof.
rewrite leEsub leEseqlexi.
case: sh; case: d => [|n] sh Hsh; first by rewrite intpartn0 /= rowpartn0E.
rewrite /= colpartnE.
move: Hsh => /andP[Hsum Hpart]; have := part_head_non0 Hpart.
case: sh Hsum Hpart => [|s0 sh]//= Hsum /andP[Hhead Hpart].
rewrite !leEnat -lt0n => Hs0; rewrite Hs0 /=; case: leqP => //= les01.
have {les01}Hs0 : s0 = 1 by apply anti_leq; rewrite Hs0 les01.
subst s0; suff -> : sh = nseq n 1 by apply: Order.SeqLexiOrder.refl.
move: Hsum; rewrite add1n eqSS => /eqP <-.
exact: (part_nseq1P Hpart Hhead).
Qed.

Definition bottomMixin := BottomMixin colpartn_bot.
Canonical bLatticeType := BLatticeType 'PLexi bottomMixin.
Definition topMixin := TopMixin rowpartn_top.
Canonical tbLatticeType := TBLatticeType 'PLexi topMixin.
Canonical finLatticeType := Eval hnf in [finLatticeType of 'PLexi].
Canonical bDistrLatticeType :=
  Eval hnf in [bDistrLatticeType of 'PLexi].
Canonical tbDistrLatticeType :=
  Eval hnf in [tbDistrLatticeType of 'PLexi].
Canonical finDistrLatticeType :=
  Eval hnf in [finDistrLatticeType of 'PLexi].
Canonical finOrderType := Eval hnf in [finOrderType of 'PLexi].

Canonical inhType := InhType 'PLexi (InhMixin (rowpartn d)).
Canonical inhPOrderType := [inhPOrderType of 'PLexi].
Canonical inhFinPOrderType := [inhFinPOrderType of 'PLexi].
Canonical inhOrderType := [inhOrderType of 'PLexi].
Canonical inhFinOrderType := [inhFinOrderType of 'PLexi].

Lemma botEintpartnlexi : 0%O = colpartn d :> 'PLexi.
Proof. by []. Qed.
Lemma topEintpartnlexi : 1%O = rowpartn d :> 'PLexi.
Proof. by []. Qed.

End IntPartNLexi.

Module Exports.

Notation "''PLexi_' n" := (intpartnlexi n).

Set Warnings "-redundant-canonical-projection".
Canonical porderType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tbLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tbDistrLatticeType.
Canonical orderType.
Canonical finPOrderType.
Canonical finLatticeType.
Canonical finDistrLatticeType.
Canonical finOrderType.
Canonical inhType.
Canonical inhPOrderType.
Canonical inhFinPOrderType.
Canonical inhOrderType.
Canonical inhFinOrderType.
Set Warnings "+redundant-canonical-projection".

Definition botEintpartnlexi := @botEintpartnlexi.
Definition topEintpartnlexi := @topEintpartnlexi.
Definition leEintpartnlexi := @leEintpartnlexi.
Definition ltEintpartnlexi := @ltEintpartnlexi.

End Exports.
End IntPartNLexi.
Export IntPartNLexi.Exports.


(**  * Counting functions *)

Fixpoint intpartnsk_nb sm sz mx : nat :=
  if sz is sz.+1 then
    (* \sum_(1 <= i <= (minn sm mx)) intpartnsk_nb (sm - i) sz i *)
    iteri (minn sm mx) (fun i n => n + intpartnsk_nb (sm - i.+1) sz i.+1) 0
  else if sm is sm.+1 then 0 else 1.
Definition intpartns_nb sm sz := intpartnsk_nb sm sz sm.
Definition intpartn_nb sm :=
  iteri (sm.+1) (fun sz n => n + intpartns_nb sm sz) 0.

Lemma size_enum_partnsk sm sz mx :
  size (enum_partnsk sm sz mx) = (intpartnsk_nb sm sz mx).
Proof.
elim: sz sm mx => [ [] | sz IHsz] //= sm mx.
rewrite size_flatten /shape -[1]addn0 iotaDl -!map_comp.
rewrite (eq_map (f2 := fun i => intpartnsk_nb (sm - i.+1) sz i.+1)); first last.
  by move=> i /=; rewrite size_map IHsz.
elim: (minn sm mx) => [//= | n IHn].
by rewrite -{1}[n.+1]addn1 iotaD add0n map_cat sumn_cat IHn /= addn0.
Qed.

Lemma size_enum_partns sm sz : size (enum_partns sm sz) = (intpartns_nb sm sz).
Proof. by rewrite size_enum_partnsk. Qed.

Lemma size_enum_partn sm : size (enum_partn sm) = intpartn_nb sm.
Proof.
rewrite /intpartn_nb /enum_partn size_flatten /shape.
elim: (sm.+1) => [//= | n IHn].
rewrite -{1}[n.+1]addn1 iotaD add0n !map_cat sumn_cat IHn /= addn0.
by rewrite size_enum_partns.
Qed.

Lemma card_intpartn sm : #|{:'P_sm}| = intpartn_nb sm.
Proof.
by rewrite [#|_|]cardT -(size_map val) /= enum_intpartnE -size_enum_partn.
Qed.

#[export] Hint Resolve intpartP intpart_sorted intpartnP intpartn_sorted : core.


(** * A finite type [finType] for coordinate of boxes inside a shape *)
Section BoxInSkew.

Variable inner outer : seq nat.

Structure box_skew : Set :=
  BoxSkew {box_skewval :> nat * nat; _ : in_skew inner outer box_skewval}.
Canonical box_skew_subType := Eval hnf in [subType for box_skewval].
Definition box_skew_eqMixin := Eval hnf in [eqMixin of box_skew by <:].
Canonical box_skew_eqType := EqType box_skew box_skew_eqMixin.
Definition box_skew_choiceMixin := Eval hnf in [choiceMixin of box_skew by <:].
Canonical box_skew_choiceType := ChoiceType box_skew box_skew_choiceMixin.
Definition box_skew_countMixin := Eval hnf in [countMixin of box_skew by <:].
Canonical box_skew_countType := CountType box_skew box_skew_countMixin.
Canonical box_skew_subCountType := Eval hnf in [subCountType of box_skew].

Lemma box_skewP (rc : box_skew) : in_skew inner outer rc.
Proof using. by case: rc. Qed.

Definition enum_box_skew :=
  [seq (r, c) | r <- iota 0 (size outer),
                c <- iota (nth 0 inner r) (nth 0 outer r - nth 0 inner r)].

Lemma enum_box_skew_uniq : uniq enum_box_skew.
Proof using.
apply: allpairs_uniq_dep => [|i _|]; try exact: iota_uniq.
by move=> [r c] [r' c'] /= _ _ [<-{r'} <-{c'}].
Qed.

Lemma mem_enum_box_skew : enum_box_skew =i in_skew inner outer.
Proof.
move=> [r c]; apply/allpairsPdep/idP.
  move=> [r'][c'][_] /[swap] [[<-{r'} <-{c'}]].
  rewrite mem_iota /in_skew unfold_in /=.
  case: (leqP (nth 0 inner r) (nth 0 outer r)) => [inout | /ltnW].
    by rewrite subnKC.
  rewrite -subn_eq0 => /eqP ->; rewrite addn0.
  by move=> /andP[/leq_ltn_trans/[apply]]; rewrite ltnn.
rewrite unfold_in -/(in_skew _ _ (r, c)) in_skewE => /andP[rcinn rcout].
exists r, c; rewrite !mem_iota /= !add0n (in_shape_size rcout); split => //.
rewrite /in_shape /= -?leqNgt in rcinn rcout.
by rewrite rcinn /= subnKC // (leq_trans rcinn (ltnW rcout)).
Qed.

Let type :=
  sub_uniq_finType box_skew_subCountType enum_box_skew_uniq mem_enum_box_skew.
Canonical box_skew_finType := Eval hnf in [finType of box_skew for type].
Canonical box_skew_subFinType := Eval hnf in [subFinType of box_skew].

Lemma enum_box_skewE : map val (enum {: box_skew}) = enum_box_skew.
Proof using. exact: enum_subE. Qed.

Lemma card_box_skew : #|{: box_skew}| = sumn (outer / inner).
Proof using.
rewrite card_subE /enum_box_skew size_allpairs_dep; congr sumn.
apply: (eq_from_nth (x0 := 0));
  rewrite size_map size_iota ?size_diff_shape // => i ltisz.
by rewrite (nth_map 0) size_iota // nth_iota // add0n nth_diff_shape.
Qed.


(** ** Rewriting bigops running along the boxes of a shape *)
Lemma big_box_skew R (idx : R) (op : Monoid.com_law idx) (f : nat * nat -> R):
  \big[op/idx]_(b : box_skew) f b = \big[op/idx]_(b <- enum_box_skew) f b.
Proof using. by rewrite -enum_box_skewE big_map /= big_enum. Qed.

Lemma big_box_skew2 R (idx : R) (op : Monoid.com_law idx) (f : nat -> nat -> R):
  \big[op/idx]_(b : box_skew) f b.1 b.2 =
  \big[op/idx]_(b <- enum_box_skew) f b.1 b.2.
Proof using. exact: big_box_skew. Qed.

Lemma big_enum_box_skew
      (R : Type) (idx : R) (op : Monoid.law idx) (f : nat -> nat -> R):
  \big[op/idx]_(b <- enum_box_skew) f b.1 b.2 =
  \big[op/idx]_(0 <= r < size outer)
   \big[op/idx]_(nth 0 inner r <= c < nth 0 outer r) f r c.
Proof using.
rewrite /enum_box_skew.
rewrite big_flatten /index_iota big_map !subn0; apply eq_bigr => r _.
by rewrite big_map; apply eq_bigr.
Qed.

End BoxInSkew.
#[export] Hint Resolve box_skewP : core.

Notation box_in := (box_skew [::]).
Notation enum_box_in := (enum_box_skew [::]).

Lemma BoxIn_subproof sh rc : in_shape sh rc -> in_skew [::] sh rc.
Proof. by rewrite in_skewE in_shape_nil. Qed.
Definition BoxIn sh rc (rc_sh : in_shape sh rc) : box_in sh :=
  BoxSkew (BoxIn_subproof rc_sh).

Lemma box_inP sh (rc : box_in sh) : in_shape sh rc.
Proof using. exact: in_skew_out. Qed.

Lemma big_enum_box_in sh
      (R : Type) (idx : R) (op : Monoid.law idx) (f : nat -> nat -> R):
  \big[op/idx]_(b <- enum_box_in sh ) f b.1 b.2 =
  \big[op/idx]_(0 <= r < size sh)
   \big[op/idx]_(0 <= c < nth 0 sh r) f r c.
Proof using.
by rewrite big_enum_box_skew; apply eq_bigr => i _; rewrite nth_nil.
Qed.

Lemma card_box_in sh : #|{: box_in sh}| = sumn sh.
Proof using. by rewrite card_box_skew; case: sh. Qed.

Lemma enum_box_in_uniq sh : uniq (enum_box_in sh).
Proof using. exact: enum_box_skew_uniq. Qed.

Lemma mem_enum_box_in sh : enum_box_in sh =i in_shape sh.
Proof.
move=> rc; rewrite mem_enum_box_skew.
by rewrite !unfold_in -/(in_skew [::] _ rc) in_skewE in_shape_nil /=.
Qed.


(** ** Adding a box to a shape *)
Lemma box_in_incr_nth sh i :
  perm_eq ((i, nth 0 sh i) :: enum_box_in sh) (enum_box_in (incr_nth sh i)).
Proof.
apply uniq_perm.
- rewrite /= enum_box_skew_uniq andbT mem_enum_box_skew unfold_in.
  by rewrite /= nth_nil leq0n ltnn.
- exact: enum_box_skew_uniq.
- move=> [r c]; rewrite !inE !mem_enum_box_skew !unfold_in /in_shape nth_nil /=.
  apply/idP/idP => [/orP[/eqP [-> ->]|] | ].
    * by rewrite nth_incr_nth eq_refl add1n ltnS.
    * move => /leq_trans; apply.
      by rewrite nth_incr_nth; exact: leq_addl.
  + rewrite nth_incr_nth xpair_eqE eq_sym.
    case: eqP => [-> {r} | Hri] /=; last by rewrite add0n.
    by rewrite add1n ltnS leq_eqVlt.
Qed.


(** * The union of two integer partitions *)

Lemma merge_is_part l k :
  is_part l -> is_part k -> is_part (merge geq l k).
Proof.
rewrite !is_part_sortedE => /andP[sortl l0] /andP[sortk k0].
apply/andP; split; first exact: merge_sorted.
by rewrite mem_merge mem_cat negb_or l0 k0.
Qed.

Lemma merge_sortedE l k :
  is_part l -> is_part k -> merge geq l k = sort geq (l ++ k).
Proof.
rewrite !is_part_sortedE => /andP[sortl _] /andP[sortk _].
apply (sorted_eq (leT := geq)) => //.
- apply: merge_sorted => //.
- exact: sort_sorted.
- by rewrite perm_merge perm_sym perm_sort.
Qed.

Lemma sumn_union_part l k : sumn (merge geq l k) = sumn l + sumn k.
Proof.
have:= perm_merge geq l k => /permPl/perm_sumn ->.
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
apply (perm_trans (y := l ++ (k ++ j))).
- by rewrite perm_cat2l perm_sort.
- apply (perm_trans (y := (k ++ l) ++ j)).
  + by rewrite catA perm_cat2r perm_catC.
  + by rewrite perm_cat2r perm_sym perm_sort.
Qed.

Section UnionPart.

Variables (m n : nat) (l : 'P_m) (k : 'P_n).

Lemma union_intpartn_subproof : is_part_of_n (m + n) (merge geq l k).
Proof.
apply /andP; split.
- by rewrite sumn_union_part !sumn_intpartn.
- exact: merge_is_part.
Qed.
Definition union_intpartn := IntPartN union_intpartn_subproof.

Lemma union_intpartnE : val union_intpartn = sort geq (l ++ k).
Proof. by rewrite /= merge_sortedE. Qed.

Lemma perm_union_intpartn : perm_eq union_intpartn (l ++ k).
Proof. by rewrite /= perm_merge. Qed.

End UnionPart.

Notation "a +|+ b" := (union_intpartn a b) (at level 50) : Combi_scope.
Bind Scope Combi_scope with intpartn.


Section IntpartnCons.

Import LeqGeqOrder.

Variables (d l0 : nat) (la : seq nat).
Hypotheses (Hla : is_part_of_n d la)
           (Hlla : is_part_of_n (l0 + d)%N (l0 :: la)).

Lemma intpartn_cons : IntPartN Hlla = rowpartn l0 +|+ IntPartN Hla.
Proof.
apply val_inj; rewrite union_intpartnE /= rowpartnE.
move: Hlla => /andP[_] Hpart.
have:= part_head_non0 Hpart => /=.
move: Hpart; rewrite is_part_sortedE => /andP[Hsort _].
case: l0 Hsort => // l Hsort _.
apply (sorted_eq (leT := geq)) => //; first exact: sort_sorted.
by rewrite perm_sym perm_sort.
Qed.

End IntpartnCons.


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

#[export] Hint Resolve partdom_nil partdom_refl : core.

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

Lemma partdom_consK x s1 s2 : partdom (x :: s1) (x :: s2) -> partdom s1 s2.
Proof.
rewrite /partdom partdomsh_cons2 add0n leqnn /=.
by rewrite -(addn0 x) partdomsh_add.
Qed.

Lemma sumn_take_merge t x i :
  is_part t ->
  sumn (take i.+1 (merge geq [:: x] t)) =
  maxn (sumn (take i.+1 t)) (x + sumn (take i t)).
Proof.
elim: t i => /= [i _| t0 t IHt i /andP[Hhead Hpart]].
  by rewrite addn0 max0n.
case: (leqP t0 x) => [/maxn_idPr Hxt0 | /ltnW /maxn_idPl Hxt0];
  case: i => [|i]; rewrite /= ?take0 /= ?addn0 ?Hxt0 //.
- rewrite {IHt} [x + (t0 + _)]addnC -addnA -addn_maxr [_ + x]addnC.
  congr (t0 + _); apply esym; apply/maxn_idPr.
  move: Hxt0 => /maxn_idPr/(leq_trans Hhead).
  elim: t i Hpart {Hhead t0} =>
     [i _ _| t0 t IHt [|i] /andP[Hhead Hpart] /= Ht0] //=.
  + by rewrite take0 !addn0.
  + rewrite [x + (t0 + _)]addnC -addnA leq_add2l addnC.
    exact: (IHt i Hpart (leq_trans Hhead Ht0)).
- move/(_ _ Hpart) : IHt => /= ->.
  by rewrite [x + (t0 + _)]addnC -addnA -addn_maxr [_ + x]addnC.
Qed.

Lemma merge_cons x s t :
  is_part (x :: s) -> is_part t ->
  merge geq (x :: s) t = merge geq [:: x] (merge geq s t).
Proof.
move=> Hxs Ht.
have Hs := is_part_consK Hxs.
have Hx : is_part [:: x] by rewrite /= lt0n (part_head_non0 Hxs).
rewrite (merge_sortedE Hxs Ht) (merge_sortedE Hx) ?merge_is_part //=.
apply (sorted_eq (leT := geq)) => //; try exact: sort_sorted.
by rewrite perm_sort perm_sym perm_sort perm_cons perm_merge.
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
Section IntPartNDom.

Variable d : nat.
Definition intpartndom := 'P_d.
Local Notation "'PDom" := intpartndom.
Implicit Type (sh : 'PDom).

Fact partdom_antisym : antisymmetric (fun x y : 'P_d => partdom x y).
Proof.
by move=> x y /andP[Hxy Hyx]; apply val_inj => /=; apply: partdom_anti.
Qed.

Definition porderMixin :=
  LePOrderMixin (le := fun x y : 'PDom => partdom x y)
                (fun _ _ => erefl _) partdom_refl partdom_antisym partdom_trans.

Lemma partdom_display : unit. Proof. exact: tt. Qed.
Canonical porderType :=
  POrderType partdom_display 'PDom porderMixin.
Canonical finPOrderType := Eval hnf in [finPOrderType of 'PDom].
Canonical inhType := InhType 'PDom (InhMixin (rowpartn d)).
Canonical inhPOrderType := Eval hnf in [inhPOrderType of 'PDom].
Canonical inhFinPOrderType := Eval hnf in [inhFinPOrderType of 'PDom].

Lemma leEpartdom : @Order.le partdom_display porderType = partdom.
Proof. by []. Qed.

Local Notation "sh '^#'" := (conj_intpartn sh : 'PDom)
                              (at level 10, format "sh '^#'").

Lemma sum_diff sh i :
  \sum_(l <- sh) (l - i) = \sum_(l <- take (nth 0 (conj_part sh) i) sh) (l - i).
Proof.
set c := nth 0 (conj_part sh) i.
rewrite -{1}(cat_take_drop c sh) !big_cat /=.
rewrite [X in _ + X]big_seq [X in _ + X]big1 ?addn0 // => /= j jin.
rewrite -(nth_index 0 jin) nth_drop.
apply/eqP; rewrite subn_eq0.
by rewrite conj_leqE // /c leq_addr.
Qed.

Lemma partdom_conj_intpartn sh1 sh2 : (sh2^# <= sh1^#)%O = (sh1 <= sh2)%O.
Proof.
suff {sh1 sh2} decr sh1 sh2 : (sh1 <= sh2)%O -> (sh2^# <= sh1^#)%O.
  by apply/idP/idP => /decr //; rewrite !conj_intpartnK.
move => /partdomP Hdom; apply/partdomP => i.
rewrite -!sum_conj.
rewrite !sum_minn !sumn_intpartn; apply: leq_sub => //.
pose c1 := nth 0 (conj_part sh1) i.
have Hc1 : c1 <= size sh1 by rewrite /c1 -conj_leqE // nth_default.
have -> : \sum_(l <- sh1) (l - i) = \sum_(l <- take c1 sh1) (l - i).
  rewrite -{1}(cat_take_drop c1 sh1) !big_cat /=.
  rewrite [X in _ + X]big_seq [X in _ + X]big1 ?addn0 // => /= j jin.
  rewrite -(nth_index 0 jin) nth_drop.
  apply/eqP; rewrite subn_eq0.
  by rewrite conj_leqE // leq_addr.
rewrite -(leq_add2r (c1 * i)) -{2}(size_takel Hc1) -sum1_size.
rewrite big_distrl -big_split /=.
rewrite big_seq [X in X <= _](eq_bigr id) -?big_seq; first last.
  move=> j /(mem_takeP 0) [pos Hpos ->{j}].
  rewrite mul1n; apply: subnK.
  apply ltnW; rewrite conj_ltnE // -/c1.
  exact: (leq_trans Hpos (geq_minl _ _)).
move/(_  c1): Hdom; rewrite !sumnE => /leq_trans; apply.
rewrite -{2}(cat_take_drop c1 sh2) !big_cat /= addnC addnA.
apply: (leq_trans _ (leq_addr _ _)); rewrite -sumnE sumn_take.
rewrite [X in _ <= X](_ : _ = \sum_(0 <= i0 < c1) maxn i (nth 0 sh2 i0)).
  by apply leq_sum => j _; apply leq_maxr.
rewrite sum_take ?sub0n //.
rewrite -{1}(subn0 c1) -sum_nat_const_nat.
rewrite -big_split; apply eq_bigr => /= j _.
by rewrite maxnE.
Qed.

Lemma take_intpartn_over sh i : d <= i -> take i sh = sh.
Proof.
move=> Hd; rewrite take_oversize // (leq_trans _ Hd) //.
by rewrite -{2}(sumn_intpartn sh) size_part.
Qed.

Implicit Type t : d.+1.-tuple nat.

Definition parttuple sh := [tuple sumn (take i sh) | i < d.+1].
Definition from_parttuple t :=
  rem_trail0 [seq nth 0 t i.+1 - nth 0 t i | i <- iota 0 d].
Definition is_parttuple t :=
  [&& tnth t ord0 == 0, tnth t ord_max == d, sorted leq t &
      all (fun i => (nth 0 t i).*2 >= nth 0 t i.-1 + nth 0 t i.+1)
          (iota 1 d.-1)].

Lemma is_parttupleP t :
  reflect
    [/\ tnth t ord0 = 0, tnth t ord_max = d, sorted leq t &
      forall i, 0 < i < d -> (nth 0 t i).*2 >= nth 0 t i.-1 + nth 0 t i.+1]
    (is_parttuple t).
Proof.
apply (iffP and4P) => [[/eqP->/eqP->->/allP Hall] | [->->-> Hall]].
  split=> // i Hi; apply: Hall; rewrite mem_iota add1n.
  by case: d {t} i Hi => [] [|].
split => //; apply/allP => i; rewrite mem_iota add1n => Hi; apply: Hall.
  by case: d {t} i Hi => [] [|].
Qed.

Lemma nth_parttuple i sh :
  i < d.+1 -> nth 0 (parttuple sh) i = sumn (take i sh).
Proof.
by move=> ltid1; rewrite (nth_map ord0) ?size_enum_ord ?nth_enum_ord.
Qed.

Lemma parttupleP sh : is_parttuple (parttuple sh).
Proof.
apply/is_parttupleP; split.
- by rewrite tnth_mktuple /= take0.
- by rewrite tnth_mktuple take_intpartn_over // sumn_intpartn.
- apply/(sorted1P 0) => i; rewrite size_tuple => ltid.
  rewrite !nth_parttuple //; last exact: ltnW.
  case: (ltnP i (size sh)) => Hi.
    by rewrite (take_nth 0) // sumn_rcons leq_addr.
  by rewrite !take_oversize // (leq_trans Hi).
- move=> [|i]// /andP[_ ltid].
  rewrite !nth_parttuple /= ?ltnS //=; try exact: ltnW; first last.
    by apply ltnW; apply ltnW.
  rewrite -addnn !sumn_take !big_nat_recr //= -!addnA leq_add2l.
  rewrite [X in _ <= X]addnC addnA leq_add2l.
  by have /is_partP [_] : is_part sh by [].
Qed.

Lemma sum_diff_tuple t :
  sorted leq t ->
  forall i, i < d.+1 ->
    \sum_(0 <= j < i) (nth 0 t j.+1 - nth 0 t j) = nth 0 t i - nth 0 t 0.
Proof.
move=> /(sortedP 0 leq_trans leqnn) srt.
elim=> [|i IHi] ltid; first by rewrite big_nil subnn.
rewrite big_nat_recr //= IHi; last exact: ltnW.
rewrite addnC addnBA ?srt ?size_tuple //=; last exact: ltnW.
by rewrite subnK // srt // size_tuple leqnSn.
Qed.

Lemma from_parttupleP t : is_parttuple t -> is_part_of_n d (from_parttuple t).
Proof.
move=> /is_parttupleP [t0 td srt conv].
have {}t0 : nth 0 t 0 = 0 by move: t0; rewrite (tnth_nth 0).
have {}td : nth 0 t d = d by move: td; rewrite (tnth_nth 0).
apply/andP; split.
  rewrite sumn_rem_trail0 sumnE big_map.
  by rewrite -{1}(subn0 d) -/(index_iota _ _) sum_diff_tuple // t0 td subn0.
move: srt => /sorted1P srt.
apply: is_part_rem_trail0; apply/(sorted1P 0) => i /=.
rewrite size_map size_iota => H1.
have Hi1 : i.+1 < d.+1 by apply ltnW.
rewrite !(nth_map 0) ?size_iota ?nth_iota // add0n.
rewrite leq_subLR addnBA ?srt ?size_tuple // add0n addnn.
rewrite leq_subRL ?conv // -addnn.
apply: (leq_trans (srt _ _ _) (leq_addr _ _)).
by rewrite size_tuple.
Qed.
Definition part_fromtuple t (H : is_parttuple t) :=
  IntPartN (from_parttupleP H).

Lemma sumn_take_part_fromtuple t (H : is_parttuple t) i :
  i < d.+1 -> sumn (take i (part_fromtuple H)) = nth 0 t i.
Proof.
rewrite /part_fromtuple /from_parttuple /= => Hi.
move/is_parttupleP : H => [t0 _ srt _].
have {}t0 : nth 0 t 0 = 0 by move: t0; rewrite (tnth_nth 0).
rewrite sumn_take big_nat.
under eq_bigr => j /= Hj.
  have lejd : j < d by rewrite (leq_trans Hj) // -ltnS.
  by rewrite nth_rem_trail0 (nth_map 0) ?size_iota // nth_iota // over.
by rewrite -big_nat sum_diff_tuple // t0 subn0.
Qed.
Lemma from_parttupleK t (H : is_parttuple t) :
  parttuple (part_fromtuple H) = t.
Proof.
apply eq_from_tnth => i.
by rewrite tnth_mktuple sumn_take_part_fromtuple // (tnth_nth 0).
Qed.

Lemma parttupleK sh : from_parttuple (parttuple sh) = sh.
Proof.
have /andP[/eqP Hsum Hpart] := from_parttupleP (parttupleP sh).
apply: sumn_take_inj => // k.
case: (ltnP k d.+1) => [ltkd1 | /ltnW ltdk].
  have /= -> := sumn_take_part_fromtuple (parttupleP sh) ltkd1.
  by rewrite (nth_map ord0) ?size_enum_ord // nth_enum_ord.
rewrite take_intpartn_over //.
rewrite !take_oversize ?Hsum /= -?{1}(sumn_intpartn sh) //.
by apply: (leq_trans _ ltdk); rewrite -Hsum size_part.
Qed.
Lemma parttuplePK sh : part_fromtuple (parttupleP sh) = sh.
Proof. by apply val_inj; rewrite /= parttupleK. Qed.

Definition parttuple_minn sh1 sh2 :=
  [tuple minn (tnth (parttuple sh1) i) (tnth (parttuple sh2) i) | i < d.+1].

Lemma parttuple_minnC sh1 sh2 :
  parttuple_minn sh1 sh2 = parttuple_minn sh2 sh1.
Proof. by apply eq_from_tnth => i; rewrite !tnth_mktuple minnC. Qed.

Lemma nth_parttuple_minn i sh1 sh2 :
  i < d.+1 -> nth 0 (parttuple_minn sh1 sh2) i =
              minn (sumn (take i sh1)) (sumn (take i sh2)).
Proof.
move=> ltid1.
by rewrite -/(nat_of_ord (Ordinal ltid1)) nth_mktuple !tnth_mktuple /=.
Qed.

Lemma double_minn m n : (minn m n).*2 = minn m.*2 n.*2.
Proof. by rewrite /minn ltn_double; case: ltnP. Qed.

Lemma parttuple_minnP sh1 sh2 : is_parttuple (parttuple_minn sh1 sh2).
Proof.
have /is_parttupleP [t10 t1d /(sorted1P 0) sort1 conv1] := parttupleP sh1.
have /is_parttupleP [t20 t2d /(sorted1P 0) sort2 conv2] := parttupleP sh2.
rewrite size_tuple in sort1; rewrite size_tuple in sort2.
apply/is_parttupleP; split.
- by rewrite !tnth_mktuple /= !take0.
- by rewrite tnth_mktuple t1d t2d minnn.
- apply/(sorted1P 0) => i {conv1 conv2}; rewrite size_tuple => lti1d1.
  have ltid1 : i < d.+1 by apply: ltnW.
  move: sort2 => /(_ _ lti1d1); move: sort1 => /(_ _ lti1d1).
  rewrite !nth_parttuple_minn // !nth_parttuple // !leq_min !geq_min => -> ->.
  by rewrite orbT.
- move=> i Hi; move: conv2 => /(_ _ Hi); move: conv1 => /(_ _ Hi).
  case: i Hi => [|i]// /andP[_]; rewrite -ltnS => lti2d1.
  have lti1d1 : i.+1 < d.+1 by apply: ltnW.
  have ltid1  : i    < d.+1 by apply: ltnW.
  rewrite !nth_parttuple_minn // !nth_parttuple //= => conv1 conv2.
  rewrite double_minn !leq_min; apply/andP; split.
  - by apply: (leq_trans (leq_add _ _) conv1); apply: geq_minl.
  - by apply: (leq_trans (leq_add _ _) conv2); apply: geq_minr.
Qed.
Definition inf_intpartn sh1 sh2 : 'PDom :=
  IntPartN (from_parttupleP (parttuple_minnP sh1 sh2)).
Definition sup_intpartn sh1 sh2 := (inf_intpartn (sh1^#) (sh2^#))^#.

Lemma inf_intpartnC sh1 sh2 : inf_intpartn sh1 sh2 = inf_intpartn sh2 sh1.
Proof. by apply val_inj; rewrite /= parttuple_minnC. Qed.

Lemma le_inf_intpartn sh1 sh2 : (inf_intpartn sh1 sh2 <= sh1)%O.
Proof.
apply/partdomP => i; case: (ltnP i d.+1) => [Hi| /ltnW Hi].
  by rewrite sumn_take_part_fromtuple // nth_parttuple_minn // geq_minl.
by rewrite !take_intpartn_over // !sumn_intpartn.
Qed.


Lemma inf_intpartnP sh sh1 sh2 :
  (sh <= inf_intpartn sh1 sh2)%O = (sh <= sh1)%O && (sh <= sh2)%O.
Proof.
apply/idP/andP => [Hinf | [/partdomP H1 /partdomP H2]].
  split; apply: (le_trans Hinf); first exact: le_inf_intpartn.
  by rewrite inf_intpartnC le_inf_intpartn.
apply/partdomP => i.
case: (ltnP i d.+1) => [Hi | /ltnW Hi]; first last.
  by rewrite !take_intpartn_over // !sumn_intpartn.
rewrite sumn_take_part_fromtuple // nth_parttuple_minn //.
by rewrite leq_min H1 H2.
Qed.
Lemma sup_intpartnP sh1 sh2 sh :
  (sup_intpartn sh1 sh2 <= sh)%O = (sh1 <= sh)%O && (sh2 <= sh)%O.
Proof.
rewrite /sup_intpartn /= -{1}(conj_intpartnK sh).
by rewrite partdom_conj_intpartn inf_intpartnP !partdom_conj_intpartn.
Qed.

Definition latticeMixin :=
  MeetJoinLeMixin inf_intpartnP sup_intpartnP.
Canonical latticeType := LatticeType 'PDom latticeMixin.

End IntPartNDom.

Section IntPartNTopBottom.

Variable d : nat.
Local Notation "'PDom" := (intpartndom d).
Implicit Type (sh : 'PDom).

Lemma partdom_rowpartn sh : (sh <= rowpartn d)%O.
Proof.
apply/partdomP.
case: d sh => [|d1] sh; first by rewrite /= !val_intpartn0.
case=> [|i] /=; rewrite ?take0 ?addn0 //.
rewrite rowpartnSE /= addn0 -{2}(sumn_intpartn sh).
by rewrite -{2}(cat_take_drop i.+1 sh) sumn_cat leq_addr.
Qed.

Lemma partdom_colpartn sh : (colpartn d <= sh :> 'PDom)%O.
Proof. by rewrite -partdom_conj_intpartn conj_colpartn partdom_rowpartn. Qed.

Definition bottomMixin := BottomMixin partdom_colpartn.
Canonical bLatticeType := BLatticeType 'PDom bottomMixin.
Definition topMixin := TopMixin partdom_rowpartn.
Canonical tbLatticeType := TBLatticeType 'PDom topMixin.
Canonical finLatticeType := Eval hnf in [finLatticeType of 'PDom].

Lemma botEintpartndom : 0%O = colpartn d :> 'PDom.
Proof. by []. Qed.
Lemma topEintpartndom : 1%O = rowpartn d :> 'PDom.
Proof. by []. Qed.


End IntPartNTopBottom.

Module Exports.

Notation "''PDom_' n" := (intpartndom n).
Set Warnings "-redundant-canonical-projection".
Canonical porderType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tbLatticeType.
Canonical finPOrderType.
Canonical finLatticeType.
Canonical inhType.
Canonical inhPOrderType.
Canonical inhFinPOrderType.
Set Warnings "+redundant-canonical-projection".

Definition leEpartdom := @leEpartdom.
Definition partdom_conj_intpartn := @partdom_conj_intpartn.
Definition botEintpartndom := @botEintpartndom.
Definition topEintpartndom := @topEintpartndom.

End Exports.
End IntPartNDom.
Export IntPartNDom.Exports.


Lemma le_intpartndomlexi d :
  {homo (id : 'PDom_d -> 'PLexi_d) : x y / (x <= y)%O}.
Proof.
move=> sh1 sh2.
rewrite leEpartdom leEintpartnlexi leEseqlexi.
case: sh1 => [sh1 /andP[/eqP Hsum1 Hpart1]] /=.
case: sh2 => [sh2 /andP[/eqP Hsum2 Hpart2]] /=.
move: Hsum1; rewrite -{}Hsum2.
elim: sh1 Hpart1 sh2 Hpart2 => [|s01 sh1 IHsh] Hpart1 sh2 Hpart2.
  by move/esym/(part0 Hpart2) => ->.
case: sh2 Hpart2 => [|s02 sh2] Hpart2 //=.
  move: Hpart1 => /part_head_non0 /= /negbTE H0 /eqP.
  by rewrite addn_eq0 H0.
move: Hpart1 => /= /andP[_ Hpart1].
move: Hpart2 => /= /andP[_ Hpart2].
move=> Hsum Hdom.
have /partdomP/(_ 1) := Hdom; rewrite /= !take0 /= !addn0 => les0.
rewrite !leEnat les0 /= leqNgt.
move: les0; rewrite leq_eqVlt => /orP [/eqP Heq|->]//.
subst s02; rewrite ltnn /= leEseqlexi; apply: IHsh => //.
  by move: Hsum => /eqP; rewrite eqn_add2l => /eqP.
exact: (partdom_consK Hdom).
Qed.
Lemma lt_intpartndomlexi d :
  {homo (id : 'PDom_d -> 'PLexi_d) : x y / (x < y)%O}.
Proof. by move=> sh1 sh2; rewrite !lt_def=> /andP[-> /le_intpartndomlexi]. Qed.


(** * Shape of set partitions and integer partitions *)
Section SetPartitionShape.

Variable T : finType.
Implicit Types (A B X : {set T}) (P Q : {set {set T}}).

Lemma count_set_of_card (p : pred nat) P :
  count p [seq #{x} | x in P] = #|P :&: [set x | p #{x}]|.
Proof using.
rewrite cardE -size_filter /enum_mem -enumT /=.
rewrite filter_map size_map; congr size.
rewrite -filter_predI -enumT /=; apply eq_filter.
by move=> S; rewrite !inE andbC.
Qed.

Definition setpart_shape P := sort geq [seq #{X} | X in P].

Lemma setpart_shapeP P D :
  partition P D -> is_part_of_n #|D| (setpart_shape P).
Proof using.
rewrite /setpart_shape => /and3P [/eqP Hcov Htriv Hnon0].
rewrite /is_part_of_n /= is_part_sortedE.
apply/and3P; split.
- by rewrite sumn_sort sumnE big_map big_enum -Hcov.
- exact: sort_sorted.
- move: Hnon0; apply contra.
  rewrite mem_sort => /mapP [x].
  by rewrite mem_enum => Hx /esym/cards0_eq <-.
Qed.

Lemma ex_subset_card B k :
 k <= #{B} -> exists2 A : {set T}, A \subset B & #{A} == k.
Proof using.
rewrite -bin_gt0 -(cards_draws B k) card_gt0 => /set0Pn [x].
by rewrite inE => /andP[H1 H2]; exists x.
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

Lemma ex_set_setpart_shape A (sh : 'P_#|A|) :
  exists2 P, partition P A & setpart_shape P = sh.
Proof using.
case: sh => sh.
rewrite /is_part_of_n /= is_part_sortedE => /andP[/eqP shsum /andP[shsort]].
move=> /(ex_setpart_shape shsum) [P [Puniq Ppart Psh]].
exists [set X in P]; first exact: Ppart.
apply (sorted_eq (leT := geq)) => //.
- exact: sort_sorted.
- rewrite /setpart_shape -Psh perm_sort; apply: perm_map.
  apply: (uniq_perm (enum_uniq [set X in P]) Puniq) => x.
  by rewrite mem_enum inE.
Qed.

Lemma setpart_shape_union P Q :
  [disjoint P & Q] ->
  setpart_shape (P :|: Q) = sort geq (setpart_shape P ++ setpart_shape Q).
Proof using.
rewrite /setpart_shape -setI_eq0 => /eqP disj.
apply/perm_sortP/permP => // Prd.
have count_sort l : count ^~ (sort geq l) =1 count ^~ l.
  by apply/permP; rewrite perm_sort perm_refl.
rewrite count_cat !count_sort !count_set_of_card.
rewrite setIUl cardsU -[RHS]subn0; congr(_ - _).
apply/eqP; rewrite cards_eq0 -subset0 -disj.
by apply/subsetP => x; rewrite !inE => /andP[/andP[-> _] /andP[-> _]].
Qed.

End SetPartitionShape.

Lemma setpart_shape_imset
      (T1 T2 : finType) (f : T1 -> T2) (A : {set {set T1}}) :
  injective f ->
  setpart_shape [set f @: x | x : {set T1} in A] = setpart_shape A.
Proof using.
rewrite /setpart_shape /= => Hinj.
apply/perm_sortP/permP => // P.
rewrite !count_set_of_card -(card_imset _ (imset_inj Hinj)).
rewrite imsetI; last by move=> B C _ _; exact: imset_inj.
congr #{_}; apply/setP => S; rewrite !inE.
case: (boolP (S \in (imset _ _))) => //= /imsetP [U _ -> {S}].
rewrite (card_imset _ Hinj).
apply/idP/imsetP => [| [V]].
- by exists U; rewrite // inE.
- by rewrite inE => HP /(imset_inj Hinj) ->.
Qed.
