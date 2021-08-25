(** * Combi.Combi.bintree : Binary Trees *)
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
(** * Binary Trees

A _binary tree_ is a rooted tree such that each node has two distiguished,
children the left one and the right one. The main goal of this file is to
construct the Tamari lattice which is the transitive closure of the directed
graph of left rotation. We show that it is indeed a lattice.

Basic definitions:

- [bintree] == the type of binary trees this is canonically a [countType]
- [BinLeaf] == the leaf for binary trees
- [BinNode left right] == the binary tree with subtrees [left] [right]

Binary trees of size n:

- [size_tree t] == the number of node of the tree [t]
- [enum_bintreesz n] == the list of a trees of size [n]
- [bintreesz n] == the Sigma type for trees of size [n]. This is
        canonically a [finType] with enumeration [enum_bintreesz n]
- [Catalan_bin n] == Catalan number defined using the binary tree recursion:
        [C_0 = 1] and [C_{n+1} = sum__(i+j = n) C_i C_j]. We show that they
        count the number of binary trees of size [n]. The binomial formula
        will be proved using Dyck word.

Left branch surgery:

- [left_branch t] == the sequence of the right subtrees of the nodes
        starting for the root of [t] and going only left
- [from_left s] == the tree whose left branch is [s]
- [cat_left t1 t2] == the tree whose left branch is the concatenation of
        the left branches of [t1] and [t2]

- [rightcomb n] == the right comb binary tree of size [n] as a [bintree]
- [leftcomb n] == the left comb binary tree of size [n] as a [bintree]
- [flip t] == the left/right mirror of [t]
- [rightcombsz n] == the right comb binary tree of size [n] as a [bintreesz n]
- [leftcombsz n] == the left comb binary tree of size [n] as a [bintreesz n]
- [flipsz t] == the left/right mirror of [t] as a [bintreesz n]

Rotations and Tamari order:

- [rotations t] == the list of right rotations of the tree [t]
- [rightsizesum t] == the sum over all nodes [n] of [t] of the size of the
        right subtree of [n]
- [t1 <=T t2] == [t1] is smaller than [t2] in the Tamari order

Tamari bracketing vectors:

- [right_sizes t] == the sequence in infix order reading of the node of [t]
        of the the sizes of the right subtrees
- [from_vct vct] == recovers the tree [t] from its right sizes vector.
- [v \is a TamariVector] == [v] is the right sizes vector of some tree [t].
        The characterization of a Tamari vector of size [n] is that
        for all [i < n] then [v_i + 1 < n] and
        for all [j] such that [i < j <= v_i + i] then [v_j + j <= v_i + i].
The function [right_sizes] and [from_vct] are two inverse bijection from
binary trees to Tamari vectors as stated in theorems [right_sizesK],
[right_sizesP] and [from_vctK].

- [vctleq v1 v2] = [v1 <=V v2] == [v1] and [v2] are of the same lenght
        and [v1] is smaller than [v2] componentwise (ie. for all [i] then
        [v1_i <= v2_i]
- [vctmin v1 v2] == the componentwise min of [v1] and [v2]

Tamari Lattice:

- [t1 \/T t2] == the meet of [t1] and [t2] in the Tamari lattice.
- [t1 /\T t2] == the join of [t1] and [t2] in the Tamari lattice.
 *********************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun bigop ssrnat eqtype fintype choice seq.
From mathcomp Require Import fingraph path finset order.

Require Import tools combclass lattice ordtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.


Reserved Notation "x '<=T' y" (at level 70, y at next level).
Reserved Notation "x '<T' y"  (at level 70, y at next level).
Reserved Notation "x '/\T' y" (at level 70, y at next level).
Reserved Notation "x '\/T' y" (at level 70, y at next level).


(** * Inductive type for binary trees *)
Inductive bintree : predArgType :=
  | BinLeaf  : bintree
  | BinNode  : bintree -> bintree -> bintree.

Fixpoint eq_bintree (b1 b2 : bintree) : bool :=
  match b1, b2 with
  | BinLeaf, BinLeaf => true
  | BinNode l1 r1, BinNode l2 r2 => eq_bintree l1 l2 && eq_bintree r1 r2
  | _, _ => false
  end.

Lemma eq_bintreeP : Equality.axiom eq_bintree.
Proof.
move=> t1 t2; apply: (iffP idP) => [|<-]; last by elim: t1 => //= r -> l ->.
elim: t1 t2 => [|l1 IHl r1 IHr]; first by case.
by case => //= [l2 r2] /andP [] Hr Hl; rewrite (IHl _ Hr)  (IHr _ Hl).
Qed.

Definition bintree_eqMixin := EqMixin eq_bintreeP.
Canonical bintree_eqType := Eval hnf in EqType bintree bintree_eqMixin.

Fixpoint tree_encode (t : bintree) : GenTree.tree unit :=
  match t with
  | BinLeaf  => GenTree.Leaf tt
  | BinNode tl tr => GenTree.Node 2 [:: tree_encode tl; tree_encode tr]
  end.
Fixpoint tree_decode (gt : GenTree.tree unit) :=
  match gt with
  | GenTree.Leaf tt => BinLeaf
  | GenTree.Node 2 [:: tl; tr] => BinNode (tree_decode tl) (tree_decode tr)
  | _ => BinLeaf       (** unused case *)
  end.

Lemma tree_encodeK : cancel tree_encode tree_decode.
Proof. by elim=> [// | //= tl -> tr ->]. Qed.

Definition bintree_choiceMixin := CanChoiceMixin tree_encodeK.
Canonical bintree_choiceType :=
  Eval hnf in ChoiceType bintree bintree_choiceMixin.
Definition bintree_countMixin := CanCountMixin tree_encodeK.
Canonical bintree_countType :=
  Eval hnf in CountType bintree bintree_countMixin.

Fixpoint size_tree t :=
  match t with
  | BinLeaf => 0
  | BinNode l r => 1 + (size_tree l) + (size_tree r)
  end.

Lemma LeafP t : reflect (t = BinLeaf) (size_tree t == 0).
Proof. by case: t => [|l r]; constructor. Qed.
Lemma size_tree_eq0 t : (size_tree t == 0) = (t == BinLeaf).
Proof. by case: t. Qed.

Section Size.

Variable (n : nat).

Structure bintreesz : predArgType :=
  BinTreeSZ {trval :> bintree; _ : size_tree trval == n}.
Canonical bintreesz_subType := Eval hnf in [subType for trval].
Definition bintreesz_eqMixin := [eqMixin of bintreesz by <:].
Canonical bintreesz_eqType := Eval hnf in EqType bintreesz bintreesz_eqMixin.
Definition bintreesz_choiceMixin := [choiceMixin of bintreesz by <:].
Canonical bintreesz_choiceType :=
  Eval hnf in ChoiceType bintreesz bintreesz_choiceMixin.
Definition bintreesz_countMixin := [countMixin of bintreesz by <:].
Canonical bintreesz_countType :=
  Eval hnf in CountType bintreesz bintreesz_countMixin.

Lemma bintreeszP (t : bintreesz) : size_tree t = n.
Proof. by case: t => t /= /eqP. Qed.

End Size.

(** ** Catalan numbers *)

(** The intent of the two following recursive definition is the recursion of lemmas
    [CatalanS] and [enum_bintreeszS]:
[[
Fixpoint Catalan n :=
  if n is n'.+1 then
    sumn [Catalan i * Catalan (n - i) | i <- iota 0 n.+1]
  else 1.
]]
however [i] and [n - i] are not structurally smaller than [n.+1] so the
definition is refused by coq as not well founded. So we write the following
functions which returns a cache containing the list of the results of
[Catalan i] and [enum_bintreesz i] for [i = 0 ... n]. Otherwise said, to define
the [enum_bintreesz] function we need a strong [nat] induction where Coq only
allows simple [nat] induction. *)


(** A seq of size n.+1 whose i-th element is Catalan i *)
Fixpoint Catalan_bin_leq n :=
  if n is n.+1 then
    let cr := Catalan_bin_leq n in
    let new := sumn [seq nth 0 cr i * nth 0 cr (n - i) | i <- iota 0 n.+1]
    in rcons cr new
  else [:: 1].
Definition Catalan_bin n := last 0 (Catalan_bin_leq n).

(** A seq of size n.+1 whose i-th element contains the list of all binary trees of
    size i *)
Fixpoint enum_bintreesz_leq n :=
  if n is n'.+1 then
    let rec := enum_bintreesz_leq n' in
    let listn :=
        flatten [seq [seq BinNode tl tr |
                      tl <- nth [::] rec i,
                      tr <- nth [::] rec (n' - i)] | i <- iota 0 n'.+1]
    in rcons rec listn
  else [:: [:: BinLeaf]].
Definition enum_bintreesz n := last [::] (enum_bintreesz_leq n).

Goal [seq Catalan_bin n | n <- iota 0 10] =
     [:: 1; 1; 2; 5; 14; 42; 132; 429; 1430; 4862].
Proof. by []. Qed.


Lemma size_Catalan_bin_leq n : size (Catalan_bin_leq n) = n.+1.
Proof. by elim: n => [|n] //=; rewrite size_rcons => ->. Qed.

Lemma size_enum_bintreesz n : size (enum_bintreesz_leq n) = n.+1.
Proof. by elim: n => //= n; rewrite size_rcons => ->. Qed.

Lemma size_enum_bintreeszE n : size (enum_bintreesz n) = Catalan_bin n.
Proof.
rewrite /Catalan_bin /enum_bintreesz -[LHS]last_map ; congr last.
elim: n => [//= |n IHn].
rewrite [LHS]/= map_rcons IHn /=; congr rcons.
rewrite -[RHS]/(sumn (map _ (iota 0 n.+1))).
rewrite -[LHS]/(size (flatten (map _ (iota 0 n.+1)))).
rewrite size_flatten /shape -map_comp; congr sumn.
apply eq_in_map => i; rewrite mem_iota /= add0n ltnS => Hi.
rewrite size_allpairs -!IHn !(nth_map [::]) // size_enum_bintreesz ltnS //.
exact: leq_subr.
Qed.


Lemma Catalan_bin_leqE i m :
  i <= m -> nth 0 (Catalan_bin_leq m) i = Catalan_bin i.
Proof.
rewrite /Catalan_bin => Hi.
rewrite -nth_last size_Catalan_bin_leq /= -(subnK Hi).
elim: (m-i) => // d <-.
by rewrite addSn nth_rcons size_Catalan_bin_leq ltnS leq_addl.
Qed.

Lemma enum_bintreesz_leq_leqE i n m :
  i <= n <= m ->
  nth [::] (enum_bintreesz_leq n) i = nth [::] (enum_bintreesz_leq m) i.
Proof.
move=> /andP [Hi Hn]; rewrite -(subnK Hn).
elim: (m - n) => {m Hn} [| m ->] //.
rewrite addSn /= nth_rcons size_enum_bintreesz ltnS (leq_trans Hi _) //.
exact: leq_addl.
Qed.

Lemma enum_bintreesz_leqE n m :
  n <= m -> enum_bintreesz n = nth [::] (enum_bintreesz_leq m) n.
Proof.
move=> H; rewrite /enum_bintreesz.
rewrite -nth_last size_enum_bintreesz /=.
apply: enum_bintreesz_leq_leqE.
by rewrite leqnn H.
Qed.


Lemma Catalan0 : Catalan_bin 0 = 1.
Proof. by []. Qed.

Lemma enum_bintreesz0 : enum_bintreesz 0 = [:: BinLeaf].
Proof. by []. Qed.


Lemma Catalan_binS n :
  Catalan_bin n.+1 = \sum_(0 <= i < n.+1) Catalan_bin i * Catalan_bin (n - i).
Proof.
rewrite /Catalan_bin -sumn_mapE last_rcons.
rewrite -/Catalan_bin_leq; congr sumn.
rewrite /index_iota subn0; apply eq_in_map => i.
rewrite mem_iota /= add0n ltnS => Hi.
rewrite -!nth_last !size_Catalan_bin_leq /= !Catalan_bin_leqE //.
exact: leq_subr.
Qed.

Lemma enum_bintreeszE n :
  enum_bintreesz n.+1 =
  flatten [seq [seq BinNode tl tr |
                tl <- enum_bintreesz i,
                tr <- enum_bintreesz (n - i)] | i <- iota 0 n.+1].
Proof.
rewrite [in LHS]/enum_bintreesz.
rewrite -nth_last size_enum_bintreesz [n.+2.-1]/=.
rewrite nth_rcons -!/(enum_bintreesz_leq _) !size_enum_bintreesz ltnn eq_refl.
congr flatten; apply eq_in_map => i.
rewrite mem_iota add0n ltnS /= => Hi.
by rewrite -!(enum_bintreesz_leqE (m := n)) // leq_subr.
Qed.


Lemma size_mem_enum_bintreeszP n t :
  t \in enum_bintreesz n -> size_tree t = n.
Proof.
have [m] := ubnP n; elim: m => // m IHm in n t * => /ltnSE.
case: n => [_|n ltnm]; first by rewrite enum_bintreesz0 inE => /eqP ->.
rewrite enum_bintreeszE => /flatten_mapP [j].
rewrite mem_iota /= add0n ltnS => lejn.
have ltjn1 := leq_ltn_trans lejn ltnm.
have:= leq_subr j n; rewrite -ltnS => /leq_trans/(_ ltnm) ltnjn1.
move/allpairsP => [[l r] /= [/(IHm _ _ ltjn1) szl /(IHm _ _ ltnjn1) szr ->{t}]].
by rewrite /= szl szr add1n addSn addnC subnK.
Qed.

Lemma enum_bintreeszP n :
  all (fun t => size_tree t == n) (enum_bintreesz n).
Proof. by apply/allP => /= t /size_mem_enum_bintreeszP ->. Qed.

Lemma enum_bintreesz_uniq n : uniq (enum_bintreesz n).
Proof.
elim/ltn_ind: n => [[//|n IHn]].
rewrite enum_bintreeszE.
have [i] := ubnPgeq n.+1; elim: i => // i IHi /ltnSE-ltin.
rewrite -addn1 iota_add add0n /=.
rewrite map_cat flatten_cat /= cats0 cat_uniq.
rewrite {}IHi /=; last exact: (leq_trans ltin).
apply/andP; split.
- apply/hasP => [] /= [[| l r]] /allpairsP/= [[l1 r1] /= []].
  + by move=> _ _ /eqP; rewrite eqE.
  + move/size_mem_enum_bintreeszP => Hszl1 _ -> {l r}.
    move/flattenP => [/= ltj /mapP /= [j]].
    rewrite mem_iota /= add0n => Hj ->.
    move/allpairsP => [/= [l r] /= []].
    move/size_mem_enum_bintreeszP => Hszl _ [] Hl1 _.
    move: Hszl1 Hj; rewrite Hl1 Hszl => ->.
    by rewrite ltnn.
- have:= IHn i ltin.
  elim: (enum_bintreesz i) => [// | l ll IHll] /= /andP[Hnotin {}/IHll Hrec].
  rewrite cat_uniq Hrec /= andbT.
  apply/andP; split.
  + rewrite map_inj_uniq; first by apply IHn; apply leq_subr.
    by move=> r1 r2 [].
  + apply/hasP => [] /= [t].
    move/allpairsP => [] /= [l1 r1 /= [Hl1 _ ->{t}]].
    move/mapP => [] /= r2 _ [] Heql _.
    by move: Hnotin; rewrite -Heql Hl1.
Qed.

Lemma mem_enum_bintreesz n t :
  size_tree t == n -> t \in enum_bintreesz n.
Proof.
elim/ltn_ind: n t => [[_|n IHn]] [|l r] //=.
rewrite add1n addSn eqSS => /eqP Hn.
rewrite enum_bintreeszE; apply/flattenP.
exists [seq BinNode tl tr
       | tl <- enum_bintreesz (size_tree l),
         tr <- enum_bintreesz (n - (size_tree l))]; first last.
  apply/allpairsP; exists (l, r); split => //=.
  - by apply IHn => //; rewrite -Hn; apply leq_addr.
  - apply IHn => //; first exact: leq_subr.
    by rewrite -Hn addKn.
apply/mapP; exists (size_tree l) => //.
by rewrite mem_iota /= add0n ltnS -Hn leq_addr.
Qed.

Lemma enum_bintreesz_countE n t :
  size_tree t == n -> count_mem t (enum_bintreesz n) = 1.
Proof.
move/mem_enum_bintreesz => H.
by rewrite (count_uniq_mem _ (enum_bintreesz_uniq n)) H.
Qed.

Local Definition type n := Eval hnf in
  sub_subFinType [subCountType of bintreesz n]
                 (enum_bintreeszP n) (@enum_bintreesz_countE n).
Canonical bintreesz_finType n := Eval hnf in [finType of bintreesz n for type n].
Canonical bintreesz_subFinType n := Eval hnf in [subFinType of bintreesz n].


Theorem card_bintreesz n : #|bintreesz n| = Catalan_bin n.
Proof.
rewrite /= !cardT -!(size_map val) !enumT unlock !subType_seqP /=.
by rewrite size_enum_bintreeszE.
Qed.


(** ** Left branch surgery in binary trees *)
Fixpoint left_branch t :=
  if t is BinNode l r then r :: left_branch l else [::].
Fixpoint from_left l :=
  if l is l0 :: l then BinNode (from_left l) l0 else BinLeaf.
Definition cat_left t1 t2 := from_left (left_branch t1 ++ left_branch t2).


Lemma left_branchK : cancel left_branch from_left.
Proof. by elim=> //= l ->. Qed.
Lemma from_leftK : cancel from_left left_branch.
Proof. by elim=> //= l0 l ->. Qed.

Lemma cat_left0t t : cat_left BinLeaf t = t.
Proof. by rewrite /cat_left /= left_branchK. Qed.
Lemma cat_leftt0 t : cat_left t BinLeaf = t.
Proof. by rewrite /cat_left /= cats0 left_branchK. Qed.
Lemma cat_left_Node l r :
  cat_left (BinNode BinLeaf r) l = BinNode l r.
Proof. by rewrite /cat_left /= left_branchK. Qed.
Lemma cat_leftA t u v :
  cat_left (cat_left t u) v = cat_left t (cat_left u v).
Proof. by rewrite /cat_left !from_leftK catA. Qed.
Lemma size_from_left s :
  size_tree (from_left s) = sumn [seq (size_tree t).+1 | t <- s].
Proof. by elim: s => //= s0 s <-; rewrite add1n !addSn addnC. Qed.

Lemma size_cat_left t u :
  size_tree (cat_left t u) = size_tree t + size_tree u.
Proof.
rewrite /cat_left size_from_left map_cat sumn_cat.
by rewrite -!size_from_left !left_branchK.
Qed.

Lemma from_left_cat s1 s2 :
  from_left (s1 ++ s2) = cat_left (from_left s1) (from_left s2).
Proof. by rewrite /cat_left !from_leftK. Qed.

Lemma size_left_branch t :
  all (fun l => size_tree l < size_tree t) (left_branch t).
Proof.
rewrite -{1}(left_branchK t) size_from_left.
elim: (left_branch t) => //= l lb /allP IHlb.
rewrite {1}addSn ltnS leq_addr /=.
apply/allP => t1 /IHlb /leq_trans; apply.
exact: leq_addl.
Qed.


(** ** Various particular binary trees *)
Fixpoint rightcomb n :=
  if n is n'.+1 then
    BinNode BinLeaf (rightcomb n')
  else BinLeaf.
Fixpoint leftcomb n :=
  if n is n'.+1 then
    BinNode (leftcomb n') BinLeaf
  else BinLeaf.
Fixpoint flip t :=
  if t is BinNode l r then
    BinNode (flip r) (flip l)
  else BinLeaf.

Lemma size_rightcomb n : size_tree (rightcomb n) = n.
Proof. elim: n => //= n ->; by rewrite addn0 add1n. Qed.
Lemma size_leftcomb n : size_tree (leftcomb n) = n.
Proof. elim: n => //= n ->; by rewrite addn0 add1n. Qed.
Lemma size_flip t : size_tree (flip t) = size_tree t.
Proof.
elim: t => //= l -> r -> /=.
by rewrite -!addnA [X in 1 + X]addnC.
Qed.
Lemma flipK : involutive flip.
Proof. by elim => //= l -> r ->. Qed.
Lemma flip_rightcomb n : flip (rightcomb n) = leftcomb n.
Proof. by elim: n => //= n ->. Qed.
Lemma flip_leftcomb n : flip (leftcomb n) = rightcomb n.
Proof. by elim: n => //= n ->. Qed.


(** * Tamari's lattice *)
(** ** Rotations in binary trees *)
Fixpoint rotations t :=
  if t is BinNode l r then
    let rec := [seq BinNode lrot r | lrot <- rotations l] ++
               [seq BinNode l rrot | rrot <- rotations r]
    in if l is BinNode ll lr then
         BinNode ll (BinNode lr r) :: rec
       else rec
  else [::].

Lemma rotations_left_sub l1 l2 r :
  l1 \in rotations l2 -> BinNode l1 r \in rotations (BinNode l2 r).
Proof.
case H2 : l2 => [/= |ll2 lr2]; first by rewrite in_nil.
rewrite -H2 /= {2}H2 => Hin.
rewrite inE; apply/orP; right.
rewrite mem_cat; apply/orP; left.
by apply/mapP; exists l1.
Qed.

Lemma rotations_right_sub l r1 r2 :
  r1 \in rotations r2 -> BinNode l r1 \in rotations (BinNode l r2).
Proof.
case Hl : l => [/= |ll lr] H; first by apply/mapP; exists r1.
rewrite -Hl /= {2}Hl.
rewrite inE; apply/orP; right.
rewrite mem_cat; apply/orP; right.
by apply/mapP; exists r1.
Qed.

Lemma rotationP t1 t2 :
  reflect (exists a b c,
              [\/ [/\ t1 = BinNode (BinNode a b) c & t2 = BinNode a (BinNode b c)],
                  [/\ t1 = BinNode a c, t2 = BinNode b c & b \in rotations a] |
                  [/\ t1 = BinNode a b, t2 = BinNode a c & c \in rotations b]])
          (t2 \in rotations t1).
Proof.
apply (iffP idP) => [|].
- case Ht1 : t1 => [//|[|a b] c].
    rewrite /= => /mapP /= [rc Hrc ->].
    by exists BinLeaf, c, rc; apply Or33.
  rewrite [X in X -> _]/= inE => /orP [/eqP -> {t2}|].
    by exists a, b, c; apply Or31.
  rewrite mem_cat => /orP [/mapP [lrot] | /mapP [rrot Hrrot ->]].
  + rewrite -[lrot \in _]/(lrot \in rotations (BinNode a b)) => Hlrot ->.
    by exists (BinNode a b), lrot, c; apply Or32.
  + by exists (BinNode a b), c, rrot; apply Or33.
- move=> [a] [b] [c] [] [-> ->].
  + by rewrite inE eq_refl.
  + exact: rotations_left_sub.
  + exact: rotations_right_sub.
Qed.

Lemma size_rotations t t' :
  t' \in rotations t -> size_tree t' = size_tree t.
Proof.
elim: t t' => [//= | l IHl r IHr] t' /=.
case H: l => [| ll lr] //; first by move/mapP => [/= lrot /IHr <- ->].
rewrite inE => /orP [/eqP ->|]; first by rewrite /= !(add1n, addSn, addnS) addnA.
by rewrite -H mem_cat => /orP [/mapP /= [lrot/IHl]|/mapP /= [rrot/IHr]] <- ->.
Qed.

Lemma rotations_flip_impl t1 t2:
  (t1 \in rotations t2) -> (flip t2 \in rotations (flip t1)).
Proof.
elim: t2 t1 => [//|l IHl r IHr] t2.
move/rotationP => [a] [b] [c] [] [H1 H2]; rewrite H1 H2.
- by rewrite /= inE eq_refl.
- move=> H; apply/rotationP.
  move: H1 => [Hl Hr]; subst a; subst c => /=.
  exists (flip r), (flip b), (flip l); apply Or33; split => //=.
  exact: IHl.
- move=> H; apply/rotationP.
  move: H1 => [Hl Hr]; subst a; subst b => /=.
  exists (flip c), (flip r), (flip l); apply Or32; split => //=.
  exact: IHr.
Qed.

Lemma rotations_flip t1 t2:
  (t1 \in rotations t2) = (flip t2 \in rotations (flip t1)).
Proof.
apply/idP/idP; first exact: rotations_flip_impl.
by move=> /rotations_flip_impl; rewrite !flipK.
Qed.

Lemma catleft_rotations t t1 t2 :
  t1 \in rotations t2 -> (cat_left t t1) \in rotations (cat_left t t2).
Proof.
elim: t => [| tl IHtl tr _]; first by rewrite !cat_left0t.
move/IHtl => {IHtl} Hrec.
apply/rotationP; exists (cat_left tl t2), (cat_left tl t1), tr.
by apply Or32.
Qed.

Lemma rightcomb_rotations n : rotations (rightcomb n) = [::].
Proof. by elim: n => //= n ->. Qed.
Lemma rightcomb_rotationsE t :
  (rotations t == [::]) = (t == rightcomb (size_tree t)).
Proof.
apply/eqP/eqP => [|->].
- elim: t => [//=| l _ r IHr].
  case: l => [| ll lr] //= Hrot.
  have {Hrot} /IHr -> : rotations r = [::] by move: Hrot; case: (rotations r).
  by rewrite size_rightcomb.
- exact: rightcomb_rotations.
Qed.
Lemma leftcomb_rotations t : leftcomb (size_tree t) \notin rotations t.
Proof. by rewrite rotations_flip flip_leftcomb rightcomb_rotations in_nil. Qed.


Fixpoint rightsizesum t :=
  if t is BinNode l r then
    rightsizesum l + size_tree r + rightsizesum r
  else 0.

Lemma rightsizesum_gt t t' :
  t' \in rotations t -> rightsizesum t < rightsizesum t'.
Proof.
elim: t t' => [//| l IHl r IHr] t'.
case Hl : l IHl => [| ll lr] // IHl.
  rewrite /= add0n => /mapP [/= rot Hrot -> {t'}] /=.
  rewrite add0n (size_rotations Hrot) ltn_add2l.
  exact: IHr.
rewrite -Hl /= {1}Hl /= inE => /orP [/eqP -> /=|].
  rewrite Hl /= add1n !(addSn, addnS) ltnS -!addnA !leq_add2l.
  exact: leq_addl.
rewrite -Hl in IHl.
rewrite mem_cat => /orP [/mapP /= [lrot Hlrot] | /mapP /= [rrot Hrrot]] -> /=.
- rewrite !ltn_add2r.
  exact: IHl.
- rewrite (size_rotations Hrrot) ltn_add2l.
  exact: IHr.
Qed.

Lemma rotations_neq t t' : t' \in rotations t -> t != t'.
Proof.
move/rightsizesum_gt; apply contraL => /eqP ->.
by rewrite ltnn.
Qed.


Fact Tamari_display : unit. Proof. exact: tt. Qed.

(** ** Definition of Tamari order *)
Module Tamari.
Section Tamari.

Variable n : nat.
Implicit Type t : bintreesz n.

Definition Tamari := connect (fun t1 t2 : bintreesz n => grel rotations t1 t2).
Definition Tamari_lt t1 t2 := (t2 != t1) && (Tamari t1 t2).

Local Notation "x '<=T' y" := (Tamari x y) (at level 70, y at next level).
Local Notation "x '<T' y" := (Tamari_lt x y) (at level 70, y at next level).

Lemma Tamari_def s t : (s <T t) = ((t != s) && (s <=T t)).
Proof. by []. Qed.

Lemma rotations_Tamari t t' :
  trval t' \in rotations t -> t <T t'.
Proof.
move=> H; rewrite /Tamari_lt eq_sym rotations_neq //.
exact: connect1.
Qed.

Lemma Tamari_refl : reflexive Tamari.
Proof. exact: connect0. Qed.

Lemma Tamari_trans : transitive Tamari.
Proof. exact: connect_trans. Qed.

Lemma Tamari_rightsizesum t1 t2 :
  t1 <=T t2 -> rightsizesum t1 <= rightsizesum t2 ?= iff (t1 == t2).
Proof.
move/connectP => [] /= p.
elim: p t1 t2 => [| t0 p IHp] t1 t2 /=.
  by move=> _ /= ->; split; rewrite // !eq_refl.
move=> /andP [/rightsizesum_gt Hgt {}/IHp H{}/H].
move=> [] /(leq_trans Hgt) Hlt _ {Hgt p t0}.
split; first exact: (ltnW Hlt).
have:= Hlt; rewrite ltn_neqAle => /andP [/negbTE -> _].
by case: eqP Hlt => [->|] //; rewrite ltnn.
Qed.

Lemma Tamari_anti : antisymmetric Tamari.
Proof.
move=> t1 t2 /andP [ /Tamari_rightsizesum [leq21 eq]].
move=> /Tamari_rightsizesum [leq12 _].
by apply/eqP; rewrite -eq eqn_leq leq21 leq12.
Qed.

Definition porderMixin :=
  LePOrderMixin Tamari_def Tamari_refl Tamari_anti Tamari_trans.
Canonical porderType :=
  POrderType Tamari_display (bintreesz n) porderMixin.
Canonical finPOrderType := Eval hnf in [finPOrderType of bintreesz n].

End Tamari.

Module Exports.

Set Warnings "-redundant-canonical-projection".
Canonical porderType.
Canonical finPOrderType.
Set Warnings "+redundant-canonical-projection".

Notation "x <=T y" := (@Order.le Tamari_display _ x y).
Notation "x <T y" := (@Order.lt Tamari_display _ x y).
Notation "x /\T y" := (@Order.meet Tamari_display _ x y).
Notation "x \/T y" := (@Order.join Tamari_display _ x y).

End Exports.
End Tamari.
Export Tamari.Exports.


Section Flip.

Variable n : nat.
Implicit Type t : bintreesz n.

Definition TamariE t1 t2 :
  (t1 <=T t2) = connect (fun x y : bintreesz n => grel rotations x y) t1 t2.
Proof. by []. Qed.
Lemma rotations_Tamari t t' :
  trval t' \in rotations t -> t <T t'.
Proof. exact: Tamari.rotations_Tamari. Qed.

Local Fact rightcombsz_proof : size_tree (rightcomb n) == n.
Proof. apply/eqP; exact: size_rightcomb. Qed.
Canonical rightcombsz := BinTreeSZ rightcombsz_proof.
Local Fact leftcombsz_proof : size_tree (leftcomb n) == n.
Proof. apply/eqP; exact: size_leftcomb. Qed.
Canonical leftcombsz := BinTreeSZ leftcombsz_proof.
Local Lemma flipsz_proof t : size_tree (flip t) == n.
Proof. by rewrite size_flip bintreeszP. Qed.
Canonical flipsz t := BinTreeSZ (flipsz_proof t).

Lemma flipszK : involutive flipsz.
Proof. move=> t; apply val_inj => /=; exact: flipK. Qed.
Lemma flipsz_rightcomb : flipsz rightcombsz = leftcombsz.
Proof. by apply val_inj => /=; exact: flip_rightcomb. Qed.
Lemma flipsz_leftcomb : flipsz leftcombsz = rightcombsz.
Proof. by apply val_inj => /=; exact: flip_leftcomb. Qed.

Lemma Tamari_flip t1 t2 : (flipsz t2 <=T flipsz t1) = (t1 <=T t2).
Proof.
suff {t1 t2} Timpl t1 t2 : (flipsz t2 <=T flipsz t1) -> t1 <=T t2.
  apply/idP/idP; first exact: Timpl.
  by rewrite -{1}(flipszK t1) -{1}(flipszK t2); exact: Timpl.
rewrite TamariE => /connectP /= [].
case/lastP => [//= _ | p l Hp] /=.
  move=> /(congr1 flipsz). rewrite !flipszK => ->.
  exact: connect0.
rewrite last_rcons => Hl; subst l; move: Hp.
have /eq_path -> : (fun t t' => trval t' \in rotations t)
                   =2 (fun t t' => trval (flipsz t) \in rotations (flipsz t')).
  by move=> t t' /=; exact: rotations_flip.
rewrite -rev_path /= last_rcons belast_rcons.
have -> : rev (flipsz t2 :: p) =
          [seq flipsz t | t <- rcons [seq flipsz t' | t' <- rev p] t2].
  rewrite map_rev -rev_cons map_rev /=.
  rewrite -map_comp (eq_map (f2 := id)); last by move=> x /=; rewrite flipszK.
  by rewrite map_id.
rewrite (map_path (b := pred0)
                  (e' := (fun t t' => trval t' \in rotations t))); first last.
  - by apply/hasP => [] [t /=].
  - by rewrite /rel_base => u v _; rewrite /= !flipK.
set pp := rcons _ _ => Hp; apply/connectP; exists pp; first by [].
by rewrite /pp last_rcons.
Qed.

End Flip.


(** ** Tamari vectors *)
Fixpoint right_sizes t :=
  if t is BinNode l r then
        right_sizes l ++ size_tree r :: right_sizes r
  else [::].
Fixpoint is_Tamari v :=
  if v is v0 :: v' then
    [&& v0 <= size v',
     is_Tamari v' &
     all (fun i => nth 0 v' i + i < v0) (iota 0 v0)]
  else true.
Definition TamariVector := [qualify a v : seq nat | is_Tamari v].

Lemma size_right_sizes t : size (right_sizes t) = size_tree t.
Proof.
elim: t => //= l <- r <-.
by rewrite size_cat /= addnS add1n addSn.
Qed.

Lemma rightsizesumE t : sumn (right_sizes t) = rightsizesum t.
Proof. by elim: t => //= l <- r <-; rewrite sumn_cat /= addnA. Qed.

Lemma right_sizes_left_comb n :
  right_sizes (leftcomb n) = nseq n 0.
Proof.
elim: n => //= n ->.
by rewrite -[RHS]cat1s -[[:: 0]]/(nseq 1 0) -!nseqD addnC.
Qed.

Lemma right_sizes_from_left s :
  right_sizes (from_left s) =
  flatten [seq size_tree t :: right_sizes t | t <- rev s].
Proof.
elim: s => //= s0 s ->.
by rewrite rev_cons -cats1 map_cat !flatten_cat /= cats0.
Qed.

Lemma right_sizes_cat_left t1 t2 :
  right_sizes (cat_left t1 t2) = right_sizes t2 ++ right_sizes t1.
Proof.
rewrite /cat_left right_sizes_from_left rev_cat map_cat flatten_cat.
by rewrite -!right_sizes_from_left !left_branchK.
Qed.


Lemma Tamari_consP v0 v :
  reflect
    [/\ v0 <= size v,
     v \is a TamariVector &
     forall i, i < v0 -> nth 0 v i + i < v0]
    (v0 :: v \is a TamariVector).
Proof.
rewrite !unfold_in /=.
apply (iffP and3P) => [] [Hsz Htam Hall]; split => //.
- by move/allP: Hall => H i Hi; apply H; rewrite mem_iota.
- by apply/allP => i; rewrite mem_iota /= add0n; exact: Hall.
Qed.

Lemma TamariP v :
  reflect
    ((forall i, i < size v -> nth 0 v i + i < size v) /\
     (forall i j, i < j <= nth 0 v i + i -> nth 0 v j + j <= nth 0 v i + i))
    (v \is a TamariVector).
Proof.
apply (iffP idP); elim: v => [_ | v0 v IHv ] //=.
  by split => // i j; rewrite !nth_nil => /andP [_]; rewrite !add0n.
- move/Tamari_consP => [Hv0 /IHv{IHv} [Hrec1 Hrec2] H]; split.
  + case=> [_ |i]; rewrite !ltnS /= ?addn0 // addnS; exact: Hrec1.
  + case=> [//=| i] [//=| j] /=.
      by rewrite !addnS !addn0 ; exact: H.
    by rewrite !addnS !ltnS; exact: Hrec2.
- move=> [H1 H2].
  apply/Tamari_consP; split.
  + by have:= H1 0 (ltn0Sn _); rewrite addn0 ltnS.
  + apply: IHv; split => [i Hi | i j Hij].
    * by have:= H1 i.+1 Hi; rewrite /= addnS ltnS.
    * by have:= H2 i.+1 j.+1; rewrite /= !addnS !ltnS; apply.
  + move=> i Hi.
    by have:= H2 0 i.+1; rewrite /= !addn0 addnS; apply.
Qed.

Lemma Tamari_drop n v :
  v \is a TamariVector -> drop n v \is a TamariVector.
Proof.
rewrite !unfold_in; elim: n v => [//= | n IHn] v; first by rewrite drop0.
by case: v => [| v0 v] //= /and3P [_ /IHn ->].
Qed.

Lemma Tamari_catr u v :
  u ++ v \is a TamariVector -> v \is a TamariVector.
Proof.
by move=> /(Tamari_drop (size u)); rewrite drop_cat ltnn subnn drop0.
Qed.

Lemma Tamari_take v0 v :
  v0 :: v \is a TamariVector -> take v0 v \is a TamariVector.
Proof.
elim: v0 v => [| v0 IHv0] v; first by rewrite take0.
case: v => [//= | v1 v].
move/Tamari_consP; rewrite /= ltnS => [] [Hsz Htam H].
apply/Tamari_consP; rewrite (size_takel Hsz).
have:= H 0 (ltn0Sn _); rewrite ltnS addn0 => /= Hv1.
split.
- exact: Hv1.
- apply: IHv0; move: Htam => /Tamari_consP [_ Hv H1].
  apply/Tamari_consP; split => // i.
  by rewrite -ltnS => /H; rewrite /= ltnS addnS.
- move/Tamari_consP: Htam {H} => [_ _ H] i Hi.
  by rewrite nth_take ?H // (leq_trans Hi Hv1).
Qed.

Lemma Tamari_cat v1 v2 :
  v1 \is a TamariVector ->
  v2 \is a TamariVector ->
  v1 ++ v2 \is a TamariVector.
Proof.
elim: v1 => [| v0 v1 IHv1] //= /Tamari_consP [Hv0 Hv1 Hall] Hv2.
apply/Tamari_consP; split.
- rewrite size_cat; apply: (leq_trans Hv0); apply leq_addr.
- exact: IHv1.
- by move=> i Hi; rewrite nth_cat (leq_trans Hi Hv0) Hall.
Qed.

Lemma cons_TamariP v : v \is a TamariVector -> size v :: v \is a TamariVector.
Proof.
move=> H; apply/Tamari_consP; split => // i Hi.
by move: H => /TamariP [H _]; apply H.
Qed.

Theorem right_sizesP t : right_sizes t \is a TamariVector.
Proof.
have [n] := ubnP (size_tree t); elim: n => // n IHn in t * => /ltnSE-leszt.
rewrite -(left_branchK t) right_sizes_from_left.
have : all (fun t => size_tree t < n) (rev (left_branch t)).
  rewrite all_rev; have:= size_left_branch t.
  by apply sub_all => l Hl; apply: leq_trans Hl leszt.
elim: (rev (left_branch t)) => [| b0 br IHbr] //=.
move=> /andP [{}/IHn Hb0 {}/IHbr Hbr].
rewrite -/((_ :: _) ++ _); apply Tamari_cat; last exact: Hbr.
by rewrite -size_right_sizes; exact: cons_TamariP.
Qed.

#[local] Hint Resolve right_sizesP : core.



(** ** Bijection with Tamari vectors *)
Fixpoint from_vct_rec fuel lft vct :=
  if fuel is fuel.+1 then
    if vct is v0 :: vct' then
      from_vct_rec fuel
                   (BinNode lft (from_vct_rec fuel BinLeaf (take v0 vct')))
                   (drop v0 vct')
    else lft
  else BinLeaf.
Definition from_vct_acc lft vct := from_vct_rec (size vct).+1 lft vct.
Definition from_vct := from_vct_acc BinLeaf.

Section Tests.

Goal [seq right_sizes t | t <- enum_bintreesz 3] =
[:: [:: 2; 1; 0]; [:: 2; 0; 0]; [:: 0; 1; 0]; [:: 1; 0; 0]; [:: 0; 0; 0]].
Proof. by []. Qed.

Goal [seq right_sizes t | t <- enum_bintreesz 4] =
[:: [:: 3; 2; 1; 0]; [:: 3; 2; 0; 0]; [:: 3; 0; 1; 0]; [:: 3; 1; 0; 0];
    [:: 3; 0; 0; 0]; [:: 0; 2; 1; 0]; [:: 0; 2; 0; 0]; [:: 1; 0; 1; 0];
    [:: 0; 0; 1; 0]; [:: 2; 1; 0; 0]; [:: 2; 0; 0; 0]; [:: 0; 1; 0; 0];
    [:: 1; 0; 0; 0]; [:: 0; 0; 0; 0] ].
Proof. by []. Qed.

Let bla := Eval hnf in nth BinLeaf (enum_bintreesz 5) 21.
Goal right_sizes bla = [:: 0; 0; 2; 1; 0].
Proof. by []. Qed.

Goal [seq right_sizes rot | rot <- rotations bla] =
[:: [:: 0; 3; 2; 1; 0]; [:: 1; 0; 2; 1; 0]].
Proof. by []. Qed.

Goal all
     (fun i => all (fun t => t == from_vct (right_sizes t)) (enum_bintreesz i))
     (iota 0 7).
Proof. by []. Qed.

Goal all
     (fun i => all (fun t => right_sizes t \is a TamariVector) (enum_bintreesz i))
     (iota 0 7).
Proof. by []. Qed.

Goal [:: 1; 1; 0] \isn't a TamariVector.
Proof. by []. Qed.
Goal [:: 2; 0; 1; 0] \isn't a TamariVector.
Proof. by []. Qed.

Goal [:: 2; 0; 0; 1; 0] \is a TamariVector.
Proof. by []. Qed.

End Tests.


Lemma from_vct_acc_nil lft : from_vct_acc lft [::] = lft.
Proof. by []. Qed.

Lemma from_vct_fuelE fuel lft vct :
  size vct < fuel -> from_vct_rec fuel lft vct = from_vct_acc lft vct.
Proof.
rewrite /from_vct_acc.
have [fuel1] := ubnPleq (size vct).+1.
elim: fuel => [| fuel IHfuel] in vct fuel1 lft *.
  by move=> /leq_trans H{}/H.
case: fuel1 => // fuel1; rewrite !ltnS.
case: vct => // v0 vct /= Hsz Hfuel1.
rewrite !(IHfuel _ fuel1) //.
- by rewrite size_take; exact: (leq_ltn_trans (geq_minr _ _) Hsz).
- by rewrite size_drop; exact: (leq_ltn_trans (leq_subr _ _) Hsz).
Qed.

Lemma from_vct_accE lft v0 vct :
  from_vct_acc lft (v0 :: vct) =
  from_vct_acc (BinNode lft (from_vct_acc BinLeaf (take v0 vct)))
               (drop v0 vct).
Proof.
rewrite -[in RHS](from_vct_fuelE (fuel := size (v0 :: vct))); first last.
  by rewrite /= ltnS size_drop leq_subr.
rewrite {2}/from_vct_acc.
rewrite -[_ _.+1 _ _](from_vct_fuelE (fuel := size (v0 :: vct))); first by [].
by rewrite /= size_take -/(minn _ _) ltnS geq_minr.
Qed.

Lemma from_vct_cat_leftE lft vct :
  from_vct_acc lft vct = cat_left (from_vct_acc BinLeaf vct) lft.
Proof.
have [n/ltnW] := ubnP (size vct); elim: n => [|n IHn] in vct lft * => /ltnSE.
  by rewrite leqn0 /from_vct_acc => /nilP ->; rewrite /= cat_left0t.
case: vct => [_ | v0 v] /=.
  by rewrite /from_vct_acc /= cat_left0t.
rewrite ltnS -{1}(cat_take_drop v0 v) size_cat !from_vct_accE /=.
move: (take v0 v) (drop v0 v) => {v0 v} u v Huv.
rewrite IHn; last exact: (leq_trans (leq_addl _ _) Huv).
rewrite [in RHS]IHn; last exact: (leq_trans (leq_addl _ _) Huv).
by rewrite cat_leftA cat_left_Node.
Qed.

Lemma size_from_vct_acc s :
  size_tree (from_vct_acc BinLeaf s) = size s.
Proof.
have [n/ltnW] := ubnP (size s); elim: n => [|n IHn] in s * => /ltnSE.
  by rewrite leqn0 => /nilP ->.
case: s => [| s0 s] //=.
rewrite ltnS -{1}(cat_take_drop s0 s) size_cat => Hsz.
rewrite from_vct_accE from_vct_cat_leftE.
rewrite size_cat_left /= addn0 add1n addnS.
rewrite IHn; last exact: (leq_trans (leq_addl _ _) Hsz).
rewrite IHn; last exact: (leq_trans (leq_addr _ _) Hsz).
by rewrite addnC -size_cat cat_take_drop.
Qed.

Lemma size_from_vct s :
  size_tree (from_vct s) = size s.
Proof. exact : size_from_vct_acc. Qed.

Theorem right_sizesK : cancel right_sizes from_vct.
Proof.
rewrite /from_vct => t.
have [n] := ubnPleq (size_tree t); elim: n => [|n IHn] in t *.
  by rewrite leqn0 => /LeafP ->.
rewrite -(left_branchK t).
case/lastP: {t} (left_branch t) => //= [br r].
rewrite -cats1 -(from_leftK br) -(from_leftK [:: r]) -/(cat_left _ _) /=.
rewrite right_sizes_cat_left /=.
rewrite from_vct_accE -!size_right_sizes drop_size_cat // take_size_cat //.
rewrite size_right_sizes size_cat_left /= addn0 add1n addnS ltnS => H.
rewrite IHn /=; last exact: (leq_trans (leq_addl _ _) H).
rewrite from_vct_cat_leftE.
by rewrite IHn; last exact: (leq_trans (leq_addr _ _) H).
Qed.

Theorem from_vctK s :
  s \is a TamariVector -> right_sizes (from_vct s) = s.
Proof.
rewrite /from_vct.
have [n] := ubnPleq (size s); elim: n => [|n IHn] in s *.
  by rewrite leqn0 => /nilP ->.
case: s => [| s0 s] //=.
rewrite ltnS -{1}(cat_take_drop s0 s) size_cat => Hsz Hcons.
have:= Hcons => /Tamari_consP [Hs0 Hs Hall].
rewrite from_vct_accE from_vct_cat_leftE right_sizes_cat_left.
rewrite IHn /=; first last.
  - exact: Tamari_drop.
  - exact: (leq_trans (leq_addl _ _) Hsz).
rewrite {}IHn /=; first last.
  - exact: Tamari_take.
  - exact: (leq_trans (leq_addr _ _) Hsz).
by rewrite cat_take_drop size_from_vct_acc size_takel.
Qed.

Lemma from_vct_cat u v t :
  u \is a TamariVector ->
  from_vct_acc t (u ++ v) = from_vct_acc (from_vct_acc t u) v.
Proof.
rewrite /from_vct => /from_vctK <-.
rewrite -(left_branchK (from_vct u)).
elim/last_ind: (left_branch _) t => [| br bn IHbr] //= t.
rewrite right_sizes_from_left rev_rcons /= -right_sizes_from_left.
rewrite !from_vct_accE -catA.
rewrite !take_size_cat ?size_right_sizes //.
by rewrite !drop_size_cat ?size_right_sizes //.
Qed.

Lemma from_vct0 n : from_vct (nseq n 0) = leftcomb n.
Proof. by rewrite -right_sizes_left_comb right_sizesK. Qed.


(** ** Comparison of Tamari vectors *)

Definition vctleq v1 v2 :=
  (size v1 == size v2) && (all (fun p => p.1 <= p.2) (zip v1 v2)).
Definition vctmin v1 v2 := [seq minn p.1 p.2 | p <- zip v1 v2].

Local Notation "x '<=V' y" := (vctleq x y) (at level 70, y at next level).

Section TestsComp.

Goal all (fun t => all
                     (vctleq (right_sizes t))
                     [seq right_sizes rot | rot <- rotations t])
     (enum_bintreesz 6).
Proof. by []. Qed.

End TestsComp.

Lemma vctleqP v1 v2 :
  reflect (size v1 = size v2 /\ forall i, nth 0 v1 i <= nth 0 v2 i)
          (v1 <=V v2).
Proof.
rewrite /vctleq; apply (iffP andP).
- move=> [/eqP Hsz /allP/= Hleq]; split; first by [].
  move=> i; case: (ltnP i (size (zip v1 v2))).
  + by move=> /(mem_nth (0, 0))/Hleq; rewrite !nth_zip.
  + rewrite size_zip Hsz minnn => Hi.
    by rewrite !nth_default ?Hsz.
- move=> [Hsz Hall]; rewrite Hsz; split; first by [].
  apply/allP => /= [[a b]] Hin.
  have:= nth_index (0, 0) Hin; move: Hin; rewrite -index_mem.
  move: (index _ _) => i /=.
  rewrite size_zip Hsz minnn => Hi.
  rewrite nth_zip //= => [] [<- <-].
  exact: Hall.
Qed.

Lemma vctleq_refl : reflexive vctleq.
Proof. by move=> v; apply/vctleqP. Qed.
Lemma vctleq_trans : transitive vctleq.
Proof.
move=> v2 v1 v3 /vctleqP [Hsz12 H12] /vctleqP [Hsz23 H23].
apply/vctleqP; rewrite Hsz12; split; first by [].
by move=> i; exact: leq_trans (H12 i) (H23 i).
Qed.
Lemma vctleq_anti : antisymmetric vctleq.
Proof.
move=> v1 v2 /andP [/vctleqP [Hsz12 H12] /vctleqP [_ H21]].
apply (eq_from_nth Hsz12 (x0 := 0)) => i _.
by apply anti_leq; rewrite H12 H21.
Qed.

Lemma vctleq_rightsizesum t1 t2 :
  right_sizes t1 <=V right_sizes t2 ->
  rightsizesum t1 <= rightsizesum t2 ?= iff (t1 == t2).
Proof.
rewrite /vctleq -!rightsizesumE -(inj_eq (can_inj right_sizesK)) => /andP [].
elim: (right_sizes t1) (right_sizes t2) => [| u0 u IHu] [| v0 v] //=.
rewrite eqSS => /IHu{IHu}Hrec /andP [H0 /Hrec{Hrec}] [Hleq Heq].
exact: leqif_add.
Qed.

Lemma all_leqzip_refl l : all (fun p => p.1 <= p.2) (zip l l).
Proof. by elim: l => //= a l ->; rewrite leqnn. Qed.

Lemma size_vctmin v1 v2 : size (vctmin v1 v2) = minn (size v1) (size v2).
Proof. by rewrite size_map size_zip. Qed.
Lemma nth_vctmin v1 v2 i :
  nth 0 (vctmin v1 v2) i = minn (nth 0 v1 i) (nth 0 v2 i).
Proof.
rewrite /vctmin.
case: (ltnP i (minn (size v1) (size v2))) => Hi.
- rewrite (nth_map (0,0)) ?size_zip //=.
  by rewrite !nth_zip_cond ?size_zip Hi /=.
- rewrite nth_default; last by rewrite size_map size_zip.
  move: Hi.
  by rewrite geq_min => /orP [] /(nth_default 0) ->; rewrite ?min0n ?minn0.
Qed.

Lemma vctminC: commutative vctmin.
Proof.
move=> v1 v2.
apply (eq_from_nth (x0 := 0)); first by rewrite !size_vctmin minnC.
by move=> i Hi; rewrite !nth_vctmin minnC.
Qed.

Lemma vctminPr v1 v2 :
  size v1 = size v2 -> vctmin v1 v2 <=V v2.
Proof.
move=> Hsz; apply/vctleqP.
rewrite size_vctmin Hsz minnn; split; first by [].
move=> i; rewrite nth_vctmin.
exact: geq_minr.
Qed.

Lemma vctminPl v1 v2 :
  size v1 = size v2 -> vctmin v1 v2 <=V v1.
Proof. by move=> H; rewrite vctminC; apply vctminPr; rewrite H. Qed.

Lemma vctminP v1 v2 v :
  v <=V v1 -> v <=V v2 -> v <=V (vctmin v1 v2).
Proof.
move=> /vctleqP [Hsz1 Hv1] /vctleqP [Hsz2 Hv2].
apply/vctleqP; rewrite size_vctmin -Hsz1 -Hsz2 minnn; split; first by [].
by move=> i; rewrite nth_vctmin leq_min Hv1 Hv2.
Qed.

Lemma vctmin_Tamari v1 v2 :
  size v1 = size v2 ->
  v1 \is a TamariVector ->
  v2 \is a TamariVector ->
  vctmin v1 v2 \is a TamariVector.
Proof.
move=> Hsz /TamariP [Hleq1 H1] /TamariP [Hleq2 H2].
apply/TamariP; rewrite size_vctmin Hsz minnn; split.
- move=> i Hi {Hleq1 H1 H2}; rewrite nth_vctmin addn_minl.
  exact: leq_ltn_trans (geq_minr _ _) (Hleq2 _ Hi).
- move=> i j {Hleq1 Hleq2}; rewrite !nth_vctmin !addn_minl.
  rewrite leq_min=> /andP [Hij /andP [Hj1 Hj2]].
  by rewrite leq_min !geq_min H1 /= ?H2 ?orbT // Hij.
Qed.


(** * Isomorphism between Tamari order on binary trees and Tamari vectors *)

Lemma rotations_vctleq_impl t1 t2 :
  t1 \in rotations t2 -> right_sizes t2 <=V right_sizes t1.
Proof.
move=> Hrot; apply/vctleqP.
split; first  by rewrite !size_right_sizes (size_rotations Hrot).
elim: t2 t1 Hrot => [//|l IHl r IHr] t2.
move/rotationP => [a] [b] [c] [] [H1 H2].
- rewrite /= {IHl IHr}; subst t2 => /=.
  move: H1 => [Hl Hr]; subst l r => /=.
  rewrite -!catA !cat_cons => i.
  rewrite !nth_cat; case: ltnP => // _.
  by case: (i - _) => //=; rewrite add1n addSnnS leq_addr.
- move: H1 => [Ha Hc]; subst a; subst c; subst t2 => Hrot.
  have:= IHl _ Hrot => {IHl IHr} Hrec i /=.
  rewrite !nth_cat !size_right_sizes (size_rotations Hrot).
  by case: ltnP.
- move: H1 => [Ha Hc]; subst a; subst b; subst t2 => Hrot.
  have:= IHr _ Hrot => {IHl IHr} Hrec i /=.
  rewrite !nth_cat !size_right_sizes (size_rotations Hrot).
  case: ltnP => // _.
  by case: (i - _) => //=; rewrite add1n addSnnS leq_addr.
Qed.

Lemma Tamari_add_head v0 v :
  v0 :: v \is a TamariVector ->
  v0 < size v ->
  (nth 0 v v0 + v0).+1 :: v \is a TamariVector.
Proof.
move => /Tamari_consP [_ Hv Htam0] Hv0.
have /TamariP [Hc Htamv] := Hv.
apply/Tamari_consP; split => //; first exact: Hc.
move=> i; rewrite !ltnS => H.
  case: (ltngtP i v0) => [ltnv0i | ltniv0 | -> //].
  + exact: leq_trans (ltnW (Htam0 i ltnv0i)) (leq_addl _ _).
  + by apply: Htamv; rewrite ltniv0 H.
Qed.

Lemma rotations_add_head v0 v t :
  v0 :: v \is a TamariVector ->
  (nth 0 v v0 + v0).+1 :: v \is a TamariVector ->
  from_vct_acc t ((nth 0 v v0 + v0).+1 :: v) \in
    rotations (from_vct_acc t (v0 :: v)).
Proof.
set v1 := nth 0 v v0 => Htam0 Htam1.
have {Htam1} Hv1 : (nth 0 v v0 + v0).+1 <= size v.
  by move/Tamari_consP: Htam1 => [].
have Hv0 : v0 < size v by apply: leq_ltn_trans (leq_addl _ _) Hv1.
have -> : v = (take v0 v) ++
           v1 :: (take v1 (drop v0.+1 v)) ++ (drop (v1 + v0.+1) v).
  rewrite -drop_drop cat_take_drop.
  rewrite -{1}(cat_take_drop v0 v); congr (_ ++ _).
  rewrite -add1n -drop_drop drop1.
  have -> : v1 = head 0 (drop v0 v) by rewrite -nth0 nth_drop addn0.
  apply/esym/cons_head_behead.
  by apply/eqP/nilP; rewrite /nilp size_drop subn_eq0 -ltnNge.
have szvl : size (take v0 v) = v0 by rewrite size_take Hv0.
have szvm : size (take v1 (drop v0.+1 v)) = v1.
  rewrite size_takel // size_drop.
  by move: Hv1 => /(leq_sub2r v0.+1); rewrite subSS addnK.
rewrite /from_vct !from_vct_accE.
rewrite !drop_cat !take_cat szvl ltnn subnn drop0 cats0.
rewrite -addSn ltnNge leq_addl /= addnK /=.
rewrite from_vct_accE !take_cat szvm ltnn subnn take0 cats0.
rewrite drop_cat szvm ltnn subnn drop0.
have {Htam0} Htam := Tamari_take Htam0.
rewrite (from_vct_cat _ _ Htam) from_vct_accE.
rewrite -{1 3}szvm take_size drop_size from_vct_acc_nil.
rewrite from_vct_cat_leftE [X in rotations X]from_vct_cat_leftE.
apply catleft_rotations.
move: (from_vct_acc _ (take v0 _)) => tb.
move: (from_vct_acc _ (take v1 _)) => tc.
by apply/rotationP; exists t, tb, tc; exact: Or31.
Qed.

Lemma Tamari_add_min u v0 v w0 w :
  u ++ w0 :: w \is a TamariVector ->
  u ++ v0 :: v <=V u ++ w0 :: w ->
  v0 < w0 ->
  nth 0 v v0 + v0 < w0.
Proof.
move/Tamari_catr/Tamari_consP => [_ _ Hv] Hleq /Hv/(leq_ltn_trans _); apply.
rewrite leq_add2r.
move/vctleqP : Hleq => [_ /(_ ((size u) + v0.+1))].
rewrite !nth_cat /=.
by rewrite [_ + _ < _]ltnNge leq_addr /= addKn.
Qed.

Lemma Tamari_add_bounded u v0 v w0 w :
  u ++ v0 :: v \is a TamariVector ->
  u ++ w0 :: w \is a TamariVector ->
  u ++ v0 :: v <=V u ++ w0 :: w ->
  v0 < w0 ->
  u ++ (nth 0 v v0 + v0).+1 :: v \is a TamariVector.
Proof.
elim: u => [| u0 u IHu] Hv Hw /= Hleq H0.
  apply Tamari_add_head; first by [].
  move: Hleq => /vctleqP [/=/eq_add_S -> _]; apply (leq_trans H0).
  by have:= Hw => /Tamari_consP [].
apply/Tamari_consP; split.
- by move/Tamari_consP: Hv => []; rewrite !size_cat /=.
- apply: IHu => //.
  + by move/Tamari_consP: Hv => [].
  + by move/Tamari_consP: Hw => [].
  + move: Hleq; rewrite /vctleq /= => /and3P [].
    by rewrite eqSS => -> _ ->.
- move=> i Hi {IHu}; rewrite nth_cat.
  case: (ltngtP i (size u)) => Hiu.
  + move/Tamari_consP: Hv => [_ _ /(_ i Hi)].
    by rewrite nth_cat Hiu.
  + have/Tamari_consP := Hv => [] [_ _ /(_ i Hi)].
    rewrite nth_cat [i < size u]ltnNge (ltnW Hiu) /=.
    move: Hiu; rewrite -subn_gt0.
    by case: (i - size u).
  + subst i; rewrite subnn /=.
    have/Tamari_consP := Hw => [] [_ _ /(_ _ Hi)].
    rewrite nth_cat ltnn subnn /= => /(leq_ltn_trans _); apply.
    rewrite leq_add2r.
    exact: Tamari_add_min Hw Hleq H0.
Qed.

Lemma rotations_add u v0 v :
  u ++ v0 :: v \is a TamariVector ->
  u ++ (nth 0 v v0 + v0).+1 :: v \is a TamariVector ->
  from_vct (u ++ (nth 0 v v0 + v0).+1 :: v)
           \in rotations (from_vct (u ++ v0 :: v)).
Proof.
rewrite /from_vct; move: BinLeaf.
have [n/ltnW] := ubnP (size u); elim: n => [|n IHn] in u v0 v *.
  by rewrite leqn0 => /nilP -> /=; apply: rotations_add_head.
case: u => [_ | u0 u] //=; first exact: rotations_add_head.
rewrite ltnS => Hsz t Htam0 Htam1.
case: (leqP u0 (size u)) => Hu0; rewrite !(from_vct_accE t).
- move/(Tamari_drop u0.+1): Htam0.
  move/(Tamari_drop u0.+1): Htam1.
  have dropl_cat d (s1 : seq nat) :
      d <= size s1 -> forall s2, drop d (s1 ++ s2) = drop d s1 ++ s2.
    rewrite leq_eqVlt => /orP [/eqP |] H s; rewrite drop_cat H //.
    by rewrite ltnn subnn drop0 drop_size.
  rewrite /= !(takel_cat _ Hu0) !(dropl_cat _ _ Hu0) => Htam0 Htam1.
  apply: IHn => //.
  rewrite size_drop leq_subLR.
  exact: leq_trans Hsz (leq_addl _ _).
- have H0 : v0 < (u0 - size u).-1.
    rewrite -ltnS; apply: (leq_trans _ (leqSpred _)).
    rewrite -(ltn_add2r (size u)) subnK; last exact: ltnW.
    move/Tamari_consP: Htam1 => [_ _ /(_ _ Hu0)].
    rewrite nth_cat ltnn subnn /=.
    rewrite -[(_ + v0).+1]addnS -addnA /=.
    exact: (leq_ltn_trans (leq_addl _ _)).
  move/Tamari_take: Htam0.
  move/Tamari_take: Htam1.
  rewrite !take_cat !drop_cat ltnNge (ltnW Hu0) /=.
  have:= Hu0; rewrite -subn_gt0 => /prednK <- /= => Htam0 Htam1.
  rewrite from_vct_cat_leftE [X in rotations X]from_vct_cat_leftE.
  apply catleft_rotations; apply rotations_right_sub.
  move: Htam0.
  have -> : nth 0 v v0 = nth 0 (take (u0 - size u).-1 v) v0 by rewrite nth_take.
  exact: IHn.
Qed.

Lemma rotations_add_bounded u v0 v w0 w :
  u ++ v0 :: v \is a TamariVector ->
  u ++ w0 :: w \is a TamariVector ->
  u ++ v0 :: v <=V u ++ w0 :: w ->
  v0 < w0 ->
  from_vct (u ++ (nth 0 v v0 + v0).+1 :: v)
           \in rotations (from_vct (u ++ v0 :: v)).
Proof.
move=> Hv Hw Hleq H0.
apply: rotations_add => //.
exact: (Tamari_add_bounded Hv Hw Hleq H0).
Qed.

Lemma vctleq_rotation t1 t2 :
  right_sizes t1 <=V right_sizes t2 ->
  t1 != t2 ->
  exists t, t \in rotations t1 /\ right_sizes t <=V right_sizes t2.
Proof.
move=> Hvctleq Huv.
have/vctleqP:= Hvctleq => [] [Hsz Hleq].
have Hneq : exists i, nth 0 (right_sizes t1) i < nth 0 (right_sizes t2) i.
  have {Huv} Hneq : (right_sizes t1) != (right_sizes t2).
    move: Huv; apply contra => /eqP/(congr1 from_vct).
    by rewrite !right_sizesK => ->.
  move: Hsz Hneq Hleq {Hvctleq}.
  elim: (right_sizes t1) (right_sizes t2) => {t1 t2} [| u0 u IHu] [| v0 v] //=.
  move/eq_add_S => Hsz; rewrite eqseq_cons negb_and => /orP [] Hneq Hleq.
  - exists 0; rewrite /= ltn_neqAle Hneq /=.
    exact: (Hleq 0).
  - have {}Hleq i : nth 0 u i <= nth 0 v i by apply: Hleq i.+1.
    have [i Hi] := IHu _ Hsz Hneq Hleq.
    by exists i.+1.
case: (ex_minnP Hneq) => {Hneq} i.
set v0 := nth 0 (right_sizes t1) i.
set w0 := nth 0 (right_sizes t2) i => H0.
have Hi : i < size (right_sizes t1).
  move: H0; apply contraLR; rewrite -!ltnNge !ltnS /v0 /w0 => H.
  by rewrite nth_default; last by rewrite -Hsz.
pose u := take i (right_sizes t1).
pose v := drop i.+1 (right_sizes t1).
pose w := drop i.+1 (right_sizes t2) => Hmin.
have Hv : right_sizes t1 = u ++ v0 :: v.
  rewrite /u /v -{1}(cat_take_drop i (right_sizes t1)); congr (_ ++ _).
  rewrite -add1n -drop_drop drop1.
  have -> : v0 = head 0 (drop i (right_sizes t1)).
    by rewrite -nth0 nth_drop addn0.
  apply/esym/cons_head_behead.
  by apply/eqP/nilP; rewrite /nilp size_drop subn_eq0 -ltnNge.
have {Hmin} Hw : right_sizes t2 = u ++ w0 :: w.
  rewrite /u /v /w -{1}(cat_take_drop i (right_sizes t2)); congr (_ ++ _).
  - apply (eq_from_nth (x0 := 0)); rewrite !size_take -Hsz Hi //.
    move=> j Hj; rewrite !nth_take -?hsz //.
    apply anti_leq; rewrite Hleq andbT.
    move: Hj; apply contraLR; rewrite -leqNgt -ltnNge.
    exact: Hmin.
  - rewrite -add1n -drop_drop drop1.
    have -> : w0 = head 0 (drop i (right_sizes t2)).
      by rewrite -nth0 nth_drop addn0.
    apply/esym/cons_head_behead.
    by apply/eqP/nilP; rewrite /nilp size_drop subn_eq0 -ltnNge -Hsz.
move: Hvctleq (right_sizesP t1) (right_sizesP t2).
rewrite -{3}(right_sizesK t1); rewrite Hv Hw => Hvctleq Htamv Htamw.
exists (from_vct (u ++ (nth 0 v v0 + v0).+1 :: v)).
split; first exact: rotations_add_bounded Htamv Htamw Hvctleq H0.
have Htam0 := Tamari_add_bounded Htamv Htamw Hvctleq H0.
rewrite (from_vctK Htam0); apply/vctleqP.
split => [|j]; first by rewrite -Hw -Hsz Hv !size_cat.
have Hieq : i = size u by rewrite /u size_take Hi.
case: (ltngtP j i) => Hj.
  + by rewrite !nth_cat -Hieq Hj.
  + move/(_ j): Hleq; rewrite Hv Hw => /=.
    rewrite !nth_cat -Hieq [j < i]ltnNge (ltnW Hj) /=.
    move: Hj; rewrite -subn_gt0.
    by case: (j - i).
  + subst j. rewrite Hieq !nth_cat ltnn subnn /=.
    exact: Tamari_add_min Htamw Hvctleq H0.
Qed.

Theorem rotations_right_sizesP t1 t2 :
  reflect
    (exists u v0 v,
        right_sizes t1 = u ++ v0 :: v /\
        right_sizes t2 = u ++ (nth 0 v v0 + v0).+1 :: v)
    (t2 \in rotations t1).
Proof.
apply (iffP idP); first last.
  move=> [u] [v0] [v] [Ht1 Ht2].
  rewrite -(right_sizesK t1) -(right_sizesK t2) Ht1 Ht2.
  by apply: rotations_add; rewrite -?Ht1 -?Ht2; apply: right_sizesP.
have [n] := ubnPleq (size_tree t1); elim: n => [|n IHn] in t1 t2 *.
  by rewrite leqn0 => /LeafP ->.
rewrite leq_eqVlt => /orP [/eqP Hsz Hrot|]; last by rewrite ltnS; exact: IHn.
move/rotationP: Hrot Hsz => [a] [b] [c] [] [->{t1} ->{t2}] /=.
- exists (right_sizes a), (size_tree b),
     (right_sizes b ++ size_tree c :: right_sizes c); split.
  + by rewrite -!catA.
  + by rewrite nth_cat size_right_sizes ltnn subnn nth0 /= add1n addSn addnC.
- move/IHn => {IHn} Hrec.
  rewrite /= add1n addSn => /succn_inj Hsz.
  have: size_tree a <= n by rewrite -Hsz leq_addr.
  move/Hrec => {Hrec} [u] [v0] [v] [Ha Hb].
  exists u, v0, (v ++ size_tree c :: right_sizes c); split.
  + by rewrite Ha -!catA.
  + rewrite Hb nth_cat.
    suff -> : v0 < size v by rewrite -!catA.
    have := right_sizesP b; rewrite Hb => /Tamari_catr/Tamari_consP [H _ _].
    exact: (leq_ltn_trans (leq_addl _ _) H).
- move/IHn => {IHn} Hrec.
  rewrite /= add1n addSn => /succn_inj Hsz.
  have: size_tree b <= n by rewrite -Hsz leq_addl.
  move/Hrec => {Hrec} [u] [v0] [v] [Hb Hc].
  exists (right_sizes a ++ size_tree b :: u), v0, v; split.
  + by rewrite Hb -!catA.
  + rewrite Hc /= -!catA /=.
    suff -> : size_tree b = size_tree c by [].
    by rewrite -!size_right_sizes Hb Hc !size_cat /=.
Qed.

Lemma vct_succ u v0 v w :
  w \is a TamariVector ->
  u ++ v0 :: v  <=V  w ->
  w  <=V  u ++ (nth 0 v v0 + v0).+1 :: v ->
  w = u ++ v0 :: v  \/  w = u ++ (nth 0 v v0 + v0).+1 :: v.
Proof.
move=> Htamw Hvw Hwv0.
case: (altP (w =P u ++ v0 :: v)) => [Heq|Hneq]; first by left.
right; pose w0 := nth 0 w (size u).
have Hw : w = u ++ w0 :: v.
  have Hsz : size w = (size u + size v).+1.
    by move: Hvw => /vctleqP [<- _]; rewrite !size_cat /= addnS.
  apply (eq_from_nth (x0 := 0)); first by rewrite Hsz size_cat /= addnS.
  move=> i; rewrite Hsz ltnS => Hi.
  case: (ltngtP i (size u)) => [Hiu | Hui | ->].
  - rewrite nth_cat Hiu; apply/anti_leq/andP; split.
    + by move/vctleqP: Hwv0 => [_ /(_ i)]; rewrite nth_cat Hiu.
    + by move/vctleqP: Hvw  => [_ /(_ i)]; rewrite nth_cat Hiu.
  - have Hf : i < size u = false by rewrite ltnNge (ltnW Hui).
    rewrite nth_cat Hf.
    have:= Hui; rewrite -subn_gt0; case Hd : (i - size u) => [| d] //= _.
    apply/anti_leq/andP; split.
    + by move/vctleqP: Hwv0 => [_ /(_ i)]; rewrite nth_cat Hf Hd.
    + by move/vctleqP: Hvw  => [_ /(_ i)]; rewrite nth_cat Hf Hd.
    + by rewrite nth_cat ltnn subnn.
rewrite Hw; suff -> : w0 = (nth 0 v v0 + v0).+1 by [].
apply/anti_leq/andP; split.
- by move/vctleqP: Hwv0 => [_ /(_ (size u))]; rewrite Hw !nth_cat ltnn subnn.
- have Hv0w0 : v0 < w0.
    rewrite ltn_neqAle; apply/andP; split.
    + by move: Hneq; apply contra; rewrite Hw => /eqP ->.
    + by move/vctleqP: Hvw => [_ /(_ (size u))]; rewrite Hw !nth_cat ltnn subnn.
- by rewrite Hw in Htamw Hvw; exact: (Tamari_add_min Htamw).
Qed.


Theorem Tamari_vctleq n (t1 t2 : bintreesz n) :
  (right_sizes t1 <=V right_sizes t2) = (t1 <=T t2).
Proof.
apply/idP/idP.
- have [i] := ubnPleq (rightsizesum t2 - rightsizesum t1).
  rewrite leq_subLR.
  elim: i => [|i IHi] in t1 t2 * => Hsum Hleq.
    rewrite addn0 in Hsum.
    suff -> : t1 = t2 by apply: le_refl.
    apply/val_inj/eqP => /=.
    have [Hsum2 Heq] := vctleq_rightsizesum Hleq.
    rewrite -Heq; apply/eqP/anti_leq.
    by rewrite Hsum Hsum2.
  case: (altP (t1 =P t2)) => [-> | Hneq]; first by apply: le_refl.
  have [/= tt [Hrot Htleq]] := vctleq_rotation Hleq Hneq.
  have Hszt : size_tree tt == n by rewrite (size_rotations Hrot) bintreeszP.
  pose t := BinTreeSZ Hszt.
  rewrite -[tt]/(trval t) in Hrot Htleq.
  have:= rightsizesum_gt Hrot.
  rewrite -(leq_add2r i) addSnnS => /(leq_trans Hsum).
  move=> /IHi{IHi}/(_ Htleq) /(le_trans _); apply.
  by apply: ltW; apply: rotations_Tamari.
- rewrite TamariE => /connectP /= [p].
  elim: p t1 t2 => /= [| p0 p IHp] t1 t2.
    by move => _ ->; exact: vctleq_refl.
  move/andP => [Hrot Hpath Ht2].
  suff /vctleq_trans : right_sizes t1 <=V right_sizes p0 by apply; apply IHp.
  exact: rotations_vctleq_impl.
Qed.


Module TamariLattice.
Section Def.

Variable n : nat.
Implicit Types t : bintreesz n.

Lemma Tmeet_proof t1 t2 :
  size_tree (from_vct (vctmin (right_sizes t1) (right_sizes t2))) == n.
Proof.
by rewrite size_from_vct size_vctmin !size_right_sizes !bintreeszP minnn.
Qed.
Definition Tmeet t1 t2 := BinTreeSZ (Tmeet_proof t1 t2).
Definition Tjoin t1 t2 := flipsz (Tmeet (flipsz t1) (flipsz t2)).

Lemma TmeetC  t1 t2 : Tmeet t1 t2 = Tmeet t2 t1.
Proof. by rewrite /Tmeet /=; apply val_inj; rewrite /= vctminC. Qed.

Lemma TmeetPr t1 t2 : Tmeet t1 t2 <=T t2.
Proof.
have Hszeq : size (right_sizes t1) = size (right_sizes t2).
  by rewrite !size_right_sizes !bintreeszP.
rewrite /Tmeet -Tamari_vctleq /= from_vctK ?vctmin_Tamari //.
exact: vctminPr.
Qed.

Lemma TmeetE t t1 t2 : (t <=T Tmeet t1 t2) = (t <=T t1) && (t <=T t2).
Proof.
apply/idP/andP => [/le_trans Htr| []].
  by split; apply: Htr; first rewrite TmeetC; rewrite TmeetPr.
have Hszeq : size (right_sizes t1) = size (right_sizes t2).
  by rewrite !size_right_sizes !bintreeszP.
rewrite /Tmeet -!Tamari_vctleq /= from_vctK ?vctmin_Tamari //.
exact: vctminP.
Qed.
Lemma TjoinE t1 t2 t : (Tjoin t1 t2 <=T t) = (t1 <=T t) && (t2 <=T t).
Proof. by rewrite /Tjoin -![_ <=T t]Tamari_flip flipszK TmeetE. Qed.

Definition latticeMixin := MeetJoinLeMixin TmeetE TjoinE.
Canonical latticeType := LatticeType (bintreesz n) latticeMixin.

End Def.

Section Theory.

Variable n : nat.
Implicit Types t : bintreesz n.

Lemma right_sizes_meet t1 t2 :
  right_sizes (t1 /\T t2) = vctmin (right_sizes t1) (right_sizes t2).
Proof.
rewrite /Order.meet /= from_vctK // vctmin_Tamari //.
by rewrite !size_right_sizes !bintreeszP.
Qed.

Lemma flipsz_meet t1 t2 : flipsz (t1 \/T t2) = (flipsz t1 /\T flipsz t2).
Proof. by apply val_inj => /=; rewrite flipK. Qed.
Lemma flipsz_join t1 t2 : flipsz (t1 /\T t2) = (flipsz t1 \/T flipsz t2).
Proof. by rewrite -[RHS]flipszK flipsz_meet !flipszK. Qed.

Fact leftcomb_bottom t : leftcombsz n <=T t.
Proof.
rewrite -Tamari_vctleq right_sizes_left_comb.
apply/vctleqP; split; first by rewrite size_nseq size_right_sizes bintreeszP.
by move=> i; rewrite nth_nseq if_same.
Qed.

Fact rightcomb_top t : t <=T rightcombsz n.
Proof. by rewrite -Tamari_flip flipsz_rightcomb; exact: leftcomb_bottom. Qed.

Definition bottomMixin := BottomMixin leftcomb_bottom.
Canonical blatticeType := BLatticeType (bintreesz n) bottomMixin.
Definition topMixin := TopMixin rightcomb_top.
Canonical tblatticeType := TBLatticeType (bintreesz n) topMixin.
Canonical finLatticeType :=
  Eval hnf in [finLatticeType of (bintreesz n)].

Lemma botETamari : 0%O = leftcombsz n.
Proof. by []. Qed.
Lemma topETamari : 1%O = rightcombsz n.
Proof. by []. Qed.

End Theory.
Module Exports.

Set Warnings "-redundant-canonical-projection".
Canonical latticeType.
Canonical blatticeType.
Canonical tblatticeType.
Canonical finLatticeType.
Set Warnings "+redundant-canonical-projection".

Definition right_sizes_meet := right_sizes_meet.
Definition flipsz_meet := flipsz_meet.
Definition flipsz_join := flipsz_join.
Definition botETamari := botETamari.
Definition topETamari := topETamari.

End Exports.
End TamariLattice.
Export TamariLattice.Exports.


Section TamariCover.

Variable n : nat.
Implicit Types t : bintreesz n.

Lemma Tamari_succ t1 t2 t :
  trval t2 \in rotations t1 -> t1 <=T t -> t <=T t2 -> t = t1 \/ t = t2.
Proof.
move/rotations_right_sizesP => [u] [v0] [v] [Ht1 Ht2].
move: (right_sizesP t); rewrite -!Tamari_vctleq Ht1 Ht2 => Htam H1 H2.
have [] := vct_succ Htam H1 H2.
- rewrite -Ht1 => /(congr1 from_vct); rewrite !right_sizesK => Heq.
  by left; apply val_inj.
- rewrite -Ht2 => /(congr1 from_vct); rewrite !right_sizesK => Heq.
  by right; apply val_inj.
Qed.

Lemma covers_Tamari t1 t2 : (trval t2 \in rotations t1) = (covers t1 t2).
Proof.
apply/idP/coversP => [Hrot|].
- split => /= [|z /andP[H1 H2]]; first exact: rotations_Tamari.
  have [HA1|HA2] := Tamari_succ Hrot (ltW H1) (ltW H2).
  + by move: H1; rewrite HA1 ltxx.
  + by move: H2; rewrite HA2 ltxx.
- rewrite lt_def => [[/andP[neq le12 Hcov]]].
  move: le12; rewrite TamariE => /connectP [/= [|s0 [|s1 s]] /= Hpath Ht2].
  + by rewrite Ht2 eqxx in neq.
  + by move: Hpath; rewrite andbT Ht2.
  + move: Hpath => /and3P [Hs0 Hs1 Hpath]; exfalso; apply: (Hcov s0).
    rewrite (rotations_Tamari Hs0) /=.
    apply: (lt_le_trans (rotations_Tamari Hs1)).
    by rewrite TamariE; apply/connectP; exists s.
Qed.

End TamariCover.


