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

We define the following notions

- [bintree] == the type of binary trees this is canonically a [countType]
- [BinLeaf] == the leaf for binary trees
- [BinNode left right] == the binary tree with subtrees [left] [right]
- [size_tree t] == the number of node of the tree [t]
- [enum_bintreesz n] == the list of a trees of size [n]
- [bintreesz n] == the sigma type for trees of size [n]. This is canonically
        a [finType]
- [catalan n] == the number of binary trees of size [n]

 *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun bigop ssrnat eqtype fintype choice seq.

Require Import tools combclass.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


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


Section Size.

Variable (n : nat).

Structure bintreesz : predArgType :=
  BintreeSZ {tval :> bintree; _ : size_tree tval == n}.
Canonical bintreesz_subType := Eval hnf in [subType for tval].
Definition bintreesz_eqMixin := [eqMixin of bintreesz by <:].
Canonical bintreesz_eqType := Eval hnf in EqType bintreesz bintreesz_eqMixin.
Definition bintreesz_choiceMixin := [choiceMixin of bintreesz by <:].
Canonical bintreesz_choiceType :=
  Eval hnf in ChoiceType bintreesz bintreesz_choiceMixin.
Definition bintreesz_countMixin := [countMixin of bintreesz by <:].
Canonical bintreesz_countType :=
  Eval hnf in CountType bintreesz bintreesz_countMixin.

End Size.

(** The intent of the following recursive definition is the recursion of lemma
    [enum_bintreeszE]:
[[
Fixpoint enum_bintreesz n :=
  if n is n'.+1 then
    flatten [seq [seq BinNode tl tr |
                  tl <- enum_bintreesz i,
                  tr <- enum_bintreesz (n - i)] | i <- iota 0 n.+1].
  else [:: [:: BinLeaf]].
]]
however [i] and [n - i] are not structurally smaller than [n.+1] so the
definition is refused by coq as not well founded. So we write the following
function which returns a cache containing the list of the results of
[enum_bintreesz i] for [i = 0 ... n]. Otherwise said, to define the
[enum_bintreesz] function we need a strong [nat] induction where Coq only
allows simple [nat] induction. *)

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

Lemma size_enum_bintreesz n : size (enum_bintreesz_leq n) = n.+1.
Proof. by elim: n => //= n; rewrite size_rcons => ->. Qed.

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

Lemma enum_bintreesz0 : enum_bintreesz 0 = [:: BinLeaf].
Proof. by []. Qed.

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
elim: n {1 3 4}n (leqnn n) t => [| n IHn] i.
  rewrite leqn0 => /eqP -> t.
  by rewrite enum_bintreesz0 inE => /eqP ->.
case: (leqP i n) => [Hi _| Hi Hi1] t; first by move/(IHn i Hi).
have {Hi Hi1 i} -> : i = n.+1.
  by apply anti_leq; rewrite Hi1.
rewrite enum_bintreeszE => /flatten_mapP [j].
rewrite mem_iota /= add0n ltnS => Hj.
have Hnj := leq_subr j n.
move/allpairsP => [[l r] /= [/(IHn j Hj) Hl /(IHn _ Hnj) Hr -> {t}]] /=.
by rewrite Hl Hr add1n addSn addnC subnK.
Qed.

Lemma enum_bintreeszP n :
  all (fun t => size_tree t == n) (enum_bintreesz n).
Proof. by apply/allP => /= t /size_mem_enum_bintreeszP ->. Qed.

Lemma enum_bintreesz_uniq n : uniq (enum_bintreesz n).
Proof.
elim: n {1 3}n (leqnn n) => [| n IHn] i.
  by rewrite leqn0 => /eqP ->.
case: (leqP i n) => [Hi _| Hi Hi1]; first exact: IHn.
have {Hi Hi1 i} -> : i = n.+1.
  by apply anti_leq; rewrite Hi1.
rewrite enum_bintreeszE.
elim: {1 3}(n.+1) (leqnn n.+1) => [| i IHi] //.
rewrite ltnS => Hi.
rewrite -addn1 iota_add add0n /=.
rewrite map_cat flatten_cat /= cats0 cat_uniq.
rewrite {}IHi /=; last exact: (leq_trans Hi).
apply/andP; split.
- apply/hasP => [] /= [[| l r]] /allpairsP/= [[l1 r1] /= []].
  + by move=> _ _ /eqP; rewrite eqE /=.
  + move/size_mem_enum_bintreeszP => Hszl1 _ -> {l r}.
    move/flattenP => [/= ltj /mapP /= [j]].
    rewrite mem_iota /= add0n => Hj ->.
    move/allpairsP => [/= [l r] /= []].
    move/size_mem_enum_bintreeszP => Hszl _ [] Hl1 _.
    move: Hszl1 Hj; rewrite Hl1 Hszl => ->.
    by rewrite ltnn.
- have:= IHn i Hi.
  elim: (enum_bintreesz i) => [// | l ll IHll] /= /andP [Hnotin /IHll{IHll} Hrec].
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
elim: n {1 3 4}n (leqnn n) t => [| n IHn] i.
  by rewrite leqn0 => /eqP -> [].
case: (leqP i n) => [Hi _| Hi Hi1] t; first by move/(IHn i Hi).
have {Hi Hi1 i} -> : i = n.+1.
  by apply anti_leq; rewrite Hi1.
rewrite enum_bintreeszE.
case: t => // l r.
rewrite [X in X -> _]/= add1n addSn eqSS => /eqP Hn.
apply/flattenP.
exists [seq BinNode tl tr
       | tl <- enum_bintreesz (size_tree l),
         tr <- enum_bintreesz (n - (size_tree l))]; first last.
  apply/allpairsP; exists (l, r) => /=; split => //.
  - by apply IHn => //; rewrite -Hn; apply leq_addr.
  - apply IHn => //; first exact: leq_subr.
    by rewrite -Hn addKn.
apply/mapP; exists (size_tree l) => //.
rewrite mem_iota /= add0n ltnS -Hn.
exact: leq_addr.
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


Definition catalan n := #|bintreesz n|.

Lemma catalan0 : catalan 0 = 1.
Proof. by rewrite /catalan cardT -(size_map val) enumT unlock subType_seqP. Qed.

Lemma catalan10 :
  [seq catalan i | i <- iota 0 10] = [:: 1; 1; 2; 5; 14; 42; 132; 429; 1430; 4862].
Proof.
by rewrite /catalan /= !cardT -!(size_map val) !enumT !unlock !subType_seqP.
Qed.

Lemma catalan_rec n :
  catalan n.+1 = \sum_(0 <= i < n.+1) catalan i * catalan (n - i).
Proof.
rewrite /catalan /= !cardT -!(size_map val) !enumT unlock !subType_seqP /=.
rewrite enum_bintreeszE size_flatten.
rewrite /shape -map_comp -sumn_mapE; apply eq_bigr => i _.
rewrite size_allpairs.
by rewrite !cardT -!(size_map val) !enumT unlock !subType_seqP /=.
Qed.
