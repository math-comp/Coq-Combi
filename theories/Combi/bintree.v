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
- [catalan n] == the number of binary trees of size [n]
- [rotations t] == the list of right rotations of the tree [t]
- [rightcomb n] == the right comb binary tree of size [n] as a [bintree]
- [leftcomb n] == the left comb binary tree of size [n] as a [bintree]
- [flip t] == the left/right mirror of [t]
- [sumsizeleft t] == the sum over all node of [t] of the size of the left
        subtree.

Binary trees of size n:

- [bintreesz n] == the sigma type for trees of size [n]. This is canonically
        a [finType]
- [Tamari t1 t2] == [t1] is smaller than [t2] in the tamari order.
- [rightcombsz n] == the right comb binary tree of size [n] as a [bintreesz n]
- [leftcombsz n] == the left comb binary tree of size [n] as a [bintreesz n]
- [flipsz t] == the left/right mirror of [t] as a [bintreesz n]

 *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun bigop ssrnat eqtype fintype choice seq.
From mathcomp Require Import fingraph path finset.

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
  BinTreeSZ {tval :> bintree; _ : size_tree tval == n}.
Canonical bintreesz_subType := Eval hnf in [subType for tval].
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

Fixpoint rotations t :=
  if t is BinNode l r then
    let rec := [seq BinNode lrot r | lrot <- rotations l] ++
               [seq BinNode l rrot | rrot <- rotations r]
    in if l is BinNode ll lr then
         BinNode ll (BinNode lr r) :: rec
       else rec
  else [::].

Lemma rotation_left_sub l1 l2 r :
  l1 \in rotations l2 -> BinNode l1 r \in rotations (BinNode l2 r).
Proof.
case H2 : l2 => [/= |ll2 lr2]; first by rewrite in_nil.
rewrite -H2 /= {2}H2 => Hin.
rewrite inE; apply/orP; right.
rewrite mem_cat; apply/orP; left.
by apply/mapP; exists l1.
Qed.

Lemma rotation_right_sub l r1 r2 :
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
  + exact: rotation_left_sub.
  + exact: rotation_right_sub.
Qed.

Lemma size_rotations t t' :
  t' \in rotations t -> size_tree t' = size_tree t.
Proof.
elim: t t' => [//= | l IHl r IHr] t' /=.
case H: l => [| ll lr] //; first by move/mapP => [/= lrot /IHr <- ->].
rewrite inE => /orP [/eqP ->|]; first by rewrite /= !(add1n, addSn, addnS) addnA.
by rewrite -H mem_cat => /orP [/mapP /= [lrot/IHl]|/mapP /= [rrot/IHr]] <- ->.
Qed.

Lemma rightcomb_rotations t :
  (rotations t == [::]) = (t == rightcomb (size_tree t)).
Proof.
apply/eqP/eqP => [|->].
- elim: t => [//=| l _ r IHr].
  case: l => [| ll lr] //= Hrot.
  have {Hrot} /IHr -> : rotations r = [::] by move: Hrot; case: (rotations r).
  by rewrite size_rightcomb.
- by elim: (size_tree t) => {t} //= n ->.
Qed.

Lemma rotation_flip_impl t1 t2:
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

Lemma rotation_flip t1 t2:
  (t1 \in rotations t2) = (flip t2 \in rotations (flip t1)).
Proof.
apply/idP/idP; first exact: rotation_flip_impl.
by move=> /rotation_flip_impl; rewrite !flipK.
Qed.

Fixpoint sumsizeleft t :=
  if t is BinNode l r then
    size_tree l + sumsizeleft l + sumsizeleft r
  else 0.

Lemma sumsizeleft_gt t t' :
  t' \in rotations t -> sumsizeleft t > sumsizeleft t'.
Proof.
elim: t t' => [//| l IHl r IHr] t'.
case Hl : l IHl => [| ll lr] // IHl.
  rewrite /= !add0n => /mapP [/= rot /IHr Hleq -> {t'}].
  by rewrite /= !add0n.
rewrite -Hl /= {1}Hl /= inE => /orP [/eqP -> /=|].
  rewrite Hl /= add1n !addSn ltnS -!addnA leq_add2l.
  rewrite !addnA !leq_add2r addnC leq_add2r.
  exact: leq_addr.
rewrite -Hl in IHl.
rewrite mem_cat => /orP [/mapP /= [lrot Hlrot] | /mapP /= [rrot Hrrot]] -> /=.
- rewrite (size_rotations Hlrot) ltn_add2r ltn_add2l.
  exact: IHl.
- rewrite !ltn_add2l.
  exact: IHr.
Qed.

Lemma rotations_neq t t' : t' \in rotations t -> t != t'.
Proof.
move/sumsizeleft_gt; apply contraL => /eqP ->.
by rewrite ltnn.
Qed.



Section Tamari.

Variable n : nat.
Implicit Type t : bintreesz n.

Definition Tamari := connect (fun t1 t2 : bintreesz n => grel rotations t1 t2).
Local Notation "x '<=T' y" := (Tamari x y) (at level 70, y at next level).

Lemma Tamari_rotations t t' :
  val t' \in rotations t -> t <=T t'.
Proof. by move=> H; apply connect1; rewrite /grel /=. Qed.

Lemma Tamari_refl : reflexive Tamari.
Proof. exact: connect0. Qed.

Lemma Tamari_trans : transitive Tamari.
Proof. exact: connect_trans. Qed.

Lemma Tamari_sumsizeleft t1 t2 :
  t1 <=T t2 -> sumsizeleft t2 <= sumsizeleft t1 ?= iff (t1 == t2).
Proof.
move/connectP => [] /= p.
elim: p t1 t2 => [| t0 p IHp] t1 t2 /=.
  by move=> _ /= ->; split; rewrite // !eq_refl.
move=> /andP [/sumsizeleft_gt Hgt /IHp H/H{IHp H}].
move=> [] /leq_ltn_trans/(_ Hgt) Hlt _ {Hgt}.
split; first exact: (ltnW Hlt).
have:= Hlt; rewrite ltn_neqAle => /andP [/negbTE -> _].
by case: eqP Hlt => [->|] //; rewrite ltnn.
Qed.

Lemma Tamari_anti : antisymmetric Tamari.
Proof.
move=> t1 t2 /andP [ /Tamari_sumsizeleft [leq21 eq]].
move=> /Tamari_sumsizeleft [leq12 _].
by apply/eqP; rewrite -eq eqn_leq leq21 leq12.
Qed.

Local Fact size_rightcombE : size_tree (rightcomb n) == n.
Proof. apply/eqP; exact: size_rightcomb. Qed.
Canonical rightcombsz := BinTreeSZ size_rightcombE.
Local Fact size_leftcombE : size_tree (leftcomb n) == n.
Proof. apply/eqP; exact: size_leftcomb. Qed.
Canonical leftcombsz := BinTreeSZ size_leftcombE.
Local Lemma size_flipE t : size_tree (flip t) == n.
Proof. by rewrite size_flip bintreeszP. Qed.
Canonical flipsz t := BinTreeSZ (size_flipE t).

Lemma flipszK : involutive flipsz.
Proof. move=> t; apply val_inj => /=; exact: flipK. Qed.

Lemma Tamari_flip_impl t1 t2 : (flipsz t2 <=T flipsz t1) -> t1 <=T t2.
Proof.
rewrite /Tamari => /connectP /= [].
case/lastP => [//= _ | p l Hp].
  move=> /(congr1 flipsz); rewrite !flipszK => ->.
  exact: connect0.
rewrite last_rcons => Hl; subst l; move: Hp.
have /eq_path -> :
    (fun t t' => val t' \in rotations t)
    =2 (fun t t' => (fun t' t => val (flipsz t) \in rotations (flipsz t')) t' t).
  by move=> t t' /=; exact: rotation_flip.
rewrite -rev_path /= last_rcons belast_rcons.
have -> : (rev (flipsz t2 :: p)) =
          [seq flipsz t | t <- rcons [seq flipsz t' | t' <- rev p] t2].
  rewrite -[RHS]revK; congr rev.
  rewrite -map_rev rev_rcons /= -map_rev revK.
  rewrite -map_comp (eq_map (f2 := id)); last by move=> x /=; rewrite flipszK.
  by rewrite map_id.
rewrite (map_path (b := pred0)
                  (e' := (fun t t' => val t' \in rotations t))); first last.
  - by apply/hasP => [] [t /=].
  - by rewrite /rel_base => u v _; rewrite /= !flipK.
set pp := rcons _ _ => Hp; apply/connectP; exists pp; first by [].
by rewrite /pp last_rcons.
Qed.

Lemma Tamari_flip t1 t2 : (flipsz t2 <=T flipsz t1) = (t1 <=T t2).
Proof.
apply/idP/idP; first exact: Tamari_flip_impl.
rewrite -{1}(flipszK t1) -{1}(flipszK t2).
exact: Tamari_flip_impl.
Qed.

Lemma rightcomb_bottom t : t <=T rightcombsz.
Proof.
move: {2}#|_| (leqnn #|[set t' | t <=T t' & t != t']|) => bound.
elim: bound t => [| b IHb] t.
  rewrite leqn0 cards_eq0 => /eqP Hlt.
  have {Hlt} : rotations t == [::].
    case Hrot : (rotations t) => [//| t0 r]; exfalso.
    have {Hrot} Hrot : t0 \in rotations t by rewrite Hrot; exact: mem_head.
    move/eqP : (size_rotations Hrot); rewrite bintreeszP => Ht0.
    pose t' := BinTreeSZ Ht0.
    have : t' \in [set t' | t <=T t' & t != t'].
      rewrite inE; rewrite Tamari_rotations //=.
      apply (introN idP) => /eqP /(congr1 val) /= Ht.
      by move/rotations_neq: Hrot; rewrite Ht eq_refl.
    by rewrite Hlt inE.
  rewrite rightcomb_rotations => /eqP Ht.
  suff -> : t = rightcombsz by exact: Tamari_refl.
  by apply val_inj; rewrite /= Ht bintreeszP.
move=> Hleq.
case: (leqP #|[set t' | t <=T t' & t != t']| b) => [| Hlt]; first exact: IHb.
have {Hleq Hlt} Hcard : #|[set t' | t <=T t' & t != t']| = b.+1.
  by apply anti_leq; rewrite Hleq Hlt.
case Hrot : (rotations t) => [| t0 s].
  exfalso => {IHb}.
  have {Hcard} : #|[set t' | t <=T t' & t != t']| > 0 by rewrite Hcard.
  rewrite card_gt0 => /set0Pn [/= t0].
  rewrite inE => /andP [].
  rewrite /Tamari => /connectP [] [_ /= ->|t1 s] /=; first by rewrite eq_refl.
  by rewrite Hrot in_nil.
have {Hrot} Hrot : t0 \in rotations t by rewrite Hrot; exact: mem_head.
move/eqP : (size_rotations Hrot); rewrite bintreeszP => Ht0.
pose t' := BinTreeSZ Ht0.
have:= Hrot; rewrite -[t0]/(val t') => /Tamari_rotations/Tamari_trans.
apply; apply: IHb.
rewrite -ltnS -{}Hcard; apply proper_card.
rewrite /proper; apply/andP; split; apply/subsetP.
- move=> /= z; rewrite !inE => /andP [Ht'z Hneq].
  have Htz : t <=T z by apply: (Tamari_trans _ Ht'z); exact: Tamari_rotations.
  rewrite Htz /=.
  move: Hneq; apply contra => /eqP Heq; subst z.
  apply/eqP; apply Tamari_anti; rewrite Ht'z /=.
  exact: Tamari_rotations.
- move/(_ t'); rewrite !inE.
  rewrite eq_refl /= andbF => H; apply not_false_is_true; apply: H.
  apply/andP; split; first exact: Tamari_rotations.
  exact: rotations_neq.
Qed.

Lemma leftcomb_top t : leftcombsz <=T t.
Proof.
rewrite -Tamari_flip.
suff -> : flipsz leftcombsz = rightcombsz by exact: rightcomb_bottom.
by apply val_inj => /=; exact: flip_leftcomb.
Qed.

