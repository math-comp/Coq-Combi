(** * Combi.Combi.ordree : Ordered Trees *)
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
(** * Ordered Trees

An _ordered tree_ is a rooted tree such that each node has a possibly empty
list of child that are ordered trees.

Basic definitions:

- [ordtree]   == the type of ordered trees. This is canonically a [countType]
- [forest]    == the type of forest, that is sequence of ordered trees
- [OrdNode f] == the ordered tree with subtrees from the forest [f]

Ordered trees of size n:

- [size_ordtree t]   == the number of node of the ordered tree [t]
- [enum_ordtreesz n] == the list of a ordered trees of size [n]
- [ordtreesz n]      == the Sigma type for ordered trees of size [n].
        This is canonically a [finType] with enumeration [enum_ordtreesz n]

Various Notion:

- [depth_ordtree t]  == the depth of the ordered tree [t], that is the
        maximum number of node on a branch.
- [line_ordtree n]   == the linear tree of size n + 1
 *********************)
From HB Require Import structures.
From mathcomp Require Import all_boot.
Require Import tools combclass bintree.

Set SsrOldRewriteGoalsOrder.  (* change to Unset and remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Inductive type for ordered trees *)
Unset Elimination Schemes.
Inductive ordtree : Set := OrdNode : seq ordtree -> ordtree.
Set Elimination Schemes.
Notation forest := (seq ordtree).

Lemma OrdNode_inj : injective OrdNode.
Proof. by move=> f1 f2 []. Qed.

(** Induction scheme for ordtrees *)
Section Recursion.

Variables (P : ordtree -> Type) (PF : seq ordtree -> Type).
Hypothesis HPnil : PF [::].
Hypothesis IHforest : forall tr f, P tr -> PF f -> PF (tr :: f).
Hypothesis IHtree : forall f, PF f -> P (OrdNode f).

Fixpoint recforest rt f : PF f :=
  if f is tr :: tlf then IHforest (rt tr) (recforest rt tlf)
  else HPnil.
Fixpoint rectree t : P t :=
  let: OrdNode f := t in IHtree (recforest rectree f).

End Recursion.
Definition indtreeforest
  (P : ordtree -> Prop) (PF : forest -> Prop) := @rectree P PF.


Fixpoint eq_forest (eqtr : ordtree -> ordtree -> bool) (f1 f2 : seq ordtree) :=
  match f1, f2 with
  | [::], [::] => true
  | tr1 :: tl1, tr2 :: tl2 => eqtr tr1 tr2 && eq_forest eqtr tl1 tl2
  | _, _ => false
  end.
Fixpoint eq_ordtree tr1 tr2 :=
  match tr1, tr2 with
    OrdNode f1, OrdNode f2 => eq_forest eq_ordtree f1 f2
  end.
Fact eq_ordtreeP : Equality.axiom eq_ordtree.
Proof.
move=> t1 t2; apply: (iffP idP) => [|<-]; first last.
  by apply: (indtreeforest
               (P := fun t => eq_ordtree t t)
               (PF := fun f => eq_forest eq_ordtree f f)) => //= tr f -> ->.
apply: (indtreeforest
          (P := fun t => forall t2, eq_ordtree t t2 -> t = t2)
          (PF := fun f => forall f2, eq_forest eq_ordtree f f2 -> f = f2))
     => {t1 t2}.
- by case.
- by move=> tr f IHt IHf /=; case=> [|t2 f2] // /andP[/IHt-> /IHf->].
- by move=> f IHf [f2] /= /IHf ->.
Qed.
HB.instance Definition _ := hasDecEq.Build ordtree eq_ordtreeP.


Section SimpleRecursion.

Variables (P : ordtree -> Type).
Hypothesis IHtree :
  forall f : forest, (forall t : ordtree, t \in f -> P t) -> P (OrdNode f).
Lemma rec_tree t : P t.
Proof.
apply (rectree (PF := fun f => forall t : ordtree, t \in f -> P t))
      => // tr f Htr Hf tr1.
by rewrite inE; case: eqP => [-> // | _ /= /Hf].
Qed.

End SimpleRecursion.
Definition indtree (P : ordtree -> Prop) := @rec_tree P.


Fixpoint ord_to_bintree (t : ordtree) : bintree :=
  let fix f_to_bin t_to_bin (f : forest) : bintree :=
    match f with
    | [::] => BinLeaf
    | t :: ftl => BinNode (t_to_bin t) (f_to_bin t_to_bin ftl)
    end
  in let: OrdNode f := t in f_to_bin ord_to_bintree f.
Definition forest_to_bintree f := ord_to_bintree (OrdNode f).

Fixpoint bin_to_forest (t : bintree) : forest :=
  if t is BinNode l r then OrdNode (bin_to_forest l) :: bin_to_forest r
  else [::].
Definition bin_to_ordtree t := OrdNode (bin_to_forest t).

Lemma bin_to_forestK : cancel bin_to_forest forest_to_bintree.
Proof. by rewrite /forest_to_bintree /=; elim=> [| l /[swap] r /= -> ->]. Qed.
Lemma bin_to_ordtreeK : cancel bin_to_ordtree ord_to_bintree.
Proof. exact: bin_to_forestK. Qed.

Lemma ord_to_bintreeK : cancel ord_to_bintree bin_to_ordtree.
Proof.
rewrite /bin_to_ordtree; elim/indtree; elim => [// | t f IHf IHt /=].
congr (OrdNode (_ :: _)); first by apply: IHt; rewrite inE eqxx.
by apply/OrdNode_inj/IHf => t0 t0inf; apply: IHt; rewrite inE t0inf orbT.
Qed.
Lemma forest_to_bintreeK : cancel forest_to_bintree bin_to_forest.
Proof. by move=> f; apply OrdNode_inj; exact: ord_to_bintreeK. Qed.

HB.instance Definition _ :=
  Choice.copy ordtree (can_type ord_to_bintreeK).
HB.instance Definition _ :=
  Countable.copy ordtree (can_type ord_to_bintreeK).


Fixpoint size_ordtree t :=
  let: OrdNode f := t in (sumn [seq size_ordtree t | t <- f]).+1.
Lemma size_ordtreeE f :
  size_ordtree (OrdNode f) = (sumn [seq size_ordtree t | t <- f]).+1.
Proof. by []. Qed.
Lemma size_ordtree_pos t : size_ordtree t > 0.
Proof. by case: t. Qed.
Lemma size_tree_eq1 t : (size_ordtree t == 1) = (t == OrdNode [::]).
Proof.
case: t => [[| t f]] //=; rewrite eqSS.
by case: (size_ordtree t) (size_ordtree_pos t).
Qed.
Lemma size_bin_to_ordtree bt :
  size_ordtree (bin_to_ordtree bt) = (size_tree bt).+1.
Proof.
elim: bt => [//| l Hl r Hr /=].
by rewrite add1n -!addnS -!size_ordtreeE {}Hl {}Hr.
Qed.
Lemma size_ord_to_bintree t :
  size_ordtree t = (size_tree (ord_to_bintree t)).+1.
Proof. by rewrite -size_bin_to_ordtree ord_to_bintreeK. Qed.


Section OfSize.

Variable (n : nat).

Structure ordtreesz : predArgType :=
  OrdTreeSZ {trval :> ordtree; _ : size_ordtree trval == n}.
HB.instance Definition _ := [isSub of ordtreesz for trval].
HB.instance Definition _ := [Countable of ordtreesz by <:].

Lemma ordtreeszP (t : ordtreesz) : size_ordtree t = n.
Proof. by case: t => t /= /eqP. Qed.

End OfSize.

Section FinType.

Implicit Type (t : ordtree).

Definition enum_ordtreesz n :=
  if n is n'.+1 then [seq bin_to_ordtree b | b <- enum_bintreesz n']
  else [::].

Lemma size_mem_enum_ordtreeszP n t :
  t \in enum_ordtreesz n -> size_ordtree t = n.
Proof.
case: n => [//| n].
rewrite -(ord_to_bintreeK t) size_bin_to_ordtree.
by rewrite (mem_map (can_inj bin_to_ordtreeK)) => /size_mem_enum_bintreeszP ->.
Qed.

Lemma enum_ordtreeszP n :
  all (fun t => size_ordtree t == n) (enum_ordtreesz n).
Proof. by apply/allP => /= t /size_mem_enum_ordtreeszP ->. Qed.

Lemma enum_ordtreesz_uniq n : uniq (enum_ordtreesz n).
Proof.
case: n => [// |n].
rewrite /enum_ordtreesz (map_inj_uniq (can_inj bin_to_ordtreeK)).
exact: enum_bintreesz_uniq.
Qed.

Lemma mem_enum_ordtreesz n t :
  size_ordtree t == n -> t \in enum_ordtreesz n.
Proof.
case: n => [/eqP sz0|n].
  by have := size_ordtree_pos t; rewrite sz0.
rewrite size_ord_to_bintree eqSS => /mem_enum_bintreesz.
by move=> /(map_f bin_to_ordtree); rewrite ord_to_bintreeK.
Qed.

Lemma enum_ordtreesz_countE n t :
  size_ordtree t == n -> count_mem t (enum_ordtreesz n) = 1.
Proof.
move/mem_enum_ordtreesz => H.
by rewrite (count_uniq_mem _ (enum_ordtreesz_uniq n)) H.
Qed.
HB.instance Definition _ n :=
  Finite.copy (ordtreesz n)
    (seq_finType (ordtreesz n : subCountType _)
       (enum_ordtreeszP n) (@enum_ordtreesz_countE n)).

Theorem card_ordtreesz n : #|ordtreesz n.+1| = Catalan_bin n.
Proof.
rewrite /= !cardT -!(size_map val) !enumT unlock /=.
rewrite subType_seqP ?enum_ordtreeszP //= size_map.
by rewrite size_enum_bintreeszE.
Qed.

End FinType.

Fixpoint depth_ordtree t :=
  let: OrdNode f := t in (foldr maxn 0 [seq depth_ordtree t | t <- f]).+1.
Lemma depth_ordtreeE f :
  depth_ordtree (OrdNode f) = (foldr maxn 0 [seq depth_ordtree t | t <- f]).+1.
Proof. by []. Qed.
Lemma depth_ordtree_pos t : depth_ordtree t > 0.
Proof. by case: t. Qed.
Lemma depth_tree_eq1 t : (depth_ordtree t == 1) = (t == OrdNode [::]).
Proof.
case: t => [[| t f]] //=; rewrite eqSS.
case: (depth_ordtree t) (depth_ordtree_pos t) => // n _.
by case: foldr => // m; rewrite maxnSS.
Qed.
Lemma depth_tree_eq2P t :
  reflect (exists n, t = OrdNode (nseq n.+1 (OrdNode [::])))
    (depth_ordtree t == 2).
Proof.
apply (iffP idP) => [| [n {t}-> /=]]; first last.
  by rewrite eqSS; elim: n => [//| n /= /eqP ->].
case: t => f; rewrite [X in X -> _]/= eqSS => /eqP eqmax.
have /allP alld1 : all (fun t => depth_ordtree t == 1) f.
  move/eqP : eqmax; rewrite eqn_leq => /andP[+ _].
  elim: f => [//| t f IHf] /=.
  rewrite geq_max leq_eqVlt andbC => /andP[{}/IHf -> /orP[-> //|]].
  by move/(leq_ltn_trans (depth_ordtree_pos t)).
suff [n eqf] : exists n : nat, f = (nseq n.+1 (OrdNode [::])).
  by exists n; rewrite eqf.
exists (size f).-1.
have {eqmax} -> : (size f).-1.+1 = (size f) by case: f eqmax {alld1}.
by apply/all_pred1P/allP => /= t {}/alld1; rewrite depth_tree_eq1.
Qed.


Fixpoint line_ordtree n :=
  if n is n0.+1 then OrdNode [:: line_ordtree n0] else OrdNode [::].

Lemma size_line_ordtree n : size_ordtree (line_ordtree n) = n.+1.
Proof. by elim: n => // n /= ->; rewrite addn0. Qed.
Lemma depth_line_ordtree n : depth_ordtree (line_ordtree n) = n.+1.
Proof. by elim: n => // n /= ->; rewrite maxn0. Qed.
Lemma depth_le_size t :
  depth_ordtree t <= size_ordtree t
                  ?= iff (t == line_ordtree (size_ordtree t).-1).
Proof.
have dlesz t1 : depth_ordtree t1 <= size_ordtree t1.
  elim/indtree: t1  {t} => /=; elim=> [// |t f IHf Ht] /=.
  have /Ht ledt : t \in t :: f by rewrite inE eqxx.
  have {Ht} /IHf : forall t, t \in f -> depth_ordtree t <= size_ordtree t.
    by move=> t0 t0in; apply: Ht; rewrite inE t0in orbT.
  rewrite !ltnS -(leq_add2l (size_ordtree t)) => /(leq_trans _); apply.
  by rewrite geq_max leq_addl andbT (leq_trans ledt) // leq_addr.
split; first exact: dlesz.
apply/eqP/eqP => [|->]; last by rewrite size_line_ordtree depth_line_ordtree.
elim/indtree: t => /= [[// | t f]] IHf [] Heq.
have /= := dlesz (OrdNode f); rewrite ltnS.
rewrite -(leq_add2l (size_ordtree t)) -Heq.
rewrite leq_max => /orP[]; first last.
  by rewrite -{2}(add0n (foldr _ _ _)) leq_add2r leqNgt size_ordtree_pos.
move/leq_trans => /(_ _ (dlesz t)).
rewrite -{2}(addn0 (size_ordtree t)) leq_add2l leqn0 => H0.
move: Heq; have {H0} -> : f = [::].
  case: f H0 {IHf} => //= t1 f.
  by rewrite -leqn0 geq_max leqNgt depth_ordtree_pos.
rewrite /= maxn0 addn0 => /[dup] + ->.
have {}/IHf/[apply] : t \in t :: f by rewrite inE eqxx.
by case: size_ordtree (size_ordtree_pos t) => //= n _ ->.
Qed.
