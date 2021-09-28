(** * Combi.SymGroup.towerSn : The Tower of the Symmetric Groups *)
(******************************************************************************)
(*      Copyright (C) 2016-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * The Tower of the Symmetric Groups

External product of class functions:

We fix two groups [G] and [H]. Then we define:

- [f \ox g] = [cfextprod g h]  == the external product of class function,
                defined by [f \ox g (u, v) := f u * f v] for [(u, v) in G * H].
                It is of of type ['CF(setX G H)] when [g : 'CF(G)] and
                [h : 'CF(H)].
- [cfextprodr g h] == [cfextprod h g]
- [extprod_repr rG rH] == the external product (tensor product) of matrix
                representation. Its character is the external product of the
                character of [rG] and [rH].


The tower of the symmetric groups

- [tinj]     == the tower injection morphism : ['S_m * 'S_n -> 'S_(m + n)]
- [f \o^ g]  == the image along [tinj] of the external product of [f] and [g].

Induction and restriction of class functions

- ['z_p] == [zcoeff p] == The cardinality of the centralizer of any
                permutation of cycle type [p] in [algC], that is
                [#|'S_k| / #|class p|].
- ['1z_p] = [ncfuniCT p] == the normalized cycle indicator class function
                for cycle type [p] == ['z_p *: '1_[p]].

The two main results are:

- Theorem [cfuni_Res] which expands the restriction to ['S_m * 'S_n]
  of the cycle indicator class function ['1_[l]]:
[[
    'Res[tinj @* ('dom tinj)] '1_[l] =
      \sum_(pp | l == pp.1 +|+ pp.2) '1_[pp.1] \o^ '1_[pp.2].
]]
  by Frobenius duality it implies:

- Theorem [ncfuniCT_Ind] which expands the induction of two normalized
  cycle indicator class functions:
[[
    'Ind['SG_(m + n)] ('1z_[p] \o^ '1z_[q]) = '1z_[p +|+ q].
]]
***************)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import finfun fintype tuple finset bigop.
From mathcomp Require Import ssralg fingroup morphism perm gproduct.
From mathcomp Require Import ssralg ssrnum matrix vector mxalgebra algC.
From mathcomp Require Import classfun character mxrepresentation.

Require Import tools ordcast partition sorted.
Require Import permcomp cycles cycletype permcent.

Notation "''SG_' n" := [set: 'S_n]
  (at level 8, n at level 2, format "''SG_' n").

Import LeqGeqOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope Combi_scope.

Local Notation algCF := [fieldType of algC].


Section classGroup.

Variables gT aT: finGroupType.
Variable G H : {group gT}.

Lemma class_disj x y :
  y \notin x ^: G -> x ^: G :&: y ^: G = set0.
Proof using.
move/class_eqP=> xy.
apply /setP=> a; rewrite !inE.
apply /andP => [][/class_eqP ax /class_eqP ay].
by apply xy; rewrite -ax -ay.
Qed.

Lemma prod_conjg (x y : gT * aT) : x ^ y = (x.1 ^ y.1, x.2 ^ y.2).
Proof using. by []. Qed.

End classGroup.


(** * External product of class functions *)
Section CFExtProdDefs.

Variables (gT aT : finGroupType).
Variables (G : {group gT}) (H : {group aT}).

Local Open Scope ring_scope.

(** One could use the following alternative definition
[[
Definition cast_cf (G H : {set gT}) (eq_GH : G = H) (f : 'CF(G)) :=
  let: erefl in _ = H := eq_GH return 'CF(H) in f.
Definition cfextprod (g : 'CF(G)) (h : 'CF(H)) : 'CF(setX G H) :=
  (cfMorph (cast_cf (esym (@morphim_fstX _ _ G H)) g)) *
  (cfMorph (cast_cf (esym (@morphim_sndX _ _ G H)) h)).
]]
and prove the equivalence:
[[
Lemma cfextprodE g h x y : (g \ox h) (x, y) = (g x) * (h y).
]]
However, the more direct definition below leads to simpler proofs, at least
once we have proved that it is indeed a class function.
 *********)
Lemma cfextprod_subproof (g : 'CF(G)) (h : 'CF(H)) :
  is_class_fun <<setX G H>> [ffun x => g x.1 * h x.2].
Proof using.
rewrite genGid; apply intro_class_fun => [x y|].
- rewrite !inE => /andP [x1 x2] /andP [y1 y2].
  by rewrite !cfunJgen ?genGid.
- move=> x; rewrite inE => /nandP [x1|x2].
  + by rewrite cfun0gen ?mul0r ?genGid.
  + by rewrite [h _]cfun0gen ?mulr0 ?genGid.
Qed.
Definition cfextprod g h := Cfun 0 (cfextprod_subproof g h).
Definition cfextprodr_head k g h := let: tt := k in cfextprod h g.

End CFExtProdDefs.

Notation "f \ox g" := (cfextprod f g) (at level 40, left associativity).
Notation cfextprodr := (cfextprodr_head tt).

Section CFExtProdTheory.

Variables (gT aT : finGroupType).
Variables (G : {group gT}) (H : {group aT}).
Implicit Type (g : 'CF(G)) (h : 'CF(H)).

Local Open Scope ring_scope.

Lemma cfextprodrE h g : cfextprodr h g = g \ox h.
Proof using. by []. Qed.

Lemma cfextprod_is_linear g : linear (cfextprod g : 'CF(H) -> 'CF(setX G H)).
Proof using.
move=> /= a h1 h2.
apply/cfunP=> /= x.
by rewrite !cfunE !mulrDr mulrA [g _ * _]mulrC mulrA.
Qed.
Canonical cfextprod_additive g := Additive (cfextprod_is_linear g).
Canonical cfextprod_linear g := Linear (cfextprod_is_linear g).

Lemma cfextprod0r g : g \ox (0 : 'CF(H)) = 0.
Proof using. by rewrite linear0. Qed.
Lemma cfextprodNr g h : g \ox - h = - (g \ox h).
Proof using. by rewrite linearN. Qed.
Lemma cfextprodDr g h1 h2 : g \ox (h1 + h2) = g \ox h1 + g \ox h2.
Proof using. by rewrite linearD. Qed.
Lemma cfextprodBr g h1 h2 : g \ox (h1 - h2) = g \ox h1 - g \ox h2.
Proof using. by rewrite linearB. Qed.
Lemma cfextprodMnr h g n : g \ox (h *+ n) = (g \ox h) *+ n.
Proof using. by rewrite linearMn. Qed.
Lemma cfextprod_sumr g I r (P : pred I) (phi : I -> 'CF(H)) :
  g \ox (\sum_(i <- r | P i) phi i) = \sum_(i <- r | P i) g \ox phi i.
Proof using. by rewrite linear_sum. Qed.
Lemma cfextprodZr g a h : g \ox (a *: h) = a *: (g \ox h).
Proof using. by rewrite linearZ. Qed.

Lemma cfextprodr_is_linear h : linear (cfextprodr h : 'CF(G) -> 'CF(setX G H)).
Proof using.
move=> /= a g1 g2; rewrite !cfextprodrE.
apply/cfunP=> /= x.
by rewrite !cfunE !mulrDl -mulrA.
Qed.
Canonical cfextprodr_additive h := Additive (cfextprodr_is_linear h).
Canonical cfextprodr_linear h := Linear (cfextprodr_is_linear h).

Lemma cfextprod0l h : (0 : 'CF(G)) \ox h = 0.
Proof using. by rewrite -cfextprodrE linear0. Qed.
Lemma cfextprodNl h g : - g \ox h = - g \ox h.
Proof using. by rewrite -!cfextprodrE linearN. Qed.
Lemma cfextprodDl h g1 g2 : (g1 + g2) \ox h = g1 \ox h + g2 \ox h.
Proof using. by rewrite -!cfextprodrE linearD. Qed.
Lemma cfextprodBl h g1 g2 : (g1 - g2) \ox h = g1 \ox h - g2 \ox h.
Proof using. by rewrite -!cfextprodrE linearB. Qed.
Lemma cfextprodMnl h g n : g *+ n \ox h = g \ox h *+ n.
Proof using. by rewrite -!cfextprodrE linearMn. Qed.
Lemma cfextprod_suml h I r (P : pred I) (phi : I -> 'CF(G)) :
  (\sum_(i <- r | P i) phi i) \ox h = \sum_(i <- r | P i) phi i \ox h.
Proof using. by rewrite -!cfextprodrE linear_sum. Qed.
Lemma cfextprodZl h a g : (a *: g) \ox h = a *: (g \ox h).
Proof using. by rewrite -!cfextprodrE linearZ. Qed.

Section ReprExtProd.

Variables (n1 n2 : nat).
Variables (rG : mx_representation algCF G n1)
          (rH : mx_representation algCF H n2).

Lemma extprod_mx_repr : mx_repr (setX G H) (fun x => tprod (rG x.1) (rH x.2)).
Proof using.
split=>[|i j]; first by rewrite !repr_mx1 tprod1.
rewrite !inE => /andP [i1 i2] /andP [j1 j2].
by rewrite !repr_mxM // tprodE.
Qed.
Definition extprod_repr := MxRepresentation extprod_mx_repr.

Lemma cfRepr_extprod : cfRepr extprod_repr = cfRepr rG \ox cfRepr rH.
Proof using.
apply/cfun_inP=> x GXHx.
by have:= GXHx; rewrite !inE !cfunE GXHx mxtrace_prod => /andP [-> ->] /=.
Qed.

End ReprExtProd.

Lemma cfextprod_char g h :
  g \is a character -> h \is a character -> g \ox h \is a character.
Proof.
move=> /char_reprP [rG ->{g}] /char_reprP [rH ->{h}].
apply/char_reprP; exists (Representation (extprod_repr rG rH)).
by rewrite /= cfRepr_extprod.
Qed.

End CFExtProdTheory.


(** * Injection morphism of the tower of the symmetric groups *)
Section TowerMorphism.

Variables m n : nat.

Local Notation ct := cycle_typeSn.
Local Notation SnXm := (setX 'SG_m 'SG_n).

Definition tinjval (s : 'S_m * 'S_n) :=
  fun (x : 'I_(m + n)) => match split x  with
  | inl a => unsplit (inl (s.1 a))
  | inr a => unsplit (inr (s.2 a))
  end.

Fact tinjval_inj s : injective (tinjval s).
Proof using.
rewrite /tinjval => x y.
case: (split_ordP x) => xs ->{x} /=;
  case: (split_ordP y) => ys ->{y} /=.
- by move=> /lshift_inj/perm_inj ->.
- by move/eqP; rewrite eq_lrshift.
- by move/eqP; rewrite eq_rlshift.
- by move=> /rshift_inj/perm_inj ->.
Qed.
Definition tinj s : 'S_(m + n) := perm (@tinjval_inj s).

Fact tinj_morphM : {morph tinj : x y / x * y >-> x * y}.
Proof using.
rewrite /tinj => /= s1 s2; apply /permP => /= x.
rewrite permM -(splitK x) !permE.
by case: splitP => [] j _; rewrite /tinjval !unsplitK /= permM.
Qed.
Canonical morph_of_tinj := Morphism (D := SnXm) (in2W tinj_morphM).

Lemma isom_tinj : isom SnXm (tinj @* ('dom tinj)) tinj.
Proof using.
apply/isomP; split; last by [].
apply/subsetP => [] /= [s1 s2]; rewrite inE => /andP [_].
rewrite !inE /= => /eqP/permP H.
rewrite -[1]/(1,1) /xpair_eqE /=.
apply/andP; split; apply/eqP/permP => x; rewrite !perm1.
- have:= H (unsplit (inl x)).
  by rewrite permE /tinjval unsplitK perm1 /=; apply: lshift_inj.
- have:= H (unsplit (inr x)).
  by rewrite permE /tinjval unsplitK perm1 /=; apply: rshift_inj.
Qed.

Lemma expg_tinj_lshift s a i :
 (tinj s ^+ i) (lshift n a) = lshift n ((s.1 ^+ i) a).
Proof using.
elim: i => [|i IHi]; first by rewrite !expg0 !perm1.
rewrite !expgSr !permM IHi permE /tinjval /=.
pose y := inl ((s.1 ^+ i) a).
by rewrite (_: lshift _ _ = unsplit (y _)) // unsplitK.
Qed.

Lemma expg_tinj_rshift s a i :
  (tinj s ^+ i) (rshift m a) = rshift m ((s.2 ^+ i) a).
Proof using.
elim: i => [|i IHi]; first by rewrite !expg0 !perm1.
rewrite !expgSr !permM IHi permE /tinjval /=.
pose y := inr ((s.2 ^+ i) a).
by rewrite (_: rshift _ _ = unsplit (y _)) // unsplitK.
Qed.

Lemma porbit_tinj_lshift s a :
  porbit (tinj s) (lshift n a) = [set @lshift m n x | x in porbit s.1 a].
Proof using.
apply/setP => /= Y.
apply/porbitP/imsetP => /= [[i ->]|[y]].
- exists ((s.1 ^+ i) a); first by apply /porbitP; exists i.
  exact: expg_tinj_lshift.
- move /porbitP => [i ->] ->.
  by exists i; rewrite expg_tinj_lshift.
Qed.

Lemma porbit_tinj_rshift s a :
  porbit (tinj s) (rshift m a) = [set @rshift m n x | x in porbit s.2 a].
Proof using.
apply/setP => /= Y.
apply/porbitP/imsetP => /= [[i ->]|[y]].
- exists ((s.2 ^+ i) a); first by apply /porbitP; exists i.
  exact: expg_tinj_rshift.
- move /porbitP => [i ->] ->.
  by exists i; rewrite expg_tinj_rshift.
Qed.

Lemma porbits_tinj s :
  porbits (tinj s) =
  [set (@lshift m n) @: x | x : {set 'I_m} in porbits s.1]
    :|:
    [set (@rshift m n) @: x | x : {set 'I_n} in porbits s.2].
Proof using.
apply/setP => S; rewrite /porbits inE.
apply/imsetP/orP => [[x _ ->{S}] | [] /imsetP[T /imsetP[x _] ->{T}] ->{S}].
- rewrite -(splitK x); case: splitP => j _ {x}.
  + left; apply/imsetP; exists (porbit s.1 j) => /=; first exact: imset_f.
    exact: porbit_tinj_lshift.
  + right; apply/imsetP; exists (porbit s.2 j) => /=; first exact: imset_f.
    exact: porbit_tinj_rshift.
  - by exists (lshift n x); last by rewrite porbit_tinj_lshift.
  - by exists (rshift m x); last by rewrite porbit_tinj_rshift.
Qed.

Lemma cycle_type_tinj s : ct (tinj s) = ct s.1 +|+ ct s.2.
Proof using.
apply val_inj; rewrite union_intpartnE cast_intpartnE /=.
rewrite porbits_tinj setpart_shape_union; first last.
  rewrite -setI_eq0; apply/eqP/setP => S.
  rewrite !inE; apply/negP => /andP [].
  move=> /imsetP [X /imsetP [x _ ->]] -> {X}.
  move=> /imsetP [X /imsetP [y _ ->]].
  move/setP => /(_ (lshift n x)).
  rewrite imset_f; last exact: porbit_id.
  move=> /esym/imsetP => [] [z _] /eqP.
  by rewrite eq_lrshift.
by congr sort; rewrite /ct !cast_intpartnE /=; congr (_ ++ _);
  apply setpart_shape_imset; [exact: lshift_inj | exact: rshift_inj].
Qed.

End TowerMorphism.

Arguments tinj {m n} s.


(** ** The tower is associative (upto isomorphism) with unit *)
Section Assoc.

Variables m n p : nat.

Lemma cast_rshift j : cast_ord (esym (add0n n)) j = rshift 0 j.
Proof. by apply val_inj; rewrite /= add0n. Qed.

Lemma cast_lshift j : cast_ord (esym (addn0 n)) j = lshift 0 j.
Proof. by apply val_inj. Qed.

Lemma tinj1E (t : 'S_n) : tinj (1%g, t) = cast_perm (esym (add0n n)) t.
Proof.
apply/permP => /= itmp.
rewrite -(splitK itmp) !permE.
case: splitP => i _ {itmp}; first by case: i.
by rewrite /tinjval !unsplitK /= -!cast_rshift cast_ord_permE.
Qed.

Lemma tinjE1 (t : 'S_n) : tinj (t, 1%g) = cast_perm (esym (addn0 n)) t.
Proof.
apply/permP => /= itmp.
rewrite -(splitK itmp) !permE.
case: splitP => i _ {itmp}; last by case: i.
by rewrite /tinjval !unsplitK /= -!cast_lshift cast_ord_permE.
Qed.

Lemma tinjA (s : 'S_m) (t : 'S_n) (u : 'S_p) :
  tinj (tinj(s, t), u) = cast_perm (addnA m n p) (tinj (s, tinj (t, u))).
Proof using.
apply/permP => /= itmp.
rewrite -(splitK itmp) !permE.
case: splitP => i _ {itmp}; rewrite /tinjval !unsplitK /= cast_permE.
- rewrite -(splitK i) !permE.
  case: splitP => j _ {i}; rewrite /tinjval !unsplitK /=.
  + rewrite [cast_ord (esym _) _](_ : _ = unsplit (inl j));
      last exact: val_inj.
    by rewrite !unsplitK /=; apply val_inj.
  + rewrite [cast_ord (esym _) _](_ : _ = unsplit (inr (lshift _ j)));
      last exact: val_inj.
    rewrite !unsplitK /=; apply val_inj => /=.
    rewrite (_: lshift _ _ = unsplit (inl j)) //.
    by rewrite !permE /tinjval !unsplitK /=.
- rewrite [cast_ord (esym _) _](_ : _ = unsplit (inr (rshift _ i)));
    last by apply: val_inj => /=; rewrite addnA.
  rewrite !permE /tinjval !unsplitK /=.
  rewrite (_: rshift n _ = unsplit (inr i)) //.
  rewrite !permE /tinjval !unsplitK /=.
  by apply val_inj; rewrite /= addnA.
Qed.

Lemma cycle_type_tinjC (s : 'S_m) (t : 'S_n) :
  cycle_typeSn (tinj (s, t)) =
  cycle_typeSn (cast_perm (esym (addnC m n)) (tinj (t, s))).
Proof.
rewrite !cast_cycle_typeSN !cycle_type_tinj /=.
apply val_inj; rewrite [RHS]cast_intpartnE !union_intpartnE /=.
apply/perm_sortP => //.
by rewrite perm_catC.
Qed.

End Assoc.


Notation "f \o^ g" := (cfIsom (isom_tinj _ _) (f \ox g)) (at level 40).

Local Open Scope ring_scope.

(** * Restriction formula *)
Section Restriction.

Variables m n : nat.
Local Notation ct := cycle_typeSn.

Lemma cfuni_tinj s (l : 'P_(m + n)) :
  '1_[l] (tinj s) = (l == ct s.1 +|+ ct s.2)%:R.
Proof using. by rewrite cfuniCTnE cycle_type_tinj eq_sym. Qed.

Theorem cfuni_Res (l : 'P_(m + n)) :
  'Res[tinj @* ('dom tinj)] '1_[l] =
  \sum_(pp | l == pp.1 +|+ pp.2) '1_[pp.1] \o^ '1_[pp.2].
Proof using.
apply/cfunP => /= s.
case: (boolP (s \in tinj @* ('dom tinj))) => Hs; first last.
  by rewrite !cfun0gen // genGid.
rewrite (cfResE _ _ Hs); last exact: subsetT.
move: Hs => /imsetP/= [[s1 s2]].
rewrite inE => /andP [H1 _] -> {s}.
rewrite cfuni_tinj /= -linear_sum (cfIsomE _ _ H1).
rewrite /cfextprod /= sum_cfunE.
symmetry; transitivity
  (\sum_(pp | l == pp.1 +|+ pp.2) '1_[pp.1] s1 * '1_[pp.2] s2).
  by apply eq_bigr => i _; rewrite cfunE.
case: (altP (l =P _ )) => [->| Hl] /=.
- rewrite (bigD1 (ct s1, ct s2)) //=.
  rewrite !cfuniCTnE !eqxx /= mulr1.
  rewrite big1 ?addr0 // => [[t1 t2]] /andP [_].
  rewrite !cfuniCTnE eq_sym xpair_eqE.
  by move=> /nandP [] /negbTE -> /=; rewrite ?mulr0 ?mul0r.
- rewrite big1 // => [[t1 t2]] /= /eqP Hll; subst l.
  have {Hl} : (t1, t2) != (ct s1, ct s2).
    by move: Hl; apply contra => /eqP [-> ->].
  rewrite !cfuniCTnE eq_sym xpair_eqE.
  by move=> /nandP [] /negbTE -> /=; rewrite ?mulr0 ?mul0r.
Qed.

End Restriction.


(** * Induction formula *)
Section Induction.

Variables m n : nat.

Implicit Types (p : 'P_m) (q : 'P_n).

Local Notation ct := cycle_typeSn.
Local Notation SnXm := (setX 'SG_m 'SG_n).
Local Notation classX p q := ((permCT p, permCT q) ^: SnXm).

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma classXE p q : classX p q = setX (classCT p) (classCT q).
Proof using.
apply /setP => /= x; rewrite inE.
apply /imsetP/andP => /= [[i _ ] | [/imsetP/=[i1 _ xi1] /imsetP/=[i2 _ xi2]]].
- rewrite prod_conjg /= => -> /=.
  by split; apply memJ_class; rewrite inE.
- exists (i1, i2); first by rewrite inE; apply /andP; split; rewrite inE.
  by rewrite prod_conjg -xi1{xi1} -xi2{xi2}; case: x => /=.
Qed.

Lemma cfextprod_cfuni p q : '1_[p] \ox '1_[q] = '1_(classX p q).
Proof using.
apply/cfunP => /= x.
rewrite cfunE !cfuniCTnE /= cfunElock genGid !inE /= -natrM mulnb.
congr ((nat_of_bool _)%:R); rewrite classXE.
apply /andP/subsetP => [[ct1 ct2] /= y /imsetP[/= x0 _ ] -> {y} | /(_ x)].
- rewrite inE; apply/andP.
  by split; rewrite classes_of_permP permCTP prod_conjg /=;
         rewrite cycle_type_conjg partnCTE CTpartnK eq_sym ?ct1 ?ct2.
- rewrite class_refl => /(_ isT).
  rewrite inE => /andP [/imsetP/=[y1 _ ->] /imsetP/=[y2 _ ->]].
  by rewrite /ct !cycle_type_conjg !permCTP !CTpartnK !eqxx.
Qed.


Lemma cfdot_classfun_part p1 p2 :
  '[ '1_[p1], '1_[p2] ] = #|'SG_m|%:R^-1 * #|classCT p1|%:R * (p1 == p2)%:R.
Proof.
rewrite /cfdot /= -mulrA; congr (_ * _).
case: (altP (p1 =P p2)) => [<-{p2} | /negbTE Hneq]; rewrite /= ?mulr1 ?mulr0.
- rewrite (bigID (fun x => x \in classCT p1)) /=.
  under eq_bigr => i /andP [_].
    rewrite -classCTP !cfuniCTE => -> /=.
    by rewrite mul1r conjC1 over.
  rewrite sumr_const /= big1 ?addr0; first last => [i /andP [_]|].
    rewrite -classCTP !cfuniCTE => /negbTE -> /=.
    by rewrite mul0r.
  congr _%:R; apply eq_card => /= x.
  by rewrite unfold_in inE.
- apply big1 => i _; rewrite !cfuniCTE.
  case: (altP (_ =P _)) => [-> | Hi]; rewrite /= ?mul0r // mul1r {i}.
  by rewrite partnCTE /= !CTpartnK Hneq /= conjC0.
Qed.

Lemma decomp_cf_triv : \sum_(p : 'P_n) '1_[p] = 1.
Proof using.
apply/cfunP => /= x.
rewrite cfun1Egen genGid inE /=.
rewrite sum_cfunE (bigD1 (ct x)) //=.
rewrite big1 ?addr0 ?cfuniCTnE ?eqxx //=.
by move=> p /negbTE pct; rewrite cfuniCTnE eq_sym pct.
Qed.

Lemma classXI p1 p2 q1 q2 :
  (p2, q2) != (p1, q1) -> (classX p1 q1) :&: (classX p2 q2) = set0.
Proof using.
move=> /eqP qp; apply class_disj.
apply/imsetP => []/= [x _].
rewrite prod_conjg /= => [] [] qp1 qp2.
by apply qp; congr (_, _);
  rewrite -[LHS]CTpartnK -[RHS]CTpartnK; congr partnCT;
  rewrite -[LHS]permCTP -[RHS]permCTP ?qp1 ?qp2 cycle_type_conjg.
Qed.


(** The normalized cycle type indicator basis *)
Definition zcoeff (k : nat) (p : 'P_k) : algC :=
  #|'SG_k|%:R / #|classCT p|%:R.

Notation "''z_' p" := (zcoeff p) (at level 2, format "''z_' p").

Lemma zcoeffE k (l : 'P_k) : zcoeff l = (zcard l)%:R.
Proof.
rewrite /zcoeff card_class_of_part cardsT card_Sn.
rewrite char0_natf_div; [| exact: Cchar | exact: dvdn_zcard_fact].
rewrite invf_div mulrC mulfVK //.
by rewrite pnatr_eq0 -lt0n; apply: fact_gt0.
Qed.

Lemma neq0zcoeff (k : nat) (p : 'P_k) : 'z_p != 0.
Proof using. by rewrite zcoeffE pnatr_eq0 neq0zcard. Qed.

Hint Resolve neq0zcoeff : core.

Definition ncfuniCT (k : nat) (p : 'P_k) := 'z_p *: '1_[p].

Notation "''1z_[' p ]" := (ncfuniCT p)  (format "''1z_[' p ]").

Lemma ncfuniCT_gen k (f : 'CF('SG_k)) :
  f = \sum_(p : 'P_k) f (permCT p) / 'z_p *: '1z_[p].
Proof using.
apply/cfunP => /= x.
rewrite (bigD1 (ct x)) //= cfunE sum_cfunE big1.
- rewrite addr0 !cfunE cfuniCTnE eqxx /= mulr1.
  rewrite -mulrA [_^-1 *_]mulrC mulrA mulfK //.
  have: (permCT (ct x)) \in x ^: 'SG_k.
    rewrite classes_of_permP permCTP.
    by rewrite (partnCTK (cycle_type x)).
  by move/imsetP => [y _ ->]; rewrite cfunJgen ?genGid ?inE.
- by move=> p /negbTE pct; rewrite !cfunE cfuniCTnE eq_sym pct /= !mulr0.
Qed.

Lemma cfdotr_ncfuniCT k (f : 'CF('SG_k)) (s : 'S_k) : (f s) = '[f, '1z_[ct s]].
Proof using.
rewrite {2}(ncfuniCT_gen f) cfdot_suml.
rewrite (bigD1 (ct s)) //= !cfdotZl cfdotZr.
rewrite mulrA (divfK _) //.
rewrite cfdot_cfuni; try (by apply: class_normal; rewrite inE).
rewrite setIid big1 ?addr0.
- have: (permCT (ct s)) \in s ^: 'SG_k.
    rewrite classes_of_permP permCTP.
    by rewrite (partnCTK (cycle_type s)).
  move/imsetP => [y _ ->]; rewrite cfunJgen ?genGid ?inE //.
  rewrite fmorph_div !conjC_nat !mulrA divfK ?pnatr_eq0 ?card_classCT_neq0 //.
  by rewrite mulfK // neq0CG.
- move=> p /negbTE pct.
  rewrite !cfdotZl cfdotZr.
  rewrite cfdot_cfuni; try (by apply: class_normal; rewrite inE).
  rewrite class_disj; first by rewrite cards0 mul0r !mulr0.
  apply/negP; rewrite classes_of_permP !permCTP.
  by rewrite partnCTE !CTpartnK pct.
Qed.

(** Application of Frobenius duality : [cfdot_Res_r] *)
Lemma cfdot_Ind_cfuniCT p q (l : 'P_(m + n)) :
  '[ 'Ind['SG_(m + n)] ('1_[p] \o^ '1_[q]), '1_[l] ] =
  (p +|+ q == l)%:R / 'z_p / 'z_q.
Proof using.
rewrite -cfdot_Res_r cfuni_Res -linear_sum cfIsom_iso cfdot_sumr.
transitivity
  (\sum_(i | l == i.1 +|+ i.2)
    #|(classX p q) :&: (classX i.1 i.2)|%:R / #|SnXm|%:R : algC).
  apply eq_bigr => i _; rewrite !cfextprod_cfuni.
  by rewrite cfdot_cfuni //=; apply: class_normal; rewrite !inE.
case: (boolP (p +|+ q == l)) => [|] /= unionp; [rewrite mul1r|rewrite !mul0r].
- rewrite (bigD1 (p, q)) /=; last by rewrite eq_sym.
  rewrite setIid big1.
    rewrite addr0 classXE !cardsX natrM /zcoeff.
    rewrite !invfM !invrK.
    rewrite [_ * #|classCT p|%:R]mulrC -!mulrA; congr (_ * _).
    by rewrite [RHS]mulrA [RHS]mulrC natrM invfM.
  by move=> i /andP [] _ ip; rewrite classXI ?cards0 ?mul0r.
- rewrite big1 //= => i /eqP unioni.
  have ip: i != (p, q).
    move: unionp; apply contraR; rewrite negbK {}unioni => /eqP.
    by case: i => [i1 i2] [-> ->].
  by rewrite classXI ?cards0 ?mul0r.
Qed.

Lemma cfdot_Ind_ncfuniCT p q (l : 'P_(m + n)) :
  '[ 'Ind['SG_(m + n)] ('1z_[p] \o^ '1z_[q]), '1z_[l] ] =
  (p +|+ q == l)%:R * 'z_l.
Proof using.
rewrite cfextprodZl cfextprodZr.
rewrite !linearZ /= !cfdotZl cfdotZr cfdot_Ind_cfuniCT.
case: eqP => _ /=; rewrite ?mul0r ?mulr0 // !mul1r.
rewrite 2!mulrA mulrC mulrA [X in (X * _)]mulrC -invfM divff ?mul1r.
  by rewrite fmorph_div !conjC_nat.
by apply mulf_neq0.
Qed.

Theorem ncfuniCT_Ind p q :
  'Ind['SG_(m + n)] ('1z_[p] \o^ '1z_[q]) = '1z_[p +|+ q].
Proof using.
apply/cfunP => /= x; rewrite cfunE.
rewrite cfdotr_ncfuniCT cfdot_Ind_ncfuniCT.
rewrite cfuniCTnE eq_sym mulrC.
by case: (boolP (_ == _)) => [/eqP ->|] //=; rewrite !mulr0.
Qed.

End Induction.

Notation "''z_' p" := (zcoeff p) (at level 2, format "''z_' p").
Notation "''1z_[' p ]" := (ncfuniCT p)  (format "''1z_[' p ]").

#[export] Hint Resolve neq0zcoeff : core.
