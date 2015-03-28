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
Require Import path finset finfun fingraph tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma eq_in_path (T : eqType) (e e' : T -> T -> bool) s0 (s : seq T) :
  {in (s0 :: s) &, e =2 e'} -> path e s0 s = path e' s0 s.
Proof.
  elim: s s0 => [//=| s1 s IHs] s0 H /=.
  have /IHs -> : {in (s1 :: s) &, e =2 e'}.
    move=> x y Hx Hy /=; apply H; by rewrite in_cons; apply/orP; right.
  by rewrite H // !in_cons eq_refl ?orbT.
Qed.

Lemma in_pair (T : finType) x y (E F : {set T}) :
  (x, y) \in [set (e, f) | e in E, f in F] = (x \in E) && (y \in F).
Proof.
  apply/(sameP idP); apply(iffP idP).
  - move=> /andP [] Hx Hy; apply /imset2P; by exists x y.
  - move=> /imset2P [] x1 y1 Hx1 Hy1 [] -> ->; by rewrite Hx1 Hy1.
Qed.

Section FiniteRelations.

Variable T : finType.
Variable E : {set T}.

Definition relset := {set (T * T)}.
Definition set_of_rel (R : rel T) : relset := [set p | R p.1 p.2].
Definition rel_of_set (R : relset) : rel T := fun x y => (x, y) \in R.

Lemma rel_of_setK (R : rel T) : rel_of_set (set_of_rel R) =2 R.
Proof. move=> x y; by rewrite /set_of_rel/rel_of_set /= inE /=. Qed.

Definition stable (R : rel T) := forall x y, R x y -> x \in E /\ y \in E.

Definition full : relset := [set p | (p.1 \in E) && (p.2 \in E)].
Definition stablerel (R : relset) := R \subset full.

Lemma stablerelP R : reflect (stable (rel_of_set R)) (stablerel R).
Proof.
  apply (iffP idP) => /=.
  - move=> /subsetP H x y; rewrite /rel_of_set => /H.
    by rewrite inE /= => /andP [].
  - move=> H; apply/subsetP => [[x y]] /H [].
    by rewrite inE /= => -> ->.
Qed.

Record finrelType := FinRel { RelSet : relset; _ : stablerel RelSet }.
Canonical finrel_subType := Eval hnf in [subType for RelSet].
Definition finrel_eqMixin := Eval hnf in [eqMixin of finrelType by <:].
Canonical finrel_eqType := Eval hnf in EqType finrelType finrel_eqMixin.
Definition finrel_choiceMixin := Eval hnf in [choiceMixin of finrelType by <:].
Canonical finrel_choiceType := Eval hnf in ChoiceType finrelType finrel_choiceMixin.
Definition finrel_countMixin := Eval hnf in [countMixin of finrelType by <:].
Canonical finrel_countType := Eval hnf in CountType finrelType finrel_countMixin.
Canonical finrel_subCountType := Eval hnf in [subCountType of finrelType].
Definition finrel_finMixin := Eval hnf in [finMixin of finrelType by <:].
Canonical finrel_finType := Eval hnf in  FinType finrelType finrel_finMixin.
Canonical finrel_subFinType := Eval hnf in [subFinType of finrelType].

Definition rel_of_finrel (R : finrelType) : rel T := fun x y => (x, y) \in RelSet R.
Coercion rel_of_finrel : finrelType >-> rel.

Implicit Type R S : finrelType.

Lemma finrel_setE R : R =2 rel_of_set (RelSet R).
Proof. by []. Qed.

Lemma finrel_relsetE R x y : R x y = ((x, y) \in (RelSet R)).
Proof. by []. Qed.

Lemma stableP R : stable R.
Proof. move=> x y; rewrite finrel_relsetE; case: R => r /= /stablerelP; by apply. Qed.

Lemma finrel_notinL R x y : x \notin E -> R x y = false.
Proof. by apply contraNF => /stableP []. Qed.
Lemma finrel_notinR R x y : y \notin E -> R x y = false.
Proof. by apply contraNF => /stableP []. Qed.

Lemma finrel_eqE R S : R = S <-> R =2 S.
Proof.
  split; first by move ->.
  move=> H; apply val_inj; rewrite -setP /= => [[x y]].
  by rewrite -!finrel_relsetE.
Qed.

Lemma finrel_eq_inE R S : R = S <-> {in E &, R =2 S}.
Proof.
  split; first by move ->.
  move=> H; apply val_inj; rewrite -setP /= => [[x y]].
  rewrite -!finrel_relsetE.
  case: (boolP (x \in E)) => HxE.
  - case: (boolP (y \in E)) => HyE; first by apply H.
    case: (boolP (R x y)) => [/stableP [] _ Habs| _]; first by rewrite Habs in HyE.
    case: (boolP (S x y)) => [/stableP [] _ Habs|  ]; first by rewrite Habs in HyE.
    by [].
  - case: (boolP (R x y)) => [/stableP [] Habs _| _]; first by rewrite Habs in HxE.
    case: (boolP (S x y)) => [/stableP [] Habs _|  ]; first by rewrite Habs in HxE.
    by [].
Qed.


Lemma stable_finrel (r : rel T) :
  stablerel [set p | [&& p.1 \in E, p.2 \in E & r p.1 p.2]].
Proof. by apply/stablerelP => x y; rewrite /rel_of_set inE /= => /and3P []. Qed.
Definition finrel (r : rel T) := FinRel (stable_finrel r).
Lemma finrel_inE (r : rel T) : {in E &, finrel (r : rel T) =2 r}.
Proof. by move=> x y Hx Hy /=; rewrite finrel_relsetE inE Hx Hy /=. Qed.
Lemma finrelE_tmp (r : rel T) x y :
  finrel (r : rel T) x y = [&& x \in E, y \in E & r x y].
Proof. by rewrite finrel_relsetE inE /=. Qed.

Section Stable.

Variable r : rel T.
Hypothesis Hstable : stable r.

Lemma finrel_of_stablerel : stablerel [set p | r p.1 p.2].
Proof. apply/stablerelP => x y; rewrite /rel_of_set inE /=; exact: Hstable. Qed.
Definition finrel_stable := FinRel finrel_of_stablerel.
Lemma finrel_stableE : finrel_stable =2 r.
Proof. move=> x y; by rewrite finrel_relsetE inE /=. Qed.

End Stable.

Let finrelE := (finrelE_tmp, finrel_stableE).

Lemma stablerel_diag : stablerel [set (x, x) | x in E].
Proof. apply/stablerelP => x y. by rewrite /rel_of_set => /imsetP [] z Hz [] -> ->. Qed.
Definition diagrel := FinRel stablerel_diag.
Lemma diagrelE x y : diagrel x y = (x \in E) && (x == y).
Proof.
  rewrite finrel_relsetE /=; apply/(sameP idP); apply(iffP idP).
  - move=> /andP [] Hx /eqP <-; apply/imsetP; by exists x.
  - move/imsetP => [] z Hz [] -> ->; by rewrite eq_refl Hz.
Qed.

Lemma stablerel_rev R : stablerel [set p | R p.2 p.1].
Proof. apply/stablerelP => x y; by rewrite /rel_of_set inE /= => /stableP []. Qed.
Definition revrel R := FinRel (stablerel_rev R).
Lemma revrelE R x y : revrel R x y = R y x.
Proof. by rewrite finrel_relsetE /= inE /=. Qed.
Lemma revrelK : involutive revrel.
Proof. move=> P; rewrite finrel_eqE => x y; by rewrite !revrelE. Qed.

Definition comprel R S := finrel (fun x z => [exists y : T, R x y && S y z]).
Lemma comprelP R S x y : reflect (exists z, R x z /\ S z y) (comprel R S x y).
Proof.
  rewrite finrelE; apply (iffP idP).
  - move=> /and3P [] _ _ /existsP [] z /andP H; by exists z.
  - move=> [] z [] HR HS; have:= stableP HR => [] [] -> _; have:= stableP HS => [] [] _ ->.
    rewrite /=; apply/existsP; exists z; by rewrite HR HS.
Qed.

Lemma comprelA Q R S : comprel (comprel Q R) S = comprel Q (comprel R S).
Proof.
  rewrite finrel_eqE => x y.
  apply/(sameP idP); apply(iffP idP) => [/comprelP [] a| /comprelP [] b] [].
  - move=> Qxa /comprelP [] b [] Rab Sby.
    apply/comprelP; exists b; split; last exact Sby.
    apply/comprelP; by exists a.
  - move=> /comprelP [] a [] Qxa Rab Sby.
    apply/comprelP; exists a; split; first exact Qxa.
    apply/comprelP; by exists b.
Qed.

Lemma stablerel_inter R S : stablerel (RelSet R :&: RelSet S).
Proof.
  apply/stablerelP => x y. rewrite /rel_of_set inE => /andP [].
  by rewrite -finrel_relsetE => /stableP.
Qed.
Definition inter R S := FinRel (stablerel_inter R S).
Lemma interE R S x y : inter R S x y = R x y && S x y.
Proof. by rewrite finrel_relsetE /= inE /=. Qed.

Lemma interC R S : inter R S = inter S R.
Proof. rewrite finrel_eqE => x y; by rewrite !interE andbC. Qed.
Lemma interA Q R S : inter (inter Q R) S = inter Q (inter R S).
Proof. rewrite finrel_eqE => x y; by rewrite !interE andbA. Qed.

Definition ext R S := [forall x in E, forall y in E, R x y ==> S x y].
Definition totalrel R := [forall x in E, forall y in E, R x y || R y x ].
Definition reflexiverel R := [forall x in E, R x x].
Definition irreflexiverel R := [forall x in E, R x x == false].
Definition symmetricrel R := revrel R == R.
Definition antisymmetricrel R := ext (inter R (revrel R)) diagrel.
Definition transitiverel R := ext (comprel R R) R.

Definition orderrel R :=
  [&& reflexiverel R, antisymmetricrel R & transitiverel R].
Definition equivalencerel R :=
  [&& reflexiverel R, symmetricrel R & transitiverel R].


Lemma extP R S : reflect (forall x y, R x y -> S x y) (ext R S).
Proof.
  apply (iffP idP).
  - move=> /forallP Hall x y HR; have:= stableP HR => [] [] Hx Hy.
    exact: (implyP (implyP (forallP (implyP (Hall x) Hx) y) Hy)).
  - move=> H; apply/forallP => x; apply/implyP => Hx; apply/forallP => y; apply/implyP => Hy.
    apply/implyP; by apply H.
Qed.

Lemma totalrelP R : reflect {in E &, total R} (totalrel R).
Proof.
  apply (iffP idP) => /=.
  - move=> /forallP Hall x y Hx Hy.
    exact: (implyP (forallP (implyP (Hall x) Hx) y) Hy).
  - move=> H; apply/forallP => x; apply/implyP => Hx; apply/forallP => y; apply/implyP => Hy.
    by apply H.
Qed.

Lemma reflexiverelP R : reflect {in E, reflexive R} (reflexiverel R).
Proof.
  apply (iffP idP).
  - move=> /forallP Hall x Hx; exact: (implyP (Hall x)). 
  - move=> H; apply/forallP => x; apply/implyP => Hx; by apply H.
Qed.

Lemma irreflexiverelP R :
  reflect {in E, irreflexive R} (irreflexiverel R).
Proof.
  apply (iffP idP).
  - move=> /forallP Hall x Hx; apply/eqP; exact: (implyP (Hall x)).
  - move=> H; apply/forallP => x; apply/implyP => Hx; apply/eqP.
    by apply H.
Qed.

Lemma symmetricrelP R : reflect (symmetric R) (symmetricrel R).
Proof.
  apply (iffP idP).
  - move=> /eqP; rewrite finrel_eqE => H x y; by rewrite -H revrelE.
  - move=> H; apply/eqP; rewrite finrel_eqE => x y; rewrite revrelE; by apply H.
Qed.

Lemma antisymmetricrelP R : reflect (antisymmetric R) (antisymmetricrel R).
Proof.
  apply (iffP idP).
  - move=> /extP H x y /andP [] Rxy Ryx.
    have {H} := H x y; rewrite diagrelE interE Rxy revrelE /= => H.
    by have:= H Ryx => [] /andP [] _ /eqP.
  - move=> H; apply/extP => x y.
    rewrite diagrelE interE revrelE /= => /andP [] Rxy Ryx.
    have:= stableP Rxy => [] [] -> _ /=; apply/eqP.
    apply H; by rewrite Rxy Ryx.
Qed.

Lemma transitiverelP R : reflect (transitive R) (transitiverel R).
Proof.
  apply (iffP idP).
  - move=> /extP H y x z Hxy Hyz; apply H; apply/comprelP; by exists y.
  - move=> H; apply/extP => x z /comprelP [] y []; by apply H.
Qed.

Lemma equivalence_relsetP R :
  reflect ({in E & &, equivalence_rel R}) (equivalencerel R).
Proof.
  apply (iffP idP) => /=.
  - move=> /and3P [] /reflexiverelP Hrefl /symmetricrelP Hsym
            /transitiverelP Htrans=> x y z Hx Hy Hz.
    + split; first exact: Hrefl.
      by move=> /(sym_left_transitive Hsym Htrans) ->.
  - move=> H; apply/and3P; split.
    + apply/reflexiverelP => x Hx; by have:= H x x x Hx Hx Hx => [] [].
    + apply/symmetricrelP => x y.
      case: (boolP (x \in E)) => Hx;
        last by rewrite (finrel_notinR _ _ Hx) (finrel_notinL _ _ Hx).
      case: (boolP (y \in E)) => Hy;
        last by rewrite (finrel_notinR _ _ Hy) (finrel_notinL _ _ Hy).
      apply/(sameP idP); apply(iffP idP).
      * by have {H} := H _ _ _ Hy Hx Hy => [] [] -> H/H <-.
      * by have {H} := H _ _ _ Hx Hy Hx => [] [] -> H/H <-.
  - apply/transitiverelP => y x z Rxy Ryz.
    have:= stableP Rxy => [] [] Hx Hy; have:= stableP Ryz => [] [] _ Hz.
    by have {H} := H _ _ _ Hx Hy Hz => [] [] _ ->.
Qed.


Lemma orderrelP R :
  reflect [/\ {in E, reflexive R}, antisymmetric R & transitive R] (orderrel R).
Proof.
  apply (iffP idP) => /=.
  - by move=> /and3P [] /reflexiverelP Hrefl /antisymmetricrelP Hanti
            /transitiverelP Htrans.
  - move=> [] /reflexiverelP Hrefl /antisymmetricrelP Hanti
              /transitiverelP Htrans.
    by apply/and3P.
Qed.

End FiniteRelations.

Definition finrelE := (finrelE_tmp, finrel_stableE).


Section PosetDefs.

Variable T : finType.
Variable E : {set T}.

Record poset := Poset { Rel :> finrelType E; _ : orderrel Rel }.
Canonical poset_subType := Eval hnf in [subType for Rel].
Definition poset_eqMixin := Eval hnf in [eqMixin of poset by <:].
Canonical poset_eqType := Eval hnf in EqType poset poset_eqMixin.
Definition poset_choiceMixin := Eval hnf in [choiceMixin of poset by <:].
Canonical poset_choiceType := Eval hnf in ChoiceType poset poset_choiceMixin.
Definition poset_countMixin := Eval hnf in [countMixin of poset by <:].
Canonical poset_countType := Eval hnf in CountType poset poset_countMixin.
Canonical poset_subCountType := Eval hnf in [subCountType of poset].
Definition poset_finMixin := Eval hnf in [finMixin of poset by <:].
Canonical poset_finType := Eval hnf in  FinType poset poset_finMixin.
Canonical poset_subFinType := Eval hnf in [subFinType of poset].

Definition set_of_poset (P : poset) : {set T} := E.
Coercion set_of_poset : poset >-> set_of.

Variable (P : poset).

Lemma posetE : P =i E.
Proof. by []. Qed.

Definition strict : rel T := [fun x y => (P x y) && (x != y)].

Lemma strictW x y : strict x y -> P x y.
Proof. by rewrite /strict /= => /andP []. Qed.

Lemma strict_neq x y : strict x y -> x != y.
Proof. by rewrite /strict /= => /andP []. Qed.

End PosetDefs.


Section PosetTheory.

Variable T : finType.
Variable E : {set T}.
Implicit Type P Q : poset E.

Lemma poset_eqE P Q : P = Q <-> P =2 Q.
Proof.
  split; first by move ->.
  move=> H; apply val_inj => /=; by rewrite finrel_eqE.
Qed.

Lemma poset_eq_inE P Q : P = Q <-> {in E &, P =2 Q}.
Proof.
  split; first by move ->.
  move=> H; apply val_inj; by rewrite finrel_eq_inE.
Qed.

Lemma posetnn P n : n \in P -> P n n.
Proof.
  case: P => rel Hrel; rewrite posetE /=.
  by move: Hrel => /and3P [] /reflexiverelP Hrefl _ _ /Hrefl.
Qed.

Lemma anti_poset P m n : P m n -> P n m -> m = n.
Proof.
  case: P => rel Hrel /=.
  move: Hrel => /and3P [] _ /antisymmetricrelP Hanti _ Hnm Hmn.
  apply (Hanti m n); by rewrite Hnm Hmn.
Qed.

Lemma poset_trans P : transitive P.
Proof.
  case: P => rel Hrel y x z /=.
  move: Hrel => /and3P [] _ _ /transitiverelP Htrans.
  by apply Htrans.
Qed.

Lemma poset_strict_trans P m n p :
  P m n -> strict P n p -> strict P m p.
Proof.
  rewrite /strict /= => Pmn /andP [] Pnp Hneq.
  apply/andP; split; first by apply: (poset_trans Pmn).
  move: Hneq; apply contra => /eqP Heq; rewrite Heq {Heq} in Pmn.
  apply/eqP; by apply: anti_poset.
Qed.

Lemma strict_poset_trans P m n p :
  strict P m n -> P n p -> strict P m p.
Proof.
  rewrite /strict /= => /andP [] Pmn Hneq Pnp.
  apply/andP; split; first by apply: (poset_trans Pmn).
  move: Hneq; apply contra => /eqP Heq; rewrite -Heq {Heq} in Pnp.
  apply/eqP; by apply: anti_poset.
Qed.

Lemma strict_trans P m n p :
  strict P m n -> strict P n p -> strict P m p.
Proof. move/strictW; by apply poset_strict_trans. Qed.

End PosetTheory.

Hint Resolve posetnn.


(******************************************************************************)
(*                                                                            *)
(*                           Examples of Posets                               *)
(*                                                                            *)
(******************************************************************************)
Section TrivOrder.

Variable T : finType.
Variable E : {set T}.

Lemma diagrel_order : orderrel (diagrel E).
Proof.
  apply/orderrelP.
  split => [ a | a b | b a c]; rewrite !diagrelE.
  - move=> ->; by rewrite eq_refl.
  - by move=> /andP [] /andP [] _ /eqP ->.
  - by move=> /andP [] _ /eqP ->.
Qed.
Definition triv_poset := Poset diagrel_order.

End TrivOrder.

Section Boolean.

Variable T : finType.

Lemma subset_order :
  orderrel (finrel [set: {set T}] (fun (A B : {set T}) => A \subset B)).
Proof.
  apply/orderrelP.
  split => [x Hx | x y | y x z] /=; rewrite !finrelE !in_setT //=.
  - by rewrite -eqEsubset => /eqP.
  - exact: subset_trans.
Qed.
Definition Bool := Poset subset_order.

End Boolean.

(******************************************************************************)
(*                                                                            *)
(*                       Constructions on Posets                              *)
(*                                                                            *)
(******************************************************************************)

Section Cast.

Variable T : finType.
Variable E F : {set T}.
Implicit Type P : poset E.

Lemma cast_poset_exist P : E = F -> { Q : poset F | Q =2 P }.
Proof. move => H; subst F; by exists P. Qed.

Definition cast_poset (H : E = F) P := let: exist L _ := cast_poset_exist P H in L.
Lemma cast_posetE (H : E = F) P : cast_poset H P =2 P.
Proof. rewrite/cast_poset; by case: cast_poset_exist. Qed.

End Cast.

Section Dual.

Variable T : finType.
Variable E : {set T}.
Implicit Type P : poset E.

Lemma revrel_order P : orderrel (revrel P).
Proof.
  apply/orderrelP.
  split => [x Hx | x y | y x z] /=; rewrite !revrelE.
  - exact: posetnn.
  - rewrite andbC => /andP []; exact: anti_poset.
  - move=> Pxy Pzx; apply (poset_trans Pzx Pxy).
Qed.

Definition dual_poset P := Poset (revrel_order P).

Lemma dual_posetE P x y : dual_poset P y x = P x y.
Proof. by rewrite revrelE. Qed.

Lemma dualK : involutive dual_poset.
Proof. move=> P; apply val_inj => /=; by apply revrelK. Qed.

End Dual.


Section Induced.

Variable T : finType.
Variable E F : {set T}.
Hypothesis Hsub : E \subset F.
Implicit Type P : poset F.
Implicit Type Q : poset E.

Lemma induced_order P : orderrel (finrel E P).
Proof.
  move: Hsub => /subsetP Hin.
  apply/orderrelP; split => [x Hx | x y | y x z] /=; rewrite !finrelE.
  - rewrite Hx /=; apply posetnn; by apply (Hin _ Hx).
  - move=> /andP [] /and3P [] _ _ Pxy /and3P [] _ _ Pyx.
    by apply: anti_poset.
  - move=> /and3P [] -> _ Pxy /and3P [] _ -> Pyz /=.
    by apply (poset_trans Pxy Pyz).
Qed.
Definition induced P := Poset (induced_order P).

Lemma inducedE P : {in E &, (induced P) =2 P}.
Proof. move=> x y Hx Hy /=; by rewrite finrelE Hx Hy /=. Qed.

Lemma inducedP P (S : poset E) : {in E &, S =2 P} <-> S = (induced P).
Proof.
  split; last by move->; exact: inducedE.
  move=> H; rewrite poset_eq_inE => x y Hx Hy.
  rewrite inducedE //; by apply H.
Qed.

Definition expandedrel Q := finrel F (fun x y => (x == y) || Q x y).
Lemma expanded_order Q : orderrel (expandedrel Q).
Proof.
  apply/orderrelP.
  split => [x Hx | x y | y x z] /=; rewrite !finrelE.
  - by rewrite Hx eq_refl.
  - move=> /and4P [] /and3P [] _ _ /orP [/eqP -> //| Qxy] _ _ /orP [/eqP -> //| Qyx].
    exact: (anti_poset Qxy Qyx).
  - move=> /and3P [] Hx _  /orP [/eqP -> //| Qxy]; rewrite Hx.
    move=> /and3P [] _  -> /orP [/eqP <-| Qyz] /=; first by rewrite Qxy !orbT.
    by rewrite (poset_trans Qxy Qyz) orbT.
Qed.
Definition expanded Q := Poset (expanded_order Q).
Lemma expanded_inE Q : {in E &, Q =2 expanded Q}.
Proof.
  move: Hsub => /subsetP HEF.
  move=> x y Hx Hy /=; rewrite finrelE (HEF _ Hx) (HEF _ Hy) /=.
  case: (altP (x =P y)) => //= <-; by rewrite posetnn.
Qed.

Lemma induced_expanded Q : Q = induced (expanded Q).
Proof. apply inducedP => x y Hx Hy; by rewrite expanded_inE. Qed.

End Induced.

Section InducedTrans.

Variable T : finType.
Variable E F G : {set T}.
Hypothesis HsubFE : F \subset E.
Hypothesis HsubGF : G \subset F.

Lemma induced_comp :
  induced HsubGF \o induced HsubFE =1 induced (subset_trans HsubGF HsubFE).
Proof.
  move=> R; apply inducedP => x y Hx Hy.
  rewrite inducedE // inducedE //; by apply (subsetP HsubGF).
Qed.

End InducedTrans.


Section Sum.

Variable T : finType.
Variable E F : {set T}.
Hypothesis Hsub : [disjoint E & F].
Variable P : poset E.
Variable Q : poset F.

Lemma ExF x : x \in E -> x \in F = false.
Proof.
  move=> HxE; apply (introF idP) => HxF.
  move: Hsub => /disjoint_setI0; rewrite -setP => Habs.
  have:= Habs x; by rewrite !inE HxE HxF.
Qed.
Lemma FxE x : x \in F -> x \in E = false.
Proof. move=> HxF; apply (introF idP) => HxE; by rewrite ExF in HxF. Qed.

Lemma PxE x y : P x y -> x \in E. Proof. by move=> /stableP []. Qed.
Lemma PyE x y : P x y -> y \in E. Proof. by move=> /stableP []. Qed.
Lemma QxF x y : Q x y -> x \in F. Proof. by move=> /stableP []. Qed.
Lemma QyF x y : Q x y -> y \in F. Proof. by move=> /stableP []. Qed.

Lemma PxnF x y : x \in E = false -> P x y = false.
Proof. by apply contraFF => /stableP []. Qed.
Lemma PnxF x y : x \in E = false -> P y x = false.
Proof. by apply contraFF => /stableP []. Qed.
Definition PF x y (H : x \in E = false) := (PxnF y H, PnxF y H).
Lemma QxnF x y : x \in F = false -> Q x y = false.
Proof. by apply contraFF => /stableP []. Qed.
Lemma QnxF x y : x \in F = false -> Q y x = false.
Proof. by apply contraFF => /stableP []. Qed.
Definition QF x y (H : x \in F = false) := (QxnF y H, QnxF y H).

Definition simplP x y (H : P x y) z :=
  (PxE H, PyE H,
   ExF (PxE H), ExF (PyE H),
   QF z (ExF (PxE H)), QF z (ExF (PyE H)), andbF, orbF).
Definition simplQ x y (H : Q x y) z :=
  (QxF H, QyF H,
   FxE (QxF H), FxE (QyF H),
   PF z (FxE (QxF H)), PF z (FxE (QyF H)), andbF, orbF).

Lemma ordsumrel_stable :
  stable (E :|: F) (fun x y => [|| P x y, Q x y | (x \in E) && (y \in F)]).
Proof.
  move=> x y /=.
  rewrite !inE => /or3P [/stableP [] -> -> // | /stableP [] -> ->| /andP [] -> ->];
    by rewrite !orbT.
Qed.
Definition ordsumrel := finrel_stable ordsumrel_stable.

Lemma sum_order : orderrel ordsumrel.
Proof.
  move: Hsub => /disjoint_setI0; rewrite -setP => Habs.
  apply/orderrelP; split => [x Hx | x y | y x z] /=; rewrite !finrelE.
  - move: Hx; rewrite inE => /orP [] /posetnn -> //; by rewrite orbT.
  - move=> /andP [] /or3P [Pxy | Qxy | /andP [] HxE HyF].
    + rewrite !(simplP Pxy) /=; by apply (anti_poset Pxy).
    + rewrite !(simplQ Qxy) /=; by apply (anti_poset Qxy).
    + rewrite (ExF HxE) andbF orbF => /orP [/PxE/ExF|/QyF/FxE]; by rewrite ?HxE ?HyF.
  - move=> /or3P [Pxy | Qxy | /andP [] HxE HyF].
    + rewrite !(simplP Pxy) /= => /orP [|->] /=; last by rewrite orbT.
      by move /(poset_trans Pxy) ->.
    + rewrite !(simplQ Qxy) /=; by apply poset_trans.
    + rewrite HxE (FxE HyF) !(QF _ (ExF HxE)) !(PF _ (FxE HyF)) /= orbF.
      move=> /stableP [] _ ->; by rewrite orbT.
Qed.
Definition sum_poset := Poset sum_order.

Lemma sum_posetP x y :
  reflect ([\/ P x y, Q x y | (x \in E) /\ (y \in F)]) (sum_poset x y).
Proof.
  rewrite finrelE; apply (iffP idP).
  - move=> /or3P [->| -> |].
    + by apply Or31. + by apply Or32.
    + move=> /andP [] -> ->; by apply Or33.
  - move=> [H | H | [] -> ->]; rewrite ?orbT //=; by rewrite H ?orbT.
Qed.

Lemma sumLE : {in E &, sum_poset =2 P}.
Proof.
  move=> x y Hx Hy /=; rewrite finrelE /=.
  by rewrite (ExF Hy) (QF _ (ExF Hy)) !andbF !orbF.
Qed.

Lemma sumPE : {in F &, sum_poset =2 Q}.
Proof.
  move=> x y Hx Hy /=; rewrite finrelE /=.
  by rewrite (FxE Hx) (PF _ (FxE Hx)) !orbF /=.
Qed.

End Sum.


Section WellFounded.

Variable T : finType.
Variable E : {set T}.
Implicit Type P : poset E.


Definition expand P (f : T -> T) := forall x, x \in E -> P x (f x).
Definition contract P (f : T -> T) := forall x, x \in E -> P (f x) x.

Lemma expand_contract_dual P f : expand P f -> contract (dual_poset P) f.
Proof. move=> H x Hx; rewrite dual_posetE; exact: H. Qed.
Lemma contract_expand_dual P f : contract P f -> expand (dual_poset P) f.
Proof. move=> H x Hx; rewrite dual_posetE; exact: H. Qed.
Lemma expand_dual_contract P f : expand (dual_poset P) f -> contract P f.
Proof. rewrite -{2}(dualK P); exact: expand_contract_dual. Qed.
Lemma contract_dual_expand P f : contract (dual_poset P) f -> expand P f.
Proof. rewrite -{2}(dualK P); exact: contract_expand_dual. Qed.

Lemma expand_stable P f x : expand P f -> x \in E -> f x \in E.
Proof. by move => H/H/stableP []. Qed.
Lemma contract_stable P f x : contract P f -> x \in E -> f x \in E.
Proof. by move => H/H/stableP []. Qed.

Lemma expand_iterP P f n x :
  expand P f -> x \in E -> iter n f x \in E /\ P x (iter n f x).
Proof.
  move=> H Hx; elim: n x Hx => [| n IHn] x Hx /=; first by split; last exact: posetnn.
  have:= IHn x Hx => [] [] Hiter Pif; split; first exact: expand_stable.
  apply (poset_trans Pif); exact: H.
Qed.
Lemma contract_iterP P f n x :
  contract P f -> x \in E -> iter n f x \in E /\ P (iter n f x) x.
Proof. move/contract_expand_dual; rewrite -dual_posetE; exact: expand_iterP. Qed.

Theorem expand_iter_fix P f x :
  expand P f -> x \in E -> { i | iter i.+1 f x = iter i f x }.
Proof.
  move=> Hexp Hx.
  have : #|[set y | P x y]| <= #|[set: T]| by apply subset_leqif_card; apply subsetT.
  case: #|[set: T]| => [| n] H.
    exfalso; move: H; rewrite leqn0 cards_eq0 -subset0 => /subsetP H.
    have {H} := H x; rewrite inE in_set0 => H.
    by have:= H (posetnn Hx).
  elim: n x Hx H => [| n IHn] x Hx H.
  - exists 0; apply/eqP.
    have {H} : [set y | P x y] = [set x].
      apply/eqP; rewrite eq_sym eqEcard; apply/andP; split; last by rewrite cards1.
      apply/subsetP => z; rewrite in_set1 inE => /eqP ->; exact: posetnn.
    rewrite -setP /= => Heq.
    have:= Heq (f x); rewrite !inE => <-.
    by apply Hexp.
  - case (leqP #|[set y | P x y]| n.+1) => [/(IHn x Hx) //| Hcard].
    case: (altP (f x =P x)) => Hfx; first by exists 0.
    have {H Hcard} /eqP : #|[set y | P x y]| = n.+2 by apply anti_leq; rewrite H Hcard.
    have Hint : [set y | strict P x y] :&: [set x] = set0.
      rewrite -setP => z; by rewrite !inE /strict /= eq_sym -andbA andNb andbF.
    have <- : [set y | strict P x y] :|: [set x] = [set y | P x y].
      rewrite -setP => z; rewrite !inE /strict /=.
      case (boolP (P x z)) => /=; first by rewrite eq_sym orNb.
      apply contraNF => /eqP ->; exact: posetnn.
    rewrite cardsU Hint {Hint} cards1 cards0 addn1 subn0 eqSS => /eqP Hcard.
    have {IHn} /IHn Hrec : (f x) \in E by move: (stableP (Hexp x Hx)) => [].
    have /Hrec : #|[set y | P (f x) y]| <= n.+1.
      rewrite -Hcard; apply subset_leqif_card; apply/subsetP => z.
      rewrite !inE; apply strict_poset_trans.
      by rewrite /strict /= (Hexp x Hx) eq_sym Hfx.
    move=> [] i Hi; exists i.+1; move: Hi; by rewrite !iterSr.
Qed.

Corollary contract_iter_fix P f x :
  contract P f -> x \in E -> { i | iter i.+1 f x = iter i f x }.
Proof. move/contract_expand_dual; exact: expand_iter_fix. Qed.

End WellFounded.


(******************************************************************************)
(*                                                                            *)
(*                            Poset's elements                                *)
(*                                                                            *)
(******************************************************************************)

Section MaxMin.

Variable T : finType.
Variable E : {set T}.
Implicit Type P : poset E.

Definition ismax P x := x \in P /\ forall y, y \in P -> P x y -> x = y.
Definition predmax P x := (x \in P) && [forall y in P, (P x y) ==> (x == y)].
Definition ismin P x := x \in P /\ forall y, y \in P -> P y x -> x = y.
Definition predmin P x := predmax (dual_poset P) x.

Lemma max_minE P x : ismax P x <-> ismin (dual_poset P) x.
Proof.
  rewrite /ismax /ismin /= !posetE.
  split => [] [] Hx H; split => [//| y].
  - rewrite dual_posetE posetE; exact: H.
  - have:= H y; by rewrite dual_posetE posetE.
Qed.
Lemma min_maxE P x : ismin P x <-> ismax (dual_poset P) x.
Proof. by rewrite -{1}(dualK P) max_minE. Qed.

Lemma predmaxP P x : reflect (ismax P x) (predmax P x).
Proof.
  apply (iffP idP).
  - move=> /andP [] Hx /forallP Hall; split => [| y Hy Hxy]; first exact Hx.
    have {Hall} := Hall y => /implyP Hall.
    have {Hall} := Hall Hy => /implyP Hall.
    apply/eqP; by apply Hall.
  - move=> [] Hx H; apply/andP; split; first exact Hx.
    apply/forallP => y; apply/implyP => /H{H}H.
    by apply/implyP => /H ->.
Qed.

Lemma predminP P x : reflect (ismin P x) (predmin P x).
Proof. rewrite /predmin; apply (iffP idP); by rewrite min_maxE => /predmaxP. Qed.

Theorem hasmaxrel P x : x \in P -> { m | ismax P m /\ P x m }.
Proof.
  pose f z := if pickP (mem [set y | strict P z y]) is Pick y _ then y else z.
  have Hf : expand P f.
    move=> z Hz; rewrite /f.
    case: (pickP (mem [set y | strict P z y])) => [y |_]; last exact: posetnn.
    rewrite !inE; exact: strictW.
  move=> Hx; have := (expand_iter_fix Hf Hx) => [] [] n /=.
  set m := iter n f x => Hn.
  exists m; repeat split; try by have := (expand_iterP n Hf Hx) => [] [].
  move=> y Hy Pyf.
  move: Hn; rewrite {1}/f.
  case: (pickP (mem [set y | strict P m y])) => [y0 Habs Hy0| H _].
  - exfalso; move: Habs; by rewrite !inE /strict Hy0 /= eq_refl andbF.
  - have:= H y; by rewrite !inE /strict /= Pyf /= => /negbFE/eqP.
Qed.

Corollary hasminrel P x : x \in P -> { m | ismin P m /\ P m x}.
Proof.
  rewrite posetE -(posetE (dual_poset P)) => /hasmaxrel [] m [].
  have:= (min_maxE P m) => [] [] _ H/H{H} Hmin.
  rewrite dual_posetE => Hxm.
  by exists m.
Qed.

Corollary hasmax P x : x \in P -> { m | ismax P m }.
Proof. move/hasmaxrel => [] m [] Hm _; by exists m. Qed.

Corollary hasmin P x : x \in P -> { m | ismin P m }.
Proof. move/hasminrel => [] m [] Hm _; by exists m. Qed.

End MaxMin.

Section Covers.

Variable T : finType.
Variable E : {set T}.
Variable P Q : poset E.

Definition closed_interv m n := [set x : T | (P m x) && (P x n)].
Definition open_interv m n := [set x : T | (strict P m x) && (strict P x n)].

Definition cover : rel T := fun m n => (strict P m n) && (open_interv m n == set0).

Lemma cover_rel a b : cover a b -> P a b.
Proof. by rewrite /cover /strict /= => /andP [] /andP []. Qed.

Lemma cover_intrans a b c : cover a b -> cover b c -> ~~ cover a c.
Proof.
  move => /andP [] Qab _ /andP [] Qbc _.
  apply (introN idP) => /andP [] _ /eqP; rewrite /open_interv -setP => Iac.
  have := Iac b.
  by rewrite in_set0 inE Qab Qbc.
Qed.

End Covers.

Section Extension.

Variable T : finType.
Variable E : {set T}.

Implicit Type R S : finrelType E.
Implicit Type P Q : poset E.

Lemma ext_refl R : ext R R.
Proof. by apply/extP. Qed.

Lemma ext_antisym_rel R S : ext R S -> ext S R -> R = S.
Proof.
  move=> /extP HRS /extP HSR; rewrite finrel_eqE => x y.
  apply/(sameP idP); apply(iffP idP).
  - exact: HSR. - exact: HRS.
Qed.

Lemma ext_antisym P Q : ext P Q -> ext Q P -> P = Q.
Proof. move=> HPQ HQP; apply val_inj => /=; by apply ext_antisym_rel. Qed.

Lemma ext_trans R S U : ext R S -> ext S U -> ext R U.
Proof. move=> /extP HRS /extP HSU; apply/extP => x y HP; apply HSU; by apply HRS. Qed.

Lemma ext_revrel_impl R S : ext (revrel R) (revrel S) -> ext R S.
Proof. move/extP=> H; apply /extP => x y. rewrite -revrelE => /H; by rewrite revrelE. Qed.

Lemma ext_revrelE R S : ext (revrel R) (revrel S) = ext R S.
Proof.
  apply/(sameP idP); apply(iffP idP); last by apply ext_revrel_impl.
  rewrite -{1}(revrelK R) -{1}(revrelK S); by apply ext_revrel_impl.
Qed.

Lemma ext_dualE P Q : ext (dual_poset P) (dual_poset Q) = ext P Q.
Proof. rewrite /dual_poset /=; exact: ext_revrelE. Qed.

Lemma ext_triv P : ext (triv_poset E) P.
Proof. apply/extP => x y; rewrite diagrelE => /andP [] Hx /eqP <-; by apply posetnn. Qed.

Variable P Q : poset E.
Hypothesis HPQ : ext P Q.

Lemma ext_total : {in E &, total P} -> P = Q.
Proof.
  rewrite poset_eqE; move: HPQ => /extP Hext; rewrite /total => Htot x y.
  case: (boolP (x \in E)) => HxE.
  - case: (boolP (y \in E)) => HyE.
    + have := Htot x y HxE HyE => /orP => [] [Hxy | Hyx].
      * by rewrite Hxy (Hext _ _ Hxy).
      * case (boolP (P x y)) => [/Hext -> //| HnP].
        case (boolP (Q x y)) => [HQ |//].
        have Heq := anti_poset HQ (Hext _ _ Hyx); subst y.
        move: HnP; by rewrite Hyx.
    + by rewrite !(finrel_notinR _ x HyE).
    + by rewrite !(finrel_notinL _ y HxE).
Qed.

Lemma strict_ext x y : strict P x y -> strict Q x y.
Proof.
  move: HPQ => /extP Hext.
  rewrite /strict /= => /andP [] /Hext Hs ->.
  by rewrite Hs.
Qed.

Lemma closed_interv_ext m n : closed_interv P m n \subset closed_interv Q m n.
Proof.
  rewrite /closed_interv; move: HPQ => /extP Hext.
  apply/subsetP => i; by rewrite !inE => /andP [] /Hext -> /Hext ->.
Qed.

Lemma open_interv_ext m n : open_interv P m n \subset open_interv Q m n.
Proof.
  rewrite /open_interv.
  apply/subsetP => i; rewrite !inE => /andP [].
  by move=> /strict_ext -> /strict_ext ->.
Qed.

Lemma cover_ext m n : cover Q m n -> P m n -> cover P m n.
Proof.
  rewrite /cover /strict /= => /andP [] /andP [] _ -> Hopen -> /=.
  move: Hopen; rewrite -!subset0; apply: subset_trans.
  by apply open_interv_ext.
Qed.

End Extension.


Section InducedExt.

Variable T : finType.
Variable E F : {set T}.
Hypothesis Hsub : E \subset F.
Variable P Q : poset F.

Lemma ext_induced : ext P Q -> ext (induced Hsub P) (induced Hsub Q).
Proof.
  move/extP => H; apply/extP => x y.
  by rewrite /induced /= !finrelE /= => /and3P [] -> -> /H ->.
Qed.

End InducedExt.


Section SumExtMax.

Variable T : finType.
Variable E F : {set T}.
Hypothesis Hsub : [disjoint E & F].
Variable P : poset E.
Variable Q : poset F.

Lemma sum_ext_max (R : poset (E :|: F)) :
  {in E &, R =2 P} -> {in F &, R =2 Q} ->
  ext (sum_poset Hsub P Q) R -> R = (sum_poset Hsub P Q).
Proof.
  move=> HEP HFQ /extP Hext.
  rewrite poset_eq_inE => x y; rewrite !inE => Hx Hy.
  apply/(sameP idP); apply(iffP idP); first exact: Hext.
  move=> Rxy; apply/sum_posetP.
  move: Hx Hy => /orP [] Hx /orP [] Hy.
  - apply Or31; by rewrite -HEP.
  - by apply Or33.
  - exfalso.
    have Hxy : x = y by apply: (anti_poset Rxy); apply Hext; apply/sum_posetP; apply Or33.
    move: Hsub => /disjoint_setI0; rewrite -setP => Habs.
    have:= Habs x; by rewrite !inE Hx Hxy Hy.
  - apply Or32; by rewrite -HFQ.
Qed.

End SumExtMax.


Section RemCov.

Variable T : finType.
Variable E : {set T}.
Variable P : poset E.
Variable a b : T.
Hypothesis Hcov : cover P a b.

Let Neqab : a != b.
Proof. move: Hcov => /andP []; by rewrite /strict /= => /andP []. Qed.

Lemma remcovrel_stable : stable E (fun m n => (P m n) && ((m, n) != (a, b))).
Proof. by move=> x y /= /andP [] /stableP. Qed.

Lemma remcov_order : orderrel (finrel_stable remcovrel_stable).
Proof.
  apply/orderrelP.
  split => [x Hx | x y | x y z] /=; rewrite !finrelE /=.
  - apply/andP; split; first by apply posetnn.
    by move: Neqab; apply contra => /eqP [] <- <-.
  - move=> /and3P [] /andP [] Pxy _ Pyx _.
    by apply: anti_poset.
  - move=> /andP [] Pxy Hxy /andP [] Pyz Hyz.
    apply/andP; split; first by apply: (poset_trans Pxy Pyz).
    apply (introN idP) => /eqP [] Hy Hz; subst y z.
    move: Hcov => /andP [] _ /eqP; rewrite /open_interv -setP => Iab.
    have := Iab x.
    rewrite in_set0 inE /strict /=.
    rewrite Pxy Pyz /=.
    have -> : x != b by move: Hxy; apply contra => /eqP ->.
    have -> : a != x by move: Hyz; rewrite eq_sym; apply contra => /eqP ->.
    by [].
Qed.
Definition remcov := Poset remcov_order.

Lemma remcov_ext : ext remcov P.
Proof. apply/extP => x y; by rewrite finrelE => /andP []. Qed.

Lemma remcov_max_ext Q : ext Q P -> ~~ Q a b -> ext Q remcov.
Proof.
  move=> /extP HQP Hab; apply/extP => x y Qxy.
  rewrite finrelE; have:= stableP Qxy => [] [] Hx Hy.
  apply/andP; split => //; first by apply HQP.
  move: Hab; by apply contra => /eqP [] <- <-.
Qed.

Lemma remcov_incomp_ab : ~~ (remcov a b || remcov b a).
Proof.
  rewrite !finrelE.
  apply/norP; split; apply/nandP.
  + right; by rewrite negbK.
  + left; move: Neqab; apply contra => H.
    apply/eqP; apply: (anti_poset _ H); by apply cover_rel.
Qed.

End RemCov.


Section AddCov.

Variable T : finType.
Variable E : {set T}.
Variable P : poset E.
Variable a b : T.
Hypothesis Ha : a \in E.
Hypothesis Hb : b \in E.
Hypothesis Hinc : ~~ (P a b || P b a).

Let Neqab : a != b.
Proof.
  move: Hinc => /norP [] _.
  apply contra => /eqP ->.
  by apply posetnn.
Qed.

Lemma addcovrel_stable : stable E (fun m n => (P m n) || (P m a && P b n)).
Proof. by move=> x y /orP [/stableP // |] /andP [] /stableP [] -> _ /stableP [] _ ->. Qed.

Lemma addcov_order : orderrel (finrel_stable addcovrel_stable).
Proof.
  apply/orderrelP.
  split => [x Hx | x y | x y z] /=; rewrite !finrelE /=.
  - apply/orP; left; by apply: posetnn.
  - move=> /andP [] /orP [Hxy | /andP [] Hxa Hby] /orP [Hyx | /andP [] Hya Hbx].
    + by apply: anti_poset.
    + exfalso; move: Hinc.
      by rewrite (poset_trans Hbx (poset_trans Hxy Hya)) orbT.
    + exfalso; move: Hinc.
      by rewrite (poset_trans Hby (poset_trans Hyx Hxa)) orbT.
    + exfalso; move: Hinc.
      by rewrite (poset_trans Hby Hya) orbT.
  - move=> /orP [Hyx | /andP [] Hya Hbx] /orP [Hxz | /andP [] Hxa Hbz]; apply/orP.
    + left; by apply (poset_trans Hyx Hxz).
    + right; by rewrite (poset_trans Hyx Hxa) Hbz.
    + right; by rewrite Hya (poset_trans Hbx Hxz).
    + exfalso; move: Hinc.
      by rewrite (poset_trans Hbx Hxa) orbT.
Qed.
Definition addcov := Poset addcov_order.

Lemma addcov_ext : ext P addcov.
Proof. apply/extP => x y Pxy /=; rewrite finrelE; by rewrite Pxy. Qed.

Lemma addcov_min_ext (Q : poset E) : ext P Q -> Q a b -> ext addcov Q.
Proof.
  move=> /extP HPQ Hab; apply/extP => x y.
  rewrite finrelE => /orP [Pxy | /andP [] Pxa Pyb].
  - by apply HPQ.
  - apply (poset_trans (HPQ _ _ Pxa)); apply (poset_trans Hab); by apply HPQ.
Qed.

Lemma addcov_ab : cover addcov a b.
Proof.
  rewrite /cover/strict /= finrelE Neqab !posetnn //= orbT /open_interv -subset0 /=.
  apply/subsetP => i; rewrite in_set0 inE.
  rewrite /strict /= !finrelE !posetnn // /= andbT.
  move=> /and3P [] /andP [] /orP [Pai|Pbi] Hai /orP [Pib|Pia] Hib.
  + move: Hinc; by rewrite (poset_trans Pai Pib).
  + move: Hai; by rewrite (anti_poset Pai Pia) eq_refl.
  + move: Hib; by rewrite (anti_poset Pbi Pib) eq_refl.
  + move: Hinc; by rewrite (poset_trans Pbi Pia) orbT.
Qed.

End AddCov.


Section Intersect.

Variable T : finType.
Variable E : {set T}.
Variable SP : {set poset E}.
Hypothesis SPn0 : SP != set0.

Definition intrelset := \bigcap_(P in SP) RelSet P.

Lemma intrelsetP x y :
  reflect (forall P : poset E, P \in SP -> P x y) ((x, y) \in intrelset).
Proof.
  apply (iffP idP).
  - move=> /bigcapP H P /H{H}; by rewrite -finrel_relsetE.
  - move=> H; apply/bigcapP => P /H{H}; by rewrite -finrel_relsetE.
Qed.

Lemma intrelset_stable : stablerel E intrelset.
Proof.
  apply/stablerelP => x y; rewrite /rel_of_set => /intrelsetP Hxy.
  move: SPn0 => /set0Pn [] P /Hxy; exact: stableP.
Qed.

Lemma intrelset_order : orderrel (FinRel intrelset_stable).
Proof.
  apply/orderrelP.
  split => [x Hx | x y | y x z] /=; rewrite !finrel_setE /= /rel_of_set.
  - apply/intrelsetP => Q _; exact: posetnn.
  - move=> /andP [] /intrelsetP Hxy /intrelsetP Hyx.
    move: SPn0 => /set0Pn [] P HP.
    exact: (anti_poset (Hxy _ HP) (Hyx _ HP)).
  - move=> /intrelsetP Hxy /intrelsetP Hyz.
    apply/intrelsetP => P HP.
    exact: (poset_trans (Hxy _ HP) (Hyz _ HP)).
Qed.
Definition intposet := Poset intrelset_order.

Lemma intposetP x y :
  reflect (forall P : poset E, P \in SP -> P x y) (intposet x y).
Proof. rewrite finrel_setE /=; by apply intrelsetP. Qed.

Lemma intposet_meet P :
  (forall Q : poset E, Q \in SP -> ext P Q) -> ext P intposet.
Proof.
  move=> H; apply/extP => x y Pxy.
  apply/intposetP => Q /H /extP; by apply.
Qed.

End Intersect.


Section ExtRelPoset.

Variable T : finType.
Variable E : {set T}.
Implicit Type P L : finrelType E.

Lemma ext_rel_stable : stable [set: finrelType E] (fun A B => ext A B).
Proof. move=> x y /= _; by rewrite inE. Qed.
Lemma ext_rel_order : orderrel (finrel_stable ext_rel_stable).
Proof.
  apply/orderrelP;
  split => [x Hx | x y | y x z] /=; rewrite !finrelE.
  - exact: ext_refl.
  - move=> /andP []; exact: ext_antisym_rel.
  - exact: ext_trans.
Qed.
Definition ExtRelPoset := Poset ext_rel_order.

End ExtRelPoset.


Section ExtPoset.

Variable T : finType.
Variable E : {set T}.
Implicit Type P L : poset E.

Lemma ext_stable : stable [set: poset E] (fun A B => ext A B).
Proof. move=> x y /= _; by rewrite inE. Qed.
Lemma ext_order : orderrel (finrel_stable ext_stable).
Proof.
  apply/orderrelP;
  split => [x Hx | x y | y x z] /=; rewrite !finrelE.
  - exact: ext_refl.
  - move=> /andP []; exact: ext_antisym.
  - exact: ext_trans.
Qed.
Definition ExtPoset := Poset ext_order.

Lemma max_extP P : (ismax ExtPoset P) <-> {in E &, total P}.
Proof.
  split.
  - move=> /predmaxP H; apply/totalrelP; move: H; apply contraLR.
    rewrite negb_forall => /existsP [] x; rewrite negb_imply => /andP [] Hx.
    rewrite negb_forall => /existsP [] y; rewrite negb_imply => /andP [] Hy Hinc.
    rewrite negb_and inE //= negb_forall; apply/existsP.
    exists (addcov Hinc); apply/implyP; rewrite inE /= => /implyP.
    rewrite finrelE => H.
    have {H} /eqP := (H (addcov_ext Hinc)); rewrite poset_eqE => H.
    have:= H x y.
    have:= Hinc; rewrite negb_or => /andP [] /negbTE -> _.
    have:= addcov_ab Hx Hy Hinc; by rewrite /cover => /andP [] /strictW ->.
  - move=> H; split; first by rewrite inE.
    move=> Q _; rewrite finrelE => Hext.
    exact: ext_total.
Qed.

Definition linext P L := ext P L && (totalrel L).

Lemma linextP P L : reflect (ext P L /\ {in E &, total L}) (linext P L).
Proof.
  rewrite /linext; apply (iffP idP).
  - move=> /andP [] -> /totalrelP Htot; split; first by [].
    by move=> x y /= /Htot{Htot} H/H{H}.
  - by move=> [] -> /= /totalrelP.
Qed.

Theorem exists_linext P : { L : poset E | linext P L }.
Proof.
  have /hasmaxrel : P \in ExtPoset by rewrite inE.
  move=> [] L [] /max_extP; rewrite !finrelE => Htot Hext.
  exists L; apply/linextP; split; first exact Hext.
  by move=> x y /Htot H/H{H}.
Qed.

Lemma linext_ncmp P x y :
  x \in P -> y \in P -> ~~ P x y -> { L : poset E | linext P L /\ L y x }.
Proof.
  move=> /= Hx Hy; case: (boolP (P y x)) => Hyx Hxy.
  - have := exists_linext P => [] [] L HL.
    exists L; split; first exact HL.
    move: HL => /linextP [] /extP H _; by apply H.
  - have Hinc : ~~ (P y x || P x y) by rewrite negb_or Hyx Hxy.
    have := exists_linext (addcov Hinc) => [] [] L /linextP [] Hext Htot.
    exists L; split.
    + apply/linextP; split; last exact Htot.
      apply: (ext_trans _ Hext).
      by apply addcov_ext.
    + apply: (extP _ _ Hext).
      apply cover_rel.
      by apply addcov_ab.
Qed.

Lemma linextn0 P : [set L : poset E | linext P L ] != set0.
Proof.
  apply/set0Pn; have:= exists_linext P => [] [] L HL.
  exists L; by rewrite inE.
Qed.

Theorem linext_inter P : P = intposet (linextn0 P).
Proof.
  rewrite poset_eqE => x y.
  apply/(sameP idP); apply(iffP idP).
  - case: (boolP (P x y)) => // Hxy Habs.
    have:= stableP Habs => [] [] Hx Hy.
    have:= linext_ncmp Hx Hy Hxy => [] [] L [].
    rewrite -in_set => /(intposetP (linextn0 P)) Hncmp Lxy.
    have Heq : x = y by apply: (anti_poset _ Lxy); apply Hncmp.
    move: Hxy; by rewrite Heq (posetnn).
  - move=> HP; apply/intposetP => L.
    rewrite inE => /linextP [] /extP Hext _.
    by apply Hext.
Qed.

End ExtPoset.


Section Convex.

Variable T : finType.

Definition convex E (P : poset E) (S : {set T}) :=
  [forall x in S, forall z in S, forall y, (P x y && P y z) ==> (y \in S)].

Lemma convexP E (P : poset E) (S : {set T}) :
  reflect (forall x y z, x \in S -> z \in S -> P x y -> P y z -> y \in S) (convex P S).
Proof.
  apply (iffP idP) => [|H].
  - move=> /forallP Hallx x y z /(implyP (Hallx x)) {Hallx}.
    move=> /forallP Hallz /(implyP (Hallz z)) {Hallz} /forallP Hally Hxy Hyz.
    apply (implyP (Hally y)); by rewrite Hxy Hyz.
  - apply/forallP => x; apply/implyP => /H{H}H.
    apply/forallP => z; apply/implyP => /H{H}H.
    apply/forallP => y; apply/implyP => /andP [].
    exact: H.
Qed.

Variable E F : {set T}.
Hypothesis Hsub : E \subset F.
Variable P : poset F.
Hypothesis Hconv : convex P E.

Definition Sup := [set x in F :\: E | [exists z in E, P z x]].
Definition Inf := F :\: ( E :|: Sup ).

Lemma InfF : Inf \subset F. by apply/subsetP => x; rewrite !inE => /andP []. Qed.
Lemma SupF : Sup \subset F. by apply/subsetP => x; rewrite !inE => /andP [] /andP []. Qed.
Lemma disjoint_E_Sup : [disjoint E & Sup].
Proof.
  rewrite disjoint_sym disjoints_subset /Sup.
  apply/subsetP => x; by rewrite !inE => /andP [] /andP [].
Qed.
Lemma disjoint_Inf_ESup : [disjoint Inf & (E :|: Sup)].
Proof.
  rewrite disjoint_sym disjoints_subset /Inf.
  apply/subsetP => x; rewrite !inE => H; by rewrite H.
Qed.
Lemma disjoint_Inf_E : [disjoint Inf & E].
Proof.
  have:= disjoint_Inf_ESup; rewrite !disjoints_subset setCU => /subset_trans; apply.
  by apply/subsetP => z; rewrite !inE => /andP [].
Qed.
Lemma disjoint_Inf_Sup : [disjoint Inf & Sup].
Proof.
  have:= disjoint_Inf_ESup; rewrite !disjoints_subset setCU => /subset_trans; apply.
  by apply/subsetP => z; rewrite !inE => /andP [].
Qed.
Lemma HeqF : (Inf :|: (E :|: Sup)) = F.
Proof.
  rewrite /Inf /Sup -setP => x; rewrite !inE.
  case: (boolP (x \in F)) => Hx; rewrite ?andbT /= ?andbF /= ?orbF.
  - case: (boolP (x \in E)) => HxE; by rewrite //= orNb.
  - move: Hx; apply contraNF; by apply (subsetP Hsub).
Qed.
Lemma FuP x : x \in F -> [|| x \in Inf, x \in E | x \in Sup].
Proof.
  rewrite -{1}HeqF inE => /orP [-> //=|].
  rewrite inE => /orP [] ->; by rewrite !orbT.
Qed.

Definition simpl := (cast_posetE, finrelE, in_setU, orbA).

Theorem convex_extlin_extend (L : poset E) :
  linext (induced Hsub P) L ->
  { M : poset F | [/\ induced Hsub M = L, linext P M & convex M E] }.
Proof.
  move=> Hlin.
  have := exists_linext (induced SupF P) => [] [] LSup LSupP.
  have := exists_linext (induced InfF P) => [] [] LInf LInfP.
  pose LESup := sum_poset disjoint_E_Sup L LSup.
  pose M := sum_poset disjoint_Inf_ESup LInf LESup.

  exists (cast_poset HeqF M); split.
  - rewrite poset_eq_inE => x y Hx Hy.
    rewrite inducedE // !simpl.
    have HySup := ExF disjoint_E_Sup Hy; rewrite HySup (QF _ _ HySup) !orbF {HySup}.
    have:= disjoint_Inf_ESup; rewrite disjoints_subset setCU => H1.
    have HxInf := FxE disjoint_Inf_E Hx; by rewrite HxInf (QF _ _ HxInf) /= andbF !orbF.
  - apply/linextP; split.
    apply/extP => x y Pxy; have:= stableP Pxy => [] [] /FuP/or3P [] Hx.
    + move=> /FuP/orP [Hy|].
      * suff: LInf x y by rewrite !simpl => ->.
        move: LInfP => /linextP [] /extP Hext _; apply Hext => {Hext}.
        by rewrite inducedE.
      * move=> /orP [] Hy; by rewrite !simpl Hx Hy /= !orbT.
    + move=> /FuP/or3P [] Hy.
      * exfalso; move: Hy; rewrite inE => /andP []; rewrite inE negb_or => /andP [] H1 H2 _.
        move: H2; rewrite inE negb_and inE negb_and H1 /=.
        have := stableP Pxy => [] [] _ -> /=.
        rewrite negb_exists => /forallP H.
        have:= H x; by rewrite Hx Pxy.
      * suff: L x y by rewrite !simpl => ->; rewrite orbT.
        move: Hlin => /linextP [] /extP Hext _; apply Hext => {Hext}.
        by rewrite inducedE.
      * by rewrite !simpl Hx Hy /= !orbT.
    + move=> /FuP/or3P [] Hy.
      * exfalso.
        move: Hy Hx; rewrite !inE negb_or => /andP [] /andP [] Hy; rewrite Hy /=.
        have:= stableP Pxy => [] [] -> ->; rewrite !andbT /=.
        rewrite negb_exists => /forallP H _ /andP [] Hx /existsP [] z /andP [] Hz Pzx.
        have:= H z; by rewrite Hz /= (poset_trans Pzx Pxy).
      * exfalso.
        move: Hy Hx; rewrite !inE => Hy /andP [] /andP [] HxE HxF.
        move=> /existsP [] z /andP [] Hz Pzx.
        move: Hconv => /convexP HconvP.
        by rewrite (HconvP _ _ _ Hz Hy Pzx Pxy) in HxE.
      * suff: LSup x y by rewrite !simpl => ->; rewrite !orbT.
        move: LSupP => /linextP [] /extP Hext _; apply Hext => {Hext}.
        by rewrite inducedE.
  - move=> x y /=.
    rewrite !simpl => /FuP/or3P [] Hx /FuP/or3P [] Hy; try by rewrite Hx Hy /= !orbT /=.
    * move: LInfP => /linextP [] _ Htot.
      have := Htot _ _ Hx Hy => /orP [] ->; by rewrite /= ?orbT.
    * move: Hlin => /linextP [] _ Htot.
      have := Htot _ _ Hx Hy => /orP [] ->; by rewrite /= ?orbT.
    * move: LSupP => /linextP [] _ Htot.
      have := Htot _ _ Hx Hy => /orP [] ->; by rewrite /= ?orbT.
  - apply/convexP => x y z Hx Hz.
    rewrite !simpl Hx Hz.
    have HxInf := FxE disjoint_Inf_E Hx; rewrite HxInf (QF _ _ HxInf) /= ?andbT ?orbF.
    have HxSup := ExF disjoint_E_Sup Hx; rewrite (QF _ _ HxSup) /= ?andbT ?orbF.
    have HzInf := FxE disjoint_Inf_E Hz; rewrite (QF _ _ HzInf) /= ?andbT ?orbF.
    have HzSup := ExF disjoint_E_Sup Hz; rewrite HzSup (QF _ _ HzSup) andbF /= ?andbT ?orbF.
    move {HxInf HxSup HzInf HzSup} => /orP [Lxy _| Supy /orP [Lyz|Infy]].
    + by have := stableP Lxy => [] [].
    + by have := stableP Lyz => [] [].
    + exfalso.
      have:= disjoint_Inf_ESup; rewrite disjoints_subset => /subsetP H.
      have := H y Infy; by rewrite inE inE Supy orbT.
Qed.

End Convex.

Section LinearPoset.

Require Import path.
Variable T : finType.
Variable E : {set T}.
Implicit Type s : seq T.

Lemma index_mem2 s x y :
  y \in s -> (index x s <= index y s) -> mem2 s x y.
Proof.
  rewrite /mem2 => Hy.
  elim: s (index x s) Hy => [|s0 s' IHs] n //=.
  rewrite in_cons eq_sym => /orP [/eqP -> | H].
    rewrite eq_refl; case: n => //=; by rewrite in_cons eq_refl.
  have {IHs} Hrec := IHs _ H.
  case: (altP (s0 =P y)) => [<-| Hneq].
  + rewrite leqn0 => /eqP ->; by rewrite in_cons eq_refl.
  + case: n => [_|n] //=; first by rewrite in_cons H orbT.
    rewrite ltnS; by apply Hrec.
Qed.

Lemma mem2_index s x y :
  uniq s -> mem2 s x y -> (index x s <= index y s).
Proof.
  rewrite /mem2; elim: s (index x s) => [|s0 s IHs] n //= /andP [] Hs0 H.
  case: n => [| n] //= Hdrop.
  case: (altP (s0 =P y)) => Hsy.
  - exfalso; subst s0; move: Hs0.
    by rewrite -(cat_take_drop n s) mem_cat Hdrop orbT.
  - case: n Hdrop => [_|n] //=.
    rewrite ltnS; by apply IHs.
Qed.

Lemma mem2_indexE s x y :
  y \in s -> uniq s -> mem2 s x y = (index x s <= index y s).
Proof.
  move=> Hy Huniq; apply/(sameP idP); apply(iffP idP).
  - exact: index_mem2.
  - exact: mem2_index.
Qed.

Section PermEqS.

Variable s : seq T.
Hypothesis Hperm : perm_eq s (enum E).

Lemma mem2_stable : stable E (mem2 s).
Proof.
  move=> x y. rewrite /mem2 -![_ \in E]mem_enum -!(perm_eq_mem Hperm).
  case: (boolP (x \in s)) => [_ Hy|Hx].
  - split => //; by rewrite -(cat_take_drop (index x s) s) mem_cat Hy orbT.
  - have -> : index x s = size s.
      apply/eqP; move: Hx; by rewrite -index_mem -leqNgt eqn_leq index_size => ->.
    by rewrite drop_size in_nil.
Qed.

Lemma rel_of_seq_order : orderrel (finrel_stable mem2_stable).
Proof.
  apply/orderrelP.
  have Huniq : uniq s by rewrite (perm_eq_uniq Hperm); apply enum_uniq.
  have Hin : E =i s by move => x; rewrite (perm_eq_mem Hperm) mem_enum.
  split => [x Hx | x y | y x z] /=; rewrite !finrelE //=.
  - move: Hx; rewrite Hin.
    elim: s {Huniq Hin} => [| s0 st IHs] //=.
    rewrite /mem2 in_cons /= eq_sym.
    case: (altP (s0 =P x)) => [-> _ |_] /=; first by rewrite in_cons eq_refl.
    by apply IHs.
  - move=> /andP [] Hsxy Hsyx.
    have Heq : index x s = index y s.
      apply anti_leq; by rewrite (mem2_index Huniq Hsxy) (mem2_index Huniq Hsyx).
    have:= mem2_stable Hsxy; rewrite !Hin => [] [] Hx Hy.
    by rewrite -(nth_index x Hx) Heq (nth_index _ Hy).
  - move=> /(mem2_index Huniq) Hxy Hyz.
    have:= mem2_stable Hyz => [] [] _; rewrite Hin => Hz.
    move: Hyz => /(mem2_index Huniq) Hyz.
    apply (index_mem2 Hz); by apply (leq_trans Hxy Hyz).
Qed.

Definition poset_of_seq := Poset rel_of_seq_order.

Lemma poset_of_seq_total : {in E &, total poset_of_seq}.
Proof.
  move=> x y Hx Hy /=.
  rewrite !finrelE /=.
  have Huniq : uniq s by rewrite (perm_eq_uniq Hperm); apply enum_uniq.
  have := Hy; have := Hx.
  rewrite -mem_enum -[y \in _]mem_enum -!(perm_eq_mem Hperm) => Hxs Hyx.
  rewrite !mem2_indexE //; by apply leq_total.
Qed.

End PermEqS.

Section PosetOfSeq.

Variable P : poset E.
Hypothesis HtotP : {in E &, total P}.

Definition expposet_of_seq :=
  let: exist L _ := exists_linext (expanded [set: T] P) in L.

Lemma expposet_of_seq_total : total expposet_of_seq.
Proof.
  rewrite /expposet_of_seq; case: exists_linext => L /linextP [] _ Hlin.
  by move=> x y; apply Hlin.
Qed.
Lemma expposet_of_seqE : P = induced (subsetT E) expposet_of_seq.
Proof.
  apply: (ext_total _ HtotP).
  rewrite [P](induced_expanded (subsetT E)) /expposet_of_seq.
  apply ext_induced.
  by case: exists_linext => L /linextP [].
Qed.

Definition seq_of_poset := sort expposet_of_seq (enum E).

Lemma perm_seq_of_poset : (perm_eq seq_of_poset (enum E)).
Proof. apply/perm_eqlP; by apply perm_sort. Qed.

Lemma seq_of_poset_uniq : uniq seq_of_poset.
Proof. rewrite (perm_eq_uniq perm_seq_of_poset); by apply enum_uniq. Qed.

Lemma sorted_seq_of_poset : sorted P seq_of_poset.
Proof.
  have:= sort_sorted expposet_of_seq_total (enum E); rewrite -/seq_of_poset.
  have: all (mem E) seq_of_poset.
    apply/allP => x /=; by rewrite (perm_eq_mem perm_seq_of_poset) mem_enum.
  case: seq_of_poset => [| s0 s] //= /andP [].
  elim: s s0 => [| s1 s IHs] //= s0 Hs0.
  move=> /andP [] Hs1 /(IHs s1 Hs1) {IHs} Hrec /andP [] Hexp /Hrec ->.
  by rewrite andbT expposet_of_seqE inducedE.
Qed.

Lemma seq_of_posetK : P = poset_of_seq perm_seq_of_poset.
Proof.
  apply ext_total; last exact HtotP.
  apply/extP => x y Pxy.
  have /perm_eqlP := perm_sort expposet_of_seq (enum E); rewrite -/seq_of_poset => Hperm.
  rewrite finrelE; have:= stableP Pxy => [] [] Hx Hy.
  rewrite (mem2_indexE _ _ seq_of_poset_uniq); last by rewrite (perm_eq_mem Hperm) mem_enum.
  move: sorted_seq_of_poset Hx Hy.
  rewrite -[x \in E]mem_enum -[y \in E]mem_enum -!(perm_eq_mem Hperm).
  case: seq_of_poset {Hperm} => [|s0 s] //=.
  elim: s s0 => [| s1 s IHs] //= s0.
    move=> _; rewrite !in_cons !in_nil !orbF=> /eqP -> /eqP ->; by rewrite eq_refl.
  move=> /andP [] P01 Hpath.
  rewrite in_cons [y \in _]in_cons eq_sym [y == _]eq_sym.
  case: (altP (s0 =P x)) => //= Hxs0 Hxs.
  case: (altP (s0 =P y)) => //= Hys0 Hys.
  - exfalso; subst s0.
    have /allP Hall := order_path_min (poset_trans (P := P)) Hpath.
    move: Hxs Hxs0 => /orP [/eqP Hx |/Hall].
    + rewrite -Hx in P01; by rewrite (anti_poset Pxy P01) eq_refl.
    + move=> /(poset_trans P01) /(anti_poset Pxy) <-; by rewrite eq_refl.
  - rewrite ltnS; by apply (IHs _ Hpath Hxs Hys).
Qed.

End PosetOfSeq.


Lemma poset_of_seqK s (Hperm : perm_eq s (enum E)) : seq_of_poset (poset_of_seq Hperm) = s.
Proof.
  apply (eq_sorted (poset_trans (P := poset_of_seq Hperm))).
  - move=> x y => /andP []; by apply anti_poset.
  - apply (sorted_seq_of_poset (poset_of_seq_total Hperm)).
  - have : all (mem E) s by apply /allP => x; rewrite (perm_eq_mem Hperm) mem_enum.
    have /= := enum_uniq (mem E); rewrite -(perm_eq_uniq Hperm).
    case: s Hperm => [//=| s0 s] Hperm Huniq /= Hall.
    rewrite (eq_path (finrel_stableE _)) {Hperm}.
    elim: s s0 Huniq Hall => [//=| s1 s IHs] s0 Huniq /andP [] Hs0 Hall /=.
    apply/andP; split; first by rewrite /mem2 /= eq_refl !in_cons eq_refl orbT.
    have {IHs} /IHs Hrec : uniq (s1 :: s) by move: Huniq => /= /andP [].
    have {Hrec Hall} Hpath := Hrec Hall.
    rewrite (eq_in_path (e' := (fun x : T => mem2 (s1 :: s) x))) //.
    move=> x y Hx Hy /=; rewrite !mem2_indexE //=; first last.
    + move: Hy; rewrite !in_cons => ->; by rewrite orbT.
    + by move: Huniq => /= /andP [].
    case: (altP (s0 =P x)) => [Habs| _].
      exfalso; subst s0; by move: Hx Huniq => /= ->.
    case: (altP (s0 =P y)) => [Habs| _].
      exfalso; subst s0; by move: Hy Huniq => /= ->.
    by rewrite ltnS.
  - apply (perm_eq_trans (perm_seq_of_poset _)); by rewrite perm_eq_sym.
Qed.

Record linposet := LinPoset { POS :> poset E; _ : totalrel POS }.
Canonical linposet_subType := Eval hnf in [subType for POS].
Definition linposet_eqMixin := Eval hnf in [eqMixin of linposet by <:].
Canonical linposet_eqType := Eval hnf in EqType linposet linposet_eqMixin.

Record permseq := PermSeq { Perm :> seq T; _ : perm_eq Perm (enum E) }.
Canonical permseq_subType := Eval hnf in [subType for Perm].
Definition permseq_eqMixin := Eval hnf in [eqMixin of permseq by <:].
Canonical permseq_eqType := Eval hnf in EqType permseq permseq_eqMixin.

Definition permseq_of_linposet (P  : linposet) : permseq :=
  PermSeq (perm_seq_of_poset P).

Definition linposet_of_permseq (s : permseq) : linposet :=
  let: PermSeq perm Hperm := s in
  LinPoset (introT (totalrelP (poset_of_seq Hperm)) (poset_of_seq_total Hperm) ).

Lemma linposet_of_permseqK : cancel permseq_of_linposet linposet_of_permseq.
Proof.
  case=> pos Hpos /=; apply val_inj => /=; apply esym; apply seq_of_posetK.
  by apply/totalrelP.
Qed.

Lemma permseq_of_linposetK : cancel linposet_of_permseq permseq_of_linposet.
Proof. case=> perm Hperm /=; apply val_inj => /=; by apply poset_of_seqK. Qed.

Lemma linposet_of_permseq_bij : bijective linposet_of_permseq.
Proof.
  exists permseq_of_linposet.
  exact permseq_of_linposetK.
  exact linposet_of_permseqK.
Qed.

Section SeqExt.

Implicit Type P : poset E.
Definition seqext P (s : permseq) := [forall x, forall y, P x y ==> mem2 s x y].

Lemma seqextP P (s : permseq) : reflect (forall x y, P x y -> mem2 s x y) (seqext P s).
Proof.
  apply (iffP idP).
  - move=> /forallP H x y Pxy.
    have {H} := H x => /forallP H; have {H} := H y => /implyP; by apply.
  - move=> Hall; apply/forallP => x; apply/forallP => y; apply/implyP; exact: Hall.
Qed.

Lemma seqext_linext P (s : permseq) : seqext P s = linext P (linposet_of_permseq s).
Proof.
  case: s => perm Hperm /=; apply/(sameP idP); apply(iffP idP).
  - move=> /linextP [] /extP H _; apply/seqextP => x y /H{H}.
    by rewrite finrelE.
  - move=> /seqextP /= Hall; apply/linextP; split; last exact: poset_of_seq_total.
    apply/extP => x y Pxy; rewrite finrelE; by apply Hall.
Qed.

Lemma linext_seqext P (L : linposet) : linext P L = seqext P (permseq_of_linposet L).
Proof.
  have := linposet_of_permseq_bij => [] [] inv _ H.
  by rewrite -{1}[L]linposet_of_permseqK -seqext_linext.
Qed.

End SeqExt.

End LinearPoset.



Require Import finfun.


(* Definition refltransclosure R :=
  let fix rec n R :=
      if n is n'.+1 then
        let C := (comprel R R) in
        if C == R then R else rec n' C
      else R
  in rec (#|T|*#|T|) (R :|: diagrel).

Lemma refl_refltransclosure R : reflexiverel (refltransclosure R).
Proof.
  rewrite /reflexiverel.
*)
