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

Definition relset := {set (T * T)}.
Definition set_of_rel (R : rel T) : relset := [set p | R p.1 p.2].
Definition rel_of_set (R : relset) : rel T := fun x y => (x, y) \in R.

Lemma rel_of_setK (R : rel T) : rel_of_set (set_of_rel R) =2 R.
Proof. move=> x y; by rewrite /set_of_rel/rel_of_set /= inE /=. Qed.

Implicit Type E : {set T}.
Implicit Type R S : relset.

Definition full E : relset := [set p | (p.1 \in E) && (p.2 \in E)].
Definition diagrel E : relset := [set (x, x) | x in E].
Definition revrel R : relset := [set p | (p.2, p.1) \in R].
Definition comprel R S : relset :=
  [set p | [exists z : T, ((p.1, z) \in R) && ((z, p.2) \in S)]].

Definition stablerel E R := R \subset (full E).
Definition totalrel E R := (full E) \subset (R :|: revrel R).
Definition reflexiverel E R := (diagrel E) \subset R.
Definition irreflexiverel E R := R :&: (diagrel E) == set0.
Definition symmetricrel R := revrel R == R.
Definition antisymmetricrel R := R :&: revrel R \subset (diagrel setT).
Definition transitiverel R := comprel R R \subset R.

Lemma comprelA Q R S : comprel (comprel Q R) S = comprel Q (comprel R S).
Proof.
  rewrite !/comprel -setP => [[x t]]; rewrite !inE /=.
  apply/(sameP idP); apply(iffP idP) => /existsP [].
  + move=> y /andP [] HQ; rewrite inE => /existsP [] z /= /andP [] HR HS.
    apply/existsP; exists z; rewrite HS andbT.
    rewrite inE /=; apply/existsP; exists y; by rewrite HQ HR.
  + move=> z /andP []; rewrite inE /= => /existsP [] y /= /andP [] HQ HR HS.
    apply/existsP; exists y; rewrite HQ /=.
    rewrite inE /=; apply/existsP; exists z; by rewrite HR HS.
Qed.

Lemma diagrelE E x y : (x, y) \in diagrel E = (x == y) && (x \in E).
Proof.
  apply/(sameP idP); apply(iffP idP).
  - move=> /andP [] /eqP ->; by apply: mem_imset.
  - move=> /imsetP [] z Hz [] -> ->; by rewrite eq_refl Hz.
Qed.

Lemma stablerelP E R :
  reflect (forall x y, rel_of_set R x y -> x \in E /\ y \in E) (stablerel E R).
Proof.
  apply (iffP idP) => /=.
  - move=> /subsetP H x y; rewrite /rel_of_set => /H.
    by rewrite inE /= => /andP [].
  - move=> H; apply/subsetP => [[x y]] /H [].
    by rewrite inE /= => -> ->.
Qed.

Lemma totalrelP E R : reflect ({in E &, total (rel_of_set R)}) (totalrel E R).
Proof.
  apply (iffP idP) => /=.
  - move/subsetP => H x y Hx Hy.
    have /H : (x, y) \in full E by rewrite inE /= Hx Hy.
    by rewrite !inE /=.
  - move => H; apply/subsetP => [[x y]].
    rewrite inE /= => /andP [] /H{H}H/H{H}.
    by rewrite !inE.
Qed.

Lemma transitiverelP R : reflect (transitive (rel_of_set R)) (transitiverel R).
Proof.
  apply (iffP idP).
  - move=> /subsetP H y x z; rewrite /rel_of_set => Hxy Hyz; apply: H.
    rewrite inE; apply/existsP; exists y => /=.
    by rewrite Hxy Hyz.
  - move=> H; apply/subsetP => [[x z]].
    rewrite !inE /= => /existsP [] y /andP [].
    by apply H.
Qed.

Lemma symmetricrelP R : reflect (symmetric (rel_of_set R)) (symmetricrel R).
Proof.
  apply (iffP idP).
  - move=> /eqP H x y; by rewrite /rel_of_set -{2}H inE.
  - move=> H; apply/eqP; rewrite -setP => [[x y]].
    have:= H x y; by rewrite /rel_of_set inE /= => ->.
Qed.

Lemma antisymmetricrelP R : reflect (antisymmetric (rel_of_set R)) (antisymmetricrel R).
Proof.
  apply (iffP idP).
  - move=> /subsetP H x y /andP []; rewrite /rel_of_set => Rxy Ryx; apply/eqP.
    have {H} := H (x, y); rewrite diagrelE in_setT andbT; apply.
    by rewrite !inE /= Rxy Ryx.
  - move=> H; apply/subsetP => [[x y]].
    rewrite !inE /revrel /= diagrelE => /H ->.
    by rewrite eq_refl in_setT.
Qed.

Lemma isreflexiveP E R : reflect ({in E, reflexive (rel_of_set R)}) (reflexiverel E R).
Proof.
  apply (iffP idP).
  - move=> /subsetP H x Hx; apply: H => /=.
    by apply: mem_imset.
  - move=> H; apply/subsetP => [[x y]] /imsetP [] z Hz [] -> ->.
    by apply: H.
Qed.

Lemma irreflexiverelP E R :
  reflect ({in E, irreflexive (rel_of_set R)}) (irreflexiverel E R).
Proof.
  apply (iffP idP).
  - move/eqP; rewrite -setP => H x Hx.
    have := H (x, x); rewrite !inE.
    apply contraFF; rewrite /rel_of_set => /= -> /=.
    by apply: mem_imset.
  - move=> H; apply/eqP; rewrite -setP => [[x y]]; rewrite !inE diagrelE.
    case: (boolP (x \in E)); last by rewrite !andbF.
    move => /H; apply contraFF; rewrite andbT => /andP [] HR /eqP Heq.
    by rewrite -Heq in HR.
Qed.

Definition equivalence_relset E R :=
  [&& reflexiverel E R, symmetricrel R, transitiverel R & stablerel E R].

Lemma equivalence_relsetP E R :
  let Rel := rel_of_set R in
  reflect [/\ {in E, reflexive Rel},
              symmetric Rel,
              transitive Rel &
              forall x y, Rel x y -> x \in E /\ y \in E
          ] (equivalence_relset E R).
Proof.
  apply (iffP idP) => /=.
  - by move=> /and4P [] /isreflexiveP Hrefl /symmetricrelP Hanti
            /transitiverelP Htrans /stablerelP.
  - move=> [] /isreflexiveP Hrefl /symmetricrelP Hanti
              /transitiverelP Htrans /stablerelP Hstable.
    by apply/and4P.
Qed.

Definition order_relset E R :=
  [&& reflexiverel E R, antisymmetricrel R, transitiverel R & stablerel E R].

Lemma order_relsetP E R :
  let Rel := rel_of_set R in
  reflect [/\ {in E, reflexive Rel},
              antisymmetric Rel,
              transitive Rel &
              forall x y, Rel x y -> x \in E /\ y \in E
          ] (order_relset E R).
Proof.
  apply (iffP idP) => /=.
  - by move=> /and4P [] /isreflexiveP Hrefl /antisymmetricrelP Hanti
            /transitiverelP Htrans /stablerelP.
  - move=> [] /isreflexiveP Hrefl /antisymmetricrelP Hanti
              /transitiverelP Htrans /stablerelP Hstable.
    by apply/and4P.
Qed.

End FiniteRelations.


Section PosetDefs.

Variable T : finType.
Variable E : {set T}.

Record poset := Poset { RelSet : relset T; _ : order_relset E RelSet }.
Canonical poset_subType := Eval hnf in [subType for RelSet].
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

Definition rel_of_poset (P : poset) : rel T := fun x y => (x, y) \in RelSet P.
Coercion rel_of_poset : poset >-> rel.

Definition set_of_poset (P : poset) : {set T} := E.
Coercion set_of_poset : poset >-> set_of.

Variable P : poset.

Lemma poset_orderE : P =2 rel_of_set (RelSet P).
Proof. by []. Qed.

Lemma poset_relsetE x y : P x y = ((x, y) \in (RelSet P)).
Proof. by []. Qed.

Lemma posetE : P =i E.
Proof. by []. Qed.

Definition strict_rel : rel T := [fun x y => (P x y) && (x != y)].

Lemma strict_relW x y : strict_rel x y -> P x y.
Proof. by rewrite /strict_rel /= => /andP []. Qed.

End PosetDefs.


Section PosetTheory.

Variable T : finType.
Variable E : {set T}.
Implicit Type P Q : poset E.

Lemma poset_stable P x y : P x y -> x \in E /\ y \in E.
Proof.
  case: P => rel Hrel; rewrite /rel_of_poset /set_of_poset /= => H.
  move: Hrel => /and4P [] _ _ _ /stablerelP; by apply.
Qed.

Lemma poset_notinL P x y : x \notin E -> P x y = false.
Proof. by apply contraNF => /poset_stable []. Qed.
Lemma poset_notinR P x y : y \notin E -> P x y = false.
Proof. by apply contraNF => /poset_stable []. Qed.

Lemma poset_eqE P Q : P = Q <-> P =2 Q.
Proof.
  split; first by move ->.
  move=> H; apply val_inj; rewrite -setP /= => [[x y]].
  by rewrite -!poset_relsetE.
Qed.

Lemma poset_eq_inE P Q : P = Q <-> {in E &, P =2 Q}.
Proof.
  split; first by move ->.
  move=> H; apply val_inj; rewrite -setP /= => [[x y]].
  rewrite -!poset_relsetE.
  case: (boolP (x \in E)) => HxE.
  - case: (boolP (y \in E)) => HyE; first by apply H.
    case: (boolP (P x y)) => [/poset_stable [] _ Habs| _]; first by rewrite Habs in HyE.
    case: (boolP (Q x y)) => [/poset_stable [] _ Habs|  ]; first by rewrite Habs in HyE.
    by [].
  - case: (boolP (P x y)) => [/poset_stable [] Habs _| _]; first by rewrite Habs in HxE.
    case: (boolP (Q x y)) => [/poset_stable [] Habs _|  ]; first by rewrite Habs in HxE.
    by [].
Qed.

Lemma posetnn P n : n \in P -> P n n.
Proof.
  case: P => rel Hrel; rewrite /rel_of_poset /set_of_poset /=.
  by move: Hrel => /and4P [] /isreflexiveP Hrefl _ _ _ /Hrefl.
Qed.

Lemma anti_poset P m n : P m n -> P n m -> m = n.
Proof.
  case: P => rel Hrel; rewrite /rel_of_poset /set_of_poset /=.
  move: Hrel => /and4P [] _ /antisymmetricrelP Hanti _ _ Hnm Hmn.
  apply Hanti; by rewrite /rel_of_set Hnm Hmn.
Qed.

Lemma poset_trans P : transitive P.
Proof.
  case: P => rel Hrel y x z; rewrite !poset_relsetE /=.
  move: Hrel => /and4P [] _ _ /transitiverelP Htrans _.
  by apply Htrans.
Qed.

Lemma strict_poset_trans P m n p :
  strict_rel P m n -> strict_rel P n p -> strict_rel P m p.
Proof.
  rewrite /strict_rel /= => /andP [] Pmn Heqmn /andP [] Pnp Heqnp.
  apply/andP; split; first by apply: (poset_trans Pmn).
  apply (introN idP) => /eqP Hmp; subst p.
  have Heq := anti_poset Pmn Pnp; subst n.
  by rewrite eq_refl in Heqmn.
Qed.

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

Lemma diagrel_order : order_relset E (diagrel E).
Proof.
  apply/order_relsetP.
  split => [ a | a b | a b c | a b]; rewrite /rel_of_set !diagrelE.
  - move=> ->; by rewrite eq_refl.
  - by move=> /andP [] /andP [] /eqP.
  - by move=> /andP [] /eqP -> ->.
  - by move=> /andP [] /eqP -> ->.
Qed.
Definition triv_poset := Poset diagrel_order.

End TrivOrder.

Section Boolean.

Variable T : finType.

Lemma poset_bool :
  order_relset [set: {set T}] (set_of_rel (fun (A B : {set T}) => A \subset B)).
Proof.
  apply/order_relsetP;
  split => [x Hx | x y | y x z | x y] /=; rewrite !rel_of_setK //=.
  - by rewrite -eqEsubset => /eqP.
  - exact: subset_trans.
Qed.

Definition Bool := Poset poset_bool.

End Boolean.


(******************************************************************************)
(*                                                                            *)
(*                       Constructions on Posets                              *)
(*                                                                            *)
(******************************************************************************)
Section Dual.

Variable T : finType.
Variable E : {set T}.
Implicit Type P : poset E.

Lemma revrel_order P : order_relset E (revrel (RelSet P)).
Proof.
  apply/order_relsetP; rewrite /revrel /=.
  split => [x Hx | x y | x y z | x y] /=; rewrite /rel_of_set !inE /= -!poset_relsetE.
  - exact: posetnn.
  - rewrite andbC => /andP []; exact: anti_poset.
  - move=> Pxy Pzx; apply (poset_trans Pzx Pxy).
  - by move=> /poset_stable [].
Qed.

Definition dual_poset P := Poset (revrel_order P).

Lemma dual_posetE P x y : dual_poset P y x = P x y.
Proof. by rewrite [dual_poset _ _ _]poset_relsetE inE /= -poset_relsetE. Qed.

Lemma dualK : involutive dual_poset.
Proof. move=> P; rewrite poset_eqE => x y; by rewrite !dual_posetE. Qed.

End Dual.


Section Induced.

Variable T : finType.
Variable E F : {set T}.
Hypothesis Hsub : E \subset F.
Implicit Type P : poset F.
Implicit Type Q : poset E.

Definition indrelset P := RelSet P :&: full E.

Lemma indrelsetE P x y :
  rel_of_set (indrelset P) x y = [&& (x \in E), (y \in E) & P x y].
Proof. by rewrite poset_relsetE /rel_of_set !inE /= andbC andbA. Qed.

Lemma induced_order P : order_relset E (indrelset P).
Proof.
  move: Hsub => /subsetP Hin.
  apply/order_relsetP; split => [x Hx | x y | y x z | x y] /=; rewrite !indrelsetE.
  - rewrite Hx /=; apply posetnn; by apply (Hin _ Hx).
  - move=> /andP [] /and3P [] _ _ Pxy /and3P [] _ _ Pyx.
    by apply: anti_poset.
  - move=> /and3P [] -> _ Pxy /and3P [] _ -> Pyz /=.
    by apply (poset_trans Pxy Pyz).
  - by move=> /andP [] -> /andP [] -> _.
Qed.

Definition induced P := Poset (induced_order P).

Lemma inducedE P : {in E &, (induced P) =2 P}.
Proof. move=> x y Hx Hy /=; by rewrite poset_orderE /= indrelsetE Hx Hy /=. Qed.

Lemma inducedP P (S : poset E) : {in E &, S =2 P} <-> S = (induced P).
Proof.
  split; last by move->; exact: inducedE.
  move=> H; rewrite poset_eq_inE => x y Hx Hy.
  rewrite inducedE //; by apply H.
Qed.

Definition rel_expanded Q := diagrel F :|: RelSet Q.
Lemma rel_expanded_order Q : order_relset F (rel_expanded Q).
Proof.
  apply/order_relsetP; rewrite /revrel /=.
  split => [x Hx | x y | y x z | x y] /=;
    rewrite /rel_of_set !inE /= -!poset_relsetE !diagrelE.
  - by rewrite Hx eq_refl.
  - move=> /andP [] /orP [/andP [] /eqP -> //| Qxy].
    move=>          /orP [/andP [] /eqP -> //| Qyx].
    exact: (anti_poset Qxy Qyx).
  - move=> /orP [/andP [] /eqP -> //| Qxy].
    move=> /orP [/andP [] /eqP <- //| Qyz]; first by rewrite Qxy orbT.
    by rewrite (poset_trans Qxy Qyz) orbT.
  - move=> /orP [/andP [] /eqP -> //| Qxy].
    by have := (poset_stable Qxy) => [] [] /(subsetP Hsub) -> /(subsetP Hsub) ->.
Qed.

Definition expanded Q := Poset (rel_expanded_order Q).
Lemma expanded_inE Q : {in E &, Q =2 expanded Q}.
Proof.
  move=> x y Hx Hy /=.
  rewrite [(expanded Q) x y]poset_relsetE !inE !diagrelE -poset_relsetE.
  rewrite (subsetP Hsub _ Hx) andbT.
  case: (altP (x =P y)) => //= <-; rewrite posetnn //.
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

Definition sumrelset := RelSet P :|: RelSet Q :|: [set (e, f) | e in E, f in F].

Lemma sumrelsetE x y :
  rel_of_set sumrelset x y = [|| P x y, Q x y | (x \in E) && (y \in F)].
Proof.
  rewrite poset_relsetE /rel_of_set !inE /= orbA -!poset_relsetE.
  congr (_ || _); by rewrite in_pair.
Qed.

Lemma ExF x : x \in E -> x \in F = false.
Proof.
  move=> HxE; apply (introF idP) => HxF.
  move: Hsub => /disjoint_setI0; rewrite -setP => Habs.
  have:= Habs x; by rewrite !inE HxE HxF.
Qed.
Lemma FxE x : x \in F -> x \in E = false.
Proof. move=> HxF; apply (introF idP) => HxE; by rewrite ExF in HxF. Qed.

Lemma PxE x y : P x y -> x \in E. Proof. by move=> /poset_stable []. Qed.
Lemma PyE x y : P x y -> y \in E. Proof. by move=> /poset_stable []. Qed.
Lemma QxF x y : Q x y -> x \in F. Proof. by move=> /poset_stable []. Qed.
Lemma QyF x y : Q x y -> y \in F. Proof. by move=> /poset_stable []. Qed.

Lemma PxnF x y : x \in E = false -> P x y = false.
Proof. by apply contraFF => /poset_stable []. Qed.
Lemma PnxF x y : x \in E = false -> P y x = false.
Proof. by apply contraFF => /poset_stable []. Qed.
Definition PF x y (H : x \in E = false) := (PxnF y H, PnxF y H).
Lemma QxnF x y : x \in F = false -> Q x y = false.
Proof. by apply contraFF => /poset_stable []. Qed.
Lemma QnxF x y : x \in F = false -> Q y x = false.
Proof. by apply contraFF => /poset_stable []. Qed.
Definition QF x y (H : x \in F = false) := (QxnF y H, QnxF y H).

Definition simplP x y (H : P x y) z :=
  (PxE H, PyE H,
   ExF (PxE H), ExF (PyE H),
   QF z (ExF (PxE H)), QF z (ExF (PyE H)), andbF, orbF).
Definition simplQ x y (H : Q x y) z :=
  (QxF H, QyF H,
   FxE (QxF H), FxE (QyF H),
   PF z (FxE (QxF H)), PF z (FxE (QyF H)), andbF, orbF).

Lemma sum_order : order_relset (E :|: F) sumrelset.
Proof.
  move: Hsub => /disjoint_setI0; rewrite -setP => Habs.
  apply/order_relsetP; split => [x Hx | x y | y x z | x y] /=; rewrite !sumrelsetE.
  - move: Hx; rewrite inE /= => /orP [] /posetnn -> //; by rewrite orbT.
  - move=> /andP [] /or3P [Pxy | Qxy | /andP [] HxE HyF].
    + rewrite !(simplP Pxy) /=; by apply (anti_poset Pxy).
    + rewrite !(simplQ Qxy) /=; by apply (anti_poset Qxy).
    + rewrite (ExF HxE) andbF orbF => /orP [/PxE/ExF|/QyF/FxE]; by rewrite ?HxE ?HyF.
  - move=> /or3P [Pxy | Qxy | /andP [] HxE HyF].
    + rewrite !(simplP Pxy) /= => /orP [|->]; last by rewrite orbT.
      by move /(poset_trans Pxy) ->.
    + rewrite !(simplQ Qxy) /=; by apply poset_trans.
    + rewrite HxE (FxE HyF) !(QF _ (ExF HxE)) !(PF _ (FxE HyF)) /= orbF.
      move=> /poset_stable [] _ ->; by rewrite orbT.
  - move=> /or3P [|| /andP []]; rewrite !inE ?orbT.
    + by move=> /poset_stable [] -> ->.
    + by move=> /poset_stable [] -> ->; rewrite !orbT.
    + by move=> -> ->; rewrite !orbT.
Qed.

Definition sum_poset := Poset sum_order.

Lemma sum_posetP x y :
  reflect ([\/ P x y, Q x y | (x \in E) /\ (y \in F)]) (sum_poset x y).
Proof.
  rewrite [sum_poset x y]poset_orderE sumrelsetE.
  apply (iffP idP).
  - move=> /or3P [->| -> |].
    + by apply Or31. + by apply Or32.
    + move=> /andP [] -> ->; by apply Or33.
  - move=> [-> | -> | [] -> ->]; by rewrite ?orbT /=.
Qed.

Lemma sumLE : {in E &, sum_poset =2 P}.
Proof.
  move=> x y Hx Hy /=; rewrite poset_orderE /= sumrelsetE Hx /=.
  by rewrite (ExF Hy) (QF _ (ExF Hy)) !orbF.
Qed.

Lemma sumPE : {in F &, sum_poset =2 Q}.
Proof.
  move=> x y Hx Hy /=; rewrite poset_orderE /= sumrelsetE Hy /=.
  by rewrite (FxE Hx) (PF _ (FxE Hx)) !orbF.
Qed.

End Sum.


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

Theorem hasmax P x : x \in P -> { m | ismax P m }.
Proof.
  move=> Hx.
  have : #|[set y | P x y]| <= #|[set: T]| by apply subset_leqif_card; apply subsetT.
  case: #|[set: T]| => [| n] H.
    exfalso; move: H; rewrite leqn0 cards_eq0 -subset0 => /subsetP H.
    have {H} := H x; rewrite inE in_set0 => H.
    by have:= H (posetnn Hx).
  elim: n x Hx H => [| n IHn] x Hx H.
  - exists x; split => [| y Hy HP]; first exact Hx.
    have Heq : [set y | P x y] = [set x].
      apply/eqP; rewrite eq_sym eqEcard; apply/andP; split; last by rewrite cards1.
      apply/subsetP => z; rewrite in_set1 inE => /eqP ->; exact: posetnn.
    apply/eqP; by rewrite eq_sym -in_set1 -Heq inE.
  - case (leqP #|[set y | P x y]| n.+1) => [/(IHn x Hx) //| Hcard].
    have {H Hcard} /eqP : #|[set y | P x y]| = n.+2 by apply anti_leq; rewrite H Hcard.
    have Hint : [set y | strict_rel P x y] :&: [set x] = set0.
      rewrite -setP => z; by rewrite !inE /strict_rel /= eq_sym -andbA andNb andbF.
    have <- : [set y | strict_rel P x y] :|: [set x] = [set y | P x y].
      rewrite -setP => z; rewrite !inE /strict_rel /=.
      case (boolP (P x z)) => /=; first by rewrite eq_sym orNb.
      apply contraNF => /eqP ->; exact: posetnn.
    rewrite cardsU Hint {Hint} cards1 cards0 addn1 subn0 eqSS => /eqP Hcard.
    case: (pickP (mem [set y | strict_rel P x y])) => [/= y | Habs].
    + rewrite inE => Hy.
      apply: (IHn y); first by have:= Hy => /strict_relW/poset_stable [] _.
      rewrite -Hcard; apply subset_leqif_card; apply/subsetP => z.
      rewrite !inE; move: Hy; rewrite /strict_rel /= => /andP [] Hxy Hneq Hyz.
      rewrite (poset_trans Hxy Hyz) /=.
      move: Hneq; apply contra => /eqP Hz; apply/eqP; subst x.
      exact: anti_poset.
    + exfalso; have := eq_card Habs; by rewrite Hcard card0.
Qed.

Theorem hasmin P x : x \in P -> { m | ismin P m }.
Proof.
  rewrite posetE -(posetE (dual_poset P)) => /hasmax [] m.
  have:= (min_maxE P m) => [] [] _ H/H{H} Hmin.
  by exists m.
Qed.

End MaxMin.

Section MinMaxRel.

Variable T : finType.
Variable E : {set T}.
Implicit Type P : poset E.

Theorem hasmaxrel P x : x \in P -> { m | ismax P m /\ P x m }.
Proof.
  move=> Hx.
  pose F := [set y | (y \in P) && (P x y)].
  have Hind : F \subset P by apply/subsetP => y; rewrite !inE => /andP [].
  pose PF := induced Hind P.
  have : x \in PF by rewrite inE Hx; exact: posetnn.
  move=> /hasmax [] m [] Hm Hmax; exists m; split.
  - split; first by apply (subsetP Hind).
    move=> y Hy Pmy.
    have HyPF : y \in PF.
      rewrite inE Hy /=; apply: (poset_trans _ Pmy).
      move: Hm; by rewrite inE => /andP [].
    apply Hmax; first exact HyPF.
    by rewrite inducedE //.
  - move: Hm; by rewrite inE => /andP [].
Qed.

Theorem hasminrel P x : x \in P -> { m | ismin P m /\ P m x}.
Proof.
  rewrite posetE -(posetE (dual_poset P)) => /hasmaxrel [] m [].
  have:= (min_maxE P m) => [] [] _ H/H{H} Hmin.
  rewrite dual_posetE => Hxm.
  by exists m.
Qed.

End MinMaxRel.


Section Covers.

Variable T : finType.
Variable E : {set T}.
Variable P Q : poset E.

Definition closed_interv m n := [set x : T | (P m x) && (P x n)].
Definition open_interv m n := [set x : T | (strict_rel P m x) && (strict_rel P x n)].

Definition cover : rel T := fun m n => (strict_rel P m n) && (open_interv m n == set0).

Lemma cover_rel a b : cover a b -> P a b.
Proof. by rewrite /cover /strict_rel /= => /andP [] /andP []. Qed.

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
Implicit Type P Q : poset E.

Definition ext P Q := (RelSet P) \subset (RelSet Q).

Lemma extP P Q : reflect (forall x y : T, P x y -> Q x y) (ext P Q).
Proof.
  rewrite /ext; apply (iffP idP).
  - move=> /subsetP H x y; by apply: H.
  - move=> H; apply/subsetP => [[x y]]; by apply: H.
Qed.

Lemma ext_refl P : ext P P.
Proof. by apply/extP. Qed.

Lemma ext_antisym P Q : ext Q P -> ext P Q -> Q = P.
Proof.
  rewrite /ext => HQP HPQ.
  apply val_inj; apply /eqP; by rewrite eqEsubset /= HQP HPQ.
Qed.

Lemma ext_trans P Q U : ext P Q -> ext Q U -> ext P U.
Proof. rewrite /ext; by apply subset_trans. Qed.

Lemma ext_dual_impl P Q : ext (dual_poset P) (dual_poset Q) -> ext P Q.
Proof.
  move/extP=> H; apply /extP => x y.
  rewrite -dual_posetE => /H; by rewrite dual_posetE.
Qed.

Lemma ext_dualE P Q : ext (dual_poset P) (dual_poset Q) = ext P Q.
Proof.
  apply/(sameP idP); apply(iffP idP); last by apply ext_dual_impl.
  rewrite -{1}(dualK P) -{1}(dualK Q); by apply ext_dual_impl.
Qed.

Lemma ext_triv P : ext (triv_poset E) P.
Proof.
  apply/extP => i j.
  have := diagrelE E i j.
  rewrite !poset_relsetE /= => -> /andP [] /eqP -> Hj.
  by apply posetnn.
Qed.

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
    + by rewrite !(poset_notinR _ x HyE).
    + by rewrite !(poset_notinL _ y HxE).
Qed.

Lemma strict_ext x y : strict_rel P x y -> strict_rel Q x y.
Proof.
  move: HPQ => /extP Hext.
  rewrite /strict_rel /= => /andP [] /Hext Hs ->.
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
  rewrite /cover /strict_rel /= => /andP [] /andP [] _ -> Hopen -> /=.
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
  rewrite poset_orderE indrelsetE => /and3P [] Hx Hy /H.
  by rewrite inducedE.
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
Proof. move: Hcov => /andP []; by rewrite /strict_rel /= => /andP []. Qed.

Definition remcov_rel := set_of_rel (fun m n => (P m n) && ((m, n) != (a, b))).

Lemma remcov_order : order_relset E remcov_rel.
Proof.
  apply/order_relsetP; rewrite /remcov_rel /=.
  split => [x Hx | x y | x y z | x y] /=; rewrite !rel_of_setK.
  - apply/andP; split; first by apply posetnn.
    by move: Neqab; apply contra => /eqP [] <- <-.
  - move=> /andP [] /andP [] Hxy _ /andP [] Hyx _.
    by apply: anti_poset.
  - move=> /andP [] Pxy Hxy /andP [] Pyz Hyz.
    apply/andP; split; first by apply: (poset_trans Pxy Pyz).
    apply (introN idP) => /eqP [] Hy Hz; subst y z.
    move: Hcov => /andP [] _ /eqP; rewrite /open_interv -setP => Iab.
    have := Iab x.
    rewrite in_set0 inE /strict_rel /=.
    rewrite Pxy Pyz /=.
    have -> : x != b by move: Hxy; apply contra => /eqP ->.
    have -> : a != x by move: Hyz; rewrite eq_sym; apply contra => /eqP ->.
    by [].
  - by move=> /andP [] /poset_stable.
Qed.

Definition remcov := Poset remcov_order.

Lemma remcov_ext : ext remcov P.
Proof. apply/extP => x y; by rewrite poset_relsetE inE /= => /andP []. Qed.

Lemma remcov_max_ext Q : ext Q P -> ~~ Q a b -> ext Q remcov.
Proof.
  move=> /extP HQP Hab; apply/extP => x y Hxy.
  rewrite poset_relsetE inE /=.
  apply/andP; split; first by apply HQP.
  move: Hab; by apply contra => /eqP [] <- <-.
Qed.

Lemma remcov_incomp_ab : ~~ (remcov a b || remcov b a).
Proof.
  rewrite !poset_relsetE !inE /=.
  apply/norP; split; apply/nandP.
  + right; by rewrite negbK.
  + left; move: Neqab; apply contra => H.
    apply/eqP. apply: (anti_poset _ H).
    by apply cover_rel.
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

Definition addcov_rel := set_of_rel (fun m n => (P m n) || (P m a && P b n)).

Lemma poset_addcov : order_relset E addcov_rel.
Proof.
  apply/order_relsetP.
  split => [x Hx | x y | x y z | x y] /=; rewrite !rel_of_setK.
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
  - move=> /orP []; first by apply poset_stable.
    by move=> /andP [] /poset_stable [] Hx _ /poset_stable [] _ Hy.
Qed.

Definition addcov := Poset poset_addcov.

Lemma addcov_ext : ext P addcov.
Proof.
  apply/extP => x y /=.
  by rewrite [addcov x y]poset_relsetE inE => -> /=.
Qed.

Lemma addcov_min_ext Q : ext P Q -> Q a b -> ext addcov Q.
Proof.
  move=> /extP HPQ Hab; apply/extP => x y.
  rewrite poset_relsetE inE => /orP [Pxy | /andP [] Pxa Pyb].
  - by apply HPQ.
  - apply (poset_trans (HPQ _ _ Pxa)).
    apply (poset_trans Hab).
    by apply HPQ.
Qed.

Lemma addcov_ab : cover addcov a b.
Proof.
  rewrite /cover/strict_rel /= !poset_relsetE inE /= Neqab !posetnn //= orbT /=.
  rewrite /open_interv -subset0.
  apply/subsetP => i; rewrite in_set0 inE.
  rewrite /strict_rel /= !poset_relsetE !inE !posetnn //= andbT /=.
  move=> /andP [] /andP [] /orP [Pai|Pbi] Hai /andP [] /orP [Pib|Pia] Hib.
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
  - move=> /bigcapP H P /H{H}; by rewrite -poset_relsetE.
  - move=> H; apply/bigcapP => P /H{H}; by rewrite -poset_relsetE.
Qed.

Lemma intrelset_order : order_relset E intrelset.
Proof.
  apply/order_relsetP.
  split => [x Hx | x y | y x z | x y] /=; rewrite /rel_of_set.
  - apply/intrelsetP => Q _; exact: posetnn.
  - move=> /andP [] /intrelsetP Hxy /intrelsetP Hyx.
    move: SPn0 => /set0Pn [] P HP.
    exact: (anti_poset (Hxy _ HP) (Hyx _ HP)).
  - move=> /intrelsetP Hxy /intrelsetP Hyz.
    apply/intrelsetP => P HP.
    exact: (poset_trans (Hxy _ HP) (Hyz _ HP)).
  - move=> /intrelsetP Hxy.
    move: SPn0 => /set0Pn [] P /Hxy.
    exact: poset_stable.
Qed.

Definition intposet := Poset intrelset_order.

Lemma intposetP x y :
  reflect (forall P : poset E, P \in SP -> P x y) (intposet x y).
Proof. rewrite poset_relsetE /=; by apply intrelsetP. Qed.

Lemma intposet_meet P :
  (forall Q : poset E, Q \in SP -> ext P Q) -> ext P intposet.
Proof.
  move=> H; apply/extP => x y Pxy.
  apply/intposetP => Q /H /extP; by apply.
Qed.

End Intersect.


Section ExtPoset.

Variable T : finType.
Variable E : {set T}.
Implicit Type P : poset E.

Lemma ext_order :
  order_relset [set: poset E] (set_of_rel (fun (A B : poset E) => ext A B)).
Proof.
  apply/order_relsetP;
  split => [x Hx | x y | y x z | x y] /=; rewrite !rel_of_setK //=.
  - exact: ext_refl.
  - move=> /andP []; exact: ext_antisym.
  - exact: ext_trans.
Qed.

Definition ExtPoset := Poset ext_order.

Lemma max_extP P : (ismax ExtPoset P) <-> {in E &, total P}.
Proof.
  split.
  - move=> /predmaxP H; apply/totalrelP; move: H; apply contraLR => /subsetPn [[x y]].
    rewrite !inE -!poset_relsetE /= => /andP [] Hx Hy Hinc.
    rewrite negb_and inE //= negb_forall; apply/existsP.
    exists (addcov Hinc); apply/implyP; rewrite inE /= => /implyP.
    rewrite poset_relsetE inE /= => H.
    have {H} /eqP := (H (addcov_ext Hinc)); rewrite poset_eqE => H.
    have:= H x y.
    have:= Hinc; rewrite negb_or => /andP [] /negbTE -> _.
    have:= addcov_ab Hx Hy Hinc; by rewrite /cover => /andP [] /strict_relW ->.
  - move=> H; split; first by rewrite inE.
    move=> Q _; rewrite poset_relsetE inE /= => Hext.
    exact: ext_total.
Qed.

Definition linext P L := ext P L && (totalrel E (RelSet L)).

Lemma linextP P L : reflect (ext P L /\ {in E &, total L}) (linext P L).
Proof.
  rewrite /linext; apply (iffP idP).
  - move=> /andP [] -> /totalrelP Htot; split; first by [].
    move=> x y /= /Htot{Htot} H/H{H}.
    by rewrite !poset_orderE.
  - by move=> [] -> /= /totalrelP.
Qed.

Theorem exists_linext P : { L : poset E | linext P L }.
Proof.
  have /hasmaxrel : P \in ExtPoset by rewrite inE.
  move=> [] L [] /max_extP; rewrite !poset_relsetE inE /= => Htot Hext.
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
    have:= poset_stable Habs => [] [] Hx Hy.
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

Theorem convex_extlin_extend (L : poset E) :
  linext (induced Hsub P) L ->
  { M : poset F | [/\ induced Hsub M = L, linext P M & convex M E] }.
Proof.
  move=> Hlin.
  have := exists_linext (induced SupF P) => [] [] LSup LSupP.
  have := exists_linext (induced InfF P) => [] [] LInf LInfP.
  pose LESup := sum_poset disjoint_E_Sup L LSup.
  pose Mtmp := sum_poset disjoint_Inf_ESup LInf LESup.
  have /eqP := HeqF; rewrite eqEsubset => /andP [] _ HFsubu.
  move HM : (induced HFsubu Mtmp) => M.
  pose MRel x y := [|| LInf x y, L x y, LSup x y,
                    (x \in E) && (y \in Sup)
                   | (x \in Inf) && ((y \in E) || (y \in Sup))].

  have MRelF x y : MRel x y = [&& x \in F, y \in F & MRel x y].
    case (boolP (MRel x y)); last by rewrite !andbF.
    rewrite /MRel => /or4P [|||/orP[]].
    - by move/poset_stable=> [] /(subsetP InfF) -> /(subsetP InfF) ->.
    - by move/poset_stable=> [] /(subsetP Hsub) -> /(subsetP Hsub) ->.
    - by move/poset_stable=> [] /(subsetP SupF) -> /(subsetP SupF) ->.
    - by move=> /andP [] /(subsetP Hsub) -> /(subsetP SupF) ->.
    - by move=> /andP [] /(subsetP InfF) -> /orP [/(subsetP Hsub) ->|/(subsetP SupF) ->].
  have {MRelF} MP : M =2 MRel.
    move=> x y; rewrite poset_orderE -HM /= indrelsetE MRelF /MRel.
    by rewrite poset_orderE sumrelsetE [LESup _ _]poset_orderE sumrelsetE !orbA in_setU.
  rewrite /MRel {MRel HM Mtmp LESup HFsubu} in MP.
  exists M; split.
  - rewrite poset_eq_inE => x y Hx Hy.
    rewrite inducedE // MP.
    have HySup := ExF disjoint_E_Sup Hy; rewrite HySup (QF _ _ HySup) !orbF {HySup}.
    have:= disjoint_Inf_ESup; rewrite disjoints_subset setCU => H1.
    have HxInf := FxE disjoint_Inf_E Hx; by rewrite HxInf (QF _ _ HxInf) /= andbF !orbF.
  - apply/linextP; split.
    apply/extP => x y Pxy; have:= poset_stable Pxy => [] [] /FuP/or3P [] Hx.
    + move=> /FuP/orP [Hy|].
      * suff: LInf x y by rewrite MP => ->.
        move: LInfP => /linextP [] /extP Hext _; apply Hext => {Hext}.
        by rewrite inducedE.
      * move=> /orP [] Hy; by rewrite MP Hx Hy /= !orbT.
    + move=> /FuP/or3P [] Hy.
      * exfalso; move: Hy; rewrite inE => /andP []; rewrite inE negb_or => /andP [] H1 H2 _.
        move: H2; rewrite inE negb_and inE negb_and H1 /=.
        have := poset_stable Pxy => [] [] _ -> /=.
        rewrite negb_exists => /forallP H.
        have:= H x; by rewrite Hx Pxy.
      * suff: L x y by rewrite MP => ->; rewrite orbT.
        move: Hlin => /linextP [] /extP Hext _; apply Hext => {Hext}.
        by rewrite inducedE.
      * by rewrite MP Hx Hy /= !orbT.
    + move=> /FuP/or3P [] Hy.
      * exfalso.
        move: Hy Hx; rewrite !inE negb_or => /andP [] /andP [] Hy; rewrite Hy /=.
        have:= poset_stable Pxy => [] [] -> ->; rewrite !andbT /=.
        rewrite negb_exists => /forallP H _ /andP [] Hx /existsP [] z /andP [] Hz Pzx.
        have:= H z; by rewrite Hz /= (poset_trans Pzx Pxy).
      * exfalso.
        move: Hy Hx; rewrite !inE => Hy /andP [] /andP [] HxE HxF.
        move=> /existsP [] z /andP [] Hz Pzx.
        move: Hconv => /convexP HconvP.
        by rewrite (HconvP _ _ _ Hz Hy Pzx Pxy) in HxE.
      * suff: LSup x y by rewrite MP => ->; rewrite !orbT.
        move: LSupP => /linextP [] /extP Hext _; apply Hext => {Hext}.
        by rewrite inducedE.
  - move=> x y /=.
    rewrite !MP => /FuP/or3P [] Hx /FuP/or3P [] Hy; try by rewrite Hx Hy /= !orbT /=.
    * move: LInfP => /linextP [] _ Htot.
      have := Htot _ _ Hx Hy => /orP [] ->; by rewrite /= ?orbT.
    * move: Hlin => /linextP [] _ Htot.
      have := Htot _ _ Hx Hy => /orP [] ->; by rewrite /= ?orbT.
    * move: LSupP => /linextP [] _ Htot.
      have := Htot _ _ Hx Hy => /orP [] ->; by rewrite /= ?orbT.
  - apply/convexP => x y z Hx Hz.
    rewrite !MP Hx Hz.
    have HxInf := FxE disjoint_Inf_E Hx; rewrite HxInf (QF _ _ HxInf) /= ?andbT ?orbF.
    have HxSup := ExF disjoint_E_Sup Hx; rewrite (QF _ _ HxSup) /= ?andbT ?orbF.
    have HzInf := FxE disjoint_Inf_E Hz; rewrite (QF _ _ HzInf) /= ?andbT ?orbF.
    have HzSup := ExF disjoint_E_Sup Hz; rewrite HzSup (QF _ _ HzSup) andbF /= ?andbT ?orbF.
    move {HxInf HxSup HzInf HzSup} => /orP [Lxy _| Supy /orP [Lyz|Infy]].
    + by have := poset_stable Lxy => [] [].
    + by have := poset_stable Lyz => [] [].
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

Definition rel_of_seq s := [fun x y => [&& x \in E, y \in E & (mem2 s x y)]].

Lemma rel_of_seq_order s :
  perm_eq s (enum E) -> order_relset E (set_of_rel (rel_of_seq s)).
Proof.
  move=> Hperm; apply/order_relsetP.
  have Huniq : uniq s by rewrite (perm_eq_uniq Hperm); apply enum_uniq.
  have Hin : E =i s by move => x; rewrite (perm_eq_mem Hperm) mem_enum.
  split => [x Hx | x y | y x z | x y] /=; rewrite !rel_of_setK //=.
  - rewrite Hx /=. move: Hx; rewrite Hin.
    elim: s {Hperm Huniq Hin} => [| s0 s IHs] //=.
    rewrite /mem2 in_cons /= eq_sym.
    case: (altP (s0 =P x)) => [-> _ |_] /=; first by rewrite in_cons eq_refl.
    by apply IHs.
  - move=> /and4P [] /and3P []; rewrite !Hin => Hx Hy.
    move=> /(mem2_index Huniq) Hxy _ _ /(mem2_index Huniq) Hyx.
    have {Hxy Hyx} Heq : index x s = index y s by apply anti_leq; rewrite Hxy Hyx.
    by rewrite -(nth_index x Hx) Heq (nth_index _ Hy).
  - rewrite !Hin => /and3P [] Hx Hy /(mem2_index Huniq) Hxy.
    move=> /and3P [] _ Hz /(mem2_index Huniq) Hyz.
    rewrite Hx Hz /=; apply (index_mem2 Hz).
    by apply (leq_trans Hxy Hyz).
  - by move=> /and3P [].
Qed.

Definition poset_of_seq s (Hperm : perm_eq s (enum E)) := Poset (rel_of_seq_order Hperm).

Lemma poset_of_seq_total s (Hperm : perm_eq s (enum E)) :
  {in E &, total (poset_of_seq Hperm)}.
Proof.
  move=> x y Hx Hy /=.
  rewrite !poset_relsetE !inE /= Hx Hy /=.
  have Huniq : uniq s by rewrite (perm_eq_uniq Hperm); apply enum_uniq.
  have := Hy; have := Hx.
  rewrite -mem_enum -[y \in _]mem_enum -!(perm_eq_mem Hperm) => Hxs Hyx.
  rewrite !mem2_indexE //; by apply leq_total.
Qed.

Section PosetOfSeq.

Variable P : poset E.
Hypothesis HtotP : {in E &, total P}.

Definition expposet_of_seq :=
  let: exist L _ := exists_linext (expanded (subsetT E) P) in L.

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
  rewrite poset_relsetE inE /=.
  have:= poset_stable Pxy => [] [] Hx Hy; rewrite Hx Hy /=.
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
    rewrite (eq_path (poset_orderE _)) /= (eq_path (rel_of_setK _)) {Hperm}.
    elim: s s0 Huniq Hall => [//=| s1 s IHs] s0 Huniq /andP [] Hs0 Hall /=.
    have:= Hall => /= /andP [] -> _; rewrite Hs0 /=.
    apply/andP; split; first by rewrite /mem2 /= eq_refl !in_cons eq_refl orbT.
    have {IHs} /IHs Hrec : uniq (s1 :: s) by move: Huniq => /= /andP [].
    have {Hrec Hall} Hpath := Hrec Hall.
    rewrite (eq_in_path (e' := (fun x : T => rel_of_seq (s1 :: s) x))) //.
    move=> x y Hx Hy /=; congr [&& _, _ & _].
    rewrite !mem2_indexE //=; first last.
    + move: Hy; rewrite !in_cons => ->; by rewrite orbT.
    + by move: Huniq => /= /andP [].
    case: (altP (s0 =P x)) => [Habs| _].
      exfalso; subst s0; by move: Hx Huniq => /= ->.
    case: (altP (s0 =P y)) => [Habs| _].
      exfalso; subst s0; by move: Hy Huniq => /= ->.
    by rewrite ltnS.
  - apply (perm_eq_trans (perm_seq_of_poset _)); by rewrite perm_eq_sym.
Qed.

Record linposet := LinPoset { POS :> poset E; _ : totalrel E (RelSet POS) }.
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
  LinPoset
    (introT (totalrelP E (RelSet (poset_of_seq Hperm)))
            (poset_of_seq_total Hperm) ).

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
    by rewrite poset_relsetE inE /= => /and3P [].
  - move=> /seqextP /= Hall; apply/linextP; split; last exact: poset_of_seq_total.
    apply/extP => x y Pxy; rewrite poset_relsetE /= inE /=.
    have:= poset_stable Pxy => [] [] -> -> /=; by apply Hall.
Qed.

Lemma linext_seqext P (L : linposet) : linext P L = seqext P (permseq_of_linposet L).
Proof.
  have := linposet_of_permseq_bij => [] [] inv _ H.
  by rewrite -{1}[L]linposet_of_permseqK -seqext_linext.
Qed.

End SeqExt.

End LinearPoset.


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



(* Unused *)
Section SizeRel.

Variable T : finType.
Variable E : {set T}.
Implicit Type R S : poset E.

Lemma card_poset R : #|R| = #|E|.
Proof. by apply eq_card. Qed.

Definition cardcmp := [fun R : poset E => #|RelSet R|].

Lemma card_triv : cardcmp (triv_poset E) = #|E|.
Proof.
  rewrite /= (eq_card (B := pred_of_set (diagrel E))) //.
  by rewrite /diagrel card_imset // => x y [].
Qed.

Lemma cardcmp_extE R S : cardcmp R = cardcmp S -> ext R S -> R = S.
Proof.
  case: R => [R HR]; rewrite /= (eq_card (B := pred_of_set R)) //.
  case: S => [S HS]; rewrite /= [X in _ = X](eq_card (B := pred_of_set S)) // => Hcard.
  rewrite /ext /= => Hext; apply val_inj => /=.
  apply/eqP; by rewrite eqEcard Hext Hcard leqnn.
Qed.

Lemma triv_cart R : cardcmp R = #|E| -> R = triv_poset E.
Proof.
  move => H; apply esym; apply cardcmp_extE.
  - by rewrite card_triv H.
  - by apply ext_triv.
Qed.

Lemma card_remcov a b R (H : cover R a b) : (cardcmp (remcov H)).+1 = cardcmp R.
Proof.
  rewrite /remcov -addn1 -(cards1 (a, b)) /=.
  rewrite (eq_card (B := pred_of_set (remcov_rel R a b))) // -cardsUI.
  rewrite (eq_card (B := pred_of_set (RelSet R))); first last.
    move=> [x y]; rewrite /remcov_rel /= !inE /=.
    case: (altP ((x,y) =P (a, b))) => [-> |] //=; last by rewrite andbT orbF.
    by rewrite orbT -poset_relsetE (cover_rel H).
  suff -> : remcov_rel R a b :&: [set (a, b)] = set0 by rewrite cards0.
  rewrite -setP => [[x y]]; rewrite !inE /=.
  by rewrite -andbA andNb andbF.
Qed.

Lemma card_addcov a b R (H : ~~ (R a b || R b a)) :
  a \in E -> b \in E -> cardcmp R < cardcmp (addcov H).
Proof.
  move => Ha Hb; rewrite /addcov -addn1 -(cards1 (a, b)) /=.
  rewrite -cardsUI.
  rewrite [X in _ + X](eq_card (B := pred0)); first last.
    move=> [x y]; rewrite !inE andbC; apply (introF idP) => /andP [] /eqP ->.
    rewrite -poset_relsetE => Habs.
    by rewrite Habs /= in H.
  rewrite card0 addn0; apply subset_leqif_cards; apply/subsetP => [[x y]].
  rewrite !inE /= -poset_relsetE => /orP [-> //| /eqP [] -> ->].
  by rewrite !posetnn //= orbT.
Qed.

Lemma cardcmp_full R : cardcmp R <= #|full E|.
Proof.
  rewrite [cardcmp R]/=; apply subset_leqif_cards.
  case: R => rel Hrel; rewrite [RelSet _]/=.
  move: Hrel; by rewrite /order_relset /stablerel => /and4P [].
Qed.

Lemma card_full : #|full E| = #|E| * #|E|.
Proof.
  pose P := [set [set (x, y) | x in E] | y in E].
  have Hpart : partition P (full E).
    rewrite /partition; apply/and3P; split.
    - rewrite eqEsubset; apply/andP; split.
      + apply/subsetP => [[x y]] /bigcupP [] S /imsetP [] a Ha -> {S} /imsetP [] b Hb ->.
        by rewrite !inE /= Ha Hb.
      + apply/subsetP => [[x y]]; rewrite inE /= => /andP [] Hx Hy.
        apply/bigcupP; exists [set (a, y) | a in E]; apply/imsetP; first by exists y.
        by exists x.
    - apply/trivIsetP => A B /imsetP [] a Ha -> /imsetP [] b Hb -> {A B} Hneq.
      have {Hneq} Hneq : a != b by move: Hneq; apply contra => /eqP ->.
      rewrite -setI_eq0; apply/eqP; rewrite -setP => [[x y]].
      rewrite !inE; move: Hneq. apply contraNF => /andP [].
      by move=> /imsetP [] u _ [] -> -> /imsetP [] v _ [] _ ->.
    - apply (introN idP) => /imsetP [] x Hx.
      rewrite -setP => H.
      have := H (x, x); rewrite !inE.
      suff -> : ((x, x) \in [set (x0, x) | x0 in E]) by [].
      apply/imsetP; by exists x.
  rewrite (card_uniform_partition _ Hpart (n := #|E|)).
  - rewrite card_in_imset // => i j Hi _.
    rewrite -setP => H; have {H} := H (i, i).
    have -> : ((i, i) \in [set (x, i) | x in E]) by apply/imsetP; exists i.
    by move=> /esym/imsetP [] x _ [].
  - move=> S /imsetP [] x Hx -> {S}.
    by apply card_imset => i j [].
Qed.

End SizeRel.
