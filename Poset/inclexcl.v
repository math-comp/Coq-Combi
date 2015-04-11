(******************************************************************************)
(*       Copyright (C) 2015 Florent Hivert <florent.hivert@lri.fr>            *)
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
Require Import path finset finfun fingraph tuple bigop ssrint ssralg.

Require Import poset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Reserved Notation "''Ind_' P"     (at level 8, P at level 2, format "''Ind_' P").
Reserved Notation "''Ind[' R ]_ P"     (at level 8).

(* Reserved Notation "[ 'ind[' k ']' i j : P => E ]"
  (at level 36, E at level 36, i, j at level 50).
Reserved Notation "[ 'ind' i j => E ]"
  (at level 36, E at level 36, i, j at level 50, format "[ 'ind' i j => E ]").
*)

Section Interval.

Variable T : finType.
Variable E : {set T}.
Variable P : poset E.

Record interval := Interval { Inter :> T * T; _ : Inter \in RelSet P }.
Canonical interval_subType := Eval hnf in [subType for Inter].
Definition interval_eqMixin := Eval hnf in [eqMixin of interval by <:].
Canonical interval_eqType := Eval hnf in EqType interval interval_eqMixin.
Definition interval_choiceMixin := Eval hnf in [choiceMixin of interval by <:].
Canonical interval_choiceType := Eval hnf in ChoiceType interval interval_choiceMixin.
Definition interval_countMixin := Eval hnf in [countMixin of interval by <:].
Canonical interval_countType := Eval hnf in CountType interval interval_countMixin.
Canonical interval_subCountType := Eval hnf in [subCountType of interval].
Definition interval_finMixin := Eval hnf in [finMixin of interval by <:].
Canonical interval_finType := Eval hnf in  FinType interval interval_finMixin.
Canonical interval_subFinType := Eval hnf in [subFinType of interval].

End Interval.

(* Also called the incidence algebra *)
Section IncidenceFunction.

Variable R : Type.
Variable T : finType.
Variable E : {set T}.
Variable P : poset E.

Inductive incidType : predArgType := Incid of {ffun interval P -> R}.

Definition incidType_of of phant (interval P -> R) := incidType.

Identity Coercion type_of_finfun : incidType_of >-> incidType.

Definition incid_val A := let: Incid g := A in g.
Canonical incid_subType := Eval hnf in [newType for incid_val].

End IncidenceFunction.

Notation "''Ind[' R ]_ P" := (incidType R P) (only parsing) : type_scope.

Notation "{ 'ind' P '=>' R }" := (incidType_of (Phant (interval P -> R)))
  (at level 0, format "{ 'ind' P '=>' R }") : type_scope.

Section Bla.

Variable R : Type.
Variable T : finType.
Variable E : {set T}.
Variable P : poset E.

Fact incid_key : unit. Proof. by []. Qed.
Definition incid_of_fun_def F : 'Ind[R]_P := Incid [ffun ij : (interval P) => F ij.1 ij.2].
Definition incid_of_fun k := locked_with k incid_of_fun_def.
Canonical incid_unlockable k := [unlockable fun incid_of_fun k].

End Bla.


Bind Scope ring_scope with incidType.

Notation "''Ind[' R ]_ P" := (incidType R P) (only parsing) : type_scope.
Notation "''Ind_' P" := 'Ind[_]_P : type_scope.

Notation "[ 'ind[' k ']' i j : P => E ]" := (@incid_of_fun _ _ _ P k (fun i j => E))
  (at level 36, E at level 36, i ident, j ident): ring_scope.

Notation "[ 'ind' i j : P => E ]" := (@incid_of_fun _ _ _ P incid_key (fun i j => E))
  (at level 36, E at level 36, i ident, j ident, only parsing) : ring_scope.

Section Defs.

Variable T : finType.
Variable E : {set T}.
Variable P : poset E.

Definition incid_eqMixin (R : eqType) := Eval hnf in [eqMixin of 'Ind[R]_P by <:].
Canonical incid_eqType (R : eqType) := Eval hnf in EqType 'Ind[R]_P (incid_eqMixin R).
Definition incid_choiceMixin (R : choiceType) := [choiceMixin of 'Ind[R]_P by <:].
Canonical incid_choiceType (R : choiceType) :=
  Eval hnf in ChoiceType 'Ind[R]_P (incid_choiceMixin R).
Definition incid_countMixin (R : countType) := [countMixin of 'Ind[R]_P by <:].
Canonical incid_countType (R : countType):=
  Eval hnf in CountType 'Ind[R]_P (incid_countMixin R).
Canonical incid_subCountType (R : countType) := Eval hnf in [subCountType of 'Ind[R]_P].
Definition incid_finMixin (R : finType) := [finMixin of 'Ind[R]_P by <:].
Canonical incid_finType (R : finType) := Eval hnf in FinType 'Ind[R]_P (incid_finMixin R).
Canonical incid_subFinType (R : finType) := Eval hnf in [subFinType of 'Ind[R]_P].

Section IncidenceStructural.

Variable R : Type.

(* Constant incidence *)
Fact const_incid_key : unit. Proof. by []. Qed.
Definition const_incid P a : 'Ind[R]_P := \ind[const_mx_key]_P ( i, j ) a.
Implicit Arguments const_incid [P].


Definition fun_of_incid (A : incidType) (i : T) (j : T) : R :=
  if boolP ((i, j) \in RelSet P) is AltTrue Prf then incid_val A (Interval Prf) else 0%R.

Coercion fun_of_incid : incidType >-> Funclass.

Lemma incidE k F i j : P i j -> incid_of_fun k F i j = F i j.
Proof.
  rewrite unlock /fun_of_incid /rel_of_finrel.
  case (boolP ((i, j) \in RelSet P)) => //= Prf _.
  by rewrite ffunE /=.
Qed.


Definition const1 := finfun 
Definition delta x y : R := if diagrel E x y then 1 else 0.

Import GRing.
Open Scope ring_scope.



(* Also called the incidence algebra *)
Section IncidenceAlgebra.

Variable T : finType.
Variable R : ringType.
Variable E : {set T}.
Variable P : poset E.

Definition supported (f : T -> T -> R) := [forall x, forall y, (~~ P x y) ==> (f x y == 0)].
Lemma supportedP (f : T -> T -> R) :
  reflect (forall x y, ~~ P x y -> f x y = 0) (supported f).
Proof.
  apply (iffP idP).
  - move=> /forallP H x y Hxy; apply/eqP; by apply (implyP (forallP (H x) y)).
  - move=> H; apply/forallP => x; apply/forallP => y; apply/implyP => nPxy.
    apply/eqP; exact: H.
Qed.

Definition convol (f g : T -> T -> R) x y :=
  \sum_(z : T | P x z && P z y) (f x z) * (g z y).

Notation "f \* g" := (convol f g) (at level 50, format "f  \* '/ '  g").

Definition delta x y : R := if diagrel E x y then 1 else 0.
Lemma delta_supported : supported delta.
Proof.
  apply/supportedP => x y; rewrite /delta diagrelE.
  case: (boolP (x \in E)) => [H|] //=.
  by case: (altP (x =P y)) => [<- | Hxy]; first by rewrite posetnn.
Qed.

Lemma supported_conv f g : supported (f \* g).
Proof.
  apply/supportedP => x y nPxy; rewrite /convol /=.
  rewrite (eq_bigl pred0); first by rewrite big_pred0.
  move=> z /=; apply (introF idP) => /andP [] /poset_trans TR/TR{TR} Pxy.
  move: nPxy; by rewrite Pxy.
Qed.

Lemma convd1 f : supported f -> delta \* f =2 f.
Proof.
  move=> /supportedP Hf x y; case: (boolP (P x y)) => Pxy; first last.
    by rewrite (Hf _ _ Pxy) (supportedP _ (supported_conv _ _) _ _ Pxy).
  rewrite /convol (bigID (pred1 x)) /=.
  set S := (X in X + _); have {S} -> : S = f x y.
    rewrite /S{S} (eq_bigl (pred1 x)); first last.
      move=> i /=; case (altP (i =P x)) => [->|]; last by rewrite andbF.
      rewrite Pxy; by have:= stablerelP Pxy => [] [] /posetnn ->.
    rewrite big_pred1_eq /delta diagrelE eq_refl.
    have:= stablerelP Pxy => [] [] -> _ /=; by rewrite mul1r.
  set S := (X in _ + X); suff -> : S = 0 by rewrite addr0.
  rewrite /S{S} (eq_bigr (fun x => 0)); first last.
    move=> z /andP [] Pyx /negbTE Hneq; by rewrite /delta diagrelE eq_sym Hneq andbF mul0r.
  by rewrite sumr_const mul0rn.
Qed.

Lemma conv1d f : supported f -> f \* delta =2 f.
Proof.
  move=> /supportedP Hf x y; case: (boolP (P x y)) => Pxy; first last.
    by rewrite (Hf _ _ Pxy) (supportedP _ (supported_conv _ _) _ _ Pxy).
  rewrite /convol (bigID (pred1 y)) /=.
  set S := (X in X + _); have {S} -> : S = f x y.
    rewrite /S{S} (eq_bigl (pred1 y)); first last.
      move=> i /=; case (altP (i =P y)) => [->|]; last by rewrite andbF.
      rewrite Pxy; by have:= stablerelP Pxy => [] [] _ /posetnn ->.
    rewrite big_pred1_eq /delta diagrelE eq_refl.
    have:= stablerelP Pxy => [] [] _ -> /=; by rewrite mulr1.
  set S := (X in _ + X); suff -> : S = 0 by rewrite addr0.
  rewrite /S{S} (eq_bigr (fun x => 0)); first last.
    move=> z /andP [] Pyx /negbTE Hneq; by rewrite /delta diagrelE Hneq andbF mulr0.
  by rewrite sumr_const mul0rn.
Qed.

Definition convolA f g h : (f \* g) \* h =2 f \* (g \* h).
Proof.
  move=> x y; rewrite /convol/=.
  rewrite [LHS](eq_bigr (fun z => \sum_(z0 | P x z0 && P z0 z) f x z0 * g z0 z * h z y));
    last by move=> z _; rewrite mulr_suml.
  rewrite [RHS](eq_bigr (fun z => \sum_(z0 | P z z0 && P z0 y) f x z * g z z0 * h z0 y));
    first last.
    move=> z _; rewrite mulr_sumr; apply eq_bigr => t _; by rewrite mulrA.
  rewrite !pair_big_dep /=.
  rewrite (reindex (fun p => (p.2, p.1))) /=; first last.
    apply onW_bij; by apply inv_bij => [[u v]].
  apply eq_bigl => [[a b]] /=.
  case: (boolP (P x a)) => [Pxa |]/=; last by rewrite !andbF.
  case: (boolP (P a b)) => [Pab |]/=; last by rewrite !andbF.
  case: (boolP (P b y)) => [Pby |]/=; last by rewrite !andbF.
  by rewrite (poset_trans Pxa Pab) (poset_trans Pab Pby).
Qed.

(* This is an instance of the classical fact that in a monoid *)
(* right and left inverse are equal                           *)
Lemma convinvlr f g h :
  supported f -> supported h -> f \* g =2 delta -> g \* h =2 delta -> f =2 h.
Proof.
  move=> Hf Hh Hfg Hgh x y.
  have := eq_refl (((f \* g) \* h) x y).
  rewrite {1}convolA {1 3}/convol.
  rewrite (eq_bigr (fun z => f x z * delta z y)); last by move=> z _; rewrite Hgh.
  have:= conv1d Hf x y; rewrite {1}/convol => ->.
  rewrite (eq_bigr (fun z => delta x z * h z y)); last by move=> z _; rewrite Hfg.
  have:= convd1 Hh x y; by rewrite {1}/convol => -> /eqP.
Qed.

End IncidenceAlgebra.

Section InclusionExclusion.

Variable T : finType.
Variable R : ringType.
Variable E : {set T}.
Variable P : poset E.

Lemma sum_interval (M : T -> T -> R) x y :
  P x y ->
  \sum_(z : T | P x z && P z y) M x z
  = M x y + \sum_(z : T | P x z && strict P z y) M x z.
Proof.
  move=> Pxy.
  rewrite (bigID (pred1 y)) /=.
  rewrite (eq_bigl (pred1 y)); first last.
    move=> z /=; case (altP (z =P y)) => [->|]; last by rewrite andbF.
    by rewrite Pxy; have:= stablerelP Pxy => [] [] _ /posetnn ->.
  rewrite big_pred1_eq.
  rewrite (eq_bigl (fun z => P x z && strict P z y)); first by [].
  by move=> z /=; rewrite /strict /= andbA.
Qed.


CoInductive moebius_fun (M : T -> T -> R) : Prop :=
  Moebius_Fun :
    (forall x, x \in E -> M x x = 1) ->
    (forall x y, x \in E -> ~~ P x y -> M x y = 0) ->
    (forall x y, strict P x y -> \sum_(z : T | P x z && P z y) M x z = 0) -> moebius_fun M.

Variable M : T -> T -> R.
Hypothesis HM : moebius_fun M.
Variable f g : T -> R.
Hypothesis Hfg : forall x : T, f x = \sum_(y : T | P x y) g y.

Theorem poset_incl_excl x : x \in E -> g x = \sum_(y : T| P x y) (M x y) * (f y).
Proof.
  move: HM x => [] HMfix HMnP HMinter x Hx.
  rewrite (eq_bigr (fun y => \sum_(z | P y z) (M x y) * (g z))); first last.
    move=> y Hy; rewrite (Hfg y); by rewrite GRing.mulr_sumr.
  rewrite (exchange_big_dep (P x)) /=; last by move=> y z; apply: poset_trans.
  rewrite (bigID (pred1 x)) /=.
  set S := (X in X + _); have {S} -> : S = g x.
    rewrite /S{S} (eq_bigl (pred1 x)); first last.
      move=> i /=; case (altP (i =P x)) => [->|]; last by rewrite andbF.
      by rewrite posetnn.
    rewrite big_pred1_eq (eq_bigl (pred1 x)); first last.
      move=> i /=; apply (sameP idP); apply (iffP idP) => [/eqP ->|].
      - by rewrite posetnn.
      - move=> /andP [] Hxi Hix; apply/eqP.
        exact: (anti_poset Hix Hxi).
    by rewrite big_pred1_eq (HMfix x Hx) mul1r.
  set S := (X in _ + X); suff -> : S = 0 by rewrite addr0.
  rewrite /S{S} (eq_bigr (fun x => 0)); first last.
    move=> y /andP [] Pyx Hneq.
    rewrite -mulr_suml HMinter; last by rewrite /strict /= Pyx eq_sym Hneq.
    by rewrite mul0r.
  by rewrite sumr_const mul0rn.
Qed.

End InclusionExclusion.


(*
Section Dual.

Variable T : finType.
Variable R : ringType.
Variable E : {set T}.
Variable P : poset E.

Lemma moebius_fun_dual (M : T -> T -> R) :
  moebius_fun P M -> moebius_fun (dual_poset P) (fun x y => M y x).
Proof.
  move=> [] Mfix MnP Minter; constructor => //.
  - move=> x y; rewrite dual_posetE; apply MnP.
  - move=> x y; rewrite strict_dualE.
    rewrite (eq_bigl (fun z => P y z && P z x)); first last.
      move=> z /=; by rewrite !revrelE andbC.
    move=> /Minter.
*)

Section Unicity.

Variable T : finType.
Variable R : ringType.
Variable E : {set T}.
Variable P : poset E.

Theorem moebius_fun_uniq (M1 M2 : T -> T -> R) :
  moebius_fun P M1 -> moebius_fun P M2 -> {in E, M1 =2 M2}.
Proof.
  move=> [] Mfix1 MnP1 Minter1 [] Mfix2 MnP2 Minter2 x Hx.
  apply: (well_founded_ind (strict_Wf P)) => y IHy.
  case: (altP (x =P y)) => [<- | Hneq]; first by rewrite Mfix1 // Mfix2.
  case: (boolP (P x y)) => [Pxy | nPxy]; last by rewrite MnP1 // MnP2.
  have sPxy: strict P x y by rewrite /strict /= Pxy Hneq.
  have := Minter1 _ _ sPxy; rewrite (sum_interval _ Pxy) => /eqP.
  rewrite addr_eq0 => /eqP ->.
  have := Minter2 _ _ sPxy; rewrite (sum_interval _ Pxy) => /eqP.
  rewrite addr_eq0 => /eqP ->.
  congr (- _); apply eq_bigr => z /andP [] _; exact: IHy.
Qed.

End Unicity.



Section Moebius.

Variable T : finType.
Variable R : ringType.
Variable E : {set T}.
Variable P : poset E.

Require Import Wf.

Definition moebius_rec (x y : T) (rec : forall z, strict P z y -> R) : R :=
  if y == x then 1 else
    let callrec (z : T) := if boolP (strict P z y) is AltTrue Prf then rec _ Prf else 0
    in - \sum_(z | P x z) callrec z.

Definition moebius x : T -> R := Fix (strict_Wf P) _ (moebius_rec x).

Lemma moebius_inc x y : x \in E -> ~~ P x y -> moebius x y = 0.
Proof.
  move=> Hx Hinc.
  rewrite /moebius/moebius_rec/=/Fix/Fix_F/=.
  case: (strict_Wf P y) => A.
  case: (altP (y =P x)) => [Heq | Hneq]; first by move: Hinc; rewrite Heq (posetnn Hx).
  rewrite (eq_bigr (fun x => 0)); first by rewrite sumr_const mul0rn oppr0.
  move=> z Pxz; case (boolP (strict P z y)) => sPzy //.
  exfalso; move: Hinc; by rewrite (poset_trans Pxz (strictW sPzy)).
Qed.

Lemma moebius_interv_ind x y :
  strict P x y -> moebius x y = - \sum_(z : T | P x z && strict P z y) moebius x z.
Proof.
  move: y; apply: (well_founded_ind (strict_Wf P)) => y IHy Hy.
  rewrite /moebius /Fix -Fix_F_eq /=.
  case : (strict_Wf P y) => Accy /=.
  have:= Hy; rewrite {1}/moebius_rec eq_sym {1}/strict/= => /andP [] _ /negbTE ->.
  congr (- _); rewrite (bigID (fun z => strict P z y)) /=.
  set S := (X in (_ + X)); have {S} -> : S = 0.
    rewrite /S {S} (eq_bigr (fun x => 0)); first by rewrite sumr_const mul0rn.
    move=> z /andP [] _; by case (boolP (strict P z y)).
  rewrite addr0; apply eq_bigr => z /andP [] Pxz.
  case (boolP (strict P z y)) => //= sPzy _.
  apply: (Fix_F_inv (strict_Wf P)) => {y IHy Hy Accy sPzy z Pxz} y f g Hfg.
  rewrite /moebius_rec; case: (y == x) => //.
  congr (- _); apply: eq_bigr => z Pxz; by case (boolP (strict P z y)).
Qed.

Lemma moebius_interv x y :
  strict P x y -> \sum_(z : T | P x z && P z y) moebius x z = 0.
Proof.
  move=> sPxy.
  by rewrite (sum_interval _ (strictW sPxy)) (moebius_interv_ind sPxy) addNr.
Qed.

Lemma moebiusP : moebius_fun P moebius.
Proof.
  constructor.
  - move => x Hx; by rewrite /moebius /Fix -Fix_F_eq /= /moebius_rec eq_refl.
  - exact moebius_inc.
  - exact moebius_interv.
Qed.

Definition moebius_inv := poset_incl_excl moebiusP.

End Moebius.



Section Boolean.

Variable T : finType.
Variable R : ringType.

Definition boolmoebius (S1 S2 : {set T}) : R :=
  if (S1 \subset S2) then (-1) ^+ #|S2 :\: S1| else 0.

Lemma boolmoebiusP : moebius_fun (boolposet T) boolmoebius.
Proof.
  rewrite /boolmoebius; constructor.
  - move=> X _; by rewrite subxx_hint setDv cards0.
  - move=> X Y _; by rewrite finrelE => /negbTE ->.
  - move=> X Y; rewrite /strict /= finrelE andbC -properEneq => PrXY.
    rewrite (eq_bigr (fun z => (-1) ^+ #|z :\: X|)); first last.
      move=> Z /=; by rewrite finrelE => /andP [] ->.
    rewrite (eq_bigl (fun Z : {set T} => (X \subset Z) && (Z \subset Y))); first last.
      by move => Z /=; rewrite !finrelE.
    have {PrXY} := properP PrXY => [] [] HXY [] a HaY HanX.
    rewrite (bigID (fun (i : {set T}) => a \in i)) /=.
    rewrite (reindex_onto (fun Z => a |: Z) (fun Z => Z :\ a)) /=; first last.
      move=> i /andP [] _; by apply setD1K.
    set P := (X in \sum_( i | X i ) _ + _).
    set Q := (X in _ + \sum_( i | X i ) _).
    rewrite (eq_bigl Q); first last.
      move=> S; rewrite /P/Q{P Q} setU11 andbT.
      have -> : ((a |: S) :\ a == S) = (a \notin S).
        apply (sameP idP); apply (iffP idP) => [/setU1K -> // | /eqP <-].
        by rewrite !inE negb_and negbK eq_refl.
        case: (boolP (a \in S)) => [_| Ha] //=; first by rewrite !andbF.
        rewrite !andbT; congr (_ && _).
        - apply (sameP idP); apply (iffP idP) => /subsetP Hsub; apply/subsetP => i.
          + rewrite inE => /Hsub ->; by rewrite orbT.
          + move=> Hi; have:= Hsub _ Hi; rewrite !inE.
            case: (altP (i =P a)) => [Hia|] //=.
            exfalso; move: HanX; by rewrite -Hia Hi.
        - apply (sameP idP); apply (iffP idP) => /subsetP Hsub; apply/subsetP => i.
          + rewrite !inE; case: (altP (i =P a)) => [Hia _ | _] //=; last by apply Hsub.
            by rewrite Hia.
          + move=> Hi; apply Hsub; by rewrite inE Hi orbT.
    rewrite {P} (eq_bigr (fun i => - (-1) ^+ #|i :\: X|)); first last.
      move=> S; rewrite /Q{Q} => /andP [] /andP [] XsS _ HanS.
      suff -> : (a |: S) :\: X = a |: (S :\: X).
        by rewrite cardsU1 inE HanX /= HanS /= addSn add0n exprS mulN1r.
      rewrite -setP => i; rewrite !inE.
      by case (altP (i =P a)) => [/= ->| //]; first by rewrite HanX.
    by rewrite sumrN addNr.
Qed.

(*
Corollary inclusion_exclusion (f g : {set T} -> R) :
  (forall X, f X = \sum_(Y : {set T} | Y \subset X) g Y)
  -> (forall X, g X = \sum_(Y : {set T} | Y \subset X) (-1) ^+ #|X :\: Y| * (f Y)).
Proof.
  move=> H X.
  
Theorem poset_incl_excl x : x \in E -> 
  
*)

End Boolean.
