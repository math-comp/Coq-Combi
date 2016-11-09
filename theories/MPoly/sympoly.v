(** * Combi.MPoly.sympoly : Symmetric Polynomials *)
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
(** * The Ring of Symmetric Polynomials *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun finset.
From mathcomp Require Import bigop ssralg ssrint path perm fingroup.
From mathcomp Require ssrnum.
From SsrMultinomials Require Import ssrcomplements freeg bigenough mpoly.

Require Import sorted tools ordtype permuted partition Yamanouchi std tableau stdtab.
Require Import skewtab antisym Schur_mpoly therule Schur_altdef unitriginv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.


Lemma boolRP (R : ringType) (b : bool) : reflect (b%:R = 0 :> R) (~~b).
Proof using.
apply (iffP idP) => [/negbTE -> // | H].
apply/negP => Hb; move: H; rewrite Hb /= => /eqP.
by rewrite oner_eq0.
Qed.

Reserved Notation "{ 'sympoly' T [ n ] }"
  (at level 0, T, n at level 2, format "{ 'sympoly'  T [ n ] }").


Section DefType.

Variable n : nat.
Variable R : ringType.

Record sympoly : predArgType :=
  SymPoly {sympol :> {mpoly R[n]}; _ : sympol \is symmetric}.

Canonical sympoly_subType := Eval hnf in [subType for sympol].
Definition sympoly_eqMixin := Eval hnf in [eqMixin of sympoly by <:].
Canonical sympoly_eqType := Eval hnf in EqType sympoly sympoly_eqMixin.
Definition sympoly_choiceMixin := Eval hnf in [choiceMixin of sympoly by <:].
Canonical sympoly_choiceType :=
  Eval hnf in ChoiceType sympoly sympoly_choiceMixin.

Definition sympoly_of of phant R := sympoly.

Identity Coercion type_sympoly_of : sympoly_of >-> sympoly.

Lemma sympol_inj : injective sympol. Proof. exact: val_inj. Qed.

End DefType.

(* We need to break off the section here to let the argument scope *)
(* directives take effect.                                         *)
Bind Scope ring_scope with sympoly_of.
Bind Scope ring_scope with sympoly.
Arguments Scope sympol [_ ring_scope].
Arguments Scope sympol_inj [_ ring_scope ring_scope _].

Notation "{ 'sympoly' T [ n ] }" := (sympoly_of n (Phant T)).


Section SymPolyRingType.

Variable n : nat.
Variable R : ringType.

Definition sympoly_zmodMixin :=
  Eval hnf in [zmodMixin of {sympoly R[n]} by <:].
Canonical sympoly_zmodType :=
  Eval hnf in ZmodType {sympoly R[n]} sympoly_zmodMixin.
Canonical sympolynom_zmodType :=
  Eval hnf in ZmodType (sympoly n R) sympoly_zmodMixin.

Definition sympoly_ringMixin :=
  Eval hnf in [ringMixin of {sympoly R[n]} by <:].
Canonical sympoly_ringType :=
  Eval hnf in RingType {sympoly R[n]} sympoly_ringMixin.
Canonical sympolynom_ringType :=
  Eval hnf in RingType (sympoly n R) sympoly_ringMixin.

Definition sympoly_lmodMixin :=
  Eval hnf in [lmodMixin of {sympoly R[n]} by <:].
Canonical sympoly_lmodType :=
  Eval hnf in LmodType R {sympoly R[n]} sympoly_lmodMixin.
Canonical sympolynom_lmodType :=
  Eval hnf in LmodType R (sympoly n R) sympoly_lmodMixin.

Definition sympoly_lalgMixin :=
  Eval hnf in [lalgMixin of {sympoly R[n]} by <:].
Canonical sympoly_lalgType :=
  Eval hnf in LalgType R {sympoly R[n]} sympoly_lalgMixin.
Canonical sympolynom_lalgType :=
  Eval hnf in LalgType R (sympoly n R) sympoly_lalgMixin.

Lemma sympol_is_lrmorphism :
  lrmorphism (@sympol n R : {sympoly R[n]} -> {mpoly R[n]}).
Proof. by []. Qed.
Canonical sympol_additive   := Additive   sympol_is_lrmorphism.
Canonical sympol_rmorphism  := RMorphism  sympol_is_lrmorphism.
Canonical sympol_linear     := AddLinear  sympol_is_lrmorphism.
Canonical sympol_lrmorphism := LRMorphism sympol_is_lrmorphism.

Lemma sympol_is_symmetric (x : {sympoly R[n]}) : sympol x \is symmetric.
Proof. by case: x. Qed.

End SymPolyRingType.

Hint Resolve sympol_is_symmetric.


Section SymPolyComRingType.

Variable n : nat.
Variable R : comRingType.

Definition sympoly_comRingMixin :=
  Eval hnf in [comRingMixin of {sympoly R[n]} by <:].
Canonical sympoly_comRingType :=
  Eval hnf in ComRingType {sympoly R[n]} sympoly_comRingMixin.
Canonical sympolynom_comRingType :=
  Eval hnf in ComRingType (sympoly n R) sympoly_comRingMixin.

Definition sympoly_algMixin :=
  Eval hnf in [algMixin of {sympoly R[n]} by <:].
Canonical sympoly_algType :=
  Eval hnf in AlgType R {sympoly R[n]} sympoly_algMixin.
Canonical sympolynom_algType :=
  Eval hnf in AlgType R (sympoly n R) sympoly_algMixin.

End SymPolyComRingType.

Section SymPolyIdomainType.

Variable n : nat.
Variable R : idomainType.

Definition sympoly_unitRingMixin :=
  Eval hnf in [unitRingMixin of {sympoly R[n]} by <:].
Canonical sympoly_unitRingType :=
  Eval hnf in UnitRingType {sympoly R[n]} sympoly_unitRingMixin.
Canonical sympolynom_unitRingType :=
  Eval hnf in UnitRingType (sympoly n R) sympoly_unitRingMixin.

Canonical sympoly_comUnitRingType :=
  Eval hnf in [comUnitRingType of {sympoly R[n]}].
Canonical sympolynom_comUnitRingType :=
  Eval hnf in [comUnitRingType of sympoly n R].

Definition sympoly_idomainMixin :=
  Eval hnf in [idomainMixin of {sympoly R[n]} by <:].
Canonical sympoly_idomainType :=
  Eval hnf in IdomainType {sympoly R[n]} sympoly_idomainMixin.
Canonical sympolynom_idomainType :=
  Eval hnf in IdomainType (sympoly n R) sympoly_idomainMixin.

Canonical sympoly_unitAlgType :=
  Eval hnf in [unitAlgType R of {sympoly R[n]}].
Canonical sympolynom_unitAlgType :=
  Eval hnf in [unitAlgType R of (sympoly n R)].

End SymPolyIdomainType.



(* Print Canonical Projections. *)


Section Bases.

Variable n : nat.

Variable R : comRingType.
Implicit Type m : 'X_{1.. n}.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").


(* From  mpoly.v : \sum_(h : {set 'I_n} | #|h| == k) \prod_(i in h) 'X_i. *)
Fact syme_sym d : mesym n R d \is symmetric.
Proof using. exact: mesym_sym. Qed.
Definition syme d : {sympoly R[n]} := SymPoly (syme_sym d).
Lemma syme_geqnE d : d > n -> syme d = 0.
Proof. by move=> Hd; apply val_inj; rewrite /= mesym_geqnE. Qed.
Lemma mesym_homog d : mesym n R d \is d.-homog.
Proof using.
apply/dhomogP => m.
rewrite msupp_mesymP => /existsP [] s /andP [] /eqP <- {d} /eqP -> {m}.
exact: mdeg_mesym1.
Qed.
Lemma syme_homog d : sympol (syme d) \is d.-homog.
Proof using. by rewrite mesym_homog. Qed.

Definition symh_pol_bound b d : {mpoly R[n]} :=
  \sum_(m : 'X_{1..n < b} | mdeg m == d) 'X_[m].
Definition symh_pol d : {mpoly R[n]} := symh_pol_bound d.+1 d.
Lemma mcoeff_symh_pol_bound b d m :
  b > d -> (symh_pol_bound b d)@_m = (mdeg m == d)%:R.
Proof.
rewrite linear_sum /= => H.
case: (altP (mdeg m =P d)) => Hd /=.
- have Hsm : mdeg m < b by rewrite Hd.
  rewrite (bigD1 (BMultinom Hsm)) ?Hd //= mcoeffX eq_refl big1 ?addr0 //=.
  by move=> mon /andP [_ /negbTE]; rewrite {1}/eq_op /= mcoeffX => ->.
- rewrite big1 // => mon /eqP Hd1; rewrite mcoeffX.
  by apply/boolRP; move: Hd; rewrite -{1}Hd1; apply contra=> /eqP ->.
Qed.
Lemma mcoeff_symh_pol d m : (symh_pol d)@_m = (mdeg m == d)%:R.
Proof. exact: mcoeff_symh_pol_bound. Qed.
Lemma symh_pol_any b d : d < b -> symh_pol d = symh_pol_bound b d.
move=> H; apply/mpolyP => m.
by rewrite mcoeff_symh_pol mcoeff_symh_pol_bound.
Qed.
Fact symh_sym d : symh_pol d \is symmetric.
Proof using.
apply/issymP => s; rewrite -mpolyP => m.
by rewrite mcoeff_sym !mcoeff_symh_pol mdeg_mperm.
Qed.
Definition symh d : {sympoly R[n]} := SymPoly (symh_sym d).
Lemma mcoeff_symh d m : (symh d)@_m = (mdeg m == d)%:R.
Proof. exact: mcoeff_symh_pol. Qed.
Lemma symh_homog d : sympol (symh d) \is d.-homog.
Proof using. by apply rpred_sum => m /eqP H; rewrite dhomogX /= H. Qed.

Definition symp_pol d  : {mpoly R[n]} := \sum_(i < n) 'X_i ^+ d.
Fact symp_sym d : symp_pol d \is symmetric.
Proof using.
apply/issymP => s.
rewrite linear_sum /= (reindex_inj (h := s^-1))%g /=; last by apply/perm_inj.
apply eq_bigr => i _; rewrite rmorphX /=; congr (_ ^+ _).
rewrite msymX /=; congr mpolyX.
rewrite mnmP => j; rewrite !mnmE /=; congr nat_of_bool.
by apply/eqP/eqP => [|->//]; apply: perm_inj.
Qed.
Definition symp d : {sympoly R[n]} := SymPoly (symp_sym d).
Lemma symp_homog d : sympol (symp d) \is d.-homog.
Proof using.
apply rpred_sum => m _.
have /(dhomogMn d) : ('X_m : {mpoly R[n]}) \is 1.-homog.
  by rewrite dhomogX /= mdeg1.
by rewrite mul1n.
Qed.


Definition symm_pol (sh : n.-tuple nat) : {mpoly R[n]} :=
  (\sum_(p : permuted sh) 'X_[Multinom p] ).
Lemma mcoeff_symm_pol sh m : (symm_pol sh)@_m = (perm_eq sh m)%:R.
Proof.
rewrite linear_sum /=.
case: (boolP (perm_eq sh m)) => /= [| /(elimN idP)] Hperm.
- rewrite (bigD1 (Permuted Hperm)) //= (_ : [multinom m] = m);
    last exact: val_inj.
  rewrite mcoeffX eq_refl /= big1 ?addr0 // => p /eqP Hp.
  rewrite mcoeffX; case: (altP (_ =P _)) => //= Heq.
  by exfalso; apply: Hp; apply val_inj; rewrite /= -Heq.
- rewrite big1 // => p _.
  rewrite mcoeffX; case: (altP (_ =P _)) => //= Heq.
  by exfalso; apply Hperm; rewrite -Heq /=; exact: permutedP.
Qed.
Fact symm_sym sh : symm_pol sh \is symmetric.
Proof.
apply/issymP => s; apply/mpolyP => m.
rewrite mcoeff_sym !mcoeff_symm_pol.
have: perm_eq (m#s) m by apply/tuple_perm_eqP; exists s.
by move=> /perm_eqrP ->.
Qed.
Definition symm sh : {sympoly R[n]} :=
  if size sh <= n then SymPoly (symm_sym (mpart sh)) else 0 : {sympoly R[n]}.
Lemma symm_oversize sh : n < size sh -> symm sh = 0.
Proof. by rewrite ltnNge /symm => /negbTE ->. Qed.
Lemma mcoeff_symm sh m :
  size sh <= n -> (symm sh)@_m = (perm_eq (mpart (n := n) sh) m)%:R.
Proof. by move=> H; rewrite /symm H mcoeff_symm_pol. Qed.
Lemma symm_homog d (sh : 'P_d) :
  sympol (symm sh) \is d.-homog.
Proof using.
case: (leqP (size sh) n) => [Hsz | /symm_oversize ->]; last exact: dhomog0.
rewrite /= unfold_in; apply/allP => /= m.
rewrite mcoeff_msupp mcoeff_symm //.
case: (boolP (perm_eq _ _)) => [Hperm _ | _]; last by rewrite /= eq_refl.
rewrite /mdeg sumnE -(intpartn_sumn sh).
move: Hperm => /perm_sumn <-{m}.
rewrite -{2}(mpartK _ Hsz) // is_dominant_partm; last exact: mpart_is_dominant.
apply/eqP; rewrite -!sumnE big_filter.
rewrite [LHS](bigID (fun i => i == 0%N)) /= big1 ?add1n //.
by move=> i /eqP.
Qed.

Lemma issym_symmE (p : {mpoly R[n]}) :
  p \is symmetric ->
  p = \sum_(m <- msupp p | m \is dominant) p@_m *: symm (partm m).
Proof.
move=> Hsym; apply/mpolyP => m.
case: (boolP (m \in msupp p)) => Hm.
- rewrite -big_filter (bigD1_seq (mpart (partm m))) /=; first last.
  + by apply filter_uniq; apply msupp_uniq.
  + rewrite mem_filter mpart_is_dominant //= mcoeff_msupp.
    have [s /eqP ->] := mpart_partm_perm m.
    by rewrite -mcoeff_sym (issymP p Hsym) -mcoeff_msupp.
  rewrite linearD linearZ /= mpartK ?size_partm //.
  rewrite big_filter_cond /=.
  have -> : p@_(mpart (partm m)) = p@_m.
    have [/= s /eqP ->]:= mpart_partm_perm m.
    by rewrite -mcoeff_sym (issymP p Hsym).
  have -> : (symm (partm m))@_m = 1.
    by rewrite (mcoeff_symm _ (size_partm _)) perm_eq_sym partm_perm_eqK.
  rewrite mulr1 -[LHS]addr0; congr (_ + _); symmetry.
  rewrite !raddf_sum /=.
  rewrite big_seq_cond; apply big1 => /= m' /and3P [_ Hdom Hm'].
  rewrite mcoeffZ (mcoeff_symm _ (size_partm _)).
  rewrite [perm_eq _ _](_ : _ = false) /= ?mulr0 //.
  apply (introF idP) => /perm_eq_partm
                         /(congr1 (fun x : intpart => mpart (n := n) x)) H.
  by move: Hm'; rewrite -{}H !(partmK Hdom) eq_refl.
- rewrite (memN_msupp_eq0 Hm); symmetry.
  rewrite !raddf_sum /=.
  rewrite big_seq_cond; apply big1 => /= m' /andP [Hsupp Hdom].
  rewrite mcoeffZ (mcoeff_symm _ (size_partm _)) partmK //.
  rewrite [perm_eq _ _](_ : _ = false) /= ?mulr0 //.
  apply (introF idP) => /mnm_perm_eq [/= s /eqP Hs].
  move: Hm Hsupp; rewrite -mcoeff_eq0 mcoeff_msupp Hs.
  rewrite -mcoeff_sym (issymP p Hsym) => /eqP ->.
  by rewrite eq_refl.
Qed.

Lemma symm_genE (f : {sympoly R[n]}) :
  f = \sum_(m <- msupp f | m \is dominant) f@_m *: symm (partm m).
Proof. by apply val_inj => /=; apply issym_symmE. Qed.


Lemma size_mpart_in_supp (f : {mpoly R[n]}) d (p : 'P_d) :
  f \is d.-homog -> mpart p \in msupp f -> size p <= n.
Proof.
rewrite /mpart; case: leqP => //= H1 /dhomogP H/H /=.
rewrite /= mdeg0 => Hd; subst d.
by move: H1; rewrite intpartn0.
Qed.

Lemma homog_symmE d (f : {sympoly R[n]}) :
  sympol f \is d.-homog ->
  f = \sum_(l : 'P_d) f@_(mpart l) *: symm l.
Proof.
move=> Hhomog; rewrite {1}(symm_genE f).
apply val_inj => /=.
rewrite !linear_sum /=  (bigID (fun i : 'P_d => mpart i \in msupp f)) /=.
rewrite [X in _ + X]big1 ?addr0;
  last by move=> i /memN_msupp_eq0 ->; rewrite scale0r.
rewrite (eq_bigr (fun i : 'P_d =>
           f@_(mpart i) *:
            sympol (symm (partm (n := n) (mpart i)))));
    first last.
  move=> i Hi; congr (_ *: _); congr sympol; congr symm.
  by rewrite mpartK //; apply (size_mpart_in_supp Hhomog Hi).
rewrite /index_enum -enumT.
transitivity (\sum_(m <- [seq mpart (i : 'P_d) |
                          i <- enum (intpartn_finType d)] |
                    m \in msupp f)
      f@_m *: sympol (symm (partm m))); last by rewrite big_map /=.
rewrite -big_filter -[RHS]big_filter; apply eq_big_perm; apply uniq_perm_eq.
- by apply filter_uniq; apply msupp_uniq.
- rewrite filter_map map_inj_in_uniq; first by apply filter_uniq; apply enum_uniq.
  move=> /= c1 c2; rewrite !mem_filter /= => /andP [Hc1 _] /andP [Hc2 _].
  move=> /(congr1 (@partm n)) /(congr1 val) /=.
  rewrite !mpartK // ?(size_mpart_in_supp _ Hc1) ?(size_mpart_in_supp _ Hc2) //.
  exact: val_inj.
- move=> /= m; rewrite !mem_filter andbC.
  case: (boolP (m \in msupp f)) => //= Hsupp.
  apply/idP/mapP => /= [Hdom | [l _ ->]]; last exact: mpart_is_dominant.
  have Hp : is_part_of_n d (partm m).
    rewrite /is_part_of_n /= intpartP andbT sumn_partm //.
    by move: Hhomog => /dhomogP/(_ _ Hsupp) /= ->.
  exists (IntPartN Hp); first by rewrite mem_enum.
  by rewrite /= partmK.
Qed.

Lemma symm_unique d (f : {sympoly R[n]}) c :
  f = \sum_(l : 'P_d) (c l) *: symm l ->
  forall l : 'P_d, (size l <= n)%N -> c l = f@_(mpart l).
Proof.
move=> -> l Hl.
rewrite !linear_sum /=.
rewrite (bigD1 l) //= !linearZ /= (mcoeff_symm _ Hl) perm_eq_refl /= mulr1.
rewrite big1 ?addr0 // => i Hil /=.
case: (leqP (size i) n) => [Hi | /symm_oversize ->];
                          last by rewrite scaler0 mcoeff0.
rewrite linearZ /= mcoeff_symm //.
rewrite [perm_eq _ _](_ : _ = false) /= ?mulr0 //.
apply negbTE; move: Hil; apply contra.
move=> /perm_eq_partm/(congr1 pval).
rewrite !mpartK // => Hil.
by apply/eqP/val_inj.
Qed.

Lemma symm_unique0 d c :
  \sum_(l : 'P_d) (c l) *: symm l = 0 ->
  forall l : 'P_d, (size l <= n)%N -> c l = 0.
Proof.
move=> /esym/symm_unique => H l /H ->.
by rewrite mcoeff0.
Qed.

(** Basis at degree 0 *)
Lemma syme0 : syme 0 = 1.
Proof using. by apply val_inj; rewrite /= mesym0E. Qed.

Lemma powersum0 : symp 0 = n%:R.
Proof using.
apply /val_inj.
rewrite /= /symp_pol (eq_bigr (fun => 1));
  last by move=> i _; rewrite expr0.
by rewrite sumr_const card_ord /= raddfMn.
Qed.

Lemma symh0 : symh 0 = 1.
Proof using.
have Hd0 : (mdeg (0%MM : 'X_{1..n})) < 1 by rewrite mdeg0.
apply val_inj => /=.
rewrite /symh_pol /symh_pol_bound (big_pred1 (BMultinom Hd0)); first last.
  by move=> m; rewrite /= mdeg_eq0 {2}/eq_op.
by rewrite mpolyX0.
Qed.


(** All basis agrees at degree 1 *)
Lemma syme1 : val (syme 1) = \sum_(i < n) 'X_i.
Proof using. by rewrite /= mesym1E. Qed.

Lemma sympe1E : symp 1 = syme 1.
Proof using.
apply val_inj; rewrite syme1 /=.
by apply eq_bigr => i _; rewrite expr1.
Qed.

Lemma symhe1E : symh 1 = syme 1.
Proof using.
apply val_inj; rewrite syme1 /= -mpolyP => m.
rewrite !raddf_sum /=.
case: (boolP (mdeg m == 1%N)) => [/mdeg1P [] i /eqP -> | Hm].
- have Hdm : (mdeg U_(i))%MM < 2 by rewrite mdeg1.
  rewrite (bigD1 (BMultinom Hdm)) /=; last by rewrite mdeg1.
  rewrite mcoeffX eq_refl big1; first last.
    move=> mm /andP [] _ /negbTE.
    by rewrite mcoeffX {1}/eq_op /= => ->.
  rewrite /= (bigD1 i) // mcoeffX eq_refl /= big1 // => j /negbTE H.
  rewrite mcoeffX.
  case eqP => //; rewrite mnmP => /(_ i).
  by rewrite !mnm1E H eq_refl.
- rewrite big1; first last.
    move=> p /eqP Hp; rewrite mcoeffX.
    case eqP => // Hpm; subst m.
    by move: Hm; rewrite Hp.
  rewrite big1 // => p _.
  rewrite mcoeffX; case eqP => // Hmm; subst m.
  by rewrite mdeg1 in Hm.
Qed.

End Bases.

Section Schur.

Variable n0 : nat.
Variable R : comRingType.

Local Notation n := n0.+1.

Definition syms d (la : 'P_d) : {sympoly R[n]} :=
  SymPoly (Schur_sym n0 R la).
Lemma syms_homog d (la : 'P_d) : sympol (syms la) \is d.-homog.
Proof. exact: Schur_homog. Qed.

Lemma syms0 (la : 'P_0) : syms la = 1.
Proof. by apply val_inj; rewrite /= Schur0. Qed.

Lemma syms1 (la : 'P_1) : syms la = \sum_(i < n) 'X_i :> {mpoly R[n]}.
Proof. by rewrite /= Schur1. Qed.

Lemma syms_rowpartn d : syms (rowpartn d) = symh n R d.
Proof.
by apply val_inj; rewrite /= /symh_pol /symh_pol_bound Schur_rowpartn.
Qed.

Lemma syms_colpartn d : syms (colpartn d) = syme n R d.
Proof.
by apply val_inj; rewrite /= mesym_SchurE.
Qed.

End Schur.

Notation "''e_' k" := (syme _ _ k)
                              (at level 8, k at level 2, format "''e_' k").
Notation "''h_' k" := (symh _ _ k)
                              (at level 8, k at level 2, format "''h_' k").
Notation "''p_' k" := (symp _ _ k)
                              (at level 8, k at level 2, format "''p_' k").

(** Prod of generator *)

Section ProdGen.

Variable n : nat.
Variable R : comRingType.
Local Notation SF := {sympoly R[n]}.

Section Defs.

Variable gen : nat -> SF.
Hypothesis gen_homog : forall d, sympol (gen d) \is d.-homog.

Definition prod_gen d (sh : 'P_d) := \prod_(i <- sh) gen i.
Lemma prod_gen_homog d (sh : 'P_d) :
  sympol (prod_gen sh) \is d.-homog.
Proof using gen_homog.
rewrite /prod_gen; case: sh => sh /= /andP [/eqP <- _] {d}.
elim: sh => [| d sh IHsh] /=; first by rewrite big_nil /= dhomog1.
by rewrite big_cons; apply dhomogM; first exact: gen_homog.
Qed.

Lemma prod_gen0 (l : 'P_0) : prod_gen l = 1.
Proof. by rewrite /prod_gen intpartn0 big_nil. Qed.

Lemma prod_genM c d (l : 'P_c) (k : 'P_d) :
  (prod_gen l) * (prod_gen k) = prod_gen (l +|+ k).
Proof using.
by rewrite /prod_gen (eq_big_perm _ (perm_union_intpartn l k)) big_cat.
Qed.

End Defs.

Definition prod_syme := prod_gen (@syme n R).
Definition prod_syme_homog := prod_gen_homog (@syme_homog n R).
Definition prod_symh := prod_gen (@symh n R).
Definition prod_symh_homog := prod_gen_homog (@symh_homog n R).
Definition prod_symp := prod_gen (@symp n R).
Definition prod_symp_homog := prod_gen_homog (@symp_homog n R).

Variable gA gB : nat -> SF.
Variable co : forall (d : nat), 'P_d -> R.

Fixpoint coeff_prodgen_seq l : 'P_(sumn l) -> R :=
  if l is l0 :: l' then
    fun la : 'P_(sumn (l0 :: l')) =>
             \sum_(p | la == p.1 +|+ p.2) co p.1 * coeff_prodgen_seq p.2
  else fun _ => 1.
Definition coeff_prodgen_intpartn d (la mu : 'P_d) : R :=
  coeff_prodgen_seq (l := la) (cast_intpartn (esym (intpartn_sumn la)) mu).

Lemma coeff_prodgen_cast l k nu
      (eqlamu : l = k) (eqsum : sumn l = sumn k) :
  coeff_prodgen_seq (cast_intpartn eqsum nu) = coeff_prodgen_seq nu.
Proof.
by subst k; congr coeff_prodgen_seq; apply val_inj; rewrite cast_intpartnE.
Qed.

Lemma prod_prodgen :
  (forall d, gA d = \sum_(la : 'P_d) co la *: prod_gen gB la :> SF) ->
  forall d (la : 'P_d),
    prod_gen gA la = \sum_(mu : 'P_d)
                      coeff_prodgen_intpartn la mu *: prod_gen gB mu :> SF.
Proof.
rewrite /coeff_prodgen_intpartn /= {2}/prod_gen => H d la.
have := intpartn_sumn la.
case: la => [la /= Hla] Hd; subst d.
rewrite (eq_bigr (fun mu => coeff_prodgen_seq mu *: prod_gen gB mu)); first last.
  by move=> mu _; congr (_ *: _); rewrite coeff_prodgen_cast /=.
elim: la {Hla} => [| l la IHla] /=.
  rewrite big_nil (big_pred1 (rowpartn 0)) ?prod_gen0 ?scale1r // => la.
  by symmetry; apply/eqP/val_inj; rewrite /= intpartn0.
rewrite big_cons H; symmetry.
transitivity
  (\sum_(mu : _) \sum_(p | mu == p.1 +|+ p.2)
    (co (d := l) p.1 * coeff_prodgen_seq (l := la) p.2) *: prod_gen gB mu).
  by apply eq_bigr => mu _; rewrite scaler_suml.
rewrite (exchange_big_dep xpredT) //=.
pose f mu nu := (co (d := l) mu *: prod_gen gB mu) *
                (coeff_prodgen_seq (l := la) nu *: prod_gen gB nu).
transitivity (\sum_(p : _) f p.1 p.2).
  apply eq_bigr => [[mu nu] _] /=; rewrite big_pred1_eq.
  by rewrite /f -scalerAl -scalerAr scalerA prod_genM.
rewrite -(pair_big xpredT xpredT) /=.
rewrite mulr_suml; apply eq_bigr => nu _.
by rewrite /f -mulr_sumr -IHla.
Qed.

End ProdGen.

Notation "''e[' k ]" := (prod_syme _ _ k)
                              (at level 8, k at level 2, format "''e[' k ]").
Notation "''h[' k ]" := (prod_symh _ _ k)
                              (at level 8, k at level 2, format "''h[' k ]").
Notation "''p[' k ]" := (prod_symp _ _ k)
                              (at level 8, k at level 2, format "''p[' k ]").
Notation "''m[' k ]" := (symm _ _ k)
                              (at level 8, k at level 2, format "''m[' k ]").
Notation "''s[' k ]" := (syms _ _ k)
                              (at level 8, k at level 2, format "''s[' k ]").


Section LRrule_Pieri.

Variable n0 : nat.
Local Notation n := n0.+1.
Variables R : comRingType.
Local Notation SF := {sympoly R[n]}.

Lemma syms_symsM d1 (la : 'P_d1) d2 (mu : 'P_d2) :
  's[la] * 's[mu] =
  \sum_(nu : 'P_(d1 + d2) | included la nu)
     's[nu] *+ LRyam_coeff la mu nu :> SF.
Proof.
apply val_inj; rewrite /= LRyam_coeffP linear_sum /=; apply eq_bigr => nu Hnu.
by rewrite raddfMn /=.
Qed.

Lemma syms_symhM d1 (la : 'P_d1) d2 :
  's[la] * 'h_d2 = \sum_(nu : 'P_(d1 + d2) | hb_strip la nu) 's[nu] :> SF.
Proof.
by apply val_inj; rewrite -syms_rowpartn /= Pieri_rowpartn raddf_sum.
Qed.

Lemma syms_symeM d1 (la : 'P_d1) d2 :
  's[la] * 'e_d2 = \sum_(nu : 'P_(d1 + d2) | vb_strip la nu) 's[nu] :> SF.
Proof.
by apply val_inj; rewrite -syms_colpartn /= Pieri_colpartn raddf_sum.
Qed.

End LRrule_Pieri.


Section ScalarChange.

Variables R S : comRingType.
Variable mor : {rmorphism R -> S}.
Variable n0 : nat.
Local Notation n := n0.+1.

Lemma map_mpoly_issym (f : {sympoly R[n]}) : map_mpoly mor f \is symmetric.
Proof.
apply/issymP => s.
by rewrite msym_map_mpoly (issymP _ (sympol_is_symmetric f)).
Qed.
Definition map_sympoly (f : {sympoly R[n]}) : {sympoly S[n]} :=
           SymPoly (map_mpoly_issym f).

Lemma map_sympoly_is_rmorphism : rmorphism map_sympoly.
Proof.
rewrite /map_sympoly; repeat split.
- by move=> i j /=; apply val_inj; rewrite /= rmorphB.
- by move=> i j /=; apply val_inj; rewrite /= rmorphM.
- by apply val_inj; rewrite /= rmorph1.
Qed.
Canonical map_sympol_additive   := Additive  map_sympoly_is_rmorphism.
Canonical map_sympoly_rmorphism := RMorphism map_sympoly_is_rmorphism.

Lemma scale_map_sympoly (r : R) (p : {sympoly R[n]}) :
  map_sympoly (r *: p) = (mor r) *: (map_sympoly p).
Proof.
apply val_inj; rewrite /= (mpolyE p) raddf_sum /=.
apply/mpolyP => m.
rewrite mcoeffZ !mcoeff_map_mpoly /= -!rmorphM /=; congr (mor _).
rewrite !linear_sum /= mulr_sumr.
by apply eq_bigr => i _; rewrite /= !linearZ /=.
Qed.

Lemma map_symm d : map_sympoly 'm[d] = 'm[d].
Proof.
apply val_inj; rewrite /= /symm.
case: leqP => _ /=; last exact: rmorph0.
rewrite /symm_pol rmorph_sum /=.
apply eq_bigr => X _; exact: map_mpolyX.
Qed.

Lemma map_syme d : map_sympoly 'e_d = 'e_d.
Proof.
apply val_inj; rewrite /= /mesym rmorph_sum /=.
apply eq_bigr => X _; rewrite rmorph_prod /=.
by apply eq_bigr => i _; rewrite map_mpolyX.
Qed.
Lemma map_syme_prod d (l : 'P_d) : map_sympoly 'e[l] = 'e[l].
Proof. by rewrite rmorph_prod; apply eq_bigr => i _; exact: map_syme. Qed.

Lemma map_symh d : map_sympoly 'h_d = 'h_d.
Proof.
apply val_inj; rewrite /= /symh_pol rmorph_sum /=.
by apply eq_bigr => X _; rewrite map_mpolyX.
Qed.
Lemma map_symh_prod d (l : 'P_d) : map_sympoly 'h[l] = 'h[l].
Proof. by rewrite rmorph_prod; apply eq_bigr => i _; exact: map_symh. Qed.

Lemma map_symp d : map_sympoly 'p_d = 'p_d.
Proof.
apply val_inj; rewrite /= /symp_pol rmorph_sum /=.
by apply eq_bigr => X _; rewrite rmorphX /= map_mpolyX.
Qed.
Lemma map_symp_prod d (l : 'P_d) : map_sympoly 'p[l] = 'p[l].
Proof. by rewrite rmorph_prod; apply eq_bigr => i _; exact: map_symp. Qed.

Lemma map_syms d (la : 'P_d) :
  map_sympoly 's[la] = 's[la].
Proof.
apply val_inj; rewrite /= rmorph_sum /=.
apply eq_bigr => X _; rewrite rmorph_prod; apply eq_bigr => /= i _.
by rewrite map_mpolyX.
Qed.

End ScalarChange.


Require Import composition.

Section ChangeBasis.

Variable n0 : nat.
Local Notation n := n0.+1.
Variable R : comRingType.

Local Notation "''XX'" := 'X_{1.. n}.
Local Notation "''XX_' m " := 'X_{1.. n < (mdeg m).+1, (mdeg m).+1} (at level 0).
Implicit Type m : 'XX.
Local Notation SF := {sympoly R[n]}.


From mathcomp Require Import binomial.

Lemma sum_symh_syme (d : nat) :
  d != 0%N ->
  \sum_(0 <= i < d.+1) (-1)^+i *: ('h_i * 'e_(d - i)) = 0 :> SF.
Proof.
move=> Hd; apply val_inj; rewrite /= rmorph_sum /=.
apply mpolyP => m; rewrite linear_sum /= mcoeff0.
case: (altP (mdeg m =P d)) => Hm; first last.
  rewrite big_nat big1 // => i /=; rewrite ltnS => Hi.
  rewrite linearZ /= mcoeffM big1 ?mulr0 //= => [[m1 m2] /= /eqP Hmm].
  rewrite mcoeff_symh mcoeff_mesym.
  case: (altP (mdeg m1 =P i)) => Hm1; rewrite ?mul0r // mul1r.
  rewrite /mechar.
  case: (altP (mdeg m2 =P (d - i)%N)) => Hm2; rewrite ?mul0r //=.
  exfalso; move: Hm; rewrite Hmm.
  by rewrite mdegD Hm1 Hm2 subnKC // eq_refl.
rewrite big_nat_rev /= add0n.
apply/eqP; rewrite -(mulrI_eq0 _ (lreg_sign (n := d))) mulr_sumr; apply/eqP.
transitivity
  (\sum_(0 <= i < d.+1) (-1)^+i * (binomial #|[set j | m j != 0%N]| i)%:R : R).
  apply eq_big_nat => /= i; rewrite ltnS => Hi.
  rewrite subSS subKn // linearZ /= mulrA; congr (_ * _).
    rewrite -signr_odd -[X in _ * X]signr_odd -signr_addb.
    by rewrite odd_sub // addKb signr_odd.
  rewrite mcoeffM.
  rewrite (bigID (fun k : 'XX_(m) => (mechar i k.2))) /=.
  rewrite addrC big1 ?add0r; first last.
    move=> [/= m1 m2 /andP [Hmm /negbTE Hf]].
    by rewrite mcoeff_mesym Hf /= mulr0.
  rewrite (eq_bigr (fun k : 'XX_m => 1)); first last.
    move=> [/= m1 m2 /andP [/eqP H1 H2]].
    rewrite mcoeff_symh mcoeff_mesym H2 /= mulr1.
    suff -> : mdeg m1 == (d - i)%N by [].
    move: Hm; rewrite {1}H1 mdegD.
    move: H2 => /andP [/eqP -> _] <-.
    by rewrite addnK.
  subst d; rewrite sumr_const /= -cards_draws; congr _%:R.
  pose f := (fun mm : 'XX => [set j | mm j != 0%N] : {set 'I_n}).
  pose g := (fun S : {set 'I_n} => [multinom (i \in S : nat) | i < n]).
  have canfg : {in mechar i, cancel f g}.
    move=> m2.
    rewrite unfold_in /mechar /= => /andP [_ /forallP /= Hall].
    rewrite /f /g {f g} /=.
    apply/mnmP => j; rewrite mnmE inE.
    case: (altP (m2 j =P 0%N)) => [-> |] //=.
    by move/(_ j): Hall; case: (m2 j) => [|[|k]].
  rewrite -(card_in_imset (f := f \o (fun mm : 'XX_m => bmnm mm.2))); first last.
    move=> /= [m1 m2] [n1 n2].
    rewrite !unfold_in /= => /andP [/eqP Hmm Hm2] /andP [/eqP Hnn Hn2] /(congr1 g).
    rewrite !canfg // {f g canfg} => /= [] H1.
    congr (_ , _); apply val_inj => //=.
    by rewrite -(addmK m2 m1) -Hmm -(addmK n2 n1) -Hnn H1.
  congr #|pred_of_set _|; apply/setP => /= S; rewrite !inE !unfold_in.
  apply/imsetP/andP => /= [[[m1 m2]] | [/subsetP Hsubs /eqP Hs] ].
  - rewrite unfold_in /= /mechar =>
      /andP [/eqP Hmm] /andP [/eqP Hmdeg /forallP /= Hall ->{S}].
    rewrite /f /= {f g canfg}; split.
    + apply/subsetP => j; rewrite !inE /= {2}Hmm.
      by apply contra; rewrite mnmDE addn_eq0 => /andP [].
    + apply/eqP; rewrite -Hmdeg /mdeg [RHS]big_tuple.
      rewrite (bigID (mem [set j | m2 j != 0%N])) /= addnC.
      rewrite [X in _ = (X + _)%N]big1 ?add0n; first last.
        by move=> j; rewrite inE negbK -mnm_tnth => /eqP ->.
      rewrite [RHS](eq_bigr (fun => 1%N)) ?sum1_card //.
      move=> j; rewrite inE -mnm_tnth.
      by move/(_ j): Hall; case: (m2 j) => [|[|k]].
  - have : mdeg (g S) = #|S|.
      rewrite /mdeg [LHS]big_tuple (bigID (mem S)) /= addnC.
      rewrite [X in (X + _)%N]big1 ?add0n; first last.
        by move=> j /negbTE; rewrite tnth_mktuple => ->.
      rewrite [LHS](eq_bigr (fun => 1%N)) ?sum1_card //.
      by move=> j; rewrite tnth_mktuple => ->.
    rewrite Hs => HmdeggS.
    have Hm2 : mdeg (g S) < (mdeg m).+1 by rewrite HmdeggS ltnS.
    pose m2 := BMultinom Hm2.
    have Hm2m : (m2 <= m)%MM.
      apply/mnm_lepP => j; rewrite /= mnmE.
      case: (boolP (j \in S)) => //= /Hsubs.
      by rewrite inE lt0n.
    have Hmm := submK Hm2m.
    have Hm1 : mdeg (m - m2) < (mdeg m).+1.
      by rewrite  ltnS -{3}Hmm mdegD leq_addr.
    exists (BMultinom Hm1, m2) => /=.
    - rewrite unfold_in Hmm /= /mechar HmdeggS !eq_refl /=.
      apply/forallP => /= j; rewrite /g mnmE.
      by case: (j \in S).
    - rewrite /f /g; apply/setP => j; rewrite inE mnmE.
      by case: (j \in S).
subst d.
have : #|[set j | m j != 0%N]| <= mdeg m.
  rewrite /mdeg -sum1_card big_tuple.
  rewrite [X in _ <= X](bigID (mem [set j | m j != 0%N])) /=.
  rewrite [X in (_ + X)%N]big1 ?addn0; first last.
    by move=> i; rewrite inE negbK mnm_tnth => /eqP.
  by apply leq_sum => i; rewrite inE mnm_tnth lt0n.
have : #|[set j | m j != 0%N]| != 0%N.
  move: Hd; apply contra; rewrite cards_eq0 => /eqP/setP H.
  rewrite mdeg_eq0; apply/eqP/mnmP => i.
  by have:= H i; rewrite mnmE !inE => /negbFE => /eqP ->.
move: (#|[set j | m j != 0%N]|) => C HC HCd.
transitivity
  (\sum_(i < C.+1) (-1)^+i * 1^+(C - i) * 1^+i *+ 'C(C, i) : R); first last.
  by rewrite -exprBn subrr expr0n (negbTE HC).
rewrite big_mkord.
rewrite [LHS](bigID (fun i : 'I__ => i < C.+1)) /= addrC big1 ?add0r; first last.
  move=> i; rewrite -leqNgt => /bin_small ->.
  by rewrite mulr0.
transitivity (\sum_(i < C.+1) (-1) ^+ i * ('C(C, i))%:R : R).
  rewrite -ltnS in HCd.
  by rewrite [RHS](big_ord_widen _ (fun i => (-1) ^+ i * ('C(C, i))%:R) HCd).
apply eq_bigr => i _.
by rewrite !expr1n !mulr1 mulr_natr.
Qed.

Lemma sum_syme_symh (d : nat) :
  d != 0%N ->
  \sum_(0 <= i < d.+1) (-1)^+i *: ('e_i * 'h_(d - i)) = 0 :> SF.
Proof.
move=> Hd; rewrite big_nat_rev /=.
rewrite -[RHS](scaler0 _ ((-1)^+d)) -[in RHS](sum_symh_syme Hd) scaler_sumr /=.
rewrite !big_nat; apply eq_bigr => i /andP [_ Hi].
rewrite mulrC !add0n subSS subKn // scalerA; congr (_ *: ('h__ * 'e__)).
by rewrite -signr_odd odd_sub // signr_addb !signr_odd.
Qed.


Section HandE.

Variable E H : nat -> {sympoly R[n]}.

Hypothesis E0 : E 0 = 1.
Hypothesis H0 : H 0 = 1.
Hypothesis Hanti : forall d : nat,
    d != 0%N ->
    \sum_(0 <= i < d.+1) (-1)^+i *: (H i * E (d - i)) = 0.

Lemma symHE_rec (d : nat) :
  d != 0%N ->
  E d = \sum_(1 <= i < d.+1) H i * ((-1)^+i.-1 *: E (d - i)).
Proof.
move=> Hd; have:= Hanti Hd.
rewrite big_nat_recl // expr0 scale1r H0 mul1r subn0 => /eqP.
rewrite (addr_eq0 (E d)) => /eqP ->; rewrite big_add1 /= -sumrN.
rewrite !big_nat; apply eq_bigr => i /= Hi.
rewrite scalerAr -mulrN; congr (_ * _).
rewrite -scaleNr; congr (_ *: _).
by rewrite exprS mulN1r opprK.
Qed.

Lemma symHE_prod_intcomp d :
  E d = \sum_(c : intcompn d) (-1)^+(d - size c) *: (\prod_(i <- c) H i).
Proof.
rewrite /index_enum -enumT /=.
rewrite -[RHS](big_map (@cnval d) xpredT
   (fun c : seq nat => (-1)^+(d - size c) *: \prod_(i <- c) H i)).
rewrite enum_intcompnE.
elim: d {-2}d (leqnn d) => [| m IHm] d.
  rewrite leqn0 => /eqP ->.
  by rewrite /enum_compn /= big_seq1 /= subnn expr0 scale1r big_nil E0.
rewrite leq_eqVlt => /orP [/eqP Hm|]; last by rewrite ltnS; exact: IHm.
rewrite enum_compnE Hm // -Hm big_flatten /=.
rewrite symHE_rec; last by rewrite Hm.
rewrite big_map /index_iota subSS subn0; apply eq_big_seq => i.
rewrite mem_iota add1n ltnS => /andP [Hi Hid].
rewrite big_map.
rewrite (eq_big_seq
    (fun c : seq nat => - H i * ((-1) ^+ (d - size c) *: \prod_(i0 <- c) H i0)));
  first last.
  move=> s; rewrite -enum_compnP /is_comp_of_n /= => /andP [/eqP Hsum Hcomp].
  rewrite big_cons -scalerAr mulNr scalerN -scaleNr; congr (_ *: _).
  subst d; rewrite subSS subSn; first last.
    apply (leq_trans (size_comp Hcomp)); rewrite {}Hsum.
    case: i Hi {Hid} => // i' _.
    by rewrite subSS leq_subr.
  by rewrite exprS mulN1r opprK.
rewrite -mulr_sumr.
case: (altP (d - i =P 0)%N) => [/eqP | Hdi] /=.
  rewrite subn_eq0 => Hdi.
  have -> : i = d by apply anti_leq; rewrite Hid Hdi.
  subst d => /=.
  rewrite subnn /enum_compn /= big_seq1 big_nil /=.
  rewrite subn0 E0 mulNr -mulrN -scaleNr; congr (_ * (_)%:A).
  by rewrite exprS mulN1r opprK.
rewrite {}IHm //; first last.
  rewrite Hm; case: i Hi {Hid Hdi} => // i' _.
  by rewrite subSS leq_subr.
rewrite scaler_sumr mulNr -mulrN -sumrN; congr (_ * _).
apply eq_big_seq => s.
rewrite -enum_compnP /is_comp_of_n /= => /andP [/eqP Hsum Hn0].
rewrite scalerA -scaleNr; congr (_ *: _).
subst d; rewrite -exprD.
move: Hdi; rewrite subn_eq0 -leqNgt => {Hid} Hid.
rewrite subSn //.
case: i Hi Hsum Hid => // i _.
rewrite subSS => Hsum Him /=.
have Hsz : size s <= m.
  by apply (leq_trans (size_comp Hn0)); rewrite {}Hsum leq_subr.
rewrite -subSn // subSS subSn // exprS mulN1r opprK.
rewrite subnAC subnKC //.
have:= size_comp Hn0; rewrite Hsum.
rewrite -!subn_eq0 !subnBA //; last exact: ltnW.
by rewrite addnC.
Qed.

Lemma symHE_intcompn d :
  E d = \sum_(c : intcompn d) (-1)^+(d - size c) *: prod_gen H (partn_of_compn c).
Proof.
rewrite symHE_prod_intcomp; apply eq_bigr => c _; congr (_ *: _).
rewrite /prod_symh /prod_gen; apply eq_big_perm.
by rewrite perm_eq_sym; apply: perm_partn_of_compn.
Qed.

Definition signed_sum_compn d (la : 'P_d) :=
  \sum_(c | la == partn_of_compn c) (-1)^+(d - size c) : R.

Lemma symHE_intpartn d :
  E d = \sum_(la : 'P_d) signed_sum_compn la *: prod_gen H la.
Proof.
rewrite /signed_sum_compn symHE_intcompn; symmetry.
transitivity
  (\sum_(la : 'P_d)
      (\sum_(c | la == partn_of_compn c) (-1) ^+ (d - size c) *:
        prod_gen H la)).
  by apply eq_bigr => la _; rewrite scaler_suml.
rewrite (exchange_big_dep xpredT) //=.
apply eq_bigr => la _.
by rewrite big_pred1_eq.
Qed.

End HandE.


Lemma syme_symhE (d : nat) :
  d != 0%N ->
  'e_d = \sum_(1 <= i < d.+1) 'h_i * ((-1)^+i.-1 *: 'e_(d - i)) :> SF.
Proof.
apply: (symHE_rec (symh0 _ _)); exact: sum_symh_syme.
Qed.

Lemma symh_symeE (d : nat) :
  d != 0%N ->
  'h_d = \sum_(1 <= i < d.+1) 'e_i * ((-1)^+i.-1 *: 'h_(d - i)) :> SF.
Proof.
apply: (symHE_rec (syme0 _ _)); exact: sum_syme_symh.
Qed.

Lemma syme_to_symh n :
  'e_n = \sum_(la : 'P_n) signed_sum_compn la *: 'h[la] :> SF.
Proof.
apply: (symHE_intpartn (syme0 _ _) (symh0 _ _)); exact: sum_symh_syme.
Qed.

Lemma symh_to_syme n :
  'h_n = \sum_(la : 'P_n) signed_sum_compn la *: 'e[la] :> SF.
Proof.
apply: (symHE_intpartn (symh0 _ _) (syme0 _ _)); exact: sum_syme_symh.
Qed.


(** * Newton formula. *)
Lemma mult_symh_U k d i m :
  (('h_k : {mpoly R[n]}) * 'X_i ^+ d)@_m =
  ((mdeg m == (k + d)%N) && (m i >= d))%:R.
Proof using.
rewrite /symh_pol mulr_suml linear_sum /=; case: leqP => /= H.
- pose Ud := (U_(i) *+ d)%MM.
  have Hleq : (Ud <= m)%MM.
    apply/mnm_lepP => j; rewrite mulmnE mnm1E.
    by case: eqP => /= [<- | _]; rewrite ?muln1 ?muln0.
  rewrite andbT -(submK Hleq).
  case: (altP (_ =P _)) => Hdeg /=.
  + move: Hdeg => /eqP; rewrite mdegD mdegMn mdeg1 mul1n eqn_add2r => /eqP Hdeg.
    have Hbound : mdeg (m - Ud) < k.+1 by rewrite Hdeg.
    rewrite (bigD1 (BMultinom Hbound)) /=; last by rewrite Hdeg.
    rewrite mpolyXn -mpolyXD mcoeffX eq_refl /=.
    rewrite big1 ?addr0 // => m' /andP [_ ] Hneq.
    rewrite -mpolyXD mcoeffX.
    apply/boolRP; move: Hneq; apply contra.
    rewrite eqm_add2r => /eqP Heq.
    by apply/eqP/val_inj => /=.
  + rewrite big1 // => m' /eqP Hm'.
    rewrite mpolyXn -mpolyXD mcoeffX.
    apply/boolRP; move: Hdeg; apply contra => /eqP <-.
    by rewrite mdegD Hm' mdegMn mdeg1 mul1n.
- rewrite andbF big1 // => m' _.
  rewrite mpolyXn -mpolyXD mcoeffX.
  apply/boolRP/eqP/mnmP => /(_ i).
  rewrite mnmDE mulmnE mnm1E eq_refl muln1 => Habs.
  by move: H; rewrite -Habs ltnNge leq_addl.
Qed.

Lemma mult_symh_powersum k d m :
  ('h_k * 'p_d : SF)@_m =
  (mdeg m == (k + d)%N)%:R * \sum_(i < n) (m i >= d)%:R.
Proof using.
rewrite rmorphM /= /symp_pol !mulr_sumr linear_sum.
apply eq_bigr=> i _ /=; rewrite mult_symh_U.
by case: eqP => _ //=; rewrite ?mul0r ?mul1r.
Qed.

Lemma Newton_symh (k : nat) :
  k%:R *: 'h_k = \sum_(0 <= i < k) 'h_i * 'p_(k - i) :> SF.
Proof using.
apply val_inj => /=; apply/mpolyP => m.
rewrite mcoeffZ mcoeff_symh !linear_sum big_nat.
rewrite (eq_bigr
           (fun i =>
              (mdeg m == k)%:R *
                \sum_(j < n) (m j >= (k - i)%N)%:R)) /=; first last.
  move=> i Hi /=; rewrite mult_symh_powersum.
  by rewrite subnKC //; apply ltnW.
rewrite -big_nat -mulr_sumr mulrC.
case: (altP (mdeg m =P k)) => Hdegm; rewrite /= ?mul1r ?mul0r //.
rewrite exchange_big /=.
rewrite (eq_bigr (fun i : 'I_n => (m i)%:R)).
  by rewrite -Hdegm mdegE -natr_sum; congr (_%:R).
move=> i _ /=; rewrite -natr_sum; congr (_%:R).
have : m i <= k.
  by move: Hdegm; rewrite mdegE => <-; rewrite (bigD1 i) //=; apply leq_addr.
rewrite big_mkord (reindex_inj rev_ord_inj) /=.
rewrite (eq_bigr (fun j : 'I_k => nat_of_bool (j < m i))); first last.
  by move=> j _; rewrite subKn //.
move: (m i) => n {m Hdegm i} Hn.
rewrite (bigID (fun i : 'I_k => i < n)) /=.
rewrite (eq_bigr (fun i => 1%N)); last by move=> i ->.
rewrite sum_nat_const /= muln1 big1 ?addn0; last by move=> i /negbTE ->.
rewrite cardE /= /enum_mem -enumT /=.
rewrite (eq_filter (a2 := (preim nat_of_ord (fun i => i < n)))) //.
rewrite -(size_map nat_of_ord).
by rewrite -filter_map val_enum_ord iota_ltn // size_iota.
Qed.

Lemma Newton_symh_iota (k : nat) :
  k%:R *: 'h_k = \sum_(i <- iota 1 k) 'p_i * 'h_(k - i) :> SF.
Proof using.
rewrite Newton_symh big_mkord (reindex_inj rev_ord_inj) /=.
rewrite -(addn0 1%N) iota_addl big_map -val_enum_ord big_map.
rewrite /index_enum /= enumT; apply eq_bigr => i _.
by rewrite mulrC add1n subKn.
Qed.

End ChangeBasis.

Import IntPartNDom.
Import OrdNotations.
Close Scope ord_scope.

(** * Basis change from Schur to monomial *)
Section SymsSymmInt.

Variable (n : nat) (d : nat).
Local Notation SF := {sympoly int[n.+1]}.
Implicit Type (la mu : 'P_d).
Local Notation P := (intpartndom d).

Lemma syms_symm_int la :
  's[la] = \sum_(mu : 'P_d) 'K(la, mu)%:R *: 'm[mu] :> SF.
Proof.
rewrite /Kostka; apply val_inj; rewrite /= linear_sum /=.
apply mpolyP => m; rewrite Kostka_Coeff linear_sum /=.
case: (altP (mdeg m =P sumn la)) => Heq; first last.
- rewrite (KostkaMon_sumeval Heq); symmetry; apply big1 => i _.
  rewrite mcoeffZ.
  case: (leqP (size i) n.+1) => [Hszl | /symm_oversize ->]; first last.
    by rewrite mcoeff0 mulr0.
  rewrite mcoeff_symm //=.
  rewrite [perm_eq _ _](_ : _ = false) /= ?mulr0 //.
  apply (introF idP) => /perm_sumn.
  rewrite -!sumnE -!/(mdeg _) -sumn_partm mpartK // intpartn_sumn => Habs.
  by move: Heq; rewrite intpartn_sumn Habs eq_refl.
- have Hpm : is_part_of_n d (partm m).
   by rewrite /= sumn_partm Heq intpartn_sumn eq_refl /=.
  rewrite (bigD1 (IntPartN Hpm)) //= big1 ?addr0.
  + rewrite mcoeffZ (mcoeff_symm _ _ (size_partm _)).
    rewrite perm_eq_sym partm_perm_eqK /= mulr1.
    congr _%:R.
    rewrite -Kostka_any ?leqSpred // [RHS](Kostka_any _ (size_partm m)).
    by apply perm_KostkaMon; apply: partm_perm_eqK.
  + move=> mu Hmu; rewrite mcoeffZ.
    case: (leqP (size mu) n.+1) => [Hszl | /symm_oversize ->]; first last.
      by rewrite mcoeff0 mulr0.
    rewrite mcoeff_symm //=.
    suff /negbTE -> : ~~ (perm_eq (mpart (n := n.+1) mu) m) by rewrite mulr0.
    move: Hmu; apply contra => /perm_eq_partm H.
    apply/eqP/val_inj => /=; rewrite -H.
    by rewrite mpartK.
Qed.

Lemma syms_symm_partdom_int la :
  's[la] = 'm[la] + \sum_(mu : P | mu <A la) 'K(la, mu) *: 'm[mu] :> SF.
Proof.
rewrite -(unitrig_sum1l (fun mu : P => 'm[mu]) la (@Kostka_unitrig d)).
by rewrite -syms_symm_int.
Qed.

Lemma symm_syms_int la : 'm[la] = \sum_(mu : P) KostkaInv la mu *: 's[mu] :> SF.
Proof.
rewrite /KostkaInv.
apply (Minv_lincombl (@Kostka_unitrig d)
         (F := fun mu : P => 's[mu]) (G := fun mu : P => 'm[mu])).
exact: syms_symm_int.
Qed.

Lemma symm_syms_partdom_int la :
  'm[la] = 's[la] + \sum_(mu : P | mu <A la) KostkaInv la mu *:'s[mu] :> SF.
Proof.
rewrite -(unitrig_sum1l (fun mu : P => 's[mu]) la (@KostkaInv_unitrig d)).
by rewrite -symm_syms_int.
Qed.

End SymsSymmInt.


Section SymsSymm.

Variable (n : nat) (R : comRingType) (d : nat).
Local Notation SF := {sympoly R[n.+1]}.
Implicit Type (la mu : 'P_d).
Local Notation P := (intpartndom d).

Lemma syms_symm la :
  's[la] = \sum_(mu : 'P_d) 'K(la, mu)%:R *: 'm[mu] :> SF.
Proof.
rewrite -(map_syms [rmorphism of intr]) syms_symm_int.
rewrite rmorph_sum /=; apply eq_bigr => i _.
rewrite scale_map_sympoly map_symm /=; congr (_ *: _).
by rewrite mulrz_nat.
Qed.

Lemma syms_symm_partdom la :
  's[la] = 'm[la] + \sum_(mu : P | mu <A la) 'K(la, mu) *: 'm[mu] :> SF.
Proof.
rewrite -(map_syms [rmorphism of intr]) syms_symm_partdom_int.
rewrite rmorphD rmorph_sum /= map_symm; congr (_ + _); apply eq_bigr => i _.
rewrite scale_map_sympoly map_symm /=; congr (_ *: _).
by rewrite mulrz_nat.
Qed.

Lemma symm_syms la :
  'm[la] = \sum_(mu : P) 'K^-1(la, mu) *: 's[mu] :> SF.
Proof.
rewrite -(map_symm [rmorphism of intr]) symm_syms_int.
rewrite rmorph_sum /=; apply eq_bigr => i _.
by rewrite scale_map_sympoly map_syms.
Qed.

Lemma symm_syms_partdom la :
  'm[la] = 's[la] + \sum_(mu : P | mu <A la) 'K^-1(la, mu) *: 's[mu] :> SF.
Proof.
rewrite -(map_symm [rmorphism of intr]) symm_syms_partdom_int.
rewrite rmorphD rmorph_sum /= map_syms; congr (_ + _); apply eq_bigr => i _.
by rewrite scale_map_sympoly map_syms.
Qed.

End SymsSymm.


(** * Basis change from complete to Schur *)
Section SymhSymsInt.

Variables (n : nat) (d : nat).
Local Notation SF := {sympoly int[n.+1]}.
Local Notation P := (intpartndom d).
Implicit Type la mu : 'P_d.

Lemma symh_syms_int mu : 'h[mu] = \sum_(la : P) 'K(la, mu) *: 's[la] :> SF.
Proof.
case: mu => [mu Hmu] /=; rewrite /prod_symh /prod_gen /=.
elim: mu d Hmu => [|m mu IHmu] deg.
  rewrite big_nil => /andP [/eqP /= /esym Hd _].
  symmetry; subst deg; rewrite (big_pred1 (rowpartn 0)); first last.
    by move=> i; symmetry; apply/eqP/val_inj; rewrite /= intpartn0.
  by rewrite syms0 -[[::]]/(pnval (rowpartn 0)) Kostka_diag scale1r.
move=> /andP [/eqP Hdeg /andP [_ Hpart]].
rewrite big_cons /= {}(IHmu (sumn mu)) /= ?eq_refl ?Hpart //.
rewrite [RHS](eq_bigr
    (fun la : 'P_deg =>
       \sum_(nu : 'P_(sumn mu) | hb_strip nu la) 'K(nu, mu) *: 's[la]));
    first last.
  by move=> la _; rewrite -scaler_suml -natr_sum Kostka_ind.
rewrite mulr_sumr [RHS](exchange_big_dep predT) //=.
apply eq_bigr => la _.
rewrite -scalerAr -scaler_sumr mulrC syms_symhM; congr (_ *: _).
have H : (sumn mu + m)%N = deg by rewrite addnC -Hdeg.
rewrite (reindex (cast_intpartn H)) /=; first last.
  by apply onW_bij; apply (Bijective (cast_intpartnK _) (cast_intpartnKV _)).
apply eq_big => [nu | nu _].
- by case: nu => nu /= Hnu; rewrite cast_intpartnE /=.
- by apply val_inj; rewrite /= Schur_cast.
Qed.

Lemma symh_syms_partdom_int mu :
  'h[mu] = 's[mu] + \sum_(la : P | (mu:P) <A la ) 'K(la, mu) *: 's[la] :> SF.
Proof.
rewrite -(unitrig_sum1r (fun la : P => 's[la]) mu (@Kostka_unitrig d)).
by rewrite -symh_syms_int.
Qed.

Lemma syms_symh_int mu : 's[mu] = \sum_(la : P) KostkaInv la mu *: 'h[la] :> SF.
Proof.
rewrite /KostkaInv.
apply (Minv_lincombr (@Kostka_unitrig d)
         (G := fun mu : P => 's[mu]) (F := fun mu : P => 'h[mu])).
exact: symh_syms_int.
Qed.

Lemma syms_symh_partdom_int mu :
  's[mu] = 'h[mu] + \sum_(la : P | (mu:P) <A la) KostkaInv la mu *: 'h[la] :> SF.
Proof.
rewrite -(unitrig_sum1r (fun la : P => 'h[la]) mu (@KostkaInv_unitrig d)).
by rewrite -syms_symh_int.
Qed.

End SymhSymsInt.



Section SymhSyms.

Variables (R : comRingType) (n : nat) (d : nat).
Local Notation SF := {sympoly R[n.+1]}.
Local Notation P := (intpartndom d).
Implicit Type la mu : 'P_d.

Lemma symh_syms mu : 'h[mu] = \sum_(la : P) 'K(la, mu) *: 's[la] :> SF.
Proof.
rewrite -(map_symh_prod [rmorphism of intr]) symh_syms_int.
rewrite rmorph_sum /=; apply eq_bigr => i _.
rewrite scale_map_sympoly map_syms /=; congr (_ *: _).
by rewrite mulrz_nat.
Qed.

Lemma symh_syms_partdom mu :
  'h[mu] = 's[mu] + \sum_(la : P | (mu:P) <A la ) 'K(la, mu) *: 's[la] :> SF.
Proof.
rewrite -(map_symh_prod [rmorphism of intr]) symh_syms_partdom_int.
rewrite rmorphD rmorph_sum /= map_syms; congr (_ + _); apply eq_bigr => i _.
rewrite scale_map_sympoly map_syms /=; congr (_ *: _).
by rewrite mulrz_nat.
Qed.

Lemma syms_symh mu : 's[mu] = \sum_(la : P) 'K^-1(la, mu) *: 'h[la] :> SF.
Proof.
rewrite -(map_syms [rmorphism of intr]) syms_symh_int.
rewrite rmorph_sum /=; apply eq_bigr => i _.
by rewrite scale_map_sympoly map_symh_prod.
Qed.

Lemma syms_symh_partdom mu :
  's[mu] = 'h[mu] + \sum_(la : P | (mu:P) <A la) 'K^-1(la, mu) *: 'h[la] :> SF.
Proof.
rewrite -(map_syms [rmorphism of intr]) syms_symh_partdom_int.
rewrite rmorphD rmorph_sum /= map_symh_prod; congr (_ + _); apply eq_bigr => i _.
by rewrite scale_map_sympoly map_symh_prod.
Qed.

End SymhSyms.


Section ChangeBasisSymhPowerSum.

Import ssrnum Num.Theory.

Variable nvar0 : nat.
Variable R : fieldType.
Local Notation nvar := nvar0.+1.
Local Notation SF := {sympoly R[nvar]}.

Fixpoint prod_partsum (s : seq nat) :=
  if s is _ :: s' then (sumn s * prod_partsum s')%N else 1%N.

Local Notation "\Pi s" := (prod_partsum s)%:R^-1 (at level 0, s at level 2).

Lemma symh_to_symp_prod_partsum n :
  [char R] =i pred0 ->
  'h_n = \sum_(c : intcompn n) \Pi c *: \prod_(i <- c) 'p_i :> SF.
Proof using.
rewrite /index_enum -enumT /= charf0P => Hchar.
rewrite -[RHS](big_map (@cnval n) xpredT
   (fun c : seq nat => \Pi c *: \prod_(i <- c) 'p_i)).
rewrite enum_intcompnE.
elim: n {-2}n (leqnn n) => [| m IHm] n.
  rewrite leqn0 => /eqP ->.
  by rewrite big_seq1 big_nil symh0 /= invr1 scale1r.
rewrite leq_eqVlt => /orP [/eqP Hm|]; last by rewrite ltnS; exact: IHm.
rewrite enum_compnE Hm // -Hm big_flatten /=.
have Hn : (n%:R : R) != 0 by rewrite Hchar Hm.
apply (scalerI Hn); rewrite Newton_symh_iota.
rewrite scaler_sumr big_map; apply eq_big_seq => i.
rewrite mem_iota add1n ltnS => /andP [Hi Hin].
rewrite big_map big_seq.
rewrite (eq_bigr
    (fun c : seq nat => (n%:R^-1 *: 'p_i) *
         (\Pi c *: \prod_(j <- c) 'p_j))); first last.
  move=> s; rewrite -enum_compnP /is_comp_of_n /= => /andP [/eqP -> _].
  rewrite subnKC // big_cons scalerAr.
  by rewrite natrM invfM -!scalerAr -scalerAl scalerA mulrC.
rewrite -big_seq -mulr_sumr {}IHm; first last.
  by rewrite leq_subLR Hm -(add1n m) leq_add2r.
by rewrite -scalerAl scalerA divff // scale1r; congr(_ * _).
Qed.

Import LeqGeqOrder.

Lemma symh_to_symp_intpartn n :
  [char R] =i pred0 ->
  'h_n = \sum_(l : 'P_n)
           (\sum_(c : intcompn n | perm_eq l c) \Pi c) *: 'p[l] :> SF.
Proof.
move/symh_to_symp_prod_partsum => ->.
rewrite (partition_big (@partn_of_compn n) xpredT) //=.
apply eq_bigr => l _; rewrite scaler_suml; apply eq_big.
- move=> c; apply/eqP/idP => [<- | Hperm]; first exact: perm_partn_of_compn.
  apply val_inj => /=; apply (eq_sorted geq_trans) => //.
  + exact: sort_sorted.
  + by rewrite (perm_eqrP Hperm) perm_sort.
- move=> c /eqP <-; congr (_ *: _).
  rewrite /prod_symp /prod_gen; apply eq_big_perm.
  by rewrite perm_eq_sym; apply: perm_partn_of_compn.
Qed.

Require Import permcent.

Lemma intcompn_cons_sub_proof i n (c : intcompn (n - i)) :
  i != 0%N -> (i <= n)%N -> is_comp_of_n n (i :: c).
Proof.
move=> Hi Hin.
rewrite /is_comp_of_n /= intcompn_sumn subnKC // eq_refl /=.
rewrite /is_comp inE negb_or eq_sym Hi /=.
exact: intcompnP.
Qed.
Definition intcompn_cons i (Hi : i != 0%N) n (Hin : (i <= n)%N) c :=
  IntCompN (intcompn_cons_sub_proof c Hi Hin).

Lemma intcompn_behead_sub_proof i n (c : intcompn n) :
  i != 0%N -> (i <= n)%N ->
  is_comp_of_n (n - i)%N (if head 0%N c == i then behead c else rowcompn (n-i)).
Proof.
case: c => [[|c0 c] /= /andP [/eqP <- Hcomp]] Hi0 Hin.
  by exfalso; move: Hin Hi0; rewrite leqn0 => /eqP ->; rewrite eq_refl.
case: (altP (c0 =P i)) => Hc0 /=; last exact: rowcompnP.
subst c0; rewrite addKn eq_refl /=.
move: Hcomp; rewrite /is_comp inE; apply contra => ->.
by rewrite orbT.
Qed.
Definition intcompn_behead i (Hi : i != 0%N) n (Hin : (i <= n)%N) c :=
  IntCompN (intcompn_behead_sub_proof c Hi Hin).


Lemma part_sumn_count_bound b l :
  (sumn l < b)%N ->
  is_part l ->
  (\sum_(i < b | (i : nat) \in l) i * (count_mem (i : nat) l))%N = sumn l.
Proof.
move=> Hb; have {Hb} Hb : all (gtn b) l.
  elim: l Hb => //= l0 l IHl H; apply/andP; split.
  - exact: (leq_ltn_trans (leq_addr _ _) H).
  - by apply IHl; exact: (leq_ltn_trans (leq_addl _ _) H).
elim: l Hb => [_ _ | l0 l IHl]; first by apply big1.
move=> /andP [Hb /IHl{IHl}Hrec] Hpart.
move: Hb => /= Hl0b.
have /= Hl0 := part_head_non0 Hpart.
move: Hpart => /andP [_] /Hrec{Hrec}Hrec.
case: (boolP (l0 \in l)) => Hl0l.
- rewrite (eq_bigl (fun i : 'I_b => (i : nat) \in l)); first last.
    by move=> i; rewrite inE; case: (altP (i =P l0 :> nat)) => [-> |].
  rewrite (bigD1 (Ordinal Hl0b)) //=.
  rewrite eq_refl /= mulnDr muln1 -addnA; congr (_ + _)%N.
  (* TODO : Factorize *)
  rewrite (eq_bigr (fun i : 'I_b => i * (count_mem (i : nat) l)))%N;
      first last.
    move=> i /andP [_ Hi].
    have : (i : nat) != l0 by [].
    rewrite eq_sym => /negbTE ->.
    by rewrite add0n.
  by rewrite -Hrec [RHS](bigD1 (Ordinal Hl0b)).
- rewrite (bigD1 (Ordinal Hl0b)) //= ?inE eq_refl //=.
  rewrite (count_memPn Hl0l) addn0 muln1; congr (_ + _)%N.
  rewrite (eq_bigr (fun i : 'I_b => i * (count_mem (i : nat) l)))%N;
      first last.
    move=> i /andP [_ Hi].
    have : (i : nat) != l0 by [].
    rewrite eq_sym => /negbTE ->.
    by rewrite add0n.
  rewrite (eq_bigl (fun i : 'I_b => (i : nat) \in l)); first last.
    move=> i /=; rewrite inE; case: (altP (i =P l0 :> nat)) => [Hi | Hil0] /=.
    + subst l0; rewrite (negbTE Hl0l).
      by apply negbTE; rewrite negbK; apply/eqP/val_inj.
    + by case: ((i : nat) \in l).
  exact: Hrec.
Qed.

Lemma part_sumn_count l :
  is_part l ->
  (\sum_(i < (sumn l).+1 | (i : nat) \in l) i * (count_mem (i : nat) l))%N
  = sumn l.
Proof. by move/part_sumn_count_bound; apply. Qed.

Lemma coeff_symh_to_symp n (l : 'P_n) :
  [char R] =i pred0 ->
  (\sum_(c : intcompn n | perm_eq l c) \Pi c) = (zcard l)%:R^-1 :> R.
Proof.
rewrite charf0P => Hchar.
case: l => l /= /andP [/eqP].
elim: n {-2}n (leqnn n) l => [| m IHm] n.
  rewrite leqn0 => /eqP -> l /part0 H/H{H} ->{l}.
  rewrite zcard_nil /=.
  rewrite (eq_bigl (xpred1 (IntCompN (cnval := [::]) (n := 0%N) isT))); first last.
    move=> i; apply/idP/eqP => [Hperm | /(congr1 val)/= -> //].
    by apply val_inj => /=; apply/nilP; rewrite /nilp -(perm_eq_size Hperm).
  by rewrite big_pred1_eq.
rewrite leq_eqVlt => /orP [/eqP Hm|]; last by rewrite ltnS; exact: IHm.
move => l Hsum Hpart.
have head_intcompn (c : intcompn n) : (head 0 c < n.+1)%N.
  rewrite ltnS; case: c => [[|c0 c]] //= /andP [/eqP <- _].
  exact: leq_addr.
pose headcomp c := Ordinal (head_intcompn c).
rewrite (partition_big headcomp xpredT) //=.
transitivity (\sum_(j < n.+1)
                \sum_(i : intcompn n |
                 perm_eq l i && (head 0%N i == j :> nat)) \Pi i : R).
  by apply eq_bigr=> i _; apply eq_bigl => c.
rewrite (bigID (fun j : 'I_(n.+1) => (j : nat) \in l)) /=
        [X in _ + X]big1 ?addr0; first last.
  move=> i Hi; apply big1 => [] [[|c0 c] /= _ /andP [Hperm /eqP Hhead]]; exfalso.
  - by move/perm_sumn: Hperm; rewrite /= Hsum Hm.
  - subst c0; move/perm_eq_mem: Hperm Hi => /(_ i).
    by rewrite inE eq_refl /= => ->.
transitivity (\sum_(i < n.+1 | (i : nat) \in l)
               n%:R^-1 * (zcard (rem (i : nat) l))%:R^-1 : R).
  apply eq_bigr => /= i Hi.
  have H0i : i != 0%N :> nat.
    move: Hi; apply contraL => /eqP ->.
    by move: Hpart; rewrite is_part_sortedE => /andP [].
  have Hin : (i <= n)%N by rewrite -ltnS.
  rewrite (reindex (intcompn_cons H0i Hin)) /=; first last.
    exists (intcompn_behead H0i Hin) => c; rewrite inE => /andP [Hperm Hhead];
        apply val_inj; rewrite /= ?eq_refl //.
    rewrite /= Hhead.
    case: c Hperm Hhead => [[|c0 c]] //= _.
    + by move/perm_sumn; rewrite /= Hsum {1}Hm.
    + by move=> _ /eqP ->.
  rewrite (eq_bigl (fun c : intcompn (n - i)%N =>
                      perm_eq (rem (i : nat) l) c)); first last.
    move=> c; rewrite eq_refl andbT.
    have /perm_eqlP -> := perm_to_rem Hi.
    by rewrite perm_cons.
  transitivity (\sum_(c : intcompn (n - i)%N | perm_eq (rem (i : nat ) l) c)
                 n%:R^-1 * \Pi c : R).
    by apply eq_bigr => c _; rewrite intcompn_sumn subnKC // natrM invfM.
  rewrite -mulr_sumr IHm //.
  - rewrite -ltnS -Hm -{3}(subnK Hin).
    move: H0i; case i => [/= [//=|i']] _.
    by rewrite addnS ltnS leq_addr.
  - rewrite -[LHS](addKn i).
    have /perm_sumn /= <- := perm_to_rem Hi.
    by rewrite Hsum.
  - move: Hpart; rewrite !is_part_sortedE => /andP [Hsort H0].
    have Hrem := rem_subseq (i :nat) l; apply/andP; split.
    + exact: (subseq_sorted _ Hrem).
    + by move: H0; apply contra; apply (mem_subseq Hrem).
rewrite {IHm} -mulr_sumr.
transitivity (n%:R^-1 *
       (\sum_(i < n.+1 | (i : nat) \in l)
         (i * (count_mem (i : nat) l))%:R / (zcard l)%:R) : R).
  congr (_ * _); apply eq_bigr => i Hi.
  have H0i : i != 0%N :> nat.
    move: Hi; apply contraL => /eqP ->.
    by move: Hpart; rewrite is_part_sortedE => /andP [].
  rewrite -(zcard_rem H0i Hi) [X in _ / X]natrM invfM -[LHS]mul1r !mulrA.
  congr (_ * _); rewrite divff // Hchar.
  rewrite muln_eq0 negb_or H0i /=.
  by move: Hi; apply contraL => /eqP H; apply/count_memPn.
rewrite -mulr_suml mulrA -[RHS]mul1r; congr (_ * _).
rewrite -natr_sum -Hsum part_sumn_count // mulrC divff //.
by rewrite Hchar Hsum Hm.
Qed.

Lemma symh_to_symp n :
  [char R] =i pred0 ->
  'h_n = \sum_(l : 'P_n) (zcard l)%:R^-1 *: 'p[l] :> SF.
Proof.
move=> Hchar.
rewrite symh_to_symp_intpartn //; apply eq_bigr => l _.
by rewrite coeff_symh_to_symp.
Qed.

End ChangeBasisSymhPowerSum.


Section MPoESymHomog.

Variable (n0 : nat) (R : comRingType).
Local Notation n := (n0.+1).

Implicit Types p q r : {mpoly R[n]}.
Implicit Type m : 'X_{1..n}.

Lemma prod_homog nv l (dt : l.-tuple nat) (mt : l.-tuple {mpoly R[nv]}) :
  (forall i : 'I_l, tnth mt i \is (tnth dt i).-homog) ->
  \prod_(i <- mt) i \is (\sum_(i <- dt) i).-homog.
Proof using .
elim: l dt mt => [| l IHl] dt mt H.
  rewrite tuple0 big_nil tuple0 big_nil; exact: dhomog1.
case/tupleP: dt H => d dt.
case/tupleP: mt => p mt H /=.
rewrite !big_cons; apply dhomogM.
  by have := H ord0 => /=; rewrite (tnth_nth 0) (tnth_nth 0%N).
apply IHl => i.
have := H (inord i.+1).
rewrite !(tnth_nth 0) !(tnth_nth 0%N) /=.
by rewrite !inordK; last exact: (ltn_ord i).
Qed.

Local Notation E nv := [tuple mesym nv R i.+1  | i < n].

Lemma homog_X_mPo_elem (nv0 : nat) m :
  'X_[m] \mPo (E nv0.+1) \is (mnmwgt m).-homog.
Proof using .
rewrite comp_mpolyX.
pose dt := [tuple (i.+1 * (m i))%N | i < n].
pose mt := [tuple (mesym nv0.+1 R i.+1) ^+ m i | i < n] : n.-tuple {mpoly R[_]}.
rewrite (eq_bigr (fun i : 'I_n => tnth mt i)); first last.
  by move=> k _ /=; rewrite !tnth_mktuple.
rewrite -(big_tuple _ _ mt xpredT id).
rewrite /mnmwgt (eq_bigr (fun i : 'I_n => tnth dt i)); first last.
  by move=> k _ /=; rewrite !tnth_mktuple mulnC.
rewrite -(big_tuple _ _ dt xpredT id).
apply prod_homog => k.
rewrite !tnth_mktuple {mt dt}; apply: dhomogMn.
exact: mesym_homog.
Qed.

Lemma pihomog_mPo nv0 p d :
  pihomog [measure of mdeg] d (p \mPo (E nv0.+1)) =
  (pihomog [measure of mnmwgt] d p) \mPo (E nv0.+1).
Proof using .
elim/mpolyind: p => [| c m p Hm Hc IHp] /=; first by rewrite !linear0.
rewrite !linearP /= {}IHp; congr (c *: _ + _).
case: (altP (mnmwgt m =P d)) => Hd.
- have/eqP := Hd; rewrite -(dhomogX R) => /pihomog_dE ->.
  by have:= homog_X_mPo_elem nv0 m; rewrite Hd => /pihomog_dE ->.
- rewrite (pihomog_ne0 Hd (homog_X_mPo_elem nv0 m)).
  rewrite (pihomog_ne0 Hd); first by rewrite linear0.
  by rewrite dhomogX.
Qed.

Lemma mwmwgt_homogP (p : {mpoly R[n]}) d :
  reflect
    (forall nv, p \mPo (E nv.+1) \is d.-homog)
    (p \is d.-homog for [measure of mnmwgt]).
Proof using.
rewrite !homog_piE.
apply (iffP eqP) => [Homog nv | H].
- by rewrite -Homog -pihomog_mPo pihomogP.
- apply pihomog_dE.
  suff -> : p = pihomog [measure of mnmwgt] d p by apply: pihomogP.
  apply msym_fundamental_un; apply esym.
  by rewrite -pihomog_mPo; apply pihomog_dE.
Qed.

Lemma sym_fundamental_homog (p : {mpoly R[n]}) (d : nat) :
  p \is symmetric -> p \is d.-homog ->
  { t | t \mPo (E n) = p /\ t \is d.-homog for [measure of mnmwgt] }.
Proof.
move=> /sym_fundamental [t [Ht _]] Hhom.
exists (pihomog [measure of mnmwgt] d t); split.
- by rewrite -pihomog_mPo Ht pihomog_dE.
- exact: pihomogP.
Qed.

End MPoESymHomog.


Section SymPolF.

Variable R : comRingType.
Variable m : nat.
Implicit Type p : {sympoly R[m]}.

Local Notation E := [tuple syme m R i.+1 | i < m.+1].
Local Notation SF p := (sym_fundamental (sympol_is_symmetric p)).

Definition sympolyf p := let: exist t _  := SF p in t.

Lemma sympolyf_is_lrmorphism : lrmorphism sympolyf.
Proof.
rewrite /sympolyf; repeat split.
- move=> u v.
  case: (SF (u - v)) (SF u) (SF v) => [puv [Hpuv _]] [pu [Hpu _]] [pv [Hpv _]].
  by apply msym_fundamental_un; rewrite [RHS]raddfB /= Hpu Hpv Hpuv.
- move=> u v.
  case: (SF (u * v)) (SF u) (SF v) => [puv [Hpuv _]] [pu [Hpu _]] [pv [Hpv _]].
  apply msym_fundamental_un.
  by rewrite [RHS]rmorphM /= -/(pu \mPo _) -/(pv \mPo _) Hpu Hpv Hpuv.
- case: (SF 1) => [p1 [Hp1 _]].
  by apply msym_fundamental_un; rewrite Hp1 comp_mpoly1.
- move=> a u.
  case: (SF (a *: u)) (SF u) => [pau [Hpau _]] [pu [Hpu _]].
  by apply msym_fundamental_un; rewrite linearZ /= Hpau Hpu.
Qed.
Canonical sympolyf_additive   := Additive   sympolyf_is_lrmorphism.
Canonical sympolyf_rmorphism  := RMorphism  sympolyf_is_lrmorphism.
Canonical sympolyf_linear     := AddLinear  sympolyf_is_lrmorphism.
Canonical sympolyf_lrmorphism := LRMorphism sympolyf_is_lrmorphism.

End SymPolF.

Local Close Scope Combi_scope.

Section ChangeNVar.

Variable R : comRingType.
Variable m0 n0 : nat.
Local Notation m := m0.+1.
Local Notation n := n0.+1.
Local Notation SF p := (sym_fundamental (sympol_is_symmetric p)).
Local Notation E := [tuple mesym n R i.+1 | i < m].

Lemma cnvarsym_subproof (p : {sympoly R[m]}) : sympolyf p \mPo E \is symmetric.
Proof. by apply mcomp_sym => i; rewrite -tnth_nth tnth_mktuple mesym_sym. Qed.
Definition cnvarsym p : {sympoly R[n]} := SymPoly (cnvarsym_subproof p).

Lemma cnvarsym_is_lrmorphism : lrmorphism cnvarsym.
Proof.
rewrite /cnvarsym; repeat split.
- by move=> u v; apply val_inj; rewrite /= !raddfB.
- by move=> u v; apply val_inj; rewrite /= !rmorphM.
- by apply val_inj; rewrite /= /comp_mpoly !rmorph1.
- by move=> a u; apply val_inj; rewrite /= !linearZ.
Qed.
Canonical cnvarsym_additive   := Additive   cnvarsym_is_lrmorphism.
Canonical cnvarsym_rmorphism  := RMorphism  cnvarsym_is_lrmorphism.
Canonical cnvarsym_linear     := AddLinear  cnvarsym_is_lrmorphism.
Canonical cnvarsym_lrmorphism := LRMorphism cnvarsym_is_lrmorphism.

Lemma cnvar_leq_symeE i : (i <= m)%N -> cnvarsym 'e_i = 'e_i.
Proof.
move=> Hi; apply val_inj; rewrite /= /sympolyf.
case: (SF 'e_i) => /= p [Hp _].
case: i Hi Hp => [_ |i Hi Hp] /=.
  rewrite !mesym0E /= => Hp.
  have {Hp} -> : p = 1 by apply msym_fundamental_un; rewrite Hp comp_mpoly1.
  by rewrite comp_mpoly1.
have {Hp} -> : p = 'X_(Ordinal Hi).
  apply msym_fundamental_un; rewrite Hp comp_mpolyXU.
  by rewrite -tnth_nth tnth_mktuple.
by rewrite comp_mpolyXU -tnth_nth tnth_mktuple.
Qed.

Lemma cnvarsyme i : (i <= m)%N || (n <= m)%N -> cnvarsym 'e_i = 'e_i.
Proof.
move=> /orP [] H; first exact: cnvar_leq_symeE.
case: (ssrnat.leqP i m) => [] H1; first exact: cnvar_leq_symeE.
by rewrite !syme_geqnE ?raddf0 // (leq_ltn_trans H H1).
Qed.

Lemma cnvarsymh i : (i <= m)%N || (n <= m)%N -> cnvarsym 'h_i = 'h_i.
Proof.
move=> Hi; rewrite !symh_to_syme.
rewrite linear_sum /=; apply eq_bigr => la _.
rewrite linearZ rmorph_prod /=; congr(_ *: _); apply eq_big_seq => j Hj.
apply cnvarsyme.
move: Hi => /orP [Hi | ->]; last by rewrite orbT.
apply/orP; left; apply: (leq_trans _ Hi).
have:= (intpartn_sumn la); rewrite -sumnE (big_rem j Hj) /= => <-.
exact: leq_addr.
Qed.

Lemma cnvarsymp i : (i < m)%N || (n <= m)%N -> cnvarsym 'p_i.+1 = 'p_i.+1.
Proof.
elim: i {-2}i (leqnn i) => [/= | i IHi] d.
  rewrite leqn0 => /eqP -> H.
  by rewrite !sympe1E cnvarsyme.
rewrite leq_eqVlt => /orP [/eqP ->{d} | ] Hi; last exact: IHi.
have:= Newton_symh m0 R i.+2 => /(congr1 cnvarsym).
rewrite linearZ /= cnvarsymh // Newton_symh.
rewrite big_ltn // symh0 mul1r subn0 => /esym.
rewrite linear_sum big_ltn //= rmorphM /= symh0 rmorph1 mul1r subn0.
suff -> : \sum_(1 <= j < i.+2) cnvarsym ('h_j * 'p_(i.+2 - j)) =
          \sum_(1 <= j < i.+2) 'h_j * 'p_(i.+2 - j).
  by apply: addIr.
rewrite !big_nat; apply eq_bigr => d /andP [H0d Hd].
rewrite rmorphM /= cnvarsymh; first last.
  move: Hi => /orP [Hi | ->]; last by rewrite orbT.
  by apply/orP; left; exact: (leq_trans (ltnW Hd) Hi).
congr (_ * _); rewrite subSn //; apply IHi.
- case: d H0d Hd => d //= _ _.
  by rewrite subSS; apply leq_subr.
- move: Hi => /orP [Hi | ->]; last by rewrite orbT.
  apply/orP; left; apply: (leq_trans _ Hi).
  by rewrite ltnS; apply leq_subr.
Qed.

Section ProdGen.

Variable Gen : forall nvar d : nat, {sympoly R[nvar]}.
Hypothesis Hcnvargen :
  forall d : nat, (d < m)%N || (n <= m)%N -> cnvarsym (Gen _ d.+1) = (Gen _ d.+1).

Lemma cnvar_prodgen d (la : 'P_d) :
  (d <= m)%N || (n <= m)%N ->
  cnvarsym (prod_gen (Gen _) la) = prod_gen (Gen _) la.
Proof.
move=> Hd; rewrite /prod_gen rmorph_prod.
apply eq_big_seq => i /mem_intpartn /andP [H0i Hi].
case: i H0i Hi => //= i _ Hi; apply Hcnvargen.
move: Hd => /orP [Hd | ->]; last by rewrite orbT.
by apply/orP; left; apply: (leq_trans Hi Hd).
Qed.

End ProdGen.

Variable d : nat.

Hypothesis Hd : (d <= m)%N || (n <= m)%N.

Lemma cnvar_prodsyme (la : 'P_d) : cnvarsym 'e[la] = 'e[la].
Proof.
rewrite /prod_syme; apply (@cnvar_prodgen (syme^~ R)); last by [].
by move=> i Hi; apply: cnvarsyme.
Qed.

Lemma cnvar_prodsymh (la : 'P_d) : cnvarsym 'h[la] = 'h[la].
Proof.
rewrite /prod_symh; apply (@cnvar_prodgen (symh^~ R)); last by [].
by move=> i Hi; apply: cnvarsymh.
Qed.

Lemma cnvar_prodsymp (la : 'P_d) : cnvarsym 'p[la] = 'p[la].
Proof.
rewrite /prod_symp; apply (@cnvar_prodgen (symp^~ R)); last by [].
by move=> i Hi; apply: cnvarsymp.
Qed.

Lemma cnvar_syms (la : 'P_d) : cnvarsym 's[la] = 's[la].
Proof.
rewrite !syms_symh linear_sum; apply eq_bigr => mu _.
by rewrite linearZ /= cnvar_prodsymh.
Qed.

Lemma cnvar_symm (la : 'P_d) : cnvarsym 'm[la] = 'm[la].
Proof.
rewrite !symm_syms linear_sum; apply eq_bigr => mu _.
by rewrite linearZ /= cnvar_syms.
Qed.

End ChangeNVar.
