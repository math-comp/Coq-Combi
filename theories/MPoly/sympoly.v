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
From mathcomp Require Import tuple finfun finset bigop ssralg path perm fingroup.
From SsrMultinomials Require Import ssrcomplements poset freeg bigenough mpoly.

Require Import tools ordtype permuted partition Yamanouchi std tableau stdtab antisym.

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
Variable R : ringType.
Implicit Type m : 'X_{1.. n}.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").


(* From  mpoly.v : \sum_(h : {set 'I_n} | #|h| == k) \prod_(i in h) 'X_i. *)
Fact syme_sym d : mesym n R d \is symmetric.
Proof using. exact: mesym_sym. Qed.
Definition syme d : {sympoly R[n]} := SymPoly (syme_sym d).
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
Lemma symm_homog d (sh : intpartn d) :
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

Lemma symm_genE (p : {sympoly R[n]}) :
  p = \sum_(m <- msupp p | m \is dominant) p@_m *: symm (partm m).
Proof. by apply val_inj => /=; apply issym_symmE. Qed.


Lemma size_mpart_in_supp (f : {mpoly R[n]}) d (p : intpartn d) :
  f \is d.-homog -> mpart p \in msupp f -> size p <= n.
Proof.
rewrite /mpart; case: leqP => //= H1 /dhomogP H/H /=.
rewrite /= mdeg0 => Hd; subst d.
by move: H1; rewrite intpartn0.
Qed.

Lemma homog_symmE d (p : {sympoly R[n]}) :
  sympol p \is d.-homog ->
  p = \sum_(l : intpartn d) p@_(mpart l) *: symm l.
Proof.
move=> Hhomog; rewrite {1}(symm_genE p).
apply val_inj => /=.
rewrite !linear_sum /=  (bigID (fun i : intpartn d => mpart i \in msupp p)) /=.
rewrite [X in _ + X]big1 ?addr0;
  last by move=> i /memN_msupp_eq0 ->; rewrite scale0r.
rewrite (eq_bigr (fun i : intpartn d =>
           p@_(mpart i) *:
            sympol (symm (partm (n := n) (mpart i)))));
    first last.
  move=> i Hi; congr (_ *: _); congr sympol; congr symm.
  by rewrite mpartK //; apply (size_mpart_in_supp Hhomog Hi).
rewrite /index_enum -enumT.
transitivity (\sum_(m <- [seq mpart (i : intpartn d) |
                          i <- enum (intpartn_finType d)] |
                    m \in msupp p)
      p@_m *: sympol (symm (partm m))); last by rewrite big_map /=.
rewrite -big_filter -[RHS]big_filter; apply eq_big_perm; apply uniq_perm_eq.
- by apply filter_uniq; apply msupp_uniq.
- rewrite filter_map map_inj_in_uniq; first by apply filter_uniq; apply enum_uniq.
  move=> /= c1 c2; rewrite !mem_filter /= => /andP [Hc1 _] /andP [Hc2 _].
  move=> /(congr1 (@partm n)) /(congr1 val) /=.
  rewrite !mpartK // ?(size_mpart_in_supp _ Hc1) ?(size_mpart_in_supp _ Hc2) //.
  exact: val_inj.
- move=> /= m; rewrite !mem_filter andbC.
  case: (boolP (m \in msupp p)) => //= Hsupp.
  apply/idP/mapP => /= [Hdom | [l _ ->]]; last exact: mpart_is_dominant.
  have Hp : is_part_of_n d (partm m).
    rewrite /is_part_of_n /= intpartP andbT sumn_partm //.
    by move: Hhomog => /dhomogP/(_ _ Hsupp) /= ->.
  exists (IntPartN Hp); first by rewrite mem_enum.
  by rewrite /= partmK.
Qed.

Lemma symm_unique d (p : {sympoly R[n]}) c :
  p = \sum_(l : intpartn d) (c l) *: symm l ->
  forall l : intpartn d, (size l <= n)%N -> c l = p@_(mpart l).
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
  \sum_(l : intpartn d) (c l) *: symm l = 0 ->
  forall l : intpartn d, (size l <= n)%N -> c l = 0.
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
Lemma syme1 : syme 1 = \sum_(i < n) 'X_i :> {mpoly R[n]}.
Proof using. by rewrite /= mesym1E. Qed.

Lemma symp1 : symp 1 = \sum_(i < n) 'X_i :> {mpoly R[n]}.
Proof using. by apply eq_bigr => i _; rewrite expr1. Qed.

Lemma symh1 : symh 1 = \sum_(i < n) 'X_i :> {mpoly R[n]}.
Proof using.
rewrite /symh -mpolyP => m.
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
Implicit Type m : 'X_{1.. n}.

Section Defs.

Variable gen : nat -> {sympoly R[n]}.
Hypothesis gen_homog : forall d, sympol (gen d) \is d.-homog.

Definition prod_gen d (sh : intpartn d) := \prod_(i <- sh) gen i.
Lemma prod_gen_homog d (sh : intpartn d) :
  sympol (prod_gen sh) \is d.-homog.
Proof using gen_homog.
rewrite /prod_gen; case: sh => sh /= /andP [/eqP <- _] {d}.
elim: sh => [| d sh IHsh] /=; first by rewrite big_nil /= dhomog1.
by rewrite big_cons; apply dhomogM; first exact: gen_homog.
Qed.

Lemma prod_genM c d (l : intpartn c) (k : intpartn d) :
  (prod_gen l) * (prod_gen k) = (prod_gen (union_intpartn l k)).
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

End ProdGen.

Notation "''e[' k ]" := (prod_syme _ _ k)
                              (at level 8, k at level 2, format "''e[' k ]").
Notation "''h[' k ]" := (prod_symh _ _ k)
                              (at level 8, k at level 2, format "''h[' k ]").
Notation "''p[' k ]" := (prod_symp _ _ k)
                              (at level 8, k at level 2, format "''p[' k ]").
Notation "''m[' k ]" := (symm _ _ k)
                              (at level 8, k at level 2, format "''m[' k ]").



Require Import composition.

Section ChangeBasis.

Variable nvar : nat.
Variable R : comRingType.

Local Notation "''XX'" := 'X_{1.. nvar}.
Local Notation "''XX_' m " := 'X_{1.. nvar < (mdeg m).+1, (mdeg m).+1} (at level 0).
Implicit Type m : 'XX.
Local Notation SF := {sympoly R[nvar]}.

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
  pose f := (fun mm : 'XX => [set j | mm j != 0%N] : {set 'I_nvar}).
  pose g := (fun S : {set 'I_nvar} => [multinom (i \in S : nat) | i < nvar]).
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

Lemma syme_symhE (d : nat) :
  d != 0%N ->
  'e_d = \sum_(1 <= i < d.+1) 'h_i * ((-1)^+i.-1 *: 'e_(d - i)) :> SF.
Proof.
move=> Hd.
have := sum_symh_syme Hd.
rewrite big_nat_recl // expr0 scale1r symh0 mul1r subn0 => /eqP.
rewrite (addr_eq0 'e_d) => /eqP ->; rewrite big_add1 /= -sumrN.
rewrite !big_nat; apply eq_bigr => i /= Hi.
rewrite scalerAr -mulrN; congr (_ * _).
rewrite -scaleNr; congr (_ *: _).
by rewrite exprS mulN1r opprK.
Qed.

Lemma syme_to_symh_partsum n :
  'e_n = \sum_(c : intcompn n) (-1)^+(n - size c) *: (\prod_(i <- c) 'h_i) :> SF.
Proof.
rewrite /index_enum -enumT /=.
rewrite -[RHS](big_map (@cnval n) xpredT
   (fun c : seq nat => (-1)^+(n - size c) *: \prod_(i <- c) 'h_i)).
rewrite enum_intcompnE.
elim: n {-2}n (leqnn n) => [| m IHm] n.
  rewrite leqn0 => /eqP ->.
  by rewrite /enum_compn /= big_seq1 /= subnn expr0 scale1r big_nil syme0.
rewrite leq_eqVlt => /orP [/eqP Hm|]; last by rewrite ltnS; exact: IHm.
rewrite enum_compnE Hm // -Hm big_flatten /=.
rewrite syme_symhE; last by rewrite Hm.
rewrite big_map /index_iota subSS subn0; apply eq_big_seq => i.
rewrite mem_iota add1n ltnS => /andP [Hi Hin].
rewrite big_map.
rewrite (eq_big_seq
    (fun c : seq nat => - 'h_i * ((-1) ^+ (n - size c) *: \prod_(i0 <- c) 'h_i0)));
  first last.
  move=> s; rewrite -enum_compnP /is_comp_of_n /= => /andP [/eqP Hsum Hn0].
  rewrite big_cons -scalerAr mulNr scalerN -scaleNr; congr (_ *: _).
  subst n; rewrite subSS subSn; first last.
    apply (leq_trans (size_comp Hn0)); rewrite {}Hsum.
    case: i Hi {Hin} => // i' _.
    by rewrite subSS leq_subr.
  by rewrite exprS mulN1r opprK.
rewrite -mulr_sumr.
case: (altP (n-i =P 0)%N) => [/eqP | Hni] /=.
  rewrite subn_eq0 => Hni.
  have -> : i = n by apply anti_leq; rewrite Hin Hni.
  subst n => /=.
  rewrite subnn /enum_compn /= big_seq1 big_nil /=.
  rewrite subn0 syme0 mulNr -mulrN -scaleNr; congr (_ * (_)%:A).
  by rewrite exprS mulN1r opprK.
rewrite {}IHm //; first last.
  rewrite Hm; case: i Hi {Hin Hni} => // i' _.
  by rewrite subSS leq_subr.
rewrite scaler_sumr mulNr -mulrN -sumrN; congr (_ * _).
apply eq_big_seq => s.
rewrite -enum_compnP /is_comp_of_n /= => /andP [/eqP Hsum Hn0].
rewrite scalerA -scaleNr; congr (_ *: _).
subst n; rewrite -exprD.
move: Hni; rewrite subn_eq0 -leqNgt => {Hin} Hin.
rewrite subSn //.
case: i Hi Hsum Hin => // i _.
rewrite subSS => Hsum Him /=.
have Hsz : size s <= m.
  by apply (leq_trans (size_comp Hn0)); rewrite {}Hsum leq_subr.
rewrite -subSn // subSS subSn // exprS mulN1r opprK.
rewrite subnAC subnKC //.
have:= size_comp Hn0; rewrite Hsum.
rewrite -!subn_eq0 !subnBA //; last exact: ltnW.
by rewrite addnC.
Qed.


(** * Newton formula. *)
Lemma mult_symh_U k d i m :
  (('h_k : {mpoly R[nvar]}) * 'X_i ^+ d)@_m =
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
  (mdeg m == (k + d)%N)%:R * \sum_(i < nvar) (m i >= d)%:R.
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
                \sum_(j < nvar) (m j >= (k - i)%N)%:R)) /=; first last.
  move=> i Hi /=; rewrite mult_symh_powersum.
  by rewrite subnKC //; apply ltnW.
rewrite -big_nat -mulr_sumr mulrC.
case: (altP (mdeg m =P k)) => Hdegm; rewrite /= ?mul1r ?mul0r //.
rewrite exchange_big /=.
rewrite (eq_bigr (fun i : 'I_nvar => (m i)%:R)).
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

From mathcomp Require Import ssrnum.

Section ChangeBasisSymhPowerSum.

Import Num.Theory.

Variable R : numFieldType.
Variable nvar : nat.
Local Notation SF := {sympoly R[nvar]}.

Fixpoint prod_partsum (s : seq nat) :=
  if s is _ :: s' then (sumn s * prod_partsum s')%N else 1%N.

Local Notation "\Pi s" := (prod_partsum s)%:R^-1 (at level 0, s at level 2).

Lemma symh_to_symp_prod_partsum n :
  'h_n = \sum_(c : intcompn n) \Pi c *: \prod_(i <- c) 'p_i :> SF.
Proof using.
rewrite /index_enum -enumT /=.
rewrite -[RHS](big_map (@cnval n) xpredT
   (fun c : seq nat => \Pi c *: \prod_(i <- c) 'p_i)).
rewrite enum_intcompnE.
elim: n {-2}n (leqnn n) => [| m IHm] n.
  rewrite leqn0 => /eqP ->.
  by rewrite big_seq1 big_nil symh0 /= invr1 scale1r.
rewrite leq_eqVlt => /orP [/eqP Hm|]; last by rewrite ltnS; exact: IHm.
rewrite enum_compnE Hm // -Hm big_flatten /=.
have Hn : (n%:R : R) != 0 by rewrite pnatr_eq0 Hm.
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
  'h_n = \sum_(l : intpartn n)
           (\sum_(c : intcompn n | perm_eq l c) \Pi c) *: 'p[l] :> SF.
Proof.
rewrite symh_to_symp_prod_partsum.
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

Lemma coeff_symh_to_symp n (l : intpartn n) :
  (\sum_(c : intcompn n | perm_eq l c) \Pi c) = (zcard l)%:R^-1 :> R.
Proof.
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
  transitivity (\sum_(c : intcompn (n - i)%N | perm_eq (rem (i :nat ) l) c)
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
  rewrite -(zcard_rem H0i Hi) [X in _/X]natrM invfM -[LHS]mul1r !mulrA.
  congr (_ * _); rewrite divff // pnatr_eq0.
  rewrite muln_eq0 negb_or H0i /=.
  by move: Hi; apply contraL => /eqP H; apply/count_memPn.
rewrite -mulr_suml mulrA -[RHS]mul1r; congr (_ * _).
rewrite -natr_sum -Hsum part_sumn_count // mulrC divff //.
by rewrite Hsum Hm pnatr_eq0.
Qed.

Lemma symh_to_symp n :
  'h_n = \sum_(l : intpartn n) (zcard l)%:R^-1 *: 'p[l] :> SF.
Proof.
rewrite symh_to_symp_intpartn; apply eq_bigr => l _.
by rewrite coeff_symh_to_symp.
Qed.

End ChangeBasisSymhPowerSum.


Section Schur.

Variable n0 : nat.
Local Notation n := n0.+1.
Variable R : ringType.

Definition Schur d (sh : intpartn d) : {mpoly R[n]} :=
  \sum_(t : tabsh n0 sh) \prod_(v <- to_word t) 'X_v.

Lemma Schur_tabsh_readingE  d (sh : intpartn d) :
  Schur sh =
  \sum_(t : d.-tuple 'I_n | tabsh_reading sh t) \prod_(v <- t) 'X_v.
Proof using.
rewrite /Schur /index_enum -!enumT.
pose prodw := fun w => \prod_(v <- w) 'X_v : {mpoly R[n]}.
rewrite -[LHS](big_map (fun t => to_word (val t)) xpredT prodw).
rewrite -[RHS](big_map val (tabsh_reading sh) prodw).
rewrite -[RHS]big_filter.
by rewrite (eq_big_perm _ (to_word_enum_tabsh _ sh)).
Qed.

Lemma Schur0 (sh : intpartn 0) : Schur sh = 1.
Proof using.
rewrite Schur_tabsh_readingE (eq_bigl (xpred1 [tuple])); first last.
  by move=> i /=; rewrite tuple0 [RHS]eq_refl intpartn0.
by rewrite big_pred1_eq big_nil.
Qed.

Lemma Schur_oversize d (sh : intpartn d) : (size sh > n)%N -> Schur sh = 0.
Proof using.
move=> Hn; apply big1 => t _; exfalso.
have:= size_tabsh t; rewrite -(size_map size) -/(shape t) shape_tabsh.
by move=> /(leq_trans Hn); rewrite ltnn.
Qed.



Lemma tabwordshape_row d (w : d.-tuple 'I_n) :
  tabsh_reading (rowpartn d) w = sorted leq [seq val i | i <- w].
Proof using.
rewrite /tabsh_reading /= /rowpart ; case: w => w /=/eqP Hw.
case: d Hw => [//= | d] Hw; rewrite Hw /=; first by case: w Hw.
rewrite addn0 eq_refl andbT //=.
case: w Hw => [//= | w0 w] /= /eqP; rewrite eqSS => /eqP <-.
rewrite take_size; apply esym; apply (map_path (b := pred0)) => /=.
- move=> i j /= _ ; exact: leqXnatE.
- by apply/hasPn => x /=.
Qed.


Lemma perm_eq_enum_basis d :
  perm_eq [seq s2m (val s) | s <- enum (basis n d)]
          [seq val m | m <- enum [set m : 'X_{1..n < d.+1} | mdeg m == d]].
Proof using.
apply uniq_perm_eq.
- rewrite map_inj_in_uniq; first exact: enum_uniq.
  move=> i j; rewrite !mem_enum => Hi Hj; exact: inj_s2m.
- rewrite map_inj_uniq; [exact: enum_uniq | exact: val_inj].
move=> m; apply/mapP/mapP => [[] s | [] mb].
- rewrite mem_enum inE /= => Hsort ->.
  have mdegs : mdeg (s2m s) = d.
    rewrite /s2m /mdeg mnm_valK /= big_map enumT -/(index_enum _).
    by rewrite combclass.sum_count_mem count_predT size_tuple.
  have mdegsP : (mdeg (s2m s) < d.+1)%N by rewrite mdegs.
  exists (BMultinom mdegsP) => //.
  by rewrite mem_enum inE /= mdegs.
- rewrite mem_enum inE => /eqP Hmb ->.
  have Ht : size (m2s mb) == d by rewrite -{2}Hmb size_m2s.
  exists (Tuple Ht) => /=; last by rewrite s2mK.
  rewrite mem_enum inE /=; exact: srt_m2s.
Qed.

(** Equivalent definition of symh symmetric function *)
Lemma symh_basisE d :
  \sum_(s in (basis n d)) 'X_[s2m s] = Schur (rowpartn d).
Proof using.
rewrite Schur_tabsh_readingE (eq_bigl _ _ (@tabwordshape_row d)).
rewrite [RHS](eq_bigr (fun s : d.-tuple 'I_n => 'X_[s2m s])); first last.
  move=> [s _] /= _; rewrite /s2m; elim: s => [| s0 s IHs]/=.
    by rewrite big_nil -/mnm0 mpolyX0.
  rewrite big_cons {}IHs -mpolyXD; congr ('X_[_]).
  by rewrite mnmP => i; rewrite mnmDE !mnmE.
by apply eq_bigl => m; rewrite inE /=.
Qed.
End Schur.


Section SchurComRingType.

Variable n0 : nat.
Local Notation n := (n0.+1).
Variable R : comRingType.

Lemma symhE d : symh n R d = Schur n0 R (rowpartn d) :> {mpoly R[n]}.
Proof using.
rewrite /= -symh_basisE /symh_pol /symh_pol_bound.
rewrite -(big_map (@bmnm n d.+1) (fun m => mdeg m == d) (fun m => 'X_[m])).
rewrite /index_enum -enumT -big_filter.
rewrite [filter _ _](_ : _ =
    [seq val m | m <- enum [set m : 'X_{1..n < d.+1} | mdeg m == d]]);
    first last.
  rewrite /enum_mem filter_map -filter_predI; congr map.
  by apply eq_filter => s /=; rewrite !inE andbT.
rewrite -(eq_big_perm _ (perm_eq_enum_basis _ d)) /=.
by rewrite big_map -[RHS]big_filter.
Qed.

Lemma tabwordshape_col d (w : d.-tuple 'I_n) :
  tabsh_reading (colpartn d) w = sorted gtnX w.
Proof using.
rewrite /tabsh_reading /= /colpart ; case: w => w /=/eqP Hw.
have -> : sumn (nseq d 1%N) = d.
  by elim: d {Hw} => //= d /= ->; rewrite add1n.
rewrite Hw eq_refl /= rev_nseq.
have -> : rev (reshape (nseq d 1%N) w) = [seq [:: i] | i <- rev w].
  rewrite map_rev; congr rev.
  elim: d w Hw => [| d IHd] //=; first by case.
  case => [| w0 w] //= /eqP; rewrite eqSS => /eqP /IHd <-.
  by rewrite take0 drop0.
rewrite -rev_sorted.
case: {w} (rev w) {d Hw} => [|w0 w] //=.
elim: w w0 => [//= | w1 w /= <-] w0 /=.
by congr andb; rewrite /dominate /= andbT {w}.
Qed.

(** The definition of syme symmetric polynomials as column Schur
    function agrees with the one from mpoly *)
Lemma symeE d :
  syme n R d = Schur n0 R (colpartn d) :> {mpoly R[n]}.
Proof using.
rewrite /= mesym_tupleE /tmono /syme Schur_tabsh_readingE.
rewrite (eq_bigl _ _ (@tabwordshape_col d)).
set f := BIG_F.
rewrite (eq_bigr (fun x => f (rev_tuple x))) /f {f}; first last.
  by move => i _ /=; apply: eq_big_perm; exact: perm_eq_rev.
rewrite (eq_bigl (fun i => sorted gtnX (rev_tuple i))); first last.
  move=> [t /= _]; rewrite rev_sorted.
  case: t => [//= | t0 t] /=.
  apply: (map_path (b := pred0)) => [x y /= _|].
  + by rewrite -ltnXnatE.
  + by apply/hasPn => x /=.
rewrite [RHS](eq_big_perm
                (map (@rev_tuple _ _)
                     (enum (tuple_finType d (ordinal_finType n))))) /=.
  by rewrite big_map /=; first by rewrite /index_enum /= enumT.
apply uniq_perm_eq.
- rewrite /index_enum -enumT; exact: enum_uniq.
- rewrite map_inj_uniq; first exact: enum_uniq.
  apply (can_inj (g := (@rev_tuple _ _))).
  by move=> t; apply val_inj => /=; rewrite revK.
- rewrite /index_enum -enumT /= => t.
  rewrite mem_enum /= inE; apply esym; apply/mapP.
  exists (rev_tuple t) => /=.
  + by rewrite mem_enum.
  + by apply val_inj; rewrite /= revK.
Qed.

Lemma Schur1 (sh : intpartn 1) : Schur n0 R sh = \sum_(i < n) 'X_i.
Proof using.
suff -> : sh = rowpartn 1 by rewrite -symhE symh1.
by apply val_inj => /=; exact: intpartn1.
Qed.

End SchurComRingType.


Section ScalarChange.

Variables R S : comRingType.
Variable mor : {rmorphism R -> S}.
Variable n : nat.

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
Canonical map_sympoly_rmorphism := RMorphism map_sympoly_is_rmorphism.

Lemma scale_map_sympoly (r : R) (p : {sympoly R[n]}) :
  map_sympoly (r *: p) = (mor r) *: (map_sympoly p).
Proof.
apply val_inj => /=.
rewrite (mpolyE p) raddf_sum /=.
apply/mpolyP => m.
rewrite mcoeffZ !mcoeff_map_mpoly /= -!rmorphM /=; congr (mor _).
rewrite !linear_sum /= mulr_sumr.
apply eq_bigr => i _ /=.
by rewrite !linearZ /=.
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
Lemma map_syme_prod d (l : intpartn d) : map_sympoly 'e[l] = 'e[l].
Proof.
by rewrite rmorph_prod; apply eq_bigr => i _; exact: map_syme.
Qed.

Lemma map_symh d : map_sympoly 'h_d = 'h_d.
Proof.
apply val_inj; rewrite /= /symh_pol rmorph_sum /=.
by apply eq_bigr => X _; rewrite map_mpolyX.
Qed.
Lemma map_symh_prod d (l : intpartn d) : map_sympoly 'h[l] = 'h[l].
Proof.
by rewrite rmorph_prod; apply eq_bigr => i _; exact: map_symh.
Qed.

Lemma map_symp d : map_sympoly 'p_d = 'p_d.
Proof.
apply val_inj; rewrite /= /symp_pol rmorph_sum /=.
by apply eq_bigr => X _; rewrite rmorphX /= map_mpolyX.
Qed.
Lemma map_symp_prod d (l : intpartn d) : map_sympoly 'p[l] = 'p[l].
Proof.
by rewrite rmorph_prod; apply eq_bigr => i _; exact: map_symp.
Qed.

End ScalarChange.


From mathcomp Require Import poly.
Section KillLastVar.

Variable R : comRingType.
Variable n : nat.

Definition restr : {mpoly R[n.+1]} -> {mpoly R[n]} := coefp 0 \o (@muni n R).

Lemma restr_is_linear : scalable restr.
Proof.
rewrite /restr => /= a p.
by rewrite [coefp 0]lock /= muniZ; unlock; rewrite linearZ -mul_mpolyC.
Qed.
Canonical restr_linear := AddLinear restr_is_linear.

(* This is an algebra morphism [rmorphism of restr]. *)

Lemma lift_ord_max (i : 'I_n) :
  fintype.lift ord_max i = i :> nat.
Proof. by rewrite /= /bump leqNgt ltn_ord add0n. Qed.

Lemma widen_lift (i : 'I_n) :
  widen_ord (leqnSn n) i = fintype.lift ord_max i.
Proof. by apply val_inj; rewrite [RHS]lift_ord_max. Qed.

Lemma restrX0 (m : 'X_{1..n.+1}) : m ord_max != 0%N -> restr 'X_[m] = 0.
Proof.
rewrite /restr /= muniE msuppX big_seq1 mcoeffX eq_refl scale1r => Hm.
move: ('X_[[multinom _ | i < n]]) => C.
case: (altP (C =P 0)) => [-> | HC]; first by rewrite scale0r polyseq0.
case: (m ord_max) Hm => //= d.
rewrite -[C *: _]mulr_algl polyseqMXn /= ?scaler0 //.
by rewrite alg_polyC polyC_eq0.
Qed.

Lemma mpolyX_neq0 nv (m : 'X_{1..nv}) : 'X_[m] != 0 :> {mpoly R[_]}.
Proof. by rewrite -msupp_eq0 msuppX. Qed.

Lemma msym_restr s p :
  msym s (restr p) = restr (msym (lift_perm ord_max ord_max s) p).
Proof.
rewrite (mpolyE p) ![in LHS]linear_sum.
rewrite [msym _ _]linear_sum linear_sum /=.
apply eq_bigr => m _ /=; rewrite !linearZ /=; congr (_ *: _).
case: (altP ((m ord_max) =P 0%N)) => Hm.
- rewrite !msymX /restr [coefp 0]lock /=.
  rewrite !muniE !msuppX !big_seq1 !mcoeffX !eq_refl !scale1r.
  rewrite Hm expr0 alg_polyC; unlock; rewrite {2}[coefp 0]lock /=.
  rewrite polyseqC /= mpolyX_neq0 /=.
  rewrite mnmE lift_permV lift_perm_id Hm.
  unlock; rewrite linearZ expr0 /= polyseq1 mulr1.
  rewrite msymX; congr 'X_[_]; apply/mnmP => i; rewrite !mnmE; congr (m _).
  apply val_inj; rewrite /=.
  by rewrite widen_lift lift_perm_lift lift_ord_max.
- rewrite restrX0 // msym0 msymX restrX0 //.
  by rewrite !mnmE lift_permV lift_perm_id.
Qed.

Lemma restr_sym_subproof (p : {sympoly R[n.+1]}) :
  restr p \in symmetric.
Proof.
case: p => p /= /issymP Hp.
by apply/issymP => s; rewrite msym_restr Hp.
Qed.
Definition restr_sym p : {sympoly R[n]} := SymPoly (restr_sym_subproof p).

Lemma restr_syme k : restr_sym 'p_k.+1 = 'p_k.+1.
Proof.
apply val_inj; rewrite /= linear_sum.
rewrite (bigD1 ord_max) //=.
rewrite mpolyXn restrX0 ?add0r; first last.
  by rewrite mulmS !mnmE eq_refl add1n.
rewrite (reindex (@fintype.lift n.+1 ord_max)) /=; first last.
  
  liftK
    
Lemma restr_syme k : restr_sym 'e_k = 'e_k.
Proof.
apply val_inj; rewrite /= !mesymE linear_sum.
rewrite (bigID (fun s : {set _} => ord_max \in s)) /= big1 ?add0r; first last.
  move=> S /andP [_ Hin].
  by rewrite /mesym1 restrX0 // mnmE Hin.
pose f (s : {set 'I_n}) := (@fintype.lift n.+1 ord_max) @: s.
pose g (s : {set 'I_n.+1}) := (@fintype.lift n.+1 ord_max) @^-1: s.
rewrite (reindex f) /=; first last.
  exists g => s; rewrite inE => /andP [_ Hmax]; apply/setP => /= i.
  - rewrite !inE; apply/imsetP/idP => /= [[j Hj] /lift_inj -> // | Hi].
    by exists i.
  - apply/imsetP/idP => /= [[j] | Hi].
    + by rewrite /g inE => H ->.
    + case: (unliftP ord_max i) => /= [j Hj | Hj]; subst i.
      * by exists j => //; rewrite inE.
      * by rewrite Hi in Hmax.
apply eq_big => s.
- rewrite card_imset; last exact: lift_inj.
  case: eqP => //= _.
  rewrite /f; apply/negP => /imsetP /= [x _ /(congr1 val) /=].
  rewrite /bump leqNgt ltn_ord add0n => /eqP.
  by rewrite (gtn_eqF (ltn_ord x)).
- move=> /andP [/eqP Hcard H].
  rewrite /restr /=.
  
Section NVarChange.


Variable R : comRingType.
Variables N n : nat.
Hypothesis HnN : (n <= N)%N.

Local Notation polN := {mpoly R[N]}.
Local Notation poln := {mpoly R[n]}.
Local Notation symN := {sympoly R[N]}.
Local Notation symn := {sympoly R[n]}.

Definition restr_nvar (p : polN) : poln :=
  p \mPo [tuple nth 0 [tuple 'X_i | i < n] i | i < N].

Lemma restr_nvar_sym_subproof (p : symN) : restr_nvar p \in symmetric.
Proof.
rewrite /restr_nvar; apply msym_comp_poly => // s.
apply/tuple_perm_eqP.

Lemma restr_nvar_msymX m :
  restr_nvar 'X_[m] =
  if all (pred1 0%N) (drop n m) then
    'X_[[multinom nth 0%N m i | i < n]]
  else 0.
Proof.
rewrite /restr_nvar comp_mpolyX.
case: n HnN => [_ | n0 Hn0].
  rewrite drop0; case: (altP (m =P 0%MM)) => [-> /= | Hm].
  - rewrite big1 => [| i _]; last by rewrite tnth_mktuple mnmE expr0.
    rewrite all_map (eq_all (a2 := predT)) // all_predT.
    apply esym; rewrite [m in 'X_[m]](_ : _ = mnm0) ?mpolyX0 //.
    by apply mnmP => [[i]].
  - have [i Hi] : {i | m i != 0%N}.
      apply/sigW/existsP; move: Hm; apply contraR.
      rewrite negb_exists => /forallP Hall.
      apply/eqP/mnmP => i.
      by have := Hall i; rewrite negbK mnmE => /eqP ->.
    rewrite (bigD1 i) //= tnth_mktuple nth_default; first last.
      by rewrite size_map size_enum_ord.
    rewrite expr0n (negbTE Hi) mul0r.
    suff /negbTE -> : ~~ (all (pred1 0%N) m) by [].
    rewrite -has_predC; apply/(has_nthP 0%N); exists i; rewrite ?size_tuple //=.
    by rewrite -mnm_nth.
case: (boolP (all _ _)) => [/allP Hall| /allPn].
- rewrite (bigID (fun i : 'I_N => (i < n0.+1)%N)) /= mulrC big1 ?mul1r; first last.
    move=> i; rewrite -ltnNge ltnS => Hi.
    suff -> : (m i) = 0%N by rewrite expr0.
    apply/eqP/Hall; rewrite (mnm_nth 0).
    rewrite -(subnKC Hi) -nth_drop; apply mem_nth.
    by rewrite size_drop ltn_subRL subnKC // size_tuple.
  pose f := fun i =>
              'X_(nth ord0 (enum 'I_n0.+1) i)^+(nth 0%N m i) : {mpoly R[_]}.
  rewrite (eq_bigr (f \o nat_of_ord))=> [|i Hi]; first last.
    by rewrite /f tnth_mktuple /= (nth_map ord0) ?size_enum_ord // (mnm_nth 0).
  rewrite -big_ord_widen // /f.
  rewrite mpolyXE_id; apply eq_bigr => i _.
  by rewrite nth_ord_enum mnmE.
- move=> [/= i Hidrop].
  rewrite -(nth_index 0%N Hidrop) nth_drop.
  set ind := (_ + _)%N => Hnthind.
  have Hind : (ind < N)%N.
    by move: Hidrop; rewrite -index_mem size_drop size_tuple ltn_subRL.
  rewrite (bigD1 (Ordinal Hind)) //=.
  rewrite tnth_mktuple (mnm_nth 0) [nat_of_ord (Ordinal Hind)]/=.
  rewrite nth_default; first last.
    by rewrite size_map size_enum_ord /ind addSn ltnS leq_addr.
  by rewrite expr0n (negbTE Hnthind) mul0r.
Qed.

Lemma restr_nvar_symm_pol (p : symN) : restr_nvar p \in symmetric.

Lemma restr_nvar_sym_subproof (p : symN) : restr_nvar p \in symmetric.
Proof.
case: p => p /= /issym_symmE ->.
rewrite /restr_nvar !linear_sum /=; apply/issymP => s.
rewrite linear_sum; apply eq_bigr => m Hm.
rewrite !linearZ /=; congr (_ *: _).
rewrite /symm size_partm /=; move: (mpart _) => {m Hm} m.
rewrite /symm_pol.
; apply rpred_sum => m Hm.
rewrite linearZ; apply rpredZ => /=.


apply/issymP => s; apply/mpolyP => m.
rewrite /restr_nvar !linear_sum /=. apply eq_bigr => m _.
rewrite linearZ rmorph_prod /=; congr (_ *: _); apply eq_bigr => i _.
rewrite rmorphX /=; congr (_ ^+ _).
rewrite tnth_mktuple; case: (ssrnat.ltnP i n) => Hi.
- rewrite (nth_map (Ordinal Hi)).
