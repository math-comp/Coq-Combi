(** * Combi.MPoly.sympoly : Symmetric Polynomials *)
(******************************************************************************)
(*      Copyright (C) 2015-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * The Ring of Symmetric Polynomials

- [{sympoly R[n]}] == the ring of symmetric polynomial in [n] variable over [R].
- [sympol f] == the coercion from [{sympoly R[n]}] to [{mpoly R[n]}]

Classical bases

- ['e_k] == the [k]-th elementary symmetric polynomial
- ['h_k] == the [k]-th complete homogeneous symmetric polynomial
- ['p_k] == the [k]-th power sum symmetric polynomial

- [prod_gen G la] == given a familly of generators [G : nat -> {sympoly R[n]}]
             the product [\prod_(i <- la) G i].

- ['e[mu]] == the product of elementary symmetric polynomial
- ['h[mu]] == the product of complete homogeneous symmetric polynomial
- ['p[mu]] == the product of power sum symmetric polynomial
- ['m[mu]] == the monomial symmetric polynomial
- ['s[mu]] == the Schur symmetric polynomial

- [coeff_prodgen Co la mu] == the coefficient of the product ['g[la]]
             on ['g_[mu]] assuming that [co : forall d : nat, 'P_d -> R] gives
             the coefficients of ['f_i] on ['g_[mu]]

Change of scalars

- [map_sympoly M] == the ring morphism [{sympoly R[n]} -> {sympoly S[n]}]
             obtained by the change of scalar [M : {rmorphism R -> S}]

Formula for basis changes

- [perm_partn la] == the number of composition which are permuted of [la]
- [prod_partsum la] == the product of the sum of all the prefix of [la]

We list here a few theorems expressing a basis in another one. See the file
for a more comprehensive list. The rule is that we call [syma_to_symb] when
we expand a genrator of [syma] in [symb]. We call [syma_symb] the expansion
of a basis element of [syma] in [symb]

- e and h : [syme_to_symh] [symh_to_syme]
- s and m : [syms_symm] [symm_syms]
- s and h : [syms_symh] [symh_syms]
- h and p : [symh_to_symp] and Newton's formulas [Newton_symh] [Newton_symh1]
- e and p : Newton's formulas [Newton_syme1]
- h and m : [symh_to_symm]
- p and m : [symp_to_symm]

The omega involution

- [omegasf] == the omega involution, that is the unique ring morphism
             exchanging ['e_k] and ['h_k] wheneven [k] is smaller than the
             number of variables.

Change of the number of variables

- [sympolyf R m] == the algebra morphism expanding any symetric polynomial
             (in [{sympoly R[m]}]) as a polynomial in the ['e_i]
             (in [{mpoly R[m]}]) by the fundamental theorem of symmetric
             polynomials.
- [cnvarsym R m n] == the canonical algebra morphism
             [{sympoly R[m.+1]} -> {sympoly R[n.+1]}] sending ['e_i] to ['e_i]
             computed thanks to the fundamental theorem.

We show that if [d ≤ m] or [n ≤ m], for any partition in ['P_d] the change of
number of variables sends a basis element ['b[la]] to the same element. These
are lemmas

[cnvar_prodsyme], [cnvar_prodsymh], [cnvar_prodsymp], [cnvar_syms]
and [cnvar_symm].

 ******)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun finset binomial order.
From mathcomp Require Import bigop ssralg ssrint path perm fingroup.
From SsrMultinomials Require Import ssrcomplements freeg mpoly.
From SsrMultinomials Require monalg.

Require Import sorted tools ordtype permuted partition skewpart composition.
Require Import Yamanouchi std tableau stdtab skewtab permcent.
Require Import antisym Schur_mpoly therule Schur_altdef unitriginv.

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

Section MultinomCompl.

Variables (n : nat) (R : comRingType).

Lemma mnm_n0E : @all_equal_to 'X_{1..0} 0%MM.
Proof. by move=> mon; apply mnmP => [[i Hi]]. Qed.

Lemma eq_mnm1 (i j : 'I_n) : (U_(i)%MM == U_(j)%MM) = (i == j).
Proof.
case: (altP (i =P j)) => [->|/negbTE neq]; first by rewrite eqxx.
apply/negbTE/negP => /eqP; rewrite mnmP => /(_ j).
by rewrite !mnm1E eqxx neq.
Qed.

Lemma mcoeffXU (i j : 'I_n) : ('X_i : {mpoly R[n]})@_U_(j) = (i == j)%:R.
Proof. by rewrite mcoeffX eq_mnm1. Qed.

End MultinomCompl.


Reserved Notation "{ 'sympoly' T [ n ] }"
  (at level 0, T, n at level 2, format "{ 'sympoly'  T [ n ] }").
Reserved Notation "''e_' k" (at level 8, k at level 2, format "''e_' k").
Reserved Notation "''h_' k" (at level 8, k at level 2, format "''h_' k").
Reserved Notation "''p_' k" (at level 8, k at level 2, format "''p_' k").
Reserved Notation "''e[' k ]" (at level 8, format "''e[' k ]").
Reserved Notation "''h[' k ]" (at level 8, format "''h[' k ]").
Reserved Notation "''p[' k ]" (at level 8, format "''p[' k ]").
Reserved Notation "''m[' k ]" (at level 8, format "''m[' k ]").
Reserved Notation "''s[' k ]" (at level 8, format "''s[' k ]").


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
Arguments sympol n%N R%R.

Notation "{ 'sympoly' T [ n ] }" := (sympoly_of n (Phant T)).


Section SymPolyRingType.

Variable n : nat.
Variable R : ringType.

Definition sympoly_zmodMixin :=
  Eval hnf in [zmodMixin of {sympoly R[n]} by <:].
Canonical sympoly_zmodType :=
  Eval hnf in ZmodType {sympoly R[n]} sympoly_zmodMixin.

Definition sympoly_ringMixin :=
  Eval hnf in [ringMixin of {sympoly R[n]} by <:].
Canonical sympoly_ringType :=
  Eval hnf in RingType {sympoly R[n]} sympoly_ringMixin.

Definition sympoly_lmodMixin :=
  Eval hnf in [lmodMixin of {sympoly R[n]} by <:].
Canonical sympoly_lmodType :=
  Eval hnf in LmodType R {sympoly R[n]} sympoly_lmodMixin.

Definition sympoly_lalgMixin :=
  Eval hnf in [lalgMixin of {sympoly R[n]} by <:].
Canonical sympoly_lalgType :=
  Eval hnf in LalgType R {sympoly R[n]} sympoly_lalgMixin.

Fact sympol_is_lrmorphism :
  lrmorphism (@sympol n R : {sympoly R[n]} -> {mpoly R[n]}).
Proof. by []. Qed.
Canonical sympol_additive   := Additive   sympol_is_lrmorphism.
Canonical sympol_rmorphism  := RMorphism  sympol_is_lrmorphism.
Canonical sympol_linear     := AddLinear  sympol_is_lrmorphism.
Canonical sympol_lrmorphism := LRMorphism sympol_is_lrmorphism.

Lemma sympolP (x : {sympoly R[n]}) : sympol x \is symmetric.
Proof. by case: x. Qed.

End SymPolyRingType.

#[export] Hint Resolve sympolP : core.


Section SymPolyComRingType.

Variable n : nat.
Variable R : comRingType.

Definition sympoly_comRingMixin :=
  Eval hnf in [comRingMixin of {sympoly R[n]} by <:].
Canonical sympoly_comRingType :=
  Eval hnf in ComRingType {sympoly R[n]} sympoly_comRingMixin.

Definition sympoly_algMixin :=
  Eval hnf in [algMixin of {sympoly R[n]} by <:].
Canonical sympoly_algType :=
  Eval hnf in AlgType R {sympoly R[n]} sympoly_algMixin.

End SymPolyComRingType.

Section SymPolyIdomainType.

Variable n : nat.
Variable R : idomainType.

Definition sympoly_unitRingMixin :=
  Eval hnf in [unitRingMixin of {sympoly R[n]} by <:].
Canonical sympoly_unitRingType :=
  Eval hnf in UnitRingType {sympoly R[n]} sympoly_unitRingMixin.

Canonical sympoly_comUnitRingType :=
  Eval hnf in [comUnitRingType of {sympoly R[n]}].

Definition sympoly_idomainMixin :=
  Eval hnf in [idomainMixin of {sympoly R[n]} by <:].
Canonical sympoly_idomainType :=
  Eval hnf in IdomainType {sympoly R[n]} sympoly_idomainMixin.

Canonical sympoly_unitAlgType :=
  Eval hnf in [unitAlgType R of {sympoly R[n]}].

End SymPolyIdomainType.


Section Bases.

Variable n : nat.

Variable R : comRingType.
Implicit Type m : 'X_{1.. n}.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").


(** ** Elementary symmetric polynomials *)
(* From  mpoly.v : \sum_(h : {set 'I_n} | #|h| == k) \prod_(i in h) 'X_i. *)
Fact syme_sym d : mesym n R d \is symmetric.
Proof using. exact: mesym_sym. Qed.
Canonical syme d : {sympoly R[n]} := SymPoly (syme_sym d).
Local Notation "''e_' k" := (syme k).

Lemma syme_geqnE d : d > n -> 'e_d = 0.
Proof. by move=> Hd; apply val_inj; rewrite /= mesym_geqnE. Qed.
Lemma syme_homog d : sympol 'e_d \is d.-homog.
Proof using. by rewrite dhomog_mesym. Qed.


(** ** Complete homogeneous symmetric polynomials *)
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
Canonical symh d : {sympoly R[n]} := SymPoly (symh_sym d).
Local Notation "''h_' k" := (symh k).

Lemma mcoeff_symh d m : 'h_d@_m = (mdeg m == d)%:R.
Proof. exact: mcoeff_symh_pol. Qed.
Lemma symh_homog d : sympol 'h_d \is d.-homog.
Proof using. by apply rpred_sum => m /eqP H; rewrite dhomogX /= H. Qed.


(** ** Power sum symmetric polynomials *)
Definition symp_pol d  : {mpoly R[n]} := \sum_(i < n) 'X_i ^+ d.
Fact symp_sym d : symp_pol d \is symmetric.
Proof using.
apply/issymP => s.
rewrite linear_sum /= (reindex_inj (perm_inj (s := s^-1)))%g /=.
apply eq_bigr => i _; rewrite rmorphX /=; congr (_ ^+ _).
rewrite msymX /=; congr mpolyX.
rewrite mnmP => j; rewrite !mnmE /=; congr nat_of_bool.
by apply/eqP/eqP => [|->//]; apply: perm_inj.
Qed.
Canonical symp d : {sympoly R[n]} := SymPoly (symp_sym d).
Local Notation "''p_' k" := (symp k).

Lemma symp_homog d : sympol 'p_d \is d.-homog.
Proof using.
apply rpred_sum => m _.
have /(dhomogMn d) : ('X_m : {mpoly R[n]}) \is 1.-homog.
  by rewrite dhomogX /= mdeg1.
by rewrite mul1n.
Qed.


(** ** Monomial symmetric polynomials *)
Definition symm_pol (sh : n.-tuple nat) : {mpoly R[n]} :=
  \sum_(p : permuted sh) 'X_[Multinom p].
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
have: perm_eq (m#s) m by apply/tuple_permP; exists s.
by move=> /permPr ->.
Qed.
Definition symm sh : {sympoly R[n]} :=
  if size sh <= n then SymPoly (symm_sym (mpart sh)) else 0 : {sympoly R[n]}.
Notation "''m[' k ]" := (symm k).

Lemma symm_oversize sh : n < size sh -> 'm[sh] = 0.
Proof. by rewrite ltnNge /symm => /negbTE ->. Qed.
Lemma mcoeff_symm sh m :
  size sh <= n -> 'm[sh]@_m = (perm_eq (mpart (n := n) sh) m)%:R.
Proof. by move=> H; rewrite /symm H mcoeff_symm_pol. Qed.
Lemma symm_homog d (sh : 'P_d) : sympol 'm[sh] \is d.-homog.
Proof using.
case: (leqP (size sh) n) => [Hsz | /symm_oversize ->]; last exact: dhomog0.
rewrite /= unfold_in; apply/allP => /= m.
rewrite mcoeff_msupp mcoeff_symm //.
case: (boolP (perm_eq _ _)) => [Hperm _ | _]; last by rewrite /= eq_refl.
rewrite /mdeg -sumnE -(sumn_intpartn sh).
move: Hperm => /perm_sumn <-{m}.
rewrite -{2}(mpartK _ Hsz) // is_dominant_partm; last exact: mpart_is_dominant.
apply/eqP; rewrite /= !sumnE big_filter.
rewrite [LHS](bigID (fun i => i == 0%N)) /= big1 ?add1n //.
by move=> i /eqP.
Qed.

Lemma symE (p q : {sympoly R[n]}) :
  reflect (forall m, m \is dominant -> p@_m = q@_m) (p == q).
Proof.
apply (iffP eqP) => [-> //| Hdom]; apply/val_inj/mpolyP => m /=.
have [s /eqP <- ] := perm_mpart_partm m.
rewrite -(issymP p (sympolP p) (s^-1)%g) -(issymP q (sympolP q) (s^-1)%g).
rewrite !mcoeff_sym mpermKV.
by apply: Hdom; apply/mpart_is_dominant.
Qed.

(** *** Expansion of symmetric polynomials on monomials *)
Lemma sym_symmE (p : {sympoly R[n]}) :
  p = \sum_(m <- msupp p | m \is dominant) p@_m *: 'm[partm m].
Proof.
apply/eqP/symE => // m mdom; rewrite !raddf_sum /=.
case: (boolP (m \in msupp p)) => [minsupp|mninsupp].
- rewrite -big_filter (bigD1_seq m) /=; first last.
  + by apply filter_uniq; apply msupp_uniq.
  + by rewrite mem_filter mdom.
  rewrite linearZ /= mcoeff_symm ?size_partm //.
  rewrite perm_sym partm_permK mulr1 big_seq_cond /=.
  rewrite big1 ?addr0 // => mon /andP [].
  rewrite linearZ /= mcoeff_symm ?size_partm //.
  rewrite mem_filter => /andP [mondom monsupp] neq.
  case: (boolP (perm_eq _ _)) => [/permPr Hperm|]; last by rewrite mulr0.
  exfalso; move: neq => /negP; apply; apply/eqP.
  apply: dominant_eq => //.
  by rewrite -{}Hperm partm_permK.
- rewrite (memN_msupp_eq0 mninsupp); symmetry.
  rewrite big_seq_cond; apply big1 => /= m' /andP [Hsupp Hdom].
  rewrite mcoeffZ (mcoeff_symm _ (size_partm _)) partmK //.
  suff -> : perm_eq m' m = false by rewrite mulr0.
  apply/negP => Hperm; move: mninsupp.
  by rewrite -(dominant_eq Hdom mdom Hperm) Hsupp.
Qed.

Lemma size_mpart_in_supp (f : {mpoly R[n]}) d (p : 'P_d) :
  f \is d.-homog -> mpart p \in msupp f -> size p <= n.
Proof.
rewrite /mpart; case: leqP => //= H1 /dhomogP H{}/H /=.
rewrite /= mdeg0 => Hd; subst d.
by move: H1; rewrite intpartn0 size_rowpartn.
Qed.

Lemma dominant_mpart d m :
  m \is dominant -> mdeg m = d -> { p : 'P_d | m = mpart p }.
Proof.
move=> mdom degm.
have hpm : is_part_of_n d (partm m).
  by rewrite /= -degm sumn_partm eqxx /=.
by exists (IntPartN hpm); rewrite partmK.
Qed.

Lemma homog_symmE d (f : {sympoly R[n]}) :
  sympol f \is d.-homog -> f = \sum_(l : 'P_d) f@_(mpart l) *: 'm[l].
Proof.
move=> Hhomog; rewrite {1}(sym_symmE f).
apply val_inj => /=.
rewrite !linear_sum /=  (bigID (fun i : 'P_d => mpart i \in msupp f)) /=.
rewrite [X in _ + X]big1 ?addr0;
  last by move=> i /memN_msupp_eq0 ->; rewrite scale0r.
under [RHS]eq_bigr => i Hi.
  rewrite -{2}(@mpartK n i) //; last exact: (size_mpart_in_supp Hhomog).
over. rewrite /=.
transitivity (\sum_(m <- [seq mpart i | i : 'P_d ] | m \in msupp f)
               f@_m *: sympol ('m[partm m])); first last.
  by rewrite big_map big_enum_cond.
rewrite -big_filter -[RHS]big_filter; apply perm_big; apply uniq_perm.
- by apply filter_uniq; apply msupp_uniq.
- rewrite filter_map map_inj_in_uniq; first by apply filter_uniq; apply enum_uniq.
  move=> /= c1 c2; rewrite !mem_filter /= => /andP [Hc1 _] /andP [Hc2 _].
  move=> /(congr1 (@partm n)) /(congr1 val) /=.
  rewrite !mpartK // ?(size_mpart_in_supp _ Hc1) ?(size_mpart_in_supp _ Hc2) //.
  exact: val_inj.
- move=> /= m; rewrite !mem_filter andbC.
  case: (boolP (m \in msupp f)) => //= Hsupp.
  apply/idP/mapP => /= [Hdom | [l _ ->]]; last exact: mpart_is_dominant.
  have {Hsupp} degm : mdeg m = d.
    by move: Hhomog => /dhomogP/(_ _ Hsupp).
  have {Hdom degm} [p ->] := dominant_mpart Hdom degm.
  by exists p => //; rewrite mem_enum.
Qed.

Lemma symm_unique d (f : {sympoly R[n]}) c :
  f = \sum_(l : 'P_d) (c l) *: 'm[l] ->
  forall l : 'P_d, size l <= n -> c l = f@_(mpart l).
Proof.
move=> -> l Hl.
rewrite !linear_sum /=.
rewrite (bigD1 l) //= !linearZ /= (mcoeff_symm _ Hl) perm_refl /= mulr1.
rewrite big1 ?addr0 // => i Hil /=.
case: (leqP (size i) n) => [Hi | /symm_oversize ->];
                          last by rewrite scaler0 mcoeff0.
rewrite linearZ /= mcoeff_symm //.
rewrite [perm_eq _ _](_ : _ = false) /= ?mulr0 //.
apply negbTE; move: Hil; apply contra.
move=> /perm_partm/(congr1 pval).
rewrite !mpartK // => Hil.
by apply/eqP/val_inj.
Qed.

Lemma symm_unique0 d c :
  \sum_(l : 'P_d) (c l) *: 'm[l] = 0 ->
  forall l : 'P_d, size l <= n -> c l = 0.
Proof. by move=> /esym/symm_unique => H l /H ->; rewrite mcoeff0. Qed.

Lemma sum_symmE d (f : {sympoly R[n]}) :
  \sum_(l : 'P_d) f@_(mpart l) *: 'm[l] =
  \sum_(l <- [seq val p | p <- enum {: 'P_d}]) f@_(mpart l) *: 'm[l].
Proof. by rewrite big_map big_enum. Qed.

(** ** Basis at degree 0 *)
Lemma syme0 : 'e_0 = 1.
Proof using. by apply val_inj; rewrite /= mesym0E. Qed.

Lemma symp0 : 'p_0 = n%:R.
Proof using.
apply /val_inj; rewrite /= /symp_pol.
under eq_bigr do rewrite expr0.
by rewrite sumr_const card_ord /= raddfMn.
Qed.

Lemma symh0 : 'h_0 = 1.
Proof using.
have Hd0 : (mdeg (0%MM : 'X_{1..n})) < 1 by rewrite mdeg0.
apply val_inj => /=.
rewrite /symh_pol /symh_pol_bound (big_pred1 (BMultinom Hd0)); first last.
  by move=> m; rewrite /= mdeg_eq0 {2}/eq_op.
by rewrite mpolyX0.
Qed.

Lemma symm0 : 'm[[::]] = 1.
Proof using.
have /homog_symmE -> : (sympol (1 : {sympoly R[n]})) \is 0.-homog.
  by rewrite rmorph1 dhomog1.
rewrite sum_symmE enum_intpartnE /enum_partn /= big_cons big_nil addr0.
by rewrite mcoeff1 mpart0 eqxx scale1r.
Qed.


(** ** All basis agrees at degree 1 *)
Lemma syme1 : val ('e_1) = \sum_(i < n) 'X_i.
Proof using. by rewrite /= mesym1E. Qed.

Lemma sympe1E : 'p_1 = 'e_1.
Proof using.
apply val_inj; rewrite syme1 /=.
by apply eq_bigr => i _; rewrite expr1.
Qed.

Lemma symhe1E : 'h_1 = 'e_1.
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

Notation "''e_' k" := (syme _ _ k).
Notation "''h_' k" := (symh _ _ k).
Notation "''p_' k" := (symp _ _ k).
Notation "''m[' k ]" := (symm _ _ k).

Section ChangeBaseMonomial.

Variables (n : nat) (R : comRingType).
Local Notation SP := {sympoly R[n]}.

Lemma expUmpartE nv k :
  (U_(ord0) *+ k)%MM = mpart (rowpartn k) :> 'X_{1..nv.+1}.
Proof.
rewrite rowpartnE.
apply/mnmP => [[i Hi]]; rewrite /mpart mulmnE !mnmE -val_eqE /=.
case: k => [|k] /=; first by rewrite mul0n mnmE nth_default.
rewrite mnmE /=;
by case: i {Hi} => [|i] /=; rewrite ?muln1 // muln0 nth_default.
Qed.

Lemma expUmpartNE nv k i (P : intpartn k.+1) :
  ((U_(i) *+ k.+1)%MM == mpart P :> 'X_{1..nv.+1})
  = (i == ord0) && (P == rowpartn k.+1).
Proof.
apply/eqP/andP => [| [/eqP ->{i} /eqP ->{P}]]; last exact: expUmpartE.
rewrite /mpart; case: leqP => _; first last.
  move/(congr1 (fun mon : 'X_{1..nv.+1} => mon i)).
  by rewrite mulmnE !mnmE -val_eqE /= eqxx muln1.
case: (altP (i =P ord0)) => [->{i} | neq H]; first split => //.
  apply/eqP/val_inj; rewrite /= rowpartnE.
  case: P H => [[|p0 [|p1 p]]]//=.
    by rewrite addn0 => /andP [/eqP ->].
  rewrite -/(is_part (p1 :: p)) => /and3P [Hsum _ Hpart].
  move/(congr1 (fun mon : 'X_{1..nv.+1} => mon ord0)).
  rewrite mulmnE !mnmE -val_eqE /= muln1 => Hp0; exfalso.
  move: Hsum Hpart; rewrite -{}Hp0 -{2}(addn0 k.+1) eqn_add2l.
  by rewrite addn_eq0 => /andP [/eqP -> _] /part_head_non0.
exfalso; move/(congr1 (fun mon : 'X_{1..nv.+1} => mon ord0)): H.
rewrite mulmnE !mnmE (negbTE neq) {neq} muln0 /= => Hp0.
case: P Hp0 => [[//|p0 p]] Hp /= Hp0.
by move: Hp; rewrite -{}Hp0 => /andP [_ /part_head_non0].
Qed.

Lemma symp_to_symm k : 'p_k.+1 = 'm[rowpartn k.+1] :> SP.
Proof.
case: n => [|n0].
  apply/val_inj; rewrite [RHS]nvar0_mpolyC [LHS]nvar0_mpolyC.
  rewrite (dhomog_nemf_coeff (symm_homog 0 R (rowpartn k.+1)));
    last by rewrite /= mdeg0.
  by rewrite (dhomog_nemf_coeff (symp_homog 0 R k.+1)) //= mdeg0.
move HK : k.+1 => K.
rewrite (homog_symmE (symp_homog n0.+1 R K)) (bigD1 (rowpartn K)) //=.
have -> : (symp_pol n0.+1 R K)@_(mpart (rowpartn K)) = 1.
  rewrite /symp_pol (bigD1 ord0) // raddfD raddf_sum //.
  rewrite mpolyXn [rowpartn _]lock /= mcoeffX -HK.
  rewrite -{1}lock expUmpartNE /= eqxx big1 ?addr0 // => i /negbTE Hi.
  by rewrite mpolyXn /= mcoeffX expUmpartNE Hi.
rewrite scale1r big1 ?addr0 -{}HK // => P /negbTE HP.
suff -> : (symp_pol n0.+1 R k.+1)@_(mpart P) = 0 by rewrite scale0r.
rewrite /symp_pol raddf_sum big1 ?mcoeff0 //= => i _.
by rewrite mpolyXn /= mcoeffX expUmpartNE HP andbF.
Qed.

Lemma symh_to_symm k : 'h_k = \sum_(l : 'P_k) 'm[l] :> SP.
Proof.
rewrite (homog_symmE (symh_homog n R k)); apply eq_bigr => l _.
case: (leqP (size l) n) => [Hsz | /symm_oversize ->]; last by rewrite scaler0.
by rewrite mcoeff_symh mdeg_mpart // sumn_intpartn eqxx scale1r.
Qed.

Lemma syme_to_symm k : 'e_k = 'm[colpartn k] :> SP.
Proof.
case: (leqP k n) => [|ltnk]; first last.
  by rewrite symm_oversize ?size_colpartn ?syme_geqnE.
rewrite -{1}(size_colpartn k) => leszn.
rewrite (homog_symmE (syme_homog n R k)).
rewrite (bigD1 (colpartn k)) //= mcoeff_mesym /mechar.
rewrite mdeg_mpart // sumn_intpartn eqxx /=.
rewrite [[forall i, _]](_ : _ = true) ?scale1r; first last.
  apply/forallP => /= i; rewrite /mpart leszn mnmE colpartnE nth_nseq.
  by case: ltnP.
rewrite big1 ?addr0 // => P HP.
rewrite mcoeff_mesym /mechar.
rewrite [[forall i, _]](_ : _ = false) ?andbF ?scale0r //.
move: leszn; rewrite (size_colpartn k) => lekn.
apply/negbTE; move: HP; apply contra => /forallP /= HP.
rewrite /mpart in HP; apply/eqP/(colpartnP (x0 := 1)).
case: n lekn HP => [|n0 Hk /(_ ord0)].
  by rewrite leqn0 => /eqP Hk _; subst k; rewrite intpartn0 rowpartn0E.
have -> := leq_trans (size_part (intpartP P)); last by rewrite sumn_intpartn.
by rewrite mnmE /=; case: P => [[|]].
Qed.

End ChangeBaseMonomial.

(** ** Schur symmetric polynomials *)
Section Schur.

Variable n0 : nat.
Variable R : comRingType.

Local Notation n := n0.+1.

Definition syms d (la : 'P_d) : {sympoly R[n]} :=
  SymPoly (Schur_sym n0 R la).

Local Notation "''s[' k ]" := (syms k).

Lemma syms_homog d (la : 'P_d) : sympol 's[la] \is d.-homog.
Proof. exact: Schur_homog. Qed.

Lemma syms0 (la : 'P_0) : 's[la] = 1.
Proof. by apply val_inj; rewrite /= Schur0. Qed.

Lemma syms1 (la : 'P_1) : 's[la] = \sum_(i < n) 'X_i :> {mpoly R[n]}.
Proof. by rewrite /= Schur1. Qed.

Lemma syms_rowpartn d : 's[rowpartn d] = 'h_d.
Proof.
by apply val_inj; rewrite /= /symh_pol /symh_pol_bound Schur_rowpartn.
Qed.

Lemma syms_colpartn d : 's[colpartn d] = 'e_d.
Proof. by apply val_inj; rewrite /= mesym_SchurE. Qed.

Lemma syms_oversize d (la : 'P_d) : n < size la -> 's[la] = 0.
Proof. by move=> /Schur_oversize => over; apply val_inj => /=. Qed.

End Schur.

Notation "''s[' k ]" := (syms _ _ k).


(** * Multiplicative bases.

Given a family of generators ['g_k], we define ['g[la]] as the product of the
generators \prod_(i <- la) 'g_i.
 *****)
Section ProdGen.

Variable n : nat.
Variable R : comRingType.
Local Notation SF := {sympoly R[n]}.

Section Defs.

Variable gen : nat -> SF.
Hypothesis gen_homog : forall d, sympol (gen d) \is d.-homog.

Definition prod_gen d (sh : 'P_d) := \prod_(i <- sh) gen i.

Local Notation "''g_' k" := (gen k) (at level 8, format "''g_' k").
Local Notation "''g[' k ]" := (prod_gen k) (at level 8, format "''g[' k ]").

Lemma prod_gen_homog d (sh : 'P_d) : sympol 'g[sh] \is d.-homog.
Proof using gen_homog.
rewrite /prod_gen; case: sh => sh /= /andP [/eqP <- _] {d}.
elim: sh => [| d sh IHsh] /=; first by rewrite big_nil /= dhomog1.
by rewrite big_cons; apply dhomogM; first exact: gen_homog.
Qed.

Lemma prod_gen0 (l : 'P_0) : 'g[l] = 1.
Proof. by rewrite /prod_gen val_intpartn0 big_nil. Qed.

Lemma prod_genM c d (l : 'P_c) (k : 'P_d) : 'g[l] * 'g[k] = 'g[l +|+ k].
Proof using.
by rewrite /prod_gen (perm_big _ (perm_union_intpartn l k)) big_cat.
Qed.

Lemma prod_gen_colpartn d : 'g[colpartn d] = 'g_1 ^+ d.
Proof.
rewrite /prod_gen /= colpartnE big_nseq.
by elim: d => //= d ->; rewrite exprS.
Qed.

Lemma prod_gen_cast d1 d2 (eq_d : d1 = d2) (la : 'P_d1) :
  'g[cast_intpartn eq_d la] = 'g[la].
Proof. by rewrite /prod_gen /= cast_intpartnE. Qed.

End Defs.

Variable gA gB : nat -> SF.
Variable co : forall (d : nat), 'P_d -> R.

Local Notation "''gA_' k" := (gA k) (at level 8, format "''gA_' k").
Local Notation "''gA[' k ]" :=
  (prod_gen gA k) (at level 8, format "''gA[' k ]").
Local Notation "''gB_' k" := (gB k) (at level 8, format "''gB_' k").
Local Notation "''gB[' k ]" :=
  (prod_gen gB k) (at level 8, format "''gB[' k ]").

Fixpoint coeff_prodgen_seq l : 'P_(sumn l) -> R :=
  if l is l0 :: l' then
    fun la : 'P_(sumn (l0 :: l')) =>
             \sum_(p | la == p.1 +|+ p.2) co p.1 * coeff_prodgen_seq p.2
  else fun _ => 1.

Local Notation "''co[' k ]" := (coeff_prodgen_seq k)
                                 (at level 8, format "''co[' k ]").
Local Notation "''co[' k ]_ l" := (coeff_prodgen_seq (l := l) k)
                                 (at level 8, only parsing).

Definition coeff_prodgen d (la mu : 'P_d) : R :=
  'co[cast_intpartn (esym (sumn_intpartn la)) mu].

Lemma coeff_prodgen_cast l k nu (eqlamu : l = k) (eqsum : sumn l = sumn k) :
  'co[cast_intpartn eqsum nu] = 'co[nu].
Proof.
by subst k; congr coeff_prodgen_seq; apply val_inj; rewrite cast_intpartnE.
Qed.

Lemma prod_prodgen :
  (forall d, 'gA_d = \sum_(la : 'P_d) co la *: 'gB[la] :> SF) ->
  forall d (la : 'P_d),
    'gA[la] = \sum_(mu : 'P_d)
               coeff_prodgen la mu *: 'gB[mu] :> SF.
Proof.
rewrite /coeff_prodgen /= {2}/prod_gen => H d la.
have := sumn_intpartn la.
case: la => [la /= Hla] Hd; subst d.
under [RHS]eq_bigr do rewrite coeff_prodgen_cast //.
elim: la {Hla} => [| l la IHla] /=.
  rewrite big_nil (big_pred1 (rowpartn 0)) ?prod_gen0 ?scale1r // => la.
  by symmetry; apply/eqP/val_inj; rewrite /= intpartn0.
rewrite big_cons H; symmetry.
under [LHS]eq_bigr do rewrite scaler_suml.
rewrite (exchange_big_dep xpredT) //=.
under [LHS]eq_bigr do rewrite big_pred1_eq -prod_genM -scalerA scalerAr scalerAl.
rewrite -[LHS](pair_big xpredT xpredT
    (fun mu nu => _ mu *: _ mu * (_ nu *: _ nu))) /=.
rewrite mulr_suml.
by under eq_bigr do rewrite -mulr_sumr -IHla.
Qed.

Definition prod_syme := prod_gen (@syme n R).
Definition prod_syme_homog := prod_gen_homog (@syme_homog n R).
Definition prod_symh := prod_gen (@symh n R).
Definition prod_symh_homog := prod_gen_homog (@symh_homog n R).
Definition prod_symp := prod_gen (@symp n R).
Definition prod_symp_homog := prod_gen_homog (@symp_homog n R).

End ProdGen.

Notation "''e[' k ]" := (prod_syme _ _ k).
Notation "''h[' k ]" := (prod_symh _ _ k).
Notation "''p[' k ]" := (prod_symp _ _ k).


(** Casting the index *)
Section Cast.

Variable n0 : nat.
Local Notation n := n0.+1.
Variables R : comRingType.
Local Notation SF := {sympoly R[n]}.

Variables (d1 d2 : nat) (eq_d : d1 = d2) (la : 'P_d1).

Lemma syms_cast : 's[cast_intpartn eq_d la] = 's[la] :> SF.
Proof. by apply val_inj; rewrite /= Schur_cast. Qed.
Lemma syme_cast : 'e[cast_intpartn eq_d la] = 'e[la] :> SF.
Proof. exact: prod_gen_cast. Qed.
Lemma symh_cast : 'h[cast_intpartn eq_d la] = 'h[la] :> SF.
Proof. exact: prod_gen_cast. Qed.
Lemma symp_cast : 'p[cast_intpartn eq_d la] = 'p[la] :> SF.
Proof. exact: prod_gen_cast. Qed.
Lemma symm_cast : 'm[cast_intpartn eq_d la] = 'm[la] :> SF.
Proof. by apply val_inj; rewrite /= /symm cast_intpartnE. Qed.

End Cast.


(** * Littlewood-Richardson and Pieri rules *)
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
apply val_inj; rewrite /= LRyam_coeffP linear_sum /=.
by under [RHS]eq_bigr do rewrite raddfMn.
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


(** * Change of scalars *)
Section ScalarChange.

Variables R S : comRingType.
Variable mor : {rmorphism R -> S}.
Variable n0 : nat.
Local Notation n := n0.+1.

Lemma map_mpoly_issym (f : {sympoly R[n]}) : map_mpoly mor f \is symmetric.
Proof.
apply/issymP => s.
by rewrite msym_map_mpoly (issymP _ (sympolP f)).
Qed.
Definition map_sympoly (f : {sympoly R[n]}) : {sympoly S[n]} :=
           SymPoly (map_mpoly_issym f).

Fact map_sympoly_is_rmorphism : rmorphism map_sympoly.
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



(** * Bases change formulas *)
Section ChangeBasis.

Variable n0 : nat.
Local Notation n := n0.+1.
Variable R : comRingType.

Local Notation "''Xn'" := 'X_{1.. n}.
Local Notation "''Xn_' m" := 'X_{1.. n < (mdeg m).+1}
          (at level 10, m at next level, format "''Xn_' m").
Local Notation "''XXn_' m" := 'X_{1.. n < (mdeg m).+1, (mdeg m).+1}
          (at level 10, m at next level, format "''XXn_' m").
Implicit Type m : 'Xn.
Local Notation SF := {sympoly R[n]}.

(** ** Bases change between homogeneous and elementary *)
Lemma sum_symh_syme (d : nat) :
  d != 0%N ->
  \sum_(0 <= i < d.+1) (-1) ^+ i *: ('h_i * 'e_(d - i)) = 0 :> SF.
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
transitivity (\sum_(0 <= i < d.+1)
               (-1) ^+ i * (binomial #|[set j | m j != 0%N]| i)%:R : R).
  apply eq_big_nat => /= i; rewrite ltnS => Hi.
  rewrite subSS subKn // linearZ /= mulrA; congr (_ * _).
    rewrite -signr_odd -[X in _ * X]signr_odd -signr_addb.
    by rewrite oddB // addKb signr_odd.
  rewrite mcoeffM.
  rewrite (bigID (fun k : 'XXn_m => (mechar i k.2))) /=.
  rewrite addrC big1 ?add0r; first last.
    move=> [/= m1 m2 /andP [Hmm /negbTE Hf]].
    by rewrite mcoeff_mesym Hf /= mulr0.
  rewrite (eq_bigr (fun k : 'XXn_m => 1)); first last.
    move=> [/= m1 m2 /andP [/eqP H1 H2]].
    rewrite mcoeff_symh mcoeff_mesym H2 /= mulr1.
    suff -> : mdeg m1 == (d - i)%N by [].
    move: Hm; rewrite {1}H1 mdegD.
    move: H2 => /andP [/eqP -> _] <-.
    by rewrite addnK.
  subst d; rewrite sumr_const /= -cards_draws; congr _%:R.
  pose f := (fun mm : 'Xn => [set j | mm j != 0%N] : {set 'I_n}).
  pose g := (fun S : {set 'I_n} => [multinom (i \in S : nat) | i < n]).
  have canfg : {in mechar i, cancel f g}.
    move=> m2.
    rewrite unfold_in /mechar /= => /andP [_ /forallP /= Hall].
    rewrite /f /g {f g} /=.
    apply/mnmP => j; rewrite mnmE inE.
    case: (altP (m2 j =P 0%N)) => [-> |] //=.
    by move/(_ j): Hall; case: (m2 j) => [|[|k]].
  rewrite -(card_in_imset (f := f \o (fun mm : 'XXn_m => bmnm mm.2))); first last.
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
      rewrite -sum1_card; apply eq_bigr => j.
      rewrite inE -mnm_tnth.
      by move/(_ j): Hall; case: (m2 j) => [|[|k]].
  - have : mdeg (g S) = #|S|.
      rewrite /mdeg [LHS]big_tuple (bigID (mem S)) /= addnC.
      rewrite [X in (X + _)%N]big1 ?add0n; first last.
        by move=> j /negbTE; rewrite tnth_mktuple => ->.
      under eq_bigr => j do rewrite tnth_mktuple => ->.
      exact: sum1_card.
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
  (\sum_(i < C.+1) (-1) ^+ i * 1 ^+ (C - i) * 1 ^+ i *+ 'C(C, i) : R); first last.
  by rewrite -exprBn subrr expr0n (negbTE HC).
rewrite big_mkord.
rewrite [LHS](bigID (fun i : 'I__ => i < C.+1)) /= addrC big1 ?add0r; first last.
  move=> i; rewrite -leqNgt => /bin_small ->.
  by rewrite mulr0.
under [RHS]eq_bigr do rewrite !expr1n !mulr1 -mulr_natr.
exact/esym/(big_ord_widen _ (fun i => (-1) ^+ i * ('C(C, i))%:R)).
Qed.

Lemma sum_syme_symh (d : nat) :
  d != 0%N ->
  \sum_(0 <= i < d.+1) (-1) ^+ i *: ('e_i * 'h_(d - i)) = 0 :> SF.
Proof.
move=> Hd; rewrite big_nat_rev /=.
rewrite -[RHS](scaler0 _ ((-1)^+d)) -[in RHS](sum_symh_syme Hd) scaler_sumr /=.
rewrite !big_nat; apply eq_bigr => i /andP [_ Hi].
rewrite mulrC !add0n subSS subKn // scalerA; congr (_ *: ('h__ * 'e__)).
by rewrite -signr_odd oddB // signr_addb !signr_odd.
Qed.


Section HandE.

Variable E H : nat -> {sympoly R[n]}.

Hypothesis E0 : E 0 = 1.
Hypothesis H0 : H 0 = 1.
Hypothesis Hanti : forall d : nat,
    d != 0%N ->
    \sum_(0 <= i < d.+1) (-1) ^+ i *: (H i * E (d - i)) = 0.

Lemma symHE_rec (d : nat) :
  d != 0%N ->
  E d = \sum_(1 <= i < d.+1) H i * ((-1) ^+ i.-1 *: E (d - i)).
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
  E d = \sum_(c : intcompn d) (-1) ^+ (d - size c) *: (\prod_(i <- c) H i).
Proof.
rewrite -big_enum /=.
rewrite -[RHS](big_map (@cnval d) xpredT
   (fun c : seq nat => (-1)^+(d - size c) *: \prod_(i <- c) H i)).
rewrite enum_intcompnE.
have [m/ltnW] := ubnP d; elim: m => [| m IHm] in d *.
  rewrite leqn0 => /eqP ->.
  by rewrite /enum_compn /= big_seq1 /= subnn expr0 scale1r big_nil E0.
rewrite leq_eqVlt => /orP [/eqP Hm|]; last by rewrite ltnS; exact: IHm.
rewrite enum_compnE Hm // -Hm big_flatten /=.
rewrite symHE_rec; last by rewrite Hm.
rewrite big_map /index_iota subSS subn0; apply eq_big_seq => i.
rewrite mem_iota add1n ltnS => /andP [Hi Hid].
rewrite big_map.
under eq_big_seq => s.
  rewrite -enum_compnP /is_comp_of_n /= => /andP[/eqP Hsum Hcomp].
  rewrite big_cons scalerAr -mulrNN -scaleNr -[- (-1) ^+ _]mulN1r.
  rewrite -exprS -subSn; first last.
    rewrite Hm ltnS (leq_trans (size_comp Hcomp)) // {}Hsum.
    case: i Hi {Hid} => // i' _.
    by rewrite Hm subSS leq_subr.
  by rewrite subSS over.
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
move: Hdi; rewrite subn_eq0 -leqNgt => {}Hid.
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
  E d = \sum_(c : intcompn d)
         (-1)^+(d - size c) *: prod_gen H (partn_of_compn c).
Proof.
rewrite symHE_prod_intcomp; apply eq_bigr => c _; congr (_ *: _).
rewrite /prod_symh /prod_gen; apply: perm_big.
by rewrite perm_sym perm_sort.
Qed.

Definition perm_partn d (la : 'P_d) :=
  #|[set c : intcompn d | sort geq c == la]|.

Lemma symHE_intpartn d :
  E d = \sum_(la : 'P_d)
         (-1)^+(d - size la) * (perm_partn la)%:R *: prod_gen H la.
Proof.
rewrite symHE_intcompn; symmetry.
transitivity
  (\sum_(la : 'P_d)
    (\sum_(c : intcompn d | sort geq c == la)
      (-1) ^+ (d - size c) *: prod_gen H la)).
  apply eq_bigr => la _; rewrite /perm_partn -sum1_card.
  rewrite natr_sum mulr_sumr -scaler_suml; congr (_ *: _).
  apply eq_big => /= co; rewrite inE //= => /eqP <-.
  rewrite mulr1; congr (_ ^+ (d - _)).
  by apply: perm_size; rewrite perm_sort.
rewrite (exchange_big_dep xpredT) //=.
apply eq_bigr => la _.
rewrite (eq_bigl (xpred1 (partn_of_compn la))) ?big_pred1_eq //.
by move=> mu; rewrite eq_sym -val_eqE.
Qed.

End HandE.


Lemma syme_symhE (d : nat) :
  d != 0%N ->
  'e_d = \sum_(1 <= i < d.+1) 'h_i * ((-1) ^+ i.-1 *: 'e_(d - i)) :> SF.
Proof. by apply: (symHE_rec (symh0 _ _)); exact: sum_symh_syme. Qed.

Lemma symh_symeE (d : nat) :
  d != 0%N ->
  'h_d = \sum_(1 <= i < d.+1) 'e_i * ((-1) ^+ i.-1 *: 'h_(d - i)) :> SF.
Proof. by apply: (symHE_rec (syme0 _ _)); exact: sum_syme_symh. Qed.

Lemma syme_to_symh d :
  'e_d = \sum_(la : 'P_d)
          (-1) ^+ (d - size la) * (perm_partn la)%:R *: 'h[la] :> SF.
Proof.
by apply: (symHE_intpartn (syme0 _ _) (symh0 _ _)); exact: sum_symh_syme.
Qed.

Lemma symh_to_syme d :
  'h_d = \sum_(la : 'P_d)
          (-1) ^+ (d - size la) * (perm_partn la)%:R *: 'e[la] :> SF.
Proof.
by apply: (symHE_intpartn (symh0 _ _) (syme0 _ _)); exact: sum_syme_symh.
Qed.


(** ** Newton formulas *)
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
under eq_bigr => i /= Hi do rewrite mult_symh_powersum subnKC // ?(ltnW Hi) //.
rewrite -big_nat -mulr_sumr mulrC.
case: (altP (mdeg m =P k)) => Hdegm; rewrite /= ?mul1r ?mul0r //.
rewrite exchange_big /=.
transitivity (\sum_(i < n) (m i)%:R : R).
  by rewrite -Hdegm mdegE -natr_sum.
apply: eq_bigr => i _ /=; rewrite -natr_sum; congr (_%:R).
have : m i <= k.
  by move: Hdegm; rewrite mdegE => <-; rewrite (bigD1 i) //=; apply leq_addr.
rewrite big_mkord (reindex_inj rev_ord_inj) /=.
under eq_bigr do rewrite subKn //.
move: (m i) => n {m Hdegm i} Hn.
rewrite (bigID (fun i : 'I_k => i < n)) /=.
under eq_bigr => i -> /= do [].
rewrite sum_nat_const /= muln1 big1 ?addn0; last by move=> i /negbTE ->.
rewrite cardE /= /enum_mem -enumT /=.
rewrite (eq_filter (a2 := (preim nat_of_ord (fun i => i < n)))) //.
rewrite -(size_map nat_of_ord).
by rewrite -filter_map val_enum_ord iota_ltn // size_iota.
Qed.

Lemma Newton_symh1 (k : nat) :
  k%:R *: 'h_k = \sum_(1 <= i < k.+1) 'p_i * 'h_(k - i) :> SF.
Proof using.
rewrite Newton_symh big_mkord (reindex_inj rev_ord_inj) /=.
rewrite big_add1 /= big_mkord; apply eq_bigr => i _.
by rewrite mulrC subKn.
Qed.

Lemma mult_syme_U k d i m :
  (('e_k : {mpoly R[n]}) * 'X_i ^+ d)@_m =
  [&& mdeg m == (k + d)%N, (d <= m i <= d.+1) &
   [forall j : 'I_n, (j != i) ==> (m j <= 1%N)]]%:R.
Proof using.
rewrite mpolyXn.
case: (altP (_ =P _)) => /= [degm | /negbTE Hneq]; first last.
  have /dhomog_nemf_coeff -> // :
    (('e_k : {mpoly R[n]}) * 'X_[(U_( i) *+ d)]) \is (k + d).-homog.
    by rewrite dhomogM ?syme_homog // dhomogX /= mdegMn mdeg1 mul1n.
  by rewrite /= Hneq.
case: leqP => /= dmi; first last.
  apply/memN_msupp_eq0/negP.
  rewrite (perm_mem (msuppMX _ _)) => /mapP => [/=[mon _]].
  move=> /(congr1 (fun m => m i)) Hmi; move: dmi; rewrite {}Hmi.
  by rewrite mnmDE mulmnE mnmE eqxx muln1 leqNgt ltnS leq_addr.
case: leqP => /= dmi2; first last.
  apply/memN_msupp_eq0/negP.
  rewrite (perm_mem (msuppMX _ _)) => /mapP => [/=[mon]].
  rewrite mem_msupp_mesym /mechar => /andP [_ /forallP /= /(_ i) Hmon].
  move=> /(congr1 (fun m => m i)) Hmi; move: dmi2; rewrite {}Hmi.
  rewrite mnmDE mulmnE mnmE eqxx muln1.
  by rewrite leqNgt !(addSn, ltnS) -(addn1 d) leq_add2l Hmon.
case: (boolP [forall _, _]) => [/forallP Hall | /=]; first last.
  rewrite negb_forall => /existsP [/= j].
  rewrite negb_imply -ltnNge => /andP [/negbTE neji mj].
  apply/memN_msupp_eq0/negP.
  rewrite (perm_mem (msuppMX _ _)) => /mapP => [/=[mon]].
  rewrite mem_msupp_mesym /mechar => /andP [_ /forallP /= /(_ j) Hmon].
  move=> /(congr1 (fun m => m j)) Hmj; move: mj; rewrite {}Hmj.
  by rewrite mnmDE mulmnE mnmE eq_sym {}neji muln0 add0n leqNgt ltnS Hmon.
have {}Hall x : x != i -> m x <= 1 by move=> H; apply: (implyP (Hall x)).
have leqUm : (U_(i) *+ d <= m)%MM.
  apply/mnm_lepP => j; rewrite mulmnE mnmE.
  by case: eqP => [<-|]; rewrite ?muln0 // muln1.
rewrite -(submK leqUm) addmC mcoeffMX mcoeff_mesym /mechar.
move: leqUm => /submK/(congr1 mdeg); rewrite mdegD degm mdegMn mdeg1 mul1n.
move/eqP; rewrite eqn_add2r => /eqP ->; rewrite eqxx /=.
case: forallP => // H; exfalso; apply: H => /= j.
rewrite mnmBE mulmnE mnmE eq_sym.
case: (altP (_ =P _)) => [->{j} | /Hall]; last by rewrite muln0 subn0.
by rewrite muln1 leq_subLR addn1.
Qed.

Lemma mul_ek_p1 (k : nat) :
  'e_k.+1 * 'p_1 = k.+2%:R *: 'e_k.+2 + 'm[hookpartn k.+2 1] :> SF.
Proof.
case: (leqP k.+1 n) => [ltkn | Hkn]; first last.
  rewrite !syme_geqnE //; last exact: ltnW.
  by rewrite mul0r scaler0 add0r symm_oversize // size_hookpartn.
have /homog_symmE -> : sympol ('e_k.+1 * 'p_1: SF) \is k.+2.-homog.
  by rewrite -(addn1 k.+1) dhomogM ?syme_homog ?symp_homog.
rewrite (syme_to_symm _ _ k.+2).
rewrite (bigD1 (hookpartn k.+2 1)) //=/symp_pol {1}mulr_sumr !raddf_sum /=.
rewrite [RHS]addrC -[X in _ = X + _]scale1r; congr ((_ *: _) + _).
  have szhk11 : size (hookpartn k.+2 1) = k.+1 by rewrite size_hookpartn.
  rewrite (bigD1 ord0) //= big1 ?addr0; first last.
    case: (altP (n =P 1%N)) => [neq1 [i Hi] | nneq1 i /negbTE in0].
      by rewrite -val_eqE /= -lt0n leqNgt -neq1 Hi.
    rewrite mult_syme_U.
    case: (boolP [&& _, _ & _]) => // /and3P [_ _ /forallP/(_ ord0)].
    rewrite eq_sym {}in0 /= /mpart szhk11 ltkn.
    by rewrite mnmE hookpartnE.
  rewrite mult_syme_U.
  rewrite mdeg_mpart ?szhk11 // sumn_intpartn addn1 eqxx /=.
  rewrite {1 2}/mpart szhk11 ltkn mnmE {1 2}hookpartnE //=.
  case: forallP => // H; exfalso; apply: H => /= j.
  apply/implyP => /negbTE jn0.
  rewrite /mpart szhk11 ltkn mnmE hookpartnE /= //.
  case: j jn0 => [[|j]] //= Hj _ {Hj}.
  by rewrite nth_nseq; case: ltnP.
rewrite (bigD1 (colpartn k.+2)) /=; first last.
  by rewrite -val_eqE /= colpartnE !hookpartnE.
rewrite [X in _ + X]big1 ?addr0 => [| la /andP[lahk lacol] ]; first last.
  case: (leqP (size la) n) => szla; last by rewrite symm_oversize // scaler0.
  rewrite {1}mulr_sumr !raddf_sum /= big1 ?scale0r // => i /= _.
  rewrite mult_syme_U.
  case: (boolP [&& _, _ & _]) => //= /and3P [_ H2 /forallP H]; exfalso.
  case: (altP (i =P ord0)) => [ieq0 | ineq0].
  - subst i; case Hla0 : (mpart la ord0) H2 => [|[|[|l0]]] _ //=.
    + move: Hla0 {lahk H}; rewrite /mpart {}szla mnmE //= => la0.
      move: lacol; rewrite (colpartnP (x0 := 0) (la := la)) ?eqxx //.
      by rewrite -nth0; case: la la0 => [[|l0 la]] //= _ ->.
    + move: Hla0 {lacol}; rewrite /mpart szla mnmE //= => la0.
      move: lahk; suff -> : la = hookpartn k.+2 1 by rewrite eqxx.
      case: (ltnP 1 n) => [lt1n|]; first last.
        rewrite ltnS leqn0 => /eqP Hn; subst n0.
        move: ltkn; rewrite ltnS leqn0 => /eqP Hk; subst k.
        rewrite hookpartn_row; case: (intpartn2 la) => [-> // | lacol].
        by move: szla; rewrite lacol size_colpartn.
      move/(_ (Ordinal lt1n)): H; rewrite -val_eqE /=.
      rewrite /mpart szla /= mnmE /= => /(hookpartnPE 0) ->.
      by rewrite la0.
  - move: (H ord0) lacol; rewrite eq_sym {}ineq0 /= /mpart szla mnmE.
    by move/colpartnP => ->; rewrite eqxx.
case: (leqP k.+2 n) => {ltkn}ltk1n; first last.
  by rewrite !symm_oversize ?size_colpartn // !scaler0.
congr (_ *: _); rewrite mulr_sumr raddf_sum /=.
rewrite (bigID (fun i : 'I_n => i < k.+2)) /=.
rewrite [X in _ + X]big1 ?addr0 => [|i]; first last.
  rewrite -leqNgt mult_syme_U => ltk1i.
  case: (boolP [&& _, _ & _]) => //= /and3P [_ Hnthi _]; exfalso.
  move: Hnthi; rewrite /mpart size_colpartn ltk1n mnmE colpartnE nth_nseq.
  by rewrite (ltnNge i _) ltk1i.
transitivity (\sum_(0 <= i < k.+2) 1 : R); last by rewrite sumr_const_nat subn0.
rewrite [RHS](big_nat_widen _ _ _ _ _ ltk1n) big_mkord /=.
apply eq_bigr => i ltik2.
rewrite mult_syme_U.
rewrite mdeg_mpart ?size_colpartn // sumn_intpartn addn1 eqxx /=.
rewrite /mpart size_colpartn ltk1n mnmE {1 2}colpartnE nth_nseq ltik2 /=.
case: forallP => // H; exfalso; apply: H => /= j.
apply/implyP => /negbTE jn0.
by rewrite mnmE colpartnE nth_nseq; case: ltnP.
Qed.

Lemma mul_ek_pk (k l : nat) :
  'e_k.+1 * 'p_l.+2 =
  'm[hookpartn (k + l).+3 l.+1] + 'm[hookpartn (k + l).+3 l.+2] :> SF.
Proof.
have szhook2 : size (hookpartn (k + l).+3 l.+2) = k.+1.
  rewrite size_hookpartn; last by rewrite !ltnS leq_addl.
  by rewrite !subSS -!addSn addnK.
have szhook1 : size (hookpartn (k + l).+3 l.+1) = k.+2.
  rewrite size_hookpartn; last by rewrite !ltnS -addSn leq_addl.
  by rewrite !subSS -!addSn addnK.
have hook2ok : l.+1 < (k + l).+2 by rewrite !ltnS leq_addl.
have hook1ok : l < (k + l).+2 by apply ltnW.
case: (leqP k.+1 n) => [ltkn | Hkn]; first last.
  rewrite !syme_geqnE // mul0r.
  by rewrite !symm_oversize ?addr0 // ?szhook1 ?szhook2 //; apply ltnW.
have /homog_symmE -> : sympol ('e_k.+1 * 'p_l.+2: SF) \is (k + l).+3.-homog.
  by rewrite -addSn -!addnS dhomogM ?syme_homog ?symp_homog.
rewrite (bigD1 (hookpartn (k + l).+3 l.+2)) //=.
rewrite /symp_pol {1}mulr_sumr !raddf_sum /=.
rewrite [RHS]addrC -[X in _ = X + _]scale1r; congr ((_ *: _) + _).
  rewrite {szhook1 hook1ok} (bigD1 ord0) //= big1 ?addr0; first last.
    case: (altP (n =P 1%N)) => [neq1 [i ltin]| nneq1 i /negbTE in0].
      by rewrite -val_eqE /= -lt0n leqNgt -neq1 ltin.
    rewrite mult_syme_U.
    case: (boolP [&& _, _ & _]) => // /and3P [_ _ /forallP/(_ ord0)].
    rewrite eq_sym {}in0 /= /mpart szhook2 ltkn.
    by rewrite mnmE hookpartnE.
  rewrite mult_syme_U.
  rewrite mdeg_mpart ?szhook2 // sumn_intpartn !addSn !addnS eqxx /=.
  rewrite {1 2}/mpart szhook2 ltkn mnmE.
  rewrite {1 2}hookpartnE //= leqnSn leqnn /=.
  case: forallP => // H; exfalso; apply: H => /= j.
  apply/implyP => /negbTE jn0.
  rewrite /mpart szhook2 ltkn mnmE hookpartnE //=.
  case: j jn0 => [[|j]]//= Hj _ {Hj}.
  by rewrite nth_nseq; case: ltnP.
rewrite (bigD1 (hookpartn (k + l).+3 l.+1)) //=; first last.
  by rewrite -val_eqE /= !hookpartnE //= eqseq_cons !eqSS presentSn.ieqi1F.
rewrite /symp_pol {1}mulr_sumr !raddf_sum /=.
rewrite -[RHS]addr0; congr (_ + _).
  case: (leqP k.+2 n) => {ltkn} ltk1n; first last.
    by rewrite !symm_oversize ?size_colpartn ?szhook1 // !scaler0.
  rewrite {szhook2 hook2ok} (bigD1 ord0) //= big1 ?addr0; first last.
    case: (altP (n =P 1%N)) => [ltin [i ine0]| nne1 i /negbTE ine0].
      by rewrite -val_eqE /= -lt0n leqNgt -ltin ine0.
    rewrite mult_syme_U.
    case: (boolP [&& _, _ & _]) => // /and3P [_ _ /forallP/(_ ord0)].
    rewrite eq_sym {}ine0 /= /mpart szhook1 ltk1n.
    by rewrite mnmE hookpartnE.
  rewrite -[RHS]scale1r; congr (_ *: _).
  rewrite mult_syme_U.
  rewrite mdeg_mpart ?szhook1 // sumn_intpartn !addSn !addnS eqxx /=.
  rewrite {1 2}/mpart szhook1 ltk1n mnmE.
  rewrite {1 2}hookpartnE //= leqnSn leqnn /=.
  case: forallP => // H; exfalso; apply: H => /= j.
  apply/implyP => /negbTE jn0.
  rewrite /mpart szhook1 ltk1n mnmE hookpartnE //=.
  case: j jn0 => [[|j]]//= Hj _ {Hj}.
  by rewrite nth_nseq; case: ltnP.
rewrite {szhook1 hook1ok szhook2 hook2ok} big1 => [| la /andP[lahk1 lahk2]]//.
case: (leqP (size la) n) => szla; last by rewrite symm_oversize // scaler0.
rewrite {1}mulr_sumr !raddf_sum /= big1 ?scale0r // => i /= _.
rewrite mult_syme_U.
case: (boolP [&& _, _ & _]) => //= /and3P [_ Hnthi /forallP H]; exfalso.
case: (ltnP 1 n) => [lt1n|neq1]; first last.
  have {}neq1 : n = 1%N.
    by apply anti_leq; rewrite neq1 /= (leq_ltn_trans _ ltkn).
  move: ltkn {lahk2 H}; rewrite neq1 ltnS leqn0 => /eqP Hk; subst k.
  move: szla; rewrite {}neq1.
  case: la Hnthi lahk1  => [[|l0 [|]]] //= H _.
  rewrite -val_eqE /= add0n hookpartn_row rowpartnE.
  move: H; rewrite addn0 add0n => /andP [/eqP ->].
  by rewrite eqxx.
case: (altP (i =P ord0)) => [ieq0 | /negbTE ineq0].
- subst i; move: Hnthi; rewrite /mpart szla mnmE => /andP/= [H1 H2].
  move: lahk1 lahk2.
  move/(_ (Ordinal lt1n)): H; rewrite -val_eqE /=.
  rewrite /mpart szla /= mnmE /= => /(hookpartnPE 0).
  case (leqP (nth 0%N la 0) l.+2) => H3.
  + have {H1 H2 H3} -> /= : nth 0%N la 0 = l.+2.
      by apply/esym/anti_leq; rewrite H1 H3.
    by move=> ->; rewrite eqxx.
  + have {H1 H2 H3} -> /= : nth 0%N la 0 = l.+3.
      by apply/esym/anti_leq; rewrite H3 H2.
    by move=> ->; rewrite eqxx.
- move: (H ord0) Hnthi; rewrite eq_sym {lahk1 lahk2}ineq0 /= /mpart szla mnmE.
  move/colpartnP ->; rewrite mnmE /= colpartnE nth_nseq.
  by case: (i < _).
Qed.

Lemma expri2 i : (-1) ^+ i.+2 = (-1) ^+ i :> R.
Proof. by rewrite !exprS !mulN1r opprK. Qed.
Lemma Newton_syme1 (k : nat) :
  k%:R *: 'e_k =
  \sum_(1 <= i < k.+1) (-1) ^+ i.+1 *: 'p_i * 'e_(k - i) :> SF.
Proof using.
case: k => [|[|k]]; first by rewrite scale0r big_nil.
  rewrite scale1r /index_iota big_cons big_nil addr0.
  by rewrite subnn syme0 sympe1E mulr1 -(expr1 (-1)) sqrr_sign scale1r.
rewrite big_nat_recl // -(expr1 (-1)) sqrr_sign scale1r.
rewrite subn1 /= mulrC mul_ek_p1 -[LHS]addr0 -addrA; congr (_ + _).
apply esym; rewrite big_add1 /=.
rewrite big_nat_recr //= subnn syme0 mulr1 expr1 expri2.
rewrite big_nat (eq_bigr (fun i => (-1) ^+ i.+1 *: 'm[hookpartn k.+2 i.+2]
                   - (-1) ^+ i *: 'm[hookpartn k.+2 i.+1])); first last.
  move=> i /= ltin; rewrite expri2 -scaleNr -(mulrN1 ((-1) ^+ i)) -exprSr.
  rewrite -scalerDr -scalerAl; congr (_ *: _).
  by rewrite subSS subSn // mulrC mul_ek_pk -addnS subnK // addrC.
rewrite -big_nat telescope_sumr // expr0 scale1r.
rewrite [_ - _]addrC !addrA subrr add0r.
rewrite exprS mulN1r scaleNr -scalerBr.
by rewrite hookpartn_row -symp_to_symm subrr scaler0.
Qed.

Lemma Newton_syme (k : nat) :
  k%:R *: 'e_k =
  \sum_(0 <= i < k) (-1) ^+ (k - i).+1 *: 'e_i * 'p_(k - i) :> SF.
Proof.
rewrite Newton_syme1 big_mkord (reindex_inj rev_ord_inj) /=.
rewrite big_add1 /= big_mkord; apply eq_bigr => i _.
by rewrite mulrC subKn // scalerCA.
Qed.

End ChangeBasis.


(** ** Basis change from Schur to monomial *)

(** We start by doing the computation on [int] using [Kostka] and [KostkaInv]
and then tranfer to any commutative ring *)
Section SymsSymmInt.

Variable (n : nat) (d : nat).
Local Notation SF := {sympoly int[n.+1]}.
Implicit Type (la mu : 'P_d).

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
  rewrite [perm_eq _ _](_ : _ = false) /= ?mulr0 //; apply/negP => /perm_sumn.
  rewrite !sumnE -!/(mdeg _) -sumn_partm mpartK // sumn_intpartn => Habs.
  by move: Heq; rewrite sumn_intpartn Habs eq_refl.
- have Hpm : is_part_of_n d (partm m).
   by rewrite /= sumn_partm Heq sumn_intpartn eq_refl /=.
  rewrite (bigD1 (IntPartN Hpm)) //= big1 ?addr0.
  + rewrite mcoeffZ (mcoeff_symm _ _ (size_partm _)).
    rewrite perm_sym partm_permK /= mulr1.
    congr _%:R.
    rewrite -Kostka_any ?leqSpred // [RHS](Kostka_any _ (size_partm m)).
    by apply perm_KostkaMon; apply: partm_permK.
  + move=> mu Hmu; rewrite mcoeffZ.
    case: (leqP (size mu) n.+1) => [Hszl | /symm_oversize ->]; first last.
      by rewrite mcoeff0 mulr0.
    rewrite mcoeff_symm //=.
    suff /negbTE -> : ~~ (perm_eq (mpart (n := n.+1) mu) m) by rewrite mulr0.
    move: Hmu; apply contra => /perm_partm H.
    apply/eqP/val_inj => /=; rewrite -H.
    by rewrite mpartK.
Qed.

Lemma syms_symm_partdom_int la :
  's[la] =
  'm[la] + \sum_(mu : 'PDom_d | (mu < la)%O) 'K(la, mu) *: 'm[mu] :> SF.
Proof.
rewrite -(unitrig_sum1l (fun mu : 'PDom_d => 'm[mu]) la (Kostka_unitrig _ d)).
by rewrite -syms_symm_int.
Qed.

Lemma symm_syms_int la :
  'm[la] = \sum_(mu : 'P_d) KostkaInv la mu *: 's[mu] :> SF.
Proof.
rewrite /KostkaInv.
apply: (Minv_lincombl (Kostka_unitrig _ d)
                      (F := fun mu => 's[mu]) (G := fun mu => 'm[mu])).
exact: syms_symm_int.
Qed.

Lemma symm_syms_partdom_int la :
  'm[la] =
  's[la] + \sum_(mu : 'PDom_d | (mu < la)%O) KostkaInv la mu *:'s[mu] :> SF.
Proof.
rewrite -(unitrig_sum1l (fun mu : 'PDom_d => 's[mu]) la (KostkaInv_unitrig d)).
by rewrite -symm_syms_int.
Qed.

End SymsSymmInt.


Section SymsSymm.

Variable (n : nat) (R : comRingType) (d : nat).
Local Notation SF := {sympoly R[n.+1]}.
Implicit Type (la mu : 'P_d).

Lemma syms_symm la :
  's[la] = \sum_(mu : 'P_d) 'K(la, mu)%:R *: 'm[mu] :> SF.
Proof.
rewrite -(map_syms [rmorphism of intr]) syms_symm_int.
rewrite rmorph_sum /=; apply eq_bigr => i _.
rewrite scale_map_sympoly map_symm /=; congr (_ *: _).
by rewrite mulrz_nat.
Qed.

Lemma syms_symm_partdom la :
  's[la] =
  'm[la] + \sum_(mu | (mu < la :> 'PDom_d)%O) 'K(la, mu) *: 'm[mu] :> SF.
Proof.
rewrite -(map_syms [rmorphism of intr]) syms_symm_partdom_int.
rewrite rmorphD rmorph_sum /= map_symm; congr (_ + _); apply eq_bigr => i _.
rewrite scale_map_sympoly map_symm /=; congr (_ *: _).
by rewrite mulrz_nat.
Qed.

Lemma symm_syms la :
  'm[la] = \sum_(mu : 'P_d) 'K^-1(la, mu) *: 's[mu] :> SF.
Proof.
rewrite -(map_symm [rmorphism of intr]) symm_syms_int.
rewrite rmorph_sum /=; apply eq_bigr => i _.
by rewrite scale_map_sympoly map_syms.
Qed.

Lemma symm_syms_partdom la :
  'm[la] =
  's[la] + \sum_(mu | (mu < la :> 'PDom_d)%O) 'K^-1(la, mu) *: 's[mu] :> SF.
Proof.
rewrite -(map_symm [rmorphism of intr]) symm_syms_partdom_int.
rewrite rmorphD rmorph_sum /= map_syms; congr (_ + _); apply eq_bigr => i _.
by rewrite scale_map_sympoly map_syms.
Qed.

End SymsSymm.


(** ** Basis change from complete and elementary to Schur *)

(** We start by doing the computation on [int] using [Kostka] and [KostkaInv]
and then tranfer to any commutative ring *)
Section SymheSymsInt.

Variables (n : nat) (d : nat).
Local Notation SF := {sympoly int[n.+1]}.
Implicit Type la mu : 'P_d.

Lemma symh_syms_int mu :
  'h[mu] = \sum_(la : 'P_d) 'K(la, mu) *: 's[la] :> SF.
Proof.
case: mu => [mu Hmu] /=; rewrite /prod_symh /prod_gen /=.
elim: mu d Hmu => [|m mu IHmu] deg.
  rewrite big_nil => /andP [/eqP /= /esym Hd _].
  symmetry; subst deg; rewrite (big_pred1 (rowpartn 0)); first last.
    by move=> i; symmetry; apply/eqP/val_inj; rewrite /= intpartn0.
  by rewrite syms0 -rowpartn0E Kostka_diag scale1r.
move=> /=/andP[/eqP/esym Hdeg /andP [_ Hpart]].
rewrite big_cons /= {}(IHmu (sumn mu)) /= ?eq_refl ?Hpart //.
under [RHS]eq_bigr do rewrite Kostka_ind ?Hdeg // natr_sum scaler_suml.
rewrite mulr_sumr [RHS](exchange_big_dep predT) //=.
apply eq_bigr => la _.
rewrite -scalerAr -scaler_sumr mulrC syms_symhM; congr (_ *: _).
rewrite addnC in Hdeg.
rewrite (reindex _ (onW_bij _ (cast_intpartn_bij Hdeg))) /=.
apply eq_big => [nu | nu _].
- by case: nu => nu /= Hnu; rewrite cast_intpartnE /=.
- by apply val_inj; rewrite /= Schur_cast.
Qed.

Lemma symh_syms_partdom_int mu :
  'h[mu] =
  's[mu] + \sum_(la | (mu < la :> 'PDom_d)%O) 'K(la, mu) *: 's[la] :> SF.
Proof.
rewrite -(unitrig_sum1r (fun la : 'PDom_d => 's[la]) mu (Kostka_unitrig _ d)).
by rewrite -symh_syms_int.
Qed.

Lemma syms_symh_int mu :
  's[mu] = \sum_(la : 'P_d) KostkaInv la mu *: 'h[la] :> SF.
Proof.
rewrite /KostkaInv.
apply: (Minv_lincombr (Kostka_unitrig _ d)
         (G := fun mu : 'PDom_d => 's[mu]) (F := fun mu : 'PDom_d => 'h[mu])).
exact: symh_syms_int.
Qed.

Lemma syms_symh_partdom_int mu :
  's[mu] =
  'h[mu] + \sum_(la | (mu < la :> 'PDom_d)%O) KostkaInv la mu *: 'h[la] :> SF.
Proof.
rewrite -(unitrig_sum1r (fun la : 'PDom_d => 'h[la]) mu (KostkaInv_unitrig d)).
by rewrite -syms_symh_int.
Qed.

Local Notation "la '^~'" := (conj_intpartn la) (at level 10).

Lemma syme_syms_int mu :
  'e[mu] = \sum_(la : 'P_d) 'K(la, mu) *: 's[la^~] :> SF.
Proof.
case: mu => [mu Hmu] /=; rewrite /prod_syme /prod_gen /=.
elim: mu d Hmu => [|m mu IHmu] deg.
  rewrite big_nil => /andP [/eqP /= /esym Hd _].
  symmetry; subst deg; rewrite (big_pred1 (rowpartn 0)); first last.
    by move=> i; symmetry; apply/eqP/val_inj; rewrite /= intpartn0.
  by rewrite syms0 -rowpartn0E Kostka_diag scale1r.
move=> /= /andP[/eqP/esym Hdeg /andP [_ Hpart]].
rewrite big_cons /= {}(IHmu (sumn mu)) /= ?eq_refl ?Hpart //.
under [RHS]eq_bigr do rewrite Kostka_ind ?Hdeg // natr_sum scaler_suml.
rewrite mulr_sumr [RHS](exchange_big_dep predT) //=.
apply eq_bigr => la _.
rewrite -scalerAr -scaler_sumr mulrC syms_symeM; congr (_ *: _).
rewrite addnC in Hdeg.
rewrite (reindex _ (onW_bij _ (inv_bij (@conj_intpartnK _)))) /=.
rewrite (reindex _ (onW_bij _ (cast_intpartn_bij Hdeg))) /=.
apply eq_big => [nu | nu _].
- case: nu => nu /= Hnu; rewrite cast_intpartnE /= vb_strip_conjE //.
  by move: Hnu => /andP [].
- by apply val_inj; rewrite /= -cast_conj_inpart Schur_cast.
Qed.

Lemma syme_syms_partdom_int mu :
  'e[mu] =
  's[mu^~] + \sum_(la | (mu < la :> 'PDom_d)%O) 'K(la, mu) *: 's[la^~] :> SF.
Proof.
rewrite -(unitrig_sum1r (fun la : 'PDom_d => 's[la^~]) mu (Kostka_unitrig _ d)).
by rewrite -syme_syms_int.
Qed.

Lemma syms_syme_int mu :
  's[mu^~] = \sum_(la : 'P_d) KostkaInv la mu *: 'e[la] :> SF.
Proof.
rewrite /KostkaInv.
apply: (Minv_lincombr (Kostka_unitrig _ d)
         (G := fun mu : 'PDom_d => 's[mu^~]) (F := fun mu : 'PDom_d => 'e[mu])).
exact: syme_syms_int.
Qed.

Lemma syms_syme_partdom_int mu :
  's[mu^~] =
  'e[mu] + \sum_(la | (mu < la :> 'PDom_d)%O) KostkaInv la mu *: 'e[la] :> SF.
Proof.
rewrite -(unitrig_sum1r (fun la : 'PDom_d => 'e[la]) mu (KostkaInv_unitrig d)).
by rewrite -syms_syme_int.
Qed.

End SymheSymsInt.

Section SymheSyms.

Variables (R : comRingType) (n : nat) (d : nat).
Local Notation SF := {sympoly R[n.+1]}.
Implicit Type la mu : 'P_d.

Lemma symh_syms mu : 'h[mu] = \sum_(la : 'P_d) 'K(la, mu) *: 's[la] :> SF.
Proof.
rewrite -(map_symh_prod [rmorphism of intr]) symh_syms_int.
rewrite rmorph_sum /=; apply eq_bigr => i _.
rewrite scale_map_sympoly map_syms /=; congr (_ *: _).
by rewrite mulrz_nat.
Qed.

Lemma symh_syms_partdom mu :
  'h[mu] =
  's[mu] + \sum_(la | (mu < la :> 'PDom_d)%O) 'K(la, mu) *: 's[la] :> SF.
Proof.
rewrite -(map_symh_prod [rmorphism of intr]) symh_syms_partdom_int.
rewrite rmorphD rmorph_sum /= map_syms; congr (_ + _); apply eq_bigr => i _.
rewrite scale_map_sympoly map_syms /=; congr (_ *: _).
by rewrite mulrz_nat.
Qed.

Lemma syms_symh mu : 's[mu] = \sum_(la : 'P_d) 'K^-1(la, mu) *: 'h[la] :> SF.
Proof.
rewrite -(map_syms [rmorphism of intr]) syms_symh_int.
rewrite rmorph_sum /=; apply eq_bigr => i _.
by rewrite scale_map_sympoly map_symh_prod.
Qed.

Lemma syms_symh_partdom mu :
  's[mu] =
  'h[mu] + \sum_(la | (mu < la :> 'PDom_d)%O) 'K^-1(la, mu) *: 'h[la] :> SF.
Proof.
rewrite -(map_syms [rmorphism of intr]) syms_symh_partdom_int.
rewrite rmorphD rmorph_sum /= map_symh_prod; congr (_ + _); apply eq_bigr => i _.
by rewrite scale_map_sympoly map_symh_prod.
Qed.

Local Notation "la '^~'" := (conj_intpartn la) (at level 10).

Lemma syme_syms mu : 'e[mu] = \sum_(la : 'P_d) 'K(la, mu) *: 's[la ^~] :> SF.
Proof.
rewrite -(map_syme_prod [rmorphism of intr]) syme_syms_int.
rewrite rmorph_sum /=; apply eq_bigr => i _.
rewrite scale_map_sympoly map_syms /=; congr (_ *: _).
by rewrite mulrz_nat.
Qed.

Lemma syme_syms_partdom mu :
  'e[mu] =
  's[mu^~] + \sum_(la | (mu < la :> 'PDom_d)%O) 'K(la, mu) *: 's[la^~] :> SF.
Proof.
rewrite -(map_syme_prod [rmorphism of intr]) syme_syms_partdom_int.
rewrite rmorphD rmorph_sum /= map_syms; congr (_ + _); apply eq_bigr => i _.
rewrite scale_map_sympoly map_syms /=; congr (_ *: _).
by rewrite mulrz_nat.
Qed.

Lemma syms_syme mu : 's[mu^~] = \sum_(la : 'P_d) 'K^-1(la, mu) *: 'e[la] :> SF.
Proof.
rewrite -(map_syms [rmorphism of intr]) syms_syme_int.
rewrite rmorph_sum /=; apply eq_bigr => i _.
by rewrite scale_map_sympoly map_syme_prod.
Qed.

Lemma syms_syme_partdom mu :
  's[mu^~] =
  'e[mu] + \sum_(la | (mu < la :> 'PDom_d)%O) 'K^-1(la, mu) *: 'e[la] :> SF.
Proof.
rewrite -(map_syms [rmorphism of intr]) syms_syme_partdom_int.
rewrite rmorphD rmorph_sum /= map_syme_prod; congr (_ + _); apply eq_bigr => i _.
by rewrite scale_map_sympoly map_syme_prod.
Qed.

End SymheSyms.


(** ** Basis change from complete to power sums *)
Section ChangeBasisSymhPowerSum.

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
rewrite -big_enum /= charf0P => Hchar.
rewrite -[RHS](big_map (@cnval n) xpredT
   (fun c : seq nat => \Pi c *: \prod_(i <- c) 'p_i)).
rewrite enum_intcompnE.
have [m/ltnW] := ubnP n; elim: m => [| m IHm] in n *.
  rewrite leqn0 => /eqP ->.
  by rewrite big_seq1 big_nil symh0 /= invr1 scale1r.
rewrite leq_eqVlt => /orP [/eqP Hm|]; last by rewrite ltnS; exact: IHm.
rewrite enum_compnE Hm // -Hm big_flatten /=.
have Hn : (n%:R : R) != 0 by rewrite Hchar Hm.
apply (scalerI Hn); rewrite Newton_symh1 /index_iota subn1 /=.
rewrite scaler_sumr big_map; apply eq_big_seq => i.
rewrite mem_iota add1n ltnS => /andP [Hi Hin].
rewrite big_map big_seq.
rewrite (eq_bigr
    (fun c => (n%:R^-1 *: 'p_i) * (\Pi c *: \prod_(j <- c) 'p_j))); first last.
  move=> s; rewrite -enum_compnP /is_comp_of_n /= => /andP [/eqP -> _].
  rewrite subnKC // big_cons scalerAr.
  by rewrite natrM invfM -!scalerAr -scalerAl scalerA mulrC.
rewrite -big_seq -mulr_sumr {}IHm; first last.
  by rewrite leq_subLR Hm -(add1n m) leq_add2r.
by rewrite -scalerAl scalerA divff // scale1r.
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
- move=> c; apply/eqP/idP => [<- | Hperm];
      first by rewrite /partn_of_compn /= perm_sort.
  apply val_inj => /=; apply (sorted_eq geq_trans) => //.
  by rewrite (permPr Hperm) perm_sort.
- move=> c /eqP <-; congr (_ *: _).
  rewrite /prod_symp /prod_gen; apply: perm_big.
  by rewrite /partn_of_compn perm_sym /= perm_sort.
Qed.

Lemma intcompn_cons_sub_proof i n (c : intcompn (n - i)) :
  i != 0%N -> i <= n -> is_comp_of_n n (i :: c).
Proof.
move=> Hi Hin.
rewrite /is_comp_of_n /= intcompn_sumn subnKC // eq_refl /=.
rewrite /is_comp inE negb_or eq_sym Hi /=.
exact: intcompnP.
Qed.
Local Definition intcompn_cons i (Hi : i != 0%N) n (Hin : i <= n) c :=
  IntCompN (intcompn_cons_sub_proof c Hi Hin).

Lemma intcompn_behead_sub_proof i n (c : intcompn n) :
  i != 0%N -> i <= n ->
  is_comp_of_n (n - i)%N (if head 0%N c == i then behead c else rowcompn (n-i)).
Proof.
case: c => [[|c0 c] /= /andP [/eqP <- Hcomp]] Hi0 Hin.
  by exfalso; move: Hin Hi0; rewrite leqn0 => /eqP ->; rewrite eq_refl.
case: (altP (c0 =P i)) => Hc0 /=; last exact: rowcompnP.
subst c0; rewrite addKn eq_refl /=.
move: Hcomp; rewrite /is_comp inE; apply contra => ->.
by rewrite orbT.
Qed.
Local Definition intcompn_behead i (Hi : i != 0%N) n (Hin : i <= n) c :=
  IntCompN (intcompn_behead_sub_proof c Hi Hin).


Lemma part_sumn_count l :
  is_part l ->
  (\sum_(i < (sumn l).+1 | val i \in l) i * (count_mem (val i) l))%N
  = sumn l.
Proof.
have [b Hb]:= ubnPleq (sumn l).+1.
have {}Hb : all (gtn b) l.
  elim: l Hb => //= l0 l IHl H; apply/andP; split.
  - exact: (leq_ltn_trans (leq_addr _ _) H).
  - by apply IHl; exact: (leq_ltn_trans (leq_addl _ _) H).
elim: l Hb => [_ _ | l0 l IHl]; first by apply big1.
move=> /andP [Hb /IHl{IHl}Hrec] Hpart.
move: Hb => /= Hl0b.
have /= Hl0 := part_head_non0 Hpart.
move: Hpart => /andP [_] {}/Hrec Hrec.
rewrite (bigD1 (Ordinal Hl0b)) /=; last by rewrite inE eq_refl.
rewrite eq_refl /= mulnDr muln1 -addnA; congr (_ + _)%N.
under eq_bigr => i /andP[_ /negbTE Hi].
  rewrite -val_eqE /= in Hi.
  by rewrite eq_sym Hi add0n over.
case: (boolP (l0 \in l)) => Hl0l.
- rewrite -{}Hrec [RHS](bigD1 (Ordinal Hl0b)) //=; congr (_ + _)%N.
  apply: eq_bigl => i; congr (_ && _); rewrite inE.
  by case: eqP => [->|].
- rewrite (count_memPn Hl0l) muln0 add0n.
  rewrite -{}Hrec; apply eq_bigl => i.
  rewrite inE; case: (altP (i =P l0 :> nat)) => [Hi | Hil0] /=.
  + subst l0; rewrite (negbTE Hl0l).
    by apply negbTE; rewrite negbK; apply/eqP/val_inj.
  + by rewrite Hil0 andbT.
Qed.

Lemma coeff_symh_to_symp n (l : 'P_n) :
  [char R] =i pred0 ->
  \sum_(c : intcompn n | perm_eq l c) \Pi c = (zcard l)%:R^-1 :> R.
Proof.
rewrite charf0P => Hchar.
case: l => l /= /andP [/eqP].
have [m/ltnW] := ubnP n; elim: m => [| m IHm] in n l *.
  rewrite leqn0 => /eqP -> /part0 H{}/H ->{l}.
  rewrite zcard_nil /=.
  rewrite (eq_bigl (xpred1 (rowcompn 0))); first by rewrite big_pred1_eq.
  move=> i; apply/idP/eqP => [Hperm | /(congr1 val)/= -> //].
  by apply val_inj => /=; apply/nilP; rewrite /nilp -(perm_size Hperm).
rewrite leq_eqVlt => /orP [/eqP Hm|]; last by rewrite ltnS; exact: IHm.
move => Hsum Hpart.
have head_intcompn (c : intcompn n) : head 0%N c < n.+1.
  rewrite ltnS; case: c => [[|c0 c]] //= /andP [/eqP <- _].
  exact: leq_addr.
pose headcomp c := Ordinal (head_intcompn c).
rewrite (partition_big headcomp xpredT) //=.
under eq_bigr do under eq_bigl do rewrite -val_eqE /=.
rewrite (bigID (fun j => val j \in l)) /= [X in _ + X]big1 ?addr0; first last.
  move=> i Hi; apply big1 => [] [[|c0 c]/= _ /andP[Hperm /eqP Hhead]]; exfalso.
  - by move/perm_sumn: Hperm; rewrite /= Hsum Hm.
  - subst c0; move/perm_mem: Hperm Hi => /(_ i).
    by rewrite inE eq_refl /= => ->.
rewrite (eq_bigr (fun i => n%:R^-1 * (zcard (rem (val i) l))%:R^-1 : R));
      first last => [/= i Hi|].
  have H0i := in_part_non0 Hpart Hi.
  have Hin : i <= n by rewrite -ltnS.
  rewrite (reindex (intcompn_cons H0i Hin)) /=; first last.
    exists (intcompn_behead H0i Hin) => c; rewrite inE => /andP [Hperm Hhead];
        apply val_inj; rewrite /= ?eq_refl //.
    rewrite /= Hhead.
    case: c Hperm Hhead => [[|c0 c]] //= _.
    + by move/perm_sumn; rewrite /= Hsum {1}Hm.
    + by move=> _ /eqP ->.
  under eq_bigl => c do
    rewrite eq_refl andbT (permPl (perm_to_rem Hi)) perm_cons.
  under eq_bigr => c _ do rewrite intcompn_sumn subnKC // natrM invfM.
  rewrite -mulr_sumr IHm //.
  - move: H0i; case i => [/= [//|i']] _ _.
    by rewrite Hm subSS leq_subr.
  - rewrite -[LHS](addKn i).
    have /perm_sumn /= <- := perm_to_rem Hi.
    by rewrite Hsum.
  - move: Hpart; rewrite !is_part_sortedE => /andP[Hsort H0].
    have Hrem := rem_subseq (val i) l; apply/andP; split.
    + exact: (subseq_sorted _ Hrem).
    + by move: H0; apply contra; apply (mem_subseq Hrem).
rewrite {IHm} -mulr_sumr.
rewrite (eq_bigr (fun i => (val i * (count_mem (val i) l))%:R / (zcard l)%:R));
  first last => [i Hi|] /=.
  have H0i := in_part_non0 Hpart Hi.
  rewrite -(zcard_rem H0i Hi) [X in _ / X]natrM invfM -[LHS]mul1r !mulrA.
  congr (_ * _); rewrite divff // Hchar.
  rewrite muln_eq0 negb_or H0i /=.
  by move: Hi; apply contraL => /eqP H; apply/count_memPn.
rewrite -mulr_suml mulrA -[RHS]mul1r; congr (_ * _).
rewrite -natr_sum -Hsum part_sumn_count // mulrC divff //.
by rewrite Hchar Hsum Hm.
Qed.

Theorem symh_to_symp n :
  [char R] =i pred0 -> 'h_n = \sum_(l : 'P_n) (zcard l)%:R^-1 *: 'p[l] :> SF.
Proof.
move=> Hchar.
rewrite symh_to_symp_intpartn //; apply eq_bigr => l _.
by rewrite coeff_symh_to_symp.
Qed.

End ChangeBasisSymhPowerSum.


Section Generators.

Variables (n : nat) (R : comRingType).

Lemma prod_homog nv l (df : 'I_l -> nat) (mf : 'I_l -> {mpoly R[nv]}) :
  (forall i : 'I_l, mf i \is (df i).-homog) ->
  \prod_(i < l) mf i \is (\sum_(i < l) df i).-homog.
Proof using .
elim: l => [| l IHl] in df mf * => H.
  by rewrite !big_ord0 dhomog1.
rewrite !big_ord_recr /=; apply dhomogM; last exact: H.
by apply: IHl => i; exact: H.
Qed.

Variable   gen : forall nv : nat, nat -> {mpoly R[nv]}.
Hypothesis gen_homog : forall nv i : nat, gen nv i \is i.-homog.
Local Notation G nv := [tuple gen nv i.+1 | i < n].

Lemma homog_X_mPo_gen nv m : 'X_[m] \mPo G nv \is (mnmwgt m).-homog.
Proof using gen gen_homog.
rewrite comp_mpolyX /mnmwgt; apply: prod_homog => k.
by rewrite tnth_mktuple mulnC dhomogMn.
Qed.

Lemma pihomog_mPo nv p d :
  pihomog [measure of mdeg] d (p \mPo G nv) =
  (pihomog [measure of mnmwgt] d p) \mPo G nv.
Proof using gen gen_homog.
elim/mpolyind: p => [| c m p Hm Hc IHp] /=; first by rewrite !linear0.
rewrite !linearP /= {}IHp; congr (c *: _ + _).
case: (altP (mnmwgt m =P d)) => Hd.
- have/eqP := Hd; rewrite -(dhomogX R) => /pihomog_dE ->.
  by have:= homog_X_mPo_gen nv m; rewrite Hd => /pihomog_dE ->.
- rewrite (pihomog_ne0 Hd (homog_X_mPo_gen nv m)).
  rewrite (pihomog_ne0 Hd); first by rewrite linear0.
  by rewrite dhomogX.
Qed.

End Generators.


(** ** Symmetric polynomials expressed as polynomial in the elementary *)
Section MPoESymHomog.

Variables (n : nat) (R : comRingType).
Local Notation E nv := [tuple mesym nv R i.+1 | i < n].

Lemma mwmwgt_homogP (p : {mpoly R[n]}) d :
  reflect
    (forall nv, p \mPo E nv \is d.-homog)
    (p \is d.-homog for [measure of mnmwgt]).
Proof using.
rewrite !homog_piE.
apply (iffP eqP) => [Homog nv | H].
- by rewrite -Homog -(pihomog_mPo (fun nv i => dhomog_mesym nv R i)) pihomogP.
- apply pihomog_dE.
  suff -> : p = pihomog [measure of mnmwgt] d p by apply: pihomogP.
  apply msym_fundamental_un; apply esym.
  rewrite -(pihomog_mPo (fun nv i => dhomog_mesym nv R i)).
  exact: pihomog_dE.
Qed.

Lemma sym_fundamental_homog (p : {mpoly R[n]}) (d : nat) :
  p \is symmetric -> p \is d.-homog ->
  { t | t \mPo (E n) = p /\ t \is d.-homog for [measure of mnmwgt] }.
Proof.
move=> /sym_fundamental [t [Ht _]] Hhom.
exists (pihomog [measure of mnmwgt] d t); split.
- by rewrite -(pihomog_mPo (fun nv i => dhomog_mesym nv R i)) Ht pihomog_dE.
- exact: pihomogP.
Qed.

End MPoESymHomog.


Section SymPolF.

Variable R : comRingType.
Variable m : nat.
Implicit Type p : {sympoly R[m]}.

Local Notation SF p := (sym_fundamental (sympolP p)).

Definition sympolyf p := let: exist t _  := SF p in t.

Fact sympolyf_is_lrmorphism : lrmorphism sympolyf.
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


(** ** Fundamental theorem of symmetric polynomials *)
Lemma sympolyfP p : (sympolyf p) \mPo [tuple sympol 'e_i.+1 | i < m] = p.
Proof. by rewrite /sympolyf; case: (SF p) => f [] <- _. Qed.

Definition sympolyf_eval : {mpoly R[m]} -> {sympoly R[m]} :=
  mmap (GRing.in_alg {sympoly R[m]}) (fun i : 'I_m => 'e_i.+1).
Lemma sympolyf_evalE (q : {mpoly R[m]}) :
  q \mPo [tuple sympol 'e_i.+1 | i < m] = sympolyf_eval q.
Proof.
rewrite /sympolyf_eval /mmap /mmap1 comp_mpolyE.
rewrite raddf_sum /=; apply eq_bigr => mon _.
rewrite mulr_algl; congr (_ *: _).
rewrite rmorph_prod /=; apply eq_bigr => i _.
by rewrite tnth_mktuple rmorphX /=.
Qed.

Lemma sympolyfK p : sympolyf_eval (sympolyf p) = p.
Proof. by apply val_inj; rewrite /= -[RHS]sympolyfP sympolyf_evalE. Qed.

Lemma sympolyf_evalK q : sympolyf (sympolyf_eval q) = q.
Proof.
rewrite /sympolyf; case: (SF _) => [x [xeq _]].
move: xeq; rewrite -sympolyf_evalE.
exact: msym_fundamental_un.
Qed.

Fact sympolyf_eval_is_lrmorphism : lrmorphism sympolyf_eval.
Proof.
rewrite /sympolyf_eval; repeat split.
- by move=> u v; apply val_inj; rewrite /= raddfB.
- by move=> u v; apply val_inj; rewrite /= !rmorphM.
- by apply val_inj; rewrite /= !rmorph1.
- by move=> a u; apply val_inj; rewrite mmapZ /= mulr_algl.
Qed.
Canonical sympolyf_eval_additive   := Additive   sympolyf_eval_is_lrmorphism.
Canonical sympolyf_eval_rmorphism  := RMorphism  sympolyf_eval_is_lrmorphism.
Canonical sympolyf_eval_linear     := AddLinear  sympolyf_eval_is_lrmorphism.
Canonical sympolyf_eval_lrmorphism := LRMorphism sympolyf_eval_is_lrmorphism.

Lemma sympolyf_evalX (i : 'I_m) : sympolyf_eval 'X_i = 'e_i.+1.
Proof.
by apply val_inj; rewrite /= -sympolyf_evalE comp_mpolyXU nth_mktuple.
Qed.

End SymPolF.


Section Omega.

Variable R : comRingType.
Variable n0 : nat.
Local Notation n := n0.+1.
Implicit Type p : {sympoly R[n]}.
Local Notation SF p := (sym_fundamental (sympolP p)).

Fact omegasf_is_symmetric p :
  (sympolyf p) \mPo [tuple sympol 'h_i.+1 | i < n] \is @symmetric n R.
Proof.
rewrite comp_mpolyE; apply: rpred_sum => mon _; apply: rpredZ.
apply: rpred_prod => i _; rewrite tnth_mktuple.
by apply: rpredX; apply: sympolP.
Qed.
Definition omegasf p : {sympoly R[n]} := SymPoly (omegasf_is_symmetric p).

Lemma val_omegasf p :
  sympol (omegasf p) = (sympolyf p) \mPo [tuple sympol 'h_i.+1 | i < n].
Proof. by []. Qed.

Fact omegasf_is_lrmorphism : lrmorphism omegasf.
Proof.
rewrite /omegasf; repeat split.
- by move=> u v; apply val_inj; rewrite /= !raddfB.
- by move=> u v; apply val_inj; rewrite /= !rmorphM.
- by apply val_inj; by rewrite /= !rmorph1.
- by move=> a u; apply val_inj; rewrite /= !linearZ.
Qed.
Canonical omegasf_additive   := Additive   omegasf_is_lrmorphism.
Canonical omegasf_rmorphism  := RMorphism  omegasf_is_lrmorphism.
Canonical omegasf_linear     := AddLinear  omegasf_is_lrmorphism.
Canonical omegasf_lrmorphism := LRMorphism omegasf_is_lrmorphism.

Lemma omegasf_syme i : i <= n -> omegasf 'e_i = 'h_i.
Proof.
move=> Hi; apply val_inj; rewrite /= /sympolyf.
case: (SF 'e_i) => /= p [Hp _].
case: i Hi Hp => [_ |i Hi Hp] /=.
  rewrite !mesym0E /= => Hp.
  have {Hp} -> : p = 1 by apply msym_fundamental_un; rewrite Hp comp_mpoly1.
  rewrite comp_mpoly1.
  by have /= -> := congr1 val (symh0 n R).
have {Hp} -> : p = 'X_(Ordinal Hi).
  apply msym_fundamental_un; rewrite Hp comp_mpolyXU.
  by rewrite -tnth_nth tnth_mktuple.
by rewrite comp_mpolyXU -tnth_nth tnth_mktuple.
Qed.

Lemma omegasf_symh i : i <= n -> omegasf 'h_i = 'e_i.
Proof.
have [k/ltnW] := ubnP i; elim: k => [| k IHk] in i *.
  by rewrite leqn0 => /eqP ->; rewrite symh0 syme0 rmorph1.
rewrite leq_eqVlt => /orP [/eqP -> {i} lt_kn|]; last by rewrite ltnS => /IHk.
rewrite symh_symeE // rmorph_sum //= syme_symhE //.
rewrite !big_nat; apply eq_bigr => [][|j]//; rewrite !ltnS leq0n /= => le_jk.
rewrite subSS rmorphM linearZ /= IHk ?leq_subr //; first last.
  by apply ltnW; apply: (leq_ltn_trans (leq_subr _ _) lt_kn).
by rewrite omegasf_syme // (leq_ltn_trans le_jk lt_kn).
Qed.

Lemma omegasfK : involutive omegasf.
Proof.
move=> p; rewrite -(sympolyfK p).
rewrite (mpolyE (sympolyf p)); move: (sympolyf p) => q.
rewrite [sympolyf_eval _]raddf_sum !raddf_sum /=; apply eq_bigr => mon _.
rewrite !linearZ /=; congr (_ *: _).
rewrite mpolyXE_id !rmorph_prod /=; apply eq_bigr => i _.
rewrite !rmorphX /=; congr ( _ ^+ _).
by rewrite sympolyf_evalX omegasf_syme // omegasf_symh.
Qed.

Lemma omegasf_symp i : 0 < i <= n -> omegasf 'p_i = (-1) ^+ i.+1 *: 'p_i.
Proof.
rewrite andbC => /andP [lein].
have [j] := ubnPgeq i; elim: i lein j => [//| i IHi] /= ltin j.
  by move=> /(leq_trans _) H{}/H.
move=> H1 lt0j; move: H1.
rewrite leq_eqVlt orbC => /orP [/IHi->// | /eqP->{j lt0j}]; first exact: ltnW.
have {}IHi := IHi (ltnW ltin).
have := Newton_symh1 n0 R i.+1.
rewrite big_nat_recr //= subnn symh0 mulr1 addrC => /eqP.
have /= <- := subr_eq _ 'p_i.+1 => /eqP {1}<-.
rewrite linearP linearN linear_sum /= omegasf_symh //.
rewrite big_nat; under eq_bigr => j /andP[lt0j ltji1].
  by rewrite rmorphM /= IHi // omegasf_symh ?(leq_trans (leq_subr _ _)) // over.
rewrite -big_nat (Newton_syme1 n0 R i.+1).
rewrite big_nat_recr //= [X in X - _]addrC addrK.
by rewrite subnn syme0 mulr1.
Qed.

Lemma omegasf_homog d :
  {homo omegasf: p / sympol p \in [in R[n], d.-homog]}.
Proof.
move=> p H; rewrite /omegasf /= homog_piE.
have Hhom nv i : symh_pol nv R i \is i.-homog by apply symh_homog.
have {Hhom} -> := pihomog_mPo Hhom.
rewrite /sympolyf; case: (SF p) => [f [eqf _]].
by move: H; rewrite -{}eqf -mwmwgt_homogE homog_piE => /eqP ->.
Qed.

Lemma omegasf_homogE d :
  {mono omegasf: p / sympol p \in [in R[n], d.-homog]}.
Proof.
move=> p; apply/idP/idP; last exact: omegasf_homog.
by rewrite -{2}(omegasfK p); apply: omegasf_homog.
Qed.

Notation S := ([tuple sympol 'h_i.+1 | i < n] : n.-tuple {mpoly R[n]}).
Notation E := ([tuple sympol 'e_i.+1 | i < n] : n.-tuple {mpoly R[n]}).

Lemma msym_fundamental_symh_un (t1 t2 : {mpoly R[n]}) :
  t1 \mPo S = t2 \mPo S -> t1 = t2.
Proof.
move=> Heq.
have {Heq} : omegasf (sympolyf_eval t1) = omegasf (sympolyf_eval t2).
  by apply val_inj; rewrite /= !sympolyf_evalK.
move=> /(congr1 omegasf); rewrite !omegasfK /=.
move=> /(congr1 val); rewrite /= -!sympolyf_evalE.
exact: msym_fundamental_un.
Qed.

Lemma omegasf_sympolyf_eval q :
  sympol (omegasf (sympolyf_eval q)) = q \mPo [tuple sympol 'h_i.+1 | i < n].
Proof. by rewrite val_omegasf sympolyf_evalK. Qed.

Lemma omegasf_compsymh p q :
  (sympol p == q \mPo [tuple sympol 'h_i.+1 | i < n]) =
  (sympol (omegasf p) == q \mPo [tuple sympol 'e_i.+1 | i < n]).
Proof.
rewrite -(omegasf_sympolyf_eval q); apply/eqP/eqP => [/val_inj ->| Heq].
- by rewrite omegasfK sympolyf_evalE.
- have {Heq} /(congr1 omegasf) : omegasf p = sympolyf_eval q.
    by apply: sympol_inj; rewrite Heq sympolyf_evalE.
  by rewrite omegasfK => ->.
Qed.

Lemma sym_fundamental_symh_homog (p : {mpoly R[n]}) (d : nat) :
  p \is symmetric -> p \is d.-homog ->
  { t | t \mPo S = p /\ t \is d.-homog for [measure of mnmwgt] }.
Proof.
move=> psym Hhom.
set f := omegasf (SymPoly psym).
have sympol_homog : sympol f \is d.-homog by rewrite omegasf_homogE.
have [g [geq ghom]] :=
  sym_fundamental_homog (sympolP f) sympol_homog.
exists g; split; last by [].
apply esym; apply/eqP.
by rewrite (omegasf_compsymh (SymPoly psym) g) geq.
Qed.

Lemma sym_fundamental_symh (p : {mpoly R[n]}) :
  p \is symmetric -> { t | t \mPo S = p }.
Proof.
move=> psym.
set f := omegasf (SymPoly psym).
have [g [geq gwght]] := sym_fundamental (sympolP f).
exists g; apply esym; apply/eqP.
by rewrite (omegasf_compsymh (SymPoly psym) g) geq.
Qed.

Variable (d : nat).
Implicit Type (la : 'P_d).

Lemma omegasf_prodsyme la : head 0%N la <= n -> omegasf 'e[la] = 'h[la].
Proof.
move=> Hhead.
rewrite /prod_syme /prod_symh /prod_gen rmorph_prod /=.
apply eq_big_seq => /= i /intpartn_leq_head/leq_trans/(_ Hhead).
exact: omegasf_syme.
Qed.

Lemma omegasf_prodsymh la : head 0%N la <= n -> omegasf 'h[la] = 'e[la].
Proof. by move/omegasf_prodsyme => <-; rewrite omegasfK. Qed.

Lemma exp1sumnDsize la :
  (-1) ^+ (d - size la) = \prod_(i <- la) (-1) ^+ i.+1 :> R.
Proof.
case: la => [la /= /andP [/eqP <-]].
elim: la => [/=|l0 la IHla] Hpart; first by rewrite subnn expr0 big_nil.
have /= l0ne0 := part_head_non0 Hpart.
have /= Hla := size_part Hpart.
move: Hpart => /= /andP [_ Hpart].
rewrite big_cons -(IHla Hpart) {IHla}.
rewrite -expri2 subnS prednK ?subn_gt0 // -subSn; last exact: ltnW.
by rewrite -addSn -exprD addnBA // size_part.
Qed.

Lemma omegasf_prodsymp la :
  head 0%N la <= n -> omegasf 'p[la] = (-1) ^+ (d - size la) *: 'p[la].
Proof.
move=> Hhead.
rewrite /prod_symp /prod_gen rmorph_prod /= exp1sumnDsize.
rewrite -scaler_prod !big_seq.
apply: eq_bigr => i Hin; rewrite omegasf_symp //.
rewrite lt0n (in_part_non0 _ Hin) //=.
exact: (leq_trans (intpartn_leq_head Hin) Hhead).
Qed.

Lemma omegasf_syms la : d <= n -> omegasf 's[la] = 's[conj_intpartn la].
Proof.
move=> ledn.
rewrite syms_symh raddf_sum /= syms_syme.
apply eq_bigr => /= s _.
rewrite linearZ /= omegasf_prodsymh //.
apply: (leq_trans _ ledn).
rewrite -{2}(sumn_intpartn s).
by case: s => [[|s0 s]//= _]; rewrite leq_addr.
Qed.

End Omega.

Local Close Scope Combi_scope.


(** * Change of the number of variables *)
Section ChangeNVar.

Variable R : comRingType.
Variable m0 n0 : nat.
Local Notation m := m0.+1.
Local Notation n := n0.+1.
Local Notation SF p := (sym_fundamental (sympolP p)).
Local Notation E := ([tuple sympol 'e_(i.+1) | i < m] : m.-tuple {mpoly R[n]}).

Lemma cnvarsym_subproof (p : {sympoly R[m]}) : sympolyf p \mPo E \is symmetric.
Proof. by apply mcomp_sym => i; rewrite -tnth_nth tnth_mktuple mesym_sym. Qed.
Definition cnvarsym p : {sympoly R[n]} := SymPoly (cnvarsym_subproof p).

Fact cnvarsym_is_lrmorphism : lrmorphism cnvarsym.
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

Lemma cnvar_leq_symeE i : i <= m -> cnvarsym 'e_i = 'e_i.
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

Lemma cnvar_syme i : (i <= m) || (n <= m) -> cnvarsym 'e_i = 'e_i.
Proof.
move=> /orP [] H; first exact: cnvar_leq_symeE.
case: (leqP i m) => [] H1; first exact: cnvar_leq_symeE.
by rewrite !syme_geqnE ?raddf0 // (leq_ltn_trans H H1).
Qed.

Lemma cnvar_symh i : (i <= m) || (n <= m) -> cnvarsym 'h_i = 'h_i.
Proof.
move=> Hi; rewrite !symh_to_syme.
rewrite linear_sum /=; apply eq_bigr => la _.
rewrite linearZ rmorph_prod /=; congr(_ *: _).
apply eq_big_seq => j /intpartn_leq le_ji; apply cnvar_syme.
move: Hi => /orP [Hi | ->]; last by rewrite orbT.
by apply/orP; left; apply: (leq_trans le_ji Hi).
Qed.

Lemma cnvar_symp i : (i < m) || (n <= m) -> cnvarsym 'p_i.+1 = 'p_i.+1.
Proof.
have [b/ltnW] := ubnP i; elim: b i => [| i IHi] d.
  rewrite leqn0 => /eqP -> H.
  by rewrite !sympe1E cnvar_syme.
rewrite leq_eqVlt => /orP [/eqP ->{d} | ] Hi; last exact: IHi.
have:= Newton_symh m0 R i.+2 => /(congr1 cnvarsym).
rewrite linearZ /= cnvar_symh // Newton_symh.
rewrite big_ltn // symh0 mul1r subn0 => /esym.
rewrite linear_sum big_ltn //= rmorphM /= symh0 rmorph1 mul1r subn0.
suff -> : \sum_(1 <= j < i.+2) cnvarsym ('h_j * 'p_(i.+2 - j)) =
          \sum_(1 <= j < i.+2) 'h_j * 'p_(i.+2 - j).
  by apply: addIr.
rewrite !big_nat; apply eq_bigr => d /andP [H0d Hd].
rewrite rmorphM /= cnvar_symh; first last.
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
  forall d : nat, (d < m) || (n <= m) -> cnvarsym (Gen _ d.+1) = (Gen _ d.+1).

Lemma cnvar_prodgen d (la : 'P_d) :
  (d <= m) || (n <= m) ->
  cnvarsym (prod_gen (Gen _) la) = prod_gen (Gen _) la.
Proof.
move=> Hd; rewrite /prod_gen rmorph_prod.
apply eq_big_seq => i Hin.
have := intpartn_leq Hin.
move: Hin => /(in_part_non0 (intpartnP la)).
case: i => //= i _ Hi; apply Hcnvargen.
move: Hd => /orP [Hd | ->]; last by rewrite orbT.
by apply/orP; left; apply: (leq_trans Hi Hd).
Qed.

End ProdGen.

Variable d : nat.

Hypothesis Hd : (d <= m) || (n <= m).

Lemma cnvar_prodsyme (la : 'P_d) : cnvarsym 'e[la] = 'e[la].
Proof.
rewrite /prod_syme; apply (@cnvar_prodgen (syme^~ R)); last by [].
by move=> i Hi; apply: cnvar_syme.
Qed.

Lemma cnvar_prodsymh (la : 'P_d) : cnvarsym 'h[la] = 'h[la].
Proof.
rewrite /prod_symh; apply (@cnvar_prodgen (symh^~ R)); last by [].
by move=> i Hi; apply: cnvar_symh.
Qed.

Lemma cnvar_prodsymp (la : 'P_d) : cnvarsym 'p[la] = 'p[la].
Proof.
rewrite /prod_symp; apply (@cnvar_prodgen (symp^~ R)); last by [].
by move=> i Hi; apply: cnvar_symp.
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


Section CategoricalSystems.

Variable R : comRingType.

Lemma cnvarsym_id n : @cnvarsym R n n =1 id.
Proof. by move=> f; apply val_inj; rewrite /= sympolyfP. Qed.

Lemma cnvarsym_leq_trans m n p :
  (m <= n) -> (n <= p) ->
  @cnvarsym R n p \o @cnvarsym R m n =1 @cnvarsym R m p.
Proof.
move=> le_m_n le_n_p f; rewrite -(sympolyfK f) /=.
move: (sympolyf f) => {}f; rewrite (mpolyE f) !raddf_sum /=.
apply eq_bigr => x _; rewrite !mulr_algl !linearZ /=; congr (_ *: _).
rewrite (multinomUE_id x) !rmorph_prod /=.
apply eq_bigr => i _; rewrite !rmorphX /= !cnvar_leq_symeE //.
by rewrite ltnS (leq_trans _ le_m_n) // -ltnS.
Qed.

Lemma cnvarsym_geq_trans m n p :
  (m >= n) -> (n >= p) ->
  @cnvarsym R n p \o @cnvarsym R m n =1 @cnvarsym R m p.
Proof.
move=> le_n_m le_p_n f; rewrite -(sympolyfK f) /=.
move: (sympolyf f) => {}f; rewrite (mpolyE f) !raddf_sum /=.
apply eq_bigr => x _; rewrite !mulr_algl !linearZ /=; congr (_ *: _).
rewrite (multinomUE_id x) !rmorph_prod /=.
apply eq_bigr => [[i le_i_m]] _; rewrite !rmorphX /=; congr (_ ^+ _).
rewrite !(@cnvar_leq_symeE R m) //.
case: (ltnP i n.+1) => [le_i_n1|lt_n_i]; first exact: cnvar_leq_symeE.
rewrite !syme_geqnE ?raddf0 // ltnS.
exact: (leq_ltn_trans le_p_n lt_n_i).
Qed.

End CategoricalSystems.

