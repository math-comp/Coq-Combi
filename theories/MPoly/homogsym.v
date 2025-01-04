(** * Combi.MPoly.homogsym : Homogenous Symmetric Polynomials *)
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
(** * The Space of Homogeneous Symmetric Polynomials

In this file we study the vector space of homogeneous symmetric polynomials.
The main goal is to construct its classical basis and Cauchy's scalar product.

- [f \is d.-homsym] == f is a homogenerous of degree d symmetric polynomial.
- [f \is [in R[n], d.-homsym]] == idem specifying the ring and number of
                     variables.
- [{homsym R[n, d]}] == the space of homogenerous of degree [d] symmetric
                     polynomials in [n] variables over [R].
- [p *h q]        == the product of two homogeneous symmetric polynomial as a
                     homogeneous symmetric polynomials.

The classical bases:

- ['he[la]]       == the elementary hom. sym. poly. associated to [la]
- ['hh[la]]       == the complete   hom. sym. poly. associated to [la]
- ['hp[la]]       == the power sum  hom. sym. poly. associated to [la]
- ['hm[la]]       == the monomial   hom. sym. poly. associated to [la]
- ['hs[la]]       == the Schur      hom. sym. poly. associated to [la]

- [in_homsym d p] == if [p] is a polynomial [{mpoly R[n]}] which is both
                     symmetric and homogeneous of degree [d], return it as a
                     [{homsym R[n, d]}]. It is canonically linear.

- ['he]           == the elementary hom. sym. basis
- ['hh]           == the complete   hom. sym. basis
- ['hp]           == the power sum  hom. sym. basis
- ['hm]           == the monomial   hom. sym. basis
- ['hs]           == the Schur      hom. sym. basis

The omega involution

- [omegahomsym f] == the image of f under the omega involution.

Changing the base ring and the number of variables:

- [intpart_of_mon m] == if [m] is the monomial [x_1^{i_1}x_2^{i_2}...x_n^{i_n}]
                     returns the integer partition [n^{i_n}...2^{i_2}1^{i_1}]
- [intpartn_of_mon H] == the same as an [intpart_of_mon d] where [H] is a proof of
                     [mnmwgt m = d]

- [map_homsym mor f] == change the base ring of the hom. sym. poly [f] using
                     the ring morphism [mor]. This is canonically additive.
- [cnvarhomsym n f] == change the number of variables of the hom. sym. poly
                     [f] by sending elementary to elementary. This is
                     canonically linear.

The scalar product:

- ['[ u | v ]]    == the scalar product of hom. sym. poly., only defined over
                     the field [algC].
- ['[ u | v ] _(n, d)] == the scalar product of hom. sym. poly. specifying
                     the number of variable and degree.

The main results are [symbm_basis], [symbe_basis], [symbs_basis],
[symbh_basis], [symbp_basis] which asserts that they are all bases (if the
characteristic of the base ring is zero for [symbp_basis]), and the definition
of the scalar product.
 ******)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg matrix vector ssrnum algC archimedean.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import fingroup perm.
From mathcomp Require Import ssrcomplements freeg mpoly.

Require Import tools sorted ordtype permuted partition permcent.
Require Import antisym Schur_mpoly Schur_altdef sympoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import ssrnum algC GRing.Theory Num.Theory.

#[local] Open Scope nat_scope.
#[local] Open Scope ring_scope.

Reserved Notation "{ 'homsym' T [ n , d ] }"
  (at level 0, T, n, d at level 2, format "{ 'homsym'  T [ n ,  d ] }").
#[warning="-closed-notation-not-level-0"]
Reserved Notation "'[ p | q ]"
  (at level 2, format "'[hv' ''[' p  | '/ '  q ] ']'").
#[warning="-closed-notation-not-level-0"]
Reserved Notation "'[ p | q ] _( R , n )"
  (at level 2, format "'[hv' ''[' p  | '/ '  q ] ']' '_(' R ,  n )").


Definition ishomogsym1 {n} {R : ringType} (d : nat) :
  qualifier 0 {sympoly R[n]} := [qualify p | sympol p \is d.-homog].

Module SymPolyHomogKey.
Fact homogsym1_key {n} {R : ringType} d : pred_key (@ishomogsym1 n R d).
Proof. by []. Qed.
Definition homogsym1_keyed {n R} d := KeyedQualifier (@homogsym1_key n R d).
End SymPolyHomogKey.
Canonical SymPolyHomogKey.homogsym1_keyed.

Notation "d .-homsym" := (@ishomogsym1 _ _ d)
  (at level 1, format "d .-homsym") : form_scope.
Notation "[ 'in' R [ n ] , d .-homsym ]" := (@ishomogsym1 n R d)
  (at level 0, R, n at level 2, d at level 0,
     format "[ 'in'  R [ n ] ,  d .-homsym ]") : form_scope.

(** ** Homogeneous symmetric polynomials *)
Section DefType.

Variable n : nat.
Variable R : ringType.
Variable d : nat.

Implicit Types p q : {sympoly R[n]}.

Definition is_homsym p := sympol p \is d.-homog.

Lemma homsymE p : (p \is d.-homsym) = (is_homsym p).
Proof. by []. Qed.

Hypothesis Hvar : (d <= n.+1)%N.

Record homogsym : predArgType :=
  HomogSym {homsym :> {sympoly R[n]}; _ : is_homsym homsym}.

HB.instance Definition _ := [isSub of homogsym for homsym].
HB.instance Definition _ := [Choice of homogsym by <:].

Lemma homsym_inj : injective homsym. Proof. exact: val_inj. Qed.

End DefType.

(* We need to break off the section here to let the argument scope *)
(* directives take effect.                                         *)
Bind Scope ring_scope with homogsym.
(* Arguments homogsym n%_N R%_R. *)
(* Arguments homsym_inj n%_N R%_R d%_N. *)


Notation "{ 'homsym' T [ n , d ] }" := (homogsym n T d).

Section HomogSymLModType.

Variable n : nat.
Variable R : ringType.
Variable d : nat.

#[local] Notation is_homsym := (@is_homsym n R d).

Fact is_homsym_submod_closed : submod_closed is_homsym.
Proof.
split => [|a p q Hp Hq]; rewrite !homsymE.
- exact: dhomog0.
- by apply rpredD => //; apply rpredZ.
Qed.
HB.instance Definition _ :=
  GRing.isSubmodClosed.Build R {sympoly R[n]}
    is_homsym is_homsym_submod_closed.
HB.instance Definition _ :=
  [SubChoice_isSubLmodule of {homsym R[n, d]} by <:].

Lemma homsym_is_linear :
  linear (@homsym n R d : {homsym R[n, d]} -> {sympoly R[n]}).
Proof. by []. Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build
    R {homsym R[n, d]} {sympoly R[n]} _ _ homsym_is_linear.

Fact homsym_is_dhomog (x : {homsym R[n, d]}) : sympol x \is d.-homog.
Proof. by case: x. Qed.
Definition dhomog_of_homogsym (p : {homsym R[n, d]}) :=
  DHomog (homsym_is_dhomog p).

Fact dhomog_of_sym_is_linear : linear dhomog_of_homogsym.
Proof. by move=> r p q; apply val_inj. Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build
    R {homsym R[n, d]} (dhomog n R d) _ _ dhomog_of_sym_is_linear.

End HomogSymLModType.


(** ** Homogeneous symmetric polynomials as a vector space *)
Section Vector.

Variable n0 : nat.
#[local] Notation n := (n0.+1).
Variable R : comRingType.

Variable d : nat.
#[local] Notation SF := {sympoly R[n]}.
Implicit Type (la : 'P_d).

Definition homsymm la : {homsym R[n, d]} := HomogSym (symm_homog n R la).
Definition homsyme la : {homsym R[n, d]} := HomogSym (prod_syme_homog n R la).
Definition homsymh la : {homsym R[n, d]} := HomogSym (prod_symh_homog n R la).
Definition homsymp la : {homsym R[n, d]} := HomogSym (prod_symp_homog n R la).
Definition homsyms la : {homsym R[n, d]} := HomogSym (syms_homog n0 R la).

Lemma homsymmE (f : {homsym R[n, d]}) :
  f = \sum_(l : 'P_d) f@_(mpart l) *: homsymm l.
Proof.
by apply val_inj; rewrite /= {1}(homog_symmE (homsym_is_dhomog f)) !linear_sum.
Qed.

Fact homogsym_vecaxiom :
  Vector.axiom #|[set p : 'P_d | (size p <= n)%N]| {homsym R[n, d]}.
Proof.
pose b := [set p : 'P_d | (size p <= n)%N].
pose t := enum_tuple (pred_of_set b).
have sztntht k : (size (tnth t k) <= n)%N.
  by have := mem_tnth k t; rewrite /t mem_enum inE.
exists (fun p : {homsym R[n, d]} => \row_(i < #|b|) p@_(mpart (tnth t i))).
  by move=> c p q; apply/matrixP=> i j; rewrite !mxE /= mcoeffD mcoeffZ.
exists (fun r : 'rV[R]_(#|b|) =>
          \sum_(i < #|b|) (r ord0 i) *: (homsymm (tnth t i))).
- move=> p; rewrite [RHS]homsymmE.
  rewrite (bigID (mem b)) /= [X in _ + X]big1 ?addr0 => [|la]; first last.
    rewrite inE => /negbTE H .
    by apply val_inj; apply val_inj; rewrite /= /symm H scaler0.
  rewrite [RHS](eq_bigl (fun la => la \in b)); first last.
    by move=> i /=; rewrite inE.
  rewrite -[RHS]big_enum /= -[enum _]/(tval t).
  rewrite big_tuple; apply eq_bigr => i _; congr (_ *: _).
  by rewrite mxE.
- move=> r /=; apply/matrixP=> i j.
  rewrite mxE !raddf_sum ord1 /= (bigD1 j) //=.
  rewrite !linearZ /= mcoeff_symm ?sztntht //.
  rewrite perm_refl mulr1 big1 ?addr0 //.
  move=> k Hkj.
  rewrite !linearZ /= mcoeff_symm ?sztntht //.
  suff : ~~(perm_eq (mpart (n := n) (tnth t k)) (mpart (n := n) (tnth t j))).
    by move /negbTE ->; rewrite mulr0.
  move: Hkj; apply contra => /perm_partm/(congr1 val)/eqP.
  rewrite /= !mpartK // !(tnth_nth (rowpartn d)) /t /= => H.
  apply/eqP/val_inj/eqP => /=.
  by rewrite -(nth_uniq (rowpartn d) _ _ (enum_uniq (pred_of_set b))) // -cardE.
Qed.
HB.instance Definition _ := Lmodule_hasFinDim.Build R {homsym R[n, d]}
  homogsym_vecaxiom.

End Vector.

Notation "''he[' k ]" := (homsyme _ _ k)
                              (at level 8, k at level 2, format "''he[' k ]").
Notation "''hh[' k ]" := (homsymh _ _ k)
                              (at level 8, k at level 2, format "''hh[' k ]").
Notation "''hp[' k ]" := (homsymp _ _ k)
                              (at level 8, k at level 2, format "''hp[' k ]").
Notation "''hm[' k ]" := (homsymm _ _ k)
                              (at level 8, k at level 2, format "''hm[' k ]").
Notation "''hs[' k ]" := (homsyms _ _ k)
                              (at level 8, k at level 2, format "''hs[' k ]").


(** ** Products of homogeneous symmetric polynomials *)
Section HomogSymProd.

Variable n : nat.
Variable R : comRingType.
Variable c d : nat.

Fact homsymprod_subproof (p : {homsym R[n, c]}) (q : {homsym R[n, d]}) :
  homsym p * homsym q \is (c + d).-homsym.
Proof. by apply: dhomogM => /=; apply: homsym_is_dhomog. Qed.
Canonical homsymprod p q : {homsym R[n, c + d]} :=
  HomogSym (homsymprod_subproof p q).
Fact homsymprod_is_bilinear : bilinear_for *:%R *:%R homsymprod.
Proof.
split => /= p r /= u v; apply val_inj => /=.
- by rewrite mulrDl -scalerAl.
- by rewrite mulrDr -scalerAr.
Qed.
HB.instance Definition _ :=
  bilinear_isBilinear.Build
    R {homsym R[n, c]} {homsym R[n, d]} {homsym R[n, c + d]}
    *:%R *:%R homsymprod homsymprod_is_bilinear.

#[local] Notation "p *h q" := (homsymprod p q)
                             (at level 20, format "p  *h  q").

Lemma homsymprod0r p : p *h 0 = 0. Proof. exact: linear0r. Qed.
Lemma homsymprodBr p q1 q2 : p *h (q1 - q2) = p *h q1 - p *h q2.
Proof. exact: linearBr. Qed.
Lemma homsymprodNr p q : p *h (- q) = - p *h q.
Proof. exact: linearNr. Qed.
Lemma homsymprodDr p q1 q2 : p *h (q1 + q2) = p *h q1 + p *h q2.
Proof. exact: linearDr. Qed.
Lemma homsymprodMnr p q m : p *h (q *+ m) = (p *h q) *+ m.
Proof. exact: linearMnr. Qed.
Lemma homsymprod_sumr p I r (P : pred I) (q : I -> {homsym R[n, d]}) :
  p *h (\sum_(i <- r | P i) q i) = \sum_(i <- r | P i) p *h q i.
Proof. exact: linear_sumr. Qed.
Lemma homsymprodZr a p q : p *h (a *: q) = a *: (p *h q).
Proof. by rewrite linearZr. Qed.

Lemma homsymprod0l p : 0 *h p = 0.
Proof. by rewrite linear0l. Qed.
Lemma homsymprodNl p q : (- q) *h p = - q *h p.
Proof. by rewrite linearNl. Qed.
Lemma homsymprodDl p q1 q2 : (q1 + q2) *h p = q1 *h p + q2 *h p.
Proof. by rewrite linearDl. Qed.
Lemma homsymprodBl p q1 q2 : (q1 - q2) *h p = q1 *h p - q2 *h p.
Proof. by rewrite linearBl. Qed.
Lemma homsymprodMnl p q m : (q *+ m) *h p = q *h p *+ m.
Proof. by rewrite linearMnl. Qed.
Lemma homsymprod_suml p I r (P : pred I) (q : I -> {homsym R[n, c]}) :
  (\sum_(i <- r | P i) q i) *h p = \sum_(i <- r | P i) q i *h p.
Proof. by rewrite linear_sumlz. Qed.
Lemma homsymprodZl p a q : (a *: q) *h p = a *: q *h p.
Proof. by rewrite linearZl. Qed.

End HomogSymProd.

Notation "p *h q" := (homsymprod p q)
                       (at level 20, format "p  *h  q").

Section HomSymProdGen.

Variable n0 : nat.
#[local] Notation n := (n0.+1).
Variable R : comRingType.
#[local] Notation HSF := {homsym R[n, _]}.

Import LeqGeqOrder.

Variables (d l0 : nat) (la : seq nat).
Hypotheses (Hla : is_part_of_n d la)
           (Hlla : is_part_of_n (l0 + d)%N (l0 :: la)).
Notation Plla := (IntPartN Hlla).
Notation Pla := (IntPartN Hla).

Lemma homsymprod_hh : 'hh[Plla] = 'hh[rowpartn l0] *h 'hh[Pla] :> HSF.
Proof. by apply val_inj; rewrite /= prod_genM intpartn_cons. Qed.
Lemma homsymprod_he : 'he[Plla] = 'he[rowpartn l0] *h 'he[Pla] :> HSF.
Proof. by apply val_inj; rewrite /= prod_genM intpartn_cons. Qed.
Lemma homsymprod_hp : 'hp[Plla] = 'hp[rowpartn l0] *h 'hp[Pla] :> HSF.
Proof. by apply val_inj; rewrite /= prod_genM intpartn_cons. Qed.

End HomSymProdGen.


Section InHomSym.

Variable n0 d : nat.
#[local] Notation n := (n0.+1).
Variable R : comRingType.
#[local] Notation Pol := {mpoly R[n]}.
#[local] Notation HSF := {homsym R[n, d]}.

#[local] Notation "''pi_' d" :=
  (pihomog mdeg d) (at level 5, format "''pi_' d").

(** TODO: Contribute to Pierre-Yves's multinomials *)
Lemma msym_pihomog nv s (p : {mpoly R[nv]}) :
  msym s ('pi_d p) = 'pi_d (msym s p).
Proof.
rewrite (mpolyE p) ![_ (\sum_(m <- msupp p) _)]linear_sum /=.
rewrite [msym s _]linear_sum linear_sum /=.
apply eq_bigr => m _; rewrite !linearZ /=; congr (_ *: _).
rewrite msymX !pihomogX /=.
have -> : mdeg [multinom m ((s^-1)%g i) | i < nv] = mdeg m.
  rewrite /mdeg; apply perm_big.
  by apply/tuple_permP; exists (s^-1)%g.
by case: (mdeg m == d); rewrite ?msym0 ?msymX.
Qed.

Lemma pihomog_sym nv (p : {mpoly R[nv]}) :
  p \is symmetric -> 'pi_d p \is symmetric.
Proof. by move=> /issymP Hp; apply/issymP => s; rewrite msym_pihomog Hp. Qed.

Definition in_homsym (p : Pol) : HSF :=
  \sum_(la : 'P_d) p@_(mpart la) *: 'hm[la].

Fact in_homsym_is_linear : linear in_homsym.
Proof.
rewrite /in_homsym => a u v.
rewrite linear_sum /= -big_split /=; apply eq_bigr => la _.
by rewrite scalerA -scalerDl mcoeffD mcoeffZ.
Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build
    R {mpoly R[n]} {homsym R[n, d]} _ _ in_homsym_is_linear.

Lemma in_homsymE (p : HSF) : in_homsym p = p.
Proof. by rewrite {2}(homsymmE p). Qed.

End InHomSym.


(** ** The omega involution *)
Section OmegaHomSym.

Variable n0 d : nat.
#[local] Notation n := (n0.+1).
Variable R : comRingType.
#[local] Notation HSF := {homsym R[n, d]}.
Implicit Types (p q : HSF) (la : intpartn d).

Fact omegahomsym_subproof p : is_homsym d (omegasf p).
Proof using.
by apply: omegasf_homog; rewrite -/(is_homsym _ _) -homsymE; case: p.
Qed.
Definition omegahomsym p : HSF := HomogSym (omegahomsym_subproof p).
Fact omegahomsym_is_linear : linear omegahomsym.
Proof using.
by move=> a f g; apply val_inj; rewrite /= !linearD !linearZ /=.
Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build
    R {homsym R[n, d]} {homsym R[n, d]} _ _ omegahomsym_is_linear.


Lemma omega_homsymh la :
  (head 0%N la <= n)%N -> omegahomsym 'hh[la] = 'he[la].
Proof using. by move=> Hd; apply val_inj; rewrite /= omegasf_prodsymh. Qed.
Lemma omega_homsyme la :
  (head 0%N la <= n)%N -> omegahomsym 'he[la] = 'hh[la].
Proof using. by move=> Hd; apply val_inj; rewrite /= omegasf_prodsyme. Qed.
Lemma omega_homsyms la :
  (d <= n)%N -> omegahomsym 'hs[la] = 'hs[conj_intpartn la].
Proof using. by move=> Hd; apply val_inj; rewrite /= omegasf_syms. Qed.
Lemma omega_homsymp la :
  (head 0%N la <= n)%N -> omegahomsym 'hp[la] = (-1) ^+ (d - size la) *: 'hp[la].
Proof using. by move=> Hd; apply val_inj; rewrite /= omegasf_prodsymp. Qed.

End OmegaHomSym.

Section OmegaProd.

Variable n0 : nat.
#[local] Notation n := (n0.+1).
Variable R : comRingType.

Lemma omegahomsym_rmorph c d (p : {homsym R[n, c]}) (q : {homsym R[n, d]}) :
  omegahomsym (p *h q) = (omegahomsym p) *h (omegahomsym q).
Proof. by apply val_inj; rewrite /= rmorphM. Qed.

End OmegaProd.


(** * The classical bases of homogeneous symmetric polynomials *)
Section HomSymField.

Variable n0 d : nat.
#[local] Notation n := (n0.+1).
Variable R : fieldType.
#[local] Notation HSF := {homsym R[n, d]}.


#[local] Notation Basis := (#|{:'P_d}|.-tuple HSF).
Definition symbe : Basis := [tuple of [seq 'he[la] | la : 'P_d]].
Definition symbh : Basis := [tuple of [seq 'hh[la] | la : 'P_d]].
Definition symbm : Basis := [tuple of [seq 'hm[la] | la : 'P_d]].
Definition symbs : Basis := [tuple of [seq 'hs[la] | la : 'P_d]].
Definition symbp : Basis := [tuple of [seq 'hp[la] | la : 'P_d]].

Hypothesis Hd : (d <= n)%N.

Lemma basis_homsym : [set p : 'P_d | (size p <= n)%N] =i {:'P_d}.
Proof using Hd.
move=> la.
rewrite !inE; apply: (leq_trans _ Hd).
by rewrite -[X in (_ <= X)%N](sumn_intpartn la); apply: size_part.
Qed.

Lemma dim_homsym :
  \dim (fullv (vT := HSF)) = #|{:'P_d}|.
Proof using Hd. by rewrite dimvf /=; apply eq_card; apply basis_homsym. Qed.

Lemma symbm_free : free symbm.
Proof using Hd.
apply/freeP => co.
rewrite (reindex _ (onW_bij _ (@enum_rank_bij 'P_d))) /=.
rewrite (eq_bigr (fun la : 'P_d => (co (enum_rank la)) *: 'hm[la])); first last.
  move=> la _; rewrite (nth_map (rowpartn _)) /= -?cardE ?ltn_ord //.
  by rewrite -?enum_val_nth enum_rankK.
move => /(congr1 val).
rewrite /= linear_sum /= => /symm_unique0 H i.
rewrite -(enum_valK i); apply H.
apply: (leq_trans _ Hd).
rewrite -[X in (_ <= X)%N](sumn_intpartn (enum_val i)).
exact: size_part.
Qed.

Lemma symbm_basis : basis_of fullv symbm.
Proof using Hd.
by rewrite basisEfree symbm_free subvf size_map size_tuple /= dim_homsym.
Qed.

Lemma symbs_basis : basis_of fullv symbs.
Proof using Hd.
rewrite basisEdim size_map size_tuple dim_homsym leqnn andbT.
rewrite -(span_basis symbm_basis).
apply/span_subvP => s /mapP[/= la]; rewrite !mem_enum => _ ->{s}.
have -> : 'hm[la] = \sum_(mu : 'P_d) 'K^-1(la, mu) *: 'hs[mu] :> HSF.
  by apply val_inj; rewrite /= (symm_syms _ _ la) !linear_sum.
rewrite span_def; apply memv_suml => mu _; apply memvZ.
rewrite big_map (bigD1_seq mu) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
by apply memv_add; [exact: memv_line | exact: mem0v].
Qed.
Lemma symbs_free : free symbs.
Proof. exact/basis_free/symbs_basis. Qed.

Theorem mcoeff_symbs (la : 'P_d) f :
  coord symbs (enum_rank la) f =
  (alternpol 'X_[rho n] * sympol (homsym f))@_(mpart la + rho n).
Proof.
have /coord_span -> : f \in span symbs.
  by rewrite (span_basis symbs_basis) memvf.
rewrite !coord_sum_free ?(basis_free symbs_basis) //.
rewrite (reindex _ (onW_bij _ (@enum_rank_bij 'P_d))) /=.
rewrite !linear_sum /= mulr_sumr linear_sum /= (bigD1 la) //=.
rewrite (nth_map (rowpartn d)) -?cardE ?ltn_ord // nth_enum_rank.
rewrite -scalerAr linearZ /=.
have Hszp (nu : 'P_d) : (size nu <= n)%N.
  by apply: (leq_trans _ Hd); rewrite -{2}(sumn_intpartn nu) size_part.
rewrite mcoeff_alt_SchurE // eq_refl mulr1 big1 ?addr0 // => mu /negbTE Hmula.
rewrite (nth_map (rowpartn d)) -?cardE ?ltn_ord // nth_enum_rank.
rewrite -scalerAr linearZ /=.
by rewrite mcoeff_alt_SchurE // Hmula mulr0.
Qed.

#[local] Notation E := [tuple mesym n R i.+1 | i < n].

Definition intpart_of_mon m : seq nat :=
  rev (flatten [tuple nseq (m i) i.+1 | i < n]).

Lemma intpart_of_monP m : mnmwgt m = d -> is_part_of_n d (intpart_of_mon m).
Proof using.
rewrite /mnmwgt => H.
rewrite /= is_part_sortedE; apply/and3P; split.
- rewrite /intpart_of_mon sumn_rev sumn_flatten -[X in _ == X]H.
  rewrite sumnE big_map big_tuple.
  apply/eqP/eq_bigr => /= i _.
  by rewrite sumnE tnth_mktuple big_nseq iter_addn_0 mulnC.
- rewrite /intpart_of_mon /= rev_sorted.
  apply/(sorted2P 0%N) => //=; first exact: leq_trans.
  move=> i j; rewrite !nth_flatten.
  rewrite size_flatten.
  have -> : shape [seq nseq (m i0) i0.+1 | i0 : 'I_n] = m.
    rewrite /shape -map_comp (tuple_map_ord m) /=.
    apply eq_map => k /=.
    by rewrite size_nseq.
  move=> /andP[Hij Hjm]; have Him := leq_ltn_trans Hij Hjm.
  have:= reshape_indexP Hjm; have:= reshape_offsetP Hjm.
  have:= reshape_indexP Him; have:= reshape_offsetP Him.
  rewrite size_tuple => Hc1 Hr1 Hc2 Hr2.
  do 2 (rewrite (nth_map ord0); last by rewrite size_enum_ord).
  rewrite !(mnm_nth 0) !nth_nseq !nth_enum_ord //= {Hr1 Hr2}.
  rewrite {}Hc1 {}Hc2 ltnS; move: Hij.
  by rewrite (reshape_leq m) => /orP[/ltnW | /andP[/eqP->]].
- rewrite /intpart_of_mon; rewrite mem_rev; apply/flatten_mapP => /= [[s _]].
  by move=> /nseqP[].
Qed.
Canonical intpartn_of_mon m (H : mnmwgt m = d) := IntPartN (intpart_of_monP H).

#[local] Lemma Esym : (forall i : 'I_n, E`_i \is symmetric).
Proof using.
move=> i; rewrite (nth_map i) ?size_tuple //.
by rewrite -tnth_nth tnth_ord_tuple mesym_sym.
Qed.

Lemma comp_symbe m (H : mnmwgt m = d) :
  'X_[m] \mPo E = 'he[intpartn_of_mon H].
Proof using.
rewrite comp_mpolyX /= /prod_gen /intpartn_of_mon /intpart_of_mon /=.
rewrite rmorph_prod /= [RHS](perm_big _ (permEl (perm_rev _))) /=.
rewrite big_flatten /= big_map /= -big_enum /=; apply eq_bigr => i _.
rewrite big_nseq tnth_mktuple.
by rewrite -big_const_ord prodr_const cardT -cardE card_ord.
Qed.

Lemma in_homsym_comp_symbe m (H : mnmwgt m = d) :
  in_homsym d ('X_[m] \mPo E) = 'he[intpartn_of_mon H].
Proof using. by rewrite comp_symbe in_homsymE. Qed.

Lemma symbe_basis : basis_of fullv symbe.
Proof using Hd.
rewrite basisEdim size_map size_tuple dim_homsym leqnn andbT.
apply/subvP => /= p _; rewrite span_def big_map.
have:= sym_fundamental_homog (sympolP p) (homsym_is_dhomog p).
move=> [t [Hp /dhomogP Hhomt]].
have {Hp} -> : p = \sum_(m <- msupp t) t@_m *: in_homsym d ('X_[m] \mPo E).
  apply val_inj; apply val_inj; rewrite /= -{1}Hp {1}(mpolyE t) {Hp}.
  rewrite !linear_sum /=; apply eq_big_seq => m /Hhomt /= Hm.
  rewrite !linearZ /=; congr (_ *: _).
  by rewrite in_homsym_comp_symbe /= comp_symbe /=.
rewrite big_seq; apply memv_suml => m Hm; apply memvZ.
rewrite (in_homsym_comp_symbe (Hhomt m Hm)).
move: (intpartn_of_mon _) => {m Hm} la.
rewrite (bigD1_seq la) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
apply memv_add; first exact: memv_line.
exact: mem0v.
Qed.
Lemma symbe_free : free symbe.
Proof. exact/basis_free/symbe_basis. Qed.

Lemma symbh_basis : basis_of fullv symbh.
Proof using Hd.
rewrite basisEdim size_map size_tuple dim_homsym leqnn andbT.
rewrite -(span_basis symbe_basis).
apply/span_subvP => s /mapP[/= la]; rewrite !mem_enum => _ ->{s}.
have -> : 'he[la] = \sum_(mu : 'P_d) coeff_prodgen (fun d (la : 'P_d) =>
            (-1)^+(d - size la) * (perm_partn la)%:R) la mu *: 'hh[mu] :> HSF.
  by apply val_inj; rewrite /= linear_sum /= (prod_prodgen (syme_to_symh n0 R)).
rewrite span_def; apply memv_suml => mu _; apply memvZ.
rewrite big_map (bigD1_seq mu) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
by apply memv_add; [exact: memv_line | exact: mem0v].
Qed.
Lemma symbh_free : free symbh.
Proof. exact/basis_free/symbh_basis. Qed.

Lemma symbp_basis : [char R] =i pred0 -> basis_of fullv symbp.
Proof using Hd.
move=> Hchar.
rewrite basisEdim size_map size_tuple dim_homsym leqnn andbT.
rewrite -(span_basis symbh_basis).
apply/span_subvP => s /mapP[/= la]; rewrite !mem_enum => _ ->{s}.
pose co := fun (n : nat) (l : 'P_n) => (permcent.zcard l)%:R^-1 : R.
have -> : 'hh[la] = \sum_(mu : 'P_d)
                     coeff_prodgen co la mu *: 'hp[mu] :> HSF.
  apply val_inj; rewrite /= linear_sum /=.
  by rewrite (prod_prodgen (fun n => symh_to_symp n0 n Hchar)).
rewrite span_def; apply memv_suml => mu _; apply memvZ.
rewrite big_map (bigD1_seq mu) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
by apply memv_add; [exact: memv_line | exact: mem0v].
Qed.
Lemma symbp_free : [char R] =i pred0 -> free symbp.
Proof. by move=> Hchar; apply/basis_free/symbp_basis. Qed.

End HomSymField.


Notation "''he'" := (symbe _ _ _) (at level 8, format "''he'").
Notation "''hh'" := (symbh _ _ _) (at level 8, format "''hh'").
Notation "''hp'" := (symbp _ _ _) (at level 8, format "''hp'").
Notation "''hm'" := (symbm _ _ _) (at level 8, format "''hm'").
Notation "''hs'" := (symbs _ _ _) (at level 8, format "''hs'").


(** ** Changing the base field *)
Section ChangeField.

Variable R S : fieldType.
Variable mor : {rmorphism R -> S}.

Variable n0 d : nat.
#[local] Notation n := (n0.+1).
#[local] Notation HSFR := {homsym R[n, d]}.
#[local] Notation HSFS := {homsym S[n, d]}.

Fact map_sympoly_d_homog (p : HSFR) : map_sympoly mor p \is d.-homsym.
Proof.
rewrite homsymE /=; apply/dhomogP => /= m.
rewrite mcoeff_msupp mcoeff_map_mpoly => Hm.
have {Hm} : p@_m != 0.
  move: Hm; apply contra => /eqP ->.
  by apply/eqP; apply: (rmorph0 mor).
rewrite -mcoeff_msupp => Hm.
by have /dhomogP/(_ _ Hm) := homsym_is_dhomog p.
Qed.
Definition map_homsym (p : HSFR) : HSFS := HomogSym (map_sympoly_d_homog p).

Fact map_homsym_is_additive : additive map_homsym.
Proof. by move=> /= p q; apply val_inj; rewrite /= rmorphB. Qed.
HB.instance Definition _ :=
  GRing.isAdditive.Build
    {homsym R[n, d]} {homsym S[n, d]} _ map_homsym_is_additive.

Lemma map_homsym_is_scalable : scalable_for (mor \; *:%R) map_homsym.
Proof. by move=> a /= p; apply val_inj; rewrite /= linearZ. Qed.
HB.instance Definition _ :=
  GRing.isScalable.Build _ {homsym R[n, d]} {homsym S[n, d]}
    _ _ map_homsym_is_scalable.


Lemma coord_map_homsym (b : #|{:'P_d}|.-tuple HSFR) j (f : HSFR) :
  basis_of fullv b ->
  basis_of fullv (map_tuple map_homsym b) ->
  coord (map_tuple map_homsym b) j (map_homsym f) = mor (coord b j f).
Proof.
move=> Hbasis Hmap_basis.
have toSf : f \in span b by rewrite (span_basis Hbasis) // memvf.
rewrite {1}(coord_span toSf) raddf_sum /=.
rewrite (eq_bigr
           (fun i : 'I_#|{:'P_d}| =>
              (mor (coord b i f)) *: (map_tuple map_homsym b)`_i )).
  by rewrite coord_sum_free //; apply: (basis_free Hmap_basis).
move=> i _; rewrite linearZ /=.
congr (_ *: _); apply esym; apply nth_map.
by rewrite size_tuple ltn_ord.
Qed.

Lemma map_homsymm la : map_homsym 'hm[la] = 'hm[la].
Proof. by apply val_inj; rewrite /= map_symm. Qed.
Lemma map_homsyme la : map_homsym 'he[la] = 'he[la].
Proof. by apply val_inj; rewrite /= map_syme_prod. Qed.
Lemma map_homsymh la : map_homsym 'hh[la] = 'hh[la].
Proof. by apply val_inj; rewrite /= map_symh_prod. Qed.
Lemma map_homsymp la : map_homsym 'hp[la] = 'hp[la].
Proof. by apply val_inj; rewrite /= map_symp_prod. Qed.
Lemma map_homsyms la : map_homsym 'hs[la] = 'hs[la].
Proof. by apply val_inj; rewrite /= map_syms. Qed.

Lemma map_homsymbm : map_tuple map_homsym 'hm = 'hm.
Proof. by apply eq_from_tnth => i; rewrite !tnth_map map_homsymm. Qed.
Lemma map_homsymbe : map_tuple map_homsym 'he = 'he.
Proof. by apply eq_from_tnth => i; rewrite !tnth_map map_homsyme. Qed.
Lemma map_homsymbh : map_tuple map_homsym 'hh = 'hh.
Proof. by apply eq_from_tnth => i; rewrite !tnth_map map_homsymh. Qed.
Lemma map_homsymbp : map_tuple map_homsym 'hp = 'hp.
Proof. by apply eq_from_tnth => i; rewrite !tnth_map map_homsymp. Qed.
Lemma map_homsymbs : map_tuple map_homsym 'hs = 'hs.
Proof. by apply eq_from_tnth => i; rewrite !tnth_map map_homsyms. Qed.

End ChangeField.


(** ** Extracting coords *)
Section Coord.

Variable n0 d : nat.
#[local] Notation n := (n0.+1).
Variable R : fieldType.
#[local] Notation HSF := {homsym R[n, d]}.
Implicit Type (la : 'P_d).

Lemma symbmE la : ('hm)`_(enum_rank la) = 'hm[la] :> HSF.
Proof. by rewrite /symbm tupleE /= (nth_map la) ?nth_enum_rank // -cardE. Qed.
Lemma symbeE la : ('he)`_(enum_rank la) = 'he[la] :> HSF.
Proof. by rewrite /symbe tupleE /= (nth_map la) ?nth_enum_rank // -cardE. Qed.
Lemma symbhE la : ('hh)`_(enum_rank la) = 'hh[la] :> HSF.
Proof. by rewrite /symbh tupleE /= (nth_map la) ?nth_enum_rank // -cardE. Qed.
Lemma symbpE la : ('hp)`_(enum_rank la) = 'hp[la] :> HSF.
Proof. by rewrite /symbp tupleE /= (nth_map la) ?nth_enum_rank // -cardE. Qed.
Lemma symbsE la : ('hs)`_(enum_rank la) = 'hs[la] :> HSF.
Proof. by rewrite /symbs tupleE /= (nth_map la) ?nth_enum_rank // -cardE. Qed.

#[local] Lemma er_eqE (la mu : 'P_d) :
  (enum_rank la == enum_rank mu) = (la == mu).
Proof. by rewrite inj_eq //; apply: enum_rank_inj. Qed.

#[local] Notation coord := (coord (vT := HSF)).

Hypothesis (Hd : (d <= n)%N).
Lemma coord_symbm la mu : coord 'hm (enum_rank mu) 'hm[la] = (la == mu)%:R.
Proof. by rewrite -symbmE coord_free ?er_eqE; last exact: symbm_free. Qed.
Lemma coord_symbe la mu : coord 'he (enum_rank mu) 'he[la] = (la == mu)%:R.
Proof. by rewrite -symbeE coord_free ?er_eqE; last exact: symbe_free. Qed.
Lemma coord_symbh la mu : coord 'hh (enum_rank mu) 'hh[la] = (la == mu)%:R.
Proof. by rewrite -symbhE coord_free ?er_eqE; last exact: symbh_free. Qed.
Lemma coord_symbs la mu : coord 'hs (enum_rank mu) 'hs[la] = (la == mu)%:R.
Proof. by rewrite -symbsE coord_free ?er_eqE; last exact: symbs_free. Qed.

Lemma coord_symbp (char0 : [char R] =i pred0) la mu :
  coord 'hp (enum_rank mu) 'hp[la] = (la == mu)%:R.
Proof. by rewrite -symbpE coord_free ?er_eqE; last exact/symbp_free. Qed.

End Coord.


(** ** Changing the number of variables *)
Section ChangeNVar.

Variable R : comRingType.
Variable m0 n0 : nat.
#[local] Notation m := m0.+1.
#[local] Notation n := n0.+1.
Variable d : nat.
Hypothesis Hd : (d <= m)%N || (n0 < m)%N.

Fact cnvarhomsym_subproof (p : {homsym R[m, d]}) :
  (cnvarsym n0 p) \is d.-homsym.
Proof using.
case: p => [p] /=; rewrite unfold_in /= => Hp; rewrite unfold_in.
rewrite /cnvarsym /=; apply/mwmwgt_homogP.
have [f [Hf Hfhom]] := sym_fundamental_homog (sympolP p) Hp.
rewrite /sympolyf; case: (sym_fundamental _) => [g []] /=.
by rewrite -Hf => H _; rewrite (msym_fundamental_un H).
Qed.
Definition cnvarhomsym (p : {homsym R[m, d]}) : {homsym R[n, d]} :=
  HomogSym (cnvarhomsym_subproof p).
Fact cnvarhomsym_is_linear : linear cnvarhomsym.
Proof. by move=> a f g; apply val_inj; rewrite /= !linearD !linearZ /=. Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build
    R {homsym R[m, d]} {homsym R[n, d]} _ _ cnvarhomsym_is_linear.

Lemma cnvarhomsyme la : cnvarhomsym 'he[la] = 'he[la].
Proof using Hd. by apply val_inj; rewrite /= -/'e[_] cnvar_prodsyme. Qed.
Lemma cnvarhomsymh la : cnvarhomsym 'hh[la] = 'hh[la].
Proof using Hd. by apply val_inj; rewrite /= -/'h[_] cnvar_prodsymh. Qed.
Lemma cnvarhomsymp la : cnvarhomsym 'hp[la] = 'hp[la].
Proof using Hd. by apply val_inj; rewrite /= -/'p[_] cnvar_prodsymp. Qed.
Lemma cnvarhomsymm la : cnvarhomsym 'hm[la] = 'hm[la].
Proof using Hd. by apply val_inj; rewrite /= cnvar_symm. Qed.
Lemma cnvarhomsyms la : cnvarhomsym 'hs[la] = 'hs[la].
Proof using Hd. by apply val_inj; rewrite /= cnvar_syms. Qed.

End ChangeNVar.



#[local] Lemma char0_algC : [char algC] =i pred0.
Proof. exact: char_num. Qed.
#[local] Hint Resolve char0_algC : core.

(** * The scalar product *)
Section ScalarProduct.

Context {n0 d : nat}.
#[local] Notation n := (n0.+1).
#[local] Notation HSF := {homsym algC[n, d]}.

Definition homsymdot (p q : HSF) : algC :=
  \sum_(i < #|{:'P_d}|)
    (zcard (enum_val i))%:R * (coord 'hp i p) * (coord 'hp i q)^*.
Notation "''[' u | v ]" := (homsymdot u v) : ring_scope.
Lemma homsymdotE p q :
  '[ p | q ] =
  \sum_(la : 'P_d) (zcard la)%:R *
    (coord 'hp (enum_rank la) p) * (coord 'hp (enum_rank la) q)^*.
Proof.
rewrite /homsymdot [RHS](reindex _ (onW_bij _ (@enum_val_bij _))) /=.
by apply/eq_bigr => i _; rewrite enum_valK.
Qed.
Lemma homsymdotC p q : '[p | q] = ('[q | p])^*.
Proof.
rewrite /homsymdot rmorph_sum /=.
apply: eq_bigr=> x _.
rewrite [in RHS]rmorphM [X in _ = X * _]rmorphM conjCK -!mulrA.
have /geC0_conj -> : 0 <= ((zcard (enum_val x))%:R : algC).
  by rewrite -nnegrE ?nnegrE ?ler01 ?ler0n ?oner_neq0.
by congr (_ * _); rewrite mulrC.
Qed.
Fact homsymdot_is_bilinear : bilinear_for *%R (Num.conj_op \; *%R) homsymdot.
Proof.
have lin r p u v : '[r *: u + v | p] = r * '[u | p] + '[v | p].
  rewrite !homsymdotE mulr_sumr /= -big_split; apply: eq_bigr => x _ /=.
  rewrite linearD linearZ /= mulrDr mulrDl !mulrA; congr (_ + _).
  by rewrite [_ * r]mulrC -!mulrA.
split => /= p r /= u v; first exact: lin.
by rewrite !(homsymdotC p) lin rmorphD rmorphM.
Qed.
HB.instance Definition _ :=
  bilinear_isBilinear.Build algC HSF HSF algC *%R (Num.conj_op \; *%R)
    homsymdot homsymdot_is_bilinear.
Notation "''[' u | v ]" := (homsymdot u v) : ring_scope.

Lemma homsymdot0l p : '[0 | p] = 0.
Proof. exact: linear0l. Qed.
Lemma homsymdotNl p q : '[- q | p] = - '[q | p].
Proof. exact: linearNl. Qed.
Lemma homsymdotDl p q1 q2 : '[q1 + q2 | p] = '[q1 | p] + '[q2 | p].
Proof. exact: linearDl. Qed.
Lemma homsymdotBl p q1 q2 : '[q1 - q2 | p] = '[q1 | p] - '[q2 | p].
Proof. exact: linearBl. Qed.
Lemma homsymdotMnl p q n : '[q *+ n | p] = '[q | p] *+ n.
Proof. exact: linearMnl. Qed.
Lemma homsymdot_suml p I r (P : pred I) (q : I -> HSF) :
  '[\sum_(i <- r | P i) q i | p] = \sum_(i <- r | P i) '[q i | p].
Proof. exact: linear_sumlz. Qed.
Lemma homsymdotZl p a q : '[a *: q | p] = a * '[q | p].
Proof. exact: linearZl. Qed.


Lemma homsymdot0r p : '[p | 0] = 0.
Proof. exact: linear0r. Qed.
Lemma homsymdotNr p q : '[p | - q] = - '[p | q].
Proof. exact: linearNr. Qed.
Lemma homsymdotDr p q1 q2 : '[p | q1 + q2] = '[p | q1] + '[p | q2].
Proof. exact: linearDr. Qed.
Lemma homsymdotBr p q1 q2 : '[p | q1 - q2] = '[p | q1] - '[p | q2].
Proof. exact: linearBr. Qed.
Lemma homsymdotMnr p q n : '[p | q *+ n] = '[p | q] *+ n.
Proof. exact: linearMnr. Qed.
Lemma homsymdot_sumr p I r (P : pred I) (q : I -> HSF) :
  '[p | \sum_(i <- r | P i) q i] = \sum_(i <- r | P i) '[p | q i].
Proof. exact: linear_sumr. Qed.
Lemma homsymdotZr a p q : '[p | a *: q] = a^* * '[p | q].
Proof. exact: linearZr. Qed.

Lemma homsymdotpp (Hd : (d <= n)%N) la mu :
  '[ 'hp[la] | 'hp[mu] ] = (zcard la)%:R * (la == mu)%:R.
Proof.
rewrite homsymdotE (bigD1 mu) //= big1 ?addr0 => [| nu /negbTE Hneq].
- rewrite !(coord_symbp Hd) // eq_refl /= conjC1 mulr1.
  by case: eqP => [-> //| _]; rewrite !mulr0.
- by rewrite !(coord_symbp Hd) // [mu == nu]eq_sym Hneq conjC0 mulr0.
Qed.

Lemma homsymdot_omegasf f g :
  (d <= n)%N -> '[ omegahomsym f | omegahomsym g ] = '[ f | g ].
Proof.
move=> Hd; have /andP[/eqP Hfull Hfree]:= symbp_basis Hd char0_algC.
have:= (memvf g); rewrite -Hfull => /coord_span ->.
rewrite raddf_sum /= !homsymdot_sumr; apply eq_bigr => i _.
have:= (memvf f); rewrite -Hfull => /coord_span ->.
rewrite raddf_sum /= !homsymdot_suml; apply eq_bigr => j _.
rewrite !linearZ /= !homsymdotZl !homsymdotZr; congr (_ * (_ * _)).
rewrite ![_`_i](nth_map (rowpartn d)) -?cardE //.
rewrite ![_`_j](nth_map (rowpartn d)) -?cardE //.
rewrite !omega_homsymp //;
  try by apply: (leq_trans (leq_head_sumn _)); rewrite sumn_intpartn.
rewrite homsymdotZl homsymdotZr !homsymdotpp //.
case: eqP => /= [->|_]; rewrite ?mulr0 // !mulr1 !mulrA.
move: (nth _ _ _) => la {i j}.
have /Num.Theory.conj_intr -> :
  (-1) ^+ (d - size la) \in (@archimedean.Num.int algC) by apply rpred_sign.
by rewrite -exprD addnn -muln2 exprM sqrr_sign mul1r.
Qed.

End ScalarProduct.

Notation "''[' u | v ]" := (homsymdot u v) : ring_scope.
Notation "''[' u | v ] _( n , d )" :=
  (@homsymdot n d u v) (only parsing) : ring_scope.
