(** * Combi.MPoly.Cauchy : Cauchy formula for symmetric polynomials *)
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
(** * Cauchy formula for symmetric polynomials and the scalar product.

We first define the scalar product:

- ['[ u | v ]]    == the scalar product of hom. sym. poly., only defined over
                     the field [algC].
- ['[ u | v ] _(n, d)] == the scalar product of hom. sym. poly. specifying
                     the number of variable and degree.

Then we fix two non zero natural [m] and [n] and consider the two sets
of variables [X := (x_i)_{i < m}] and [Y := (y_j)_{j < n}]. We also consider
the variables [z_{i,j} := x_i * y_j].

We encode polynomial in [X \cup Y] as polynomials in [X] whose coefficient are
polynomials in [Y]. We denote by [mz] a monomial in the [Z].

- [monX mz]     == the monomial in [X] obtained by setting all the [y_i] to [1].
- [monsY mz]    == the [m.-tuple] of whose [i]-th element is the monomial in [Y]
                   obtained by putting [x_i] to [1] and all the others to [0].
- [Ymon ms]     == given [ms : m.-tuple 'X_{1.. n}] assemble them to get a
                   monomial in the [Z].
- [polXY m n R] == polynomial in [m] variable whose coefficients are polynomials
                   in [n] over the commutative ring [R]. This is canonically a
                   [algType] over [R].
- [polXY_scale c p] == base ring multiplication for elements of [polXY m n R]
- [p(X)]        == the image of [p] by the canonical inclusion algebra morphism
                   [polX -> polXY]
- [p(Y)]        == the image of [p] by the canonical inclusion algebra morphism
                   [polY -> polXY]
- [p(XY)]       == the polynomial in [polXY] from a polynomials in the [Z_{i,j}].
- [Cauchy_kernel d] == the Cauchy reproducing kernel in degree [d], that is
                   the sum of all monomial in [x_i*y_i] of degree [d]
                   which is defined as ['h_d(XY)]
- [co_hp la p] == if [p] is symmetric in [X], returns the coefficient of [p] on
                   ['hp[la]]
- [co_hpXY la mu p] == if [p] is symmetric both in [X] and [Y], returns the
                   coefficient of [p] on ['hp[la](X) 'hp[mu](Y)].

The main result is Theorem [homsymdotss] which asserts that Schur function are
orthonormal for the scalar product.
*******)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import ssrint rat ssralg ssrnum algC matrix vector.
From mathcomp Require Import sesquilinear archimedean.
From mathcomp Require Import mpoly.

Require Import tools partition ordtype.
Require Import antisym Schur_mpoly Schur_altdef sympoly homogsym permcent.

Require ordtype.


Unset SsrOldRewriteGoalsOrder.  (* change to Unset and remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
#[local] Open Scope ring_scope.

#[local] Lemma pchar0_rat : [pchar rat] =i pred0.
Proof. exact: Num.Theory.pchar_num. Qed.
#[local] Lemma pchar0_algC : [pchar algC] =i pred0.
Proof. exact: Num.Theory.pchar_num. Qed.
#[local] Hint Resolve pchar0_algC pchar0_rat : core.

Set Warnings "-postfix-notation-not-level-1".
Reserved Notation "p '(Y)'"  (at level 20, format "p '(Y)'").
Reserved Notation "p '(X)'"  (at level 20, format "p '(X)'").
Reserved Notation "p '(XY)'" (at level 20, format "p '(XY)'").
Set Warnings "postfix-notation-not-level-1".



(** * The scalar product *)
Section ScalarProduct.

Context {n0 d : nat}.
#[local] Abbreviation n := (n0.+1).
#[local] Abbreviation HSF := {homsym algC[n, d]}.

Implicit Type (p q u v : HSF).

Definition homsymdot p q : algC :=
  \sum_(i < #|{: 'P_d}|)
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
rewrite [in RHS]rmorphM [X in _ = X * _]rmorphM /= conjCK -!mulrA.
have /geC0_conj -> : 0 <= ((zcard (enum_val x))%:R : algC).
  by rewrite -nnegrE ?nnegrE ?ler01 ?ler0n ?oner_neq0.
by congr (_ * _); rewrite mulrC.
Qed.
Fact homsymdot_is_bilinear : bilinear_for *%R (Num.conj \; *%R) homsymdot.
Proof.
have lin r p u v : '[r *: u + v | p] = r * '[u | p] + '[v | p].
  rewrite !homsymdotE mulr_sumr /= -big_split; apply: eq_bigr => x _ /=.
  rewrite linearD linearZ /= mulrDr mulrDl !mulrA; congr (_ + _).
  by rewrite [_ * r]mulrC -!mulrA.
split => /= p r /= u v; first exact: lin.
by rewrite !(homsymdotC p) lin rmorphD rmorphM.
Qed.
HB.instance Definition _ :=
  bilinear_isBilinear.Build algC HSF HSF algC *%R (Num.conj \; *%R)
    homsymdot homsymdot_is_bilinear.
Notation "''[' u | v ]" := (homsymdot u v) : ring_scope.

Fact homsymdot_is_hermitian p q : '[p | q] = (-1) ^+ false * '[q | p]^*.
Proof. by rewrite expr0 mul1r -homsymdotC. Qed.
HB.instance Definition _ :=
  isHermitianSesquilinear.Build
    algC HSF false Num.conj homsymdot homsymdot_is_hermitian.

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


Hypothesis (Hd : (d <= n)%N).

Fact homsymdot_is_dot f : f != 0 -> 0 < '[f | f].
Proof.
rewrite lt0r andbC.
pose co (la : 'P_d) :=
  (zcard la)%:R * coord 'hp (enum_rank la) f * (coord 'hp (enum_rank la) f)^*.
have le0zcc (la : 'P_d) : 0 <= co la.
  by rewrite /co -mulrA mulr_ge0 // mul_conjC_ge0.
have -> /= : 0 <= '[f | f].
  by rewrite homsymdotE; apply: sumr_ge0 => /= la _; apply: le0zcc.
have /andP[/eqP Hfull Hfree]:= symbp_basis Hd pchar0_algC.
have:= memvf f; rewrite -Hfull => /coord_span {1}->.
apply contra; rewrite homsymdotE => /eqP H.
have {H le0zcc} eq0zcc (la : 'P_d) : co la = 0.
  by apply/(psumr_eq0P _ H) => //= mu _; apply le0zcc.
suff allc0 i : coord 'hp i f = 0.
  by apply/eqP/big1 => /= i _; rewrite allc0 scale0r.
have {eq0zcc} /eqP := eq0zcc (enum_val i).
rewrite {}/co enum_valK -mulrA mulf_eq0 pnatr_eq0 (negbTE (neq0zcard _)) /=.
by rewrite mul_conjC_eq0 => /eqP.
Qed.
HB.instance Definition _ :=
  isDotProduct.Build algC HSF homsymdot homsymdot_is_dot.


(** Formulas for other bases will be proved in Cauchy *)
Lemma homsymdotpp la mu :
  '['hp[la] | 'hp[mu]] = (zcard la)%:R * (la == mu)%:R.
Proof.
rewrite homsymdotE (bigD1 mu) //= big1 ?addr0 => [nu /negbTE Hneq|].
  by rewrite !(coord_symbp Hd) // [mu == nu]eq_sym Hneq conjC0 mulr0.
rewrite !(coord_symbp Hd) // eq_refl /= conjC1 mulr1.
by case: eqP => [-> //| _]; rewrite !mulr0.
Qed.

Lemma homsymdot_omegasf f g :
  '[omegahomsym f | omegahomsym g ] = '[f | g].
Proof.
have /andP[/eqP Hfull Hfree]:= symbp_basis Hd pchar0_algC.
have:= memvf g; rewrite -Hfull => /coord_span ->.
rewrite raddf_sum /= !homsymdot_sumr; apply eq_bigr => i _.
have:= memvf f; rewrite -Hfull => /coord_span ->.
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

Lemma homsymp_orthogonal : pairwise_orthogonal homsymdot 'hp.
Proof.
apply/pairwise_orthogonalP => /=; split.
  have pfree := basis_free (symbp_basis Hd pchar0_algC).
  rewrite free_uniq // andbT.
  by move: pfree; rewrite free_directv /= => /andP[].
move=> f g /mapP[/= la _ {f}->]/mapP[/= mu _ {g}->].
rewrite homsymdotpp.
by case: (altP (la =P mu)) => [->|_]; rewrite /= ?mulr0 // eqxx.
Qed.

End ScalarProduct.

Notation "''[' u | v ]" := (homsymdot u v) : ring_scope.
Notation "''[' u | v ] _( n , d )" :=
  (@homsymdot n d u v) (only parsing) : ring_scope.





(** ** Polynomials in two sets of variables *)
Section CauchyKernel.

Variables (m0 n0 : nat).
Abbreviation m := m0.+1.
Abbreviation n := n0.+1.
Abbreviation mxvec_index := (@mxvec_index m n).

Let vecmx_index : 'I_(m * n) -> 'I_m * 'I_n :=
  (enum_val \o cast_ord (esym (mxvec_cast m n))).

Lemma vecmx_indexK i : mxvec_index (vecmx_index i).1 (vecmx_index i).2 = i.
Proof.
rewrite /vecmx_index/mxvec_index/uncurry/=.
case H : (enum_val (cast_ord (esym (mxvec_cast m n)) i)) => /= [a b].
by rewrite -H enum_valK cast_ordKV.
Qed.
Lemma mxvec_indexK i j : vecmx_index (mxvec_index i j) = (i, j).
Proof.
rewrite /vecmx_index/mxvec_index/uncurry/=.
by rewrite cast_ordK enum_rankK.
Qed.

Section Big.

Variables (R : Type) (idx : R).
Variable op : Monoid.com_law idx.

Lemma big_mxvec_index P F :
  \big[op/idx]_(i : 'I_(m * n) | P i) F i =
   \big[op/idx]_(i < m)
    \big[op/idx]_(j < n | P (mxvec_index i j)) F (mxvec_index i j).
Proof.
rewrite pair_big_dep (reindex (uncurry mxvec_index)).
  exact: (subon_bij _ (curry_mxvec_bij m n)).
by apply eq_big => [] [i j].
Qed.

End Big.

Definition monX (mon : 'X_{1..(m*n)}) : 'X_{1.. m} :=
  [multinom (\sum_(j < n) mon (mxvec_index i j))%N | i < m].

Lemma mdeg_monX mon : mdeg (monX mon) = mdeg mon.
Proof.
rewrite /mdeg /monX !big_tuple big_mxvec_index /=; apply eq_bigr => i _.
rewrite tnth_mktuple; apply eq_bigr => j _.
by rewrite mnm_tnth.
Qed.

Definition monsY (mz : 'X_{1..(m*n)}) :=
  [tuple [multinom mz (mxvec_index i j) | j < n] | i < m].

Definition Ymon (ms : m.-tuple 'X_{1.. n}) :=
  [multinom (tnth ms (vecmx_index i).1) (vecmx_index i).2 | i < m*n].

Lemma monsYK : cancel monsY Ymon.
Proof.
move=> mz; apply mnmP => i.
by rewrite mnmE tnth_mktuple mnmE /= vecmx_indexK.
Qed.
Lemma YmonK : cancel Ymon monsY.
move=> ms; apply eq_from_tnth => i.
by rewrite tnth_mktuple; apply mnmP => j; rewrite !mnmE mxvec_indexK.
Qed.
Lemma monsY_bij : bijective monsY.
Proof. by exists Ymon; [exact: monsYK | exact: YmonK]. Qed.
Lemma Ymon_bij : bijective Ymon.
Proof. by exists monsY; [exact: YmonK | exact: monsYK]. Qed.

Lemma mdeg_tnth_monsY mz i :
  mdeg (tnth (monsY mz) i) = tnth (monX mz) i.
Proof.
rewrite /monsY /monX !tnth_mktuple /mdeg big_tuple.
by apply eq_bigr => j _; rewrite -mnm_tnth mnmE.
Qed.


Variable (R : comNzRingType).

#[local] Abbreviation polZ := {mpoly R[m * n]}.
#[local] Abbreviation polX := {mpoly R[m]}.
#[local] Abbreviation polY := {mpoly R[n]}.
Definition polXY := {mpoly polY[m]}.
Definition polXY_scale (c : R) (p : polXY) : polXY := c%:MP *: p.
#[local] Notation "c *:M p" := (polXY_scale c p)
  (at level 40, left associativity).

HB.instance Definition _ := GRing.NzRing.on polXY.

Fact scale_polXYA a b p : a *:M (b *:M p) = (a * b) *:M p.
Proof. by rewrite /polXY_scale scalerA rmorphM. Qed.
Fact scale_polXY1m p : 1 *:M p = p.
Proof. by rewrite /polXY_scale rmorph1 scale1r. Qed.
Fact scale_polXYDr c p1 p2 :
  c *:M (p1 + p2) = c *:M p1 + c *:M p2.
Proof. exact: scalerDr. Qed.
Fact scale_polXYDl p c1 c2 :
  (c1 + c2) *:M p = c1 *:M p + c2 *:M p.
Proof. by rewrite /polXY_scale rmorphD /= scalerDl. Qed.
HB.instance Definition _ :=
  GRing.Zmodule_isLmodule.Build R polXY
    scale_polXYA scale_polXY1m scale_polXYDr scale_polXYDl.

Lemma scale_polXYE (c : R) (p : polXY) : c *: p = c *:M p.
Proof. by []. Qed.

Fact polXY_scaleAl (c : R) (p q : polXY) : c *: (p * q : polXY) = (c *: p) * q.
Proof. by rewrite !scale_polXYE /polXY_scale /= -!mul_mpolyC mulrA. Qed.
HB.instance Definition _ :=
  GRing.Lmodule_isLalgebra.Build R polXY polXY_scaleAl.

Fact polXY_scaleAr (c : R) (p q : polXY) : c *: (p * q : polXY) = p * (c *: q).
Proof.
rewrite !scale_polXYE /polXY_scale /= -!mul_mpolyC.
by rewrite mulrA [_ * p]mulrC mulrA.
Qed.
HB.instance Definition _ :=
  GRing.Lalgebra_isAlgebra.Build R polXY polXY_scaleAr.


Definition polX_XY : polX -> polXY := map_mpoly (mpolyC n (R := R)).

Fact polX_XY_is_zmod_morphism : zmod_morphism polX_XY.
Proof. by rewrite /polX_XY; exact: rmorphB. Qed.
HB.instance Definition _ :=
  GRing.isZmodMorphism.Build polX polXY polX_XY polX_XY_is_zmod_morphism.

Fact polX_XY_is_monoid_morphism : monoid_morphism polX_XY.
Proof. by rewrite /polX_XY; split; [exact: rmorph1 | exact: rmorphM]. Qed.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build polX polXY polX_XY polX_XY_is_monoid_morphism.

Fact polX_XY_is_linear : linear polX_XY.
Proof.
rewrite /polX_XY => r /= p q.
rewrite /map_mpoly mmapD mmapZ /=.
by rewrite scale_polXYE /polXY_scale /= -!mul_mpolyC.
Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build R polX polXY _ polX_XY polX_XY_is_linear.

Definition polY_XY : polY -> polXY := mpolyC m (R := {mpoly R[n]}).

Fact polY_XY_is_zmod_morphism : zmod_morphism polY_XY.
Proof. by rewrite /polY_XY; exact: rmorphB. Qed.
HB.instance Definition _ :=
  GRing.isZmodMorphism.Build polY polXY polY_XY polY_XY_is_zmod_morphism.

Fact polY_XY_is_monoid_morphism : monoid_morphism polY_XY.
Proof. by rewrite /polY_XY; split; [exact: rmorph1 | exact: rmorphM]. Qed.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build polY polXY polY_XY polY_XY_is_monoid_morphism.

Fact polY_XY_is_linear : linear polY_XY.
Proof.
rewrite /polY_XY => r /= p q.
rewrite scale_polXYE /polXY_scale /= -!mul_mpolyC.
by rewrite raddfD /= rmorphM.
Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build R polY polXY _ polY_XY polY_XY_is_linear.


Notation "p '(Y)'" := (polY_XY p).
Notation "p '(X)'" := (polX_XY p).

Lemma polyXY_scale p q : p(X) * q(Y) = q *: p(X).
Proof. by rewrite mulrC mul_mpolyC. Qed.

Lemma symmX d (la : 'P_d) : 'hm[la](X) = 'hm[la].
Proof.
by have /(congr1 val) := map_symm (mpolyC n (R:=R)) m0 la.
Qed.


Definition evalXY : polZ -> polXY :=
  mmap ((@mpolyC m _) \o (@mpolyC n R))
       (fun i => 'X_((vecmx_index i).1) (X) * 'X_((vecmx_index i).2) (Y)).
Notation "p '(XY)'" := (evalXY p).


Fact evalXY_is_zmod_morphism : zmod_morphism evalXY.
Proof. by rewrite /evalXY; exact: rmorphB. Qed.
HB.instance Definition _ :=
  GRing.isZmodMorphism.Build {mpoly R[(m * n)]} polXY _ evalXY_is_zmod_morphism.

Fact evalXY_is_monoid_morphism : monoid_morphism evalXY.
Proof. by rewrite /evalXY; split=> [|p q]; rewrite /= ?rmorphM ?rmorph1. Qed.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build {mpoly R[(m * n)]} polXY
    _ evalXY_is_monoid_morphism.

Fact evalXY_is_linear : linear evalXY.
Proof.
rewrite /evalXY => r p q.
by rewrite mmapD mmapZ /= scale_polXYE /polXY_scale /= -!mul_mpolyC.
Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build R {mpoly R[(m * n)]} polXY _ _ evalXY_is_linear.

Lemma evalXY_XE mz :
  'X_[mz](XY) = 'X_[monX mz](X) * \prod_(i < m) 'X_[tnth (monsY mz) i](Y).
Proof.
rewrite -rmorph_prod polyXY_scale /monX.
transitivity (\prod_(i : 'I_(m*n))
                 (('X_(vecmx_index i).2 : polY) ^+ mz i *:
                              ('X_(vecmx_index i).1(X) ^+ mz i))).
  rewrite (multinomUE_id mz) /evalXY mmapX /mmap1.
  by apply eq_bigr => [i _]; rewrite -exprZn polyXY_scale.
rewrite big_mxvec_index /=.
rewrite mpolyXE_id rmorph_prod -scaler_prod; apply eq_bigr => i _.
rewrite scaler_prod /=; congr (_ *: _).
- rewrite /monsY tnth_mktuple mpolyXE_id; apply eq_bigr => j _.
  by rewrite mxvec_indexK /= mnmE.
- rewrite mnmE -prodrXr rmorph_prod /=; apply eq_bigr => j _.
  by rewrite mxvec_indexK /= rmorphXn.
Qed.

Lemma evalXY_homog d p : p \is d.-homog -> p(XY) \is d.-homog.
Proof.
move/pihomog_dE <-; rewrite pihomogE.
rewrite rmorph_sum /=; apply: rpred_sum => mon /eqP Hdeg.
rewrite linearZ /= scale_polXYE; apply: rpredZ.
rewrite evalXY_XE -rmorph_prod /= polyXY_scale /=; apply: rpredZ.
by rewrite /polX_XY map_mpolyX dhomogX /= mdeg_monX Hdeg.
Qed.

Lemma sympXY k : 'p_k(XY) = 'p_k(X) * 'p_k(Y).
Proof.
rewrite /= /symp_pol /= /evalXY /= !rmorph_sum /= big_mxvec_index /=.
rewrite [RHS]mulr_suml; apply eq_bigr => i _ /=.
rewrite [RHS]mulr_sumr; apply eq_bigr => j _ /=.
by rewrite !rmorphXn /= mmapX mmap1U mxvec_indexK /= exprMn.
Qed.

Lemma prod_sympXY d (la : 'P_d) : 'hp[la](XY) = 'hp[la](X) * 'hp[la](Y).
Proof.
rewrite /prod_symp /prod_gen /= !rmorph_prod /=.
rewrite -big_split /=; apply eq_bigr => i _.
by rewrite [LHS]sympXY.
Qed.


(** ** The Cauchy reproducing kernel *)
Definition Cauchy_kernel d := 'h_d(XY).

Lemma Cauchy_kernel_dhomog d : Cauchy_kernel d \is d.-homog.
Proof. by rewrite /Cauchy_kernel; apply evalXY_homog; apply: symh_homog. Qed.

Section BijectionFam.

Variable d : nat.

Fact famY_subproof (mz : 'X_{1.. (m * n) < d.+1}) i :
    (mdeg (tnth (monsY (val mz)) i) < d.+1)%N.
Proof.
apply: (leq_ltn_trans _ (bmdeg mz)).
rewrite /mdeg /monsY tnth_mktuple !big_tuple big_mxvec_index /=.
under eq_bigr do rewrite tnth_mktuple mnm_tnth.
by rewrite (bigD1 i) //= leq_addr.
Qed.
Definition famY mz : {ffun 'I_m -> 'X_{1.. n < d.+1}} :=
  [ffun i : 'I_m => BMultinom (famY_subproof mz i)].

Let famYinv_fun (ff : {ffun 'I_m -> 'X_{1.. n < d.+1}}) :=
  let mz := [multinom (ff (vecmx_index i).1 (vecmx_index i).2) | i < m * n]
  in if (mdeg mz < d.+1)%N then mz else 0%MM.
Fact famYinv_subproof ff : (mdeg (famYinv_fun ff) < d.+1)%N.
Proof.
rewrite /famYinv_fun /=.
case: (ssrnat.ltnP (mdeg [multinom _ | i < _]) d.+1) => //= _.
by rewrite mdeg0.
Qed.
Definition famYinv ff := BMultinom (famYinv_subproof ff).

Lemma famY_bij (mon : 'X_{1.. m}) :
  mdeg mon = d ->
  {on [pred i in
       family (fun i0 (j : 'X_{1.. n < d.+1}) => mdeg j == tnth mon i0)],
    bijective famY}.
Proof.
move=> Hdeg; exists famYinv.
- move=> mz; rewrite inE => /familyP Hff.
  apply val_inj => /=; rewrite /famYinv_fun.
  rewrite (([multinom _ | i < m * n] =P val mz) _) /= ?bmdeg //.
  apply/eqP/mnmP => c; rewrite mnmE /famY ffunE /=.
  by rewrite tnth_mktuple mnmE //= -[in RHS](vecmx_indexK c).
- move=> ff; rewrite inE => /familyP H /=.
  apply/ffunP => /= i; rewrite ffunE; apply val_inj => /=.
  rewrite /famYinv_fun [mdeg _](_ : _ = d) ?ltnSn.
    rewrite -[RHS]Hdeg !mdegE big_mxvec_index => /=; apply eq_bigr => i' _.
    have {H} := H i'; rewrite unfold_in mnm_tnth => /eqP <-.
    rewrite mdegE; apply eq_bigr => j _.
    by rewrite mnmE mxvec_indexK /=.
   by rewrite tnth_mktuple; apply mnmP => j; rewrite !mnmE mxvec_indexK /=.
Qed.

End BijectionFam.

Variable d : nat.

(** *** Cauchy formula for complete and monomial symmetric polynomials *)
Lemma Cauchy_symm_symh :
  Cauchy_kernel d = \sum_(la : 'P_d) ('h[la] : polY) *: ('m[la] : polXY).
Proof.
apply/mpolyP => mon.
case/altP: (mdeg mon =P d) => Hdeg; first last.
rewrite (dhomog_nemf_coeff (Cauchy_kernel_dhomog d) Hdeg).
  rewrite linear_sum /= big1 ?mcoeff0 // => la _.
  rewrite mcoeffZ.
  case: (ssrnat.leqP (size la) m) => [Hi | /symm_oversize ->].
  - rewrite mcoeff_symm //.
    suff /negbTE -> : ~~ perm_eq (mpart (n := m) la) mon by rewrite mulr0.
    apply/negP => /perm_sumn.
    rewrite sumn_mpart // sumn_intpartn sumnE -/(mdeg _) => Hd.
    by rewrite -Hd eq_refl in Hdeg.
  - by rewrite mcoeff0 mulr0.
have Hpm : is_part_of_n d (partm mon).
  by rewrite /= intpartP andbT sumn_partm Hdeg.
pose pm := IntPartN Hpm.
suff -> : (Cauchy_kernel d)@_mon = 'h[pm].
  rewrite (bigID (fun mu : 'P_d => (size mu <= m)%N)) /=.
  rewrite linearD ![in RHS]linear_sum /=.
  rewrite addrC big1 ?add0r => [la |].
    by rewrite -ltnNge => /symm_oversize ->; rewrite !raddf0.
  rewrite (bigD1 pm) ?size_partm //= ?big1 ?addr0 => [la /andP[Hszla Hla] |].
    rewrite mcoeffZ mcoeff_symm //.
    suff /negbTE -> : ~~ perm_eq (mpart (n := m) la) mon by rewrite mulr0.
    apply/negP => /perm_partm/(congr1 val)/=.
    rewrite mpartK // => Heq.
    by move: Hla; rewrite /eq_op /= Heq eq_refl.
  by rewrite mcoeffZ mcoeff_symm ?size_partm // perm_sym partm_permK mulr1.
rewrite /Cauchy_kernel /prod_symh /prod_gen {1}/symh /= rmorph_prod /=.
rewrite rmorph_sum raddf_sum /= partmE; apply esym.
transitivity (\prod_(i <- mon) sympol 'h_i : polY ).
  rewrite [RHS](bigID (fun i => i == 0%N)) /=.
  rewrite [in RHS]big1 ?mul1r => [i /eqP ->|].
    exact: (congr1 val (symh0 n R)).
  rewrite /= -[RHS]big_filter; apply: perm_big.
  by rewrite perm_sort.
rewrite {Hpm pm} /= big_tuple; symmetry.
rewrite (bigID (fun mZ : 'X_{1.. _ < _} => monX mZ == mon)) /=.
rewrite addrC big1 ?add0r => [i /andP[_ /negbTE Hneq] |].
  rewrite evalXY_XE -rmorph_prod /= polyXY_scale.
  by rewrite linearZ /= /polX_XY map_mpolyX mcoeffX Hneq mulr0.
under eq_bigl=> i do [rewrite andb_idl;
  first by move=> /eqP; rewrite -{3}Hdeg => <-; rewrite mdeg_monX].
under [LHS]eq_bigr => mz Hmz.
  rewrite evalXY_XE -rmorph_prod /= polyXY_scale.
  by rewrite linearZ /= /polX_XY map_mpolyX mcoeffX Hmz mulr1 over.
under [RHS]eq_bigr => i _ do
  [rewrite (@symh_pol_any _ _ d.+1) //;
     first by rewrite ltnS -Hdeg /mdeg big_tuple (bigD1 i) // leq_addr].
rewrite bigA_distr_big_dep => /=.
rewrite (reindex (famY (d := d))) /=; first exact: famY_bij.
apply eq_big => [mz | mz /eqP Hmz].
- apply/eqP/familyP => [/= Hmon i | Hfam].
  + by rewrite unfold_in ffunE /= mdeg_tnth_monsY Hmon.
  + apply/mnmP => i.
    have := Hfam i; rewrite unfold_in /= !mnm_tnth => /eqP <-.
    rewrite ffunE /= !tnth_mktuple mdegE.
    by apply eq_bigr => j _; rewrite mnmE.
- by apply eq_bigr => i _; rewrite ffunE /= !tnth_mktuple.
Qed.

Lemma Cauchy_homsymm_homsymh :
  Cauchy_kernel d = \sum_(la : 'P_d) 'hm[la](X) * 'hh[la](Y).
Proof.
rewrite Cauchy_symm_symh.
by apply eq_bigr => i _; rewrite polyXY_scale symmX.
Qed.

(** *** Cauchy formula for Schur symmetric polynomials *)
Lemma Cauchy_homsyms_homsyms :
  Cauchy_kernel d = \sum_(la : 'P_d) 'hs[la](X) * 'hs[la](Y).
Proof.
rewrite Cauchy_homsymm_homsymh.
transitivity (\sum_(mu : 'P_d) \sum_(la : 'P_d)
               'hm[mu](X) * ('K(la, mu) *: 'hs[la])(Y)).
  apply eq_bigr => la _.
  rewrite [X in X(Y)](_ : _ = sympol 'h[la]) //.
  by rewrite symh_syms -mulr_sumr !linear_sum.
rewrite exchange_big /=; apply eq_bigr => la _.
have /= -> /= := congr1 val (syms_symm m0 R la).
rewrite 2!linear_sum /= mulr_suml; apply eq_bigr => mu _.
by rewrite !linearZ /= -scalerAr -scalerAl.
Qed.


(** Unused lemma *)
Lemma Cauchy_kernel_symmetric : Cauchy_kernel d \is symmetric.
Proof.
rewrite Cauchy_symm_symh; apply: rpred_sum => la _.
by apply: rpredZ; apply sympolP.
Qed.

(** Unused lemma *)
Lemma Cauchy_kernel_coeff_symmetric mon :
  (Cauchy_kernel d)@_mon \is symmetric.
Proof.
rewrite Cauchy_symm_symh linear_sum /=; apply rpred_sum => la _.
rewrite linearZ /= rpredM ?sympolP //.
case: (ssrnat.leqP (size la) m) => [/mcoeff_symm -> | /symm_oversize ->].
- by case: (perm_eq _ _) => /=; [exact: rpred1 | exact: rpred0].
- by rewrite mcoeff0 rpred0.
Qed.

(** Unused lemma *)
Lemma Cauchy_kernel_coeff_homog mon :
  (Cauchy_kernel d)@_mon \is d.-homog.
Proof.
rewrite Cauchy_symm_symh linear_sum /=; apply rpred_sum => la _.
rewrite linearZ /=.
case: (ssrnat.leqP (size la) m) => [/mcoeff_symm -> | /symm_oversize ->].
- case: (perm_eq _ _) => /=; rewrite ?mulr1 ?mulr0 ?rpred0 //.
  exact: prod_symh_homog.
- by rewrite mcoeff0 mulr0 rpred0.
Qed.

End CauchyKernel.

Notation "p '(Y)'" := (@polY_XY _ _ _ p).
Notation "p '(X)'" := (@polX_XY _ _ _ p).
Notation "p '(XY)'" := (@evalXY _ _ _ p).


Section CauchyKernelField.
Variable R : fieldType.

(** *** Cauchy formula for power sum symmetric polynomials *)
Lemma Cauchy_homsymp_zhomsymp m n d :
  [pchar R] =i pred0 ->
  Cauchy_kernel m n R d =
  \sum_(la : 'P_d) 'hp[la](X) * ((zcard la)%:R^-1 *: 'hp[la](Y)).
Proof.
move=> Hpchar.
rewrite /Cauchy_kernel symh_to_symp // !rmorph_sum /=; apply eq_bigr => la _.
by rewrite linearZ /= -scalerAr prod_sympXY; congr (_ *: _).
Qed.

End CauchyKernelField.


(** * Cauchy kernel and scalar product of symmetric functions *)
Section Scalar.

Variable n0 d : nat.
#[local] Abbreviation n := n0.+1.
Hypothesis Hd : (d <= n)%N.

#[local] Abbreviation HSC := {homsym algC[n, d]}.
#[local] Abbreviation polXY := (polXY n0 n0 algC).
#[local] Abbreviation pol := {mpoly algC[n]}.
#[local] Notation "p '(Y)'" := (@polY_XY n0 n0 _ p).
#[local] Notation "p '(X)'" := (@polX_XY n0 n0 _ p).

#[local] Notation "''hsC[' la ]" := ('hs[la] : HSC).
#[local] Notation "''hpC[' la ]" := ('hp[la] : HSC).


Definition co_hp (la : 'P_d) : pol -> algC :=
  homsymdot^~ 'hp[la] \o in_homsym d (R := algC).
Definition co_hpXY (la mu : 'P_d) : polXY -> algC :=
  locked (co_hp la \o map_mpoly (co_hp mu)).

Fact co_hp_is_zmod_morphism la : zmod_morphism (co_hp la).
Proof. by rewrite /co_hp => p q; rewrite /= raddfB homsymdotBl. Qed.
HB.instance Definition _ la :=
  GRing.isZmodMorphism.Build pol algC _ (co_hp_is_zmod_morphism la).

Fact co_hp_is_scalar la : scalar (co_hp la).
Proof.
rewrite /co_hp => /= r p q.
by rewrite /= linearD linearZ homsymdotDl homsymdotZl /=.
Qed.
HB.instance Definition _ p :=
  GRing.isLinear.Build algC pol algC _ _ (co_hp_is_scalar p).

Lemma co_hp_hp la mu : co_hp la 'hp[mu] = (zcard mu)%:R * (mu == la)%:R.
Proof using Hd.
by rewrite /co_hp /= -![prod_gen _ _]/(homsym 'hp[_]) in_homsymE homsymdotpp.
Qed.

Fact co_hpXY_is_zmod_morphism la mu : zmod_morphism (co_hpXY la mu).
Proof. by rewrite /co_hpXY; unlock => p q; rewrite raddfB. Qed.
HB.instance Definition _ la mu :=
  GRing.isZmodMorphism.Build
    (Cauchy.polXY n0 n0 algC) algC _ (co_hpXY_is_zmod_morphism la mu).

Lemma co_hpYE la (p q : pol) :
  map_mpoly (co_hp la) (p(X) * q(Y)) = (co_hp la q) *: p.
Proof.
rewrite polyXY_scale /=; apply/mpolyP => /= m.
rewrite linearZ /= mcoeff_map_mpoly /= linearZ /= mulrC.
rewrite /polX_XY /= mcoeff_map_mpoly /= mul_mpolyC.
by rewrite mulrC -linearZ.
Qed.

Lemma co_hprXYE la mu (p q : pol) :
  co_hpXY la mu (p(X) * q(Y)) = (co_hp la p) * (co_hp mu q).
Proof. by rewrite /co_hpXY; unlock; rewrite /= co_hpYE linearZ mulrC. Qed.

Lemma coord_zsympsps (la mu : 'P_d) :
  (\sum_nu
    (coord 'hp (enum_rank la) 'hsC[nu]) *
    ((zcard mu)%:R * coord 'hp (enum_rank mu) 'hsC[nu]))
  = (la == mu)%:R.
Proof using Hd.
have to_p (nu : 'P_d) : ('hsC[nu] : HSC) \in span 'hp.
  by rewrite (span_basis (symbp_basis Hd _)) //= memvf.
have : \sum_(nu : 'P_d) 'hsC[nu](X) * 'hsC[nu](Y) =
       \sum_(nu : 'P_d) 'hp[nu](X) * ((zcard nu)%:R^-1 *: 'hp[nu](Y)).
  by rewrite -Cauchy_homsyms_homsyms Cauchy_homsymp_zhomsymp.
have sum_coord (p : HSC) :
      \sum_i homsym (coord 'hp i p *: ('hp)`_i : HSC) =
      \sum_px coord 'hp (enum_rank px) p *: 'hp[px] :> pol.
  rewrite (reindex _ (onW_bij _ (@enum_rank_bij _))) /=.
  rewrite !linear_sum /=; apply eq_bigr => i _.
  rewrite (nth_map inh) /= -?enum_val_nth // ?enum_rankK //.
  by rewrite -cardE ltn_ord.
rewrite (eq_bigr (fun nu : 'P_d =>
             (\sum_px (coord 'hp (enum_rank px) 'hsC[nu]) *: 'hp[px])(X) *
             (\sum_py (coord 'hp (enum_rank py) 'hsC[nu]) *: 'hp[py])(Y)
        )) => [nu _ |].
  by rewrite {1 2}(coord_span (to_p nu)) linear_sum /= sum_coord.
move=> {sum_coord to_p} /(congr1 (co_hpXY la mu)).
rewrite !raddf_sum /= => /esym.
rewrite (bigD1 la) //= -[(zcard la)%:R^-1 *: 'hp[la](Y)]linearZ /=.
rewrite -![prod_gen _ _]/(homsym 'hp[_]).
rewrite co_hprXYE linearZ co_hp_hp //.
rewrite eq_refl mulr1 !mulrA divff ?mul1r; first by rewrite pnatr_eq0 neq0zcard.
rewrite big1 ?addr0 => [nu /negbTE Hnu |].
  rewrite -![prod_gen _ _]/(homsym 'hp[_]).
  rewrite -[(zcard nu)%:R^-1 *: 'hp[nu](Y)]linearZ /=.
  rewrite -![prod_gen _ _]/(homsym 'hp[_]).
  rewrite co_hprXYE linearZ co_hp_hp //.
  move: Hnu; rewrite -(inj_eq (@val_inj _ _ _)) /= => ->.
  by rewrite mulr0 !mul0r.
rewrite /= co_hp_hp // => /(congr1 (fun x => (zcard la)%:R^-1 * x)).
rewrite mulrA [X in X * _]mulrC divff; first by rewrite pnatr_eq0 neq0zcard.
rewrite mul1r !mulr_sumr => -> .
apply eq_bigr => nu _.
rewrite co_hprXYE.
suff dot_sumhp (eta tau : 'P_d) :
  co_hp eta (\sum_px coord 'hp (enum_rank px) 'hsC[tau] *: 'hp[px]) =
    coord 'hp (enum_rank eta) 'hsC[tau] * (zcard eta)%:R.
  rewrite !{}dot_sumhp ![_ * (zcard _)%:R]mulrC !mulrA.
  by rewrite ![_ * (zcard la)%:R]mulrC divff ?mul1r // pnatr_eq0 neq0zcard.
rewrite !raddf_sum /= (bigD1 eta) //=.
rewrite -![prod_gen _ _]/(homsym 'hp[_]).
rewrite linearZ /= co_hp_hp // eq_refl mulr1.
rewrite big1 ?addr0 // => p => /negbTE Hp.
rewrite -![prod_gen _ _]/(homsym 'hp[_]).
rewrite linearZ /= co_hp_hp //.
move: Hp; rewrite -(inj_eq (@val_inj _ _ _)) /= => ->.
by rewrite !mulr0.
Qed.

Lemma coord_zsymspsp (la mu : 'P_d) :
  (\sum_nu
    (coord 'hp (enum_rank nu) 'hsC[la]) *
    ((zcard nu)%:R * coord 'hp (enum_rank nu) 'hsC[mu]))
  = (la == mu)%:R.
Proof using Hd.
pose matsp : 'M[algC]_#|{: 'P_d}| :=
  \matrix_(i, j < #|{: 'P_d}|) (coord 'hp i 'hsC[enum_val j]).
pose matzsp : 'M[algC]_#|{: 'P_d}| :=
  \matrix_(i, j < #|{: 'P_d}|)
   ((zcard (enum_val j))%:R * (coord 'hp j 'hsC[enum_val i])).
have: matsp *m matzsp = 1%:M.
  apply/matrixP => i j /=.
  rewrite /matsp /matzsp /= !mxE.
  rewrite (reindex _ (onW_bij _ (@enum_rank_bij _))) /=.
  rewrite -(inj_eq (@enum_val_inj _ _)) /= -coord_zsympsps //.
  apply eq_bigr => /= nu _.
  by rewrite !mxE !enum_valK !enum_rankK.
move=> /mulmx1C/matrixP/(_ (enum_rank mu) (enum_rank la)).
rewrite /matsp /matzsp /= !mxE.
rewrite (inj_eq (@enum_rank_inj _)) eq_sym => <-.
rewrite (reindex _ (onW_bij _ (@enum_rank_bij _))) /=.
apply eq_bigr => /= nu _.
by rewrite !mxE !enum_rankK mulrC.
Qed.

(** ** Schur function are orthonormal *)
Theorem homsymdotss la mu : '[ 'hsC[la] | 'hsC[mu] ] = (la == mu)%:R.
Proof using Hd.
have to_p (nu : 'P_d) : 'hsC[nu] \in span 'hp.
  by rewrite (span_basis (symbp_basis Hd _)) // memvf.
rewrite (coord_span (to_p la)) (coord_span (to_p mu)).
transitivity
  (\sum_i (coord 'hp i 'hsC[la]) *
          (zcard (enum_val i))%:R * (coord 'hp i 'hsC[mu])); first last.
  rewrite (reindex _ (onW_bij _ (@enum_rank_bij _))) /=.
  rewrite -coord_zsymspsp //; apply eq_bigr => /= nu _.
  by rewrite enum_rankK mulrA.
rewrite homsymdot_suml; apply eq_bigr => /= l _.
rewrite homsymdotZl homsymdot_sumr -mulrA; congr (_ * _).
transitivity
  (\sum_(i < #|{: 'P_d}|)
    (coord 'hp i 'hsC[mu])^* * (zcard (enum_val l))%:R * (i == l)%:R).
  apply: eq_bigr => i _; rewrite homsymdotZr -mulrA; congr (_ * _).
  rewrite !(nth_map inh _ (fun l => 'hp[l])) -?cardE ?ltn_ord //.
  by rewrite -!enum_val_nth homsymdotpp // (inj_eq enum_val_inj) eq_sym.
rewrite (bigD1 l) //= big1 ?addr0 => [m /negbTE -> |].
  by rewrite mulr0.
rewrite eq_refl mulr1 mulrC; congr (_ * _).
by rewrite -coord_map_homsym ?map_homsymbp ?symbp_basis // map_homsyms.
Qed.

Theorem homsyms_orthonormal : orthonormal homsymdot ('hs : seq HSC).
Proof.
have hs_uniq := free_uniq (basis_free (symbs_basis algC Hd)).
apply/orthonormalP; split => /=; first exact: hs_uniq.
move=> f g /mapP[/= la _ {f}->]/mapP[/= mu _ {g}->].
by rewrite homsymdotss (inj_eq (injectiveP _ hs_uniq)).
Qed.

End Scalar.
