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
(** * Cauchy formula for symmetric polynomials

In this file we fix two non zero natural [m] and [n] and consider the two sets
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
*)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple bigop path finfun.
From mathcomp Require Import ssrint rat ssralg ssrnum algC matrix vector.

From SsrMultinomials Require Import ssrcomplements mpoly.

Require Import tools partition.
Require Import antisym Schur_mpoly Schur_altdef sympoly homogsym permcent.

Require ordtype.
Local Notation inh := ordtype.Inhabited.Exports.inh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Lemma char0_rat : [char rat] =i pred0.
Proof. exact: Num.Theory.char_num. Qed.
Local Lemma char0_algC : [char algC] =i pred0.
Proof. exact: Num.Theory.char_num. Qed.
#[local] Hint Resolve char0_algC char0_rat : core.


Reserved Notation "p '(Y)'"  (at level 20, format "p '(Y)'").
Reserved Notation "p '(X)'"  (at level 20, format "p '(X)'").
Reserved Notation "p '(XY)'" (at level 20, format "p '(XY)'").


(** ** Polynomials in two sets of variables *)
Section CauchyKernel.

Variables (m0 n0 : nat).
Notation m := m0.+1.
Notation n := n0.+1.
Notation mxvec_index := (@mxvec_index m n).

Let vecmx_index : 'I_(m * n) -> 'I_m * 'I_n :=
  (enum_val \o cast_ord (esym (mxvec_cast m n))).

Lemma vecmx_indexK i : mxvec_index (vecmx_index i).1 (vecmx_index i).2 = i.
Proof.
rewrite /vecmx_index/mxvec_index/prod_curry/=.
case H : (enum_val (cast_ord (esym (mxvec_cast m n)) i)) => /= [a b].
by rewrite -H enum_valK cast_ordKV.
Qed.
Lemma mxvec_indexK i j : vecmx_index (mxvec_index i j) = (i, j).
Proof.
rewrite /vecmx_index/mxvec_index/prod_curry/=.
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
rewrite pair_big_dep.
rewrite (reindex (prod_curry mxvec_index)); first last.
  by apply: (subon_bij _ (curry_mxvec_bij m n)).
by apply eq_big => [] [i j].
Qed.

End Big.

Definition monX (mon : 'X_{1.. m*n}) : 'X_{1.. m} :=
  [multinom (\sum_(j < n) mon (mxvec_index i j))%N | i < m].

Lemma mdeg_monX mon : mdeg (monX mon) = mdeg mon.
Proof.
rewrite /mdeg /monX !big_tuple big_mxvec_index /=; apply eq_bigr => i _.
rewrite tnth_mktuple; apply eq_bigr => j _.
by rewrite mnm_tnth.
Qed.

Definition monsY (mz : 'X_{1.. m*n}) :=
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


Variable (R : comRingType).

Local Notation polZ := {mpoly R[m * n]}.
Local Notation polX := {mpoly R[m]}.
Local Notation polY := {mpoly R[n]}.
Definition polXY := {mpoly polY[m]}.
Definition polXY_scale (c : R) (p : polXY) : polXY := c%:MP *: p.
Local Notation "c *:M p" := (polXY_scale c p)
  (at level 40, left associativity).

Lemma scale_polXYA a b p : a *:M (b *:M p) = (a * b) *:M p.
Proof. by rewrite /polXY_scale scalerA rmorphM. Qed.
Lemma scale_polXY1m p : 1 *:M p = p.
Proof. by rewrite /polXY_scale rmorph1 scale1r. Qed.
Lemma scale_polXYDr c p1 p2 :
  c *:M (p1 + p2) = c *:M p1 + c *:M p2.
Proof. exact: scalerDr. Qed.
Lemma scale_polXYDl p c1 c2 :
  (c1 + c2) *:M p = c1 *:M p + c2 *:M p.
Proof. by rewrite /polXY_scale rmorphD /= scalerDl. Qed.

Definition polXY_lmodMixin :=
  LmodMixin scale_polXYA scale_polXY1m scale_polXYDr scale_polXYDl.
Canonical polXY_lmodType := Eval hnf in LmodType R polXY polXY_lmodMixin.
Lemma scale_polXYE (c : R) (p : polXY) : c *: p = c *:M p.
Proof. by []. Qed.

Lemma polXY_scaleAl (c : R) (p q : polXY) : c *: (p * q : polXY) = (c *: p) * q.
Proof. by rewrite !scale_polXYE /polXY_scale /= -!mul_mpolyC mulrA. Qed.
Canonical polXY_lalgType := Eval hnf in LalgType R polXY polXY_scaleAl.

Lemma polXY_scaleAr (c : R) (p q : polXY) : c *: (p * q : polXY) = p * (c *: q).
Proof.
rewrite !scale_polXYE /polXY_scale /= -!mul_mpolyC.
by rewrite mulrA [_ * p]mulrC mulrA.
Qed.
Canonical polXY_algType := Eval hnf in AlgType R polXY polXY_scaleAr.


Definition polX_XY : polX -> polXY := map_mpoly (mpolyC n (R := R)).
Lemma polX_XY_is_lrmorphism : lrmorphism polX_XY.
Proof.
rewrite /polX_XY; repeat split.
- exact: rmorphB.
- exact: rmorphM.
- exact: rmorph1.
- move=> p c.
  by rewrite /map_mpoly mmapZ /= scale_polXYE /polXY_scale /= -!mul_mpolyC.
Qed.
Canonical polX_XY_additive   := Additive   polX_XY_is_lrmorphism.
Canonical polX_XY_rmorphism  := RMorphism  polX_XY_is_lrmorphism.
Canonical polX_XY_linear     := AddLinear  polX_XY_is_lrmorphism.
Canonical polX_XY_lrmorphism := LRMorphism polX_XY_is_lrmorphism.


Definition polY_XY : polY -> polXY := mpolyC m (R := [ringType of mpoly n R]).
Lemma polY_XY_is_lrmorphism : lrmorphism polY_XY.
Proof.
rewrite /polY_XY; repeat split.
- exact: rmorphB.
- exact: rmorphM.
- move=> p c.
  by rewrite scale_polXYE /polXY_scale /= -!mul_mpolyC rmorphM.
Qed.
Canonical polY_XY_additive   := Additive   polY_XY_is_lrmorphism.
Canonical polY_XY_rmorphism  := RMorphism  polY_XY_is_lrmorphism.
Canonical polY_XY_linear     := AddLinear  polY_XY_is_lrmorphism.
Canonical polY_XY_lrmorphism := LRMorphism polY_XY_is_lrmorphism.


Notation "p '(Y)'" := (polY_XY p).
Notation "p '(X)'" := (polX_XY p).

Lemma polyXY_scale p q : p(X) * q(Y) = q *: p(X).
Proof. by rewrite mulrC mul_mpolyC. Qed.

Lemma symmX d (la : 'P_d) : 'hm[la](X) = 'hm[la].
Proof.
by have /(congr1 val) := map_symm [rmorphism of (mpolyC n (R:=R))] m0 la.
Qed.


Definition evalXY : polZ -> polXY :=
  mmap ((@mpolyC m _) \o (@mpolyC n R))
       (fun i => 'X_((vecmx_index i).1) (X) * 'X_((vecmx_index i).2) (Y)).
Notation "p '(XY)'" := (evalXY p).

Lemma evalXY_is_lrmorphism : lrmorphism evalXY.
Proof.
rewrite /evalXY; repeat split.
- exact: rmorphB.
- exact: rmorphM.
- exact: rmorph1.
- move=> p c.
  by rewrite  mmapZ /= scale_polXYE /polXY_scale /= -!mul_mpolyC.
Qed.
Canonical evalXY_additive   := Additive   evalXY_is_lrmorphism.
Canonical evalXY_rmorphism  := RMorphism  evalXY_is_lrmorphism.
Canonical evalXY_linear     := AddLinear  evalXY_is_lrmorphism.
Canonical evalXY_lrmorphism := LRMorphism evalXY_is_lrmorphism.

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
  by rewrite mxvec_indexK /= rmorphX.
Qed.

Lemma evalXY_homog d p : p \is d.-homog -> p(XY) \is d.-homog.
Proof.
move/pihomog_dE <-; rewrite pihomogE.
rewrite rmorph_sum /=; apply rpred_sum => mon /eqP Hdeg.
rewrite linearZ /= scale_polXYE; apply rpredZ.
rewrite evalXY_XE -rmorph_prod /= polyXY_scale; apply rpredZ.
by rewrite /polX_XY map_mpolyX dhomogX /= mdeg_monX Hdeg.
Qed.

Lemma sympXY k : 'p_k(XY) = 'p_k(X) * 'p_k(Y).
Proof.
rewrite /= /symp_pol /= /evalXY /= !rmorph_sum /= big_mxvec_index /=.
rewrite mulr_suml; apply eq_bigr => i _ /=.
rewrite mulr_sumr; apply eq_bigr => j _ /=.
by rewrite !rmorphX /= mmapX mmap1U mxvec_indexK /= exprMn.
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

Lemma famY_subproof (mz : 'X_{1.. (m * n) < d.+1}) i :
    (mdeg (tnth (monsY (val mz)) i) < d.+1)%N.
Proof.
apply: (leq_ltn_trans _ (bmdeg mz)).
rewrite /mdeg /monsY tnth_mktuple !big_tuple big_mxvec_index /=.
under eq_bigr do rewrite tnth_mktuple mnm_tnth.
by rewrite (bigD1 i) //= leq_addr.
Qed.
Definition famY mz := [ffun i : 'I_m => BMultinom (famY_subproof mz i)].
Let famYinv_fun (ff : {ffun 'I_m -> 'X_{1.. n < d.+1}}) :=
  let mz := [multinom (ff (vecmx_index i).1 (vecmx_index i).2) | i < m * n]
  in if (mdeg mz < d.+1)%N then mz else 0%MM.
Lemma famYinv_subproof ff : (mdeg (famYinv_fun ff) < d.+1)%N.
Proof.
rewrite /famYinv_fun /=.
case: (ssrnat.ltnP (mdeg [multinom _ | i < _]) d.+1) => //= _.
by rewrite mdeg0.
Qed.
Definition famYinv ff := BMultinom (famYinv_subproof ff).

End BijectionFam.

Variable d : nat.

(** *** Cauchy formula for complete and monomial symmetric polynomials *)
Lemma Cauchy_symm_symh :
  Cauchy_kernel d = \sum_(la : 'P_d) ('h[la] : polY) *: ('m[la] : polXY).
Proof.
apply/mpolyP => mon.
case: (altP (mdeg mon =P d)) => Hdeg; first last.
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
have Hpm : is_part_of_n d (partm mon) by rewrite /= intpartP andbT sumn_partm Hdeg.
pose pm := IntPartN Hpm.
rewrite (bigID (fun mu : 'P_d => (size mu <= m)%N)) /=.
rewrite linearD ![in RHS]linear_sum /=.
rewrite addrC big1 ?add0r; first last.
  by move=> la; rewrite -ltnNge => /symm_oversize ->; rewrite !raddf0.
rewrite (bigD1 pm) ?size_partm //= ?big1 ?addr0; first last.
  move=> la /andP [Hszla Hla].
  rewrite mcoeffZ mcoeff_symm //.
  suff /negbTE -> : ~~ perm_eq (mpart (n := m) la) mon by rewrite mulr0.
  apply/negP => /perm_partm/(congr1 val)/=.
  rewrite mpartK // => Heq.
  by move: Hla; rewrite /eq_op /= Heq eq_refl.
rewrite mcoeffZ mcoeff_symm ?size_partm // perm_sym partm_permK mulr1.
rewrite /Cauchy_kernel /prod_symh /prod_gen {1}/symh /= rmorph_prod /=.
rewrite rmorph_sum raddf_sum /= partmE; apply esym.
transitivity (\prod_(i <- mon) sympol 'h_i : polY ).
  rewrite [RHS](bigID (fun i => i == 0%N)) /=.
  rewrite [in RHS]big1 ?mul1r; first last => [i /eqP ->|].
    exact: (congr1 val (symh0 n R)).
  rewrite /= -[RHS]big_filter; apply: perm_big.
  by rewrite perm_sort.
rewrite {Hpm pm} /= big_tuple; symmetry.
rewrite (bigID (fun mZ : 'X_{1.. _ < _} => monX mZ == mon)) /=.
rewrite addrC big1 ?add0r; first last.
  move=> i /andP [_ /negbTE Hneq].
  rewrite evalXY_XE -rmorph_prod /= polyXY_scale.
  by rewrite linearZ /= /polX_XY map_mpolyX mcoeffX Hneq mulr0.
under eq_bigl=> i do [rewrite andb_idl;
  last by move=> /eqP; rewrite -{3}Hdeg => <-; rewrite mdeg_monX].
under [LHS]eq_bigr => mz Hmz.
  rewrite evalXY_XE -rmorph_prod /= polyXY_scale.
  by rewrite linearZ /= /polX_XY map_mpolyX mcoeffX Hmz mulr1 over.
under [RHS]eq_bigr => i _ do
  [rewrite (@symh_pol_any _ _ d.+1) //;
     last by rewrite ltnS -Hdeg /mdeg big_tuple (bigD1 i) // leq_addr].
rewrite bigA_distr_big_dep => /=.
rewrite (reindex (famY (d := d))) /=; first last.
  exists (famYinv (d := d)).
  + move=> mz; rewrite inE => /familyP Hff.
    apply val_inj => /=.
    rewrite [[multinom _ | i < m * n]](_ : _ = val mz) /= ?bmdeg //.
    apply mnmP => c; rewrite mnmE /famY ffunE /=.
    by rewrite tnth_mktuple mnmE //= -[in RHS](vecmx_indexK c).
  + move=> ff; rewrite inE => /familyP H /=.
    apply/ffunP => /= i; rewrite ffunE; apply val_inj => /=.
    rewrite [mdeg _](_ : _ = d) ?ltnSn; first last.
      rewrite -[RHS]Hdeg !mdegE big_mxvec_index => /=; apply eq_bigr => i' _.
      have {H} := H i'; rewrite unfold_in mnm_tnth => /eqP <-.
      rewrite mdegE; apply eq_bigr => j _.
      by rewrite mnmE mxvec_indexK /=.
    by rewrite tnth_mktuple; apply mnmP => j; rewrite !mnmE mxvec_indexK /=.
apply eq_big => [mz | mz /eqP Hmz].
- apply/eqP/familyP => [/= Hmon i | Hfam].
  + by rewrite unfold_in ffunE /= mdeg_tnth_monsY Hmon.
  + apply/mnmP => i.
    have := Hfam i; rewrite unfold_in /= !mnm_tnth => /eqP <-.
    by rewrite ffunE /= !tnth_mktuple mdegE; apply eq_bigr => j _; rewrite mnmE.
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
rewrite Cauchy_symm_symh; apply rpred_sum => la _.
by apply rpredZ; apply sympolP.
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
  [char R] =i pred0 ->
  Cauchy_kernel m n R d =
  \sum_(la : 'P_d) 'hp[la](X) * ((zcard la)%:R^-1 *: 'hp[la](Y)).
Proof.
move=> Hchar.
rewrite /Cauchy_kernel symh_to_symp // !rmorph_sum /=; apply eq_bigr => la _.
by rewrite linearZ /= -scalerAr prod_sympXY; congr (_ *: _).
Qed.

End CauchyKernelField.


(** * Cauchy kernel and scalar product of symmetric functions *)
Section Scalar.

Variable n0 d : nat.
Local Notation n := n0.+1.
Hypothesis Hd : (d <= n)%N.

Local Notation ratF := [numFieldType of rat].
Local Notation algCF := [numFieldType of algC].
Local Notation HSC := {homsym algC[n, d]}.
Local Notation HSQ := {homsym rat[n, d]}.
Local Notation polXY := (polXY n0 n0 algCF).
Local Notation pol := {mpoly algC[n]}.
Local Notation "p '(Y)'" := (@polY_XY n0 n0 _ p)
                             (at level 20, format "p '(Y)'").
Local Notation "p '(X)'" := (@polX_XY n0 n0 _ p)
                             (at level 20, format "p '(X)'").

Local Notation "''hsC[' la ]" := ('hs[la] : HSC).
Local Notation "''hsQ[' la ]" := ('hs[la] : HSQ).
Local Notation "''hpC[' la ]" := ('hp[la] : HSC).
Local Notation "''hpQ[' la ]" := ('hp[la] : HSQ).


Definition co_hp (la : 'P_d) : pol -> algC :=
  homsymdotr 'hp[la] \o in_homsym d (R := algCF).
Definition co_hpXY (la mu : 'P_d) : polXY -> algC :=
  locked (co_hp la \o map_mpoly (co_hp mu)).

Lemma co_hp_is_additive la : additive (co_hp la).
Proof. by rewrite /co_hp => p q; rewrite raddfB. Qed.
Canonical co_hp_additive la := Additive (co_hp_is_additive la).
Lemma scale_co_hp la p a : co_hp la (a *: p) = a * co_hp la p.
Proof. by rewrite /co_hp /= linearZ homsymdotZl. Qed.
Lemma co_hp_hp la mu : co_hp la 'hp[mu] = (zcard mu)%:R * (mu == la)%:R.
Proof using Hd.
by rewrite /co_hp /= -![prod_gen _ _]/(homsym 'hp[_]) in_homsymE homsymdotpp.
Qed.

Lemma co_hpXY_is_additive la mu : additive (co_hpXY la mu).
Proof. by rewrite /co_hpXY; unlock => p q; rewrite raddfB. Qed.
Canonical co_hpXY_additive la mu := Additive (co_hpXY_is_additive la mu).

Lemma co_hpYE la (p q : pol) :
  map_mpoly (co_hp la) (p(X) * q(Y)) = co_hp la q *: p.
Proof.
rewrite polyXY_scale /=; apply/mpolyP => /= m.
rewrite linearZ /= mcoeff_map_mpoly /= linearZ /= mulrC.
rewrite /polX_XY /= mcoeff_map_mpoly /= mul_mpolyC.
by rewrite mulrC -scale_co_hp.
Qed.

Lemma co_hprXYE la mu (p q : pol) :
  co_hpXY la mu (p(X) * q(Y)) = (co_hp la p) * (co_hp mu q).
Proof. by rewrite /co_hpXY; unlock; rewrite /= co_hpYE scale_co_hp mulrC. Qed.

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
        )); first last.
  move=> nu _; rewrite {1 2}(coord_span (to_p nu)).
  by rewrite linear_sum; congr ((_)(X) * (_)(Y)); rewrite sum_coord.
move=> {sum_coord to_p} /(congr1 (co_hpXY la mu)).
rewrite !raddf_sum /= => /esym.
rewrite (bigD1 la) //= -[(zcard la)%:R^-1 *: 'hp[la](Y)]linearZ /=.
rewrite -![prod_gen _ _]/(homsym 'hp[_]).
rewrite co_hprXYE scale_co_hp co_hp_hp //.
rewrite eq_refl mulr1 !mulrA divff ?mul1r; last by rewrite pnatr_eq0 neq0zcard.
rewrite big1 ?addr0; first last => [nu /negbTE Hnu |].
  rewrite -![prod_gen _ _]/(homsym 'hp[_]).
  rewrite -[(zcard nu)%:R^-1 *: 'hp[nu](Y)]linearZ /=.
  rewrite -![prod_gen _ _]/(homsym 'hp[_]).
  rewrite co_hprXYE scale_co_hp co_hp_hp //.
  move: Hnu; rewrite -(inj_eq (@val_inj _ _ _)) /= => ->.
  by rewrite mulr0 !mul0r.
rewrite co_hp_hp // => /(congr1 (fun x => (zcard la)%:R^-1 * x)).
rewrite mulrA [X in X * _]mulrC divff; last by rewrite pnatr_eq0 neq0zcard.
rewrite mul1r !mulr_sumr => -> .
apply eq_bigr => nu _.
rewrite co_hprXYE.
have dot_sumhp (eta tau : 'P_d) :
  co_hp eta (\sum_px coord 'hp (enum_rank px) 'hsC[tau] *: 'hp[px]) =
  coord 'hp (enum_rank eta) 'hsC[tau] * (zcard eta)%:R.
  rewrite !raddf_sum /= (bigD1 eta) //=.
  rewrite -![prod_gen _ _]/(homsym 'hp[_]).
  rewrite scale_co_hp co_hp_hp // eq_refl mulr1.
  rewrite big1 ?addr0 // => p => /negbTE Hp.
  rewrite -![prod_gen _ _]/(homsym 'hp[_]).
  rewrite scale_co_hp co_hp_hp //.
  move: Hp; rewrite -(inj_eq (@val_inj _ _ _)) /= => ->.
  by rewrite !mulr0.
rewrite !{}dot_sumhp ![_ * (zcard _)%:R]mulrC !mulrA.
by rewrite ![_ * (zcard la)%:R]mulrC divff ?mul1r // pnatr_eq0 neq0zcard.
Qed.

Lemma coord_zsymspsp (la mu : 'P_d) :
  (\sum_nu
    (coord 'hp (enum_rank nu) 'hsC[la]) *
    ((zcard nu)%:R * coord 'hp (enum_rank nu) 'hsC[mu]))
  = (la == mu)%:R.
Proof using Hd.
pose matsp : 'M[algCF]_#|{:'P_d}| :=
  \matrix_(i, j < #|{:'P_d}|) (coord 'hp i 'hsC[enum_val j]).
pose matzsp : 'M[algCF]_#|{:'P_d}| :=
  \matrix_(i, j < #|{:'P_d}|)
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
  (\sum_(i < #|{:'P_d}|)
    (coord 'hp i 'hsC[mu])^* * (zcard (enum_val l))%:R * (i == l)%:R).
  apply: eq_bigr => i _; rewrite homsymdotZr -mulrA; congr (_ * _).
  rewrite !(nth_map inh _ (fun l => 'hp[l])) -?cardE ?ltn_ord //.
  by rewrite -!enum_val_nth homsymdotpp // (inj_eq enum_val_inj) eq_sym.
rewrite (bigD1 l) //= big1 ?addr0; last by move=> m /negbTE ->; rewrite mulr0.
rewrite eq_refl mulr1 mulrC; congr (_ * _).
by rewrite -coord_map_homsym ?map_homsymbp ?symbp_basis // map_homsyms.
Qed.

End Scalar.

