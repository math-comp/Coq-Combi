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
From mathcomp Require Import tuple finfun finset bigop ssrint ssralg path div.
From mathcomp Require Import rat ssralg ssrnum algC matrix.

From SsrMultinomials Require Import ssrcomplements poset freeg bigenough mpoly.

Require Import tools ordtype permuted partition Yamanouchi std tableau stdtab.
Require Import antisym sympoly Schur_basis permcent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma mprodXnE R nv (I : Type) (F : I -> 'X_{1..nv}) P m (r : seq _) :
    \prod_(i <- r | P i) 'X_[R, F i] ^+ m i
  = 'X_[\sum_(i <- r | P i) (F i *+ m i)].
Proof.
elim: r => [|x r ih]; first by rewrite !big_nil mpolyX0.
by rewrite !big_cons; case: (P x); rewrite ?(mpolyXD, mpolyXn) ih.
Qed.

Section CauchyKernel.

Variables (m0 n0 : nat).
Notation m := m0.+1.
Notation n := n0.+1.
Notation mxvec_index := (@mxvec_index m n).

Let vecmx_index := (enum_val \o cast_ord (esym (mxvec_cast m n))).

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
Notation Local "1" := idx.
Variable op : Monoid.com_law 1.
Local Notation "'*%M'" := op (at level 0).
Local Notation "x * y" := (op x y).

Lemma big_mxvec_index P F :
  \big[op/idx]_(i : 'I_(m*n) | P i) F i =
   \big[op/idx]_(i < m)
    \big[op/idx]_(j < n | P (mxvec_index i j)) F (mxvec_index i j).
Proof.
rewrite pair_big_dep.
rewrite (reindex (prod_curry mxvec_index)); first last.
  by apply: (subon_bij _ (curry_mxvec_bij m n)).
by apply eq_big => [] [i j].
Qed.

End Big.

Definition monX (mon : 'X_{1.. m*n}) :=
  [multinom (\sum_(j < n) mon (mxvec_index i j))%N | i < m].

Lemma mdeg_monX mon : mdeg (monX mon) = mdeg mon.
Proof.
rewrite /mdeg /monX !big_tuple.
rewrite big_mxvec_index /=; apply eq_bigr => i _.
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

Let polZ := {mpoly R[m*n]}.
Let polX := {mpoly R[m]}.
Let polY := {mpoly R[n]}.
Let polXY := {mpoly polY[m]}.
Definition polXY_scale (c : R) (p : polXY) := c%:MP *: p.
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
Canonical polXY_lmodType :=
  Eval hnf in LmodType R polXY polXY_lmodMixin.

Lemma scale_polXYE (c : R) (p : polXY) : c *: p = c *:M p.
Proof. by []. Qed.

Lemma polXY_scaleAl (c : R) (p q : polXY) : c *: (p * q : polXY) = (c *: p) * q.
Proof. by rewrite !scale_polXYE /polXY_scale /= -!mul_mpolyC mulrA. Qed.
Canonical polXY_lalgType :=
  Eval hnf in LalgType R polXY polXY_scaleAl.

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
  by rewrite scale_polXYE /polXY_scale /= -!mul_mpolyC rmorphM /=.
Qed.
Canonical polY_XY_additive   := Additive   polY_XY_is_lrmorphism.
Canonical polY_XY_rmorphism  := RMorphism  polY_XY_is_lrmorphism.
Canonical polY_XY_linear     := AddLinear  polY_XY_is_lrmorphism.
Canonical polY_XY_lrmorphism := LRMorphism polY_XY_is_lrmorphism.

Notation "p '(Y)'" := (polY_XY p) (at level 20, format "p '(Y)'").
Notation "p '(X)'" := (polX_XY p) (at level 20, format "p '(X)'").

Lemma polyXY_scale p q : p(X) * q(Y) = q *: p(X).
Proof. by rewrite mulrC mul_mpolyC. Qed.

Definition evalXY : polZ -> polXY :=
  mmap ((@mpolyC m _) \o (@mpolyC n R))
       (fun i => 'X_((vecmx_index i).1) (X) * 'X_((vecmx_index i).2) (Y)).
Notation "p '(XY)'" := (evalXY p) (at level 20, format "p '(XY)'").
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
rewrite big_mxvec_index.
rewrite /= mpolyXE_id rmorph_prod -scaler_prod; apply eq_bigr => i _.
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

Lemma prod_sympXY d (la : intpartn d) : 'p[la](XY) = 'p[la](X) * 'p[la](Y).
Proof.
rewrite /prod_symp /prod_gen /= !rmorph_prod /=.
rewrite -big_split /=; apply eq_bigr => i _.
by rewrite [LHS]sympXY.
Qed.

Definition Cauchy_kernel d := 'h_d(XY).

Lemma Cauchy_kernel_dhomog d : Cauchy_kernel d \is d.-homog.
Proof. by rewrite /Cauchy_kernel; apply evalXY_homog; apply: symh_homog. Qed.

Lemma symmX la : 'm[la](X) = 'm[la].
Proof.
have : map_sympoly (n := m) [rmorphism of (mpolyC n (R:=R))] 'm[la] = 'm[la].
  exact: map_symm.
by rewrite /polX_XY => /(congr1 val) => /= ->.
Qed.

Section BijectionFam.

Variable d : nat.

Lemma famY_subproof (mz : 'X_{1.. (m * n) < d.+1}) i :
    (mdeg (tnth (monsY (val mz)) i) < d.+1)%N.
Proof.
apply: (leq_ltn_trans _ (bmdeg mz)).
rewrite /mdeg /monsY tnth_mktuple !big_tuple big_mxvec_index /=.
rewrite (eq_bigr (fun j => tnth mz (mxvec_index i j))); first last.
  by move=> j _; rewrite tnth_mktuple -mnm_tnth.
by rewrite (bigD1 i) //= leq_addr.
Qed.
Definition famY mz := [ffun i => BMultinom (famY_subproof mz i)].
Let famYinv_fun (ff : {ffun ordinal_finType m -> 'X_{1.. n < d.+1}}) :=
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

Lemma Cauchy_symm_symh d :
  Cauchy_kernel d = \sum_(la : intpartn d) 'm[la](X) * 'h[la](Y).
Proof.
apply/mpolyP => mon.
case: (altP (mdeg mon =P d)) => Hdeg; first last.
  rewrite (dhomog_nemf_coeff (Cauchy_kernel_dhomog d) Hdeg).
  rewrite linear_sum /= big1 ?mcoeff0 // => la _.
  rewrite polyXY_scale mcoeffZ symmX.
  case: (ssrnat.leqP (size la) m) => [Hi | /symm_oversize ->].
  - rewrite mcoeff_symm //.
    suff /negbTE -> : ~~ perm_eq (mpart (n := m) la) mon by rewrite mulr0.
    apply/negP => /perm_sumn.
    rewrite sumn_mpart // intpartn_sumn -sumnE -/(mdeg _) => Hd.
    by rewrite -Hd eq_refl in Hdeg.
  - by rewrite mcoeff0 mulr0.
rewrite (eq_bigr (fun la => ('h[la] : polY) *: ('m[la] : polXY))); first last.
  by move=> la _; rewrite polyXY_scale symmX.
have Hpm : is_part_of_n d (partm mon) by rewrite /= intpartP andbT sumn_partm Hdeg.
pose pm := IntPartN Hpm.
rewrite (bigID (fun mu : intpartn d => (size mu <= m)%N)) /=.
rewrite linearD ![in RHS]linear_sum /=.
rewrite addrC big1 ?add0r; first last.
  move=> la; rewrite -ltnNge => /symm_oversize ->.
  by rewrite !raddf0.
rewrite (bigD1 pm) ?size_partm //= ?big1 ?addr0; first last.
  move=> la /andP [Hszla Hla].
  rewrite mcoeffZ mcoeff_symm //.
  suff /negbTE -> : ~~ perm_eq (mpart (n := m) la) mon by rewrite mulr0.
  apply/negP => /perm_eq_partm/(congr1 val)/=.
  rewrite mpartK // => Heq.
  by move: Hla; rewrite /eq_op /= Heq eq_refl.
rewrite mcoeffZ mcoeff_symm ?size_partm // perm_eq_sym partm_perm_eqK mulr1.
rewrite /Cauchy_kernel /prod_symh /prod_gen {1}/symh /= rmorph_prod /=.
rewrite rmorph_sum raddf_sum /= partmE; apply esym.
transitivity (\prod_(i <- mon) sympol 'h_i : polY ).
  rewrite [RHS](bigID (fun i => i == 0%N)) /=.
  rewrite [in RHS]big1 ?mul1r; first last.
    move=> i /eqP ->; exact: (congr1 val (symh0 n R)).
  rewrite /= -[RHS]big_filter; apply eq_big_perm.
  by rewrite perm_sort.
rewrite {Hpm pm} /= big_tuple; symmetry.
rewrite (bigID (fun mZ : 'X_{1.. _ < _} => monX mZ == mon)) /=.
rewrite addrC big1 ?add0r; first last.
  move=> i /andP [_ /negbTE Hneq].
  rewrite evalXY_XE -rmorph_prod /= polyXY_scale.
  by rewrite linearZ /= /polX_XY map_mpolyX mcoeffX Hneq mulr0.
rewrite (eq_bigl (fun mZ : 'X_{1.. _ < _} => monX mZ == mon)); first last.
  move=> i; rewrite andbC; case: eqP => //= Heq.
  by rewrite -{2}Hdeg -Heq mdeg_monX eq_refl.
rewrite (eq_bigr (fun mZ : 'X_{1.. _ < _} =>
                    \prod_(i < m) 'X_[tnth (monsY mZ) i])); first last.
  move=> mz Hmz; rewrite evalXY_XE -rmorph_prod /= polyXY_scale.
  by rewrite linearZ /= /polX_XY map_mpolyX mcoeffX Hmz mulr1.
rewrite (eq_bigr (fun i : 'I_m => symh_pol_bound n R d.+1 (tnth mon i)));
    first last.
    move=> i _; apply: symh_pol_any.
    rewrite ltnS -Hdeg /mdeg big_tuple (bigD1 i) //=.
    exact: leq_addr.
rewrite bigA_distr_big_dep => /=.
rewrite (reindex (famY (d := d))) /=; first last.
  exists (famYinv (d := d)).
  + move=> mz; rewrite inE => /familyP Hff.
    apply val_inj => /=.
    rewrite [[multinom _ | i < m * n]](_ : _ = val mz) /= ?bmdeg //.
    apply mnmP => c; rewrite mnmE /famY ffunE /=.
    rewrite tnth_mktuple mnmE //= -[in RHS](vecmx_indexK c).
    by case (vecmx_index c).
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
  + rewrite unfold_in ffunE /=.
    by rewrite mdeg_tnth_monsY Hmon.
  + apply/mnmP => i.
    have := Hfam i; rewrite unfold_in /= !mnm_tnth => /eqP <-.
    rewrite ffunE /= !tnth_mktuple.
    by rewrite mdegE; apply eq_bigr => j _; rewrite mnmE.
- apply eq_bigr => i _.
  by rewrite ffunE /= !tnth_mktuple.
Qed.

Lemma Cauchy_syms_syms d :
  Cauchy_kernel d = \sum_(la : intpartn d) 's[la](X) * 's[la](Y).
Proof.
rewrite Cauchy_symm_symh.
transitivity (\sum_(mu : intpartn d) \sum_(la : intpartn d)
               'm[mu](X) * ('K(la, mu) *: 's[la])(Y)).
  by apply eq_bigr => la _; rewrite symh_syms -mulr_sumr !linear_sum.
rewrite exchange_big /=; apply eq_bigr => la _.
have /= -> /= := congr1 val (syms_symm m0 R la).
rewrite 2!linear_sum /= mulr_suml; apply eq_bigr => mu _.
by rewrite !linearZ /= -scalerAr -scalerAl.
Qed.

End CauchyKernel.

Section CauchyKernelRat.
Notation "p '(Y)'" := (@polY_XY _ _ _ p) (at level 20, format "p '(Y)'").
Notation "p '(X)'" := (@polX_XY _ _ _ p) (at level 20, format "p '(X)'").
Notation "p '(XY)'" := (@evalXY _ _ _ p) (at level 20, format "p '(XY)'").


Lemma Cauchy_symp_symp m n d :
  Cauchy_kernel m n [comRingType of rat] d =
  \sum_(la : intpartn d) 'p[la](X) * ((zcard la)%:R^-1 *: 'p[la](Y)).
Proof.
rewrite /Cauchy_kernel symh_to_symp !rmorph_sum /=; apply eq_bigr => la _.
rewrite linearZ /= -scalerAr prod_sympXY; congr (_ *: _).
rewrite -rmorphMn /= rmorphV //=.
by rewrite unitfE pnatr_eq0 neq0zcard.
Qed.


End CauchyKernelRat.
