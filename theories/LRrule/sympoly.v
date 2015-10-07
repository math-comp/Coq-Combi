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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice.
Require Import finset fintype finfun tuple bigop ssralg ssrint.
Require Import ssrcomplements poset freeg bigenough mpoly.

Require Import partition skewtab Schur sym_group therule Schur_alt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory BigEnough.




Local Open Scope ring_scope.

Section MPoESymHomog.

Variable n : nat.
Variable R : comRingType.

Implicit Types p q r : {mpoly R[n]}.
Implicit Types m : 'X_{1..n}.

Lemma prod_homog l (dt : l.-tuple nat) (mt : l.-tuple {mpoly R[n]}) :
  (forall i : 'I_l, tnth mt i \is (tnth dt i).-homog) ->
  \prod_(i <- mt) i \is (\sum_(i <- dt) i).-homog.
Proof.
  elim: l dt mt => [| l IHl] dt mt H.
    rewrite tuple0 big_nil tuple0 big_nil; exact: dhomog1.
  case/tupleP: dt H => d dt.
  case/tupleP: mt => p mt H /=.
  rewrite !big_cons; apply dhomogM.
    have := H ord0 => /=; by rewrite (tnth_nth 0) (tnth_nth 0%N).
  apply IHl => i.
  have := H (inord i.+1).
  rewrite !(tnth_nth 0) !(tnth_nth 0%N) /=.
  by rewrite !inordK; last exact: (ltn_ord i).
Qed.

Local Notation E := [tuple mesym n R i.+1  | i < n].

Lemma mesym_homog k : mesym n R k \is k.-homog.
Proof.
  apply/dhomogP => m.
  rewrite msupp_mesymP => /existsP [] s /andP [] /eqP <- {k} /eqP -> {m}.
  exact: mdeg_mesym1.
Qed.

Lemma homog_X_mPo_elem (m : 'X_{1..n}) :
  'X_[m] \mPo E \is (mnmwgt m).-homog.
Proof.
  rewrite comp_mpolyX.
  pose dt := [tuple (i.+1 * (m i))%N | i < n].
  pose mt := [tuple (mesym n R i.+1) ^+ m i | i < n] : n.-tuple {mpoly R[n]}.
  rewrite (eq_bigr (fun i : 'I_n => tnth mt i)); first last.
    by move=> i _ /=; rewrite !tnth_mktuple.
  rewrite -(big_tuple _ _ mt xpredT id).
  rewrite /mnmwgt (eq_bigr (fun i : 'I_n => tnth dt i)); first last.
    by move=> i _ /=; rewrite !tnth_mktuple mulnC.
  rewrite -(big_tuple _ _ dt xpredT id).
  apply prod_homog => i.
  rewrite !tnth_mktuple {mt dt}; apply: dhomog_expr.
  exact: mesym_homog.
Qed.

Lemma pihomog_mPo p d :
  pihomog [measure of mdeg] d (p \mPo E) = (pihomog [measure of mnmwgt] d p) \mPo E.
Proof.
  elim/mpolyind: p => [| c m p Hm Hc IHp] /=; first by rewrite !linear0.
  rewrite !linearP /= {}IHp; congr (c *: _ + _).
  case: (altP (mnmwgt m =P d)) => H.
  - have/eqP := H; rewrite -(dhomogX R) => /pihomog_dE ->.
    have:= homog_X_mPo_elem m; by rewrite H => /pihomog_dE ->.
  - rewrite (pihomog_ne0 H (homog_X_mPo_elem m)).
    rewrite (pihomog_ne0 H); first by rewrite linear0.
    by rewrite dhomogX.
Qed.

Lemma mwmwgt_homogE (p : {mpoly R[n]}) d :
  p \is d.-homog for [measure of mnmwgt] = ((p \mPo E) \is d.-homog).
Proof.
  rewrite !homog_piE; rewrite pihomog_mPo.
  by apply (sameP idP); apply (iffP idP) => [/eqP/msym_fundamental_un | /eqP] ->.
Qed.

End MPoESymHomog.



Section SchurBasis.

Variable n : nat.
Variable R : idomainType.
Hypothesis Hnpos : n != 0%N.
Local Notation Alph := (Alph Hnpos).

Local Notation "''e_' k" := (@mesym n R k)
                              (at level 8, k at level 2, format "''e_' k").
Local Notation "''s_' k" := (Schur Hnpos R k) (at level 8, k at level 2, format "''s_' k").
Local Notation S := [tuple mesym n R i.+1 | i < n].

Lemma Schur_homog (d : nat) (sh : intpartn d) : 's_sh \is d.-homog.
Proof.
  rewrite /Schur /polylang /commword; apply rpred_sum => [[t Ht]] _ /=.
  move: Ht => /eqP <-; elim: t => [| s0 s IHs]/=.
    rewrite big_nil; exact: dhomog1.
  rewrite big_cons -add1n; apply dhomogM; last exact: IHs.
  by rewrite dhomogX /= mdeg1.
Qed.

Record homcoeff : Type := HomCoeff { d : nat; coe :> intpartn d -> R }.

Definition Schur_dec (p : {mpoly R[n]}) :=
  { coe : homcoeff | p = \sum_(p : intpartn _) coe p *: 's_p }.

Lemma Schur_dec1 : Schur_dec 1.
Proof.
  exists (HomCoeff (fun p : intpartn 0 => 1)) => /=.
  rewrite (eq_bigr (fun p => 1)); last by move=> p _; rewrite scale1r; exact: Schur0.
  by rewrite sumr_const /= card_intpartn /intpartn_nb /= /intpartns_nb /= add0n.
Qed.

Lemma Schur_dec_mesym k : Schur_dec 'e_k.
Proof.
  rewrite /= elementaryE /elementary.
  exists (HomCoeff (fun p : intpartn k => (p == colpartn k)%:R)) => /=.
  rewrite (bigID (fun p => p == colpartn k)) /=.
  rewrite big_pred1_eq eq_refl /= scale1r.
  rewrite (eq_bigr (fun p => 0)); last by move=> i /negbTE ->; rewrite scale0r.
  by rewrite big1_eq addr0.
Qed.

Lemma Schur_dec_mesym_pow k i : Schur_dec ('e_k ^+ i).
Proof.
  elim: i => [| i [[d coe /= Hcoe]]] /=; first exact: Schur_dec1.
  exists (HomCoeff (fun p : intpartn (d + k) =>
                      \sum_(sh : intpartn d | vb_strip sh p) coe sh)).
  rewrite /= exprS Hcoe mulrC mulr_suml.
  rewrite (eq_bigr
             (fun sh : intpartn d =>
                 (\sum_(p : intpartn (d + k) | vb_strip sh p) coe sh *: 's_p))); first last.
    by move=> p _; rewrite -scalerAl elementaryE Pieri_elementary scaler_sumr.
  rewrite (exchange_big_dep xpredT) //=.
  apply eq_bigr => sh _; by rewrite scaler_suml.
Qed.

Lemma Schur_decM p q : Schur_dec p -> Schur_dec q -> Schur_dec (p * q).
Proof.
  move=> [[d1 c1 /= ->]] [[d2 c2 /= ->]].
  exists (HomCoeff (fun p : intpartn (d1 + d2) =>
                      \sum_(sh1 : intpartn d1)
                       \sum_(sh2 : intpartn d2)
                       c1 sh1 * c2 sh2 * (LRtab_coeff sh1 sh2 p)%:R)) => /=.
  rewrite mulr_suml.
  rewrite (eq_bigr
             (fun sh : intpartn (d1 + d2) =>
                (\sum_sh1 c1 sh1 *: \sum_sh2 c2 sh2 * (LRtab_coeff sh1 sh2 sh)%:R
                  *: Schur Hnpos R sh)));
    first last.
    move=> sh _; rewrite scaler_suml; apply eq_bigr => sh1 _.
    rewrite scaler_suml scaler_sumr; apply eq_bigr => sh2 _.
    by rewrite !scalerA mulrA.
  rewrite exchange_big /=; apply eq_bigr => sh1 _.
  rewrite -scaler_sumr -scalerAl; congr (c1 sh1 *: _).
  rewrite exchange_big /= mulr_sumr; apply eq_bigr => sh2 _.
  rewrite -scalerAr Schur.LRtab_coeffP.
  rewrite scaler_sumr; apply eq_bigr => sh _.
  by rewrite -scalerA scaler_nat.
Qed.

Lemma Schur_dec_mPoS m : Schur_dec ('X_[m] \mPo S).
Proof.
  rewrite comp_mpolyX /index_enum -enumT.
  elim: (enum _) => [| s IHs]; first by rewrite big_nil; exact: Schur_dec1.
  rewrite big_cons; apply: Schur_decM.
  rewrite tnth_mktuple; exact: Schur_dec_mesym_pow.
Qed.

Lemma Schur_dec_homog d p : p \is d.-homog -> Schur_dec p ->
  { coe : intpartn d -> R | p = \sum_(p : intpartn _) coe p *: 's_p }.
Proof.
  move=> Hp [[d1 co /= Hco]].
  case: (altP (p =P 0)) => [-> | Hn0].
    exists (fun _ => 0); apply esym; apply big1 => sh _; by rewrite scale0r.
  have : \sum_p0 co p0 *: Schur Hnpos R p0 \is d1.-homog.
    apply rpred_sum => sh _; apply rpredZ; exact: Schur_homog.
  rewrite -Hco => /(dhomog_uniq Hn0 Hp) Hd; subst d1.
  exists co; by rewrite Hco.
Qed.

Lemma Schur_dec_sym_homog d p : p \is symmetric -> p \is d.-homog ->
  { coe : intpartn d -> R | p = \sum_(p : intpartn _) coe p *: 's_p }.
Proof.
  move=> /sym_fundamental [] pe [] <- _.
  rewrite -mwmwgt_homogE => /dhomogP.
  rewrite {2}(mpolyE pe); elim: (msupp pe) => [_| m0 supp IHsupp Hhomog] /=.
    rewrite big_nil comp_mpoly0.
    exists (fun _ => 0); apply esym; apply big1 => sh _; by rewrite scale0r.
  have : {in supp, forall m : 'X_{1..n}, [measure of mnmwgt] m = d}.
    by move=> m Hm /=; apply Hhomog; rewrite inE Hm orbT.
  rewrite big_cons linearP /= => /IHsupp{IHsupp} [coe ->].
  have : 'X_[m0] \mPo [tuple mesym n R i.+1  | i < n] \is d.-homog.
    by rewrite -mwmwgt_homogE dhomogX; rewrite Hhomog // inE eq_refl.
  move/Schur_dec_homog/(_ (Schur_dec_mPoS m0)) => [com0 ->].
  exists (fun sh => pe@_m0 * (com0 sh) + coe sh).
  rewrite scaler_sumr -big_split /=; apply eq_bigr => sh _.
  by rewrite scalerA scalerDl.
Qed.

End SchurBasis.

Reserved Notation "{ 'sympoly' T [ n ] }"
  (at level 0, T, n at level 2, format "{ 'sympoly'  T [ n ] }").


Section Canonical.

Variable n : nat.
Variable R : idomainType.

Structure sympoly : predArgType :=
  SymPoly {spol :> {mpoly R[n]}; _ : spol \in symmetric}.

Canonical sympoly_subType := [subType for spol].
Definition sympoly_eqMixin := [eqMixin of sympoly by <:].
Canonical sympoly_eqType := EqType sympoly sympoly_eqMixin.
Definition sympoly_choiceMixin := [choiceMixin of sympoly by <:].
Canonical sympoly_choiceType := ChoiceType sympoly sympoly_choiceMixin.
Definition sympoly_zmodMixin := [zmodMixin of sympoly by <:].
Canonical sympoly_zmodType := ZmodType sympoly sympoly_zmodMixin.
Definition sympoly_ringMixin := [ringMixin of sympoly by <:].
Canonical sympoly_ringType := RingType sympoly sympoly_ringMixin.
Definition sympoly_comRingMixin := [comRingMixin of sympoly by <:].
Canonical sympoly_comRingType := ComRingType sympoly sympoly_comRingMixin.
Definition sympoly_unitRingMixin := [unitRingMixin of sympoly by <:].
Canonical sympoly_unitRingType := UnitRingType sympoly sympoly_unitRingMixin.
Canonical sympoly_comUnitRingType := [comUnitRingType of sympoly].
Definition sympoly_idomainMixin := [idomainMixin of sympoly by <:].
Canonical sympoly_idomainType := IdomainType sympoly sympoly_idomainMixin.
Definition sympoly_lmodMixin := [lmodMixin of sympoly by <:].
Canonical sympoly_lmodType := LmodType R sympoly sympoly_lmodMixin.
Definition sympoly_lalgMixin := [lalgMixin of sympoly by <:].
Canonical sympoly_lalgType := LalgType R sympoly sympoly_lalgMixin.
Definition sympoly_algMixin := [algMixin of sympoly by <:].
Canonical sympoly_algType := AlgType R sympoly sympoly_algMixin.
Canonical sympoly_unitAlgType := [unitAlgType R of sympoly].

Definition sympoly_of of phant R := sympoly.

Identity Coercion type_sympoly_of : sympoly_of >-> sympoly.

End Canonical.

Bind Scope ring_scope with sympoly_of.
Bind Scope ring_scope with sympoly.

Notation "{ 'sympoly' T [ n ] }" := (sympoly_of n (Phant T)).



Section SchurSym.

Variable n : nat.
Variable R : idomainType.

Definition mesym_sympoly k : {sympoly R[n]} := SymPoly (mesym_sym n R k).

Local Notation "''e_' k" := (@mesym_sympoly k)
                              (at level 8, k at level 2, format "''e_' k").

Definition mesym_part (s : seq nat) : {sympoly R[n]} := \prod_(i <- s) 'e_i.

Local Notation "''e_(' s ')'" := (@mesym_part s).

Hypothesis Hnpos : n != 0%N.
Local Notation Alph := (Alph Hnpos).

Definition Schur_sympoly d (k : intpartn d) : {sympoly R[n]} :=
  match (boolP ((size k) <= n)) with
    | AltTrue pf => SymPoly (Schur_sym R Hnpos pf)
    | AltFalse _ => 0
  end.

Local Notation "''s_' k" := (Schur Hnpos R k) (at level 8, k at level 2, format "''s_' k").

End SchurSym.
