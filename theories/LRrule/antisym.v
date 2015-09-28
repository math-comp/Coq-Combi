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
Require Import fingroup perm zmodp binomial poly.
Require Import ssrcomplements poset freeg mpoly.

Require Import sym_group.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Section Msym_Mpo.

Require Import bigenough.
Import BigEnough.

Variable n m : nat.
Variable R : comRingType.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Lemma msym_mPo (s : 'S_n) (p : {mpoly R[n]}) (T : n.-tuple {mpoly R[m]}) :
  (msym s p) \mPo T = p \mPo [tuple tnth T (s i) | i < n].
Proof.
  pose_big_enough l.
  rewrite !(comp_mpolywE _ (w := l)) //. 2: by close.
  pose F := fun m0 : 'X_{1..n < l} => m0#s.
  have FP m0 : mdeg (F m0) < l by rewrite /F mdeg_mperm; exact: bmdeg.
  pose FB := fun m0 : 'X_{1..n < l} => BMultinom (FP m0).
  have FB_inj : injective FB.
    move=> i j => H; apply val_inj => /=.
    have := erefl (val (FB i)); rewrite {2}H /=.
    rewrite /F; exact: mperm_inj.
  rewrite [RHS](reindex_inj FB_inj) /=.
  apply: eq_bigr => m0 _.
  rewrite {FB_inj FB FP}/F mcoeff_sym; congr (_ *: _).
  rewrite (reindex_inj (@perm_inj _ s)) /=.
  apply: eq_bigr => i _.
  by rewrite mnmE tnth_mktuple.
Qed.

End Msym_Mpo.

Section CharMPoly.

Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.

Lemma char_mpoly : [char R] =i [char {mpoly R[n]}].
Proof.
  move=> p; rewrite !unfold_in /= -mpolyC_nat.
  case: (prime.prime p) => //=.
  apply (sameP idP); apply (iffP idP) => [/eqP | /eqP -> //=].
  rewrite -(mpolyP) => H; have {H} /= := H 0%MM.
  by rewrite mcoeff0 raddfMn /= mcoeffMn mcoeff1 eq_refl /= => ->.
Qed.

End CharMPoly.


Section MPolySym.

Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.

Lemma issym_tpermP p :
  reflect (forall i j, msym (tperm i j) p = p)
          (p \is symmetric).
Proof.
  apply (iffP idP).
  - move=> /forallP Hsym i j.
    by rewrite (eqP (Hsym (tperm _ _))).
  - move=> Htperm; apply/forallP => s.
    case: (prod_tpermP s) => ts -> {s} Hall.
    elim: ts Hall => [_ | t0 ts IHts] /=.
      by rewrite !big_nil /= msym1m.
    move=> /andP [] _ /IHts{IHts}/eqP Hrec.
    by rewrite !big_cons msymMm Htperm Hrec.
Qed.

Definition antisym : qualifier 0 {mpoly R[n]} :=
  [qualify p | [forall s, msym s p == (-1) ^+ s *: p]].

Fact antisym_key : pred_key antisym. Proof. by []. Qed.
Canonical antisym_keyed := KeyedQualifier antisym_key.

Lemma isantisymP p :
  reflect (forall s, msym s p = (-1) ^+ s *: p) (p \is antisym).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti s.
    by rewrite (eqP (Hanti s )).
  - move=> H; apply/forallP => s.
    by rewrite H.
Qed.

Definition simplexp := (expr0, expr1, scale1r, scaleN1r, mulrN, mulNr, mulrNN, opprK).

Lemma isantisym_tpermP p :
  reflect (forall i j, msym (tperm i j) p = if (i != j) then - p else p)
          (p \is antisym).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti i j.
    rewrite (eqP (Hanti (tperm _ _))) odd_tperm.
    case: (i != j); by rewrite !simplexp.
  - move=> Htperm; apply/forallP => s.
    case: (prod_tpermP s) => ts -> {s} Hall.
    elim: ts Hall => [_ | t0 ts IHts] /=.
      by rewrite !big_nil odd_perm1 /= msym1m expr0 scale1r.
    move=> /andP [] H0 /IHts{IHts}/eqP Hrec.
    rewrite !big_cons msymMm Htperm H0 msymN Hrec.
    rewrite odd_mul_tperm H0 /=.
    by case: (odd_perm _); rewrite !simplexp.
Qed.

Lemma antisym_char2 : (2 \in [char R]) -> symmetric =i antisym.
Proof.
  move=> Hchar p /=.
  apply (sameP idP); apply (iffP idP).
  - move=> /isantisymP H; apply/issymP => s.
    by rewrite H oppr_char2; first by rewrite expr1n scale1r.
  - move => /issymP H; apply/isantisymP => s.
    by rewrite H oppr_char2; first by rewrite expr1n scale1r.
Qed.

Lemma perm_smalln : n <= 1 -> forall s : 'S_n, s = 1%g.
Proof.
  move=> Hn s; rewrite -permP => i.
  rewrite perm1.
  case: n Hn s i => [| [| n']] //= Hn s; first by case.
  move=> i; case: (s i) => a Ha; case: i => b Hb.
  apply val_inj => /=.
  by case: a b Ha Hb => [|a][|b].
Qed.

Lemma sym_smalln : n <= 1 -> (@symmetric n R) =i predT.
Proof.
  move=> Hn p /=; rewrite [RHS]unfold_in /=.
  apply/issymP => s.
  by rewrite (perm_smalln Hn s) msym1m.
Qed.

Lemma antisym_smalln : n <= 1 -> antisym =i predT.
Proof.
  move=> Hn p /=; rewrite [RHS]unfold_in /=.
  apply/isantisymP => s.
  by rewrite (perm_smalln Hn s) odd_perm1 msym1m expr0 scale1r.
Qed.

Lemma sym_anti p q :
  p \is antisym -> q \is symmetric -> p * q \is antisym.
Proof.
  move=> /isantisymP Hsym /issymP Hanti.
  apply/isantisymP => s.
  rewrite msymM Hsym Hanti.
  by case: (odd_perm _); rewrite !simplexp.
Qed.

Lemma anti_anti p q :
  p \is antisym -> q \is antisym -> p * q \is symmetric.
Proof.
  move=> /isantisymP Hp /isantisymP Hq.
  apply/issymP => s.
  rewrite msymM Hp Hq.
  by case: (odd_perm _); rewrite !simplexp.
Qed.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Lemma isantisym_msupp p (s : 'S_n) (m : 'X_{1..n}) : p \is antisym ->
  (m#s \in msupp p) = (m \in msupp p).
Proof.
  rewrite !mcoeff_msupp -mcoeff_sym => /isantisymP ->.
  case: (odd_perm s); last by rewrite expr0 scale1r.
  rewrite expr1 scaleN1r !mcoeff_eq0.
  by rewrite (perm_eq_mem (msuppN _)).
Qed.

Lemma mlead_antisym_sorted (p : {mpoly R[n]}) : p \is antisym ->
  forall (i j : 'I_n), i <= j -> (mlead p) j <= (mlead p) i.
Proof.
move=> sym_p i j le_ij; have [->|nz_p] := eqVneq p 0.
  by rewrite mlead0 !mnm0E.
set m := mlead p; case: leqP=> // h.
pose s := tperm i j; pose ms := m#s; have: (m < ms)%O.
  apply/lemP; first by rewrite mdeg_mperm.
  exists i=> [k lt_ki|]; last by rewrite mnmE tpermL.
  rewrite mnmE tpermD // neq_ltn orbC ?lt_ki //.
  by move/leq_trans: lt_ki => /(_ _ le_ij) ->.
have: ms \in msupp p by rewrite isantisym_msupp // mlead_supp.
by move/msupp_le_mlead/leoNgt/negbTE=> ->.
Qed.

End MPolySym.

Implicit Arguments antisym [n R].



Lemma issym_eltrP n (R : ringType) (p : {mpoly R[n.+1]}) :
  reflect (forall i, i < n -> msym (eltr n i) p = p) (p \is symmetric).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti i Hi.
    by have /eqP -> := Hanti (eltr n i).
  - move=> Heltr; apply/forallP; elim/eltr_ind => [| S i Hi /eqP IH].
    + by rewrite msym1m.
    + by rewrite msymMm (Heltr i Hi) IH.
Qed.

Lemma isantisym_eltrP n (R : ringType) (p : {mpoly R[n.+1]}) :
  reflect (forall i, i < n -> msym (eltr n i) p = - p) (p \is antisym).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti i Hi.
    have /eqP -> := Hanti (eltr n i).
    by rewrite /eltr odd_tperm (inordi1 Hi) !simplexp.
  - move=> Heltr; apply/forallP; elim/eltr_ind => [| S i Hi /eqP IH].
    + by rewrite odd_perm1 /= msym1m !simplexp.
    + rewrite msymMm (Heltr i Hi).
      rewrite msymN IH odd_mul_tperm (inordi1 Hi) addTb.
      by case: (odd_perm _); rewrite !simplexp.
Qed.


Section MPolyIDomain.

Variable n : nat.
Variable R : idomainType.

Implicit Types p q r : {mpoly R[n]}.

Lemma sym_antiE p q :
  p != 0 -> p \is antisym -> (q \is symmetric) = (p * q \is antisym).
Proof.
  case: (leqP n 1) => Hn.
    by rewrite !(sym_smalln Hn) !(antisym_smalln Hn) !unfold_in /=.
  move=> Hp H; apply (sameP idP); apply (iffP idP); last exact: (sym_anti H).
  move: H => /isantisymP Hsym /isantisymP Hpq.
  apply/issymP => s.
  have:= Hpq s; rewrite msymM Hsym => H.
  apply (mulfI Hp).
  move: H; case: (odd_perm s); rewrite !simplexp; last by [].
  by move=> /oppr_inj.
Qed.

Lemma sym_antisym_char2 :
  n >= 2 -> ~~ (2 \in [char R]) -> forall p, p \is symmetric -> p \is antisym -> p = 0.
Proof.
  rewrite (char_mpoly n R) => H1 Hchar p /= /issymP Hsym /isantisymP Hanti.
  have H0 : 0 < n by apply: (ltn_trans _ H1).
  pose s := (tperm (Ordinal H0) (Ordinal H1)).
  have := Hanti s; rewrite Hsym.
  rewrite odd_tperm /= => /eqP; rewrite !simplexp -addr_eq0.
  rewrite -mulr2n -mulr_natr mulf_eq0 => /orP [/eqP -> //|] /= /eqP H2.
  exfalso; rewrite {H1 p Hsym Hanti H0 s}.
  move: Hchar; rewrite negb_and /=.
  by rewrite H2 eq_refl.
Qed.

End MPolyIDomain.



Definition vandermonde n (R : ringType) : {mpoly R[n]} :=
  \prod_(p : 'I_n * 'I_n | p.1 < p.2) ('X_p.1 - 'X_p.2).

Implicit Arguments vandermonde [n R].

Definition eltrp n i (p : 'I_n.+1 * 'I_n.+1) := (eltr n i p.1, eltr n i p.2).

Definition predi n i (p : 'I_n.+1 * 'I_n.+1) :=
  (p.1 < p.2) && (p != (inord i, inord i.+1)).

Lemma predi_eltrp n i (p : 'I_n.+1 * 'I_n.+1) :
  i < n ->
  predi i p -> predi i (eltrp i p).
Proof.
  move=> Hi.
  have Hii1 : val (@inord n i.+1) = (@inord n i).+1.
    rewrite /= inordK; last by apply (leq_trans Hi).
    by rewrite /= inordK; last by apply (leq_trans Hi).
  move: p => [u v] /=; rewrite /predi /= /eltrp /eltr => /andP [] Hlt Hneq.
  case: (altP (inord i =P u)) => Hu.
    subst u; rewrite tpermL.
    case: (altP (v =P inord i.+1)) Hneq Hlt => Hu; first by subst v => /=; rewrite eq_refl.
    move=> _ Hlt.
    rewrite tpermD; first last.
      by rewrite eq_sym.
      by rewrite neq_ltn Hlt.
    apply/andP; split.
    - rewrite ltn_neqAle eq_sym Hu /=.
      by rewrite Hii1.
    - rewrite /eq_op /= eq_sym.
      apply/nandP; left.
      rewrite /eq_op /= Hii1.
      by rewrite ieqi1F.
  case: (altP (inord i.+1 =P u)) => Hu1.
    subst u; rewrite tpermR /=.
    rewrite tpermD; first last.
    - move: Hlt; by rewrite ltn_neqAle => /andP [].
    - move: Hlt; rewrite Hii1 => /ltnW.
      by rewrite ltn_neqAle => /andP [].
    apply/andP; split.
    - apply: (ltn_trans _ Hlt).
      by rewrite Hii1.
    - rewrite /eq_op /= eq_refl /= eq_sym.
      move: Hlt; by rewrite ltn_neqAle => /andP [].
  rewrite (tpermD Hu Hu1); apply/andP; split; first last.
    apply/nandP => /=; left; by rewrite eq_sym.
  case: (altP (inord i =P v)) => Hv.
    subst v; rewrite tpermL Hii1.
    by apply (leq_trans Hlt).
  case: (altP (inord i.+1 =P v)) => Hv1.
    subst v; rewrite tpermR.
    move: Hlt; by rewrite Hii1 ltnS ltn_neqAle eq_sym Hu /=.
  by rewrite tpermD.
Qed.

Lemma predi_eltrpE n i (p : 'I_n.+1 * 'I_n.+1) :
  i < n ->
  predi i p = predi i (eltr n i p.1, eltr n i p.2).
Proof.
  move=> Hi; apply/(sameP idP); apply(iffP idP); last by apply predi_eltrp.
  set p1 := ( _, _).
  suff -> : p = ((eltr n i) p1.1, (eltr n i) p1.2) by apply predi_eltrp.
  rewrite /p1 /= !tpermK {p1}.
  by case: p.
Qed.

Lemma anti_vandermonde n (R : comRingType) : @vandermonde n R \is antisym.
Proof.
  case: n => [| n].
    apply/isantisymP => s.
    have -> : s = 1%g by rewrite -permP => i; have := ltn_ord i.
    by rewrite msym1m odd_perm1 simplexp.
  apply/isantisym_eltrP => i Hi.
  rewrite /vandermonde.
  rewrite (bigD1 (inord i, inord i.+1)) /=; last by rewrite !inordK //=; apply (leq_trans Hi).
  rewrite msymM -mulNr; congr (_ * _).
    rewrite msymB opprB; congr (_ - _); rewrite /msym mmapX mmap1U /eltr.
    - by rewrite tpermL.
    - by rewrite tpermR.
  rewrite (big_morph _ (msymM (eltr n i)) (msym1 _ (eltr n i))) /=.
  rewrite (eq_bigl (fun p : 'I_n.+1 * 'I_n.+1 => predi i (eltrp i p)));
        first last.
    move=> [u v] /=; by rewrite -/(predi i (u,v)) (predi_eltrpE (u, v) Hi) /=.
  rewrite (eq_bigr (fun p => 'X_(eltrp i p).1 - 'X_(eltrp i p).2)); first last.
    move => [u v] /= _; by rewrite msymB /msym !mmapX !mmap1U.
  rewrite -(big_map (@eltrp n i) (predi i) (fun p => ('X_p.1 - 'X_p.2))) /=.
  rewrite /index_enum -enumT /=.
  set en := enum _.
  rewrite (eq_big_perm en) //=.
  have Hin : map (eltrp i) en =i en.
    move=> [u v].
    rewrite mem_enum inE.
    have -> : (u, v) = eltrp i (eltrp i (u, v)) by rewrite /eltrp /= !tpermK.
    apply map_f.
    by rewrite mem_enum inE.
  apply: (uniq_perm_eq _ _ Hin).
  - rewrite (perm_uniq Hin); first by apply enum_uniq.
    by rewrite size_map.
  - by apply enum_uniq.
Qed.

Lemma sym_vanderM n (R : comRingType) (p : {mpoly R[n]}) :
  p \is symmetric -> vandermonde * p \is antisym.
Proof. apply sym_anti; by apply anti_vandermonde. Qed.

Definition vander_fact n (R : comRingType) : {mpoly R[n.+1]} :=
  (\prod_(i < n.+1 | i < n) ('X_i - 'X_(ord_max))).


Lemma mwiden_inord n (R : ringType) (k : 'I_n) :
  'X_(inord k) = mwiden ('X_k : {mpoly R[n]}).
Proof.
  rewrite mwidenX; congr mpolyX.
  rewrite /mnmwiden /= /mnm1 mnmP => i.
  rewrite mnmE (mnm_nth 0) nth_rcons size_map size_enum_ord.
  case: (ssrnat.ltnP i n) => Hi.
  - rewrite (nth_map k); last by rewrite size_enum_ord.
    rewrite /eq_op /= nth_enum_ord //.
    by rewrite !(inordK (ltn_trans _ (ltnSn _))).
  - rewrite {1}/eq_op /=.
    have -> : i = n :> nat.
      apply anti_leq; rewrite Hi.
      by have:= ltn_ord i; rewrite ltnS => ->.
    rewrite eq_refl !(inordK (ltn_trans (ltn_ord k) (ltnSn _))).
    by rewrite (ltn_eqF (ltn_ord k)).
Qed.

Lemma vander_rec n (R : comRingType) :
  vandermonde = mwiden vandermonde * (vander_fact n R).
Proof.
  rewrite /vander_fact /vandermonde /=.
  rewrite (bigID (fun p : 'I_n.+1 * 'I_n.+1 => p.2 == ord_max)) /=.
  rewrite mulrC; congr (_ * _).
  - rewrite rmorph_prod.
    case: (altP (n =P 0%N)) => Hn.
      subst n; rewrite !big_pred0 //.
      * move=> [i j] /=; exfalso; by have := ltn_ord i.
      * move=> [[i Hi] [j Hj]] /=.
        move: Hi; rewrite !ltnS leqn0 => /eqP ->.
        have:= Hj; rewrite ltnS leqn0 => /eqP {1}->.
        by rewrite ltnn.
    rewrite (reindex (fun i : 'I_n * 'I_n => (inord i.1, inord i.2))) /=.
    + rewrite (eq_bigl (fun i : 'I_n * 'I_n => i.1 < i.2)); first last.
        move=> [[i Hi] [j Hj]] /=.
        rewrite !(inordK (ltn_trans _ (ltnSn _))) //.
        case: (i < j) => //=.
        apply/(introN idP) => /eqP H.
        have:= (erefl (val (@inord n j))).
        rewrite {2}H{H} /= !(inordK (ltn_trans _ (ltnSn _))) // => H.
        move: Hj; by rewrite H ltnn.
      apply (eq_bigr) => [[i j]] /= _.
      by rewrite mwidenB !mwiden_inord.
    move: Hn; rewrite -lt0n => Hn.
    pose Z := Ordinal Hn.
    pose F (i : 'I_n.+1) := nth Z (enum 'I_n) i.
    have FP (i : 'I_n.+1) : i < n -> inord (F i) = i.
      case: i => [i Hordi] Hi; apply val_inj => /=.
      by rewrite inordK /F /= nth_enum_ord.
    exists (fun i : 'I_n.+1 * 'I_n.+1 => (F i.1, F i.2)).
    + move=> [[i Hi] [j Hj]] /=; rewrite !inE /=; rewrite /F /=.
      rewrite !(inordK (ltn_trans _ (ltnSn _))) // => /andP [] Hij Hjn.
      apply/eqP; rewrite xpair_eqE; apply/andP.
      split; apply/eqP; apply val_inj; by rewrite /= nth_enum_ord.
    + move => [i j] /=; rewrite inE /= => /andP [] Hij Hjmax.
      have Hj : j < n.
        rewrite ltn_neqAle -ltnS (ltn_ord j) andbT.
        move: Hjmax; apply contra => /eqP Hj.
        apply/eqP; by apply val_inj.
      rewrite FP; last exact: ltn_trans Hij Hj.
      by rewrite FP.
  - rewrite (eq_bigr (fun i => 'X_i.1 - 'X_ord_max)); first last.
      by move=> [i j] /= /andP [] _ /eqP ->.
    rewrite (reindex (fun i : 'I_(n.+1) => (i, ord_max))) /=.
    + apply eq_bigl => i; by rewrite eq_refl andbT.
    + exists (fun i => i.1); first by [].
      by move=> [i j] /=; rewrite inE /= => /andP [] _ /eqP ->.
Qed.

Theorem sym_anti_iso2 (R : idomainType) (p : {mpoly R[2]}) :
  ~~ (2 \in [char R]) ->
  p \is antisym ->
  { q : {mpoly R[2]} | q \is symmetric & p = ('X_0 - 'X_1) * q }.
Proof.
  move=> Hchar /isantisymP Hp.
  have {Hp} := Hp (eltr 1 0)%N.
  rewrite odd_tperm.
  have -> : inord 0 != (inord 1 : 'I_2) by rewrite /eq_op /= !inordK.
  rewrite expr1 scaleN1r => Hp.
  have {Hp} Hp : p = - msym (eltr 1 0) p by rewrite Hp opprK.
  pose T := [tuple ('X_0 : {mpoly R[2]}); 'X_0].
  have:= erefl (p \mPo T).
  rewrite {2}Hp comp_mpolyN msym_mPo.
  set t := [tuple _ | i < 2]; have {t} -> : t = T.
    apply eq_from_tnth => i.
    rewrite !tnth_mktuple {t} /T.
    case: tpermP => // -> /=; by rewrite !(tnth_nth 'X_0) !inordK.
  move=> /eqP; rewrite -addr_eq0.
  rewrite -mulr2n -mulr_natr mulf_eq0.
  move: Hchar; rewrite (char_mpoly 2 R); rewrite inE /= => /negbTE ->.
  rewrite orbF /T {T} => /eqP.
  admit.
Qed.

Theorem sym_anti_iso n (R : comRingType) (q : {mpoly R[n]}) :
  q \is antisym ->
  { p : {mpoly R[n]} | p \is symmetric & q = vandermonde * p }.
Proof.
  elim: n q => [| n IHn] q /=.
    move=> _; exists q.
    - apply/issymP => s.
      have -> : s = 1%g by rewrite -permP => i; have := ltn_ord i.
      by rewrite msym1m.
    - rewrite /vandermonde.
      rewrite big_pred0; last by move=> [[u Hu] v].
      by rewrite mul1r.
   admit.
Qed.
