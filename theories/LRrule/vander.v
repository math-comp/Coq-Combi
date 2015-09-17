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
Require Import fingroup perm zmodp binomial poly ssrcomplements poset freeg matrix.

Require Import sym_group.
(*
Require Import tools ordcast combclass partition schensted ordtype std stdtab invseq congr plactic greeninv yamplact skewtab.
Require Import shuffle multpoly Sn.
*)

Require Import bigenough mpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory BigEnough.

Local Open Scope ring_scope.

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
Variable R : comRingType.

Implicit Types p q r : {mpoly R[n]}.

Definition antisym : qualifier 0 {mpoly R[n]} :=
  [qualify p | [forall s, msym s p == if odd_perm s then - p else p]].

Fact antisym_key : pred_key antisym. Proof. by []. Qed.
Canonical antisym_keyed := KeyedQualifier antisym_key.

Lemma isantisymP p :
  reflect (forall s, msym s p = if odd_perm s then - p else p) (p \is antisym).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti s.
    by rewrite (eqP (Hanti s )).
  - move=> H; apply/forallP => s.
    by rewrite H.
Qed.

Lemma antisym_char2 : (2 \in [char R]) -> symmetric =i antisym.
Proof.
  move=> Hchar p /=.
  apply (sameP idP); apply (iffP idP).
  - move=> /isantisymP H; apply/issymP => s.
    rewrite H oppr_char2; first by case: (odd_perm s).
    by apply: (rmorph_char (mpolyC_rmorphism _ _)).
  - move => /issymP H; apply/isantisymP => s.
    rewrite H oppr_char2; first by case: (odd_perm s).
    by apply: (rmorph_char (mpolyC_rmorphism _ _)).
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
  by rewrite (perm_smalln Hn s) odd_perm1 msym1m.
Qed.

Lemma isantisym_tpermP p :
  reflect (forall i j, msym (tperm i j) p = if (i != j) then - p else p)
          (p \is antisym).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti i j.
    by rewrite (eqP (Hanti (tperm _ _))) odd_tperm.
  - move=> Htperm; apply/forallP => s.
    case: (prod_tpermP s) => ts -> {s} Hall.
    elim: ts Hall => [_ | t0 ts IHts] /=.
      by rewrite !big_nil odd_perm1 /= msym1m.
    move=> /andP [] H0 /IHts{IHts}/eqP Hrec.
    rewrite !big_cons msymMm Htperm H0 msymN Hrec.
    rewrite odd_mul_tperm H0 /=.
    case: (odd_perm _) => //=.
    by rewrite opprK.
Qed.

Lemma sym_anti p q :
  p \is antisym -> q \is symmetric -> p * q \is antisym.
Proof.
  move=> /isantisymP Hsym /issymP Hpq.
  apply/isantisymP => s.
  rewrite msymM Hsym Hpq.
  case: (odd_perm s) => //=.
  by rewrite mulNr.
Qed.

Lemma anti_anti p q :
  p \is antisym -> q \is antisym -> p * q \is symmetric.
Proof.
  move=> /isantisymP Hp /isantisymP Hq.
  apply/issymP => s.
  rewrite msymM Hp Hq.
  case: (odd_perm s) => //=.
  by rewrite mulrN mulNr opprK.
Qed.

End MPolySym.

Implicit Arguments antisym [n R].


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
  move: H; case: (odd_perm s); last by [].
  by rewrite mulNr => /oppr_inj.
Qed.

Lemma sym_antisym_char2 :
  n >= 2 -> ~~ (2 \in [char R]) -> forall p, p \is symmetric -> p \is antisym -> p = 0.
Proof.
  rewrite (char_mpoly n R) => H1 Hchar p /= /issymP Hsym /isantisymP Hanti.
  have H0 : 0 < n by apply: (ltn_trans _ H1).
  pose s := (tperm (Ordinal H0) (Ordinal H1)).
  have := Hanti s; rewrite Hsym.
  rewrite odd_tperm /= => /eqP; rewrite -addr_eq0.
  rewrite -mulr2n -mulr_natr mulf_eq0 => /orP [/eqP -> //|] /= /eqP H2.
  exfalso; rewrite {H1 p Hsym Hanti H0 s}.
  move: Hchar; rewrite negb_and /=.
  by rewrite H2 eq_refl.
Qed.

End MPolyIDomain.

Lemma isantisym_eltrP n (R : comRingType) (p : {mpoly R[n.+1]}) :
  reflect (forall i, i < n -> msym (eltr n i) p = - p) (p \is antisym).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti i Hi.
    have /eqP -> := Hanti (eltr n i).
    by rewrite /eltr odd_tperm (inordi1 Hi).
  - move=> Heltr; apply/forallP; elim/eltr_ind => [| S i Hi /eqP IH].
    + by rewrite odd_perm1 /= msym1m.
    + rewrite msymMm (Heltr i Hi).
      rewrite msymN IH odd_mul_tperm (inordi1 Hi) addTb if_neg /=.
      case: (odd_perm S) => //=.
    by rewrite opprK.
Qed.

Section VandermondeDet.

Variable n : nat.
Variable R : comRingType.

Definition antim (s : seq nat) : 'M[ {mpoly R[n]} ]_n :=
  \matrix_(i, j < n) 'X_i ^+ (nth 0 s j + n - j)%N.
Definition Vandmx : 'M[ {mpoly R[n]} ]_n := \matrix_(i, j < n) 'X_i ^+ (n - j).
Definition Vandet := \det Vandmx.

Lemma Vandmx_antimE : Vandmx = antim [::].
Proof. rewrite /Vandmx /antim -matrixP => i j /=; by rewrite !mxE nth_default. Qed.

Lemma tperm_antim_xrow s i j :
  i != j -> msym (tperm i j) (\det (antim s)) = \det (xrow i j (antim s)).
Proof.
  rewrite /antim => Hij.
  rewrite -det_map_mx /=; congr (\det _).
  rewrite /map_mx -matrixP => r c /=.
  rewrite !mxE rmorphX /= msymX /=.
  congr (mpolyX _ _ ^+ _) => {c}.
  rewrite mnmP => u /=; rewrite !mnm_tnth /=.
  rewrite !tnth_map /= tnth_ord_tuple /= mnm1E tpermV.
  congr (nat_of_bool _); apply (sameP idP); apply (iffP idP).
  - by move/eqP <-; rewrite tpermK.
  - by move/eqP ->; rewrite tpermK.
Qed.

Lemma tperm_antim s i j : i != j -> msym (tperm i j) (\det (antim s)) = - (\det (antim s)).
Proof.
  move=> Hij; rewrite (tperm_antim_xrow _ Hij).
  rewrite xrowE det_mulmx det_perm.
  by rewrite odd_tperm Hij /= expr1 mulN1r.
Qed.

Lemma antimP s : \det (antim s) \is antisym.
Proof.
  apply/isantisym_tpermP => i j.
  case: (altP (i =P j)) => [-> |] /=; first by rewrite tperm1 msym1m.
  exact: tperm_antim.
Qed.

Corollary Vander_anti : Vandet \is antisym.
Proof. rewrite /Vandet Vandmx_antimE. exact: antimP. Qed.

End VandermondeDet.








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
    by rewrite msym1m odd_perm1.
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

Definition vander_fact n (R : comRingType) : {ipoly R[n.+1]}
  := (\prod_(i < n) ('X - (minject 'X_i)%:P)).

Lemma vander_rec n (R : comRingType) :
  minject (@vandermonde n.+1 R) =
  minject (@vandermonde n R) *: (vander_fact n R).
Proof.
  rewrite /vander_fact /minject /vandermonde /=.
  rewrite (bigID (fun p : 'I_n.+1 * 'I_n.+1 => p.2 == inord n)) /=.
  set Peq := (\prod_(i : 'I_n.+1 * 'I_n.+1 | (i.1 < i.2) && (i.2 == inord n))
              ('X_i.1 - 'X_i.2)).
  set Pneq := (\prod_(i : 'I_n.+1 * 'I_n.+1 | (i.1 < i.2) && (i.2 != inord n))
              ('X_i.1 - 'X_i.2)).
  have := erefl (mpoly_mul Peq Pneq).
    rewrite {1}/mpoly_mul /=.
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
