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

Lemma antisym_zmod : zmod_closed antisym.
Proof.
split=> [|p q /isantisymP sp /isantisymP sq]; apply/isantisymP=> s.
  by rewrite msym0 scaler0.
by rewrite msymB sp sq scalerBr.
Qed.

Canonical antisym_opprPred := OpprPred antisym_zmod.
Canonical antisym_addrPred := AddrPred antisym_zmod.
Canonical antisym_zmodPred := ZmodPred antisym_zmod.


Lemma antisym_submod_closed : submod_closed antisym.
Proof.
split=> [|c p q /isantisymP sp /isantisymP sq]; apply/isantisymP=> s.
  by rewrite msym0 scaler0.
rewrite msymD msymZ sp sq.
by rewrite scalerA commr_sign -scalerA scalerDr.
Qed.

Canonical antisym_submodPred := SubmodPred antisym_submod_closed.

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


