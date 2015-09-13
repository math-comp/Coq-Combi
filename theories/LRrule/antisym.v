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
Require Import fingroup perm zmodp binomial poly ssrcomplements poset freeg.

Require Import Sn.
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


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory BigEnough.

Local Open Scope ring_scope.


Section MPoly.
  Variable n : nat.
  Variable R : ringType.

  Implicit Types p q r : {mpoly R[n]}.

  Lemma msym_act1 p : msym 1 p = p.
  Proof.
    rewrite -mpolyP => m.
    rewrite !mcoeff_sym; congr mcoeff.
    rewrite mnmP => i.
    by rewrite !multinomE tnth_mktuple /= perm1.
  Qed.

  Lemma msym_actM s t p : msym (s * t)%g p = msym t (msym s p).
  Proof.
    rewrite -mpolyP => m.
    rewrite !mcoeff_sym; congr mcoeff.
    rewrite mnmP => i.
    by rewrite !multinomE !tnth_mktuple multinomE tnth_mktuple permM  /=.
  Qed.

End MPoly.

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
        by rewrite !big_nil /= msym_act1.
      move=> /andP [] _ /IHts{IHts}/eqP Hrec.
      by rewrite !big_cons msym_actM Htperm Hrec.
  Qed.

  Definition antisymmetric : qualifier 0 {mpoly R[n]} :=
    [qualify p | [forall s, msym s p == if odd_perm s then - p else p]].

  Lemma isantisymP p :
    reflect (forall s, msym s p = if odd_perm s then - p else p) (p \is antisymmetric).
  Proof.
    apply (iffP idP).
    - move=> /forallP Hanti s.
      by rewrite (eqP (Hanti s )).
    - move=> H; apply/forallP => s.
      by rewrite H.
  Qed.

  Lemma isantisym_tpermP p :
    reflect (forall i j, msym (tperm i j) p = if (i != j) then - p else p)
            (p \is antisymmetric).
  Proof.
    apply (iffP idP).
    - move=> /forallP Hanti i j.
      by rewrite (eqP (Hanti (tperm _ _))) odd_tperm.
    - move=> Htperm; apply/forallP => s.
      case: (prod_tpermP s) => ts -> {s} Hall.
      elim: ts Hall => [_ | t0 ts IHts] /=.
        by rewrite !big_nil odd_perm1 /= msym_act1.
      move=> /andP [] H0 /IHts{IHts}/eqP Hrec.
      rewrite !big_cons msym_actM Htperm H0 msymN Hrec.
      rewrite odd_mul_tperm H0 /=.
      case: (odd_perm _) => //=.
      by rewrite opprK.
  Qed.

  Lemma sym_anti p q :
    p \is antisymmetric -> q \is symmetric -> p * q \is antisymmetric.
  Proof.
    move=> /isantisymP Hsym /issymP Hanti.
    apply/isantisymP => s.
    rewrite msymM Hsym Hanti.
    case: (odd_perm s) => //=.
    by rewrite mulNr.
  Qed.

  Lemma anti_anti p q :
    p \is antisymmetric -> q \is antisymmetric -> p * q \is symmetric.
  Proof.
    move=> /isantisymP Hp /isantisymP Hq.
    apply/issymP => s.
    rewrite msymM Hp Hq.
    case: (odd_perm s) => //=.
    by rewrite mulrN mulNr opprK.
  Qed.

End MPolySym.

Implicit Arguments antisymmetric [n R].

Lemma issym_eltrP n (R : ringType) (p : {mpoly R[n.+1]}) :
  reflect (forall i, i < n -> msym (eltr n i) p = p) (p \is symmetric).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti i Hi.
    by have /eqP -> := Hanti (eltr n i).
  - move=> Heltr; apply/forallP; elim/eltr_ind => [| S i Hi /eqP IH].
    + by rewrite msym_act1.
    + by rewrite msym_actM (Heltr i Hi) IH.
Qed.

Lemma isantisym_eltrP n (R : ringType) (p : {mpoly R[n.+1]}) :
  reflect (forall i, i < n -> msym (eltr n i) p = - p) (p \is antisymmetric).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti i Hi.
    have /eqP -> := Hanti (eltr n i).
    by rewrite /eltr odd_tperm (inordi1 Hi).
  - move=> Heltr; apply/forallP; elim/eltr_ind => [| S i Hi /eqP IH].
    + by rewrite odd_perm1 /= msym_act1.
    + rewrite msym_actM (Heltr i Hi).
      rewrite msymN IH odd_mul_tperm (inordi1 Hi) addTb if_neg /=.
      case: (odd_perm S) => //=.
    by rewrite opprK.
Qed.

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

Lemma anti_vandermonde n (R : comRingType) : @vandermonde n R \is antisymmetric.
Proof.
  case: n => [| n].
    apply/isantisymP => s.
    have -> : s = 1%g by rewrite -permP => i; have := ltn_ord i.
    by rewrite msym_act1 odd_perm1.
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
  p \is symmetric -> vandermonde * p \is antisymmetric.
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
  q \is antisymmetric ->
  { p : {mpoly R[n]} | p \is symmetric & q = vandermonde * p }.
Proof.
  elim: n q => [| n IHn] q /=.
    move=> _; exists q.
    - apply/issymP => s.
      have -> : s = 1%g by rewrite -permP => i; have := ltn_ord i.
      by rewrite msym_act1.
    - rewrite /vandermonde.
      rewrite big_pred0; last by move=> [[u Hu] v].
      by rewrite mul1r.
   admit.
Qed.
