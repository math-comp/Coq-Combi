(** * Combi.MPoly.Schur_mpoly : Schur symmetric polynomials *)
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
(** * Combinatorial definition of Schur symmetric polynomials

- [Schur n0 R la] == The Schur polynomial associated to the partition [la] in
                     [{mpoly R[n0.+1]}] as the sum of all tableau of shape
                     [la] over the alphabet ['I_n0.+1].

We give some values for particular partition such as small one, rows and columns.
***********)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun finset bigop ssralg order path.
From SsrMultinomials Require Import ssrcomplements freeg mpoly.

Require Import tools ordtype partition tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.
Local Open Scope ring_scope.
Import GRing.Theory.

Section Schur.

Variable n0 : nat.
Local Notation n := n0.+1.
Variable R : ringType.

Lemma mons2mE s : 'X_[s2m s] = \prod_(i <- s) 'X_i :> {mpoly R[n]}.
Proof.
rewrite /s2m; elim: s => [| s0 s IHs]/=.
  by rewrite big_nil -/mnm0 mpolyX0.
rewrite big_cons -{}IHs -mpolyXD; congr ('X_[_]).
by rewrite mnmP => i; rewrite mnmDE !mnmE.
Qed.


Definition Schur d (sh : 'P_d) : {mpoly R[n]} :=
  \sum_(t : tabsh sh) \prod_(i <- to_word t) 'X_i.

Lemma Schur_tabsh_readingE  d (sh : 'P_d) :
  Schur sh =
  \sum_(t : d.-tuple 'I_n | tabsh_reading sh t) \prod_(i <- t) 'X_i.
Proof using.
rewrite /Schur -big_enum /=.
pose prodw := fun w => \prod_(i <- w) 'X_i : {mpoly R[n]}.
rewrite -[LHS](big_map (fun t => to_word (val t)) xpredT prodw).
rewrite -[RHS](big_map val (tabsh_reading sh) prodw).
rewrite -[RHS]big_filter.
rewrite (perm_big _ (to_word_enum_tabsh sh)) /=.
by rewrite !big_filter !big_map.
Qed.

(** ** Some particular Schur functions *)

Lemma Schur0 (sh : 'P_0) : Schur sh = 1.
Proof using.
rewrite Schur_tabsh_readingE (eq_bigl (xpred1 [tuple])); first last.
  by move=> i /=; rewrite tuple0 [RHS]eq_refl val_intpartn0.
by rewrite big_pred1_eq big_nil.
Qed.

Lemma Schur_oversize d (sh : 'P_d) : (size sh > n)%N -> Schur sh = 0.
Proof using.
move=> Hn; apply big1 => t _; exfalso.
have:= size_tabsh t; rewrite -(size_map size) -/(shape t) shape_tabsh.
by move=> /(leq_trans Hn); rewrite ltnn.
Qed.

(** Equivalent definition of symh symmetric function *)

Lemma tabwordshape_row d (w : d.-tuple 'I_n) :
  tabsh_reading (rowpartn d) w = sorted leq [seq val i | i <- w].
Proof using.
rewrite /tabsh_reading /= rowpartnE ; case: w => w /=/eqP Hw.
case: d Hw => [//= | d] Hw; rewrite Hw /=; first by case: w Hw.
rewrite addn0 eq_refl andbT //=.
case: w Hw => [//= | w0 w] /= /eqP; rewrite eqSS => /eqP <-.
rewrite take_size; apply esym; apply (map_path (b := pred0)) => //.
by apply/hasPn => x /=.
Qed.

Lemma symh_basisE d :
  \sum_(s in basis n d) 'X_[s2m s] = Schur (rowpartn d).
Proof using.
rewrite Schur_tabsh_readingE (eq_bigl _ _ (@tabwordshape_row d)).
under [LHS]eq_bigr do rewrite mons2mE.
by apply eq_bigl => m; rewrite inE.
Qed.

End Schur.


Section SchurComRingType.

Variable n0 : nat.
Local Notation n := (n0.+1).
Variable R : comRingType.


Lemma perm_enum_basis d :
  perm_eq [seq s2m (tval s) | s in basis n d]
          [seq val m | m in [set m : 'X_{1..n < d.+1} | mdeg m == d]].
Proof using.
apply uniq_perm.
- rewrite map_inj_in_uniq; first exact: enum_uniq.
  move=> i j; rewrite !mem_enum => Hi Hj; exact: inj_s2m.
- rewrite map_inj_uniq; [exact: enum_uniq | exact: val_inj].
move=> m; apply/mapP/mapP => [[] s | [] mb].
- rewrite mem_enum inE /= => Hsort ->.
  have mdegs : mdeg (s2m s) = d.
    rewrite /s2m /mdeg mnm_valK /= big_map enumT -/(index_enum _).
    by rewrite combclass.sum_count_mem count_predT size_tuple.
  have mdegsP : (mdeg (s2m s) < d.+1)%N by rewrite mdegs.
  exists (BMultinom mdegsP) => //.
  by rewrite mem_enum inE /= mdegs.
- rewrite mem_enum inE => /eqP Hmb ->.
  have Ht : size (m2s mb) == d by rewrite -{2}Hmb size_m2s.
  exists (Tuple Ht) => /=; last by rewrite s2mK.
  rewrite mem_enum inE /=; exact: srt_m2s.
Qed.

Lemma Schur_rowpartn d :
  \sum_(m : 'X_{1..n < d.+1} | mdeg m == d) 'X_[m] = Schur n0 R (rowpartn d).
Proof using.
rewrite -symh_basisE.
transitivity
  (\sum_(m <- [seq s2m (tval s) | s in basis n d]) 'X_[m] : {mpoly R[n]});
    last by rewrite big_map big_enum.
rewrite (perm_big _ (perm_enum_basis d)) big_map big_enum /=.
by apply eq_bigl => m; rewrite inE.
Qed.


(** The definition of column Schur symmetric polynomials agrees with mesym
    from mpoly *)

Lemma tabwordshape_col d (w : d.-tuple 'I_n) :
  tabsh_reading (colpartn d) w = sorted >%O w.
Proof using.
rewrite /tabsh_reading /= colpartnE ; case: w => w /=/eqP Hw.
have -> : sumn (nseq d 1%N) = d.
  by elim: d {Hw} => //= d /= ->; rewrite add1n.
rewrite Hw eq_refl /= rev_nseq.
have -> : rev (reshape (nseq d 1%N) w) = [seq [:: i] | i <- rev w].
  rewrite map_rev; congr rev.
  elim: d w Hw => [| d IHd] //=; first by case.
  case => [| w0 w] //= /eqP; rewrite eqSS => /eqP /IHd <-.
  by rewrite take0 drop0.
rewrite -rev_sorted.
case: {w} (rev w) {d Hw} => [|w0 w] //=.
elim: w w0 => [//= | w1 w /= <-] w0 /=.
by congr andb; rewrite /dominate /= andbT {w}.
Qed.

Lemma mesym_SchurE d :
  mesym n R d = Schur n0 R (colpartn d).
Proof using.
rewrite /= mesym_tupleE /tmono Schur_tabsh_readingE.
rewrite (eq_bigl _ _ (@tabwordshape_col d)).
under [LHS]eq_bigr => i do have /permPl/(perm_big _) <- /= := perm_rev i.
rewrite (eq_bigl (fun i => sorted >%O (rev_tuple i))); first last.
  move=> [t /= _]; rewrite rev_sorted sorted_map.
  exact: sorted.eq_sorted.
by apply/esym/reindex/onW_bij/inv_bij => x; apply val_inj; rewrite /= revK.
Qed.

Lemma Schur1 (sh : 'P_1) : Schur n0 R sh = \sum_(i < n) 'X_i.
Proof using.
suff -> : sh = colpartn 1 by rewrite -mesym_SchurE mesym1E.
by rewrite !intpartn1.
Qed.

End SchurComRingType.
