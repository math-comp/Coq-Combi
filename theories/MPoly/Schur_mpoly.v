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
From mathcomp Require Import tuple finfun finset bigop ssralg path perm fingroup.
From SsrMultinomials Require Import ssrcomplements freeg bigenough mpoly.

Require Import tools ordtype permuted partition Yamanouchi std tableau stdtab antisym.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Section Schur.

Variable n0 : nat.
Local Notation n := n0.+1.
Variable R : ringType.

Definition Schur d (sh : 'P_d) : {mpoly R[n]} :=
  \sum_(t : tabsh n0 sh) \prod_(v <- to_word t) 'X_v.

Lemma Schur_tabsh_readingE  d (sh : 'P_d) :
  Schur sh =
  \sum_(t : d.-tuple 'I_n | tabsh_reading sh t) \prod_(v <- t) 'X_v.
Proof using.
rewrite /Schur /index_enum -!enumT.
pose prodw := fun w => \prod_(v <- w) 'X_v : {mpoly R[n]}.
rewrite -[LHS](big_map (fun t => to_word (val t)) xpredT prodw).
rewrite -[RHS](big_map val (tabsh_reading sh) prodw).
rewrite -[RHS]big_filter.
by rewrite (eq_big_perm _ (to_word_enum_tabsh _ sh)).
Qed.

Lemma Schur0 (sh : 'P_0) : Schur sh = 1.
Proof using.
rewrite Schur_tabsh_readingE (eq_bigl (xpred1 [tuple])); first last.
  by move=> i /=; rewrite tuple0 [RHS]eq_refl intpartn0.
by rewrite big_pred1_eq big_nil.
Qed.

Lemma Schur_oversize d (sh : 'P_d) : (size sh > n)%N -> Schur sh = 0.
Proof using.
move=> Hn; apply big1 => t _; exfalso.
have:= size_tabsh t; rewrite -(size_map size) -/(shape t) shape_tabsh.
by move=> /(leq_trans Hn); rewrite ltnn.
Qed.

Lemma tabwordshape_row d (w : d.-tuple 'I_n) :
  tabsh_reading (rowpartn d) w = sorted leq [seq val i | i <- w].
Proof using.
rewrite /tabsh_reading /= /rowpart ; case: w => w /=/eqP Hw.
case: d Hw => [//= | d] Hw; rewrite Hw /=; first by case: w Hw.
rewrite addn0 eq_refl andbT //=.
case: w Hw => [//= | w0 w] /= /eqP; rewrite eqSS => /eqP <-.
rewrite take_size; apply esym; apply (map_path (b := pred0)) => /=.
- move=> i j /= _ ; exact: leqXnatE.
- by apply/hasPn => x /=.
Qed.


Lemma perm_eq_enum_basis d :
  perm_eq [seq s2m (val s) | s <- enum (basis n d)]
          [seq val m | m <- enum [set m : 'X_{1..n < d.+1} | mdeg m == d]].
Proof using.
apply uniq_perm_eq.
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

(** Equivalent definition of symh symmetric function *)
Lemma symh_basisE d :
  \sum_(s in (basis n d)) 'X_[s2m s] = Schur (rowpartn d).
Proof using.
rewrite Schur_tabsh_readingE (eq_bigl _ _ (@tabwordshape_row d)).
rewrite [RHS](eq_bigr (fun s : d.-tuple 'I_n => 'X_[s2m s])); first last.
  move=> [s _] /= _; rewrite /s2m; elim: s => [| s0 s IHs]/=.
    by rewrite big_nil -/mnm0 mpolyX0.
  rewrite big_cons {}IHs -mpolyXD; congr ('X_[_]).
  by rewrite mnmP => i; rewrite mnmDE !mnmE.
by apply eq_bigl => m; rewrite inE /=.
Qed.

End Schur.


Section SchurComRingType.

Variable n0 : nat.
Local Notation n := (n0.+1).
Variable R : comRingType.

Lemma Schur_rowpartn d :
  \sum_(m : 'X_{1..n < d.+1} | mdeg m == d) 'X_[m] = Schur n0 R (rowpartn d).
Proof using.
rewrite /= -symh_basisE.
rewrite -(big_map (@bmnm n d.+1) (fun m => mdeg m == d) (fun m => 'X_[m])).
rewrite /index_enum -enumT -big_filter.
rewrite [filter _ _](_ : _ =
    [seq val m | m <- enum [set m : 'X_{1..n < d.+1} | mdeg m == d]]);
    first last.
  rewrite /enum_mem filter_map -filter_predI; congr map.
  by apply eq_filter => s /=; rewrite !inE andbT.
rewrite -(eq_big_perm _ (perm_eq_enum_basis _ d)) /=.
by rewrite big_map -[RHS]big_filter.
Qed.

Lemma tabwordshape_col d (w : d.-tuple 'I_n) :
  tabsh_reading (colpartn d) w = sorted gtnX w.
Proof using.
rewrite /tabsh_reading /= /colpart ; case: w => w /=/eqP Hw.
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

(** The definition of column Schur symmetric polynomials agrees with mesym
    from mpoly *)

Lemma mesym_SchurE d :
  mesym n R d = Schur n0 R (colpartn d).
Proof using.
rewrite /= mesym_tupleE /tmono Schur_tabsh_readingE.
rewrite (eq_bigl _ _ (@tabwordshape_col d)).
set f := BIG_F.
rewrite (eq_bigr (fun x => f (rev_tuple x))) /f {f}; first last.
  by move => i _ /=; apply: eq_big_perm; exact: perm_eq_rev.
rewrite (eq_bigl (fun i => sorted gtnX (rev_tuple i))); first last.
  move=> [t /= _]; rewrite rev_sorted.
  case: t => [//= | t0 t] /=.
  apply: (map_path (b := pred0)) => [x y /= _|].
  + by rewrite -ltnXnatE.
  + by apply/hasPn => x /=.
rewrite [RHS](eq_big_perm
                (map (@rev_tuple _ _) (enum {:d.-tuple 'I_n}))) /=.
  by rewrite big_map /=; first by rewrite /index_enum /= enumT.
apply uniq_perm_eq.
- rewrite /index_enum -enumT; exact: enum_uniq.
- rewrite map_inj_uniq; first exact: enum_uniq.
  apply (can_inj (g := (@rev_tuple _ _))).
  by move=> t; apply val_inj => /=; rewrite revK.
- rewrite /index_enum -enumT /= => t.
  rewrite mem_enum /= inE; apply esym; apply/mapP.
  exists (rev_tuple t) => /=.
  + by rewrite mem_enum.
  + by apply val_inj; rewrite /= revK.
Qed.

Lemma Schur1 (sh : 'P_1) : Schur n0 R sh = \sum_(i < n) 'X_i.
Proof using.
suff -> : sh = colpartn 1 by rewrite -mesym_SchurE mesym1E.
by apply val_inj => /=; exact: intpartn1.
Qed.

End SchurComRingType.
