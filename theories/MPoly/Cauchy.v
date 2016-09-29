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
From mathcomp Require Import vector.

From SsrMultinomials Require Import ssrcomplements poset freeg bigenough mpoly.

Require Import tools ordtype permuted partition Yamanouchi std tableau stdtab.
Require Import antisym sympoly Schur_basis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section CauchyKernel.

Variables (m0 n0 : nat).
Notation m := m0.+1.
Notation n := n0.+1.

Lemma card_pair : #|{: 'I_m * 'I_n}| = (m * n)%N.
Proof. by rewrite card_prod !card_ord. Qed.

Definition ctopair (i : 'I_(m*n)) : 'I_m * 'I_n :=
  enum_val (cast_ord (esym card_pair) i).
Definition pairtoc (p : 'I_m * 'I_n) : 'I_(m * n) :=
  cast_ord card_pair (enum_rank p).

Lemma ctopairK : cancel ctopair pairtoc.
Proof. by move=> i; rewrite /ctopair/pairtoc enum_valK cast_ordKV. Qed.
Lemma pairtocK : cancel pairtoc ctopair.
Proof. by move=> p; rewrite /ctopair/pairtoc cast_ordK enum_rankK. Qed.
Lemma pairtoc_inj : injective pairtoc.
Proof. exact: can_inj pairtocK. Qed.
Lemma ctopair_inj : injective ctopair.
Proof. exact: can_inj ctopairK. Qed.
Lemma pairtoc_bij : bijective pairtoc.
Proof. by exists ctopair; [exact: pairtocK | exact: ctopairK]. Qed.
Lemma ctopair_bij : bijective ctopair.
Proof. by exists pairtoc; [exact: ctopairK |  exact: pairtocK]. Qed.

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
Lemma polX_XY_is_lrmorphism : rmorphism polX_XY.
Definition polY_XY : polY -> polXY := mpolyC m (R := [ringType of mpoly n R]).
Notation "p '(Y)'" := (polY_XY p) (at level 20, format "p '(Y)'").
Notation "p '(X)'" := (polX_XY p) (at level 20, format "p '(X)'").
Lemma polyXY_scale p q : p(X) * q(Y) = q *: p(X).
Proof. by rewrite mulrC mul_mpolyC. Qed.

Definition evalXY : polZ -> polXY :=
  mmap ((@mpolyC m _) \o (@mpolyC n R))
       (fun i => 'X_((ctopair i).1) (X) * 'X_((ctopair i).2) (Y)).
Notation "p '(XY)'" := (evalXY p) (at level 20, format "p '(XY)'").

Lemma sympXY k : 'p_k(XY) = 'p_k(X) * 'p_k(Y).
Proof.
rewrite /= /symp_pol /= /evalXY /= !rmorph_sum /=.
rewrite (reindex pairtoc) /=; last exact: onW_bij pairtoc_bij.
pose XY := fun i j => 'X_i(X) ^+ k * 'X_j(Y) ^+ k.
rewrite [LHS](eq_bigr (fun p => XY p.1 p.2)); first last.
  by move=> [i j] _; rewrite rmorphX /= mmapX mmap1U pairtocK /= exprMn.
rewrite -[LHS](pair_big predT predT XY) /=.
rewrite [_(X)]rmorph_sum mulr_suml; apply eq_bigr => i _ /=.
rewrite [_(Y)]rmorph_sum mulr_sumr; apply eq_bigr => j _ /=.
by rewrite !rmorphX /=.
Qed.

Lemma prod_sympXY d (la : intpartn d) : 'p[la] (XY) = 'p[la] (X) * 'p[la] (Y).
Proof.
rewrite /prod_symp /prod_gen /= !rmorph_prod /= [LHS]rmorph_prod /=.
rewrite [_(X)]rmorph_prod [_(Y)]rmorph_prod /=.
rewrite -big_split /=; apply eq_bigr => i _.
by rewrite [LHS]sympXY.
Qed.

End CauchyKernel.
