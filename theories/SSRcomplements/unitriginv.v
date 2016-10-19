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
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype finfun tuple bigop ssralg ssrint.
From mathcomp Require Import finset fingroup perm matrix.


Require Import tools ordtype sorted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section TriangularInv.

Variable R : comUnitRingType.
Variable T : finPOrdType.
Variable M : T -> T -> R.
Implicit Types t u v : T.

Hypothesis Muni : forall t, M t t = 1.
Hypothesis Mtrig : forall t u, M u t != 0 -> (t <= u)%Ord.

Local Notation n := #|{: T}|.
Definition Mat : 'M[R]_n := \matrix_(i, j < n) M (enum_val i) (enum_val j).

(* Triangular (for dominance order) matrix with 1 on the diagonal *)
Lemma det_unitrig : \det Mat = 1.
Proof.
rewrite /Mat /determinant (bigD1 1%g) //=.
rewrite !big1 ?mulr1 ?odd_perm1 ?expr0 ?addr0 //.
- move=> s Hs.
  have [i /eqP Hi] : exists i, M (enum_val i) (enum_val (s i)) == 0.
    apply/existsP; move: Hs; apply contraR.
    rewrite negb_exists => /forallP /= H.
    have {H} H : forall i : 'I_n, (enum_val (s i) <= enum_val i)%Ord.
      by move=> i; exact: Mtrig (H i).
    suff Hfix : forall t, s (enum_rank t) = enum_rank t.
      by apply/eqP/permP => /= i; rewrite perm1 -(enum_valK i); apply: Hfix.
    elim/finord_wf => t IHt.
    move/(_ (enum_rank t)) : H.
    rewrite leqX_eqVltnX => /orP [/eqP/(can_inj (@enum_valK _)) // |].
    by rewrite enum_rankK => /IHt; rewrite !enum_valK => /perm_inj.
  by rewrite (bigD1 i) //= mxE Hi mul0r mulr0.
- by move=> i _; rewrite mxE perm1 Muni.
Qed.

Definition Minv t u : R := invmx Mat (enum_rank t) (enum_rank u).

Lemma Minvl t u : \sum_(v : T) (Minv t v) * (M v u) = (u == t)%:R.
Proof.
rewrite (reindex _ (onW_bij _ (@enum_val_bij _))) /=.
transitivity (mulmx (invmx Mat) Mat (enum_rank t) (enum_rank u)).
  rewrite mxE; apply eq_bigr => /= i _.
  by rewrite /Minv mxE enum_rankK enum_valK.
rewrite mulVmx; last by rewrite unitmxE det_unitrig unitr1.
rewrite mxE; congr (nat_of_bool _)%:R.
by apply/eqP/eqP => [/(can_inj (@enum_rankK _))|] ->.
Qed.

Lemma Minvr t u : \sum_(v : T) (M t v) * (Minv v u) = (u == t)%:R.
Proof.
rewrite (reindex _ (onW_bij _ (@enum_val_bij _))) /=.
transitivity (mulmx Mat (invmx Mat) (enum_rank t) (enum_rank u)).
  rewrite mxE; apply eq_bigr => /= i _.
  by rewrite /Minv mxE enum_valK enum_rankK.
rewrite mulmxV; last by rewrite unitmxE det_unitrig unitr1.
rewrite mxE; congr (nat_of_bool _)%:R.
by apply/eqP/eqP => [/(can_inj (@enum_rankK _))|] ->.
Qed.

Lemma Minv_trig t u : Minv u t != 0 -> (t <= u)%Ord.
Proof.
apply contraR => H; apply/eqP; elim/finord_wf: u H => /= u IHu Hu.
have:= Minvr u t.
rewrite [X in  _ = (nat_of_bool X)%:R](_ : _ = false) /=; first last.
  by apply negbTE; move: Hu; apply contra => /eqP ->.
rewrite (bigID (fun v => v <= u)%Ord) /= [X in _ + X]big1 ?addr0; first last.
  by move=> v /(contraR (@Mtrig _ _)) /eqP ->; rewrite mul0r.
rewrite (bigD1 u) //= Muni mul1r big1 ?addr0 // => i /andP [Hneq Hlt].
rewrite IHu ?mulr0 //.
- (*Work around finOrdType double inheritance bug *)
  rewrite ltnX_neqAleqX Hneq andbT.
  by move: Hlt; apply contra => /eqP ->.
- by move: Hu; apply contra => /leqX_trans; apply.
Qed.

Lemma Minv_uni t : Minv t t = 1.
Proof.
have:= Minvr t t; rewrite eq_refl /= -[1%:R]/1 => <-.
rewrite (bigID (fun v => v <= t)%Ord) /= [X in _ + X]big1 ?addr0; first last.
  by move=> v /(contraR (@Mtrig _ _))/eqP ->; rewrite mul0r.
rewrite (bigID (fun v => t <= v)%Ord) /= [X in _ + X]big1 ?addr0; first last.
  by move=> v /andP [_ /(contraR (@Minv_trig _ _))/eqP ->]; rewrite mulr0.
rewrite (big_pred1 t) ?Muni ?mul1r // => v /=.
by rewrite -eqn_leqX; apply/eqP/eqP. (* finOrdType bug *)
Qed.

End TriangularInv.
