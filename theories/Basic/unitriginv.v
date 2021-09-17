(** * Combi.Basic.unitriginv : Uni-triangular Matrices *)
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
(** * Triangular matrix with 1 on the diagonal

We deal with "matrices" which are triangular for a _possibly partial_ order
with 1 on the diagonal. The goal is to show that such a matrix is invertible
on any ring and to give formulas for the inverse. The matrices are given as a
function [M : T -> T -> R] for a finite partially ordered type [T] and a
commutative unit ring [R].

- [unitrig M] == [M] is unitriangular where [M].
- [Mat M] == transform [M] to a usual mathcomp square matrix of order [#|T|]
- [Minv M] == the inverse of the matrix [M].

We show that such a matrix has determinant 1 (Lemma [det_unitrig]) and is
therefore invertible. Moreover Lemma [Minv_unitrig] says that the inverse
is unitriangular too.
 *******)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat order.
From mathcomp Require Import fintype bigop ssralg.
From mathcomp Require Import finset fingroup perm matrix.

Require ordtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.
Import GRing.Theory.
Local Open Scope ring_scope.

Section UniTriangular.

Variable R : comUnitRingType.
Variable disp : unit.
Variable T : finPOrderType disp.
Implicit Type M : T -> T -> R.
Implicit Types t u v : T.

Definition unitrig M :=
  [forall t, M t t == 1] && [forall t, [forall (u | M u t != 0), (t <= u)%O]].
Lemma unitrigP M :
  reflect ((forall t, M t t = 1) /\ (forall t u, M u t != 0 -> (t <= u)%O))
          (unitrig M).
Proof.
apply/(iffP andP) => [[/forallP Huni /forallP Htrig] | [Huni Htrig]].
- split => [t | t u]; first by apply/eqP.
  by have:= Htrig t => /forall_inP; apply.
- split; apply/forallP => t; first by rewrite Huni.
  by apply/forall_inP; apply Htrig.
Qed.

Lemma unitrig1 : unitrig (fun x y => (x == y)%:R).
Proof.
apply/unitrigP; split => [u | u v] /=; first by rewrite eq_refl.
by case: (altP (v =P u)) => [-> |] //=; rewrite eq_refl.
Qed.

(** TODO : construct the group of unitriangular matrix *)

Lemma unitrig_suml M (Mod : lmodType R) (F : T -> Mod) u :
  unitrig M ->
  \sum_(t : T) M u t *: F t = \sum_(t | (t <= u)%O) M u t *: F t.
Proof.
move=> /unitrigP [Muni Mtrig].
rewrite (bigID (fun t => (t <= u)%O)) /= addrC big1 ?add0r // => i.
by move=> /(contraR (@Mtrig _ _))/eqP ->; rewrite scale0r.
Qed.

Lemma unitrig_sum1l M (Mod : lmodType R) (F : T -> Mod) u :
  unitrig M ->
  \sum_(t : T) M u t *: F t = F u + \sum_(t | (t < u)%O) M u t *: F t.
Proof.
move=> Hut; rewrite unitrig_suml // (bigD1 u) //=.
move: Hut => /unitrigP [-> _]; rewrite scale1r; congr (_ + _).
by apply eq_bigl => t; rewrite lt_neqAle andbC.
Qed.

Lemma unitrig_sumr M (Mod : lmodType R) (F : T -> Mod) t :
  unitrig M ->
  \sum_(u : T) M u t *: F u = \sum_(u | (t <= u)%O) M u t *: F u.
Proof.
move=> /unitrigP [Muni Mtrig].
rewrite (bigID (fun u => (t <= u)%O)) /= addrC big1 ?add0r // => i.
by move=> /(contraR (@Mtrig _ _))/eqP ->; rewrite scale0r.
Qed.

Lemma unitrig_sum1r M (Mod : lmodType R) (F : T -> Mod) t :
  unitrig M ->
  \sum_(u : T) M u t *: F u = F t + \sum_(u | (t < u)%O) M u t *: F u.
Proof.
move=> Hut; rewrite unitrig_sumr // (bigD1 t) //=.
move: Hut => /unitrigP [-> _]; rewrite scale1r; congr (_ + _).
by apply eq_bigl => u; rewrite lt_def andbC.
Qed.


Lemma unitrig_sumlV M (Mod : lmodType R) (F : T -> Mod) u :
  unitrig M ->
  \sum_(t : T) M t u *: F t = \sum_(t | (u <= t)%O) M t u *: F t.
Proof.
move=> /unitrigP [Muni Mtrig].
rewrite (bigID (fun t => (u <= t)%O)) /= addrC big1 ?add0r // => i.
by move=> /(contraR (@Mtrig _ _))/eqP ->; rewrite scale0r.
Qed.

Lemma unitrig_sum1lV M (Mod : lmodType R) (F : T -> Mod) u :
  unitrig M ->
  \sum_(t : T) M t u *: F t = F u + \sum_(t | (u < t)%O) M t u *: F t.
Proof.
move=> Hut; rewrite unitrig_sumlV // (bigD1 u) //=.
move: Hut => /unitrigP [-> _]; rewrite scale1r; congr (_ + _).
by apply eq_bigl => t; rewrite lt_def andbC.
Qed.

Lemma unitrig_sumrV M (Mod : lmodType R) (F : T -> Mod) t :
  unitrig M ->
  \sum_(u : T) M t u *: F u = \sum_(u | (u <= t)%O) M t u *: F u.
Proof.
move=> /unitrigP [Muni Mtrig].
rewrite (bigID (fun u => (u <= t)%O)) /= addrC big1 ?add0r // => i.
by move=> /(contraR (@Mtrig _ _))/eqP ->; rewrite scale0r.
Qed.

Lemma unitrig_sum1rV M (Mod : lmodType R) (F : T -> Mod) t :
  unitrig M ->
  \sum_(u : T) M t u *: F u = F t + \sum_(u | (u < t)%O) M t u *: F u.
Proof.
move=> Hut; rewrite unitrig_sumrV // (bigD1 t) //=.
move: Hut => /unitrigP [-> _]; rewrite scale1r; congr (_ + _).
by apply eq_bigl => u; rewrite lt_neqAle andbC.
Qed.

End UniTriangular.

Section TriangularInv.

Variable R : comUnitRingType.
Variable disp : unit.
Variable T : finPOrderType disp.
Variable M : T -> T -> R.
Implicit Types t u v : T.

Hypothesis Munitrig : unitrig M.

Local Notation n := #|{: T}|.
Definition Mat : 'M[R]_n := \matrix_(i, j < n) M (enum_val i) (enum_val j).

Lemma det_unitrig : \det Mat = 1.
Proof.
have [Muni Mtrig] := unitrigP _ Munitrig.
rewrite /Mat /determinant (bigD1 1%g) //=.
rewrite !big1 ?mulr1 ?odd_perm1 ?expr0 ?addr0 //.
- move=> s Hs.
  have [i /eqP Hi] : exists i, M (enum_val i) (enum_val (s i)) == 0.
    apply/existsP; move: Hs; apply contraR.
    rewrite negb_exists => /forallP /= H.
    have {}H : forall i : 'I_n, (enum_val (s i) <= enum_val i)%O.
      by move=> i; exact: Mtrig (H i).
    suff Hfix : forall t, s (enum_rank t) = enum_rank t.
      by apply/eqP/permP => /= i; rewrite perm1 -(enum_valK i); apply: Hfix.
    elim/ordtype.finord_wf => t IHt.
    move/(_ (enum_rank t)) : H.
    rewrite le_eqVlt => /orP [/eqP/(can_inj (@enum_valK _)) // |].
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

Lemma Minv_trig t u : Minv u t != 0 -> (t <= u)%O.
Proof.
have [Muni Mtrig] := unitrigP _ Munitrig.
apply contraR => H; apply/eqP; elim/ordtype.finord_wf: u H => /= u IHu Hu.
have:= Minvr u t.
rewrite [X in  _ = (nat_of_bool X)%:R](_ : _ = false) /=; first last.
  by apply negbTE; move: Hu; apply contra => /eqP ->.
rewrite (bigID (fun v => v <= u)%O) /= [X in _ + X]big1 ?addr0; first last.
  by move=> v /(contraR (@Mtrig _ _)) /eqP ->; rewrite mul0r.
rewrite (bigD1 u) //= Muni mul1r big1 ?addr0 // => i /andP [Hneq Hlt].
rewrite IHu ?mulr0 //.
- by rewrite lt_neqAle Hlt Hneq.
- by move: Hu; apply contra => /le_trans; apply.
Qed.

Lemma Minv_uni t : Minv t t = 1.
Proof.
have [Muni Mtrig] := unitrigP _ Munitrig.
have:= Minvr t t; rewrite eq_refl /= -[1%:R]/1 => <-.
rewrite (bigID (fun v => v <= t)%O) /= [X in _ + X]big1 ?addr0; first last.
  by move=> v /(contraR (@Mtrig _ _))/eqP ->; rewrite mul0r.
rewrite (bigID (fun v => t <= v)%O) /= [X in _ + X]big1 ?addr0; first last.
  by move=> v /andP [_ /(contraR (@Minv_trig _ _))/eqP ->]; rewrite mulr0.
rewrite (big_pred1 t) ?Muni ?mul1r // => v /=.
by rewrite eq_le.
Qed.

Lemma Minv_unitrig : unitrig Minv.
Proof. apply/unitrigP; split; [exact: Minv_uni | exact: Minv_trig]. Qed.

Lemma Minv_lincombl (Mod : lmodType R) (F G : T -> Mod) :
  (forall t, F t = \sum_u M t u *: G u) ->
  (forall t, G t = \sum_u Minv t u *: F u).
Proof.
move=> H t.
under eq_bigr do [rewrite H scaler_sumr; under eq_bigr do rewrite scalerA].
rewrite exchange_big /= (bigD1 t) //= -scaler_suml Minvl eq_refl scale1r.
rewrite big1 ?addr0 // => i /negbTE Hi.
by rewrite -scaler_suml Minvl Hi scale0r.
Qed.

Lemma Minv_lincombr (Mod : lmodType R) (F G : T -> Mod) :
  (forall t, F t = \sum_u M u t *: G u) ->
  (forall t, G t = \sum_u Minv u t *: F u).
Proof.
move=> H t.
under eq_bigr do [rewrite H scaler_sumr; under eq_bigr do rewrite scalerA mulrC].
rewrite exchange_big /= (bigD1 t) //= -scaler_suml Minvr eq_refl scale1r.
rewrite big1 ?addr0 // => i /negbTE Hi.
by rewrite -scaler_suml Minvr eq_sym Hi scale0r.
Qed.

End TriangularInv.
