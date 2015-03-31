(******************************************************************************)
(*       Copyright (C) 2015 Florent Hivert <florent.hivert@lri.fr>            *)
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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import path finset finfun fingraph tuple bigop ssrint ssralg.

Require Import poset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Import GRing.

Section InclusionExclusion.

Variable T : finType.
Variable R : ringType.
Variable E : {set T}.
Variable P : poset E.

CoInductive moebius_fun (M : T -> T -> R) : Prop :=
  Moebius_Fun :
    (forall x, x \in E -> M x x = 1) ->
    (forall x y, x \in E -> ~~ P x y -> M x y = 0) ->
    (forall x y, strict P x y -> \sum_(z : T | P x z && P z y) M x z = 0) -> moebius_fun M.

Variable M : T -> T -> R.
Hypothesis HM : moebius_fun M.
Variable f g : T -> R.
Hypothesis Hfg : forall x : T, f x = \sum_(y : T | P x y) g y.

Theorem incl_excl x : x \in E -> g x = \sum_(y : T| P x y) (M x y) * (f y).
Proof.
  move: HM x => [] HMfix HMnP HMinter x Hx.
  rewrite (eq_bigr (fun y => \sum_(z | P y z) (M x y) * (g z))); first last.
    move=> y Hy; rewrite (Hfg y); by rewrite GRing.mulr_sumr.
  rewrite (exchange_big_dep (P x)) /=; last by move=> y z; apply: poset_trans.
  rewrite (bigID (pred1 x)) /=.
  set S := (X in X + _); have {S} -> : S = g x.
    rewrite /S{S}.
    rewrite (eq_bigl (pred1 x)); first last.
      move=> i /=; case (altP (i =P x)) => [->|]; last by rewrite andbF.
      by rewrite posetnn.
    rewrite big_pred1_eq (eq_bigl (pred1 x)); first last.
      move=> i /=; apply (sameP idP); apply (iffP idP) => [/eqP ->|].
      - by rewrite posetnn.
      - move=> /andP [] Hxi Hix; apply/eqP.
        exact: (anti_poset Hix Hxi).
    by rewrite big_pred1_eq (HMfix x Hx) mul1r.
  set S := (X in _ + X); suff -> : S = 0 by rewrite addr0.
  rewrite /S{S} (eq_bigr (fun x => 0)); first last.
    move=> y /andP [] Pyx Hneq.
    rewrite -mulr_suml HMinter; last by rewrite /strict /= Pyx eq_sym Hneq.
    by rewrite mul0r.
  by rewrite sumr_const mul0rn.
Qed.

End InclusionExclusion.



Section Moebius.

Variable T : finType.
Variable R : ringType.
Variable E : {set T}.
Variable P : poset E.

Require Import Wf.

Definition moebius_rec (x y : T) (rec : forall z, strict P z y -> R) : R :=
  if y == x then 1 else
    let callrec (z : T) := if boolP (strict P z y) is AltTrue Prf then rec _ Prf else 0
    in - \sum_(z | P x z) callrec z.

Definition moebius x : T -> R := Fix (strict_Wf P) _ (moebius_rec x).

Lemma moebius_inc x y : x \in E -> ~~ P x y -> moebius x y = 0.
Proof.
  move=> Hx Hinc.
  rewrite /moebius/moebius_rec/=/Fix/Fix_F/=.
  case: (strict_Wf P y) => A.
  case: (altP (y =P x)) => [Heq | Hneq]; first by move: Hinc; rewrite Heq (posetnn Hx).
  rewrite (eq_bigr (fun x => 0)); first by rewrite sumr_const mul0rn oppr0.
  move=> z Pxz; case (boolP (strict P z y)) => sPzy //.
  exfalso; move: Hinc; by rewrite (poset_trans Pxz (strictW sPzy)).
Qed.

Lemma moebius_interv_ind x y :
  strict P x y -> moebius x y = - \sum_(z : T | P x z && strict P z y) moebius x z.
Proof.
  move: y; apply: (well_founded_ind (strict_Wf P)) => y IHy Hy.
  rewrite /moebius /Fix -Fix_F_eq /=.
  case : (strict_Wf P y) => Accy /=.
  have:= Hy; rewrite {1}/moebius_rec eq_sym {1}/strict/= => /andP [] _ /negbTE ->.
  congr (- _); rewrite (bigID (fun z => strict P z y)) /=.
  set S := (X in (_ + X)); have {S} -> : S = 0.
    rewrite /S {S} (eq_bigr (fun x => 0)); first by rewrite sumr_const mul0rn.
    move=> z /andP [] _; by case (boolP (strict P z y)).
  rewrite addr0; apply eq_bigr => z /andP [] Pxz.
  case (boolP (strict P z y)) => //= sPzy _.
  apply: (Fix_F_inv (strict_Wf P)) => {y IHy Hy Accy sPzy z Pxz} y f g Hfg.
  rewrite /moebius_rec; case: (y == x) => //.
  congr (- _); apply: eq_bigr => z Pxz; by case (boolP (strict P z y)).
Qed.

Lemma moebius_interv x y :
  strict P x y -> \sum_(z : T | P x z && P z y) moebius x z = 0.
Proof.
  move=> sPxy; rewrite (bigID (pred1 y)) /=.
  rewrite (eq_bigl (pred1 y)); first last.
    move=> z /=; case (altP (z =P y)) => [->|]; last by rewrite andbF.
    rewrite (strictW sPxy) posetnn //.
    by move: (stablerelP (strictW sPxy)) => [].
  rewrite big_pred1_eq.
  rewrite (eq_bigl (fun z => P x z && strict P z y)); first last.
    by move=> z /=; rewrite /strict /= andbA.
  by rewrite -[X in _ + X]opprK -(moebius_interv_ind sPxy) addrN.
Qed.

Lemma moebiusP : moebius_fun P moebius.
Proof.
  constructor.
  - move => x Hx; by rewrite /moebius /Fix -Fix_F_eq /= /moebius_rec eq_refl.
  - exact moebius_inc.
  - exact moebius_interv.
Qed.

Definition moebius_inv := incl_excl moebiusP.

End Moebius.
