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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import path.

(******************************************************************************)
(** * Various Lemmas about [path] and [sorted] which are missing in MathComp  *)
(*                                                                            *)
(** TODO: these probably should be contributed to path.v                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope N.


Section Sorted.

  Variable T : eqType.
  Variable Z : T.
  Variable R : rel T.

  Implicit Type l : T.
  Implicit Type r : seq T.

  Local Notation sorted r := (sorted R r).
  Local Notation "x <=R y" := (R x y) (at level 70, y at next level).

  Lemma sorted_consK l r : sorted (cons l r) -> sorted r.
  Proof. by case: r => [//=| r0 r] => /andP []. Qed.

  Lemma sorted_rconsK l r : sorted (rcons r l) -> sorted r.
  Proof. case: r => [//=| r0 r] /=; by rewrite rcons_path => /andP []. Qed.

  Lemma sorted_take r n : sorted r -> sorted (take n r).
  Proof.
    elim: r n => [//= | r0 r IHr] [//=| n] /= H.
    case: r r0 H IHr => [//=| r1 r] r0 /= /andP [] H Hp /(_ n Hp).
    case: n => [//=|n] /= ->; by rewrite H.
  Qed.

  Lemma sorted_drop r n : sorted r -> sorted (drop n r).
  Proof.
    elim: n r => [//= | n IHn ]; first by case.
    case => [//= | r0 r /=] H; apply IHn => {IHn}.
    by case: r H => [//=|r1 r] /andP [].
  Qed.

  Lemma sorted_catL u v : sorted (u ++ v) -> sorted u.
  Proof. move/(sorted_take (size u)); by rewrite take_size_cat. Qed.

  Lemma sorted_catR u v : sorted (u ++ v) -> sorted v.
  Proof. move/(sorted_drop (size u)); by rewrite drop_size_cat. Qed.

  Lemma sorted1P r :
    reflect
      (forall (i : nat), i.+1 < (size r) -> (nth Z r i <=R nth Z r i.+1))
      (sorted r).
  Proof. case: r => [| r0 r] /=; first by apply/(iffP idP). by apply/pathP. Qed.

  Lemma sorted_rcons l r : sorted r -> (last l r <=R l) -> sorted (rcons r l).
  Proof. case: r => [//=| r0 r] /=; by rewrite rcons_path => -> ->. Qed.

  Hypothesis Rtrans : transitive R.

  Lemma incr_equiv r :
    (forall (i j : nat), i < j < (size r) -> nth Z r i <=R nth Z r j)
    <->
    (forall (i : nat), i.+1 < (size r) -> nth Z r i <=R nth Z r i.+1).
  Proof.
    split => H.
    - move=> i Hi; by apply: H; rewrite Hi ltnSn.
    - move=> i j; move Hdiff : (j - i.+1) => diff.
      elim: diff i j Hdiff => [| diff IHdiff] i j /=.
      + move/eqP; rewrite -/(leq j i) => /eqP H1 /andP [] H2 Hj.
        have Hij : i.+1 = j by apply/eqP; rewrite eqn_leq H2 /= /leq H1.
        rewrite -Hij; apply: H; by rewrite Hij.
      + move=> Hdiff => /andP [] _ Hj.
        have Hij : i < j.-1.
          move: Hdiff; by rewrite subnS -subn1 subnAC subn1 -subn_gt0 => ->.
        apply: (Rtrans (y := nth Z r j.-1)).
        - apply: IHdiff; last by rewrite Hij /=; apply (leq_ltn_trans (leq_pred _)).
          apply/eqP; rewrite -eqSS -Hdiff.
          rewrite -(subSn Hij).
          move: Hij; by case j.
        - by case: j Hj Hij {Hdiff} => [//= | j ] /H /=.
  Qed.

  Lemma sorted_strictP r :
    reflect
      (forall (i j : nat), i < j < (size r) -> (nth Z r i <=R nth Z r j))
      (sorted r).
  Proof. apply/(iffP idP); by rewrite incr_equiv => /sorted1P. Qed.

  Hypothesis Rrefl : reflexive R.

  Lemma non_decr_equiv r :
    (forall (i j : nat), i <= j < (size r) -> nth Z r i <=R nth Z r j)
    <->
    (forall (i : nat), i.+1 < (size r) -> nth Z r i <=R nth Z r i.+1).
  Proof.
    split => H.
    - move=> i Hi.
      have : i <= i.+1 < size r by rewrite Hi andbT.
      exact: H.
    - move=> i j; move Hdiff : (j - i) => diff.
      elim: diff i j Hdiff => [| diff IHdiff] i j /=.
      + move/eqP; rewrite -/(leq j i) => H1 /andP [] H2 Hj.
        by rewrite (_ : i = j); last by apply/eqP; rewrite eqn_leq H1 H2.
      + move=> Hdiff => /andP [] _ Hj.
        have Hiltj : i < j by rewrite -subn_gt0 Hdiff.
        apply: (Rtrans (y := nth Z r i.+1)).
        * apply: H; exact: (leq_ltn_trans Hiltj).
        * apply: IHdiff => //=; first by rewrite subnS Hdiff.
          by rewrite Hiltj Hj.
  Qed.

  Lemma sortedP r :
    reflect
      (forall (i j : nat), i <= j < (size r) -> (nth Z r i <=R nth Z r j))
      (sorted r).
  Proof. apply/(iffP idP); by rewrite non_decr_equiv => /sorted1P. Qed.

  Lemma sorted_cons l r : sorted (cons l r) -> (l <=R head l r) /\ sorted r.
  Proof. case: r => [//=| r0 r]; by move => /andP [] /= ->. Qed.

  Lemma sorted_last l r : sorted (rcons r l) -> (last l r <=R l).
  Proof. case: r => [//=| r0 r] /=; by rewrite rcons_path => /andP []. Qed.

  Lemma head_leq_last_sorted l r : sorted (l :: r) -> (l <=R last l r).
  Proof.
    elim: r l => [//=| t0 r IHr] l /= /andP [] Hl /IHr {IHr}.
    exact: Rtrans Hl.
  Qed.

  Hypothesis Hanti : antisymmetric R.

  Lemma sorted_lt_by_pos r p q :
    sorted r -> p < size r -> q < size r ->
     (nth Z r p != nth Z r q) && (nth Z r p <=R nth Z r q) -> p < q.
  Proof.
    move=> /sortedP Hsort Hp Hq /andP [] Hneq Hpq.
    have H : q <= p -> (nth Z r q <=R nth Z r p).
      by move=> Hqp; apply Hsort; rewrite Hqp Hp.
    have:= contra H; rewrite ltnNge; apply.
    apply (introN idP) => Hqp.
    move: Hneq; suff -> : nth Z r p = nth Z r q by rewrite eq_refl.
    by apply Hanti; rewrite Hqp Hpq.
  Qed.

End Sorted.

Lemma sorted_enum_ord N :
  sorted (fun i j : 'I_N => i <= j) (enum 'I_N).
Proof.
  rewrite /sorted; case Henum : (enum 'I_N) => [//= | a l].
  rewrite -(map_path (h := val) (e := leq) (b := pred0)).
  - rewrite (_ : l = behead (enum 'I_N)); last by rewrite Henum.
    rewrite (_ : val a = head 0 (map val (enum 'I_N))); last by rewrite Henum.
    rewrite -behead_map val_enum_ord.
    case: N {a l Henum} => [//= | N] /=.
    exact: (iota_sorted 0 N.+1).
  - by [].
  - by rewrite (eq_has (a2 := pred0)); first by rewrite has_pred0.
Qed.
