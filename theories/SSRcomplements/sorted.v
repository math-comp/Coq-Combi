(** * Combi.SSRcomplements.sorted : [path] and [sorted] complements *)
(******************************************************************************)
(*      Copyright (C) 2015-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(******************************************************************************)
(** * Various Lemmas about [path] and [sorted] which are missing in MathComp  *)
(**                                                                           *)
(** TODO: these probably should be contributed to path.v                      *)
(******************************************************************************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N.


Module LeqGeqOrder.

Definition geq_refl : reflexive geq :=
  fun x => leqnn x.
Definition geq_total : total geq :=
  fun x y => leq_total y x.
Definition geq_trans : transitive geq :=
  fun x y z H1 H2 => leq_trans H2 H1.
Definition anti_geq : antisymmetric geq :=
  fun x y H => esym (anti_leq H).
Definition ltn_irr : irreflexive ltn :=
  fun x => ltnn x.
Definition gtn_trans : transitive gtn :=
  fun x y z H1 H2 => ltn_trans H2 H1.
Definition gtn_irr : irreflexive gtn :=
  fun x => ltnn x.

#[export] Hint Resolve leq_total leq_trans anti_leq : core.
#[export] Hint Resolve geq_refl geq_total geq_trans anti_geq : core.
#[export] Hint Resolve ltn_trans ltn_irr gtn_trans gtn_irr : core.

End LeqGeqOrder.

Import LeqGeqOrder.

(* TODO: remove me when merged in mathcomp *)
Lemma eq_sorted (T : Type) (e e' : rel T) : e =2 e' -> sorted e =1 sorted e'.
Proof. by move=> ee' [] // ? ?; apply: eq_path. Qed.

Section Sorted.

Variable T : eqType.
Variable Z : T.
Variable R : rel T.

Implicit Type l : T.
Implicit Type r : seq T.

Local Notation sorted r := (sorted R r).
Local Notation "x <=R y" := (R x y) (at level 70, y at next level).

Lemma sorted_consK l r : sorted (cons l r) -> sorted r.
Proof using. by case: r => [//=| r0 r] => /andP []. Qed.

Lemma sorted_rconsK l r : sorted (rcons r l) -> sorted r.
Proof using. by case: r => [//=| r0 r] /=; rewrite rcons_path => /andP []. Qed.

Lemma sorted_take r n : sorted r -> sorted (take n r).
Proof using.
elim: r n => [//= | r0 r IHr] [//=| n] /= H.
case: r r0 H IHr => [//=| r1 r] r0 /= /andP [H Hp] /(_ n Hp).
by case: n => [//=|n] /= ->; rewrite H.
Qed.

Lemma sorted_drop r n : sorted r -> sorted (drop n r).
Proof using.
elim: n r => [//= | n IHn ]; first by case.
case => [//= | r0 r /=] H; apply: IHn.
by case: r H => [//=|r1 r] /andP [].
Qed.

Lemma sorted_catL u v : sorted (u ++ v) -> sorted u.
Proof using. by move/(sorted_take (size u)); rewrite take_size_cat. Qed.

Lemma sorted_catR u v : sorted (u ++ v) -> sorted v.
Proof using. by move/(sorted_drop (size u)); rewrite drop_size_cat. Qed.

Lemma sorted1P r :
  reflect
    (forall (i : nat), i.+1 < (size r) -> (nth Z r i <=R nth Z r i.+1))
    (sorted r).
Proof using.
case: r => [| r0 r] /=; first by apply/(iffP idP).
exact/pathP.
Qed.

Lemma sorted_rcons l r : sorted r -> (last l r <=R l) -> sorted (rcons r l).
Proof using. by case: r => [//=| r0 r] /=; rewrite rcons_path => -> ->. Qed.

Hypothesis Rtrans : transitive R.

Lemma incr_equiv r :
  (forall (i j : nat), i < j < (size r) -> nth Z r i <=R nth Z r j)
  <->
  (forall (i : nat), i.+1 < (size r) -> nth Z r i <=R nth Z r i.+1).
Proof using Rtrans.
split => H.
- by move=> i Hi; apply: H; rewrite Hi ltnSn.
- move=> i j; move Hdiff : (j - i.+1) => diff.
  elim: diff i j Hdiff => [| diff IHdiff] i j /=.
  + move/eqP; rewrite -/(leq j i) => /eqP H1 /andP [H2 Hj].
    have Hij : i.+1 = j by apply/eqP; rewrite eqn_leq H2 /= /leq H1.
    by rewrite -Hij; apply: H; rewrite Hij.
  + move=> Hdiff => /andP [_ Hj].
    have Hij : i < j.-1.
      by move: Hdiff; rewrite subnS -subn1 subnAC subn1 -subn_gt0 => ->.
    apply: (Rtrans (y := nth Z r j.-1)).
    - apply: IHdiff; last by rewrite Hij /=; apply (leq_ltn_trans (leq_pred _)).
      apply/eqP; rewrite -eqSS -Hdiff.
      rewrite -(subSn Hij).
      by move: Hij; case j.
    - by case: j Hj Hij {Hdiff} => [//= | j ] /H /=.
Qed.

Lemma sorted_strictP r :
  reflect
    (forall (i j : nat), i < j < (size r) -> (nth Z r i <=R nth Z r j))
    (sorted r).
Proof using Rtrans. by apply/(iffP idP); rewrite incr_equiv => /sorted1P. Qed.

Hypothesis Rrefl : reflexive R.

Lemma non_decr_equiv r :
  (forall (i j : nat), i <= j < (size r) -> nth Z r i <=R nth Z r j)
  <->
  (forall (i : nat), i.+1 < (size r) -> nth Z r i <=R nth Z r i.+1).
Proof using Rrefl Rtrans.
split => H.
- move=> i Hi.
  have : i <= i.+1 < size r by rewrite Hi andbT.
  exact: H.
- move=> i j; move Hdiff : (j - i) => diff.
  elim: diff i j Hdiff => [| diff IHdiff] i j /=.
  + move/eqP; rewrite -/(leq j i) => H1 /andP [H2 Hj].
    by rewrite (_ : i = j); last by apply/eqP; rewrite eqn_leq H1 H2.
  + move=> Hdiff => /andP [_ Hj].
    have Hiltj : i < j by rewrite -subn_gt0 Hdiff.
    apply: (Rtrans (y := nth Z r i.+1)).
    * by apply: H; exact: (leq_ltn_trans Hiltj).
    * apply: IHdiff => //=; first by rewrite subnS Hdiff.
      by rewrite Hiltj Hj.
Qed.

Lemma sortedP r :
  reflect
    (forall (i j : nat), i <= j < (size r) -> (nth Z r i <=R nth Z r j))
    (sorted r).
Proof using Rrefl Rtrans.
by apply/(iffP idP); rewrite non_decr_equiv => /sorted1P.
Qed.

Lemma sorted_cons l r : sorted (cons l r) -> (l <=R head l r) /\ sorted r.
Proof using Rrefl.
by case: r => [//=| r0 r]; move => /andP [/= ->].
Qed.

Lemma sorted_last l r : sorted (rcons r l) -> (last l r <=R l).
Proof using Rrefl.
by case: r => [//=| r0 r] /=; rewrite rcons_path => /andP [].
Qed.

Lemma head_leq_last_sorted l r : sorted (l :: r) -> (l <=R last l r).
Proof using Rrefl Rtrans.
elim: r l => [//=| t0 r IHr] l /= /andP [Hl {}/IHr].
exact: Rtrans Hl.
Qed.

Hypothesis Hanti : antisymmetric R.

Lemma sorted_lt_by_pos r p q :
  sorted r -> p < size r -> q < size r ->
   (nth Z r p != nth Z r q) && (nth Z r p <=R nth Z r q) -> p < q.
Proof using Hanti Rrefl Rtrans.
move=> /sortedP Hsort Hp Hq /andP [Hneq Hpq].
have H : q <= p -> (nth Z r q <=R nth Z r p).
  by move=> Hqp; apply Hsort; rewrite Hqp Hp.
have:= contra H; rewrite ltnNge; apply.
apply/negP => Hqp.
move: Hneq; suff -> : nth Z r p = nth Z r q by rewrite eq_refl.
by apply Hanti; rewrite Hqp Hpq.
Qed.

End Sorted.

Require Import tools.

Lemma enum_ord_sorted_ltn N :
  sorted (fun i j : 'I_N => i < j) (enum 'I_N).
Proof.
rewrite /sorted; case Henum : (enum 'I_N) => [//= | a l].
rewrite -(map_path (h := val) (e := ltn) (b := pred0)) //.
- rewrite (_ : l = behead (enum 'I_N)); last by rewrite Henum.
  rewrite (_ : val a = head 0 (map val (enum 'I_N))); last by rewrite Henum.
  rewrite -behead_map val_enum_ord.
  case: N {a l Henum} => [//= | N] /=.
  exact: (iota_ltn_sorted 0 N.+1).
- by rewrite (eq_has (a2 := pred0)); first by rewrite has_pred0.
Qed.

Lemma enum_ord_sorted N :
  sorted (fun i j : 'I_N => i <= j) (enum 'I_N).
Proof.
by have:= enum_ord_sorted_ltn N; apply: sub_sorted => i j /=/ltnW.
Qed.

Lemma sorted_ltn_ind s :
  sorted ltn s -> sumn (iota 0 (size s)) <= sumn s /\ last 0 s >= (size s).-1.
Proof.
elim/last_ind: s => [//=| s sn IHs] /= Hsort.
move/(_ (sorted_rconsK Hsort)): IHs => [Hsum Hlast]; split.
- rewrite -{2}(revK (rcons s sn)) rev_rcons sumn_rev /= [sn + _]addnC sumn_rev.
  rewrite size_rcons -addn1 iota_add /= sumn_cat /= add0n addn0.
  apply (leq_add Hsum).
  case/lastP: s Hsort Hlast {Hsum} => [//= | s sn1] /=.
  rewrite !size_rcons !last_rcons /= -!cats1 -catA cat1s => /sorted_catR /=.
  by rewrite andbT => /(leq_ltn_trans _); apply.
- case/lastP: s Hsort Hlast {Hsum} => [//= | s sn1] /=.
  rewrite !size_rcons !last_rcons /= -!cats1 -catA cat1s => /sorted_catR /=.
  by rewrite andbT => /(leq_ltn_trans _); apply.
Qed.

Lemma sorted_sumn_iotaE s :
  sorted ltn s -> sumn s = sumn (iota 0 (size s)) -> s = iota 0 (size s).
Proof.
elim/last_ind: s => [//= | s sn IHs] /= Hsort.
have:= sorted_ltn_ind Hsort.
rewrite -{2 5}(revK (rcons s sn)) rev_rcons sumn_rev /= [sn + _]addnC sumn_rev.
rewrite size_rcons -{1 3 4}addn1 iota_add /= sumn_cat /= add0n addn0 cats1.
rewrite last_rcons => [] [_ Hsn].
have [Hsum _] := sorted_ltn_ind (sorted_rconsK Hsort).
by move=> /esym/(leq_addE Hsum Hsn) [/esym/(IHs (sorted_rconsK Hsort)) <- <-].
Qed.
