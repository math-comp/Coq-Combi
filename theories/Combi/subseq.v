(** * Combi.Combi.subseq : Subsequence of a sequence as a fintype *)

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
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype choice fintype seq.
From mathcomp Require Import path.
From Combi Require Import tools combclass.

(******************************************************************************)
(** TODO: these probably should be contributed to path.v                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

(** ** A few lemmas about [subseq] and [rcons] *)
Section RCons.

  Variable (T : eqType).
  Implicit Type s w : seq T.
  Implicit Type a b l : T.

  Lemma subseq_rcons_eq s w l : subseq s w <-> subseq (rcons s l) (rcons w l).
  Proof.
    split.
    - by rewrite -!cats1 => H; apply: cat_subseq => //=; rewrite (eq_refl _).
    - elim: w s => [|w0 w IHw s] /=.
      case=> //= s0 s; case (altP (s0 =P l)) => _ //=; by rewrite rcons_nilF.
    - case: s IHw => //= s0 s; case (altP (s0 =P w0)) => _ //= H1 H2; first exact: H1.
      rewrite -rcons_cons in H2; exact: H1.
  Qed.

  Lemma subseq_rcons_neq s si w wn :
    si != wn -> subseq (rcons s si) (rcons w wn) -> subseq (rcons s si) w.
  Proof.
    elim: w s si=> [/=| w0 w IHw] s si H.
    - case: s => [| s0 s] /=; first by case: eqP H.
      case (altP (s0 =P wn)) => //= ->; by rewrite rcons_nilF.
    - case: s => [/=| s0 s].
      * case eqP => [_ |] _; first exact: sub0seq.
        rewrite -[ [:: si] ]/(rcons [::] si); exact (IHw _ _ H).
      * rewrite !rcons_cons /=; case (altP (s0 =P w0)) => _; first exact (IHw _ _ H).
        rewrite -rcons_cons; exact (IHw _ _ H).
  Qed.

  Lemma subseq_rev s w : subseq s w -> subseq (rev s) (rev w).
  Proof.
    elim: w s => [/= s /eqP -> //= | w0 w IHw] s //=.
    case: s => [_ | s0 s /=]; first by rewrite {1}/rev /=; case (rev _).
    rewrite !rev_cons; case eqP => [-> | _].
    - move/IHw; by rewrite -subseq_rcons_eq.
    - move/IHw; rewrite rev_cons => {IHw} IHw; apply: (@subseq_trans _ (rev w) _ _ IHw).
      exact: subseq_rcons.
  Qed.

End RCons.


(** ** Subsequence of a sequence as a [fintype]                                *)
(**
We define a dependent type [SubSeq w] and provide it with a Canonical
[finType] structure
**)

Section Fintype.

Variable (T : countType).
Implicit Type s w : seq T.

Fixpoint enum_subseqs w :=
  if w is w0 :: w' then
    let rec := enum_subseqs w' in [seq w0 :: s | s <- rec ] ++ rec
  else [:: [::] ].

Lemma cons_in_enum_subseq x0 x s :
  x0 :: x \in enum_subseqs s -> x0 \in s.
Proof.
  elim: s => [//= | s0 s IHs] /=.
  rewrite inE mem_cat => /orP [].
  - move=> /mapP [] x1 _ [] -> _.
    by rewrite eq_refl.
  - move/IHs ->; by rewrite orbT.
Qed.

Lemma enum_subseqs_uniq s : uniq s -> uniq (enum_subseqs s).
Proof.
  elim: s => [//= | s0 s IHs] /= /andP [] Hs0 /IHs{IHs} Huniq.
  rewrite cat_uniq; apply/and3P; split.
  - by rewrite map_inj_uniq // => i j [].
  - apply/hasP => [] [] x.
    case: x => [_| x0 x] /=; first by move=> /mapP [] y _.
    move=> /cons_in_enum_subseq Hs0' /mapP [] y _ [] Hx0 _.
    move: Hs0; by rewrite -Hx0 Hs0'.
  - exact: Huniq.
Qed.

Variable (w : seq T).

Lemma enum_subseqsP : all (fun s => subseq s w) (enum_subseqs w).
Proof.
  apply/allP; elim: w => [| w0 wtl IHw] s /=.
    by rewrite mem_seq1 => /eqP ->.
  rewrite mem_cat => /orP [].
  - move/mapP => [] s' /IHw Hsubs -> /=.
    by rewrite eq_refl.
  - case: s => [//= | s0 s].
    move=> /IHw Hsubs; case eqP => Hs0.
    + apply: (@subseq_trans _ (s0 :: s)); first exact: subseq_cons.
      exact Hsubs.
    + exact Hsubs.
Qed.

Lemma mem_enum_subseqs s :
  subseq s w -> s \in (enum_subseqs w).
Proof.
  elim: w s => [| w0 wtl IHw] s /=.
    move/eqP ->; by rewrite mem_seq1.
  case: s => [/= _ | s0 s].
  - by rewrite mem_cat (IHw [::] (sub0seq wtl)) orbT.
  - have Hinjcons: injective (cons w0) by move=> x1 x2 [].
    case eqP => [-> | _] H; move: {H} (IHw _ H); rewrite mem_cat.
    + by rewrite (mem_map Hinjcons) => ->.
    + by move => ->; rewrite orbT.
Qed.

Structure subseqs : predArgType :=
  Subseqs {subseqsval :> seq T; _ : subseq subseqsval w}.
Canonical subseqs_subType := Eval hnf in [subType for subseqsval].
Definition subseqs_eqMixin := Eval hnf in [eqMixin of subseqs by <:].
Canonical subseqs_eqType := Eval hnf in EqType subseqs subseqs_eqMixin.
Definition subseqs_choiceMixin := Eval hnf in [choiceMixin of subseqs by <:].
Canonical subseqs_choiceType := Eval hnf in ChoiceType subseqs subseqs_choiceMixin.
Definition subseqs_countMixin := Eval hnf in [countMixin of subseqs by <:].
Canonical subseqs_countType := Eval hnf in CountType subseqs subseqs_countMixin.
Canonical subseqs_subCountType := Eval hnf in [subCountType of subseqs].
Let type := sub_undup_finType subseqs_subCountType enum_subseqsP mem_enum_subseqs.
Canonical subseqs_finType := [finType of subseqs for type].
Canonical subseqs_subFinType := Eval hnf in [subFinType of subseqs].

Lemma subseqsP (s : subseqs) : subseq s w.
Proof. by case: s => /= s. Qed.

Lemma enum_subseqsE :
  map val (enum subseqs) = undup (enum_subseqs w).
Proof. rewrite /=; exact: enum_sub_undupE. Qed.

Lemma uniq_enum_subseqsE :
  uniq w -> map val (enum subseqs) = enum_subseqs w.
Proof. move/enum_subseqs_uniq/undup_id <-. exact: enum_subseqsE. Qed.

Definition sub_nil  : subseqs := Subseqs (sub0seq w).
Definition sub_full : subseqs := Subseqs (subseq_refl w).

Lemma size_le (s : subseqs) : size s <= size w.
Proof. case: s => s Ps /=; exact: size_subseq. Qed.

End Fintype.

Require Import sorted.

(** ** Relating sub sequences of [iota] and being sorted *)
Lemma sorted_subseq_iota_rcons s n : subseq s (iota 0 n) = sorted ltn (rcons s n).
Proof.
  apply/idP/idP.
  - move=> Hsubs.
    apply: (subseq_sorted ltn_trans (s2 := (iota 0 n.+1))).
    + by rewrite -addn1 iota_add add0n /= cats1 -subseq_rcons_eq.
    + exact: iota_ltn_sorted.
  - elim: n s => [/= [//=| s0 s]| n IHn s].
      rewrite rcons_cons /= => /(order_path_min ltn_trans) /= /allP Hall.
      exfalso.
      suff /Hall : 0 \in rcons s 0 by [].
      by rewrite mem_rcons inE eq_refl.
    case/lastP: s => [_| s sn]; first exact: sub0seq.
    case: (ltnP sn n) => Hsn.
    + move/sorted_rconsK => Hsort.
      have:= Hsn; rewrite -{1}(last_rcons n s sn) => /(sorted_rcons Hsort)/IHn.
      move/subseq_trans; apply.
      rewrite -addn1 iota_add add0n cats1.
      exact: subseq_rcons.
    + move=> Hsort; have H : sn = n.
        apply anti_leq; rewrite Hsn andbT.
        move: Hsort.
        rewrite -!cats1 -catA => /sorted_catR => /= /andP [].
        by rewrite ltnS.
      subst sn.
      rewrite -addn1 iota_add add0n /= cats1.
      rewrite -subseq_rcons_eq; apply IHn.
      exact: (sorted_rconsK Hsort).
Qed.
