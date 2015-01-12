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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype choice fintype seq.
Require Import tools combclass.

Set Implicit Arguments.
Unset Strict Implicit.

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
    - case: s IHw => //= s0 s; case (altP (s0 =P w0)) => _ //= H1 H2; first by apply: H1.
      rewrite -rcons_cons in H2; by apply: H1.
  Qed.

  Lemma subseq_rcons_neq s si w wn :
    si != wn -> subseq (rcons s si) (rcons w wn) -> subseq (rcons s si) w.
  Proof.
    elim: w s si=> [/=| w0 w IHw] s si H.
    - case: s => [| s0 s] /=; first by case: eqP H.
      case (altP (s0 =P wn)) => //= ->; by rewrite rcons_nilF.
    - case: s => [/=| s0 s].
      * case eqP => [_ |] _; first by apply: sub0seq.
        rewrite -[ [:: si] ]/(rcons [::] si); exact (IHw _ _ H).
      * rewrite !rcons_cons /=; case (altP (s0 =P w0)) => _; first exact (IHw _ _ H).
        rewrite -rcons_cons; exact (IHw _ _ H).
  Qed.

  Lemma subseq_rev s w : subseq s w -> subseq (rev s) (rev w).
  Proof.
    elim: w s => [/= s /eqP -> //= | w0 w IHw] s //=.
    case: s => [_ | s0 s /=]; first by rewrite {1}/rev /=; case (rev _).
    rewrite !rev_cons; case eqP => [-> | _].
    - move/IHw; by apply subseq_rcons_eq.
    - move/IHw; rewrite rev_cons => {IHw} IHw; apply: (@subseq_trans _ (rev w) _ _ IHw).
      by apply: subseq_rcons.
  Qed.

End RCons.

Section Fintype.
  (* We define SubSeq w as a finType *)

Variable (T : countType) (w : seq T).
Implicit Type s w : seq T.

Fixpoint enum_subseqs w :=
  if w is w0 :: w' then
    let rec := enum_subseqs w' in [seq w0 :: s | s <- rec ] ++ rec
  else [:: [::] ].

Lemma enum_subseqsP : all (fun s => subseq s w) (enum_subseqs w).
Proof.
  apply/allP; elim: w => [| w0 wtl IHw] s /=.
    by rewrite mem_seq1 => /eqP ->.
  rewrite mem_cat => /orP [].
  - move/mapP => [] s' /IHw Hsubs -> /=.
    by rewrite eq_refl.
  - case: s => [//= | s0 s].
    move=> /IHw Hsubs; case eqP => Hs0.
    + apply: (@subseq_trans _ (s0 :: s)); first by apply: subseq_cons.
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
Proof. rewrite /=; by apply enum_sub_undupP. Qed.

Definition sub_nil  : subseqs := Subseqs (sub0seq w).
Definition sub_full : subseqs := Subseqs (subseq_refl w).

Lemma size_le (s : subseqs) : size s <= size w.
Proof. case: s => s Ps /=; by apply: size_subseq. Qed.

End Fintype.

