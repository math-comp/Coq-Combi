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

Set Implicit Arguments.
Unset Strict Implicit.

Lemma incr_nth_inj sh : injective (incr_nth sh).
Proof.
  move=> i j Hsh.
  case (altP (i =P j)) => [//= | /negbTE Hdiff].
  have:= eq_refl (nth 0 (incr_nth sh i) j).
  by rewrite {2}Hsh !nth_incr_nth eq_refl Hdiff eqn_add2r.
Qed.

Section RCons.

  Variable (T : eqType).
  Implicit Type s w : seq T.
  Implicit Type a b l : T.

  Lemma head_any s a b : s != [::] -> head a s = head b s.
  Proof. by elim: s. Qed.

  Lemma nth_any s a b i : i < size s -> nth a s i = nth b s i.
  Proof. elim: s i => //= s0 s IHs [//=|i] Hsize /=. by apply: IHs. Qed.

  Lemma rcons_set_nth a s l : set_nth a s (size s) l = rcons s l.
  Proof. elim: s => [//=| l0 s IHs]. by rewrite rcons_cons -IHs /=. Qed.

  Lemma set_nth_non_nil d s n y : set_nth d s n y != [::].
  Proof. elim: s => [|s0 s]; by case n. Qed.

  Lemma set_nth_rcons (x0 : T) s x n y :
    set_nth x0 (rcons s x) n y =
    if n < size s then rcons (set_nth x0 s n y) x
    else if n == size s then rcons s y else (rcons s x) ++ ncons (n - size s).-1 x0 [:: y].
  Proof.
    elim: s n => [//= | s0 s IHs] n.
    + case eqP => [-> //= |]; by case: n => [| []].
    + rewrite rcons_cons /=; case: n => [//= | n] /=.
      have {IHs} := (IHs n). rewrite eqSS -[n.+1 < (size s).+1]/(n < (size s)).
      by case (ltngtP n (size s)) => _ <-.
  Qed.

  Lemma cons_in_map_cons a b s w :
    forall l : seq (seq T), a :: s \in [seq b :: s1 | s1 <- l] -> a == b.
  Proof.
    elim=> [//=| l0 l H]; rewrite map_cons in_cons; move/orP => []; last by exact H.
    by move=> /eqP [] ->.
  Qed.

  Lemma rcons_nilF s l : ((rcons s l) == [::]) = false.
  Proof. case eqP=>//= H; have:= eq_refl (size (rcons s l)). by rewrite {2}H size_rcons. Qed.

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

  Lemma count_mem_rcons w l i : count_mem i (rcons w l) = count_mem i w + (l == i).
  Proof. by rewrite -count_rev rev_rcons /= count_rev addnC. Qed.

End RCons.



Section Fintype.
  (* We define SubSeq w as a finType *)

Variable (T : countType) (w : seq T).
Implicit Type s w : seq T.
Implicit Type a b l : T.

Structure subseqs : Type :=
  Subseqs {subseqsval :> seq T; _ : subseq subseqsval w}.
Canonical subseqs_subType := Eval hnf in [subType for subseqsval].
Definition subseqs_eqMixin := Eval hnf in [eqMixin of subseqs by <:].
Canonical subseqs_eqType := Eval hnf in EqType subseqs subseqs_eqMixin.
Definition subseqs_choiceMixin := Eval hnf in [choiceMixin of subseqs by <:].
Canonical subseqs_choiceType := Eval hnf in ChoiceType subseqs subseqs_choiceMixin.
Definition subseqs_countMixin := Eval hnf in [countMixin of subseqs by <:].
Canonical subseqs_countType := Eval hnf in CountType subseqs subseqs_countMixin.
Canonical subseqs_subCountType := Eval hnf in [subCountType of subseqs].

Fixpoint list_subseqs w :=
  if w is w0 :: w' then
    let rec := list_subseqs w' in [seq w0 :: s | s <- rec ] ++ rec
  else [:: [::] ].

Lemma list_subseqsP : all (fun s => subseq s w) (list_subseqs w).
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

Lemma mem_list_subseqs s :
  subseq s w -> s \in (list_subseqs w).
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

Definition subseqs_enum : seq subseqs := pmap insub (undup (list_subseqs w)).

Lemma finite_subseqs : Finite.axiom subseqs_enum.
Proof.
  case=> /= s Hs; rewrite -(count_map _ (pred1 s)) (pmap_filter (@insubK _ _ _)).
  rewrite count_filter -(@eq_count _ (pred1 s)) => [|s' /=]; last first.
    by rewrite isSome_insub; case: eqP=> // ->.
  rewrite count_uniq_mem.
  + by rewrite mem_undup (mem_list_subseqs Hs).
  + by apply: undup_uniq.
Qed.

Canonical subseqs_finMixin := Eval hnf in FinMixin finite_subseqs.
Canonical subseqs_finType := Eval hnf in FinType subseqs subseqs_finMixin.
Canonical subseqs_subFinType := Eval hnf in [subFinType of subseqs_countType].

Lemma subseqsP (s : subseqs) : subseq s w.
Proof. by case: s => /= s. Qed.

Definition sub_nil  : subseqs := Subseqs (sub0seq w).
Definition sub_full : subseqs := Subseqs (subseq_refl w).

Lemma size_le (s : subseqs) : size s <= size w.
Proof. case: s => s Ps /=; by apply: size_subseq. Qed.

End Fintype.

