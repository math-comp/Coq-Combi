(** * Combi.Combi.subseq : Subsequence of a sequence as a fintype *)
(******************************************************************************)
(*      Copyright (C) 2014-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * Subsequence of a sequence as a [fintype]
We define a sigma-type [subseqs w] for subsequence of a given sequence [w]
We show that [subseqs w] is canonically a [finType]. We define the three
following constructor

- [Subseqs Pf] == construct a [subseqs w] from a proof [subseq x w].
- [sub_nil w] == the empty sequence [[::]] as a [subseqs w].
- [sub_full w] == [w] as as a [subseqs w].

 *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat bigop.
From mathcomp Require Import eqtype choice fintype seq path tuple.
Require Import tools combclass sorted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(******************************************************************************)
(** TODO: these probably should be contributed to path.v                      *)
(******************************************************************************)

(** ** A few lemmas about [subseq] and [rcons] *)
Section RCons.

Variable (T : eqType).
Implicit Type s w : seq T.
Implicit Type a b l : T.

Lemma subseq_rcons_eq s w l : subseq s w = subseq (rcons s l) (rcons w l).
Proof using. by rewrite -!cats1 subseq_cat2r. Qed.

Lemma subseq_rcons_neq s si w wn :
  si != wn -> subseq (rcons s si) (rcons w wn) = subseq (rcons s si) w.
Proof using.
move/negbTE => neq.
by rewrite -subseq_rev !rev_rcons /= neq -rev_rcons subseq_rev.
Qed.

End RCons.

Section SubseqSorted.

Variable (T : eqType) (leT : rel T).
Implicit Type s : seq T.

Lemma sorted_subseqP s1 s2 :
  transitive leT -> irreflexive leT -> sorted leT s1 -> sorted leT s2 ->
  reflect {subset s1 <= s2} (subseq s1 s2).
Proof.
move=> leT_trans leT_irr s1_sort s2_sort.
apply (iffP idP) => [|sub_s12]; first exact: mem_subseq.
apply/subseqP; exists [seq i \in s1 | i <- s2]; first by rewrite size_map.
apply: (irr_sorted_eq leT_trans leT_irr s1_sort).
  exact: (sorted_mask leT_trans).
move=> i; rewrite -filter_mask mem_filter.
by case: (boolP (i \in s1)) => // /sub_s12 ->.
Qed.

End SubseqSorted.

Section SubseqSortedIn.

Variable (T : eqType) (leT : rel T).
Implicit Type s : seq T.

Lemma sorted_subseq_inP s1 s2 :
  {in s2 & &, transitive leT} -> {in s2, irreflexive leT} ->
  sorted leT s1 -> sorted leT s2 ->
  reflect {subset s1 <= s2} (subseq s1 s2).
Proof.
move=> leT_tr leT_irr ss1 ss2; apply (iffP idP); first exact: mem_subseq.
move: leT_tr leT_irr ss1 ss2 => /in3_sig leT_tr /in1_sig leT_irr .
have /all_sigP[s2' ->] := allss s2 => + + /[dup] subs12.
have /all_sigP[{subs12}s1 ->] : all (mem s2) s1.
  by apply/allP => i /subs12 /mapP [[j /= j_in_s2 _ ->{i}]].
rewrite !sorted_map => ss1 ss2' subs12.
apply/map_subseq/(sorted_subseqP leT_tr leT_irr ss1 ss2').
by move=> i /(map_f sval) /subs12 /mapP[j j_in_s2'] /val_inj->.
Qed.

End SubseqSortedIn.


(** * Subsequence of a sequence as a [fintype]                                *)
(**
We define a dependent type [SubSeq w] and provide it with a Canonical
[finType] structure
**)

Section FinType.

Variables (T : choiceType) (w : seq T).

Structure subseqs : predArgType :=
  Subseqs {subseqsval :> seq T; _ : subseq subseqsval w}.
Canonical subseqs_subType := Eval hnf in [subType for subseqsval].
Definition subseqs_eqMixin := Eval hnf in [eqMixin of subseqs by <:].
Canonical subseqs_eqType := EqType subseqs subseqs_eqMixin.
Definition subseqs_choiceMixin := Eval hnf in [choiceMixin of subseqs by <:].
Canonical subseqs_choiceType := ChoiceType subseqs subseqs_choiceMixin.

Implicit Type (s : subseqs).

Lemma subseqsP s : subseq s w.
Proof using. by case: s => /= s. Qed.

Definition sub_nil  : subseqs := Subseqs (sub0seq w).
Definition sub_full : subseqs := Subseqs (subseq_refl w).

Lemma to_mask_spec s : {m : (size w).-tuple bool | mask m w == s}.
Proof.
move: s => [s subs]; apply/sigW => /=.
by move: subs => /subseqP [m /eqP szm ->{s}]; exists (Tuple szm).
Qed.
Definition to_mask s := let: exist m _ := to_mask_spec s in m.

Lemma to_maskK : cancel to_mask (fun m => Subseqs (mask_subseq (val m) w)).
Proof.
by rewrite /to_mask => s; case: to_mask_spec => m /eqP eqm; apply val_inj.
Qed.

Lemma mask1E x0 i :
  i < size w -> mask [tuple val x == i | x < size w] w = [:: nth x0 w i].
Proof.
move=> lti.
rewrite [val (mktuple _)](_ : _ = [seq x == i | x <- iota 0 (size w)]);
  last by rewrite /= (map_comp (pred1 i) val) val_enum_ord.
elim: w i lti => //= v0 v IHv [_|i /ltnSE lti] /=.
  rewrite [map _ _](_ : _ = nseq (size v) false) ?mask_false //.
  apply (eq_from_nth (x0 := false)) => [|i].
    by rewrite size_map size_iota size_nseq.
  rewrite size_map => lti; rewrite (nth_map 0) //.
  by rewrite size_iota in lti; rewrite nth_nseq lti nth_iota.
by rewrite -(add1n 0) iotaDl -map_comp -{}IHv.
Qed.

Lemma mask_injP :
  reflect (injective (fun m : (size w).-tuple bool => mask (val m) w))
          (uniq w).
Proof.
apply (iffP idP) => [w_uniq m1 m2 eqmask |].
- apply: eq_from_tnth => i; rewrite !(tnth_nth false).
  have Z : T by case: w i {w_uniq m1 m2 eqmask} => [[]|].
  have nthE m : (nth false m i) = (nth Z w i \in mask m w).
    by rewrite in_mask // (mem_nth Z (ltn_ord i)) /= index_uniq.
  by rewrite !nthE eqmask.
- case Hw: w => [//|w0 w']; rewrite -Hw => minj.
  pose f := (fun i : T => [:: i]).
  apply/(uniqP w0) => i j; rewrite !inE => lti ltj Heq.
  have {Heq}:= congr1 (cons^~ [::]) Heq.
  rewrite -!mask1E // => /minj /(congr1 (fun t => tnth t (Ordinal lti))).
  by rewrite !tnth_mktuple /= eqxx => /esym/eqP.
Qed.

Lemma Subseqs_maskK :
  uniq w -> cancel (fun m => Subseqs (mask_subseq (val m) w)) to_mask.
Proof.
rewrite /to_mask=> w_uniq m; case: to_mask_spec => m' /= /eqP.
exact/mask_injP.
Qed.

Definition subseqs_countMixin := CanCountMixin to_maskK.
Canonical subseqs_countType := CountType subseqs subseqs_countMixin.
Definition subseqs_finMixin := CanFinMixin to_maskK.
Canonical subseqs_finType := FinType subseqs subseqs_finMixin.

Lemma enum_subseqsE :
  perm_eq
    (enum {: subseqs})
    (undup [seq Subseqs (mask_subseq (val m) w) | m : (size w).-tuple bool]).
Proof.
apply: uniq_perm; [exact: enum_uniq | exact: undup_uniq |].
move=> [s subs] /=; rewrite mem_enum inE mem_undup.
apply/esym/mapP; have /subseqP [m /eqP szm eqs] := subs.
by exists (Tuple szm); [exact: mem_enum | exact: val_inj].
Qed.

Lemma val_enum_subseqs :
  perm_eq
    (map val (enum {: subseqs}))
    (undup [seq mask (val m) w | m : (size w).-tuple bool]).
Proof.
have /permPl -> := perm_map val enum_subseqsE.
rewrite -(undup_map_inj val_inj) -map_comp.
exact: (eq_ind _ (perm_eq _)).
Qed.

Lemma seq_masks_uniq :
  uniq w -> uniq [seq mask (val m) w | m : (size w).-tuple bool].
Proof.
move=> w_uniq; rewrite map_inj_uniq; first exact: enum_uniq.
exact/mask_injP.
Qed.

Lemma subseqs_masks_uniq :
  uniq w ->
  uniq [seq Subseqs (mask_subseq (val m) w) | m : (size w).-tuple bool].
Proof.
move /seq_masks_uniq => s_uniq.
by rewrite -(map_inj_uniq val_inj) -map_comp.
Qed.

End FinType.


Section Bigop.

Context {R : Type} {idx : R} {op : Monoid.com_law idx}.
Local Notation "1" := idx.
Local Notation "'*%M'" := op (at level 0).
Local Notation "x * y" := (op x y).
Context {T : choiceType}.

Lemma big_subseqs (F : seq T -> R) (s : seq T) :
  uniq s ->
  \big[*%M/1]_(i : subseqs s) F i =
  \big[*%M/1]_(m : (size s).-tuple bool) F (mask m s).
Proof.
move=> suniq; rewrite -big_enum.
rewrite (perm_big _ (enum_subseqsE s)) undup_id ?subseqs_masks_uniq //.
by rewrite big_map big_enum; exact: eq_bigr.
Qed.

Lemma big_subseqs_cond (P : pred (seq  T)) (F : seq T -> R) (s : seq T) :
  uniq s ->
  \big[*%M/1]_(i : subseqs s | P i) F i =
  \big[*%M/1]_(m : (size s).-tuple bool | P (mask m s)) F (mask m s).
Proof.
move=> suniq; rewrite [LHS]big_mkcond [RHS]big_mkcond.
exact: (big_subseqs (fun i => if P i then F i else 1)).
Qed.

Lemma big_subseqs0 (F : seq T -> R) :
  \big[*%M/1]_(i : subseqs [::]) F i = F [::].
Proof.
transitivity (\big[*%M/1]_(s <- [:: sub_full [::]]) F s); last by rewrite big_seq1.
apply: perm_big; apply uniq_perm => //; first exact: index_enum_uniq.
by move=> [{}s Hs]; rewrite !inE mem_index_enum -val_eqE /= -subseq0 Hs.
Qed.

Lemma big_subseqs_cons (F : seq T -> R) (a : T) (s : seq T) :
  uniq (a :: s) ->
  \big[*%M/1]_(i : subseqs (a :: s)) F i =
  \big[*%M/1]_(i : subseqs s) F (a :: i) * \big[*%M/1]_(i : subseqs s) F (i).
Proof.
move=> asuniq; have := asuniq => /= /andP [_ suniq].
rewrite !big_subseqs //.
rewrite [X in X * _](big_subseqs (fun s => F (a :: s))) //.
rewrite (bigID (fun m => tnth m ord0)) /=; congr( _ * _).
- rewrite [RHS](eq_big
                  (fun m => tnth (cons_tuple true m) ord0)
                  (fun m => F (mask (cons_tuple true m) (a :: s)))) //.
  apply: (reindex (@cons_tuple _ _ true)); exists (@behead_tuple _ _).
  + by move=> m _; apply val_inj; case: m => [[|m0 m]].
  + by move=> m; rewrite inE; case: m => [[|[|] m]]//= Hm _; exact: val_inj.
- rewrite [RHS](eq_big
                  (fun m => ~~ tnth (cons_tuple false m) ord0)
                  (fun m => F (mask (cons_tuple false m) (a :: s)))) //.
  apply: (reindex (@cons_tuple _ _ false)); exists (@behead_tuple _ _).
  + by move=> m _; apply val_inj; case: m => [[|m0 m]].
  + by move=> m; rewrite inE; case: m => [[|[|] m]]//= Hm _; exact: val_inj.
Qed.

Lemma big_subseqs_cons_cond
      (F : seq T -> R) (P : pred (seq T)) (a : T) (s : seq T) :
  uniq (a :: s) ->
  \big[*%M/1]_(i : subseqs (a :: s) | P i) F i =
  \big[*%M/1]_(i : subseqs s | P (a :: i)) F (a :: i) *
  \big[*%M/1]_(i : subseqs s | P i) F (i).
Proof.
move=> asuniq.
rewrite big_mkcond (big_subseqs_cons (fun i => if P i then F i else 1)) //.
by congr (_ * _); rewrite -big_mkcond.
Qed.

Lemma big_subseqs_undup (F : seq T -> R) (s : seq T) :
  idempotent op ->
  \big[*%M/1]_(i : subseqs s) F i =
  \big[*%M/1]_(m : (size s).-tuple bool) F (mask m s).
Proof.
move=> opid; rewrite -big_enum.
rewrite (perm_big _ (enum_subseqsE s)) big_undup //.
by rewrite big_map big_enum; exact: eq_bigr.
Qed.

Lemma big_subseqs_undup_cond (F : seq T -> R) (P : pred (seq T)) (s : seq T) :
  idempotent op ->
  \big[*%M/1]_(i : subseqs s | P i) F i =
  \big[*%M/1]_(m : (size s).-tuple bool | P (mask m s)) F (mask m s).
Proof.
move=> opid; rewrite big_mkcond /=.
by rewrite (big_subseqs_undup (fun i => if P i then F i else 1)) // big_mkcond.
Qed.

End Bigop.


(** * Relating sub sequences of [iota] and being sorted *)
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
