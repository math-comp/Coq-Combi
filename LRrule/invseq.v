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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm fingroup path.

Require Import subseq partition permuted ordtype std stdtab ordcast.
Require Import schensted congr plactic green greeninv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section InvSeq.

Implicit Type n : nat.

Definition linvseq s :=
  [fun t => all (fun i => nth (size s) t (nth (size t) s i) == i) (iota 0 (size s))].
Definition invseq s t := linvseq s t && linvseq t s.

Lemma linvseqP s t :
  reflect (forall i, i < size s -> nth (size s) t (nth (size t) s i) = i) (linvseq s t).
Proof.
  rewrite /linvseq; apply (iffP idP) => /=.
  - move=> /allP H i Hi.
    apply /eqP; apply H; by rewrite mem_iota.
  - move=> H; apply /allP => /= i; rewrite mem_iota /= add0n => Hi.
    by rewrite (H i Hi).
Qed.

Lemma invseq_sym s t : invseq s t -> invseq t s.
Proof. by rewrite /invseq andbC. Qed.

Lemma size_all_leq n t : (forall i, i < n -> i \in t) -> n <= size t.
Proof.
  move=> H.
  pose s := undup (filter (gtn n) t).
  have Hperm : perm_eq s (iota 0 n).
    apply uniq_perm_eq.
    + by apply undup_uniq.
    + by apply iota_uniq.
    + move=> i; rewrite /s mem_undup mem_iota /= add0n mem_filter /=.
      apply/(sameP idP); apply(iffP idP).
      * move=> Hi; by rewrite Hi (H i Hi).
      * by move/andP => [] ->.
  have -> : n = size (iota 0 n) by rewrite size_iota.
  rewrite -(perm_eq_size Hperm) /s.
  apply (leq_trans (size_undup _)).
  rewrite size_filter; by apply count_size.
Qed.

Lemma linvseq_ltn_szt s t :
  linvseq s t -> forall i, i < size s -> nth (size t) s i < size t.
Proof.
  move/linvseqP => Hinv i Hi.
  have:= Hinv i Hi.
  case: (ltnP (nth (size t) s i) (size t)) => //= Habs.
  rewrite (nth_default _ Habs) => H.
  by move: Hi; rewrite H ltnn.
Qed.

Lemma size_leq_invseq s t : linvseq s t -> size s <= size t.
Proof.
  move=> Hinv; have:= Hinv => /linvseqP H.
  apply size_all_leq => i Hi.
  have {H} H := H i Hi.
  rewrite -H; apply mem_nth.
  by apply linvseq_ltn_szt.
Qed.

Section KsuppInj.

Variable s t : seq nat.
Hypothesis Hinv : invseq s t.

Lemma size_invseq : size s = size t.
Proof.
  have:= Hinv; rewrite /invseq => /andP [] Hst Hts.
  apply/eqP; rewrite eqn_leq.
  apply/andP; split; by apply size_leq_invseq.
Qed.

Let Hinvst : linvseq s t.
Proof. have:= Hinv; by rewrite /invseq => /andP []. Qed.
Let Hinvts : linvseq t s.
Proof. have:= Hinv; by rewrite /invseq => /andP []. Qed.

Definition val2pos := fun (i : 'I_(size s)) => Ordinal (linvseq_ltn_szt Hinvst (ltn_ord i)).

Lemma val2posE : val \o val2pos =1 nth (size t) s.
Proof. by []. Qed.

Lemma val2pos_inj : injective val2pos.
Proof.
  move: Hinvst => /linvseqP Hv.
  move=> i j; rewrite /val2pos; set posi := Ordinal _ => Heq.
  apply/val_inj => /=.
  rewrite -(Hv i (ltn_ord i)) -(Hv j (ltn_ord j)); congr (nth _ _ _).
  have:= erefl (val posi); by rewrite {2}Heq /=.
Qed.

Lemma mem_mem n (st : {set 'I_n}) : mem (mem st) =1 mem st.
Proof. by []. Qed.

Let leqtransi : transitive leq.
Proof. move=> i j k H1 H2; by apply (leq_trans H1 H2). Qed.

Lemma val2pos_enum (p : {set 'I_(size s)}) :
  (* Hypothesis : val2pos sorted in p *)
  sorted (leqX _) [seq tnth (in_tuple s) i | i <- enum (mem p)] ->
  enum (mem [set val2pos x | x in p]) = [seq val2pos x | x <- enum p].
Proof.
  rewrite /enum_mem /= (eq_filter (mem_mem _)) -!enumT /= => H.
  apply (inj_map val_inj).
  rewrite -map_comp (eq_map val2posE).
  rewrite (eq_filter (mem_mem _)).
  move: H; have /eq_map -> : (tnth (in_tuple s)) =1 (nth (size t) s).
    move=> i /=; by apply tnth_nth.
  set l1 := (X in sorted _ X); set l := (X in _ = X).
  have {l1} -> : l1 = l by [].
  move=> H; apply (eq_sorted (leT := leq)).
  - exact leqtransi.
  - move=> i j H1; apply/eqP; by rewrite eqn_leq.
  - apply (subseq_sorted leqtransi (s2 := map val (enum 'I_(size t)))).
    + apply map_subseq; by apply filter_subseq.
    + rewrite val_enum_ord; by apply iota_sorted.
  - move: H; rewrite /sorted; case: l => [//= | l0 l].
    by rewrite (eq_path (e' := leq)); last by move=> i j /=; rewrite leqXnatE.
  - apply uniq_perm_eq.
    + rewrite map_inj_in_uniq.
      * apply filter_uniq; by apply enum_uniq.
      * move=> i j Hi _ /=; by apply val_inj.
    + rewrite map_inj_in_uniq.
      * apply filter_uniq; by apply enum_uniq.
      * move=> i j Hij _ /= HH; apply val_inj.
        have:= Hinvst => /linvseqP Heq.
        by rewrite /= -(Heq _ (ltn_ord i)) -(Heq _ (ltn_ord j)) HH.
    + rewrite /l; move => i /=; apply/(sameP idP); apply(iffP idP).
      * move/mapP => [] j; rewrite mem_filter => /andP [] /= Hj _ -> {i}.
        apply/mapP; exists (Ordinal (linvseq_ltn_szt Hinvst (ltn_ord j))); last by [].
        rewrite mem_filter; apply /andP; split => /=; last by rewrite mem_enum.
        rewrite /val2pos; by rewrite mem_imset.
      * move/mapP => [] j; rewrite mem_filter => /andP [] /= /imsetP [] i' Hi' -> _ -> {i}.
        apply/mapP; exists i'; last by [].
        rewrite mem_filter /= Hi' /=; by rewrite mem_enum.
Qed.

Lemma ksupp_inj_invseq k : ksupp_inj (leqX _) (leqX _) k s t.
Proof.
  rewrite /ksupp_inj /ksupp => ks /and3P [] Hsz Htriv /forallP Hall.
  exists [set val2pos @: (p : {set 'I_(size s)}) | p in ks].
  apply/and4P; split.
  + rewrite /=; apply /eqP; apply size_cover_inj; by apply val2pos_inj.
  + apply (@leq_trans #|ks|); last exact Hsz.
    by apply leq_imset_card.
  + apply imset_trivIset; last exact Htriv.
    by apply val2pos_inj.
  + apply/forallP => ptmp; apply/implyP => /imsetP [] p Hp -> {ptmp}.
    have:= Hall p; rewrite Hp /= /extractpred.
(**)
   move/val2pos_enum ->; rewrite -map_comp /=.
   set f := (X in map X _); have {f} /eq_map -> : f =1 id.
     rewrite /f => i /=.
     rewrite (tnth_nth (size s)) /=.
     by have:= Hinvst => /linvseqP ->.
   set l := map _ _; have : subseq l [seq val x | x  <- enum 'I_(size s)].
     apply map_subseq; rewrite /enum_mem.
     set pr := (X in subseq _ (filter X _)).
     have /eq_filter -> : pr =1 predT by [].
     rewrite filter_predT; by apply filter_subseq.
   move /subseq_sorted; apply; first by move=> a b c H1 H2; by apply (leqX_trans H1 H2).
   rewrite val_enum_ord.
   apply iota_sorted.
Qed.

End KsuppInj.

Lemma green_invseq s t k : invseq s t -> greenRow s k = greenRow t k.
Proof.
  move=> Hst; have Hts := invseq_sym Hst.
  apply /eqP; rewrite eqn_leq; apply/andP; split;
    apply leq_green; by apply ksupp_inj_invseq.
Qed.

Lemma shape_invseq s t : invseq s t -> shape (RS s) = shape (RS t).
Proof.
  move=> Hinv; apply greenRow_tab_eq_shape; try apply is_tableau_RS.
  move=> k.
  rewrite -(greenRow_invar_plactic (congr_RS s) k).
  rewrite -(greenRow_invar_plactic (congr_RS t) k).
  by apply green_invseq.
Qed.

Lemma invseqK s0 s t tn :
  invseq (s0 :: s) (rcons t tn) -> invseq (rembig (s0 :: s)) (std t).
Proof.
  rewrite /invseq => /andP [] /linvseqP Hst /linvseqP Hts.
  apply/andP; split; apply/linvseqP => i.
  + admit.
  + admit.
Qed.

Theorem invseqRSPQE s t :
  invseq s t -> (RStabmap s).1 = (RStabmap t).2.
Proof.
  rewrite /RStabmap /= => Hinv.
  case HRSs : (RSmap s) => [Ps Qs] /=.
  have {HRSs Ps Qs} -> : Ps = RS s by rewrite -RSmapE HRSs.
  case HRSt : (RSmap t) => [Pt Qt] /=.
  have {HRSt Pt Qt}-> : Qt = (RSmap t).2 by rewrite HRSt.
  move Hn: (size s) => n.
  have Hsize := size_invseq Hinv.
  elim: n s t Hn Hinv Hsize => [/= | n IHn] s t Hn Hinv Hsize.
    by move: Hn Hsize => /eqP/nilP Hs; subst s => /= /esym/eqP/nilP -> /=.
  have:= shape_invseq Hinv.
  rewrite -!RSmapE [shape (RSmap t).1]shape_RSmap_eq !RSmapE.
  case Hs : s Hn Hinv Hsize => [//= | s0 s']; rewrite -Hs => Hn Hinv Hsize.
  rewrite Hs (rembig_RS_last_big s0 s') shape_append_nth -Hs.
  set irow := last_big _ _.
  move=> Hshape.
  have Hszrem : size (rembig (s0 :: s')) = n.
    by move: Hn => /eqP; rewrite size_rembig Hs /= eqSS => /eqP.
  case/lastP Ht : t => [//= | t' tn].
    exfalso; move: Hsize; by rewrite Hn Ht.
  have:= Hinv; rewrite Hs Ht => /invseqK Hrec.
  have Hsize' : size (rembig (s0 :: s')) = size (std t').
    by rewrite size_rembig -Hs Hsize Ht size_rcons /std size_std_rec.
  have {IHn} IHn := IHn _ _ Hszrem Hrec Hsize'.
  move: Hshape; rewrite -Hs Ht /RSmap rev_rcons /=.
  rewrite -[RSmap_rev (rev t')]/(RSmap t').
  case HRSt : (RSmap t') => [t0 rowt'].
  case Hins : (instabnrow t0 tn) => [tr irowt'] /=.
  move: IHn; rewrite -Hs RSmap_std HRSt /= => ->.
  rewrite shape_stdtab_of_yam => /incr_nth_inj ->.
  congr (append_nth _ _ _).
  admit.
Qed.


End InvSeq.
