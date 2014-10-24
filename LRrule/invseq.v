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


Lemma perm_eq_size_uniq (T : eqType) (s1 s2 : seq T) :
  uniq s1 -> {subset s1 <= s2} -> size s2 <= size s1 -> perm_eq s1 s2.
Proof.
  move=> Hus1 Hsubs Hszleq.
  have := leq_size_perm Hus1 Hsubs Hszleq => [] [] Heq Hsz.
  apply (uniq_perm_eq Hus1); last exact Heq.
  by rewrite -(perm_uniq Heq Hsz).
Qed.

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

Lemma size_invseq s t : invseq s t -> size s = size t.
Proof.
  rewrite /invseq => /andP [] Hst Hts.
  apply/eqP; rewrite eqn_leq.
  apply/andP; split; by apply size_leq_invseq.
Qed.

Lemma linvseq_subset_iota s t : linvseq s t -> {subset iota 0 (size s) <= t}.
Proof.
  move/linvseqP => Hinv i.
  rewrite mem_iota /= add0n => Hi.
  have Heq := Hinv i Hi; rewrite -Heq.
  apply mem_nth; move: Hi; apply contraLR; rewrite -!ltnNge !ltnS => H.
  have := nth_default (size s) H.
  by rewrite Heq => ->.
Qed.

Lemma invseq_is_std s t : invseq s t -> is_std s.
Proof.
  move=> /invseq_sym Hinv; rewrite /is_std perm_eq_sym.
  apply perm_eq_size_uniq.
  - by apply iota_uniq.
  - rewrite -(size_invseq Hinv); apply linvseq_subset_iota.
    move: Hinv; by rewrite /invseq => /andP [].
  - by rewrite size_iota.
Qed.

Lemma linvseq_sizeP s t :
  linvseq s t -> size s = size t -> invseq s t.
Proof.
  move=> Hinv Hsize; rewrite /invseq; apply/andP; split; first exact Hinv.
  have Hiota := linvseq_subset_iota Hinv.
  have Htmp : size t <= size (iota 0 (size s)) by rewrite size_iota Hsize.
  have Huniq := leq_size_uniq (iota_uniq 0 (size s)) Hiota Htmp.
  have {Htmp Hiota} Hperm := perm_eq_size_uniq (iota_uniq 0 (size s)) Hiota Htmp.
  apply/linvseqP => i Hi; move: Hinv => /linvseqP Hinv.
  have:= mem_nth (size s) Hi; rewrite -(perm_eq_mem Hperm) mem_iota /= add0n => Hnth.
  have {Hinv} Heq := Hinv _ Hnth.
  have /eqP := Heq; rewrite nth_uniq //=; first by move/eqP.
  case: (ltnP (nth (size t) s (nth (size s) t i)) (size t)) => //= H.
  move: Heq; rewrite (nth_default _ H) => /eqP.
  by rewrite (gtn_eqF Hnth).
Qed.

Lemma invseq_nthE s t :
  invseq s t ->
  forall i j, i < size s -> j < size t -> (i = nth (size s) t j <-> nth (size t) s i = j).
Proof.
  move=> Hinv i j Hi Hj.
  move: Hinv; rewrite /invseq => /andP [] /linvseqP Hst /linvseqP Hts.
  split => H.
  + have:= Hts j Hj; by rewrite H.
  + have:= Hst i Hi; by rewrite H.
Qed.

Definition invstd s := mkseq (fun i => index i s) (size s).

Lemma is_std_invseq s : is_std s -> invseq s (invstd s).
Proof.
  move=> Hstd; rewrite /invseq; apply/andP; split; apply/linvseqP; rewrite size_mkseq => i Hi.
  - rewrite nth_mkseq.
    + apply (index_uniq _ Hi). by apply std_uniq.
    + by rewrite -(mem_std _ Hstd) mem_nth.
  - rewrite nth_mkseq //=; apply nth_index; by rewrite (mem_std _ Hstd).
Qed.

Lemma invseqE s t1 t2 : invseq s t1 -> invseq s t2 -> t1 = t2.
Proof.
  move=> Hinv1 Hinv2.
  have Hsz: size t1 = size t2 by rewrite -(size_invseq Hinv1) -(size_invseq Hinv2).
  apply (eq_from_nth (x0 := size s) Hsz) => i Hi1.
  have:= Hi1; rewrite Hsz => Hi2.
  have := Hinv1; rewrite /invseq => /andP [] _ Ht1s.
  have Hnth1 := linvseq_ltn_szt Ht1s Hi1.
  rewrite (invseq_nthE Hinv2 Hnth1 Hi2).
  rewrite -Hsz.
  by move: Ht1s => /linvseqP ->.
Qed.

Section KsuppInj.

Variable s t : seq nat.
Hypothesis Hinv : invseq s t.


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

Lemma std_rcons_shiftinv t tn :
  is_std (rcons t tn) -> std t = map (shiftinv_pos tn) t.
Proof.
  move=> H; apply /eqP/stdP; constructor.
  - rewrite /is_std size_map perm_eq_sym.
    apply perm_eq_size_uniq.
    + by apply iota_uniq.
    + move=> i; move: H; rewrite /is_std => /perm_eq_mem Hperm.
      case (ltnP i tn) => Hi.
      * have {2}-> : i = shiftinv_pos tn i by rewrite /shiftinv_pos Hi.
        move=> Hiota; apply map_f; have:= Hperm i; move: Hiota.
        rewrite !mem_iota /= !add0n size_rcons ltnS => /ltnW ->.
        by rewrite mem_rcons inE (ltn_eqF Hi) /= => ->.
      * have {2}-> : i = shiftinv_pos tn i.+1.
          by rewrite /shiftinv_pos ltnNge (leq_trans Hi (leqnSn _)).
        move=> Hiota; apply map_f; have:= Hperm i.+1; move: Hiota.
        rewrite !mem_iota /= !add0n size_rcons ltnS => ->.
        rewrite mem_rcons inE.
        move: Hi; rewrite -ltnS => /ltn_eqF; by rewrite eq_sym => -> /= ->.
    + by rewrite size_map size_iota.
  - apply/eq_invP; split; first by rewrite size_map.
    move => i j /andP [] Hij Hj.
    rewrite (nth_map (inhabitant nat_ordType)); last exact (leq_ltn_trans Hij Hj).
    rewrite (nth_map (inhabitant nat_ordType)); last exact Hj.
    rewrite !leqXnatE.
    apply/(sameP idP); apply(iffP idP).
    + apply contraLR; rewrite -!ltnNge !ltn_neqAle => /andP [] Hneq /shiftinv_pos_incr ->.
      rewrite andbT.
      have:= (std_uniq H); rewrite rcons_uniq => /andP [] Htn Huniqt.
      move: Hneq; set xi := nth _ _ i; set xj := nth _ _ j.
      rewrite /shiftinv_pos.
      case (ltnP xi tn) => Hxi; case (ltnP xj tn) => Hxj.
      * by apply.
      * apply contra => /eqP H1; move: Hxj Hxi; rewrite -H1 {H1 i xi Hij} => H1 H2.
        exfalso; have Hneq : xj != tn.
          move: Htn; apply contra => /eqP <-; by rewrite /xj mem_nth.
        move: H2; have {H1 Hneq} : tn < xj by rewrite ltn_neqAle eq_sym Hneq H1.
        case: xj => [//= | x] /=.
        rewrite ltnS => H1 H2; have := leq_ltn_trans H1 H2.
        by rewrite ltnn.
      * apply contra => /eqP H1; move: Hxj Hxi.
        have {Hij Hj} Hi := leq_ltn_trans Hij Hj; rewrite H1 {H1 j xj} => H1 H2.
        exfalso; have Hneq : xi != tn.
          move: Htn; apply contra => /eqP <-; by rewrite /xi mem_nth.
        have {H2 Hneq} : tn < xi by rewrite ltn_neqAle eq_sym Hneq H2.
        case: xi H1 => [//= | x] /=.
        rewrite ltnS => H1 H2; have := leq_ltn_trans H2 H1.
        by rewrite ltnn.
      * apply contra => /eqP H1.
        have Hi := leq_ltn_trans Hij Hj.
        have {Hxi} : tn < xi.
          rewrite ltn_neqAle Hxi andbT.
          move: Htn; apply contra => /eqP ->; by rewrite /xi mem_nth.
        have {Hxj} : tn < xj.
          rewrite ltn_neqAle Hxj andbT.
          move: Htn; apply contra => /eqP ->; by rewrite /xj mem_nth.
        case: xi H1 => [//= | xi] /=.
        by case: xj => [//= | xj] /= ->.
    + by apply shiftinv_pos_incr.
Qed.

Lemma posbig_invseq s0 s t tn :
  invseq (s0 :: s) (rcons t tn) -> posbig (s0 :: s) = tn.
Proof.
  move => Hinv; have:= Hinv; rewrite /invseq => /andP [] Hst Hts.
  have Hpos := (posbig_size_cons s0 s).
  have Hszt : size t < size (rcons t tn) by rewrite size_rcons.
  have:= linvseq_ltn_szt Hts Hszt; rewrite nth_rcons ltnn eq_refl (size_invseq Hinv) => Htn.
  have:= invseq_nthE Hinv Hpos Hszt.
  rewrite (nth_any _ (inhabitant _) Hpos) nth_posbig.
  rewrite nth_rcons ltnn eq_refl => ->.
  rewrite (std_max (invseq_is_std Hinv)).
  have:= (size_invseq Hinv); rewrite size_rcons /= => /eqP; by rewrite eqSS => /eqP.
Qed.

Lemma nth_std_pos s i x :
  is_std s -> i < size s -> i != posbig s -> nth x s i < (size s).-1.
Proof.
  case: s => [//= | s0 s] Hstd Hi Hipos.
  rewrite [nth _ _ _ < _]ltn_neqAle -ltnS; apply/andP; split.
  - rewrite /= -(std_max Hstd) -(nth_posbig s0 s).
    rewrite (nth_any x (inhabitant nat_ordType) Hi).
    by rewrite (nth_uniq _ Hi (posbig_size_cons s0 s) (std_uniq Hstd)).
  - have -> :  (size (s0 :: s)).-1.+1 = size (s0 :: s) by [].
    rewrite -(mem_std _ Hstd); by apply mem_nth.
Qed.

Lemma linvseqK s0 s t tn :
  invseq (s0 :: s) (rcons t tn) -> linvseq (rembig (s0 :: s)) (std t).
Proof.
  move=> Hinv.
  rewrite (std_rcons_shiftinv (invseq_is_std (invseq_sym Hinv))).
  have := Hinv; rewrite /invseq => /andP [] /linvseqP Hst /linvseqP Hts.
  apply/linvseqP => i Hi.
  rewrite (nth_any _ (inhabitant nat_ordType) Hi) -nth_rembig.
  rewrite (nth_map (size (s0 :: s))); first last.
    set si := shift_pos _ _; have Hsipos : si != posbig (s0 :: s).
      rewrite /si /shift_pos; case: (ltnP i (posbig (s0 :: s))).
      + by move /ltn_eqF ->.
      + by rewrite -ltnS => /gtn_eqF ->.
    have Hsi : si < (size (s0 :: s)).
      rewrite /si /shift_pos; case: (ltnP i (posbig (s0 :: s))) => H.
      + apply (ltn_trans Hi); by rewrite size_rembig /=.
      + apply (leq_trans Hi); by rewrite size_rembig /=.
    apply (leq_trans (nth_std_pos _ (invseq_is_std Hinv) Hsi Hsipos)).
    have:= size_invseq Hinv; rewrite size_rcons /= => /eqP.
    by rewrite eqSS => /eqP ->.
  rewrite (posbig_invseq Hinv).
  have Hpos : shift_pos tn i < size (s0 :: s).
    move: Hi; rewrite /shift_pos size_rembig /=.
    case (i < tn); last by [].
    move/leq_trans; by apply.
  rewrite (nth_any (inhabitant _) (size (rcons t tn)) Hpos).
  move: (Hst _ Hpos); rewrite nth_rcons.
  set x := nth _ _ _; have -> : x < size t.
    rewrite /x.
    have -> : size t = (size (s0 :: s)).-1 by rewrite (size_invseq Hinv) size_rcons.
    apply (nth_std_pos (size (rcons t tn)) (invseq_is_std Hinv) Hpos).
    rewrite (posbig_invseq Hinv) /shift_pos.
    case (ltnP i tn); first by move /ltn_eqF ->.
    by rewrite -ltnS => /gtn_eqF ->.
  move ->; by rewrite shift_posK.
Qed.

Lemma invseqK s0 s t tn :
  invseq (s0 :: s) (rcons t tn) -> invseq (rembig (s0 :: s)) (std t).
Proof.
  move=> Hinv; apply linvseq_sizeP; first by apply (linvseqK Hinv).
  rewrite size_rembig /= size_std.
  have := size_invseq Hinv; rewrite size_rcons /= => /eqP; by rewrite eqSS => /eqP ->.
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

  have := eq_refl (sumn (shape (RSmap t').1)).
  rewrite {1}RSmapE (shape_RSmap_eq t') shape_rowseq_eq_size HRSt /= => /eqP <-.
  have := (eqP (size_RS t')); rewrite /size_tab => ->.
  move: Hsize; rewrite Ht Hn size_rcons => /eqP; rewrite eqSS => /eqP <-.
  have := (invseq_is_std Hinv); rewrite Hs => /std_max ->.
  move: Hn; rewrite Hs /= => /eqP; by rewrite eqSS => /eqP <-.
Qed.

Corollary invseqRSE s t :
  invseq s t -> RStabmap s = ((RStabmap t).2, (RStabmap t).1).
Proof.
  move=> Hinv.
  rewrite -(invseqRSPQE Hinv) (invseqRSPQE (invseq_sym Hinv)).
  by case (RStabmap s).
Qed.

Corollary invstdRSE s :
  is_std s -> let (P, Q) := RStabmap (invstd s) in RStabmap s = (Q, P).
Proof.
  move=> Hstd.
  case H : (RStabmap (invstd s)) => [P Q].
  by rewrite (invseqRSE (is_std_invseq Hstd)) H.
Qed.

Corollary RSTabmapstdE (T : ordType) (w : seq T) :
  (RStabmap (invstd (std w))).1 = (RStabmap (std w)).2.
Proof.
  have := invstdRSE (std_is_std w).
  by case (RStabmap (invstd (std w))) => [P Q] /= ->.
Qed.

Corollary RSinvstdE (T : ordType) (w : seq T) :
  RS (invstd (std w)) = (RStabmap w).2.
Proof.
  rewrite -RStabmapE RSTabmapstdE.
  rewrite /RStabmap; set Ls := LHS; set Rs := RHS.
  have {Ls} -> : Ls = stdtab_of_yam (RSmap (std w)).2 by rewrite /Ls; case: RSmap.
  have {Rs} -> : Rs = stdtab_of_yam (RSmap w).2 by rewrite /Rs; case: RSmap.
  congr (stdtab_of_yam _).
  by apply RSmap_std.
Qed.

End InvSeq.
