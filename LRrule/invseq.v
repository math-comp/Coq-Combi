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

Require Import tools partition Yamanouchi ordtype std stdtab ordcast.
Require Import Schensted congr plactic Greene Greene_inv stdplact.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
Proof. move=> i j k H1 H2; by apply: (leq_trans H1 H2). Qed.

Lemma val2pos_enum (p : {set 'I_(size s)}) :
  (* Hypothesis : val2pos sorted in p *)
  sorted leqX [seq tnth (in_tuple s) i | i <- enum (mem p)] ->
  enum (mem [set val2pos x | x in p]) = [seq val2pos x | x <- enum p].
Proof.
  rewrite /enum_mem /= (eq_filter (mem_mem _)) -!enumT /= => H.
  apply: (inj_map val_inj).
  rewrite -map_comp (eq_map val2posE).
  rewrite (eq_filter (mem_mem _)).
  move: H; have /eq_map -> : (tnth (in_tuple s)) =1 (nth (size t) s).
    move=> i /=; by apply: tnth_nth.
  set l1 := (X in sorted _ X); set l := (X in _ = X).
  have {l1} -> : l1 = l by [].
  move=> H; apply: (eq_sorted (leT := leq)).
  - exact leqtransi.
  - move=> i j H1; apply/eqP; by rewrite eqn_leq.
  - apply: (subseq_sorted leqtransi (s2 := map val (enum 'I_(size t)))).
    + apply: map_subseq; by apply: filter_subseq.
    + rewrite val_enum_ord; by apply: iota_sorted.
  - move: H; rewrite /sorted; case: l => [//= | l0 l].
    by rewrite (eq_path (e' := leq)); last by move=> i j /=; rewrite leqXnatE.
  - apply: uniq_perm_eq.
    + rewrite map_inj_in_uniq.
      * apply: filter_uniq; by apply: enum_uniq.
      * move=> i j Hi _ /=; by apply: val_inj.
    + rewrite map_inj_in_uniq.
      * apply: filter_uniq; by apply: enum_uniq.
      * move=> i j Hij _ /= HH; apply: val_inj.
        have:= Hinvst => /linvseqP Heq.
        by rewrite /= -(Heq _ (ltn_ord i)) -(Heq _ (ltn_ord j)) HH.
    + rewrite /l; move => i /=; apply/(sameP idP); apply(iffP idP).
      * move/mapP => [] j; rewrite mem_filter => /andP [] /= Hj _ -> {i}.
        apply/mapP; exists (Ordinal (linvseq_ltn_szt Hinvst (ltn_ord j))); last by [].
        rewrite mem_filter; apply/andP; split => /=; last by rewrite mem_enum.
        rewrite /val2pos; by rewrite mem_imset.
      * move/mapP => [] j; rewrite mem_filter => /andP [] /= /imsetP [] i' Hi' -> _ -> {i}.
        apply/mapP; exists i'; last by [].
        rewrite mem_filter /= Hi' /=; by rewrite mem_enum.
Qed.

Lemma ksupp_inj_invseq k : ksupp_inj leqX leqX k s t.
Proof.
  rewrite /ksupp_inj /ksupp => ks /and3P [] Hsz Htriv /forallP Hall.
  exists [set val2pos @: (p : {set 'I_(size s)}) | p in ks].
  apply/and4P; split.
  + rewrite /=; apply/eqP; apply: size_cover_inj; by apply: val2pos_inj.
  + apply: (@leq_trans #|ks|); last exact Hsz.
    by apply: leq_imset_card.
  + apply: imset_trivIset; last exact Htriv.
    by apply: val2pos_inj.
  + apply/forallP => ptmp; apply/implyP => /imsetP [] p Hp -> {ptmp}.
    have:= Hall p; rewrite Hp /= /extractpred.
    move/val2pos_enum ->; rewrite -map_comp /=.
    set f := (X in map X _); have {f} /eq_map -> : f =1 id.
      rewrite /f => i /=.
      rewrite (tnth_nth (size s)) /=.
      by have:= Hinvst => /linvseqP ->.
    set l := map _ _; have : subseq l [seq val x | x  <- enum 'I_(size s)].
      apply: map_subseq; rewrite /enum_mem.
      set pr := (X in subseq _ (filter X _)).
      have /eq_filter -> : pr =1 predT by [].
      rewrite filter_predT; by apply: filter_subseq.
    move /subseq_sorted; apply; first by move=> a b c H1 H2; by apply: (leqX_trans H1 H2).
    rewrite val_enum_ord.
    apply: iota_sorted.
Qed.

End KsuppInj.

Lemma Greene_invseq s t k : invseq s t -> Greene_row s k = Greene_row t k.
Proof.
  move=> Hst; have Hts := invseq_sym Hst.
  apply/eqP; rewrite eqn_leq; apply/andP; split;
    apply: leq_Greene; by apply: ksupp_inj_invseq.
Qed.

Lemma shape_invseq s t : invseq s t -> shape (RS s) = shape (RS t).
Proof.
  move=> Hinv; apply: Greene_row_tab_eq_shape; try apply: is_tableau_RS.
  move=> k.
  rewrite -(Greene_row_invar_plactic (congr_RS s) k).
  rewrite -(Greene_row_invar_plactic (congr_RS t) k).
  by apply: Greene_invseq.
Qed.

Lemma std_rcons_shiftinv t tn :
  is_std (rcons t tn) -> std t = map (shiftinv_pos tn) t.
Proof.
  move=> H; apply/eqP/stdP; constructor.
  - rewrite /is_std size_map perm_eq_sym.
    apply: perm_eq_size_uniq.
    + by apply: iota_uniq.
    + move=> i; move: H; rewrite /is_std => /perm_eq_mem Hperm.
      case (ltnP i tn) => Hi.
      * have {2}-> : i = shiftinv_pos tn i by rewrite /shiftinv_pos Hi.
        move=> Hiota; apply: map_f; have:= Hperm i; move: Hiota.
        rewrite !mem_iota /= !add0n size_rcons ltnS => /ltnW ->.
        by rewrite mem_rcons inE (ltn_eqF Hi) /= => ->.
      * have {2}-> : i = shiftinv_pos tn i.+1.
          by rewrite /shiftinv_pos ltnNge (leq_trans Hi (leqnSn _)).
        move=> Hiota; apply: map_f; have:= Hperm i.+1; move: Hiota.
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
    + apply: contraLR; rewrite -!ltnNge !ltn_neqAle => /andP [] Hneq /shiftinv_pos_incr ->.
      rewrite andbT.
      have:= (std_uniq H); rewrite rcons_uniq => /andP [] Htn Huniqt.
      move: Hneq; set xi := nth _ _ i; set xj := nth _ _ j.
      rewrite /shiftinv_pos.
      case (ltnP xi tn) => Hxi; case (ltnP xj tn) => Hxj.
      * by apply.
      * apply: contra => /eqP H1; move: Hxj Hxi; rewrite -H1 {H1 i xi Hij} => H1 H2.
        exfalso; have Hneq : xj != tn.
          move: Htn; apply: contra => /eqP <-; by rewrite /xj mem_nth.
        move: H2; have {H1 Hneq} : tn < xj by rewrite ltn_neqAle eq_sym Hneq H1.
        case: xj => [//= | x] /=.
        rewrite ltnS => H1 H2; have := leq_ltn_trans H1 H2.
        by rewrite ltnn.
      * apply: contra => /eqP H1; move: Hxj Hxi.
        have {Hij Hj} Hi := leq_ltn_trans Hij Hj; rewrite H1 {H1 j xj} => H1 H2.
        exfalso; have Hneq : xi != tn.
          move: Htn; apply: contra => /eqP <-; by rewrite /xi mem_nth.
        have {H2 Hneq} : tn < xi by rewrite ltn_neqAle eq_sym Hneq H2.
        case: xi H1 => [//= | x] /=.
        rewrite ltnS => H1 H2; have := leq_ltn_trans H2 H1.
        by rewrite ltnn.
      * apply: contra => /eqP H1.
        have Hi := leq_ltn_trans Hij Hj.
        have {Hxi} : tn < xi.
          rewrite ltn_neqAle Hxi andbT.
          move: Htn; apply: contra => /eqP ->; by rewrite /xi mem_nth.
        have {Hxj} : tn < xj.
          rewrite ltn_neqAle Hxj andbT.
          move: Htn; apply: contra => /eqP ->; by rewrite /xj mem_nth.
        case: xi H1 => [//= | xi] /=.
        by case: xj => [//= | xj] /= ->.
    + by apply: shiftinv_pos_incr.
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
    rewrite -(mem_std _ Hstd); by apply: mem_nth.
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
      + apply: (ltn_trans Hi); by rewrite size_rembig /=.
      + apply: (leq_trans Hi); by rewrite size_rembig /=.
    apply: (leq_trans (nth_std_pos _ (invseq_is_std Hinv) Hsi Hsipos)).
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
    apply: (nth_std_pos (size (rcons t tn)) (invseq_is_std Hinv) Hpos).
    rewrite (posbig_invseq Hinv) /shift_pos.
    case (ltnP i tn); first by move /ltn_eqF ->.
    by rewrite -ltnS => /gtn_eqF ->.
  move ->; by rewrite shift_posK.
Qed.

Lemma invseqK s0 s t tn :
  invseq (s0 :: s) (rcons t tn) -> invseq (rembig (s0 :: s)) (std t).
Proof.
  move=> Hinv; apply: linvseq_sizeP; first by apply: (linvseqK Hinv).
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
  rewrite -/(RSmap t').
  case HRSt : (RSmap t') => [t0 rowt'].
  case Hins : (instabnrow t0 tn) => [tr irowt'] /=.
  move: IHn; rewrite -Hs RSmap_std HRSt /= => ->.
  rewrite shape_stdtab_of_yam => /incr_nth_inj ->.
  congr (append_nth _ _ _).

  have := eq_refl (sumn (shape (RSmap t').1)).
  rewrite {1}RSmapE (shape_RSmap_eq t') evalseq_eq_size HRSt /= => /eqP <-.
  rewrite -/(size_tab (RS t')) size_RS.
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
  by rewrite (invseqRSE (invseq_invstd Hstd)) H.
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
  by apply: RSmap_std.
Qed.

Section Test.

  Let u := [:: 4;1;2;2;5;3].
  Let v := [:: 0;4;3;3].

  Goal std u = [:: 4; 0; 1; 2; 5; 3].
  Proof. compute; by apply: erefl. Qed.

  Goal invstd (std u) = filter (gtn (size u)) (invstd (std (u ++ v))).
  Proof. compute; by apply: erefl. Qed.

End Test.

