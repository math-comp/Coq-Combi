(** * Combi.LRrule.stdplact : Plactic congruences and standardization *)
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
(** * Plactic congruences and standardization

The goal of this file is to show a few important properties of plactic
congruence related to standardisation.

The first one is easy: it says that standardization preserve plactic congruence.
This is Theorem [std_plact] and is stated as [u =Pl v -> std u =Pl std v.]

The next series of results relates the result of the RS map applied on
[u] and [std u]:
- the insertion tableau have the same shape: Theorem [shape_RS_std];
- the recording tableau are equal: Theorem [RSmap_std] and [RStabmap_std].

And finally, inverting a standard word amount to exchange the insertion and
the recording tableaux: Theorem [invseqRSPQE], and Corollaries [invseqRSE],
[invstdRSE], [RSTabmapstdE] and [RSinvstdE].
 *************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype finfun fintype choice.
From mathcomp Require Import seq tuple finset perm fingroup path order.

Require Import tools combclass ordcast partition Yamanouchi ordtype std tableau.
Require Import stdtab sorted Schensted congr plactic Greene Greene_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.


(** ** Plactic congruence and standardization *)
Section StdRS.

Context {disp : unit} {Alph : inhOrderType disp}.
Implicit Type s u v w : seq Alph.
Implicit Type p : seq nat.
Implicit Type t : seq (seq Alph).

Lemma std_plact1 (u v1 w v2 : seq Alph) :
  v2 \in plact1 v1 -> std (u ++ v1 ++ w) =Pl std (u ++ v2 ++ w).
Proof using.
move/plact1P => [a] [b] [c] [Habc -> ->].
have:= std_cutabc u w a c b => [] [U] [V] [A] [C] [B] [Hsz Hstd].
have Hac : (a < c)%O by move: Habc => /andP []; apply: le_lt_trans.
rewrite Hstd (std_transp Hac Hsz Hstd) -[[:: C; A] ++ B :: V]/([:: C; A; B] ++ V).
apply: plact_catr; apply: plact_catl.
apply: rule_gencongr => /=.
suff -> : (A <= B < C)%O by rewrite inE eq_refl.
have:= eq_inv_std (u ++ [:: a; c; b] ++ w).
rewrite Hstd {Hstd} => /eq_invP [Hsize Hinv].
have:= Hinv (size u) (size u).+2.
set Hyp := (X in (X -> _ ) -> _) => Hinvab.
have {Hyp} /Hinvab : Hyp.
  rewrite /Hyp (leq_trans (leqnSn _) (leqnSn _)) /= size_cat /=.
  by rewrite -2!addSnnS -{1}[(size u).+2]addn0 ltn_add2l.
rewrite {3 4}Hsz !nth_sizeu !nth_sizeu2 => <-.
move/(_ (size u).+1 (size u).+2): Hinv.
set Hyp := (X in (X -> _ ) -> _) => Hinvbc.
have {Hyp}/Hinvbc : Hyp.
  rewrite /Hyp (ltn_trans (ltnSn _) (ltnSn _)) /= size_cat /=.
  by rewrite -2!addSnnS -{1}[(size u).+2]addn0 ltn_add2l.
rewrite {3 4}Hsz !nth_sizeu1 !nth_sizeu2 ltNge => <-.
by rewrite -ltNge.
Qed.


Lemma std_plact2 (u v1 w v2 : seq Alph) :
  v2 \in plact2 v1 -> std (u ++ v1 ++ w) =Pl std (u ++ v2 ++ w).
Proof using.
have reorg3 (T : eqType) (U W : seq T) b a c :
  U ++ [:: b; a; c] ++ W = (U ++ [:: b]) ++ [:: a; c] ++ W by rewrite -catA.
move/plact2P => [a] [b] [c] [Habc -> ->].
have:= std_cutabc u w b a c => [] [U] [W] [B] [A] [C] [Hsz].
have Hac : (a < c)%O by move: Habc => /andP []; apply: lt_le_trans.
rewrite !reorg3.
have Hsz1 : size (u ++ [:: b]) = size (U ++ [:: B]) by rewrite !size_cat Hsz.
move=> Hstd; rewrite Hstd (std_transp Hac Hsz1 Hstd).
rewrite -!reorg3.
apply: plact_catr; apply: plact_catl.
apply: rule_gencongr => /=.
suff -> : (A < B <= C)%O by rewrite !mem_cat inE eq_refl /= !orbT.
rewrite -!reorg3  in Hstd.
have:= eq_inv_std (u ++ [:: b; a; c] ++ w).
rewrite Hstd {Hstd} => /eq_invP [Hsize Hinv].
have:= Hinv (size u) (size u).+2.
set Hyp := (X in (X -> _ ) -> _) => Hinvab.
have {Hyp}/Hinvab : Hyp.
  rewrite /Hyp (leq_trans (leqnSn _) (leqnSn _)) /= size_cat /=.
  by rewrite -2!addSnnS -{1}[(size u).+2]addn0 ltn_add2l.
rewrite {3 4}Hsz !nth_sizeu !nth_sizeu2 => <-.
move/(_ (size u) (size u).+1): Hinv.
set Hyp := (X in (X -> _ ) -> _) => Hinvbc.
have {Hyp}/Hinvbc : Hyp.
  rewrite /Hyp (leqnSn _) /= size_cat /=.
  by rewrite -addSnnS -{1}[(size u).+1]addn0 ltn_add2l.
rewrite {3 4}Hsz !nth_sizeu !nth_sizeu1 ltNge => <-.
by rewrite -ltNge.
Qed.

Theorem std_plact u v : u =Pl v -> std u =Pl std v.
Proof using.
move: v; apply: gencongr_ind; first exact: plact_refl.
move=> a b1 c b2 H Hplact.
rewrite (plact_ltrans H).
move: Hplact {H} => /plactruleP [].
- exact: std_plact1.
- rewrite -plact1I => /std_plact1-/(_ a c)/plact_ltrans <-; exact: plact_refl.
- exact: std_plact2.
- rewrite -plact2I => /std_plact2-/(_ a c)/plact_ltrans <-; exact: plact_refl.
Qed.

(** ** Robinson-Schensted correspondence and standardization *)
Lemma cast_enum u (S : {set 'I_(size u)}) :
  enum (mem (cast_set (esym (size_std u)) S)) =
  map (cast_ord (esym (size_std u))) (enum (mem S)).
Proof using.
rewrite {1}/enum_mem -enumT /=.
rewrite -[filter _ _]map_id (cast_map_cond _ _ (esym (size_std u))).
congr (map _ _).
rewrite {2}/enum_mem -enumT /=.
apply: eq_filter => i /=.
exact/mem_imset_eq/cast_ord_inj.
Qed.

Lemma sorted_std_extract u (S : {set 'I_(size u)}) :
  sorted <=%O (extractpred (in_tuple u) (mem S)) =
  sorted <=%O (extractpred (in_tuple (std u))
                           (mem (cast_set (esym (size_std u)) S))).
Proof using.
rewrite /extractpred cast_enum /= /sorted.
set leqI := (fun i j : 'I_(size u) => i <= j).
have leqI_trans : transitive leqI.
  move=> i j k; rewrite /leqI; exact: leq_trans.
have: sorted leqI (enum (mem S)).
  rewrite {1}/enum_mem -enumT /=.
  apply: (sorted_filter leqI_trans).
  exact: enum_ord_sorted.
case: (enum (mem S)) => [//= | i0 l] {S} /=.
elim: l i0 => [//= | i1 l IHl] i0 /= /andP [Hleqi Hpath].
rewrite -(IHl i1 Hpath) {IHl Hpath}; congr (_ && _).
rewrite !(tnth_nth inh) /=.
have:= eq_inv_std u => /eq_invP [Hsz]; apply.
move: Hleqi; rewrite /leqI => -> /=.
exact: ltn_ord.
Qed.

Lemma ksupp_inj_std u k : ksupp_inj <=%O <=%O k u (std u).
Proof using.
rewrite /ksupp_inj /ksupp => ks /and3P [Hsz Htriv /forallP Hall].
exists (cast_set (esym (size_std u)) @: ks).
apply/and4P; split.
- rewrite cover_cast /cast_set /=.
  by rewrite card_imset; last exact: cast_ord_inj.
- apply: (@leq_trans #|ks|); last exact: Hsz.
  exact: leq_imset_card.
- apply: imset_trivIset; last exact: Htriv.
  exact: cast_ord_inj.
- apply/forallP => Sstd; apply/implyP => /imsetP [S HS -> {Sstd}].
  move/(_ S): Hall; rewrite HS /=.
  by rewrite sorted_std_extract.
Qed.

Lemma ksupp_inj_stdI u k : ksupp_inj <=%O <=%O k (std u) u.
Proof using.
rewrite /ksupp_inj /ksupp => ks /and3P [Hsz Htriv /forallP Hall].
exists (cast_set (size_std u) @: ks).
apply/and4P; split.
- rewrite cover_cast /cast_set /=.
  by rewrite card_imset; last exact: cast_ord_inj.
- apply: (@leq_trans #|ks|); last exact: Hsz.
  exact: leq_imset_card.
- apply: imset_trivIset; last exact: Htriv.
  exact: cast_ord_inj.
- apply/forallP => Sstd; apply/implyP => /imsetP [S HS -> {Sstd}].
  move/(_ S): Hall; rewrite HS /=.
  rewrite sorted_std_extract; congr (path.sorted _ ).
  rewrite /extractpred; congr (map _ _).
  apply: eq_enum => i.
  rewrite inE /cast_set /= -imset_comp.
  rewrite (eq_imset (g := id)); first last.
    by move=> j; rewrite /= (cast_ordK (size_std u)).
  by rewrite imset_id inE.
Qed.

Lemma Greene_std u k : Greene_row (std u) k = Greene_row u k.
Proof using.
apply/eqP; rewrite eqn_leq; apply/andP; split; apply: leq_Greene.
+ exact: ksupp_inj_stdI.
+ exact: ksupp_inj_std.
Qed.

Theorem shape_RS_std u : shape (RS (std u)) = shape (RS u).
Proof using. by apply: Greene_row_eq_shape_RS; exact: Greene_std. Qed.

End StdRS.

Theorem RSmap_std (d : unit) (T : inhOrderType d) (w : seq T) :
  (RSmap (std w)).2 = (RSmap w).2.
Proof.
move Hn : (size w) => n.
elim: n d T w Hn => [/= | n IHn] d T w; first by move/eqP/nilP => ->.
case/lastP Hw : w => [//= | w' wn] Hn.
have:= shape_RS_std (rcons w' wn).
rewrite -!RSmapE !shape_RSmap_eq.
case/lastP H : (std (rcons w' wn)) => [/= | st stn].
  exfalso; move: H => /(congr1 size).
  by rewrite size_std_rec size_rcons.
case HRS : ((RSmap (rcons w' wn)).2) => [/= | iw yamw].
  exfalso; move: HRS => /(congr1 size).
  by rewrite size_RSmap2 size_rcons.
have Hyamw : yamw = (RSmap w').2.
  move: HRS; rewrite /RSmap rev_rcons /=.
  case: (RSmap_rev (rev w')) => [t rows] /=.
  by case: (instabnrow t wn) => [tr nrow] /= [_ ->].
have Hsize : size w' = n by move: Hn; rewrite size_rcons => /succn_inj.
have /std_rconsK Hst : std (rcons w' wn) = std (rcons st stn).
  by rewrite -H std_stdE.
rewrite {wn Hw Hn H HRS} Hyamw /= -(IHn _ _ _ Hsize).
have Hsizest : size st = n.
  move: Hst; rewrite /std -{2}(size_std_rec (size st) st) => <-.
  by rewrite size_std_rec.
rewrite Hst (IHn _ _ _ Hsizest) {Hst IHn Hsize Hsizest}.
rewrite /RSmap rev_rcons /= -[RSmap_rev (rev st)]/(RSmap st).
case HRS : (RSmap st) => [t0 rows].
by case Hins : (instabnrow t0 stn) => [tr irow] /= /incr_nth_inj ->.
Qed.

Corollary RStabmap_std (d : unit) (T : inhOrderType d) (w : seq T) :
  (RStabmap (std w)).2 = (RStabmap w).2.
Proof.
rewrite /RStabmap.
move H : (RSmap w) => [P Q].
move Hs : (RSmap (std w)) => [Ps Qs] /=.
by rewrite -[Q]/(P, Q).2 -H -[Qs]/(Ps, Qs).2 -Hs RSmap_std.
Qed.


(** ** Robinson-Schensted correspondence and inversion *)
Section KsuppInj.

Variable s t : seq nat.
Hypothesis Hinv : invseq s t.

Let Hinvst : linvseq s t.
Proof using Hinv. by have:= Hinv; rewrite /invseq => /andP []. Qed.
Let Hinvts : linvseq t s.
Proof using Hinv. by have:= Hinv; rewrite /invseq => /andP []. Qed.

Local Definition val2pos :=
  fun (i : 'I_(size s)) => Ordinal (linvseq_ltn_szt Hinvst (ltn_ord i)).

Lemma val2posE : val \o val2pos =1 nth (size t) s.
Proof using. by []. Qed.
Lemma val2pos_inj : injective val2pos.
Proof using.
move: Hinvst => /linvseqP Hv.
move=> i j; rewrite /val2pos; set posi := Ordinal _ => /(congr1 val) /= Heq.
by apply/val_inj; rewrite /= -(Hv i (ltn_ord i)) -(Hv j (ltn_ord j)) Heq.
Qed.

Lemma val2pos_enum (p : {set 'I_(size s)}) :
  (* Hypothesis : val2pos sorted in p *)
  sorted <=%O [seq tnth (in_tuple s) i | i <- enum (mem p)] ->
  enum (mem [set val2pos x | x in p]) = [seq val2pos x | x <- enum p].
Proof using.
rewrite /enum_mem (eq_filter (a2 := mem p)) // -!enumT /= => H.
apply: (inj_map val_inj).
rewrite -map_comp (eq_map val2posE).
rewrite (eq_filter (a2 := mem [set val2pos x | x in p])) //.
move: H; rewrite (eq_map (f2 := fun i : 'I_(_) => nth (size t) s i)); first last.
  by move=> i /=; exact: tnth_nth.
set l := (X in sorted _ X); rewrite -[RHS]/l.
move=> H; apply: (sorted_eq (leT := leq)).
- exact: leq_trans.
- by move=> i j H1; apply/eqP; rewrite eqn_leq.
- apply: (subseq_sorted leq_trans (s2 := map val (enum 'I_(size t)))).
  + by apply: map_subseq; exact: filter_subseq.
  + by rewrite val_enum_ord; exact: iota_sorted.
- move: H; rewrite /sorted; case: l => [//= | l0 l].
  by rewrite (eq_path (e' := leq)); last by move=> i j /=; rewrite leEnat.
- apply: uniq_perm.
  + rewrite map_inj_in_uniq.
    * by apply: filter_uniq; exact: enum_uniq.
    * by move=> i j Hi _ /=; exact: val_inj.
  + rewrite map_inj_in_uniq.
    * by apply: filter_uniq; exact: enum_uniq.
    * move=> i j Hij _ /= HH; apply: val_inj.
      have:= Hinvst => /linvseqP Heq.
      by rewrite /= -(Heq _ (ltn_ord i)) -(Heq _ (ltn_ord j)) HH.
  + rewrite /l {l H} => i /=; apply/idP/idP => /mapP [j].
    * rewrite mem_filter => /andP [/= /imsetP [i' Hi' -> _] -> {i}].
      apply/mapP; exists i'; last by [].
      by rewrite mem_filter /= Hi' /=; rewrite mem_enum.
    * rewrite mem_filter => /andP [/= Hj _ -> {i}].
      apply/mapP; exists (Ordinal (linvseq_ltn_szt Hinvst (ltn_ord j))); last by [].
      rewrite mem_filter; apply/andP; split => /=; last by rewrite mem_enum.
      by rewrite /val2pos; rewrite imset_f.
Qed.

Lemma ksupp_inj_invseq k : ksupp_inj <=%O <=%O k s t.
Proof using Hinvst.
rewrite /ksupp_inj /ksupp => ks /and3P [Hsz Htriv /forallP Hall].
exists [set val2pos @: (p : {set 'I_(size s)}) | p in ks].
apply/and4P; split.
- by rewrite /=; apply/eqP; apply: size_cover_inj; exact: val2pos_inj.
- exact: (leq_trans (leq_imset_card _ _) Hsz).
- exact: (imset_trivIset val2pos_inj).
- apply/forallP => ptmp; apply/implyP => /imsetP [p Hp -> {ptmp}].
  move/(_ p): Hall; rewrite Hp /= /extractpred.
  move/val2pos_enum ->; rewrite -map_comp /=.
  rewrite (eq_map (f2 := nat_of_ord)); first last.
    move=> i /=; rewrite (tnth_nth (size s)) /=.
    by have:= Hinvst => /linvseqP ->.
  set l := map _ _; have : subseq l [seq val x | x  <- enum 'I_(size s)].
    apply: map_subseq; rewrite /enum_mem.
    rewrite [X in subseq _ X](eq_filter (a2 := xpredT)) //.
    by rewrite filter_predT; exact: filter_subseq.
  move/subseq_sorted; apply; first by move=> a b c H1 H2; exact: le_trans H1 H2.
  by rewrite val_enum_ord; exact: iota_sorted.
Qed.


End KsuppInj.

Lemma Greene_invseq s t k : invseq s t -> Greene_row s k = Greene_row t k.
Proof.
move=> Hst; have Hts := invseq_sym Hst.
by apply/eqP; rewrite eqn_leq; apply/andP; split;
  apply: leq_Greene; exact: ksupp_inj_invseq.
Qed.

Lemma shape_invseq s t : invseq s t -> shape (RS s) = shape (RS t).
Proof.
move=> Hinv; apply: Greene_row_tab_eq_shape; try apply: is_tableau_RS.
move=> k; rewrite -!(Greene_row_invar_plactic (congr_RS _) k).
exact: Greene_invseq.
Qed.

Lemma std_rcons_shiftinv t tn :
  is_std (rcons t tn) -> std t = map (shiftinv_pos tn) t.
Proof.
move=> H; apply/eqP/stdP; constructor.
- rewrite /is_std size_map perm_sym.
  apply: perm_size_uniq.
  + exact: iota_uniq.
  + move=> i; move: H; rewrite /is_std => /perm_mem Hperm.
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
      by move: Hi; rewrite -ltnS => /ltn_eqF; rewrite eq_sym => -> /= ->.
  + by rewrite size_map size_iota.
- apply/eq_invP; split; first by rewrite size_map.
  move=> i j /andP [Hij Hj].
  rewrite (nth_map inh); last exact (leq_ltn_trans Hij Hj).
  rewrite (nth_map inh); last exact Hj.
  rewrite !leEnat.
  apply/idP/idP; first exact: shiftinv_pos_incr.
  apply: contraLR.
  rewrite -!ltnNge !ltn_neqAle => /andP [Hneq /shiftinv_pos_incr ->].
  rewrite andbT.
  have:= std_uniq H; rewrite rcons_uniq => /andP [Htn Huniqt].
  move: Hneq; set xi := nth _ _ i; set xj := nth _ _ j.
  rewrite /shiftinv_pos.
  case (ltnP xi tn) => Hxi; case (ltnP xj tn) => Hxj.
  + by apply.
  + apply: contra => /eqP H1; move: Hxj Hxi; rewrite -H1 {H1 i xi Hij} => H1 H2.
    exfalso; have Hneq : xj != tn.
      by move: Htn; apply: contra => /eqP <-; rewrite /xj mem_nth.
    move: H2; have {H1 Hneq} : tn < xj by rewrite ltn_neqAle eq_sym Hneq H1.
    case: xj => [//= | x] /=.
    rewrite ltnS => H1 H2; have:= leq_ltn_trans H1 H2.
    by rewrite ltnn.
  + apply: contra => /eqP H1; move: Hxj Hxi.
    have {Hij Hj} Hi := leq_ltn_trans Hij Hj; rewrite H1 {H1 j xj} => H1 H2.
    exfalso.
    have Hneq : xi != tn.
      by move: Htn; apply: contra => /eqP <-; rewrite /xi mem_nth.
    have {H2 Hneq} : tn < xi by rewrite ltn_neqAle eq_sym Hneq H2.
    case: xi H1 => [//= | x] /=.
    rewrite ltnS => H1 H2; have := leq_ltn_trans H2 H1.
    by rewrite ltnn.
  + apply: contra => /eqP H1.
    have Hi := leq_ltn_trans Hij Hj.
    have {Hxi} : tn < xi.
      rewrite ltn_neqAle Hxi andbT.
      by move: Htn; apply: contra => /eqP ->; rewrite /xi mem_nth.
    have {Hxj} : tn < xj.
      rewrite ltn_neqAle Hxj andbT.
      by move: Htn; apply: contra => /eqP ->; rewrite /xj mem_nth.
    case: xi H1 => [//= | xi] /=.
    by case: xj => [//= | xj] /= ->.
Qed.

Lemma posbig_invseq s0 s t tn :
  invseq (s0 :: s) (rcons t tn) -> posbig (s0 :: s) = tn.
Proof.
move => Hinv; have:= Hinv; rewrite /invseq => /andP [Hst Hts].
have Hpos := posbig_size_cons s0 s.
have Hszt : size t < size (rcons t tn) by rewrite size_rcons.
have:= linvseq_ltn_szt Hts Hszt.
rewrite nth_rcons ltnn eq_refl (size_invseq Hinv) => Htn.
have:= invseq_nthE Hinv Hpos Hszt.
rewrite (set_nth_default inh _ Hpos) nth_posbig.
rewrite nth_rcons ltnn eq_refl => ->.
rewrite (std_max (invseq_is_std Hinv)); apply/eqP.
by move: Hinv => /size_invseq; rewrite size_rcons /= => /eqP.
Qed.

Lemma nth_std_pos s i x :
  is_std s -> i < size s -> i != posbig s -> nth x s i < (size s).-1.
Proof.
case: s => [//= | s0 s] Hstd Hi Hipos.
rewrite [nth _ _ _ < _]ltn_neqAle -ltnS; apply/andP; split.
- rewrite /= -(std_max Hstd) -(nth_posbig inh s0 s).
  rewrite (set_nth_default inh x Hi).
  by rewrite (nth_uniq _ Hi (posbig_size_cons s0 s) (std_uniq Hstd)).
- rewrite -[(size (s0 :: s)).-1.+1]/(size (s0 :: s)).
  by rewrite -(mem_std _ Hstd); exact: mem_nth.
Qed.

Lemma linvseqK s0 s t tn :
  invseq (s0 :: s) (rcons t tn) -> linvseq (rembig (s0 :: s)) (std t).
Proof.
move=> Hinv.
rewrite (std_rcons_shiftinv (invseq_is_std (invseq_sym Hinv))).
have := Hinv; rewrite /invseq => /andP [/linvseqP Hst /linvseqP Hts].
apply/linvseqP => i Hi.
rewrite (set_nth_default inh _ Hi) -nth_rembig.
rewrite (nth_map (size (s0 :: s))); first last.
  set si := shift_pos _ _; have Hsipos : si != posbig (s0 :: s).
    rewrite /si /shift_pos; case: (ltnP i (posbig (s0 :: s))).
    + by move /ltn_eqF ->.
    + by rewrite -ltnS => /gtn_eqF ->.
  have Hsi : si < (size (s0 :: s)).
    rewrite /si /shift_pos; case: (ltnP i (posbig (s0 :: s))) => H.
    + by apply: (ltn_trans Hi); rewrite size_rembig /=.
    + by apply: (leq_trans Hi); rewrite size_rembig /=.
  apply: (leq_trans (nth_std_pos _ (invseq_is_std Hinv) Hsi Hsipos)).
  by move: Hinv => /size_invseq /=; rewrite size_rcons => /succn_inj ->.
rewrite (posbig_invseq Hinv).
have Hpos : shift_pos tn i < size (s0 :: s).
  move: Hi; rewrite /shift_pos size_rembig /=.
  by case (i < tn); first by move/leq_trans; apply.
rewrite (set_nth_default (size (rcons t tn)) inh Hpos).
move: (Hst _ Hpos); rewrite nth_rcons.
rewrite (_ : nth _ _ _ < size t); first by move ->; rewrite shift_posK.
have -> : size t = (size (s0 :: s)).-1 by rewrite (size_invseq Hinv) size_rcons.
apply: (nth_std_pos (size (rcons t tn)) (invseq_is_std Hinv) Hpos).
rewrite (posbig_invseq Hinv) /shift_pos.
case (ltnP i tn); first by move /ltn_eqF ->.
by rewrite -ltnS => /gtn_eqF ->.
Qed.

Lemma invseqK s0 s t tn :
  invseq (s0 :: s) (rcons t tn) -> invseq (rembig (s0 :: s)) (std t).
Proof.
move=> Hinv; apply: linvseq_sizeP; first exact: (linvseqK Hinv).
rewrite size_rembig /= size_std.
by move: Hinv => /size_invseq; rewrite size_rcons /= => /succn_inj ->.
Qed.

Theorem invseqRSPQE s t :
  invseq s t -> (RStabmap s).1 = (RStabmap t).2.
Proof.
rewrite /RStabmap /= => Hinv.
case HRSs : (RSmap s) => [Ps Qs] /=.
have -> : Ps = RS s by rewrite -RSmapE HRSs.
case HRSt : (RSmap t) => [Pt Qt] /=.
have -> : Qt = (RSmap t).2 by rewrite HRSt.
move Hn: (size s) => n {Ps Qs HRSs Pt Qt HRSt}.
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
  by move: Hn; rewrite Hs size_rembig /= => /succn_inj.
case/lastP Ht : t => [//= | t' tn].
  by exfalso; move: Hsize; rewrite Hn Ht.
have:= Hinv; rewrite Hs Ht => /invseqK Hrec.
have Hsize' : size (rembig (s0 :: s')) = size (std t').
  by rewrite size_rembig -Hs Hsize Ht size_rcons /std size_std_rec.
move/(_ _ _ Hszrem Hrec Hsize'): IHn => IHn.
move: Hshape; rewrite -Hs Ht /RSmap rev_rcons /= -/(RSmap t').
case HRSt : (RSmap t') => [t0 rowt'].
case Hins : (instabnrow t0 tn) => [tr irowt'] /=.
move: IHn; rewrite -Hs RSmap_std HRSt /= => ->.
rewrite shape_stdtab_of_yam => /incr_nth_inj ->.
congr (append_nth _ _ _).

have:= (congr1 (fun t => sumn (shape t)) (RSmapE t')).
rewrite (shape_RSmap_eq t') evalseq_eq_size HRSt => ->.
rewrite -/(size_tab (RS t')) size_RS.
move: Hsize; rewrite Ht Hn size_rcons => /succn_inj <-.
move: Hinv => /invseq_is_std; rewrite Hs => /std_max ->.
by apply succn_inj; rewrite -Hn Hs.
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

Corollary RSTabmapstdE (disp : unit) (T : inhOrderType disp) (w : seq T) :
  (RStabmap (invstd (std w))).1 = (RStabmap (std w)).2.
Proof.
have := invstdRSE (std_is_std w).
by case (RStabmap (invstd (std w))) => [P Q] /= ->.
Qed.

Corollary RSinvstdE (disp : unit) (T : inhOrderType disp) (w : seq T) :
  RS (invstd (std w)) = (RStabmap w).2.
Proof.
rewrite -RStabmapE RSTabmapstdE /RStabmap.
rewrite [LHS](_ : _ = stdtab_of_yam (RSmap (std w)).2); last by case: RSmap.
rewrite [RHS](_ : _ = stdtab_of_yam (RSmap w).2); last by case: RSmap.
by congr (stdtab_of_yam _); exact: RSmap_std.
Qed.
