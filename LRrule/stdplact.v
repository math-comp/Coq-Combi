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

Require Import tools combclass ordcast partition Yamanouchi ordtype permuted std.
Require Import Schensted congr plactic Greene Greene_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import OrdNotations.

Section StdRS.

Variable Alph : ordType.
Let Z := (inhabitant Alph).
Implicit Type s u v w : seq Alph.
Implicit Type p : seq nat.
Implicit Type t : seq (seq Alph).

Lemma std_plact1 (u v1 w v2 : seq Alph) :
  v2 \in plact1 v1 -> std (u ++ v1 ++ w) =Pl (std (u ++ v2 ++ w)).
Proof.
  have Hcongr := @plactcongr_is_congr nat_ordType.
  move/plact1P => [] a [] b [] c [] Habc -> ->.
  have := (std_cutabc u w a c b) => [] [] U [] V [] A [] C [] B [] Hsz Hstd.
  have Hac : a <A c by move: Habc => /andP []; apply: leqX_ltnX_trans.
  rewrite Hstd (std_transp Hac Hsz Hstd) -[[:: C; A] ++ B :: V]/([:: C; A; B] ++ V).
  apply: (congr_catr Hcongr); apply: (congr_catl Hcongr).
  apply: rule_gencongr => /=.
  suff -> : (A <= B < C)%Ord by rewrite inE eq_refl.
  have := eq_inv_std (u ++ [:: a; c; b] ++ w); rewrite Hstd {Hstd} => /eq_invP [] Hsize Hinv.
  have := Hinv (size u) (size u).+2.
  set Hyp := (X in (X -> _ ) -> _) => Hinvab.
  have {Hyp Hinvab} /Hinvab : Hyp.
    rewrite /Hyp (leq_trans (leqnSn _) (leqnSn _)) /= size_cat /=.
    by rewrite -2!addSnnS -{1}[(size u).+2]addn0 ltn_add2l.
  rewrite {3 4}Hsz !nth_sizeu !nth_sizeu2 => <-.
  have := Hinv (size u).+1 (size u).+2.
  set Hyp := (X in (X -> _ ) -> _) => Hinvbc.
  have {Hyp Hinvbc} /Hinvbc : Hyp.
    rewrite /Hyp (ltn_trans (ltnSn _) (ltnSn _)) /= size_cat /=.
    by rewrite -2!addSnnS -{1}[(size u).+2]addn0 ltn_add2l.
  rewrite {3 4}Hsz !nth_sizeu1 !nth_sizeu2 ltnXNgeqX => <-.
  by rewrite -ltnXNgeqX.
Qed.

Lemma reorg3 (T : eqType) (u w : seq T) b a c :
  u ++ [:: b; a; c] ++ w = (u ++ [:: b]) ++ [:: a; c] ++ w.
Proof. by rewrite -catA. Qed.

Lemma std_plact2 (u v1 w v2 : seq Alph) :
  v2 \in plact2 v1 -> std (u ++ v1 ++ w) =Pl (std (u ++ v2 ++ w)).
Proof.
  have Hcongr := @plactcongr_is_congr nat_ordType.
  move/plact2P => [] a [] b [] c [] Habc -> ->.
  have := (std_cutabc u w b a c) => [] [] U [] W [] B [] A [] C [] Hsz.
  have Hac : a <A c by move: Habc => /andP []; apply: ltnX_leqX_trans.
  rewrite !reorg3.
  have Hsz1 : size (u ++ [:: b]) = size (U ++ [:: B]) by rewrite !size_cat Hsz.
  move=> Hstd; rewrite Hstd (std_transp Hac Hsz1 Hstd).
  rewrite -!reorg3.
  apply: (congr_catr Hcongr); apply: (congr_catl Hcongr).
  apply: rule_gencongr => /=.
  suff -> : (A < B <= C)%Ord by rewrite !mem_cat inE eq_refl /= !orbT.
  rewrite -!reorg3  in Hstd.
  have := eq_inv_std (u ++ [:: b; a; c] ++ w).
  rewrite Hstd {Hstd} => /eq_invP [] Hsize Hinv.
  have := Hinv (size u) (size u).+2.
  set Hyp := (X in (X -> _ ) -> _) => Hinvab.
  have {Hyp Hinvab} /Hinvab : Hyp.
    rewrite /Hyp (leq_trans (leqnSn _) (leqnSn _)) /= size_cat /=.
    by rewrite -2!addSnnS -{1}[(size u).+2]addn0 ltn_add2l.
  rewrite {3 4}Hsz !nth_sizeu !nth_sizeu2 => <-.
  have := Hinv (size u) (size u).+1.
  set Hyp := (X in (X -> _ ) -> _) => Hinvbc.
  have {Hyp Hinvbc} /Hinvbc : Hyp.
    rewrite /Hyp (leqnSn _) /= size_cat /=.
    by rewrite -addSnnS -{1}[(size u).+1]addn0 ltn_add2l.
  rewrite {3 4}Hsz !nth_sizeu !nth_sizeu1 ltnXNgeqX => <-.
  by rewrite -ltnXNgeqX.
Qed.

Theorem std_plact u v : u =Pl v -> std u =Pl std v.
Proof.
  have:= @plactcongr_equiv nat_ordType => /equivalence_relP [] Hrefl Htrans.
  move: v; apply: gencongr_ind; first by apply: Hrefl.
  move=> a b1 c b2 H Hplact.
  rewrite -(@Htrans (std (a ++ b1 ++ c))); last by rewrite -(Htrans _ _ H); apply: Hrefl.
  move: Hplact {H} => /plactruleP [].
  + apply: std_plact1.
  + rewrite -plact1I => /std_plact1 H.
    have {H} H := H a c.
    by rewrite -(Htrans _ _ H); apply: Hrefl.
  + apply: std_plact2.
  + rewrite -plact2I => /std_plact2 H.
    have {H} H := H a c.
    by rewrite -(Htrans _ _ H); apply: Hrefl.
Qed.

Lemma cast_enum u (S : {set 'I_(size u)}) :
  enum (mem (cast_set (esym (size_std u)) S)) =
  map (cast_ord (esym (size_std u))) (enum (mem S)).
Proof.
  rewrite {1}/enum_mem -enumT /=.
  rewrite -[filter _ _]map_id (cast_map_cond _ _ (esym (size_std u))).
  congr (map _ _).
  rewrite {2}/enum_mem -enumT /=.
  apply: eq_filter => i /=.
  by rewrite mem_cast.
Qed.

Lemma sorted_enum_ord N :
  sorted (fun i j : 'I_N => i <= j) (enum 'I_N).
Proof.
  rewrite /sorted; case Henum : (enum 'I_N) => [//= | a l].
  rewrite -(map_path (h := val) (e := leq) (b := pred0)).
  - have -> : l = behead (enum 'I_N) by rewrite Henum.
    have -> : val a = head 0 (map val (enum 'I_N)) by rewrite Henum.
    rewrite -behead_map val_enum_ord.
    case: N {a l Henum} => [//= | N] /=.
    by apply: (iota_sorted 0 N.+1).
  - by [].
  - by rewrite (eq_has (a2 := pred0)); first by rewrite has_pred0.
Qed.

Lemma sorted_std_extract u (S : {set 'I_(size u)}) :
   sorted leqX (extractpred (in_tuple u) (mem S)) =
   sorted leqX (extractpred (in_tuple (std u)) (mem (cast_set (esym (size_std u)) S))).
Proof.
  rewrite /extractpred cast_enum /= /sorted.
  set leqI := (fun i j : 'I_(size u) => i <= j).
  have leqI_trans : transitive leqI.
    move=> i j k; rewrite /leqI; by apply: leq_trans.
  have: sorted leqI (enum (mem S)).
    rewrite {1}/enum_mem -enumT /=.
    apply: (sorted_filter leqI_trans).
    by apply: sorted_enum_ord.
  case: (enum (mem S)) => [//= | i0 l] {S} /=.
  elim: l i0 => [//= | i1 l IHl] i0 /= /andP [] Hleqi Hpath.
  rewrite -(IHl i1 Hpath) {IHl Hpath}; congr (_ && _).
  rewrite !(tnth_nth Z) !(tnth_nth (inhabitant (nat_ordType))) /=.
  have := eq_inv_std u => /eq_invP [] Hsz Hinv.
  apply: Hinv.
  move: Hleqi; rewrite /leqI => -> /=.
  by apply: ltn_ord.
Qed.

Lemma ksupp_inj_std u k : ksupp_inj leqX leqX k u (std u).
Proof.
  rewrite /ksupp_inj /ksupp => ks /and3P [] Hsz Htriv /forallP Hall.
  exists (cast_set (esym (size_std u)) @: ks).
  apply/and4P; split.
  - rewrite /scover /= cover_cast /cast_set /=.
    by rewrite card_imset; last by apply: cast_ord_inj.
  - apply: (@leq_trans #|ks|); last exact Hsz.
    by apply: leq_imset_card.
  - apply: imset_trivIset; last exact Htriv.
    by apply: cast_ord_inj.
  - apply/forallP => Sstd; apply/implyP => /imsetP [] S HS -> {Sstd}.
    have {Hall} := Hall S; rewrite HS /=.
    by rewrite sorted_std_extract.
Qed.

Lemma ksupp_inj_stdI u k : ksupp_inj leqX leqX k (std u) u.
Proof.
  rewrite /ksupp_inj /ksupp => ks /and3P [] Hsz Htriv /forallP Hall.
  exists (cast_set (size_std u) @: ks).
  apply/and4P; split.
  - rewrite /scover /= cover_cast /cast_set /=.
    by rewrite card_imset; last by apply: cast_ord_inj.
  - apply: (@leq_trans #|ks|); last exact Hsz.
    by apply: leq_imset_card.
  - apply: imset_trivIset; last exact Htriv.
    by apply: cast_ord_inj.
  - apply/forallP => Sstd; apply/implyP => /imsetP [] S HS -> {Sstd}.
    have {Hall} := Hall S; rewrite HS /=.
    rewrite sorted_std_extract; congr (path.sorted _ ).
    rewrite /extractpred; congr (map _ _).
    apply: eq_enum => i.
    rewrite inE /cast_set /= -imset_comp.
    set f := (X in imset X _).
    have /eq_imset -> : f =1 id.
      by move=> j; rewrite /f /= (cast_ordK (size_std u)).
    by rewrite imset_id inE.
Qed.

Lemma Greene_std u k : Greene_row (std u) k = Greene_row u k.
Proof.
  apply/eqP; rewrite eqn_leq; apply/andP; split;
    apply: leq_Greene.
  + by apply: ksupp_inj_stdI.
  + by apply: ksupp_inj_std.
Qed.

Theorem shape_RS_std u : shape (RS (std u)) = shape (RS u).
Proof. apply: Greene_row_eq_shape_RS; by apply: Greene_std. Qed.

Lemma size_RSmap2 u : size ((RSmap u).2) = size u.
Proof.
  elim/last_ind: u => [//= | u un].
  rewrite /RSmap rev_rcons /=.
  case: (RSmap_rev (rev u)) => [t rows] /=.
  case: (instabnrow t un) => [tr nrow] /= ->.
  by rewrite size_rcons.
Qed.

End StdRS.

Theorem RSmap_std (T : ordType) (w : seq T) : (RSmap (std w)).2 = (RSmap w).2.
Proof.
  move Hn : (size w) => n.
  elim: n T w Hn => [/= | n IHn] T w; first by move/eqP/nilP => ->.
  case/lastP Hw : w => [//= | w' wn] Hn.
  have:= shape_RS_std (rcons w' wn).
  rewrite -!RSmapE !shape_RSmap_eq.
  case/lastP H : (std (rcons w' wn)) => [/= | st stn].
    exfalso; have:= eq_refl (@size nat [::]).
    by rewrite -{1}H size_std_rec size_rcons.
  case HRS : ((RSmap (rcons w' wn)).2) => [/= | iw yamw].
    exfalso; have:= eq_refl (@size nat [::]).
    by rewrite -{1}HRS size_RSmap2 size_rcons.
  have Hyamw : yamw = (RSmap w').2.
    move: HRS; rewrite /RSmap rev_rcons /=.
    case: (RSmap_rev (rev w')) => [t rows] /=.
    by case: (instabnrow t wn) => [tr nrow] /= [] _ ->.
  have Hsize : size w' = n by move: Hn => /eqP; rewrite size_rcons eqSS => /eqP.
  have /std_rconsK Hst : std (rcons w' wn) = std (rcons st stn) by rewrite -H std_stdE.
  rewrite {wn Hw Hn H HRS} Hyamw /= -(IHn _ _ Hsize).
  have Hsizest : size st = n.
    have := Hst; rewrite /std -{2}(size_std_rec (size st) st) => <-.
    by rewrite size_std_rec.
  rewrite Hst (IHn _ _ Hsizest) {Hst IHn Hsize Hsizest}.
  rewrite /RSmap rev_rcons /= -[RSmap_rev (rev st)]/(RSmap st).
  case HRS : (RSmap st) => [t0 rows].
  case Hins : (instabnrow t0 stn) => [tr irow] /=.
  by move/incr_nth_inj ->.
Qed.

