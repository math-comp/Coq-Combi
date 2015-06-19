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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import tuple finfun finset bigop path.

Require Import tools ordcast combclass partition yama schensted ordtype std stdtab invseq congr plactic greeninv yamplact skewtab.
Require Import shuffle multpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N.


Section LR.

Notation Z := (inhabitant nat_ordType).

Lemma to_word_map_shiftn sh t : to_word (map (shiftn sh) t) = shiftn sh (to_word t).
Proof.
  rewrite /shiftn.
  elim: t => [//= | t0 t IHt] /=.
  by rewrite !to_word_cons IHt map_cat.
Qed.

Lemma filter_leq_shiftn sh t : [seq x - sh | x <- [seq sh + i | i <- t] & sh <= x] = t.
Proof. elim: t => [//= | l0 r IHt] /=; by rewrite leq_addr /= addKn IHt. Qed.

Lemma filter_gtn_shiftn sh t : [seq x <- [seq sh + i | i <- t] | gtn sh x] = [::].
Proof. elim: t => [//= | l0 r /= ->] /=; by rewrite ltnNge leq_addr. Qed.

Lemma shiftn_skew_dominate n sh u v :
  skew_dominate sh u v -> skew_dominate sh (shiftn n u) (shiftn n v).
Proof.
  rewrite /skew_dominate /dominate !size_map => /andP [] Hsz.
  rewrite -map_drop size_map Hsz /=.
  set p1 := (X in all X) => H.
  set p2 := (X in all X).
  rewrite (eq_in_all (a2 := p1)) //=.
  move => i /=; rewrite mem_iota add0n => /= Hi1.
  case (leqP sh (size u)) => Hu.
  + rewrite /p1 /p2 {p1 p2 H} /shiftn.
    rewrite !ltnXnatE (nth_map Z _ _ (leq_trans Hi1 Hsz)) (nth_map Z _ _ Hi1).
    by rewrite ltn_add2l.
  + exfalso; move: Hi1; rewrite size_drop.
    have:= (ltnW Hu); rewrite {1}/leq => /eqP ->.
    by rewrite ltn0.
Qed.

Lemma is_skew_tableau_map_shiftn sh inn t :
  is_skew_tableau inn t -> is_skew_tableau inn (map (shiftn sh) t).
Proof.
  elim: t inn => [//= | r0 t IHt] /= inn.
  move=> /and4P [] Hszr0 Hrow0 Hdom Hskew.
  apply/and4P; split.
  - by rewrite size_map.
  - rewrite /shiftn.
    case: r0 Hrow0 {Hdom Hskew IHt Hszr0} => [//= | l0 r] /= H.
    rewrite (map_path (e' := leqX_op) (b := pred0)).
    + exact H.
    + move=> i j /= _; by rewrite !leqXnatE leq_add2l.
    + by apply/hasPn => i.
  - have -> : head [::] (map (shiftn sh) t) = shiftn sh (head [::] t) by case t.
    by apply shiftn_skew_dominate.
  - by apply IHt.
Qed.

Lemma join_stdtab s t :
  is_stdtab s -> is_skew_tableau (shape s) t ->
  is_tableau (join_tab s (map (shiftn (size_tab s)) t)).
Proof.
  rewrite /is_stdtab => /andP [].
  rewrite /is_std -size_to_word /= => Htabs Hperm /(is_skew_tableau_map_shiftn (size_tab s)).
  apply: join_tab_skew; last exact Htabs.
  rewrite {2}/to_word -map_rev -map_flatten.
  move: (flatten (rev t)) => w.
  apply/allP => x /mapP [] i _ -> {x}.
  rewrite /allLtn; apply/allP => j.
  rewrite (perm_eq_mem Hperm) mem_iota /= add0n ltnXnatE => /leq_trans; apply.
  by apply leq_addr.
Qed.

Lemma join_stdtab_in_shuffle s t :
  is_stdtab s ->
  size s <= size t ->
  to_word (join_tab s (map (shiftn (size_tab s)) t)) \in shsh (to_word s) (to_word t).
Proof.
  rewrite /join_tab /is_stdtab => /andP [] _ Hstd Hsize.
  rewrite (mem_shsh _ _ Hstd).
  move: Hstd; rewrite /is_std -size_to_word /= => Hperm.
  have {Hperm} : all (gtn (size_tab s)) (to_word s).
    apply/allP => i; rewrite (perm_eq_mem Hperm).
    by rewrite mem_iota /= add0n.
  move: (size_tab s) => sh.
  rewrite /shiftn => Hall; apply /andP; split; apply/eqP.
  - elim: s t Hsize Hall => [| s0 s IHs] /= t.
    + rewrite subn0 size_map => _ _.
      set t' := map _ _.
      have {t'} -> : t' = map (shiftn sh) t.
        by rewrite /t'; elim: t {t'} => //= r t ->.
      elim: t => [//= | t0 t IHt] /=.
      rewrite to_word_cons filter_cat IHt cat0s {t IHt}.
      by rewrite filter_gtn_shiftn.
    + case: t => [//= | t0 t] /=.
      rewrite ltnS to_word_cons all_cat => /IHs{IHs}Hrec /andP [] /Hrec{Hrec} Hrec.
      rewrite to_word_cons !filter_cat subSS Hrec {Hrec} => /all_filterP ->.
      suff -> : [seq x <- [seq sh + i | i <- t0] | gtn sh x] = [::] by rewrite cats0.
      by rewrite filter_gtn_shiftn.
  - elim: s t Hsize Hall => [| s0 s IHs] /= t.
    + rewrite subn0 size_map => _ _.
      elim: t => [//= | t0 t IHt] /=.
      rewrite !to_word_cons !filter_cat map_cat IHt {IHt}.
      by rewrite filter_leq_shiftn.
    + case: t => [//= | t0 t] /=.
      rewrite ltnS to_word_cons all_cat => /IHs{IHs}Hrec /andP [] /Hrec{Hrec} Hrec.
      rewrite !to_word_cons !filter_cat !map_cat subSS Hrec {Hrec}.
      rewrite filter_leq_shiftn => Hall.
      suff -> : [seq x - sh | x <- s0 & sh <= x] = [::] by rewrite cat0s.
      elim: s0 Hall {t s t0} => [//= | l0 s IHs] /= /andP [] H /IHs.
      by rewrite leqNgt H.
Qed.

Variables d1 d2 : nat.
Variables (P1 : intpartn d1) (P2 : intpartn d2).

Lemma size_tab_P1 : d1 = size_tab (RS (std (hyper_yam P1))).
Proof. by rewrite size_RS size_std size_hyper_yam intpartn_sumn. Qed.

Lemma size_yam (y : yameval_finType (intpartnP P2)) : size y = sumn P2.
Proof. by rewrite -evalseq_eq_size eval_yameval. Qed.

Lemma sfilterleq_LR_supportP Q :
  Q \in LR_support (hyper_stdtab P1) (hyper_stdtab P2) ->
  exists y : yameval_finType (intpartnP P2), std y = (sfilterleq d1 (to_word Q)).
Proof.
  rewrite /LR_support inE.
  rewrite -LRTripleE; try apply stdtabnP.
  move/(LRTripleP _ (stdtabnP (hyper_stdtab P1)) (stdtabnP (hyper_stdtab P2))).
  move=> [] p1 p2 p /= Hp1 Hp2 Hp.
  have Hstdp1 : is_std p1.
    rewrite -RSstdE Hp1.
    by have := hyper_stdtabP P1 => /andP [].
  rewrite (mem_shsh _ _ Hstdp1) => /andP [].
  rewrite -(size_RS p1) Hp1.
  have := hyper_stdtabP P1 => /andP [] _ /eqP -> /eqP Hsfp1 /eqP Hsfp2.
  suff : sfilterleq d1 (to_word Q) =Pl std (hyper_yam P2).
    move/(plact_from_yam (intpartnP P2)) => [] yam Hyam; by exists (YamEval Hyam).
  rewrite -Hp plactic_RS -Hp2 -Hsfp2 eq_sym -plactic_RS.
  rewrite /sfilterleq /=.
  apply: plact_map_in_incr.
    move=> i j; rewrite !mem_filter => /andP [] Hi _ /andP [] Hj _.
    rewrite !ltnXnatE => Hij.
    by rewrite ltn_subRL subnKC.
  apply: (plactic_filter_leqX d1).
  by apply: congr_RS.
Qed.

Lemma filter_gtnX_to_word (T : ordType) n (t : seq (seq T)) :
  filter (gtnX n) (to_word t) = to_word (filter_gtnX_tab n t).
Proof.
  elim: t => [//= | t0 t IHt] /=.
  rewrite to_word_cons filter_cat /=.
  case: (altP (filter (gtnX n) t0 =P [::])) => H /=.
  - by rewrite H cats0 IHt.
  - by rewrite to_word_cons IHt.
Qed.

Lemma filter_leqX_to_word (T : ordType) n (t : seq (seq T)) :
  filter (leqX n) (to_word t) = to_word (filter_leqX_tab n t).
Proof.
  elim: t => [//= | t0 t IHt] /=.
  rewrite to_word_cons filter_cat /=.
  case: (altP (filter (leqX n) t0 =P [::])) => H /=.
  - by rewrite H cats0 IHt to_word_cons cats0.
  - by rewrite to_word_cons IHt.
Qed.

Section OneCoeff.

Variable P : intpartn (d1 + d2).
Hypothesis Hincl : included P1 P.

Lemma sumn_diffE : sumn (diff_shape P1 P) = sumn P2.
Proof. by rewrite (sumn_diff_shape Hincl) !intpartn_sumn addKn. Qed.

Definition is_skew_reshape_tableau (w : seq nat) :=
  is_skew_tableau P1 (skew_reshape P1 P w).
Lemma is_skew_reshape_tableauP (w : seq nat) :
  size w = sumn (diff_shape P1 P) ->
  reflect
    (exists tab, [/\ is_skew_tableau P1 tab, shape tab = diff_shape P1 P & to_word tab = w])
    (is_skew_reshape_tableau w).
Proof.
  rewrite /is_skew_reshape_tableau => Hsize; apply (iffP idP).
  - move=> H; exists (skew_reshape P1 P w); split; first exact H.
    + exact: (shape_skew_reshape Hincl Hsize).
    + exact: (to_word_skew_reshape Hincl Hsize).
  - move=> [] tab [] Htab Hsh <-.
    rewrite -(diff_shapeK Hincl) -Hsh.
    rewrite skew_reshapeK; first exact Htab.
    rewrite -(size_map size) -/(shape tab) Hsh size_diff_shape.
    by apply size_included.
Qed.

Lemma size_leq_skew_reshape (y : seq nat) :
  size (RS (std (hyper_yam P1))) <= size (skew_reshape P1 P y).
Proof.
  rewrite -(size_map size) -/(shape (RS _)) shape_RS_std.
  rewrite shape_RS_yam; last by apply hyper_yamP; apply intpartnP.
  rewrite (evalseq_hyper_yam (intpartnP P1)).
  rewrite size_skew_reshape; by apply size_included.
Qed.

Definition bijLRyam :=
  [fun y : seq nat =>
     join_tab (hyper_stdtab P1) (map (shiftn d1) (skew_reshape P1 P (std y)))].

Lemma predLRTripleFast_bijLRyam (yam : yameval P2) :
  is_skew_reshape_tableau yam ->
  predLRTripleFast (hyper_stdtab P1) (hyper_stdtab P2) (bijLRyam yam).
Proof.
  rewrite/is_skew_reshape_tableau => Hskew.
  apply/hasP; exists (std yam).
    rewrite RSclassE; last by apply is_tableau_RS.
    rewrite -plactic_RS.
    apply std_plact.
    rewrite -{2}(eval_yameval yam).
    apply yam_plactic_hyper; by apply yamevalP.
  have Hstd1 : is_std (to_word (hyper_stdtab P1)).
    have /= := hyper_stdtabP P1 => /andP [].
    by rewrite /is_stdtab => /andP [].
  rewrite -[std yam](to_word_skew_reshape Hincl); first last.
    by rewrite size_std size_yam sumn_diffE.
  rewrite /= {2}size_tab_P1.
  apply: join_stdtab_in_shuffle.
  - rewrite RSstdE; by apply std_is_std.
  - by apply size_leq_skew_reshape.
Qed.

Lemma bijLRyamP (yam : yameval P2) :
  is_skew_reshape_tableau yam -> is_stdtab_of_n (d1 + d2) (bijLRyam yam).
Proof.
  rewrite /is_skew_reshape_tableau /= /is_stdtab => Hskew.
  set sz := size_tab _.
  have {sz} -> : sz = d1 + d2.
    rewrite /sz{sz}  size_join_tab.
    + rewrite size_RS size_std size_hyper_yam intpartn_sumn; congr (_ + _).
      rewrite /size_tab /shape -map_comp.
      have /eq_map -> : (size \o shiftn d1) =1 size by move=> s /=; rewrite size_map.
      rewrite -/(shape _) (shape_skew_reshape Hincl).
      * by rewrite (sumn_diff_shape Hincl) !intpartn_sumn addKn.
      * by rewrite size_std size_yam sumn_diffE.
    + rewrite size_map; by apply size_leq_skew_reshape.
  rewrite eq_refl andbT.
  apply/andP; split.
  - rewrite {2}size_tab_P1.
    apply join_stdtab.
    rewrite RSstdE; by apply std_is_std.
  - rewrite shape_RS_std shape_RS_yam; last by apply hyper_yamP; apply intpartnP.
    rewrite (evalseq_hyper_yam (intpartnP P1)).
    rewrite -(is_skew_tableau_reshape_std (size_included Hincl)).
    + exact Hskew.
    + by rewrite size_yam sumn_diffE.
  - have /= /hasP [] := predLRTripleFast_bijLRyam Hskew => z.
    set image := to_word _.
    rewrite (RSclassE _ (is_tableau_RS _)) -plactic_RS => /plactcongr_homog Hz.
    have {Hz} Hz : is_std z by apply: (perm_eq_std _ Hz); apply std_is_std.
    have : is_stdtab (RS (std (hyper_yam P1))) by rewrite RSstdE; apply std_is_std.
    rewrite /is_stdtab => /andP [] _ Hstd1.
    by apply (allP (std_shsh Hstd1 Hz)).
Qed.

Definition LRyam_set :=
  [set y : yameval_finType (intpartnP P2) | is_skew_reshape_tableau y].
Definition LRyam_coeff := #|LRyam_set|.
Definition bijLR (yam : yameval P2) : stdtabn (d1 + d2) :=
  if (boolP (is_skew_reshape_tableau yam)) is AltTrue pf then
    StdtabN (bijLRyamP pf)
  else
    hyper_stdtab P.

Lemma bijLR_LR_support yam :
  yam \in LRyam_set ->
  bijLR yam \in LR_support (hyper_stdtab P1) (hyper_stdtab P2).
Proof.
  rewrite !inE /bijLR /= => Hskew.
  case (boolP (is_skew_reshape_tableau yam)) => /=; last by rewrite Hskew.
  by move/predLRTripleFast_bijLRyam => /=.
Qed.

Lemma map_reshape (T1 T2 : Type) (f : T1 -> T2) sh (s : seq T1) :
  map (map f) (reshape sh s) = reshape sh (map f s).
Proof. elim: sh s => [//= | sh0 sh IHsh] /= s;  by rewrite map_take IHsh map_drop. Qed.

Lemma filtergtn_LR_support Q :
  Q \in LR_support (hyper_stdtab P1) (hyper_stdtab P2) ->
    filter_gtnX_tab d1 Q = hyper_stdtab P1.
Proof.
  rewrite inE.
  move/(predLRTripleFast_filter_gtnX (stdtabnP (hyper_stdtab P1)) (stdtabnP Q)) => ->.
  by rewrite stdtabn_size.
Qed.

Lemma size_zip2 (T : Type) (s t : seq (seq T)) :
  [seq size p.1 + size p.2 | p <- zip s t] =
  [seq p.1 + p.2 | p <- zip (map size s) (map size t)].
Proof.
  elim: s t => [| s0 s IHs] /=; first by elim=> [| t0 t IHt].
  case => [//= | t0 t] /=.
  by rewrite -IHs.
Qed.

Lemma shape_bijLR yam :
  yam \in LRyam_set -> shape (bijLR yam) = P.
Proof.
  rewrite !inE /bijLR /= => Hskew.
  case (boolP (is_skew_reshape_tableau yam)) => [_|] /=; last by rewrite Hskew.
  rewrite /shape /join_tab.
  rewrite !size_map -map_comp.
  set f := (X in map X); have {f} /eq_map -> : f =1 fun p => size p.1 + size p.2.
    rewrite /f {f} => i /=; by rewrite size_cat.
  rewrite size_zip2 size_skew_reshape.
  set t := map size _; have {t} -> : t = pad 0 (size P) P1.
    rewrite /t{t} /pad /= map_cat.
    rewrite -(size_map size) -/(shape (RS _)) shape_RS_std.
    rewrite shape_RS_yam; last by apply hyper_yamP; apply intpartnP.
    rewrite (evalseq_hyper_yam (intpartnP P1)).
    by rewrite map_nseq.
  set t := map size _; have {t} -> : t = diff_shape P1 P.
    rewrite /t{t} /= -map_comp.
    have /eq_map -> : size \o shiftn d1 =1 size by move=> i /=; rewrite size_map.
    rewrite -/(shape _) shape_skew_reshape //=.
    by rewrite size_std size_yam sumn_diffE.
  rewrite -(size_diff_shape P1 P).
  rewrite -/(outer_shape P1 (diff_shape P1 P)).
  by apply diff_shapeK.
Qed.

Lemma filterleq_LR_support Q :
  Q \in LRtab_set P1 P2 P ->
  (skew_reshape P1 P [seq x <- to_word Q | d1 <= x]) = filter_leqX_tab d1 Q.
Proof.
  rewrite /LRtab_set inE => /andP [] HLR /eqP Hshape.
  rewrite /filter_leqX_tab -(eq_filter (leqXnatE _)).
  rewrite -Hshape filter_leqX_to_word /=.
  have -> : val P1 = shape (filter_gtnX_tab d1 Q).
    by rewrite (filtergtn_LR_support HLR) -{1}(shaped_hyper_stdtabP P1) /=.
  set t := map _ _.
  have -> : shape Q = outer_shape (shape (filter_gtnX_tab d1 Q)) (shape t).
    rewrite /outer_shape /= /t {t}.
    have := stdtabnP Q; rewrite /is_stdtab => /andP [] /(join_tab_filter d1) {2}<- _.
    rewrite /= /shape /join_tab /pad /=.
    rewrite !size_map -map_comp.
    set f := (X in map X); have {f} /eq_map -> : f =1 fun p => size p.1 + size p.2.
      rewrite /f {f} => i /=; by rewrite size_cat.
    rewrite size_zip2; congr (map _ (zip _ _)).
    move: (size Q) => n.
    elim: (filter _ _) n => [//= | t0 t IHt] n /=; first by rewrite map_nseq.
    case: n => [| n] /=; first by rewrite !cats0.
    by rewrite subSS IHt.
  apply skew_reshapeK.
  rewrite /t /= /shape !size_map size_filter.
  apply (leq_trans (count_size _ _)).
  by rewrite size_map.
Qed.

Lemma sfilterleq_LR_support_skew Q :
  Q \in LRtab_set P1 P2 P -> is_skew_reshape_tableau (sfilterleq d1 (to_word Q)).
Proof.
  have := stdtabnP (hyper_stdtab P2); rewrite /is_stdtab => /andP [] Htab2 Hstd2.
  have /allP /= Hall := RSclassP Htab2.
  move=> HLRtab; have := HLRtab; rewrite /LRtab_set inE => /andP [] HLR /eqP Hshape.
  have Hfilter := filtergtn_LR_support HLR.
  have:= HLR; rewrite inE /= => /hasP [] p2 /Hall{Hall} /Sch_plact Hpl Hshsh.
  have := hyper_stdtabP P1 => /=; rewrite /is_stdtab => /andP [] /andP [] _ Hstd /= /eqP Hsz.
  have := (shsh_sfilterleq Hstd Hshsh).
  rewrite -size_to_word Hsz /= {Hstd Hsz} => Hp2; subst p2.
  apply (eq_inv_is_skew_tableau_reshape (u1 := [seq x <- to_word Q | d1 <= x])).
  - by apply size_included.
  - apply/eq_invP; split; first by rewrite size_map.
    move=> i j /andP [] Hij Hj.
    rewrite (nth_map Z); last by apply (leq_ltn_trans Hij Hj).
    rewrite (nth_map Z); last by apply Hj.
    rewrite !leqXnatE leq_subLR subnKC //=.
    have:= mem_nth Z Hj; by rewrite mem_filter => /andP [].
  - move: Hpl => /plactcongr_homog/perm_eq_size.
    rewrite size_map => ->.
    rewrite size_std sumn_diffE -evalseq_eq_size evalseq_hyper_yam //=.
    by apply intpartnP.
  - rewrite (filterleq_LR_support HLRtab).
    have -> : val P1 = shape (filter_gtnX_tab d1 Q).
      by rewrite Hfilter -{1}(shaped_hyper_stdtabP P1) /=.
    apply is_skew_tableau_filter_leqX.
    have:= stdtabnP Q; by rewrite /is_stdtab => /andP [].
Qed.

Lemma bijLR_surj Q :
  Q \in LRtab_set P1 P2 P ->
  exists2 yam, yam \in LRyam_set & bijLR yam = Q.
Proof.
  move=> HLRtab; have := HLRtab; rewrite /LRtab_set inE => /andP [] HLR /eqP Hshape.
  have:= HLR => /sfilterleq_LR_supportP [] y Hmap.
  have Hskew : is_skew_reshape_tableau y.
    rewrite /is_skew_reshape_tableau (is_skew_tableau_reshape_std (size_included Hincl)).
    + rewrite Hmap; by apply sfilterleq_LR_support_skew.
    + by rewrite size_yam sumn_diffE.
  exists y.
  - rewrite inE /=; exact Hskew.
  - rewrite /bijLR.
    case (boolP (is_skew_reshape_tableau y)) => /=; last by rewrite Hskew.
    move=> pf; apply val_inj => /= {pf}.
    have -> : RS (std (hyper_yam P1)) = filter_gtnX_tab d1 Q.
      have := (hyper_stdtabP P1) => /andP [] Htab1 /eqP Hsz1.
      rewrite inE in HLR.
      rewrite (predLRTripleFast_filter_gtnX Htab1 (stdtabnP Q) HLR).
      by rewrite Hsz1.
    have -> : [seq shiftn d1 i | i <- skew_reshape P1 P (std y)] = filter_leqX_tab d1 Q.
      rewrite Hmap /= /skew_reshape map_rev map_reshape -/(shiftn d1) sfilterleqK.
      rewrite -/(skew_reshape _ _ _).
      rewrite -(eq_filter (leqXnatE _)).
      by rewrite filterleq_LR_support.
    rewrite join_tab_filter //=.
    by have := stdtabnP Q; rewrite /is_stdtab => /andP [].
Qed.

Lemma bijLR_inj : {in LRyam_set &, injective bijLR}.
Proof.
  move=> x y; rewrite !inE /bijLR => Hx Hy.
  case (boolP (is_skew_reshape_tableau x)) => /=; last by rewrite Hx.
  case (boolP (is_skew_reshape_tableau y)) => /=; last by rewrite Hy.
  move=> Hy1 Hx1 H.
  apply val_inj => /=.
  have:= erefl (to_word (StdtabN (bijLRyamP Hx1))); rewrite {2}H /= {H Hx1 Hy1 Hx Hy} => H.
  pose f := [fun s : seq nat =>
               to_word (join_tab (hyper_stdtab P1) (map (shiftn d1) (skew_reshape P1 P s)))].
  have {H} H : f (std x) = f (std y) by rewrite /= H.
  have invf (s : yameval_finType (intpartnP P2)) : std s = sfilterleq d1 (f (std s)).
    have /= := join_stdtab_in_shuffle
                 (stdtabnP (hyper_stdtab P1)) (size_leq_skew_reshape (std s)).
    rewrite /size_tab.
    have := erefl (val P1); rewrite -{2}(shaped_hyper_stdtabP P1) /= => <-.
    rewrite intpartn_sumn.
    have := stdtabnP (hyper_stdtab P1); rewrite /is_stdtab => /andP [] _ /=.
    move /shsh_sfilterleq => HH/HH{HH}.
    rewrite -size_to_word -size_tab_P1 /sfilterleq /=.
    by rewrite to_word_skew_reshape //= size_std size_yam sumn_diffE.
  apply perm_eq_stdE.
  - by rewrite perm_eq_evalseq !eval_yameval.
  - by rewrite (invf x) (invf y) H.
Qed.

Lemma bijLR_image : LRtab_set P1 P2 P = [set bijLR x | x in LRyam_set].
Proof.
  rewrite -setP => Q.
  apply/(sameP idP); apply(iffP idP).
  - move/imsetP => [] y Hy ->.
    rewrite /LRtab_set inE (bijLR_LR_support Hy) /=.
    by rewrite shape_bijLR.
  - move/bijLR_surj => [] y Hy <-.
    by apply mem_imset.
Qed.

Theorem LR_coeff_yamP : LRtab_coeff P1 P2 P = LRyam_coeff.
Proof.
  rewrite /LRtab_coeff /LRyam_coeff.
  suff -> : LRtab_set P1 P2 P = bijLR @: LRyam_set by apply card_in_imset; apply bijLR_inj.
  exact: bijLR_image.
Qed.

(* Unused ************************)
Definition LRyam_enum (P1 P2 P : seq nat) :=
  [seq x <- enum_yameval P2 | is_skew_reshape_tableau x].
Definition LRyam_compute (P1 P2 P : seq nat) := size (LRyam_enum P1 P2 P).

Lemma LR_coeff_computeP : LRyam_compute P1 P2 P = LRyam_coeff.
Proof.
  rewrite /LRyam_coeff /LRyam_set /LRyam_compute /LRyam_enum.
  rewrite cardE (eq_enum (in_set _)) /enum_mem -enumT.
  rewrite (eq_filter (a2 := (fun x => is_skew_reshape_tableau (val x)))).
  - by rewrite -(size_map val) map_filter_comp enum_yamevalE map_id.
  - by move=> i /=; rewrite unfold_in.
Qed.
(* End of Unused *****************)

End OneCoeff.

Lemma included_shape_filter_gtnX_tab (T : ordType) (n : T) t :
  is_tableau t ->
  included (shape (filter_gtnX_tab n t)) (shape t).
Proof.
  elim: t => [//= | r0 t /= IHt] /= /and4P [] Hnnil Hrow Hdom Htab.
  case: (altP ([seq x <- r0 | (x < n)%Ord] =P [::])) => Hr0 /=.
    rewrite (filter_leqX_first_row0 Htab Hdom Hr0).
    set f := filter _ _; by have -> : f = [::] by rewrite /f; by elim: (size t).
  by rewrite size_filter count_size (IHt Htab).
Qed.

Lemma LRtab_set_included (P : intpartn (d1 + d2)) Q :
  Q \in LRtab_set P1 P2 P -> included P1 P.
Proof.
  rewrite !inE => /andP [] Hhas /eqP <-.
  have {Hhas} Hpred : predLRTripleFast (hyper_stdtab P1) (hyper_stdtab P2) Q by [].
  rewrite -(shaped_hyper_stdtabP P1) /=.
  have {Hpred} /= -> :=
    predLRTripleFast_filter_gtnX (stdtabnP (hyper_stdtab P1)) (stdtabnP Q) Hpred.
  case: Q => Q /= /andP [].
  rewrite /is_stdtab => /andP [] HQ _ _.
  by apply included_shape_filter_gtnX_tab.
Qed.


Require Import ssralg.

Local Open Scope ring_scope.
Import GRing.Theory.

Variable (n : nat) (R : comRingType).

Hypothesis Hnpos : n != 0%N.

Notation Schur p := (Schur Hnpos R p).

Theorem LRtab_coeffP :
  Schur P1 * Schur P2 =
  \sum_(P : intpartn (d1 + d2) | included P1 P) Schur P *+ LRyam_coeff P.
Proof.
  rewrite LRtab_coeffP.
  rewrite (bigID (fun P : intpartn (d1 + d2) => included P1 P) predT) /=.
  set S := (X in _ + X); have {S} -> : S = 0.
    rewrite /S{S}.
    rewrite (eq_bigr (fun _ => 0)).
    - by rewrite sumr_const mul0rn.
    - move=> P Hincl.
      suff -> : LRtab_coeff P1 P2 P = 0%nat by apply mulr0n.
      apply/eqP; move: Hincl; apply contraR.
      rewrite /LRtab_coeff cards_eq0 => /set0Pn [] Q.
      by apply LRtab_set_included.
  rewrite addr0.
  by apply: eq_bigr => P /LR_coeff_yamP ->.
Qed.

End LR.



