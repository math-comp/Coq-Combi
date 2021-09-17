(** * Combi.LRrule.therule : The Littlewood-Richardson rule *)
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
(** * The Littlewood-Richardson rule

The goal of this file is to formalize the final step ot the proof: a bijection
beetween LR-standard tableau as defined in [LRsupport Q1 Q2] and LR-Yamanouchi
tableaux.

Below we use the following notation:
- [d1] and [d2] are [nat],
- [P1] : a partition of d1 (of type: [inpartn d1]).
- [P2] : a partition of d2 (of type: [inpartn d2]).
- [P] : a partition of d1 + d2 (of type: [inpartn d1 + d2]).


We define the following:
- [is_skew_reshape_tableau P P1 w] == w is the row reading of a skew tableau of
             shape P/P1. Equivalently, the P/P1-reshape of w is a skew tableau.
- [bijLRyam P P1] == a map from [seq nat] to [seq (seq nat)] which defines a
             bijection between LR yamanouchi tableaux and LR-standard tableaux
- [bijLR P P1] == the sigma-type version of bijLRyam:
                  [(yam : yameval P2) -> stdtabn (d1 + d2)]

- [LRyam_set P1 P2 P] == the set of LR Yamanouchi words.
- [LRyam_coeff P1 P2 P] == the LR coefficient defined as the cardinality of
             the set of LR Yamanouchi words.

- [LRyam_enum P1 P2 P] == a list for the LR Yamanouchi words.
- [LRyam_compute P1 P2 P] == the length LRyam_enum, allows to compute LR-coeffs
             and LR-tableaux from the definition inside coq. As an
             implementation, its a very slow way to compute LR-coeff. Indeed,
             the set of Yamanouchi words where we are looking for LR words is
             much too large. The module [implem] will provide a much efficient
             way using backtracking instead of filtering to enumerate those.

- [yamrow n] == the trivial Yamanouchi word of size n whis is constant to 0


The main theorem is [Theorem LRyam_coeffP]:

[
  Schur P1 * Schur P2 =
  \sum_(P : 'P_(d1 + d2) | included P1 P) Schur P *+ LRyam_coeff P.
]

As a corollary we provide the two Pieri rules [Pieri_rowpartn] and
[Pieri_colpartn].
*******************************************************************************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple finfun finset bigop path ssralg order.
From SsrMultinomials Require Import mpoly.

Require Import tools ordcast combclass partition skewpart Yamanouchi ordtype.
Require Import std tableau stdtab Schensted congr plactic Greene_inv.
Require Import stdplact Yam_plact skewtab shuffle Schur_mpoly freeSchur.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.
Open Scope N.
Local Open Scope Combi.

(** * Gluing a standard tableaux with a skew tableau *)
Section LR.

Lemma to_word_map_shiftn sh t :
  to_word (map (shiftn sh) t) = shiftn sh (to_word t).
Proof.
rewrite /shiftn.
elim: t => [//= | t0 t IHt] /=.
by rewrite !to_word_cons IHt map_cat.
Qed.

Lemma filter_le_shiftn sh t :
  [seq x - sh | x <- [seq sh + i | i <- t] & sh <= x] = t.
Proof. by elim: t => [//= | l0 r IHt] /=; rewrite leq_addr /= addKn IHt. Qed.

Lemma filter_gt_shiftn sh t :
  [seq x <- [seq sh + i | i <- t] | gtn sh x] = [::].
Proof. by elim: t => [//= | l0 r /= ->] /=; rewrite ltnNge leq_addr. Qed.

Lemma shiftn_skew_dominate n sh u v :
  skew_dominate sh u v -> skew_dominate sh (shiftn n u) (shiftn n v).
Proof.
rewrite /skew_dominate /dominate !size_map => /andP [Hsz].
rewrite -map_drop size_map Hsz /=.
set p1 := (X in all X) => H.
set p2 := (X in all X).
rewrite (eq_in_all (a2 := p1)) //=.
move => i /=; rewrite mem_iota add0n => /= Hi1.
case (leqP sh (size u)) => Hu.
+ rewrite /p1 /p2 {p1 p2 H} /shiftn.
  rewrite !ltEnat /= (nth_map inh _ _ (leq_trans Hi1 Hsz)) (nth_map inh _ _ Hi1).
  by rewrite ltn_add2l.
+ exfalso; move: Hi1; rewrite size_drop.
  move: Hu => /ltnW; rewrite {1}/leq => /eqP ->.
  by rewrite ltn0.
Qed.

Lemma is_skew_tableau_map_shiftn sh inn t :
  is_skew_tableau inn t -> is_skew_tableau inn (map (shiftn sh) t).
Proof.
elim: t inn => [//= | r0 t IHt] /= inn.
move=> /and4P [Hszr0 Hrow0 Hdom Hskew].
apply/and4P; split.
- by rewrite size_map.
- rewrite /shiftn.
  case: r0 Hrow0 {Hdom Hskew IHt Hszr0} => [//= | l0 r] /= H.
  rewrite (map_path (e' := <=%O) (b := pred0)).
  + exact: H.
  + by move=> i j /= _; rewrite !leEnat leq_add2l.
  + by apply/hasPn => i.
- have -> : head [::] (map (shiftn sh) t) = shiftn sh (head [::] t) by case t.
  exact: shiftn_skew_dominate.
- exact: IHt.
Qed.

Lemma join_stdtab s t :
  is_stdtab s -> is_skew_tableau (shape s) t ->
  is_tableau (join_tab s (map (shiftn (size_tab s)) t)).
Proof.
rewrite /is_stdtab => /andP [].
rewrite /is_std size_to_word /= => Htabs
    Hperm /(is_skew_tableau_map_shiftn (size_tab s)).
apply: join_tab_skew; last exact Htabs.
rewrite {2}/to_word -map_rev -map_flatten.
move: (flatten (rev t)) => w.
apply/allP => x /mapP [i _ -> {x}].
rewrite /allLtn; apply/allP => j.
rewrite (perm_mem Hperm) mem_iota /= add0n ltEnat => /leq_trans; apply.
exact: leq_addr.
Qed.

Lemma join_stdtab_in_shuffle s t :
  is_stdtab s ->
  size s <= size t ->
  to_word (join_tab s (map (shiftn (size_tab s)) t)) \in
       shsh (to_word s) (to_word t).
Proof.
rewrite /join_tab /is_stdtab => /andP [_ Hstd] Hsize.
rewrite (mem_shsh _ _ Hstd).
move: Hstd; rewrite /is_std size_to_word /= => Hperm.
have {Hperm} : all (gtn (size_tab s)) (to_word s).
  apply/allP => i; rewrite (perm_mem Hperm).
  by rewrite mem_iota /= add0n.
move: (size_tab s) => sh.
rewrite /shiftn => Hall; apply /andP; split; apply/eqP.
- elim: s t Hsize Hall => [| s0 s IHs] /= t.
  + rewrite subn0 size_map => _ _.
    rewrite (_ : map _ _ = map (shiftn sh) t); last by elim: t => //= r t ->.
    elim: t => [//= | t0 t IHt] /=.
    rewrite to_word_cons filter_cat IHt cat0s {t IHt}.
    by rewrite filter_gt_shiftn.
  + case: t => [//= | t0 t] /=.
    rewrite ltnS to_word_cons all_cat => {}/IHs Hrec /andP [{}/Hrec Hrec].
    rewrite to_word_cons !filter_cat subSS Hrec {Hrec} => /all_filterP ->.
    suff -> : [seq x <- [seq sh + i | i <- t0] | gtn sh x] = [::].
      by rewrite cats0.
    by rewrite filter_gt_shiftn.
- elim: s t Hsize Hall => [| s0 s IHs] /= t.
  + rewrite subn0 size_map => _ _.
    elim: t => [//= | t0 t IHt] /=.
    rewrite !to_word_cons !filter_cat map_cat IHt {IHt}.
    by rewrite filter_le_shiftn.
  + case: t => [//= | t0 t] /=.
    rewrite ltnS to_word_cons all_cat => {}/IHs Hrec /andP [{}/Hrec Hrec].
    rewrite !to_word_cons !filter_cat !map_cat subSS Hrec {Hrec}.
    rewrite filter_le_shiftn => Hall.
    suff -> : [seq x - sh | x <- s0 & sh <= x] = [::] by rewrite cat0s.
    elim: s0 Hall {t s t0} => [//= | l0 s IHs] /= /andP [H /IHs].
    by rewrite leqNgt H.
Qed.

Variables d1 d2 : nat.

Section TheRule.

Variables (P1 : 'P_d1) (P2 : 'P_d2).

Lemma sfilterleq_LRsupportP Q :
  Q \in LRsupport (hyper_stdtabn P1) (hyper_stdtabn P2) ->
  exists y : yameval P2, std y = (sfilterleq d1 (to_word Q)).
Proof using .
rewrite /LRsupport inE -LRtriple_fastE //.
move/(LRtripleP _ (stdtabnP (hyper_stdtabn P1)) (stdtabnP (hyper_stdtabn P2))).
move=> [p1 p2 p]; rewrite /hyper_stdtab => Hp1 Hp2 Hp.
have Hstdp1 : is_std p1 by rewrite -RSstdE Hp1.
rewrite (mem_shsh _ _ Hstdp1) => /andP [].
rewrite -(size_RS p1) Hp1.
rewrite (size_tab_stdtabn (hyper_stdtabn P1)) => /eqP Hsfp1 /eqP Hsfp2.
suff : sfilterleq d1 (to_word Q) =Pl std (hyper_yam P2).
  move/(plact_from_yam (intpartnP P2)) => [yam].
  rewrite -[val P2]/(val (intpart_of_intpartn P2)) => Hyam.
  by exists (YamEval Hyam).
rewrite /=/hyper_stdtab in Hp2.
rewrite -Hp plactic_RS -Hp2 -Hsfp2 eq_sym -plactic_RS.
rewrite /sfilterleq /=.
apply: plact_map_in_incr.
  move=> i j; rewrite !mem_filter => /andP [Hi _] /andP [Hj _].
  rewrite !ltEnat /= => Hij.
  by rewrite ltn_subRL subnKC.
apply: (plactic_filter_le d1).
exact: congr_RS.
Qed.

Lemma filter_gt_to_word (d : unit) (T : inhOrderType d) n (t : seq (seq T)) :
  filter (>%O n) (to_word t) = to_word (filter_gt_tab n t).
Proof using .
elim: t => [//= | t0 t IHt] /=.
rewrite to_word_cons filter_cat /=.
case: (altP (filter (>%O n) t0 =P [::])) => H /=.
- by rewrite H cats0 IHt.
- by rewrite to_word_cons IHt.
Qed.

Lemma filter_le_to_word (d : unit) (T : inhOrderType d) n (t : seq (seq T)) :
  filter (<=%O n) (to_word t) = to_word (filter_le_tab n t).
Proof using .
elim: t => [//= | t0 t IHt] /=.
rewrite to_word_cons filter_cat /=.
case: (altP (filter (<=%O n) t0 =P [::])) => H /=.
- by rewrite H cats0 IHt to_word_cons cats0.
- by rewrite to_word_cons IHt.
Qed.

(** * Littlewood-Richardson Yamanouchi tableaux *)
Section OneCoeff.

Variable P : 'P_(d1 + d2).
Hypothesis Hincl : included P1 P.

Lemma sumn_diff_shape_intpartE : sumn (P / P1) = sumn P2.
Proof using Hincl.
by rewrite (sumn_diff_shape Hincl) !sumn_intpartn addKn.
Qed.

Definition is_skew_reshape_tableau (P P1 : seq nat) (w : seq nat) :=
  is_skew_tableau P1 (skew_reshape P1 P w).
Definition LRyam_set :=
  [set y : yameval P2 | is_skew_reshape_tableau P P1 y].
Definition LRyam_coeff := #|LRyam_set|.

Lemma is_skew_reshape_tableauP (w : seq nat) :
  size w = sumn (P / P1) ->
  reflect
    (exists tab, [/\ is_skew_tableau P1 tab,
                  shape tab = P / P1 & to_word tab = w])
    (is_skew_reshape_tableau P P1 w).
Proof using Hincl.
rewrite /is_skew_reshape_tableau => Hsize; apply (iffP idP).
- move=> H; exists (skew_reshape P1 P w); split; first exact H.
  + exact: (shape_skew_reshape Hincl Hsize).
  + exact: (to_word_skew_reshape Hincl Hsize).
- move=> [tab] [Htab Hsh <-].
  rewrite -(diff_shapeK Hincl) -Hsh.
  rewrite skew_reshapeK; first exact Htab.
  rewrite -(size_map size) -/(shape tab) Hsh size_diff_shape.
  exact: size_included.
Qed.

Lemma size_leq_skew_reshape (y : seq nat) :
  size (RS (std (hyper_yam P1))) <= size (skew_reshape P1 P y).
Proof using Hincl.
rewrite -(size_map size) -/(shape (RS _)) shape_RS_std.
rewrite shape_RS_yam; last by apply hyper_yamP; apply intpartnP.
rewrite (evalseq_hyper_yam (intpartnP P1)).
rewrite size_skew_reshape; exact: size_included.
Qed.

(** ** The final bijection *)
Definition bijLRyam :=
  [fun y : seq nat =>
     join_tab (hyper_stdtabn P1) (map (shiftn d1) (skew_reshape P1 P (std y)))].

Lemma pred_LRtriple_fast_bijLRyam (yam : yameval P2) :
  is_skew_reshape_tableau P P1 yam ->
  pred_LRtriple_fast (hyper_stdtabn P1) (hyper_stdtabn P2) (bijLRyam yam).
Proof using Hincl.
rewrite/is_skew_reshape_tableau => Hskew.
apply/hasP; exists (std yam).
  rewrite RSclassE; last exact: is_tableau_RS.
  rewrite -plactic_RS.
  apply: std_plact.
  have /= <- := eval_yameval yam.
  apply yam_plactic_hyper; exact: yamevalP.
have Hstd1 : is_std (to_word (hyper_stdtabn P1)).
  have /= := hyper_stdtabnP P1 => /andP [].
  by rewrite /is_stdtab => /andP [].
rewrite -[std yam](to_word_skew_reshape Hincl); first last.
  by rewrite size_std size_yameval sumn_diff_shape_intpartE.
rewrite /= -{2}(size_tab_stdtabn (hyper_stdtabn P1)).
apply: join_stdtab_in_shuffle.
- rewrite RSstdE; exact: std_is_std.
- exact: size_leq_skew_reshape.
Qed.

Lemma bijLRyamP (yam : yameval P2) :
  is_skew_reshape_tableau P P1 yam -> is_stdtab_of_n (d1 + d2) (bijLRyam yam).
Proof using Hincl.
rewrite /is_skew_reshape_tableau /= /is_stdtab => Hskew.
rewrite (_ : size_tab _ = d1 + d2); first last.
  rewrite size_join_tab.
  + rewrite size_RS size_std size_hyper_yam sumn_intpartn; congr (_ + _).
    rewrite /size_tab /shape -map_comp.
    rewrite (eq_map (f2 := size)); last by move=> s /=; rewrite size_map.
    rewrite -/(shape _) (shape_skew_reshape Hincl).
    * by rewrite (sumn_diff_shape Hincl) !sumn_intpartn addKn.
    * by rewrite size_std size_yameval sumn_diff_shape_intpartE.
  + rewrite size_map; exact: size_leq_skew_reshape.
rewrite eq_refl andbT.
apply/andP; split.
- rewrite -{2}(size_tab_stdtabn (hyper_stdtabn P1)).
  apply join_stdtab.
  rewrite RSstdE; exact: std_is_std.
- rewrite shape_RS_std shape_RS_yam; last by apply hyper_yamP; apply intpartnP.
  rewrite (evalseq_hyper_yam (intpartnP P1)).
  rewrite -(is_skew_tableau_reshape_std (size_included Hincl)).
  + exact: Hskew.
  + by rewrite size_yameval sumn_diff_shape_intpartE.
- have /= /hasP [] := pred_LRtriple_fast_bijLRyam Hskew => z.
  move: (to_word _) => image.
  rewrite (RSclassE _ (is_tableau_RS _)) -plactic_RS => /plact_homog Hz.
  have {}Hz : is_std z by apply: (perm_std _ Hz); apply std_is_std.
  have : is_stdtab (RS (std (hyper_yam P1))) by rewrite RSstdE; apply std_is_std.
  rewrite /is_stdtab => /andP [_ Hstd1].
  exact: (allP (std_shsh Hstd1 Hz)).
Qed.

Definition bijLR (yam : yameval P2) : stdtabn (d1 + d2) :=
  if (boolP (is_skew_reshape_tableau P P1 yam)) is AltTrue pf then
    StdtabN (bijLRyamP pf)
  else
    hyper_stdtabn P.

Lemma bijLR_LRsupport yam :
  yam \in LRyam_set ->
  bijLR yam \in LRsupport (hyper_stdtabn P1) (hyper_stdtabn P2).
Proof using .
rewrite !inE /bijLR /= => Hskew.
case (boolP (is_skew_reshape_tableau P P1 yam)) => /=; last by rewrite Hskew.
by move/pred_LRtriple_fast_bijLRyam => /=.
Qed.

Lemma filtergtn_LRsupport Q :
  Q \in LRsupport (hyper_stdtabn P1) (hyper_stdtabn P2) ->
  filter_gt_tab d1 Q = hyper_stdtabn P1.
Proof using .
rewrite inE.
move/(pred_LRtriple_fast_filter_gt
        (stdtabnP (hyper_stdtabn P1)) (stdtabnP Q)) => ->.
by rewrite size_tab_stdtabn.
Qed.

Lemma size_zip2 (T : Type) (s t : seq (seq T)) :
  [seq size p.1 + size p.2 | p <- zip s t] =
  [seq p.1 + p.2 | p <- zip (map size s) (map size t)].
Proof using .
elim: s t => [| s0 s IHs] /=; first by elim=> [| t0 t IHt].
case => [//= | t0 t] /=.
by rewrite -IHs.
Qed.

Lemma shape_bijLR yam : yam \in LRyam_set -> shape (bijLR yam) = P.
Proof using .
rewrite !inE /bijLR /= => Hskew.
case (boolP (is_skew_reshape_tableau P P1 yam)) => [_|] /=; last by rewrite Hskew.
rewrite /shape /join_tab.
rewrite !size_map -map_comp.
rewrite (eq_map (f2 := fun p => size p.1 + size p.2)); first last.
  by move=> i /=; rewrite size_cat.
rewrite size_zip2 size_skew_reshape.
rewrite (_ : map size _ = pad 0 (size P) P1); first last.
  rewrite /pad /= map_cat.
  rewrite -(size_map size) -/(shape (RS _)) shape_RS_std.
  rewrite shape_RS_yam; last by apply hyper_yamP; apply intpartnP.
  rewrite (evalseq_hyper_yam (intpartnP P1)).
  by rewrite map_nseq.
rewrite (_ : map size _ = P / P1); first last.
  rewrite /= -map_comp.
  rewrite (eq_map (f2 := size)); last by move=> i /=; rewrite size_map.
  rewrite -/(shape _) shape_skew_reshape //=.
  by rewrite size_std size_yameval sumn_diff_shape_intpartE.
rewrite -(size_diff_shape P1 P).
rewrite -/(outer_shape P1 (P / P1)).
exact: diff_shapeK.
Qed.

Lemma filterleq_LRsupport Q :
  Q \in LRtab_set P1 P2 P ->
  (skew_reshape P1 P [seq x <- to_word Q | d1 <= x]) = filter_le_tab d1 Q.
Proof using .
rewrite /LRtab_set inE => /andP [HLR /eqP Hshape].
rewrite /filter_le_tab -Hshape filter_le_to_word /=.
have -> : val P1 = shape (filter_gt_tab d1 Q).
  by rewrite (filtergtn_LRsupport HLR) -{1}(shaped_hyper_stdtabnP P1) /=.
set t := map _ _.
have -> : shape Q = outer_shape (shape (filter_gt_tab d1 Q)) (shape t).
  rewrite /outer_shape /= /t {t}.
  have:= stdtabP (stdtabnP Q) => /(join_tab_filter d1) {1}<-.
  rewrite /= /shape /join_tab /pad /=.
  rewrite !size_map -map_comp.
  rewrite (eq_map (f2 := fun p => size p.1 + size p.2)); first last.
    by move=> i /=; rewrite size_cat.
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

Lemma sfilterleq_LRsupport_skew Q :
  Q \in LRtab_set P1 P2 P ->
        is_skew_reshape_tableau P P1 (sfilterleq d1 (to_word Q)).
Proof using Hincl.
have:= stdtabnP (hyper_stdtabn P2); rewrite /is_stdtab => /andP [Htab2 Hstd2].
have /allP /= Hall := RSclassP Htab2.
move=> HLRtab.
have := HLRtab; rewrite /LRtab_set inE => /andP [HLR /eqP Hshape].
have Hfilter := filtergtn_LRsupport HLR.
have:= HLR; rewrite inE /= => /hasP [] p2 /Hall{Hall} /Sch_plact Hpl Hshsh.
have:= hyper_stdtabnP P1 => /=.
rewrite /is_stdtab => /andP [/andP [_ Hstd] /= /eqP Hsz].
have:= (shsh_sfilterleq Hstd Hshsh).
rewrite size_to_word Hsz /= {Hstd Hsz} => Hp2; subst p2.
apply (eq_inv_is_skew_tableau_reshape (u1 := [seq x <- to_word Q | d1 <= x])).
- exact: size_included.
- apply/eq_invP; split; first by rewrite size_map.
  move=> i j /andP [Hij Hj].
  rewrite (nth_map inh); last exact: (leq_ltn_trans Hij Hj).
  rewrite (nth_map inh); last exact: Hj.
  rewrite !leEnat leq_subLR subnKC //=.
  by have:= mem_nth inh Hj; rewrite mem_filter => /andP [].
- move: Hpl => /plact_homog/perm_size.
  rewrite size_map => ->.
  by rewrite size_std sumn_diff_shape_intpartE -evalseq_eq_size evalseq_hyper_yam.
- rewrite (filterleq_LRsupport HLRtab).
  have -> : val P1 = shape (filter_gt_tab d1 Q).
    by rewrite Hfilter -{1}(shaped_hyper_stdtabnP P1) /=.
  apply is_skew_tableau_filter_le; exact: stdtabP.
Qed.

Lemma bijLR_surj Q :
  Q \in LRtab_set P1 P2 P -> exists2 yam, yam \in LRyam_set & bijLR yam = Q.
Proof using .
move=> HLRtab; have:= HLRtab; rewrite /LRtab_set inE => /andP [HLR /eqP Hshape].
have:= HLR => /sfilterleq_LRsupportP [] y Hmap.
have Hskew : is_skew_reshape_tableau P P1 y.
  rewrite /is_skew_reshape_tableau
          (is_skew_tableau_reshape_std (size_included Hincl)).
  + rewrite Hmap; exact: sfilterleq_LRsupport_skew.
  + by rewrite size_yameval sumn_diff_shape_intpartE.
exists y.
- rewrite inE /=; exact Hskew.
- rewrite /bijLR.
  case (boolP (is_skew_reshape_tableau P P1 y)) => /=; last by rewrite Hskew.
  move=> pf; apply val_inj => /= {pf}.
  have -> : hyper_stdtab P1 = filter_gt_tab d1 Q.
    have:= hyper_stdtabnP P1 => /andP [Htab1 /eqP Hsz1].
    rewrite inE in HLR.
    rewrite (pred_LRtriple_fast_filter_gt Htab1 (stdtabnP Q) HLR).
    by rewrite Hsz1.
  have -> : [seq shiftn d1 i | i <- skew_reshape P1 P (std y)] =
              filter_le_tab d1 Q.
    rewrite Hmap /= /skew_reshape map_rev map_reshape -/(shiftn d1) sfilterleqK.
    by rewrite -/(skew_reshape _ _ _) filterleq_LRsupport.
  rewrite join_tab_filter //=; exact: stdtabP.
Qed.

Lemma bijLR_inj : {in LRyam_set &, injective bijLR}.
Proof using .
move=> x y; rewrite !inE /bijLR => Hx Hy.
case (boolP (is_skew_reshape_tableau P P1 x)) => /=; last by rewrite Hx.
case (boolP (is_skew_reshape_tableau P P1 y)) => /=; last by rewrite Hy.
move=> Hy1 Hx1 /(congr1 (@val _ _ _))/(congr1 to_word) /= {Hx1 Hy1 Hx Hy} => H.
apply val_inj => /=.
pose f := [fun s : seq nat =>
             to_word (join_tab (hyper_stdtabn P1)
                               (map (shiftn d1) (skew_reshape P1 P s)))].
have {H} Heq : f (std x) = f (std y) by rewrite /= H.
have invf (s : yameval P2) : std s = sfilterleq d1 (f (std s)).
  have /= := join_stdtab_in_shuffle
               (stdtabnP (hyper_stdtabn P1)) (size_leq_skew_reshape (std s)).
  rewrite /size_tab.
  have /= -> := congr1 (@val _ _ _) (shaped_hyper_stdtabnP P1).
  rewrite sumn_intpartn.
  have:= stdtabnP (hyper_stdtabn P1); rewrite /is_stdtab => /andP [_ /=].
  move /shsh_sfilterleq => H{}/H.
  rewrite size_to_word (size_tab_stdtabn (hyper_stdtabn P1)) /sfilterleq /=.
  rewrite to_word_skew_reshape //.
  by rewrite size_std size_yameval sumn_diff_shape_intpartE.
apply perm_stdE.
- by rewrite perm_evalseq !eval_yameval.
- by rewrite (invf x) (invf y) Heq.
Qed.

Lemma bijLR_image : LRtab_set P1 P2 P = [set bijLR x | x in LRyam_set].
Proof using .
apply setP => Q; apply/idP/idP.
- move/bijLR_surj => [y Hy <-].
  exact: imset_f.
- move/imsetP => [y Hy ->].
  rewrite /LRtab_set inE (bijLR_LRsupport Hy) /=.
  by rewrite shape_bijLR.
Qed.

Theorem LRyam_coeffE : LRtab_coeff P1 P2 P = LRyam_coeff.
Proof using Hincl.
rewrite /LRtab_coeff /LRyam_coeff.
suff -> : LRtab_set P1 P2 P = bijLR @: LRyam_set.
  by apply card_in_imset; apply bijLR_inj.
exact: bijLR_image.
Qed.

(** ** A slow way to compute LR coefficients in coq:

We enumerate Yamanouchi words and filter those who are row reading of the skew
tableaux of shape P/P1. This is very innefficient. A better way is to use
backtracking as in [implem].
************************)

Definition LRyam_enum (P1 P2 P : seq nat) :=
  [seq x <- enum_yameval P2 | is_skew_reshape_tableau P P1 x].
Definition LRyam_compute (P1 P2 P : seq nat) := size (LRyam_enum P1 P2 P).

Lemma LRcoeff_computeP : LRyam_compute P1 P2 P = LRyam_coeff.
Proof using .
rewrite /LRyam_coeff /LRyam_set /LRyam_compute /LRyam_enum.
rewrite cardE (eq_enum (in_set _)) /enum_mem -enumT.
rewrite (eq_filter (a2 := (fun x => is_skew_reshape_tableau P P1 (val x)))).
- by rewrite -(size_map val) map_filter_comp enum_yamevalE map_id.
- by move=> i /=; rewrite unfold_in.
Qed.

End OneCoeff.

Lemma included_shape_filter_gt_tab
      (d : unit) (T : inhOrderType d) (n : T) t :
  is_tableau t -> included (shape (filter_gt_tab n t)) (shape t).
Proof using .
elim: t => [//= | r0 t /= IHt] /= /and4P [Hnnil Hrow Hdom Htab].
case: (altP ([seq x <- r0 | (x < n)%O] =P [::])) => Hr0 /=.
  rewrite (filter_le_first_row0 Htab Hdom Hr0).
  by rewrite (_ : filter _ _ = [::]); last by elim: (size t).
by rewrite size_filter count_size (IHt Htab).
Qed.

Lemma LRtab_set_included (P : 'P_(d1 + d2)) Q :
  Q \in LRtab_set P1 P2 P -> included P1 P.
Proof using .
rewrite !inE => /andP [Hhas /eqP <-].
rewrite -(shaped_hyper_stdtabnP P1) /=.
have : pred_LRtriple_fast (hyper_stdtabn P1) (hyper_stdtabn P2) Q by [].
move/(pred_LRtriple_fast_filter_gt
        (stdtabnP (hyper_stdtabn P1)) (stdtabnP Q))=> /= ->.
case: Q {Hhas} => Q /= /andP [].
rewrite /is_stdtab => /andP [HQ _] _.
exact: included_shape_filter_gt_tab.
Qed.

(** * The statement of the Littlewood-Richardson rule *)
Local Open Scope ring_scope.
Import GRing.Theory.

Variable (n0 : nat) (R : comRingType).
Local Notation n := (n0.+1).
Notation Schur p := (Schur n0 R p).

Theorem LRyam_coeffP :
  Schur P1 * Schur P2 =
  \sum_(P : 'P_(d1 + d2) | included P1 P) Schur P *+ LRyam_coeff P.
Proof using .
rewrite LRtab_coeffP.
rewrite (bigID (fun P : 'P_(d1 + d2) => included P1 P) predT) /=.
rewrite [X in _ + X]big1 ?addr0; first last => [P Hincl|].
  suff -> : LRtab_coeff P1 P2 P = 0%N by exact: mulr0n.
  apply/contraNeq: Hincl.
  rewrite /LRtab_coeff cards_eq0 => /set0Pn [Q].
  exact: LRtab_set_included.
by apply: eq_bigr => P /LRyam_coeffE ->.
Qed.

End TheRule.


(** * Pieri's rules *)
Section Pieri.

Local Open Scope ring_scope.
Import GRing.Theory.

Variable (n0 : nat) (R : comRingType).
Local Notation n := (n0.+1).
Notation Schur p := (Schur n0 R p).

Lemma yamrowP :
  is_yam_of_eval (intpart_of_intpartn (rowpartn d2)) (ncons d2 0%N [::]).
Proof using .
rewrite /is_yam_of_eval; elim: d2 => [|d]; rewrite /= !rowpartnE //.
by move=> /andP [/= -> /eqP ->]; case: d => /=.
Qed.
Definition yamrow : yameval (rowpartn d2) := YamEval yamrowP.

Lemma is_row_yamrow : is_row (ncons d2 0%N [::]).
Proof using . by elim: d2 => [| [|d]]. Qed.

Lemma yam_of_rowpart d y : is_yam_of_eval (rowpartn d) y -> y = ncons d 0%N [::].
Proof using .
rewrite rowpartnE => /andP [Hyam /eqP].
elim: d y Hyam => [//= | d IHd] //=.
  move=> y _; exact: evalseq0.
case=> [| y0 y] //= /andP [_ /IHd{IHd} Hrec].
case: y0 => [| y0] /= Heval.
* case Heval: (evalseq y) Heval => [| ev0 ev] //=.
    by move: Heval => /evalseq0 -> [<- /=].
  move => [Hev0 Hev]; subst.
  rewrite Hrec // Heval {Hrec}.
  case: d Heval => [|//=] Heval.
  exfalso; case: y Heval => [//=| y0 y] /=.
  case: (evalseq y) y0 => [| a [| l0 l]] [|[|y0]] //=.
* by exfalso; case: (evalseq y) y0 Heval => [| a [| l0 l]] [|y0].
Qed.

Theorem LRyam_coeff_rowpart (P1 : 'P_d1) (P : 'P_(d1 + d2)) :
included P1 P -> LRyam_coeff P1 (rowpartn d2) P = hb_strip P1 P.
Proof using .
rewrite /LRyam_coeff /LRyam_set => Hincl.
rewrite /is_skew_reshape_tableau.
set LRset := (X in #|pred_of_set X|).
case: (boolP (hb_strip P1 P)) => Hstrip /=.
- suff -> : LRset = [set yamrow] by rewrite cards1.
  apply setP => y; rewrite !inE {LRset}.
  case: y => y Hy /=.
  have -> : (YamEval Hy == yamrow) = (y == (ncons d2 0%N [::])).
    apply/idP/idP => /eqP Heq.
    + by rewrite -[y]/(val (YamEval Hy)) Heq.
    + apply/eqP; exact: val_inj.
  move: Hy => /= /yam_of_rowpart ->.
  rewrite eq_refl; move: Hstrip.
  rewrite -(hb_strip_rowE (intpartnP _) (intpartnP _)
                          (u := (ncons d2 0%N [::]))); first last.
  + rewrite size_ncons /= addn0 (sumn_diff_shape_intpartE (rowpartn d2)) //=.
    by rewrite rowpartnE; case: d2 => [//= | d] /=; rewrite addn0.
  + exact: is_row_yamrow.
  by move=> /andP [].
- suff -> : LRset = set0 by rewrite cards0.
  apply/eqP; rewrite -subset0.
  apply/subsetP => y; rewrite in_set0 inE => Hskew.
  move: Hstrip.
  rewrite -(hb_strip_rowE (intpartnP _) (intpartnP _) (u := y)); first last.
  + rewrite -evalseq_eq_size eval_yameval.
    by rewrite (sumn_diff_shape_intpartE (rowpartn d2)).
  + case: y {Hskew} => y /= Hy.
    suff -> : y = ncons d2 0%N [::] by exact: is_row_yamrow.
    exact: yam_of_rowpart.
  by rewrite Hincl Hskew.
Qed.

Theorem Pieri_rowpartn (P1 : 'P_d1) :
  Schur P1 * Schur (rowpartn d2) =
  \sum_(P : 'P_(d1 + d2) | hb_strip P1 P) Schur P.
Proof using .
rewrite LRyam_coeffP.
rewrite [LHS]big_mkcond [RHS]big_mkcond /=.
apply eq_bigr => p _.
case: (boolP (included P1 p)) => Hincl; first last.
  suff /negbTE -> : ~~ hb_strip P1 p by [].
  move: Hincl; apply contra; exact: hb_strip_included.
rewrite (LRyam_coeff_rowpart Hincl).
by case: (hb_strip P1 p); rewrite /= ?mulr1n ?mulr0n.
Qed.

Theorem LRyam_coeff_colpartn (P1 : 'P_d1) (P : 'P_(d1 + d2)) :
  included P1 P -> LRyam_coeff P1 (colpartn d2) P = vb_strip P1 P.
Proof using .
move=> Hincl.
have Hinclc : included (conj_intpartn P1) (conj_intpartn P).
  exact: included_conj_part.
rewrite -conj_rowpartn -{1}(conj_intpartnK P1) -{1}(conj_intpartnK P).
rewrite -LRyam_coeffE; last by rewrite !conj_intpartnK.
rewrite -LRtab_coeff_conj (LRyam_coeffE _ Hinclc) (LRyam_coeff_rowpart Hinclc).
by rewrite /= hb_strip_conjE.
Qed.

Theorem Pieri_colpartn (P1 : 'P_d1) :
  Schur P1 * Schur (colpartn d2) =
  \sum_(P : 'P_(d1 + d2) | vb_strip P1 P) Schur P.
Proof using .
rewrite LRyam_coeffP.
rewrite [LHS]big_mkcond [RHS]big_mkcond /=.
apply eq_bigr => p _.
case: (boolP (included P1 p)) => Hincl; first last.
  suff /negbTE -> : ~~ vb_strip P1 p by [].
  move: Hincl; apply contra; exact: vb_strip_included.
rewrite (LRyam_coeff_colpartn Hincl).
by case: (vb_strip P1 p); rewrite /= ?mulr1n ?mulr0n.
Qed.

End Pieri.

End LR.
