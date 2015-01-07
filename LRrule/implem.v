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

Require Import tools partition yama schensted ordtype std stdtab invseq congr plactic greeninv.
Require Import yamplact skewtab shuffle multpoly therule.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N.


Lemma head_pad0 (T : Type) n (p : T) s : head p (pad p n s) = head p s.
Proof. elim: s => [| s0 s IHs] //=; rewrite subn0; by case: n. Qed.

Lemma included_pad0 inner outer :
  included inner outer = included (pad 0 (size outer) inner) outer.
Proof.
  elim: inner outer => [//= | inn0 inn IHinn] /= outer /=.
    rewrite subn0; by elim: outer.
  case: outer => [//= | out0 out] /=.
  by rewrite subSS IHinn.
Qed.

Lemma sorted_is_part p :
  is_part p -> sorted geq p.
Proof.
  case: p => [//= | p0 p] /= /andP [].
  elim: p p0 => [//= | p1 p IHp] /= p0 -> /andP [] /=.
  by apply IHp.
Qed.

Lemma is_part_pad0 n p :
  is_part p -> sorted geq (pad 0 n p).
Proof.
  have Hpath x i : path geq x (nseq i 0).
    case: i => [//= | i] /=; by elim: i.
  case: p => [_ | p0 p]; case: n => [| n /=] //=.
    rewrite cats0 -/(sorted geq (p0 :: p)) -/(is_part (p0 :: p)).
    by apply sorted_is_part.
  rewrite subSS.
  elim: p p0 n => [| p1 p IHp] /= p0 n.
    move=> _; by apply Hpath.
  move=> /andP [] -> /IHp{IHp} Hrec /=.
  case: n => [| n /=].
    have := Hrec 0; by rewrite !sub0n.
  rewrite subSS; by apply Hrec.
Qed.

(* COQ implementation of the LR rule *)
Section OutEval.

Variable outev : seq nat.

Definition choose_one_letter innev mini maxi :=
  filter
    (fun i => is_in_corner innev i && (nth 0 innev i < nth 0 outev i))
    (iota mini ((minn (size innev) maxi).+1 - mini) ).

Fixpoint yamtab_row innev row :=
  if row is r0 :: tlr then
    flatten [seq
               [seq (i :: res.1, incr_nth res.2 i) |
                i <- choose_one_letter res.2 r0.+1 (head (size outev) res.1)
               ] |
             res <- yamtab_row innev tlr ]
  else [:: ([::], innev) ].

Fixpoint yamtab_shift innev sh sol :=
  if sh is s.+1 then
    let maxi := head (size innev) sol in
    flatten [seq
               [seq (i :: res.1, incr_nth res.2 i) |
                i <- choose_one_letter res.2 0 (head maxi res.1)
               ] |
             res <- yamtab_shift innev s sol ]
  else [:: (sol, innev) ].

Fixpoint LRyamtab_list_rec innev inner outer sh0 row0 :=
  if outer is out0 :: out then
    let inn0 := head 0 inner in let inn := behead inner in
    let rowres := yamtab_row innev (take (out0 - sh0) row0) in
    let rows :=
        flatten [seq yamtab_shift res.2 ((minn sh0 out0) - inn0) res.1
                | res <- rowres ] in
    flatten [seq [seq row.1 :: tab |
                  tab <- LRyamtab_list_rec row.2 inn out inn0 row.1] |
             row <- rows]
  else [:: [::]].

Fixpoint LRyamtab_count_rec innev inner outer sh0 row0 :=
  if outer is out0 :: out then
    let inn0 := head 0 inner in let inn := behead inner in
    let rowres := yamtab_row innev (take (out0 - sh0) row0) in
    sumn [seq sumn [seq LRyamtab_count_rec row.2 inn out inn0 row.1 |
                    row <- yamtab_shift res.2 ((minn sh0 out0) - inn0) res.1 ]
         | res <- rowres ]
  else 1.

Lemma LRyam_tab_countE innev inner outer sh0 row0 :
  size (LRyamtab_list_rec innev inner outer sh0 row0) =
  LRyamtab_count_rec innev inner outer sh0 row0.
Proof.
  elim: outer innev inner sh0 row0 => [//= | out0 out IHout] /= innev inner sh0 row0.
  rewrite size_flatten /shape !map_flatten sumn_flatten -map_comp.
  congr (sumn _).
  rewrite (eq_map (f2 := map (fun row =>
                     LRyamtab_count_rec row.2 (behead inner) out (head 0 inner) row.1))).
  - rewrite -!map_comp; by apply eq_map.
  - move=> s /=; rewrite -map_comp; apply eq_map => {s} [] [row sh] /=.
    by rewrite size_map IHout.
Qed.

(* LRyamtab_list_rec returns Yamanouchi words *)
Lemma choose_one_letterP innev mini maxi y :
  is_yam_of_shape innev y ->
  forall i, i \in choose_one_letter innev mini maxi ->
                  is_yam_of_shape (incr_nth innev i) (i :: y).
Proof.
  rewrite /is_yam_of_shape => /andP [] Hyam /eqP <- i.
  rewrite mem_filter mem_iota => /andP [] /andP [] Hcorn _ _.
  apply/andP; split => //=.
  rewrite Hyam andbT.
  apply is_part_incr_nth; last exact Hcorn.
  by apply is_part_shyam.
Qed.

Lemma yamtab_rowP innev row y :
  is_yam_of_shape innev y ->
  forall res shape, (res, shape) \in yamtab_row innev row ->
  is_yam_of_shape shape (res ++ y).
Proof.
  elim: row y innev => [| r0 tlr IHrow] /= y innev Hy res shres.
    rewrite mem_seq1 => /eqP [] -> ->.
    by rewrite cat0s.
  move/flatten_mapP => [[rec shrec]] /(IHrow y innev Hy) {IHrow} Hrec.
  by move/mapP => [i] /(choose_one_letterP Hrec) {Hrec} /= Hrec [] -> ->.
Qed.

Lemma yamtab_shiftP innev sh row y :
  is_yam_of_shape innev (row ++ y) ->
  forall res shape, (res, shape) \in yamtab_shift innev sh row ->
  is_yam_of_shape shape (res ++ y).
Proof.
  elim: sh y row innev => [| sh IHsh] /= y row innev Hy res shres.
    by rewrite mem_seq1 => /eqP [] -> ->.
  move/flatten_mapP => [[rec shrec]] /(IHsh y row innev Hy) {IHsh} Hrec.
  by move/mapP => [i] /(choose_one_letterP Hrec) {Hrec} /= Hrec [] -> ->.
Qed.

Lemma LRyamtab_list_recP innev inner outer sh0 row0 y :
  is_yam_of_shape innev y ->
  forall res, res \in LRyamtab_list_rec innev inner outer sh0 row0 ->
  is_yam (to_word res ++ y).
Proof.
  elim: outer innev inner sh0 row0 y => [//= | out0 out IHout] /=
              innev inner sh0 row0 y Hy res.
    rewrite mem_seq1 => /eqP -> /=.
    by move: Hy; rewrite /is_yam_of_shape => /andP [].
  move=> /flatten_mapP [[rshift shrshift]] /flatten_mapP [[rrow shrrow]] /= Hrow Hshift.
  move=> /mapP [] rec Hrec -> {res}; rewrite to_word_cons.
  have {Hrow} Hrow := yamtab_rowP Hy Hrow.
  have {Hshift Hrow} Hshift := yamtab_shiftP Hrow Hshift.
  rewrite -catA.
  exact (IHout _ _ _ _ _ Hshift _ Hrec).
Qed.

(* LRyamtab_list_rec returns words whose rowshape in included in outshape *)
Lemma one_letter_included innev mini maxi :
  included innev outev ->
  forall i, i \in choose_one_letter innev mini maxi ->
                  included (incr_nth innev i) outev.
Proof.
  move=> Hincl => i.
  rewrite /choose_one_letter mem_filter mem_iota => /andP [] /andP [] _ Hnth _.
  by apply included_incr_nth.
Qed.

Lemma yamtab_row_included innev row :
  included innev outev ->
  forall res shape, (res, shape) \in yamtab_row innev row ->
  included shape outev.
Proof.
  elim: row innev => [| r0 tlr IHrow] /= innev Hincl res shres.
    by rewrite mem_seq1 => /eqP [] _ ->.
  move/flatten_mapP => [[rec shrec]] /(IHrow innev Hincl) {IHrow} Hrec.
  move/mapP => [] i Hi [] _ ->.
  apply: (one_letter_included Hrec  Hi).
Qed.

Lemma yamtab_shift_included innev sh y :
  included innev outev ->
  forall res shape, (res, shape) \in yamtab_shift innev sh y ->
  included shape outev.
Proof.
  elim: sh innev y => [| sh IHsh] /= innev y Hincl res shres.
    by rewrite mem_seq1 => /eqP [] _ ->.
  move/flatten_mapP => [[rec shrec]] /(IHsh innev y Hincl) {IHsh} Hrec.
  move/mapP => [] i Hi [] _ ->.
  apply: (one_letter_included Hrec  Hi).
Qed.

Lemma LRyamtab_list_included innev inner outer sh0 row0 y :
  included innev outev ->
  is_yam_of_shape innev y ->
  forall res, res \in LRyamtab_list_rec innev inner outer sh0 row0 ->
  included (shape_rowseq (to_word res ++ y)) outev.
Proof.
  elim: outer innev inner sh0 row0 y => [//= | out0 out IHout] /=
              innev inner sh0 row0 y Hincl Hy res.
    rewrite mem_seq1 => /eqP -> /=.
    move: Hy; by rewrite /is_yam_of_shape => /andP [] Hyam /eqP ->.
  move=> /flatten_mapP [[rshift shrshift]] /flatten_mapP [[rrow shrrow]] /= Hrow Hshift.
  move=> /mapP [] rec Hrec -> {res}; rewrite to_word_cons -catA.
  have Hshrow := yamtab_rowP Hy Hrow.
  have {Hshrow} Hshshift := yamtab_shiftP Hshrow Hshift.
  have {Hrow} Hrow := yamtab_row_included Hincl Hrow.
  have {Hshift Hrow} Hshift := yamtab_shift_included Hrow Hshift.
  exact (IHout _ _ _ _ _ Hshift Hshshift _ Hrec).
Qed.

(* LRyamtab_list_rec returns fillings of skew shape outer/inner *)
Lemma yamtab_row_size innev row :
  forall res shape, (res, shape) \in yamtab_row innev row ->
  size res = size row.
Proof.
  elim: row innev => [| r0 tlr IHrow] /= innev res shape.
    by rewrite mem_seq1 => /eqP [] ->.
  move/flatten_mapP => [[rec shrec]] /(IHrow innev) {IHrow} <-.
  by move/mapP => [] i Hi [] -> _.
Qed.

Lemma yamtab_shift_size innev sh y :
  forall res shape, (res, shape) \in yamtab_shift innev sh y ->
  size res = sh + size y.
Proof.
  elim: sh innev y => [| sh IHsh] /= innev y res shres.
    rewrite mem_seq1 => /eqP [] ->; by rewrite add0n.
  move/flatten_mapP => [[rec shrec]] /(IHsh innev y) {IHsh} Hrec.
  move/mapP => [] i Hi [] -> _.
  by rewrite /= Hrec addSn.
Qed.

Lemma LRyamtab_list_pad0 innev inner outer sh0 row0 :
      LRyamtab_list_rec innev inner outer sh0 row0 =
      LRyamtab_list_rec innev (pad 0 (size outer) inner) outer sh0 row0.
Proof.
  elim: outer innev inner sh0 row0 => [//= | out0 out IHout] /=
              innev inner sh0 row0.
  congr flatten.
  have -> : head 0 (inner ++ nseq _ 0) = head 0 inner.
    move=> n; case inner => //=; by case n.
  apply eq_map => i; congr map.
  rewrite IHout /=; congr LRyamtab_list_rec.
  case: inner => //=; by rewrite subn0.
Qed.

Lemma LRyamtab_list_size innev inner outer sh0 row0 :
  forall res, res \in LRyamtab_list_rec innev inner outer sh0 row0 ->
  size res = size outer.
Proof.
  elim: outer innev inner sh0 row0 => [//= | out0 out IHout] /=
              innev inner sh0 row0 res.
    by rewrite mem_seq1 => /eqP -> /=.
  move=> /flatten_mapP [[rshift shrshift]] /flatten_mapP [[rrow shrrow]] /= Hrow Hshift.
  move=> /mapP [] rec Hrec -> {res} /=.
  by rewrite (IHout _ _ _ _  _ Hrec).
Qed.

Lemma LRyamtab_list_shape innev inner outer sh0 row0 :
  is_part inner -> is_part outer -> included inner outer ->
  head 0 outer <= sh0 + size row0 ->
  sh0 >= head 0 inner ->
  forall res, res \in LRyamtab_list_rec innev inner outer sh0 row0 ->
  shape res = diff_shape inner outer.
Proof.
  (* Replace inner by its padded 0 version *)
  rewrite -(head_pad0 (size outer) _ inner) -diff_shape_pad0 LRyamtab_list_pad0.
  move=> /(is_part_pad0 (size outer)) Hinn Hout Hincl.
  have Hsize : size (pad 0 (size outer) inner) = size outer.
    rewrite size_cat size_nseq subnKC //=.
    by apply size_included.
  move: Hincl Hinn Hout Hsize; rewrite included_pad0.
  move: (pad 0 _ _) => {inner} inner.

  elim: outer innev inner sh0 row0 => [//= | out0 out IHout] /=
              innev inner sh0 row0 Hincl Hinn Hout Hsize Hsh0 Hhead res.
    by rewrite mem_seq1 => /eqP -> /=; move: Hsize => /eqP/nilP ->.
  case: inner Hinn Hincl Hsize Hhead => [//= | inn0 inn] Hinn /= /andP [] H0 Hincl.
  move/eqP; rewrite eqSS => /eqP Hsize Hinn0.
  move=> /flatten_mapP [[rshift shrshift]] /flatten_mapP [[rrow shrrow]] /= Hrow Hshift.
  move=> /mapP [] rec Hrec -> {res}.
  have {Hshift} Hshift := yamtab_shift_size Hshift.
  have H : minn sh0 out0 - inn0 + size rrow + inn0 = out0.
    have {Hrow} -> := yamtab_row_size Hrow.
    rewrite !size_take bad_if_leq; last by rewrite leq_subLR.
    rewrite /minn.
    case: ltnP; last rewrite /leq => /eqP ->.
    + move/ltnW => H1.
      by rewrite addnC addnA (subnKC Hinn0) (subnKC H1).
    + by rewrite addn0 subnK //=.
  rewrite /= Hshift (IHout _ _ _ _ _ _ _ _ _ _ _ Hrec) {IHout Hrec} //=.
  - have {Hrow} -> := yamtab_row_size Hrow.
    rewrite !size_take bad_if_leq; last by rewrite leq_subLR.
    rewrite /minn.
    case: ltnP; last by rewrite /leq => /eqP ->; rewrite addn0.
    by rewrite addnC (addnBA _ Hinn0) => /ltnW/subnK ->.
  - by apply (path_sorted Hinn).
  - by move: Hout => /andP [].
  - rewrite Hshift addnC H.
    apply (@leq_trans (head 1 out)); first by case out.
    by move: Hout => /andP [].
  - move: Hinn => /=; by case inn => [//= | inn1 inn'] /= /andP [].
Qed.


(* LRyamtab_list_rec returns skew_tableau for inner *)
Lemma yamtab_row_dominate innev row :
  forall res shape, (res, shape) \in yamtab_row innev row ->
  dominate res row.
Proof.
  elim: row innev => [| r0 tlr IHrow] /= innev res shape.
    by rewrite mem_seq1 => /eqP [] ->.
  move/flatten_mapP => [[rec shrec]] /(IHrow innev) {IHrow} /dominateP [] Hsize Hdom.
  move/mapP => [] i Hi [] -> _ /=.
  apply/dominateP; split; first by rewrite ltnS.
  case=> [_ /=| j]; last by rewrite /= ltnS; apply Hdom.
  move: Hi; rewrite /choose_one_letter mem_filter mem_iota /= => /and3P [] _.
  by rewrite ltnXnatE.
Qed.

Lemma yamtab_shift_dominate innev sh row y :
  dominate y row ->
  forall res shape, (res, shape) \in yamtab_shift innev sh y ->
  skew_dominate sh res row.
Proof.
  rewrite -skew_dominate0; elim: sh innev y => [//= | sh IHsh] /= innev y Hdom res shape.
    by rewrite mem_seq1 => /eqP [] ->.
  move/flatten_mapP => [[rec shrec]] /(IHsh _ _ Hdom){IHsh Hdom}Hrec.
  move/mapP => [] i _ [] -> _.
  move: Hrec => /skew_dominateP [] Hsize Hdom.
  apply/skew_dominateP; split; first by rewrite /= addnS ltnS.
  case => [//= | i0] /=.
  rewrite !ltnS subSS.
  exact (Hdom i0).
Qed.

Lemma yamtab_row_is_row innev row :
  forall res shape, (res, shape) \in yamtab_row innev row ->
  is_row res.
Proof.
  elim: row innev => [| r0 tlr IHrow] /= innev res shape.
    by rewrite mem_seq1 => /eqP [] ->.
  move/flatten_mapP => [[rec shrec]] /(IHrow innev) {IHrow} Hrow.
  move/mapP => [] i Hi [] -> _ /=.
  move: Hi; rewrite /choose_one_letter mem_filter mem_iota /=.
  move => /and3P [] /andP [] _ Hnth Hr0.
  rewrite subSS addSn ltnS.
  case: (ltnP (minn (size shrec) (head (size outev) rec)) r0) => H.
  - have := ltnW H; rewrite {1}/leq => /eqP ->.
    rewrite addn0 => /(leq_trans Hr0).
    by rewrite ltnn.
  - rewrite (subnKC H) leq_min => /andP [] _.
    case: rec Hrow {H} => [//= | rec0 rec /= ->].
    by rewrite leqXnatE => ->.
Qed.

Lemma yamtab_shift_is_row innev sh y :
  is_row y ->
  forall res shape, (res, shape) \in yamtab_shift innev sh y ->
  is_row res.
Proof.
  elim: sh innev y => [//= | sh IHsh] /= innev y Hdom res shape.
    by rewrite mem_seq1 => /eqP [] ->.
  move/flatten_mapP => [[rec shrec]] /(IHsh _ _ Hdom){IHsh Hdom}Hrec.
  move/mapP => [] i Hi [] -> _.
  move: Hi; rewrite /choose_one_letter mem_filter mem_iota /= add0n subn0 ltnS.
  move=> /andP [] _; rewrite  leq_min => /andP [] _.
  case: rec Hrec => [//= | rec0 rec /= ->].
  by rewrite leqXnatE => ->.
Qed.

Lemma skew_dominate_take (T : ordType) n sh (u v : seq T) :
  skew_dominate sh u (take n v) -> skew_dominate sh u v.
Proof.
  move/skew_dominateP => [] Hsize Hdom.
  apply/skew_dominateP; split.
  - apply (leq_trans Hsize); rewrite leq_add2r size_take.
    rewrite -/(minn n _); by apply geq_minr.
  - move=> i Hi; have := Hdom i Hi.
    rewrite nth_take; first by [].
    move: Hi => /andP [] Hsh Hi.
    rewrite -(leq_add2r sh) addSn (subnK Hsh).
    apply (leq_trans Hi); apply (leq_trans Hsize).
    rewrite leq_add2r size_take.
    rewrite -/(minn n _); by apply geq_minl.
Qed.

Lemma skew_dominate_no_overlap (T : ordType) sh (u v : seq T) :
  size u <= sh -> skew_dominate sh u v.
Proof.
  move => Hsize.
  apply/skew_dominateP; split.
  - apply (leq_trans Hsize); by apply leq_addl.
  - move=> i /andP [] H1 H2; exfalso.
    have := leq_trans H2 (leq_trans Hsize H1).
    by rewrite ltnn.
Qed.

Lemma LRyamtab_list_skew_tableau innev inner outer sh0 row0 :
  is_part inner -> is_part outer -> included inner outer ->
  head 0 outer <= sh0 + size row0 ->
  sh0 >= head 0 inner ->
  forall res, res \in LRyamtab_list_rec innev inner outer sh0 row0 ->
  is_skew_tableau inner res.
Proof.
  (* Replace inner by its padded 0 version *)
  move=>  Hinn Hout Hincl Hhout Hhinn res Hres.
  have Hshape := LRyamtab_list_shape Hinn Hout Hincl Hhout Hhinn Hres.
  move: Hres; rewrite LRyamtab_list_pad0 => Hres.
  move: Hinn => /(is_part_pad0 (size outer)) Hinn.
  rewrite is_skew_tableau_pad0 (LRyamtab_list_size Hres).
  have Hsize : size (pad 0 (size outer) inner) = size outer.
    rewrite size_cat size_nseq subnKC //=.
    by apply size_included.
  suff : skew_dominate ((minn sh0 (head 0 outer)) - head 0 inner) (head [::] res)
                 (take ((head 0 outer) - sh0) row0)
         /\
         is_skew_tableau ((pad 0 (size outer)) inner) res by move => [].
  move: Hout Hinn Hincl Hhout Hhinn Hsize res Hshape Hres.
  rewrite -(head_pad0 (size outer) _ inner) included_pad0 -diff_shape_pad0.
  move: (pad 0 _ _) => {inner} inner.

  elim: outer innev inner sh0 row0 => [//= | out0 out IHout] /=
              innev inner sh0 row0 Hout Hinn Hincl Hhout Hhinn Hsize res Hshape.
    by rewrite mem_seq1 => /eqP -> /=; move: Hsize => /eqP/nilP ->.
  move: Hout => /andP [] Hheadout Hpartout.
  have {IHout} IHout := IHout _ _ _ _ Hpartout.
  case: inner Hinn Hincl Hsize Hhinn Hshape => [//= | inn0 inn] Hinn /= /andP [] H0 Hincl.
  move/eqP; rewrite eqSS => /eqP Hsize Hinn0 Hshape.
  move=> /flatten_mapP [[rshift shrshift]] /flatten_mapP [[rrow shrrow]] /= Hrow Hshift.
  move=> /mapP [] rec Hrec Hres; subst res.
  have Hrshiftrow := yamtab_shift_is_row (yamtab_row_is_row Hrow) Hshift.
  have Hrshiftdom := yamtab_shift_dominate (yamtab_row_dominate Hrow) Hshift.
  move: Hshape {Hshift Hrow rrow shrrow}=> /= [] Hshift Hshape.
  rewrite /= Hshift (subnK H0); split; first exact Hrshiftdom.
  have {IHout Hrec Hrshiftdom} //= Hrec :=
    (IHout _ _ _ _ (path_sorted Hinn) Hincl _ _ Hsize _ _ Hrec).
  apply/and3P; split => //=.
  - move: Hpartout; apply contraL => /eqP Hout0.
    move: Hheadout; by rewrite Hout0 leqn0 => /part_head0F ->.
  - have H1 : head 0 out <= inn0 + size rshift.
      rewrite Hshift (subnKC H0).
      by apply (@leq_trans (head 1 out)); first by case out.
    have H2 : head 0 inn <= inn0.
      move: Hinn => /=; by case inn => [//= | inn1 inn'] /= /andP [].
    have {Hrec H1 H2} := Hrec H1 H2 Hshape => [] [] /skew_dominate_take Hdom ->.
    rewrite andbT.
    case: (leqP inn0 (head 0 out)) Hdom => [/minn_idPl -> //= |] /ltnW Hover _.
    apply skew_dominate_no_overlap.
    case: out Hincl Hsize Hshape Hover {Hheadout Hpartout} => [| out1 out] /=.
      move=> _ /eqP/nilP -> /=.
      rewrite /shape; by case rec.
    case: inn Hinn => [//= | inn1 inn] /= H1 H2 H3.
    rewrite /shape; case: rec => [//= | rec0 rec] /= [] -> _.
    apply leq_sub2r.
Qed.

End OutEval.

Definition LRyamtab_list inner eval outer :=
  LRyamtab_list_rec eval [::] inner outer (head 0 outer) [::].
Definition LRcoeff inner eval outer :=
  LRyamtab_count_rec eval [::] inner outer (head 0 outer) [::].

Lemma LRcoeffE inner eval outer :
  size (LRyamtab_list inner eval outer) = LRcoeff inner eval outer.
Proof. by rewrite LRyam_tab_countE. Qed.

Lemma LRyamtab_yam inner eval outer tab:
  tab \in (LRyamtab_list inner eval outer) -> is_yam (to_word tab).
Proof.
  rewrite /LRyamtab_list -(cats0 (to_word tab)).
  by apply LRyamtab_list_recP.
Qed.

Lemma LRyamtab_included inner eval outer tab:
  tab \in (LRyamtab_list inner eval outer) -> included (shape_rowseq (to_word tab)) eval.
Proof.
  rewrite /LRyamtab_list -(cats0 (to_word tab)).
  by apply LRyamtab_list_included.
Qed.

Lemma LRyamtab_shape inner eval outer tab :
  is_part inner -> is_part outer -> included inner outer ->
  tab \in (LRyamtab_list inner eval outer) -> shape tab = diff_shape inner outer.
Proof.
  move=> Hinn Hout Hincl.
  rewrite /LRyamtab_list => /LRyamtab_list_shape; apply => //=.
  - by rewrite addn0.
  - case: inner Hincl {Hinn Hout} => [//= | inn0 inn].
    by case outer => [//= | out0 out] /= /andP [].
Qed.

Lemma LRyamtab_skew_tableau inner eval outer tab :
  is_part inner -> is_part outer -> included inner outer ->
  tab \in (LRyamtab_list inner eval outer) -> is_skew_tableau inner tab.
Proof.
  move=> Hinn Hout Hincl.
  rewrite /LRyamtab_list => /LRyamtab_list_skew_tableau; apply => //=.
  - by rewrite addn0.
  - case: inner Hincl {Hinn Hout} => [//= | inn0 inn].
    by case outer => [//= | out0 out] /= /andP [].
Qed.

Lemma LRyamtab_eval inner eval outer tab:
  is_part inner -> is_part outer -> included inner outer ->
  is_part eval -> sumn eval = sumn (diff_shape inner outer) ->
  tab \in (LRyamtab_list inner eval outer) -> shape_rowseq (to_word tab) = eval.
Proof.
  move=> Hinn Hout Hincl Hev Hsumn Htab.
  apply (included_sumnE Hev (LRyamtab_included Htab)).
  rewrite Hsumn shape_rowseq_eq_size -size_to_word /size_tab.
  by rewrite (LRyamtab_shape Hinn Hout Hincl Htab).
Qed.

Lemma count_mem_LRyamtab_list inner eval outer yamtab :
  is_part inner -> is_part outer -> included inner outer ->
  is_skew_tableau inner yamtab -> shape yamtab = diff_shape inner outer ->
  is_yam_of_shape eval (to_word yamtab) ->
  count_mem yamtab (LRyamtab_list inner eval outer) = 1.
Proof.
  rewrite /LRyamtab_list.
  admit.
Qed.

Section Spec.

Variables d1 d2 : nat.
Variables (P1 : intpartn d1) (P2 : intpartn d2).
Variable P : intpartn (d1 + d2).
Hypothesis Hincl : included P1 P.

Lemma LRyamtabP tab :
  tab \in (LRyamtab_list P1 P2 P) -> is_yam_of_shape P2 (to_word tab).
Proof.
  rewrite /is_yam_of_shape => Htab; apply /andP; split.
  - by apply (LRyamtab_yam Htab).
  - rewrite (LRyamtab_eval (intpartnP P1) (intpartnP P) Hincl (intpartnP P2) _ Htab) //=.
    by rewrite (sumn_diff_shape Hincl) !intpartn_sumn addKn.
Qed.

Lemma LRyamtab_spec tab (Htab : tab \in (LRyamtab_list P1 P2 P)) :
  YamSh (LRyamtabP Htab) \in LRyam_set P1 P2 P.
Proof.
  rewrite inE /= -(diff_shapeK Hincl).
  have Hshape := (LRyamtab_shape (intpartnP P1) (intpartnP P) Hincl Htab).
  rewrite -Hshape skew_reshapeK.
  - by apply (LRyamtab_skew_tableau (intpartnP P1) (intpartnP P) Hincl Htab).
  - have -> : size tab = size (shape tab) by rewrite size_map.
    rewrite Hshape size_diff_shape.
    by apply size_included.
Qed.


Lemma LRyamtab_spec_recip yam :
  yam \in LRyam_set P1 P2 P ->
  count_mem (val yam) (map (@to_word _) (LRyamtab_list P1 P2 P)) = 1.
Proof.
  rewrite inE => Hyam.
  have Hszyam : size yam = sumn (diff_shape P1 P).
    by rewrite -shape_rowseq_eq_size shape_yamsh (sumn_diffE P2).
  rewrite -[val yam](to_word_skew_reshape Hincl Hszyam).
  rewrite count_map.
  rewrite (eq_in_count (a2 := pred1 (skew_reshape P1 P (val yam)))); first last.
    move=> tab /= Htab; apply/(sameP idP); apply(iffP idP) => [/eqP -> //= | /eqP].
    rewrite (to_word_skew_reshape Hincl Hszyam).
    move <-.
    have Hshape := (LRyamtab_shape (intpartnP P1) (intpartnP P) Hincl Htab).
    have <- : (outer_shape P1 (shape tab)) = P.
      by rewrite Hshape diff_shapeK.
    rewrite skew_reshapeK //= -(size_map size tab) -/(shape tab) Hshape size_diff_shape.
    by apply size_included.
  apply (count_mem_LRyamtab_list (intpartnP P1) (intpartnP P) Hincl Hyam).
  - by rewrite (shape_skew_reshape Hincl Hszyam).
  - rewrite /is_yam_of_shape; rewrite (to_word_skew_reshape Hincl Hszyam).
    by rewrite yamshP shape_yamsh eq_refl.
Qed.

Eval compute in LRyamtab_list [:: 2] [:: 1; 1] [:: 3; 1].

Eval compute in LRyamtab_list [:: 2] [:: 1] [:: 3].

Eval compute in LRyamtab_list [:: 2; 1] [:: 2; 1] [:: 3; 2; 1].

Eval compute in LRyamtab_list [:: 3; 3; 1] [:: 3; 2; 1; 1] [:: 5; 4; 3; 2].

Eval compute in
    map (@to_word _) (LRyamtab_list [:: 3; 3; 1] [:: 3; 2; 1; 1] [:: 5; 4; 3; 2]).
(*
Eval compute in LRyam_list [:: 3; 3; 1] [:: 3; 2; 1; 1] [:: 5; 4; 3; 2].
     = [:: [:: 0; 3; 1; 2; 1; 0; 0]; [:: 1; 3; 0; 2; 1; 0; 0]]
...00 ...00
...1  ...1
.02   .12
13    03
*)

Eval compute in
    map (@to_word _) (LRyamtab_list [:: 3; 3; 1] [:: 4; 2; 1] [:: 5; 4; 3; 2]).
(*
Eval compute in LRyam_list [:: 3; 3; 1] [:: 4; 2; 1] [:: 5; 4; 3; 2].
     = [:: [:: 0; 1; 0; 2; 1; 0; 0]; [:: 0; 2; 0; 1; 1; 0; 0];
           [:: 1; 2; 0; 0; 1; 0; 0]]
...11 ...11 ...11
...2  ...2  ...2
.11   .12   .13
23    13    12
*)

(* According LRcalc = 18 *)
Eval compute in size (LRyamtab_list
  [:: 4; 3; 2; 1] [:: 4; 3; 2; 1] [:: 6; 5; 4; 3; 1; 1]).
(* According LRcalc = 9 *)
Eval compute in size (LRyamtab_list
  [:: 4; 3; 2; 1] [:: 4; 3; 2; 1] [:: 5; 5; 3; 3; 2; 1; 1]).
(* According to LRcalc and Wikipedia = 176 *)
Eval compute in size (LRyamtab_list
  [:: 5; 4; 3; 2; 1] [:: 5; 4; 3; 2; 1] [:: 8; 6; 5; 4; 3; 2; 1; 1]).
Eval compute in LRcoeff
  [:: 5; 4; 3; 2; 1] [:: 5; 4; 3; 2; 1] [:: 8; 6; 5; 4; 3; 2; 1; 1].
(* According to LRcalc and Wikipedia = 2064 *)
Eval compute in size (LRyamtab_list
  [:: 6; 5; 4; 3; 2; 1] [:: 6; 5; 4; 3; 2; 1] [:: 9; 8; 7; 5; 4; 3; 3; 2; 1]).
Eval compute in LRcoeff
  [:: 6; 5; 4; 3; 2; 1] [:: 6; 5; 4; 3; 2; 1] [:: 9; 8; 7; 5; 4; 3; 3; 2; 1].
