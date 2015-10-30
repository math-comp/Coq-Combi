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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import tuple finfun finset bigop path.
Require Import mpoly.

Require Import tools combclass partition Yamanouchi ordtype tableau.
Require Import skewtab sympoly freeSchur therule.

(******************************************************************************)
(** This file contains a Coq implementation of the Littlewood-Richardson rule *)
(**                                                                           *)
(** [LRcoeff]       : [seq nat -> seq nat -> seq nat -> nat]                  *)
(**                   returns the LR coefficient                              *)
(** [LRyamtab_list] : seq nat -> seq nat -> seq nat -> seq (seq (seq nat))    *)
(**                   returns the list of LR tableaux                         *)
(**                                                                           *)
(** The following lemma assert that LRcoeff agrees with LRyamtab_list         *)
(**                                                                           *)
(**  [Lemma LRcoeffP inner eval outer :                                       *)
(**     size (LRyamtab_list inner eval outer) = LRcoeff inner eval outer.]    *)
(**                                                                           *)
(******************************************************************************)



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N.

Lemma sorted_is_part p :
  is_part p -> sorted geq p.
Proof.
  case: p => [//= | p0 p] /= /andP [].
  elim: p p0 => [//= | p1 p IHp] /= p0 -> /andP [] /=.
  exact: IHp.
Qed.

Lemma is_part_pad0 n p :
  is_part p -> sorted geq (pad 0 n p).
Proof.
  have Hpath x i : path geq x (nseq i 0).
    case: i => [//= | i] /=; by elim: i.
  case: p => [_ | p0 p]; case: n => [| n /=] //=.
    rewrite cats0 -/(sorted geq (p0 :: p)) -/(is_part (p0 :: p)).
    exact: sorted_is_part.
  rewrite subSS.
  elim: p p0 n => [| p1 p IHp] /= p0 n.
    move=> _; exact: Hpath.
  move=> /andP [] -> /IHp{IHp} Hrec /=.
  case: n => [| n /=].
    move/(_ 0): Hrec; by rewrite !sub0n.
  rewrite subSS; exact: Hrec.
Qed.

Lemma head_row_skew_yam innev shape l r :
  is_part innev -> sorted leqX_op (l :: r) ->
  is_skew_yam innev shape (l :: r) ->
  l <= head (size innev) r.
Proof.
  case: r => [| l1 r /=] Hinn Hrow Hskew.
    apply (is_part_incr_nth_size Hinn).
    move/(_ _ (hyper_yam_of_eval Hinn)): Hskew.
    rewrite /= /is_yam_of_eval /=.
    by rewrite (evalseq_hyper_yam Hinn) => /andP [] /andP [].
  move: Hrow => /andP [].
  by rewrite leqXnatE.
Qed.


(* COQ implementation of the LR rule *)
Section OutEval.

(* For some reason, using ssrnat's add prevents OCaml extraction *)
Fixpoint add m n := if m is m'.+1 then add m' n.+1 else n.
Lemma addE : add =2 addn.
Proof. by elim=> //= n IHn m; rewrite IHn addSnnS. Qed.

Let tsumn := foldl add 0.
Lemma tsumnE : tsumn =1 sumn.
Proof.
  rewrite /tsumn => s; rewrite -(add0n (sumn s)); move: 0 => i.
  elim: s i => [//= | s0 s IHs] i /=.
  by rewrite IHs addE addnA.
Qed.

Variable outev : seq nat.

Definition choose_one_letter innev mini maxi :=
  filter
    (fun i => is_add_corner innev i && (nth 0 innev i < nth 0 outev i))
    (iota mini ((minn (size innev) maxi).+1 - mini) ).

Fixpoint yamtab_row innev row :=
  if row is r0 :: tlr then
    flatten [seq
               [seq (i :: res.1, incr_nth res.2 i) |
                i <- choose_one_letter res.2 r0.+1 (head (size innev) res.1)
               ] |
             res <- yamtab_row innev tlr ]
  else [:: ([::], innev) ].

Fixpoint yamtab_shift innev maxi sh sol :=
  if sh is s.+1 then
    flatten [seq
               [seq (i :: res.1, incr_nth res.2 i) |
                i <- choose_one_letter res.2 0 (head maxi res.1)
               ] |
             res <- yamtab_shift innev maxi s sol ]
  else [:: (sol, innev) ].

Fixpoint LRyamtab_list_rec innev inner outer sh0 row0 :=
  if outer is out0 :: out then
    let inn0 := head 0 inner in let inn := behead inner in
    let rowres := yamtab_row innev (take (out0 - sh0) row0) in
    let rows :=
        flatten [seq yamtab_shift res.2 (head (size innev) res.1)
                     ((minn sh0 out0) - inn0) res.1
                | res <- rowres ] in
    flatten [seq [seq row.1 :: tab |
                  tab <- LRyamtab_list_rec row.2 inn out inn0 row.1] |
             row <- rows]
  else [:: [::]].

Fixpoint LRyamtab_count_rec innev inner outer sh0 row0 :=
  if outer is out0 :: out then
    let inn0 := head 0 inner in let inn := behead inner in
    let rowres := yamtab_row innev (take (out0 - sh0) row0) in
    tsumn [seq tsumn [seq LRyamtab_count_rec row.2 inn out inn0 row.1 |
                    row <- yamtab_shift res.2 (head (size innev) res.1)
                        ((minn sh0 out0) - inn0) res.1 ]
         | res <- rowres ]
  else 1.


Lemma size_LRyamtab_listE innev inner outer sh0 row0 :
  size (LRyamtab_list_rec innev inner outer sh0 row0) =
  LRyamtab_count_rec innev inner outer sh0 row0.
Proof.
  elim: outer innev inner sh0 row0 => [//= | out0 out IHout] /= innev inner sh0 row0.
  rewrite size_flatten /shape !map_flatten sumn_flatten -map_comp.
  rewrite tsumnE; congr (sumn _).
  rewrite (eq_map (f2 := map (fun row =>
                     LRyamtab_count_rec row.2 (behead inner) out (head 0 inner) row.1))).
  - rewrite [RHS]map_comp (eq_map tsumnE) -!map_comp; exact: eq_map.
  - move=> s /=; rewrite -map_comp; apply eq_map => {s} [] [row sh] /=.
    by rewrite size_map IHout.
Qed.


(* Basic lemma *)
Lemma yamtab_shift_drop innev maxi sh y :
  forall res shape, (res, shape) \in yamtab_shift innev maxi sh y ->
  drop sh res = y.
Proof.
  elim: sh => [//= | sh IHsh] /= res shape.
    rewrite mem_seq1 => /eqP [] -> _; by rewrite drop0.
  by move=> /flatten_mapP [[rec shrec]] /IHsh Hdrop /mapP [] i _ [] -> _ /=.
Qed.


(* LRyamtab_list_rec returns Yamanouchi words *)
Lemma choose_one_letterP innev mini maxi :
  forall i, i \in choose_one_letter innev mini maxi ->
  is_skew_yam innev (incr_nth innev i) [:: i].
Proof.
  rewrite /is_skew_yam /is_yam_of_eval => i.
  rewrite mem_filter mem_iota => /andP [] /andP [] Hcorn _ _.
  move => y /andP [] Hyam /eqP Hinnev; subst innev.
  apply/andP; split => //=.
  rewrite Hyam andbT.
  apply is_part_incr_nth; last exact Hcorn.
  exact: is_part_eval_yam.
Qed.

Lemma yamtab_rowP innev row :
  forall res shape, (res, shape) \in yamtab_row innev row ->
  is_skew_yam innev shape res.
Proof.
  elim: row innev => [| r0 tlr IHrow] /= innev res shres.
    rewrite mem_seq1 => /eqP [] -> ->; exact: skew_yam_nil.
  move/flatten_mapP => [[rec shrec]] /(IHrow innev) {IHrow} Hrec.
  move/mapP => [i] /choose_one_letterP /= Hi [] -> -> {res shres}.
  rewrite -cat1s; exact: skew_yam_cat Hrec Hi.
Qed.

Lemma yamtab_shiftP innev maxi sh row shrow :
  is_skew_yam innev shrow row ->
  forall res shape, (res, shape) \in yamtab_shift shrow maxi sh row ->
  is_skew_yam innev shape res.
Proof.
  elim: sh row innev => [| sh IHsh] /= row innev Hrow res shres.
    by rewrite mem_seq1 => /eqP [] -> ->.
  move/flatten_mapP => [[rec shrec]] /(IHsh row innev Hrow) {IHsh} Hrec.
  move/mapP => [i] /choose_one_letterP /= Hi [] -> -> {res shres}.
  rewrite -cat1s; exact (skew_yam_cat Hrec Hi).
Qed.

Lemma LRyamtab_list_recP innev inner outer sh0 row0 y :
  is_yam_of_eval innev y ->
  forall res, res \in LRyamtab_list_rec innev inner outer sh0 row0 ->
  is_yam (to_word res ++ y).
Proof.
  elim: outer innev inner sh0 row0 y => [//= | out0 out IHout] /=
              innev inner sh0 row0 y Hy res.
    rewrite mem_seq1 => /eqP -> /=.
    by move: Hy; rewrite /is_yam_of_eval => /andP [].
  move=> /flatten_mapP [[rshift shrshift]] /flatten_mapP [[rrow shrrow]] /= Hrow Hshift.
  move=> /mapP [] rec Hrec -> {res}; rewrite to_word_cons.
  move: Hrow => /yamtab_rowP/yamtab_shiftP/(_ _ _ Hshift _ Hy) => {Hshift}Hshift.
  rewrite -catA; exact: (IHout _ _ _ _ _ Hshift _ Hrec).
Qed.


(* LRyamtab_list_rec returns words whose rowshape in included in outshape *)
Lemma one_letter_included innev mini maxi :
  included innev outev ->
  forall i, i \in choose_one_letter innev mini maxi ->
                  included (incr_nth innev i) outev.
Proof.
  move=> Hincl => i.
  rewrite /choose_one_letter mem_filter mem_iota => /andP [] /andP [] _ Hnth _.
  exact: included_incr_nth_inner.
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

Lemma yamtab_shift_included innev maxi sh y :
  included innev outev ->
  forall res shape, (res, shape) \in yamtab_shift innev maxi sh y ->
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
  is_yam_of_eval innev y ->
  forall res, res \in LRyamtab_list_rec innev inner outer sh0 row0 ->
  included (evalseq (to_word res ++ y)) outev.
Proof.
  elim: outer innev inner sh0 row0 y => [//= | out0 out IHout] /=
              innev inner sh0 row0 y Hincl Hy res.
    rewrite mem_seq1 => /eqP -> /=.
    move: Hy; by rewrite /is_yam_of_eval => /andP [] Hyam /eqP ->.
  move=> /flatten_mapP [[rshift shrshift]] /flatten_mapP [[rrow shrrow]] /= Hrow Hshift.
  move=> /mapP [] rec Hrec -> {res}; rewrite to_word_cons -catA.
  have Hshshift := yamtab_shiftP (yamtab_rowP Hrow) Hshift Hy.
  move: Hrow => /(yamtab_row_included Hincl)/yamtab_shift_included/(_ _ _ Hshift).
  move/IHout; by apply; last exact: Hrec.
Qed.


(* LRyamtab_list_rec returns fillings of skew shape (inner, outer) *)
Lemma yamtab_row_size innev row :
  forall res shape, (res, shape) \in yamtab_row innev row ->
  size res = size row.
Proof.
  elim: row innev => [| r0 tlr IHrow] /= innev res shape.
    by rewrite mem_seq1 => /eqP [] ->.
  move/flatten_mapP => [[rec shrec]] /(IHrow innev) {IHrow} <-.
  by move/mapP => [] i Hi [] -> _.
Qed.

Lemma yamtab_shift_size innev maxi sh y :
  forall res shape, (res, shape) \in yamtab_shift maxi innev sh y ->
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
  rewrite (_ : head 0 (inner ++ nseq _ 0) = head 0 inner); last by case inner.
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

(* inner is padded with 0 *)
Lemma LRyamtab_list_shape0 innev inner outer sh0 row0 :
  sorted geq (sh0 :: inner) -> is_part (sh0 + size row0 :: outer) ->
  included inner outer -> size inner = size outer ->
  forall res, res \in LRyamtab_list_rec innev inner outer sh0 row0 ->
  shape res = diff_shape inner outer.
Proof.
  elim: outer innev inner sh0 row0 => [//= | out0 out IHout]
              innev inner sh0 row0 Hinn Hout /= Hincl Hsize res.
    by rewrite mem_seq1 => /eqP -> /=; move: Hsize => /eqP/nilP ->.
  case: inner Hinn Hincl Hsize => [//= | inn0 inn] Hinn /= /andP [] H0 Hincl.
  move/eqP; rewrite eqSS => /eqP Hsize.
  move=> /flatten_mapP [[rshift shrshift]] /flatten_mapP [[rrow shrrow]] /= Hrow Hshift.
  move=> /mapP [] rec Hrec -> /= {res}.
  have {Hshift} Hshift : size rshift = out0 - inn0.
    rewrite (yamtab_shift_size Hshift) {Hshift}.
    move: Hout => /= /andP [] Hout0 _.
    move: Hinn => /= /andP [] Hinn0 _.
    move: Hrow => /yamtab_row_size ->.
    rewrite !size_take bad_if_leq; last by rewrite leq_subLR.
    rewrite /minn; case: ltnP; last rewrite /leq => /eqP ->.
    + move/ltnW => H1.
      by rewrite addnC (addnBA _ Hinn0) (subnK H1).
    + by rewrite addn0.
  rewrite Hshift; congr (_ :: _).
  rewrite (IHout _ _ _ _ (path_sorted Hinn) _ _ _ _ Hrec) {IHout Hrec} //=.
  rewrite Hshift (subnKC H0) -/(is_part (out0 :: out)).
  exact (is_part_consK Hout).
Qed.


(* LRyamtab_list_rec returns skew_tableau with inner shape inner *)
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

Lemma yamtab_shift_dominate innev maxi sh row y :
  dominate y row ->
  forall res shape, (res, shape) \in yamtab_shift innev maxi sh y ->
  skew_dominate sh res row.
Proof.
  rewrite -skew_dominate0; elim: sh innev y => [//= | sh IHsh] /= innev y Hdom res shape.
    by rewrite mem_seq1 => /eqP [] ->.
  move/flatten_mapP => [[rec shrec]] /(IHsh _ _ Hdom){IHsh Hdom}Hrec.
  move/mapP => [] i _ [] -> _.
  exact: skew_dominate_consl.
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
  case: (ltnP (minn (size shrec) (head (size innev) rec)) r0) => H.
  - move/ltnW: H; rewrite {1}/leq => /eqP ->.
    rewrite addn0 => /(leq_trans Hr0).
    by rewrite ltnn.
  - rewrite (subnKC H) leq_min => /andP [] _.
    case: rec Hrow {H} => [//= | rec0 rec /= ->].
    by rewrite leqXnatE => ->.
Qed.

Lemma yamtab_shift_is_row innev maxi sh y :
  is_row y ->
  forall res shape, (res, shape) \in yamtab_shift innev maxi sh y ->
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

(* inner is padded with 0 *)
Lemma LRyamtab_list_skew_tableau0 innev inner outer sh0 row0 :
  sorted geq (sh0 :: inner) -> is_part (sh0 + size row0 :: outer) ->
  included inner outer -> size inner = size outer ->
  is_row row0 ->
  forall res, res \in LRyamtab_list_rec innev inner outer sh0 row0 ->
  is_skew_tableau (sh0 :: inner) (row0 :: res).
Proof.
  move=> Hinn Hout Hincl Hsize Hrow0 res Hres.
  have:= LRyamtab_list_shape0 Hinn Hout Hincl Hsize Hres.
  move: Hinn Hout Hincl Hsize Hrow0 res Hres.
  elim: outer innev inner sh0 row0 => [//= | out0 out IHout]
              innev inner sh0 row0 Hinn Hout /= Hincl Hsize Hrow0 res.
    rewrite mem_seq1 => /eqP -> /=; move: Hsize => /eqP/nilP ->.
    move: Hout; by rewrite eq_refl Hrow0 !andbT addnC lt0n.
  case: inner Hinn Hincl Hsize => [//= | inn0 inn] Hinn /= /andP [] H0 Hincl.
  move/eqP; rewrite eqSS => /eqP Hsize.
  move=> /flatten_mapP [[rshift shrshift]] /flatten_mapP [[rrow shrrow]] /= Hrow Hshift.
  move=> /mapP [] rec Hrec Hres; subst res.
  have Hrshiftrow := yamtab_shift_is_row (yamtab_row_is_row Hrow) Hshift.
  have Hrshiftdom := yamtab_shift_dominate (yamtab_row_dominate Hrow) Hshift.
  move {Hshift Hrow rrow shrrow}=> /= [] Hshift Hshape.
  rewrite (part_head_non0 Hout) Hrow0 Hrshiftrow.
  rewrite Hshift (subnKC H0) (part_head_non0 (is_part_consK Hout)) /=.
  have Hpart0 : is_part (inn0 + size rshift :: out).
    have:= is_part_consK Hout => /=/andP [] Hhout ->.
    by rewrite andbT Hshift (subnKC H0).
  move/(_ _ _ _ _ (path_sorted Hinn) Hpart0 Hincl Hsize Hrshiftrow _ Hrec Hshape): IHout.
  move=> {Hrec Hpart0} /= /and3P [] _ _ ->; rewrite andbT.
  case: (leqP sh0 out0) Hrshiftdom => [/minn_idPl -> //= | /ltnW Hover _].
  - exact: skew_dominate_take.
  - apply skew_dominate_no_overlap.
    rewrite Hshift leq_subLR.
    move: Hinn => /= /andP [] Hsh0 _.
    by rewrite (subnKC Hsh0).
Qed.

(* Mutiplicities are all one *)
Lemma choose_one_countE shr innev shape mini maxi row l :
  is_part innev ->
  is_skew_yam innev shr row ->
  is_skew_yam innev shape (l :: row) ->
  included shape outev ->
  mini <= l <= maxi ->
  is_row (l :: row) ->
  (count_mem l) (choose_one_letter shr mini maxi) = 1.
Proof.
  rewrite /choose_one_letter count_filter
    => Hpart Hrow Hlrw Hincl /andP [] Hmin Hmax Hisrow.
  move/(_ _ (hyper_yam_of_eval Hpart)): Hrow => /= /andP [] Hyamrow /eqP Hshr.
  move/(_ _ (hyper_yam_of_eval Hpart)): Hlrw => /= /andP [] Hyamlrow /eqP Hshape.
  rewrite (eq_count (a2 := pred1 l)); first last.
    move=> i /=; case (altP (i =P l)) => [Hi | //=]; subst i.
    have -> /= : is_add_corner shr l by rewrite -Hshr; exact: is_add_corner_yam.
    move: Hincl => /includedP [] _ Hincl.
    apply: (leq_trans _ (Hincl l)).
    rewrite -Hshape /= Hshr.
    by rewrite nth_incr_nth eq_refl add1n ltnS.
  rewrite (count_uniq_mem _ (iota_uniq _ _)) mem_iota Hmin /=.
  set m := minn _ _.
  suff : l <= m.
    case (ltnP mini m.+1) => [/ltnW | ] H Hl.
    - by rewrite (subnKC H) ltnS Hl.
    - have:= H; rewrite {1}/leq => /eqP ->.
      by rewrite addn0 (leq_ltn_trans Hl H).
  rewrite {}/m leq_min Hmax andbT.
  apply is_part_incr_nth_size.
  - rewrite -Hshr; exact (is_part_eval_yam Hyamrow).
  - rewrite -Hshr; exact (is_part_eval_yam Hyamlrow).
Qed.

Lemma yamtab_row_countE innev shape row base :
  is_part innev ->
  size row = size base ->
  dominate row base ->
  is_row row ->
  is_skew_yam innev shape row ->
  included shape outev ->
  count (preim (fst (B:=seq nat)) (pred1 row))
        (yamtab_row innev base) = 1.
Proof.
  move=> Hinn.
  elim: row base shape => [| l0 row IHrow] [| b0 base] //= shape.
  move/eqP; rewrite eqSS => /eqP Hsize Hdom Hisrow Hskew Hincl.
  rewrite count_flatten -map_comp.
  set f1 := (X in map X); set rec := (X in map _ X).
  pose f2 := nat_of_bool \o (pred1 row) \o (@fst (seq nat) (seq nat)).
  have : {in rec, f1 =1 f2}.
    rewrite /rec /f1 /f2 {rec f1 f2} => [[r shr]] /= Hr.
    rewrite count_map.
    case: (altP (r =P row)) => [Hrow | /negbTE Hneq] /=.
    - subst r.
      rewrite (eq_count (a2 := pred1 l0)); first last.
        move=> i /=; by rewrite eqseq_cons eq_refl andbT.
      apply: (choose_one_countE Hinn (yamtab_rowP Hr) Hskew Hincl _ Hisrow).
      have /dominate_head/(_ Hdom) : l0 :: row != [::] by [].
      rewrite ltnXnatE => -> /=.
      exact: head_row_skew_yam Hinn Hisrow Hskew.
    - rewrite (eq_count (a2 := pred0)); first by rewrite count_pred0.
      move=> y /=; by rewrite eqseq_cons Hneq andbF.
  rewrite eq_in_map /rec /f2 => -> {f1 f2 rec}.
  rewrite sumn_count /=.
  apply: (IHrow _ _ Hsize (dominate_tl Hdom) (is_row_consK Hisrow)
                 (skew_yam_consK Hinn Hskew)).
  apply: (included_trans _ Hincl).
  exact: included_decr_nth.
Qed.

Lemma yamtab_shift_countE inn0 innev shape sh row sol :
  is_part inn0 ->
  is_row (row ++ sol) ->
  size row = sh ->
  is_skew_yam inn0 innev sol ->
  is_skew_yam innev shape row ->
  included shape outev ->
  count (preim (fst (B:=seq nat)) (pred1 (row ++ sol)))
        (yamtab_shift innev (head (size inn0) sol) sh sol) = 1.
Proof.
  move=> Hinn0.
  elim : sh row sol shape => [| sh IHsh ] row sol shape /= Hisrow.
    move=> /eqP/nilP -> _ /=; by rewrite eq_refl.
  case: row Hisrow => [//= |r0 row] Hisrow /=.
  move/eqP; rewrite eqSS => /eqP Hsize Hskew0 Hskew Hincl.
  have Hinn := is_part_skew_yam Hinn0 Hskew0.
  rewrite count_flatten -map_comp.
  set f1 := (X in map X); set rec := (X in map _ X).
  pose f2 := nat_of_bool \o (pred1 (row ++ sol)) \o (@fst (seq nat) (seq nat)).
  have : {in rec, f1 =1 f2}.
    rewrite /rec /f1 /f2 {rec f1 f2} => [[r shr]] /= Hr.
    rewrite count_map.
    case: (altP (r =P (row ++ sol))) => [Heq | /negbTE Hneq] /=.
    - subst r.
      rewrite (eq_count (a2 := pred1 r0)); first last.
        move=> i /=; by rewrite eqseq_cons eq_refl andbT.
      rewrite (_ : head _ _ = head (size inn0) (row ++ sol)); first last.
        by case row => //=; case sol.
      apply: (choose_one_countE Hinn0 (yamtab_shiftP Hskew0 Hr)
                 (skew_yam_cat Hskew0 Hskew) Hincl _ Hisrow).
      rewrite /=.
      exact: head_row_skew_yam Hinn0 Hisrow (skew_yam_cat Hskew0 Hskew).
    - rewrite (eq_count (a2 := pred0)); first by rewrite count_pred0.
      move=> y /=; by rewrite eqseq_cons Hneq andbF.
  rewrite eq_in_map /rec /f2 => -> {f1 f2 rec}.
  rewrite sumn_count /=.
  apply: (IHsh _ _ _ (is_row_consK Hisrow) Hsize Hskew0 (skew_yam_consK Hinn Hskew)).
  apply: (included_trans _ Hincl).
  exact: included_decr_nth.
Qed.


Lemma LRyamtab_list_countE innev inner sh0 row0 yamtab :
  is_part innev ->
  sorted geq (sh0 :: inner) ->
  is_part (sh0 + size row0 :: (outer_shape inner (shape yamtab))) ->
  size inner = size yamtab ->
  is_skew_tableau (sh0 :: inner) (row0 :: yamtab) ->
  is_skew_yam innev outev (to_word yamtab) ->
  count_mem yamtab
    (LRyamtab_list_rec innev inner (outer_shape inner (shape yamtab)) sh0 row0) = 1.
Proof.
  elim: yamtab innev inner sh0 row0 => [//= | row1 yamtab IHyamtab]
               innev [//= | inn0 inn] sh0 row0 Hinnev.
     by move=> _ _ /eqP/nilP -> /=.
  move=> Hinn Hout Hsize Hskew Hyam.
  rewrite /= in Hsize; move: Hsize => /eqP; rewrite eqSS => /eqP Hsize.
  have Hskewrec : is_skew_tableau (inn0 :: inn) (row1 :: yamtab).
    by move: Hskew => /=/and4P [].
  move/(_ _ inn inn0 row1 _ (path_sorted Hinn)
          (is_part_consK Hout) Hsize Hskewrec) : IHyamtab => Hrec.
  rewrite /= count_flatten -map_comp subSS -/(outer_shape _ _).
  set f1 := (X in map X); set rec := (X in map _ X).
  pose f2 := nat_of_bool \o (pred1 row1) \o (@fst (seq nat) (seq nat)).
  have : {in rec, f1 =1 f2}.
    rewrite /rec /f1 /f2 {rec f1 f2} => [[rshift shrshift]] /= Hrshift.
    rewrite count_map /=.
    case: (altP (rshift =P row1)) => [Hrow1 | /negbTE Hneq] /=.
    - rewrite Hrow1 (eq_count (a2 := pred1 yamtab)); first last.
        by move => y /=; rewrite eqseq_cons eq_refl /=.
      move: Hyam; rewrite to_word_cons.
      move: Hrshift => /flatten_mapP [] [row shrow] /yamtab_rowP/yamtab_shiftP H/H{H}.
      rewrite Hrow1 => Hsk1 Hsk2.
      apply (Hrec shrshift (is_part_skew_yam Hinnev Hsk1)).
      exact: (skew_yam_catrK Hinnev Hsk1 Hsk2).
    - rewrite (eq_count (a2 := pred0)); first by rewrite count_pred0.
      move=> y /=; by rewrite eqseq_cons Hneq.
  rewrite eq_in_map /rec /f2 => -> {f1 f2 rec Hrec}.
  rewrite !map_comp map_flatten -!map_comp sumn_count.
  rewrite count_flatten -map_comp.
  set f1 := (X in map X); set rowl := (X in map _ X).
  pose f2 := nat_of_bool \o (pred1 (drop (sh0 - inn0) row1)) \o (@fst (seq nat) (seq nat)).
  have : {in rowl, f1 =1 f2}.
    rewrite /rowl /f1 /f2 {rowl f1 f2} => [[row shrow]] /= Hrow.
    rewrite count_map /=.
    case: (altP (row =P (drop (sh0 - inn0) row1))) => [Hrow1 | /negbTE Hneq] /=.
    - have Hshrow := yamtab_rowP Hrow.
      rewrite -(cat_take_drop (sh0 - inn0) row1) -Hrow1.
      move: Hyam; rewrite to_word_cons => /(skew_yam_catK Hinnev) [] shrow1 Hshrow1.
      move=> /(skew_yam_included (is_part_skew_yam Hinnev Hshrow1)) Hincl.
      apply: (yamtab_shift_countE Hinnev _ _ Hshrow _ Hincl).
      + rewrite Hrow1 cat_take_drop.
        by move: Hskew => /= /and5P [] _ _ _ _ /andP [].
      + rewrite size_cat Hrow1 -size_cat cat_take_drop size_take -/(minn _ _).
        move: Hinn => /= /andP [] H0 _.
        by rewrite -{2}[sh0](subnKC H0) -addn_minr addKn.
      + move: Hshrow; rewrite Hrow1 => /(skew_yam_catrK Hinnev) H.
        move: Hshrow1; rewrite -{1}(cat_take_drop (sh0 - inn0) row1).
        exact: H.
    - rewrite (eq_in_count (a2 := pred0)); first by rewrite count_pred0.
      move=> [shift shshift] /yamtab_shift_drop /= Hshift.
      move: Hneq; apply contraFF.
      rewrite -Hshift => /eqP ->.
      case: (leqP sh0 (inn0 + size row1)) => [/minn_idPl -> //= | /ltnW Hover].
      have:= leq_sub2r inn0 Hover; rewrite (minn_idPr Hover) addKn.
      move => /drop_oversize ->.
      by rewrite drop_oversize.
  rewrite eq_in_map /rowl /f2 => -> {f1 f2 rowl}.
  rewrite map_comp sumn_count count_map /=.
  move: Hyam; rewrite to_word_cons -{1}(cat_take_drop (sh0 - inn0) row1) catA => Hyam.
  have:= skew_yam_catK Hinnev Hyam => [] [] shape Hdrop.
  move=> /(skew_yam_included (is_part_skew_yam Hinnev Hdrop)) Hshape.
  have Heq : size (drop (sh0 - inn0) row1) = size (take (inn0 + size row1 - sh0) row0).
    rewrite size_drop size_take bad_if_leq.
      move: Hinn => /=/andP [] /subnBA -> _.
      by rewrite addnC.
    move: Hout => //= /andP [] /(leq_sub2r sh0) H _.
    by rewrite addKn in H.
  apply: (yamtab_row_countE Hinnev Heq _ (is_row_drop _ _) Hdrop Hshape).
  - move: Hskew => /= /and4P [] _ _; rewrite skew_dominate_cut /skew_dominate => Hdom _.
    suff <- : size row1 - (sh0 - inn0) = inn0 + size row1 - sh0 by exact Hdom.
    move: Hinn => /= /andP [] /subnBA -> _.
    by rewrite addnC.
  - by move: Hskew => /= /and5P [] _ _ _ _ /andP [].
Qed.

End OutEval.

Definition LRyamtab_list inner eval outer :=
  LRyamtab_list_rec eval [::] inner outer (head 1 outer) [::].
Definition LRcoeff inner eval outer :=
  LRyamtab_count_rec eval [::] inner outer (head 1 outer) [::].

Lemma LRcoeffP inner eval outer :
  size (LRyamtab_list inner eval outer) = LRcoeff inner eval outer.
Proof. by rewrite size_LRyamtab_listE. Qed.

Lemma LRyamtab_yam inner eval outer tab:
  tab \in (LRyamtab_list inner eval outer) -> is_yam (to_word tab).
Proof.
  rewrite /LRyamtab_list -(cats0 (to_word tab)).
  exact: LRyamtab_list_recP.
Qed.

Lemma LRyamtab_included inner eval outer tab:
  tab \in (LRyamtab_list inner eval outer) -> included (evalseq (to_word tab)) eval.
Proof.
  rewrite /LRyamtab_list -(cats0 (to_word tab)).
  exact: LRyamtab_list_included.
Qed.

Lemma LRyamtab_shape inner eval outer tab :
  is_part inner -> is_part outer -> included inner outer ->
  tab \in (LRyamtab_list inner eval outer) -> shape tab = diff_shape inner outer.
Proof.
  move=> Hinn Hout Hincl.
  rewrite /LRyamtab_list LRyamtab_list_pad0 -diff_shape_pad0.
  move => /LRyamtab_list_shape0; apply => //=.
  - have /= := is_part_pad0 (size outer) Hinn.
    case: inner Hincl {Hinn Hout} => [//= | inn0 inn] /=.
    + rewrite subn0; by case outer.
    + by case: outer => [//= | out0 out] /= /andP [] -> _ ->.
  - by rewrite addn0 leqnn Hout.
  - by rewrite -included_pad0.
  - rewrite size_cat size_nseq; apply subnKC.
    exact: size_included.
Qed.

Lemma LRyamtab_skew_tableau inner eval outer tab :
  is_part inner -> is_part outer -> included inner outer ->
  tab \in (LRyamtab_list inner eval outer) -> is_skew_tableau inner tab.
Proof.
  move=> Hinn Hout Hincl.
  rewrite /LRyamtab_list LRyamtab_list_pad0 is_skew_tableau_pad0 => Htab.
  rewrite (LRyamtab_list_size Htab); move: Htab.
  have {Hinn} Hinn : sorted geq (head 1 outer :: (pad 0 (size outer)) inner).
    have /= := is_part_pad0 (size outer) Hinn.
    case: inner Hincl {Hinn Hout} => [//= | inn0 inn] /=.
    + rewrite subn0; by case outer.
    + by case: outer => [//= | out0 out] /= /andP [] -> _ ->.
  have {Hout} Hout : is_part (head 1 outer + (@size nat) [::] :: outer).
    by rewrite /= addn0 leqnn Hout.
  have Hincl0 : included ((pad 0 (size outer)) inner) outer.
    by rewrite -included_pad0.
  have Hsize : size ((pad 0 (size outer)) inner) = size outer.
    rewrite size_cat size_nseq; apply subnKC.
    exact: size_included.
  have Hrow : is_row (@nil nat) by [].
  by move/(LRyamtab_list_skew_tableau0 Hinn Hout Hincl0 Hsize Hrow) => /= /and3P [].
Qed.

Lemma LRyamtab_eval inner eval outer tab:
  is_part inner -> is_part outer -> included inner outer ->
  is_part eval -> sumn eval = sumn (diff_shape inner outer) ->
  tab \in (LRyamtab_list inner eval outer) -> evalseq (to_word tab) = eval.
Proof.
  move=> Hinn Hout Hincl Hev Hsumn Htab.
  apply (included_sumnE Hev (LRyamtab_included Htab)).
  rewrite Hsumn evalseq_eq_size size_to_word /size_tab.
  by rewrite (LRyamtab_shape Hinn Hout Hincl Htab).
Qed.

Lemma count_mem_LRyamtab_list inner eval outer yamtab :
  is_part inner -> is_part outer -> included inner outer ->
  is_skew_tableau inner yamtab -> shape yamtab = diff_shape inner outer ->
  is_yam_of_eval eval (to_word yamtab) ->
  count_mem yamtab (LRyamtab_list inner eval outer) = 1.
Proof.
  move=> Hinn Hout Hincl.
  rewrite /LRyamtab_list LRyamtab_list_pad0 is_skew_tableau_pad0 => Htab Hshape Hyam.
  have Hnil : is_part [::] by [].
  have {Hinn} Hinn : sorted geq (head 1 outer :: (pad 0 (size outer)) inner).
    have /= := is_part_pad0 (size outer) Hinn.
    case: inner Hincl {Hinn Hout Htab Hshape} => [//= | inn0 inn] /=.
    + rewrite subn0; by case outer.
    + by case: outer => [//= | out0 out] /= /andP [] -> _ ->.
  have Hsztab : size yamtab = size outer.
    by rewrite -(size_diff_shape inner outer) -Hshape size_map.
  have {Hout} Hout : is_part
                       ((head 1 outer + @size nat [::])
                          :: outer_shape ((pad 0 (size outer)) inner) (shape yamtab)).
    rewrite [size [::]]/= addn0 -Hsztab -(size_map size yamtab) -/(shape _).
    rewrite outer_shape_pad0 Hshape (diff_shapeK Hincl).
    case: outer Hout {Hincl Hshape Hinn Hsztab} => [//= | s0 s] /= ->.
    by rewrite leqnn.
  have Hsize : size ((pad 0 (size outer)) inner) = size yamtab.
    rewrite size_cat size_nseq subnKC; last exact: size_included.
    by rewrite -(size_diff_shape inner outer) -Hshape size_map.
  have Hskew : is_skew_tableau (head 1 outer :: (pad 0 (size outer)) inner)
                               ([::] :: yamtab).
    move: Htab; rewrite Hsztab /= => ->; rewrite andbT (part_head_non0 Hout) /=.
    case: outer Hincl Hshape Hsztab {Hinn Hout Hsize} => [|out0 out] /=.
      case: inner => [ _ _ /eqP/nilP ->| in0 inn] //=.
    case: inner => [_ | in0 inn] //=.
      case: yamtab {Hyam} => [ | yam0 yam] //= [] Hyam _ _.
      rewrite subn0; by rewrite /skew_dominate -Hyam drop_size.
    move=> /andP [] Hincl _.
    case: yamtab {Hyam}=> [ | yam0 yam] //= [] Hyam _ _.
    by rewrite /skew_dominate -Hyam drop_size.
  have {2}-> : outer = outer_shape ((pad 0 (size outer)) inner) (shape yamtab).
    by rewrite Hshape -(size_diff_shape inner outer)
                         outer_shape_pad0 (diff_shapeK Hincl).
  exact: LRyamtab_list_countE Hnil Hinn Hout Hsize Hskew (skew_nil_yamE Hyam).
Qed.


Section PackedSpec.

Variable  inner eval outer : seq nat.

Record inputSpec :=
  InputSpec {
      inner_part : is_part inner;
      outer_part : is_part outer;
      incl       : included inner outer;
      eval_part  : is_part eval;
      sumn_eq    : sumn eval = sumn (diff_shape inner outer)
    }.

Record outputSpec (tab : seq (seq nat)) :=
  OutputSpec {
      skew        : is_skew_tableau inner tab;
      shaps_eq    : shape tab = diff_shape inner outer;
      yam_to_word : is_yam (to_word tab);
      eval_eq     : evalseq (to_word tab) = eval
    }.

Lemma outputSpecP tab :
  inputSpec -> tab \in (LRyamtab_list inner eval outer) -> outputSpec tab.
Proof.
  move=> [] Hinn Hout Hincl Hev Hsumn Htab; constructor.
  - exact: (@LRyamtab_skew_tableau inner eval outer tab).
  - exact: (@LRyamtab_shape inner eval outer tab).
  - exact: (@LRyamtab_yam inner eval outer tab).
  - exact: (@LRyamtab_eval inner eval outer tab).
Qed.

Lemma outputSpec_count_mem tab :
  inputSpec -> outputSpec tab -> count_mem tab (LRyamtab_list inner eval outer) = 1.
Proof.
  move=> [] Hinn Hout Hincl Hev Hsumnc [] Htab Hshape Hyam Heval.
  apply: count_mem_LRyamtab_list => //=.
  by rewrite /is_yam_of_eval Hyam Heval eq_refl.
Qed.

End PackedSpec.

Section Spec.

Variables d1 d2 : nat.
Variables (P1 : intpartn d1) (P2 : intpartn d2).
Variable P : intpartn (d1 + d2).
Hypothesis Hincl : included P1 P.

Lemma LRyamtabP tab :
  tab \in (LRyamtab_list P1 P2 P) -> is_yam_of_eval P2 (to_word tab).
Proof.
  rewrite /is_yam_of_eval => Htab; apply /andP; split.
  - exact: LRyamtab_yam Htab.
  - rewrite (LRyamtab_eval (intpartnP P1) (intpartnP P) Hincl (intpartnP P2) _ Htab) //=.
    by rewrite (sumn_diff_shape Hincl) !intpartn_sumn addKn.
Qed.

Lemma LRyamtab_all :
  all (is_yam_of_eval P2) (map (@to_word _) (LRyamtab_list P1 P2 P)).
Proof. by apply/allP => w /mapP [] tab /LRyamtabP Htab ->. Qed.
Let bla := Eval hnf in [subCountType of yameval P2].
Definition LRyam_list := subType_seq bla LRyamtab_all.

Lemma LRyamtab_spec_recip yam :
  yam \in LRyam_set P1 P2 P ->
  count_mem (val yam) (map (@to_word _) (LRyamtab_list P1 P2 P)) = 1.
Proof.
  rewrite inE => Hyam.
  have Hszyam : size yam = sumn (diff_shape P1 P).
    by rewrite -evalseq_eq_size eval_yameval (sumn_diff_shape_intpartE P2).
  rewrite -[val yam](to_word_skew_reshape Hincl Hszyam).
  rewrite count_map.
  rewrite (eq_in_count (a2 := pred1 (skew_reshape P1 P (val yam)))); first last.
    move=> tab /= Htab; apply/idP/idP => [/eqP| /eqP -> //].
    rewrite (to_word_skew_reshape Hincl Hszyam) => <-.
    have Hshape := (LRyamtab_shape (intpartnP P1) (intpartnP P) Hincl Htab).
    have <- : (outer_shape P1 (shape tab)) = P by rewrite Hshape diff_shapeK.
    rewrite skew_reshapeK //= -(size_map size tab) -/(shape tab) Hshape size_diff_shape.
    exact: size_included.
  apply (count_mem_LRyamtab_list (intpartnP P1) (intpartnP P) Hincl Hyam).
  - by rewrite (shape_skew_reshape Hincl Hszyam).
  - rewrite /is_yam_of_eval; rewrite (to_word_skew_reshape Hincl Hszyam).
    by rewrite yamevalP eval_yameval eq_refl.
Qed.

Lemma LRyam_spec_recip yam :
  yam \in LRyam_set P1 P2 P -> count_mem yam LRyam_list = 1.
Proof.
  move=> /LRyamtab_spec_recip Hyam.
  rewrite (eq_count (a2 := pred1 (val yam) \o val)); last by [].
  by rewrite -count_map subType_seqP.
Qed.

Theorem LRcoeffE : LRyam_coeff P1 P2 P = LRcoeff P1 P2 P.
Proof.
  rewrite /LRyam_coeff -LRcoeffP -(size_map (@to_word _)).
  rewrite -sum1dep_card (eq_bigr (fun y => count_mem y LRyam_list)); first last.
    by move=> yam Hyam; rewrite LRyam_spec_recip //= inE.
  rewrite sum_count_mem.
  rewrite (eq_in_count (a2 := predT));
    first by rewrite count_predT -(size_map val) subType_seqP.
  move=> yam /=.
  rewrite -(mem_map val_inj) subType_seqP /= => /mapP [] tab Htab -> {yam}.
  have Hskew := LRyamtab_skew_tableau (intpartnP P1) (intpartnP P) Hincl Htab.
  have Hshape := LRyamtab_shape (intpartnP P1) (intpartnP P) Hincl Htab.
  rewrite /is_skew_reshape_tableau /=.
  have <- : (outer_shape P1 (shape tab)) = P by rewrite Hshape diff_shapeK.
  rewrite skew_reshapeK //= -(size_map size tab) -/(shape tab) Hshape size_diff_shape.
  exact: size_included.
Qed.

End Spec.

Section LR.

Variables d1 d2 : nat.
Variables (P1 : intpartn d1) (P2 : intpartn d2).

Require Import ssralg.

Local Open Scope ring_scope.
Import GRing.Theory.

Variable (n : nat) (R : comRingType).

Hypothesis Hnpos : n != 0%N.

Notation Schur p := (Schur Hnpos R p).

Theorem LRtab_coeffP :
  Schur P1 * Schur P2 =
  \sum_(P : intpartn (d1 + d2) | included P1 P) Schur P *+ LRcoeff P1 P2 P.
Proof.
  rewrite (LRtab_coeffP P1 P2 R Hnpos).
  by apply eq_bigr => outer /LRcoeffE ->.
Qed.

End LR.
