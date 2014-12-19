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
Require Import tuple finfun finset bigop.

Require Import partition schensted ordtype std stdtab invseq congr plactic greeninv yamplact.
Require Import shuffle multpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N.

Section Dominate.

  Variable T : ordType.
  Notation Z := (inhabitant T).

  Implicit Type u v : seq T.

  Definition skew_dominate sh u v :=
    ((size u) <= (size v) + sh) &&
     (all (fun i => (nth Z u i > nth Z v (i - sh))%Ord) (iota sh ((size u) - sh))).

  Lemma skew_dominate0 : skew_dominate 0 =2 (@dominate T).
  Proof.
    move=> u v /=; rewrite /skew_dominate /dominate addn0 subn0.
    bool_congr; apply eq_all => i.
    by rewrite subn0.
  Qed.

  Lemma skew_dominateP sh u v :
    reflect (((size u) <= (size v) + sh) /\
             forall i, sh <= i < size u -> (nth Z u i > nth Z v (i - sh))%Ord)
            (skew_dominate sh u v).
  Proof.
    rewrite /dominate /mkseq /skew_dominate; apply/(iffP idP).
    - move=> /andP [] Hsz /allP Hall; split; first by exact Hsz.
      move=> i /andP [] Hi Hisz; apply: Hall.
      rewrite mem_iota Hi /= subnKC; first exact Hisz.
      apply: (leq_trans Hi); by apply ltnW.
    - move=> [] -> /= H; apply/allP => i; rewrite mem_iota => /andP [] Hi Hisz.
      apply: H; rewrite Hi /=.
      move: Hisz; case (leqP sh (size u)) => Hu.
      + by rewrite (subnKC Hu).
      + have := ltnW Hu; rewrite {1}/leq => /eqP ->.
        rewrite addn0 => /(leq_ltn_trans Hi).
        by rewrite ltnn.
  Qed.

  Fixpoint is_skew_tableau inner t :=
    if t is t0 :: t'
    then [&& size t0 + head 0 inner != 0,
         is_row t0,
         skew_dominate ((head 0 inner) - (head 0 (behead inner)))
                       (head [::] t') t0 & is_skew_tableau (behead inner) t']
    else inner == [::].

  Lemma is_skew_tableau0 : is_skew_tableau [::] =1 (@is_tableau T).
  Proof.
    elim => [//=| t0 t IHt] /=.
    rewrite addn0 subn0 skew_dominate0 IHt.
    by case t0.
  Qed.

  Fixpoint included inner outer :=
    if inner is inn0 :: inn then
      if outer is out0 :: out then
        inn0 <= out0 && included inn out
      else false
    else true.

  (* zip add completing with 0s *)
  Fixpoint outer_shape inner size_seq :=
    if inner is inn0 :: inn then
      if size_seq is sq0 :: sq then
        sq0 + inn0 :: outer_shape inn sq
      else inner
    else size_seq.

  Fixpoint diff_shape inner outer :=
    if inner is inn0 :: inn then
      if outer is out0 :: out then
        out0 - inn0 :: diff_shape inn out
      else [::] (* Wrong case *)
    else outer.

  Definition skew_reshape (inner outer : seq nat) (s : seq T) :=
    rev (reshape (rev (diff_shape inner outer)) s).

  Lemma diff_outer_shape inner (t : seq (seq T)) :
    is_skew_tableau inner t ->
    diff_shape inner (outer_shape inner (shape t)) = shape t.
  Proof.
    elim: inner t => [//= | inn0 inn IHinn] /=.
    case=> [//=| t0 t] /and4P [] _ _ _ /IHinn{IHinn} Hrec /=.
    by rewrite addnK Hrec.
  Qed.

  Lemma skew_reshapeK inner t :
    is_skew_tableau inner t ->
    skew_reshape inner (outer_shape inner (shape t)) (to_word t) = t.
  Proof.
    move=> H; rewrite /skew_reshape (diff_outer_shape H).
    by rewrite /to_word -shape_rev flattenK revK.
  Qed.

End Dominate.

Lemma reshape_rcons (T : eqType) (s : seq T) sh sn :
  sumn sh + sn = size s ->
  reshape (rcons sh sn) s = rcons (reshape sh (take (sumn sh) s)) (drop (sumn sh) s).
Proof.
  elim: sh s => [//= | s0 sh IHsh] /= s.
    rewrite add0n => Hsz.
    by rewrite drop0 take_oversize; last by rewrite Hsz.
  move=> Hsize.
  have Hs0 : (if s0 < size s then s0 else size s) = s0.
    by rewrite bad_if_leq; last by rewrite -Hsize -addnA; apply leq_addr.
  have -> : take (s0 + sumn sh) s = take s0 s ++ take (sumn sh) (drop s0 s).
    rewrite -{1 3}[s](cat_take_drop s0) drop_cat take_cat size_take.
    by rewrite Hs0 ltnNge leq_addr /= addKn ltnn subnn drop0.
  rewrite take_cat size_take Hs0 ltnn subnn take0 cats0.
  rewrite drop_cat size_take Hs0 ltnn subnn drop0.
  have -> : drop (s0 + sumn sh) s = drop (sumn sh) (drop s0 s).
    rewrite -[s](cat_take_drop s0) !drop_cat size_take.
    by rewrite Hs0 ltnNge leq_addr /= addKn ltnn subnn drop0.
  by rewrite -IHsh; last by rewrite size_drop -Hsize -addnA addKn.
Qed.

Lemma is_row_stdE (T : ordType) (w : seq T) : is_row (std w) = is_row w.
Proof.
  apply/(sameP idP); apply(iffP idP) => /is_rowP Hrow.
  - apply/(is_rowP (inhabitant nat_ordType)) => i j Hij; rewrite size_std => Hj.
    have := eq_inv_std w; rewrite -eq_invP => [] [] _ <-; last by rewrite Hij Hj.
    by apply Hrow.
  - apply/(is_rowP (inhabitant T)) => i j Hij Hj.
    have := eq_inv_std w; rewrite -eq_invP => [] [] _ ->; last by rewrite Hij Hj.
    by apply Hrow; last by rewrite size_std.
Qed.

Lemma eq_inv_skew_dominate (T1 T2 : ordType) (u1 v1 : seq T1) (u2 v2 : seq T2) s :
  eq_inv (u1 ++ v1) (u2 ++ v2) -> size u1 = size u2 ->
  skew_dominate s u1 v1 -> skew_dominate s u2 v2.
Proof.
  move/eq_invP => []; rewrite !size_cat => Hsz Hinv Hszu /skew_dominateP [] Hsz1 Hdom.
  apply/skew_dominateP; split.
    by rewrite -(leq_add2l (size u1)) addnA {2}Hszu -Hsz -addnA leq_add2l -Hszu.
  rewrite -Hszu => i Hi; have {Hdom} := Hdom _ Hi.
  set Z1 := inhabitant T1; set Z2 := inhabitant T2.
  rewrite -/Z1 -/Z2 in Hinv.
  move: Hi => /andP [] Hs Hi.
  have -> : nth Z1 v1 (i - s) = nth Z1 (u1 ++ v1) (i - s + size u1).
    by rewrite nth_cat -{2}[size u1]add0n ltn_add2r /= addnK.
  have -> : nth Z2 v2 (i - s) = nth Z2 (u2 ++ v2) (i - s + size u1).
    by rewrite nth_cat -{1}[size u2]add0n Hszu ltn_add2r /= addnK.
  have -> : nth Z1 u1 i = nth Z1 (u1 ++ v1) i.
    by rewrite nth_cat Hi.
  have -> : nth Z2 u2 i = nth Z2 (u2 ++ v2) i.
    by rewrite nth_cat -Hszu Hi.
  rewrite !ltnXNgeqX; apply contra.
  rewrite Hinv {Hinv Z1 Z2} //.
  rewrite -(leq_add2r s) -(ltn_add2r s) -addnA [size u1 + s]addnC addnA (subnK Hs).
  rewrite leq_add2l (leq_trans Hs (ltnW Hi)) /= addnC -addnA ltn_add2l.
  by apply (leq_trans Hi).
Qed.

(*
Lemma skew_reshape_stdK (T : ordType) inner (t : seq (seq T)) :
  is_skew_tableau inner
                  (skew_reshape inner (outer_shape inner (shape t)) (std (to_word t))) ->
  is_skew_tableau inner t.
Proof.
  rewrite /skew_reshape /to_word.
  elim: inner => [| inn0 inn IHinn] /=.
    elim: t => [//= | t0 t IHt] /=.
    rewrite addn0 subn0 !rev_cons flatten_rcons.
    rewrite reshape_rcons; last by rewrite size_std size_cat size_flatten shape_rev.
    rewrite rev_rcons /= addn0 subn0 => /and4P [].
    rewrite size_drop size_std size_cat size_flatten shape_rev addKn => -> /=.
    rewrite -is_row_stdE -shape_rev -size_flatten std_drop_std is_row_stdE => -> /=.
    move=> Hdom Htab; apply /andP; split.
    - admit.
    - apply IHt.
    rewrite drop_cat.
      admit.
    case: outer => [//= | out0 out] /=.
    rewrite rev_cons /= !reshape_rcons. rev_rcons.
*)

Definition LR_yam_compute (P1 P2 P : seq nat) :=
  (filter
     ((is_skew_tableau P1) \o (skew_reshape P1 P))
     (list_yamsh P2)).
Definition LR_coeff_compute (P1 P2 P : seq nat) :=
  size (LR_yam_compute P1 P2 P).

Definition LR_coeff_yam d1 d2
           (P1 : intpartn d1) (P2 : intpartn d2) (P : intpartn (d1 + d2)) :=
  #|[set s : yamsh_finType (intpartnP P2) | is_skew_tableau P1 (skew_reshape P1 P s)]|.

Lemma LR_coeff_computeP d1 d2
           (P1 : intpartn d1) (P2 : intpartn d2) (P : intpartn (d1 + d2)) :
    LR_coeff_compute P1 P2 P = LR_coeff_yam P1 P2 P.
Proof.
  rewrite /LR_coeff_yam /LR_coeff_compute /LR_yam_compute.
  rewrite cardE /enum_mem.
  rewrite -(size_map val); congr (size _).
  set E := Finite.enum _; have -> : (list_yamsh P2) = map val E.
    rewrite /E unlock /= /yamsh_enum (pmap_filter (insubK _)).
    rewrite (eq_in_filter (a2 := predT)); first by rewrite filter_predT.
    move=> i /= /(allP (list_yamshP (intpartP P2))).
    by rewrite isSome_insub => ->.
  rewrite filter_map; congr (map _ _).
  apply eq_filter => y /=.
  by rewrite inE.
Qed.


(*
Definition yam_from_LRtab inner eval (tab : seq (seq nat)) :=
  let sinn := sumn inner in
    map (subs_eval eval) (sfilterleq sinn ((@to_word _) tab)).

(* Definition LR_support :=
  [set Q : stdtabn (d1 + d2) | predLRTriple Q1 Q2 Q ]. *)

Lemma bij1 d1 d2 (P1 : intpartn d1) (P2 : intpartn d2) (P : intpartn (d1 + d2)) Q :
  Q \in (LR_support (hyper_stdtab P1) (hyper_stdtab P2)) -> (shape Q == P)
       -> is_yam_of_shape P2 (yam_from_LRtab P1 P2 Q).
Proof.
  rewrite /LR_support inE => /LRTripleP Htmp.
  have:= hyper_stdtabP P1 => /= /andP [] Hstd1 _.
  have:= hyper_stdtabP P2 => /= /andP [] Hstd2 _.
  have {Htmp} := Htmp Hstd1 Hstd2 => [] [] p1 p2 p Hp1 Hp2 <- {Q} Hshsh Hsh.
  have -> : val P1 = shape (RS p1).
    by rewrite Hp1 shape_stdtab_of_yam (shape_rowseq_hyper_yam (intpartnP P1)).
  rewrite /yam_from_LRtab -[sumn (shape (RS p1))]/(size_tab (RS p1)) (size_RS p1).

  have := (shsh_sfilterleq _ Hshsh).
  have: plactcongr w p2.
  admit.
Qed.

Theorem LR_coeff_yamP d1 d2 (P1 : intpartn d1) (P2 : intpartn d2) (P : intpartn (d1 + d2)) :
  (LR_coeff P1 P2 P) = (LR_coeff_yam P1 P2 P).
Proof.
  rewrite /LR_coeff /LR_coeff_yam.
  admit.
Qed.
*)
(*
Eval compute in is_skew_tableau _ [:: 1] [:: [:: 2] ; [:: 1; 3]].
Eval compute in is_skew_tableau _ [:: 1] [:: [:: 3] ; [:: 1; 2]].

Eval compute in diff_shape [:: 2; 1] [:: 3; 2; 1].
Eval compute in LR_coeff_compute [:: 2; 1] [:: 2; 1] [:: 3; 2; 1].
Eval compute in LR_coeff_compute [:: 3; 3; 1] [:: 4; 2; 1] [:: 5; 4; 3; 2].
Eval compute in LR_coeff_compute [:: 4; 3; 1] [:: 4; 3; 2; 1] [:: 7; 5; 4; 2].
Eval compute in LR_coeff_compute [:: 4; 3; 2; 1] [:: 4; 3; 1] [:: 7; 5; 4; 2].
*)
