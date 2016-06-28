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
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
From mathcomp Require Import finset perm fingroup matrix ssralg path bigop.
Require Import tools combclass subseq partition Yamanouchi tableau permuted stdtab ordtype Schensted plactic Greene Greene_inv std skewtab shuffle freeSchur therule.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Move in Yamanouchi *)

Lemma evalseq_nseq0 n : evalseq (nseq n.+1 0) = [:: n.+1].
Proof. by elim: n => [| n] //= ->. Qed.

Lemma evalseq_size1 n s : evalseq s = [:: n] -> s = nseq n 0.
Proof.
  elim: n s => [| n IHn] //= s Hs.
    exfalso; suff {Hs} : last 1 (evalseq s) != 0 by rewrite Hs.
    elim: s => [| s0 s] //=; exact: last_incr_nth_non0.
  case: n IHn Hs => [_| n IHn].
  - case: s => [| s0 [|s1 s]] //=; first by case: s0.
    by move=> /(congr1 sumn) /=; rewrite !sumn_incr_nth addn0.
  - case: s => [| s0 s] //=.
    case: s0 => [//=|s0].
    + case H : (evalseq s) => [//= | e0 e] [] He0 He; subst e0 e.
      by move: H => /IHn ->.
    + case H : (evalseq s) => [//= | e0 e] /=.
      move=> /(congr1 size) /=; rewrite size_incr_nth.
      case: ltnP => //= Hs0 [] Hsz.
      by rewrite Hsz in Hs0.
Qed.

Section RSKSeqRow.

Variable T : inhOrdType.
Notation Z := (inhabitant T).

Implicit Type s r : seq T.
Implicit Type sr : seq (seq T).

Fixpoint RS_insrow (P : seq (seq T)) r :=
  if r is r0 :: r then RS_insrow (instab P r0) r
  else P.

Fixpoint RSKSeqRow_rev sr : seq (seq T) * seq (seq nat) :=
  if sr is r :: sr then
    let: (P, Q) := RSKSeqRow_rev sr in
    let: Pres := RS_insrow P r in
    (Pres, join_tab Q (skew_reshape (shape P) (shape Pres)
                                   (nseq (size r) (size sr))))
  else ([::], [::]).
Definition RSKSeqRow sr : seq (seq T) * seq (seq nat) := RSKSeqRow_rev (rev sr).

Lemma RS_insrowP w r : RS_insrow (RS w) r = RS (w ++ r).
Proof using  .
  elim: r w => [| r0 r IHr] w /=; first by rewrite cats0.
  rewrite -cat1s catA cats1.
  have -> : instab (RS w) r0 = RS (rcons w r0) by rewrite /RS rev_rcons /=.
  exact: IHr.
Qed.

Lemma RS_insrow_rcons P r rn :
  RS_insrow P (rcons r rn) = instab (RS_insrow P r) rn.
Proof using. by elim: r P => [| r0 r IHr] P /=. Qed.

Lemma included_shape_RS_insrow P r :
  is_tableau P -> included (shape P) (shape (RS_insrow P r)).
Proof.
  move=> HP.
  elim/last_ind: r => [| r rn IHr] /=; first exact: included_refl.
  rewrite RS_insrow_rcons; apply (included_trans IHr).
  rewrite -(RS_tabE HP) RS_insrowP.
  rewrite -instabnrowE.
  have := shape_instabnrow rn (is_tableau_RS (to_word P ++ r)).
  case: (instabnrow (RS (to_word P ++ r)) rn) => [tr nrow] /= ->.
  exact: included_incr_nth.
Qed.

Lemma row_langQ r :
  is_row r -> r \in langQ (stdtab_of_yam (nseq (size r) 0)).
Proof.
  case: (altP (r =P [::])) => [-> //=| Hnnil].
  rewrite inE => Hrow.
  have Htabr : is_tableau [:: r] by rewrite /= Hnnil Hrow.
  have:= shape_RStabmapE r.
  have {Hnnil Hrow Htabr} := RS_tabE Htabr; rewrite /to_word /= cats0.
  rewrite -RStabmapE /RStabmap; case: (RSmap r) => [P Q] /= -> /= /esym.
  by rewrite shape_stdtab_of_yam => /evalseq_size1 ->.
Qed.

Lemma hb_row s r :
  is_row r -> hb_strip (shape (RS s)) (shape (RS (s ++ r))).
Proof.
  move=> Hrow.
  rewrite -!RStabmapE !shape_RStabmapE.
  have Hst1 := is_stdtab_RStabmap2 s.
  have /stdtab_of_yamP Hst2 : is_yam (nseq (size r) 0).
    case: (size r) => [//=| n].
    elim: n => //= n /andP [-> ->].
    by have := evalseq_nseq0 n => /= ->.
  have {Hst1} Hstn1 : is_stdtab_of_n (size s) (RStabmap s).2.
    rewrite /= Hst1 /=.
    by rewrite /size_tab -shape_RStabmapE RStabmapE -/(size_tab _) size_RS.
  pose tab1 := StdtabN Hstn1.
  have {Hst2} Hstn2 : is_stdtab_of_n (size r) (stdtab_of_yam (nseq (size r) 0)).
    rewrite /= Hst2 /=.
    rewrite /size_tab shape_stdtab_of_yam.
    case: (size r) => [//= | n].
    by rewrite evalseq_nseq0 /= addn0.
  pose tab2 := StdtabN Hstn2.
  have Hstnres : is_stdtab_of_n (size s + size r) (RStabmap (s ++ r)).2.
    rewrite /= is_stdtab_RStabmap2 /=.
    rewrite /size_tab -shape_RStabmapE RStabmapE -/(size_tab _) size_RS.
    by rewrite size_cat.
  pose tabres := StdtabN Hstnres.
  have {Hrow} Htriple : LRtriple tab1 tab2 tabres.
    apply LRtriple_cat_langQ; rewrite // inE //.
    exact: row_langQ Hrow.
  have {Htriple} Hsupp : tabres \in LRsupport tab1 tab2.
    by rewrite /LRsupport inE -LRtriple_fastE //; apply/LRtripleP.
  have Hincl : included (shape_deg tab1) (shape_deg tabres).
    rewrite /= -!shape_RStabmapE !RStabmapE -RS_insrowP.
    apply: included_shape_RS_insrow; exact: is_tableau_RS.
  have /= := LRyam_coeff_rowpart Hincl.
  case: (hb_strip _ _) => //=; rewrite -LRyam_coeffE //.
  rewrite (LRtab_coeff_shapeE (T1 := tab1) (T2 := tab2)) //=; first last.
    rewrite shape_stdtab_of_yam /rowpart /=.
    by case: (size r) => [//= |n]; rewrite evalseq_nseq0.
  by move=> /card0_eq/(_ tabres); rewrite inE Hsupp /= eq_refl inE.
Qed.


Lemma RSKSeqRow_PE sr : (RSKSeqRow sr).1 = RS (flatten sr).
Proof using .
  rewrite /RSKSeqRow.
  elim/last_ind: sr => [//= | sr r].
  rewrite rev_rcons /=.
  case: (RSKSeqRow_rev (rev sr)) => [P Q] /= ->.
  by rewrite flatten_rcons RS_insrowP.
Qed.

Lemma shape_join_tab (S : inhOrdType) (s t : seq (seq S)) :
  shape (join_tab s t) =
  ([seq r.1 + r.2 | r <- zip (pad 0 (size t) (shape s)) (shape t)])%N.
Proof using .
  rewrite /shape /join_tab -map_comp.
  rewrite (eq_map (f2 := (fun p => p.1 + p.2) \o
                         (fun p => (size p.1, size p.2)))); first last.
    by move=> [a b] /=; rewrite size_cat.
  rewrite map_comp; congr map.
  elim: t s => [| t0 t IHt] [| s0 s] //=.
    by have /= := (IHt [::]); rewrite subn0 => ->.
  by rewrite IHt /= subSS.
Qed.

Lemma shape_join_tab_skew_reshape
      (S : inhOrdType) (t : seq (seq S)) sh w:
  included (shape t) sh ->
  size w = sumn (diff_shape (shape t) sh) ->
  shape (join_tab t (skew_reshape (shape t) sh w)) = sh.
Proof using.
  move=> Hincl Hsz.
  rewrite shape_join_tab size_skew_reshape shape_skew_reshape // {Hsz w}.
  move: (shape t) Hincl => inner {t}.
  elim: sh inner => [| s0 sh IHsh] [|in0 inn] //=.
    rewrite add0n => _ {IHsh}; congr (_ :: _) => {s0}.
    by elim: sh => //= s0 sh ->.
  move=> /andP [Hin0 /IHsh {IHsh}]; rewrite /pad /= => Hrec.
  by rewrite subSS (subnKC Hin0) Hrec.
Qed.

Lemma shape_RSKSeqRow sr :
  let: (P, Q) := RSKSeqRow sr in shape P = shape Q.
Proof using .
  elim/last_ind: sr => [| sr r] //=.
  have := RSKSeqRow_PE sr.
  rewrite /RSKSeqRow rev_rcons /=.
  case: (RSKSeqRow_rev (rev sr)) => [P Q] /= HPRS Hsh.
  have := is_tableau_RS (flatten sr); rewrite -HPRS.
  move=> /(included_shape_RS_insrow r) Hincl.
  rewrite Hsh shape_join_tab_skew_reshape // -Hsh //.
  rewrite size_nseq sumn_diff_shape //.
  by rewrite -!/(size_tab _) HPRS RS_insrowP !size_RS size_cat addKn.
Qed.

Lemma allLtn_RSKSeqRow sr :
  allLtn (to_word (RSKSeqRow sr).2) (size sr).
Proof using .
  elim/last_ind: sr => [| sr r] //=.
  have := RSKSeqRow_PE sr.
  have := shape_RSKSeqRow sr.
  rewrite /RSKSeqRow rev_rcons /=.
  case: (RSKSeqRow_rev (rev sr)) => [P Q] /= Hsh HPRS Hall.
  have:= is_tableau_RS (flatten sr); rewrite -HPRS.
  move=> /(included_shape_RS_insrow r) Hincl.
  have : size Q <=
         size
           (skew_reshape (shape P) (shape (RS_insrow P r))
                         (nseq (size r) (size sr))).
    rewrite size_skew_reshape -(size_map size Q) -/(shape Q) -Hsh.
    by move: Hincl => /includedP [].
  rewrite size_rev => /perm_eq_join_tab/perm_eq_allLtnE => ->.
  rewrite /allLtn all_cat size_rcons; apply /andP; split.
  - move:Hall; rewrite /allLtn.
    apply sub_all => i /=.
    rewrite !ltnXnatE; exact: ltnW.
  - rewrite to_word_skew_reshape //.
    + by rewrite all_nseq /= ltnXnatE ltnS leqnn orbT.
    + rewrite size_nseq sumn_diff_shape //.
      by rewrite -!/(size_tab _) HPRS RS_insrowP !size_RS size_cat addKn.
Qed.


Lemma RSKSeqRow_QP sr :
  all (sorted leqX_op) sr -> is_tableau (RSKSeqRow sr).2.
Proof using .
  elim/last_ind: sr => [| sr r] //= IHsr /=.
  rewrite all_rcons => /andP [Hrow /IHsr {IHsr}].
  have := RSKSeqRow_PE sr.
  have := shape_RSKSeqRow sr.
  have := allLtn_RSKSeqRow sr.
  rewrite /RSKSeqRow rev_rcons /=.
  case: (RSKSeqRow_rev (rev sr)) => [P Q] /= Hall Hsh HPRS HQ.
  have := is_tableau_RS (flatten sr); rewrite -HPRS.
  move=> /(included_shape_RS_insrow r) Hincl.
  apply join_tab_skew => //.
  - rewrite to_word_skew_reshape //; first last.
      rewrite size_nseq sumn_diff_shape //.
      by rewrite -!/(size_tab _) HPRS RS_insrowP !size_RS size_cat addKn.
    by rewrite all_nseq size_rev Hall orbT.
  - rewrite -Hsh.
    suff : hb_strip (shape P) (shape (RS_insrow P r)).
      rewrite -(hb_strip_rowE (u := (nseq (size r) (size (rev sr))))).
      + by move=> /andP [].
      + by rewrite HPRS; apply is_part_sht; exact: is_tableau_RS.
      + by rewrite HPRS RS_insrowP; apply is_part_sht; exact: is_tableau_RS.
      + apply/(is_rowP 0) => i j; rewrite size_nseq => /andP [Hij Hj].
        by rewrite !nth_nseq Hj (leq_ltn_trans Hij Hj).
      + rewrite size_nseq sumn_diff_shape //.
        by rewrite -!/(size_tab _) HPRS RS_insrowP !size_RS size_cat addKn.
    rewrite HPRS RS_insrowP.
    exact: hb_row.
Qed.

Lemma RSKSeqRowP sr :
  all (sorted leqX_op) sr ->
  let: (P, Q) := RSKSeqRow sr in
  is_tableau P && is_tableau Q && (shape P == shape Q).
Proof.
  move=> Hrow.
  have:= RSKSeqRow_QP Hrow.
  have:= shape_RSKSeqRow sr.
  have:= is_tableau_RS (flatten sr).
  rewrite -(RSKSeqRow_PE sr).
  case: (RSKSeqRow sr) => [P Q] /= -> -> ->.
  by rewrite eq_refl.
Qed.

Lemma eval_RSKSeqRowP sr :
  evalseq (to_word (RSKSeqRow sr).2) = shape sr.
Proof.
  rewrite /RSKSeqRow.
  elim/last_ind: sr => [| sr r] //=.
  rewrite rev_rcons /=.
  case: (RSKSeqRow_rev (rev sr)) => [P Q] /=.
  rewrite {4}/shape map_rcons -/(shape _) => <-.
  
  
Lemma std_RSKSeqRow_QP (sr : seq (seq T)) :
  all (sorted leqX_op) sr ->
  (RStabmap (to_word sr)).2 =
  skew_reshape [::] (shape (RSKSeqRow sr).1) (std (to_word (RSKSeqRow sr).2)).
Proof.
Admitted.

End Defs.



  Local Open Scope ring_scope.
Import GRing.Theory.

(* Definition bimon (A B : finType) := {ffun A*B -> nat}. *)
Definition word_of_mat m n (M : 'M[nat]_(m, n)) : seq 'I_n :=
  flatten [seq flatten [seq nseq (M a b) b | a : 'I_m] | b : 'I_n].

Section Defs.

Variables (m n : nat).

Definition bimon_of_mat (M : 'M[nat]_(m, n)) : seq ('I_m * 'I_n) :=
  flatten [seq nseq (M a b) (a, b) | a <- enum 'I_m, b <- enum 'I_n].

Definition RSK (M : 'M[nat]_(m.+1, n.+1)) :=
  (RS (word_of_mat M), RS (word_of_mat M^T)).

End Defs.
