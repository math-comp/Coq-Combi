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


Lemma sumn_rev s : sumn (rev s) = sumn s.
Proof.
  elim: s => [//= | s0 s /= <-].
  by rewrite rev_cons -cats1 sumn_cat /= addn0 addnC.
Qed.

Lemma size_reshape (T : Type) sh (s : seq T) : size (reshape sh s) = size sh.
Proof. elim: sh s => [//= | s0 sh IHsh] /= s; by rewrite IHsh. Qed.

Lemma reshape_rcons (T : Type) (s : seq T) sh sn :
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

  Lemma is_skew_tableau_nil : is_skew_tableau [::] =1 (@is_tableau T).
  Proof.
    elim => [//=| t0 t IHt] /=.
    rewrite addn0 subn0 skew_dominate0 IHt.
    by case t0.
  Qed.

  Definition pad0 sz := [fun s => s ++ nseq (sz - size s) 0].

  Lemma is_skew_tableau_pad0 inner t :
    is_skew_tableau inner t = is_skew_tableau (pad0 (size t) inner) t.
  Proof.
    elim: t inner => [| t0 t IHt] /= inner; first by rewrite cats0.
    case: inner => [| inn0 inn] /=.
      rewrite (IHt [::]) /= addn0.
      by rewrite !subn0.
    rewrite (IHt inn) subSS /=.
    suff -> : head 0 (inn ++ nseq (size t - size inn) 0) = head 0 inn by [].
    case: inn => [| inn1 inn] //=.
    by case: (size t - 0).
  Qed.

  Fixpoint included inner outer :=
    if inner is inn0 :: inn then
      if outer is out0 :: out then
        (inn0 <= out0) && (included inn out)
      else false
    else true.

  Fixpoint diff_shape inner outer :=
    if inner is inn0 :: inn then
      if outer is out0 :: out then
        out0 - inn0 :: diff_shape inn out
      else [::] (* Wrong case *)
    else outer.

  Lemma size_diff_shape inner outer : size (diff_shape inner outer) = size outer.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] /= [//= | out0 out] /=.
    by rewrite IHinn.
  Qed.

  Lemma sumn_diff_shape inner outer :
    included inner outer -> sumn (diff_shape inner outer) = sumn outer - sumn inner.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] /= [//= | out0 out] /=.
      by rewrite subn0.
    move/andP => [] Hleq Hincl.
    rewrite (IHinn _ Hincl) {IHinn}.
    have Hsumn : sumn inn <= sumn out.
      elim: inn out Hincl => [//= | inn1 inn IHinn] /= [//= | out1 out] /=.
      move/andP => [] H1 /IHinn; by apply leq_add.
    by rewrite subnDA (addnBA _ Hsumn) addnC (addnBA _ Hleq) [out0 + _]addnC.
  Qed.

  Definition skew_reshape (inner outer : seq nat) (s : seq T) :=
    rev (reshape (rev (diff_shape inner outer)) s).

  Lemma diff_shape_pad0 inner outer :
    diff_shape ((pad0 (size outer)) inner) outer = diff_shape inner outer.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] //=.
      elim=> [//= | out0 out] /=; by rewrite !subn0 => ->.
    case=> [//= | out0 out] /=.
    by rewrite subSS IHinn.
  Qed.

  Definition outer_shape inner size_seq :=
    [seq p.1 + p.2 | p <- zip (pad0 (size (size_seq)) inner) size_seq].

  Lemma diff_outer_shape inner (t : seq (seq T)) :
    size inner <= size t ->
    diff_shape inner (outer_shape inner (shape t)) = shape t.
  Proof.
    rewrite /outer_shape.
    elim: inner t => [//= | inn0 inn IHinn] /=.
      move=> t _; elim: t=> [//= | t0 t] /=.
      by rewrite add0n subn0 => ->.
    case=> [//=| t0 t] /=; rewrite ltnS subSS => /IHinn /= ->.
    by rewrite addKn.
  Qed.

  Lemma skew_reshapeK inner t :
    size inner <= size t ->
    skew_reshape inner (outer_shape inner (shape t)) (to_word t) = t.
  Proof.
    move=> H; rewrite /skew_reshape (diff_outer_shape H).
    by rewrite /to_word -shape_rev flattenK revK.
  Qed.

End Dominate.


Section FilterLeqGeq.

Variable T : ordType.
Notation Z := (inhabitant T).

Implicit Type l : T.
Implicit Type r w : seq T.
Implicit Type t : seq (seq T).

Lemma filter_geqX_row r n :
  is_row r -> filter (ltnX n) r = drop (count (geqX n) r) r.
Proof.
  elim: r => [//= | r0 r IHr] Hrow /=.
  case: (leqXP r0 n) => Hr0.
  - by rewrite add1n (IHr (is_row_consK Hrow)).
  - rewrite add0n; have Hcount : count (geqX n) r = 0.
      elim: r r0 Hr0 Hrow {IHr} => [//= | r1 r /= IHr] r0 Hr0 /andP [] Hr0r1 Hpath.
      have Hr1 := ltnX_leqX_trans Hr0 Hr0r1.
      by rewrite leqXNgtnX Hr1 (IHr r1 Hr1 Hpath).
    by rewrite Hcount (IHr (is_row_consK Hrow)) Hcount drop0.
Qed.

(*
Lemma filter_geqX_dominate r1 r0 n :
    is_row r0 -> is_row r1 -> dominate r1 r0 ->
    dominate (filter (ltnX n) r1) (filter (ltnX n) r0).
Proof.
  move=> Hrow0 Hrow1 /dominateP [] Hsz Hdom.
  have Hsize : (count (geqX n) r1) <= (count (geqX n) r0).
    rewrite -[r0](mkseq_nth Z) -[r1](mkseq_nth Z) /mkseq !count_map.
    rewrite -(subnKC Hsz).
    rewrite iota_add count_cat.
    set s0 := (X in X + _).
    apply (@leq_trans s0); last by apply leq_addr.
    rewrite /s0 {s0} -!size_filter.
    set f1 := (X in filter X _); set f0 := (X in _ <= size (filter X _)).
    rewrite (eq_in_filter (a1 := f1) (a2 := predI f1 (gtn (size r1)))); first last.
      move=> i; rewrite mem_iota /= add0n => ->; by rewrite andbT.
    rewrite (eq_in_filter (a1 := f0) (a2 := predI f0 (gtn (size r1)))); first last.
      move=> i; rewrite mem_iota /= add0n => ->; by rewrite andbT.
    rewrite !size_filter; apply sub_count => i /=.
    rewrite /f1 /f0 {f1 f0} /= => /andP [] Hn Hi;
    rewrite Hi andbT; apply ltnXW.
    by apply (ltnX_leqX_trans (Hdom i Hi) Hn).
  apply/dominateP; rewrite !size_filter.
  split; first exact Hsize.
  move=> i Hi.
  rewrite (filter_geqX_row _ Hrow0) (filter_geqX_row _ Hrow1) !nth_take.
  - apply Hdom; apply (leq_trans Hi); by apply count_size.
  - exact Hi.
  - by apply (leq_trans Hi).
Qed.

Definition filter_geqX_tab n :=
  [fun t : (seq (seq T)) => filter (fun r => r != [::])
                                   [seq [seq x <- i | geqX T n x] | i <- t]].

Lemma to_word_filter_nnil t : to_word (filter (fun r => r != [::]) t) = to_word t.
Proof.
  rewrite /to_word; elim: t => [//= | t0 t IHt] /=.
  rewrite !rev_cons !flatten_rcons -IHt.
  case: (altP (t0 =P [::])) => [-> | _] /=; first by rewrite cats0.
  by rewrite rev_cons flatten_rcons.
Qed.

Lemma filter_to_word t p : filter p (to_word t) = to_word (map (filter p) t).
Proof.
    rewrite /to_word; elim: t => [//= | t0 t IHt] /=.
    by rewrite !rev_cons !flatten_rcons -IHt filter_cat.
Qed.

Lemma head_filter_geqX_tab n t :
  is_tableau t ->
  head [::] (filter_geqX_tab n t) = [seq x <- head [::] t | (x <= n)%Ord].
Proof.
  elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil0 Hrow0 Hdom Htab.
  case: (altP ([seq x <- t0 | (x <= n)%Ord] =P [::])) => Ht0 //=.
  rewrite (IHt Htab) Ht0 {IHt}.
  case: t Hdom Htab => [//= | t1 t] /= Hdom /and3P [] Hnnil1 Hrow1 _.
  have /dominateP := filter_geqX_dominate n Hrow0 Hrow1 Hdom => [] [].
  by rewrite Ht0 /= leqn0 => /nilP ->.
Qed.

Lemma is_tableau_filter_geqX t n : is_tableau t -> is_tableau (filter_geqX_tab n t).
Proof.
  elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil Hrow Hdom Htab.
  case: (altP ([seq x <- t0 | (x <= n)%Ord] =P [::])) => Ht0 /=; first by apply IHt.
  rewrite Ht0 /=; apply/and3P; split; last by apply IHt.
  - apply sorted_filter; last exact Hrow.
    move=> a b c; by apply leqX_trans.
  - rewrite (head_filter_geqX_tab _ Htab).
    apply filter_geqX_dominate => //=.
    move: Htab; by case t => [//= | t1 t'] /= /and3P [].
Qed.
*)

End FilterLeqGeq.

Lemma eq_inv_is_row (T1 T2 : ordType) (u1 : seq T1) (u2 : seq T2) :
  eq_inv u1 u2 -> is_row u1 -> is_row u2.
Proof.
  move/eq_invP => [] Hsz.
  set Z1 := inhabitant T1; set Z2 := inhabitant T2 => Hinv /(is_rowP Z1) Hrow.
  apply/(is_rowP Z2) => i j; rewrite -Hsz => Hij.
  rewrite -(Hinv i j Hij).
  by apply Hrow.
Qed.

Lemma is_row_stdE (T : ordType) (w : seq T) : is_row (std w) = is_row w.
Proof.
  apply/(sameP idP); apply(iffP idP);
    apply eq_inv_is_row; last apply eq_inv_sym; by apply eq_inv_std.
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

Lemma eq_inv_is_skew_tableau_reshape_size inner outer
      (T1 T2 : ordType) (u1 : seq T1) (u2 : seq T2) :
  size inner = size outer -> (* complete with 0 if needed *)
  eq_inv u1 u2 -> size u1 = sumn (diff_shape inner outer) ->
  is_skew_tableau inner (skew_reshape inner outer u1) ->
  is_skew_tableau inner (skew_reshape inner outer u2).
Proof.
  rewrite /skew_reshape.
  elim: inner outer u1 u2 => [| inn0 inn IHinn] /=; first by case.
  case => [//= | out0 out] /= u1 u2 /eqP.
  set szres := (sumn (diff_shape inn out)).
  rewrite eqSS => /eqP Hsz Hinv Hszeq /=.
  have Hszres : szres <= size u1.
    rewrite Hszeq; apply leq_addl.
  have Hbad : (if szres < size u1 then szres else size u1) = szres.
    move: Hszres; rewrite leq_eqVlt => /orP [/eqP ->| -> //=]; by rewrite ltnn.
  have := Hinv => /eq_invP [] Hszu _.
  set r1 := take szres u1; set r2 := take szres u2.
  have Hinvr : eq_inv r1 r2.
    apply (eq_inv_catl (v1 := drop szres u1)
                       (v2 := drop szres u2) );
        last by rewrite !size_take -Hszu.
    by rewrite !cat_take_drop.
  have Hszr1 : size r1 = szres by rewrite size_take Hbad.
  have {IHinn Hszr1} IH := IHinn _ r1 r2 Hsz Hinvr Hszr1.
  rewrite !rev_cons !reshape_rcons; first last.
    by rewrite sumn_rev addnC Hszeq.
    by rewrite -Hszu sumn_rev addnC Hszeq.
  rewrite sumn_rev -/szres.
  rewrite !rev_rcons /= !size_drop.
  move/and4P => [] Hnnil /= Hrow Hdom /IH -> {IH}.
  have Heqdrop : eq_inv (drop szres u1) (drop szres u2).
    apply (eq_inv_catr (u1 := take szres u1)
                       (u2 := take szres u2) );
        last by rewrite !size_take -Hszu.
    by rewrite !cat_take_drop.
  rewrite -Hszu Hnnil andbT /=; apply/andP; split.
  - move: Hrow; by apply eq_inv_is_row.
  - move: Hdom; case/lastP Hd : (rev (diff_shape inn out)) => [//= | d dl] /=.
    have Htmp : sumn d + dl = (if szres < size u1 then szres else size u1).
      rewrite Hbad /szres -(sumn_rev (diff_shape _ _)) Hd.
      by rewrite -(sumn_rev (rcons _ _)) rev_rcons /= sumn_rev addnC.
    rewrite reshape_rcons; last by rewrite size_take.
    rewrite reshape_rcons; last by rewrite size_take -Hszu.
    rewrite !rev_rcons /=.
    apply: eq_inv_skew_dominate; last by rewrite !size_drop !size_take Hszu.
    have Hsum : (sumn d) <= szres by move: Htmp; rewrite Hbad => <-; apply leq_addr.
    have HH u : szres <= size u ->
                (drop (sumn d) (take szres u) ++ drop szres u) = drop (sumn d) u.
      move=> Hu; have := erefl (drop (sumn d) u).
      rewrite -{1}(cat_take_drop szres u) drop_cat size_take (bad_if_leq Hu).
      move: Hsum; rewrite leq_eqVlt => /orP [/eqP -> _| -> //=].
      rewrite drop_oversize; first by rewrite cat0s.
      by rewrite size_take (bad_if_leq Hu).
    rewrite (HH _ _ Hszres); have := Hszres; rewrite Hszu => /HH ->.
    apply (eq_inv_catr (u1 := take (sumn d) u1)
                       (u2 := take (sumn d) u2) );
      last by rewrite !size_take -Hszu.
    by rewrite !cat_take_drop.
Qed.

Theorem eq_inv_is_skew_tableau_reshape inner outer
      (T1 T2 : ordType) (u1 : seq T1) (u2 : seq T2) :
  size inner <= size outer ->
  eq_inv u1 u2 -> size u1 = sumn (diff_shape inner outer) ->
  is_skew_tableau inner (skew_reshape inner outer u1) ->
  is_skew_tableau inner (skew_reshape inner outer u2).
Proof.
  move=> Hleq Hinv Hsz.
  have H u : is_skew_tableau inner (skew_reshape inner outer u) =
             is_skew_tableau ((pad0 (size outer)) inner)
                             (skew_reshape ((pad0 (size outer)) inner) outer u).
    rewrite is_skew_tableau_pad0 {1}/skew_reshape
            size_rev size_reshape size_rev size_diff_shape.
    congr (is_skew_tableau _ _).
    by rewrite /skew_reshape diff_shape_pad0.
  rewrite (H _ u1) (H _ u2) {H}.
  apply eq_inv_is_skew_tableau_reshape_size.
  - elim: outer inner Hleq {Hsz} => [//= | out0 out IHout] [| inn0 inn] //=.
    + by rewrite size_nseq.
    + by rewrite ltnS subSS => /IHout /= ->.
  - exact Hinv.
  - by rewrite diff_shape_pad0.
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

Definition LRyam_list (P1 P2 P : seq nat) :=
  (filter
     ((is_skew_tableau P1) \o (skew_reshape P1 P))
     (list_yamsh P2)).
Definition LRyam_compute (P1 P2 P : seq nat) := size (LRyam_list P1 P2 P).

(*
Lemma is_std_hyper_stdtab d (P : intpartn d) :
  is_std_of_n d (to_word (hyper_stdtab P)).
Proof.
  have := hyper_stdtabP P.
  rewrite /is_std_of_n /= /is_stdtab => /andP [] /andP [] _ -> /=.
  by rewrite size_to_word.
Qed.
*)

Section LR.

Variables d1 d2 : nat.
Variables (P1 : intpartn d1) (P2 : intpartn d2) (P : intpartn (d1 + d2)).

Definition LRyam_set :=
  [set s : yamsh_finType (intpartnP P2) | is_skew_tableau P1 (skew_reshape P1 P s)].

Definition LRyam_coeff := #|LRyam_set|.

Lemma LR_coeff_computeP : LRyam_compute P1 P2 P = LRyam_coeff.
Proof.
  rewrite /LRyam_coeff /LRyam_set /LRyam_compute /LRyam_list.
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

Lemma size_hyper_yam sh : size (hyper_yam sh) = sumn sh.
Proof.
  elim/last_ind: sh => [//= | sh sn] /=.
  rewrite /hyper_yam -(sumn_rev (rcons _ _)) rev_rcons /= size_cat => ->.
  by rewrite size_nseq sumn_rev.
Qed.

Lemma sfilterleq_LR_supportP Q :
  Q \in LR_support (hyper_stdtab P1) (hyper_stdtab P2) ->
        is_std_of_n d2 (sfilterleq d1 (to_word Q)).
Proof.
  have := stdtabnP (hyper_stdtab P2); rewrite /is_stdtab => /andP [] Htab2 Hstd2.
  have /allP /= Hall := RSclassP Htab2.
  rewrite inE /= => /hasP [] p2 /Hall{Hall} /Sch_plact Hpl.
  have := hyper_stdtabP P1 => /=; rewrite /is_stdtab => /andP [] /andP [] _ Hstd /= /eqP Hsz.
  move/(shsh_sfilterleq Hstd).
  rewrite -size_to_word Hsz /= {Hstd Hsz} => <-.
  apply/andP; split.
  - apply: (perm_eq_std (std_is_std (hyper_yam P2))).
    by apply: plactcongr_homog.
  - rewrite (size_plactcongr Hpl) size_std.
    by rewrite size_hyper_yam intpartn_sumn.
Qed.
Definition wordLRtab Q (H : Q \in LR_support (hyper_stdtab P1) (hyper_stdtab P2)) :=
  StdWordN (sfilterleq_LR_supportP H).

(*
Lemma sfilterleq_LR_support_skew Q :
  Q \in LR_support (hyper_stdtab P1) (hyper_stdtab P2) ->
        is_skew_tableau P1 (skew_reshape P1 P (sfilterleq d1 (to_word Q))).
Proof.
  have := stdtabnP (hyper_stdtab P2); rewrite /is_stdtab => /andP [] Htab2 Hstd2.
  have /allP /= Hall := RSclassP Htab2.
  rewrite inE /= => /hasP [] p2 /Hall{Hall} /Sch_plact Hpl Hshsh.
  have := hyper_stdtabP P1 => /=; rewrite /is_stdtab => /andP [] /andP [] _ Hstd /= /eqP Hsz.
  have := (shsh_sfilterleq Hstd Hshsh).
  have := (shsh_sfiltergtn Hstd Hshsh).
  rewrite -size_to_word Hsz /= {Hstd Hsz}.
  apply/andP; split.
  - apply: (perm_eq_std (std_is_std (hyper_yam P2))).
    by apply: plactcongr_homog.
  - rewrite (size_plactcongr Hpl) size_std.
    by rewrite size_hyper_yam intpartn_sumn.
*)
Lemma std_LRyam_setP (y : yamsh_finType (intpartnP P2)) : is_std_of_n d2 (std y).
Proof.
  rewrite inE std_is_std /= size_std -shape_rowseq_eq_size.
  by rewrite shape_yamsh intpartn_sumn.
Qed.
Definition wordLRyam (y : yamsh_finType (intpartnP P2)) := StdWordN (std_LRyam_setP y).


(*
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
  have: w =Pl p2.
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

End LR.


