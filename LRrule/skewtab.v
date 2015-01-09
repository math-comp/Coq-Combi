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

Require Import tools partition yama ordtype tableau std stdtab.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N.

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

Section SkewShape.

  Fixpoint included inner outer :=
    if inner is inn0 :: inn then
      if outer is out0 :: out then
        (inn0 <= out0) && (included inn out)
      else false
    else true.

  Lemma includedP inner outer :
    reflect (size inner <= size outer /\ forall i, nth 0 inner i <= nth 0 outer i)
            (included inner outer).
  Proof.
    apply (iffP idP).
    - elim: inner outer => [//= | inn0 inn IHinn] /=.
        move=> outer _; by split; last by move=> i; rewrite nth_nil.
      case=> [//= | out0 out] /= /andP [] H0 /IHinn{IHinn} [] Hsize H.
      split; first by rewrite ltnS.
      by case.
    - elim: inner outer => [//= | inn0 inn IHinn] /=.
      case=> [ [] //= | out0 out] [] /=.
      rewrite ltnS => Hsize H.
      apply/andP; split; first by apply (H 0).
      apply: IHinn; split; first exact Hsize.
      move=> i; by apply (H i.+1).
  Qed.

  Lemma included_incr_nth inner outer i :
    nth 0 inner i < nth 0 outer i ->
    included inner outer -> included (incr_nth inner i) outer.
  Proof.
    move=> Hnth /includedP [] Hsize Hincl.
    apply/includedP; split.
    - rewrite size_incr_nth; case ltnP => _; first exact Hsize.
      rewrite ltnNge; apply (introN idP) => Hout.
      move: Hnth; by rewrite (nth_default _ Hout).
    - move=> j; rewrite nth_incr_nth.
      case eqP => [<- | _].
      - by rewrite add1n.
      - by rewrite add0n.
  Qed.

  Lemma size_included inner outer : included inner outer -> size inner <= size outer.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] /=.
    case=> [//= | outer0 outer] /= /andP [] _ /IHinn.
    by rewrite ltnS.
  Qed.

  Lemma sumn_included inner outer : included inner outer -> sumn inner <= sumn outer.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] /=.
    case=> [//= | outer0 outer] /= /andP [] H0 /IHinn.
    by apply: leq_add.
  Qed.

  Lemma included_sumnE inner outer :
    is_part outer ->
    included inner outer ->
    sumn inner = sumn outer ->
    inner = outer.
  Proof.
    elim: inner outer => [| inn0 inn IHinn] /=.
      by move=> outer Houter _ /esym/(part0 Houter) ->.
    case=> [//= | outer0 out] /= /andP [] _ /IHinn{IHinn}Hrec /andP [] H0 Hincl Heq.
    have {H0} H0 : inn0 = outer0.
      apply anti_leq; rewrite H0 /=.
      have := leq_sub2l (inn0 + sumn inn) (sumn_included Hincl).
      by rewrite {1}Heq !addnK.
    move: Heq => /eqP; by rewrite H0 eqn_add2l => /eqP/(Hrec Hincl) ->.
  Qed.

  Fixpoint diff_shape inner outer :=
    if inner is inn0 :: inn then
      if outer is out0 :: out then
        out0 - inn0 :: diff_shape inn out
      else [::] (* Unused case *)
    else outer.

  Definition pad (T : Type) (x : T) sz := [fun s => s ++ nseq (sz - size s) x].

  Definition outer_shape inner size_seq :=
    [seq p.1 + p.2 | p <- zip (pad 0 (size (size_seq)) inner) size_seq].

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

  Lemma diff_shape_pad0 inner outer :
    diff_shape ((pad 0 (size outer)) inner) outer = diff_shape inner outer.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] //=.
      elim=> [//= | out0 out] /=; by rewrite !subn0 => ->.
    case=> [//= | out0 out] /=.
    by rewrite subSS IHinn.
  Qed.

  Lemma diff_shapeK inner outer :
    included inner outer ->
    outer_shape inner (diff_shape inner outer) = outer.
  Proof.
    rewrite /outer_shape.
    elim: inner outer => [//= | inn0 inn IHinn] /= outer.
      rewrite subn0 => _; elim: outer => [//= | out0 out /= ->].
      by rewrite add0n.
   case: outer => [//= | out0 out] /= /andP [] Hin /IHinn{IHinn} ->.
   by rewrite addnC subnK.
  Qed.

  Lemma outer_shapeK inner diff :
    size inner <= size diff ->
    diff_shape inner (outer_shape inner diff) = diff.
  Proof.
    rewrite /outer_shape.
    elim: inner diff => [//= | inn0 inn IHinn] /= diff.
      rewrite subn0 => _; elim: diff => [//= | d0 diff /= ->].
      by rewrite add0n.
    case: diff => [//=| t0 t] /=; rewrite ltnS subSS => /IHinn /= ->.
    by rewrite addKn.
  Qed.

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

End SkewShape.

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

  Lemma skew_dominate_take n sh u v :
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

  Lemma skew_dominate_no_overlap sh u v :
    size u <= sh -> skew_dominate sh u v.
  Proof.
    move => Hsize.
    apply/skew_dominateP; split.
    - apply (leq_trans Hsize); by apply leq_addl.
    - move=> i /andP [] H1 H2; exfalso.
      have := leq_trans H2 (leq_trans Hsize H1).
        by rewrite ltnn.
  Qed.

  Fixpoint is_skew_tableau inner t :=
    if t is t0 :: t'
    then [&& head 0 inner + size t0 != 0,
         is_row t0,
         skew_dominate ((head 0 inner) - (head 0 (behead inner)))
                       (head [::] t') t0 & is_skew_tableau (behead inner) t']
    else inner == [::].

  Lemma is_skew_tableau0 : is_skew_tableau [::] =1 (@is_tableau T).
  Proof.
    elim => [//=| t0 t IHt] /=.
    rewrite add0n subn0 skew_dominate0 IHt.
    by case t0.
  Qed.

  Lemma is_skew_tableau_pad0 inner t :
    is_skew_tableau inner t = is_skew_tableau (pad 0 (size t) inner) t.
  Proof.
    elim: t inner => [| t0 t IHt] /= inner; first by rewrite cats0.
    case: inner => [| inn0 inn] /=.
      rewrite (IHt [::]) /= add0n.
      by rewrite !subn0.
    rewrite (IHt inn) subSS /=.
    suff -> : head 0 (inn ++ nseq (size t - size inn) 0) = head 0 inn by [].
    case: inn => [| inn1 inn] //=.
    by case: (size t - 0).
  Qed.

  Definition skew_reshape (inner outer : seq nat) (s : seq T) :=
    rev (reshape (rev (diff_shape inner outer)) s).

  Lemma size_skew_reshape inner outer s :
    size (skew_reshape inner outer s) = size outer.
  Proof. by rewrite /skew_reshape size_rev size_reshape size_rev size_diff_shape. Qed.

  Lemma shape_skew_reshape inner outer s :
    included inner outer ->
    size s = sumn (diff_shape inner outer) ->
    shape (skew_reshape inner outer s) = diff_shape inner outer.
  Proof.
    rewrite /shape /skew_reshape.
    elim: inner outer s => [| inn0 inn IHinn] /= outer s.
      move=> _; elim: outer s => [s /eqP/nilP -> //= | out0 out IHout] /= s Hsz.
      rewrite rev_cons reshape_rcons; last by rewrite sumn_rev addnC -Hsz.
      rewrite rev_rcons /= IHout.
      - by rewrite size_drop sumn_rev Hsz addnK.
      - rewrite size_take bad_if_leq sumn_rev //=.
        rewrite Hsz; by apply leq_addl.
    case: outer s => [//= | out0 out] /= s /andP [] H0 Hincl Hsz.
    rewrite rev_cons reshape_rcons; last by rewrite sumn_rev addnC -Hsz.
    rewrite rev_rcons /= size_drop sumn_rev.
    rewrite (IHinn _ _ Hincl); first by rewrite Hsz addnK.
    rewrite size_take Hsz bad_if_leq //=.
    by apply leq_addl.
  Qed.

  Lemma to_word_skew_reshape inner outer s :
    included inner outer ->
    size s = sumn (diff_shape inner outer) ->
    to_word (skew_reshape inner outer s) = s.
  Proof.
    rewrite /skew_reshape /to_word revK.
    elim: inner outer s => [| inn0 inn IHinn] /= outer s.
      move=> _; elim: outer s => [s /eqP/nilP -> //= | out0 out IHout] /= s Hsz.
      rewrite rev_cons reshape_rcons; last by rewrite sumn_rev addnC -Hsz.
      rewrite flatten_rcons IHout; first by rewrite cat_take_drop.
      rewrite sumn_rev size_take bad_if_leq //= Hsz; by apply leq_addl.
    case: outer s => [//= | out0 out] /= s /andP [] H0 Hincl Hsz.
    rewrite rev_cons reshape_rcons; last by rewrite sumn_rev addnC -Hsz.
    rewrite flatten_rcons IHinn.
    - by rewrite cat_take_drop.
    - exact Hincl.
    - rewrite sumn_rev size_take bad_if_leq //= Hsz; by apply leq_addl.
  Qed.

  Lemma skew_reshapeK inner t :
    size inner <= size t ->
    skew_reshape inner (outer_shape inner (shape t)) (to_word t) = t.
  Proof.
    rewrite -(size_map size).
    move=> H; rewrite /skew_reshape (outer_shapeK H).
    by rewrite /to_word -shape_rev flattenK revK.
  Qed.

End Dominate.

Section FilterLeqGeq.

Variable T : ordType.
Notation Z := (inhabitant T).

Implicit Type l : T.
Implicit Type r w : seq T.
Implicit Type t : seq (seq T).

Lemma filter_leqX_row n r :
  is_row r -> filter (leqX n) r = drop (count (gtnX n) r) r.
Proof.
  elim: r => [//= | r0 r IHr] Hrow /=.
  case: (leqXP n r0) => Hr0.
  - rewrite add0n; have Hcount : count (gtnX n) r = 0.
      elim: r r0 Hr0 Hrow {IHr} => [//= | r1 r /= IHr] r0 Hr0 /andP [] Hr0r1 Hpath.
      have Hr1 := leqX_trans Hr0 Hr0r1.
      by rewrite ltnXNgeqX Hr1 (IHr r1 Hr1 Hpath).
    by rewrite Hcount (IHr (is_row_consK Hrow)) Hcount drop0.
  - by rewrite add1n (IHr (is_row_consK Hrow)).
Qed.

Lemma filter_leqX_dominate n r1 r0 :
    is_row r0 -> is_row r1 -> dominate r1 r0 ->
    skew_dominate ((count (gtnX n) r0) - (count (gtnX n) r1))
      (filter (leqX n) r1) (filter (leqX n) r0).
Proof.
  move=> Hrow0 Hrow1 Hdom.
  have Hsize := count_gtnX_dominate n Hdom.
  move: Hdom => /dominateP [] Hsz Hdom.
  have /eq_count Hcount : (gtnX n) =1 predC (leqX n).
    move=> i /=; by apply ltnXNgeqX.
  apply/skew_dominateP; rewrite !size_filter.
  split.
  - rewrite -(leq_add2r (count (gtnX n) r1)).
    rewrite -addnA (subnK Hsize).
    by rewrite !Hcount !count_predC.
  - move=> i /andP [] Himin Himax.
    rewrite (filter_leqX_row _ Hrow0) (filter_leqX_row _ Hrow1) !nth_drop.
    rewrite (addnBA _ Himin) -{1}(subnK Hsize) -addnA addKn.
    apply Hdom.
    by rewrite -(count_predC (leqX n) r1) Hcount addnC ltn_add2r.
Qed.

Definition filter_leqX_tab n :=
  [fun t : (seq (seq T)) => [seq [seq x <- i | leqX n x] | i <- t]].

Lemma is_skew_tableau_filter_leqX_tmp n t :
  is_tableau t -> is_skew_tableau
                    (shape ([seq [seq x <- i | (x < n)%Ord] | i <- t]))
                    (filter_leqX_tab n t).
Proof.
  elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil Hrow Hdom Htab.
  apply/and4P; split.
  - rewrite !size_filter /=.
    set p1 := (X in count X); set p2 := (X in _ + count X _).
    have /eq_count -> : p2 =1 predC p1.
      rewrite /p1 /p2; move=> i /=; by rewrite -leqXNgtnX.
    rewrite count_predC.
    move: Hnnil; by apply contra => /nilP ->.
  - apply sorted_filter; last exact Hrow.
    move=> a b c; by apply leqX_trans.
  - case: t Hdom Htab {IHt} => [//= | t1 t] /= Hdom /and4P [] _ Hrow1 _ _ {t}.
    rewrite !size_filter.
    by apply filter_leqX_dominate.
  - by apply IHt.
Qed.

Lemma filter_gtnX_first_row0 n r t :
  is_tableau t ->
  dominate (head [::] t) r ->
  [seq x <- r | (x < n)%Ord] = [::] ->
  [seq [seq x <- i | (n <= x)%Ord] | i <- t] = t.
Proof.
  elim: t r => [//= | t0 t IHt] /= r.
  move=> /and4P [] _ Hrow Hdom Htab Hdomr Hr.
  have:= count_gtnX_dominate n Hdomr.
  rewrite -!size_filter Hr /= leqn0 => /nilP Ht0.
  rewrite (IHt t0 Htab Hdom Ht0).
  rewrite (filter_leqX_row n Hrow).
  by rewrite -!size_filter Ht0 /= drop0.
Qed.

Lemma filter_leqX_first_row0 n r t :
  is_tableau t ->
  dominate (head [::] t) r ->
  [seq x <- r | (x < n)%Ord] = [::] ->
  [seq [seq x <- i | (x < n)%Ord] | i <- t] = nseq (size t) [::].
Proof.
  elim: t r => [//= | t0 t IHt] /= r.
  move=> /and4P [] _ Hrow Hdom Htab Hdomr Hr.
  have:= count_gtnX_dominate n Hdomr.
  rewrite -!size_filter Hr /= leqn0 => /nilP Ht0.
  by rewrite Ht0 (IHt t0 Htab Hdom).
Qed.

Lemma shape_inner_filter_leqX n t :
  is_tableau t ->
  shape ([seq [seq x <- i | (x < n)%Ord] | i <- t]) =
  pad 0 (size t) (shape (filter_gtnX_tab n t)).
Proof.
  rewrite /pad /=.
  elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil0 Hrow0 Hdom Htab.
  case: (altP ([seq x <- t0 | (x < n)%Ord] =P [::])) => Ht0 /=;
    last by rewrite subSS -(IHt Htab).
  rewrite Ht0 /= {IHt}.
  rewrite (filter_leqX_first_row0 Htab Hdom Ht0).
  set f := filter _ _; have -> : f = [::] by rewrite /f; by elim: (size t).
  by rewrite /= /shape map_nseq /=.
Qed.

Lemma is_skew_tableau_filter_leqX n t:
  is_tableau t -> is_skew_tableau (shape (filter_gtnX_tab n t)) (filter_leqX_tab n t).
Proof.
  move=> Htab.
  rewrite is_skew_tableau_pad0 /filter_leqX_tab size_map.
  rewrite -(shape_inner_filter_leqX n Htab).
  by apply is_skew_tableau_filter_leqX_tmp.
Qed.

Definition join_tab s t :=
  [seq r.1 ++ r.2 | r <- zip (pad [::] (size t) s) t].

Lemma size_join_tab s t :
  size s <= size t ->
  size_tab (join_tab s t) = size_tab s + size_tab t.
Proof.
  rewrite /join_tab /size_tab.
  elim: s t => [| s0 s IHs] /= t.
    by rewrite add0n subn0; elim: t => //= t0 t /= ->.
  case: t => [//= | t0 t] /=.
  rewrite ltnS subSS => /IHs -> {IHs}.
  rewrite size_cat -!addnA; congr (_ + _).
  by rewrite addnA addnAC addnC.
Qed.

Lemma perm_eq_join_tab s t :
  size s <= size t ->
  perm_eq (to_word (join_tab s t)) (to_word s ++ to_word t).
Proof.
  rewrite /join_tab /to_word /=.
  elim: t s => [//= | t0 t IHt] /= s; first by rewrite leqn0 => /nilP -> /=.
  case: s => [_ | s0 s] /=.
    rewrite !rev_cons !flatten_rcons {IHt}.
    set t' := map _ _; suff -> : t' = t by apply perm_eq_refl.
    rewrite /t' {t' t0}; by elim: t => //= t0 t /= -> .
  rewrite ltnS subSS => /IHt{IHt}.
  rewrite !rev_cons !flatten_rcons -!/(to_word _) !catA perm_cat2r.
  set m := map _ _.
  rewrite -(perm_cat2r s0) => /perm_eq_trans; apply.
  rewrite -!catA perm_cat2l.
  apply/perm_eqlP; by apply perm_catC.
Qed.

Lemma join_tab_filter n t :
  is_tableau t -> join_tab (filter_gtnX_tab n t) (filter_leqX_tab n t) = t.
Proof.
  rewrite /join_tab.
  elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil Hrow0 Hdom Htab.
  case H: [seq x <- t0 | (x < n)%Ord] => [//= | f0 f] /=.
  - rewrite (filter_leqX_first_row0 Htab Hdom H) {IHt}.
    have -> : [seq r <- nseq (size t) [::] | r != [::]] = [::] by elim: (size t).
    rewrite cat0s /=.
    rewrite (filter_leqX_row n Hrow0) -!size_filter /= H /= drop0.
    congr (_ :: _).
    rewrite (filter_gtnX_first_row0 Htab Hdom H).
    by elim: t {Hdom Htab H Hrow0 Hnnil} => [//= | t1 t /= ->].
  - rewrite (IHt Htab) (filter_leqX_row _ Hrow0).
    by rewrite -[f0 :: _ ++ _]cat1s catA cat1s -H (filter_gtnX_row _ Hrow0) cat_take_drop.
Qed.

End FilterLeqGeq.

Section EqInvSkewTab.

Implicit Type T : ordType.

Lemma eq_inv_is_row T1 T2 (u1 : seq T1) (u2 : seq T2) :
  eq_inv u1 u2 -> is_row u1 -> is_row u2.
Proof.
  move/eq_invP => [] Hsz.
  set Z1 := inhabitant T1; set Z2 := inhabitant T2 => Hinv /(is_rowP Z1) Hrow.
  apply/(is_rowP Z2) => i j; rewrite -Hsz => Hij.
  rewrite -(Hinv i j Hij).
  by apply Hrow.
Qed.

Lemma is_row_stdE T (w : seq T) : is_row (std w) = is_row w.
Proof.
  apply/(sameP idP); apply(iffP idP);
    apply eq_inv_is_row; last apply eq_inv_sym; by apply eq_inv_std.
Qed.

Lemma eq_inv_skew_dominate T1 T2 (u1 v1 : seq T1) (u2 v2 : seq T2) s :
  eq_inv (u1 ++ v1) (u2 ++ v2) ->
  size u1 = size u2 ->
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

Lemma eq_inv_is_skew_tableau_reshape_size inner outer T1 T2 (u1 : seq T1) (u2 : seq T2) :
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

Lemma is_skew_tableau_skew_reshape_pad0 inner outer T (u : seq T) :
  is_skew_tableau inner (skew_reshape inner outer u) =
  is_skew_tableau ((pad 0 (size outer)) inner)
                  (skew_reshape ((pad 0 (size outer)) inner) outer u).
Proof.
  rewrite is_skew_tableau_pad0 {1}/skew_reshape
          size_rev size_reshape size_rev size_diff_shape.
  congr (is_skew_tableau _ _).
  by rewrite /skew_reshape diff_shape_pad0.
Qed.

Theorem eq_inv_is_skew_tableau_reshape inner outer T1 T2 (u1 : seq T1) (u2 : seq T2) :
  size inner <= size outer ->
  eq_inv u1 u2 ->
  size u1 = sumn (diff_shape inner outer) ->
  is_skew_tableau inner (skew_reshape inner outer u1) ->
  is_skew_tableau inner (skew_reshape inner outer u2).
Proof.
  rewrite (is_skew_tableau_skew_reshape_pad0 _ _ u1).
  rewrite (is_skew_tableau_skew_reshape_pad0 _ _ u2).
  move=> Hleq Hinv Hsz.
  apply eq_inv_is_skew_tableau_reshape_size.
  - elim: outer inner Hleq {Hsz} => [//= | out0 out IHout] [| inn0 inn] //=.
    + by rewrite size_nseq.
    + by rewrite ltnS subSS => /IHout /= ->.
  - exact Hinv.
  - by rewrite diff_shape_pad0.
Qed.

Theorem is_skew_tableau_reshape_std inner outer T  (u : seq T) :
  size inner <= size outer ->
  size u = sumn (diff_shape inner outer) ->
  is_skew_tableau inner (skew_reshape inner outer u) =
  is_skew_tableau inner (skew_reshape inner outer (std u)).
Proof.
  move=> Hin Hsize.
  apply/(sameP idP); apply(iffP idP); apply eq_inv_is_skew_tableau_reshape => //=.
  - apply eq_inv_sym; by apply eq_inv_std.
  - by rewrite size_std.
  - by apply eq_inv_std.
Qed.

End EqInvSkewTab.



