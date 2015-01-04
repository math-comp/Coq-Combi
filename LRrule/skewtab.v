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

Require Import partition schensted ordtype std stdtab invseq congr plactic greeninv yamplact.
Require Import shuffle multpoly.

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

  Lemma size_included inner outer : included inner outer -> size inner <= size outer.
  Proof.
    elim: inner outer => [//= | inn0 inn IHinn] /=.
    case=> [//= | outer0 outer] /= /andP [] _ /IHinn.
    by rewrite ltnS.
  Qed.

  Fixpoint diff_shape inner outer :=
    if inner is inn0 :: inn then
      if outer is out0 :: out then
        out0 - inn0 :: diff_shape inn out
      else [::] (* Wrong case *)
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

  Lemma is_skew_tableau_pad0 inner t :
    is_skew_tableau inner t = is_skew_tableau (pad 0 (size t) inner) t.
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

Lemma to_word_map_shiftn sh t : to_word (map (shiftn sh) t) = shiftn sh (to_word t).
Proof.
  rewrite /to_word /shiftn.
  elim: t => [//= | t0 t IHt] /=.
  by rewrite !rev_cons !flatten_rcons IHt map_cat.
Qed.

Lemma shiftn_skew_dominate n sh u v :
  skew_dominate sh u v -> skew_dominate sh (shiftn n u) (shiftn n v).
Proof.
  rewrite /skew_dominate !size_map => /andP [] Hsz.
  rewrite Hsz /=.
  set p1 := (X in all X) => H.
  set p2 := (X in all X).
  rewrite (eq_in_all (a2 := p1)) //=.
  move => i /=; rewrite mem_iota => /andP [] Hi1.
  case (leqP sh (size u)) => Hu.
  + rewrite (subnKC Hu) => Hi2.
    rewrite /p1 /p2 {p1 p2 H} /shiftn.
    rewrite !ltnXnatE.
    rewrite (nth_map (inhabitant nat_ordType)); first last.
      rewrite -(ltn_add2l sh) (subnKC Hi1) addnC.
      by apply (leq_trans Hi2).
    rewrite (nth_map (inhabitant nat_ordType)); last exact Hi2.
    by rewrite ltn_add2l.
  + move=> Hi2; exfalso.
    have := (ltnW Hu); rewrite /leq => /eqP Hleq.
    move: Hi2; by rewrite Hleq addn0 ltnNge Hi1.
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
      rewrite /p1 /p2; move=> i /=; by apply ltnXNgeqX.
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

Lemma join_stdtab s t :
  is_stdtab s -> is_skew_tableau (shape s) t ->
  is_tableau (join_tab s (map (shiftn (size_tab s)) t)).
Proof.
  rewrite /join_tab /is_stdtab => /andP [].
  rewrite /is_std -size_to_word /= => Htabs Hperm.
  have {Hperm} : all (gtn (size_tab s)) (to_word s).
    apply/allP => i; rewrite (perm_eq_mem Hperm).
    by rewrite mem_iota /= add0n.
  move: (size_tab s) => sh.
  rewrite /to_word.
  elim: s t Htabs => [| s0 s IHs] /= t.
    move => _ _ Ht; rewrite subn0.
    set t' := map _ _.
    have {t'} -> : t' = map (shiftn sh) t.
      by rewrite /t'; elim: t {Ht t'} => //= r t ->.
    rewrite -is_skew_tableau0.
    by apply is_skew_tableau_map_shiftn.
  move/and4P => [] Hnnils0 Hrows0 Hdoms Htabs.
  rewrite rev_cons flatten_rcons all_cat => /andP [] Halls Halls0.
  case: t => [//= | t0 t] /= /and4P [] Hszt0 Hrowt0 Hdomt Htabt.
  apply/and4P; rewrite subSS; split.
  - move: Hnnils0; apply contra; by case s0.
  - case: s0 Hnnils0 Hrows0 Halls0 {s t Hdoms Hszt0 Hdomt IHs Htabs Htabt Halls}
          => [//= | l0 s0] /= _ Hpath /andP [] Hl0 Halls0.
    rewrite cat_path Hpath {Hpath} /=.
    case: t0 Hrowt0 => [//= | m0 t0] /= Hpath.
    apply/andP; split.
    + rewrite leqXnatE; case/lastP: s0 Halls0 => [_ | s0 sn] /=.
      * apply ltnW; apply (leq_trans Hl0); by apply leq_addr.
      * rewrite all_rcons last_rcons /= => /andP [] Hsn _.
        apply ltnW; apply (leq_trans Hsn); by apply leq_addr.
    + rewrite (map_path (e' := leqX_op) (b := pred0)).
      * exact Hpath.
      * move=> i j /= _; by rewrite !leqXnatE leq_add2l.
      * by apply/hasPn => i.
  - rewrite size_map {IHs Hrows0 Hrowt0 Hnnils0 Hszt0} /=.
    case: s Hdoms Htabs Halls Hdomt Htabt => [//= _ _ _| s1 s] /=.
    + rewrite subn0.
      case: t => [//= | t1 t] /= /skew_dominateP [] Hszt Hdomt _.
      apply/dominateP; split; first by rewrite size_cat !size_map addnC.
      move: Hdomt; set Z := (inhabitant nat_ordType) => Hdomt.
      rewrite size_map => i Hi.
      rewrite nth_cat; case ltnP => His0.
      * move: Halls0 => /allP Halls0.
        have {Halls0} /Halls0 /= Hnth := mem_nth Z His0.
        rewrite ltnXnatE; apply (leq_trans Hnth).
        rewrite (nth_map Z _ _ Hi).
        by apply leq_addr.
      * rewrite (nth_map Z _ _ Hi).
        rewrite (nth_map Z); first last.
          rewrite -(ltn_add2l (size s0)) (subnKC His0) addnC.
          by apply (leq_trans Hi).
        rewrite ltnXnatE ltn_add2l -ltnXnatE.
        by apply Hdomt; rewrite His0 Hi.
    + case: t => [//= | t1 t] /= /dominateP [] Hszs Hdoms _.
      rewrite rev_cons flatten_rcons all_cat => /andP [] _ Halls1.
      move/skew_dominateP => [] Hszt Hdomt _  {s t}.
      have {Hszt} Hszt : size s1 + size t1 <= size s0 + size t0.
        by rewrite -(subnKC Hszs) -addnA leq_add2l addnC.
      apply/dominateP; split; first by rewrite !size_cat !size_map.
      move: Hdoms Hdomt; set Z := (inhabitant nat_ordType) => Hdoms Hdomt.
      rewrite size_cat size_map => i Hi.
      rewrite !nth_cat.
      case: (ltnP i (size s1)) => Hi1; first by rewrite (leq_trans Hi1 Hszs); apply Hdoms.
      case: (ltnP i (size s0)) => Hi0.
      * move: Halls0 => /allP Halls0.
        have {Halls0} /Halls0 /= Hnth := mem_nth Z Hi0.
        rewrite ltnXnatE; apply (leq_trans Hnth).
        rewrite (nth_map Z); first by apply leq_addr.
        by rewrite -(subSn Hi1) leq_subLR.
      * rewrite (nth_map Z); first last.
          rewrite -(ltn_add2l (size s0)) (subnKC Hi0).
          by apply (leq_trans Hi).
        rewrite (nth_map Z); first last.
          by rewrite -(ltn_add2l (size s1)) (subnKC Hi1).
        rewrite ltnXnatE ltn_add2l -ltnXnatE.
        rewrite -{1}(subnKC Hi1) addnC -(subnBA _ Hszs).
        apply Hdomt; apply/andP; split; first by apply leq_sub2r.
        by rewrite -(subSn Hi1) leq_subLR.
  - by apply IHs.
Qed.

Lemma filter_leq_shiftn sh t : [seq x - sh | x <- [seq sh + i | i <- t] & sh <= x] = t.
Proof. elim: t => [//= | l0 r IHt] /=; by rewrite leq_addr /= addKn IHt. Qed.

Lemma filter_gtn_shiftn sh t : [seq x <- [seq sh + i | i <- t] | gtn sh x] = [::].
Proof. elim: t => [//= | l0 r /= ->] /=; by rewrite ltnNge leq_addr. Qed.

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
  rewrite /to_word /shiftn => Hall; apply /andP; split; apply/eqP.
  - elim: s t Hsize Hall => [| s0 s IHs] /= t.
    + rewrite subn0 size_map => _ _.
      set t' := map _ _.
      have {t'} -> : t' = map (shiftn sh) t.
        by rewrite /t'; elim: t {t'} => //= r t ->.
      elim: t => [//= | t0 t IHt] /=.
      rewrite rev_cons flatten_rcons filter_cat IHt cat0s {t IHt}.
      by rewrite filter_gtn_shiftn.
    + case: t => [//= | t0 t] /=.
      rewrite ltnS rev_cons flatten_rcons all_cat => /IHs{IHs}Hrec /andP [] /Hrec{Hrec} Hrec.
      rewrite rev_cons flatten_rcons !filter_cat subSS Hrec {Hrec} => /all_filterP ->.
      suff -> : [seq x <- [seq sh + i | i <- t0] | gtn sh x] = [::] by rewrite cats0.
      by rewrite filter_gtn_shiftn.
  - rewrite /shiftninv; elim: s t Hsize Hall => [| s0 s IHs] /= t.
    + rewrite subn0 size_map => _ _.
      elim: t => [//= | t0 t IHt] /=.
      rewrite !rev_cons !flatten_rcons !filter_cat map_cat IHt {IHt}.
      by rewrite filter_leq_shiftn.
    + case: t => [//= | t0 t] /=.
      rewrite ltnS rev_cons flatten_rcons all_cat => /IHs{IHs}Hrec /andP [] /Hrec{Hrec} Hrec.
      rewrite !rev_cons !flatten_rcons !filter_cat !map_cat subSS Hrec {Hrec}.
      rewrite filter_leq_shiftn => Hall. (* => /all_filterP Hall. *)
      suff -> : [seq x - sh | x <- s0 & sh <= x] = [::] by rewrite cat0s.
      elim: s0 Hall {t s t0} => [//= | l0 s IHs] /= /andP [] H /IHs.
      by rewrite leqNgt H.
Qed.



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

End EqInvSkewTab.

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

    - apply IHt.
    rewrite drop_cat.

    case: outer => [//= | out0 out] /=.
    rewrite rev_cons /= !reshape_rcons. rev_rcons.
*)


Section LR.

Variables d1 d2 : nat.
Variables (P1 : intpartn d1) (P2 : intpartn d2).

Lemma size_tab_P1 : d1 = size_tab (RS (std (hyper_yam P1))).
Proof. by rewrite size_RS size_std size_hyper_yam intpartn_sumn. Qed.

Lemma sfilterleq_LR_supportP Q :
  Q \in LR_support (hyper_stdtab P1) (hyper_stdtab P2) ->
  exists y, is_yam_of_shape P2 y /\ std y = (sfilterleq d1 (to_word Q)).
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
    move/(plact_from_yam (intpartnP P2)) => [] yam Hyam; by exists yam.
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
  rewrite /to_word.
  elim: t => [//= | t0 t IHt] /=.
  rewrite rev_cons flatten_rcons filter_cat /=.
  case: (altP (filter (gtnX n) t0 =P [::])) => H /=.
  - by rewrite H cats0 IHt.
  - by rewrite rev_cons flatten_rcons IHt.
Qed.

Lemma filter_leqX_to_word (T : ordType) n (t : seq (seq T)) :
  filter (leqX n) (to_word t) = to_word (filter_leqX_tab n t).
Proof.
  rewrite /to_word.
  elim: t => [//= | t0 t IHt] /=.
  rewrite rev_cons flatten_rcons filter_cat /=.
  case: (altP (filter (leqX n) t0 =P [::])) => H /=.
  - by rewrite H cats0 IHt rev_cons flatten_rcons cats0.
  - by rewrite rev_cons flatten_rcons IHt.
Qed.

Section OneCoeff.

Variable P : intpartn (d1 + d2).

Definition LRyam_set :=
  [set x : yamsh_finType (intpartnP P2) | is_skew_tableau P1 (skew_reshape P1 P x)].
Definition LRyam_coeff := #|LRyam_set|.

Hypothesis Hincl : included P1 P.

Lemma size_leq_skew_reshape (y : seq nat) :
  size (RS (std (hyper_yam P1))) <= size (skew_reshape P1 P y).
Proof.
  rewrite -(size_map size) -/(shape (RS _)) shape_RS_std.
  rewrite shape_RS_yam; last by apply hyper_yamP; apply intpartnP.
  rewrite (shape_rowseq_hyper_yam (intpartnP P1)).
  rewrite size_skew_reshape; by apply size_included.
Qed.

Definition bijLRyam :=
  [fun y : seq nat =>
     join_tab (hyper_stdtab P1) (map (shiftn d1) (skew_reshape P1 P (std y)))].

Lemma predLRTripleFast_bijLRyam (yam : yamsh P2) :
  is_skew_tableau P1 (skew_reshape P1 P yam) ->
  predLRTripleFast (hyper_stdtab P1) (hyper_stdtab P2) (bijLRyam yam).
Proof.
  case: yam => y Hyam /= Hskew.
  apply/hasP; exists (std y).
    rewrite RSclassE; last by apply is_tableau_RS.
    rewrite -plactic_RS.
    apply std_plact.
    move: Hyam; rewrite /is_yam_of_shape => /andP [] Hyam /eqP <-.
    by apply yam_plactic_hyper.
  have Hstd1 : is_std (to_word (RS (std (hyper_yam P1)))).
    have /= := hyper_stdtabP P1 => /andP [].
    by rewrite /is_stdtab => /andP [].
  rewrite {2}size_tab_P1.
  rewrite -{2}[std y](to_word_skew_reshape Hincl); first last.
    rewrite size_std sumn_diff_shape; last by apply Hincl.
    rewrite !intpartn_sumn addKn -shape_rowseq_eq_size.
    move: Hyam; rewrite /is_yam_of_shape => /andP [] _ /eqP ->.
    by rewrite intpartn_sumn.
  apply join_stdtab_in_shuffle.
  - rewrite RSstdE; by apply std_is_std.
  - by apply size_leq_skew_reshape.
Qed.

Lemma bijLRyamP (yam : yamsh P2) :
  is_skew_tableau P1 (skew_reshape P1 P yam) ->
  is_stdtab_of_n (d1 + d2) (bijLRyam yam).
Proof.
  case Hy: yam => [y Hyam] Hskew /=.
  rewrite /is_stdtab.
  have Hszy : size y = d2.
    rewrite -shape_rowseq_eq_size.
    have:= Hyam; rewrite /is_yam_of_shape => /andP [] _ /eqP ->.
    by rewrite intpartn_sumn.
  set sz := size_tab _.
  have {sz} -> : sz = d1 + d2.
    rewrite /sz{sz}  size_join_tab.
    + rewrite size_RS size_std size_hyper_yam intpartn_sumn; congr (_ + _).
      rewrite /size_tab /shape -map_comp.
      have /eq_map -> : (size \o shiftn d1) =1 size by move=> s /=; rewrite size_map.
      rewrite -/(shape _) (shape_skew_reshape Hincl).
      * by rewrite (sumn_diff_shape Hincl) !intpartn_sumn addKn.
      * by rewrite size_std (sumn_diff_shape Hincl) !intpartn_sumn addKn.
    + rewrite size_map; by apply size_leq_skew_reshape.
  rewrite eq_refl andbT.
  apply/andP; split.
  - rewrite {2}size_tab_P1.
    apply join_stdtab.
    rewrite RSstdE; by apply std_is_std.
  - rewrite shape_RS_std shape_RS_yam; last by apply hyper_yamP; apply intpartnP.
    rewrite (shape_rowseq_hyper_yam (intpartnP P1)).
    apply (eq_inv_is_skew_tableau_reshape (u1 := y)).
    + by apply size_included.
    + by apply eq_inv_std.
    + by rewrite Hszy (sumn_diff_shape Hincl) !intpartn_sumn addKn.
    + exact Hskew.
  - have /= /hasP [] := predLRTripleFast_bijLRyam Hskew => z.
    set image := to_word _.
    rewrite (RSclassE _ (is_tableau_RS _)) -plactic_RS => /plactcongr_homog Hz.
    have {Hz} Hz : is_std z by apply: (perm_eq_std _ Hz); apply std_is_std.
    have : is_stdtab (RS (std (hyper_yam P1))) by rewrite RSstdE; apply std_is_std.
    rewrite /is_stdtab => /andP [] _ Hstd1.
    by apply (allP (std_shsh Hstd1 Hz)).
Qed.

Definition bijLR (yam : yamsh P2) : stdtabn (d1 + d2) :=
  if (boolP (is_skew_tableau P1 (skew_reshape P1 P yam))) is AltTrue pf then
    StdtabN (bijLRyamP pf)
  else
    hyper_stdtab P.

Lemma bijLR_LR_support yam :
  yam \in LRyam_set ->
  bijLR yam \in LR_support (hyper_stdtab P1) (hyper_stdtab P2).
Proof.
  rewrite !inE /bijLR => Hskew.
  case (boolP (is_skew_tableau P1 (skew_reshape P1 P yam))) => /=; last by rewrite Hskew.
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
  rewrite !inE /bijLR => Hskew.
  case (boolP (is_skew_tableau P1 (skew_reshape P1 P yam))) => [_|] /=; last by rewrite Hskew.
  rewrite /shape /join_tab.
  rewrite !size_map -map_comp.
  set f := (X in map X); have {f} /eq_map -> : f =1 fun p => size p.1 + size p.2.
    rewrite /f {f} => i /=; by rewrite size_cat.
  rewrite size_zip2 size_skew_reshape.
  set t := map size _; have {t} -> : t = pad 0 (size P) P1.
    rewrite /t{t} /pad /= map_cat.
    rewrite -(size_map size) -/(shape (RS _)) shape_RS_std.
    rewrite shape_RS_yam; last by apply hyper_yamP; apply intpartnP.
    rewrite (shape_rowseq_hyper_yam (intpartnP P1)).
    by rewrite map_nseq.
  set t := map size _; have {t} -> : t = diff_shape P1 P.
    rewrite /t{t} /= -map_comp.
    have /eq_map -> : size \o shiftn d1 =1 size by move=> i /=; rewrite size_map.
    rewrite -/(shape _) shape_skew_reshape //=.
    rewrite size_std sumn_diff_shape; last by apply Hincl.
    rewrite !intpartn_sumn addKn -shape_rowseq_eq_size.
    by rewrite shape_yamsh intpartn_sumn.
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
  Q \in LRtab_set P1 P2 P ->
  is_skew_tableau P1 (skew_reshape P1 P (sfilterleq d1 (to_word Q))).
Proof.
  have := stdtabnP (hyper_stdtab P2); rewrite /is_stdtab => /andP [] Htab2 Hstd2.
  have /allP /= Hall := RSclassP Htab2.
  move=> HLRtab; have := HLRtab; rewrite /LRtab_set inE => /andP [] HLR /eqP Hshape.
  have Hfilter := filtergtn_LR_support HLR.
  have:= HLR; rewrite inE /= => /hasP [] p2 /Hall{Hall} /Sch_plact Hpl Hshsh.
  have := hyper_stdtabP P1 => /=; rewrite /is_stdtab => /andP [] /andP [] _ Hstd /= /eqP Hsz.
  have := (shsh_sfilterleq Hstd Hshsh).
  rewrite -size_to_word Hsz /= {Hstd Hsz} => (* H1 *) Hp2; subst p2.
  apply (eq_inv_is_skew_tableau_reshape (u1 := [seq x <- to_word Q | d1 <= x])).
  - by apply size_included.
  - apply/eq_invP; split; first by rewrite size_map.
    move=> i j /andP [] Hij Hj.
    set Z := (inhabitant nat_ordType).
    rewrite (nth_map Z); last by apply (leq_ltn_trans Hij Hj).
    rewrite (nth_map Z); last by apply Hj.
    rewrite !leqXnatE leq_subLR subnKC //=.
    have:= mem_nth Z Hj; by rewrite mem_filter => /andP [].
  - move: Hpl => /plactcongr_homog/perm_eq_size.
    rewrite size_map => ->.
    rewrite size_std (sumn_diff_shape Hincl) !intpartn_sumn addKn.
    by rewrite -shape_rowseq_eq_size (shape_rowseq_hyper_yam (intpartnP P2)) intpartn_sumn.
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
  have:= HLR => /sfilterleq_LR_supportP [] y [] Hy Hmap.
  have Hskew : is_skew_tableau P1 (skew_reshape P1 P y).
    apply (eq_inv_is_skew_tableau_reshape (u1 := std y)).
    + by apply size_included.
    + apply eq_inv_sym; by apply eq_inv_std.
    + rewrite size_std (sumn_diff_shape Hincl) !intpartn_sumn addKn.
      rewrite -shape_rowseq_eq_size.
      have:= Hy; rewrite /is_yam_of_shape => /andP [] _ /eqP ->.
      by rewrite intpartn_sumn.
    + rewrite Hmap; by apply sfilterleq_LR_support_skew.
  exists (YamSh Hy).
  - rewrite inE /=; exact Hskew.
  - rewrite /bijLR /=.
    case (boolP (is_skew_tableau P1 (skew_reshape P1 P y))) => /=; last by rewrite Hskew.
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
  case (boolP (is_skew_tableau P1 (skew_reshape P1 P x))) => /=; last by rewrite Hx.
  case (boolP (is_skew_tableau P1 (skew_reshape P1 P y))) => /=; last by rewrite Hy.
  move=> Hy1 Hx1 H.
  apply val_inj => /=.
  have:= erefl (to_word (StdtabN (bijLRyamP Hx1))); rewrite {2}H /= {H Hx1 Hy1 Hx Hy} => H.
  pose f := [fun s : seq nat =>
               to_word (join_tab (hyper_stdtab P1) (map (shiftn d1) (skew_reshape P1 P s)))].
  have {H} H : f (std x) = f (std y) by rewrite /= H.
  have invf s : size s = sumn (diff_shape P1 P) -> sfilterleq d1 (f s) = s.
    move => Hsize /=.
    have /= := join_stdtab_in_shuffle (stdtabnP (hyper_stdtab P1)) (size_leq_skew_reshape s).
    rewrite /size_tab.
    have := erefl (val P1); rewrite -{2}(shaped_hyper_stdtabP P1) /= => <-.
    rewrite intpartn_sumn.
    have := stdtabnP (hyper_stdtab P1); rewrite /is_stdtab => /andP [] _ /=.
    move /shsh_sfilterleq => HH/HH{HH}.
    rewrite -size_to_word -size_tab_P1 /sfilterleq /= => <-.
    rewrite to_word_skew_reshape //=.
  apply perm_eq_stdE.
  - by rewrite perm_eq_shape_rowseq !shape_yamsh.
  - have bla (z : yamsh_finType (intpartnP P2)) : size (std z) = sumn (diff_shape P1 P).
      rewrite size_std sumn_diff_shape; last by apply Hincl.
      rewrite -shape_rowseq_eq_size shape_yamsh.
      by rewrite !intpartn_sumn addKn.
    by rewrite -(invf _ (bla x)) -(invf _ (bla y)) H.
Qed.

Theorem LR_coeff_yamP : LRtab_coeff P1 P2 P = LRyam_coeff.
Proof.
  rewrite /LRtab_coeff /LRyam_coeff.
  suff -> : LRtab_set P1 P2 P = bijLR @: LRyam_set by apply card_in_imset; apply bijLR_inj.
  rewrite -setP => Q.
  apply/(sameP idP); apply(iffP idP).
  - move/imsetP => [] y Hy ->.
    rewrite /LRtab_set inE (bijLR_LR_support Hy) /=.
    by rewrite shape_bijLR.
  - move/bijLR_surj => [] y Hy <-.
    by apply mem_imset.
Qed.


Definition LRyam_list (P1 P2 P : seq nat) :=
  [seq x <- list_yamsh P2 | is_skew_tableau P1 (skew_reshape P1 P x)].
Definition LRyam_compute (P1 P2 P : seq nat) := size (LRyam_list P1 P2 P).

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


Require Import ssralg zmodp.

Local Open Scope ring_scope.
Import GRing.Theory.

Variable (n : nat) (R : comRingType).

Hypothesis Hpos : n != 0%N.

Notation Schur p := (Schur Hpos R p).

Theorem LRtab_coeffP :
  Schur P1 * Schur P2 =
  \sum_(P : intpartn (d1 + d2) | included P1 P) (Schur P) *+ LRyam_coeff P.
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



