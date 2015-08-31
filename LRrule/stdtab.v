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
Require Import finset perm fingroup.
Require Import tools combclass partition Yamanouchi permuted ordtype std tableau.

Import OrdNotations.

(* TODO : move in tools.v *)
Lemma nth_map_size (T : eqType) (s : seq (seq T)) i :
  nth 0 (shape s) i = size (nth [::] s i).
Proof.
  rewrite /shape; case: (ltnP i (size s)) => Hi; first exact: nth_map.
  by rewrite !nth_default // size_map.
Qed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(** Bijection between Yamanouchi words and standard tableau                   *)
(*                                                                            *)
(** is_stdtab t == t is a *standard tableau* that is a tableau whose
                                               row reading is a standard word *)
(*                                                                            *)
(** Main results:                                                             *)
(*                                                                            *)
(** Bijections : [stdtab_of_yam] and [yam_of_stdtab]

[Lemma   stdtab_of_yamP y : is_yam y    -> is_stdtab (stdtab_of_yam y).]

[Theorem stdtab_of_yamK y : is_yam y    -> yam_of_stdtab (stdtab_of_yam y) = y.]

[Lemma   yam_of_stdtabP t : is_stdtab t -> is_yam (yam_of_stdtab t).]

[Theorem yam_of_stdtabK t : is_stdtab t -> stdtab_of_yam (yam_of_stdtab t) = t.]

The bijections preserve the shape and therefore the size:

[Lemma shape_stdtab_of_yam y : shape (stdtab_of_yam y) = evalseq y.]

[Lemma shape_yam_of_stdtab t : is_stdtab t -> evalseq (yam_of_stdtab t) = shape t.]

[Lemma size_stdtab_of_yam y  : size_tab (stdtab_of_yam y) = size y.]

[Lemma size_yam_of_stdtab t  : is_stdtab t -> size (yam_of_stdtab t) = size_tab t.]

                                                                              *)
(******************************************************************************)

Section AppendNth.

Variable T : ordType.
Implicit Type b : T.
Implicit Type t : seq (seq T).

Definition append_nth t b i := set_nth [::] t i (rcons (nth [::] t i) b).

Lemma perm_eq_append_nth t x pos :
  perm_eq (to_word (append_nth t x pos)) (x :: to_word t).
Proof.
  rewrite /append_nth; elim: t pos => [//= | t0 t IHt] /=.
  + elim => [//= | pos IHpos].
    move: IHpos; rewrite /= to_word_cons cats0.
    by rewrite nth_default //= set_nth_nil.
  + case => [//= | pos].
    * rewrite !to_word_cons -cats1 -[x :: (_ ++ _)]cat1s.
      rewrite [flatten _ ++ _ ++ _]catA.
      apply: perm_eqlE; by apply: perm_catC.
    * have {IHt} IHt := IHt pos.
      rewrite /= !to_word_cons.
      by rewrite -/((x :: to_word t) ++ t0) perm_cat2r.
Qed.

Lemma shape_append_nth t b i : shape (append_nth t b i) = incr_nth (shape t) i.
Proof.
  rewrite /shape /=; apply: (@eq_from_nth _ 0).
  + rewrite size_map size_set_nth size_incr_nth size_map /maxn.
    case (ltngtP i.+1 (size t)).
    - by move/ltnW ->.
    - by rewrite ltnNge => /negbTE ->.
    - by move => ->; rewrite leqnn.
  + move=> j Hi.
    rewrite nth_incr_nth (nth_map [::]) /=; last by move: Hi; rewrite size_map.
    rewrite nth_set_nth /= eq_sym.
    have -> : nth 0 [seq size i | i <- t] j = size (nth [::] t j).
      case (ltnP j (size t)) => Hcase.
      * by rewrite (nth_map [::] _ _ Hcase).
      * by rewrite (nth_default _ Hcase) nth_default; last by rewrite size_map.
    case eqP => [->|].
    - by rewrite size_rcons add1n.
    - by rewrite add0n.
Qed.

Lemma size_append_nth t b i : size_tab (append_nth t b i) = (size_tab t).+1.
Proof. by rewrite /size_tab shape_append_nth sumn_incr_nth. Qed.

Fixpoint last_big t b :=
  if t is t0 :: t' then
    if last b t0 == b then 0
    else (last_big t' b).+1
  else 0.

Lemma allLeq_to_word_hd r t b : allLeq (to_word (r :: t)) b -> allLeq r b.
Proof. by rewrite to_word_cons allLeq_catE => /andP [] _. Qed.
Lemma allLeq_to_word_tl r t b : allLeq (to_word (r :: t)) b -> allLeq (to_word t) b.
Proof. by rewrite to_word_cons allLeq_catE => /andP []. Qed.

Lemma last_bigP t b i :
  is_tableau t -> allLeq (to_word t) b ->
  reflect (last b (nth [::] t i) = b /\ forall j, j < i -> last b (nth [::] t j) <A b)
          (i == last_big t b).
Proof.
  move=> Htab Hmax; apply: (iffP idP).
  + move/eqP ->; split.
    * elim: t Htab {Hmax} => [//= | t0 t IHt] /= /and4P [] _ _ _ Htab.
      case eqP => [//= | _]; by apply: IHt.
    * elim: t Htab Hmax => [//= | t0 t IHt] /= /and4P [] Hnnil _ _ Htab Hmax.
      case eqP => [//= | /eqP H].
      case=> [/= _ | j].
      + have:= (allLeq_to_word_hd Hmax); move: Hnnil H.
        case/lastP: t0 {Hmax} => [//= | t0 tn] _; rewrite last_rcons => H1 /allLeq_last.
        by rewrite ltnX_neqAleqX H1.
      + rewrite /=; by apply: IHt; last by apply: (allLeq_to_word_tl Hmax).
  + move=> []; elim: t i Htab Hmax => [/= i _ _| t0 t IHt].
    * case: i => [//= | i] /= _ H.
      exfalso; have:= H 0 (ltn0Sn _); by rewrite ltnXnn.
    * case=> [/= _ _ -> _| i]; first by rewrite eq_refl.
      move=> /= /and4P [] _ _ _ Htab Hmax Hlast Hj.
      have:= Hj 0 (ltn0Sn _) => /= /ltnX_eqF ->.
      apply: (IHt _ Htab (allLeq_to_word_tl Hmax) Hlast).
      move=> j; by apply: (Hj j.+1).
Qed.

Lemma last_big_append_nth t b lb :
  (forall j : nat, j < lb -> last b (nth [::] t j) <A b) ->
  last_big (append_nth t b lb) b = lb.
Proof.
  elim: t lb =>[/= | t0 t IHt /=].
  + case => [/= _| lb Hj /=]; first by rewrite eq_refl.
    exfalso; have:= Hj 0 (ltn0Sn _); by rewrite ltnXnn.
  + case => [/= _| lb Hj /=]; first by rewrite last_rcons eq_refl.
    rewrite (ltnX_eqF (Hj 0 (ltn0Sn _))).
    have {Hj} Hj j : j < lb -> last b (nth [::] t j) <A b by apply/(Hj j.+1).
    by rewrite (IHt _ Hj).
Qed.

End AppendNth.

Section Bijection.

Implicit Type y : seq nat.
Implicit Type t : seq (seq nat).

Definition is_stdtab t := is_tableau t && is_std (to_word t).

Section StdTabInd.

Fixpoint remn_rec t n :=
  if t is t0 :: t' then
    match t0 with
      | [::] => [::] (* unused case *)
      | l0 :: t0' => if last l0 t0' == n then
                       if t0' == [::] then [::]
                       else (belast l0 t0') :: t'
                     else t0 :: remn_rec t' n
    end
  else [::] (* unused case *).
Definition remn t := remn_rec t (size_tab t).-1.

Lemma remnP t :
  is_stdtab t -> t != [::] ->
  is_tableau (remn t) /\
  append_nth (remn t) (size_tab t).-1 (last_big t (size_tab t).-1) = t.
Proof.
  rewrite /remn; move Hn : (size_tab t) => n.
  case: n Hn => [| n]; first by move=> /tab0 H /andP [] /H ->.
  move=> Hsize Hstdtab _.
  have Htab : is_tableau t by move: Hstdtab => /andP [].
  have Hstd : is_std (to_word t) by move: Hstdtab => /andP [].
  have Hperm : perm_eq (to_word t) (iota 0 n.+1) by rewrite -Hsize size_to_word.
  have := std_uniq Hstd.
  have : allLeq (to_word t) n.
    have := Hstd => /perm_eq_allLeqE ->.
    apply/allP => x.
    by rewrite mem_iota add0n -size_to_word Hsize /= leqXnatE.
  have : n \in to_word t.
    move: Hperm => /perm_eq_mem ->.
    by rewrite mem_iota /= add0n.
  elim: t Htab {Hsize Hstdtab Hstd Hperm} => [//= | t0 t' /= IHt] /and4P [].
  case: t0 => [| l0 t0] _ //.
  case: (altP ((last l0 t0) =P n)) => [{IHt} |].
  - case/lastP: t0 => [ /= Hl0 _ | t0 tn].
      subst l0.
      case: t' => [//=| t1 t'] /= Hdom /and4P [] Hnnil _ _ _ _.
      rewrite !to_word_cons !allLeq_catE => /andP [] /andP [] _ Ht1 _ _.
      exfalso.
      case: t1 Hnnil Ht1 Hdom => [//=| l1 t1] _ /= /andP [] Hl1 _.
      move=> /dominateP [] _ /= Hdom.
      have {Hdom} /Hdom /= : 0 < (size t1).+1 by [].
      by rewrite ltnXNgeqX Hl1.
    have /negbTE -> : rcons t0 tn != [::] by case t0 => [//= | l s]; rewrite rcons_cons.
    rewrite belast_rcons last_rcons => Hl0; subst tn => Hrow Hdom Htab' _ /=.
    rewrite to_word_cons cat_uniq allLeq_catE => /andP [] Ht' _ /and3P [] _.
    rewrite -all_predC => /allP /= Hall _.
    have {Hall} /Hall Hn : n \in l0 :: rcons t0 n.
      by rewrite inE mem_rcons inE eq_refl orbT.
    move: Hrow; rewrite -rcons_cons Htab' andbT => /is_row_rconsK /= -> /=.
    split; last by rewrite /append_nth /=.
    case: t' Ht' Hn Hdom Htab' => [//= | t1 t'].
    rewrite to_word_cons allLeq_catE => /andP [] _ Ht1.
    rewrite mem_cat negb_or => /andP [] _ Hn /=.
    have {Ht1 Hn} Ht1 : allLtn t1 n.
      elim: t1 Ht1 Hn => [//= | l1 t1 IHt1] /= /andP [] Hl1 /IHt1{IHt1} Hrec.
      rewrite inE negb_or => /andP [] Hl1n /Hrec ->.
      by rewrite andbT /ltnX_op Hl1 eq_sym Hl1n.
    rewrite -rcons_cons; move: (l0 :: t0) => {l0 t0} t0.
    move=> Hdom _.
    elim: t0 t1 Ht1 Hdom => [| l0 t0 IHt0] t1 /=.
      case: t1 => [| l1 [| t1]] //=.
      rewrite /dominate /= !andbT => /ltnX_trans H/H.
      by rewrite ltnXnn.
    case: t1 => [//= | l1 t1] /= /andP [] _ /IHt0 {IHt0} Hrec Hdom.
    have {Hrec} Hrec := Hrec (dominate_tl Hdom).
    have /dominate_head Htmp : l1 :: t1 != [::] by [].
    have {Htmp Hdom} /= Hl := Htmp _ Hdom.
    move: Hrec => /dominateP [] Hsz Hdom.
    apply/dominateP; split; first exact: Hsz.
    case=> [_|i] //=; by rewrite ltnS => /Hdom.
  - move => Hlast /= Hrow Hdom Htab'.
    rewrite to_word_cons mem_cat cat_uniq allLeq_catE.
    case: (boolP (n \in to_word t')) => [Hn _ | _ Hn] /andP [] Hall Hall0.
    + move => /andP [] Huniq _ {Hall0 Hlast}.
      rewrite Hrow /= {Hrow}.
      have {IHt Htab' Hn Hall Huniq} := (IHt Htab' Hn Hall Huniq) => [] [] -> Happ.
      split; last by move: Happ; rewrite /append_nth /= => ->.
      rewrite andbT {Happ}.
      move: Hdom.
      case: t' => [//= | t1 t'] /=.
      case: t1 => [//= | l1 t1] /=.
      case: eqP => //= _.
      case/lastP: t1 => [//= | t1 tl1].
      have /negbTE -> : rcons t1 tl1 != [::] by case t1 => [//= | l s]; rewrite rcons_cons.
      rewrite belast_rcons -rcons_cons.
      move: (l1 :: t1) => {l1 t1} t1 /=.
      move: (l0 :: _) => {l0 t0} t0 /dominateP [].
      rewrite size_rcons => /ltnW Hsz Hdom.
      apply/dominateP; split; first exact Hsz.
      move=> i Hi.
      have /Hdom : i < (size t1).+1 by apply ltnW.
      by rewrite nth_rcons Hi. 
    + exfalso => {IHt Hdom t' Htab' Hall}.
      case/lastP: t0 Hn Hlast Hrow Hall0 => [/= | t0 tn].
        rewrite inE => /eqP ->; by rewrite eq_refl.
      rewrite orFb -/(is_row (l0 :: _)).
      rewrite -rcons_cons last_rcons.
      move: (l0 :: t0) => {l0 t0} t0 /= Hn Htnn /is_rowP Hrow.
      have Hind := nth_index 0 Hn.
      move: Hn; rewrite -index_mem size_rcons ltnS => Hsz.
      have {Hrow} /(Hrow 0) : index n (rcons t0 tn) <= size t0 < size (rcons t0 tn).
        by rewrite Hsz size_rcons ltnS /=.
      rewrite Hind nth_rcons ltnn eq_refl {Hind Hsz} => Hn /allLeq_last.
      by rewrite leqXNgtnX /ltnX_op eq_sym Htnn Hn.
Qed.

Lemma is_stdtab_remn t : is_stdtab t -> t != [::] -> is_stdtab (remn t).
Proof.
  move Hn : (size_tab t) => n.
  case: n Hn => [| n]; first by move=> /tab0 H /andP [] /H ->.
  move=> Hsize Hstdtab Hnnil /=.
  have := remnP Hstdtab Hnnil; rewrite /remn Hsize /= => [] [] Htab Happ {Hnnil}.
  move: Hstdtab; rewrite /is_stdtab Htab /= /is_std.
  rewrite -!size_to_word {1}Hsize => /andP [] _ Hperm.
  have := erefl (size_tab t).
  rewrite -{1}Happ size_append_nth Hsize => /eqP; rewrite eqSS => /eqP Hsz.
  have := perm_eq_append_nth (remn_rec t n) n (last_big t n).
  rewrite Happ Hsz {Happ Hsz}.
  rewrite (perm_eqlP Hperm) perm_eq_sym.
  rewrite -(addn1 n) iota_add /= add0n cats1.
  by rewrite perm_eq_sym perm_rcons perm_eq_sym perm_cons.
Qed.

Lemma append_nth_remn t :
  is_stdtab t -> t != [::] ->
  append_nth (remn t) (size_tab t).-1 (last_big t (size_tab t).-1) = t.
Proof. by move=> H1 H2; have [] := remnP H1 H2. Qed.

Lemma size_tab_remn t :
  is_stdtab t -> t != [::] -> size_tab (remn t) = (size_tab t).-1.
Proof. move=> /append_nth_remn H/H{H} {2}<-. by rewrite size_append_nth. Qed.

End StdTabInd.

Fixpoint stdtab_of_yam y :=
  if y is y0 :: y' then
    append_nth (stdtab_of_yam y') (size y') y0
  else [::].

Lemma shape_stdtab_of_yam y : shape (stdtab_of_yam y) = evalseq y.
Proof. elim: y => [//= | y0 y IHy] /=. by rewrite shape_append_nth IHy. Qed.

Lemma size_stdtab_of_yam y : size_tab (stdtab_of_yam y) = size y.
Proof.
  elim: y => [//= | y0 y IHy] /=.
  by rewrite -IHy {IHy} /size_tab shape_append_nth sumn_incr_nth.
Qed.

Lemma std_of_yam y : is_std (to_word (stdtab_of_yam y)).
Proof.
  rewrite /is_std -size_to_word size_stdtab_of_yam.
  elim: y => [//= | y0 y IHy].
  have -> /= : iota 0 (size (y0 :: y)) = rcons (iota 0 (size y)) (size y).
    rewrite [size (y0 :: y)]/= -addn1 iota_add add0n /=.
    by apply: cats1.
  apply: (perm_eq_trans (perm_eq_append_nth _ _ _)).
  move: IHy; rewrite -(perm_cons (size y)) => /perm_eq_trans; apply.
  rewrite perm_eq_sym; apply/perm_eqlP; by apply: perm_rcons.
Qed.

Lemma is_tab_append_nth_size r T n :
   all (gtn n) (to_word T) ->
   is_part (incr_nth (shape T) r) ->
   is_tableau T -> is_tableau (append_nth T n r).
Proof.
  elim: T r => [//= | T0 T IHT] r /=; first by case: r => [//= | r] /=; elim: r.
  rewrite to_word_cons all_cat.
  move=> /andP [] Hall Hall0.
  case: r => [/= _ | r] /=.
  - move=> {IHT Hall} /and4P [] Hnnil Hrow Hdom ->.
    rewrite (dominate_rcons _ Hdom) {Hdom} !andbT.
    apply/andP; split; first by case T0.
    apply: (is_row_rcons Hrow); rewrite {Hrow} leqXnatE.
    case/lastP: T0 Hnnil Hall0 => [//= | T0 T0n] _.
    rewrite all_rcons last_rcons /= andbC => /andP [] _.
    by apply: ltnW.
  - move => /andP [] Hhead Hpart /and4P [] -> -> Hdom Htab /=.
    rewrite IHT //= andbT {IHT Hall Hpart Htab}.
    case: r Hhead => [| r]; last by case: T Hdom => [//= | T1 T].
    case: T Hdom => [_ | T1 T] /=.
    + case: T0 Hall0 => [//= | hT0 T0] /= /andP [] Hn _ _.
      by rewrite /dominate /= ltnXnatE Hn.
    + move/dominateP => [] _ Hdom Hsize.
      apply/dominateP; split; rewrite size_rcons; first by [].
      move=> i Hi; rewrite nth_rcons; case (ltnP i (size T1)) => Hi1.
      * by apply: Hdom.
      * have -> : i == size T1 by rewrite eqn_leq Hi1 andbT -ltnS.
        move: Hall0 => /allP Hall0.
        have /Hall0 /= := (mem_nth (inhabitant nat_ordType) (leq_trans Hi Hsize)).
        by rewrite ltnXnatE.
Qed.

Lemma stdtab_of_yamP y : is_yam y -> is_stdtab (stdtab_of_yam y).
Proof.
  rewrite /is_stdtab std_of_yam andbT.
  elim: y => [//= | y0 y IHy] /= /andP [] Hpart /IHy {IHy}.
  move: Hpart; rewrite -shape_stdtab_of_yam.
  suff : all (gtn (size y)) (to_word (stdtab_of_yam y)) by apply: is_tab_append_nth_size.
  have:= std_of_yam y; rewrite /is_std -size_to_word size_stdtab_of_yam.
  move=> /perm_eq_mem Hperm.
  apply/allP => x Hx /=.
  have:= Hperm x; by rewrite mem_iota /= add0n Hx => /esym ->.
Qed.

Fixpoint yam_of_stdtab_rec n t :=
  if n is n'.+1 then
    (last_big t n') :: yam_of_stdtab_rec n' (remn t)
  else [::].
Definition yam_of_stdtab t := yam_of_stdtab_rec (size_tab t) t.

Lemma size_yam_of_stdtab_rec n t : size (yam_of_stdtab_rec n t) = n.
Proof. elim: n t => [//= | n IHn] /= t; by rewrite IHn. Qed.

Theorem yam_of_stdtabK t : is_stdtab t -> stdtab_of_yam (yam_of_stdtab t) = t.
Proof.
  rewrite /yam_of_stdtab.
  move H : (size_tab t) => n.
  elim: n t H => [| n IHn] t.
    by rewrite /is_stdtab => /= /tab0 H /andP [] /H ->.
  move=> Hsize Hstdtab /=.
  have Hnnil : t != [::] by move: Hsize => /eqP; apply contraL => /eqP ->.
  have := size_tab_remn Hstdtab Hnnil; rewrite Hsize /= => /(IHn (remn t)) {IHn} Hrec.
  rewrite (Hrec (is_stdtab_remn Hstdtab Hnnil)) size_yam_of_stdtab_rec.
  have:= append_nth_remn Hstdtab Hnnil; by rewrite Hsize /=.
Qed.

Lemma find_append_nth l t r :
  l \notin (to_word t) -> find (fun x => l \in x) (append_nth t l r) = r.
Proof.
  rewrite /append_nth.
  elim: r t => [/= | r IHr] t /=; case: t => [_ | t0 t] /=.
  + by rewrite inE eq_refl.
  + by rewrite mem_rcons inE eq_refl /=.
  + apply/eqP; rewrite eqSS.
    elim: r {IHr} => [//= | r]; first by rewrite inE eq_refl.
    by rewrite /ncons /= => /eqP ->.
  + by rewrite to_word_cons mem_cat negb_or => /andP [] /IHr {IHr} -> /negbTE ->.
Qed.

Lemma size_notin_stdtab_of_yam y : (size y) \notin (to_word (stdtab_of_yam y)).
Proof.
  have:= std_of_yam y; rewrite /is_std -size_to_word size_stdtab_of_yam => /perm_eq_mem ->.
  by rewrite mem_iota add0n /= ltnn.
Qed.

Lemma incr_nth_injl u v i :
  0 \notin u -> 0 \notin v -> incr_nth u i = incr_nth v i -> u = v.
Proof.
  move=> Hu Hv /eqP; elim: u v Hu Hv i => [/= v _ | u0 u IHu v] /=; case: v => [//= | v0 v].
  + rewrite inE negb_or => /andP [] Hv0 _.
    by case=> [| i] /= /eqP [] H; rewrite H eq_refl in Hv0.
  + move=> {IHu}.
    rewrite inE negb_or => /andP [] Hu0 _ _.
    by case=> [| i] /= /eqP [] H; rewrite H eq_refl in Hu0.
  rewrite !inE !negb_or => /andP [] Hu0 Hu /andP [] Hv0 Hv.
  case=> [| i] /= /eqP [] ->; first by move ->.
  by move/eqP/(IHu _ Hu Hv) ->.
Qed.

Lemma shape0 (T : ordType) (u : seq (seq T)) : [::] \notin u -> 0 \notin (shape u).
Proof.
  apply: contra; rewrite /shape; elim: u => [//=| u0 u IHu] /=.
  rewrite !inE => /orP [].
  + by rewrite eq_sym => /nilP ->.
  + move/IHu ->; by rewrite orbT.
Qed.

Lemma append_nth_injl (T : ordType) u v (l : T) p :
  [::] \notin u -> [::] \notin v -> append_nth u l p = append_nth v l p -> u = v.
Proof.
  move=> Hu Hv Heq; have:= erefl (shape (append_nth u l p)); rewrite {2}Heq.
  rewrite !shape_append_nth => /(incr_nth_injl (shape0 Hu) (shape0 Hv)) => /eqP {Hu Hv}.
  move: Heq; rewrite /append_nth.
  elim: u v p => [/= | u0 u IHu] /=; case=> [| v0 v] //=.
  case=> [| p] /= []; first by move/rconsK => -> ->.
  by move=> -> Heq /eqP [] /eqP /(IHu _ _ Heq) ->.
Qed.

Lemma stdtab_of_yam_nil y : is_yam y -> [::] \notin (stdtab_of_yam y).
Proof.
  move/stdtab_of_yamP; rewrite /is_stdtab => /andP [] Htab _.
  elim: (stdtab_of_yam) Htab => [//= | t0 t IHt] /= /and4P [] Hnnil _ _ /IHt H.
  by rewrite inE negb_or eq_sym Hnnil H.
Qed.

Lemma stdtab_of_yam_inj x y :
  is_yam x -> is_yam y -> stdtab_of_yam x = stdtab_of_yam y -> x = y.
Proof.
  move=> Hx Hy H.
  have:= eq_refl (size_tab (stdtab_of_yam x)); rewrite {2}H !size_stdtab_of_yam => Hsz.
  elim: x y Hsz H Hx Hy => [| x0 x IHx]; case=> [//= | y0 y] //=.
  rewrite eqSS => Heqsz; have:= Heqsz => /eqP -> Heq.
  have Hfind w := find_append_nth _ (size_notin_stdtab_of_yam w).
  have:= Hfind x0 x; rewrite (eqP Heqsz) Heq Hfind {Hfind} => H0.
  move=> /andP [] _ Hx /andP [] _ Hy.
  rewrite H0; congr (_ :: _); apply: (IHx _ Heqsz) => {IHx Heqsz} //=.
  move: Heq; rewrite H0 {H0}.
  apply: append_nth_injl; by apply: stdtab_of_yam_nil.
Qed.

Lemma shape_yam_of_stdtab t : is_stdtab t -> evalseq (yam_of_stdtab t) = shape t.
Proof.
  move/yam_of_stdtabK => H.
  have:= erefl (shape t); by rewrite -{1}H shape_stdtab_of_yam.
Qed.

Lemma size_yam_of_stdtab t : is_stdtab t -> size (yam_of_stdtab t) = size_tab t.
Proof.
  move=> Htab.
  by rewrite /size_tab -(shape_yam_of_stdtab Htab) evalseq_eq_size.
Qed.

Lemma part_yam_of_stdtab t : is_stdtab t -> is_part (evalseq (yam_of_stdtab t)).
Proof.
  move=> Htab; rewrite (shape_yam_of_stdtab Htab).
  apply: is_part_sht.
  by move: Htab; rewrite /is_stdtab => /andP [].
Qed.

Lemma yam_of_stdtabP t : is_stdtab t -> is_yam (yam_of_stdtab t).
Proof.
  move=> Hstdtab; have := part_yam_of_stdtab Hstdtab.
  rewrite /yam_of_stdtab.
  move H : (size_tab t) => n.
  elim: n t H Hstdtab => [//= | n IHn] t Hsize Hstdtab.
  move Hw : (to_word t) Hsize => w; case : w Hw => [//= | w0 w].
    by rewrite size_to_word => -> /=.
  rewrite /= => Ht Hsize -> /=.
  have Hnnil : t != [::] by move: Hsize => /eqP; apply contraL => /eqP ->.
  have := size_tab_remn Hstdtab Hnnil; rewrite Hsize /= => Hsz.
  apply (IHn _ Hsz); first exact: is_stdtab_remn.
  rewrite -Hsz.
  exact: part_yam_of_stdtab (is_stdtab_remn Hstdtab Hnnil).
Qed.

Theorem stdtab_of_yamK y : is_yam y -> yam_of_stdtab (stdtab_of_yam y) = y.
Proof.
  move=> Hyam.
  have /yam_of_stdtabK := (stdtab_of_yamP Hyam).
  apply: stdtab_of_yam_inj; last exact Hyam.
  apply: yam_of_stdtabP; by apply: stdtab_of_yamP.
Qed.

End Bijection.


Section StdtabOfShape.

Definition is_stdtab_of_shape sh := [pred t | (is_stdtab t) && (shape t == sh) ].
Definition enum_stdtabsh sh : seq (seq (seq nat)) := map stdtab_of_yam (enum_yameval sh).

Variable sh : intpart.

Structure stdtabsh : predArgType :=
  StdtabSh {stdtabshval :> seq (seq nat); _ : is_stdtab_of_shape sh stdtabshval}.
Canonical stdtabsh_subType := Eval hnf in [subType for stdtabshval].
Definition stdtabsh_eqMixin := Eval hnf in [eqMixin of stdtabsh by <:].
Canonical stdtabsh_eqType := Eval hnf in EqType stdtabsh stdtabsh_eqMixin.
Definition stdtabsh_choiceMixin := Eval hnf in [choiceMixin of stdtabsh by <:].
Canonical stdtabsh_choiceType := Eval hnf in ChoiceType stdtabsh stdtabsh_choiceMixin.
Definition stdtabsh_countMixin := Eval hnf in [countMixin of stdtabsh by <:].
Canonical stdtabsh_countType := Eval hnf in CountType stdtabsh stdtabsh_countMixin.
Canonical stdtabsh_subCountType := Eval hnf in [subCountType of stdtabsh].

Let stdtabsh_enum : seq stdtabsh := pmap insub (enum_stdtabsh sh).

Lemma finite_stdtabsh : Finite.axiom stdtabsh_enum.
Proof.
  case=> /= t Ht; rewrite -(count_map _ (pred1 t)) (pmap_filter (@insubK _ _ _)).
  rewrite count_filter -(@eq_count _ (pred1 t)) => [|s /=]; last first.
    by rewrite isSome_insub; case: eqP=> // ->.
  move: Ht => /andP [] Htab /eqP.
  rewrite -(shape_yam_of_stdtab Htab) => Hsht.
  rewrite /enum_stdtabsh count_map.
  rewrite (eq_in_count (a2 := pred1 (yam_of_stdtab t))); first last.
    move=> y /(allP (enum_yamevalP (intpartP sh))).
    rewrite /is_yam_of_eval => /andP [] Hyam /eqP Hevy /=.
    apply/(sameP idP); apply(iffP idP) => /eqP H; apply/eqP.
    + by rewrite H yam_of_stdtabK.
    + by rewrite -H stdtab_of_yamK.
  apply: (enum_yameval_countE (intpartP sh)).
  by rewrite /is_yam_of_eval yam_of_stdtabP //= Hsht.
Qed.

Canonical stdtabsh_finMixin := Eval hnf in FinMixin finite_stdtabsh.
Canonical stdtabsh_finType := Eval hnf in FinType stdtabsh stdtabsh_finMixin.
Canonical stdtabsh_subFinType := Eval hnf in [subFinType of stdtabsh_countType].

Lemma stdtabshP (t : stdtabsh) : is_stdtab t.
Proof. by case: t => /= t /andP []. Qed.

Lemma stdtabsh_shape (t : stdtabsh) : shape t = sh.
Proof. by case: t => /= t /andP [] _ /eqP. Qed.

End StdtabOfShape.

Section StdtabCombClass.

Variable n : nat.

Definition is_stdtab_of_n := [pred t | (is_stdtab t) && (size_tab t == n) ].

Structure stdtabn : predArgType :=
  StdtabN {stdtabnval :> seq (seq nat); _ : is_stdtab_of_n stdtabnval}.
Canonical stdtabn_subType := Eval hnf in [subType for stdtabnval].
Definition stdtabn_eqMixin := Eval hnf in [eqMixin of stdtabn by <:].
Canonical stdtabn_eqType := Eval hnf in EqType stdtabn stdtabn_eqMixin.
Definition stdtabn_choiceMixin := Eval hnf in [choiceMixin of stdtabn by <:].
Canonical stdtabn_choiceType := Eval hnf in ChoiceType stdtabn stdtabn_choiceMixin.

Definition stdtabn_countMixin := Eval hnf in [countMixin of stdtabn by <:].
Canonical stdtabn_countType := Eval hnf in CountType stdtabn stdtabn_countMixin.
Canonical stdtabnn_subCountType := Eval hnf in [subCountType of stdtabn].


Definition enum_stdtabn : seq (seq (seq nat)) :=
  map (stdtab_of_yam \o val) (enum (yamn n)).
Let stdtabn_enum : seq stdtabn := pmap insub enum_stdtabn.

Lemma finite_stdtabn : Finite.axiom stdtabn_enum.
Proof.
  case=> /= t Ht; rewrite -(count_map _ (pred1 t)) (pmap_filter (@insubK _ _ _)).
  rewrite count_filter -(@eq_count _ (pred1 t)) => [|s /=]; last first.
    by rewrite isSome_insub; case: eqP=> // ->.
  move: Ht => /andP [] Htab /eqP.
  rewrite -(size_yam_of_stdtab Htab) => Hszt.
  rewrite /enum_stdtabn map_comp.
  rewrite !enumT unlock subType_seqP.
  rewrite count_map.
  rewrite (eq_in_count (a2 := pred1 (yam_of_stdtab t))); first last.
    move=> y /(allP (all_unionP _ (@yamn_PredEq _))) /=.
    rewrite /is_yam_of_size => /andP [] Hyam /eqP Hszy /=.
    apply/(sameP idP); apply(iffP idP) => /eqP H; apply/eqP.
    + by rewrite H yam_of_stdtabK.
    + by rewrite -H stdtab_of_yamK.
  apply: (count_unionP _ (@yamn_PredEq _)).
  - by apply: yamn_partition_evalseq.
  - by rewrite /is_yam_of_size yam_of_stdtabP //= Hszt.
Qed.

Canonical stdtabn_finMixin := Eval hnf in FinMixin finite_stdtabn.
Canonical stdtabn_finType := Eval hnf in FinType stdtabn stdtabn_finMixin.
Canonical stdtabn_subFinType := Eval hnf in [subFinType of stdtabn_countType].

Lemma stdtabnP (s : stdtabn) : is_stdtab s.
Proof. by case: s => s /= /andP []. Qed.

Lemma stdtabn_size (s : stdtabn) : size_tab s = n.
Proof. by case: s => s /= /andP [] _ /eqP. Qed.

End StdtabCombClass.

