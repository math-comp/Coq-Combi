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

Require Import subseq partition permuted ordtype schensted plactic greeninv std.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* Bijection between Yamanouchi word and standard tableau                     *)
(* Main results:                                                              *)
(* Bijection:

Lemma   stdtab_of_yamP y : is_yam y    -> is_stdtab (stdtab_of_yam y).
Theorem stdtab_of_yamK y : is_yam y    -> yam_of_stdtab (stdtab_of_yam y) = y.
Lemma   yam_of_stdtabP t : is_stdtab t -> is_yam (yam_of_stdtab t).
Theorem yam_of_stdtabK t : is_stdtab t -> stdtab_of_yam (yam_of_stdtab t) = t.

Statistic:

Lemma shape_stdtab_of_yam y : shape (stdtab_of_yam y) = shape_rowseq y.
Lemma shape_yam_of_stdtab t : is_stdtab t -> shape_rowseq (yam_of_stdtab t) = shape t.
Lemma size_stdtab_of_yam y  : size_tab (stdtab_of_yam y) = size y.
Lemma size_yam_of_stdtab t  : is_stdtab t -> size (yam_of_stdtab t) = size_tab t.
                                                                              *)
(******************************************************************************)


Section Bijection.

Implicit Type y : seq nat.
Implicit Type t : seq (seq nat).

Definition is_stdtab t := is_tableau t && is_std (to_word t).

Lemma RSperm n (p : 'S_n) : is_stdtab (RS (wordperm p)).
Proof.
  rewrite /is_stdtab; apply /andP; split; first by apply is_tableau_RS.
  apply (perm_eq_std (wordperm_std p)).
  rewrite perm_eq_sym; apply (perm_eq_RS (wordperm p)).
Qed.

Lemma RSstdE (p : seq nat) : is_stdtab (RS p) = is_std p.
Proof.
  rewrite /is_stdtab is_tableau_RS /=.
  apply/(sameP idP); apply(iffP idP) => Hstd; apply (perm_eq_std Hstd);
    first rewrite perm_eq_sym; apply perm_eq_RS.
Qed.

Fixpoint stdtab_of_yam y :=
  if y is y0 :: y' then
    append_nth (stdtab_of_yam y') (size y') y0
  else [::].

Lemma shape_stdtab_of_yam y : shape (stdtab_of_yam y) = shape_rowseq y.
Proof. elim: y => [//= | y0 y IHy] /=. by rewrite shape_append_nth IHy. Qed.

Lemma size_stdtab_of_yam y : size_tab (stdtab_of_yam y) = size y.
Proof.
  elim: y => [//= | y0 y IHy] /=.
  by rewrite -IHy {IHy} /size_tab shape_append_nth sum_incr_nth.
Qed.

Lemma perm_eq_append_nth t x pos :
  perm_eq (to_word (append_nth t x pos)) (x :: to_word t).
Proof.
  rewrite /append_nth /to_word; elim: t pos => [//= | t0 t IHt] /=.
  + elim => [//= | pos IHpos].
    move: IHpos; rewrite /= rev_cons flatten_rcons cats0.
    by rewrite nth_default //= set_nth_nil.
  + case => [//= | pos].
    * rewrite !rev_cons !flatten_rcons -cats1 -[x :: (_ ++ _)]cat1s.
      rewrite [flatten _ ++ _ ++ _]catA.
      apply perm_eqlE; by apply perm_catC.
    * have {IHt} IHt := IHt pos.
      rewrite !rev_cons !flatten_rcons.
      move: IHt; set T := (flatten _).
      by rewrite -[x :: flatten (rev t) ++ t0]/((x :: flatten (rev t)) ++ t0) perm_cat2r.
Qed.

Lemma std_of_yam y : is_std (to_word (stdtab_of_yam y)).
Proof.
  rewrite /is_std -size_to_word size_stdtab_of_yam.
  elim: y => [//= | y0 y IHy].
  have -> /= : iota 0 (size (y0 :: y)) = rcons (iota 0 (size y)) (size y).
    rewrite -[size (y0 :: y)]/((size y).+1) -addn1 iota_add add0n /=.
    by apply cats1.
  apply (perm_eq_trans (perm_eq_append_nth _ _ _)).
  move: IHy; rewrite -(perm_cons (size y)) => /perm_eq_trans; apply.
  rewrite perm_eq_sym; apply/perm_eqlP; by apply perm_rcons.
Qed.

Lemma is_tab_append_nth_size r T n :
   all (gtn n) (to_word T) ->
   is_part (incr_nth (shape T) r) ->
   is_tableau T -> is_tableau (append_nth T n r).
Proof.
  elim: T r => [//= | T0 T IHT] r /=; first by case: r => [//= | r] /=; elim: r.
  rewrite /to_word rev_cons flatten_rcons all_cat -[flatten (rev T)]/(to_word T).
  move=> /andP [] Hall Hall0.
  case: r => [/= _ | r] /=.
  - move=> {IHT Hall} /and4P [] Hnnil Hrow Hdom ->.
    rewrite (dominate_rcons _ Hdom) {Hdom} !andbT.
    apply /andP; split; first by case T0.
    apply (is_row_rcons Hrow); rewrite {Hrow} leqXnatE.
    case/lastP: T0 Hnnil Hall0 => [//= | T0 T0n] _.
    rewrite all_rcons last_rcons /= andbC => /andP [] _.
    by apply ltnW.
  - move => /andP [] Hhead Hpart /and4P [] -> -> Hdom Htab /=.
    rewrite IHT //= andbT {IHT Hall Hpart Htab}.
    case: r Hhead => [| r]; last by case: T Hdom => [//= | T1 T].
    case: T Hdom => [_ | T1 T] /=.
    + case: T0 Hall0 => [//= | hT0 T0] /= /andP [] Hn _ _.
      apply/dominateP; split=> //=; case => [|//=] _ /=.
      by rewrite ltnXnatE.
    + move/dominateP => [] _ Hdom Hsize.
      apply/dominateP; split; rewrite size_rcons; first by [].
      move=> i Hi; rewrite nth_rcons; case (ltnP i (size T1)) => Hi1.
      * by apply Hdom.
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
  suff : all (gtn (size y)) (to_word (stdtab_of_yam y)) by apply is_tab_append_nth_size.
  have:= std_of_yam y; rewrite /is_std -size_to_word size_stdtab_of_yam.
  move=> /perm_eq_mem Hperm.
  apply /allP => x Hx /=.
  have:= Hperm x; by rewrite mem_iota /= add0n Hx => /esym ->.
Qed.

Fixpoint yam_of_stdtab_rec n t :=
  if n is n'.+1 then
    (last_big t n') :: yam_of_stdtab_rec n' (RS (rembig (to_word t)))
  else [::].
Definition yam_of_stdtab t := yam_of_stdtab_rec (size_tab t) t.

Lemma size_yam_of_stdtab_rec n t : size (yam_of_stdtab_rec n t) = n.
Proof. elim: n t => [//= | n IHn] /= t; by rewrite IHn. Qed.


Theorem yam_of_stdtabK t : is_stdtab t -> stdtab_of_yam (yam_of_stdtab t) = t.
Proof.
  rewrite /yam_of_stdtab /is_stdtab /is_std -size_to_word => /andP [].
  move H : (size_tab t) => n.
  elim: n t H => [//= | n IHn] t Hsize Htab Hperm.
    move: Hsize => /tab0 H; by rewrite (H Htab).
  move Hw : (to_word t) Hsize => w; case : w Hw => [//= | w0 w].
    by rewrite size_to_word => -> /=.
  move=> Hw Hsize.
  have := RS_tabE Htab; rewrite Hw => Ht; have:= Ht.
  have:= (rembig_RS_last_big w0 w) => -> {2}<- /=.
  set t' := RS (rembig (w0 :: w)).
  have Htab' := is_tableau_RS (rembig (w0 :: w)).
  have Hsize' : size_tab t' = n.
    by rewrite (eqP (size_RS _)) size_rembig -Hw -size_to_word Hsize.
  have Hperm' : perm_eq (to_word t') (iota 0 n).
    rewrite -Hsize'; move: Hperm.
    rewrite /t' (eqP (size_RS _)) size_rembig -Hw -size_to_word Hsize /= => Hperm.
    have:= plactcongr_homog (congr_RS (rembig (to_word t))).
    rewrite perm_eq_sym => /perm_eq_trans; apply.
    move: Hperm; rewrite Hw.
    move/perm_eq_rembig/perm_eq_trans; apply.
    rewrite rembig_iota; by apply perm_eq_refl.
  have:= IHn t' Hsize' Htab' Hperm'.
  rewrite size_yam_of_stdtab_rec Ht Hw => ->.
  suff -> : (maxL w0 w) = n by [].
  move: Hperm; rewrite Hw /= => /maxL_perm_eq ->.
  by rewrite maxL_iota.
Qed.


Lemma find_append_nth l t r :
  l \notin (to_word t) -> find (fun x => l \in x) (append_nth t l r) = r.
Proof.
  rewrite /append_nth.
  elim: r t => [/= | r IHr] t /=; case: t => [_ | t0 t] /=.
  + by rewrite inE eq_refl.
  + by rewrite mem_rcons inE eq_refl /=.
  + apply /eqP; rewrite eqSS.
    elim: r {IHr} => [//= | r]; first by rewrite inE eq_refl.
    by rewrite /ncons /= => /eqP ->.
  + rewrite /to_word rev_cons flatten_rcons mem_cat negb_or.
    by rewrite -[flatten (rev t)]/(to_word t) => /andP [] /IHr {IHr} -> /negbTE ->.
Qed.

Lemma size_notin_stdtab_of_yam y : (size y) \notin (to_word (stdtab_of_yam y)).
Proof.
  have:= std_of_yam y; rewrite /is_std -size_to_word size_stdtab_of_yam => /perm_eq_mem ->.
  by rewrite mem_iota add0n /= ltnn.
Qed.

Lemma rconsK (T : eqType) (l : T) u v : rcons u l = rcons v l -> u = v.
Proof.
  elim: u v => [| u0 u IHu]; case=> [|v0 v] //= [].
  + move=> _; by case v.
  + move=> _; by case u.
  + by move=> -> /IHu ->.
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
  apply contra; rewrite /shape; elim: u => [//=| u0 u IHu] /=.
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
  rewrite H0; congr (_ :: _); apply (IHx _ Heqsz) => {IHx Heqsz} //=.
  move: Heq; rewrite H0 {H0}.
  apply append_nth_injl; by apply stdtab_of_yam_nil.
Qed.

Lemma shape_yam_of_stdtab t : is_stdtab t -> shape_rowseq (yam_of_stdtab t) = shape t.
Proof.
  move/yam_of_stdtabK => H.
  have:= erefl (shape t); by rewrite -{1}H shape_stdtab_of_yam.
Qed.

Lemma size_yam_of_stdtab t : is_stdtab t -> size (yam_of_stdtab t) = size_tab t.
Proof.
  move=> Htab.
  by rewrite /size_tab -(shape_yam_of_stdtab Htab) shape_rowseq_eq_size.
Qed.

Lemma part_yam_of_stdtab t : is_stdtab t -> is_part (shape_rowseq (yam_of_stdtab t)).
Proof.
  move=> Htab; rewrite (shape_yam_of_stdtab Htab).
  apply is_part_sht.
  by move: Htab; rewrite /is_stdtab => /andP [].
Qed.

Lemma stdtab_rembig t : is_stdtab t -> is_stdtab (RS (rembig (to_word t))).
Proof.
  rewrite /is_stdtab /is_std -size_to_word => /andP [].
  move H : (size_tab t) => n.
  elim: n t H => [//= | n IHn] t Hsize Htab Hperm.
  + by rewrite (tab0 Htab Hsize) /RS /=.
  + rewrite is_tableau_RS /=.
    apply (@perm_eq_trans _ (rembig (to_word t))).
    - rewrite perm_eq_sym; apply plactcongr_homog; by apply congr_RS.
    - apply (perm_eq_trans (perm_eq_rembig Hperm)).
      rewrite rembig_iota.
      by rewrite -size_to_word (eqP (size_RS _)) size_rembig -size_to_word Hsize.
Qed.

Lemma yam_of_stdtabP t : is_stdtab t -> is_yam (yam_of_stdtab t).
Proof.
  move=> Htab; have := part_yam_of_stdtab Htab.
  rewrite /yam_of_stdtab.
  move H : (size_tab t) => n.
  elim: n t H Htab => [//= | n IHn] t Hsize Htab.
  move Hw : (to_word t) Hsize => w; case : w Hw => [//= | w0 w].
    by rewrite size_to_word => -> /=.
  rewrite /= => Ht Hsize -> /=.
  have Hsize' : size_tab (RS (rembig (to_word t))) = n.
    by rewrite (eqP (size_RS _)) size_rembig -size_to_word Hsize.
  apply (IHn _ Hsize').
  + by apply stdtab_rembig.
  + rewrite -Hsize' (shape_yam_of_stdtab (stdtab_rembig Htab)).
    apply is_part_sht; by apply is_tableau_RS.
Qed.

Theorem stdtab_of_yamK y : is_yam y -> yam_of_stdtab (stdtab_of_yam y) = y.
Proof.
  move=> Hyam.
  have /yam_of_stdtabK := (stdtab_of_yamP Hyam).
  apply stdtab_of_yam_inj; last exact Hyam.
  apply yam_of_stdtabP; by apply stdtab_of_yamP.
Qed.

End Bijection.

Section RobinsonSchensted.

Variable T : ordType.

Notation TabPair := (seq (seq T) * seq (seq nat) : Type).

Definition is_RStabpair (pair : TabPair) :=
  let: (P, Q) := pair in [&& is_tableau P, is_stdtab Q & (shape P == shape Q)].

Record rstabpair := RSTabPair { pqpair :> TabPair; _ : is_RStabpair pqpair }.

Canonical rstabpair_subType := Eval hnf in [subType for pqpair].
Definition rstabpair_eqMixin := Eval hnf in [eqMixin of rstabpair by <:].
Canonical rstabpair_eqType := Eval hnf in EqType rstabpair rstabpair_eqMixin.

Lemma pqpair_inj : injective pqpair. Proof. exact: val_inj. Qed.

Definition RStabmap (w : seq T) := let (p, q) := (RSmap w) in (p, stdtab_of_yam q).

Lemma RStabmapE (w : seq T) : (RStabmap w).1 = RS w.
Proof. rewrite /RStabmap -RSmapE; by case RSmap. Qed.

Theorem RStabmap_spec w : is_RStabpair (RStabmap w).
Proof.
  have:= RSmap_spec w; rewrite /is_RStabpair /is_RSpair /RStabmap.
  case H : (RSmap w) => [P Q] /and3P [] -> /stdtab_of_yamP -> /eqP -> /=.
  by rewrite shape_stdtab_of_yam.
Qed.

Definition RStab w := RSTabPair (RStabmap_spec w).
Definition RStabinv (pair : rstabpair) :=
  let: (P, Q) := pqpair pair in RSmapinv2 (P, yam_of_stdtab Q).

Lemma bijRStab : bijective RStab.
Proof.
  split with (g := RStabinv); rewrite /RStab /RStabinv /RStabmap.
  - move=> w /=; have:= is_yam_RSmap2 w.
    case H : (RSmap w) => [P Q] /= Hyam.
    by rewrite stdtab_of_yamK; first by rewrite -H (RS_bij_1 w).
  - move=> [[P Q] H] /=; apply pqpair_inj => /=.
    move: H; rewrite /is_RStabpair => /and3P [] Htab Hstdtab Hshape //=.
    rewrite RS_bij_2.
    + by rewrite (yam_of_stdtabK Hstdtab).
    + by rewrite /is_RSpair Htab yam_of_stdtabP //= shape_yam_of_stdtab.
Qed.

End RobinsonSchensted.


Section Finset.

Variable n : nat.
Definition enum_stdtabn := [seq RS p | p <- enum_stdn n ].

Lemma enum_stdtabnE t : ((is_stdtab t) && (size_tab t == n)) = (t \in enum_stdtabn).
Proof.
  apply/(sameP idP); apply(iffP idP).
  + move/mapP => [] p; rewrite -enum_stdnE => /andP [] Hstd /eqP <- ->.
    by rewrite RSstdE Hstd size_RS.
  + rewrite /enum_stdtabn /is_stdtab => /andP [] /andP [] Htab Hstd Hsize.
    apply/mapP; exists (to_word t); last by apply esym; apply RS_tabE.
    by rewrite -enum_stdnE Hstd -size_to_word Hsize.
Qed.

Definition stdtabn := seq_sub_finType enum_stdtabn.

Lemma stdtabnP (s : stdtabn) : is_stdtab (val s).
Proof. case: s => s /=; by rewrite -enum_stdtabnE => /andP []. Qed.

Lemma size_sdtabn (s : stdtabn) : size_tab (val s) = n.
Proof. case: s => s /=; by rewrite -enum_stdtabnE => /andP [] _ /eqP. Qed.

End Finset.
