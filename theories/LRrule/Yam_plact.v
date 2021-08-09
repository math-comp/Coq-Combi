(** * Combi.LRrule.Yam_plact : Plactic classes and Yamanouchi words *)
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
(** * Plactic classes and Yamanouchi words

The goal of this file is to show that the Yamanouchi words of a given
evaluation form a plactic class.

- [yamtab sh] == the uniq Yamanouchi tableau of shape sh: the i-th line
                 contains only i's as in: 33 2222 11111 0000000.

The main result is [Corollary yam_plactic_shape]

[
  y =Pl z <-> (is_yam z /\ evalseq y = evalseq z).
]

We also show that for all partition [sh] the standardization defines a bijection
from Yamanouchi words of evaluation [sh] and a plactic class. In particular, it
is surjective. This is Theorem [plact_from_yam]:

[
  w =Pl std (hyper_yam sh) -> { y | is_yam_of_eval sh y & std y = w }.
]
****)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple finfun finset path bigop order.

Require Import tools partition Yamanouchi ordtype std tableau stdtab.
Require Import Schensted congr plactic Greene_inv stdplact.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.
Open Scope N.


Lemma is_part_incr_nthE sh i j :
  i.+1 < j -> is_part sh -> is_part (incr_nth (incr_nth sh j) i) ->
  is_part (incr_nth sh i) = is_part (incr_nth sh j).
Proof.
move=> Hij Hpart /is_partP [Hlastji Hpartij].
apply/idP/idP => /is_partP [H1 H2]; apply: (is_part_incr_nth Hpart) => /=.
- case H : j => [//= | j'] /=; subst j.
  move/(_ j'): Hpartij; rewrite !nth_incr_nth.
  rewrite eq_refl (ltn_eqF (ltnW Hij)).
  rewrite ltnS in Hij; rewrite (ltn_eqF Hij) /=.
  by rewrite eq_sym ltn_eqF //= !add0n /= add1n.
- case H : i => [//= | i'] /=; subst i.
  move/(_ i'): Hpartij; rewrite !nth_incr_nth.
  rewrite eq_refl (gtn_eqF (ltnW Hij)) (gtn_eqF (ltnW (ltnW Hij))).
  by rewrite eq_sym ltn_eqF //= !add0n /= add1n.
Qed.

Lemma is_part_incr_nth1E sh i :
  is_part sh ->
  is_part (incr_nth (incr_nth sh i.+1) i) = is_part (incr_nth sh i).
Proof.
move=> Hpart; apply/idP/idP => Hparti.
- apply (is_part_incr_nth Hpart) => /=.
  case: i Hparti => [//= | i] /is_partP [_ Hparti /=].
  move/(_ i): Hparti.
  rewrite !nth_incr_nth /= eq_refl.
  rewrite eq_sym ltn_eqF // eq_sym ltn_eqF //.
  have -> /= : (i.+2 == i) = false by elim i.
  by rewrite !add0n /= add1n.
- rewrite incr_nthC; apply (is_part_incr_nth Hparti) => /=.
  elim: sh i Hpart Hparti => [//= | s0 sh IHsh] /= i.
    by move=> _ /part_head_non0 Hhead; have -> : i = 0 by case: i Hhead.
  case: i => [| i] /=  /andP [Head Hp]; first by move=> _ ; move: Head; case sh.
  by move=> /andP [_ Hpi]; exact: IHsh.
Qed.

Lemma is_yam_plactic y : is_yam y -> forall w, y =Pl w -> is_yam w.
Proof.
move=> Hy; apply: gencongr_ind; first exact Hy.
elim => [/= | a0 aw /= IHaw].
- move=> b1 cw b2 H /plactruleP [] Hrew.
  + move: Hrew H => /plact1P [a] [b] [c] [].
    rewrite leEnat ltEnat /= => /andP [Hab Hbc] -> -> /=.
    set yc := (incr_nth (evalseq cw) b).
    move=> /and4P [H1 H2 Hpart ->]; rewrite Hpart.
    rewrite incr_nthC H1 !andbT /=.
    case (ltnP a.+1 c) => Hac; first by rewrite (is_part_incr_nthE Hac).
    have {}Hab : a = b.
      apply/eqP; rewrite eqn_leq Hab /= -ltnS.
      exact: (leq_trans Hbc).
    subst a.
    have {Hac}Hbc : c = b.+1 by apply/eqP; rewrite eqn_leq Hbc Hac.
    subst c.
    by rewrite -is_part_incr_nth1E.
  + move: Hrew H => /plact1iP [a] [b] [c] [].
    rewrite leEnat ltEnat /= => /andP [Hab Hbc] -> -> /=.
    set yc := (incr_nth (evalseq cw) b).
    move=> /and4P []; rewrite incr_nthC => H1 H2 Hpart Hyam.
    rewrite Hpart Hyam H1 !andbT /=.
    case (ltnP a.+1 c) => Hac; first by rewrite -(is_part_incr_nthE Hac Hpart).
    have {}Hab : a = b.
      apply/eqP; rewrite eqn_leq Hab /= -ltnS.
      exact: (leq_trans Hbc).
    subst a.
    have {Hac}Hbc : c = b.+1 by apply/eqP; rewrite eqn_leq Hbc Hac.
    subst c; subst yc.
    rewrite incr_nthC is_part_incr_nth1E; first exact Hpart.
    exact: is_part_eval_yam.
  + move: Hrew H => /plact2P [a] [b] [c] [].
    rewrite leEnat ltEnat /= => /andP [Hab Hbc] -> -> /=.
    move=> /and4P []; rewrite [(incr_nth (incr_nth _ a) c)]incr_nthC.
    move => H1 H2 Hpart Hyam.
    rewrite Hyam H1 H2 !andbT /= {H1}.
    case (ltnP a.+1 c) => Hac.
      by rewrite (is_part_incr_nthE Hac (is_part_eval_yam Hyam)).
    have {}Hbc : b = c.
      by apply/eqP; rewrite eqn_leq Hbc /=; exact: (leq_trans Hac).
    subst b.
    have {Hab}Hac : c = a.+1 by apply/eqP; rewrite eqn_leq Hac Hab.
    subst c.
    by rewrite -(is_part_incr_nth1E _ (is_part_eval_yam Hyam)).
  + move: Hrew H => /plact2iP [a] [b] [c] [].
    rewrite leEnat ltEnat /= => /andP [Hab Hbc] -> -> /=.
    move=> /and4P []; rewrite (incr_nthC _ a c) => H1 H2 Hpart Hyam.
    rewrite Hyam H1 H2 !andbT /=.
    case (ltnP a.+1 c) => Hac.
      by rewrite -(is_part_incr_nthE Hac (is_part_eval_yam Hyam)).
    have {}Hbc : b = c.
      by apply/eqP; rewrite eqn_leq Hbc /=; exact: (leq_trans Hac).
    subst b.
    have {Hab}Hac : c = a.+1 by apply/eqP; rewrite eqn_leq Hac Hab.
    subst c.
    apply (is_part_incr_nth (is_part_eval_yam Hyam)) => /=.
    move: H1 => /is_partP [_ /(_ a)].
    by rewrite !nth_incr_nth !eq_refl [_.+1 == _]eq_sym  ltn_eqF.
- move=> b1 cw b2 /andP [Hpart Hyam] Hrew.
  rewrite (IHaw _ _ _ Hyam Hrew) andbT.
  suff -> : (evalseq (aw ++ b2 ++ cw)) = (evalseq (aw ++ b1 ++ cw)) by [].
  rewrite -!evalseq_countE /evalseq_count /=.
  have Hperm : perm_eq (aw ++ b1 ++ cw) (aw ++ b2 ++ cw).
    apply: plact_homog; apply: plact_is_congr; apply: rule_gencongr; exact Hrew.
  rewrite !foldr_maxn (perm_big _ Hperm) /=.
  apply eq_map => i /=.
  by move: Hperm => /permP ->.
Qed.

(** * The Yamanouchi tableau *)
Fixpoint yamtab_rec i sh :=
  if sh is s0 :: s then
    nseq s0 i :: yamtab_rec (i.+1) s
  else [::].
Definition yamtab := yamtab_rec 0.

Lemma shape_yamtab sh : shape (yamtab sh) = sh.
Proof.
rewrite /yamtab; move: (0) => i.
elim: sh i => [//= | s0 sh IHsh] /= i.
by rewrite size_nseq IHsh.
Qed.

Lemma to_word_yamtab sh : to_word (yamtab sh) = hyper_yam sh.
Proof.
elim/last_ind: sh => [//= | sh sn] /=.
have -> : yamtab (rcons sh sn) = rcons (yamtab sh) (nseq sn (size sh)).
  rewrite /yamtab -[size sh]add0n; move: 0.
  elim: sh => [//= | s0 sh IHsh] /= i; first by rewrite addn0.
  by rewrite IHsh addSnnS.
rewrite /hyper_yam to_word_rcons rev_rcons /= => ->.
by rewrite size_rev.
Qed.

Lemma yamtabP sh : is_part sh -> is_tableau (yamtab sh).
Proof.
rewrite /yamtab; move: 0.
elim: sh => [//= | s0 sh IHsh] i Hpart.
have /= Hs0 := part_head_non0 Hpart.
apply /and4P; repeat split.
- by move: Hs0; apply contra; case s0.
- move: Hs0 {Hpart}; case: s0 => [//= | l] _.
  by elim: l => [//= | l] /= ->; rewrite andbT.
- have -> : head [::] (yamtab_rec i.+1 sh) = nseq (head 0 sh) i.+1.
    by case sh => [//= | l0 l] /=.
  move: Hpart => /= /andP [Hhead _].
  move: Hhead; case: sh {IHsh} => [//= | s1 /= _] Hs.
  apply /dominateP; split; first by rewrite !size_nseq.
  move=> j; rewrite size_nseq !nth_nseq => Hj.
  by rewrite Hj (leq_trans Hj Hs) ltEnat /=.
- by move: Hpart => /= /andP [_]; exact: IHsh.
Qed.

Lemma yamtab_rcons sh sn :
  yamtab (rcons sh sn) = rcons (yamtab sh) (nseq sn (size sh)).
Proof.
rewrite /yamtab -[size sh]addn0.
move: (0) => i.
elim: sh i => [//= | s0 sh IHsh] /= i .
by rewrite IHsh addSnnS.
Qed.

Lemma yamtab_unique t :
  is_tableau t -> is_yam (to_word t) -> t = yamtab (shape t).
Proof.
elim/last_ind: t => [//= | t tn IHt] /=.
rewrite to_word_rcons /= /shape map_rcons yamtab_rcons -/shape => Htab Hyam.
have {IHt} Hrec := IHt (is_tableau_rconsK Htab) (is_yam_catr Hyam).
rewrite -Hrec; congr (rcons t _).
have := is_part_sht Htab.
rewrite /shape map_rcons -/shape.
move: Hrec; move: (shape t) => sh Ht; subst t.
case/lastP: sh Htab Hyam => [| sh sn] /=.
  move=> /and3P [_ Hrow _].
  rewrite /yamtab /= cats0 => /last_yam Hlast _.
  case: tn Hrow Hlast => [//= | l0 tn] /=.
  elim: tn l0 => [l0 _ /= -> //= | l1 t' IHt] /= l0 /andP [Hl0l1 Hpath] Hlast.
  have {IHt Hpath Hlast} [] := IHt l1 Hpath Hlast => Hl1 <-.
  by move: Hl0l1; rewrite Hl1 leEnat leqn0 => /eqP ->.
rewrite {1}yamtab_rcons -2!cats1 -catA /=.
move => /is_tableau_catr /= /and4P [].
case: sn => [//= | sn] /= _ _ Hdom /and3P [Hrow Hn2 _].
rewrite to_word_yamtab size_rcons.
case/lastP: tn Hrow Hn2 Hdom => [//=| tn ln] /= _ Hrow Hdom.
rewrite -{1}cats1 -catA cat1s.
move=> /is_yam_catr /= /andP [Hpart _] /is_part_rconsK Hp0.
move: Hpart; rewrite (evalseq_hyper_yam Hp0) => Hp1.
have Hln : ln <= (size sh).+1.
  elim: sh ln Hp0 Hp1 {Hdom Hrow} => [| s0 sh IHsh] /= ln.
    case: ln => [//= | ln] _ /= /andP [_ /part_head_non0].
    by case: ln.
  case: ln => [//= | ln].
  rewrite ltnS /= => /andP [_ H1] /andP [_ H2].
  exact: IHsh.
case: tn Hrow Hdom {Hp0 Hp1} => [_ /= | l0 tn].
  move=> /dominateP [_ Hdom]; congr [:: _].
  apply/eqP; rewrite eqn_leq Hln /=.
  have {Hdom} /= := Hdom 0 (ltn0Sn _).
  by rewrite ltEnat.
rewrite rcons_cons => Hrow /dominateP [_ Hdom].
have {Hdom} /= := Hdom 0 (ltn0Sn _).
rewrite ltEnat => Hl0.
elim: tn l0 Hl0 Hrow => [/= | l1 tn /= IHtn] l0 Hl0; rewrite leEnat => /andP [].
  move=> Hl0ln _.
  have {}Hl0 : l0 = (size sh).+1.
    apply/eqP; rewrite eqn_leq Hl0 andbT.
    exact: (leq_trans Hl0ln).
  rewrite Hl0; congr [:: _; _].
  apply/eqP; rewrite eqn_leq Hln /=.
  by rewrite -Hl0.
move=> Hl0l1 Hpath.
have Hrec :=  (IHtn l1 (leq_trans Hl0 Hl0l1) Hpath).
rewrite -Hrec; congr (_ :: _).
apply/eqP; rewrite eqn_leq Hl0 andbT.
by move: Hrec => [<- _].
Qed.

Corollary RS_yam_RS y : is_yam y -> RS y = yamtab (shape (RS y)).
Proof.
move=> Hyam.
exact (yamtab_unique (is_tableau_RS y) (is_yam_plactic Hyam (congr_RS y))).
Qed.

Lemma shape_RS_yam y : is_yam y -> shape (RS y) = evalseq y.
Proof.
move => Hyam.
have:= congr_RS y => /plact_homog.
rewrite perm_evalseq => /eqP ->.
rewrite {2}(RS_yam_RS Hyam) to_word_yamtab evalseq_hyper_yam //=.
by apply is_part_sht; exact: is_tableau_RS.
Qed.

Lemma RS_yam y : is_yam y -> RS y = yamtab (evalseq y).
Proof. by move => Hyam; rewrite (RS_yam_RS Hyam) (shape_RS_yam Hyam). Qed.

Theorem yam_plactic_hyper y : is_yam y -> y =Pl hyper_yam (evalseq y).
Proof.
move => Hyam; rewrite -(shape_RS_yam Hyam) -to_word_yamtab.
have HPly := congr_RS y.
by rewrite -(yamtab_unique (is_tableau_RS y) (is_yam_plactic Hyam HPly)).
Qed.

Corollary yam_plactic_shape y z :
  is_yam y -> ( y =Pl z <-> (is_yam z /\ evalseq y = evalseq z)).
Proof.
move=> Hyam; split.
- move=> HPl; split; first exact (is_yam_plactic Hyam HPl).
  rewrite -(shape_RS_yam Hyam) -(shape_RS_yam (is_yam_plactic Hyam HPl)).
  exact: plactic_shapeRS.
- move=> [Hyamz Hsh].
  apply Sch_plact.
  by rewrite (RS_yam Hyam) (RS_yam Hyamz) Hsh.
Qed.


(** * Yamanouchi words, standardization and plactic classes*)
Lemma yam_std_inj : {in is_yam &, injective std}.
Proof.
move=> y w /=; rewrite !unfold_in -/is_yam => Hy Hw Hstd.
apply perm_stdE; last exact Hstd.
rewrite perm_evalseq.
rewrite -(shape_RS_yam Hy) -(shape_RS_yam Hw).
rewrite -(shape_RS_std y) -(shape_RS_std w).
by rewrite Hstd.
Qed.

Lemma auxbijP p (y : yameval p) : is_yam_of_eval p ((RSmap y).2).
Proof.
rewrite /is_yam_of_eval is_yam_RSmap2 /=.
rewrite -shape_RSmap_eq RSmapE.
by rewrite (shape_RS_yam (yamevalP y)) eval_yameval.
Qed.

Local Definition auxbij (p : intpart) (y : yameval p) : yameval p :=
  YamEval (auxbijP y).

Lemma auxbij_inj (p : intpart) : injective (@auxbij p).
Proof.
move=> y z /(congr1 val) /= => HRS2.
have HRS1 : RS (std y) = RS (std z).
  apply/eqP; rewrite -plactic_RS.
  apply: std_plact; rewrite (yam_plactic_shape _ (yamevalP y)).
  split; first exact: yamevalP.
  by rewrite !eval_yameval.
apply val_inj; apply perm_stdE => /=.
- by rewrite perm_evalseq !eval_yameval.
- rewrite -[std y]RSmapK -[std z]RSmapK /=.
  have RSE (x : seq nat) : RSmap x = (RS x, (RSmap x).2).
    by rewrite -RSmapE; case RSmap.
  by rewrite [RSmap (std y)]RSE [RSmap (std z)]RSE HRS1 !RSmap_std HRS2.
Qed.

Local Definition auxbij_inv (p : intpart) := invF (@auxbij_inj p).

Theorem plact_from_yam sh w :
  is_part sh ->
  w =Pl std (hyper_yam sh) ->
  { y | is_yam_of_eval sh y & std y = w }.
Proof.
move=> Hsh.
have := (plactic_RS w (std (hyper_yam sh))) => [] [H _].
move=> /H => /eqP HRS.
pose Sh := IntPart Hsh.
have Hyam : is_yam_of_eval Sh (RSmap w).2.
  rewrite /is_yam_of_eval is_yam_RSmap2 /=.
  rewrite -shape_RSmap_eq RSmapE HRS shape_RS_std.
  by rewrite (shape_RS_yam (hyper_yamP Hsh)) evalseq_hyper_yam.
pose yimg := YamEval Hyam.
have Hw : w = RSmapinv2 (RS (std (hyper_yam sh)), val yimg).
  rewrite -{1}[w]RSmapK.
  have -> : RSmap w = ((RSmap w).1, (RSmap w).2) by case RSmap.
  by rewrite RSmapE HRS.
pose y := (@auxbij_inv Sh yimg).
exists y.
- by rewrite /is_yam_of_eval yamevalP eval_yameval /=.
- rewrite -[LHS]RSmapK -[RHS]RSmapK.
  have RSE (x : seq nat) : RSmap x = (RS x, (RSmap x).2).
    by rewrite -RSmapE; case RSmap.
  rewrite RSE [RSmap w]RSE HRS.
  congr (RSmapinv2 (_, _)).
  + have := stdtab_of_yamP (hyper_yamP Hsh); rewrite /is_stdtab => /andP [Htab _].
    apply/eqP; rewrite -plactic_RS.
    apply: std_plact.
    rewrite (yam_plactic_shape _ (yamevalP _)); split; first exact: hyper_yamP.
    by rewrite eval_yameval evalseq_hyper_yam.
  + by rewrite RSmap_std (_ : (RSmap y).2 = @auxbij Sh y) // f_invF.
Qed.
