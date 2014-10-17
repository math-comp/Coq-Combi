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

Require Import subseq partition permuted ordtype schensted congr plactic greeninv std.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section StdRS.

Variable Alph : ordType.
Let Z := (inhabitant Alph).
Implicit Type s u v w : seq Alph.
Implicit Type p : seq nat.

Theorem std_plact u v : plactcongr u v -> plactcongr (std u) (std v).
Proof.
  have:= @plactcongr_equiv nat_ordType => /equivalence_relP [] Hrefl Htrans.
  move: v; apply gencongr_ind; first by apply Hrefl.
  move=> a b1 c b2 H Hplact.
  rewrite -(@Htrans (std (a ++ b1 ++ c))); last by rewrite -(Htrans _ _ H); apply Hrefl.
  move: Hplact {H} => /plactruleP.
  admit. (* TODO standardize the rules *)
Qed.

Theorem shape_RS_std u : shape (RS (std u)) = shape (RS u).
Proof.
  admit. (* TODO green invariants using specification of std by inversions *)
Qed.

Lemma shape_Qsymb (u : seq Alph) l i :
  shape_rowseq (RSmap (rcons u l)).2 = incr_nth (shape_rowseq (RSmap u).2) i ->
  (RSmap (rcons u l)).2 = i :: (RSmap u).2.
Proof.
  rewrite /RSmap rev_rcons /= -[RSmap_rev (rev u)]/(RSmap u).
  case HRS : (RSmap u) => [t0 rows].
  case Hins : (instabnrow t0 l) => [tr irow] /=.
  by move/incr_nth_inj ->.
Qed.

Lemma size_RSmap2 u : size ((RSmap u).2) = size u.
Proof.
  elim/last_ind: u => [//= | u un].
  rewrite /RSmap rev_rcons /=.
  case: (RSmap_rev (rev u)) => [t rows] /=.
  case: (instabnrow t un) => [tr nrow] /= ->.
  by rewrite size_rcons.
Qed.

End StdRS.

Theorem RSmap_std (T : ordType) (w : seq T) : (RSmap (std w)).2 = (RSmap w).2.
Proof.
  move Hn : (size w) => n.
  elim: n T w Hn => [/= | n IHn] T w; first by move/eqP/nilP => ->.
  case/lastP Hw : w => [//= | w' wn] Hn.
  have:= shape_RS_std (rcons w' wn).
  rewrite -!RSmapE !shape_RSmap_eq.
  case/lastP H : (std (rcons w' wn)) => [/= | st stn].
    exfalso; have:= eq_refl (@size nat [::]).
    by rewrite -{1}H size_std_rec size_rcons.
  case HRS : ((RSmap (rcons w' wn)).2) => [/= | iw yamw].
    exfalso; have:= eq_refl (@size nat [::]).
    by rewrite -{1}HRS size_RSmap2 size_rcons.
  have Hyamw : yamw = (RSmap w').2.
    move: HRS; rewrite /RSmap rev_rcons /=.
    case: (RSmap_rev (rev w')) => [t rows] /=.
    by case: (instabnrow t wn) => [tr nrow] /= [] _ ->.
  have Hsize : size w' = n by move: Hn => /eqP; rewrite size_rcons eqSS => /eqP.
  have /std_rconsK Hst : std (rcons w' wn) = std (rcons st stn) by rewrite -H std_stdE.
  rewrite Hyamw /= -(IHn _ _ Hsize).
  have Hsizest : size st = n.
    have := Hst; rewrite /std -{2}(size_std_rec (size st) st) => <-.
    by rewrite size_std_rec.
  rewrite Hst (IHn _ _ Hsizest).
  by apply shape_Qsymb.
Qed.


(*
Lemma is_tableau_reshape_std t :
 is_tableau t -> is_tableau (reshape (rev (shape t)) (std (to_word t))).
Proof.
  usefull ????
Qed.

Lemma is_tableau_std t : is_tableau t -> std (to_word t) = to_word (RS (std (to_word t))).
Proof.
  usefull ????
Qed.

Theorem std_RS w : to_word (RS (std w)) = std (to_word (RS w)).
Proof.
  rewrite (is_tableau_std (is_tableau_RS w)); congr (to_word _).
  apply /eqP; rewrite -plactic_RS.
  apply std_plact; by apply congr_RS.
Qed.


*)


