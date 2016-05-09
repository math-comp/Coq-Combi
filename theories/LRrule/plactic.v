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
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
From mathcomp Require Import finset perm path.
Require Import tools partition ordtype tableau stdtab Schensted congr.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bool.

Import OrdNotations.

Section Defs.

Variable Alph : inhOrdType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w : word.

Definition plact1 :=
  fun s => match s return seq word with
             | [:: a; c; b] => if (a <= b < c)%Ord then [:: [:: c; a; b]] else [::]
             | _ => [::]
           end.

Definition plact1i :=
  fun s => match s return seq word with
             | [:: c; a; b] => if (a <= b < c)%Ord then [:: [:: a; c; b]] else [::]
             | _ => [::]
           end.

Definition plact2 :=
  fun s => match s return seq word with
             | [:: b; a; c] => if (a < b <= c)%Ord then [:: [:: b; c; a]] else [::]
             | _ => [::]
           end.

Definition plact2i :=
  fun s => match s return seq word with
             | [:: b; c; a] => if (a < b <= c)%Ord then [:: [:: b; a; c]] else [::]
             | _ => [::]
           end.

Lemma plact1P u v :
  reflect (exists a b c,
             [/\ (a <= b < c)%Ord, u = [:: a; c; b] & v = [:: c; a; b] ] )
          (v \in plact1 u).
Proof using .
  apply: (iffP idP).
  + case: u => [//=|u0[//=|u1[//=|u2[]//=]]]; case H : ((u0 <= u2 < u1)%Ord).
    - rewrite mem_seq1 => /eqP ->; by exists u0, u2, u1.
    - by rewrite in_nil.
  + move=> [] a [] b [] c [] H -> ->; by rewrite /= H mem_seq1 eq_refl.
Qed.

Lemma plact1iP u v :
  reflect (exists a b c,
             [/\ (a <= b < c)%Ord, v = [:: a; c; b] & u = [:: c; a; b] ] )
          (v \in plact1i u).
Proof using .
  apply: (iffP idP).
  + case: u => [//=|u0[//=|u1[//=|u2[]//=]]]; case H : ((u1 <= u2 < u0)%Ord).
    - rewrite mem_seq1 => /eqP ->; by exists u1, u2, u0.
    - by rewrite in_nil.
  + move=> [] a [] b [] c [] H -> ->; by rewrite /= H mem_seq1 eq_refl.
Qed.


Lemma plact2P u v :
  reflect (exists a b c,
             [/\ (a < b <= c)%Ord, u = [:: b; a; c] & v = [:: b; c; a] ] )
          (v \in plact2 u).
Proof using .
  apply: (iffP idP).
  + case: u => [//=|u0[//=|u1[//=|u2[]//=]]]; case H : ((u1 < u0 <= u2)%Ord).
    - rewrite mem_seq1 => /eqP ->; by exists u1, u0, u2.
    - by rewrite in_nil.
  + move=> [] a [] b [] c [] H -> ->; by rewrite /= H mem_seq1 eq_refl.
Qed.

Lemma plact2iP u v :
  reflect (exists a b c,
             [/\ (a < b <= c)%Ord, v = [:: b; a; c] & u = [:: b; c; a] ] )
          (v \in plact2i u).
Proof using .
  apply: (iffP idP).
  + case: u => [//=|u0[//=|u1[//=|u2[]//=]]]; case H : ((u2 < u0 <= u1)%Ord).
    - rewrite mem_seq1 => /eqP ->; by exists u2, u0, u1.
    - by rewrite in_nil.
  + move=> [] a [] b [] c [] H -> ->; by rewrite /= H mem_seq1 eq_refl.
Qed.

Lemma plact1I u v : u \in plact1 v <-> v \in plact1i u.
Proof using .
  split => [/plact1P | /plact1iP] [] a [] b [] c [] H -> -> => /=;
    by rewrite H mem_seq1 eq_refl.
Qed.

Lemma plact2I u v : u \in plact2 v <-> v \in plact2i u.
Proof using .
  split => [/plact2P | /plact2iP] [] a [] b [] c [] H -> -> => /=;
    by rewrite H mem_seq1 eq_refl.
Qed.

Definition plactrule := [fun s => plact1 s ++ plact1i s ++ plact2 s ++ plact2i s].

Lemma plactruleP u v :
  reflect ([\/ v \in plact1 u, v \in plact1i u, v \in plact2 u | v \in plact2i u ])
          (v \in plactrule u).
Proof using .
  apply: (iffP idP).
  + by rewrite /plactrule /= !mem_cat => /or4P.
  + by rewrite /plactrule /= !mem_cat => H; apply/or4P.
Qed.

Lemma plactrule_sym u v : v \in (plactrule u) -> u \in (plactrule v).
Proof using .
  move/plactruleP => [] /=; rewrite !mem_cat.
  by rewrite plact1I => ->; rewrite !orbT.
  by rewrite -plact1I => ->.
  by rewrite plact2I => ->; rewrite !orbT.
  by rewrite -plact2I => ->; rewrite !orbT.
Qed.

Lemma plact1_homog : forall u : word, all (perm_eq u) (plact1 u).
Proof using .
  move=> u; apply/allP => v /plact1P.
  move=> [] a [] b [] c [] /andP [] H1 H2 -> -> /=; rewrite /perm_eq /=.
  rewrite !eq_refl ![c == a]eq_sym ![c == b]eq_sym ![b == a]eq_sym /=.
  case Hab : (a == b);
      by rewrite (ltnX_eqF H2) (ltnX_eqF (leqX_ltnX_trans H1 H2)) !eq_refl /=.
Qed.

Lemma plact1i_homog : forall u : word, all (perm_eq u) (plact1i u).
Proof using .
  move=> u; apply/allP => v /plact1iP.
  move=> [] a [] b [] c [] /andP [] H1 H2 -> -> /=; rewrite /perm_eq /=.
  rewrite !eq_refl ![c == a]eq_sym ![c == b]eq_sym ![b == a]eq_sym /=.
  case Hab : (a == b);
      by rewrite (ltnX_eqF H2) (ltnX_eqF (leqX_ltnX_trans H1 H2)) !eq_refl /=.
Qed.

Lemma plact2_homog : forall u : word, all (perm_eq u) (plact2 u).
Proof using .
  move=> u; apply/allP => v /plact2P.
  move=> [] a [] b [] c [] /andP [] H1 H2 -> -> /=; rewrite /perm_eq /=.
  rewrite !eq_refl ![c == a]eq_sym ![c == b]eq_sym ![b == a]eq_sym /=.
  case Hab : (b == c);
      by rewrite (ltnX_eqF H1) (ltnX_eqF (ltnX_leqX_trans H1 H2)) !eq_refl /=.
Qed.

Lemma plact2i_homog : forall u : word, all (perm_eq u) (plact2i u).
Proof using .
  move=> u; apply/allP => v /plact2iP.
  move=> [] a [] b [] c [] /andP [] H1 H2 -> -> /=; rewrite /perm_eq /=.
  rewrite !eq_refl ![c == a]eq_sym ![c == b]eq_sym ![b == a]eq_sym /=.
  case Hab : (b == c);
      by rewrite (ltnX_eqF H1) (ltnX_eqF (ltnX_leqX_trans H1 H2)) !eq_refl /=.
Qed.

Lemma plactrule_homog : forall u : word, all (perm_eq u) (plactrule u).
Proof using .
  move=> u; by rewrite !all_cat plact1_homog plact1i_homog plact2_homog plact2i_homog.
Qed.

Definition plactcongr := gencongr_multhom plactrule_homog.

Lemma plact_equiv : equivalence_rel plactcongr.
Proof using . apply: gencongr_equiv; exact: plactrule_sym. Qed.

Lemma plact_refl : reflexive plactcongr.
Proof using . have:= plact_equiv; by rewrite equivalence_relP => [] [] Hrefl Hltr. Qed.

Lemma plact_sym : symmetric plactcongr.
Proof using .
  have:= plact_equiv; rewrite equivalence_relP => [] [] Hrefl Hltr.
  by move=> i j; apply/idP/idP => /Hltr <-.
Qed.

Lemma plact_ltrans : left_transitive plactcongr.
Proof using . have:= plact_equiv; by rewrite equivalence_relP => [] [] Hrefl Hltr. Qed.

Lemma plact_trans : transitive plactcongr.
Proof using .
  have:= plact_equiv; rewrite equivalence_relP => [] [] Hrefl Hltr.
  by move=> i j k => /Hltr <-.
Qed.

Lemma plact_is_congr : congruence_rel plactcongr.
Proof using . apply: gencongr_is_congr; exact: plactrule_sym. Qed.

Definition plact_cons := congr_cons plact_is_congr.
Definition plact_rcons := congr_rcons plact_is_congr.
Definition plact_catl := congr_catl plact_is_congr.
Definition plact_catr := congr_catr plact_is_congr.
Definition plact_cat := congr_cat plact_is_congr plact_equiv.

Lemma plact_homog u v : plactcongr u v -> perm_eq u v.
Proof using . exact: gencongr_invar. Qed.

Lemma size_plact u v : plactcongr u v -> size u = size v.
Proof using . by move/plact_homog/perm_eq_size. Qed.

End Defs.

Notation "a =Pl b" := (plactcongr a b) (at level 70).
Hint Resolve plact_refl.

Section RowsAndCols.

Variable Alph : inhOrdType.
Let word := seq Alph.
Implicit Type u v w : word.

Lemma plact_row u v : is_row u -> u =Pl v -> u = v.
Proof using .
  move=> Hrowu; move: v; apply: gencongr_ind => [//= |] x y1 z y2 Hu /plactruleP [].
  - move/plact1P => [] a [] b [] c [] /andP [] Hab Hbc Hy _; exfalso.
    move: Hrowu; rewrite Hu Hy => /is_row_catR/is_row_catL /= /and3P [] _.
    by rewrite leqXNgtnX Hbc.
  - move/plact1iP => [] a [] b [] c [] /andP [] Hab Hbc _ Hy; exfalso.
    move: Hrowu; rewrite Hu Hy => /is_row_catR/is_row_catL /= /and3P [].
    by rewrite leqXNgtnX (leqX_ltnX_trans Hab Hbc).
  - move/plact2P => [] a [] b [] c [] /andP [] Hab Hbc Hy _; exfalso.
    move: Hrowu; rewrite Hu Hy => /is_row_catR/is_row_catL /= /and3P [].
    by rewrite leqXNgtnX Hab.
  - move/plact2iP => [] a [] b [] c [] /andP [] Hab Hbc _ Hy; exfalso.
    move: Hrowu; rewrite Hu Hy => /is_row_catR/is_row_catL /= /and3P [] _.
    by rewrite leqXNgtnX (ltnX_leqX_trans Hab Hbc).
Qed.

Lemma sorted_center u v w :
  sorted (@gtnX Alph) (u ++ v ++ w) -> sorted (@gtnX Alph) v.
Proof using .
  rewrite /sorted; case: u => [| u0 u] /=.
    case: v => [//= | v0 v] /=.
    by rewrite cat_path => /andP [].
  case: v => [//= | v0 v] /=.
  rewrite !cat_path => /andP [] /= _ /andP [] _.
  by rewrite cat_path => /andP [].
Qed.

Lemma plact_col u v : sorted (@gtnX Alph) u -> u =Pl v -> u = v.
Proof using .
  move=> Hcolu; move: v; apply: gencongr_ind => [//= |] x y1 z y2 Hu /plactruleP [].
  - move/plact1P => [] a [] b [] c [] /andP [] Hab Hbc Hy _; exfalso.
    move: Hcolu; rewrite Hu Hy => /sorted_center /= /and3P [].
    by rewrite ltnXNgeqX (leqX_trans Hab (ltnXW Hbc)).
  - move/plact1iP => [] a [] b [] c [] /andP [] Hab Hbc _ Hy; exfalso.
    move: Hcolu; rewrite Hu Hy => /sorted_center /= /and3P [] _.
    by rewrite ltnXNgeqX Hab.
  - move/plact2P => [] a [] b [] c [] /andP [] Hab Hbc Hy _; exfalso.
    move: Hcolu; rewrite Hu Hy => /sorted_center /= /and3P [] _.
    by rewrite ltnXNgeqX (leqX_trans (ltnXW Hab) Hbc).
  - move/plact2iP => [] a [] b [] c [] /andP [] Hab Hbc _ Hy; exfalso.
    move: Hcolu; rewrite Hu Hy => /sorted_center /= /and3P [].
    by rewrite ltnXNgeqX Hbc.
Qed.

End RowsAndCols.


Section Rev.

Variable Alph : inhOrdType.
Let word := seq Alph.
Implicit Type u v w : word.

Lemma plact_uniq_rev u v : uniq u -> u =Pl v -> rev u =Pl rev v.
Proof using .
  move=> Huniq.
  have {Huniq} Huniq x y z : rev u =Pl rev (x ++ y ++ z) -> uniq y.
    move=> Hpl; have : uniq (x ++ y ++ z).
      rewrite -rev_uniq -(perm_eq_uniq (s1 := rev u)) ?rev_uniq //.
      exact: plact_homog.
    by rewrite !cat_uniq => /and4P [] _ _.
  move: v; apply: gencongr_ind => [| x y1 z y2 Hv /plactruleP []] /=;
      first exact: plact_refl.
  - move/plact1P => [] a [] b [] c [] /andP [] Hab Hbc Hy1 Hy2.
    apply (plact_trans Hv); rewrite !rev_cat -!catA; apply: plact_is_congr.
    rewrite Hy1 Hy2 /rev /=; apply rule_gencongr.
    apply/plactruleP/or4P => /=.
    move: Hv => /Huniq; rewrite Hy1 /= => /andP [].
    rewrite mem_seq2 negb_or => /andP [] _ Hanb _.
    by rewrite !ltnX_neqAleqX Hab Hanb (ltnXW Hbc) /= !mem_seq1 eq_refl ?orbT.
  - move/plact1iP => [] a [] b [] c [] /andP [] Hab Hbc Hy2 Hy1.
    apply (plact_trans Hv); rewrite !rev_cat -!catA; apply: plact_is_congr.
    rewrite Hy1 Hy2 /rev /=; apply rule_gencongr.
    apply/plactruleP/or4P => /=.
    move: Hv => /Huniq; rewrite Hy1 /= => /and3P [] _.
    rewrite mem_seq1 => Hanb _.
    by rewrite !ltnX_neqAleqX Hab Hanb (ltnXW Hbc) /= !mem_seq1 eq_refl ?orbT.
  - move/plact2P => [] a [] b [] c [] /andP [] Hab Hbc Hy1 Hy2.
    apply (plact_trans Hv); rewrite !rev_cat -!catA; apply: plact_is_congr.
    rewrite Hy1 Hy2 /rev /=; apply rule_gencongr.
    apply/plactruleP/or4P => /=.
    move: Hv => /Huniq; rewrite Hy1 /= => /andP [].
    rewrite mem_seq2 negb_or => /andP [] _ Hbnc _.
    by rewrite !ltnX_neqAleqX Hbc Hbnc (ltnXW Hab) /= !mem_seq1 eq_refl ?orbT.
  - move/plact2iP => [] a [] b [] c [] /andP [] Hab Hbc Hy2 Hy1.
    apply (plact_trans Hv); rewrite !rev_cat -!catA; apply: plact_is_congr.
    rewrite Hy1 Hy2 /rev /=; apply rule_gencongr.
    apply/plactruleP/or4P => /=.
    move: Hv => /Huniq; rewrite Hy1 /= => /and3P [].
    rewrite mem_seq2 negb_or => /andP [] Hbnc _ _ _.
    by rewrite !ltnX_neqAleqX Hbc Hbnc (ltnXW Hab) /= !mem_seq1 eq_refl ?orbT.
Qed.

Lemma plact_uniq_revE u v : uniq u -> (u =Pl v) = (rev u =Pl rev v).
Proof using .
  move=> Hu; apply/idP/idP; first exact: plact_uniq_rev.
  rewrite -{2}(revK u) -{2}(revK v).
  apply: plact_uniq_rev; by rewrite rev_uniq.
Qed.

End Rev.

Section DualRule.

Variable Alph : inhOrdType.
Let word := seq Alph.

Notation Dual := (dual_inhOrdType Alph).
Implicit Type u v w : word.

Definition revdual := [fun s : seq Alph => rev s : seq Dual].
Definition from_revdual := [fun s : seq Dual => (rev s) : seq Alph].

Lemma revdualK : cancel revdual from_revdual.
Proof using . move=> u; by rewrite /= revK. Qed.

Lemma from_revdualK : cancel from_revdual revdual.
Proof using . move=> u; by rewrite /= revK. Qed.

Lemma size_revdual u : size u = size (revdual u).
Proof using . by rewrite /= size_rev. Qed.

Lemma plact2dual u v : u \in plact2 v = (revdual u \in plact1 (revdual v)).
Proof using .
  apply/idP/idP.
  + move /plact2P => [] a [] b [] c [] Habc -> ->.
    by rewrite /revdual /= (dual_leqX c b) (dual_ltnX b a) andbC Habc /rev /= mem_seq1.
  + move /plact1P => [] a' [] b' [] c' [] Habc'.
    rewrite /revdual /= => /(congr1 from_revdual) /= H1 /(congr1 from_revdual) /= H2.
    move: H1 H2; rewrite !revK /rev => -> -> /=.
    by rewrite -dual_leqX -dual_ltnX andbC Habc' /= mem_seq1.
Qed.

Lemma plact1dual u v : u \in plact1 v = (revdual u \in plact2 (revdual v)).
Proof using .
  apply/idP/idP.
  + move /plact1P => [] a [] b [] c [] Habc -> ->.
    by rewrite /revdual /= (dual_leqX b a) (dual_ltnX c b) andbC Habc /rev /= mem_seq1.
  + move /plact2P => [] a' [] b' [] c' [] Habc'.
    rewrite /revdual /= => /(congr1 from_revdual) /= H1 /(congr1 from_revdual) /= H2.
    move: H1 H2; rewrite !revK => -> -> /=.
    by rewrite -dual_leqX -dual_ltnX andbC Habc' /= mem_seq1.
Qed.

Lemma plact1idual u v : u \in plact1i v = (revdual u \in plact2i (revdual v)).
Proof using . apply/idP/idP; by rewrite -plact1I -plact2I plact1dual. Qed.

Lemma plact2idual u v : u \in plact2i v = (revdual u \in plact1i (revdual v)).
Proof using . apply/idP/idP; by rewrite -plact1I -plact2I plact2dual. Qed.

End DualRule.

Arguments revdual [Alph].
Arguments from_revdual [Alph].

Section PlactDual.

Variable Alph : inhOrdType.
Let word := seq Alph.

Let Dual := dual_inhOrdType Alph.
Implicit Type u v w : word.

Theorem plact_revdual u v : u =Pl v -> revdual u =Pl revdual v.
Proof using .
  move: v; apply: gencongr_ind; first exact: plact_refl.
  move=> a b1 c b2 Hu Hplact.
  move: Hu => /plact_trans; apply => {u}.
  rewrite /revdual /= !rev_cat.
  apply: plact_catl; apply: plact_catr.
  apply: rule_gencongr => /=; move: Hplact => /plactruleP [].
  + rewrite !mem_cat plact1dual /revdual /= => -> ; by rewrite /= !orbT.
  + rewrite !mem_cat plact1idual /revdual /= => -> ; by rewrite /= !orbT.
  + rewrite !mem_cat plact2dual /revdual /= => -> ; by rewrite /=.
  + rewrite !mem_cat plact2idual /revdual /= => -> ; by rewrite /= !orbT.
Qed.

Theorem plact_from_revdual (u v : seq Dual) :
  u =Pl v -> from_revdual u =Pl from_revdual v.
Proof using .
  move: v; apply: (@gencongr_ind Dual); first exact: plact_refl.
  move=> a b1 c b2 Hu Hplact.
  move: Hu => /plact_trans; apply => {u}.
  rewrite /from_revdual /= !rev_cat.
  apply: plact_catl. apply: plact_catr.
  apply: rule_gencongr => /=.
  move: Hplact; rewrite -{1}[b1]from_revdualK -{1}[b2]from_revdualK => /plactruleP [].
  + rewrite !mem_cat -plact2dual /from_revdual /= => ->; by rewrite /= !orbT.
  + rewrite !mem_cat -plact2idual /from_revdual /= => -> ; by rewrite /= !orbT.
  + rewrite !mem_cat -plact1dual /from_revdual /= => -> ; by rewrite /=.
  + rewrite !mem_cat -plact1idual /from_revdual /= => -> ; by rewrite /= !orbT.
Qed.

Theorem plact_dualE u v : u =Pl v <-> revdual u =Pl revdual v.
Proof using .
  split; first exact: plact_revdual.
  rewrite -{2}[u]revdualK -{2}[v]revdualK; exact: plact_from_revdual.
Qed.

Theorem plact_from_dualE (u v : seq Dual) :
  u =Pl v <-> from_revdual u =Pl from_revdual v.
Proof using .
  split; first exact: plact_from_revdual.
  move /plact_revdual; by rewrite !from_revdualK.
Qed.

End PlactDual.

Section RSToPlactic.

Variable Alph : inhOrdType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Lemma rcons_rcons w a b : rcons (rcons w a) b = w ++ [:: a; b].
Proof using . by rewrite -!cats1 -catA cat1s. Qed.

Lemma congr_row_1 r b l :
  is_row (rcons r l) -> l <A b -> rcons (rcons r b) l =Pl b :: rcons r l.
Proof using .
  elim/last_ind: r l => [| r rn IHr] l Hrow Hl.
    rewrite /=; exact: plact_refl.
  have:= is_row_last Hrow; rewrite last_rcons => Hrnl.
  apply (@plact_trans _ (rcons (rcons (rcons r b) rn) l)).
  - rewrite !rcons_rcons -!cats1 -!catA !cat1s.
    apply: plact_catr; apply: rule_gencongr => /=.
    by rewrite Hl Hrnl !mem_cat !mem_seq1 eq_refl.
  - rewrite -rcons_cons; apply: plact_rcons.
    apply: (IHr _ (is_row_rconsK Hrow)).
    exact: leqX_ltnX_trans Hrnl Hl.
Qed.

Lemma congr_row_2 a r l :
  is_row (a :: r) -> l <A a -> a :: rcons r l =Pl a :: l :: r.
Proof using .
  elim/last_ind: r => [_ _ //= | r rn]; first exact: plact_refl.
  case/lastP: r => [_ /=| r rn1].
  - move/andP => [] Harn _ Hla; apply: rule_gencongr => //=.
    by rewrite Harn Hla !mem_cat !mem_seq1 eq_refl /= !orbT.
  - move=> IH; rewrite -rcons_cons => Hrow Hla.
    move/(_ (is_row_rconsK Hrow) Hla): IH => IH.
    apply (@plact_trans  _ (a :: rcons (rcons (rcons r rn1) l) rn)) => //.
    * apply: plact_cons; rewrite !rcons_rcons -!cats1 -!catA.
      apply: plact_catr => /=; apply: rule_gencongr.
      have:= head_leq_last_row (is_row_rconsK Hrow); rewrite last_rcons => Harn1.
      have:= is_row_last Hrow. rewrite -rcons_cons last_rcons => Hrn1rn.
      by rewrite /= Hrn1rn (ltnX_leqX_trans Hla Harn1) !mem_cat !mem_seq1 eq_refl /= !orbT.
    * move: IH; rewrite -!rcons_cons; exact: plact_rcons.
Qed.

Lemma set_nth_LxR L c R l pos :
  (size L) = pos -> set_nth l (L ++ c :: R) pos l = L ++ l :: R.
Proof using .
  move Hr : (L ++ c :: R) => r Hsize.
  have Hpos : pos < size r
    by rewrite -Hsize -Hr size_cat /= -addSnnS -{1}[(size L).+1]addn0 leq_add2l.
  have Hsizeset : size (set_nth l r pos l) = size r.
    rewrite size_set_nth maxnC /maxn ltnS.
    by move: Hpos; rewrite ltnNge => /negbTE => ->.
  apply: (eq_from_nth (x0 := l)) => [| i].
  - rewrite (_ : size (_ ++ _ :: _) = size r); last by rewrite -Hr !size_cat.
    by rewrite Hsizeset.
  - rewrite Hsizeset nth_set_nth -/pos nth_cat Hsize /= => Hi.
    case (ltngtP i pos) => Hipos.
    + by rewrite -Hr nth_cat Hsize Hipos.
    + rewrite -Hr nth_cat Hsize.
      have:= ltnW Hipos; rewrite leqNgt => /negbTE ->.
      case H : (i - pos) => [|//=].
      exfalso; have H1 : i <= pos by rewrite /leq H.
      by have:= leq_trans Hipos H1; rewrite ltnn.
    + by rewrite Hipos subnn.
Qed.

Lemma congr_bump r l :
  r != [::] -> is_row r -> bump r l -> r ++ [:: l] =Pl [:: bumped r l] ++ ins r l.
Proof using .
  move=> Hnnil Hrow Hbump.
  have:= bump_inspos_lt_size Hrow Hbump; set pos := (inspos r l) => Hpos.
  move: (cat_take_drop pos r) (is_row_take pos Hrow) (is_row_drop pos Hrow).
  move HL : (take pos r) => L; move HR : (drop pos r) => R.
  case: R HR => [_ H| rpos R' HR Hr HrowL HrowR]. (* R is not empty *)
    exfalso; move: H; rewrite -HL cats0 => /(congr1 size)/eqP.
    by rewrite size_take Hpos (ltn_eqF Hpos).
  have Hrpos : (rpos = bumped r l)
    by rewrite /bumped -{1}Hr nth_cat -HL size_take Hpos /pos ltnn subnn.
  apply: (@plact_trans _ (L ++ [:: rpos, l & R'])).
  + rewrite -Hr -catA; apply: plact_catr.
    rewrite cats1 rcons_cons; apply: (congr_row_2 HrowR).
    rewrite Hrpos; exact: lt_bumped.
  + have -> : ins r l = L ++ l :: R'.
      rewrite /ins -/pos -Hr; apply: set_nth_LxR.
      by rewrite -HL size_take Hpos.
    rewrite -[[:: rpos, l & R']]cat1s -![l :: R']cat1s !catA.
    apply: plact_catl.
    rewrite -Hrpos !cats1 cat1s rcons_cons.
    apply: congr_row_1; last by rewrite Hrpos; apply: lt_bumped.
    apply: (is_row_rcons HrowL).
    case/lastP: L HL {Hr HrowL} => [//= | L ll Hll]; rewrite last_rcons.
    have H : (size L) < pos by have:= size_take pos r; rewrite Hpos Hll size_rcons => <-.
    have:= nth_lt_inspos H.
    by rewrite -(nth_take (n0 := pos) _ H) Hll nth_rcons ltnn eq_refl.
Qed.

Theorem congr_RS w : w =Pl (to_word (RS w)).
Proof using .
  elim/last_ind: w => [/=| w l0].
    rewrite /RS /to_word /=; exact: plact_refl.
  rewrite /RS rev_rcons /= -[RS_rev (rev w)]/(RS w) => H.
  apply: (@plact_trans _ (rcons (to_word (RS w)) l0)); first exact: plact_rcons.
  have:= is_tableau_RS w.
  elim: (RS w) l0 {H} => [/=| r0 t IHt] l0.
    rewrite /RS /to_word /= => _; exact: plact_refl.
  move=> /= /and4P [] Ht0 Hrow0 _ Htab.
  case (boolP (bump r0 l0)) => [Hbump | Hnbump].
  - rewrite (bump_bumprowE Hrow0 Hbump); move/(_ (bumped r0 l0) Htab) : IHt.
    rewrite !to_word_cons -!cats1 /= -catA => IHt.
    rewrite (@plact_ltrans _ _ (flatten (rev t) ++ [:: bumped r0 l0] ++ (ins r0 l0))).
    * rewrite catA; exact: plact_catl.
    * apply: plact_catr; exact: congr_bump.
  - rewrite (nbump_bumprowE Hrow0 Hnbump) {IHt}.
    rewrite !to_word_cons -!cats1 -catA cats1.
    apply: plact_catr; by rewrite nbump_ins_rconsE; first exact: plact_refl.
Qed.

Corollary Sch_plact u v : RS u == RS v -> u =Pl v .
Proof using .
  move=> /eqP Heq.
  apply: (@plact_trans _ (to_word (RS u))); first exact: congr_RS.
  rewrite Heq  plact_sym; exact: congr_RS.
Qed.

End RSToPlactic.

Section RemoveBig.

Variable Alph : inhOrdType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Lemma rembig_plact1 u v : u \in (plact1 v) -> rembig u = rembig v.
Proof using .
  move/plact1P => [] a [] b [] c [] /andP [] Hab Hbc -> -> /=.
  rewrite Hbc [b <A a]ltnXNgeqX Hab /= andbT andbF.
  by rewrite (leqX_ltnX_trans Hab Hbc).
Qed.

Lemma rembig_plact1i u v : u \in (plact1i v) -> rembig u = rembig v.
Proof using . by rewrite -plact1I => /rembig_plact1 ->. Qed.

Lemma rembig_plact2 u v : u \in (plact2 v) -> rembig u = rembig v.
Proof using .
  move/plact2P => [] a [] b [] c [] /andP [] Hab Hbc -> -> /=.
  rewrite Hab [c <A b]ltnXNgeqX Hbc /= !andbT.
  by rewrite [c <A a]ltnXNgeqX (ltnX_leqX_trans Hab Hbc) (ltnXW (ltnX_leqX_trans Hab Hbc)).
Qed.

Lemma rembig_plact2i u v : u \in (plact2i v) -> rembig u = rembig v.
Proof using . by rewrite -plact2I => /rembig_plact2 ->. Qed.

Lemma rembig_plact u v : u \in (plactrule _ v) -> rembig u = rembig v.
Proof using .
  move/plactruleP => [].
  exact: rembig_plact1. exact: rembig_plact1i.
  exact: rembig_plact2. exact: rembig_plact2i.
Qed.

Theorem rembig_plactcongr u v : u =Pl v -> (rembig u) =Pl (rembig v).
Proof using .
  move: v; apply: gencongr_ind; first exact: plact_refl.
  move=> a b1 c b2 => H Hplact.
  rewrite (plact_ltrans H).
  have:= plactrule_homog b1 => {u H} /allP/(_ _ Hplact) Heq.
  have:= Heq; rewrite -(perm_cat2r c) => Heqc.
  have:= rembig_eq_permR _ Heqc => /(_ a) [] [] -> ->.
  - apply: plact_is_congr; exact: rule_gencongr.
  - apply: plact_catr.
    have:= rembig_eq_permL _ Heq => /(_ c) [] [] -> ->.
    * apply: plact_catl; rewrite (rembig_plact Hplact); exact: plact_refl.
    * apply: plact_catl; exact: rule_gencongr.
Qed.

Lemma shape_append_nth T b i : shape (append_nth T b i) = incr_nth (shape T) i.
Proof using .
  rewrite /shape /=; apply: (@eq_from_nth _ 0).
  + rewrite size_map size_set_nth size_incr_nth size_map /maxn.
    case: (ltngtP i.+1 (size T)).
    - by move/ltnW ->.
    - by rewrite ltnNge => /negbTE ->.
    - by move => ->; rewrite leqnn.
  + move=> j Hi.
    rewrite nth_incr_nth (nth_map [::]) /=; last by move: Hi; rewrite size_map.
    rewrite nth_set_nth /= eq_sym.
    rewrite (_ : nth 0 _ _ = size (nth [::] T j)); first last.
      case: (ltnP j (size T)) => Hcase.
      * by rewrite (nth_map [::] _ _ Hcase).
      * by rewrite (nth_default _ Hcase) nth_default; last by rewrite size_map.
    case eqP => [->|].
    - by rewrite size_rcons add1n.
    - by rewrite add0n.
Qed.

Lemma inspos_rcons l r b : l <A b -> inspos r l = inspos (rcons r b) l.
Proof using . elim: r => [/= -> //= | r0 r IHr]; by rewrite rcons_cons /= => /IHr ->. Qed.

Lemma bump_bumprow_rconsE l r b :
  is_row (rcons r b) -> l <A b -> bump r l ->
  let: (lres, rres) := bumprow r l in bumprow (rcons r b) l = (lres, rcons rres b).
Proof using .
  move=> Hrowb Hl; have:= Hl => /inspos_rcons Hpos Hbump.
  have Hrow := is_row_rconsK Hrowb.
  have Hbumpb : bump (rcons r b) l by rewrite /bump last_rcons.
  rewrite (bump_bumprowE Hrow Hbump) (bump_bumprowE Hrowb Hbumpb).
  rewrite /bumped /ins -(inspos_rcons r Hl).
  have:= bump_inspos_lt_size Hrow Hbump => Hsize.
  by rewrite nth_rcons set_nth_rcons Hsize.
Qed.

Lemma nbump_bumprow_rconsE l r b :
  is_row (rcons r b) -> l <A b -> ~~bump r l ->
  let: (lres, rres) := bumprow r l in bumprow (rcons r b) l = (Some b, rres).
Proof using .
  move=> Hrowb Hl; have:= Hl => /inspos_rcons Hpos Hnbump.
  have Hrow := is_row_rconsK Hrowb.
  have Hbumpb : bump (rcons r b) l by rewrite /bump last_rcons.
  rewrite (nbump_bumprowE Hrow Hnbump) (bump_bumprowE Hrowb Hbumpb).
  rewrite /bumped /ins -(inspos_rcons r Hl).
  have:= nbump_inspos_eq_size Hrow Hnbump => Hsize.
  by rewrite nth_rcons set_nth_rcons Hsize eq_refl ltnn rcons_set_nth.
Qed.

Fixpoint last_big t b :=
  if t is t0 :: t' then
    if last b t0 == b then 0
    else (last_big t' b).+1
  else 0.

Lemma allLeq_to_word_hd t0 t b : allLeq (to_word (t0 :: t)) b -> allLeq t0 b.
Proof using . by rewrite to_word_cons allLeq_catE => /andP [] _. Qed.
Lemma allLeq_to_word_tl t0 t b : allLeq (to_word (t0 :: t)) b -> allLeq (to_word t) b.
Proof using . by rewrite to_word_cons allLeq_catE => /andP []. Qed.

Lemma last_bigP t b i :
  is_tableau t -> allLeq (to_word t) b ->
  reflect (last b (nth [::] t i) = b /\ forall j, j < i -> last b (nth [::] t j) <A b)
          (i == last_big t b).
Proof using .
  move=> Htab Hmax; apply: (iffP idP).
  + move/eqP ->; split.
    * elim: t Htab {Hmax} => [//= | t0 t IHt] /= /and4P [] _ _ _ Htab.
      case eqP => [//= | _]; exact: IHt.
    * elim: t Htab Hmax => [//= | t0 t IHt] /= /and4P [] Hnnil _ _ Htab Hmax.
      case eqP => [//= | /eqP H].
      case=> [/= _ | j].
      + have:= allLeq_to_word_hd Hmax; move: Hnnil H.
        case/lastP: t0 {Hmax} => [//= | t0 tn] _; rewrite last_rcons => H1 /allLeq_last.
        by rewrite ltnX_neqAleqX H1.
      + rewrite /=; by apply: IHt; last exact: (allLeq_to_word_tl Hmax).
  + move=> []; elim: t i Htab Hmax => [/= i _ _| t0 t IHt].
    * case: i => [//= | i] /= _ H.
      exfalso; have:= H 0 (ltn0Sn _); by rewrite ltnXnn.
    * case=> [/= _ _ -> _| i]; first by rewrite eq_refl.
      move=> /= /and4P [] _ _ _ Htab Hmax Hlast Hj.
      have:= Hj 0 (ltn0Sn _) => /= /ltnX_eqF ->.
      apply: (IHt _ Htab (allLeq_to_word_tl Hmax) Hlast).
      move=> j; exact: (Hj j.+1).
Qed.

Lemma maxL_LbR a v L b R : a :: v = L ++ b :: R -> allLeq L b -> allLeq R b -> maxL a v = b.
Proof using .
  move=> Hav /allP HL /allP HR; apply/eqP; rewrite eqn_leqX; apply/andP; split.
  - have:= in_maxL a v; rewrite Hav mem_cat inE => /orP []; last move/orP => [].
    * by move/HL.
    * by move/eqP ->.
    * by move/HR.
  - have:= maxLP a v => /allP; apply.
    by rewrite Hav mem_cat inE eq_refl orbT.
Qed.

Lemma allLeq_is_row_rcons w b :
  allLeq w b -> forall row, row \in RS w -> is_row (rcons row b).
Proof using .
  move=> H row Hin; apply: is_row_rcons.
  + move: Hin; have:= is_tableau_RS w.
    elim: (RS w) => [//= | t0 t IHt] /= /and4P [] _ Hrow _ Htab.
    rewrite inE => /orP [].
    * by move/eqP => ->.
    * exact: IHt.
  + have: allLeq (to_word (RS w)) b by rewrite (perm_eq_allLeq (perm_eq_RS w)).
    elim: (RS w) Hin => [//= | t0 t IHt] /=.
    rewrite inE to_word_cons => /orP [/eqP ->|].
    * rewrite allLeq_catE => /andP [] _; case/lastP: t0 => [//=| t0 tn].
      move/allLeq_last; by rewrite last_rcons.
    * move=> Hrow; by rewrite allLeq_catE => /andP [] /(IHt Hrow).
Qed.

Lemma last_ins_lt r l b : l <A b -> last b r <A b -> last b (ins r l) <A b.
Proof using .
  rewrite -!nth_last => Hl Hlast.
  rewrite (set_nth_default l b); first last.
    have : (ins r l) != [::] by apply: set_nth_non_nil.
    by case : (ins r l).
  rewrite nth_set_nth size_set_nth /= maxnC /maxn ltnS.
  case: (leqP (size r) (inspos r l)) => H /=; first by rewrite eq_refl.
  case: (boolP ((size r).-1 == inspos r l)) => _; first exact: Hl.
  rewrite (set_nth_default b l) //.
  by move: Hlast; case r => /=; first by rewrite ltnXnn.
Qed.

Lemma bumped_lt r b l : is_row r -> l <A b -> last b r <A b -> bumped r l <A b.
Proof using .
  rewrite -!nth_last /bumped => /is_rowP Hrow Hl Hlast.
  case: (ltnP (inspos r l) (size r)) => H.
  + rewrite (set_nth_default b l H).
    apply: (@leqX_ltnX_trans _ (nth b r (size r).-1)); last exact Hlast.
    apply: Hrow; move: H; case: (size r) => [//=| s].
    by rewrite ltnS /= => -> /=.
  + by rewrite (nth_default _ H).
Qed.

Lemma last_big_append_nth t b lb :
  (forall j : nat, j < lb -> last b (nth [::] t j) <A b) ->
  last_big (append_nth t b lb) b = lb.
Proof using .
  elim: t lb =>[/= | t0 t IHt /=].
  + case => [/= _| lb Hj /=]; first by rewrite eq_refl.
    exfalso; move/(_ 0 (ltn0Sn _)): Hj; by rewrite ltnXnn.
  + case => [/= _| lb Hj /=]; first by rewrite last_rcons eq_refl.
    rewrite (ltnX_eqF (Hj 0 (ltn0Sn _))).
    have {Hj} Hj j : j < lb -> last b (nth [::] t j) <A b by apply/(Hj j.+1).
    by rewrite (IHt _ Hj).
Qed.

Lemma bisimul_instab t l b lb :
  is_tableau t -> l <A b ->
  (forall row, row \in t -> is_row (rcons row b)) ->
  (forall j : nat, j < lb -> last b (nth [::] t j) <A b) ->
  let tres := (append_nth t b lb) in
  instab tres l = append_nth (instab t l) b (last_big (instab tres l) b).
Proof using .
  elim: t l lb => [/= l lb _| t0 t IHt l lb Htab] Hl Hallrow.
  - case: lb => [_ /=| lb Hj]; first by rewrite Hl /= (ltnX_eqF Hl) eq_refl.
    exfalso; move/(_ 0 (ltn0Sn _)): Hj; by rewrite /= ltnXnn.
  - move: Htab => /= /and4P [] Hnnil Hrow0 _ Htab.
    case: lb => [/= _ {IHt Htab} | lb Hj /=].
    * have Hrow: is_row (rcons t0 b) by apply: Hallrow; rewrite inE eq_refl.
      case: (boolP (bump t0 l)) => [Hbump | Hnbump].
      + have:= bump_bumprow_rconsE Hrow Hl Hbump.
        rewrite (bump_bumprowE Hrow0 Hbump) => ->.
        by rewrite /= last_rcons eq_refl.
      + have:= nbump_bumprow_rconsE Hrow Hl Hnbump.
        rewrite (nbump_bumprowE Hrow0 Hnbump) (nbump_ins_rconsE Hrow0 Hnbump) => ->.
        rewrite /= last_rcons (ltnX_eqF Hl) /= {Hrow0 Hrow Hnbump}.
        case: t Hallrow => [//= _ | t1 t Hallrow /=]; first by rewrite eq_refl.
        have : t1 \in [:: t0, t1 & t] by rewrite !inE eq_refl orbT.
        move/Hallrow/bumprow_rcons => -> /=.
        by rewrite last_rcons eq_refl.
    * have Hlast0:= Hj 0 (ltn0Sn _); rewrite /= in Hlast0.
      have {Hj} Hj j : j < lb -> last b (nth [::] t j) <A b by apply/(Hj j.+1).
      case: (boolP (bump t0 l)) => [Hbump | Hnbump].
      + rewrite (bump_bumprowE Hrow0 Hbump) /=.
        have Hbumped := bumped_lt Hrow0 Hl Hlast0.
        rewrite (ltnX_eqF (last_ins_lt Hl Hlast0)).
        have {Hallrow} Hallrow row : row \in t -> is_row (rcons row b).
          by move=> Hrow; apply: Hallrow; rewrite inE Hrow orbT.
        by rewrite /= {1}(IHt _ _ Htab Hbumped Hallrow Hj).
      + rewrite (nbump_bumprowE Hrow0 Hnbump) /=.
        by rewrite (ltnX_eqF (last_ins_lt Hl Hlast0)) /= (last_big_append_nth Hj).
Qed.

Theorem rembig_RS_last_big a v :
  RS (a :: v) = append_nth (RS (rembig (a :: v)))
                           (maxL a v)
                           (last_big (RS (a :: v)) (maxL a v)).
Proof using .
  have: a :: v != [::] by [].
  move Hrem : (rembig (a :: v)) => rem; move: Hrem => /eqP; rewrite eq_sym.
  move/rembigP => H/H{H} [] L [] b [] R [] -> Hav HL HR.
  rewrite (maxL_LbR Hav HL (allLtnW HR)) Hav {a v Hav}.
  elim/last_ind: R HR => [/= _| R Rn IHR].
  + rewrite cats0 cats1.
    rewrite [RS (rcons L b)]/RS rev_rcons /= -[RS_rev (rev L)]/(RS L).
    case HRS : (instab (RS L)) => [| tr0 tr /=].
    * exfalso; move: HRS; case: (RS L) => [//= | t0 t /=].
      by case: (bumprow t0 b) => [[] u v].
    * move: HRS; case HRSL : (RS L) => [//= | t0 t /=].
      - move=> [] <- <- /=; by rewrite eq_refl.
      - have Hrow: is_row (rcons t0 b).
          have := allLeq_is_row_rcons HL; rewrite HRSL; apply; by rewrite inE eq_refl orTb.
        rewrite (bumprow_rcons Hrow).
        move=> [] <- <-; by rewrite last_rcons eq_refl /=.
  + move=> Hmax; have HmaxR:= allLtn_rconsK Hmax; move: Hmax => /allLtn_last => HRnb.
    rewrite -rcons_cons -!rcons_cat /RS !rev_rcons /=.
    rewrite -[RS_rev _]/(RS (L ++ b :: R)) -[RS_rev _]/(RS (L ++ R)).
    move/(_ HmaxR) : IHR.
    move Hlb : (last_big (RS (L ++ b :: R)) b) => lb IHR.
    move: Hlb => /eqP; rewrite eq_sym => /last_bigP Htmp.
    have Htmp2 : allLeq (to_word (RS (L ++ b :: R))) b.
      apply: (perm_eq_allLeq (perm_eq_RS (L ++ b :: R))).
      by rewrite allLeq_catE //= (allLtnW HmaxR) andbT HL /=.
    have {Htmp Htmp2} := Htmp (is_tableau_RS (L ++ b :: R)) Htmp2 => [] [] _.
    rewrite {}IHR => Hj.
    apply: (bisimul_instab (is_tableau_RS (L ++ R)) HRnb).
    - apply: allLeq_is_row_rcons; by rewrite allLeq_catE HL (allLtnW HmaxR).
      move=> j Hjlb; move/(_ j Hjlb): Hj; by rewrite nth_set_nth /= (ltn_eqF Hjlb).
Qed.

Theorem rembig_RS a v :
  {i | RS (a :: v) = append_nth (RS (rembig (a :: v))) (maxL a v) i}.
Proof using . exists (last_big (RS (a :: v)) (maxL a v)); exact: rembig_RS_last_big. Qed.

End RemoveBig.


Section RestrIntervSmall.

Variable Alph : inhOrdType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Lemma plact1_geqXL L u v1 w v2 :
   v2 \in plact1 v1 ->
   [seq x <- u ++ v1 ++ w | L >=A x] =Pl [seq x <- u ++ v2 ++ w | L >=A x].
Proof using .
  move/plact1P => [] a [] b [] c [] Habc -> ->.
  rewrite !filter_cat /=.
  apply: plact_catr; apply: plact_catl.
  case: (leqXP c L) => Hc; last exact: plact_refl.
  have:= Habc => /andP [] Hab Hbc.
  have HbL := leqX_trans (ltnXW Hbc) Hc.
  rewrite HbL (leqX_trans Hab HbL).
  apply: rule_gencongr => /=.
  by rewrite Habc !mem_cat inE eq_refl.
Qed.

Lemma plact2_geqXL L u v1 w v2 :
   v2 \in plact2 v1 ->
   [seq x <- u ++ v1 ++ w | L >=A x] =Pl [seq x <- u ++ v2 ++ w | L >=A  x].
Proof using .
  move/plact2P => [] a [] b [] c [] Habc -> ->.
  rewrite !filter_cat /=.
  apply: plact_catr; apply: plact_catl.
  case: (leqXP c L) => Hc; last exact: plact_refl.
  have:= Habc => /andP [] Hab Hbc.
  have HbL := leqX_trans Hbc Hc.
  rewrite HbL (leqX_trans (ltnXW Hab) HbL).
  apply: rule_gencongr => /=.
  by rewrite Habc !mem_cat inE eq_refl /= !orbT.
Qed.

Lemma plactic_filter_geqX L u v :
  u =Pl v -> [seq x <- u | L >=A x] =Pl [seq x <- v | L >=A x].
Proof using .
  move: v; apply: gencongr_ind; first exact: plact_refl.
  move=> a b1 c b2 Hu.
  rewrite (plact_ltrans Hu) {u Hu} => /plactruleP [].
  + exact: plact1_geqXL.
  + rewrite -plact1I => /(plact1_geqXL L)-/(_ a c).
    move/plact_ltrans <-; exact: plact_refl.
  + exact: plact2_geqXL.
  + rewrite -plact2I => /(plact2_geqXL L)-/(_ a c).
    move/plact_ltrans <-; exact: plact_refl.
Qed.


Lemma plactic_filter_gtnX L u v :
  u =Pl v -> [seq x <- u | L >A x] =Pl [seq x <- v | L >A x].
Proof using .
  move=> H; case Hfu : [seq x <- u | L >A x] => [| fu0 fu'].
    suff -> : [seq x <- v | L >A x] = [::] by apply plact_refl.
    apply/eqP; move: Hfu => /eqP; apply contraLR.
    rewrite -!has_filter => /hasP [] x Hx HgtnX.
    apply/hasP; exists x; last exact HgtnX.
    by move: H => /plact_homog/perm_eq_mem ->.
  have := maxLP fu0 fu' => /allP; rewrite -Hfu => HML.
  set ML := maxL fu0 fu'.
  have Heq: {in u, gtnX L =1 geqX ML}.
    move=> x Hx /=.
    apply/idP/idP => Hxl.
    - apply HML; by rewrite mem_filter Hx /= Hxl.
    - have:= in_maxL fu0 fu'; rewrite -Hfu; rewrite mem_filter /= => /andP [] HMLL _.
      exact: leqX_ltnX_trans Hxl HMLL.
  rewrite (eq_in_filter Heq).
  have {Heq} Heq: {in v, gtnX L =1 geqX ML}.
    move=> x /=; move: H => /plact_homog/perm_eq_mem <-; exact: Heq.
  rewrite (eq_in_filter Heq).
  exact: plactic_filter_geqX.
Qed.

End RestrIntervSmall.


Section RestrIntervBig.

Variable Alph : inhOrdType.
Notation Dual := (dual_inhOrdType Alph).
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Variable L : Alph.
Notation leqXL := (@leqX Alph L).
Notation geqXL := (@geqX Dual L).
Notation ltnXL := (@ltnX Alph L).
Notation gtnXL := (@gtnX Dual L).

Lemma leqXL_geqXLdualE u : filter leqXL u = from_revdual (filter geqXL (revdual u)).
Proof using .
  rewrite /= filter_rev revK.
  apply/eq_filter => i /=; by rewrite -dual_leqX.
Qed.

Lemma ltnXL_gtnXLdualE u : filter ltnXL u = from_revdual (filter gtnXL (revdual u)).
Proof using .
  rewrite /= filter_rev revK.
  apply/eq_filter => i /=; by rewrite -dual_ltnX.
Qed.

Lemma plactic_filter_leqX u v : u =Pl v -> filter leqXL u =Pl filter leqXL v.
Proof using .
  move=> H; rewrite [filter _ u]leqXL_geqXLdualE [filter _ v]leqXL_geqXLdualE.
  rewrite -plact_from_dualE; apply: plactic_filter_geqX.
  by rewrite -plact_dualE.
Qed.

Lemma plactic_filter_ltnX u v : u =Pl v -> filter ltnXL u =Pl filter ltnXL v.
Proof using .
  move=> H; rewrite [filter _ u]ltnXL_gtnXLdualE [filter _ v]ltnXL_gtnXLdualE.
  rewrite -plact_from_dualE; apply: plactic_filter_gtnX.
  by rewrite -plact_dualE.
Qed.

End RestrIntervBig.


Section IncrMap.

Variable T1 T2 : inhOrdType.
Variable F : T1 -> T2.
Variable u v : seq T1.
Hypothesis Hincr : {in u &, forall x y, x <A y -> F x <A F y}.

Lemma Fnondecr : {in u &, forall x y, x <=A y -> F x <=A F y}.
Proof using Hincr.
  move=> x y Hx Hy /=; rewrite leqX_eqVltnX => /orP [/eqP -> //=| H].
  by rewrite leqX_eqVltnX (Hincr Hx Hy H) orbT.
Qed.

Lemma subset_abc l a b c r :
  {subset l ++ [:: a; b; c] ++ r <= u} -> [/\ a \in u, b \in u & c \in u].
Proof using . move=> H; split; apply: H; by rewrite !mem_cat !inE /= eq_refl !orbT. Qed.

Lemma plact_map_in_incr : u =Pl v -> (map F u) =Pl (map F v).
Proof using Hincr.
  move=> H.
  suff : {subset v <= u} /\ [seq F i | i <- u] =Pl [seq F i | i <- v] by move => [].
  move: v H; apply: gencongr_ind; first by split; last exact: plact_refl.
  move=> l v1 r v2 [] Hperm Hu Hrule.
  split.
  - move=> i; move/(_ i): Hperm.
    rewrite !mem_cat => Hperm /or3P [] H; apply: Hperm.
    + by rewrite H ?orbT.
    + have /allP := plactrule_homog v1 => /(_ _ Hrule)/perm_eq_mem ->.
      by rewrite H ?orbT.
    + by rewrite H ?orbT.
  rewrite (plact_ltrans Hu) {Hu} !map_cat.
  apply: plact_catr; apply: plact_catl.
  apply: rule_gencongr => /=; move: Hrule => /plactruleP [].
  + move/plact1P => [] a [] b [] c [] Hord Hv1; rewrite Hv1 => -> {v2}; subst v1.
    rewrite !mem_cat /=; move: Hord => /andP [].
    move: Hperm => /subset_abc [] Ha Hc Hb.
    move => /(Fnondecr Ha Hb) -> /(Hincr Hb Hc) -> /=.
    by rewrite mem_seq1 eq_refl ?orbT.
  + move/plact1iP => [] a [] b [] c [] Hord -> {v2} Hv1; rewrite Hv1; subst v1.
    rewrite !mem_cat /=; move: Hord => /andP [].
    move: Hperm => /subset_abc [] Hc Ha Hb.
    move => /(Fnondecr Ha Hb) -> /(Hincr Hb Hc) -> /=.
    by rewrite mem_seq1 eq_refl ?orbT.
  + move/plact2P => [] a [] b [] c [] Hord Hv1; rewrite Hv1 => -> {v2}; subst v1.
    rewrite !mem_cat /=; move: Hord => /andP [].
    move: Hperm => /subset_abc [] Hb Ha Hc.
    move => /(Hincr Ha Hb) -> /(Fnondecr Hb Hc) -> /=.
    by rewrite mem_seq1 eq_refl ?orbT.
  + move/plact2iP => [] a [] b [] c [] Hord -> {v2} Hv1; rewrite Hv1; subst v1.
    rewrite !mem_cat /=; move: Hord => /andP [].
    move: Hperm => /subset_abc [] Hb Hc Ha.
    move => /(Hincr Ha Hb) -> /(Fnondecr Hb Hc) -> /=.
    by rewrite mem_seq1 eq_refl ?orbT.
Qed.

End IncrMap.

