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

Require Import partition schensted ordtype stdtab invseq congr plactic green greeninv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N.

Section OrderedType.

Variable T : ordType.

Lemma green_rel_one (s : seq T) (R : rel T) :
  exists t : seq T, subseq t s /\ sorted R t /\ size t = (green_rel R s) 1.
Proof.
  rewrite /green_rel /= /green_rel_t.
  set P := (X in \max_(_ | X _) _).
  have : #|P| > 0.
    apply/card_gt0P; exists set0.
    rewrite /P /ksupp unfold_in cards0 /=.
    apply/andP; split.
    + apply/trivIsetP => s1 s2; by rewrite inE.
    + apply/forallP => x; by rewrite inE.
  rewrite /P {P} => /(eq_bigmax_cond scover).
  case=> x Hx Hmax; rewrite Hmax.
  move: Hx; rewrite /ksupp unfold_in => /and3P [] Hcard _ /forallP Hall.
  case Hc: #|x| => [/= | c ].
    move: Hc => /eqP; rewrite cards_eq0 => /eqP ->.
    exists [::]; repeat split; first by apply sub0seq.
    by rewrite /cover big_set0 cards0.
  have {Hcard Hc} : #|x| == 1.
    move: Hcard; rewrite Hc.
    by rewrite ltnS leqn0 => /eqP ->.
  move/cards1P => [] x0 Hx0; subst x.
  have {Hall} := Hall x0; rewrite inE eq_refl /=.
  set sol := extractpred _ _ => Hsol.
  exists sol; repeat split.
  + by apply extsubsm.
  + exact Hsol.
  + rewrite /sol size_extract.
    by rewrite /= /cover big_set1.
Qed.

Theorem Erdos_Szekeres (m n : nat) (s : seq T) :
  (size s) > (m * n) ->
  (exists t, subseq t s /\ sorted (leqX T) t /\ size t > m) \/
  (exists t, subseq t s /\ sorted (gtnX T) t /\ size t > n).
Proof.
  move=> Hsize; pose tab := RS s.
  have := (eqP (size_RS s)); rewrite /size_tab => Hsz.
  have {Hsize} : (n < size (shape (RS s))) \/ (m < head 0 (shape (RS s))).
    have Hpart := is_part_sht (is_tableau_RS s).
    apply/orP; move: Hsize; rewrite -Hsz.
    apply contraLR; rewrite negb_or -!leqNgt => /andP [] Hn Hm.
    apply (leq_trans (part_sumn_rectangle Hpart)).
    by apply leq_mul.
  move=> [] Hltn.
  - right => {m}.
    have := greenCol_RS 1 s.
    rewrite -sum_conj.
    have -> : \sum_(l <- shape (RS s)) minn l 1 = size (shape (RS s)).
      have := is_part_sht (is_tableau_RS s).
      move: (shape _) => sh.
      elim: sh => [//= | s0 sh IHsh]; first by rewrite big_nil.
      move=> Hpart; have /= Hs0 := part_head_non0 Hpart.
      move: Hpart => /= /andP [] Hhead Hpart.
      rewrite big_cons (IHsh Hpart).
      have -> : minn s0 1 = 1.
        rewrite /minn; move: Hs0; by case s0.
      by rewrite add1n.
    move=> Hgr; move: Hltn; rewrite -Hgr {tab Hgr}.
    case : (green_rel_one s (gtnX T)) => x [] Hsubs [] Hsort <- Hn.
    by exists x.
  - left.
    have := greenRow_RS 1 s.
    have -> : part_sum (shape (RS s)) 1 = head 0 (shape (RS s)).
      rewrite /part_sum.
      case: (shape (RS s)) => [| s0 l] /=; first by rewrite big_nil.
      by rewrite take0 big_cons big_nil addn0.
    rewrite /greenRow => Hgr; move: Hltn; rewrite -Hgr {tab Hgr}.
    case : (green_rel_one s (leqX T)) => x [] Hsubs [] Hsort <- Hn.
    by exists x.
Qed.


End OrderedType.
