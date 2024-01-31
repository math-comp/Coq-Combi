(** * Combi.Erdos_Szekeres.Erdos_Szekeres : The Erdös-Szekeres theorem *)
(******************************************************************************)
(*      Copyright (C) 2014-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * The Erdös-Szekeres theorem on monotonic subsequences.

A proof of the Erdös Szekeres theorem about longest increasing and
decreasing subsequences. The theorem is [Erdos_Szekeres] and
says that any sequence [s] of length at least [n*m+1] over a totally ordered
type contains
- either a nondecreasing subsequence of length [n+1];
- or a strictly decreasing subsequence of length [m+1].
We prove it as a corollary of Greene's theorem on the Robinson-Schensted
correspondance. Note that there are other proof which require less theory.
 *****)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple finfun finset bigop path order.

Require Import partition tableau Schensted ordtype Greene Greene_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.
Open Scope N.


Lemma Greene_rel_one (T : eqType) (s : seq T) (R : rel T) :
  exists t : seq T, subseq t s /\ sorted R t /\ size t = (Greene_rel R s) 1.
Proof using .
rewrite /Greene_rel /= /Greene_rel_t.
set P := (X in \max_(_ | X _) _).
have : #|P| > 0.
  apply/card_gt0P; exists set0.
  rewrite {}/P /ksupp !unfold_in /= cards0 /=.
  apply/andP; split.
  + by apply/trivIsetP => s1 s2; rewrite inE.
  + by apply/forallP => x; rewrite inE.
rewrite {}/P => /(eq_bigmax_cond (fun x => #|cover x|)).
case=> U /[swap] /[dup] Hmax ->.
rewrite /ksupp unfold_in => /and3P[Hcard _ /forallP Hall].
case HU: #|U| => [/= | c].
  move: HU => /eqP; rewrite cards_eq0 => /eqP ->.
  exists [::]; repeat split; first exact: sub0seq.
  by rewrite /cover big_set0 cards0.
have {Hcard HU} : #|U| == 1.
  by move: Hcard; rewrite HU ltnS leqn0 => /eqP ->.
move/cards1P => [x Hx]; subst U.
move/(_ x) : Hall; rewrite inE eq_refl /=.
set sol := extractpred _ _ => Hsol.
exists sol; repeat split.
+ exact: extsubsm.
+ exact: Hsol.
+ by rewrite /sol size_extract /= /cover big_set1.
Qed.

Theorem Erdos_Szekeres
  (disp : unit) (T : inhOrderType disp) (m n : nat) (s : seq T) :
  size s > m * n ->
  (exists t, subseq t s /\ sorted <=%O t /\ size t > m) \/
  (exists t, subseq t s /\ sorted >%O t /\ size t > n).
Proof using .
move=> Hsize; pose tab := RS s.
have {Hsize} : (n < size (shape tab)) \/ (m < head 0 (shape tab)).
  have Hpart := is_part_sht (is_tableau_RS s).
  apply/orP; move: Hsize; rewrite -(size_RS s) /size_tab.
  apply contraLR; rewrite negb_or -!leqNgt => /andP[Hn Hm].
  exact: (leq_trans (part_sumn_rectangle Hpart) (leq_mul _ _)).
move=> [] Hltn.
- right => {m}.
  have := Greene_col_RS 1 s.
  rewrite -sum_conj.
  rewrite (_ : \sum_(l <- _) minn l 1 = size (shape (RS s))); first last.
    have := is_part_sht (is_tableau_RS s).
    move: (shape _) => sh.
    elim: sh => [// | s0 sh IHsh Hpart]; first by rewrite big_nil.
    have /= Hs0 := part_head_non0 Hpart.
    move: Hpart => /= /andP[Hhead Hpart].
    rewrite big_cons (IHsh Hpart) (_ : minn s0 1 = 1) ?add1n //.
    by case: s0 Hs0 {Hhead}.
  move: Hltn => /[swap] <-{tab}.
  case: (Greene_rel_one s >%O) => x [Hsubs] [Hsort <- Hn].
  by exists x.
- left => {n}.
  have := Greene_row_RS 1 s.
  rewrite (_ : sumn _ = head 0 (shape (RS s))); first last.
    by case: (shape (RS s)) => [| s0 l] //=; rewrite take0 addn0.
  rewrite /Greene_row; move: Hltn => /[swap] <-{tab}.
  case: (Greene_rel_one s <=%O) => x [Hsubs] [Hsort <- Hn].
  by exists x.
Qed.


