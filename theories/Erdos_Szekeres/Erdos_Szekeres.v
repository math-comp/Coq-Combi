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

Section OrderedType.

Variables (disp : unit) (T : inhOrderType disp).

Lemma Greene_rel_one (s : seq T) (R : rel T) :
  exists t : seq T, subseq t s /\ sorted R t /\ size t = (Greene_rel R s) 1.
Proof using .
rewrite /Greene_rel /= /Greene_rel_t.
set P := (X in \max_(_ | X _) _).
have : #|P| > 0.
  apply/card_gt0P; exists set0.
  rewrite /P /ksupp !unfold_in /= cards0 /=.
  apply/andP; split.
  + by apply/trivIsetP => s1 s2; rewrite inE.
  + by apply/forallP => x; rewrite inE.
rewrite /P {P} => /(eq_bigmax_cond (fun x => #|cover x|)).
case=> x Hx Hmax; rewrite Hmax.
move: Hx; rewrite /ksupp unfold_in => /and3P [] Hcard _ /forallP Hall.
case Hc: #|x| => [/= | c ].
  move: Hc => /eqP; rewrite cards_eq0 => /eqP ->.
  exists [::]; repeat split; first exact: sub0seq.
  by rewrite /cover big_set0 cards0.
have {Hcard Hc} : #|x| == 1.
  move: Hcard; rewrite Hc.
  by rewrite ltnS leqn0 => /eqP ->.
move/cards1P => [] x0 Hx0; subst x.
move/(_ x0) : Hall; rewrite inE eq_refl /=.
set sol := extractpred _ _ => Hsol.
exists sol; repeat split.
+ exact: extsubsm.
+ exact: Hsol.
+ rewrite /sol size_extract.
  by rewrite /= /cover big_set1.
Qed.

Theorem Erdos_Szekeres (m n : nat) (s : seq T) :
  size s > m * n ->
  (exists t, subseq t s /\ sorted <=%O t /\ size t > m) \/
  (exists t, subseq t s /\ sorted >%O t /\ size t > n).
Proof using .
move=> Hsize; pose tab := RS s.
have {Hsize} : (n < size (shape tab)) \/ (m < head 0 (shape tab)).
  have Hpart := is_part_sht (is_tableau_RS s).
  apply/orP; move: Hsize; rewrite -(size_RS s) /size_tab.
  apply contraLR; rewrite negb_or -!leqNgt => /andP [] Hn Hm.
  by apply (leq_trans (part_sumn_rectangle Hpart)); apply: leq_mul.
move=> [] Hltn.
- right => {m}.
  have := Greene_col_RS 1 s.
  rewrite -sum_conj.
  rewrite (_ : \sum_(l <- shape (RS s)) minn l 1 = size (shape (RS s))); first last.
    have := is_part_sht (is_tableau_RS s).
    move: (shape _) => sh.
    elim: sh => [//= | s0 sh IHsh]; first by rewrite big_nil.
    move=> Hpart; have /= Hs0 := part_head_non0 Hpart.
    move: Hpart => /= /andP [] Hhead Hpart.
    rewrite big_cons (IHsh Hpart).
    rewrite (_ : minn s0 1 = 1) ?add1n //.
    by rewrite /minn; move: Hs0; case s0.
  move=> Hgr; move: Hltn; rewrite -Hgr {tab Hgr}.
  case: (Greene_rel_one s >%O) => x [] Hsubs [] Hsort <- Hn.
  by exists x.
- left => {n}.
  have := Greene_row_RS 1 s.
  rewrite (_ : sumn (take 1 (shape (RS s))) = head 0 (shape (RS s))); first last.
    by case: (shape (RS s)) => [| s0 l] //=; rewrite take0 addn0.
  rewrite /Greene_row => Hgr; move: Hltn; rewrite -Hgr {tab Hgr}.
  case: (Greene_rel_one s <=%O) => x [] Hsubs [] Hsort <- Hn.
  by exists x.
Qed.

End OrderedType.
