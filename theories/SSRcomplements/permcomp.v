(** * Combi.SSRcomplements.permcomp : Complement on permutations *)
(******************************************************************************)
(*      Copyright (C) 2016-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * A few lemmas on permutation
***********)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import finset fingroup perm morphism action.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Import GroupScope.

(** ** Orbit and cycles *)
Section PermComp.

Variable T : finType.
Implicit Type (s : {perm T}) (X : {set T}) (P : {set {set T}}).

Lemma porbitV s : porbit s^-1 =1 porbit s.
Proof.
move=> x; apply/setP => y; rewrite porbit_sym.
by apply/porbitP/porbitP => [][i ->]; exists i; rewrite expgVn ?permK ?permKV.
Qed.

Lemma imset_setT (V : finType) (f : T -> V) :
  [set f x | x : T] = [set f x | x in [set: T]].
Proof. by apply/setP=> x; apply/imsetP/imsetP=> [][y _ ->{x}]; exists y. Qed.

Lemma porbitsV s : porbits s^-1 = porbits s.
Proof. by rewrite /porbits !imset_setT -(eq_imset setT (porbitV s)). Qed.

Lemma setactC (aT : finGroupType) (D : {set aT})
      (rT : finType) (to : action D rT) S a :
  to^* (~: S) a = ~: to^* S a.
Proof using.
apply/eqP; rewrite eqEcard; apply/andP; split.
- apply/subsetP => x /imsetP [y]; rewrite !inE => Hy -> {x}.
  by move: Hy; apply contra => /imsetP [z Hz] /act_inj ->.
- rewrite card_setact [X in _ <= X]cardsCs setCK.
  by rewrite cardsCs setCK card_setact.
Qed.

Lemma permKP s : reflect (involutive s) (s^-1 == s).
Proof.
apply (iffP eqP) => [ssV i | invs].
- by rewrite -{1}ssV permK.
- rewrite -permP => i; apply (@perm_inj _ s).
  by rewrite invs permKV.
Qed.

End PermComp.


Section PermOnG.

Variable T : finType.
Implicit Type (s t c : {perm T}).


Lemma restr_perm_commute C s : commute (restr_perm C s) s.
Proof using.
case: (boolP (s \in 'N(C | 'P))) =>
    [HC | /triv_restr_perm ->]; last exact: (commute_sym (commute1 _)).
apply/permP => x; case: (boolP (x \in C)) => Hx; rewrite !permM.
- by rewrite !restr_permE //; move: HC => /astabsP/(_ x)/= ->.
- have:= restr_perm_on C s => /out_perm Hout.
  rewrite (Hout _ Hx) {}Hout //.
  by move: Hx; apply contra; move: HC => /astabsP/(_ x)/= ->.
Qed.

End PermOnG.
