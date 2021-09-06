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

(** TODO : submitted to mathcomp *)
Lemma porbitV s : porbit s^-1 =1 porbit s.
Proof.
move=> x; apply/setP => y; rewrite porbit_sym.
by apply/porbitP/porbitP => [][i ->]; exists i; rewrite expgVn ?permK ?permKV.
Qed.

(** TODO : submitted to mathcomp *)
Lemma porbitsV s : porbits s^-1 = porbits s.
Proof.
rewrite /porbits; apply/setP=> y.
by apply/imsetP/imsetP => [] [x _ ->{y}]; exists x; rewrite // porbitV.
Qed.

Lemma permKP s : reflect (involutive s) (s^-1 == s).
Proof.
apply (iffP eqP) => [ssV i | invs].
- by rewrite -{1}ssV permK.
- rewrite -permP => i; apply (@perm_inj _ s).
  by rewrite invs permKV.
Qed.

End PermComp.


Section SetAct.

Variables (aT : finGroupType) (D : {set aT}) (rT : finType) (to : action D rT).

(** TODO: complete setactU, setactI, setactD ... and submit to mathcomp *)
Lemma setact1 x a : to^* [set x] a = [set to x a].
Proof using. by rewrite /setact imset_set1. Qed.
Lemma setactI S T a : to^* (S :&: T) a = to^* S a :&: to^* T a.
Proof. by rewrite /setact imsetI //; apply: in2W; apply: act_inj. Qed.
Lemma setactU S T a : to^* (S :|: T) a = to^* S a :|: to^* T a.
Proof. by rewrite /setact imsetU //; apply: in2W; apply: act_inj. Qed.

Lemma setactC S a :
  to^* (~: S) a = ~: to^* S a.
Proof using.
apply/eqP; rewrite eqEcard; apply/andP; split.
- apply/subsetP => x /imsetP [y]; rewrite !inE => Hy -> {x}.
  by move: Hy; apply contra => /imsetP [z Hz] /act_inj ->.
- rewrite card_setact [X in _ <= X]cardsCs setCK.
  by rewrite cardsCs setCK card_setact.
Qed.

End SetAct.


Section PermOnG.

Variable T : finType.
Implicit Type (s t c : {perm T}).

(** TODO : submitted to mathcomp *)
Lemma perm_onV H s : perm_on H s -> perm_on H s^-1.
Proof using.
rewrite /perm_on => /subsetP Hsub; apply/subsetP => i.
rewrite inE => Hi; apply Hsub; rewrite inE.
move: Hi; apply contra => /eqP {1}<-.
by rewrite permK.
Qed.

End PermOnG.
