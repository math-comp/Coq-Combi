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
From Corelib Require Import Setoid.
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
Lemma setact0 a : to^* set0 a = set0.
Proof using. by rewrite /setact imset0. Qed.
Lemma setact1 x a : to^* [set x] a = [set to x a].
Proof using. by rewrite /setact imset_set1. Qed.
Lemma setactI S T a : to^* (S :&: T) a = to^* S a :&: to^* T a.
Proof. by rewrite /setact imsetI //; apply: in2W; apply: act_inj. Qed.
Lemma setactU S T a : to^* (S :|: T) a = to^* S a :|: to^* T a.
Proof. by rewrite /setact imsetU //; apply: in2W; apply: act_inj. Qed.
Lemma setactU1 x T a : to^* (x |: T) a = to x a |: to^* T a.
Proof. by rewrite /setact imsetU1 //; apply: in2W; apply: act_inj. Qed.

Lemma setactC S a : to^* (~: S) a = ~: to^* S a.
Proof using.
apply/eqP; rewrite eqEcard; apply/andP; split.
- apply/subsetP => x /imsetP[y]; rewrite !inE => Hy ->{x}.
  by move: Hy; apply contra => /imsetP[z Hz /act_inj->].
- rewrite card_setact [X in _ <= X]cardsCs setCK.
  by rewrite cardsCs setCK card_setact.
Qed.

End SetAct.
