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
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div fintype.
Require Import tuple ssrnum ssralg ssrint finfun bigop.

Import GRing.Theory.

Section AllPairs.

Open Scope ring_scope.

Variable (R: comRingType).
Variable idx : R.
Variable op : Monoid.com_law idx.

Local Notation "'*%M'" := op (at level 0).
Local Notation "x * y" := (op x y).

Lemma big_allpairs I J (rI : seq I) (rJ : seq J) F :
  \big[*%M/idx]_(X <- [seq (A, B) | A <- rI, B <- rJ]) F X =
    \big[*%M/idx]_(A <- rI) \big[*%M/idx]_(B <- rJ) F (A, B).
Proof.
  elim: rI => [//= | i0 rI IHrI] /=; first by rewrite !big_nil.
  by rewrite big_cat big_cons IHrI {IHrI} big_map.
Qed.

End AllPairs.
