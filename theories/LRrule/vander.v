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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice.
Require Import finset fintype finfun tuple bigop ssralg ssrint.
Require Import fingroup perm zmodp binomial poly matrix.
Require Import ssrcomplements poset freeg mpoly.

Require Import sym_group antisym.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.





Section VandermondeDet.

Variable n : nat.
Variable R : comRingType.

Definition antim (s : seq nat) : 'M[ {mpoly R[n]} ]_n :=
  \matrix_(i, j < n) 'X_i ^+ (nth 0 s j + n - j)%N.
Definition Vandmx : 'M[ {mpoly R[n]} ]_n := \matrix_(i, j < n) 'X_i ^+ (n - j).
Definition Vandet := \det Vandmx.

Lemma Vandmx_antimE : Vandmx = antim [::].
Proof. rewrite /Vandmx /antim -matrixP => i j /=; by rewrite !mxE nth_default. Qed.

Lemma tperm_antim_xrow s i j :
  i != j -> msym (tperm i j) (\det (antim s)) = \det (xrow i j (antim s)).
Proof.
  rewrite /antim => Hij.
  rewrite -det_map_mx /=; congr (\det _).
  rewrite /map_mx -matrixP => r c /=.
  rewrite !mxE rmorphX /= msymX /=.
  congr (mpolyX _ _ ^+ _) => {c}.
  rewrite mnmP => u /=; rewrite !mnm_tnth /=.
  rewrite !tnth_map /= tnth_ord_tuple /= mnm1E tpermV.
  congr (nat_of_bool _); apply (sameP idP); apply (iffP idP).
  - by move/eqP <-; rewrite tpermK.
  - by move/eqP ->; rewrite tpermK.
Qed.

Lemma tperm_antim s i j : i != j -> msym (tperm i j) (\det (antim s)) = - (\det (antim s)).
Proof.
  move=> Hij; rewrite (tperm_antim_xrow _ Hij).
  rewrite xrowE det_mulmx det_perm.
  by rewrite odd_tperm Hij /= expr1 mulN1r.
Qed.

Lemma antimP s : \det (antim s) \is antisym.
Proof.
  apply/isantisym_tpermP => i j.
  case: (altP (i =P j)) => [-> |] /=; first by rewrite tperm1 msym1m.
  exact: tperm_antim.
Qed.

Corollary Vander_anti : Vandet \is antisym.
Proof. rewrite /Vandet Vandmx_antimE. exact: antimP. Qed.

End VandermondeDet.
