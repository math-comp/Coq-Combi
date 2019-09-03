(** * Combi.Combi.multinomial : Multinomial Coefficients *)
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
(** * Multinomial Coefficients

We define:
- 'C[s] == the multinomial coefficient associated to the sequence [s].

The main expression is Lemma [multinomial_factd]:

  [ 'C[s] = (sumn s)`! %/ \prod_(i <- s) i`!. ]

******)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import bigop div binomial.

Require Import tools.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Fixpoint multinomial s :=
  if s is i :: s' then 'C(sumn s, i) * (multinomial s')
  else 1.

Notation "''C' [ s ]" := (multinomial s)
  (at level 8, format "''C' [ s ]") : nat_scope.

Lemma multinomial_fact s : 'C[s] * \prod_(i <- s) i`! = (sumn s)`!.
Proof.
elim: s => [| i s IHs] /=; first by rewrite fact0 big_nil muln1.
rewrite big_cons [i`! * _]mulnC -!mulnA ['C[s] * _]mulnA IHs.
rewrite [_ * i`!]mulnC.
rewrite -{2}(addKn i (sumn s)) bin_fact //.
exact: leq_addr.
Qed.

Lemma dvdn_prodfact s : \prod_(i <- s) i`! %| (sumn s)`! .
Proof. by apply/dvdnP; exists 'C[s]; rewrite multinomial_fact. Qed.

Lemma multinomial_factd s : 'C[s] = (sumn s)`! %/ \prod_(i <- s) i`!.
Proof.
rewrite -multinomial_fact mulnK //.
by apply prodn_gt0 => i; apply fact_gt0.
Qed.

Lemma perm_multinomial s t : perm_eq s t -> 'C[s] = 'C[t].
Proof.
rewrite !multinomial_factd => Hperm.
by rewrite (perm_sumn Hperm) (perm_big _ Hperm).
Qed.

Lemma multinomial_filter_neq0 s : 'C[[seq i <- s | i != 0]] = 'C[s].
Proof.
rewrite !multinomial_factd; congr (_ %/ _).
- congr (_`!); elim: s => [| s0 s IHs] //=.
  by case: eqP => [-> | _] /=; rewrite ?add0n IHs.
- rewrite big_filter [RHS](bigID (fun i => i == 0)) /=.
  by rewrite [X in X * _]big1 ?mul1n // => i /eqP ->.
Qed.
