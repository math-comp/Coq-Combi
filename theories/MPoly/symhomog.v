(** * Combi.MPoly.sympoly : Symmetric Polynomials *)
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
(** * The Ring of Symmetric Polynomials *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun finset bigop ssralg path perm fingroup.
From SsrMultinomials Require Import ssrcomplements poset freeg bigenough mpoly.
From mathcomp Require Import vector.

Require Import tools ordtype permuted partition Yamanouchi std tableau stdtab.
Require Import antisym sympoly Schur_basis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.


Section Homogeneous.

Variable n : nat.
Variable R : fieldType.
Variable d : nat.

Hypothesis Hvar : (d <= n.+1)%N.

Implicit Type m : 'X_{1.. n.+1}.
Local Notation SF := {sympoly R[n.+1]}.
Local Notation Pd := [set: intpartn d].
Local Notation tPd := (enum_tuple (pred_of_set Pd)).
Local Notation hPol := (dhomog n.+1 R d).

Definition homsymm (l : intpartn d) := DHomog (symm_homog n.+1 R l).
Definition homsyme (l : intpartn d) := DHomog (prod_syme_homog n.+1 R l).
Definition homsymh (l : intpartn d) := DHomog (prod_symh_homog n.+1 R l).
Definition homsymp (l : intpartn d) := DHomog (prod_symp_homog n.+1 R l).
Definition homsyms (l : intpartn d) := DHomog (syms_homog n R l).

Definition homsympoly := span [seq homsymm l | l <- tPd].

Lemma homsymmE (f : hPol) :
  mpoly_of_dhomog f \is symmetric ->
  f = \sum_(l : intpartn d) f@_(mpart l) *: homsymm l.
Proof.
move=> Hf; apply val_inj.
have:= dhomog_is_dhomog f.
rewrite -[val f]/(val (SymPoly Hf)) => fhom.
rewrite (homog_symmE fhom) /=.
rewrite [LHS](linear_sum (@sympol_lrmorphism _ _)) linear_sum /=.
rewrite (bigID (fun  l : intpartn d => (size l <= n.+1)%N)) /= addrC.
rewrite big1 ?add0r // => i /negbTE Hi.
by rewrite /symm Hi scaler0.
Qed.

Lemma dsymP f : (f \in homsympoly) = (mpoly_of_dhomog f \is symmetric).
Proof.
apply/idP/idP.
- move=> /coord_span -> /=.
  rewrite linear_sum; apply rpred_sum => i _.
  rewrite linearZZ; apply rpredZ => /=.
  by rewrite (nth_map (rowpartn d)) /=; last by move: i; rewrite cardE => i.
- move/homsymmE ->.
  rewrite /homsympoly span_def.
  apply rpred_sum => l _; apply rpredZ.
  rewrite big_map (bigD1_seq l) /= ?mem_enum ?inE ?enum_uniq //.
  rewrite -[X in X \in _]addr0.
  apply memv_add; first exact: memv_line.
  exact: mem0v.
Qed.

Lemma indpartP (l : intpartn d) : (index l tPd < #|Pd|)%N.
Proof. by rewrite [X in (_ < X)%N]cardE index_mem mem_enum inE. Qed.
Definition indpart l := Ordinal (indpartP l).
Lemma indpartE i : indpart (tnth tPd i) = i.
Proof.
apply val_inj => /=; apply index_uniq; last exact: enum_uniq.
by rewrite -cardE.
Qed.

Lemma vect_to_sym co (v : intpartn d -> hPol) :
  \sum_(i < #|Pd|) co i *: (map_tuple v tPd)`_i =
  \sum_(l : intpartn d) (co (indpart l)) *: v l.
Proof.
rewrite [RHS](eq_bigl (fun l => l \in setT)); first last.
  by move=> i /=; rewrite inE.
rewrite [RHS]big_enum /= -[enum _]/(tval tPd).
rewrite big_tuple; apply eq_bigr => i _.
rewrite indpartE; congr (_ *: _).
rewrite (nth_map (tnth tPd i)) -?cardE //.
by rewrite {2}(tnth_nth (tnth tPd i)) .
Qed.

Lemma free_homsymm : free [seq homsymm l | l <- tPd].
Proof.
apply/freeP => co.
rewrite vect_to_sym => /(congr1 val) /=; rewrite linear_sum /=.
rewrite (eq_bigr (fun l : intpartn d =>
                    sympol_lrmorphism _ _ ((co (indpart l)) *: 'm[l]))) //.
rewrite -!linear_sum => /= H i.
have {H} /symm_unique0 H0 : \sum_i (co (indpart i)) *: 'm[i] = 0 :> SF.
  by apply sympol_inj => /=.
rewrite -(indpartE i); apply: H0.
apply: (leq_trans _ Hvar).
rewrite -[X in (_ <= X)%N](intpartn_sumn (tnth tPd i)).
exact: size_part.
Qed.

Corollary dimv_homsym : dimv homsympoly = #|[set: intpartn d]|.
Proof. by have:= free_homsymm; rewrite /free size_map -cardE => /eqP <-. Qed.

Lemma homsymm_basis : basis_of homsympoly [seq homsymm l | l <- tPd].
Proof.
by rewrite basisEfree free_homsymm dimv_homsym size_map size_tuple /= leqnn andbT.
Qed.

Lemma homsyms_basis : basis_of homsympoly [seq homsyms l | l <- tPd].
Proof.
rewrite basisEdim size_map size_tuple dimv_homsym leqnn andbT.
(* TODO : rewrite using Kotksa number
rewrite /homsympoly.
apply/span_subvP => s /mapP [/= l]; rewrite {1}/Pd !mem_enum => _ ->{s}.
*)
apply/subvP => p; rewrite dsymP.
move=> /Schur_dec_sym_homog/(_ (dhomog_is_dhomog _)) [co Hp].
have -> : p = \sum_l co l *: homsyms l.
  by apply val_inj => /=; rewrite Hp linear_sum /=; apply eq_bigr => l _.
rewrite span_def.
apply rpred_sum => l _; apply rpredZ.
rewrite big_map (bigD1_seq l) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
apply memv_add; first exact: memv_line.
exact: mem0v.
Qed.

End Homogeneous.
