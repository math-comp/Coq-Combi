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
From mathcomp Require Import tuple finfun finset bigop ssrint ssralg path perm fingroup.
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
rewrite /homsympoly.
apply/span_subvP => s /mapP [/= l]; rewrite {1}/Pd !mem_enum => _ ->{s}.
have -> : homsymm l = \sum_(m : intpartn d) 'K^-1(l, m) *: homsyms m.
  apply val_inj; rewrite /=.
  rewrite (symm_syms _ _ l) [LHS](linear_sum (@sympol_lrmorphism _ _)) /=.
  by rewrite !linear_sum /=.
rewrite span_def.
apply rpred_sum => /= m _; apply rpredZ.
rewrite big_map (bigD1_seq m) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
by apply memv_add; [exact: memv_line | exact: mem0v].
Qed.


Local Notation E := [tuple mesym n.+1 R i.+1 | i < n.+1].

Definition monE m : seq nat :=
  rev (flatten [tuple nseq (m i) i.+1 | i < n.+1]).

Lemma monEP m : mnmwgt m = d -> is_part_of_n d (monE m).
Proof.
rewrite /mnmwgt => H.
rewrite /= is_part_sortedE; apply/and3P; split.
- rewrite /monE sumn_rev sumn_flatten -H.
  rewrite -sumnE big_map big_tuple.
  apply/eqP/eq_bigr => /= i _.
  by rewrite -sumnE tnth_mktuple big_nseq iter_addn_0 mulnC.
- rewrite /monE /= rev_sorted.
  apply/(sorted.sortedP 0%N) => //=; first exact: leq_trans.
  move=> i j; rewrite !nth_flatten.
  rewrite size_flatten.
  have -> : shape [seq nseq (m i0) i0.+1 | i0 <- enum 'I_n.+1] = m.
    rewrite /shape -map_comp (tuple_map_ord m) /=.
    apply eq_map => k /=.
    by rewrite size_nseq.
  move=> Hijm; have:= Hijm => /andP [Hij Hjm]; have Him := leq_ltn_trans Hij Hjm.
  move/reshape_coord_leq: Hijm.
  have:= reshape_coordP Hjm; have:= reshape_coordP Him.
  case: (reshape_coord m i) (reshape_coord m j) => [r1 c1] [r2 c2].
  rewrite size_tuple => [] [Hr1 Hc1] [Hrc Hc2].
  do 2 (rewrite (nth_map ord0); last by rewrite size_enum_ord).
  rewrite !(mnm_nth 0) !nth_nseq !nth_enum_ord //=.
  rewrite Hc1 Hc2 ltnS.
  by move=> [Hr|[-> _]] //; apply ltnW.
- rewrite /monE; rewrite mem_rev; apply/flatten_mapP => /= [[s _]].
  by move=> /nseqP [].
Qed.
Definition intpartn_of_mon m (H : mnmwgt m = d) := IntPartN (monEP H).

Lemma intpartn_of_monE m (H : mnmwgt m = d) :
  'X_[m] \mPo E = homsyme (intpartn_of_mon H).
Proof.
rewrite comp_mpolyX /= /prod_gen /intpartn_of_mon /monE /=.
rewrite [RHS](rmorph_prod (@sympol_lrmorphism _ _)) /=.
rewrite -[RHS](eq_big_perm _ (perm_eq_rev _)) /=.
rewrite big_flatten /= big_map /=.
rewrite /index_enum -!enumT /=; apply eq_bigr => i _.
rewrite big_nseq tnth_mktuple.
by rewrite -big_const_ord prodr_const cardT -cardE card_ord.
Qed.

Lemma homsyme_basis : basis_of homsympoly [seq homsyme l | l <- tPd].
Proof.
rewrite basisEdim size_map size_tuple dimv_homsym leqnn andbT.
apply/subvP => [[p Hhomp]] /=; rewrite span_def big_map.
rewrite dsymP /= => /sym_fundamental_homog/(_ Hhomp) [t [Hp /dhomogP Hhomt]].
pose pid := fun p => @DHomog n.+1 R d _ (pihomogP [measure of mdeg] d p).
have {Hp} -> : DHomog Hhomp = \sum_(m <- msupp t) t@_m *: pid ('X_[m] \mPo E).
  apply val_inj; rewrite /= -{1}Hp {1}(mpolyE t) {Hp}.
  rewrite !linear_sum /=; apply eq_big_seq => m /Hhomt /= <-.
  rewrite !linearZ /=; congr (_ *: _); rewrite pihomog_dE //.
  exact: homog_X_mPo_elem.
rewrite big_seq; apply rpred_sum => l /Hhomt /= Hl; apply rpredZ.
rewrite intpartn_of_monE; move: (intpartn_of_mon Hl) => lam.
rewrite {}/pid [DHomog _](_ : _ = homsyme lam); first last.
  by apply val_inj; rewrite /= pihomog_dE //; apply: prod_syme_homog.
rewrite (bigD1_seq lam) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
apply memv_add; first exact: memv_line.
exact: mem0v.
Qed.

End Homogeneous.
