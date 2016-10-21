(** * Combi.MPoly.homogsym : Homogenous Symmetric Polynomials *)
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
(** * The Space of Homogeneous Symmetric Polynomials *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun finset bigop ssrint ssralg path.
From mathcomp Require Import perm fingroup matrix vector zmodp.
From mathcomp Require ssrnum.
From SsrMultinomials Require Import ssrcomplements poset freeg bigenough mpoly.

Require Import tools ordtype permuted partition Yamanouchi std tableau stdtab.
Require Import antisym Schur_mpoly Schur_altdef sympoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Reserved Notation "{ 'homsym' T [ n , d ] }"
  (at level 0, T, n at level 2, format "{ 'homsym'  T [ n , d ] }").

Definition ishomogsym1 {n} {R : ringType} (d : nat) :
  qualifier 0 {sympoly R[n]} := [qualify p | sympol p \is d.-homog].

Module SymPolyHomogKey.
Fact homogsym1_key {n} {R : ringType} d : pred_key (@ishomogsym1 n R d).
Proof. by []. Qed.
Definition homogsym1_keyed {n R} d := KeyedQualifier (@homogsym1_key n R d).
End SymPolyHomogKey.
Canonical SymPolyHomogKey.homogsym1_keyed.

Notation "d .-homsym" := (@ishomogsym1 _ _ d)
  (at level 1, format "d .-homsym") : form_scope.
Notation "[ 'in' R [ n ] , d .-homsym ]" := (@ishomogsym1 n R d)
  (at level 0, R, n at level 2, d at level 0,
     format "[ 'in'  R [ n ] ,  d .-homsym ]") : form_scope.

Section DefType.

Variable n : nat.
Variable R : ringType.
Variable d : nat.

Implicit Types p q : {sympoly R[n]}.

Lemma homsymE p : (p \is d.-homsym) = (sympol p \is d.-homog).
Proof. by []. Qed.

Lemma symdhom_submod_closed : submod_closed [in R[n], d.-homsym].
Proof.
split => [|a p q Hp Hq]; rewrite !homsymE.
- exact: dhomog0.
- by apply rpredD => //; apply rpredZ.
Qed.
Canonical symdhom_addPred    := AddrPred   symdhom_submod_closed.
Canonical symdhom_oppPred    := OpprPred   symdhom_submod_closed.
Canonical symdhom_zmodPred   := ZmodPred   symdhom_submod_closed.
Canonical symdhom_submodPred := SubmodPred symdhom_submod_closed.

Hypothesis Hvar : (d <= n.+1)%N.

Record homogsym : predArgType :=
  HomogSym {homsym :> {sympoly R[n]}; _ : homsym \is d.-homsym }.

Canonical  homogsym_subType := Eval hnf in [subType for @homsym].
Definition homogsym_eqMixin := Eval hnf in [eqMixin of homogsym by <:].
Canonical  homogsym_eqType  := Eval hnf in EqType homogsym homogsym_eqMixin.

Definition homogsym_choiceMixin := [choiceMixin of homogsym by <:].
Canonical  homogsym_choiceType  :=
  Eval hnf in ChoiceType homogsym homogsym_choiceMixin.

Definition homogsym_of of phant R := homogsym.

Identity Coercion type_homsym_of : homogsym_of >-> homogsym.

Lemma homsym_inj : injective homsym. Proof. exact: val_inj. Qed.

End DefType.

(* We need to break off the section here to let the argument scope *)
(* directives take effect.                                         *)
Bind Scope ring_scope with homogsym_of.
Bind Scope ring_scope with homogsym.
Arguments Scope homogsym [_ ring_scope].
Arguments Scope homsym_inj [_ ring_scope ring_scope _].


Notation "{ 'homsym' T [ n , d ] }" := (homogsym_of n d (Phant T)).

Section HomogSymLModType.

Variable n : nat.
Variable R : ringType.
Variable d : nat.

Definition homogsym_zmodMixin := [zmodMixin of {homsym R[n, d]} by <:].
Canonical  homogsym_zmodType  :=
  Eval hnf in ZmodType {homsym R[n, d]} homogsym_zmodMixin.
Canonical  homogsymen_zmodType  :=
  Eval hnf in ZmodType (homogsym n R d) homogsym_zmodMixin.

Definition homogsym_lmodMixin := [lmodMixin of {homsym R[n, d]} by <:].
Canonical  homogsym_lmodType  :=
  Eval hnf in LmodType R {homsym R[n, d]} homogsym_lmodMixin.
Canonical  homogsymen_lmodType :=
  Eval hnf in LmodType R (homogsym n R d) homogsym_lmodMixin.

Lemma homsym_is_lmorphism :
  lmorphism (@homsym n R d : {homsym R[n, d]} -> {sympoly R[n]}).
Proof. by []. Qed.
Canonical homsym_additive   := Additive   homsym_is_lmorphism.
Canonical homsym_linear     := AddLinear  homsym_is_lmorphism.

Lemma homsym_is_dhomog (x : {homsym R[n, d]}) : sympol x \is d.-homog.
Proof. by case: x. Qed.

Coercion dhomog_of_homogsym (p : {homsym R[n, d]}) :=
  DHomog (homsym_is_dhomog p).

Lemma dhomog_of_sym_is_lmorphism : lmorphism (@homsym n R d).
Proof. by []. Qed.
Canonical dhomog_of_sym_additive := Additive  dhomog_of_sym_is_lmorphism.
Canonical dhomog_of_sym_linear   := AddLinear dhomog_of_sym_is_lmorphism.

End HomogSymLModType.

Import GRing.Theory.
Local Open Scope ring_scope.


Section Vector.

Variable n0 : nat.
Local Notation n := (n0.+1).
Variable R : comRingType.

Variable d : nat.
Local Notation SF := {sympoly R[n]}.
Implicit Type (la : intpartn d).

Definition homsymm la : {homsym R[n, d]} := HomogSym (symm_homog n0 R la).
Definition homsyme la : {homsym R[n, d]} := HomogSym (prod_syme_homog n0 R la).
Definition homsymh la : {homsym R[n, d]} := HomogSym (prod_symh_homog n0 R la).
Definition homsymp la : {homsym R[n, d]} := HomogSym (prod_symp_homog n0 R la).
Definition homsyms la : {homsym R[n, d]} := HomogSym (syms_homog n0 R la).

Lemma homsymmE (f : {homsym R[n, d]}) :
  f = \sum_(l : intpartn d) f@_(mpart l) *: homsymm l.
Proof.
by apply val_inj; rewrite /= {1}(homog_symmE (homsym_is_dhomog f)) !linear_sum.
Qed.

Lemma homogsym_vecaxiom :
  Vector.axiom #|[set p : intpartn d | size p <= n]| {homsym R[n, d]}.
Proof.
pose b := [set p : intpartn d | size p <= n].
pose t := enum_tuple (pred_of_set b).
have sztntht k : size (tnth t k) <= n.
  by have := mem_tnth k t; rewrite /t mem_enum inE.
pose f (p : {homsym R[n, d]}) := \row_(i < #|b|) p@_(mpart (tnth t i)).
exists f => /= [c p q|].
  by apply/matrixP=> i j; rewrite !mxE /= mcoeffD mcoeffZ.
pose g (r : 'rV[R]_(#|b|)) : {homsym R[n, d]} :=
  \sum_(i < #|b|) (r 0 i) *: (homsymm (tnth t i)).
exists g.
- move=> p; rewrite /g /f [RHS]homsymmE.
  rewrite (bigID (mem b)) /= [X in _ + X]big1 ?addr0 => [|la]; first last.
    rewrite inE => /negbTE H .
    by apply val_inj; apply val_inj; rewrite /= /symm H scaler0.
  rewrite [RHS](eq_bigl (fun la => la \in b)); first last.
    by move=> i /=; rewrite inE.
  rewrite [RHS]big_enum /= -[enum _]/(tval t).
  rewrite big_tuple; apply eq_bigr => i _; congr (_ *: _).
  by rewrite mxE.
- move=> r; rewrite /g /f /=; apply/matrixP=> i j.
  rewrite mxE !raddf_sum ord1 /= (bigD1 j) //=.
  rewrite !linearZ /= mcoeff_symm ?sztntht //.
  rewrite perm_eq_refl mulr1 big1 ?addr0 //.
  move=> k Hkj.
  rewrite !linearZ /= mcoeff_symm ?sztntht //.
  suff : ~~(perm_eq (mpart (n := n) (tnth t k)) (mpart (n := n) (tnth t j))).
    by move /negbTE ->; rewrite mulr0.
  move: Hkj; apply contra => /perm_eq_partm/(congr1 val)/eqP.
  rewrite /= !mpartK // !(tnth_nth (rowpartn d)) /t /= => H.
  apply/eqP/val_inj/eqP => /=.
  by rewrite -(nth_uniq (rowpartn d) _ _ (enum_uniq (pred_of_set b))) // -cardE.
Qed.
Definition homogsym_vectMixin := VectMixin homogsym_vecaxiom.
Canonical homogsym_vectType :=
  Eval hnf in VectType R {homsym R[n, d]} homogsym_vectMixin.

End Vector.


Section HomSymField.

Import ssrnum Num.Theory.

Variable n0 d : nat.
Local Notation n := (n0.+1).
Variable R : numFieldType.
Local Notation P := (intpartn d).

Definition symbe := [tuple of [seq homsyme n0 R la | la <- enum {: P}]].
Definition symbh := [tuple of [seq homsymh n0 R la | la <- enum {: P}]].
Definition symbm := [tuple of [seq homsymm n0 R la | la <- enum {: P}]].
Definition symbs := [tuple of [seq homsyms n0 R la | la <- enum {: P}]].
Definition symbp := [tuple of [seq homsymp n0 R la | la <- enum {: P}]].

Local Notation "''pi_' d" :=
  (pihomog [measure of mdeg] d) (at level 5, format "''pi_' d").

Lemma msym_pihomog nv s (p : {mpoly R[nv]}) :
  msym s ('pi_d p) = 'pi_d (msym s p).
Proof.
rewrite (mpolyE p) ![_ (\sum_(m <- msupp p) _)]linear_sum /=.
rewrite [msym s _]linear_sum linear_sum /=.
apply eq_bigr => m _; rewrite !linearZ /=; congr (_ *: _).
rewrite msymX !pihomogX /=.
have -> : mdeg [multinom m ((s^-1)%g i) | i < nv] = mdeg m.
  rewrite /mdeg; apply eq_big_perm.
  apply/tuple_perm_eqP; by exists (s^-1)%g.
by case: (mdeg m == d); rewrite ?msym0 ?msymX.
Qed.

Lemma pihomog_sym nv (p : {mpoly R[nv]}) :
  p \is symmetric -> 'pi_d p \is symmetric.
Proof. by move=> /issymP Hp; apply/issymP => s; rewrite msym_pihomog Hp. Qed.

Lemma vect_to_homsym co (v : intpartn d -> {homsym R[n, d]}) :
  \sum_(i < #|{: P}|) co i *: (map_tuple v (enum_tuple {: P}))`_i =
  \sum_(la : P) (co (enum_rank la)) *: v la.
Proof.
rewrite [RHS]big_enum /= -[enum _]/(val (enum_tuple {: P})).
rewrite big_tuple; apply eq_bigr => i _.
rewrite {1}(tnth_nth (enum_default i)) -/(enum_val i).
rewrite enum_valK; congr (_ *: _).
rewrite [in RHS](tnth_nth (tnth (enum_tuple {: P}) i)).
by rewrite (nth_map (tnth (enum_tuple {: P}) i)) -?cardE.
Qed.

Hypothesis Hd : (d <= n)%N.

Lemma basis_homsym : [set p : intpartn d | (size p <= n)%N] =i {: P}.
Proof using Hd.
move=> la.
rewrite !inE; apply: (leq_trans _ Hd).
by rewrite -[X in (_ <= X)%N](intpartn_sumn la); apply: size_part.
Qed.

Lemma dim_homsym :
  \dim (fullv (vT := [vectType R of {homsym R[n, d]}])) = #|{: P}|.
Proof using Hd.
by rewrite dimvf /Vector.dim /=; apply eq_card; apply basis_homsym.
Qed.

Lemma free_symbm : free symbm.
Proof using Hd.
apply/freeP => co; rewrite vect_to_homsym => /(congr1 val).
rewrite /= linear_sum /= => /symm_unique0 H i.
rewrite -(enum_valK i); apply H.
apply: (leq_trans _ Hd).
rewrite -[X in (_ <= X)%N](intpartn_sumn (enum_val i)).
exact: size_part.
Qed.

Lemma symbm_basis : basis_of fullv symbm.
Proof using Hd.
by rewrite basisEfree free_symbm subvf size_map size_tuple /= dim_homsym.
Qed.

Lemma symbs_basis : basis_of fullv symbs.
Proof using Hd.
rewrite basisEdim size_map size_tuple dim_homsym leqnn andbT.
rewrite -(span_basis symbm_basis).
apply/span_subvP => s /mapP [/= la]; rewrite !mem_enum => _ ->{s}.
have -> : homsymm n0 R la = \sum_(mu : intpartn d) 'K^-1(la, mu) *: homsyms n0 R mu.
  by apply val_inj; rewrite /= (symm_syms _ _ la) !linear_sum.
rewrite span_def; apply memv_suml => mu _; apply memvZ.
rewrite big_map (bigD1_seq mu) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
by apply memv_add; [exact: memv_line | exact: mem0v].
Qed.

Local Notation E := [tuple mesym n R i.+1 | i < n].

Definition monE m : seq nat :=
  rev (flatten [tuple nseq (m i) i.+1 | i < n]).

Lemma monEP m : mnmwgt m = d -> is_part_of_n d (monE m).
Proof using.
rewrite /mnmwgt => H.
rewrite /= is_part_sortedE; apply/and3P; split.
- rewrite /monE sumn_rev sumn_flatten -[X in _ == X]H.
  rewrite -sumnE big_map big_tuple.
  apply/eqP/eq_bigr => /= i _.
  by rewrite -sumnE tnth_mktuple big_nseq iter_addn_0 mulnC.
- rewrite /monE /= rev_sorted.
  apply/(sorted.sortedP 0%N) => //=; first exact: leq_trans.
  move=> i j; rewrite !nth_flatten.
  rewrite size_flatten.
  have -> : shape [seq nseq (m i0) i0.+1 | i0 <- enum 'I_n] = m.
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

Local Lemma Esym : (forall i : 'I_n, E`_i \is symmetric).
Proof using.
move=> i; rewrite (nth_map i) ?size_tuple //.
by rewrite -tnth_nth tnth_ord_tuple mesym_sym.
Qed.
Local Definition pisymhomog_fun q :=
  SymPoly (pihomog_sym (mcomp_sym q Esym)) : {sympoly R[n]}.
Local Lemma pisymhomog_funP q : pisymhomog_fun q \is d.-homsym.
Proof using. by rewrite homsymE /= pihomogP. Qed.
Local Definition pisymhomog := fun q => HomogSym (pisymhomog_funP q).

Lemma intpartn_of_monE m (H : mnmwgt m = d) :
  'X_[m] \mPo E = homsyme n0 R (intpartn_of_mon H).
Proof using.
rewrite comp_mpolyX /= /prod_gen /intpartn_of_mon /monE /=.
rewrite rmorph_prod /= -[RHS](eq_big_perm _ (perm_eq_rev _)) /=.
rewrite big_flatten /= big_map /=.
rewrite /index_enum -!enumT /=; apply eq_bigr => i _.
rewrite big_nseq tnth_mktuple.
by rewrite -big_const_ord prodr_const cardT -cardE card_ord.
Qed.

Lemma pisymhomog_monE m (H : mnmwgt m = d) :
  pisymhomog 'X_[m] = homsyme n0 R (intpartn_of_mon H).
Proof using.
apply val_inj; apply val_inj; rewrite /= intpartn_of_monE /=.
have := prod_syme_homog n0 R (intpartn_of_mon H).
exact: pihomog_dE.
Qed.

Lemma symbe_basis : basis_of fullv symbe.
Proof using Hd.
rewrite basisEdim size_map size_tuple dim_homsym leqnn andbT.
apply/subvP => /= p _; rewrite span_def big_map.
have:= sym_fundamental_homog (sympol_is_symmetric p) (homsym_is_dhomog p).
move=> [t [Hp /dhomogP Hhomt]].
have {Hp} -> : p = \sum_(m <- msupp t) t@_m *: pisymhomog 'X_[m].
  apply val_inj; apply val_inj; rewrite /= -{1}Hp {1}(mpolyE t) {Hp}.
  rewrite !linear_sum /=; apply eq_big_seq => m /Hhomt /= Hm.
  rewrite !linearZ /=; congr (_ *: _).
  rewrite pihomog_dE // -[X in _ \is X.-homog]Hm.
  exact: homog_X_mPo_elem.
rewrite big_seq; apply memv_suml => m Hm; apply memvZ.
rewrite (pisymhomog_monE (Hhomt m Hm)); move: (intpartn_of_mon _) => {m Hm} la.
rewrite (bigD1_seq la) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
apply memv_add; first exact: memv_line.
exact: mem0v.
Qed.

Lemma symbh_basis : basis_of fullv symbh.
Proof using Hd.
rewrite basisEdim size_map size_tuple dim_homsym leqnn andbT.
rewrite -(span_basis symbe_basis).
apply/span_subvP => s /mapP [/= la]; rewrite !mem_enum => _ ->{s}.
have -> : homsyme n0 R la =
         \sum_(mu : intpartn d)
          coeff_prodgen_intpartn (signed_sum_compn R) la mu *: homsymh n0 R mu.
  by apply val_inj; rewrite /= linear_sum /= (prod_prodgen (syme_to_symh n0 R)).
rewrite span_def; apply memv_suml => mu _; apply memvZ.
rewrite big_map (bigD1_seq mu) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
by apply memv_add; [exact: memv_line | exact: mem0v].
Qed.

Lemma symbp_basis : basis_of fullv symbp.
Proof using Hd.
rewrite basisEdim size_map size_tuple dim_homsym leqnn andbT.
rewrite -(span_basis symbh_basis).
apply/span_subvP => s /mapP [/= la]; rewrite !mem_enum => _ ->{s}.
pose co := fun (n : nat) (l : intpartn n) => (permcent.zcard l)%:R^-1 : R.
have -> : homsymh n0 R la =
         \sum_(mu : intpartn d)
          coeff_prodgen_intpartn co la mu *: homsymp n0 R mu.
  by apply val_inj; rewrite /= linear_sum /= (prod_prodgen (symh_to_symp n0 R)).
rewrite span_def; apply memv_suml => mu _; apply memvZ.
rewrite big_map (bigD1_seq mu) /= ?mem_enum ?inE ?enum_uniq //.
rewrite -[X in X \in _]addr0.
by apply memv_add; [exact: memv_line | exact: mem0v].
Qed.

End HomSymField.

From mathcomp Require Import ssrnum algC algnum.
Import GRing.Theory Num.Theory.
Require Import permcent.

Reserved Notation "'[ p | q ]"
  (at level 2, format "'[hv' ''[' p | '/ '  q ] ']'").

Section ScalarProduct.

Variable n0 d : nat.
Local Notation n := (n0.+1).
Local Notation P := (intpartn d).
Local Notation algCF := [numFieldType of algC].
Local Notation symH := {homsym algC[n, d]}.

Definition homsymdot (p q : symH) :=
  \sum_(i < #|{: P}|) (zcard (enum_val i))%:R *
  coord (symbp n0 d algCF) i p * (coord (symbp n0 d algCF) i q)^*.
Definition homsymdotr_head k p q := let: tt := k in homsymdot q p.

Notation homsymdotr := (homsymdotr_head tt).
Notation "''[' u | v ]" := (homsymdot u v) : ring_scope.

Lemma homsymdotE p q :
  '[ p | q ] =
  \sum_(la : intpartn d) (zcard la)%:R *
    coord (symbp n0 d algCF) (enum_rank la) p *
    (coord (symbp n0 d algCF) (enum_rank la) q)^*.
Proof.
rewrite /homsymdot [RHS](reindex (enum_val (A := {: P}))) /=; first last.
  by apply (enum_val_bij_in (x0 := (rowpartn d))).
by apply/eq_bigr => i _; rewrite enum_valK.
Qed.
Lemma homsymdotrE p q : homsymdotr p q = '[q | p]. Proof. by []. Qed.

Lemma homsymdotr_is_linear p :
  linear (homsymdotr p : symH -> algC^o).
Proof.
move=> a u v.
rewrite linear_sum -big_split; apply: eq_bigr => x _ /=.
rewrite linearD linearZ /= mulrDr mulrDl !mulrA; congr (_ + _).
by rewrite [_ * a]mulrC -!mulrA.
Qed.
Canonical homsymdotr_additive p := Additive (homsymdotr_is_linear p).
Canonical homsymdotr_linear p := Linear (homsymdotr_is_linear p).


Lemma homsymdot0l p : '[0 | p] = 0.
Proof. by rewrite -homsymdotrE linear0. Qed.
Lemma homsymdotNl p q : '[- q | p] = - '[q | p].
Proof. by rewrite -!homsymdotrE linearN. Qed.
Lemma homsymdotDl p q1 q2 : '[q1 + q2 | p] = '[q1 | p] + '[q2 | p].
Proof. by rewrite -!homsymdotrE linearD. Qed.
Lemma homsymdotBl p q1 q2 : '[q1 - q2 | p] = '[q1 | p] - '[q2 | p].
Proof. by rewrite -!homsymdotrE linearB. Qed.
Lemma homsymdotMnl p q n : '[q *+ n | p] = '[q | p] *+ n.
Proof. by rewrite -!homsymdotrE linearMn. Qed.
Lemma homsymdot_suml p I r (P : pred I) (q : I -> symH) :
  '[\sum_(i <- r | P i) q i | p] = \sum_(i <- r | P i) '[q i | p].
Proof. by rewrite -!homsymdotrE linear_sum. Qed.
Lemma homsymdotZl p a q : '[a *: q | p] = a * '[q | p].
Proof. by rewrite -!homsymdotrE linearZ. Qed.

Lemma homsymdotC p q : '[p | q] = ('[q | p])^*.
Proof.
rewrite /homsymdot rmorph_sum /=.
apply: eq_bigr=> x _; rewrite !rmorphM conjCK -!mulrA.
have /geC0_conj -> : 0 <= ((zcard (enum_val x))%:R : algC).
  by rewrite -nnegrE ?nnegrE ?ler01 ?ler0n ?oner_neq0.
by congr (_ * _); rewrite mulrC.
Qed.

Lemma homsymdotBr p q1 q2 : '[p | q1 - q2] = '[p | q1] - '[p | q2].
Proof. by rewrite !(homsymdotC p) -rmorphB homsymdotBl. Qed.
Canonical homsymdot_additive p := Additive (homsymdotBr p).

Lemma homsymdot0r p : '[p | 0] = 0. Proof. exact: raddf0. Qed.
Lemma homsymdotNr p q : '[p | - q] = - '[p | q].
Proof. exact: raddfN. Qed.
Lemma homsymdotDr p q1 q2 : '[p | q1 + q2] = '[p | q1] + '[p | q2].
Proof. exact: raddfD. Qed.
Lemma homsymdotMnr p q n : '[p | q *+ n] = '[p | q] *+ n.
Proof. exact: raddfMn. Qed.
Lemma homsymdot_sumr p I r (P : pred I) (q : I -> symH) :
  '[p | \sum_(i <- r | P i) q i] = \sum_(i <- r | P i) '[p | q i].
Proof. exact: raddf_sum. Qed.
Lemma homsymdotZr a p q : '[p | a *: q] = a^* * '[p | q].
Proof. by rewrite !(homsymdotC p) homsymdotZl rmorphM. Qed.

Lemma symbpE la : homsymp n0 algCF la = (symbp n0 d algCF)`_(enum_rank la).
Proof. by rewrite /symbp tupleE /= (nth_map la) ?nth_enum_rank // -cardE. Qed.
Lemma coord_symbp (Hd : (d <= n)%N) la mu :
  coord (symbp n0 d algCF) (enum_rank mu) (homsymp n0 algCF la) = (la == mu)%:R.
Proof.
rewrite !symbpE !(coord_free _ _ (basis_free (symbp_basis _ Hd))).
by rewrite !(inj_eq enum_rank_inj).
Qed.

Lemma homsymdotp (Hd : (d <= n)%N) la mu :
  '[ homsymp _ algCF la | homsymp _ algCF mu ] = (zcard la)%:R * (la == mu)%:R.
Proof.
rewrite homsymdotE (bigD1 mu) //= big1 ?addr0 => [| nu /negbTE Hneq].
- rewrite !(coord_symbp Hd) eq_refl /= conjC1 mulr1.
  by case: eqP => [-> //| _]; rewrite !mulr0.
- by rewrite !(coord_symbp Hd) [mu == nu]eq_sym Hneq conjC0 mulr0.
Qed.

End ScalarProduct.

Notation homsymdotr := (homsymdotr_head tt).
Notation "''[' u | v ]" := (homsymdot u v) : ring_scope.
