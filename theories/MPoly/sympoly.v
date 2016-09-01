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

Require Import tools ordtype permuted partition Yamanouchi std tableau stdtab antisym.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.


Lemma boolRP (R : ringType) (b : bool) : reflect (b%:R = 0 :> R) (~~b).
Proof using.
apply (iffP idP) => [/negbTE -> // | H].
apply/negP => Hb; move: H; rewrite Hb /= => /eqP.
by rewrite oner_eq0.
Qed.

Reserved Notation "{ 'sympoly' T [ n ] }"
  (at level 0, T, n at level 2, format "{ 'sympoly'  T [ n ] }").


Section DefType.

Variable n : nat.
Variable R : ringType.

Structure sympoly : predArgType :=
  SymPoly {sympol :> {mpoly R[n]}; _ : sympol \is symmetric}.

Canonical sympoly_subType := Eval hnf in [subType for sympol].
Definition sympoly_eqMixin := Eval hnf in [eqMixin of sympoly by <:].
Canonical sympoly_eqType := Eval hnf in EqType sympoly sympoly_eqMixin.
Definition sympoly_choiceMixin := Eval hnf in [choiceMixin of sympoly by <:].
Canonical sympoly_choiceType :=
  Eval hnf in ChoiceType sympoly sympoly_choiceMixin.

Definition sympoly_of of phant R := sympoly.

Identity Coercion type_sympoly_of : sympoly_of >-> sympoly.

Lemma sympol_inj : injective sympol. Proof. exact: val_inj. Qed.

End DefType.

(* We need to break off the section here to let the argument scope *)
(* directives take effect.                                         *)
Bind Scope ring_scope with sympoly_of.
Bind Scope ring_scope with sympoly.
Arguments Scope sympol [_ ring_scope].
Arguments Scope sympol_inj [_ ring_scope ring_scope _].

Notation "{ 'sympoly' T [ n ] }" := (sympoly_of n (Phant T)).


Section SymPolyRingType.

Variable n : nat.
Variable R : ringType.

Definition sympoly_zmodMixin :=
  Eval hnf in [zmodMixin of {sympoly R[n]} by <:].
Canonical sympoly_zmodType :=
  Eval hnf in ZmodType {sympoly R[n]} sympoly_zmodMixin.
Definition sympoly_ringMixin :=
  Eval hnf in [ringMixin of {sympoly R[n]} by <:].
Canonical sympoly_ringType :=
  Eval hnf in RingType {sympoly R[n]} sympoly_ringMixin.
Definition sympoly_lmodMixin :=
  Eval hnf in [lmodMixin of {sympoly R[n]} by <:].
Canonical sympoly_lmodType :=
  Eval hnf in LmodType R {sympoly R[n]} sympoly_lmodMixin.
Definition sympoly_lalgMixin :=
  Eval hnf in [lalgMixin of {sympoly R[n]} by <:].
Canonical sympoly_lalgType :=
  Eval hnf in LalgType R {sympoly R[n]} sympoly_lalgMixin.

Lemma sympol_is_lrmorphism :
  lrmorphism (@sympol n R : {sympoly R[n]} -> {mpoly R[n]}).
Proof. by []. Qed.
Canonical sympol_lrmorphism := LRMorphism sympol_is_lrmorphism.

Lemma sympol_is_symmetric (x : {sympoly R[n]}) : sympol x \is symmetric.
Proof. by case: x. Qed.

End SymPolyRingType.

Hint Resolve sympol_is_symmetric.


Section SymPolyComRingType.

Variable n : nat.
Variable R : comRingType.

Definition sympoly_comRingMixin :=
  Eval hnf in [comRingMixin of {sympoly R[n]} by <:].
Canonical sympoly_comRingType :=
  Eval hnf in ComRingType {sympoly R[n]} sympoly_comRingMixin.
Definition sympoly_algMixin :=
  Eval hnf in [algMixin of {sympoly R[n]} by <:].
Canonical sympoly_algType :=
  Eval hnf in AlgType R {sympoly R[n]} sympoly_algMixin.

End SymPolyComRingType.

Section SymPolyIdomainType.

Variable n : nat.
Variable R : idomainType.

Definition sympoly_unitRingMixin :=
  Eval hnf in [unitRingMixin of {sympoly R[n]} by <:].
Canonical sympoly_unitRingType :=
  Eval hnf in UnitRingType {sympoly R[n]} sympoly_unitRingMixin.
Canonical sympoly_comUnitRingType :=
  Eval hnf in [comUnitRingType of {sympoly R[n]}].
Definition sympoly_idomainMixin :=
  Eval hnf in [idomainMixin of {sympoly R[n]} by <:].
Canonical sympoly_idomainType :=
  Eval hnf in IdomainType {sympoly R[n]} sympoly_idomainMixin.
Canonical sympoly_unitAlgType :=
  Eval hnf in [unitAlgType R of {sympoly R[n]}].

End SymPolyIdomainType.



Section Bases.

Variable n : nat.
Variable R : ringType.
Implicit Type m : 'X_{1.. n}.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").


(* From  mpoly.v : \sum_(h : {set 'I_n} | #|h| == k) \prod_(i in h) 'X_i. *)
Fact elementary_sym d : mesym n R d \is symmetric.
Proof using. exact: mesym_sym. Qed.
Definition elementary d : {sympoly R[n]} := SymPoly (elementary_sym d).
Lemma mesym_homog d : mesym n R d \is d.-homog.
Proof using.
apply/dhomogP => m.
rewrite msupp_mesymP => /existsP [] s /andP [] /eqP <- {d} /eqP -> {m}.
exact: mdeg_mesym1.
Qed.
Lemma elementary_homog d : sympol (elementary d) \is d.-homog.
Proof using. by rewrite mesym_homog. Qed.

Definition complete_pol d  : {mpoly R[n]} :=
  \sum_(m : 'X_{1..n < d.+1} | mdeg m == d) 'X_[m].
Lemma mcoeff_complete d m : (complete_pol d)@_m = (mdeg m == d)%:R.
Proof.
rewrite linear_sum /=.
case: (altP (mdeg m =P d)) => [<- | Hd] /=.
- have Hsm : mdeg m < (mdeg m).+1 by [].
  rewrite (bigD1 (BMultinom Hsm)) //= mcoeffX eq_refl big1 ?addr0 //=.
  by move=> mon /andP [_ /negbTE]; rewrite {1}/eq_op /= mcoeffX => ->.
- rewrite big1 // => mon /eqP Hd1; rewrite mcoeffX.
  by apply/boolRP; move: Hd; rewrite -{1}Hd1; apply contra=> /eqP ->.
Qed.
Fact complete_sym d : complete_pol d \is symmetric.
Proof using.
apply/issymP => s; rewrite -mpolyP => m.
by rewrite mcoeff_sym !mcoeff_complete mdeg_mperm.
Qed.
Definition complete d : {sympoly R[n]} := SymPoly (complete_sym d).
Lemma complete_homog d : sympol (complete d) \is d.-homog.
Proof using. by apply rpred_sum => m /eqP H; rewrite dhomogX /= H. Qed.

Definition power_sum_pol d  : {mpoly R[n]} := \sum_(i < n) 'X_i ^+ d.
Fact power_sum_sym d : power_sum_pol d \is symmetric.
Proof using.
apply/issymP => s.
rewrite linear_sum /= (reindex_inj (h := s^-1))%g /=; last by apply/perm_inj.
apply eq_bigr => i _; rewrite rmorphX /=; congr (_ ^+ _).
rewrite msymX /=; congr mpolyX.
rewrite mnmP => j; rewrite !mnmE /=; congr nat_of_bool.
by apply/eqP/eqP => [|->//]; apply: perm_inj.
Qed.
Definition power_sum d : {sympoly R[n]} := SymPoly (power_sum_sym d).
Lemma power_sum_homog d : sympol (power_sum d) \is d.-homog.
Proof using.
apply rpred_sum => m _.
have /(dhomogMn d) : ('X_m : {mpoly R[n]}) \is 1.-homog.
  by rewrite dhomogX /= mdeg1.
by rewrite mul1n.
Qed.


Definition monomial_pol (sh : n.-tuple nat) : {mpoly R[n]} :=
  (\sum_(p : permuted sh) 'X_[Multinom p] ).
Lemma mcoeff_monomial sh m : (monomial_pol sh)@_m = (perm_eq sh m)%:R.
Proof.
rewrite linear_sum /=.
case: (boolP (perm_eq sh m)) => /= [| /(elimN idP)] Hperm.
- rewrite (bigD1 (Permuted Hperm)) //= (_ : [multinom m] = m);
    last exact: val_inj.
  rewrite mcoeffX eq_refl /= big1 ?addr0 // => p /eqP Hp.
  rewrite mcoeffX; case: (altP (_ =P _)) => //= Heq.
  by exfalso; apply: Hp; apply val_inj; rewrite /= -Heq.
- rewrite big1 // => p _.
  rewrite mcoeffX; case: (altP (_ =P _)) => //= Heq.
  by exfalso; apply Hperm; rewrite -Heq /=; exact: permutedP.
Qed.
Fact monomial_sym sh : monomial_pol sh \is symmetric.
Proof.
apply/issymP => s; apply/mpolyP => m.
rewrite mcoeff_sym !mcoeff_monomial.
have: perm_eq (m#s) m by apply/tuple_perm_eqP; exists s.
by move=> /perm_eqrP ->.
Qed.
Definition monomial sh : {sympoly R[n]} :=
  if size sh <= n then SymPoly (monomial_sym (mpart sh)) else 0 : {sympoly R[n]}.
Lemma monomial_homog d (sh : intpartn d) :
  sympol (monomial sh) \is d.-homog.
Proof using.
rewrite /monomial; case: leqP => [/= Hsz | _]; last exact: dhomog0.
rewrite /= unfold_in; apply/allP => /= m.
rewrite mcoeff_msupp mcoeff_monomial.
case: (boolP (perm_eq _ _)) => [Hperm _ | _]; last by rewrite /= eq_refl.
rewrite /mdeg sumnE -(intpartn_sumn sh).
move: Hperm => /perm_sumn <-{m}.
rewrite -{2}(mpartK _ Hsz) // is_dominant_partm; last exact: mpart_is_dominant.
apply/eqP; rewrite -!sumnE big_filter.
rewrite [LHS](bigID (fun i => i == 0%N)) /= big1 ?add1n //.
by move=> i /eqP.
Qed.

Lemma issym_monomialE (p : {mpoly R[n]}) :
  p \is symmetric ->
  p = \sum_(m <- msupp p | m \is dominant) p@_m *: monomial (partm m).
Proof.
move=> Hsym; apply/mpolyP => m.
case: (boolP (m \in msupp p)) => Hm.
- rewrite -big_filter (bigD1_seq (mpart (partm m))) /=; first last.
  + by apply filter_uniq; apply msupp_uniq.
  + rewrite mem_filter mpart_is_dominant //= mcoeff_msupp.
    have [s /eqP ->] := mpart_partm_perm m.
    by rewrite -mcoeff_sym (issymP p Hsym) -mcoeff_msupp.
  rewrite linearD linearZ /= mpartK ?size_partm //.
  rewrite big_filter_cond /=.
  have -> : p@_(mpart (partm m)) = p@_m.
    have [/= s /eqP ->]:= mpart_partm_perm m.
    by rewrite -mcoeff_sym (issymP p Hsym).
  have -> : (monomial (partm m))@_m = 1.
    by rewrite /monomial size_partm /= mcoeff_monomial perm_eq_sym partm_perm_eqK.
  rewrite mulr1 -[LHS]addr0; congr (_ + _); symmetry.
  rewrite -![sympol _]/(sympol_lrmorphism n R _) !raddf_sum /=.
  rewrite big_seq_cond; apply big1 => /= m' /and3P [_ Hdom Hm'].
  rewrite mcoeffZ /monomial /= size_partm /= mcoeff_monomial.
  rewrite [perm_eq _ _](_ : _ = false) /= ?mulr0 //.
  apply (introF idP) => /perm_eq_partm
                         /(congr1 (fun x : intpart => mpart (n := n) x)) H.
  by move: Hm'; rewrite -{}H !(partmK Hdom) eq_refl.
- rewrite (memN_msupp_eq0 Hm); symmetry.
  rewrite -![sympol _]/(sympol_lrmorphism n R _) !raddf_sum /=.
  rewrite big_seq_cond; apply big1 => /= m' /andP [Hsupp Hdom].
  rewrite mcoeffZ /monomial /= size_partm /= mcoeff_monomial partmK //.
  rewrite [perm_eq _ _](_ : _ = false) /= ?mulr0 //.
  apply (introF idP) => /mnm_perm_eq [/= s /eqP Hs].
  move: Hm Hsupp; rewrite -mcoeff_eq0 mcoeff_msupp Hs.
  rewrite -mcoeff_sym (issymP p Hsym) => /eqP ->.
  by rewrite eq_refl.
Qed.

Lemma monomial_genE (p : {sympoly R[n]}) :
  p = \sum_(m <- msupp p | m \is dominant) p@_m *: monomial (partm m).
Proof. by apply val_inj => /=; apply issym_monomialE. Qed.


Lemma size_mpart_in_supp (f : {mpoly R[n]}) d (p : intpartn d) :
  f \is d.-homog -> mpart p \in msupp f -> size p <= n.
Proof.
rewrite /mpart; case: leqP => //= H1 /dhomogP H/H /=.
rewrite /= mdeg0 => Hd; subst d.
by move: H1; rewrite intpartn0.
Qed.

Lemma homog_monomialE d (p : {sympoly R[n]}) :
  sympol p \is d.-homog ->
  p = \sum_(l : intpartn d) p@_(mpart l) *: monomial l.
Proof.
move=> Hhomog; rewrite {1}(monomial_genE p).
apply val_inj => /=.
rewrite [LHS](linear_sum (@sympol_lrmorphism _ _)).
rewrite [RHS](linear_sum (@sympol_lrmorphism _ _)) /=.
rewrite (bigID (fun i : intpartn d => mpart i \in msupp p)) /=.
rewrite [X in _ + X]big1 ?addr0;
  last by move=> i /memN_msupp_eq0 ->; rewrite scale0r.
rewrite (eq_bigr (fun i : intpartn d =>
           p@_(mpart i) *:
            sympol (monomial (partm (n := n) (mpart i)))));
    first last.
  move=> i Hi; congr (_ *: _); congr sympol; congr monomial.
  by rewrite mpartK //; apply (size_mpart_in_supp Hhomog Hi).
rewrite /index_enum -enumT.
transitivity (\sum_(m <- [seq mpart (i : intpartn d) |
                          i <- enum (intpartn_finType d)] |
                    m \in msupp p)
      p@_m *: sympol (monomial (partm m))); last by rewrite big_map /=.
rewrite -big_filter -[RHS]big_filter; apply eq_big_perm; apply uniq_perm_eq.
- by apply filter_uniq; apply msupp_uniq.
- rewrite filter_map map_inj_in_uniq; first by apply filter_uniq; apply enum_uniq.
  move=> /= c1 c2; rewrite !mem_filter /= => /andP [Hc1 _] /andP [Hc2 _].
  move=> /(congr1 (@partm n)) /(congr1 val) /=.
  rewrite !mpartK // ?(size_mpart_in_supp _ Hc1) ?(size_mpart_in_supp _ Hc2) //.
  exact: val_inj.
- move=> /= m; rewrite !mem_filter andbC.
  case: (boolP (m \in msupp p)) => //= Hsupp.
  apply/idP/mapP => /= [Hdom | [l _ ->]]; last exact: mpart_is_dominant.
  have Hp : is_part_of_n d (partm m).
    rewrite /is_part_of_n /= intpartP andbT sumn_partm //.
    by move: Hhomog => /dhomogP/(_ _ Hsupp) /= ->.
  exists (IntPartN Hp); first by rewrite mem_enum.
  by rewrite /= partmK.
Qed.

(** Basis at degree 0 *)
Lemma elementary0 : elementary 0 = 1.
Proof using. by apply val_inj; rewrite /= mesym0E. Qed.

Lemma powersum0 : power_sum 0 = n%:R.
Proof using.
apply /val_inj.
rewrite /= /power_sum_pol (eq_bigr (fun _ => 1));
  last by move=> i _; rewrite expr0.
rewrite sumr_const card_ord /=.
by rewrite [RHS](raddfMn (@sympol_lrmorphism _ _) n).
Qed.

Lemma complete0 : complete 0 = 1.
Proof using.
have Hd0 : (mdeg (0%MM : 'X_{1..n})) < 1 by rewrite mdeg0.
apply val_inj => /=.
rewrite /complete_pol (big_pred1 (BMultinom Hd0)); first last.
  by move=> m; rewrite /= mdeg_eq0 {2}/eq_op.
by rewrite mpolyX0.
Qed.


(** All basis agrees at degree 1 *)
Lemma elementary1 : elementary 1 = \sum_(i < n) 'X_i :> {mpoly R[n]}.
Proof using. by rewrite /= mesym1E. Qed.

Lemma power_sum1 : power_sum 1 = \sum_(i < n) 'X_i :> {mpoly R[n]}.
Proof using. by apply eq_bigr => i _; rewrite expr1. Qed.

Lemma complete1 : complete 1 = \sum_(i < n) 'X_i :> {mpoly R[n]}.
Proof using.
rewrite /complete -mpolyP => m.
rewrite !raddf_sum /=.
case: (boolP (mdeg m == 1%N)) => [/mdeg1P [] i /eqP -> | Hm].
- have Hdm : (mdeg U_(i))%MM < 2 by rewrite mdeg1.
  rewrite (bigD1 (BMultinom Hdm)) /=; last by rewrite mdeg1.
  rewrite mcoeffX eq_refl big1; first last.
    move=> mm /andP [] _ /negbTE.
    by rewrite mcoeffX {1}/eq_op /= => ->.
  rewrite /= (bigD1 i) // mcoeffX eq_refl /= big1 // => j /negbTE H.
  rewrite mcoeffX.
  case eqP => //; rewrite mnmP => /(_ i).
  by rewrite !mnm1E H eq_refl.
- rewrite big1; first last.
    move=> p /eqP Hp; rewrite mcoeffX.
    case eqP => // Hpm; subst m.
    by move: Hm; rewrite Hp.
  rewrite big1 // => p _.
  rewrite mcoeffX; case eqP => // Hmm; subst m.
  by rewrite mdeg1 in Hm.
Qed.

End Bases.

Notation "''e_' k" := (elementary _ _ k)
                              (at level 8, k at level 2, format "''e_' k").
Notation "''h_' k" := (complete _ _ k)
                              (at level 8, k at level 2, format "''h_' k").
Notation "''p_' k" := (power_sum _ _ k)
                              (at level 8, k at level 2, format "''p_' k").

(** Prod of generator *)

Section ProdGen.

Variable n : nat.
Variable R : comRingType.
Implicit Type m : 'X_{1.. n}.

Section Defs.

Variable gen : nat -> {sympoly R[n]}.
Hypothesis gen_homog : forall d, sympol (gen d) \is d.-homog.

Definition prod_gen d (sh : intpartn d) := \prod_(i <- sh) gen i.
Lemma prod_gen_homog d (sh : intpartn d) :
  sympol (prod_gen sh) \is d.-homog.
Proof using gen_homog.
rewrite /prod_gen; case: sh => sh /= /andP [/eqP <- _] {d}.
elim: sh => [| d sh IHsh] /=; first by rewrite big_nil /= dhomog1.
by rewrite big_cons; apply dhomogM; first exact: gen_homog.
Qed.

Lemma prod_genM c d (l : intpartn c) (k : intpartn d) :
  (prod_gen l) * (prod_gen k) = (prod_gen (union_intpartn l k)).
Proof using.
by rewrite /prod_gen (eq_big_perm _ (perm_union_intpartn l k)) big_cat.
Qed.

End Defs.

Definition prod_elementary := prod_gen (@elementary n R).
Definition prod_elementary_homog := prod_gen_homog (@elementary_homog n R).
Definition prod_complete := prod_gen (@complete n R).
Definition prod_complete_homog := prod_gen_homog (@complete_homog n R).
Definition prod_power_sum := prod_gen (@power_sum n R).
Definition prod_power_sum_homog := prod_gen_homog (@power_sum_homog n R).

End ProdGen.

Notation "''e[' k ]" := (prod_elementary _ _ k)
                              (at level 8, k at level 2, format "''e[' k ]").
Notation "''h[' k ]" := (prod_complete _ _ k)
                              (at level 8, k at level 2, format "''h[' k ]").
Notation "''p[' k ]" := (prod_power_sum _ _ k)
                              (at level 8, k at level 2, format "''p[' k ]").



Require Import composition.

Section ChangeBasis.

Variable nvar : nat.
Variable R : comRingType.
Implicit Type m : 'X_{1.. nvar}.
Local Notation SF := {sympoly R[nvar]}.

Lemma sum_complete_elementary (d : nat) :
  \sum_(0 <= i < d.+1) (-1)^+i *: ('h_i * 'e_(d - i)) = 0 :> SF.
Proof.
apply val_inj => /=.
rewrite -[sympol _]/(sympol_lrmorphism nvar R _) rmorph_sum /=.
apply mpolyP => m; rewrite linear_sum /=.
Admitted.

Lemma elementary_completeE (d : nat) :
  d != 0%N ->
  'e_d = \sum_(1 <= i < d.+1) 'h_i * ((-1)^+(d - i) *: 'e_(d - i)) :> SF.
Proof.
move=> Hd.
have := sum_complete_elementary d.
rewrite big_nat_recl // expr0 scale1r complete0 mul1r subn0 => /eqP.
rewrite (addr_eq0 'e_d) => /eqP ->; rewrite big_add1 /= -sumrN.
rewrite !big_nat; apply eq_bigr => i /= Hi.
rewrite scalerAr -mulrN; congr (_ * _).
rewrite -scaleNr; congr (_ *: _).
(*
apply/eqP; rewrite -(subr_eq0 'e_d) -oppr_eq0 opprB; apply/eqP.
rewrite big_add1 /=.
rewrite -[RHS](sum_complete_elementary d) [RHS]big_nat_recl //=.

rewrite big_nat_rev /= add0n big_nat.
(*rewrite (eq_bigr (fun i => (-1) ^+ i.+1 *: ('e_i.+1 * 'h_(d - i.+1)))); first last.
  by move=> i /andP [_ Hi]; rewrite subKn // mulrC. *)
rewrite -big_nat /=.
rewrite -[RHS](sum_complete_elementary d) [RHS]big_nat_recr //=.
congr (_ + _).
apply val_inj => /=; apply/eqP.
have:= sum_complete_elementary d.
rewrite -[X in X = 0](big_mkord xpredT (fun i => (-1)^+i *: 'e_i * 'h_(d - i))).
rewrite -[X in _ -> _ = X](big_mkord xpredT (fun i => (-1)^+(d - i) *: 'h_i * 'e_(d - i))).
rewrite big_nat_rev /= big_nat_recl // !add0n !subSS subn0 subnn.
rewrite complete0 mulr1 => /eqP.
rewrite addr_eq0.
apply val_inj => /=.
rewrite -[sympol _]/(sympol_lrmorphism nvar R _) rmorph_sum /=.
apply mpolyP => m; rewrite linear_sum /=.
*)
Admitted.

Lemma elementaty_to_complete_partsum n :
  'e_n = \sum_(c : intcompn n) (-1)^+(size c) *: \prod_(i <- c) 'h_i :> SF.
Proof.
Admitted.


(** * Newton formula. *)
Lemma mult_complete_U k d i m :
  (('h_k : {mpoly R[nvar]}) * 'X_i ^+ d)@_m =
  ((mdeg m == (k + d)%N) && (m i >= d))%:R.
Proof using.
rewrite /complete_pol mulr_suml linear_sum /=; case: leqP => /= H.
- pose Ud := (U_(i) *+ d)%MM.
  have Hleq : (Ud <= m)%MM.
    apply/mnm_lepP => j; rewrite mulmnE mnm1E.
    by case: eqP => /= [<- | _]; rewrite ?muln1 ?muln0.
  rewrite andbT -(submK Hleq).
  case: (altP (_ =P _)) => Hdeg /=.
  + move: Hdeg => /eqP; rewrite mdegD mdegMn mdeg1 mul1n eqn_add2r => /eqP Hdeg.
    have Hbound : mdeg (m - Ud) < k.+1 by rewrite Hdeg.
    rewrite (bigD1 (BMultinom Hbound)) /=; last by rewrite Hdeg.
    rewrite mpolyXn -mpolyXD mcoeffX eq_refl /=.
    rewrite big1 ?addr0 // => m' /andP [_ ] Hneq.
    rewrite -mpolyXD mcoeffX.
    apply/boolRP; move: Hneq; apply contra.
    rewrite eqm_add2r => /eqP Heq.
    by apply/eqP/val_inj => /=.
  + rewrite big1 // => m' /eqP Hm'.
    rewrite mpolyXn -mpolyXD mcoeffX.
    apply/boolRP; move: Hdeg; apply contra => /eqP <-.
    by rewrite mdegD Hm' mdegMn mdeg1 mul1n.
- rewrite andbF big1 // => m' _.
  rewrite mpolyXn -mpolyXD mcoeffX.
  apply/boolRP/eqP/mnmP => /(_ i).
  rewrite mnmDE mulmnE mnm1E eq_refl muln1 => Habs.
  by move: H; rewrite -Habs ltnNge leq_addl.
Qed.

Lemma mult_complete_powersum k d m :
  ('h_k * 'p_d : SF)@_m =
  (mdeg m == (k + d)%N)%:R * \sum_(i < nvar) (m i >= d)%:R.
Proof using.
rewrite -[sympol _]/(sympol_lrmorphism nvar R _) rmorphM /=.
rewrite /power_sum_pol !mulr_sumr linear_sum.
apply eq_bigr=> i _ /=; rewrite mult_complete_U.
by case: eqP => _ //=; rewrite ?mul0r ?mul1r.
Qed.

Lemma Newton_complete (k : nat) :
  k%:R *: 'h_k = \sum_(0 <= i < k) 'h_i * 'p_(k - i) :> SF.
Proof using.
apply val_inj => /=; apply/mpolyP => m.
rewrite mcoeffZ mcoeff_complete.
rewrite -[sympol _]/(sympol_lrmorphism nvar R _) !linear_sum big_nat.
rewrite (eq_bigr
           (fun i =>
              (mdeg m == k)%:R *
                \sum_(j < nvar) (m j >= (k - i)%N)%:R)) /=; first last.
  move=> i Hi /=; rewrite mult_complete_powersum.
  by rewrite subnKC //; apply ltnW.
rewrite -big_nat -mulr_sumr mulrC.
case: (altP (mdeg m =P k)) => Hdegm; rewrite /= ?mul1r ?mul0r //.
rewrite exchange_big /=.
rewrite (eq_bigr (fun i : 'I_nvar => (m i)%:R)).
  by rewrite -Hdegm mdegE -natr_sum; congr (_%:R).
move=> i _ /=; rewrite -natr_sum; congr (_%:R).
have : m i <= k.
  by move: Hdegm; rewrite mdegE => <-; rewrite (bigD1 i) //=; apply leq_addr.
rewrite big_mkord (reindex_inj rev_ord_inj) /=.
rewrite (eq_bigr (fun j : 'I_k => nat_of_bool (j < m i))); first last.
  by move=> j _; rewrite subKn //.
move: (m i) => n {m Hdegm i} Hn.
rewrite (bigID (fun i : 'I_k => i < n)) /=.
rewrite (eq_bigr (fun i => 1%N)); last by move=> i ->.
rewrite sum_nat_const /= muln1 big1 ?addn0; last by move=> i /negbTE ->.
rewrite cardE /= /enum_mem -enumT /=.
rewrite (eq_filter (a2 := (preim nat_of_ord (fun i => i < n)))) //.
rewrite -(size_map nat_of_ord).
by rewrite -filter_map val_enum_ord iota_ltn // size_iota.
Qed.

Lemma Newton_complete_iota (k : nat) :
  k%:R *: 'h_k = \sum_(i <- iota 1 k) 'p_i * 'h_(k - i) :> SF.
Proof using.
rewrite Newton_complete big_mkord (reindex_inj rev_ord_inj) /=.
rewrite -(addn0 1%N) iota_addl big_map -val_enum_ord big_map.
rewrite /index_enum /= enumT; apply eq_bigr => i _.
by rewrite mulrC add1n subKn.
Qed.

End ChangeBasis.

From mathcomp Require Import rat ssrnum.


Section ChangeBasisCompletePowerSum.

Import Num.Theory.

Variable nvar : nat.
Local Notation SF := {sympoly rat[nvar]}.

Fixpoint prod_partsum (s : seq nat) :=
  if s is _ :: s' then (sumn s * prod_partsum s')%N else 1%N.

Local Notation "\Pi s" := (prod_partsum s)%:R^-1 (at level 0, s at level 2).

Lemma complete_to_power_sum_prod_partsum n :
  'h_n = \sum_(c : intcompn n) \Pi c *: \prod_(i <- c) 'p_i :> SF.
Proof using.
rewrite /index_enum -enumT /=.
rewrite -[RHS](big_map (@cnval n) xpredT
   (fun c : seq nat => \Pi c *: \prod_(i <- c) 'p_i)).
rewrite enum_intcompnE.
elim: n {1 3 4}n (leqnn n) => [| m IHm] n.
  rewrite leqn0 => /eqP ->.
  by rewrite big_seq1 big_nil complete0 /= invr1 scale1r.
rewrite leq_eqVlt => /orP [/eqP Hm|]; last by rewrite ltnS; exact: IHm.
rewrite enum_compnE Hm // -Hm big_flatten /=.
have Hn : (n%:R : rat) != 0 by rewrite pnatr_eq0 Hm.
apply (scalerI Hn); rewrite Newton_complete_iota.
rewrite scaler_sumr big_map; apply eq_big_seq => i.
rewrite mem_iota add1n ltnS => /andP [Hi Hin].
rewrite big_map big_seq.
rewrite (eq_bigr
    (fun c : seq nat => (n%:R^-1 *: 'p_i) *
         (\Pi c *: \prod_(j <- c) 'p_j))); first last.
  move=> s; rewrite -enum_compnP /is_comp_of_n /= => /andP [/eqP -> _].
  rewrite subnKC // big_cons scalerAr.
  by rewrite natrM invfM -!scalerAr -scalerAl scalerA mulrC.
rewrite -big_seq -mulr_sumr {}IHm; first last.
  by rewrite leq_subLR Hm -(add1n m) leq_add2r.
by rewrite -scalerAl scalerA divff // scale1r; congr(_ * _).
Qed.

Import LeqGeqOrder.

Lemma complete_to_power_sum_intpartn n :
  'h_n = \sum_(l : intpartn n)
           (\sum_(c : intcompn n | perm_eq l c) \Pi c) *: 'p[l] :> SF.
Proof.
rewrite complete_to_power_sum_prod_partsum.
rewrite (partition_big (@partn_of_compn n) xpredT) //=.
apply eq_bigr => l _; rewrite scaler_suml; apply eq_big.
- move=> c; apply/eqP/idP => [<- | Hperm]; first exact: perm_partn_of_compn.
  apply val_inj => /=; apply (eq_sorted geq_trans) => //.
  + exact: sort_sorted.
  + by rewrite (perm_eqrP Hperm) perm_sort.
- move=> c /eqP <-; congr (_ *: _).
  rewrite /prod_power_sum /prod_gen; apply eq_big_perm.
  by rewrite perm_eq_sym; apply: perm_partn_of_compn.
Qed.

Require Import permcent.

Lemma intcompn_cons_sub_proof i n (c : intcompn (n - i)) :
  i != 0%N -> (i <= n)%N -> is_comp_of_n n (i :: c).
Proof.
move=> Hi Hin.
rewrite /is_comp_of_n /= intcompn_sumn subnKC // eq_refl /=.
rewrite /is_comp inE negb_or eq_sym Hi /=.
exact: intcompnP.
Qed.
Definition intcompn_cons i (Hi : i != 0%N) n (Hin : (i <= n)%N) c :=
  IntCompN (intcompn_cons_sub_proof c Hi Hin).

Lemma intcompn_behead_sub_proof i n (c : intcompn n) :
  i != 0%N -> (i <= n)%N ->
  is_comp_of_n (n - i)%N (if head 0%N c == i then behead c else rowcompn (n-i)).
Proof.
case: c => [[|c0 c] /= /andP [/eqP <- Hcomp]] Hi0 Hin.
  by exfalso; move: Hin Hi0; rewrite leqn0 => /eqP ->; rewrite eq_refl.
case: (altP (c0 =P i)) => Hc0 /=; last exact: rowcompnP.
subst c0; rewrite addKn eq_refl /=.
move: Hcomp; rewrite /is_comp inE; apply contra => ->.
by rewrite orbT.
Qed.
Definition intcompn_behead i (Hi : i != 0%N) n (Hin : (i <= n)%N) c :=
  IntCompN (intcompn_behead_sub_proof c Hi Hin).


Lemma part_sumn_count_bound b l :
  (sumn l < b)%N ->
  is_part l ->
  (\sum_(i < b | (i : nat) \in l) i * (count_mem (i : nat) l))%N = sumn l.
Proof.
move=> Hb; have {Hb} Hb : all (gtn b) l.
  elim: l Hb => //= l0 l IHl H; apply/andP; split.
  - exact: (leq_ltn_trans (leq_addr _ _) H).
  - by apply IHl; exact: (leq_ltn_trans (leq_addl _ _) H).
elim: l Hb => [_ _ | l0 l IHl]; first by apply big1.
move=> /andP [Hb /IHl{IHl}Hrec] Hpart.
move: Hb => /= Hl0b.
have /= Hl0 := part_head_non0 Hpart.
move: Hpart => /andP [_] /Hrec{Hrec}Hrec.
case: (boolP (l0 \in l)) => Hl0l.
- rewrite (eq_bigl (fun i : 'I_b => (i : nat) \in l)); first last.
    by move=> i; rewrite inE; case: (altP (i =P l0 :> nat)) => [-> |].
  rewrite (bigD1 (Ordinal Hl0b)) //=.
  rewrite eq_refl /= mulnDr muln1 -addnA; congr (_ + _)%N.
  (* TODO : Factorize *)
  rewrite (eq_bigr (fun i : 'I_b => i * (count_mem (i : nat) l)))%N;
      first last.
    move=> i /andP [_ Hi].
    have : (i : nat) != l0 by [].
    rewrite eq_sym => /negbTE ->.
    by rewrite add0n.
  by rewrite -Hrec [RHS](bigD1 (Ordinal Hl0b)).
- rewrite (bigD1 (Ordinal Hl0b)) //= ?inE eq_refl //=.
  rewrite (count_memPn Hl0l) addn0 muln1; congr (_ + _)%N.
  rewrite (eq_bigr (fun i : 'I_b => i * (count_mem (i : nat) l)))%N;
      first last.
    move=> i /andP [_ Hi].
    have : (i : nat) != l0 by [].
    rewrite eq_sym => /negbTE ->.
    by rewrite add0n.
  rewrite (eq_bigl (fun i : 'I_b => (i : nat) \in l)); first last.
    move=> i /=; rewrite inE; case: (altP (i =P l0 :> nat)) => [Hi | Hil0] /=.
    + subst l0; rewrite (negbTE Hl0l).
      by apply negbTE; rewrite negbK; apply/eqP/val_inj.
    + by case: ((i : nat) \in l).
  exact: Hrec.
Qed.

Lemma part_sumn_count l :
  is_part l ->
  (\sum_(i < (sumn l).+1 | (i : nat) \in l) i * (count_mem (i : nat) l))%N
  = sumn l.
Proof. by move/part_sumn_count_bound; apply. Qed.

Lemma coeff_complete_to_power_sum n (l : intpartn n) :
  (\sum_(c : intcompn n | perm_eq l c) \Pi c) = (zcard l)%:R^-1 :> rat.
Proof.
case: l => l /= /andP [/eqP].
elim: n {1 3 4 5 6 7 8 9}n (leqnn n) l => [| m IHm] n.
  rewrite leqn0 => /eqP -> l /part0 H/H{H} ->{l}.
  rewrite zcard_nil /=.
  rewrite (eq_bigl (xpred1 (IntCompN (cnval := [::]) (n := 0%N) isT))); first last.
    move=> i; apply/idP/eqP => [Hperm | /(congr1 val)/= -> //].
    by apply val_inj => /=; apply/nilP; rewrite /nilp -(perm_eq_size Hperm).
  by rewrite big_pred1_eq.
rewrite leq_eqVlt => /orP [/eqP Hm|]; last by rewrite ltnS; exact: IHm.
move => l Hsum Hpart.
have head_intcompn (c : intcompn n) : (head 0 c < n.+1)%N.
  rewrite ltnS; case: c => [[|c0 c]] //= /andP [/eqP <- _].
  exact: leq_addr.
pose headcomp c := Ordinal (head_intcompn c).
rewrite (partition_big headcomp xpredT) //=.
transitivity (\sum_(j < n.+1)
                \sum_(i : intcompn n |
                 perm_eq l i && (head 0%N i == j :> nat)) \Pi i : rat).
  by apply eq_bigr=> i _; apply eq_bigl => c.
rewrite (bigID (fun j : 'I_(n.+1) => (j : nat) \in l)) /=
        [X in _ + X]big1 ?addr0; first last.
  move=> i Hi; apply big1 => [] [[|c0 c] /= _ /andP [Hperm /eqP Hhead]]; exfalso.
  - by move/perm_sumn: Hperm; rewrite /= Hsum Hm.
  - subst c0; move/perm_eq_mem: Hperm Hi => /(_ i).
    by rewrite inE eq_refl /= => ->.
transitivity (\sum_(i < n.+1 | (i : nat) \in l)
               n%:R^-1 * (zcard (rem (i : nat) l))%:R^-1 : rat).
  apply eq_bigr => /= i Hi.
  have H0i : i != 0%N :> nat.
    move: Hi; apply contraL => /eqP ->.
    by move: Hpart; rewrite is_part_sortedE => /andP [].
  have Hin : (i <= n)%N by rewrite -ltnS.
  rewrite (reindex (intcompn_cons H0i Hin)) /=; first last.
    exists (intcompn_behead H0i Hin) => c; rewrite inE => /andP [Hperm Hhead];
        apply val_inj; rewrite /= ?eq_refl //.
    rewrite /= Hhead.
    case: c Hperm Hhead => [[|c0 c]] //= _.
    + by move/perm_sumn; rewrite /= Hsum {1}Hm.
    + by move=> _ /eqP ->.
  rewrite (eq_bigl (fun c : intcompn (n - i)%N =>
                      perm_eq (rem (i : nat) l) c)); first last.
    move=> c; rewrite eq_refl andbT.
    have /perm_eqlP -> := perm_to_rem Hi.
    by rewrite perm_cons.
  transitivity (\sum_(c : intcompn (n - i)%N | perm_eq (rem (i :nat ) l) c)
                 n%:R^-1 * \Pi c : rat).
    by apply eq_bigr => c _; rewrite intcompn_sumn subnKC // natrM invfM.
  rewrite -mulr_sumr IHm //.
  - rewrite -ltnS -Hm -{3}(subnK Hin).
    move: H0i; case i => [/= [//=|i']] _.
    by rewrite addnS ltnS leq_addr.
  - rewrite -[LHS](addKn i).
    have /perm_sumn /= <- := perm_to_rem Hi.
    by rewrite Hsum.
  - move: Hpart; rewrite !is_part_sortedE => /andP [Hsort H0].
    have Hrem := rem_subseq (i :nat) l; apply/andP; split.
    + exact: (subseq_sorted _ Hrem).
    + by move: H0; apply contra; apply (mem_subseq Hrem).
rewrite {IHm} -mulr_sumr.
transitivity (n%:R^-1 *
       (\sum_(i < n.+1 | (i : nat) \in l)
         (i * (count_mem (i : nat) l))%:R / (zcard l)%:R) : rat).
  congr (_ * _); apply eq_bigr => i Hi.
  have H0i : i != 0%N :> nat.
    move: Hi; apply contraL => /eqP ->.
    by move: Hpart; rewrite is_part_sortedE => /andP [].
  rewrite -(zcard_rem H0i Hi) [X in _/X]natrM invfM -[LHS]mul1r !mulrA.
  congr (_ * _); rewrite divff // pnatr_eq0.
  rewrite muln_eq0 negb_or H0i /=.
  by move: Hi; apply contraL => /eqP H; apply/count_memPn.
rewrite -mulr_suml mulrA -[RHS]mul1r; congr (_ * _).
rewrite -natr_sum -Hsum part_sumn_count // mulrC divff //.
by rewrite Hsum Hm pnatr_eq0.
Qed.

Lemma complete_to_power_sum n :
  'h_n = \sum_(l : intpartn n) (zcard l)%:R^-1 *: 'p[l] :> SF.
Proof.
rewrite complete_to_power_sum_intpartn; apply eq_bigr => l _.
by rewrite coeff_complete_to_power_sum.
Qed.

End ChangeBasisCompletePowerSum.

From mathcomp Require Import vector.

Section Homogeneous.

Variable n : nat.
Variable R : fieldType.
Variable d : nat.
Implicit Type m : 'X_{1.. n.+1}.

Definition hommonomial (l : intpartn d) := DHomog (monomial_homog n.+1 R l).
Definition dsym := span [seq hommonomial l | l <- enum [set: intpartn d]].

Lemma hommonomialE (f : dhomog n.+1 R d) :
  mpoly_of_dhomog f \is symmetric ->
  f = \sum_(p : intpartn d) f@_(mpart p) *: hommonomial p.
Proof.
move=> Hf; apply val_inj.
have:= dhomog_is_dhomog f.
rewrite -[val f]/(val (SymPoly Hf)) => fhom.
rewrite (homog_monomialE fhom) /=.
by rewrite [LHS](linear_sum (@sympol_lrmorphism _ _)) linear_sum.
Qed.

Lemma dsymP f : (f \in dsym) = (mpoly_of_dhomog f \is symmetric).
Proof.
apply/idP/idP.
- move=> /coord_span -> /=.
  rewrite linear_sum; apply rpred_sum => p _.
  rewrite linearZZ; apply rpredZ => /=.
  by rewrite (nth_map (rowpartn d)) /=; last by move: p; rewrite cardE => i.
- move/hommonomialE ->.
  rewrite /dsym span_def.
  apply rpred_sum => p _; apply rpredZ => /=.
  rewrite big_map -big_enum (bigD1 p) //= -[X in X \in _]addr0.
  apply memv_add; first exact: memv_line.
  exact: mem0v.
Qed.

End Homogeneous.

Section Schur.

Variable n0 : nat.
Local Notation n := n0.+1.
Variable R : ringType.

Definition Schur d (sh : intpartn d) : {mpoly R[n]} :=
  \sum_(t : tabsh n0 sh) \prod_(v <- to_word t) 'X_v.

Lemma Schur_tabsh_readingE  d (sh : intpartn d) :
  Schur sh =
  \sum_(t : d.-tuple 'I_n | tabsh_reading sh t) \prod_(v <- t) 'X_v.
Proof using.
rewrite /Schur /index_enum -!enumT.
pose prodw := fun w => \prod_(v <- w) 'X_v : {mpoly R[n]}.
rewrite -[LHS](big_map (fun t => to_word (val t)) xpredT prodw).
rewrite -[RHS](big_map val (tabsh_reading sh) prodw).
rewrite -[RHS]big_filter.
by rewrite (eq_big_perm _ (to_word_enum_tabsh _ sh)).
Qed.

Lemma Schur0 (sh : intpartn 0) : Schur sh = 1.
Proof using.
rewrite Schur_tabsh_readingE (eq_bigl (xpred1 [tuple])); first last.
  by move=> i /=; rewrite tuple0 [RHS]eq_refl intpartn0.
by rewrite big_pred1_eq big_nil.
Qed.


Lemma Schur_oversize d (sh : intpartn d) : (size sh > n)%N -> Schur sh = 0.
Proof using.
rewrite Schur_tabsh_readingE=> Hn; rewrite big_pred0 // => w.
apply (introF idP) => /tabsh_readingP [] tab [] Htab Hsh _ {w}.
suff F0 i : (i < size sh)%N -> (nth (inhabitant _) (nth [::] tab i) 0 >= i)%N.
  have H := ltn_ord (nth (inhabitant _) (nth [::] tab n) 0).
  by have:= leq_trans H (F0 _ Hn); rewrite ltnn.
rewrite -Hsh size_map; elim: i => [//= | i IHi] Hi.
have := IHi (ltn_trans (ltnSn i) Hi); move/leq_ltn_trans; apply.
rewrite -ltnXnatE.
move: Htab => /is_tableauP [] Hnnil _ Hdom.
have {Hdom} := Hdom _ _ (ltnSn i) => /dominateP [] _; apply.
rewrite lt0n; apply/nilP/eqP; exact: Hnnil.
Qed.



Lemma tabwordshape_row d (w : d.-tuple 'I_n) :
  tabsh_reading (rowpartn d) w = sorted leq [seq val i | i <- w].
Proof using.
rewrite /tabsh_reading /= /rowpart ; case: w => w /=/eqP Hw.
case: d Hw => [//= | d] Hw; rewrite Hw /=; first by case: w Hw.
rewrite addn0 eq_refl andbT //=.
case: w Hw => [//= | w0 w] /= /eqP; rewrite eqSS => /eqP <-.
rewrite take_size; apply esym; apply (map_path (b := pred0)) => /=.
- move=> i j /= _ ; exact: leqXnatE.
- by apply/hasPn => x /=.
Qed.


Lemma perm_eq_enum_basis d :
  perm_eq [seq s2m (val s) | s <- enum (basis n d)]
          [seq val m | m <- enum [set m : 'X_{1..n < d.+1} | mdeg m == d]].
Proof using.
apply uniq_perm_eq.
- rewrite map_inj_in_uniq; first exact: enum_uniq.
  move=> i j; rewrite !mem_enum => Hi Hj; exact: inj_s2m.
- rewrite map_inj_uniq; [exact: enum_uniq | exact: val_inj].
move=> m; apply/mapP/mapP => [[] s | [] mb].
- rewrite mem_enum inE /= => Hsort ->.
  have mdegs : mdeg (s2m s) = d.
    rewrite /s2m /mdeg mnm_valK /= big_map enumT -/(index_enum _).
    by rewrite combclass.sum_count_mem count_predT size_tuple.
  have mdegsP : (mdeg (s2m s) < d.+1)%N by rewrite mdegs.
  exists (BMultinom mdegsP) => //.
  by rewrite mem_enum inE /= mdegs.
- rewrite mem_enum inE => /eqP Hmb ->.
  have Ht : size (m2s mb) == d by rewrite -{2}Hmb size_m2s.
  exists (Tuple Ht) => /=; last by rewrite s2mK.
  rewrite mem_enum inE /=; exact: srt_m2s.
Qed.

(** Equivalent definition of complete symmetric function *)
Lemma complete_basisE d :
  \sum_(s in (basis n d)) 'X_[s2m s] = Schur (rowpartn d).
Proof using.
rewrite Schur_tabsh_readingE (eq_bigl _ _ (@tabwordshape_row d)).
rewrite [RHS](eq_bigr (fun s : d.-tuple 'I_n => 'X_[s2m s])); first last.
  move=> [s _] /= _; rewrite /s2m; elim: s => [| s0 s IHs]/=.
    by rewrite big_nil -/mnm0 mpolyX0.
  rewrite big_cons {}IHs -mpolyXD; congr ('X_[_]).
  by rewrite mnmP => i; rewrite mnmDE !mnmE.
by apply eq_bigl => m; rewrite inE /=.
Qed.
End Schur.


Section SchurComRingType.

Variable n0 : nat.
Local Notation n := (n0.+1).
Variable R : comRingType.

Lemma completeE d : complete n R d = Schur n0 R (rowpartn d) :> {mpoly R[n]}.
Proof using.
rewrite /= -complete_basisE /complete_pol.
rewrite -(big_map (@bmnm n d.+1) (fun m => mdeg m == d) (fun m => 'X_[m])).
rewrite /index_enum -enumT -big_filter.
rewrite [filter _ _](_ : _ =
    [seq val m | m <- enum [set m : 'X_{1..n < d.+1} | mdeg m == d]]);
    first last.
  rewrite /enum_mem filter_map -filter_predI; congr map.
  by apply eq_filter => s /=; rewrite !inE andbT.
rewrite -(eq_big_perm _ (perm_eq_enum_basis _ d)) /=.
by rewrite big_map -[RHS]big_filter.
Qed.

Lemma tabwordshape_col d (w : d.-tuple 'I_n) :
  tabsh_reading (colpartn d) w = sorted gtnX w.
Proof using.
rewrite /tabsh_reading /= /colpart ; case: w => w /=/eqP Hw.
have -> : sumn (nseq d 1%N) = d.
  by elim: d {Hw} => //= d /= ->; rewrite add1n.
rewrite Hw eq_refl /= rev_nseq.
have -> : rev (reshape (nseq d 1%N) w) = [seq [:: i] | i <- rev w].
  rewrite map_rev; congr rev.
  elim: d w Hw => [| d IHd] //=; first by case.
  case => [| w0 w] //= /eqP; rewrite eqSS => /eqP /IHd <-.
  by rewrite take0 drop0.
rewrite -rev_sorted.
case: {w} (rev w) {d Hw} => [|w0 w] //=.
elim: w w0 => [//= | w1 w /= <-] w0 /=.
by congr andb; rewrite /dominate /= andbT {w}.
Qed.

(** The definition of elementary symmetric polynomials as column Schur
    function agrees with the one from mpoly *)
Lemma elementaryE d :
  elementary n R d = Schur n0 R (colpartn d) :> {mpoly R[n]}.
Proof using.
rewrite /= mesym_tupleE /tmono /elementary Schur_tabsh_readingE.
rewrite (eq_bigl _ _ (@tabwordshape_col d)).
set f := BIG_F.
rewrite (eq_bigr (fun x => f (rev_tuple x))) /f {f}; first last.
  by move => i _ /=; apply: eq_big_perm; exact: perm_eq_rev.
rewrite (eq_bigl (fun i => sorted gtnX (rev_tuple i))); first last.
  move=> [t /= _]; rewrite rev_sorted.
  case: t => [//= | t0 t] /=.
  apply: (map_path (b := pred0)) => [x y /= _|].
  + by rewrite -ltnXnatE.
  + by apply/hasPn => x /=.
rewrite [RHS](eq_big_perm
                (map (@rev_tuple _ _)
                     (enum (tuple_finType d (ordinal_finType n))))) /=.
  by rewrite big_map /=; first by rewrite /index_enum /= enumT.
apply uniq_perm_eq.
- rewrite /index_enum -enumT; exact: enum_uniq.
- rewrite map_inj_uniq; first exact: enum_uniq.
  apply (can_inj (g := (@rev_tuple _ _))).
  by move=> t; apply val_inj => /=; rewrite revK.
- rewrite /index_enum -enumT /= => t.
  rewrite mem_enum /= inE; apply esym; apply/mapP.
  exists (rev_tuple t) => /=.
  + by rewrite mem_enum.
  + by apply val_inj; rewrite /= revK.
Qed.

Lemma Schur1 (sh : intpartn 1) : Schur n0 R sh = \sum_(i < n) 'X_i.
Proof using.
suff -> : sh = rowpartn 1 by rewrite -completeE complete1.
by apply val_inj => /=; exact: intpartn1.
Qed.

End SchurComRingType.

Notation "''s[' l ]" := (Schur _ _ l)
                              (at level 8, l at level 2, format "''s[' l ]").


From mathcomp Require Import ssrnum algC.
Import Num.Theory.

Section RatToAlgC.

Variable n : nat.

Definition tens_algC :=
  Eval hnf in [rmorphism of @map_mpoly n rat_fieldType algCfield ratr].

Lemma tens_algCX m : tens_algC 'X_[m] = 'X_[m].
Proof using.
rewrite -mpolyP => mm; rewrite mcoeff_map_mpoly /= !mcoeffX.
by case: eqP; rewrite ratr_nat.
Qed.

Lemma msym_tensR s p : msym s (tens_algC p) = tens_algC (msym s p).
Proof using.
rewrite (mpolyE p).
rewrite [tens_algC _]raddf_sum [msym s _]raddf_sum.
rewrite [msym s _]raddf_sum [tens_algC _]raddf_sum.
apply eq_bigr => i _ /=; apply/mpolyP => m.
by rewrite mcoeff_map_mpoly /= !mcoeff_sym mcoeff_map_mpoly /=.
Qed.

Lemma tens_algC_issym (f : {sympoly rat[n]}) : tens_algC f \is symmetric.
Proof.
apply/issymP => s.
by rewrite msym_tensR (issymP _ (sympol_is_symmetric f)).
Qed.
Definition tens_algC_sym (f : {sympoly rat[n]}) : {sympoly algC[n]} :=
           SymPoly (tens_algC_issym f).

Lemma tens_algC_sym_is_rmorphism : rmorphism tens_algC_sym.
Proof.
rewrite /tens_algC_sym; repeat split.
- by move=> i j /=; apply val_inj; rewrite /= rmorphB.
- by move=> i j /=; apply val_inj; rewrite /= rmorphM.
- by apply val_inj; rewrite /= rmorph1.
Qed.
Canonical tens_algC_sym_rmorphism := RMorphism tens_algC_sym_is_rmorphism.

Notation QtoC := tens_algC_sym.

Lemma scale_rat_QtoC (r : rat) (p : {sympoly rat[n]}) :
  QtoC (r *: p) = (ratr r) *: (QtoC p).
Proof.
apply val_inj => /=.
rewrite (mpolyE p) raddf_sum /=.
apply/mpolyP => m.
rewrite mcoeffZ !mcoeff_map_mpoly /= -rmorphM /=; congr ratr.
rewrite !linear_sum /= mulr_sumr.
apply eq_bigr => i _ /=.
by rewrite !linearZ /=.
Qed.

Lemma QtoCelementary d : QtoC 'e_d = 'e_d.
Proof.
apply val_inj; rewrite /= /mesym rmorph_sum /=.
apply eq_bigr => X _; rewrite rmorph_prod /=.
by apply eq_bigr => i _; rewrite tens_algCX.
Qed.
Lemma QtoCelementary_prod d (l : intpartn d) : QtoC 'e[l] = 'e[l].
Proof.
by rewrite rmorph_prod; apply eq_bigr => i _; exact: QtoCelementary.
Qed.

Lemma QtoCcomplete d : QtoC 'h_d = 'h_d.
Proof.
apply val_inj; rewrite /= /complete_pol rmorph_sum /=.
by apply eq_bigr => X _; rewrite tens_algCX.
Qed.
Lemma QtoCcomplete_prod d (l : intpartn d) : QtoC 'h[l] = 'h[l].
Proof.
by rewrite rmorph_prod; apply eq_bigr => i _; exact: QtoCcomplete.
Qed.

Lemma QtoCpower_sum d : QtoC 'p_d = 'p_d.
Proof.
apply val_inj; rewrite /= /power_sum_pol rmorph_sum /=.
by apply eq_bigr => X _; rewrite rmorphX /= tens_algCX.
Qed.
Lemma QtoCpower_sum_prod d (l : intpartn d) : QtoC 'p[l] = 'p[l].
Proof.
by rewrite rmorph_prod; apply eq_bigr => i _; exact: QtoCpower_sum.
Qed.

End RatToAlgC.

