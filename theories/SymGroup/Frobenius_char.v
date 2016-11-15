(** * Combi.SymGroup.Frobenius_char : Frobenius characteristic *)
(******************************************************************************)
(*       Copyright (C) 2016 Florent Hivert <florent.hivert@lri.fr>            *)
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
(** * Frobenius characteristic associated to a class function of ['SG_n].

- [Fchar f]     == the Frobenius characteristic of the class function [f].
                   the number of variable is inferred from the context.
- [Fchar_inv f] == the inverse Frobenius characteristic of the
                   homogeneous symmetric polynomial [f].
- ['irrSG[la]]   == the irreducible character for ['SG_n] associated to the
                   partition [la] of n.


Main results includes:

- [Fchar_isometry] : The Frobenius characteristic is an isometry.
- [Young_rule] : The Young rule for character of ['SG_n].
- [irrSGP] : The ['irrSG[la]] forms a complete set of irreducible character.
- [Frobenius_char] : Frobenius character formula for ['SG_n].
- [dim_cfReprSG] : the dimension of irreducible representation of ['SG_n].
- [LR_rule_irrSG] : Littlewood-Richardson rule for characters of ['SG_n].
 *)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import finfun fintype tuple finset bigop.
From mathcomp Require Import ssralg fingroup morphism perm gproduct.
From mathcomp Require Import rat ssralg ssrnum algC vector.
From mathcomp Require Import mxrepresentation classfun character.

From SsrMultinomials Require Import mpoly.
Require Import sorted ordtype tools partition antisym sympoly homogsym Cauchy
        Schur_altdef stdtab.
Require Import permcomp cycletype towerSn permcent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import LeqGeqOrder.
Import GroupScope GRing.Theory.
Open Scope ring_scope.

Reserved Notation "''irrSG[' l ']'"
         (at level 8, l at level 2, format "''irrSG[' l ]").
Reserved Notation "''M[' l ']'"
         (at level 8, l at level 2, format "''M[' l ]").


Local Notation algCF := [numFieldType of algC].

(** * Definition and basis properties *)
Section NVar.

Variable nvar0 : nat.
Local Notation "''z_' p" := (zcoeff p) (at level 2, format "''z_' p").
Local Notation "''1z_[' p ]" := (ncfuniCT p)  (format "''1z_[' p ]").
Local Notation nvar := nvar0.+1.

Section Defs.

Variable n : nat.
Local Notation HS := {homsym algC[nvar, n]}.

Definition Fchar (f : 'CF('SG_n)) : HS :=
  locked (\sum_(la : 'P_n) (f (permCT la) / 'z_la) *: 'hp[la]).

Definition Fchar_inv (p : HS) : 'CF('SG_n) :=
  locked (\sum_(la : 'P_n) (coord 'hp (enum_rank la) p) *: '1z_[la]).

Lemma FcharE (f : 'CF('SG_n)) :
  Fchar f = \sum_(la : 'P_n) (f (permCT la) / 'z_la) *: 'hp[la].
Proof. by rewrite /Fchar; unlock. Qed.

Lemma Fchar_invE (p : HS) :
  Fchar_inv p = \sum_(la : 'P_n) (coord 'hp (enum_rank la) p) *: '1z_[la].
Proof. by rewrite /Fchar_inv; unlock. Qed.

Lemma Fchar_is_linear : linear Fchar.
Proof using.
move=> a f g; rewrite !FcharE scaler_sumr -big_split /=.
apply eq_bigr => l _; rewrite !cfunElock.
by rewrite scalerA mulrA -scalerDl mulrDl.
Qed.
Canonical Fchar_additive := Additive Fchar_is_linear.
Canonical Fchar_linear := Linear Fchar_is_linear.

Lemma Fchar_ncfuniCT (l : 'P_n) : Fchar '1z_[l] = 'hp[l].
Proof using.
rewrite !FcharE (bigD1 l) //= big1 ?addr0; first last.
  move=> m /negbTE Hm /=.
  rewrite cfunElock cfuniCTE /=.
  rewrite /cycle_typeSn permCTP.
  rewrite partnCTE /= !CTpartnK Hm /=.
  by rewrite mulr0 mul0r scale0r.
rewrite cfunElock cfuniCTE /=.
rewrite /cycle_typeSn permCTP eq_refl /=.
by rewrite mulr1 divff ?scale1r.
Qed.

Lemma Fchar_inv_is_linear : linear Fchar_inv.
Proof using.
move=> a f g; rewrite !Fchar_invE scaler_sumr -big_split /=.
apply eq_bigr => la _.
by move: ('1z_[la]) => U; rewrite !linearD !linearZ /= scalerDl scalerA mulrC.
Qed.
Canonical Fchar_inv_additive := Additive Fchar_inv_is_linear.
Canonical Fchar_inv_linear := Linear Fchar_inv_is_linear.

Hypothesis Hn : (n <= nvar)%N.

Lemma FcharK : cancel Fchar Fchar_inv.
Proof using Hn.
move=> f.
rewrite !Fchar_invE {2}(ncfuniCT_gen f); apply eq_bigr => la _.
rewrite FcharE; congr (_ *: _).
rewrite !(reindex (enum_val (A := {:'P_n}))) /=; first last.
  by apply (enum_val_bij_in (x0 := (rowpartn n))).
transitivity
  (coord 'hp (enum_rank la)
         (\sum_(j < #|{:'P_n}|)
           (f (permCT (enum_val j)) / 'z_(enum_val j)) *: ('hp`_j : HS))).
  congr coord; apply eq_bigr => /= i _; congr (_ *: _).
  rewrite (nth_map (rowpartn n)); last by rewrite -cardE ltn_ord.
  by congr ('hp[_]); apply enum_val_nth.
rewrite coord_sum_free ?enum_rankK //.
exact: (basis_free (symbp_basis Hn _)).
Qed.

Lemma Fchar_invK : cancel Fchar_inv Fchar.
Proof using Hn.
move=> p; rewrite !Fchar_invE linear_sum.
have: p \in span 'hp.
  by rewrite (span_basis (symbp_basis Hn _ )) // memvf.
move=> /coord_span {2}->.
rewrite (reindex enum_rank) /=; last by apply onW_bij; apply enum_rank_bij.
apply eq_bigr => i _.
rewrite linearZ /= Fchar_ncfuniCT; congr (_ *: _).
rewrite (nth_map (rowpartn n)); last by rewrite -cardE ltn_ord.
by congr ('hp[_]); rewrite -enum_val_nth enum_rankK.
Qed.

Lemma Fchar_triv : Fchar 1 = 'hh[rowpartn n].
Proof.
rewrite -decomp_cf_triv linear_sum.
rewrite (eq_bigr (fun la => 'z_la^-1 *: 'hp[la])); first last.
  move=> la _.
  rewrite -Fchar_ncfuniCT /ncfuniCT /= linearZ /=.
  by rewrite scalerA /= mulrC divff // scale1r.
apply val_inj; case: n => [|n0]/=.
  rewrite /= prod_gen0.
  rewrite (big_pred1 (rowpartn 0)); first last.
    by move=> la /=; symmetry; apply/eqP/val_inj; rewrite /= intpartn0.
  rewrite linearZ /= prod_gen0.
  rewrite zcoeffE /zcard big_nil mul1n /=.
  rewrite (big_pred1 ord0); first last.
    move=> i /=; symmetry; apply/eqP/val_inj/eqP.
    by rewrite /= -leqn0 -ltnS ltn_ord.
  by rewrite fact0 invr1 scale1r.
rewrite /prod_gen big_seq1 raddf_sum symh_to_symp //=.
by apply eq_bigr => l _; rewrite zcoeffE.
Qed.

(** ** The Frobenius Characteristic is an isometry *)
Theorem Fchar_isometry f g : '[Fchar f | Fchar g] = '[f, g].
Proof using Hn.
rewrite (ncfuniCT_gen f) (ncfuniCT_gen g) !linear_sum /=.
rewrite homsymdot_suml cfdot_suml; apply eq_bigr => la _.
rewrite homsymdot_sumr cfdot_sumr; apply eq_bigr => mu _.
rewrite ![Fchar (_ *: '1z_[_])]linearZ /= !Fchar_ncfuniCT.
rewrite homsymdotZl homsymdotZr cfdotZl cfdotZr; congr (_ * (_ * _)).
rewrite homsymdotp // cfdotZl cfdotZr cfdot_classfun_part.
case: (altP (la =P mu)) => [<-{mu} | _]; rewrite ?mulr0 ?mulr1 //.
rewrite -zcoeffE -[LHS]mulr1; congr (_ * _).
rewrite /zcoeff rmorphM rmorphV; first last.
  by rewrite unitfE Num.Theory.pnatr_eq0 card_classCT_neq0.
rewrite !conjC_nat -mulrA [X in _ * X]mulrC - mulrA divff; first last.
  by rewrite Num.Theory.pnatr_eq0 card_classCT_neq0.
by rewrite mulr1 divff // Num.Theory.pnatr_eq0 -lt0n cardsT card_Sn fact_gt0.
Qed.

Theorem Fchar_inv_isometry p q : '[Fchar_inv p, Fchar_inv q] = '[p | q].
Proof using Hn. by rewrite -Fchar_isometry !Fchar_invK. Qed.

End Defs.

(**
This cannot be written as a SSReflect [{morph Fchar : f g / ...  >-> ... }]
because the dependency of Fchar on the degree [n]. The three [Fchar] below are
actually three different functions.

Note: this can be solved using a dependant record [{n; 'CF('S_n)}] with a
dependent equality but I'm not sure this is really needed.

*)


(** ** The Frobenius Characteristic is a graded ring morphism *)

Theorem Fchar_ind_morph m n (f : 'CF('SG_m)) (g : 'CF('SG_n)) :
  Fchar ('Ind['SG_(m + n)] (f \o^ g)) = Fchar f *h Fchar g.
Proof using.
rewrite (ncfuniCT_gen f) (ncfuniCT_gen g) !linear_sum; apply eq_bigr => /= l _.
rewrite cfextprod_suml homsymprod_suml !linear_sum; apply eq_bigr => /= k _.
do 2 rewrite [in RHS]linearZ /= Fchar_ncfuniCT.
rewrite cfextprodZr cfextprodZl homsymprodZr homsymprodZl !scalerA.
rewrite 2!linearZ /= Ind_ncfuniCT linearZ /= Fchar_ncfuniCT /=; congr (_ *: _).
by apply val_inj => /=; rewrite prod_genM.
Qed.


(** * Combinatorics of characters of the symmetric groups *)

(** ** Young characters and Young Rule *)
Section Character.

Import LeqGeqOrder.

Variable n : nat.
Hypothesis Hn : (n <= nvar)%N.
Local Notation HS := {homsym algC[nvar, n]}.

Lemma homsymh_character (la : 'P_n) : Fchar_inv 'hh[la] \is a character.
Proof.
move: (n) la Hn => d.
case=> [la /= Hla]; have:= Hla => /andP [/eqP Hd _]; subst d.
elim: la Hla => [| l0 la IHla] Hlla Hd.
  have -> : 'hh[(IntPartN Hlla)] = Fchar 1.
    by rewrite Fchar_triv; congr 'hh[_]; apply val_inj.
  by rewrite FcharK // cfun1_char.
have Hla : (sumn la == sumn la) && is_part la.
  by rewrite eq_refl /=; have:= Hlla => /andP [_ /is_part_consK ->].
have Hdla : (sumn la <= nvar)%N by apply: (leq_trans _ Hd); rewrite /= leq_addl.
have {IHla} Hrec := IHla Hla Hdla.
have -> : 'hh[(IntPartN Hlla)] = 'hh[rowpartn l0] *h 'hh[(IntPartN Hla)]
           :> {homsym algC[nvar, _]}.
  apply val_inj; rewrite /= prod_genM; congr prod_gen.
  apply val_inj; rewrite union_intpartnE /= /rowpart.
  move: Hlla => /andP [_] Hpart.
  have:= part_head_non0 Hpart => /=.
  move: Hpart; rewrite is_part_sortedE => /andP [Hsort _].
  case: l0 Hsort {Hd} => // l0 Hsort _.
  apply (eq_sorted (leT := geq)) => //; first exact: sort_sorted.
  by rewrite perm_eq_sym perm_sort /=.
rewrite -Fchar_triv -(Fchar_invK Hdla 'hh[(IntPartN Hla)]).
rewrite -Fchar_ind_morph (FcharK Hd).
apply cfInd_char; rewrite cfIsom_char.
exact: (cfextprod_char (cfun1_char _) Hrec).
Qed.

End Character.

End NVar.
Hint Resolve leqSpred.

Arguments Fchar nvar0 [n] f.
Arguments Fchar_inv nvar0 [n] p.

Lemma FcharNvar (nvar0 nvar1 n : nat) (f : 'CF('SG_n)) :
  (n <= nvar0.+1)%N || (nvar1 < nvar0.+1)%N ->
  cnvarhomsym nvar1 (Fchar nvar0 f) = (Fchar nvar1 f).
Proof.
rewrite !FcharE => Hn; rewrite linear_sum /=; apply eq_bigr => la _.
by rewrite linearZ /= cnvarhomsymp.
Qed.

Definition YoungSG (n : nat) (la : 'P_n) : 'CF('SG_n) :=
  Fchar_inv (n.-1) 'hh[la].

Definition irrSG (n : nat) (la : 'P_n) : 'CF('SG_n) :=
  Fchar_inv (n.-1) 'hs[la].

Notation "''M[' l ']'" := (YoungSG l).
Notation "''irrSG[' l ']'" := (irrSG l).

Local Notation PO := IntPartNDom.intpartndom_finPOrdType.

Lemma Fchar_irrSGE nvar0 n (la : 'P_n) :
  Fchar nvar0 'irrSG[la] = 'hs[la].
Proof.
rewrite /irrSG -(FcharNvar (nvar0 := n.-1) _) ?leqSpred //=.
by rewrite Fchar_invK ?leqSpred //= cnvarhomsyms ?leqSpred.
Qed.

Lemma Young_char (n : nat) (la : 'P_n) : 'M[la] \is a character.
Proof. exact: homsymh_character. Qed.

Lemma Young_rule (n : nat) (la : 'P_n) :
  'M[la] = \sum_(mu : 'P_n) 'K(mu, la)  *: 'irrSG[mu].
Proof.
pose HS := {homsym algC[n.-1.+1, n]}.
rewrite /YoungSG /irrSG.
apply: (can_inj (FcharK _)); rewrite // Fchar_invK //.
have -> : 'hh[la] = \sum_(mu : 'P_n) 'K(mu, la) *: 'hs[mu] :> HS.
  apply/val_inj; rewrite -[val 'hh[la]]/('h[la]).
  by rewrite /= symh_syms /= linear_sum /=.
rewrite linear_sum /=; apply eq_bigr => mu hmu.
by rewrite linearZ /= Fchar_invK.
Qed.

Require Import unitriginv.

Lemma Young_rule_partdom (n : nat) (la : 'P_n) :
  'M[la] = 'irrSG[la] +
           \sum_(mu | ((la : PO n) < mu)%Ord) 'K(mu, la)  *: 'irrSG[mu].
Proof.
rewrite Young_rule.
exact: (unitrig_sum1lV (fun mu : PO n => 'irrSG[mu]) la (Kostka_unitrig _ n)).
Qed.

(** ** Irreducible character *)

(** Substracting characters *)
Lemma rem_irr1 n (xi phi : 'CF('SG_n)) :
  xi \in irr 'SG_n -> phi \is a character -> '[phi, xi] != 0 ->
       phi - xi \is a character.
Proof.
move=> /irrP [i ->{xi}] Hphi.
rewrite -irr_consttE => /(constt_charP i Hphi) [psi Hpsi ->{phi Hphi}].
by rewrite [_ + psi]addrC addrK.
Qed.

Lemma rem_irr n (xi phi : 'CF('SG_n)) :
  xi \in irr 'SG_n -> phi \is a character -> phi - '[phi, xi] *: xi \is a character.
Proof.
move=> Hxi Hphi.
have /CnatP [m Hm] := Cnat_cfdot_char Hphi (irrWchar Hxi).
rewrite Hm.
elim: m phi Hphi Hm => [|m IHm] phi Hphi Hm; first by rewrite scale0r subr0.
rewrite mulrS scalerDl scale1r opprD addrA.
apply IHm; first last.
  by rewrite cfdotBl Hm irrWnorm // mulrS [1 + _]addrC addrK.
by apply rem_irr1; rewrite //= Hm Num.Theory.pnatr_eq0.
Qed.

Lemma irrSG_orthonormal n (la mu : 'P_n) :
  '['irrSG[la], 'irrSG[mu]] = (la == mu)%:R.
Proof. by rewrite /irrSG Fchar_inv_isometry // homsymdotss. Qed.

Lemma irrSG_irr n (la : 'P_n) : 'irrSG[la] \in irr 'SG_n.
Proof.
pose P := IntPartNDom.intpartndom_finPOrdType n.
elim/(finord_wf_down (T := P)): la => la IHla.
rewrite irrEchar irrSG_orthonormal !eq_refl andbT.
have -> : 'irrSG[la] =
         'M[la] - \sum_(mu : P | (la < mu)%Ord)
                   '[ 'M[la], 'irrSG[mu] ] *: 'irrSG[mu].
  apply/eqP; rewrite eq_sym subr_eq {1}Young_rule_partdom.
  apply/eqP; congr (_ + _); apply eq_bigr => mu _.
  rewrite Young_rule.
  rewrite cfdot_suml (bigD1 mu) //= cfdotZl.
  rewrite irrSG_orthonormal eq_refl mulr1 scalerDl.
  rewrite big1 ?scale0r ?addr0 // => nu /negbTE Hnu.
  by rewrite cfdotZl irrSG_orthonormal Hnu mulr0.
rewrite -big_filter /index_enum -enumT.
set L := filter _ _.
have : all (fun y => (la < y)%Ord) L by apply filter_all.
have : uniq L by apply filter_uniq; apply enum_uniq.
elim: L => [| l0 l IHl].
  by rewrite big_nil subr0 homsymh_character.
rewrite big_cons /= => /andP [Hl0l Huniq] /andP [Hl0 Hall].
rewrite [X in 'M[la] - X]addrC opprD addrA.
have {IHl Huniq Hall} := IHl Huniq Hall.
set Frec := 'M[la] - _ => HFrec.
suff -> : '['M[la], 'irrSG[l0]] = '[Frec, 'irrSG[l0]].
  by apply rem_irr => //; apply: IHla.
rewrite {HFrec}/Frec /= cfdotBl /=.
rewrite cfdot_suml big_seq big1 ?cfdot0l ?subr0 // => mu Hmu.
rewrite cfdotZl irrSG_orthonormal.
case: eqP => H; last by rewrite mulr0.
by rewrite -H Hmu in Hl0l.
Qed.

(** The ['irrSG[la]] forms a complete set of irreducible character *)
Theorem irrSGP n : perm_eq [seq 'irrSG[la] | la : 'P_n] (irr 'SG_n).
Proof.
set IRR := [seq 'irrSG[la] | la : 'P_n].
have Huniq : uniq IRR.
  rewrite map_inj_uniq ?enum_uniq // => la mu Hlamu.
  apply/eqP; have:= irrSG_orthonormal la mu.
  rewrite Hlamu irrSG_orthonormal eq_refl /=.
  by case: eqP => //= _ /eqP; rewrite oner_eq0.
apply (uniq_perm_eq Huniq).
- exact: (free_uniq (basis_free (irr_basis _))).
  have /(leq_size_perm Huniq) Htmp : {subset IRR <= irr 'SG_n}.
  move=> /= f /mapP [/= p /mapP [/= la _ ->{p}] -> {f}].
  exact: irrSG_irr.
suff /Htmp [] : (size (irr 'SG_n) <= size IRR)%N by [].
rewrite size_tuple -(vector.size_basis (irr_basis _)) dim_cfun.
rewrite card_classes_perm /=.
by rewrite size_tuple card_ord.
Qed.


(** ** Frobenius character formula for ['SG_n] *)

(** The value of the irreducible character ['irrSG[la]] using scalar product of
    symmetric function *)
Theorem Frobenius_char_homsymdot n (la : 'P_n) (sigma : 'S_n) :
  'irrSG[la] sigma = '[ 'hs[la] | 'hp[cycle_typeSn sigma] ] _(n.-1, n).
Proof.
rewrite cfdotr_ncfuniCT -(Fchar_isometry (leqSpred n)).
by rewrite Fchar_irrSGE Fchar_ncfuniCT.
Qed.

Theorem Frobenius_char_coord n (la mu : 'P_n) :
  'irrSG[la] (permCT mu) =
  coord 'hs (enum_rank la) ('hp[mu] : {homsym algC[n.-1.+1, n]}).
Proof.
(* TODO simplify me  and factor with proof of homsymdotss *)
pose HSC := {homsym algC[n.-1.+1, n]}.
pose HSR := {homsym rat[n.-1.+1, n]}.
symmetry.
rewrite Frobenius_char_homsymdot /cycle_typeSn (permCTP mu) CTpartnK.
have /coord_span {2}-> : ('hp[mu] : HSC) \in span 'hs.
  by rewrite (span_basis (symbs_basis _ (leqSpred n))) // memvf.
rewrite (reindex enum_rank) /=; last by apply onW_bij; apply enum_rank_bij.
rewrite homsymdot_sumr (bigD1 la) //=.
rewrite (nth_map (rowpartn n)) -?cardE ?ltn_ord // nth_enum_rank.
rewrite homsymdotZr homsymdotss ?leqSpred // eq_refl mulr1.
rewrite big1 ?addr0; first last.
  move=> nu /negbTE Hnu.
  rewrite (nth_map (rowpartn n)) -?cardE ?ltn_ord // nth_enum_rank.
  by rewrite homsymdotZr homsymdotss ?leqSpred // eq_sym Hnu mulr0.
suff -> : coord 'hs (enum_rank la) ('hp[mu] : HSC) =
         ratr (coord 'hs (enum_rank la) ('hp[mu] : HSR)).
  by apply/esym/CrealP; apply Creal_Crat; apply Crat_rat.
rewrite -(map_homsymp (ratr_rmorphism algCF)).
  have /coord_span -> : ('hp[mu] : HSR) \in span 'hs.
    by rewrite (span_basis (symbs_basis _ (leqSpred n))) // memvf.
  rewrite raddf_sum.
  rewrite (eq_bigr
             (fun i : 'I_#|{:'P_n}| =>
               ratr (coord 'hs i ('hp[mu] : HSR)) *: ('hs)`_i )).
    by rewrite !coord_sum_free // (basis_free (symbs_basis _ _)) // leqSpred.
  move=> i _; rewrite /= scale_map_homsym.
  have /= := map_homsymbs (@ratr_rmorphism algCF) n.-1 n.
  move=> /(congr1 (fun p : _.-tuple _ => p`_i)) /= => <-.
  congr (_ *: _); apply esym; apply nth_map.
  by rewrite size_map -cardE ltn_ord.
Qed.
Notation Delta := Vanprod.
Local Notation P d := (symp_pol _ _ d).


(** Frobenius character formula for ['SG_n] *)
Theorem Frobenius_char n (la mu : 'P_n) :
  'irrSG[la] (permCT mu) = (Delta * \prod_(d <- mu) P d)@_(mpart la + rho n).
Proof.
rewrite -/Vanprod Vanprod_alt.
case: n la mu => [//|n] //= la mu.
  (* This case is trivial and the proof is awful !!! *)
  rewrite !intpartn0 big_nil mulr1 /mpart /rho //=.
  have Hmon f : [multinom f i | i < 0] = 0%MM by apply mnmP => [[i Hi]].
  rewrite !{}Hmon addm0.
  rewrite /alternpol (big_pred1 1%g); first last.
    by move=> s /=; apply/esym/eqP/permP => [[i Hi]].
  rewrite odd_perm1 /= msym1m expr0 scale1r mcoeffX eq_refl /=.
  suff -> : 'irrSG[la] = 1 by rewrite (permS0 (permCT mu)) cfun11.
  apply (can_inj (FcharK (leqSpred 0))).
  rewrite Fchar_invK //= Fchar_triv.
  apply val_inj; rewrite /= syms0.
  by rewrite /prod_gen intpartn0 big_nil.
by rewrite Frobenius_char_coord mcoeff_symbs ?leqSpred //= rmorph_prod.
Qed.


(** The dimension of the irreducible character ['irrSG[la]] is the number of
    standard tableau of shape [la] *)
Theorem dim_irrSG n (la : 'P_n) : 'irrSG[la] 1%g = #|{: stdtabsh la}|%:R.
Proof.
pose HSC := {homsym algC[n.-1.+1, n]}.
rewrite -permCT_colpartn Frobenius_char_coord.
have -> : 'hp[colpartn n] = 'hh[colpartn n] :> HSC.
  apply val_inj; rewrite /= !prod_gen_colpartn.
  by rewrite sympe1E -symhe1E.
have -> : 'hh[colpartn n] = \sum_la 'K(la, colpartn n) *: 'hs[la] :> HSC.
  apply val_inj.
  by rewrite /= linear_sum /= -![prod_gen _ _]/('h[_]) symh_syms.
rewrite (reindex (enum_val (A := {:'P_n}))) /=; first last.
  by apply (enum_val_bij_in (x0 := (rowpartn n))).
rewrite (eq_bigr
           (fun i : 'I__ => 'K(enum_val i, colpart n) *: 'hs`_i)); first last.
  move=> /= i _.
  rewrite (nth_map (rowpartn n)); last by rewrite -cardE ltn_ord.
  by congr (_ *: 'hs[_]); apply enum_val_nth.
rewrite coord_sum_free ?enum_rankK // ?KostkaStd //.
exact: (basis_free (symbs_basis _ (leqSpred _))).
Qed.

Theorem dim_cfReprSG n (la : 'P_n) d (rG : mx_representation algCF 'SG_n d) :
  cfRepr rG = 'irrSG[la] -> d = #|{: stdtabsh la}|.
Proof.
move=> H; have := cfRepr1 rG; rewrite H dim_irrSG => /eqP.
by rewrite eqC_nat => /eqP ->.
Qed.


Require Import therule cycletype.
Open Scope ring_scope.

(** * Littlewood-Richardson rule for irreducible characters *)
Theorem LR_rule_irrSG c d (la : 'P_c) (mu : 'P_d) :
  'Ind['SG_(c + d)] ('irrSG[la] \o^ 'irrSG[mu]) =
  \sum_(nu : 'P_(c + d) | included la nu) 'irrSG[nu] *+ LRyam_coeff la mu nu.
Proof.
apply (can_inj (FcharK (leqSpred (c + d)))).
rewrite Fchar_ind_morph linear_sum //= !Fchar_irrSGE.
apply val_inj; rewrite /= linear_sum /=.
rewrite syms_symsM; apply eq_bigr => nu _.
by rewrite !linearMn /= Fchar_invK // leqSpred.
Qed.


