(** * Combi.SymGroup.Frobenius_char : Frobenius characteristic *)
(******************************************************************************)
(*      Copyright (C) 2016-2021 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * Frobenius / Schur character theory for the symmetric groups.

We develop the theory of Frobenius characteristic associated to a class
function of ['SG_n], it is an isometry from class function to symmetric
functions, mapping
- [1%g] to ['HH[rowpartn n] ] (this is Fchar_triv);
- 1z_[l] to 'hp[l] (this is [Fchar_ncfuniCT]);
- induction product to product [Fchar_ind_morph];
- omega involution to multiplication by the sign character [omega_Fchar].

We define the following notions and notations:

- [Fchar f]     == the Frobenius characteristic of the class function [f].
                   the number of variable is inferred from the context.
- [Fchar_inv f] == the inverse Frobenius characteristic of the
                   homogeneous symmetric polynomial [f].

- ['M[la]]      == the Young character for ['SG_n] associated to the
                   partition [la] of n. If [la = (l1, ..., lk)] it is the
                   character induced from the trivial representations of the
                   group ['SG_l1 * ... * SG_lk].
- ['irrSG[la]]  == the irreducible character for ['SG_n] associated to the
                   partition [la] of n.

Here is a list of fundamental results:

- [Fchar_isometry] : The Frobenius characteristic is an isometry.
- [Young_rule]     : The Young rule for character of ['SG_n].
- [irrSGP]         : The ['irrSG[la] | la : 'P_n] forms a complete set of
                     irreducible characters for ['SG_n].
- [Frobenius_char] : Frobenius character formula for ['SG_n].
- [Murnaghan_Nakayama_char] : Murnaghan-Nakayama character formula for ['SG_n].
- [dim_cfReprSG]   : the dimension of irreducible representation of ['SG_n].
- [LR_rule_irrSG]  : Littlewood-Richardson rule for characters of ['SG_n].
 ********)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import finfun fintype tuple finset bigop order.
From mathcomp Require Import ssralg fingroup morphism perm gproduct.
From mathcomp Require Import rat ssralg ssrint ssrnum algC vector.
From mathcomp Require Import mxrepresentation classfun character.

From SsrMultinomials Require Import mpoly.
Require Import sorted ordtype tools partition antisym sympoly homogsym Cauchy
        Schur_altdef stdtab therule.
Require Import permcomp cycletype towerSn permcent reprSn unitriginv.
Require Import MurnaghanNakayama.

Require ordtype.
Local Notation inh := ordtype.Inhabited.Exports.inh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import LeqGeqOrder.
Import GroupScope GRing.Theory Num.Theory.
Open Scope ring_scope.

Reserved Notation "''irrSG[' l ']'"
         (at level 8, l at level 2, format "''irrSG[' l ]").
Reserved Notation "''M[' l ']'"
         (at level 8, l at level 2, format "''M[' l ]").


Local Notation algCF := [numFieldType of algC].
Local Lemma char0_rat : [char rat] =i pred0.
Proof. exact: char_num. Qed.
Local Lemma char0_algC : [char algC] =i pred0.
Proof. exact: char_num. Qed.
#[local] Hint Resolve char0_algC char0_rat : core.


(** * Definition and basic properties *)
Section NVar.

Variable nvar0 : nat.
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
  rewrite cfunElock cfuniCTE /= permCTP partnCTE /= !CTpartnK Hm /=.
  by rewrite mulr0 mul0r scale0r.
rewrite cfunElock cfuniCTE /= permCTP eq_refl /=.
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
rewrite (reindex _ (onW_bij _ (@enum_val_bij _))) /=.
transitivity
  (coord 'hp (enum_rank la)
         (\sum_(j < #|{:'P_n}|)
           (f (permCT (enum_val j)) / 'z_(enum_val j)) *: ('hp`_j : HS))).
  congr coord; apply eq_bigr => /= i _; congr (_ *: _).
  rewrite (nth_map inh); last by rewrite -cardE ltn_ord.
  by congr ('hp[_]); apply enum_val_nth.
by rewrite coord_sum_free ?enum_rankK //; exact: symbp_free.
Qed.

Lemma Fchar_invK : cancel Fchar_inv Fchar.
Proof using Hn.
move=> p; rewrite !Fchar_invE linear_sum.
have: p \in span 'hp.
  by rewrite (span_basis (symbp_basis Hn _ )) // memvf.
move=> /coord_span {2}->.
rewrite (reindex _ (onW_bij _ (@enum_rank_bij [finType of 'P__]))) /=.
apply eq_bigr => i _.
rewrite linearZ /= Fchar_ncfuniCT; congr (_ *: _).
rewrite (nth_map inh); last by rewrite -cardE ltn_ord.
by congr ('hp[_]); rewrite -enum_val_nth enum_rankK.
Qed.

Lemma Fchar_triv : Fchar 1 = 'hh[rowpartn n].
Proof.
rewrite -decomp_cf_triv linear_sum.
rewrite (eq_bigr (fun la => 'z_la^-1 *: 'hp[la])); first last => [la _|].
  rewrite -Fchar_ncfuniCT /ncfuniCT /= linearZ /=.
  by rewrite scalerA /= mulrC divff // scale1r.
apply val_inj; case: n => [|n0]/=.
  rewrite prod_gen0 (big_pred1 (rowpartn 0)); first last.
    by move=> la /=; rewrite !intpartn0 eqxx.
  rewrite linearZ /= prod_gen0.
  rewrite zcoeffE /zcard rowpartn0E big_nil mul1n /=.
  by rewrite big1 // invr1 scale1r.
rewrite /prod_gen rowpartnE big_seq1 raddf_sum symh_to_symp //=.
by apply eq_bigr => l _; rewrite zcoeffE.
Qed.

Lemma Fchar_inv_homsymp (l : 'P_n) : Fchar_inv 'hp[l] = '1z_[l].
Proof. by rewrite -Fchar_ncfuniCT FcharK. Qed.

(** ** Frobenius Characteristic and omega involution *)
Lemma omega_Fchar_inv (p : HS) :
  Fchar_inv (omegahomsym p) = sign_char * (Fchar_inv p).
Proof.
have /coord_span -> : p \in span 'hp.
  by rewrite (span_basis (symbp_basis Hn _ )) // memvf.
rewrite !linear_sum /= mulr_sumr; apply eq_bigr => i _.
rewrite !linearZ /= -scalerAr; congr (_ *: _).
rewrite {p} (nth_map (rowpartn n)); last by rewrite -cardE ltn_ord.
move: (nth _ _ _) => la {i}.
rewrite omega_homsymp //;
  try by apply: (leq_trans (leq_head_sumn _)); rewrite sumn_intpartn.
rewrite linearZ /= Fchar_inv_homsymp.
rewrite /ncfuniCT scalerA mulrC -scalerA -scalerAr; congr (_ *: _).
rewrite -cfunP => /= s; rewrite !cfunE.
rewrite odd_cycle_type signr_odd sumn_intpartn.
rewrite cfuniCTE; case: eqP => [->|]; rewrite /= ?mulr0 // {s}.
by rewrite {1}card_ord cast_intpartnE.
Qed.

Lemma omega_Fchar f : omegahomsym (Fchar f) = Fchar (sign_char * f).
Proof. by rewrite -(FcharK f) -omega_Fchar_inv !Fchar_invK. Qed.

Lemma Fchar_sign : Fchar sign_char = 'he[rowpartn n].
Proof.
rewrite -(mulr1 sign_char) -omega_Fchar Fchar_triv omega_homsymh //.
by apply: (leq_trans (leq_head_sumn _)); rewrite sumn_intpartn.
Qed.


(** ** The Frobenius Characteristic is an isometry *)
Theorem Fchar_isometry f g : '[Fchar f | Fchar g] = '[f, g].
Proof using Hn.
rewrite (ncfuniCT_gen f) (ncfuniCT_gen g) !linear_sum /=.
rewrite homsymdot_suml cfdot_suml; apply eq_bigr => la _.
rewrite homsymdot_sumr cfdot_sumr; apply eq_bigr => mu _.
rewrite ![Fchar (_ *: '1z_[_])]linearZ /= !Fchar_ncfuniCT.
rewrite homsymdotZl homsymdotZr cfdotZl cfdotZr; congr (_ * (_ * _)).
rewrite homsymdotpp // cfdotZl cfdotZr cfdot_classfun_part.
case: (altP (la =P mu)) => [<-{mu} | _]; rewrite ?mulr0 ?mulr1 //.
rewrite -zcoeffE -[LHS]mulr1; congr (_ * _).
rewrite /zcoeff rmorphM rmorphV; first last.
  by rewrite unitfE pnatr_eq0 card_classCT_neq0.
rewrite !rmorph_nat -mulrA [X in _ * X]mulrC - mulrA divff; first last.
  by rewrite pnatr_eq0 card_classCT_neq0.
by rewrite mulr1 divff // pnatr_eq0 -lt0n cardsT card_Sn fact_gt0.
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
rewrite 2!linearZ /= ncfuniCT_Ind linearZ /= Fchar_ncfuniCT /=; congr (_ *: _).
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
move: (n) la Hn => d [la /= Hla].
have:= Hla => /andP [/eqP Hd _]; subst d.
elim: la Hla => [| l0 la IHla] Hlla Hd.
  by rewrite intpartn0 -Fchar_triv FcharK // cfun1_char.
have Hla : (sumn la == sumn la) && is_part la.
  by rewrite eq_refl /=; have:= Hlla => /andP [_ /is_part_consK ->].
have Hdla : (sumn la <= nvar)%N by apply: (leq_trans _ Hd); rewrite /= leq_addl.
have {IHla} Hrec := IHla Hla Hdla.
rewrite homsymprod_hh -Fchar_triv -(Fchar_invK Hdla 'hh[(IntPartN Hla)]).
rewrite -Fchar_ind_morph (FcharK Hd).
apply cfInd_char; rewrite cfIsom_char.
exact: (cfextprod_char (cfun1_char _) Hrec).
Qed.

Lemma homsyme_character (la : 'P_n) : Fchar_inv 'he[la] \is a character.
Proof.
rewrite -omega_homsymh; first last.
  by apply: (leq_trans _ Hn); rewrite -{2}(sumn_intpartn la) leq_head_sumn.
rewrite omega_Fchar_inv //.
exact: rpredM (lin_charW (sign_charP _)) (homsymh_character _).
Qed.

End Character.

End NVar.
#[local] Hint Resolve leqSpred : core.

Arguments Fchar nvar0 [n] f.
Arguments Fchar_inv nvar0 [n] p.

Lemma FcharNvar (nvar0 nvar1 n : nat) (f : 'CF('SG_n)) :
  (n <= nvar0.+1)%N || (nvar1 < nvar0.+1)%N ->
  cnvarhomsym nvar1 (Fchar nvar0 f) = (Fchar nvar1 f).
Proof.
rewrite !FcharE => Hn; rewrite linear_sum /=; apply eq_bigr => la _.
by rewrite linearZ /= cnvarhomsymp.
Qed.


Section YoungIrrDef.

Variable (n : nat).
Implicit Type (la mu : 'P_n).

Definition YoungSG la : 'CF('SG_n) := Fchar_inv (n.-1) 'hh[la].
Definition irrSG   la : 'CF('SG_n) := Fchar_inv (n.-1) 'hs[la].

Notation "''M[' l ']'" := (YoungSG l).
Notation "''irrSG[' l ']'" := (irrSG l).

Lemma Fchar_irrSGE nvar0 la : Fchar nvar0 'irrSG[la] = 'hs[la].
Proof.
rewrite /irrSG -(FcharNvar (nvar0 := n.-1) _) ?leqSpred //=.
by rewrite Fchar_invK ?leqSpred //= cnvarhomsyms ?leqSpred.
Qed.

Lemma Young_char la : 'M[la] \is a character.
Proof. exact: homsymh_character. Qed.

Lemma Young_rule la : 'M[la] = \sum_(mu : 'P_n) 'K(mu, la)  *: 'irrSG[mu].
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

Lemma Young_rule_partdom la :
  'M[la] =
  'irrSG[la] + \sum_(mu | (la < mu :> 'PDom_n)%O) 'K(mu, la)  *: 'irrSG[mu].
Proof.
rewrite Young_rule.
exact: (unitrig_sum1lV (fun mu : 'PDom_n => 'irrSG[mu]) la (Kostka_unitrig _ n)).
Qed.


(** ** Irreducible character *)

(** Substracting characters *)
Lemma rem_irr1 (xi phi : 'CF('SG_n)) :
  xi \in irr 'SG_n -> phi \is a character -> '[phi, xi] != 0 ->
     phi - xi \is a character.
Proof.
move=> /irrP [i ->{xi}] Hphi.
rewrite -irr_consttE => /(constt_charP i Hphi) [psi Hpsi ->{phi Hphi}].
by rewrite [_ + psi]addrC addrK.
Qed.

Lemma rem_irr (xi phi : 'CF('SG_n)) :
  xi \in irr 'SG_n -> phi \is a character ->
     phi - '[phi, xi] *: xi \is a character.
Proof.
move=> Hxi Hphi.
have /CnatP [m Hm] := Cnat_cfdot_char Hphi (irrWchar Hxi).
rewrite Hm.
elim: m phi Hphi Hm => [|m IHm] phi Hphi Hm; first by rewrite scale0r subr0.
rewrite mulrS scalerDl scale1r opprD addrA; apply: IHm.
- by apply rem_irr1; rewrite //= Hm pnatr_eq0.
- by rewrite cfdotBl Hm irrWnorm // mulrS [1 + _]addrC addrK.
Qed.

Lemma irrSG_orthonormal la mu :
  '['irrSG[la], 'irrSG[mu]] = (la == mu)%:R.
Proof. by rewrite /irrSG Fchar_inv_isometry // homsymdotss. Qed.

Theorem irrSG_irr la : 'irrSG[la] \in irr 'SG_n.
Proof.
elim/(finord_wf_down (T := [finPOrderType of 'PDom_n])): la => la IHla.
rewrite irrEchar irrSG_orthonormal !eq_refl andbT.
have -> : 'irrSG[la] = 'M[la] - \sum_(mu : 'PDom_n | (la < mu)%O)
                                   '[ 'M[la], 'irrSG[mu] ] *: 'irrSG[mu].
  apply/eqP; rewrite eq_sym subr_eq {1}Young_rule_partdom.
  apply/eqP; congr (_ + _); apply eq_bigr => mu _.
  rewrite Young_rule.
  rewrite cfdot_suml (bigD1 mu) //= cfdotZl.
  rewrite irrSG_orthonormal eq_refl mulr1 scalerDl.
  rewrite big1 ?scale0r ?addr0 // => nu /negbTE Hnu.
  by rewrite cfdotZl irrSG_orthonormal Hnu mulr0.
rewrite -big_filter; set L := filter _ _.
have : all (<%O la) L by apply filter_all.
have : uniq L by apply: filter_uniq; apply: index_enum_uniq.
elim: L => [| l0 l IHl].
  by rewrite big_nil subr0 homsymh_character.
rewrite big_cons /= => /andP [Hl0l Huniq] /andP [Hl0 Hall].
rewrite [X in 'M[la] - X]addrC opprD addrA.
have {IHl Huniq Hall} := IHl Huniq Hall.
set Frec := 'M[la] - _ => HFrec.
suff {IHla} -> : '['M[la], 'irrSG[l0]] = '[Frec, 'irrSG[l0]].
  by apply rem_irr => //; apply: IHla.
rewrite {HFrec}/Frec /= cfdotBl /=.
rewrite cfdot_suml big_seq big1 ?cfdot0l ?subr0 // => mu Hmu.
rewrite cfdotZl irrSG_orthonormal.
case: eqP => H; last by rewrite mulr0.
by rewrite -H Hmu in Hl0l.
Qed.

(** The ['irrSG[la]] forms a complete set of irreducible character *)
Theorem irrSGP : perm_eq [seq 'irrSG[la] | la : 'P_n] (irr 'SG_n).
Proof.
set IRR := [seq 'irrSG[la] | la : 'P_n].
have Huniq : uniq IRR.
  rewrite map_inj_uniq ?enum_uniq // => la mu Hlamu.
  apply/eqP; have:= irrSG_orthonormal la mu.
  rewrite Hlamu irrSG_orthonormal eq_refl /=.
  by case: eqP => //= _ /eqP; rewrite oner_eq0.
apply (uniq_perm Huniq).
  exact: (free_uniq (basis_free (irr_basis _))).
have /(uniq_min_size Huniq) Htmp : {subset IRR <= irr 'SG_n}.
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
Theorem Frobenius_char_homsymdot la (sigma : 'S_n) :
  'irrSG[la] sigma = '[ 'hs[la] | 'hp[cycle_typeSn sigma] ] _(n.-1, n).
Proof.
rewrite cfdotr_ncfuniCT -(Fchar_isometry (leqSpred n)).
by rewrite Fchar_irrSGE Fchar_ncfuniCT.
Qed.

Theorem Frobenius_char_coord la (sigma : 'S_n) :
  'irrSG[la] sigma =
  coord 'hs (enum_rank la) ('hp[cycle_typeSn sigma] : {homsym algC[n.-1.+1, n]}).
Proof.
pose HSC := {homsym algC[n.-1.+1, n]}.
symmetry.
rewrite Frobenius_char_homsymdot.
have /coord_span {2}-> : ('hp[cycle_typeSn sigma] : HSC) \in span 'hs.
  by rewrite (span_basis (symbs_basis _ (leqSpred n))) // memvf.
rewrite (reindex _ (onW_bij _ (@enum_rank_bij [finType of 'P__]))) /=.
rewrite homsymdot_sumr (bigD1 la) //=.
rewrite (nth_map (rowpartn n)) -?cardE ?ltn_ord // nth_enum_rank.
rewrite homsymdotZr homsymdotss ?leqSpred // eq_refl mulr1.
rewrite big1 ?addr0; first last.
  move=> nu /negbTE Hnu.
  rewrite (nth_map (rowpartn n)) -?cardE ?ltn_ord // nth_enum_rank.
  by rewrite homsymdotZr homsymdotss ?leqSpred // eq_sym Hnu mulr0.
by rewrite -coord_map_homsym ?map_homsymbs ?symbs_basis // map_homsymp.
Qed.

End YoungIrrDef.
Notation "''M[' l ']'" := (YoungSG l).
Notation "''irrSG[' l ']'" := (irrSG l).


(** Frobenius character formula for ['SG_n] *)
Theorem Frobenius_char n (la mu : 'P_n) :
  'irrSG[la] (permCT mu) =
  (Vanprod * \prod_(d <- mu) (symp_pol n algCF d))@_(mpart la + rho n).
Proof.
rewrite -/Vanprod Vanprod_alt.
case: n la mu => [//|n] //= la mu.
  rewrite (charSG0 (irrSG_irr _)) cfun1E inE /=.
  rewrite !mnm_n0E !intpartn0 {la mu} rowpartn0E big_nil mulr1.
  by rewrite mcoeff_alt //= map_inj_in_uniq ?enum_uniq // => /= [[]].
rewrite Frobenius_char_coord cycle_typeSn_permCT.
by rewrite mcoeff_symbs ?leqSpred //= rmorph_prod.
Qed.


(** The Murnaghan Nakayama rule for irreducible character ['irrSG[la]] *)
Theorem Murnaghan_Nakayama_char n la (sigma : 'S_n) :
  'irrSG[la] sigma = (MN_coeff la (cycle_typeSn sigma))%:~R.
Proof.
rewrite Frobenius_char_homsymdot MN_coeff_homogP raddf_sum /=.
rewrite (bigD1 la) //= big1 ?addr0 //; first last => [i /negbTE Hi|].
  by rewrite homsymdotZr homsymdotss // eq_sym Hi mulr0.
rewrite homsymdotZr homsymdotss // eqxx mulr1.
by rewrite conj_Cint // Cint_int.
Qed.
Corollary Murnaghan_NakayamaCT n (la mu : 'P_n) :
  'irrSG[la] (permCT mu) = (MN_coeff la mu)%:~R.
Proof. by rewrite Murnaghan_Nakayama_char cycle_typeSn_permCT. Qed.

Corollary irrSG_char_int n (la mu : 'P_n) : 'irrSG[la] (permCT mu) \in Cint.
Proof. by rewrite Murnaghan_NakayamaCT Cint_int. Qed.

Example Wikipedia_Murnaghan_Nakayama :
  let p521 := @IntPartN 8 [:: 5; 2; 1]%N is_true_true in
  let p3311 := @IntPartN 8 [:: 3; 3; 1; 1]%N is_true_true in
  'irrSG[p521] (permCT p3311) = - 2%:~R.
Proof. by rewrite /= Murnaghan_NakayamaCT. Qed.


(** The dimension of the irreducible character ['irrSG[la]] is the number of
    standard tableau of shape [la] *)
Theorem dim_irrSG n (la : 'P_n) : 'irrSG[la] 1%g = #|{: stdtabsh la}|%:R.
Proof.
pose HSC := {homsym algC[n.-1.+1, n]}.
rewrite -permCT_colpartn Frobenius_char_coord cycle_typeSn_permCT.
have -> : 'hp[colpartn n] = 'hh[colpartn n] :> HSC.
  apply val_inj; rewrite /= !prod_gen_colpartn.
  by rewrite sympe1E -symhe1E.
have -> : 'hh[colpartn n] = \sum_la 'K(la, colpartn n) *: 'hs[la] :> HSC.
  apply val_inj.
  by rewrite /= linear_sum /= -![prod_gen _ _]/('h[_]) symh_syms.
rewrite (reindex _ (onW_bij _ (@enum_val_bij _))) /=.
rewrite (eq_bigr
           (fun i : 'I__ => 'K(enum_val i, colpartn n) *: 'hs`_i)); first last.
  move=> /= i _.
  rewrite (nth_map inh); last by rewrite -cardE ltn_ord.
  by congr (_ *: 'hs[_]); apply enum_val_nth.
by rewrite coord_sum_free ?enum_rankK // ?KostkaStd //; exact: symbs_free.
Qed.

Theorem dim_cfReprSG n (la : 'P_n) d (rG : mx_representation algCF 'SG_n d) :
  cfRepr rG = 'irrSG[la] -> d = #|{: stdtabsh la}|.
Proof.
move=> H; have := cfRepr1 rG; rewrite H dim_irrSG => /eqP.
by rewrite eqC_nat => /eqP ->.
Qed.


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
