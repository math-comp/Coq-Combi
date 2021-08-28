(** * Combi.SymGroup.reprSn : Basic representations of the Symmetric Groups *)
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
(** * Basic representation of the Symmetric Groups

We define the two representations of dimension 1 together with the natural
representation, and show that ['S_2] has only 2 representations. More precisely,
for a fixed [n] and  [g : 'S_n]:

- [triv_mx g] == the 1x1 identity matrix.
- [sign_mx g] == the 1x1 scalar matrix equal to the sign of [g].
- [signed_mx R g] == given a representation [R] the matrix [sign g * R g]
- [nat_mx g] == the permutation matrix associated to [g]

These four matrices are actually representation matrices:

- [triv_repr] == the trivial representation
- [sign_repr] == the sign representation
- [signed_repr R] == the representation [R] times the sign
- [nat_repr n] == the natural representation of degree [n]

We show in Lemmas [repr1] and [repr_S2] that [triv_repr] and [sign_repr]
exhausts all representations of ['S_n] of degree 1 and all irreducible
representations of of ['S_2].
*************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun bigop finset fingroup perm.
From mathcomp Require Import ssralg fingroup morphism perm action.
From mathcomp Require Import zmodp. (* Defines the coercion nat -> 'I_n.+1 *)
From mathcomp Require Import vector matrix mxalgebra ssrnum algC.
From mathcomp Require Import mxrepresentation classfun character.

Require Import permcomp tools partition congr cycles cycletype presentSn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.


Local Notation algCF := [fieldType of algC].
Local Notation reprS n d := (mx_representation algCF 'SG_n d).

Section TcastVal.
Variable (T : eqType).

Lemma tval_tcastE m n (eq_mn : m = n) (t : m.-tuple T) :
  tcast eq_mn t = t :> seq T.
Proof. by case: n / eq_mn. Qed.

End TcastVal.


Section LinRepr.

Variables (gT : finGroupType) (G : {group gT}).

Lemma cfRepr1_lin_char (rG : mx_representation algCF G 1) :
  cfRepr rG \is a linear_char.
Proof. by rewrite qualifE cfRepr_char /= cfRepr1. Qed.

Lemma lin_char_reprP xi :
  reflect (exists rG : mx_representation algCF G 1, xi = cfRepr rG)
          (xi \is a linear_char).
Proof.
apply (iffP idP) => [xiL | [rG ->{xi}]].
- have:= lin_charW xiL => /char_reprP [[drG rG /= Hxi]].
  have /eqP:= lin_char1 xiL; rewrite Hxi cfRepr1 pnatr_eq1=> /eqP drG1.
  by subst drG; exists rG.
- exact: cfRepr1_lin_char.
Qed.

End LinRepr.


Lemma NirrSn n : Nirr 'SG_n = #|{:'P_n}|.
Proof using. by rewrite NirrE card_classes_perm card_ord. Qed.

Section EltrConj.

Variable n : nat.

Lemma cycle_type_eltr i :
  (i < n)%N -> cycle_typeSn (eltr n i) = hookpartn n.+1 1.
Proof.
move=> /inordi_neq_i1 Hi; rewrite /eltr; apply val_inj => /=.
by rewrite /cycle_typeSn cycle_type_tperm // /partnCT cast_intpartnE card_ord.
Qed.

Lemma eltr_conj i j :
  (i < n)%N -> (j < n)%N -> exists t, eltr n i = ((eltr n j) ^ t)%g.
Proof. by move=> /inordi_neq_i1 Hi /inordi_neq_i1 Hj; exact/tperm_conj. Qed.

End EltrConj.


(** * Representation of dimension 1 and natural representation *)
Section DefTrivSign.

Variables n d : nat.

Definition triv_mx (g : 'S_n) : 'M[algC]_1 := 1.
Definition sign_mx (g : 'S_n) : 'M[algC]_1 := (-1) ^+ (odd_perm g).
Definition signed_mx (rho : reprS n d) (g : 'S_n) : 'M[algC]_d :=
  (-1) ^+ (odd_perm g) *: rho g.

Definition nat_mx (g : 'S_n) : 'M[algC]_n := perm_mx g.


Lemma triv_mx_repr : mx_repr 'SG_n triv_mx.
Proof. by split => [//|g1 g2 _ _]; rewrite mul1mx. Qed.
Canonical triv_repr : reprS n 1 := MxRepresentation triv_mx_repr.

Lemma triv_irr : mx_irreducible triv_repr.
Proof. by apply: mx_abs_irrW; exact: linear_mx_abs_irr. Qed.

Lemma sign_mx_repr : mx_repr 'SG_n sign_mx.
Proof.
rewrite /sign_mx; split; first by rewrite /= odd_perm1.
by move=> g1 g2 _ _; rewrite odd_permM signr_addb.
Qed.
Canonical sign_repr : reprS n 1 := MxRepresentation sign_mx_repr.

Lemma sign_irr : mx_irreducible sign_repr.
Proof. apply: mx_abs_irrW; exact: linear_mx_abs_irr. Qed.

Lemma signed_mx_repr rho : mx_repr 'SG_n (signed_mx rho).
Proof.
rewrite /signed_mx; split; first by rewrite /= odd_perm1 repr_mx1 expr0 scale1r.
move=> g1 g2 _ _; rewrite odd_permM.
by rewrite -scalemxAl -scalemxAr scalerA signr_addb repr_mxM ?inE.
Qed.
Canonical signed_repr rho : reprS n d := MxRepresentation (signed_mx_repr rho).

Lemma nat_mx_repr : mx_repr 'SG_n nat_mx.
Proof. by split=> [|g1 g2 _ _]; [exact: perm_mx1 | exact: perm_mxM]. Qed.
Canonical nat_repr : reprS n n := MxRepresentation nat_mx_repr.

Lemma cfRepr_triv : cfRepr triv_repr = 1.
Proof using.
rewrite -cfunP => s.
by rewrite cfunE cfun1E !inE mulr1n mxtrace1.
Qed.

Lemma cfRepr_trivE : cfRepr triv_repr = 'chi_0.
Proof using. by rewrite irr0 cfRepr_triv. Qed.
Lemma triv_Chi : mx_rsim triv_repr 'Chi_0.
Proof using. by apply/cfRepr_rsimP; rewrite cfRepr_trivE irrRepr. Qed.

Lemma sign_char_subproof :
  is_class_fun <<'SG_n>> [ffun g => (-1) ^+ (odd_perm g)].
Proof.
rewrite genGid.
by apply: intro_class_fun => /= [s t | s]; rewrite ?odd_permJ ?inE.
Qed.
Definition sign_char := Cfun 0 sign_char_subproof.

Lemma cfRepr_sign : cfRepr sign_repr = sign_char.
Proof.
apply cfunP => /= s; rewrite /= !cfunE inE /= !mulr1n.
rewrite /trmx trace_mx11 /sign_mx.
by case: (odd_perm s) => /=; rewrite ?expr1 ?expr0 !mxE eqxx.
Qed.
Lemma sign_charP : sign_char \is a linear_char.
Proof. by rewrite -cfRepr_sign cfRepr1_lin_char. Qed.

Lemma cfRepr_signed (rho : reprS n d) :
  cfRepr (signed_repr rho) = sign_char * cfRepr rho.
Proof.
apply cfunP => /= s; rewrite /= !cfunE inE /= !mulr1n.
by rewrite /signed_mx mxtraceZ.
Qed.

End DefTrivSign.

Arguments triv_mx_repr {n}.
Arguments triv_repr {n}.
Arguments sign_mx_repr {n}.
Arguments sign_repr {n}.
Arguments sign_char {n}.


(** * Representations of the symmetric Group for n = 0 and 1  *)

Lemma row_free1 : row_free (1 : 'M[algC]_1).
Proof. by apply/row_freeP; exists 1; rewrite mul1mx. Qed.

Lemma charSG0 X : X \in irr 'SG_0 -> X = 1.
Proof.
move/irrP => [[i Hi] ->{X}].
apply/eqP; rewrite irr_eq1 -val_eqE /=.
by move: Hi; rewrite NirrSn card_intpartn -[intpartn_nb 0%N]/1%N ltnS leqn0.
Qed.

Lemma charSG1 X : X \in irr 'SG_1 -> X = 1.
Proof.
move/irrP => [[i Hi] ->{X}].
apply/eqP; rewrite irr_eq1 -val_eqE /=.
by move: Hi; rewrite NirrSn card_intpartn -[intpartn_nb 1%N]/1%N ltnS leqn0.
Qed.

Lemma repr1_S0 (rho : reprS 0 1) : mx_rsim rho triv_repr.
Proof.
have /lin_char_irr/charSG0 cfrho := cfRepr1_lin_char rho.
by apply: cfRepr_inj; rewrite cfrho cfRepr_triv.
Qed.

Lemma repr1_S1 (rho : reprS 1 1) : mx_rsim rho triv_repr.
Proof.
have /lin_char_irr/charSG1 cfrho := cfRepr1_lin_char rho.
by apply: cfRepr_inj; rewrite cfrho cfRepr_triv.
Qed.


(** * Representations of dimension 1 the symmetric Group for n > 1 *)

Lemma triv_sign_neq n : (n > 1)%N -> 1 != sign_char :> 'CF('SG_n).
Proof.
case: n => // n; rewrite ltnS => Hn.
apply/negP=> /eqP/cfunP /(_ 's_0)/eqP.
rewrite cfunE cfun1E inE /= (odd_eltr Hn) /= expr1 -addr_eq0 -mulr2n.
by have := Cchar; rewrite charf0P => /(_ 2) ->.
Qed.

Lemma triv_sign_not_sim n :
  (n > 1)%N -> ~ mx_rsim (G := [group of 'SG_n]) triv_repr sign_repr.
Proof.
move/triv_sign_neq => /negbTE Hneq /cfRepr_rsimP.
by rewrite cfRepr_triv cfRepr_sign Hneq.
Qed.

Lemma lin_char_Sn n (xi : 'CF('SG_n)) :
  xi \is a linear_char -> xi = 1 \/ xi = sign_char.
Proof.
case: n xi => [|n] xi Hxi.
  by left; apply/cfunP => /= s; rewrite cfun1E inE /= permS0 lin_char1.
have memSn p : p \in [set: 'S_n.+1]%G by rewrite in_setT.
have ch1_eltr i : (i < n)%N -> xi 's_i = xi 's_0.
  move=> ltin; have [/= t ->] := eltr_conj (leq_ltn_trans (leq0n _) ltin) ltin.
  by rewrite /conjg lin_charM // mulrC -lin_charM // mulgK.
have:= congr1 xi (eltr2 n 0); rewrite lin_charM // lin_char1 // => /eqP.
rewrite -expr2 sqrf_eq1 => /orP [] /eqP xi_s0.
- left; apply/cfunP => /= s; rewrite cfun1E inE /=.
  elim/eltr_ind: s => [|s i lti IHs]; first by rewrite lin_char1.
  by rewrite lin_charM // {}IHs mulr1 ch1_eltr.
- right; apply/cfunP => /= s; rewrite cfunE.
  elim/eltr_ind: s => [|s i lti IHs].
     by rewrite lin_char1 // odd_perm1 expr0.
  rewrite lin_charM // {}IHs odd_permM odd_eltr // ch1_eltr // xi_s0.
  by rewrite mulN1r // signrN.
Qed.

Lemma repr1 n (rho : reprS n 1) :
  mx_rsim rho triv_repr \/ mx_rsim rho sign_repr.
Proof.
have /lin_char_Sn := cfRepr1_lin_char rho.
by move=> [] cfrho; [left|right]; apply: cfRepr_inj;
  rewrite cfrho ?cfRepr_triv ?cfRepr_sign.
Qed.


(** * Representations of the symmetric Group for n=2  *)

Lemma NirrS2 : Nirr 'SG_2 = 2.
Proof using. by rewrite NirrSn card_intpartn. Qed.

Lemma cast_IirrS2 (i : Iirr 'SG_2) :
  i != 0 -> i = cast_ord (esym NirrS2) 1.
Proof using.
move=> Hi; apply val_inj => /=.
by case: i Hi => [[|[|i]]] //=; rewrite NirrS2.
Qed.

Lemma sign_char2 : sign_char = 'chi_(cast_ord (esym NirrS2) 1).
Proof using.
have /irrP [j Hj] := lin_char_irr (sign_charP 2).
rewrite -(cast_IirrS2 (i := j)) //; apply/eqP => Hj0; subst j.
by have := triv_sign_neq (n := 2) (ltnSn _); rewrite Hj irr0 eqxx.
Qed.

Lemma cfRepr_sign2 : cfRepr sign_repr = 'chi_(cast_ord (esym NirrS2) 1).
Proof using. by rewrite cfRepr_sign sign_char2. Qed.

Lemma sign_Chi2 : mx_rsim sign_repr 'Chi_(cast_ord (esym NirrS2) 1).
Proof using. by apply/cfRepr_rsimP; rewrite cfRepr_sign2 irrRepr. Qed.

Lemma irr_S2 : irr 'SG_2 = tcast (esym NirrS2) [tuple 1; sign_char].
Proof using.
apply eq_from_tnth => i; case: (altP (i =P 0)) => [-> | Hi].
- by rewrite tcastE irr0.
- by rewrite tcastE sign_char2 (cast_IirrS2 Hi).
Qed.

Lemma repr_S2 (rho : representation algCF [group of 'SG_2]) :
  mx_irreducible rho -> mx_rsim rho triv_repr \/ mx_rsim rho sign_repr.
Proof using.
move=> Hirr.
have : cfRepr rho \in irr 'SG_2 by apply/irr_reprP; exists rho.
rewrite irr_S2 memtE tval_tcastE !inE.
by move=> /orP[]/eqP cfRho; [left | right]; apply: cfRepr_inj;
  rewrite ?cfRepr_triv ?cfRepr_sign.
Qed.
