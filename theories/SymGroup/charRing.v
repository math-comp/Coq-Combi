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
(** * Frobenius characteristic

- [Fchar f] == the Frobenius characteristic of the class function [f].
               the number of variable is inferred from the context.
 *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import finfun fintype tuple finset bigop choice.
From mathcomp Require Import ssralg fingroup morphism perm gproduct.
From mathcomp Require Import rat ssralg mxalgebra ssrnum algC.
From mathcomp Require Import classfun character mxrepresentation.

From SsrMultinomials Require Import ssrcomplements poset freeg bigenough mpoly.

Require Import tools partition sympoly.
Require Import permcomp presentSn cycles cycletype towerSn permcent.

Import LeqGeqOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Open Scope ring_scope.

Local Notation algCF := [fieldType of algC].


Definition cast_cfun m n (eq_mn : m = n) f : 'CF('SG_n) :=
  let: erefl in _ = n := eq_mn return 'CF('SG_n) in f.

Lemma cast_cfunE m n (eq_mn : m = n) f s :
  cast_cfun eq_mn f s = f (cast_perm (esym eq_mn) s).
Proof. by subst m. Qed.

Record cfunSG := CFunSG { deg : nat; clfun :> 'CF('SG_deg) }.
Notation cfunSGtag := { deg : nat & 'CF('SG_deg) }.

Definition cfunSG_to_tag (cf : cfunSG) : cfunSGtag :=
  let: CFunSG d f := cf in @existT _ _ d f.
Definition tag_to_cfunSG (tcf : cfunSGtag) : cfunSG :=
  let: @existT _ _ d f := tcf in CFunSG f.
Lemma cfunSG_to_tagK : cancel cfunSG_to_tag tag_to_cfunSG.
Proof. by case. Qed.

Definition cfunSG_eqMixin := Eval hnf in CanEqMixin cfunSG_to_tagK.
Canonical cfunSG_eqType := Eval hnf in EqType cfunSG cfunSG_eqMixin.
Definition cfunSG_choiceMixin := Eval hnf in CanChoiceMixin cfunSG_to_tagK.
Canonical cfunSG_choiceType := Eval hnf in ChoiceType cfunSG cfunSG_choiceMixin.

Lemma cfunSG_eqE (f : cfunSG) n (eq_deg_n : deg f = n) :
  f = CFunSG (cast_cfun eq_deg_n f).
Proof.
case: f eq_deg_n => df f /= eq_deg_n.
by subst n; rewrite eq_axiomK.
Qed.

Definition mul_cfunSG (f g : cfunSG) :=
  CFunSG ('Ind['SG_(deg f + deg g)] (f \o^ g)).

Definition one_cfunSG := @CFunSG 0 1.

Lemma cfunSG1M f : mul_cfunSG one_cfunSG f = f.
Proof.
case: f => d f; rewrite /mul_cfunSG /one_cfunSG /=.
have -> : {| deg := d; clfun := f |} =
          {| deg := 0 + d; clfun := cast_cfun (esym (add0n d)) f |}.
  exact: cfunSG_eqE.
congr CFunSG.
apply/cfunP => /= s; rewrite cfIndE /=; last by apply/subsetP => {s} s; rewrite inE.
rewrite (eq_bigr (fun y => cast_cfun (esym (add0n d)) f s)); first last.
  move=> /= t _; rewrite cfunJ; first last.
    apply/imsetP; exists (1%g, cast_perm (add0n d) t); first by rewrite !inE.
    by rewrite /= tinj1E cast_permK.
  rewrite {t} -{1}(cast_permK (add0n d) s) /= -tinj1E cfIsomE ?inE //.
  rewrite !cfunE /= cfun1E inE /= mul1r.
  by rewrite cast_cfunE esymK.
rewrite sumr_const -[(cast_cfun _ _ _) *+ _]mulr_natl.
suff {s} -> : tinj @* setX 'SG_0 'SG_d = 'SG_(0 + d).
  rewrite mulKf // pnatr_eq0 cards_eq0.
  by apply/set0Pn; exists 1%g; rewrite inE.
apply/setP => /= s; rewrite !inE; apply/imsetP => /=.
exists (1%g, cast_perm (add0n d) s); rewrite ?inE //.
by rewrite tinj1E cast_permK.
Qed.

Require Import Frobenius_char.

Variable nvar : nat.

Definition FcharSG f := Fchar (nvar := nvar) (n := deg f) f.

Theorem FcharSG_morph : {morph FcharSG : f g / mul_cfunSG f g >-> f * g }.
Proof.
case => [df f] [dg g] /=.
by rewrite /FcharSG /= Fchar_ind_morph.
Qed.

Theorem FcharSG_inj n :
  (n <= nvar)%N -> {in [pred f | (deg f == n)%N] &, injective FcharSG}.
Proof.
move=> Hn [df f] [dg g]; rewrite !inE /= => /eqP Hdf /eqP Hdg.
rewrite /FcharSG /= => Heq.
subst df dg; congr CFunSG.
move: Heq; rewrite /Fchar.
Admitted.

Lemma cfunSGMC f g : mul_cfunSG f g = mul_cfunSG g f.
Proof.
case: f g => [df f] [dg g]; rewrite /mul_cfunSG /=.
have -> : {| deg := df + dg; clfun := 'Ind['SG_(df + dg)] (f \o^ g) |} =
          {| deg := dg + df; clfun := cast_cfun (addnC _ _)
                                                ('Ind['SG_(df + dg)] (f \o^ g)) |}.
  exact: cfunSG_eqE.
congr CFunSG.
apply/cfunP => /= s; rewrite cast_cfunE !cfIndE /=; first last.
- by apply/subsetP => {s} s; rewrite inE.
- by apply/subsetP => {s} s; rewrite inE.
rewrite card_in_imset setIid => /=; first last.
  by apply/injmP; apply: isom_inj (isom_tinj df dg).
rewrite card_in_imset setIid => /=; first last.
  by apply/injmP; apply: isom_inj (isom_tinj dg df).
rewrite !cardsX mulnC; congr (_ * _).

Admitted.


/Lemma mul_cfunSGA f g h :
  mul_cfunSG f (mul_cfunSG g h) = mul_cfunSG (mul_cfunSG f g) h.
Proof.

