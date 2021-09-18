(** * Combi.MPoly.MurnaghanNakayama : Murnaghan-Nakayama rule *)
(******************************************************************************)
(*      Copyright (C) 2021-2021 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * The Murnaghan–Nakayama rule

 ******)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun finset binomial order.
From mathcomp Require Import bigop ssralg ssrint path perm fingroup.
From SsrMultinomials Require Import ssrcomplements freeg mpoly.
From SsrMultinomials Require monalg.

Require Import sorted tools ordtype permuted partition skewpart.
Require Import antisym Schur_mpoly Schur_altdef sympoly homogsym.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.


Local Reserved Notation "''a_' k"
      (at level 8, k at level 2, format "''a_' k").
Local Reserved Notation "m # s"
      (at level 40, left associativity, format "m # s").


Section BigPMap.
Variables (R : Type) (idx : R).
Local Notation "1" := idx.
Variable (op : Monoid.law idx).
Local Notation "*%M" := op (at level 0).
Local Notation "x * y" := (op x y).
Variable I : Type.

Lemma big_pmap J (h : J -> option I) r F :
  \big[*%M/1]_(i <- pmap h r) F i = \big[*%M/1]_(j <- r) oapp F idx (h j).
Proof.
elim: r => [| r0 r IHr]/=; first by rewrite !big_nil.
rewrite /= big_cons; case: (h r0) => [i|] /=; last by rewrite Monoid.mul1m.
by rewrite big_cons IHr.
Qed.

End BigPMap.


Section MultAlternSymp.

Variable n0 : nat.
Variable R : comRingType.

Local Notation n := n0.+1.
Local Notation rho := (rho n).
Local Notation "''a_' k" := (@alternpol n R 'X_[k]).


Lemma mult_altern_symp_pol p d :
  'a_(mpart p + rho) * (symp_pol n R d.+1) =
   \sum_(i < n) 'a_(mpart p + rho + U_(i) *+ d.+1).
Proof.
rewrite /alternpol mulr_suml [RHS]exchange_big /=; apply eq_bigr => s _.
rewrite -scaler_sumr -scalerAl; congr (_ *: _).
rewrite -(issymP _ (symp_sym n R d.+1) s) -msymM -linear_sum /=; congr msym.
rewrite /symp_pol mulr_sumr; apply eq_bigr => i _.
by rewrite !mpolyXD mpolyXn.
Qed.

Lemma mult_altern_oapp p d :
  is_part p -> size p <= n ->
  'a_(mpart p + rho) * (symp_pol n R d.+1) =
  \sum_(i < n) oapp (fun ph => (-1) ^+ ph.2.-1 *: 'a_(mpart ph.1 + rho)) 0
   (add_ribbon p d.+1 i).
Proof.
move=> partp szp; rewrite mult_altern_symp_pol.
apply eq_bigr => i _ /=.
case Hrib : add_ribbon => [[sh h]|] /=.
  by rewrite (alt_straight_add_ribbon _ partp szp Hrib).
by rewrite (alt_straight_add_ribbon0 _ partp szp) // Hrib.
Qed.

Lemma mult_altern_pmap p d :
  is_part p -> size p <= n ->
  'a_(mpart p + rho) * (symp_pol n R d.+1) =
  \sum_(psh <- pmap (add_ribbon p d.+1) (iota 0 n))
   (-1) ^+ (psh.2).-1 *: 'a_(mpart psh.1 + rho).
Proof.
move=> partp szp; rewrite mult_altern_oapp //.
rewrite -(big_mkord xpredT (fun i => oapp _ 0 (add_ribbon p d.+1 i))).
by rewrite big_pmap /index_iota subn0.
Qed.


Section Bijection.

Variable (m : nat) (la : 'P_m).
Hypothesis (szla : size la <= n).
Variable nbox : nat.

Fact add_ribbon_intpartn_subproof pos :
  is_part_of_n (nbox.+1 + m)%N
               (oapp (fun p => p.1) [:: (nbox + m).+1]
                     (add_ribbon la nbox.+1 pos)).
Proof.
case Hrib : add_ribbon => [[res h]|] /=; last by rewrite addn0 addSn eqxx.
have:= is_part_of_add_ribbon (intpartnP la) Hrib => /andP[/eqP -> ->].
by rewrite sumn_intpartn eqxx.
Qed.
Local Definition add_ribbon_intpartn pos :=
  match add_ribbon la nbox.+1 pos with
  | Some (_, h) => Some (IntPartN (add_ribbon_intpartn_subproof pos))
  | None => None
  end.

Fact ribbon_stop_subproof (mu : 'P_(nbox.+1 + m)) :
  (if size mu <= n then (mindropeq la mu).-1 else 0%N) < n.
Proof.
case: (leqP (size mu) n) => // szmu.
case: mindropeq (mindropeq_leq la mu) => // md /= /leq_trans; apply.
by rewrite geq_max szla szmu.
Qed.
Local Definition ribbon_stop mu := Ordinal (ribbon_stop_subproof mu).

Lemma mult_altern_sympol :
  'a_(mpart la + rho) * (symp_pol n R nbox.+1) =
  \sum_(sh : 'P_(nbox.+1 + m) | (ribbon la sh) && (size sh <= n))
   (-1) ^+ (ribbon_height la sh).-1 *: 'a_(mpart sh + rho).
Proof.
rewrite mult_altern_oapp //.
rewrite (bigID (fun i : 'I_n => add_ribbon la nbox.+1 i)) /=.
rewrite [X in _ + X = _]big1 ?addr0; last by move=> i; case: add_ribbon.
rewrite (reindex_omap ribbon_stop add_ribbon_intpartn) /=; first last.
  move=> i; rewrite /add_ribbon_intpartn.
  case Haddrib : {1 2}(add_ribbon la nbox.+1 i) => [[res h]|]//= _.
  congr Some; apply val_inj; rewrite /= Haddrib /=.
  rewrite (size_add_ribbon Haddrib) geq_max szla ltn_ord /=.
  rewrite (ribbon_on_mindropeq (intpartnP la) _ (add_ribbon_onP Haddrib)) //.
  exact: (is_part_add_ribbon _ Haddrib).
apply esym; apply: eq_big => mu; rewrite andbC.
  case leqP => Hszmu /=; first last.
  + rewrite /add_ribbon_intpartn.
    case Haddrib : {1 2}(add_ribbon la nbox.+1 0) => [[res h]|//=].
    rewrite andTb /=; case (altP (_ =P Some mu)) => // [[/(congr1 val) /=]].
    rewrite Haddrib /= => Heq.
    have := size_add_ribbon Haddrib; rewrite Heq => {}Heq.
    by move: Hszmu; rewrite Heq leq_max 2!ltnNge szla.
  + apply esym; case: (boolP (ribbon la mu)) => [Hrib | Hnrib].
    * have := ribbon_addE (intpartnP la) (intpartnP mu) Hrib.
      rewrite sumn_diff_shape ?ribbon_included // !sumn_intpartn addnK => Heq.
      rewrite Heq andTb /=; apply/eqP; rewrite /add_ribbon_intpartn.
      rewrite {1}Heq; congr Some; apply val_inj => /=.
      by rewrite Heq /=.
    * case Haddrib : (add_ribbon la nbox.+1 _) => [[res h]|//=].
      rewrite andTb /=; apply/negP => /eqP.
      rewrite /add_ribbon_intpartn {1}Haddrib => [[/(congr1 val) /=]].
      rewrite Haddrib /= => Heq.
      by move: Hnrib; rewrite -{}Heq (add_ribbonP _ Haddrib).
move=> /andP[-> Hrib].
have:= ribbon_addE (intpartnP la) (intpartnP mu) Hrib.
by rewrite sumn_diff_shape ?ribbon_included // !sumn_intpartn addnK => ->.
Qed.

End Bijection.

End MultAlternSymp.


Section MultSymsSympIDomain.

Variable n0 : nat.
Variable R : idomainType.

Local Notation n := n0.+1.
Local Notation rho := (rho n).
Local Notation "''a_' k" := (@alternpol n R 'X_[k]).

Lemma syms_sympM_idomain m (la : 'P_m) nbox :
  's[la] * 'p_(nbox.+1) =
  \sum_(sh : 'P_(nbox.+1 + m) | ribbon la sh)
   (-1) ^+ (ribbon_height la sh).-1 *: 's[sh] :> {sympoly R[n]}.
Proof.
apply val_inj; case: (leqP (size la) n) => szla /=; first last.
  rewrite Schur_oversize // mul0r raddf_sum /=.
  apply/esym/big1 => mu Hrib.
  rewrite Schur_oversize ?scaler0 //.
  apply: (leq_trans szla).
  by move: Hrib => /ribbon_included/includedP[].
rewrite raddf_sum /= [in RHS](bigID (fun sh => size (val sh) <= n)) /=.
rewrite [X in _ = _ + X]big1 ?addr0; first last => [sh /andP[_]|].
  by rewrite -ltnNge => /Schur_oversize ->; rewrite scaler0.
apply: (mulfI (alt_rho_non0 n R)).
rewrite mulrA alt_SchurE // mult_altern_sympol //.
rewrite mulr_sumr; apply eq_bigr => mu /andP[szmu Hrib] /=.
by rewrite -scalerAr alt_SchurE.
Qed.

End MultSymsSympIDomain.


Section MultSymsSymp.

Variable n0 : nat.
Variable R : comRingType.

Local Notation n := n0.+1.
Local Notation rho := (rho n).
Local Notation "''a_' k" := (@alternpol n R 'X_[k]).

Lemma syms_sympM m (la : 'P_m) nbox :
  nbox != 0%N ->
  's[la] * 'p_(nbox) =
  \sum_(sh : 'P_(nbox + m) | ribbon la sh)
   (-1) ^+ (ribbon_height la sh).-1 *: 's[sh] :> {sympoly R[n]}.
Proof.
case: nbox => // nbox _.
rewrite -(map_syms [rmorphism of intr]) -(map_symp [rmorphism of intr]).
rewrite -rmorphM syms_sympM_idomain rmorph_sum /=.
by under [LHS]eq_bigr do rewrite scale_map_sympoly rmorphX rmorphN1 map_syms.
Qed.

End MultSymsSymp.


(** MN_coeff should only be used when [sumn la == sumn mu]. *)
Fixpoint MN_coeff (la mu : seq nat) : int :=
  if mu is m0 :: m then
    foldr (fun sh acc =>
             if ribbon sh la then
               MN_coeff sh m * (-1) ^+ (ribbon_height sh la).-1 + acc
             else acc)
          0 (enum_partn (sumn m))
  else 1.

Lemma MN_coeff0 : MN_coeff [::] [::] = 1.
Proof. by []. Qed.

Lemma MN_coeff_recE la m0 mu :
  MN_coeff la (m0 :: mu) =
  \sum_(sh : 'P_(sumn mu) | ribbon sh la)
   MN_coeff sh mu * (-1) ^+ (ribbon_height sh la).-1.
Proof.
apply esym; transitivity (
                \sum_(sh <- enum_partn (sumn mu) | ribbon sh la)
                 MN_coeff sh mu * (-1) ^+ (ribbon_height sh la).-1).
  by rewrite -enum_intpartnE [LHS]big_mkcond [RHS]big_mkcond big_map big_enum.
rewrite big_mkcond /=; elim: enum_partn => [| p0 p] /=; first by rewrite big_nil.
by rewrite big_cons => ->; case: (ribbon p0 la); rewrite //= add0r.
Qed.


Section Tests.
(** Tests :
[
sage: s(p[2,1,1])
-s[1, 1, 1, 1] - s[2, 1, 1] + s[3, 1] + s[4]
]
*****)
Goal ([seq x | x <- [seq (p, MN_coeff p [:: 2; 1; 1]) | p <- enum_partn 4]
               & x.2 != 0%R] =
      [:: ([:: 4], Posz 1);
      ([:: 3; 1], Posz 1);
      ([:: 2; 1; 1], Negz 0);
      ([:: 1; 1; 1; 1], Negz 0)])%N.
Proof. by []. Abort.

(** Tests :
[
sage: s(p[4,2,1,1])
s[1, 1, 1, 1, 1, 1, 1, 1] + s[2, 1, 1, 1, 1, 1, 1] - s[3, 1, 1, 1, 1, 1] - 2*s[3, 3, 2] - s[4, 1, 1, 1, 1] + 2*s[4, 2, 1, 1] - s[5, 1, 1, 1] - s[6, 1, 1] + s[7, 1] + s[8]
]
*****)
Goal ([seq x | x <- [seq (p, MN_coeff p [:: 4; 2; 1; 1]) | p <- enum_partn 8]
               & x.2 != 0%R] =
      [:: ([:: 8], Posz 1);
      ([:: 7; 1], Posz 1);
      ([:: 3; 3; 2], Negz 1);
      ([:: 6; 1; 1], Negz 0);
      ([:: 4; 2; 1; 1], Posz 2);
      ([:: 5; 1; 1; 1], Negz 0);
      ([:: 4; 1; 1; 1; 1], Negz 0);
      ([:: 3; 1; 1; 1; 1; 1], Negz 0);
      ([:: 2; 1; 1; 1; 1; 1; 1], Posz 1);
      ([:: 1; 1; 1; 1; 1; 1; 1; 1], Posz 1)])%N.
Proof. by []. Abort.

End Tests.

Section MNRule.

Variable n0 : nat.
Local Notation n := n0.+1.

Theorem MN_coeffP_int d (la : 'P_d) :
  'p[la] = \sum_(sh : 'P_d) MN_coeff sh la *: 's[sh] :> {sympoly int[n]}.
Proof.
rewrite /prod_symp /prod_gen.
case: la => la /= /andP [/eqP <-{d} /in_part_non0].
elim: la => [/=|l0 la IHla] Hall.
  rewrite big_nil (big_pred1 (rowpartn 0)) ?scale1r ?syms0 //.
  by move=> i /=; rewrite intpartn0 eqxx.
rewrite big_cons {}IHla; first last.
  by move=> i iinla; apply: Hall; rewrite inE {}iinla orbT.
under [RHS]eq_bigr do rewrite MN_coeff_recE.
rewrite mulr_sumr.
have {Hall} l0n0 : l0 != 0%N by apply: Hall; rewrite inE eqxx.
under eq_bigr do rewrite mulrC -scalerAl syms_sympM // scaler_sumr.
rewrite (exchange_big_dep xpredT) //=; apply: eq_bigr => mu _.
rewrite scaler_suml; apply eq_bigr => nu _.
by rewrite scalerA.
Qed.

Variable R : comRingType.

Theorem MN_coeffP d (la : 'P_d) :
  'p[la] = \sum_(sh : 'P_d) (MN_coeff sh la)%:~R *: 's[sh] :> {sympoly R[n]}.
Proof.
rewrite -(map_symp_prod [rmorphism of intr]) MN_coeffP_int rmorph_sum /=.
by under [LHS]eq_bigr do rewrite scale_map_sympoly map_syms.
Qed.

Theorem MN_coeff_homogP d (la : 'P_d) :
  'hp[la] = \sum_(sh : 'P_d) (MN_coeff sh la)%:~R *: 'hs[sh] :> {homsym R[n, d]}.
Proof.
apply val_inj => /=; apply val_inj => /=.
have /= := congr1 val (MN_coeffP la); rewrite /prod_symp => ->.
by rewrite !raddf_sum.
Qed.

End MNRule.
