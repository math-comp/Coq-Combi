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
(** * The Murnaghan-Nakayama rule

See the page
#<a href="https://en.wikipedia.org/wiki/Murnaghan%E2%80%93Nakayama_rule">Murnaghan-Nakayama</a># on Wikipedia for a statement. The fixpoint [MN_coeff la mu]
implement the recursive version, as stated in
[[
Theorem MN_coeff_consE la m0 mu :
  MN_coeff la (m0 :: mu) =
  \sum_(sh : 'P_(sumn mu) | ribbon sh la)
   MN_coeff sh mu * (-1) ^+ (ribbon_height sh la).-1.
]]
and the base case
[[
Lemma MN_coeff0 : MN_coeff [::] [::] = 1.
]]
The Murnaghan-Nakayama rule stated in terms of symmetric polynomials is then
[[
Theorem MN_coeffP d (la : 'P_d) :
  'p[la] = \sum_(sh : 'P_d) (MN_coeff sh la)%:~R *: 's[sh] :> {sympoly R[n]}.
]]
There is a second implementation which goes bottom up, adding ribbons instead
of removing them. It allows to compute skew Murnaghan-Nakayama coefficients.

We provide the following definitions:

- [MN_coeff la mu] == then Murnaghan-Nakayama coefficients. That is the
               alternating number of ribbon filling of the shape [la]
               with content [mu], defined recursively.
- [MN_coeff_fast la mu] == fast version of [MN_coeff la mu]
- [MN_coeff_rec la nu mu] == The alternating number of ribbon filling of
               the skew shape [la / nu] with content [mu], defined recursively.
 ******)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import bigop ssralg ssrint perm fingroup tuple vector rat.
From SsrMultinomials Require Import ssrcomplements freeg mpoly monalg.

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


(** ** Product of an alternating polynomial and a power sum *)
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
   (add_ribbon p d i).
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
  \sum_(psh <- pmap (add_ribbon p d) (iota 0 n))
   (-1) ^+ (psh.2).-1 *: 'a_(mpart psh.1 + rho).
Proof.
move=> partp szp; rewrite mult_altern_oapp //.
rewrite -(big_mkord xpredT (fun i => oapp _ 0 (add_ribbon p d i))).
by rewrite big_pmap /index_iota subn0.
Qed.

End MultAlternSymp.


(** ** Product of a Schur polynomial and a power sum *)
(* We first state the theorem on ints and then transfer to any ring *)
Section MultSymsSympIDomain.

Variable n0 : nat.
Local Notation n := n0.+1.
Local Notation SF := {sympoly int[n]}.

Lemma syms_sympM_oapp_int d (la : 'P_d) m :
  m != 0%N -> size la <= n ->
  's[la] * 'p_m =
  \sum_(i < n) oapp (fun ph => (-1) ^+ ph.2.-1 *: 's[ph.1]) 0
   (add_ribbon_intpartn la m.-1 i) :> SF.
Proof.
case: m => // m _ szla; apply val_inj.
rewrite /= !raddf_sum /=.
apply: (mulfI (alt_rho_non0 n _)).
rewrite mulrA alt_SchurE //= mult_altern_oapp //.
rewrite mulr_sumr; apply eq_bigr => mu _.
rewrite add_ribbon_intpartnE.
case Haddrib: add_ribbon_intpartn => [[sh h]|]/=; last by rewrite mulr0.
move/add_ribbon_intpartnP in Haddrib.
rewrite -scalerAr alt_SchurE //.
by rewrite (size_add_ribbon Haddrib) geq_max szla ltn_ord.
Qed.

End MultSymsSympIDomain.


Section MultSymsSymp.

Variable n0 : nat.
Variable R : comRingType.
Local Notation n := n0.+1.
Local Notation SF := {sympoly R[n]}.

Lemma syms_sympM_oapp d (la : 'P_d) m :
  m != 0%N ->
  's[la] * 'p_m =
  \sum_(i < n) oapp (fun ph => (-1) ^+ ph.2.-1 *: 's[ph.1]) 0
   (add_ribbon_intpartn la m.-1 i) :> SF.
Proof.
move=> Hm.
case: (leqP (size la) n) => szla; first last.
  rewrite syms_oversize // mul0r; apply/esym/big1 => /= i _.
  case Haddrib: add_ribbon_intpartn => [[sh h]|]//=.
  move/add_ribbon_intpartnP in Haddrib.
  rewrite syms_oversize ?scaler0 //.
  by rewrite (size_add_ribbon Haddrib) leq_max szla.
rewrite -(map_syms [rmorphism of intr]) -(map_symp [rmorphism of intr]).
rewrite -rmorphM syms_sympM_oapp_int // rmorph_sum /=.
apply eq_bigr => i _.
case: add_ribbon_intpartn => [p|]/=; last by rewrite rmorph0.
by rewrite scale_map_sympoly rmorphX rmorphN1 map_syms.
Qed.

Lemma syms_sympM_pmap d (la : 'P_d) m :
  m != 0%N ->
  's[la] * 'p_m =
  \sum_(ph <- pmap (add_ribbon_intpartn la m.-1) (iota 0 n))
   (-1) ^+ ph.2.-1 *: 's[ph.1] :> SF.
Proof.
move=> Hm; rewrite syms_sympM_oapp //.
by rewrite big_pmap -[n in iota 0 n](subn0 n) -/(index_iota 0 n) big_mkord.
Qed.

(** The following theorem is a step of the Murnaghan-Nakayama rule *)
Theorem syms_sympM d (la : 'P_d) m :
  m != 0%N ->
  's[la] * 'p_m =
  \sum_(sh : 'P_(m + d) | ribbon la sh)
   (-1) ^+ (ribbon_height la sh).-1 *: 's[sh] :> SF.
Proof.
move=> Hm.
case: (ltnP n (size la)) => szla.
  rewrite syms_oversize // mul0r; apply/esym/big1 => /= i.
  move=> /ribbon_included/includedP [/(leq_trans szla)/syms_oversize -> _].
    by rewrite scaler0.
rewrite (syms_sympM_oapp _ Hm).
case: m Hm => // m _.
rewrite (bigID (fun i : 'I_n => add_ribbon_intpartn la m i)) /=.
rewrite [X in _ + X = _]big1 ?addr0;
  last by move=> i; case: add_ribbon_intpartn.
rewrite [RHS](bigID (fun sh => size (val sh) <= n)) /=.
rewrite [X in _ = _ + X]big1 ?addr0; first last => [mu /andP[_]|].
  by rewrite -ltnNge => /syms_oversize ->; rewrite scaler0.
have ribbon_stop_subproof (mu : 'P_(m.+1 + d)) :
  (if size mu <= n then (mindropeq la mu).-1 else 0%N) < n.
  case: (leqP (size mu) n) => // szmu.
  case: mindropeq (mindropeq_leq la mu) => // md /= /leq_trans; apply.
  by rewrite geq_max szla szmu.
pose ribbon_stop mu := Ordinal (ribbon_stop_subproof mu).
rewrite (reindex_omap ribbon_stop
          (omap fst \o (add_ribbon_intpartn la m))) /=; first last => [i|].
  case Haddrib: add_ribbon_intpartn => [[res h]|]//= _.
  move/add_ribbon_intpartnP in Haddrib.
  congr Some; apply val_inj => /=.
  rewrite (size_add_ribbon Haddrib) geq_max szla ltn_ord /=.
  rewrite (ribbon_on_mindropeq (intpartnP la) _ (add_ribbon_onP Haddrib)) //.
  exact: (is_part_add_ribbon _ Haddrib).
apply esym; apply: eq_big => mu.
  rewrite andbC; case leqP => Hszmu /=; first last.
  + case Haddrib: add_ribbon_intpartn => [[res h]|] //=; first last.
    move/add_ribbon_intpartnP in Haddrib.
    case (altP (_ =P Some mu)) => // [[Heq]].
    have := size_add_ribbon Haddrib; rewrite {res Haddrib}Heq /= => Heq.
    by move: Hszmu; rewrite Heq leq_max 2!ltnNge szla.
  + apply esym; case: (boolP (ribbon la mu)) => [Hrib | Hnrib].
    * have := ribbon_addE (intpartnP la) (intpartnP mu) Hrib.
      rewrite sumn_diff_shape ?ribbon_included // !sumn_intpartn addnK.
      rewrite add_ribbon_intpartnE.
      case Haddrib: add_ribbon_intpartn => [[res h]|]//=.
      by move=> [/val_inj ->]; rewrite eqxx.
    * case Haddrib: add_ribbon_intpartn => [[res h]|]//=.
      move/add_ribbon_intpartnP in Haddrib.
      apply/negP => /eqP [] Heq.
      by move: Hnrib; rewrite -{}Heq (add_ribbonP _ Haddrib).
move=> /andP[Hrib ->].
have:= ribbon_addE (intpartnP la) (intpartnP mu) Hrib.
rewrite sumn_diff_shape ?ribbon_included // !sumn_intpartn addnK.
rewrite add_ribbon_intpartnE.
by case Haddrib: add_ribbon_intpartn => [[res h]|]//= [/val_inj -> <-].
Qed.

End MultSymsSymp.


(** * Murnaghan-Nakayama coefficients *)

(** We define those for any sequence of nat, but              *)
(** [MN_coeff] should only be used when [sumn la == sumn mu]. *)
Fixpoint MN_coeff (la mu : seq nat) : int :=
  if mu is m0 :: m then
    foldr (fun sh acc =>
             if ribbon sh la then
               MN_coeff sh m * (-1) ^+ (ribbon_height sh la).-1 + acc
             else acc)
          0 (enum_partn (sumn m))
  else 1.

(** Base case *)
Lemma MN_coeff0 : MN_coeff [::] [::] = 1.
Proof. by []. Qed.

(** Recursive step *)
Theorem MN_coeff_consE la m0 mu :
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
<<
sage: s(p[2,1,1])
-s[1, 1, 1, 1] - s[2, 1, 1] + s[3, 1] + s[4]
>>
*****)
Goal ([seq x | x <- [seq (p, MN_coeff p [:: 2; 1; 1]) | p <- enum_partn 4]
               & x.2 != 0%R] =
      [:: ([:: 4], Posz 1);
      ([:: 3; 1], Posz 1);
      ([:: 2; 1; 1], Negz 0);
      ([:: 1; 1; 1; 1], Negz 0)])%N.
Proof. by []. Abort.

(** Tests :
<<
sage: s(p[4,2,1,1])
s[1, 1, 1, 1, 1, 1, 1, 1] + s[2, 1, 1, 1, 1, 1, 1] - s[3, 1, 1, 1, 1, 1]
 - 2*s[3, 3, 2] - s[4, 1, 1, 1, 1] + 2*s[4, 2, 1, 1] - s[5, 1, 1, 1]
 - s[6, 1, 1] + s[7, 1] + s[8]
>>
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

(** * Murnaghan-Nakayama rule *)
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
under [RHS]eq_bigr do rewrite MN_coeff_consE.
rewrite mulr_sumr.
have {Hall} l0n0 : l0 != 0%N by apply: Hall; rewrite inE eqxx.
under eq_bigr do rewrite mulrC -scalerAl syms_sympM // scaler_sumr.
rewrite (exchange_big_dep xpredT) //=; apply: eq_bigr => mu _.
rewrite scaler_suml; apply eq_bigr => nu _.
by rewrite scalerA.
Qed.

Variable R : comRingType.
Local Notation SF := {sympoly R[n]}.
Local Notation HSF := {homsym R[n, _]}.

Theorem MN_coeffP d (la : 'P_d) :
  'p[la] = \sum_(sh : 'P_d) (MN_coeff sh la)%:~R *: 's[sh] :> SF.
Proof.
rewrite -(map_symp_prod [rmorphism of intr]) MN_coeffP_int rmorph_sum /=.
by under [LHS]eq_bigr do rewrite scale_map_sympoly map_syms.
Qed.

Corollary MN_coeff_homogP d (la : 'P_d) :
  'hp[la] = \sum_(sh : 'P_d) (MN_coeff sh la)%:~R *: 'hs[sh] :> HSF.
Proof.
apply val_inj => /=; apply val_inj => /=.
have /= := congr1 val (MN_coeffP la); rewrite /prod_symp => ->.
by rewrite !raddf_sum.
Qed.

End MNRule.



(** [MN_coeff_rec] should only be used when [sumn la == sum nu + sumn mu]. *)
Fixpoint MN_coeff_rec (la nu mu : seq nat) : int :=
  if mu is m0 :: m then
    foldr (fun psh acc =>
             MN_coeff_rec la psh.1 m * (-1) ^+ psh.2.-1 + acc)
          0
          [seq psh | psh <- pmap (add_ribbon nu m0.-1) (iota 0 (size la))
                   & included psh.1 la]
  else (la == nu).
Definition MN_coeff_fast la mu := MN_coeff_rec la [::] mu.


Lemma MN_coeff_rec_szE la nu m0 mu :
  MN_coeff_rec la nu (m0 :: mu) =
  \sum_(psh <- pmap (add_ribbon nu m0.-1) (iota 0 (size la))
       | included psh.1 la)
   MN_coeff_rec la psh.1 mu * (-1) ^+ psh.2.-1.
Proof.
rewrite /=; elim: pmap => [|[sh0 h0] s IHs]/=; first by rewrite big_nil.
by rewrite big_cons /= -{}IHs; case: included.
Qed.

Lemma MN_coeff_rec_notincl la nu mu :
  0%N \notin mu -> is_part nu ->  ~~ included nu la ->
  MN_coeff_rec la nu mu = 0.
Proof.
elim: mu nu => [/= |[|m0] mu IHmu] nu //.
  by case: eqP => // ->; rewrite included_refl.
rewrite inE negb_or eq_sym => /andP[_ {}/IHmu Hrec] partnu nincl.
rewrite MN_coeff_rec_szE big_mkcond big_pmap /=; apply big1 => i _.
case Haddrib : add_ribbon => [[sh h]|]//=.
suff /negbTE -> : ~~ included sh la by [].
by apply/contra : nincl =>
  /(included_trans (included_add_ribbon partnu Haddrib)).
Qed.

Lemma MN_coeff_rec_consE n la nu m0 mu :
  m0 != 0%N -> size la <= n ->
  MN_coeff_rec la nu (m0 :: mu) =
  \sum_(psh <- pmap (add_ribbon nu m0.-1) (iota 0 n) | included psh.1 la)
   MN_coeff_rec la psh.1 mu * (-1) ^+ psh.2.-1.
Proof.
case: m0 => // m0 _ Hsz; rewrite MN_coeff_rec_szE.
rewrite big_mkcond big_pmap -(subn0 (size la)) -/(index_iota 0 _) /=.
rewrite [RHS]big_mkcond big_pmap -(subn0 n) -/(index_iota 0 _) /=.
rewrite (big_cat_nat _ _ _ _ Hsz) //=.
rewrite [X in _ + X]big_nat [X in _ + X]big1 ?addr0 // => i /andP[leszi _].
case Haddrib : add_ribbon => [[sh h]|]//=.
suff /negbTE -> : ~~ included sh la by [].
apply/negP => /includedP [] + _.
by rewrite (size_add_ribbon Haddrib) geq_max ltnNge leszi andbF.
Qed.

Section Tests.

(** Tests :
<<
sage: s(p[3, 3, 1, 1]).coefficient([5, 2, 1])
-2
>>
*****)
Goal MN_coeff_fast [:: 5; 2; 1]%N [:: 3; 3; 1; 1]%N = - 2%:R.
Proof. by []. Abort.
(** Tests :
<<
sage: s(p[5, 2, 1]).coefficient([3, 3, 1, 1])
1
>>
*****)
Goal MN_coeff_fast [:: 3; 3; 1; 1]%N [:: 5; 2; 1]%N = 1%:R.
Proof. by []. Abort.

(** Tests :
<<
sage: s(p[6, 5, 5, 4, 2, 1]).coefficient([12, 5, 2, 2, 1, 1])
4
>>
*****)
Goal MN_coeff_fast [:: 12; 5; 2; 2; 1; 1]%N [:: 6; 5; 5; 4; 2; 1]%N = 4%:R.
Proof. by []. Abort.
(** Tests :
<<
sage: s(p[6, 5, 5, 4, 2, 1]).coefficient([12, 5, 3, 1, 1, 1])
-2
>>
*****)
Goal MN_coeff_fast [:: 12; 5; 3; 1; 1; 1]%N [:: 6; 5; 5; 4; 2; 1]%N = - 2%:R.
Proof. by []. Abort.
Goal MN_coeff_fast [:: 12; 5; 3; 2; 1]%N [:: 6; 5; 5; 4; 2; 1]%N = - 3%:R.
Proof. by []. Abort.
Goal MN_coeff_fast [:: 12; 5; 4; 1; 1]%N [:: 6; 5; 5; 4; 2; 1]%N = 2%:R.
Proof. by []. Abort.
Goal MN_coeff_fast [:: 12; 5; 4; 2]%N [:: 6; 5; 5; 4; 2; 1]%N = 4%:R.
Proof. by []. Abort.

End Tests.



Section FastImplem.

Variable n0 : nat.
Local Notation n := n0.+1.

Lemma syms_prod_sympM_int dn (nu : 'P_dn) dm (mu : 'P_dm) :
  's[nu] * 'p[mu] =
  \sum_(la : 'P_(dn + dm)) MN_coeff_rec la nu mu *: 's[la] :> {sympoly int[n]}.
Proof.
case: mu => [mu /= Hnu]; rewrite /prod_symp /prod_gen /=.
move: Hnu => /andP[/eqP <-{dm} /notin0_part].
elim: mu dn nu => [|m0 mu IHmu] d nu.
  rewrite big_nil mulr1 (bigD1 (cast_intpartn (esym (addn0 d)) nu)) //=.
  rewrite syms_cast cast_intpartnE // eqxx scale1r.
  rewrite big1 ?addr0 // => la.
  rewrite -val_eqE /= cast_intpartnE => /negbTE ->.
  by rewrite scale0r.
rewrite inE negb_or eq_sym => /andP [Hm0 Hmu].
rewrite big_cons mulrA syms_sympM_oapp //.
move Hmmu : (m0 :: mu) => mmu.  (* to prevent the expansion of MN_coeff_rec *)
rewrite [RHS](bigID (fun sh => size (val sh) <= n)) /=.
rewrite [X in _ + X]big1 ?addr0; first last => [la|].
  by rewrite -ltnNge => /syms_oversize ->; rewrite scaler0.
under [RHS]eq_bigr => la Hla.
  rewrite -{2}Hmmu (MN_coeff_rec_consE _ _ Hm0 Hla).
  rewrite big_mkcond big_pmap.
  rewrite -[n in iota 0 n](subn0 n) -/(index_iota 0 n) big_mkord /=.
  by rewrite scaler_suml over.
rewrite [RHS]exchange_big /= mulr_suml; apply: eq_bigr => i _.
rewrite -{mmu}Hmmu; case: m0 Hm0 => // m0 _ /=.
rewrite add_ribbon_intpartnE.
case Haddrib: add_ribbon_intpartn => [[res h]|]/=; first last.
  by rewrite mul0r; apply/esym/big1 => t; rewrite scale0r.
rewrite -scalerAl {}IHmu // scaler_sumr.
have cast_eq : (d + (m0.+1 + sumn mu) = m0.+1 + d + sumn mu)%N.
  by rewrite [(m0.+1 + d)%N]addnC addnA.
rewrite (reindex _ (onW_bij _ (cast_intpartn_bij cast_eq))) /=.
under [LHS]eq_bigr do rewrite cast_intpartnE syms_cast /=.
rewrite [LHS](bigID (fun sh => size (val sh) <= n)) /=.
rewrite [X in _ + X]big1 ?addr0; first last => [la|].
  by rewrite -ltnNge => /syms_oversize ->; rewrite !scaler0.
apply eq_bigr => la szla.
case: (boolP (included res la)) => incl; first by rewrite scalerA mulrC.
by rewrite MN_coeff_rec_notincl // !scale0r scaler0.
Qed.

Section ComRing.

Variable R : comRingType.
Local Notation SF := {sympoly R[n]}.
Local Notation HSF := {homsym R[n, _]}.

Theorem syms_prod_sympM dn (nu : 'P_dn) dm (mu : 'P_dm) :
  's[nu] * 'p[mu] =
  \sum_(la : 'P_(dn + dm)) (MN_coeff_rec la nu mu)%:~R *: 's[la] :> SF.
Proof.
rewrite -(map_syms [rmorphism of intr]) -(map_symp_prod [rmorphism of intr]).
rewrite -rmorphM syms_prod_sympM_int rmorph_sum /=.
by under [LHS]eq_bigr do rewrite scale_map_sympoly map_syms.
Qed.

Corollary homsyms_homsympM dn (nu : 'P_dn) dm (mu : 'P_dm) :
  'hs[nu] *h 'hp[mu] =
  \sum_(la : 'P_(dn + dm)) (MN_coeff_rec la nu mu)%:~R *: 'hs[la] :> HSF.
Proof.
apply val_inj => /=; apply val_inj => /=.
have /= := congr1 val (syms_prod_sympM nu mu); rewrite /prod_symp => ->.
by rewrite !raddf_sum.
Qed.

Corollary MN_coeff_recP d (la : 'P_d) :
  'p[la] = \sum_(sh : 'P_d) (MN_coeff_fast sh la)%:~R *: 's[sh] :> SF.
Proof.
rewrite -[LHS]mul1r -(syms0 _ _ (colpartn 0)).
by rewrite syms_prod_sympM; apply eq_bigr => sh _; rewrite colpartnE.
Qed.

Corollary MN_coeff_rec_homogP d (la : 'P_d) :
  'hp[la] = \sum_(sh : 'P_d) (MN_coeff_fast sh la)%:~R *: 'hs[sh] :> HSF.
Proof.
apply val_inj => /=; apply val_inj => /=.
have /= := congr1 val (MN_coeff_recP la); rewrite /prod_symp => ->.
by rewrite !raddf_sum.
Qed.

End ComRing.

End FastImplem.

(** The two implementations coincide *)
Corollary MN_coeffE d (la mu : 'P_d) : MN_coeff_fast la mu = MN_coeff la mu.
Proof.
pose HSF := {homsym rat[(sumn mu).+1 , d]}.
pose Pval i := (@enum_val _ xpredT i : 'P_d).
have : \sum_i (MN_coeff_rec (Pval i) [::] mu)%:~R *: 'hs`_i =
       \sum_i (MN_coeff     (Pval i) mu     )%:~R *: 'hs`_i :> HSF.
  rewrite !(reindex _ (onW_bij _ (@enum_rank_bij [finType of 'P_d]))) /=.
  under [LHS]eq_bigr do rewrite /Pval symbsE enum_rankK.
  under [RHS]eq_bigr do rewrite /Pval symbsE enum_rankK.
  by rewrite -[LHS]MN_coeff_rec_homogP -[RHS]MN_coeff_homogP.
move/(congr1 (coord 'hs (enum_rank la))) => /eqP.
have free_hs : free ('hs : seq HSF) by apply: symbs_free; rewrite sumn_intpartn.
by rewrite !coord_sum_free // {}/Pval enum_rankK => /eqP/intr_inj.
Qed.
