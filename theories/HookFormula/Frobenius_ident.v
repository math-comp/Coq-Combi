(** * Combi.hook.Frobenius_ident : Frobenius identity *)
(******************************************************************************)
(*      Copyright (C) 2015-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * A proof of Frobenius identity:

The goal of this file is to prove the following identities:
[[
Frobenius_ident n :
    n`! = \sum_(p : 'P_n) (n`! %/ (hook_length_prod p))^2.
]]
and
[[
Theorem Frobenius_ident_rat n :
    1 / (n`!)%:Q = \sum_(p : 'P_n) 1 / (hook_length_prod p)%:Q ^+ 2.
]]
 ******)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype choice ssrnat seq
        ssrint div rat fintype finset bigop path ssralg ssrnum order.
(* Import bigop before ssralg/ssrnum to get correct printing of \sum \prod*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import ordtype partition tableau Schensted std stdtab hook.

Section Identity.

Variable n : nat.

Local Notation stpn := (stdtabn n * stdtabn n)%type.
Lemma card_stpn_shape :
  #|[set p : stpn | shape p.1 == shape p.2]| =
    \sum_(sh : 'P_n) #|{:stdtabsh sh}|^2.
Proof.
pose pairsh (sh : intpartn n) :=
  [set p : stpn | (shape_deg p.1 == sh) && (shape_deg p.2 == sh)].
have pairshP (sh : intpartn n) :
  {t : stdtabsh sh | (stdtabn_of_sh t, stdtabn_of_sh t) \in pairsh sh}.
  by exists (hyper_stdtabsh sh); rewrite inE /= !shape_deg_stdtabn_of_sh eqxx.
pose shpart := [set pairsh sh | sh : intpartn n].
have /card_partition -> :
    partition shpart [set p : stpn | shape_deg p.1 == shape_deg p.2].
  apply/and3P; split.
  - apply/eqP/setP => /= [[t1 t2]]; rewrite inE /=.
    apply/bigcupP/eqP => /= [[S /imsetP [/= sh _ ->{S}]] | eqsh].
    + by rewrite inE => /= /andP [/eqP-> /eqP->].
    + exists [set p : stpn | (shape_deg p.1 == shape_deg t1) &&
                             (shape_deg p.2 == shape_deg t1)].
      apply/imsetP; exists (shape_deg t1) => //.
      by rewrite inE /= eqxx /=; apply/eqP; rewrite /= eqsh.
  - apply/trivIsetP=> /= S1 S2 /imsetP[sh1 _ ->{S1}] /imsetP[sh2 _ ->{S2}] neq.
    have {neq} neqsh : sh1 != sh2 by move: neq; apply contra => /eqP ->.
    rewrite -setI_eq0; apply/set0Pn => /=[[[t1 t2]]].
    rewrite !inE /= -!andbA => /and4P [/eqP ->] _ /eqP eqsh _.
    by rewrite eqsh eqxx in neqsh.
  - apply/negP=> /imsetP [/= sh _] Heq.
    by have [t] := pairshP sh; rewrite -Heq inE.
rewrite big_imset /=; first last.
  move=> sh1 sh2 _ _ eqsh; have [t] := pairshP sh1.
  by rewrite eqsh inE /= shape_deg_stdtabn_of_sh => /andP[/eqP].
apply eq_bigr => sh _; rewrite -mulnn -!cardsT -cardsX.
rewrite [RHS](eq_card (B := setT)) /=; last by move=> p; rewrite !inE.
pose to_stpn (p : (stdtabsh sh) * (stdtabsh sh)) : stpn :=
  (stdtabn_of_sh p.1, stdtabn_of_sh p.2).
have /card_imset <- : injective to_stpn.
  by rewrite /to_stpn => [[t1 t2] [u1 u2]] /= [/val_inj-> /val_inj->].
apply: eq_card => [[/= t1 t2]]; rewrite !inE /=.
apply/andP/imsetP => /= [[/eqP sht1 /eqP sht2] | [[u1 u2] _ [->{t1}->{t2}]]];
  last by rewrite !shape_deg_stdtabn_of_sh.
have t1sh : is_stdtab_of_shape sh t1.
  by rewrite /= stdtabnP /=; have /= -> := (congr1 val sht1).
have t2sh : is_stdtab_of_shape sh t2.
  by rewrite /= stdtabnP /=; have /= -> := (congr1 val sht2).
exists (@StdtabSh sh t1 t1sh, @StdtabSh sh t2 t2sh); first by [].
rewrite /to_stpn /=.
by apply/eqP; rewrite xpair_eqE; apply/andP; split; apply/eqP/val_inj.
Qed.

Lemma card_stpn_shape_hook :
  #|[set p : stpn | shape p.1 == shape p.2]| =
    \sum_(sh : 'P_n) (n`! %/ (hook_length_prod sh))^2.
Proof using.
rewrite card_stpn_shape; apply eq_bigr => sh _; congr (_ ^ 2).
by rewrite HookLengthFormula sumn_intpartn.
Qed.

Theorem Frobenius_ident :
  n`! = \sum_(p : 'P_n) (n`! %/ (hook_length_prod p))^2.
Proof using.
rewrite -{1}card_stdwordn -card_stpn_shape_hook.
have rst1 (w : stdwordn n) : is_stdtab_of_n n (RStabmap w).1.
  by rewrite RStabmapE /= RSstdE stdwordnP /= size_RS size_sdtn.
have rst2 (w : stdwordn n) : is_stdtab_of_n n (RStabmap w).2.
  rewrite /= is_stdtab_RStabmap2 /size_tab -shape_RStabmapE.
  by rewrite RStabmapE -/(size_tab _) size_RS size_sdtn eqxx.
pose to_pair (w : stdwordn n) := (StdtabN (rst1 w), StdtabN (rst2 w)).
pose stdrspair (p : stpn) :=
  if shape p.1 == shape p.2 then (val p.1, val p.2)
  else (val p.1, val p.1) (* Unused *).
have stdrspairP p : is_RStabpair (stdrspair p).
  rewrite /is_RStabpair/stdrspair.
  by case: eqP => /= [-> |_]; rewrite stdtabnP eqxx stdtabP.
pose stdrsinv p := RStabinv (RSTabPair (stdrspairP p)).
have from_pairP p : is_std_of_n n (stdrsinv p).
  case: p => [t1 t2]; rewrite /= /stdrsinv /= -RSstdE -size_RS -RStabmapE.
  rewrite -[RStabmap _]/(val (RStab _)) RStabinvK /stdrspair /=.
  rewrite [(_).1](_ : _ = val t1); last by case (altP (shape t1 =P shape t2)).
  by rewrite stdtabnP /= size_tab_stdtabn.
pose from_pair p := StdWordN (from_pairP p).
have to_pairK : cancel to_pair from_pair.
  move=> w; apply val_inj; rewrite /= /stdrsinv /= /stdrspair /to_pair.
  rewrite [RSTabPair _](_ : _ = RStab w) ?RStabK //.
  apply val_inj; rewrite /= /stdrspair /= shape_RStabmapE eqxx.
  by case: RStabmap.
rewrite -(card_imset _ (can_inj to_pairK)); apply eq_card => [[/= t1 t2]].
rewrite inE /=; apply/imsetP/idP=>/= [[w _ [->{t1}->{t2}/=]] | eqsh].
  by rewrite shape_RStabmapE.
exists (from_pair (t1, t2)); first by [].
apply/eqP; rewrite xpair_eqE /= -!val_eqE /= /stdrsinv.
by rewrite -[RStabmap _]/(val (RStab _)) RStabinvK /= /stdrspair eqsh !eqxx.
Qed.

Local Open Scope ring_scope.

Import GRing.Theory.
Import Num.Theory.

Theorem Frobenius_ident_rat :
  1 / (n`!)%:Q = \sum_(p : 'P_n) 1 / (hook_length_prod p)%:Q ^+ 2.
Proof using.
rewrite -[RHS]mulr1.
have Hfn0 : n`!%:Q != 0 by rewrite intr_eq0 eqz_nat -lt0n fact_gt0.
rewrite -{5}(@divff _ ((n`!%:Q) ^+ 2)); last by rewrite sqrf_eq0.
rewrite mulrA mulr_suml.
rewrite (eq_bigr (fun p : 'P_n => ((n`! %/ (hook_length_prod p)) ^ 2)%N%:Q));
  first last.
  move=> p _; rewrite PoszM intrM.
  have -> : (n`! %/ hook_length_prod p)%:Q = (n`!)%:Q / (hook_length_prod p)%:Q.
    rewrite -[LHS]mulr1 -{2}(@divff _ (hook_length_prod p)%:Q); first last.
      by rewrite intr_eq0 eqz_nat /=; apply: (hook_length_prod_non0 p).
    rewrite !mulrA -intrM -PoszM.
    have:= hook_length_prod_div p.
    by rewrite sumn_intpartn dvdn_eq => /eqP ->.
  by rewrite -expr2 expr_div_n mulrC mul1r.
rewrite -!(big_morph intr (@intrD _) (id2 := 0)) //=.
rewrite -!(big_morph Posz PoszD (id2 := 0%N)) //=.
rewrite -Frobenius_ident expr2.
by rewrite invfM mulrA divff.
Qed.

End Identity.
