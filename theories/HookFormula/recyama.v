(******************************************************************************)
(*       Copyright (C) 2015 Florent Hivert <florent.hivert@lri.fr>            *)
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
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import bigop ssrint rat ssralg ssrnum.
Require Import tools combclass partition Yamanouchi stdtab.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Definition decr_nth_part_def (p : seq nat) i : (seq nat) :=
  if is_rem_corner p i then decr_nth p i
  else p.

Lemma is_part_decr_nth_part (p : intpart) i :
  is_part (decr_nth_part_def p i).
Proof.
rewrite /decr_nth_part_def.
case: (boolP (is_rem_corner p i)).
- by apply is_part_decr_nth; apply: intpartP.
- by move=> _; apply: intpartP.
Qed.

Definition decr_nth_part (p : intpart) i  : intpart :=
  IntPart (is_part_decr_nth_part p i).

Lemma decr_nth_partE (p : intpart) i :
  is_rem_corner p i -> decr_nth_part p i = decr_nth p i :> seq nat.
Proof.
rewrite /decr_nth_part /decr_nth_part_def /=.
by case: (is_rem_corner p i).
Qed.

Lemma card_yama_rec (p : intpart) :
  (p != [::] :> seq nat) ->
  #|{:yameval p}| = \sum_(i <- rem_corners p)
                          #|{:yameval (decr_nth_part p i)}|.
Proof.
move=> H.
rewrite cardE -(size_map val) enum_yamevalE /enum_yameval.
move Hn : (sumn p) => n.
case: n Hn => [| n'] Hn' /=.
  exfalso; move: H.
  by rewrite (part0 (intpartP p) Hn').
rewrite size_flatten /shape sumn_map_condE.
rewrite /rem_corners -!map_comp.
congr sumn; apply eq_in_map => i /=.
rewrite mem_filter => /andP [] Hcorn _.
rewrite size_map cardE -(size_map val) enum_yamevalE.
rewrite /enum_yameval /= /decr_nth_part_def /= Hcorn.
by rewrite (sumn_decr_nth (intpartP p) Hcorn) Hn' /=.
Qed.

Definition empty_part := IntPart (pval := [::]) is_true_true.

Lemma card_yama0 : #|{:yameval empty_part}| = 1.
Proof.
by rewrite cardE -(size_map val) enum_yamevalE.
Qed.

Lemma card_yam_stdtabE (p : intpart) :
  #|{:yameval p}| = #|{:stdtabsh p}|.
Proof.
by rewrite !cardE -!(size_map val) enum_yamevalE enum_stdtabshE size_map.
Qed.

Lemma intpart_rem_corner_ind (f : intpart -> Type) :
  f empty_part ->
  ( forall p : intpart,
      (p != [::] :> seq nat) ->
      (forall i, is_rem_corner p i -> f (decr_nth_part p i) ) -> f p ) ->
  ( forall p : intpart, f p ).
Proof.
move=> H0 Hrec p.
move Hp : (sumn p) => n.
elim: n p Hp => [| n IHn] p Hp.
  suff -> : p = empty_part by apply H0.
  by apply val_inj => /=; apply: (part0 (intpartP p) Hp).
have Hnnil : p != [::] :> seq nat.
  by move: Hp => /eqP; apply contraL => /eqP ->.
apply (Hrec p Hnnil) => i Hi.
apply IHn.
rewrite /decr_nth_part /decr_nth_part_def /= Hi.
by rewrite (sumn_decr_nth (intpartP p) Hi) Hp.
Qed.

Lemma part_rem_corner_ind (f : seq nat -> Type) :
  f [::] ->
  ( forall p, is_part p ->
      (p != [::]) ->
      (forall i, is_rem_corner p i -> f (decr_nth p i) ) -> f p ) ->
  ( forall p, is_part p -> f p ).
Proof.
move=> H0 Hrec p Hp.
move Htmp : (IntPart Hp) => pdep.
have -> : p = pdep by rewrite -Htmp.
elim/intpart_rem_corner_ind: pdep {p Hp Htmp} => [| p Hp IHp] //=.
apply (Hrec p (intpartP p) Hp) => i Hi.
by move/(_ i Hi): IHp; rewrite /= /decr_nth_part_def Hi.
Qed.

Lemma card_stdtabsh_rec (f : intpart -> nat) :
  f empty_part = 1 ->
  ( forall p : intpart,
      (p != [::] :> seq nat) ->
      f p = \sum_(i <- rem_corners p) f (decr_nth_part p i) ) ->
  ( forall p : intpart, f p = #|{:stdtabsh p}| ).
Proof.
move=> H0 Hrec.
elim/intpart_rem_corner_ind => [//= | p Hnnil IHp] /=.
  by rewrite H0 -card_yam_stdtabE card_yama0.
rewrite (Hrec _ Hnnil) -card_yam_stdtabE (card_yama_rec Hnnil).
rewrite /rem_corners !big_filter; apply eq_bigr => i Hi.
by rewrite card_yam_stdtabE IHp //=.
Qed.

Require Import rat_coerce.
Import GRing.Theory.
Import Num.Theory.

Open Scope ring_scope.

Lemma card_stdtabsh_rat_rec (f : intpart -> rat) :
  f empty_part = 1 ->
  ( forall p : intpart,
      (p != [::] :> seq nat) ->
      f p = \sum_(i <- rem_corners p) f (decr_nth_part p i) ) ->
  ( forall p : intpart, f p = #|{:stdtabsh p}| ).
Proof.
move=> H0 Hrec.
elim/intpart_rem_corner_ind => [//= | p Hnnil IHp] /=.
  by rewrite H0 -card_yam_stdtabE card_yama0.
rewrite (Hrec _ Hnnil) -card_yam_stdtabE (card_yama_rec Hnnil).
rewrite (big_morph Posz PoszD (id1 := Posz O%N)) //.
rewrite (big_morph int_to_rat (@intrD _) (id1 := 0)) //.
rewrite /rem_corners !big_filter; apply eq_bigr => i Hi.
by rewrite card_yam_stdtabE IHp //=.
Qed.

