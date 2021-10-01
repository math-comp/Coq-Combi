(** * Combi.SSRComplement.lattice : A simpler mixin for creating lattices     *)
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
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun eqtype choice fintype finset order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Local Open Scope order_scope.

(** TODO remove me when released in MathComp *)
Module MeetJoinLeMixin.
Section MeetJoinLeMixin.
Variable (disp : unit) (T : porderType disp).

Record of_ := Build {
  meet : T -> T -> T;
  join : T -> T -> T;
  meetP : forall x y z, (x <= meet y z) = (x <= y) && (x <= z);
  joinP : forall x y z, (join x y <= z) = (x <= z) && (y <= z);
}.

Fact meet_lel (m : of_) x y : meet m x y <= meet m y x.
Proof.
have:= le_refl (meet m x y); rewrite meetP => /andP [mlex mley].
by rewrite (meetP m) mlex mley.
Qed.
Fact meetC (m : of_) : commutative (meet m).
Proof. by move=> x y; apply le_anti; rewrite !meet_lel. Qed.
Fact meet_leL (m : of_) x y : (meet m x y) <= x.
Proof. by have:= le_refl (meet m x y); rewrite (meetP m) => /andP []. Qed.
Fact meet_leR (m : of_) x y : (meet m x y) <= y.
Proof. by have:= le_refl (meet m x y); rewrite (meetP m) => /andP []. Qed.

Fact join_lel (m : of_) x y : join m x y <= join m y x.
Proof.
have:= le_refl (join m y x); rewrite joinP => /andP [ylej xlej].
by rewrite (joinP m) ylej xlej.
Qed.
Fact joinC (m : of_) : commutative (join m).
Proof. by move=> x y; apply le_anti; rewrite !join_lel. Qed.
Fact join_leL (m : of_) x y : x <= (join m x y).
Proof. by have:= le_refl (join m x y); rewrite (joinP m) => /andP []. Qed.
Fact join_leR (m : of_) x y : y <= (join m x y).
Proof. by have:= le_refl (join m x y); rewrite (joinP m) => /andP []. Qed.

Program Definition latticeMixin (m : of_) :=
  @LatticeMixin disp _ (meet m) (join m) (meetC m) (joinC m) _ _ _ _ _.
Next Obligation.
move=> x y z; apply le_anti.
apply/andP; split; rewrite !meetP -?andbA; apply/and3P; split.
- exact: meet_leL.
- exact: (le_trans (meet_leR m _ _) (meet_leL m _ _)).
- exact: (le_trans (meet_leR m _ _) (meet_leR m _ _)).
- exact: (le_trans (meet_leL m _ _) (meet_leL m _ _)).
- exact: (le_trans (meet_leL m _ _) (meet_leR m _ _)).
- exact: meet_leR.
Qed.
Next Obligation.
move=> x y z; apply le_anti.
apply/andP; split; rewrite !joinP -?andbA; apply/and3P; split.
- exact: (le_trans (join_leL m _ _) (join_leL m _ _)).
- exact: (le_trans (join_leR m _ _) (join_leL m _ _)).
- exact: join_leR.
- exact: join_leL.
- exact: (le_trans (join_leL m _ _) (join_leR m _ _)).
- exact: (le_trans (join_leR m _ _) (join_leR m _ _)).
Qed.
Next Obligation.
apply le_anti.
apply/andP; split; first exact: meet_leL.
by rewrite meetP le_refl join_leL.
Qed.
Next Obligation.
apply le_anti.
apply/andP; split; last exact: join_leL.
by rewrite joinP le_refl meet_leL.
Qed.
Next Obligation. by rewrite eq_le meetP meet_leL le_refl. Qed.

End MeetJoinLeMixin.

Module Exports.
Coercion latticeMixin : of_ >-> Order.LatticeMixin.of_.
Notation meetJoinLeMixin := of_.
Notation MeetJoinLeMixin := Build.
End Exports.

End MeetJoinLeMixin.
Export MeetJoinLeMixin.Exports.



(** * Onder structure on [{set T}] *)
Module SetSubsetOrder.
Section SetSubsetOrder.

Definition type (disp : unit) (T : finType) := {set T}.
Context {disp : unit} {T : finType}.
Local Notation "'set" := (type disp T) (at level 0) : type_scope.
Implicit Type (A B C : 'set).

Lemma le_def A B : A \subset B = (A :&: B == A).
Proof. exact/setIidPl/eqP. Qed.

Lemma setKUC B A : A :&: (A :|: B) = A.
Proof. by rewrite setUC setKU. Qed.

Lemma setKIC B A : A :|: (A :&: B) = A.
Proof. by rewrite setIC setKI. Qed.

Definition t_distrLatticeMixin :=
  MeetJoinMixin le_def (fun _ _ => erefl _) (@setIC _) (@setUC _)
                (@setIA _) (@setUA _) setKUC setKIC (@setIUl _) (@setIid _).


Lemma subset_display : unit. Proof. exact: tt. Qed.

Canonical eqType := [eqType of 'set].
Canonical choiceType := [choiceType of 'set].
Canonical countType := [countType of 'set].
Canonical finType := [finType of 'set].
Canonical porderType := POrderType subset_display 'set t_distrLatticeMixin.
Canonical latticeType := LatticeType 'set t_distrLatticeMixin.
Canonical bLatticeType := BLatticeType 'set
  (BottomMixin (@sub0set _ : forall A, (set0 <= A :> 'set)%O)).
Canonical tbLatticeType := TBLatticeType 'set
  (TopMixin (@subsetT _ : forall A, (A <= setT :> 'set)%O)).
Canonical distrLatticeType := DistrLatticeType 'set t_distrLatticeMixin.
Canonical bDistrLatticeType := [bDistrLatticeType of 'set].
Canonical tbDistrLatticeType := [tbDistrLatticeType of 'set].

Lemma setIDv A B : B :&: (A :\: B) = set0.
Proof.
apply/eqP; rewrite -subset0; apply/subsetP => x.
by rewrite !inE => /and3P[->].
Qed.

Definition t_cbdistrLatticeMixin := CBDistrLatticeMixin setIDv (@setID _).
Canonical cbDistrLatticeType := CBDistrLatticeType 'set t_cbdistrLatticeMixin.

Lemma setTDsym A : ~: A = setT :\: A.
Proof. by rewrite setTD. Qed.

Definition t_ctbdistrLatticeMixin := CTBDistrLatticeMixin setTDsym.
Canonical ctbDistrLatticeType := CTBDistrLatticeType 'set t_ctbdistrLatticeMixin.

Canonical finPOrderType := [finPOrderType of 'set].
Canonical finLatticeType := [finLatticeType of 'set].
Canonical finDistrLatticeType := [finDistrLatticeType of 'set].
Canonical finCDistrLatticeType := [finCDistrLatticeType of 'set].

Lemma leEset A B : (A <= B) = (A \subset B).
Proof. by []. Qed.
Lemma meetEset A B : A `&` B = A :&: B.
Proof. by []. Qed.
Lemma joinEset A B : A `|` B = A :|: B.
Proof. by []. Qed.
Lemma botEset : 0 = set0 :> 'set.
Proof. by []. Qed.
Lemma topEset : 1 = setT :> 'set.
Proof. by []. Qed.
Lemma subEset A B : A `\` B = A :\: B.
Proof. by []. Qed.
Lemma complEset A : ~` A = ~: A.
Proof. by []. Qed.

End SetSubsetOrder.

Module Exports.

Notation "{set[ d ]<= T }" := (type d T)
  (at level 70, d at next level, format "{set[ d ]<=  T }") : type_scope.
Notation "{set<= T }" := (type subset_display T)
  (at level 70, format "{set<=  T }") : type_scope.

Set Warnings "-redundant-canonical-projection".
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Canonical porderType.
Canonical latticeType.
Canonical bLatticeType.
Canonical tbLatticeType.
Canonical distrLatticeType.
Canonical bDistrLatticeType.
Canonical tbDistrLatticeType.
Canonical cbDistrLatticeType.
Canonical ctbDistrLatticeType.
Canonical finPOrderType.
Canonical finLatticeType.
Canonical finDistrLatticeType.
Canonical finCDistrLatticeType.
Set Warnings "+redundant-canonical-projection".

Definition leEset := @leEset.
Definition meetEset := @meetEset.
Definition joinEset := @joinEset.
Definition botEset := @botEset.
Definition topEset := @topEset.
Definition subEset := @subEset.
Definition complEset := @complEset.

End Exports.
End SetSubsetOrder.
Export SetSubsetOrder.Exports.

Section BLattice.

Variables (disp : unit) (T : porderType disp).
Variables (disp' : unit) (T' : bLatticeType disp') (f : T -> T').

Variables (f' : T' -> T) (f_can : cancel f f') (f'_can : cancel f' f).
Variable (f_mono : {mono f : x y / x <= y}).

Lemma le0x x : f' 0 <= x.
Proof. by rewrite -f_mono f'_can le0x. Qed.

Definition IsoBottomMixin :=
  @BottomMixin _ (LatticeType T (Order.CanMixin.IsoLattice f_can f'_can f_mono))
               _ le0x.

End BLattice.

Section TBLattice.

Variables (disp : unit) (T : bLatticeType disp).
Variables (disp' : unit) (T' : tbLatticeType disp') (f : T -> T').

Variables (f' : T' -> T) (f_can : cancel f f') (f'_can : cancel f' f).
Variable (f_mono : {mono f : x y / x <= y}).

Lemma lex1 x : x <= f' 1.
Proof. by rewrite -f_mono f'_can lex1. Qed.

Definition IsoTopMixin :=
  @TopMixin _ (BLatticeType T (IsoBottomMixin f_can f'_can f_mono))
            _ lex1.

End TBLattice.
