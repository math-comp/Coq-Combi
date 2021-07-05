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
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.


Module MeetJoinLeMixin.
Section MeetJoinLeMixin.
Variable (disp : unit) (T : porderType disp).
Open Scope order_scope.

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
