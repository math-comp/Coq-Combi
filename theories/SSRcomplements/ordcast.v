(** * Combi.SSRcomplements.ordcast : Cast between ordinals *)
(******************************************************************************)
(*      Copyright (C) 2014-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * Some complement on casts between ordinals

Aside a few basic lemmas, the only new definition is:
- [cast_set (H : n = m) S] == cast [S : {set 'I_n}] to [S : {set 'I_m}].
*********)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
From mathcomp Require Import finset tuple bigop.

Require Import  tools.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Lemma enum_cast_ord m n (H : n = m):
  enum 'I_m = [seq cast_ord H i | i <- enum 'I_n].
Proof.
  subst m; rewrite /= (eq_map (f2 := id)) ?map_id // => i; by apply: val_inj.
Qed.

Lemma nth_ord_ltn i n (H : i < n) x0 : nth x0 (enum 'I_n) i = (Ordinal H).
Proof. by apply: val_inj => //=; rewrite nth_enum_ord. Qed.

Section Casts.

Lemma cast_erefl n : cast_ord (erefl n) =1 id.
Proof. by move=> i; apply/eqP; rewrite /eq_op /=. Qed.

Lemma cast_eq m n i j (H : m = n) : ((cast_ord H i) == (cast_ord H j)) = (i == j).
Proof. subst m; by rewrite !cast_erefl. Qed.

Lemma sym_cast_eq m n i j : ((cast_ord (addnC m n) i) == cast_ord (addnC m n) j) = (i == j).
Proof. exact: cast_eq. Qed.

Lemma cast_map (T: Type) n m (F : 'I_n -> T) (H : m = n) :
  [seq F i | i <- enum 'I_n] = [seq F ((cast_ord H) i) | i <- enum 'I_m].
Proof. subst m; apply eq_map => i; by rewrite /= cast_erefl. Qed.

Lemma cast_map_cond (T: Type) n m (P : pred 'I_n) (F : 'I_n -> T) (H : m = n) :
  [seq F i | i <- enum 'I_n & P i] =
  [seq F ((cast_ord H) i) | i <- enum 'I_m & P ((cast_ord H) i) ].
Proof.
  subst m; have /eq_filter -> : (fun i : 'I_n => P (cast_ord (erefl n) i)) =1 P
    by move=> i; rewrite /= cast_erefl.
  by have /eq_map -> : (fun i : 'I_n => F (cast_ord (erefl n) i)) =1 F
    by move=> i; rewrite /= cast_erefl.
Qed.

Lemma mem_cast m n (H : m = n) (i : 'I_m) (S : {set 'I_m}) :
  ((cast_ord H) i) \in [set (cast_ord H) i | i in S] = (i \in S).
Proof.
  apply/idP/idP.
  - by move/imsetP => [] j Hin /cast_ord_inj ->.
  - move=> Hin; apply/imsetP; by exists i.
Qed.

Definition cast_set n m (H : n = m) : {set 'I_n} -> {set 'I_m} :=
  [fun s : {set 'I_n} => (cast_ord H) @: s].

Lemma cast_set_inj n m (H : n = m) : injective (cast_set H).
Proof. move=> S1 S2; rewrite /cast_set /=; apply: imset_inj; apply: cast_ord_inj. Qed.

Lemma cover_cast m n (P : {set {set 'I_n}}) (H : n = m) :
  cover (imset (cast_set H) (mem P)) = (cast_set H) (cover P).
Proof.
  rewrite /= cover_imset /cover; apply: esym; apply: big_morph.
  - move=> i j /=; exact: imsetU.
  - exact: imset0.
Qed.

End Casts.

