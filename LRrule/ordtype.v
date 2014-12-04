(******************************************************************************)
(*       Copyright (C) 2014 Florent Hivert <florent.hivert@lri.fr>            *)
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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype choice fintype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Order.

Definition axiom T (r : rel T) := [/\ reflexive r, antisymmetric r, transitive r &
                                   (forall m n : T, (r m n) || (r n m))].

Section ClassDef.

Record mixin_of T := Mixin { r : rel T; x : T; _ : axiom r }.

Record class_of T := Class {base : Countable.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Countable.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Countable.class bT) b => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Countable.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion countType : type >-> Countable.type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Notation ordType := type.
Notation ordMixin := mixin_of.
Notation OrdType T m := (@pack T m _ _ id).
Notation "[ 'ordType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'ordType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ordType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ordType'  'of'  T ]") : form_scope.

End Exports.

End Order.
Export Order.Exports.

Definition leqX_op T := Order.r (Order.mixin (Order.class T)).

Lemma leqXE T x : leqX_op x = Order.r (Order.mixin (Order.class T)) x.
Proof. by []. Qed.

Lemma leqXordP T : Order.axiom (@leqX_op T).
Proof. by case: T => ? [] /= base []. Qed.
Arguments leqXordP [T].

Definition ltnX_op T m n := ((m != n) && (@leqX_op T m n)).

Prenex Implicits leqX_op leqXordP.

(* Declare legacy Arith operators in new scope. *)

Delimit Scope ssr_nat_scope with ssr_nat.

Notation "m <= n" := (le m n) : ssr_nat_scope.
Notation "m < n" := (lt m n) : ssr_nat_scope.
Notation "m >= n" := (ge m n) : ssr_nat_scope.
Notation "m > n" := (gt m n) : ssr_nat_scope.

(* Rebind scope delimiters, reserving a scope for the "recursive",     *)
(* i.e., unprotected version of operators.                             *)

Delimit Scope ord_scope with Ord.
Open Scope ord_scope.

Notation "m <= n" := (leqX_op m n) : ord_scope.
Notation "m < n"  := (ltnX_op m n) : ord_scope.
Notation "m >= n" := (n <= m) (only parsing) : ord_scope.
Notation "m > n"  := (n < m) (only parsing)  : ord_scope.

Notation "m <= n <= p" := ((m <= n) && (n <= p)) : ord_scope.
Notation "m < n <= p" := ((m < n) && (n <= p)) : ord_scope.
Notation "m <= n < p" := ((m <= n) && (n < p)) : ord_scope.
Notation "m < n < p" := ((m < n) && (n < p)) : ord_scope.


Section POrderTheory.

Variable T : ordType.
Implicit Type n m : T.

(* For sorting, etc. *)
Definition leqX := [rel m n | (m:T) <= n].
Definition geqX := [rel m n | (m:T) >= n].
Definition ltnX := [rel m n | (m:T) < n].
Definition gtnX := [rel m n | (m:T) > n].

Lemma leqXnn n : n <= n.
Proof. have:= @leqXordP T; by rewrite /Order.axiom /reflexive => [] [] refl _ _. Qed.
Hint Resolve leqXnn.

Lemma ltnXnn n : n < n = false.
Proof. by rewrite /ltnX_op eq_refl. Qed.

Lemma eq_leqX n m : n = m -> n <= m.
Proof. by move->. Qed.

Lemma ltnX_eqF m n : m < n -> m == n = false.
Proof. by move/andP => [] /negbTE. Qed.

Lemma gtnX_eqF m n : m < n -> n == m = false.
Proof. rewrite [(n == m)]eq_sym. by apply ltnX_eqF. Qed.

Lemma leqX_eqVltnX m n : (m <= n) = (m == n) || (m < n).
Proof. rewrite /ltnX_op; by case eqP => [/= -> | /= _]; first by rewrite (leqXnn n). Qed.

Lemma ltnX_neqAleqX m n : (m < n) = (m != n) && (m <= n).
Proof. by []. Qed.

Lemma anti_leqX : antisymmetric (@leqX_op T).
Proof. have:= @leqXordP T; by rewrite /Order.axiom => [] []. Qed.

Lemma eqn_leqX m n : (m == n) = (m <= n <= m).
Proof.
  apply/(sameP idP); apply(iffP idP).
  - move=> H; have:= anti_leqX; rewrite /antisymmetric => Ha; by rewrite (Ha _ _ H).
  - move/eqP => ->; by rewrite leqXnn.
Qed.

Lemma leqX_trans n m p : m <= n -> n <= p -> m <= p.
Proof.
  have:= @leqXordP T; rewrite /Order.axiom /transitive => [] [] _ _ H _; by apply H.
Qed.

Lemma leqX_ltnX_trans n m p : m <= n -> n < p -> m < p.
Proof.
  move=> H1 /andP [] Hneq H2; rewrite /ltnX_op (leqX_trans H1 H2) andbT.
  move: Hneq; apply contraLR => /=.
  rewrite !negbK [n == p]eqn_leqX => /eqP Heq; rewrite Heq in H1.
  by rewrite H1 H2.
Qed.

Lemma ltnX_leqX_trans n m p : m < n -> n <= p -> m < p.
Proof.
  move=> /andP [] Hneq H1 H2; rewrite /ltnX_op (leqX_trans H1 H2) andbT.
  move: Hneq; apply contraLR => /=.
  rewrite !negbK [m == n]eqn_leqX => /eqP Heq; rewrite Heq; rewrite Heq in H1.
  by rewrite H1 H2.
Qed.

Lemma ltnXW m n : m < n -> m <= n.
Proof. by move/andP => []. Qed.

Lemma ltnX_trans n m p : m < n -> n < p -> m < p.
Proof. move=> lt_mn /ltnXW. exact: ltnX_leqX_trans. Qed.

Lemma geqX_trans : transitive geqX.
Proof. move=> m n p /= H1 H2; by apply (leqX_trans H2 H1). Qed.

Lemma gtnX_trans : transitive gtnX.
Proof. move=> m n p /= H1 H2; by apply (ltnX_trans H2 H1). Qed.

End POrderTheory.


(* Needs total ordering *)
Section OrdTheory.

Variable T : ordType.
Implicit Type n m : T.

Lemma leqX_total m n : (m <= n) || (m >= n).
Proof. have:= @leqXordP T; rewrite /Order.axiom => [] [] _ _ _; by apply. Qed.

Lemma leqXNgtnX n m : (m <= n) = ~~ (n < m).
Proof.
  case (orP (leqX_total m n)) => H.
  - rewrite H negb_and negbK; case (boolP (n <= m)) => //=.
    * by rewrite eqn_leqX H => ->.
    * by rewrite orbT.
  - by rewrite /ltnX_op eqn_leqX H /= negb_and negbK /= orbF.
Qed.

Lemma ltnXNgeqX m n : (m < n) = ~~ (n <= m).
Proof. by rewrite [n <= m]leqXNgtnX negbK. Qed.


(* Comparison predicates. *)

CoInductive leqX_xor_gtnX m n : bool -> bool -> Set :=
  | LeqXNotGtnX of m <= n : leqX_xor_gtnX m n true false
  | GtnXNotLeqX of n < m  : leqX_xor_gtnX m n false true.

Lemma leqXP m n : leqX_xor_gtnX m n (m <= n) (n < m).
Proof.
  by rewrite ltnXNgeqX; case le_mn: (m <= n); constructor; rewrite // ltnXNgeqX le_mn.
Qed.

CoInductive ltnX_xor_geqX m n : bool -> bool -> Set :=
  | LtnXNotGeqX of m < n  : ltnX_xor_geqX m n false true
  | GeqXNotLtnX of n <= m : ltnX_xor_geqX m n true false.

Lemma ltnXP m n : ltnX_xor_geqX m n (n <= m) (m < n).
Proof. by case: leqXP; constructor. Qed.

CoInductive compareX m n : bool -> bool -> bool -> Set :=
  | CompareXLt of m < n : compareX m n true false false
  | CompareXGt of m > n : compareX m n false true false
  | CompareXEq of m = n : compareX m n false false true.

Lemma compareP m n : compareX m n (m < n) (n < m) (m == n).
Proof.
  rewrite {1}/ltnX_op eqn_leqX; case: ltnXP; first by constructor.
  by rewrite leqX_eqVltnX orbC; case: leqXP => /=; constructor; first by apply/eqP.
Qed.

Definition maxX m n := if m < n then n else m.
Definition minX m n := if m < n then m else n.

Lemma maxXC : commutative maxX.
Proof. move=> m n; rewrite /maxX; by case (compareP m n). Qed.

Lemma maxXA : associative maxX.
Proof.
  move=> m n p; rewrite /maxX; case (ltnXP n p) => H1.
  - case (ltnXP m n) => H2; last by case (ltnXP m p).
    by rewrite H1 (ltnX_trans H2 H1).
  - case (ltnXP m n) => H2.
    move: H1; by rewrite ltnXNgeqX => ->.
    have:= leqX_trans H1 H2; by rewrite leqXNgtnX => /negbTE ->.
Qed.

Lemma maxX_idPl {m n} : reflect (maxX m n = m) (m >= n).
Proof.
  apply (iffP idP).
  - by rewrite /maxX leqXNgtnX => /negbTE ->.
  - rewrite /maxX. by case (ltnXP m n); first by move/ltnX_eqF => <- ->.
Qed.

Lemma maxX_idPr {m n} : reflect (maxX m n = n) (m <= n).
Proof. by rewrite maxXC; apply: maxX_idPl. Qed.

Lemma leqX_maxX m n1 n2 : (m <= maxX n1 n2) = (m <= n1) || (m <= n2).
Proof.
without loss le_n21: n1 n2 / n2 <= n1.
  by case/orP: (leqX_total n2 n1) => le_n12; last rewrite maxXC orbC; apply.
*by rewrite (maxX_idPl le_n21) orb_idr // => /leqX_trans->.
Qed.

Lemma ltnX_maxX m n1 n2 : (m < maxX n1 n2) = (m < n1) || (m < n2).
Proof.
without loss le_n21: n1 n2 / n2 <= n1.
  by case/orP: (leqX_total n2 n1) => le_n12; last rewrite maxXC orbC; apply.
by rewrite (maxX_idPl le_n21) orb_idr // => /ltnX_leqX_trans->.
Qed.

Lemma leqX_maxXl m n : m <= maxX m n. Proof. by rewrite leqX_maxX leqXnn. Qed.
Lemma leqX_maxXr m n : n <= maxX m n. Proof. by rewrite maxXC leqX_maxXl. Qed.

Lemma gtnX_maxX m n1 n2 : (m > maxX n1 n2) = (m > n1) && (m > n2).
Proof. by rewrite !ltnXNgeqX leqX_maxX negb_or. Qed.

Lemma geqX_maxX m n1 n2 : (m >= maxX n1 n2) = (m >= n1) && (m >= n2).
Proof. by rewrite leqXNgtnX [n1 <= m]leqXNgtnX [n2 <= m]leqXNgtnX ltnX_maxX negb_or. Qed.

End OrdTheory.

Hint Resolve leqXnn ltnXnn ltnXW.

Lemma inhabitant (T : ordType) : T.
Proof. move H : T => HH; case: HH H => sort [] base [] r x ax t0 HT; by apply x. Qed.

Section Dual.

Variable Alph : ordType.

Fact geqX_order : Order.axiom (geqX Alph).
Proof.
  split.
  - move=> n /=; by apply leqXnn.
  - move=> m n /= /andP [] H1 H2; apply/eqP; by rewrite eqn_leqX H1 H2.
  - move=> m n p /= H1 H2; by apply (leqX_trans H2 H1).
  - move=> m n /=; exact (leqX_total n m).
Qed.

Definition dual_ordMixin := Order.Mixin (inhabitant Alph) geqX_order.
Canonical dual_ordType := Eval hnf in OrdType Alph dual_ordMixin.

Definition to_dual : Alph -> dual_ordType := id.
Definition from_dual : dual_ordType -> Alph := id.

Lemma dual_leqX m n : (to_dual m <= to_dual n) = (n <= m).
Proof. by rewrite leqXE /=. Qed.

Lemma dual_eq m n : (to_dual m == to_dual n) = (n == m).
Proof. by rewrite !eqn_leqX !dual_leqX. Qed.

Lemma dual_ltnX m n : (to_dual m < to_dual n) = (n < m).
Proof. by rewrite /ltnX_op dual_leqX dual_eq. Qed.

Lemma dualK : cancel to_dual from_dual.
Proof. by []. Qed.

Lemma from_dualK : cancel from_dual to_dual.
Proof. by []. Qed.

End Dual.



Section MaxList.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v : word.

Definition maxL l := foldl (@maxX Alph) l.

Lemma maxXb a u : a <= maxL a u.
Proof.
  elim: u a => [//= | u0 u IHu /=] a. apply (@leqX_trans _ (maxX a u0)); last by apply IHu.
  by apply leqX_maxXl.
Qed.

Lemma in_maxL a u : (maxL a u) \in a :: u.
Proof.
  elim: u a => [//= | u0 u IHu /=] a; first by rewrite mem_seq1.
  case (leqXP a u0) => H.
  + have:= H => /maxX_idPr ->; by rewrite in_cons IHu orbT.
  + have:= ltnXW H => /maxX_idPl ->; rewrite !in_cons.
    by rewrite orbA [(_ == _) || (_ == _) ]orbC -orbA -in_cons IHu orbT.
Qed.

Lemma maxXL a b u : maxX a (maxL b u) = maxL (maxX a b) u.
Proof. elim: u b => [//= | u0 u IHu /= b]; rewrite -maxXA; by apply IHu. Qed.

Lemma maxL_cat a u b v : maxL a (u ++ b :: v) = maxX (maxL a u) (maxL b v).
Proof. elim: u a => [/= | u0 u IHu /=] a; first by rewrite maxXL. by apply IHu. Qed.

End MaxList.

Section AllLeqLtn.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v : word.

Definition allLeq v a := all (geqX Alph a) v.
Definition allLtn v a := all (gtnX Alph a) v.

Lemma maxLPt a u : allLeq u (maxL a u).
Proof.
  rewrite/allLeq; apply/allP => x Hx.
  elim: u Hx a => [//= | u0 u IHu /=]; rewrite inE => /orP [/eqP -> | /IHu Hx] a.
  + rewrite maxXC -maxXL; by apply leqX_maxXl.
  + by apply Hx.
Qed.
Lemma maxLP a u : allLeq (a :: u) (maxL a u).
Proof. by rewrite /= (maxLPt a u) (maxXb a u). Qed.

Lemma allLtnW v a : allLtn v a -> allLeq v a.
Proof. move/allP => Hall; apply/allP => x Hx /=. apply ltnXW; by apply Hall. Qed.

Lemma allLeqE u a : allLeq u a -> maxL a u = a.
Proof. by elim: u => [//= | u0 u IHu /=] /andP [] /maxX_idPl -> /IHu. Qed.
Lemma allLeqP u a : reflect (maxL a u = a) (allLeq u a).
Proof.
  apply (iffP idP); first by apply allLeqE.
  rewrite/allLeq; elim: u a => [//= | u0 u IHu /=] a.
  rewrite maxXC -maxXL => Hmax.
  have Hu : maxL a u = a.
    apply/eqP; rewrite eqn_leqX.
    have:= (leqX_maxXr u0 (maxL a u)); rewrite Hmax => -> /=.
    by apply maxXb.
  have:= Hmax; rewrite Hu => /maxX_idPr -> /=.
  by apply IHu.
Qed.

Lemma allLeqCons b u a : b <= a -> allLeq u a -> allLeq (b :: u) a.
Proof.
  move=> Hb /allP Hall; apply /allP => x.
  by rewrite inE => /orP [/eqP -> //=|] /Hall.
Qed.
Lemma allLtnCons b u a : b < a -> allLtn u a -> allLtn (b :: u) a.
Proof.
  move=> Hb /allP Hall; apply /allP => x.
  by rewrite inE => /orP [/eqP -> //=|] /Hall.
Qed.

Lemma allLeqConsE u a b : allLeq (b :: u) a = (maxL b u <= a).
Proof.
  elim: u b => [/= | u0 u IHu /=] b; first by rewrite andbT.
  by rewrite maxXC -maxXL geqX_maxX -IHu /= !andbA [(u0 <= a) && (b <= a)]andbC.
Qed.

Lemma allLtnConsE u a b : allLtn (b :: u) a = (maxL b u < a).
Proof.
  elim: u b => [/= | u0 u IHu /=] b; first by rewrite andbT.
  rewrite maxXC -maxXL gtnX_maxX -IHu /= [RHS]andbA [LHS]andbA.
  congr (_ && _); by rewrite andbC.
Qed.

Lemma allLeq_consK b u a : allLeq (b :: u) a -> allLeq u a.
Proof. move/allP => Hall; apply/allP => x Hx; apply Hall; by rewrite inE Hx orbT. Qed.
Lemma allLtn_consK b u a : allLtn (b :: u) a -> allLtn u a.
Proof. move/allP => Hall; apply/allP => x Hx; apply Hall; by rewrite inE Hx orbT. Qed.

Lemma allLeq_catE u v a : allLeq (u ++ v) a = allLeq u a && allLeq v a.
Proof. by rewrite /allLeq all_cat. Qed.
Lemma allLtn_catE u v a : allLtn (u ++ v) a = allLtn u a && allLtn v a.
Proof. by rewrite /allLtn all_cat. Qed.

(*

Lemma allLeq_cat u v a : allLeq u a -> allLeq v a -> allLeq (u ++ v) a.
Proof. by rewrite /allLeq all_cat => -> ->. Qed.
Lemma allLtn_cat u v a : allLtn u a -> allLtn v a -> allLtn (u ++ v) a.
Proof. by rewrite /allLtn all_cat => -> ->. Qed.

Lemma allLeq_catl u v a : allLeq (u ++ v) a -> allLeq u a.
Proof. by rewrite /allLeq all_cat => /andP []. Qed.
Lemma allLtn_catl u v a : allLtn (u ++ v) a -> allLtn u a.
Proof. by rewrite /allLtn all_cat => /andP []. Qed.

Lemma allLeq_catr u v a : allLeq (u ++ v) a -> allLeq v a.
Proof. by rewrite /allLeq all_cat => /andP []. Qed.
Lemma allLtn_catr u v a : allLtn (u ++ v) a -> allLtn v a.
Proof. by rewrite /allLtn all_cat => /andP []. Qed.
*)

Lemma maxL_perm_eq a u b v : perm_eq (a :: u) (b :: v) -> maxL a u = maxL b v.
Proof.
  move/perm_eqP => Hperm.
  have {Hperm} Hperm : forall x, (x \in (a :: u)) = (x \in (b :: v)).
    move=> x; have {Hperm} Hperm := Hperm (pred_of_simpl (pred1 x)).
    apply/(sameP idP); apply(iffP idP) => /count_memPn.
    + rewrite -Hperm => H; by apply /count_memPn.
    + rewrite  Hperm => H; by apply /count_memPn.
  apply /eqP; rewrite eqn_leqX; apply /andP; split.
  + have:= Hperm (maxL a u); rewrite (in_maxL a u) => /esym Hin.
    have:= maxLP b v => /allP H; by apply H.
  + have:= Hperm (maxL b v); rewrite (in_maxL b v) => Hin.
    have:= maxLP a u => /allP H; by apply H.
Qed.

Lemma perm_eq_allLeq u v a : perm_eq u v -> allLeq u a -> allLeq v a.
Proof.
  move=> Hperm /allLeqP; rewrite (maxL_perm_eq (b := a) (v := v)).
  - by move=> Hall; apply/allLeqP.
  - by rewrite perm_cons.
Qed.
Lemma perm_eq_allLeqE u v a : perm_eq u v -> allLeq u a = allLeq v a.
Proof.
  move=> H; apply/(sameP idP); apply(iffP idP); apply perm_eq_allLeq; last by [].
  by rewrite perm_eq_sym.
Qed.
Lemma perm_eq_allLtn u v a : perm_eq u v -> allLtn u a -> allLtn v a.
Proof.
  move=> Hperm /allP Hall; apply/allP => X Hx.
  apply Hall; by rewrite (perm_eq_mem Hperm).
Qed.
Lemma perm_eq_allLtnE u v a : perm_eq u v -> allLtn u a = allLtn v a.
Proof.
  move=> H; apply/(sameP idP); apply(iffP idP); apply perm_eq_allLtn; last by [].
  by rewrite perm_eq_sym.
Qed.

Lemma perm_rev u : perm_eq u (rev u).
Proof.
  elim: u => [//= | u0 u]; rewrite rev_cons -(perm_cons u0).
  move /perm_eq_trans; apply.
  rewrite perm_eq_sym; apply /perm_eqlP; by apply perm_rcons.
Qed.

Lemma allLeq_rev u a : allLeq (rev u) a = allLeq u a.
Proof. by rewrite (perm_eq_allLeqE _ (perm_rev u)). Qed.
Lemma allLtn_rev u a : allLtn (rev u) a = allLtn u a.
Proof. by rewrite (perm_eq_allLtnE _ (perm_rev u)). Qed.

Lemma allLeq_rconsK b u a : allLeq (rcons u b) a -> allLeq u a.
Proof. rewrite -allLeq_rev rev_rcons => /allLeq_consK; by rewrite allLeq_rev. Qed.
Lemma allLtn_rconsK b u a : allLtn (rcons u b) a -> allLtn u a.
Proof. rewrite -allLtn_rev rev_rcons => /allLtn_consK; by rewrite allLtn_rev. Qed.

Lemma allLeq_last b u a : allLeq (rcons u b) a -> b <= a.
Proof. by rewrite -allLeq_rev rev_rcons /= => /andP []. Qed.
Lemma allLtn_last b u a : allLtn (rcons u b) a -> b < a.
Proof. by rewrite -allLtn_rev rev_rcons /= => /andP []. Qed.


Lemma maxL_LbR a v L b R :
  a :: v = L ++ b :: R -> allLeq L b -> allLeq R b -> maxL a v = b.
Proof.
  rewrite /allLeq /maxL => Heq HL Hr.
  apply /eqP; rewrite eqn_leqX; apply/andP; split.
  + have: all (geqX _ b) (a :: v) by rewrite Heq all_cat HL /= leqXnn Hr.
    move/allP => Hallv; apply Hallv; by apply in_maxL.
  + have:= maxLP a v => /allP; rewrite Heq; apply.
    by rewrite mem_cat inE eq_refl /= orbT.
Qed.

End AllLeqLtn.

Section RemoveBig.

Variable Alph : ordType.
Let word := seq Alph.
Let Z := (inhabitant Alph).

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Fixpoint rembig w := (* Remove the last occurence of the largest letter from w *)
  if w is a :: v then
    if allLtn v a then v else a :: rembig v
  else [::].

Fixpoint posbig w := (* Position of the last occurence of the largest letter of w *)
  if w is a :: v then
    if allLtn v a then 0 else (posbig v).+1
  else 0.

Lemma size_rembig w : size (rembig w) = (size w).-1.
Proof.
  elim: w => [//= | a w IHw] /=.
  case: w IHw => [//= | b w'] IHw.
  case (allLtn (b :: w') a) => //=; by rewrite IHw.
Qed.

Lemma rembig_catR a u b v :
  maxL a u <= maxL b v -> rembig (a :: u ++ b :: v) = a :: u ++ rembig (b :: v).
Proof.
  rewrite /=; elim: u a => [| u0 u IHu] a.
    by rewrite allLtnConsE /= leqXNgtnX /= => /negbTE ->.
  rewrite allLtnConsE maxL_cat /= -maxXL geqX_maxX => /andP [] Ha Hmax.
  rewrite ltnXNgeqX leqX_maxX Ha orbT /=.
  by rewrite -(IHu _ Hmax).
Qed.


Lemma rembig_catL a u b v :
  maxL a u > maxL b v -> rembig (a :: u ++ b :: v) = rembig (a :: u) ++ b :: v.
Proof.
  rewrite /=; elim: u a => [| u0 u IHu] a.
    by rewrite allLtnConsE /= ltnXNgeqX /= => /negbTE ->.
  rewrite allLtn_catE !allLtnConsE /= -maxXL maxXC /maxX.
  case (ltnXP (maxL u0 u) a) => [H -> //= | H Hmax /=].
  by rewrite IHu.
Qed.

Lemma rembig_cat u v :
  rembig (u ++ v) = (rembig u) ++ v \/ rembig (u ++ v) = u ++ (rembig v).
Proof.
  case: u => [/= | a u]; first by right.
  case: v => [/= | b v]; first by rewrite !cats0; left.
  case (leqXP (maxL a u) (maxL b v)) => Hcase.
  + by rewrite (rembig_catR Hcase); right.
  + by rewrite (rembig_catL Hcase); left.
Qed.

Lemma rembig_eq_permL u1 u2 v :
  perm_eq u1 u2 ->
  (rembig (u1 ++ v) = (rembig u1) ++ v /\ rembig (u2 ++ v) = (rembig u2) ++ v) \/
  (rembig (u1 ++ v) = u1 ++ (rembig v) /\ rembig (u2 ++ v) = u2 ++ (rembig v)).
Proof.
  case: u2 => [//= | a2 u2]; first by move/perm_eq_size => /eqP /= /nilP ->; right.
  case: u1 => [//= | a1 u1]; first by move/perm_eq_size.
  case: v => [/= | b v]; first by rewrite /= !cats0; left.
  move/maxL_perm_eq => Heq.
  case (leqXP (maxL a1 u1) (maxL b v)) => H.
  + right; by rewrite (rembig_catR H); rewrite Heq in H; rewrite (rembig_catR H).
  + left;  by rewrite (rembig_catL H); rewrite Heq in H; rewrite (rembig_catL H).
Qed.

Lemma rembig_eq_permR u v1 v2 :
  perm_eq v1 v2 ->
  (rembig (u ++ v1) = (rembig u) ++ v1 /\ rembig (u ++ v2) = (rembig u) ++ v2) \/
  (rembig (u ++ v1) = u ++ (rembig v1) /\ rembig (u ++ v2) = u ++ (rembig v2)).
Proof.
  case: v2 => [//= | b2 v2];
             first by move/perm_eq_size => /eqP /= /nilP ->; left; rewrite !cats0.
  case: v1 => [//= | b1 v1]; first by move/perm_eq_size.
  case: u => [//= | a u]; first by right.
  move/maxL_perm_eq => Heq.
  case (leqXP  (maxL a u) (maxL b1 v1)) => H.
  + right; by rewrite (rembig_catR H); rewrite Heq in H; rewrite (rembig_catR H).
  + left;  by rewrite (rembig_catL H); rewrite Heq in H; rewrite (rembig_catL H).
Qed.

Lemma rembigP w wb : wb != [::] ->
  reflect
    (exists u b v, [/\ w = u ++ v, wb = u ++ b :: v, allLeq u b & allLtn v b])
    ( w == rembig wb).
Proof.
  move=> Hwb; apply (iffP idP).
  - elim: wb Hwb w => [//= | w0 wb IHwb _] w /=.
    case H : (allLtn wb w0) => /eqP -> {w}.
    * exists [::]; exists w0; exists wb; rewrite H !cat0s; by split.
    * have Hwb : wb != [::] by move: H; case wb.
      move Hw : (rembig wb) => w; move: Hw => /eqP; rewrite eq_sym => Hw.
      have:= IHwb Hwb w Hw => [] [] u [] b [] v [] Hcatw Hcatwb Hub Hvb.
      exists (w0 :: u); exists b; exists v; split; last exact Hvb.
      - by rewrite Hcatw.
      - by rewrite Hcatwb.
      - move: H; rewrite Hcatwb /= Hub andbT => /negbT.
        apply contraR. rewrite -ltnXNgeqX => Hb.
        rewrite allLtn_catE /= Hb /=; apply /andP; split.
        + move: Hub => /allP /= Hub; apply/allP => x Hx /=.
          by apply (leqX_ltnX_trans (Hub x Hx)).
        + move: Hvb => /allP /= Hvb; apply/allP => x Hx /=.
          by apply (ltnX_trans (Hvb x Hx)).
  - move=> [] u [] b [] v [] {Hwb}.
    elim: u w wb => [w wb -> -> _ /= -> //=| u0 u IHu].
    move => w wb -> {w} -> {wb} Hleqb Hltnb /=.
    move Hw : (u ++ v) => w; move: Hw => /eqP; rewrite eq_sym => /eqP Hw.
    move Hwb : (u ++ b :: v) => wb; move: Hwb => /eqP; rewrite eq_sym => /eqP Hwb.
    have:= IHu _ _ Hw Hwb (allLeq_consK Hleqb) Hltnb => /eqP ->.
    rewrite allLeqConsE in Hleqb.
    have:= leqX_trans (maxXb u0 u) Hleqb; rewrite {2}Hwb.
    case H : (allLtn (u ++ b :: v) u0) => //=.
    move: H; rewrite allLtn_catE allLtnConsE => /andP [] _.
    move/(leqX_ltnX_trans (maxXb _ _)) => H1 H2.
    have:= ltnX_leqX_trans H1 H2; by rewrite ltnXnn.
Qed.

Lemma perm_eq_nilF (T : eqType) (x : T) (u : seq T) :
  perm_eq [::] (x :: u) = false.
Proof.
  apply/(sameP idP); apply(iffP idP) => //=.
  rewrite /perm_eq => /allP Hperm.
    have /Hperm /= : x \in [::] ++ x :: u by rewrite /= inE eq_refl.
  by rewrite eq_refl /= add1n.
Qed.

Lemma perm_eq_rembig u v :
  perm_eq u v -> perm_eq (rembig u) (rembig v).
Proof.
  case Hu: u => [/= | u0 u']; case Hv: v => [//= | v0 v'].
  + by rewrite perm_eq_nilF.
  + by rewrite perm_eq_sym perm_eq_nilF.
  move=> Hperm; have Hmax:= maxL_perm_eq Hperm; move: Hmax Hperm.

  have:= eq_refl (rembig u); rewrite {2}Hu => /rembigP Htmp.
  have /Htmp {Htmp} : u0 :: u != [::] by [].
  move=> [] u1 [] bu [] u2 []; rewrite {1}Hu => -> Hub Hlequ Hltnu.
  have {Hlequ Hltnu} -> := maxL_LbR Hub Hlequ (allLtnW Hltnu).
  rewrite Hub {u Hu Hub u0 u'}.

  have:= eq_refl (rembig v); rewrite {2}Hv => /rembigP Htmp.
  have /Htmp {Htmp} : v0 :: v != [::] by [].
  move=> [] v1 [] bv [] v2 []; rewrite {1}Hv => -> Hvb Hleqv Hltnv.
  have {Hleqv Hltnv} -> := maxL_LbR Hvb Hleqv (allLtnW Hltnv).
  rewrite Hvb {v Hv Hvb v0 v'}.

  rename bv into mx; move ->.
  rewrite -[mx :: u2]cat1s -[mx :: v2]cat1s -[perm_eq (u1 ++ u2) _](perm_cons mx).
  have Hlemma u v : perm_eq (u ++ [:: mx] ++ v) (mx :: u ++ v).
    rewrite catA -[mx :: u ++ v]/((mx :: u) ++ v) perm_cat2r -[mx :: u]cat1s.
    apply perm_eqlE; by apply perm_catC.
  move=> H; have:= Hlemma u1 u2; rewrite perm_eq_sym.
  move/perm_eq_trans; apply.
  apply (perm_eq_trans H).
  by apply Hlemma.
Qed.

Open Scope nat_scope.

Lemma posbig_size_cons l s : posbig (l :: s) < size (l :: s).
Proof.
  elim H : s l => [//= | s0 s' IHs] l; rewrite -H /=.
  case (allLtn s l) => //=.
  rewrite H ltnS; by apply IHs.
Qed.

Lemma posbig_size s : s != [::] -> posbig s < size s.
Proof. case: s => [//= | s l _]. by apply posbig_size_cons. Qed.

Lemma posbigE u b v :
  (allLeq u b && allLtn v b) = (posbig (u ++ b :: v) == size u).
Proof.
  apply/(sameP idP); apply(iffP idP).
  - elim: u => [/= | u0 u /= IHu]; first by case (allLtn v b).
    case (boolP (allLtn (u ++ b :: v) u0)) => [//= | Hall] /=.
    rewrite eqSS => /IHu {IHu} /andP [] Hub Hvb.
    rewrite Hub Hvb !andbT.
    move: Hall; apply contraR; rewrite -ltnXNgeqX => H.
    rewrite allLtn_catE /= H /=.
    apply/andP; split; apply/allP => x.
    * move: Hub => /allP X/X{X} /= H1; by apply (leqX_ltnX_trans H1 H).
    * move: Hvb => /allP X/X{X} /= H1; by apply (ltnX_trans H1 H).
  - move=> /andP [] Hu Hv.
    elim: u Hu => [| u0 u IHu] /=; first by rewrite Hv.
    move=> /andP [] Hub Hall; rewrite allLtn_catE /= ltnXNgeqX Hub /= andbF eqSS.
    by apply IHu.
Qed.

Lemma posbig_take_dropE l s :
  take (posbig (l :: s)) (rembig (l :: s)) ++
     maxL l s
     :: drop (posbig (l :: s)) (rembig (l :: s)) = l :: s.
Proof.
  elim Hs : s l => [//= | s0 s' IHs] l; rewrite -Hs /=.
  case (boolP (allLtn s l)) => Hl /=.
  + rewrite take0 drop0 /=; by have:= (allLtnW Hl) => /allLeqE ->.
  + move: Hl; rewrite Hs allLtnConsE -leqXNgtnX /= -maxXL => /maxX_idPr ->.
    by rewrite (IHs s0).
Qed.

Lemma nth_posbig l s : nth Z (l :: s) (posbig (l :: s)) = maxL l s.
Proof.
  rewrite /=; case: (boolP (allLtn s l)).
  + by move/allLtnW/allLeqP => ->.
  + elim Hs : s l => [//= | s0 s' IHs] /= l.
    rewrite maxXC /maxX.
    case (ltnXP s0 l) => Hl /= H.
    * rewrite -(IHs l H).
      suff -> : allLtn s' s0 = false by [].
      apply negbTE; move: H; apply contra; apply sub_all => i /= Hi.
      by apply (ltnX_trans Hi).
    * case (boolP (allLtn s' s0)) => /= [|Hs0]; first by move /allLtnW/allLeqP ->.
      by apply (IHs s0 Hs0).
Qed.

Lemma allLeq_posbig l s :
  allLeq (take (posbig (l :: s)) (l :: s)) (maxL l s).
Proof.
  have:= maxLP l s; rewrite -{1}[l :: s](cat_take_drop (posbig (l :: s))).
  by rewrite allLeq_catE => /andP [].
Qed.

Lemma allLtn_posbig l s :
  allLtn (drop (posbig (l :: s)).+1 (l :: s)) (maxL l s).
Proof.
  elim Hs : s l => [//= | s0 s'] IHs l; rewrite -Hs /=.
  have {IHs} := IHs (maxX l s0); rewrite /= maxXC /maxX.
  case: (ltnXP s0 l) => Hs0; rewrite Hs /=.
  - rewrite Hs0 /=; have:= (ltnXW Hs0) => /maxX_idPl ->.
    case (boolP (allLtn s' l)) => Hall.
    + rewrite drop0 /= => ->.
      have /allLeqE -> := allLtnW Hall.
      by rewrite Hs0.
    + suff -> : allLtn s' s0 = false by [].
      apply negbTE; move: Hall; apply contra; apply sub_all => i /= Hi.
      by apply (ltnX_trans Hi).
  - rewrite ltnXNgeqX Hs0 /=.
    by move: Hs0 => /maxX_idPr ->.
Qed.

Lemma rembigE l s :
  take (posbig (l :: s)) (l :: s) ++
       drop (posbig (l :: s)).+1 (l :: s) = rembig (l :: s).
Proof.
  apply/eqP/rembigP; first by [].
  set ss := l :: s; set pos := posbig (l :: s).
  exists (take pos ss).
  exists (nth Z ss pos).
  exists (drop pos.+1 ss).
  split; first by [].
  + set sr := (X in _ ++ X); suff -> : sr = drop pos ss by rewrite cat_take_drop.
    rewrite /sr /ss /pos /= {ss pos sr}.
    elim H : s => [//= | s0 s']; rewrite -H.
    case (boolP (allLtn s l)) => Hmax /=; first by rewrite drop0.
    move: Hmax; rewrite H => Hmax /=.
    case (boolP (allLtn s' s0)) => Hmax0 /=; first by rewrite drop0.
    suff -> : allLtn s' l = false by [].
    apply negbTE; move: Hmax; apply contra => /= Hmax.
    apply allLtnCons; last exact Hmax.
    case: s' Hmax0 Hmax {H} => [//= | s1 s']; rewrite !allLtnConsE.
    rewrite -leqXNgtnX; by apply leqX_ltnX_trans.
  + rewrite /ss /pos {ss pos} nth_posbig; by apply allLeq_posbig.
  + rewrite /ss /pos {ss pos} nth_posbig; by apply allLtn_posbig.
Qed.

Lemma nth_lt_posbig i s : i < posbig s -> nth Z (rembig s) i = nth Z s i.
Proof.
  case H : s => [//= | s0 s'] => Hi.
  rewrite -rembigE -H -{5}[s](cat_take_drop (posbig s)) !nth_cat.
  by rewrite size_take posbig_size H //= Hi.
Qed.

Definition shift_pos    pos i := if i < pos then i else i.+1.
Definition shiftinv_pos pos i := if i < pos then i else i.-1.

Lemma shift_posK pos i : shiftinv_pos pos (shift_pos pos i) = i.
Proof.
  rewrite /shift_pos /shiftinv_pos.
  case (ltnP i pos) => Hi.
  + by rewrite Hi.
  + by rewrite ltnNge (leq_trans Hi (leqnSn _)).
Qed.

Lemma shiftinv_posK pos i : i != pos -> shift_pos pos (shiftinv_pos pos i) = i.
Proof.
  rewrite /shift_pos /shiftinv_pos => Hipos.
  case (ltnP i pos) => Hi.
  + by rewrite Hi.
  + case: i Hipos Hi => [| i] /=.
    - move=> H1 H2; exfalso.
      move: H2; rewrite leqn0 => /eqP H.
      by rewrite H in H1.
    - rewrite ltnNge => H1 H2.
      rewrite eq_sym in H1.
      by rewrite -ltnS ltn_neqAle H1 H2 /=.
Qed.

Lemma nth_rembig s i :
  nth Z s (shift_pos (posbig s) i) = nth Z (rembig s) i.
Proof.
  case Hs : s => [/= | s0 s']; first by rewrite !nth_nil.
  rewrite /shift_pos -rembigE nth_cat -Hs.
  rewrite size_take posbig_size; last by rewrite Hs.
  case (ltnP i (posbig s)) => Hipos.
  + by rewrite nth_take.
  + by rewrite nth_drop addSn subnKC.
Qed.

Lemma bad_if_leq i j : i <= j -> (if i < j then i else j) = i.
Proof. move=> Hi; case (ltnP i j) => //= Hj; apply /eqP; by rewrite eqn_leq Hi Hj. Qed.

Lemma nth_inspos s pos i n :
  pos <= size s ->
  nth Z ((take pos s) ++ n :: (drop pos s)) i =
  if i == pos then n else nth Z s (shiftinv_pos pos i).
Proof.
  move=> Hpos.
  case: (altP (i =P pos)) => [-> {i} | Hipos].
    by rewrite nth_cat size_take (bad_if_leq Hpos) ltnn subnn.
  rewrite /shiftinv_pos nth_cat size_take.
  case (ltnP pos (size s)) => [{Hpos} Hpos | Hpos2].
  - case: (ltnP i pos) => Hi; first by rewrite (nth_take _ Hi).
    have {Hi Hipos} Hi : pos < i by rewrite ltn_neqAle eq_sym Hipos Hi.
    case: i Hi => [//= | i] /=; rewrite ltnS => Hi.
    by rewrite (subSn Hi) /= nth_drop (subnKC Hi).
  - have {Hpos Hpos2} Hpos : pos = size s by apply/eqP; rewrite eqn_leq Hpos Hpos2.
    subst pos.
    case: (ltnP i (size s)) => Hisz; first by rewrite (nth_take _ Hisz).
    have {Hipos Hisz} : size s < i by rewrite ltn_neqAle eq_sym Hisz Hipos.
    case: i => [//= | i] /=; rewrite ltnS => Hi.
    by rewrite (subSn Hi) /= nth_drop (subnKC Hi).
Qed.

Lemma shift_pos_incr pos i j : i <= j -> shift_pos pos i <= shift_pos pos j.
Proof.
  move=> Hij; rewrite /shift_pos; case (ltnP j pos) => Hj.
  - by rewrite (leq_ltn_trans Hij Hj).
  - case (ltnP i pos) => Hi.
    + by apply (leq_trans Hij).
    + by apply (leq_ltn_trans Hij).
Qed.

Lemma shiftinv_pos_incr pos i j : i <= j -> shiftinv_pos pos i <= shiftinv_pos pos j.
Proof.
  move=> Hij; rewrite /shiftinv_pos; case (ltnP j pos) => Hj.
  - by rewrite (leq_ltn_trans Hij Hj).
  - case (ltnP i pos) => Hi.
    + have := (leq_trans Hi Hj); by case j.
    + case: i Hij {Hj Hi} => [//= | i] /=.
      by case: j.
Qed.

End RemoveBig.

Fact leq_order : Order.axiom leq.
Proof.
  split.
  - move=> n; by apply leqnn.
  - exact anti_leq.
  - move=> m n p; by apply leq_trans.
  - exact leq_total.
Qed.

Definition nat_ordMixin := Order.Mixin 0 leq_order.
Canonical nat_ordType := Eval hnf in OrdType nat nat_ordMixin.

Lemma leqXnatE m n : (n <= m)%Ord = (n <= m)%N.
Proof. by rewrite leqXE /=. Qed.

Lemma ltnXnatE m n : (n < m)%Ord = (n < m)%N.
Proof. by rewrite /ltnX_op leqXE ltn_neqAle. Qed.

Lemma maxL_iota n i : maxL i (iota i.+1 n) = i + n.
Proof. elim: n i => [//= | n IHn] /= i. by rewrite /maxX ltnXnatE ltnSn IHn addSnnS. Qed.

Lemma maxL_iota_n n : maxL 0 (iota 1 n) = n.
Proof. by rewrite -{2}[n]add0n maxL_iota. Qed.

Lemma rembig_iota n i : rembig (iota i n.+1) = iota i n.
Proof.
  elim: n i => [//= | n IHn] i.
  have /= -> := (IHn i.+1).
  by rewrite ltnXnatE ltnNge leqnSn /=.
Qed.

Module OrdNotations.

Notation "x <=A y" := (x <= y)%Ord (at level 70, y at next level).
Notation "x >=A y" := (x >= y)%Ord (at level 70, y at next level, only parsing).
Notation "x <A y"  := (x < y)%Ord (at level 70, y at next level).
Notation "x >A y"  := (x > y)%Ord (at level 70, y at next level, only parsing).

(*
Notation "[A m <= n < p ]" := ((m <=A n) && (n <A p)) (at level 71).
Notation "[A m <= n <= p ]" := ((m <=A n) && (n <=A p)) (at level 71).
Notation "[A m < n <= p ]" := ((m <A n) && (n <=A p)) (at level 71).
Notation "[A m < n < p ]" := ((m <A n) && (n <A p)) (at level 71).
*)

End OrdNotations.
