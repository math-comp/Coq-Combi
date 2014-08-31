Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Order.

Definition axiom T (r : rel T) := [/\ reflexive r, antisymmetric r, transitive r &
                                   (forall m n : T, (r m n) || (r n m))].

Section ClassDef.

Record mixin_of T := Mixin { r : rel T; x : T; _ : axiom r }.

Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Equality.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
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
Implicit Arguments leqXordP [T].

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
Notation "m < n"  := ((m != n) && (m <= n)) : ord_scope.
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
Proof. have:= (@leqXordP T); by rewrite /Order.axiom /reflexive => [] [] refl _ _. Qed.
Hint Resolve leqXnn.

Lemma ltnXnn n : n < n = false.
Proof. by rewrite eq_refl. Qed.

Lemma eq_leqX n m : n = m -> n <= m.
Proof. by move->. Qed.

Lemma ltnX_eqF m n : m < n -> m == n = false.
Proof. by move/andP => [] /negbTE. Qed.

Lemma gtnX_eqF m n : m < n -> n == m = false.
Proof. rewrite [(n == m)]eq_sym. by apply ltnX_eqF. Qed.

Lemma leqX_eqVltnX m n : (m <= n) = (m == n) || (m < n).
Proof. by case: (altP (m =P n)) => [/= -> | /= _]; first by rewrite (leqXnn n). Qed.

Lemma ltnX_neqAleqX m n : (m < n) = (m != n) && (m <= n).
Proof. by []. Qed.

Lemma anti_leqX : antisymmetric (@leqX_op T).
Proof. have:= (@leqXordP T); by rewrite /Order.axiom => [] []. Qed.

Lemma eqn_leqX m n : (m == n) = (m <= n <= m).
Proof.
  apply/(sameP idP); apply(iffP idP).
  - move=> H; have:= anti_leqX; rewrite /antisymmetric => Ha; by rewrite (Ha _ _ H).
  - move/eqP => ->; by rewrite leqXnn.
Qed.

Lemma leqX_trans n m p : m <= n -> n <= p -> m <= p.
Proof.
  have:= (@leqXordP T); rewrite /Order.axiom /transitive => [] [] _ _ H _; by apply H.
Qed.

Lemma leqX_ltnX_trans n m p : m <= n -> n < p -> m < p.
Proof.
  move=> H1 /andP [] Hneq H2; rewrite (leqX_trans H1 H2) andbT.
  move: Hneq; apply contraLR => /=.
  rewrite !negbK [n == p]eqn_leqX => /eqP Heq; rewrite Heq in H1.
  by rewrite H1 H2.
Qed.

Lemma ltnX_leqX_trans n m p : m < n -> n <= p -> m < p.
Proof.
  move=> /andP [] Hneq H1 H2; rewrite (leqX_trans H1 H2) andbT.
  move: Hneq; apply contraLR => /=.
  rewrite !negbK [m == n]eqn_leqX => /eqP Heq; rewrite Heq; rewrite Heq in H1.
  by rewrite H1 H2.
Qed.

Lemma ltnXW m n : m < n -> m <= n.
Proof. by move/andP => []. Qed.

Lemma ltnX_trans n m p : m < n -> n < p -> m < p.
Proof. move=> lt_mn /ltnXW. exact: ltnX_leqX_trans. Qed.

End POrderTheory.


(* Needs total ordering *)
Section OrdTheory.

Variable T : ordType.
Implicit Type n m : T.

Lemma leqX_total m n : (m <= n) || (m >= n).
Proof. have:= (@leqXordP T); rewrite /Order.axiom => [] [] _ _ _; by apply. Qed.

Lemma leqXNgtnX n m : (m <= n) = ~~ (n < m).
Proof.
  case: (orP (leqX_total m n)) => H.
  - rewrite H negb_and negbK; case (boolP (n <= m)) => //=.
    * by rewrite eqn_leqX H => ->.
    * by rewrite orbT.
  - by rewrite eqn_leqX H /= negb_and negbK /= orbF.
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
  rewrite eqn_leqX; case: ltnXP; first by constructor.
  by rewrite leqX_eqVltnX orbC; case: leqXP => /=; constructor; first by apply/eqP.
Qed.

Definition maxX m n := if m < n then n else m.
Definition minX m n := if m < n then m else n.

Lemma maxXC : commutative maxX.
Proof.
  move=> m n; rewrite /maxX; case (compareP m n) => //=; first by move /ltnXW ->.
  by rewrite ltnXNgeqX => /negbTE ->.
Qed.

Lemma maxXA : associative maxX.
Proof.
  move=> m n p; rewrite /maxX; case (ltnXP n p) => H1.
  - case (ltnXP m n) => H2; last by case (ltnXP m p).
    by rewrite H1 (ltnX_trans H2 H1).
  - case (ltnXP m n) => H2.
    move: H1; by rewrite ltnXNgeqX => ->.
    have:= (leqX_trans H1 H2); by rewrite leqXNgtnX => /negbTE ->.
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

Section MaxList.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v : word.

Notation maxX := (@maxX Alph).
Notation maxL := (foldl maxX).

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
  + have:= (ltnXW H) => /maxX_idPl ->; rewrite !in_cons.
    by rewrite orbA [(_ == _) || (_ == _) ]orbC -orbA -in_cons IHu orbT.
Qed.

Lemma maxLPt a u : all (geqX _ (maxL a u)) u.
Proof.
  elim: u a => [//= | u0 u IHu /=] a; apply /andP; split; last by apply IHu.
  apply (leqX_trans (leqX_maxXr a u0)); by apply maxXb.
Qed.
Lemma maxLP a u : all (geqX _ (maxL a u)) (a :: u).
Proof. by rewrite /= (maxLPt a u) (maxXb a u). Qed.

Lemma maxXL a b u : maxX a (maxL b u) = maxL (maxX a b) u.
Proof. elim: u b => [//= | u0 u IHu /= b]; rewrite -maxXA; by apply IHu. Qed.

Lemma maxL_cat a u b v : maxL a (u ++ b :: v) = maxX (maxL a u) (maxL b v).
Proof. elim: u a => [/= | u0 u IHu /=] a; first by rewrite maxXL. by apply IHu. Qed.

Definition maxLtn v a :=
  if v is v0 :: v' then (maxL v0 v') < a else true.

Definition maxLeq v a :=
  if v is v0 :: v' then (maxL v0 v') <= a else true.

Lemma maxLeqL u a : maxLeq u a -> maxL a u = a.
Proof. by case: u a => [//= | u0 u /=] a; rewrite -maxXL => /maxX_idPl. Qed.

Lemma maxLtnW v a : maxLtn v a -> maxLeq v a.
Proof. case: v => [//= | v0 v /=]. by apply ltnXW. Qed.

Lemma maxLeq_consK b u a : maxLeq (b :: u) a -> maxLeq u a.
Proof. case: u => //= c u; rewrite -maxXL; apply leqX_trans; by apply leqX_maxXr. Qed.
Lemma maxLtn_consK b u a : maxLtn (b :: u) a -> maxLtn u a.
Proof. case: u => //= c u; rewrite -maxXL; apply leqX_ltnX_trans; by apply leqX_maxXr. Qed.

Lemma maxLeq_catl u v a : maxLeq (u ++ v) a -> maxLeq u a.
Proof.
  case: u => //= u0 u; case: v => [| v0 v]; first by rewrite cats0.
  rewrite maxL_cat; apply leqX_trans; by apply leqX_maxXl.
Qed.
Lemma maxLtn_catl u v a : maxLtn (u ++ v) a -> maxLtn u a.
Proof.
  case: u => //= u0 u; case: v => [| v0 v]; first by rewrite cats0.
  rewrite maxL_cat; apply leqX_ltnX_trans; by apply leqX_maxXl.
Qed.

Lemma maxLeq_catr u v a : maxLeq (u ++ v) a -> maxLeq v a.
Proof.
  case: u => //= u0 u; case: v => [| v0 v]; first by rewrite cats0.
  rewrite maxL_cat; apply leqX_trans; by apply leqX_maxXr.
Qed.
Lemma maxLtn_catr u v a : maxLtn (u ++ v) a -> maxLtn v a.
Proof.
  case: u => //= u0 u; case: v => [| v0 v]; first by rewrite cats0.
  rewrite maxL_cat; apply leqX_ltnX_trans; by apply leqX_maxXr.
Qed.

Lemma maxLeqAllP u a : maxLeq u a = all (geqX _ a) u.
Proof.
  case: u => [//= | u0 u]; rewrite /maxLeq.
  have := maxLP u0 u.
  case: (leqXP (maxL u0 u) a) => H /allP Hall; apply esym.
  + apply/allP => x /Hall /= H1; by apply (leqX_trans H1 H). 
  + apply negbTE; move: H; apply contraL; rewrite -leqXNgtnX => /allP H.
    have Hin := in_maxL u0 u. by apply (H _ Hin).
Qed.
Lemma maxLtnAllP u a : maxLtn u a = all (gtnX _ a) u.
Proof.
  case: u => [//= | u0 u]; rewrite /maxLtn.
  have := maxLP u0 u.
  case: (ltnXP (maxL u0 u) a) => H /allP Hall; apply esym.
  + apply/allP => x /Hall /= H1; by apply (leqX_ltnX_trans H1 H).
  + apply negbTE; move: H; apply contraL; rewrite -ltnXNgeqX => /allP H.
    have Hin := in_maxL u0 u. by apply (H _ Hin).
Qed.

Lemma maxL_perm_eq a u b v : perm_eq (a :: u) (b :: v) -> maxL a u = maxL b v.
Proof.
  move/perm_eqP => Hperm.
  have {Hperm} Hperm : forall x, (x \in (a :: u)) = (x \in (b :: v)).
    move=> x; have {Hperm} Hperm := Hperm (pred_of_simpl (pred1 x)).
    apply/(sameP idP); apply(iffP idP) => /count_memPn.
    + rewrite -Hperm => H; by apply /count_memPn.
    + rewrite  Hperm => H; by apply /count_memPn.
  apply /eqP; rewrite eqn_leqX; apply /andP; split.
  + have := Hperm (maxL a u); rewrite (in_maxL a u) => /esym Hin.
    have := (maxLP b v) => /allP H; by apply H.
  + have := Hperm (maxL b v); rewrite (in_maxL b v) => Hin.
    have := (maxLP a u) => /allP H; by apply H.
Qed.

Lemma perm_eq_maxLeq u v a : perm_eq u v -> maxLeq u a -> maxLeq v a.
Proof.
  case: v => [//=| v0 v]; case: u => [//=| u0 u]; first by move=> /perm_eq_size.
  by move/maxL_perm_eq => /= ->.
Qed.
Lemma perm_eq_maxLtn u v a : perm_eq u v -> maxLtn u a -> maxLtn v a.
Proof.
  case: v => [//=| v0 v]; case: u => [//=| u0 u]; first by move=> /perm_eq_size.
  by move/maxL_perm_eq => /= ->.
Qed.

End MaxList.

Section RemoveBig.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Notation maxX := (@maxX Alph).
Notation maxL := (foldl maxX).

Fixpoint rembig w := (* Remove the last occurence of the largest letter from w *)
  if w is a :: v then
    if maxLtn v a then v else a :: rembig v
  else [::].

Lemma rembig_catR a u b v :
  maxL a u <= maxL b v -> rembig (a :: u ++ b :: v) = a :: u ++ rembig (b :: v).
Proof.
  elim: u a => [| u0 u IHu] /= a; first by rewrite ltnXNgeqX => ->.
  rewrite maxL_cat -maxXL ltnXNgeqX => H.
  rewrite (leqX_trans
             (leqX_trans (leqX_maxXl a (maxL u0 u)) H)
             (leqX_maxXr (maxL u0 u) (maxL b v)) ) /=.
  by have:= (IHu _ (leqX_trans (leqX_maxXr a (maxL u0 u)) H)) => /= ->.
Qed.

Lemma rembig_catL a u b v :
  maxL a u > maxL b v -> rembig (a :: u ++ b :: v) = rembig (a :: u) ++ b :: v.
Proof.
  elim: u a => [/= a -> //= | u0 u IHu] /= a.
  rewrite maxL_cat -maxXL.
  case (ltnXP (maxL u0 u) a) => H.
  + have:= (ltnXW H) => /maxX_idPl ->.
    case (leqXP (maxL u0 u) (maxL b v)) => [/maxX_idPr -> -> //=|].
    move=>  /ltnXW /maxX_idPl ->; by rewrite H.
  + have:= H => /maxX_idPr -> => H1; have:= H1 => /ltnXW/maxX_idPl ->.
    rewrite ltnXNgeqX H /=.
    by have:= (IHu _ H1) => /= ->.
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
    (exists u b v, [/\ w = u ++ v, wb = u ++ b :: v, maxLeq u b & maxLtn v b])
    ( w == rembig wb).
Proof.
  move=> Hwb; apply (iffP idP).
  - elim: wb Hwb w => [//= | w0 wb IHwb _] w /=.
    case H : (maxLtn wb w0) => /eqP -> {w}.
    * exists [::]; exists w0; exists wb; rewrite H !cat0s; by split.
    * have Hwb : wb != [::] by move: H; case wb.
      move Hw : (rembig wb) => w; move: Hw => /eqP; rewrite eq_sym => Hw.
      have:= (IHwb Hwb w Hw) => [] [] u [] b [] v [] Hcatw Hcatwb Hub Hvb.
      exists (w0 :: u); exists b; exists v; split; last exact Hvb.
      - by rewrite Hcatw.
      - by rewrite Hcatwb.
      - move: H; rewrite Hcatwb /maxLtn /maxLeq.
        move: Hub; case u => [/= | u0 u' /=] Hub /negbT;
          apply contraR; rewrite -ltnXNgeqX; first by rewrite (maxLeqL (maxLtnW Hvb)).
        rewrite maxL_cat (maxLeqL (maxLtnW Hvb)) -maxXL => Hu.
        rewrite maxXC {1 3}/maxX; have:= Hub; rewrite leqXNgtnX => /negbTE ->.
        move: Hub Hu; rewrite {2 4}/maxX. case (ltnXP w0 (maxL u0 u')) => //=.
        move=> _ /leqX_ltnX_trans H/H{H}; by rewrite ltnXnn.
  - move=> [] u [] b [] v [] {Hwb}.
    elim: u w wb => [w wb -> -> _ /= -> //=| u0 u IHu].
    move => w wb -> {w} -> {wb} /= Hleqb Hltnb /=.
    move Hw : (u ++ v) => w; move: Hw => /eqP; rewrite eq_sym => /eqP Hw.
    move Hwb : (u ++ b :: v) => wb; move: Hwb => /eqP; rewrite eq_sym => /eqP Hwb.
    have:= (IHu _ _ Hw Hwb (maxLeq_consK Hleqb) Hltnb) => /eqP ->.
    have:= leqX_trans (maxXb u0 u) Hleqb; rewrite {2}Hwb.
    case H : (maxLtn (u ++ b :: v) u0) => //=.
    move: H => /maxLtn_catr; rewrite /maxLtn.
    move/(leqX_ltnX_trans (maxXb _ _)) => H1 H2.
    have:= (ltnX_leqX_trans H1 H2); by rewrite ltnXnn.
Qed.

End RemoveBig.

Lemma inhabitant (T : ordType) : T.
Proof. move H : T => HH; case: HH H => sort [] base [] r x ax t0 HT; by apply x. Qed.

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
Proof. by rewrite leqXE ltn_neqAle. Qed.
