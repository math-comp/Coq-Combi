(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype.
From mathcomp Require Import div tuple bigop ssralg poly polydiv.

Set SsrOldRewriteGoalsOrder.  (* change to Unset and remove the line when requiring MathComp >= 2.6 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section MoreBigop.

Lemma big_morph_in (R1 R2 : Type)
  (f : R2 -> R1) (id1 : R1) (op1 : R1 -> R1 -> R1)
  (id2 : R2) (op2 : R2 -> R2 -> R2) (D : pred R2) :
  (forall x y, x \in D -> y \in D -> op2 x y \in D) ->
  id2 \in D ->
  {in D &, {morph f : x y / op2 x y >-> op1 x y}} ->
  f id2 = id1 ->
  forall  (I : Type) (r : seq I) (P : pred I) (F : I -> R2),
  all D [seq F x | x <- r & P x] ->
  f (\big[op2/id2]_(i <- r | P i) F i) = \big[op1/id1]_(i <- r | P i) f (F i).
Proof.
move=> Dop2 Did2 f_morph f_id I r P F.
elim: r => [|x r ihr /= DrP]; rewrite ?(big_nil, big_cons) //.
set b2 := \big[_/_]_(_ <- _ | _) _; set b1 := \big[_/_]_(_ <- _ | _) _.
have fb2 : f b2 = b1 by rewrite ihr; move: (P x) DrP => [/andP[]|].
case: (boolP (P x)) DrP => //= Px /andP[Dx allD].
rewrite f_morph ?fb2 // /b2 {b2 fb2 ihr b1 x Px Dx f_morph f_id}.
elim: r allD => [|x r ihr /=]; rewrite ?(big_nil, big_cons) //.
by case: (P x) => //= /andP [??]; rewrite Dop2 // ihr.
Qed.

Variables (R : Type) (idx : R).

Fact big_ord_exchange_cond {op : Monoid.law idx} {a b : nat}
   (P : pred nat) (F : nat -> R) :
  \big[op/idx]_(i < a | P i && (i < b)) F i =
  \big[op/idx]_(i < b | P i && (i < a)) F i.
Proof.
wlog le_b_a : a b / b <= a => [hwlog|].
  have /orP [le_a_b|le_b_a] := leq_total a b; last exact: hwlog.
  by symmetry; apply: hwlog.
rewrite big_ord_narrow_cond /=; apply: eq_big => // i.
by rewrite (leq_trans _ le_b_a) ?andbT.
Qed.

Fact big_ord_exchange {op : Monoid.law idx} {a b : nat} (F : nat -> R) :
  \big[op/idx]_(i < a | i < b) F i =
  \big[op/idx]_(i < b | i < a) F i.
Proof. exact: (big_ord_exchange_cond xpredT). Qed.

Fact big_ord1 (op : Monoid.law idx) (F : nat -> R) :
  \big[op/idx]_(i < 1) F i = F 0.
Proof. by rewrite big_ord_recl big_ord0 Monoid.mulm1. Qed.

Lemma big_nat_widen_l (op : Monoid.law idx)
     (m1 m2 n : nat) (P : pred nat) (F : nat -> R) :
   m2 <= m1 ->
   \big[op/idx]_(m1 <= i < n | P i) F i =
   \big[op/idx]_(m2 <= i < n | P i && (m1 <= i)) F i.
Proof.
move=> le_m2m1; have [ltn_m1n|geq_m1n] := ltnP m1 n; last first.
  rewrite big_geq // big_nat_cond big_pred0 // => i.
  by apply/negP => /and3P[/andP [_ /leq_trans]]; rewrite leqNgt => ->.
rewrite [RHS](@big_cat_nat _ _ _ m1) // 1?ltnW //.
rewrite [X in op X]big_nat_cond [X in op X]big_pred0; last first.
  by move=> i; have [] := ltnP i m1; rewrite ?(andbT, andbF).
rewrite Monoid.mul1m [LHS]big_nat_cond [RHS]big_nat_cond.
by apply/eq_bigl => i; have [] := ltnP i m1; rewrite ?(andbT, andbF).
Qed.

Lemma big_mknat  (op : Monoid.law idx)  (a b : nat) (F : nat -> R) :
  \big[op/idx]_(i < b | a <= i) F i = \big[op/idx]_(a <= i < b) F i.
Proof.
rewrite -(big_mkord (fun i => a <= i) F).
by rewrite -(big_nat_widen_l _ _ predT) ?leq0n.
Qed.

End MoreBigop.

Section MoreCoef.

Open Scope ring_scope.

Lemma coefMD_wid (R : nzSemiRingType) (p q : {poly R}) (m n i : nat) :
  i < m -> i < n ->
  (p * q)`_i = \sum_(j1 < m) \sum_(j2 < n | (j1 + j2)%N == i) p`_j1 * q`_j2.
Proof.
move=> m_big n_big; rewrite pair_big_dep.
pose tom := widen_ord m_big; pose ton := widen_ord n_big.
rewrite (reindex (fun j : 'I_i.+1 => (tom j, ton (rev_ord j)))) /=.
  rewrite coefM; apply: eq_big => //= j.
  by rewrite -maxnE (maxn_idPr _) ?eqxx ?leq_ord.
exists (fun k : 'I__ * 'I__ => insubd ord0 k.1) => /=.
  by move=> j _; apply/val_inj; rewrite val_insubd ltn_ord.
move=> [k1 k2] /=; rewrite inE /= {}/ton eq_sym => /eqP i_def.
apply/eqP; rewrite xpair_eqE -!val_eqE /= ?val_insubd i_def !ltnS.
by rewrite leq_addr eqxx /= subSS addKn.
Qed.

Lemma coefMD (R : nzSemiRingType) (p q : {poly R}) (i : nat) :
 (p * q)`_i = \sum_(j1 < size p)
              \sum_(j2 < size q | (j1 + j2)%N == i) p`_j1 * q`_j2.
Proof.
rewrite (@coefMD_wid _ _ _ i.+1 i.+1) //=.
rewrite (bigID (fun j1 :'I__ => j1 < size p)) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  move=> j1; rewrite -ltnNge => j1_big.
  by rewrite big1 // => j2 _; rewrite nth_default ?mul0r.
rewrite (big_ord_exchange
 (fun j1 => \sum_(j2 < i.+1 | (j1 + j2)%N == i) p`_j1 * q`_j2)) /=.
rewrite big_mkcond /=; apply: eq_bigr => j1 _; rewrite ltnS.
have [j1_small|j1_big] := leqP; last first.
  rewrite big1 // => j2; rewrite eq_sym => /eqP i_def.
  by rewrite i_def -ltn_subRL subnn ltn0 in j1_big.
rewrite (bigID (fun j2 :'I__ => j2 < size q)) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  move=> j2; rewrite -ltnNge => /andP[_ j2_big].
  by rewrite [q`__]nth_default ?mulr0.
rewrite (big_ord_exchange_cond
 (fun j2 => (j1 + j2)%N == i) (fun j2 => p`_j1 * q`_j2)) /=.
rewrite big_mkcondr /=; apply: eq_bigr => k; rewrite ltnS.
have [//|j2_big] := leqP; rewrite eq_sym=> /eqP i_def.
by rewrite i_def addnC -ltn_subRL subnn ltn0 in j2_big.
Qed.

End MoreCoef.

Local Open Scope ring_scope.

Section MoreComUnitRingTheory.
Variable (R : comUnitRingType).

Lemma eq_divr (a b c d : R) : b \is a GRing.unit -> d \is a GRing.unit ->
  (a / b == c / d) = (a * d == c * b).
Proof.
move=> b_unit d_unit; pose canM := (can2_eq (mulrVK _) (mulrK _)).
by rewrite canM // mulrAC -canM ?unitrV ?invrK.
Qed.

Lemma mulr_div (x1 y1 x2 y2 : R) :
  (y1 \is a GRing.unit) ->
  (y2 \is a GRing.unit) -> x1 / y1 * (x2 / y2) = x1 * x2 / (y1 * y2).
Proof. by move=> y1_unit y2_unit; rewrite mulrACA -invrM ?[y2 * _]mulrC. Qed.

Lemma addr_div (x1 y1 x2 y2 : R) :
  y1 \is a GRing.unit -> y2 \is a GRing.unit ->
  x1 / y1 + x2 / y2 = (x1 * y2 + x2 * y1) / (y1 * y2).
Proof.
move => y1_unit y2_unit.
by rewrite mulrDl [X in (_ * y1) / X]mulrC -!mulr_div ?divrr // !mulr1.
Qed.

End MoreComUnitRingTheory.

Section MoreFieldTheory.

Variable (K : fieldType).

Lemma eq_divf (a b c d : K) : b != 0 -> d != 0 ->
  (a / b == c / d) = (a * d == c * b).
Proof. by move=> b_neq0 d_neq0; rewrite eq_divr ?unitfE. Qed.

Lemma eq_divfC (a b c d : K) : a != 0 -> c != 0 ->
  (a / b == c / d) = (a * d == c * b).
Proof.
move=> ??; rewrite -invf_div -[c / d]invf_div (inj_eq (can_inj (@invrK _))).
by rewrite eq_divf // eq_sym [a * d]mulrC [b * c]mulrC.
Qed.

Lemma eq_divf_mul (a b c d : K) : a / b != 0 -> a / b = c / d -> a * d = c * b.
Proof.
have [->| d_neq0 ab0 /eqP] := eqVneq d 0.
  by rewrite !invr0 !mulr0 => /negPf ab0 /eqP; rewrite ab0.
rewrite eq_divf //; first by move/eqP.
by apply: contraNneq ab0 => ->; rewrite invr0 mulr0.
Qed.

End MoreFieldTheory.

Local Notation "p ^ f" := (map_poly f p).

Lemma map_poly_injective (R S : nzSemiRingType) (f : {rmorphism R -> S}) :
  injective f -> injective (map_poly f).
Proof.
move=> finj p q /polyP eq_pq; apply/polyP=> i; have := eq_pq i.
rewrite !coef_map; exact: finj.
Qed.

Section AuxiliaryResults.

Variable (R : nzSemiRingType).
Implicit Types (p : {poly R}).

Lemma map_poly_mul (c : R) p : p ^ ( *%R c) = c *: p.
Proof. by apply/polyP => i; rewrite coefZ coef_map_id0 ?mulr0. Qed.

Lemma lead_coefMXn p (n : nat) : lead_coef (p * 'X^n) = lead_coef p.
Proof. by rewrite lead_coef_Mmonic ?monicXn //. Qed.

Lemma size_polyMXn p (n : nat) : p != 0 -> size (p * 'X^n) = (size p + n)%N.
Proof. by move=> ?; rewrite size_Mmonic ?monicXn // size_polyXn addnS. Qed.

Lemma widen_poly (E : nat -> R) (a b : nat) : a <= b ->
  (forall j, a <= j < b -> E j = 0) ->
  \poly_(i < a) E i = \poly_(i < b) E i.
Proof.
move=> leq_a_b E_eq0; apply/polyP => k; rewrite !coef_poly.
have [lt_ka|le_ak] := ltnP k a; first by rewrite (leq_trans lt_ka).
by have [lt_kb|//] := ifPn; rewrite E_eq0 // le_ak lt_kb.
Qed.

End AuxiliaryResults.
