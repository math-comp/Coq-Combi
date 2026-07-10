(** * Combi.tfps : Truncated power series, i.e. polynom mod X^n *)
(******************************************************************************)
(*    Copyright (C) 2019-2026 Florent Hivert <florent.hivert@lisn.fr>         *)
(*                                                                            *)
(*    This program is free software; you can redistribute it and/or           *)
(*    modify it under the terms of the GNU Lesser General Public              *)
(*    License as published by the Free Software Foundation; either            *)
(*    version 3 of the License, or (at your option) any later version.        *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*    The full text of the LGPL is available at:                              *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
(** #
<script src="https://polyfill.io/v3/polyfill.min.js?features=es6"></script>
<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
 # *)
(** * Truncated power series, i.e. polynomials modulo X^n

This is heavily inspired from

https://github.com/Barbichu/newtonsums

In this file, we suppose that \(\mathbf{R}\) is a ring and \(n\) is a positive
integer.  The goal of this file is to construct the ring
#\(\mathbf{R}[X]/X^n\)#.

We define the following notions (where [R : ringType] and [n : nat]):

 - [{tfps R n}] == the truncated power series ring with coefficient in [R] and
                  order of truncation [n] (which is included). So the series
                  are computed modulo \(X^{n+1}\).

The base ring [R] needs to be at least a [ringType], but [{tfps R n}] aquire
more structure if [R] has more: namely [{tfps R n}] is a [unitRing] if [R] is
as well. [{tfps R n}] is commutative if [R] is.

Basic formulary:

- [\X]         == the series \(X\) in [{tfps R n}] where n is inferred.
- [\Xo(n)]     == the series \(X\) in [{tfps R n}].
- [expt n]     == the truncated exponential series in [{tfps R n}].
- [logt n]     == the truncated logarithm \(-\log(1 - X)\) series in
                  [{tfps R n}].
- [exp f]      == the truncated series \(\exp(f)\).
- [log g]      == the truncated series \(\log(f)\).
- [f ^^ r]     == [expr_tfps r f] == the truncated series \(\exp(r\log(f))\).
- [\sqrt f]    == the truncated square root series of [f].

Construction of power series:

- [x %:S] == [tfpsC r] == the constant power series.
- [[tfps s <= n => F]] == the power series #\(\sum_{i=0}^n F(i) X^i\)#.
- [[tfps s => F]] == the power series #\(\sum_{i=0}^n F(i) X^i\)# where [n]
                  is inferred from the context.
- [trXn p]     == the polynomial [p] truncated at order [n] where [n]
                  is inferred from the context.
- [trXnt n f]  == the power series [f] truncated at order [n].
- [MkTfps Pf]  == the truncated power series associated to the polynomial
                  [f] where [Pf] is a proof that [size f <= n.+1].

Dealing with coefficients of power series:

- [f`_i]       == the [i]-th coefficient #\([X^i]f\)# of [f] (reused from
                  polynomial thanks to the coercion [{tfps R n} >-> {poly R}].
- [map_tfps F f]  == the power series obtained by applying [F] to all the
                  coefficient of [f] where [F : R -> S] is a ring morphism.
- [convr_tfps f]  == [f] converted to the opposite ring [R^c]
- [iconvr_tfps f] == [f] converted from the opposite ring [R^c]

- [f \in coeft0_eq0] == the ideal of [f] such that #\([X^0]f = 0\)# that is
                    [f`_0 == 0].
- [f \in coeft0_eq1] == the ideal of [f] such that #\([X^0]f = 1\)# that is
                    [f`_0 == 1].

Standard operation on power series:

- [tmulX f] == the series \(X\,f\) in [{tfps R n.+1}].
- [tdivX f] == the series #\( (f - [X^0]f)/X \)# in [{tfps R n.-1}].

- [f^`()]   == [deriv_tfps f] (in [tfps_scope]) the derivative of [f] in the
                  ring [{tfps R n.-1}].
- [prim p]  == the primitive [p] in the ring [{poly R}].
- [\int p]  == [prim_tfps p] (in [tfps_scope]) the primitive [p] in the ring
                  [{tfps R n.+1}].

Composition of truncated power series and Lagrange inversion:

- [comp_tfps f g] == [g \oT f] (in [tfps_scope]) == the compose series of [f]
                  and [g] where [f \in coeft0_eq0].
- [lagrfix g]  == the Lagrange fix point [f] in [{tfps R n.+1}] of the iteration
                  \(f \to X\,(g \circ f)\) or more precisely
                  [f => tmulX (g \oT trXnt n f)].

- [lagrunit f] == [f] is inversible for the composition of series, that is
                  [`f_0` == 0] and [tdivX f] in a multiplicative unit.
- [lagrinv f]  == the inverse of [f] the for composition of series. It is
                  given and the Lagrange fixpoint of [(tdivX f)^-1].

Note: we cannot declare the group [(coeft0_eq0, \oT, lagrinv)] because it
is infinite, and MathComp currently formalize only finite groups.

We prove the [Lagrange_Bürmann] theorem giving the coefficent of the Lagrange
fixpoint and its compose series.
*******************************************************************************)
From Corelib Require Import Setoid.
From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import ssralg poly polydiv ring_quotient.
Require Import auxresults.

Set SsrOldRewriteGoalsOrder.  (* change to Unset and remove the line when requiring MathComp >= 2.6 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Declare Scope tfps_scope.
Delimit Scope tfps_scope with tfps.

Reserved Notation "{ 'tfps' R n }"
         (at level 0, R, n at level 2, format "{ 'tfps'  R  n }").
Reserved Notation "[ 'tfps' s <= n => F ]"
  (at level 0, n at next level, s name, format "[ 'tfps' s <= n  =>  F ]").
Reserved Notation "[ 'tfps' s => F ]"
  (at level 0, s name, format "[ 'tfps'  s  =>  F ]").
Reserved Notation "c %:S" (at level 1, format "c %:S").
Reserved Notation "\X" (at level 0).
Reserved Notation "\Xo( n )" (at level 0).
Reserved Notation "x ^^ n" (at level 29, left associativity).
Reserved Notation "f \oT g" (at level 50).
Reserved Notation "\sqrt f" (at level 10).
Reserved Notation "\int f" (at level 10).


Section MoreBigop.

Local Open Scope nat_scope.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).

Lemma index_translation (m j : nat) (F : nat -> R) :
  \big[op/idx]_(i < m - j) F i =
  \big[op/idx]_(k < m | j <= k) F (k - j).
Proof.
rewrite -(big_mkord predT F) -(big_geq_mkord j m predT (fun i => F (i - j))) /=.
rewrite -{2}[j]add0n big_addn.
by apply: eq_bigr => i _ ; rewrite addnK.
Qed.

Lemma aux_triangular_index_bigop (m : nat) (F : nat -> nat -> R) :
  \big[op/idx]_(i < m) \big[op/idx]_(j < m | i + j < m) F i j =
  \big[op/idx]_(k < m) \big[op/idx]_(l < k.+1) F l (k - l).
Proof.
evar (G : 'I_m -> R); rewrite [LHS](eq_bigr G) => [| i _] ; last first.
- rewrite (eq_bigl (fun j : 'I_m => j < m - i)) => [| j /=].
  + rewrite big_ord_narrow => [| _ /=] ; first exact: leq_subr.
    by rewrite index_translation /G.
  + by rewrite ltn_subRL.
- rewrite /G (exchange_big_dep xpredT) //.
  apply: eq_big => [// | i _].
  rewrite (eq_bigl (fun i0 : 'I_m => i0 < i.+1)) => [| j] ; last first.
  + by rewrite -ltnS.
  + by rewrite big_ord_narrow.
Qed.

Lemma triangular_index_bigop (m n : nat) (F : nat -> nat -> R) :
  n <= m ->
  \big[op/idx]_(i < m) \big[op/idx]_(j < m | i + j < n) F i j =
  \big[op/idx]_(k < n) \big[op/idx]_(l < k.+1) F l (k - l).
Proof.
move => leq_nm.
rewrite -(subnKC leq_nm) big_split_ord /=.
rewrite [X in op _ X]big1 => [| /= i _]; first last.
  apply: big_pred0 => x; apply negbTE.
  by rewrite -leqNgt -addnA leq_addr.
rewrite Monoid.simpm /= -aux_triangular_index_bigop.
apply: eq_bigr => i _ ; rewrite subnKC //.
rewrite (eq_bigl (fun j : 'I_m => (i + j < n) && (j < n))).
  by rewrite big_ord_narrow_cond.
move=> j; apply/esym/andb_idr/contraLR.
rewrite -!leqNgt => leq_nj.
exact: (leq_trans leq_nj (leq_addl _ _)).
Qed.

End MoreBigop.


Section MorePolyTheory.

Variable R : nzSemiRingType.
Implicit Type p q : {poly R}.

Lemma poly_cat p n :
  Poly (take n p) + 'X^n * Poly (drop n p) = p.
Proof.
apply/polyP => i; rewrite coefD coefXnM !coef_Poly; case: ltnP => Hi.
  by rewrite nth_take // addr0.
rewrite nth_drop subnKC // [(take _ _)`_i]nth_default ?add0r //.
by rewrite size_take -/(minn _ _) (leq_trans (geq_minl _ _) Hi).
Qed.

Fact coef0M p q : (p * q)`_0 = p`_0 * q`_0.
Proof. by rewrite coefM big_ord_recl big_ord0 addr0. Qed.

Lemma leq_size_deriv (p : {poly R}) : (size p^`() <= (size p).-1)%N.
Proof.
have [-> | pN0] := eqVneq p 0; first by rewrite deriv0 size_poly0.
by rewrite -ltnS prednK // ?lt_size_deriv // size_poly_gt0.
Qed.

Lemma p_neq0 (p : {poly R}): (exists (x : R), p.[x] != 0) -> p != 0.
Proof.
by move=> [x px_neq0]; move: px_neq0; apply: contra => /eqP ->; rewrite horner0.
Qed.

Variable (K : idomainType).

Lemma polyXP (p : {poly K}) : reflect (p`_0 = 0) ('X %| p).
Proof. by rewrite -['X]subr0 -polyC0 -horner_coef0; apply: polyXsubCP. Qed.

Lemma coef0_eq_coef0 (p q : {poly K}) :
  p %= q -> (p`_0 == 0) = (q`_0 == 0).
Proof.
move/eqp_dvdr=> p_eqp_q.
by apply/eqP/eqP => /polyXP; [rewrite p_eqp_q | rewrite -p_eqp_q] => /polyXP.
Qed.

Hypothesis char_K_is_zero : [pchar K] =i pred0.

Lemma size_deriv (p : {poly K}) : size (p^`()%R) = (size p).-1.
Proof.
have [/size1_polyC -> | le_sp_1] := ltnP (size p) 2.
  by rewrite derivC size_poly0 size_polyC; case: eqP.
rewrite size_poly_eq // !prednK ; last by case: (size p) le_sp_1.
rewrite -mulr_natr mulf_eq0 ; apply/norP ; split.
  by rewrite -lead_coefE lead_coef_eq0 -size_poly_gt0 (ltn_trans _ le_sp_1).
move/(pcharf0P K) : char_K_is_zero => ->; rewrite -lt0n.
by case: (size p) le_sp_1.
Qed.

Lemma deriv_eq0 (p : {poly K}) : p^`() = 0 -> {c : K | p = c %:P}.
Proof.
move/eqP ; rewrite -size_poly_eq0 size_deriv => /eqP H_size_p.
exists p`_0 ; apply: size1_polyC.
by rewrite (leq_trans (leqSpred _)) // H_size_p.
Qed.

End MorePolyTheory.


Section TruncFPSDef.

Variable R : nzSemiRingType.
Variable n : nat.

Implicit Types (p q r s : {poly R}).

Record truncfps := MkTfps { tfps : {poly R}; _ : size tfps <= n.+1 }.

HB.instance Definition _ := [isSub for tfps].
HB.instance Definition _ := [Choice of truncfps by <:].

Lemma tfps_inj : injective tfps. Proof. exact: val_inj. Qed.

Fact poly_of_tfps_key : unit. Proof. by []. Qed.
Definition poly_of_tfps : truncfps -> {poly R} :=
  locked_with poly_of_tfps_key tfps.
Canonical poly_of_tfps_unlockable :=
  Eval hnf in [unlockable fun poly_of_tfps].

Lemma tfpsE : tfps =1 poly_of_tfps.
Proof. by case=> p Hp; rewrite unlock. Qed.

Coercion seq_of_tfps (f : truncfps) : seq R := @tfps f.

Lemma size_tfps (f : truncfps) : size f <= n.+1.
Proof. by case: f. Qed.

Definition coeftfps i (p : truncfps) := p`_i.

End TruncFPSDef.

(* We need to break off the section here to let the Bind Scope directives     *)
(* take effect.                                                               *)
Bind Scope tfps_scope with truncfps.
Arguments tfps {R n%_N}.
Arguments tfps_inj {R} [p1%_R p2%_R] : rename.
Notation "{ 'tfps' R n }" :=  (truncfps R n).
Arguments coeftfps /.

#[export]
Hint Resolve size_tfps : core.


Section CoefTFPS.

Variable R : nzSemiRingType.
Variable n : nat.

Implicit Types (p q r s : {poly R}) (f g : {tfps R n}).

Lemma size_tfpsE f : size f = size (tfps f).
Proof. by []. Qed.

Lemma coef_tfpsE f i : f`_i = (tfps f)`_i.
Proof. by []. Qed.

Lemma coef_tfps f i : f`_i = if i <= n then f`_i else 0.
Proof.
case: (leqP i n) => Hi //.
by rewrite nth_default // (leq_trans (size_tfps _) Hi).
Qed.

Lemma tfpsP f g : (forall i, i <= n -> f`_i = g`_i) <-> (f = g).
Proof.
split => [H | H i Hi].
- apply/tfps_inj/polyP => i; rewrite [LHS]coef_tfps [RHS]coef_tfps.
  by case: leqP => //; apply: H.
- move: H => /(congr1 tfps)/(congr1 (fun r => r`_i)).
  by rewrite coef_tfps Hi.
Qed.


Fact trXn_subproof p : size (Poly (take n.+1 p)) <= n.+1.
Proof. by apply: (leq_trans (size_Poly _)); rewrite size_take geq_minl. Qed.
Definition trXn_def p := MkTfps (trXn_subproof p).
Fact trXn_key : unit. Proof. by []. Qed.
Definition trXn := locked_with trXn_key trXn_def.
Canonical trXn_unlockable := Eval hnf in [unlockable fun trXn].

Definition tfpsC_def c := trXn (c %:P).
Fact tfpsC_key : unit. Proof. by []. Qed.
Definition tfpsC := locked_with tfpsC_key tfpsC_def.
Canonical tfpsC_unlockable := Eval hnf in [unlockable fun tfpsC].

Definition tfps_of_fun (f : nat -> R) := MkTfps (size_poly n.+1 f).

Lemma trXnE p : tfps (trXn p) = Poly (take n.+1 p) :> {poly R}.
Proof. by rewrite unlock. Qed.

Lemma coef_trXn p i : (trXn p)`_i = if i <= n then p`_i else 0.
Proof.
rewrite coef_tfpsE trXnE coef_Poly.
case: leqP => Hi; first by rewrite nth_take.
by rewrite nth_default // size_take -/(minn _ _) (leq_trans (geq_minl _ _)).
Qed.

Lemma trXnP p q : (forall i, i <= n -> p`_i = q`_i) <-> (trXn p = trXn q).
Proof.
rewrite -tfpsP; split => eq_pq i le_in.
- by rewrite !coef_trXn le_in; apply eq_pq.
- by have := eq_pq i le_in; rewrite !coef_trXn le_in.
Qed.

Lemma trXnK p : size p <= n.+1 -> tfps (trXn p) = p.
Proof.
move=> le_szn; apply polyP => i.
rewrite -coef_tfpsE coef_trXn; case: leqP => // /(leq_trans le_szn) leq_szi.
by rewrite nth_default.
Qed.

Lemma coef0_trXn (p : {poly R}) : (trXn p)`_0 = p`_0.
Proof. by rewrite coef_trXn leq0n. Qed.


Lemma tfpsCE c : tfpsC c = trXn c%:P.
Proof. by rewrite unlock. Qed.

Lemma coeftC c i : (tfpsC c)`_i = if i == 0%N then c else 0.
Proof.
by rewrite tfpsCE coef_trXn coefC; case: i => //= i; rewrite if_same.
Qed.

Lemma val_tfpsC (c : R) : tfps (tfpsC c) = c %:P.
Proof. by apply/polyP => i /=; rewrite coeftC coefC. Qed.

Lemma tfpsCK : cancel tfpsC (coeftfps 0).
Proof. by move=> c; rewrite [coeftfps 0 _]coeftC. Qed.
Lemma tfpsC_inj : injective tfpsC.
Proof. exact: can_inj tfpsCK. Qed.


Lemma coef_tfps_of_fun (f : nat -> R) i :
  (tfps_of_fun f)`_i = if i <= n then f i else 0.
Proof. by rewrite /tfps_of_fun coef_poly ltnS. Qed.

Lemma tfpsK : cancel (@tfps R n) trXn.
Proof. by move=> f; apply/tfpsP => i le_in; rewrite coef_trXn le_in. Qed.
HB.instance Definition _ := isQuotient.Build {poly R} {tfps R n} tfpsK.

Lemma poly_trXn_quotP p q :
  reflect
    (forall i, (i <= n)%N -> p`_i = q`_i)
    (p == q %[mod {tfps R n}])%qT.
Proof. by rewrite !unlock; apply (iffP eqP); rewrite trXnP. Qed.


End CoefTFPS.

Local Open Scope tfps_scope.

Notation "[ 'tfps' s <= n => F ]" :=
  (tfps_of_fun n (fun s => F)) (only parsing) : tfps_scope.
Notation "[ 'tfps' s => F ]" := [tfps s <= _ => F] : tfps_scope.
Notation "c %:S" := (tfpsC _ c) : tfps_scope.
Notation "\X" := (trXn _ 'X) : tfps_scope.
Notation "\Xo( n )" := (trXn n 'X) (only parsing): tfps_scope.


Section TFPSSemiRingTheory.

Variable (R : nzSemiRingType).
Implicit Types (p q r s : {poly R}).

Fact trXnC n a : tfps (trXn n a%:P) = a%:P :> {poly R}.
Proof.
apply/polyP => i; rewrite coef_trXn coefC.
by case: eqP => [->|_] //; rewrite if_same.
Qed.

Fact trXn_trXn p m n : m <= n -> trXn m (tfps (trXn n p)) = trXn m p.
Proof.
move=> le_mn; apply/trXnP => i le_im.
by rewrite coef_trXn (leq_trans le_im le_mn).
Qed.

Variable (n : nat).

Lemma trXnCE m a : trXn n (tfps (a%:S : {tfps R m})) = a%:S.
Proof. by apply tfps_inj; rewrite val_tfpsC !tfpsCE. Qed.

Lemma trXn_mull p q : trXn n (tfps (trXn n p) * q) = trXn n (p * q).
Proof.
apply/trXnP => i le_in /=; rewrite !coefM.
apply eq_bigr => [] [j] /=; rewrite ltnS => le_ji _.
by rewrite coef_trXn (leq_trans le_ji le_in).
Qed.

Lemma trXn_mulr p q : trXn n (p * tfps (trXn n q)) = trXn n (p * q).
Proof.
apply/trXnP => i le_in /=; rewrite !coefM.
apply eq_bigr => [] [j] /=; rewrite ltnS => le_ji _.
by rewrite coef_trXn (leq_trans (leq_subr _ _) le_in).
Qed.

Lemma trXn_mul p q :
  trXn n (tfps (trXn n p) * tfps (trXn n q)) = trXn n (p * q).
Proof. by rewrite trXn_mulr trXn_mull. Qed.

(* nmodType structure *)

Implicit Types (f g : {tfps R n }).

Fact zero_tfps_subproof : size (0 : {poly R}) <= n.+1.
Proof. by rewrite size_poly0. Qed.
Definition zero_tfps := MkTfps zero_tfps_subproof.

Fact add_tfps_subproof f g :
  size (tfps f + tfps g) <= n.+1.
Proof. by rewrite (leq_trans (size_polyD _ _)) // geq_max !size_tfps. Qed.
Definition add_tfps f g := MkTfps (add_tfps_subproof f g).


Fact add_tfpsA : associative add_tfps.
Proof. by move => f1 f2 f3; apply/tfps_inj/addrA. Qed.
Fact add_tfpsC : commutative add_tfps.
Proof. by move => f1 f2; apply/tfps_inj/addrC. Qed.
Fact add_0tfps : left_id zero_tfps add_tfps.
Proof. by move => f; apply/tfps_inj/add0r. Qed.
HB.instance Definition _ :=
    GRing.isNmodule.Build {tfps R n} add_tfpsA add_tfpsC add_0tfps.

Fact trXn_is_nmod_morphism : nmod_morphism (trXn n).
Proof.
split => [| f g]; apply/tfpsP => i Hi.
  by rewrite coef0 !coef_trXn coef0 Hi.
by rewrite coefD !coef_trXn coefD Hi.
Qed.
HB.instance Definition _ :=
  GRing.isNmodMorphism.Build {poly R} {tfps R n} (trXn n) trXn_is_nmod_morphism.

Lemma coeft0 i : (0 : {tfps R n})`_i = 0.
Proof. by rewrite coef0. Qed.

Lemma trXn0 : trXn n 0 = 0.
Proof. exact: raddf0. Qed.

Fact tfps_is_nmod_morphism : nmod_morphism (tfps : {tfps R n} -> {poly R}).
Proof. by []. Qed.
HB.instance Definition _ :=
  GRing.isNmodMorphism.Build {tfps R n} {poly R} _ tfps_is_nmod_morphism.

Fact tfpsC_is_nmod_morphism : nmod_morphism (@tfpsC R n : R -> {tfps R n}).
Proof.
split => [| c1 c2]; apply tfps_inj.
  by rewrite !val_tfpsC.
by rewrite !val_tfpsC !raddfD /= !val_tfpsC.
Qed.
HB.instance Definition _ :=
  GRing.isNmodMorphism.Build R {tfps R n} _ tfpsC_is_nmod_morphism.

Lemma tfpsC0 : (0%:S : {tfps R n}) = 0.
Proof. exact: raddf0. Qed.
Lemma tfpsCB : {morph (@tfpsC R n) : a b / a + b}.
Proof. exact: raddfD. Qed.
Lemma tfpsC_sum I (r : seq I) (s : pred I) (F : I -> R) :
  (\sum_(i <- r | s i) F i)%:S = \sum_(i <- r | s i) (F i)%:S.
Proof. exact: raddf_sum. Qed.

Lemma tfpsCMn m : {morph (@tfpsC R n) : c / c *+ m}.
Proof. exact: raddfMn. Qed.

Lemma tfpsC_eq0 (c : R) : (c%:S == 0 :> {tfps R n}) = (c == 0).
Proof. by rewrite -tfpsC0; apply/inj_eq/tfpsC_inj. Qed.



(* semiRingType structure *)
Fact one_tfps_proof : size (1 : {poly R}) <= n.+1.
Proof. by rewrite size_polyC (leq_trans (leq_b1 _)). Qed.
Definition one_tfps : {tfps R n} := MkTfps one_tfps_proof.

Definition mul_tfps f g := trXn n (tfps f * tfps g).
Definition hmul_tfps f g := [tfps j <= n => f`_j * g`_j].
Local Notation "f *h g" := (hmul_tfps f g) (at level 2).

Lemma hmul_tfpsA : associative hmul_tfps.
Proof.
by move=> f1 f2 f3; apply/tfpsP => i Hi; rewrite !coef_poly ltnS Hi mulrA.
Qed.

Lemma hmul_tfps0r f : 0 *h f = 0.
Proof. by apply/tfpsP => i Hi; rewrite coef_poly coef0 mul0r if_same. Qed.

Lemma hmul_tfpsr0 f : f *h 0 = 0.
Proof. by apply/tfpsP => i Hi; rewrite coef_poly coef0 mulr0 if_same. Qed.

Fact mul_tfpsA : associative mul_tfps.
Proof. by move=> f1 f2 f3; rewrite /mul_tfps trXn_mulr trXn_mull mulrA. Qed.
Fact mul_1tfps : left_id one_tfps mul_tfps.
Proof. by move=> p; rewrite /mul_tfps mul1r tfpsK. Qed.
Fact mul_tfps1 : right_id one_tfps mul_tfps.
Proof. by move=> p; rewrite /mul_tfps mulr1 tfpsK. Qed.
Fact mul_tfpsDl : left_distributive mul_tfps +%R.
Proof. by move=> f1 f2 f3; rewrite /mul_tfps mulrDl raddfD. Qed.
Fact mul_tfpsDr : right_distributive mul_tfps +%R.
Proof. by move=> f1 f2 f3; rewrite /mul_tfps mulrDr raddfD. Qed.
Fact mul_0tfps : left_zero 0 mul_tfps.
Proof. by move=> f; rewrite /mul_tfps -trXn_mul trXn0 raddf0 mul0r trXn0. Qed.
Fact mul_tfps0 : right_zero 0 mul_tfps.
Proof. by move=> f; rewrite /mul_tfps -trXn_mul trXn0 raddf0 mulr0 trXn0. Qed.
Fact one_tfps_neq0 : one_tfps != 0.
Proof. by rewrite -val_eqE oner_neq0. Qed.

HB.instance Definition _ := GRing.Nmodule_isNzSemiRing.Build {tfps R n}
  mul_tfpsA mul_1tfps mul_tfps1 mul_tfpsDl mul_tfpsDr
  mul_0tfps mul_tfps0 one_tfps_neq0.

Lemma coeft1 i : (1 : {tfps R n})`_i = (i == 0%N)%:R.
Proof. by rewrite coef1. Qed.

Lemma trXn1 : trXn n 1 = 1.
Proof. by apply/tfpsP => i Hi; rewrite coef_trXn Hi. Qed.

Fact trXn_is_monoid_morphism : monoid_morphism (@trXn R n).
Proof. by split => [|f g] /=; [rewrite trXn1 | rewrite -trXn_mul]. Qed.
HB.instance Definition _ := GRing.isMonoidMorphism.Build {poly R} {tfps R n}
                              (trXn n) trXn_is_monoid_morphism.

Lemma mul_tfps_val f g : f * g = trXn n (tfps f * tfps g).
Proof. by []. Qed.

Lemma coeftM f g (i : nat) :
  (f * g)`_i = if i <= n then \sum_(j < i.+1) f`_j * g`_(i - j) else 0.
Proof. by rewrite !coef_tfpsE mul_tfps_val coef_trXn coefM. Qed.

Lemma coeftMr f g (i : nat) :
  (f * g)`_i = if i <= n then \sum_(j < i.+1) f`_(i - j) * g`_j else 0.
Proof. by rewrite !coef_tfpsE mul_tfps_val coef_trXn coefMr. Qed.

Lemma exp_tfps_val f (m : nat) : f ^+ m = trXn n ((tfps f) ^+ m).
Proof.
elim: m => [|m IHm]; first by rewrite !expr0 trXn1.
by rewrite exprS {}IHm /= !rmorphXn /= tfpsK -exprS.
Qed.

Fact tfpsC_is_monoid_morphism : monoid_morphism (@tfpsC R n : R -> {tfps R n}).
Proof.
split => [|c1 c2]; first by rewrite tfpsCE trXn1.
apply tfps_inj; rewrite mul_tfps_val !val_tfpsC -rmorphM /=.
apply/polyP => i; rewrite coef_tfps coef_trXn coefC; case: i => //= i.
by rewrite !if_same.
Qed.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build R {tfps R n} (tfpsC n) tfpsC_is_monoid_morphism.

Lemma tfpsC1 : (1%:S : {tfps R n}) = 1.
Proof. exact: rmorph1. Qed.
Lemma tfpsCM : {morph (@tfpsC R n) : a b / a * b}.
Proof. exact: rmorphM. Qed.
Lemma tfpsCX m : {morph (@tfpsC R n) : c / c ^+ m}.
Proof. exact: rmorphXn. Qed.
Lemma tfpsC_prod I (r : seq I) (s : pred I) (F : I -> R) :
  (\prod_(i <- r | s i) F i)%:S = \prod_(i <- r | s i) (F i)%:S.
Proof. exact: rmorph_prod. Qed.

Lemma tfpsC_eq1 (c : R) : (c%:S == 1 :> {tfps R n}) = (c == 1).
Proof. by rewrite -tfpsC1; apply/inj_eq/tfpsC_inj. Qed.


(* lSemiModType structure *)
Fact scale_tfps_subproof (c : R) f : size (c *: val f) <= n.+1.
Proof. exact: leq_trans (size_scale_leq _ _) (size_tfps _). Qed.
Definition scale_tfps (c : R) f := MkTfps (scale_tfps_subproof c f).

Fact scale_tfpsA a b v : scale_tfps a (scale_tfps b v) = scale_tfps (a * b) v.
Proof. by apply/tfpsP => i le_in /=; rewrite !coefZ mulrA. Qed.
Fact scale_0tfps v : scale_tfps 0 v = 0.
Proof. by apply/tfpsP => i le_in; rewrite coef_tfpsE /= scale0r. Qed.
Fact scale_1tfps : left_id 1 scale_tfps.
Proof. by move=> x; apply/tfpsP => i le_in; rewrite coef_tfpsE /= scale1r. Qed.
Fact scale_tfpsDr : right_distributive scale_tfps +%R.
Proof. by move=> r x y; apply/tfpsP => i; rewrite coef_tfpsE /= scalerDr. Qed.
Fact scale_tfpsDl v : {morph scale_tfps^~ v: a b / a + b}.
Proof. by move=> r s; apply/tfpsP => i; rewrite coef_tfpsE /= scalerDl. Qed.

HB.instance Definition _ := GRing.Nmodule_isLSemiModule.Build R {tfps R n}
  scale_tfpsA scale_0tfps scale_1tfps scale_tfpsDr scale_tfpsDl.

Fact trXn_is_semilinear : semilinear (@trXn R n).
Proof.
by split=> [c f | f g]; apply/tfpsP => i Hi;
     rewrite !(coefD, coefZ, coef_trXn) Hi.
Qed.
HB.instance Definition _ :=
  GRing.isSemilinear.Build
    R {poly R} {tfps R n} _ (trXn n) trXn_is_semilinear.

Fact tfps_is_semilinear : semilinear (tfps : {tfps R n} -> {poly R}).
Proof. by []. Qed.
HB.instance Definition _ :=
  GRing.isSemilinear.Build
    R {tfps R n} {poly R} _ (@tfps R n) tfps_is_semilinear.


(* lalgType structure *)
Fact scale_tfpsAl c f g : scale_tfps c (f * g) = (scale_tfps c f) * g.
Proof.
by apply tfps_inj; rewrite /= -linearZ  /= !mul_tfps_val -scalerAl linearZ.
Qed.
HB.instance Definition _ :=
  GRing.LSemiModule_isLSemiAlgebra.Build R {tfps R n} scale_tfpsAl.

Lemma alg_tfpsC (c : R) : c%:A = c%:S.
Proof. by apply/tfps_inj; rewrite {1}val_tfpsC -alg_polyC. Qed.

(* Test *)
Example trXn_poly0 : trXn n (0 : {poly R}) = 0.
Proof. by rewrite linear0. Qed.

Example trXn_poly1 : trXn n (1 : {poly R}) = 1.
Proof. by rewrite rmorph1. Qed.

Lemma trXnZ (c : R) (p : {poly R}) : trXn n (c *: p) =  c *: (trXn n p).
Proof. by rewrite linearZ. Qed.


Local Notation "f *h g" := (hmul_tfps f g) (at level 2).

Lemma hmul_tfpsr1 f : f *h 1 = (f`_0)%:S.
Proof.
apply/tfpsP => i.
rewrite coeftC coef_poly ltnS coef1 => ->.
by case: i => [|i]; rewrite ?mulr1 ?mulr0.
Qed.

Lemma hmul_tfps1r f : 1 *h f = (f`_0)%:S.
Proof.
apply/tfpsP => i.
rewrite coeftC coef_poly ltnS coef1 => ->.
by case: i => [|i]; rewrite ?mul1r ?mul0r.
Qed.

Lemma tfps_is_cst (g : {tfps R 0}) : g = (g`_0) %:S.
Proof.
apply/tfps_inj; rewrite val_tfpsC.
by apply: size1_polyC; rewrite size_tfps.
Qed.


Lemma coeftfpsE f i : coeftfps i f = coefp i (tfps f).
Proof. by rewrite /= coef_tfpsE. Qed.

Lemma coeftD i : nmod_morphism (fun f => f`_i).
Proof. by split => [| f g]; rewrite ?coef0 ?coefD. Qed.

HB.instance Definition _ i :=
  GRing.isNmodMorphism.Build {tfps R n} R (coeftfps i) (coeftD i).

Lemma coeftMn f k i : (f *+ k)`_i = f`_i *+ k.
Proof. exact: (raddfMn (coeftfps i)). Qed.
Lemma coeft_sum I (r : seq I) (P : pred I) (F : I -> {tfps R n}) k :
  (\sum_(i <- r | P i) F i)`_k = \sum_(i <- r | P i) (F i)`_k.
Proof. exact: (raddf_sum (coeftfps k)). Qed.

Fact coeftfps_is_linear i :
  scalable_for *%R (coeftfps i : {tfps R n} -> R).
Proof. by move=> c g; rewrite /= !coef_tfpsE !linearZ coefZ. Qed.
HB.instance Definition _ i :=
  GRing.isScalable.Build R {tfps R n} R _ (coeftfps i) (coeftfps_is_linear i).

Lemma coeftZ a f i : (a *: f)`_i = a * f`_i.
Proof. exact: (scalarZ (coeftfps i)). Qed.

Fact coeftfps0_is_monoid_morphism :
  monoid_morphism (coeftfps 0 : {tfps R n} -> R).
Proof.
split=> [|p q]; rewrite !coeftfpsE; first by rewrite polyCK.
rewrite mul_tfps_val /= -!/(_`_0) coef_trXn /= -!/(_`_0) -!/(coefp 0 _).
by rewrite rmorphM.
Qed.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build
    {tfps R n} R (coeftfps 0) coeftfps0_is_monoid_morphism.

Fact coeft0M f g : (f * g)`_0 = f`_0 * g`_0.
Proof. exact: (rmorphM (coeftfps 0)). Qed.
Fact coeft0X f i : (f ^+ i)`_0 = f`_0 ^+ i.
Proof. exact: (rmorphXn (coeftfps 0)). Qed.
Fact coeft0_prod I (r : seq I) (P : pred I) (F : I -> {tfps R n}) :
  (\prod_(i <- r | P i) F i)`_0 = \prod_(i <- r | P i) (F i)`_0.
Proof. exact: (rmorph_prod (coeftfps 0)). Qed.

End TFPSSemiRingTheory.


Section TFPSRingTheory.

Variable (R : nzRingType) (n : nat).
Implicit Types (p q r s : {poly R}).
Implicit Types (f g : {tfps R n}).


(* zmodType structure *)
Fact opp_tfps_subproof f : size (- tfps f) <= n.+1.
Proof. by rewrite size_polyN ?size_tfps. Qed.
Definition opp_tfps f := MkTfps (opp_tfps_subproof f).

Fact add_Ntfps : left_inverse 0 opp_tfps (+%R).
Proof. by move => f; apply/tfps_inj/addNr. Qed.
HB.instance Definition _ :=
    GRing.Nmodule_isZmodule.Build {tfps R n} add_Ntfps.

Lemma tfpsCN : {morph (@tfpsC R n) : c / - c}.
Proof. exact: raddfN. Qed.
Lemma tfpsCD : {morph (@tfpsC R n) : a b / a - b}.
Proof. exact: raddfB. Qed.

Lemma tfpsCMNn m : {morph (@tfpsC R n) : c / c *- m}.
Proof. exact: raddfMNn. Qed.

Lemma coeftB f g i : (f - g)`_i = f`_i - g`_i.
Proof. by rewrite coefB. Qed.
Lemma coeftN f i : (- f)`_i = - f`_i.
Proof. exact: (raddfN (coeftfps i)). Qed.
Lemma coeftMNn f k i : (f *- k)`_i = f`_i *- k.
Proof. exact: (raddfMNn (coeftfps i)). Qed.

End TFPSRingTheory.


Section TrXnT.

Variable R : nzSemiRingType.

Definition trXnt m n : {tfps R m} -> {tfps R n} :=
  @trXn R n  \o  @tfps R m.

Variables (m n p : nat).
Implicit Type (f : {tfps R m}).

Lemma coef_trXnt f i : (trXnt n f)`_i = if i <= n then f`_i else 0.
Proof. by rewrite coef_trXn -coef_tfpsE. Qed.

Lemma trXntE f : trXnt n f = trXn n (tfps f).
Proof. by []. Qed.

Lemma trXnt_id f : trXnt m f = f.
Proof. by rewrite /trXnt /= tfpsK. Qed.

Lemma trXnt_tfps_of_fun (f : nat -> R) :
  n <= m -> trXnt n (tfps_of_fun m f) = tfps_of_fun n f.
Proof.
move=> le_nm; apply tfpsP => i le_in.
by rewrite coef_trXnt le_in !coef_tfps_of_fun le_in (leq_trans le_in le_nm).
Qed.

Fact trXnt_trXnt f :
  p <= n -> trXnt p (trXnt n f) = trXnt p f.
Proof. exact: trXn_trXn. Qed.

Lemma trXntC a : trXnt n (a%:S : {tfps R m}) = a%:S.
Proof. exact: trXnCE. Qed.

Lemma trXnt0 : @trXnt m n 0 = 0.
Proof. exact: trXn0. Qed.
Lemma trXnt1 : @trXnt m n 1 = 1.
Proof. exact: trXn1. Qed.

Fact trXnt_is_semilinear : semilinear (@trXnt m n).
Proof. by split=> [c f | f g]; rewrite !trXntE ?linearD ?linearZ. Qed.
HB.instance Definition _ :=
  GRing.isSemilinear.Build R {tfps R m} {tfps R n} _ (@trXnt m n)
    trXnt_is_semilinear.

Hypothesis H : n <= m.
Fact trXnt_is_monoid_morphism : monoid_morphism (@trXnt m n).
Proof.
split=> [|f g] /=; first exact trXnt1.
by rewrite /trXnt /= mul_tfps_val /= -rmorphM /= trXn_trXn.
Qed.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build
    {tfps R m} {tfps R n} (@trXnt m n) trXnt_is_monoid_morphism.

End TrXnT.


Section TestTrXnT.

Variable R : nzRingType.
Variables (m n p : nat).
Implicit Type (f g : {tfps R m}).

(* Test *)
Example trXnt_tfps0 : trXnt n (0 : {tfps R m}) = 0.
Proof. by rewrite linear0. Qed.

Example trXn_tfps1 : trXn n (tfps (1 : {tfps R m})) = 1.
Proof. by rewrite rmorph1. Qed.

Example trXntD f g : trXnt n (f - g) = trXnt n f - trXnt n g.
Proof. by rewrite linearB. Qed.

Example trXntZ c f : trXnt n (c *: f) =  c *: (trXnt n f).
Proof. by rewrite linearZ. Qed.

Example trXntM f g : n <= m -> trXnt n (f * g) = trXnt n f * trXnt n g.
Proof. by move=> H; rewrite rmorphM. Qed.

Example trXntM12 (f g : {tfps R 2}) :
  trXnt 1 (f * g) =  (trXnt 1 f) * (trXnt 1 g).
Proof. by rewrite rmorphM. Qed.

End TestTrXnT.


Section TFPSX.

Variable (R : nzSemiRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Lemma tfps0X m : m = 0%N -> \Xo(m) = 0 :> {tfps R m}.
Proof.
by move=> ->; rewrite (tfps_is_cst \X) coef_trXn coefX /= tfpsC0.
Qed.

Lemma val_tfpsSX m : tfps (\Xo(m.+1)) = 'X%R :> {poly R}.
Proof.
apply/polyP => i.
by rewrite coef_trXn coefX; case: eqP => [->|] // _; rewrite if_same.
Qed.

Lemma val_tfpsX m : tfps (\Xo(m)) = (m != 0%N)%:R *: 'X%R :> {poly R}.
Proof.
case: m => [|m]; first by rewrite tfps0X /= ?scale0r.
by rewrite val_tfpsSX /= scale1r.
Qed.

Lemma coef_tfpsX m i :
  (\X : {tfps R m})`_i = (m != 0%N)%:R * (i == 1%N)%:R.
Proof. by rewrite coef_tfpsE val_tfpsX coefZ coefX. Qed.

Lemma trXn_tfpsX m : trXn n (tfps \Xo(m.+1)) = \X :> {tfps R n}.
Proof.
case: n => [|n'].
  rewrite [RHS]tfps0X //; apply tfpsP => i.
  rewrite leqn0 => /eqP ->.
  by rewrite coeft0 coef_trXn -coef_tfpsE coef_tfpsX /= mulr0.
by apply tfps_inj; rewrite !val_tfpsSX.
Qed.

Lemma trXnt_tfpsX m : trXnt n \Xo(m.+1) = \X :> {tfps R n}.
Proof. exact: trXn_tfpsX. Qed.

Lemma commr_tfpsX f : GRing.comm f \X.
Proof.
apply/tfpsP => i _.
by rewrite !mul_tfps_val /= trXn_mull trXn_mulr commr_polyX.
Qed.

Lemma commr_tfpsXn f k : GRing.comm f (\X ^+ k).
Proof.
Proof. exact/commrX/commr_tfpsX. Qed.

Lemma coef_tfpsXM f i :
  (\X * f)`_i = if i == 0%N then 0 else if i <= n then f`_i.-1 else 0.
Proof. by rewrite !mul_tfps_val /= trXn_mull coef_trXn coefXM; case: i. Qed.

Lemma coef_tfpsXnM f k i :
  (\X ^+ k * f)`_i = if i < k then 0 else if i <= n then f`_(i - k) else 0.
Proof.
elim: k i => [|k IHk] i.
  by rewrite expr0 ltn0 mul1r subn0 {1}coef_tfps.
rewrite exprS -mulrA coef_tfpsXM {}IHk.
case: i => [|i]//=; rewrite ltnS subSS.
by case: (ltnP i n) => [/ltnW ->|]//; rewrite if_same.
Qed.

Lemma coef_tfpsXn i k :
  ((\X : {tfps R n})^+ k)`_i = ((i <= n) && (i == k%N))%:R.
Proof.
rewrite -[_ ^+ k]mulr1 coef_tfpsXnM coef1 -/(leq _ _).
case: (altP (i =P k)) => [-> | Hneq]; first by rewrite ltnn leqnn; case: leqP.
case: (leqP i n) => _; last by rewrite if_same.
case: ltnP => //=.
by rewrite [i <= k]leq_eqVlt (negbTE Hneq) ltnNge => ->.
Qed.

Lemma coef_tfps_sumfXi (f : nat -> R) i :
  i <= n -> (\sum_(i < n.+1) f i *: \Xo(n) ^+ i)`_i = f i.
Proof.
rewrite -ltnS => lt_in1.
rewrite (bigD1 (Ordinal lt_in1)) //=.
rewrite coeftD coeftZ coef_tfpsXn -ltnS lt_in1 eqxx mulr1.
rewrite coeft_sum big1 ?coef0 ?addr0 // => j; rewrite -val_eqE /= => Hneq.
by rewrite coeftZ coef_tfpsXn eq_sym (negbTE Hneq) andbF mulr0.
Qed.

Lemma tfps_def f : f = \sum_(i < n.+1) f`_i *: \X ^+ i.
Proof.
apply/tfpsP => j le_jn; have:= le_jn; rewrite -ltnS => lt_jn1.
by rewrite coef_tfps_sumfXi.
Qed.

Lemma tfps_of_funE (f : nat -> R):
  [tfps i <= n => f i] = \sum_(i < n.+1) f i *: \X ^+ i.
Proof.
apply tfpsP => i le_in.
by rewrite coef_tfps_of_fun coef_tfps_sumfXi le_in.
Qed.

Lemma expr_tfpscX (c : R) i :
  (c *: \X) ^+ i = (c ^+ i) *: \X ^+ i :> {tfps R n}.
Proof.
rewrite -[c *: \X](mulr_algl c) exprMn_comm; last exact: commr_tfpsX.
by rewrite -in_algE -rmorphXn /= mulr_algl.
Qed.

End TFPSX.


Section TFPSConvRing.

Variable (R : nzSemiRingType) (n : nat).

Fact size_convr_subproof (f : {tfps R n}) :
  size (map_poly (fun c : R => c : R^c) (tfps f)) <= n.+1.
Proof. by rewrite size_map_inj_poly ?size_tfps. Qed.
Definition convr_tfps f : {tfps R^c n} := MkTfps (size_convr_subproof f).

Fact size_iconvr_subproof (f : {tfps R^c n}) :
  size (map_poly (fun c : R^c => c : R) (tfps f)) <= n.+1.
Proof. by rewrite size_map_inj_poly ?size_tfps. Qed.
Definition iconvr_tfps f : {tfps R n} := MkTfps (size_iconvr_subproof f).

Fact convr_tfps_is_nmod_morphism : nmod_morphism convr_tfps.
Proof.
split => [|f g] ; apply/tfpsP => i _.
  by rewrite coef0 !coef_map_id0 // coef0.
by rewrite /= coefD !coef_map_id0 // coefD.
Qed.
HB.instance Definition _ :=
  GRing.isNmodMorphism.Build _ _ convr_tfps convr_tfps_is_nmod_morphism.

Fact iconvr_tfps_is_nmod_morphism : nmod_morphism iconvr_tfps.
Proof.
split => [|f g] ; apply/tfpsP => i _.
  by rewrite coef0 !coef_map_id0 // coef0.
by rewrite /= coefD !coef_map_id0 // coefD.
Qed.
HB.instance Definition _ :=
  GRing.isNmodMorphism.Build _ _ iconvr_tfps iconvr_tfps_is_nmod_morphism.

Lemma convr_tfpsK : cancel convr_tfps iconvr_tfps.
Proof. by move=> f; apply/tfpsP => i _; rewrite !coef_map_id0. Qed.
Lemma iconvr_tfpsK : cancel iconvr_tfps convr_tfps.
Proof. by move=> f; apply/tfpsP => i _; rewrite !coef_map_id0. Qed.

Lemma convr_tfps1 : convr_tfps 1 = 1.
Proof. by apply/tfpsP => i Hi; rewrite coef_map_id0 // !coef1. Qed.
Lemma iconvr_tfps1 : iconvr_tfps 1 = 1.
Proof. by apply/tfpsP => i Hi; rewrite coef_map_id0 // !coef1. Qed.

Lemma convr_tfpsM f g :
  convr_tfps f * convr_tfps g = convr_tfps (g * f).
Proof.
apply/tfpsP => i Hi.
rewrite coeftM coef_map_id0 // coeftMr Hi.
by apply eq_bigr => j _ /=; rewrite !coef_map_id0.
Qed.
Lemma iconvr_tfpsM f g :
  iconvr_tfps f * iconvr_tfps g = iconvr_tfps (g * f).
Proof.
apply/tfpsP => i Hi.
rewrite coeftM coef_map_id0 // coeftMr Hi.
by apply eq_bigr => j _ /=; rewrite !coef_map_id0.
Qed.

End TFPSConvRing.


Section TFPSUnitRingLeft.

Variable (R : unitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Definition unit_tfps : pred {tfps R n} := fun f => f`_0 \in GRing.unit.

Fixpoint inv_tfps_rec f bound m :=
  if bound is b.+1 then
    if (m <= b)%N then inv_tfps_rec f b m
    else -(f`_0%N)^-1 * (\sum_(i < m) f`_i.+1 * (inv_tfps_rec f b (m - i.+1)%N))
  else (f`_0%N)^-1.
Definition inv_tfps f : {tfps R n} :=
  if unit_tfps f then [tfps i <= n => inv_tfps_rec f i i] else f.

Lemma coef0_inv_tfps f : unit_tfps f -> (inv_tfps f)`_0 = (f`_0)^-1.
Proof. by rewrite /inv_tfps => ->; rewrite coef_tfps_of_fun. Qed.

Lemma coefS_inv_tfps f m :
  unit_tfps f -> m < n ->
  (inv_tfps f)`_m.+1 =
  - (f`_0%N)^-1 *
    (\sum_(i < m.+1) f`_i.+1 * (inv_tfps f)`_(m - i)%N).
Proof.
move=> s_unit lt_mn.
rewrite /inv_tfps s_unit coef_tfps_of_fun /= ltnn lt_mn; congr (- _ * _).
apply: eq_bigr => [[i]/=]; rewrite ltnS => le_im _.
rewrite coef_tfps_of_fun (leq_trans (leq_subr _ _) (ltnW lt_mn)).
congr (_ * _); rewrite /bump /= subSS.
move: (m - i)%N (leq_subr i m) {le_im} => {}i le_im.
move: le_im => /subnKC <-; elim: (m - i)%N => [|k IHl]; first by rewrite addn0.
by rewrite addnS /= leq_addr.
Qed.

Lemma mul_tfpsVr : {in unit_tfps, right_inverse 1 inv_tfps *%R}.
Proof.
move=> f s_unit; have:= s_unit; rewrite /= unfold_in => s0_unit.
apply/tfpsP => m _; elim: m {1 3 4}m (leqnn m) => [| m IHm] i.
  rewrite leqn0 => /eqP ->.
  by rewrite coef1 coeft0M coef0_inv_tfps ?divrr.
move=> le_im1; case: (leqP i m) => [|lt_mi]; first exact: IHm.
have {le_im1 lt_mi i} -> : i = m.+1 by apply anti_leq; rewrite le_im1 lt_mi.
rewrite coef1 [RHS]/=.
case: (ltnP m.+1 n.+1) => Hmn; last first.
  by rewrite nth_default ?(leq_trans (size_tfps _)).
rewrite coeftM -ltnS Hmn big_ord_recl [val ord0]/= subn0.
rewrite coefS_inv_tfps // mulNr mulrN mulVKr // addrC.
apply/eqP; rewrite subr_eq0; apply/eqP.
by apply eq_bigr => [] [i] /=.
Qed.

Lemma inv_tfps0id : {in [predC unit_tfps], inv_tfps =1 id}.
Proof.
by move=> s; rewrite inE /= /inv_tfps unfold_in /unit_tfps => /negbTE ->.
Qed.

End TFPSUnitRingLeft.


Section TruncFPSUnitRing.

Variable (R : unitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Let invl_tfps f := iconvr_tfps (inv_tfps (convr_tfps f)).

Fact mul_tfpsVl : {in @unit_tfps R n, left_inverse 1 invl_tfps *%R}.
Proof.
move=> f Hf; rewrite /invl_tfps -{2}(convr_tfpsK f).
rewrite iconvr_tfpsM mul_tfpsVr ?iconvr_tfps1 //.
by move: Hf; rewrite !unfold_in coef_map_id0.
Qed.
(* General semi-group theory : left inverse = right inverse *)
Fact invr_tfpsE f : unit_tfps f -> inv_tfps f = invl_tfps f.
Proof.
move=> H; have:= erefl (invl_tfps f * f * inv_tfps f).
by rewrite -{2}mulrA mul_tfpsVl // mul1r mul_tfpsVr // mulr1.
Qed.
Fact mul_tfpsrV :
  {in @unit_tfps R n, left_inverse 1 (@inv_tfps R n) *%R}.
Proof. by move=> f Hs; rewrite invr_tfpsE // mul_tfpsVl. Qed.
Fact unit_tfpsP f g : g * f = 1 /\ f * g = 1 -> unit_tfps f.
Proof.
move=> [] /(congr1 (fun x : {tfps _ _ } => x`_0)).
rewrite coef1 coeft0M => Hl.
move=>    /(congr1 (fun x : {tfps _ _ } => x`_0)).
rewrite coef1 coeft0M => Hr.
by rewrite /unit_tfps; apply/unitrP; exists g`_0.
Qed.
HB.instance Definition _ :=
  GRing.NzRing_hasMulInverse.Build
    {tfps R n} mul_tfpsrV (@mul_tfpsVr R n) unit_tfpsP (@inv_tfps0id R n).


Lemma unit_tfpsE f : (f \in GRing.unit) = (f`_0 \in GRing.unit).
Proof. by []. Qed.

Lemma trXn_unitE (p : {poly R}) :
  ((trXn n p) \is a GRing.unit) = (p`_0 \is a GRing.unit).
Proof. by rewrite unit_tfpsE coef0_trXn. Qed.

Lemma coeft0V f : (f ^-1)`_0 = (f`_0)^-1.
Proof.
case (boolP (f \is a GRing.unit))=> [f_unit|]; first by rewrite coef0_inv_tfps.
move=> Hinv; rewrite (invr_out Hinv).
by move: Hinv; rewrite unit_tfpsE => /invr_out ->.
Qed.

Lemma coeftV f i : f \is a GRing.unit -> f^-1`_i =
  if i > n then 0 else
  if i == 0%N then (f`_0)^-1
  else - (f`_0) ^-1 * (\sum_(j < i) f`_j.+1 * f^-1`_(i - j.+1)).
Proof.
move=> funit; case: ltnP => Hi.
  by rewrite -(tfpsK f^-1) coef_trXnt (ltn_geF Hi).
case: i Hi => [|i] Hi; first by rewrite eq_refl coeft0V.
by rewrite coefS_inv_tfps.
Qed.

Lemma trXnCV (c : R) : (trXn n c%:P)^-1 = trXn n (c^-1)%:P.
Proof.
case (boolP (c \in GRing.unit)) => [Uc | nUc].
  by rewrite -/((trXn n \o @polyC R) _) -rmorphV.
by rewrite !invr_out // unit_tfpsE coef_trXn coefC.
Qed.

End TruncFPSUnitRing.

Definition coeft_simpl :=
  (commr_tfpsX, commr_tfpsXn,
    coeft0, coeftD, coeftN, coeftB, coeftMn, coeftMNn, coeft_sum,
    coeft1, coeftZ, coef_tfpsX, coef_tfpsXn, coef_tfpsXM, coef_tfpsXnM).


Section TruncFPSTheoryUnitRing.

Variable (R : unitRingType) (m n : nat).
Implicit Types (f g : {tfps R n}).

Lemma trXnt_unitE f :
  ((trXnt m f) \is a GRing.unit) = (f`_0 \is a GRing.unit).
Proof. exact: trXn_unitE. Qed.

Lemma trXntV f : m <= n -> trXnt m (f^-1) = (trXnt m f) ^-1.
Proof.
move=> leq_mn.
case (boolP (f`_0 \is a GRing.unit)) => f0U; first last.
  by rewrite !invr_out // unit_tfpsE ?coef0_trXn.
by rewrite rmorphV.
Qed.

End TruncFPSTheoryUnitRing.


Section TFPSComSemiRing.

Variable (R : comNzSemiRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Fact mul_tfpsC f g : f * g = g * f.
Proof. by rewrite !mul_tfps_val mulrC. Qed.
HB.instance Definition _ :=
  GRing.PzSemiRing_hasCommutativeMul.Build {tfps R n} mul_tfpsC.

(* Q: why is this needed ??? *)
HB.instance Definition _ :=
  GRing.LSemiAlgebra_isComSemiAlgebra.Build R {tfps R n}.
Let check := {tfps R n} : comSemiAlgType R.

Lemma hmul_tfpsC : commutative (@hmul_tfps R n).
Proof. by move=> f1 f2; apply/tfpsP => i; rewrite !coef_poly mulrC. Qed.

End TFPSComSemiRing.


Section TFPSComRing.

Variable (R : comNzRingType) (n : nat).

HB.instance Definition _ := GRing.ComNzSemiRing.on {tfps R n}.

(* Check {tfps R n} : comAlgType R. *)
End TFPSComRing.


Section TFPSComUnitRing.

Variable (R : comUnitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

(* Rebuilt the various instances on a comUnitRingType base ring. *)
HB.instance Definition _ := GRing.ComNzRing.on {tfps R n}.

End TFPSComUnitRing.


Section TFPSIDomain.

Variable R : idomainType.

Lemma poly_modXn n (p : {poly R}) : p %% 'X^n = Poly (take n p).
Proof.
rewrite -{1}(poly_cat p n) addrC mulrC Pdiv.IdomainUnit.modp_addl_mul_small //.
- by rewrite lead_coefXn unitr1.
- rewrite size_polyXn ltnS (leq_trans (size_Poly _)) //.
  by rewrite size_take -/(minn _ _) geq_minl.
Qed.

Lemma trXn_modE m (p : {poly R}) : p %% 'X^(m.+1) = tfps (trXn m p).
Proof. by apply/val_inj => /=; rewrite trXnE poly_modXn. Qed.

Fact tfps_modp (n m : nat) (p : {poly R}) : n <= m ->
  trXn n (p %% 'X^(m.+1)) = trXn n p.
Proof. by move=> lt_nm; apply/val_inj; rewrite /= trXn_modE trXn_trXn. Qed.

Variable n : nat.
Implicit Types (f g : {tfps R n}).

Fact mod_tfps (m : nat) f : n <= m -> (tfps f) %% 'X^(m.+1) = (tfps f).
Proof.
move=> leq_nm.
by rewrite modp_small // size_polyXn ltnS (leq_trans (size_tfps _)).
Qed.

End TFPSIDomain.


Section MapTFPS.

Variables (K L : nzSemiRingType) (n : nat) (F : {rmorphism K -> L}).

Implicit Type g h : {tfps K n}.

Fact map_tfps_subproof g : size (map_poly F (val g)) <= n.+1.
Proof.
by rewrite map_polyE (leq_trans (size_Poly _)) // size_map size_tfps.
Qed.
Definition map_tfps g := MkTfps (map_tfps_subproof g).

Lemma coef_map_tfps i g : (map_tfps g)`_i = F (g`_i).
Proof. by rewrite coef_map. Qed.

Lemma map_tfpsM g h : map_tfps (g * h) = (map_tfps g) * (map_tfps h).
Proof.
apply/tfpsP => i Hi.
rewrite coef_map_tfps !coeftM Hi rmorph_sum.
apply eq_bigr => [] [j]; rewrite /= ltnS => le_ji _.
by rewrite rmorphM !coef_map_tfps.
Qed.

Fact map_tfps_is_nmod_morphism : nmod_morphism map_tfps.
Proof. by split=> [|x y]; apply/tfps_inj => /=; rewrite ?raddf0 ?rmorphD. Qed.
HB.instance Definition _ :=
  GRing.isNmodMorphism.Build
    {tfps K n} {tfps L n} map_tfps map_tfps_is_nmod_morphism.

Lemma map_tfpsZ (c : K) g : map_tfps (c *: g) = (F c) *: (map_tfps g).
Proof. by apply/tfpsP => i le_in; rewrite coef_tfpsE /= map_polyZ. Qed.
HB.instance Definition _ i :=
  GRing.isScalable.Build _ {tfps K n} {tfps L n} _ map_tfps
    (map_tfpsZ : scalable_for (F \; *:%R) map_tfps).

Fact map_tfps_is_monoid_morphism : monoid_morphism map_tfps.
Proof.
split => [|x y]; last by rewrite map_tfpsM.
by apply/tfps_inj => /=; rewrite rmorph1.
Qed.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build
    {tfps K n} {tfps L n} map_tfps map_tfps_is_monoid_morphism.


(* Tests *)
Example test_map_tfps0 : map_tfps 0 = 0.
Proof. by rewrite linear0. Qed.

Example test_map_tfpsD g h :
  map_tfps (g + h) = (map_tfps g) + (map_tfps h).
Proof. by rewrite linearD. Qed.


Lemma trXn_map_poly (p : {poly K}) :
  trXn n (map_poly F p) = map_tfps (trXn n p).
Proof. by apply/tfpsP => i le_in; rewrite !(coef_trXn, le_in, coef_map). Qed.

Local Notation "g '^f'" := (map_tfps g).
Local Notation "f *h g" := (hmul_tfps f g) (at level 2).

Lemma map_hmul g h : (g *h h) ^f = (g ^f) *h (h ^f).
Proof.
apply/tfpsP => i le_in /=.
rewrite coef_map !coef_poly ltnS le_in [LHS]rmorphM.
have co (l : {tfps K n}) : (if i < size l then F l`_i else 0) = F l`_i.
  by case: ltnP => // H; rewrite nth_default // rmorph0.
by rewrite !co.
Qed.

End MapTFPS.

Lemma map_tfps_injective (K L : nzSemiRingType) n (F : {rmorphism K -> L}) :
  injective F -> injective (@map_tfps _ _ n F).
Proof.
by move=> Finj x y /val_eqP/eqP/(map_poly_injective Finj)/tfps_inj.
Qed.

Lemma map_tfps_inj (K : fieldType) (L : nzRingType) n (F : {rmorphism K -> L}) :
  injective (@map_tfps _ _ n F).
Proof. by move=> x y /val_eqP/eqP /= /map_poly_inj H; apply tfps_inj. Qed.

Lemma trXnt_map_poly (m n : nat) (K L : nzSemiRingType)
      (F : {rmorphism K -> L}) (g : {tfps K n}) :
  trXnt m (map_tfps F g) = map_tfps F (trXnt m g).
Proof. by apply/tfpsP=> i le_in; rewrite !(coef_map, coef_trXn) le_in. Qed.

Lemma map_poly_idfun (R : nzSemiRingType) :
  map_poly (@idfun R) =1 @idfun {poly R}.
Proof. exact: coefK. Qed.

Lemma map_tfps_idfun (K : fieldType) (m : nat) :
  map_tfps (@idfun K) =1 @idfun {tfps K m}.
Proof.
move=> f; apply/tfpsP => i le_in /=.
by rewrite coef_tfpsE /= map_poly_idfun.
Qed.


Section Coefficient01SemiRing.

Variables (R : nzSemiRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Definition coeft0_eq0 := fun f : {tfps R n} => f`_0 == 0.
Definition coeft0_eq1 := fun f : {tfps R n} => f`_0 == 1.

Lemma coeft0_eq0E f : (f \in coeft0_eq0) = (f`_0 == 0).
Proof. by rewrite -topredE. Qed.

Lemma coeft0_eq1E f : (f \in coeft0_eq1) = (f`_0 == 1).
Proof. by rewrite -topredE. Qed.

Lemma zero_in_coeft0_eq0 : 0 \in coeft0_eq0.
Proof. by rewrite coeft0_eq0E coeft0. Qed.

Lemma tfpsX_in_coeft0_eq0 : \X \in coeft0_eq0.
Proof. by rewrite coeft0_eq0E coef_tfpsX /= mulr0. Qed.

Lemma coeft0_eq0Z f c : f \in coeft0_eq0 -> c *: f \in coeft0_eq0.
Proof. by rewrite !coeft0_eq0E coeftZ => /eqP ->; rewrite mulr0. Qed.

Lemma tfpscX_in_coeft0_eq0 c : c *: \X \in coeft0_eq0.
Proof. exact/coeft0_eq0Z/tfpsX_in_coeft0_eq0. Qed.

Lemma coeft0_eq0D f g :
  f \in coeft0_eq0 -> g \in coeft0_eq0 -> f + g \in coeft0_eq0.
Proof. by rewrite !coeft0_eq0E coeftD => /eqP -> /eqP ->; rewrite addr0. Qed.

Lemma coeft0_eq0Mr f g : f \in coeft0_eq0 -> f * g \in coeft0_eq0.
Proof. by rewrite !coeft0_eq0E coeft0M => /eqP->; rewrite mul0r. Qed.
Lemma coeft0_eq0Ml f g : g \in coeft0_eq0 -> f * g \in coeft0_eq0.
Proof. by rewrite !coeft0_eq0E coeft0M => /eqP->; rewrite mulr0. Qed.

Lemma coeft0_eq0X f i : f \in coeft0_eq0 -> f ^+ i.+1 \in coeft0_eq0.
Proof.
elim: i => [| i IHi]; first by rewrite expr1.
by rewrite exprS => /coeft0_eq0Mr; apply.
Qed.

Lemma coeft0_eq1_add01 f g :
  f \in coeft0_eq0 -> g \in coeft0_eq1 -> f + g \in coeft0_eq1.
Proof.
rewrite coeft0_eq0E !coeft0_eq1E coefD => /eqP -> /eqP ->.
by rewrite add0r.
Qed.

End Coefficient01SemiRing.


Section Coefficient01Ring.

Variables (R : nzRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Local Notation coeft0_eq0 := (@coeft0_eq0 R n).
Local Notation coeft0_eq1 := (@coeft0_eq1 R n).

Fact coeft0_eq0_idealr : idealr_closed coeft0_eq0.
Proof.
split => [|| a p q ]; rewrite ?coeft0_eq0E ?coefC ?eqxx ?oner_eq0 //.
move=> /eqP p0_eq0 /eqP q0_eq0.
by rewrite coeftD q0_eq0 addr0 coeft0M p0_eq0 mulr0.
Qed.
Fact coeft0_eq0_key : pred_key coeft0_eq0. Proof. by []. Qed.
Canonical coeft0_eq0_keyed := Eval hnf in KeyedPred coeft0_eq0_key.
HB.instance Definition _ :=
  isIdealr.Build {tfps R n} coeft0_eq0 coeft0_eq0_idealr.

Lemma coeft0_eq10 f : (f \in coeft0_eq1) = ((1 - f) \in coeft0_eq0).
Proof. by rewrite ?coeft0_eq0E ?coeft0_eq1E coefB coef1 subr_eq0 eq_sym. Qed.

Lemma coeft0_eq01 f : (f \in coeft0_eq0) = ((1 + f) \in coeft0_eq1).
Proof. by rewrite coeft0_eq10 -[RHS]rpredN !opprD !opprK addKr. Qed.

Example coeft0_eq0N f : f \in coeft0_eq0 -> (-f) \in coeft0_eq0.
Proof. by move=> hf; rewrite rpredN. Qed.

Fact mulr_closed_coeft0_eq1 : mulr_closed coeft0_eq1.
Proof.
split=> [|x y]; rewrite !coeft0_eq1E ?coefC //.
by rewrite coeft0M; move/eqP ->; move/eqP ->; rewrite mul1r.
Qed.
Fact coeft0_eq1_key : pred_key coeft0_eq1. Proof. by []. Qed.
Canonical coeft0_eq1_keyed := Eval hnf in KeyedPred coeft0_eq1_key.
HB.instance Definition _ :=
  GRing.isMulClosed.Build {tfps R n} coeft0_eq1 mulr_closed_coeft0_eq1.

(* Tests *)
Example one_in_coeft0_eq1 : 1 \in coeft0_eq1.
Proof. by rewrite rpred1. Qed.

Example coeft0_eq1M f g :
  f \in coeft0_eq1 -> g \in coeft0_eq1 -> f * g \in coeft0_eq1.
Proof. by move=> hf hg; rewrite rpredM. Qed.

End Coefficient01Ring.
Arguments coeft0_eq0 {R n}.
Arguments coeft0_eq1 {R n}.

Lemma coeft0_eq0_trXnt (R : nzSemiRingType) (n m : nat) (f : {tfps R n}) :
  (trXnt m f \in coeft0_eq0) = (f \in coeft0_eq0).
Proof. by rewrite !coeft0_eq0E coef0_trXn. Qed.

Lemma coeft0_eq1_trXnt (R : nzSemiRingType) (n m : nat) (f : {tfps R n}) :
  (trXnt m f \in coeft0_eq1) = (f \in coeft0_eq1).
Proof. by rewrite !coeft0_eq1E coef0_trXn. Qed.


Section Coefficient01Unit.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Fact invr_closed_coeft0_eq1 : invr_closed (@coeft0_eq1 R n).
Proof.
move=> f; rewrite !coeft0_eq1E coeft0V; move/eqP ->.
by rewrite invr1.
Qed.
HB.instance Definition _ :=
  GRing.isInvClosed.Build {tfps R n} coeft0_eq1 invr_closed_coeft0_eq1.

Lemma coeft0_eq1V f : f \in coeft0_eq1 -> f^-1 \in coeft0_eq1.
Proof. by move=> hf; rewrite rpredVr. Qed.

Lemma coeft0_eq1_div f g :
  f \in coeft0_eq1 -> g \in coeft0_eq1 -> f / g \in coeft0_eq1.
Proof. by move=> hf hg; rewrite rpred_div. Qed.

Lemma coeft0_eq1_unit f : f \in coeft0_eq1 -> f \is a GRing.unit.
Proof. by rewrite !coeft0_eq1E unit_tfpsE => /eqP ->; apply unitr1. Qed.

End Coefficient01Unit.


Section Coefficient01IDomain.

Variables (R : idomainType) (n : nat).
Implicit Types (f g : {tfps R n}).

Fact coeft0_eq0_prime : prime_idealr_closed (@coeft0_eq0 R n).
Proof.
by move => x y; rewrite -!topredE /= /coeft0_eq0 coeft0M mulf_eq0.
Qed.
HB.instance Definition _ :=
  isPrimeIdealrClosed.Build {tfps R n} coeft0_eq0 coeft0_eq0_prime.

Example coeft0_eq0_prime_test f g :
  f * g \in coeft0_eq0 -> (f \in coeft0_eq0) || (g \in coeft0_eq0).
Proof. by rewrite prime_idealrM. Qed.

End Coefficient01IDomain.


Section MoreExpPoly.

Variable (R : nzSemiRingType).
Implicit Type (p q : {poly R}).

Lemma coefX_eq0 n m p : p`_0 = 0 -> n < m -> (p ^+ m)`_n = 0.
Proof.
elim: m n p => [|m IHm] n p Hp; first by rewrite ltn0.
case: n => [_|n].
  suff -> : (p ^+ m.+1)`_0 = (p`_0) ^+ m.+1 by rewrite Hp expr0n.
  elim: m.+1 {IHm} => {m}[|m IHm]; first by rewrite !expr0 coef1 eq_refl.
  by rewrite !exprS -{}IHm coefM big_ord_recl big_ord0 addr0.
rewrite ltnS exprS => lt_nm.
rewrite coefM; apply: big1 => [] [j]; rewrite /= ltnS => le_ji _.
case: j le_ji => [|j]; first by rewrite Hp mul0r.
rewrite !ltnS subSS => le_jn.
by rewrite IHm ?mulr0 // (leq_ltn_trans (leq_subr _ _ ) lt_nm).
Qed.

Lemma trXnX_eq0 n m p : p`_0 = 0 -> n < m -> trXn n (p ^+ m) = 0.
Proof.
move=> H1 H2.
apply/tfpsP => i le_in; rewrite coef_trXn coef0 le_in.
by rewrite coefX_eq0 // (leq_ltn_trans le_in H2).
Qed.

Lemma trXnMX_eq0 n p q i j :
  p`_0 = 0 -> q`_0 = 0 -> n < i + j -> trXn n (p ^+ i * q ^+ j) = 0.
Proof.
move=> p0 q0 lt_n_addij.
apply/tfpsP => l le_li; rewrite coef0.
rewrite coef_trXn le_li coefM.
rewrite (bigID (fun k => val k >= i)) /= ?big1 ?addr0 // => [] [k Hk] /= H.
- rewrite -ltnNge in H.
  by rewrite coefX_eq0 ?mul0r.
- rewrite ltnS in Hk.
  rewrite [X in _* X]coefX_eq0 ?mulr0 //.
  rewrite ltn_subLR //.
  exact: (leq_ltn_trans le_li (leq_trans lt_n_addij (leq_add _ _))).
Qed.

End MoreExpPoly.

Section MoreExpPolyRing.

Variable (R : nzSemiRingType).
Implicit Type (p q : {poly R}).

Lemma coefX_tfps_eq0 n m i :
  i < m -> {in coeft0_eq0, forall f : {tfps R n}, (f ^+ m)`_i = 0}.
Proof.
move=> lt_im f; rewrite coeft0_eq0E => /eqP/coefX_eq0/(_ lt_im).
by rewrite coef_tfpsE !exp_tfps_val coef_trXn => ->; rewrite if_same.
Qed.

Lemma tfpsX_eq0 (n m : nat) :
  n < m -> {in coeft0_eq0, forall f : {tfps R n}, f ^+ m = 0}.
Proof.
move=> le_nm f /coefX_tfps_eq0 H0.
apply/tfpsP => i le_in.
by rewrite coeft0 H0 // (leq_ltn_trans le_in le_nm).
Qed.

Lemma tfpsMX_eq0 n i j : n < i + j ->
  {in coeft0_eq0 &, forall f g : {tfps R n}, f ^+ i * g ^+ j = 0}.
Proof.
move=> lt_n_addij f g f0 g0.
apply tfps_inj.
rewrite mul_tfps_val !exp_tfps_val trXn_mul.
by rewrite trXnMX_eq0 //= -/(_`_0) ?(eqP f0) ?(eqP g0).
Qed.

End MoreExpPolyRing.


(* We state the lemmas with a general f and then with \X       *)
(* because substitution is not a non-commutative ring morphism *)
Lemma coeft_geometric (R : nzSemiRingType) (n m : nat) :
  m <= n -> (\sum_(i < n.+1) \X ^+ i : {tfps R n})`_m = 1.
Proof.
move=> le_mn; pose c1 := fun i : nat => 1 : R.
rewrite (eq_bigr (fun i : 'I_n.+1 => (c1 i) *: \X ^+ i)); first last.
  by move=> i _; rewrite scale1r.
by rewrite !coef_tfps_sumfXi.
Qed.


Section GeometricSeriesRing.

Variables (R : nzRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Lemma geometrictMlf f :
  f \in coeft0_eq0 -> (1 - f) * (\sum_(i < n.+1) f ^+ i) = 1.
Proof.
move=> f0_eq0.
have:= telescope_sumr (fun i => f ^+ i) (leq0n n.+1).
rewrite big_mkord expr0 tfpsX_eq0 // sub0r => /(congr1 (fun x => -x)).
rewrite opprK => {2}<-.
rewrite mulr_sumr -sumrN; apply eq_bigr => /= i _.
by rewrite opprB mulrBl mul1r -exprS.
Qed.

Lemma geometrictMrf f :
  f \in coeft0_eq0 -> (\sum_(i < n.+1) f ^+ i) * (1 - f) = 1.
Proof.
move/geometrictMlf => {2}<-; apply/commr_sym/commr_sum => i _.
apply/commr_sym/commrB; do [exact:commr1 |].
by apply/commr_sym/commrX.
Qed.

Lemma geometrictMl : (\sum_(i < n.+1) \X ^+ i) * (1 - \X) = 1 :> {tfps R n}.
Proof. exact: geometrictMrf (tfpsX_in_coeft0_eq0 _ _). Qed.

End GeometricSeriesRing.


Section GeometricSeriesUnit.

Variables (R : unitRingType) (n : nat).
Implicit Types (c : R) (f g : {tfps R n}).

Lemma geometrictV f :
  f \in coeft0_eq0 -> (1 - f)^-1 = \sum_(i < n.+1) f ^+ i.
Proof.
move=> f0_eq0.
have f1unit : 1 - f \is a GRing.unit.
  by apply: coeft0_eq1_unit; rewrite -coeft0_eq01 rpredN.
by apply: (mulrI f1unit); rewrite geometrictMlf // divrr.
Qed.

Lemma geometrict : (1 - \X)^-1 = \sum_(i < n.+1) \X ^+ i :> {tfps R n}.
Proof. exact: geometrictV (tfpsX_in_coeft0_eq0 _ _). Qed.

Lemma geometrict_1cNV c :
  (1 - c *: \Xo(n))^-1 = \sum_(i < n.+1) c ^+ i *: \X ^+ i.
Proof.
rewrite (eq_bigr (fun i : 'I_n.+1 => (c *: \X)^+ i)); first last.
  by move=> i _; rewrite expr_tfpscX.
exact/geometrictV/coeft0_eq0Z/tfpsX_in_coeft0_eq0.
Qed.

Lemma coef_geometrict_1cNV c m :
  m <= n -> ((1 - c *: \Xo(n))^-1)`_m = c ^+ m.
Proof. by move=> le_mn; rewrite geometrict_1cNV coef_tfps_sumfXi. Qed.

Lemma coef_geometrict_1cV c m :
  m <= n -> ((1 + c *: \Xo(n))^-1)`_m = (-c) ^+ m.
Proof. by rewrite -{1}[c]opprK scaleNr; apply: coef_geometrict_1cNV. Qed.

End GeometricSeriesUnit.


Section DivisionByXSemiRing.

Variable R : nzSemiRingType.

Definition tmulX m (f : {tfps R m}) :=
  [tfps i <= m.+1 => if i == 0%N then 0 else f`_i.-1].
Definition tdivX m (f : {tfps R m}) :=
  [tfps i <= m.-1 => f`_i.+1].

Lemma coeft_tmulX m (f : {tfps R m}) i :
  (tmulX f)`_i = if i == 0%N then 0 else f`_i.-1.
Proof.
rewrite coef_tfps_of_fun; case: i => //= i.
rewrite ltnS; case: leqP => // lt_mi.
by rewrite nth_default // (leq_trans (size_tfps f) lt_mi).
Qed.
Lemma coeft_tdivX m (f : {tfps R m}) i : (tdivX f)`_i = f`_i.+1.
Proof.
rewrite coef_tfps_of_fun; case: leqP => // Hi.
rewrite nth_default // (leq_trans (size_tfps f)) //.
by move: Hi; case m.
Qed.

Lemma trXnt_tmulX m (f : {tfps R m}) n :
  trXnt n.+1 (tmulX f) = tmulX (trXnt n f).
Proof.
apply/tfpsP => i le_in1.
rewrite coef_trXnt le_in1 !coeft_tmulX coef_trXnt.
by case: i le_in1 => [|i]//=; rewrite ltnS => ->.
Qed.
Lemma trXnt_tdivX m (f : {tfps R m.+1}) n :
  trXnt n (tdivX f) = tdivX (trXnt n.+1 f).
Proof.
apply/tfpsP => i le_in1.
by rewrite coef_trXnt le_in1 !coeft_tdivX coef_trXnt ltnS le_in1.
Qed.

Lemma tmulXK m : cancel (@tmulX m) (@tdivX m.+1).
Proof.
move=> p; apply/tfpsP => i Hi.
by rewrite coeft_tdivX coeft_tmulX.
Qed.

Lemma tmulX1 m : tmulX 1 = \X :> {tfps R m.+1}.
Proof.
by apply/tfpsP => [] [|[|i]] _;
  rewrite coeft_tmulX coef_tfpsX // ?coeft1 ?mulr1 ?mulr0.
Qed.
Lemma tdivXX m : tdivX (\X : {tfps R m.+1}) = 1 :> {tfps R m}.
Proof. by rewrite -[RHS]tmulXK tmulX1. Qed.

Fact tmulX_is_semilinear m : semilinear (@tmulX m).
Proof.
by split => [c f | f g]; apply/tfpsP => i _;
    rewrite !(coeftD, coeftZ, coeft_tmulX); case: eqP; rewrite ?mulr0 ?add0r.
Qed.
HB.instance Definition _ m :=
  GRing.isSemilinear.Build
    R {tfps R m} {tfps R m.+1} _ (@tmulX m) (@tmulX_is_semilinear m).

Fact tdivX_is_semilinear m : semilinear (@tdivX m).
Proof.
by split => [c f | f g]; apply/tfpsP => i _;
    rewrite !(coeftD, coeftZ, coeft_tdivX).
Qed.
HB.instance Definition _ m :=
  GRing.isSemilinear.Build
    R {tfps R m} {tfps R m.-1} _ (@tdivX m) (@tdivX_is_semilinear m).

Variable m : nat.
Implicit Type f : {tfps R m}.

Lemma trXn_tmulXE f : trXn m (tfps (tmulX f)) = \X * f.
Proof.
apply/tfpsP => i Hi.
by rewrite coef_trXn coeft_tmulX coef_tfpsXM Hi.
Qed.

Lemma tmulXE f : tmulX f = \X * trXnt m.+1 f.
Proof.
apply/tfpsP => i Hi.
rewrite coeft_tmulX coef_tfpsXM coef_trXnt Hi.
by case: i Hi => //= i /ltnW ->.
Qed.

Lemma tmulXM f (g : {tfps R m.+1}) : (tmulX f) * g = tmulX (f * trXnt m g).
Proof.
apply/tfpsP => [[|i]].
  by rewrite !(coeft0M, coeft_tmulX, coef0_trXn, coef_tfpsE) /= mul0r.
rewrite ltnS => le_im.
rewrite coeft_tmulX /= -/(_`_i.+1) !coeftM ltnS le_im.
rewrite big_ord_recl /= -/(_`_0) coeft_tmulX /= mul0r add0r.
apply eq_bigr => [[j] /=]; rewrite ltnS => le_ji _.
rewrite -/(_`_j.+1) coeft_tmulX /= /bump /= add1n subSS.
by rewrite coef_trXnt (leq_trans (leq_subr _ _) le_im).
Qed.

Lemma coeft_tmulX_exp_lt f i j : i < j -> (tmulX f ^+ j)`_i = 0.
Proof.
elim: j i => [|j IHj] i //; rewrite ltnS => le_ij.
rewrite exprS coeftM; case leqP => // _.
rewrite big_ord_recl big1 ?coeft_tmulX ?mul0r ?add0r // => [[u /=]] lt_ui _.
rewrite {}IHj ?mulr0 // /bump /= add1n.
case: i lt_ui le_ij => // i _ lt_ij.
by rewrite subSS (leq_ltn_trans (leq_subr _ _) lt_ij).
Qed.

Lemma coeft_tmulX_exp f i : i <= m.+1 -> (tmulX f ^+ i)`_i = (f ^+ i)`_0.
Proof.
elim: i => [|i IHi] lt_im1; first by rewrite !expr0 coef1.
rewrite exprS coeftM (leq_trans lt_im1 _) //.
rewrite big_ord_recl coeft_tmulX mul0r add0r.
rewrite big_ord_recl coeft_tmulX /= /bump /= add1n subSS subn0.
rewrite {}IHi ?(ltnW lt_im1) // -!/(_`_0).
rewrite -coeft0M ?rpredX // -exprS.
rewrite big1 ?addr0 // => [[j /= lt_ji]] _.
rewrite !add1n subSS coeft_tmulX_exp_lt ?mulr0 //.
case: i lt_ji {lt_im1} => // i.
by rewrite !ltnS subSS leq_subr.
Qed.

End DivisionByXSemiRing.


Lemma tdivXK (R : nzRingType) m :
  {in coeft0_eq0, cancel (@tdivX R m.+1) (@tmulX R m)}.
Proof.
move=> p Hp.
by apply/tfpsP => [[|i]] Hi; rewrite coeft_tmulX coeft_tdivX // (eqP Hp).
Qed.

Lemma tdivXE (K : idomainType) m :
  {in @coeft0_eq0 K m, forall f, tdivX f = trXn m.-1 (tfps f %/ 'X)}.
Proof.
move=> f.
move/eqP/polyXP; rewrite Pdiv.IdomainUnit.dvdp_eq ?lead_coefX ?unitr1 //.
rewrite /tdivX; move/eqP => h; apply/tfpsP => i Hi.
by rewrite coef_poly coef_trXn ltnS Hi coef_tfpsE [in LHS]h coefMX.
Qed.


Section MapMulfXDivfX.

Variables (K L : nzSemiRingType) (F : {rmorphism K -> L})
  (m : nat) (g : {tfps K m}).

Lemma map_tfps_tmulX : map_tfps F (tmulX g) = tmulX (map_tfps F g).
Proof.
apply/tfpsP => i lt_im1.
rewrite !(coeft_tmulX, coef_map, lt_im1).
by case: i {lt_im1}=> [|j]//=; rewrite rmorph0.
Qed.

Lemma map_tfps_tdivX : map_tfps F (tdivX g) = tdivX (map_tfps F g).
Proof.
apply/tfpsP => i lt_im1.
by rewrite !(coeft_tdivX, coef_map, lt_im1).
Qed.

End MapMulfXDivfX.


Section Derivative.

Variables (R : nzSemiRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Lemma deriv_trXn (p : {poly R}) :
  (tfps (trXn n.+1 p))^`() = tfps (trXn n (p^`())).
Proof.
apply/polyP => i /=.
rewrite coef_deriv !coef_trXn coef_deriv ltnS.
by case: leqP => //; rewrite mul0rn.
Qed.

Fact trXn_deriv (m : nat) (f : {tfps R n}) : n <= m ->
  tfps (trXn m (tfps f)^`()) = (tfps f)^`().
Proof.
move => le_nm; apply/polyP => i /=.
rewrite coef_deriv !coef_trXn coef_deriv.
case: leqP => lt_mi //.
by rewrite coef_tfps (leq_gtF (ltnW (leq_ltn_trans le_nm lt_mi))) mul0rn.
Qed.

Definition deriv_tfps f := [tfps j <= n.-1 => f`_j.+1 *+ j.+1].
Local Notation "f ^` () " := (deriv_tfps f) : tfps_scope.

Lemma coef_deriv_tfps f j : (f^`()%tfps)`_j = f`_j.+1 *+ j.+1.
Proof.
rewrite coef_tfps_of_fun; case: leqP => //.
rewrite coef_tfps [j < n]ltnNge.
by case: n f => /= [|m f ->]; rewrite mul0rn.
Qed.

Lemma val_deriv_tfps f : tfps (f^`()%tfps) = (tfps f)^`()%R.
Proof. by apply/polyP => i; rewrite coef_deriv_tfps coef_deriv. Qed.

Lemma deriv_tfpsE f : f^`()%tfps = trXn n.-1 (tfps f)^`().
Proof. by rewrite -val_deriv_tfps tfpsK. Qed.

Fact deriv_tfps0 : (0 : {tfps R n})^`() = 0.
Proof. by apply tfps_inj; rewrite val_deriv_tfps deriv0. Qed.

Lemma deriv_tfpsC (c : R) : c%:S^`() = 0.
Proof. by apply tfps_inj; rewrite val_deriv_tfps /= val_tfpsC derivC. Qed.

Lemma deriv_tfps1 : 1^`() = 0.
Proof. by rewrite -tfpsC1 deriv_tfpsC. Qed.

Fact derivD_tfps f g : (f + g)^`() = f^`()%tfps + g^`()%tfps.
Proof.
apply/tfpsP => i le_in1.
by rewrite coefD !coef_poly ltnS le_in1 coefD -mulrnDl.
Qed.

Fact derivZ_tfps (c : R) f : (c *: f)^`() = c *: f^`()%tfps.
Proof.
apply/tfpsP => i le_in1.
by rewrite !(coef_poly, coefZ) ltnS le_in1 mulrnAr.
Qed.

Fact deriv_tfps_is_semilinear : semilinear deriv_tfps.
Proof. by split => [c f | f g]; rewrite ?derivZ_tfps ?derivD_tfps. Qed.
HB.instance Definition _ :=
  GRing.isSemilinear.Build
    R {tfps R n} {tfps R n.-1} _ deriv_tfps deriv_tfps_is_semilinear.

(* Tests *)
Example test_deriv_tfps0 : 0^`() = 0.
Proof. by rewrite linear0. Qed.

Example test_deriv_tfpsD f g : (f + g)^`() = f^`()%tfps + g^`()%tfps.
Proof. by rewrite linearD. Qed.

End Derivative.

(* Check derivative on Ring *)
Example test_deriv_tfpsB (R : nzRingType) (n : nat) (f g : {tfps R n}) :
  (f - g)^`() = f^`()%tfps - g^`()%tfps.
Proof. by rewrite linearB. Qed.

Notation "f ^` () " := (deriv_tfps f) : tfps_scope.


Section MoreDerivative.

Variables (R : nzSemiRingType).

Lemma deriv_tfpsX n : \Xo(n.+1)^`() = 1  :> {tfps R n}.
Proof. by rewrite deriv_tfpsE val_tfpsX scale1r derivX trXn1. Qed.

Lemma deriv_trXnt m n (p : {tfps R m}) :
  (trXnt n.+1 p)^`()%tfps = trXnt n p^`()%tfps.
Proof.
rewrite /trXnt deriv_tfpsE deriv_trXn [n.+1.-1]/= trXn_trXn //.
by rewrite -val_deriv_tfps.
Qed.

Lemma deriv_tfps0p (f : {tfps R 0}) : f^`() = 0.
Proof. by rewrite [f]tfps_is_cst deriv_tfpsC. Qed.

Theorem derivM_tfps n (f g : {tfps R n}) :
  (f * g)^`() = f^`()%tfps * (trXnt n.-1 g) + (trXnt n.-1 f) * g^`()%tfps.
Proof.
move: f g; case: n => /= [f g | m f g].
  rewrite [f]tfps_is_cst [g]tfps_is_cst -tfpsCM !deriv_tfpsC.
  by rewrite mul0r mulr0 addr0.
apply/tfps_inj; rewrite !deriv_tfpsE deriv_trXn /=.
by rewrite trXn_trXn // derivM rmorphD !rmorphM.
Qed.

(* Noncommutative version *)
Theorem derivX_tfps_nc n (f : {tfps R n}) k :
  (f ^+ k)^`() =
  \sum_(i < k) (trXnt n.-1 f) ^+ i * f^`()%tfps * (trXnt n.-1 f) ^+ (k.-1 - i).
Proof.
have Hn := leq_pred n.
case: k; first by rewrite !expr0 deriv_tfps1 big_ord0.
elim=> [|k IHk] /=.
  by rewrite !expr1 big_ord_recl big_ord0 addr0 subnn expr0 mul1r mulr1.
rewrite exprS derivM_tfps big_ord_recl subn0 expr0 mul1r rmorphXn /=.
congr (_ + _).
rewrite {}IHk mulr_sumr; apply eq_bigr => i _.
by rewrite /bump /= add1n subSS !mulrA -exprS.
Qed.

End MoreDerivative.


Section DerivativeComRing.

Variables (R : comNzSemiRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Theorem derivX_tfps f k :
  (f ^+ k)^`() = (trXnt n.-1 f) ^+ k.-1 * f^`()%tfps *+ k.
Proof.
have Hn := leq_pred n.
rewrite derivX_tfps_nc -[X in _ *+ X](card_ord k) -sumr_const.
apply eq_bigr => [] [i /= Hi] _.
by rewrite mulrC mulrA -!rmorphXn -rmorphM /= -exprD subnK //; case: k Hi.
Qed.

Theorem derivX_tfps_bis f k :
  (f ^+ k)^`() = f^`()%tfps * (trXnt n.-1 f) ^+ (k.-1) *+ k.
Proof. by rewrite derivX_tfps mulrC. Qed.

End DerivativeComRing.


Section DerivativeUnitRing.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

(* Noncommutative version *)
Theorem derivV_tfps_nc f :
  f \is a GRing.unit ->
  (f ^-1)^`() = - trXnt n.-1 (f^-1) * f^`()%tfps * trXnt n.-1 (f^-1).
Proof.
move=> fU.
have:= erefl (f / f); rewrite {2}divrr // => /(congr1 (@deriv_tfps R n)).
rewrite derivM_tfps -tfpsC1 deriv_tfpsC.
move/eqP; rewrite addrC addr_eq0.
move/eqP/(congr1 (fun x => (trXnt n.-1 f ^-1) * x)).
rewrite {1}trXntV ?leq_pred // mulKr ?(mulrN, mulNr, mulrA) //.
by rewrite unit_tfpsE coef0_trXn.
Qed.

End DerivativeUnitRing.


Section DerivativeComUnitRing.

Variables (R : comUnitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Theorem derivV_tfps f :
  f \is a GRing.unit -> (f ^-1)^`() = - f^`()%tfps / trXnt n.-1 (f ^+ 2).
Proof.
move=> fU.
rewrite derivV_tfps_nc // -mulrA mulrC -mulrA !mulrN mulNr.
rewrite trXntV ?leq_pred // -invrM ?unit_tfpsE ?coef0_trXn //.
by rewrite -{1}rmorphM ?leq_pred.
Qed.

Theorem deriv_div_tfps f g :
  g \is a GRing.unit ->
  (f / g)^`() = (f^`()%tfps * trXnt n.-1 g - trXnt n.-1 f * g^`()%tfps)
                                                    / (trXnt n.-1 (g ^+ 2)).
Proof.
move => fU.
rewrite derivM_tfps derivV_tfps // mulrBl mulrA mulrN mulNr.
congr (_ - _); rewrite -mulrA; congr (_ * _).
rewrite trXntV ?leq_pred // expr2 ?leq_pred //.
rewrite rmorphM ?leq_pred //= => Hn.
by rewrite invrM ?mulrA ?divrr ?div1r // trXnt_unitE.
Qed.

End DerivativeComUnitRing.


Section Primitive.

Variables (R : unitRingType) (n : nat).

Definition prim (p : {poly R}) :=
  \poly_(i < (size p).+1) (p`_i.-1 *+ (i != 0%N) / (i%:R)).

Local Notation "\int p" := (prim p).

Lemma coef_prim (p : {poly R}) (i : nat) :
  (\int p)`_i = if i == 0%N then 0 else p`_i.-1 / (i%:R).
Proof.
case: i => [| i]; first by rewrite eqxx coef_poly invr0 mulr0.
rewrite succnK eqn0Ngt ltn0Sn coef_poly.
rewrite eqn0Ngt ltn0Sn /= -{3}[p]coefK coef_poly ltnS.
by case: (i < size p) => //; rewrite mul0r.
Qed.

Lemma coef0_prim (p : {poly R}) : (\int p)`_0 = 0.
Proof. by rewrite coef_prim eqxx. Qed.

Lemma primC (c : R) : \int (c%:P) = c *: 'X.
Proof.
apply/polyP => i.
rewrite /prim /prim coef_poly size_polyC -[c *: 'X]coefK.
case: (altP (c =P 0)) => [-> | c_neq0 ] /=.
  rewrite scale0r size_poly0 coef_poly ltn0; case: i => [|i].
    by rewrite invr0 mulr0.
    by rewrite coefC.
rewrite coef_poly coefZ coefX.
have -> : size (c *: 'X) = 2%N.
  rewrite -mulr_algl alg_polyC size_Mmonic ?monicX ?polyC_eq0 //.
  by rewrite size_polyX size_polyC c_neq0.
congr if_expr; case: i => [|i]; first by rewrite invr0 !mulr0.
rewrite coefC mulr1n.
case: i => [|i]; first by rewrite !eqxx invr1.
by rewrite /= mul0r mulr0.
Qed.

Lemma primX : \int 'X = (2%:R) ^-1 *: 'X ^+2.
Proof.
rewrite /prim /prim size_polyX ; apply/polyP => i.
rewrite coef_poly coefZ coefXn coefX.
case: i => [|i]; first by rewrite invr0 !mulr0.
rewrite eqn0Ngt ltn0Sn /=; case: i => [ | i ] ; first by rewrite mul0r mulr0.
case: i => [|i]; first by rewrite mul1r mulr1.
by rewrite mulr0.
Qed.

Lemma primXn (m : nat): \int ('X ^+ m) = (m.+1 %:R) ^-1 *: 'X ^+ m.+1.
Proof.
rewrite /prim /prim size_polyXn ; apply/polyP => i.
rewrite coefZ !coefXn coef_poly !coefXn.
case: (altP (i =P m.+1)) => [-> | /negbTE i_neq_Sm ] /=.
  by rewrite ltnSn mulr1 eqxx mul1r.
rewrite /= mulr0 ; case: (i < m.+2) => [] //.
case: (altP (i =P 0%N)) => [-> | /negbTE i_neq0 ] /=.
  by rewrite invr0 mulr0.
move/negbT : i_neq0 ; move/negbT : i_neq_Sm.
case: i => [ // | i ].
by rewrite (inj_eq succn_inj) => /negbTE -> _ ; rewrite mul0r.
Qed.

Fact prim_is_linear : linear prim.
Proof.
move => k p q ; apply/polyP => i.
case: i => [ | i]; first by rewrite coefD coefZ !coef0_prim mulr0 addr0.
by rewrite !(coef_prim, coefD, coefZ) mulrDl -mulrA.
Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build R {poly R} {poly R} _ prim prim_is_linear.


(* tests *)
Fact prim0 : \int 0 = 0.
Proof. exact: linear0. Qed.

Fact primD : {morph prim : p q / p + q}.
Proof. exact: linearD. Qed.

Fact primN : {morph prim : p / - p}.
Proof. exact: linearN. Qed.

Fact primB : {morph prim : p q / p - q}.
Proof. exact: linearB. Qed.


Implicit Types (f g : {tfps R n}).

Fact size_prim_leq f : size (\int (tfps f)) <= n.+2.
Proof.
apply: (leq_trans (size_poly _ _) _); rewrite ltnS.
exact: size_tfps.
Qed.
Definition prim_tfps f := MkTfps (size_prim_leq f).

Lemma coef_prim_tfps f i : (prim_tfps f)`_i = (\int (tfps f))`_i.
Proof. by []. Qed.

Fact prim_tfps_is_linear : linear prim_tfps.
Proof.
move=> k p q; apply/tfpsP => i lt_in1.
rewrite coefD coefZ !coef_prim.
case: i lt_in1 => [|i]/=; first by rewrite mulr0 addr0.
rewrite ltnS => lt_in.
by rewrite coefD coefZ mulrDl mulrA.
Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build
    R {tfps R n} {tfps R n.+1} _ prim_tfps prim_tfps_is_linear.


(* tests *)
Example prim_tfps0 : prim_tfps 0 = 0.
Proof. exact: linear0. Qed.

Example prim_tfpsD : {morph prim_tfps : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma coef0_prim_tfps f : (prim_tfps f)`_0 = 0.
Proof. by rewrite coef_poly eqxx mulr0n invr0 mulr0. Qed.

End Primitive.

Notation "\int f" := (prim_tfps f) : tfps_scope.


Section MoreCompPoly.

Variable (R : nzSemiRingType).
Implicit Type (p q : {poly R}).

Lemma trXn_comp_polyr n p q :
  trXn n (p \Po q) = trXn n (p \Po (tfps (trXn n q))).
Proof.
apply/trXnP => i le_in.
rewrite !coef_comp_poly; apply eq_bigr => j _; congr (_ * _).
have /= := (congr1 (fun x => (tfps x)`_i) (exp_tfps_val (trXn n q) j)).
rewrite !coef_trXn le_in => <-.
by rewrite -rmorphXn coef_trXn le_in.
Qed.

Lemma trXn_comp_polyl n p q :
  q`_0 = 0 -> trXn n (p \Po q) = trXn n ((tfps (trXn n p)) \Po q).
Proof.
move => q0_eq0; apply/trXnP => i le_in.
rewrite -{1}(poly_cat p n.+1) comp_polyD coefD !trXnE.
rewrite [X in _ + X](_ : _ = 0) ?addr0 //.
rewrite coef_comp_poly; apply: big1 => [] [j /=] le_jsz _.
rewrite coefXnM; case: ltnP => [] Hi; first by rewrite mul0r.
by rewrite coefX_eq0 ?mulr0 // (leq_ltn_trans le_in Hi).
Qed.

End MoreCompPoly.


Section Composition.

Variables (R : nzSemiRingType) (n : nat).

Definition comp_tfps m (f g : {tfps R m}) :=
  if f \in coeft0_eq0
  then trXn m (tfps g \Po tfps f)
  else (g`_0%N)%:S.  (* avoid particular cases (e.g. associativity) *)

Local Notation "f \oT g" := (comp_tfps g f) : tfps_scope.


Lemma comp_tfps_coef0_neq0 m (f g : {tfps R m}) :
  g \notin coeft0_eq0 -> f \oT g = (f`_0%N)%:S.
Proof. by move/negbTE => p0_neq0; rewrite /comp_tfps p0_neq0. Qed.

Lemma comp_tfps_coeft0_eq0 m (f g : {tfps R m}) :
  g \in coeft0_eq0 -> f \oT g = trXn m (tfps f \Po tfps g).
Proof. by move => f0_eq0 ; rewrite /comp_tfps f0_eq0. Qed.

Lemma comp_tfps0l m (f : {tfps R m}) : 0 \oT f = 0.
Proof.
case (boolP (f \in coeft0_eq0)) => [f0_eq0 | f0_neq0].
- by rewrite comp_tfps_coeft0_eq0 // comp_poly0 rmorph0.
- by rewrite comp_tfps_coef0_neq0 // coeft0 tfpsC0.
Qed.

Lemma comp_tfps0r m (f : {tfps R m}) : f \oT 0 = (f`_0)%:S.
Proof.
rewrite comp_tfps_coeft0_eq0 ?rpred0 ?zero_in_coeft0_eq0 // comp_poly0r.
by rewrite -tfpsCE -coef_tfpsE.
Qed.

Implicit Types (f g h : {tfps R n}) (p q : {poly R}).

Lemma coef0_comp_tfps f g : (f \oT g)`_0 = f`_0.
Proof.
rewrite /comp_tfps; case: (boolP (_ \in _)); last by rewrite coeftC.
rewrite coeft0_eq0E coef_trXn {-2}[0%N]lock /= -lock => /eqP g0_eq0.
rewrite coef_comp_poly.
case Hsz : (size (tfps f)) => [|sz].
  by rewrite big_ord0 nth_default // leqn0 size_tfpsE Hsz.
rewrite big_ord_recl big1.
- by rewrite addr0 -coef_tfpsE expr0 coef1 mulr1.
- move=> [i /= Hi] _.
  by rewrite /bump /= -/(_`_0) add1n exprSr coef0M -coef_tfpsE g0_eq0 !mulr0.
Qed.

Lemma coef_comp_tfps_leq k l f g :
  g \in coeft0_eq0 -> k <= l -> k <= n ->
  (f \oT g)`_k = \sum_(i < l.+1) f`_i * (g ^+ i)`_k.
Proof.
move=> g0 le_kl le_kn.
rewrite (comp_tfps_coeft0_eq0 _ g0).
rewrite coef_trXn coef_comp_poly le_kn.
have co_is0 i : minn (size f) k.+1 <= i -> f`_i * (g ^+ i)`_k = 0.
  rewrite geq_min => /orP [/(nth_default _) ->| lt_ki]; first by rewrite mul0r.
  rewrite !coef_tfpsE !exp_tfps_val coef_trXn le_kn.
  by rewrite coefX_eq0 ?mulr0 ?(eqP g0).
rewrite [RHS](bigID (fun i : 'I_ _ => i < minn (size f) k.+1)) /=.
rewrite [LHS](bigID (fun i : 'I_ _ => i < minn (size f) k.+1)) /=.
rewrite [X in _ + X]big1 ?addr0; first last.
  move=> [i /=] _; rewrite -leqNgt => /co_is0 /=.
  by rewrite !coef_tfpsE !exp_tfps_val coef_trXn le_kn.
rewrite [X in _ + X]big1 ?addr0; first last.
  by move=> [i /=] _; rewrite -leqNgt => /co_is0.
rewrite -(big_ord_widen _ (fun i => f`_i * (g ^+ i)`_k)); first last.
  exact: (leq_trans (geq_minr _ _)).
rewrite -(big_ord_widen _ (fun i => f`_i * (tfps g ^+ i)`_k)) ?geq_minl //.
by apply eq_bigr => i _; rewrite !coef_tfpsE !exp_tfps_val coef_trXn le_kn.
Qed.

Lemma coef_comp_tfps k f g :
  g \in coeft0_eq0 -> (f \oT g)`_k = \sum_(i < k.+1) f`_i * (g ^+ i)`_k.
Proof.
move=> g0.
case: (leqP k n) => [le_kn | lt_nk]; first exact: coef_comp_tfps_leq.
rewrite (comp_tfps_coeft0_eq0 _ g0) coef_trXn ltn_geF //.
apply/esym/big1 => [[l /=]]; rewrite ltnS => Hl _.
by rewrite [_`_k]coef_tfps /= (ltn_geF lt_nk) mulr0.
Qed.

Lemma trXnt_comp m f g :
  m <= n -> trXnt m (f \oT g) = (trXnt m f) \oT (trXnt m g).
Proof.
case (boolP (g \in coeft0_eq0)) => [g0_eq0 | g0_neq0] le_mn.
- rewrite !comp_tfps_coeft0_eq0 ?coeft0_eq0_trXnt //.
  rewrite /trXnt -trXn_comp_polyr -trXn_comp_polyl ?(eqP g0_eq0) //=.
  by rewrite trXn_trXn.
- rewrite !comp_tfps_coef0_neq0 ?coeft0_eq0_trXnt //.
  by rewrite trXntC coef_trXn.
Qed.

Lemma coeft0_eq0_comp f g : (f \oT g \in coeft0_eq0) = (f \in coeft0_eq0).
Proof. by rewrite !coeft0_eq0E coef0_comp_tfps. Qed.

Lemma coeft0_eq1_comp f g : (f \oT g \in coeft0_eq1) = (f \in coeft0_eq1).
Proof. by rewrite !coeft0_eq1E coef0_comp_tfps. Qed.

Lemma comp_tfpsC f (c : R) : c%:S \oT f = c%:S.
Proof.
case (boolP (f \in coeft0_eq0)) => [f0_eq0 | f0_neq0].
- by rewrite comp_tfps_coeft0_eq0 //= val_tfpsC comp_polyC -tfpsCE.
- by rewrite comp_tfps_coef0_neq0 ?coeftC.
Qed.

Lemma comp_tfps1 f : 1 \oT f = 1.
Proof. by rewrite -tfpsC1 comp_tfpsC. Qed.

Lemma comp_tfpsCf f (c : R) : f \oT (c%:S) = (f`_0)%:S.
Proof.
have [->| c_neq0] := eqVneq c 0.
  by rewrite tfpsC0 comp_tfps0r.
by rewrite comp_tfps_coef0_neq0 // coeft0_eq0E coeftC.
Qed.

Fact comp_tfps_is_semilinear (f : {tfps R n}) : semilinear (comp_tfps f).
Proof.
split=> [/= r g | /= g h]; case: (boolP (f \in coeft0_eq0)) => Hf.
- by rewrite !comp_tfps_coeft0_eq0 //= !linearZ.
- rewrite !comp_tfps_coef0_neq0 // coeftZ.
  by rewrite tfpsCM -alg_tfpsC mulr_algl.
- by rewrite !comp_tfps_coeft0_eq0 //= !linearD.
- by rewrite !comp_tfps_coef0_neq0 // coeftD raddfD.
Qed.
HB.instance Definition _ (f : {tfps R n}) :=
  GRing.isSemilinear.Build
    R {tfps R n} {tfps R n} _ (comp_tfps f) (comp_tfps_is_semilinear f).


Lemma comp_tfpsXr f : f \oT \X = f.
Proof.
case: n f => [|n'] f.
  by rewrite tfps0X // comp_tfps0r {2}(tfps_is_cst f).
rewrite comp_tfps_coeft0_eq0 ?tfpsX_in_coeft0_eq0 //.
by rewrite val_tfpsSX comp_polyXr tfpsK.
Qed.

Lemma comp_tfpsX : {in coeft0_eq0, forall f, \X \oT f = f}.
Proof.
case: n => [|n'] f.
  rewrite tfps0X // comp_tfps0l {2}(tfps_is_cst f) => /eqP ->.
  by rewrite tfpsC0.
move=> /comp_tfps_coeft0_eq0 ->.
by rewrite val_tfpsSX comp_polyX tfpsK.
Qed.

Lemma comp_tfpsXn i : {in coeft0_eq0, forall f, \X ^+ i \oT f = f ^+ i}.
Proof.
move=> f Hf; apply/tfpsP => j Hj.
rewrite coef_comp_tfps //.
case: (ltnP i j.+1) => [lt_ij1 | lt_ji].
- rewrite (bigD1 (Ordinal lt_ij1)) //= big1 ?addr0.
  + rewrite ltnS in lt_ij1.
    by rewrite coef_tfpsXn eqxx (leq_trans lt_ij1 Hj) mul1r.
  + move=> [k Hk]; rewrite -val_eqE /= coef_tfpsXn => /negbTE ->.
    by rewrite andbF mul0r.
- rewrite coefX_tfps_eq0 // big1 // => [] [k /=]; rewrite ltnS => Hk _.
  by rewrite coef_tfpsXn (ltn_eqF (leq_ltn_trans Hk lt_ji)) andbF mul0r.
Qed.

End Composition.

Notation "f \oT g" := (comp_tfps g f) : tfps_scope.


Section CompUnitRing.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Lemma comp_tfps_unitE f g :
  ((f \oT g) \is a GRing.unit) = (f \is a GRing.unit).
Proof. by rewrite !unit_tfpsE coef0_comp_tfps. Qed.

End CompUnitRing.


Section CompComSemiRing.

Variables (R : comNzSemiRingType) (n : nat).
Implicit Types (f g h : {tfps R n}) (p : {poly R}).

Fact comp_tfps_is_monoid_morphism f : monoid_morphism (comp_tfps f).
Proof.
split => /= [|g1 g2]; first exact: comp_tfps1.
case: (boolP (f \in coeft0_eq0)) => Hf.
- rewrite !comp_tfps_coeft0_eq0 // mul_tfps_val /=.
  rewrite -trXn_comp_polyl -?coef_tfpsE ?(eqP Hf) //.
  rewrite rmorphM /= -trXn_mul /=.
  by rewrite -[RHS]tfpsK mul_tfps_val /= trXn_trXn.
- by rewrite !comp_tfps_coef0_neq0 // coeft0M -rmorphM.
Qed.
HB.instance Definition _ f :=
  GRing.isMonoidMorphism.Build
    {tfps R n} {tfps R n} (comp_tfps f) (comp_tfps_is_monoid_morphism f).

Lemma comp_tfpsA f g h : f \oT (g \oT h) = (f \oT g) \oT h.
Proof.
case (boolP (h \in coeft0_eq0)) => [h0_eq0 | h0_neq0]; first last.
  rewrite !(comp_tfps_coef0_neq0 _ h0_neq0).
  by rewrite comp_tfpsCf coef0_comp_tfps.
case (boolP (g \in coeft0_eq0)) => [g0_eq0 | g0_neq0]; first last.
  by rewrite !(comp_tfps_coef0_neq0 f) ?comp_tfpsC // coeft0_eq0_comp.
rewrite comp_tfps_coeft0_eq0 ?coeft0_eq0_comp //.
rewrite !comp_tfps_coeft0_eq0 //.
rewrite -trXn_comp_polyr comp_polyA -trXn_comp_polyl //.
by move: h0_eq0; rewrite coeft0_eq0E => /eqP.
Qed.

Lemma coef_comp_poly_cX p c i : (p \Po (c *: 'X))`_i = c ^+ i * p`_i.
Proof.
rewrite coef_comp_poly.
rewrite (eq_bigr (fun j : 'I_ _ =>
                    c ^+ j * p`_j * (i == j)%:R)) => [|j _]; first last.
  rewrite -mulr_algl exprMn_comm; last exact: commr_polyX.
  by rewrite -in_algE -rmorphXn mulr_algl coefZ coefXn mulrA [p`_j * _]mulrC.
case: (ltnP i (size p)) => [lt_isz | le_szi].
- rewrite (bigD1 (Ordinal lt_isz)) //= big1 ?addr0; first last.
    move=> [j /= lt_jsz]; rewrite -val_eqE /= eq_sym => /negbTE ->.
    by rewrite mulr0.
  by rewrite eqxx mulr1.
- rewrite nth_default // mulr0 big1 // => [] [j /= lt_jsz] _.
  by rewrite (gtn_eqF (leq_trans lt_jsz le_szi)) mulr0.
Qed.

Lemma coef_comp_tfps_cX f c i : (f \oT (c *: \X))`_i = c ^+ i * f`_i.
Proof.
case: n f => [|n'] f.
  rewrite coef_tfps [in RHS]coef_tfps leqn0.
  case: i => [|i] /=; last by rewrite mulr0.
  by rewrite -!/(_`_0) expr0 mul1r coef0_comp_tfps.
case: (leqP i n'.+1) => [lt_in1 | lt_n1i]; first last.
  rewrite coef_tfps (ltn_geF lt_n1i) nth_default ?mulr0 //.
  exact: (leq_trans (size_tfps f) lt_n1i).
rewrite -coef_comp_poly_cX.
rewrite comp_tfps_coeft0_eq0 ?coeft0_eq0Z ?tfpsX_in_coeft0_eq0 //.
by rewrite coef_trXn lt_in1 linearZ /= val_tfpsX scale1r.
Qed.

Theorem deriv_tfps_comp f g :
  f \in coeft0_eq0 ->
  (g \oT f)^`() = (g^`()%tfps \oT trXnt n.-1 f) * f^`()%tfps.
Proof.
rewrite !deriv_tfpsE //.
move: f g; case: n => [|m] f g f0_eq0.
  rewrite [f]tfps_is_cst [g]tfps_is_cst /trXnt comp_tfpsC.
  by rewrite !val_tfpsC !derivC trXn0 mulr0.
rewrite -[RHS]tfpsK [m.+1.-1]/=.
rewrite /= !comp_tfps_coeft0_eq0 ?coeft0_eq0_trXnt //.
rewrite deriv_trXn !trXn_trXn // deriv_comp.
rewrite -[LHS]trXn_mul /=; congr (trXn _ (_ * _)).
by rewrite -trXn_comp_polyr -trXn_comp_polyl ?(eqP f0_eq0).
Qed.

End CompComSemiRing.


Section LagrangeFixPoint.

Variables R : unitRingType.

Variable n : nat.
Variable g : {tfps R n}.
Hypothesis gU : g \is a GRing.unit.


(** We iterate f := X (g o f) until fixpoint is reached. *)
(** At each step, the precision is incremented.          *)
Fixpoint lagriter ord : {tfps R ord} :=
  if ord is ord'.+1 then tmulX (trXnt ord' g \oT lagriter ord') else 0.
Definition lagrfix := lagriter n.+1.

Lemma coeft0_eq0_lagriter ord : lagriter ord \in coeft0_eq0.
Proof.
by rewrite coeft0_eq0E; case: ord => [|i]; rewrite ?coeft0 ?coeft_tmulX.
Qed.
Lemma coeft0_eq0_lagrfix : lagrfix \in coeft0_eq0.
Proof. exact: coeft0_eq0_lagriter. Qed.

Lemma trXnt_lagriter i j : i <= j -> trXnt i (lagriter j) = lagriter i.
Proof.
move=> /subnKC <-; elim: (j - i)%N => {j} [|j IHj].
  by rewrite addn0 trXnt_id.
rewrite addnS -(trXnt_trXnt _ (leq_addr j i)) -{}IHj; congr trXnt.
elim: {i j} (i + j)%N => [|i IHi] /=.
  apply tfpsP => i; rewrite leqn0 => /eqP ->.
  by rewrite coef_trXnt leqnn coeft_tmulX coeft0.
by rewrite !(trXnt_tmulX, trXnt_comp, trXnt_trXnt) ?IHi.
Qed.

Lemma lagrfixP : lagrfix = tmulX (g \oT trXnt n lagrfix).
Proof.
rewrite /lagrfix.
suff rec ord : ord <= n ->
     lagriter ord.+1 = tmulX (trXnt ord g \oT trXnt ord (lagriter ord.+1)).
  by rewrite [LHS](rec n (leqnn n)) trXnt_id.
elim: ord => [_ | m IHm /ltnW{}/IHm IHm]; apply tfpsP => i.
  case: i => [_|i]; first by rewrite !coeft_tmulX.
  rewrite ltnS leqn0 => /eqP ->.
  rewrite !coeft_tmulX /= -!/(_`_0).
  by rewrite comp_tfps0r !coeftC coef0_comp_tfps.
case: i => [_|i]; first by rewrite !coeft_tmulX.
rewrite ltnS => le_im1 /=.
rewrite -!/(_`_ i.+1) !coeft_tmulX /= -/(lagriter m.+1) -!/(_`_ i.+1).
have lag0 := coeft0_eq0_lagriter m.+1.
move: (lagriter m.+1) => LR in IHm lag0 *.
have Xlag0 : trXnt m.+1 (tmulX (trXnt m.+1 g \oT LR)) \in coeft0_eq0.
  by rewrite coeft0_eq0E coef_trXnt coeft_tmulX.
rewrite !coef_comp_tfps //; apply eq_bigr => k _; congr (_ * _).
rewrite {}[in LHS]IHm -rmorphXn coef_trXnt le_im1.
set X :=  (_ ^+ k in RHS); have -> : X`_i = (trXnt m.+1 X)`_i.
  by rewrite {}/X coef_trXnt le_im1.
rewrite {}/X rmorphXn /= trXnt_tmulX trXnt_comp; last exact: leqnSn.
by rewrite trXnt_trXnt.
Qed.

Lemma lagrfix_divP : tdivX lagrfix = g \oT trXnt n lagrfix.
Proof. by rewrite {1}lagrfixP tmulXK. Qed.
Lemma tdivX_lagrfix_unit : tdivX lagrfix \is a GRing.unit.
Proof. by rewrite lagrfix_divP unit_tfpsE coef0_comp_tfps -unit_tfpsE. Qed.

End LagrangeFixPoint.


Section Lagrange.

Variables R : comUnitRingType.
Variable n : nat.

Section Inverse.

Variable g : {tfps R n}.
Hypothesis gU : g \is a GRing.unit.

Lemma lagrfix_inv f :
  f \in coeft0_eq0 -> f = tmulX (g \oT trXnt n f) -> (tmulX g^-1) \oT f = \X.
Proof.
move=> f0 Heq.
have tinv0 : trXnt n f \in coeft0_eq0 by rewrite coeft0_eq0_trXnt.
rewrite tmulXE rmorphM /= comp_tfpsX //.
rewrite {1}Heq tmulXM trXnt_comp // trXnt_trXnt // trXnt_id.
rewrite (rmorphV _ gU) //= divrr ?tmulX1 //.
by rewrite unit_tfpsE coef0_comp_tfps -unit_tfpsE.
Qed.

Lemma lagrfix_invPr : (tmulX g^-1) \oT lagrfix g = \X.
Proof. exact: (lagrfix_inv (coeft0_eq0_lagrfix g) (lagrfixP g)). Qed.

End Inverse.

Lemma lagriter_trXnt (f : {tfps R n}) i m :
  i <= m.+1 -> lagriter (trXnt m f) i = lagriter f i.
Proof.
elim: i => [|i IHi] le_im //=.
by rewrite IHi ?trXnt_trXnt // ltnW.
Qed.

Lemma trXnt_lagrfix (f : {tfps R n}) m :
  m <= n -> trXnt m.+1 (lagrfix f) = lagrfix (trXnt m f).
Proof.
rewrite /lagrfix => le_mn.
by rewrite trXnt_lagriter ?(leq_ltn_trans lt_mn) // lagriter_trXnt.
Qed.


Implicit Types (f g : {tfps R n.+1}).

Definition lagrunit f := (f \in coeft0_eq0) && (tdivX f \is a GRing.unit).
Definition lagrinv f : {tfps R n.+1} := lagrfix (tdivX f)^-1.

Lemma lagrfixE (f : {tfps R n}) : lagrfix f = lagrinv (tmulX f^-1).
Proof. by rewrite /lagrinv tmulXK invrK. Qed.

Lemma coef1_comp_tfps f g :
  f \in coeft0_eq0 -> g \in coeft0_eq0 -> (f \oT g)`_1 = f`_1 * g`_1.
Proof.
move=> f0 g0.
rewrite coef_comp_tfps // big_ord_recl (eqP f0) mul0r add0r.
by rewrite big_ord_recl /= big_ord0 /bump /= -!/(_`_ 1) !add1n addr0.
Qed.

Lemma tdivX_unitE f : (tdivX f \is a GRing.unit) = (f`_1 \is a GRing.unit).
Proof. by rewrite unit_tfpsE coeft_tdivX. Qed.

Lemma lagrunit_comp : {in lagrunit &, forall f g, lagrunit (f \oT g) }.
Proof.
rewrite /lagrunit => f g /andP [f0 f1] /andP [g0 g1].
rewrite coeft0_eq0_comp f0 /=.
rewrite unit_tfpsE coeft_tdivX /= -/(_`_1).
by rewrite coef1_comp_tfps // unitrM -!tdivX_unitE f1 g1.
Qed.

Lemma lagrunitV : {in lagrunit, forall f, lagrunit (lagrinv f) }.
Proof.
rewrite /lagrunit => f /andP [H0 H1].
by rewrite coeft0_eq0_lagrfix tdivX_lagrfix_unit // unitrV.
Qed.

Lemma lagrinvPr : {in lagrunit, forall f, f \oT (lagrinv f) = \X }.
Proof.
rewrite /lagrinv/lagrunit => f /andP [H0 H1].
have /lagrfix_invPr : (tdivX f)^-1 \is a GRing.unit by rewrite unitrV.
by rewrite invrK tdivXK.
Qed.

Lemma lagrinvPl : {in lagrunit, forall f, (lagrinv f) \oT f = \X }.
Proof.
move=> f Hf.
(** Standard group theoretic argument: right inverse is inverse *)
have idemp_neutral g : lagrunit g -> g \oT g = g -> g = \X.
  move=> Hinv Hid; rewrite -(comp_tfpsXr g) // -(lagrinvPr Hinv).
  by rewrite comp_tfpsA {}Hid.
apply idemp_neutral; first exact: lagrunit_comp (lagrunitV Hf) Hf.
rewrite comp_tfpsA -[X in (X \oT f) = _]comp_tfpsA lagrinvPr //.
by rewrite comp_tfpsXr.
Qed.

Lemma lagrinvPr_uniq f g :
  f \in lagrunit -> f \oT g = \X -> g = lagrinv f.
Proof.
move=> f_lag Heq.
have g0 : g \in coeft0_eq0.
  rewrite -[_ \in _]negbK; apply/negP => H.
  move: Heq; rewrite comp_tfps_coef0_neq0 //.
  move => /(congr1 (fun s : {tfps _ _} => s`_1)).
  rewrite coef_tfpsX coeftC /= => /esym/eqP.
  by rewrite mulr1 oner_eq0.
(** Standard group theoretic argument: right inverse is uniq *)
move: Heq => /(congr1 (fun s => lagrinv f \oT s)).
by rewrite comp_tfpsA lagrinvPl // comp_tfpsX // comp_tfpsXr.
Qed.

Lemma lagrinvPl_uniq f g :
  f \in lagrunit -> g \oT f = \X -> g = lagrinv f.
Proof.
move=> f_lag /(congr1 (fun s => s \oT lagrinv f)).
(** Standard group theoretic argument: left inverse is uniq *)
rewrite -comp_tfpsA lagrinvPr // comp_tfpsXr // comp_tfpsX //.
exact: coeft0_eq0_lagrfix.
Qed.

Lemma lagrinvK : {in lagrunit, involutive lagrinv}.
Proof.
(** Standard group theoretic argument: inverse is involutive *)
move=> f Hf.
by apply/esym/lagrinvPl_uniq; [apply: lagrunitV | apply: lagrinvPr].
Qed.

Lemma lagrfix_invPl :
  {in GRing.unit, forall g : {tfps R n}, lagrfix g \oT tmulX g^-1 = \X}.
Proof.
move=> g gU.
rewrite lagrfixE; apply: lagrinvPl.
rewrite /lagrunit unfold_in coeft0_eq0E coeft_tmulX /= eqxx /=.
by rewrite tdivX_unitE coeft_tmulX /= -/(_`_0) -unit_tfpsE unitrV.
Qed.

Lemma lagrfix_uniq (g : {tfps R n}) : g \in GRing.unit ->
  forall f, f = tmulX (g \oT trXnt n f) -> f = lagrfix g.
Proof.
move=> gU f Hf.
rewrite lagrfixE; apply lagrinvPr_uniq.
- by rewrite /lagrunit unfold_in coeft0_eq0E coeft_tmulX tmulXK unitrV /= eqxx.
- by apply: lagrfix_inv => //; rewrite Hf coeft0_eq0E coeft_tmulX.
Qed.

End Lagrange.


Section LagrangeTheorem.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.

(* TODO: nat_unit is not needed here *)
Lemma tmulX_deriv_expE n (g : {tfps R n.+1}) i :
  (g ^+ i.+1 - tmulX g^`()%tfps * g ^+ i)`_i.+1 = 0.
Proof.
rewrite tmulXM mulrC rmorphXn /= -/(_`_i.+1).
apply (mulrI (nat_unit i)); rewrite mulr0 -!coeftZ scalerBr.
rewrite -linearZ /= !scaler_nat -(derivX_tfps g i.+1) -/(_`_i.+1).
by rewrite coeftB coeft_tmulX coef_deriv_tfps /= -!/(_`_i.+1) coeftMn subrr.
Qed.

Theorem Lagrange_Bürmann_exp n (g : {tfps R n}) i k :
  g \in GRing.unit ->
  k <= i <= n.+1 -> ((lagrfix g) ^+ k)`_i *+ i = (g ^+ i)`_(i - k) *+ k.
Proof.
(* We first deal with trivial cases                                    *)
case: n g => [|n] g gU.
  rewrite /lagrfix /= (tfps_is_cst g) comp_tfps0r.
  move: gU; rewrite unit_tfpsE; move: (g`_0) => g0 {g} gU.
  rewrite trXntC coeftC /=.
  case: k => [|[|k]].
  - rewrite mulr0n expr0 coef1.
    by case: i => [|i]/= _; rewrite ?mulr0n ?mul0rn.
  - move=> /andP [le1i lei1].
    have {le1i lei1} -> : i = 1%N by apply anti_leq; rewrite le1i lei1.
    by rewrite !expr1 !mulr1n subSS coeft_tmulX /=.
  - move=> /andP [leki lei1].
    by have:= leq_trans leki lei1; rewrite ltnS ltn0.
case: k i => [|k] [|i]; rewrite ?(expr0, subn0, coef1, mulr0n, mul0rn) //.
rewrite subSS !ltnS => /andP [le_ki le_in].
have Xg0 : tmulX g^-1 \in coeft0_eq0 by rewrite coeft0_eq0E coeft_tmulX.
(* The RHS is ((\X ^+ k.+1)^`() * g ^+ i.+1)`_i                        *)
have:= congr1 (fun s => (s ^+ k.+1)^`()) (lagrfix_invPl gU).
rewrite -rmorphXn /= {1}(tfps_def (lagrfix g ^+ k.+1)) rmorph_sum /=.
move: (lagrfix g ^+ k.+1) => LGRF.
rewrite raddf_sum /= derivX_tfps deriv_tfpsX mulr1 /= trXnt_tfpsX.
move=> /(congr1 (fun s => (s * g ^+ i.+1)`_i)).
rewrite mulrnAl -mulrnAr.
rewrite coef_tfpsXnM (leq_gtF le_ki) le_in coeftMn => <- {k le_ki}.
rewrite mulr_suml coeft_sum -/(_`_i.+1).
(* We extract the i.+1 term of the sum                                 *)
have Hi : i.+1 < n.+3 by rewrite ltnS (leq_ltn_trans le_in).
rewrite (bigD1 (Ordinal Hi)) //= -/(_`_i.+1).
move: (LGRF`_i.+1) => Co.
rewrite !linearZ /= -scalerAl coeftZ rmorphXn /= comp_tfpsX //.
rewrite derivX_tfps /= !mulrnAl coeftMn /= mulrnAr -mulrnAl.
rewrite -mulrA coeftM le_in big_ord_recr /=.
rewrite subnn coeft0M coef_deriv_tfps coeft_tmulX /= -!/(_`_0) mulr1n.
rewrite {2}exprS coeft0M [g^-1`_0 * _]mulrA coeft0V //.
rewrite mulVr -?unit_tfpsE // mul1r.
rewrite -rmorphXn /= coef_trXnt le_in -!/(_`_0).
rewrite coeft_tmulX_exp ?(leq_trans le_in) //.
rewrite -coeft0M exprVn mulVr ?rpredX // coef1 /=.
(* All the other terms vanish.                                         *)
rewrite !big1 ?add0r ?addr0 ?mulr1 //; first last.
  move=> [j /= lt_ji] _.
  rewrite coef_trXnt (leq_trans (ltnW lt_ji) le_in).
  by rewrite coeft_tmulX_exp_lt // mul0r.
move=> [j Hj]; rewrite -val_eqE /= {Hi} => Hneq.
rewrite !linearZ /= -scalerAl coeftZ rmorphXn /= comp_tfpsX //.
rewrite [X in _ * X](_ : _ = 0) ?mulr0 // {LGRF}.
(* We don't have the notion of residue. As a consequence the following *)
(* is a little bit convoluted...                                       *)
(* First, lets get rid of the first tmulX...                           *)
rewrite derivX_tfps /= mulrnAl coeftMn.
case: j Hneq Hj => // j /=; rewrite eqSS !ltnS => Hij le_jn1.
rewrite [X in X *+ _](_ : _ = 0) ?mul0rn //.
rewrite tmulXE derivM_tfps deriv_tfpsX mul1r /= deriv_trXnt.
rewrite trXnt_tfpsX trXnt_trXnt ?ltnS // trXnt_id.
rewrite -[X in _ + X]tmulXE.
rewrite -rmorphXn /= exprMn_comm; last exact: (commr_sym (commr_tfpsX _)).
rewrite !rmorphM !rmorphXn /= trXnt_tfpsX trXnt_trXnt // trXnt_id.
rewrite -!mulrA coef_tfpsXnM le_in; case ltnP => //= le_ji.
(* We rearange to have everything expressed in [i - j]                 *)
have {Hij le_ji} lt_ji : j < i by rewrite ltn_neqAle Hij le_ji.
rewrite mulrC -mulrA exprVn -exprB ?(leq_trans (ltnW lt_ji)) //.
rewrite (subSn (ltnW _)) // exprS mulrA mulrDl mulVr //.
move: lt_ji; rewrite -subn_gt0.
case: (i - j)%N (leq_subr j i) => // d lt_di _ {j le_jn1}.
(* We gather all the [g] and conclude                                  *)
rewrite tmulXM derivV_tfps //= -/(_`_d.+1).
rewrite !mulNr raddfN /= -/(_`_d.+1) -trXntV // -mulrA -trXntM // -!tmulXM.
rewrite mulrDl mul1r mulNr -mulrA.
rewrite {2}exprS !mulrA -[_ * g]mulrA -expr2 divrK ?unitrX //.
exact: tmulX_deriv_expE.
Qed.

Theorem coeft_lagrfix n (g : {tfps R n}) i :
  g \in GRing.unit -> (lagrfix g)`_i.+1 = (g ^+ i.+1)`_i / i.+1%:R.
Proof.
move/Lagrange_Bürmann_exp => HL.
case: (ltnP i n.+1) => [lt_in1 | le_ni]; first last.
  by rewrite coef_tfps (leq_gtF le_ni) coef_tfps (ltn_geF le_ni) mul0r.
have /HL : 1 <= i.+1 <= n.+1 by rewrite lt_in1.
rewrite subSS subn0 mulr1n expr1 => <-.
by rewrite -[X in X / _]mulr_natr mulrK.
Qed.

Theorem Lagrange_Bürmann n (g : {tfps R n}) (h : {tfps R n.+1}) i  :
  g \in GRing.unit ->
  (h \oT lagrfix g)`_i.+1 = (h^`()%tfps * g ^+ i.+1)`_i / i.+1%:R.
Proof.
move=> gU.
have lg0 := coeft0_eq0_lagrfix g.
(* We argue by linearity from the previous statement *)
rewrite (tfps_def h) !(raddf_sum, mulr_suml, coeft_sum).
apply eq_bigr => [[k /=]]; rewrite ltnS => le_kn2 _.
rewrite !linearZ /= -/(_`_i.+1) -scalerAl !coeftZ -mulrA; congr (_ * _).
case: k le_kn2 => [_|k lt_kn2].
  (* When k = 0 the result is trivial *)
  by rewrite expr0 comp_tfps1 coef1 deriv_tfps1 mul0r coef0 mul0r.
rewrite rmorphXn /= comp_tfpsX // -/(_`_i.+1).
rewrite [LHS]coef_tfps [in RHS]coef_tfps ltnS.
case: leqP => [le_in1|_]; last by rewrite mul0r.
case: (ltnP i k) => [lt_ik | le_ki].
  (* If i < k both side vanishes *)
  rewrite coefX_tfps_eq0 ?ltnS //.
  rewrite [X in X / _](_ : _ = 0) ?mul0r //.
  rewrite coeftM le_in1; apply: big1 => [[j /=]]; rewrite ltnS => le_ji _.
  rewrite coef_deriv_tfps.
  rewrite coef_tfpsXn eqSS (ltn_eqF (leq_ltn_trans le_ji lt_ik)).
  by rewrite andbF mul0rn mul0r.
(* Else we conclude by the previous theorem *)
apply (mulIr (nat_unit i)); rewrite divrK // mulr_natr.
rewrite Lagrange_Bürmann_exp //; last by rewrite !ltnS le_ki le_in1.
rewrite subSS derivX_tfps /= trXnt_tfpsX deriv_tfpsX mulr1.
rewrite mulrnAl -mulrnAr coef_tfpsXnM le_in1 (leq_gtF le_ki).
by rewrite coeftMn.
Qed.


(** This form of statement doesn't allow to compute the n.+2 coefficient *)
Theorem Lagrange_Bürmann_exp2 n (g : {tfps R n.+1}) i k :
  g \in GRing.unit ->
  k <= i <= n.+1 -> ((lagrfix g) ^+ k)`_i =
                    ((1 - tmulX g^`()%tfps / g) * \X ^+ k * g ^+ i)`_i.
Proof.
move=> gU.
case: k i => [|k] [|i] Hki //.
- by rewrite !expr0 !mulr1 coeftB coeft0M coeft_tmulX mul0r subr0.
- rewrite !expr0 !mulr1 coeft1 exprS mulrA !mulrBl mul1r.
  by rewrite divrK //= -!/(_`_i.+1) -exprS tmulX_deriv_expE.
move: Hki; rewrite !ltnS => /andP [le_ki le_in].
have le_in1 := (leq_trans le_in (leqnSn _)).
rewrite -mulrA [\X^+_ * _]mulrC mulrA mulrC !mulrBl mul1r.
rewrite (exprS g i) mulrA divrK // -exprS.
rewrite (exprS \X k) -mulrA coef_tfpsXM /= ltnS le_in -/(_`_i.+1).
apply (mulIr (nat_unit i)).
rewrite mulr_natr Lagrange_Bürmann_exp // ?ltnS ?le_ki ?le_in1 //.
have := erefl (\X ^+ k * tmulX (g ^+ i.+1))^`().
rewrite {2}tmulXE mulrA [_ * \X]mulrC -exprS.
rewrite [X in _ = X]derivM_tfps derivX_tfps /=.
rewrite trXnt_trXnt // trXnt_id trXnt_tfpsX deriv_tfpsX mulr1 mulrnAl.
move/(congr1 (fun s : {tfps R _} => s`_i)).
rewrite coeftD coeftMn [(\X^+k * _)`_i]coef_tfpsXnM le_in1 (leq_gtF le_ki).
set X := (X in _ = _ + X); move=> /(congr1 (fun s => s - X)).
rewrite addrK => <-.
rewrite {}/X deriv_trXnt [\Xo(n.+2) ^+ k.+1]exprS rmorphM /= trXnt_tfpsX.
rewrite [\X * _]mulrC -!mulrA -tmulXE rmorphXn /= trXnt_tfpsX -/(_`_i.+1).
rewrite coef_deriv_tfps.
rewrite !coef_tfpsXnM le_in1 ltnS le_in1 (leq_gtF (leq_trans le_ki (leqnSn _))).
rewrite (leq_gtF le_ki) coeft_tmulX -/(leq _ _) (leq_gtF le_ki).
rewrite subSn //= coeftB mulrBl mulr_natr; congr (_ - _).
rewrite tmulXM !coeft_tmulX -/(leq _ _).
case: leqP; rewrite ?mul0r // => lt_ki.
by rewrite derivX_tfps /= coeftMn mulrC rmorphXn /= mulr_natr.
Qed.

Theorem Lagrange_Bürmann2 n (g h : {tfps R n.+1}) i :
  g \in GRing.unit ->
  (h \oT (trXnt n.+1 (lagrfix g)))`_i =
  ((1 - tmulX g^`()%tfps / g) * h * g ^+ i)`_i.
Proof.
move=> uG.
case: (leqP i n.+1) => [le_in1 | lt_n1i]; first last.
  by rewrite coef_tfps (ltn_geF lt_n1i) coef_tfps (ltn_geF lt_n1i).
rewrite (tfps_def h) !(raddf_sum, mulr_suml, mulr_sumr, coeft_sum) /=.
apply eq_bigr => [[k /=]]; rewrite ltnS => le_kn2 _.
rewrite !linearZ /= -mulrA mulrC -!scalerAl !coeftZ; congr (_ * _).
rewrite rmorphXn /= comp_tfpsX ?coeft0_eq0_trXnt ?coeft0_eq0_lagrfix //.
rewrite -rmorphXn coef_trXnt le_in1.
case: (leqP k i) => [le_ki | lt_ik]; first last.
  rewrite coefX_tfps_eq0 ?coeft0_eq0_lagrfix //.
  by rewrite -mulrA coef_tfpsXnM lt_ik.
rewrite Lagrange_Bürmann_exp2 ?le_in1 ?andbT //.
by rewrite [in RHS]mulrC mulrA.
Qed.

End LagrangeTheorem.


Section ExpLog.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Definition expt m : {tfps R m} :=
  [tfps i <= m => i`!%:R ^-1 ].
Definition logt m : {tfps R m} :=     (* This is - log (1 - X) *)
  [tfps i <= m => if i != 0%N then i%:R ^-1 else 0].

Definition exp f : {tfps R n} := (expt n) \oT f.
Definition log f : {tfps R n} := - logt n \oT (1 - f).
Definition expr_tfps (c : R) f := exp (c *: log f).

Lemma exptE : expt n = exp \X.
Proof. by rewrite /exp comp_tfpsXr. Qed.
Lemma logtE : logt n = - log (1 - \X).
Proof. by rewrite /log raddfN opprK opprB addrC subrK /= comp_tfpsXr. Qed.

Lemma trXnt_expt m : m <= n -> trXnt m (expt n) = expt m.
Proof. exact: trXnt_tfps_of_fun. Qed.
Lemma trXnt_logt m : m <= n -> trXnt m (logt n) = logt m.
Proof. exact: trXnt_tfps_of_fun. Qed.

Lemma coeft0_expt : (expt n)`_0 = 1.
Proof. by rewrite coef_tfps_of_fun fact0 invr1. Qed.
Lemma expt_in_coeft0_eq1 : expt n \in coeft0_eq1.
Proof. by rewrite coeft0_eq1E coeft0_expt. Qed.

Lemma coeft0_exp f : (exp f)`_0 = 1.
Proof. by rewrite /exp coef0_comp_tfps coeft0_expt. Qed.
Lemma exp_in_coeft0_eq1 f : exp f \in coeft0_eq1.
Proof. by rewrite coeft0_eq1E coeft0_exp. Qed.
Lemma exp_unit f : exp f \is a GRing.unit.
Proof. exact/coeft0_eq1_unit/exp_in_coeft0_eq1. Qed.

Lemma coeft0_logt : (logt n)`_0 = 0.
Proof. by rewrite coef_tfps_of_fun. Qed.
Lemma logt_in_coeft0_eq1 : logt n \in coeft0_eq0.
Proof. by rewrite coeft0_eq0E coeft0_logt. Qed.

Lemma coeft0_log f : (log f)`_0 = 0.
Proof. by rewrite /log coef0_comp_tfps coeftN coeft0_logt oppr0. Qed.
Lemma log_in_coeft0_eq0 f : log f \in coeft0_eq0.
Proof. by rewrite coeft0_eq0E coeft0_log. Qed.

Lemma exp_coeft0_eq0 f : f \in coeft0_eq0 ->
  exp f = \sum_(i < n.+1) i`!%:R ^-1 *: f ^+ i.
Proof.
rewrite /exp /expt => f0_eq0; apply tfpsP => i le_in.
rewrite (coef_comp_tfps_leq (l := n)) // coeft_sum /=.
apply eq_bigr => k _.
by rewrite coef_tfps_of_fun -ltnS ltn_ord coeftZ.
Qed.

Lemma exp_coeft0_eq0_val f : f \in coeft0_eq0 ->
  exp f = trXn n (\sum_(i < n.+1) i`!%:R ^-1 *: (tfps f) ^+ i).
Proof.
move/exp_coeft0_eq0 ->; rewrite /= !raddf_sum; apply eq_bigr => i _ /=.
by rewrite -[LHS]tfpsK !linearZ /= exp_tfps_val trXn_trXn.
Qed.

Lemma exp_coeft0_isnt_0 f : f \notin coeft0_eq0 -> exp f = 1.
Proof.
rewrite /exp => /comp_tfps_coef0_neq0 ->.
by rewrite coef_tfps_of_fun /= fact0 invr1 tfpsC1.
Qed.

Lemma exp0 : exp 0 = 1 :> {tfps R n}.
Proof. by rewrite /exp comp_tfps0r coeft0_expt tfpsC1. Qed.

Lemma expC (c : R) : exp (c%:S) = 1 :> {tfps R n}.
Proof.
case (boolP (c%:S \in @coeft0_eq0 R n)) => [| p0N0].
- rewrite coeft0_eq0E coeftC /= => /eqP ->.
  by rewrite tfpsC0 exp0.
- exact: exp_coeft0_isnt_0.
Qed.

Lemma log_coeft0_eq1 f : f \in coeft0_eq1 ->
  log f = - \sum_(1 <= i < n.+1) i%:R ^-1 *: (1 - f) ^+i.
Proof.
rewrite /log /logt => f0_eq1; apply tfpsP => i le_in.
rewrite raddfN !coeftN /=; congr (- _).
rewrite (coef_comp_tfps_leq (l := n)) -?coeft0_eq10 // coeft_sum /=.
rewrite big_mknat /= big_ltn // inordK //=.
rewrite coef_tfps_of_fun /= mul0r add0r.
rewrite !big_nat; apply eq_bigr => j /andP[le1j /[!ltnS] ltjn].
by rewrite inordK // coef_tfps_of_fun ltjn coeftZ -lt0n le1j.
Qed.

Lemma log_coeft0_eq1_val f : f \in coeft0_eq1 ->
  log f = trXn n (- \sum_(1 <= i < n.+1) i%:R ^-1 *: (1 - val f) ^+i).
Proof.
move=> /log_coeft0_eq1 ->.
rewrite /= !raddf_sum; apply eq_bigr => i _ /=.
by rewrite -[LHS]tfpsK !linearZ !linearN /= exp_tfps_val trXn_trXn.
Qed.

Lemma log_coeft0_isnt_1 f : f \notin coeft0_eq1 -> log f = 0.
Proof.
rewrite /log coeft0_eq10 => /comp_tfps_coef0_neq0 ->.
by rewrite coeftN coef_tfps_of_fun /= oppr0 tfpsC0.
Qed.

Lemma log1 : log (1 : {tfps R n}) = 0.
Proof. by rewrite /log subrr comp_tfps0r coeftN coeft0_logt oppr0 tfpsC0. Qed.

End ExpLog.
Arguments logt {R m}.
Arguments expt {R m}.
Arguments log {R n}.
Arguments exp {R n}.
Notation "f ^^ r" := (expr_tfps r f) : tfps_scope.


Section TrXntExpLog.

Variables (R : unitRingType) (n m : nat)  (f : {tfps R n}).

Lemma trXnt_exp : m <= n -> trXnt m (exp f) = exp (trXnt m f).
Proof. by move=> le_mn; rewrite /exp trXnt_comp // trXnt_expt. Qed.
Lemma trXnt_log : m <= n -> trXnt m (log f) = log (trXnt m f).
Proof.
move=> le_mn; rewrite /log trXnt_comp //.
by rewrite raddfN /= trXnt_logt // raddfB /= trXnt1.
Qed.

End TrXntExpLog.


Module TFPSUnitRing.

Section PrimitiveUnitRing.

Variable R : unitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.

Fact natmul_inj (m : nat) : (m%:R == 0 :> R) = (m == 0%N).
Proof.
case: m => [|m]; first by rewrite eq_refl; apply/eqP.
rewrite {2}/eq_op /=.
apply/negP => /eqP/(congr1 (fun x => x \is a GRing.unit)).
by rewrite nat_unit unitr0.
Qed.

Lemma pred_size_prim (p : {poly R}) : (size (prim p)).-1 = size p.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite prim0 size_poly0.
rewrite size_poly_eq // size_poly_eq0 p_neq0 -lead_coefE /=.
have:= p_neq0; rewrite -size_poly_eq0.
case: (size p) => // sz _.
apply/negP => /eqP/(congr1 (fun x => x * sz.+1%:R))/eqP.
by rewrite mul0r divrK // mulr1n lead_coef_eq0 (negbTE p_neq0).
Qed.

Lemma primK : cancel (@prim R) (@deriv R).
Proof.
move=> p.
rewrite /prim -{3}[p]coefK ; apply/polyP => i.
rewrite coef_deriv !coef_poly ltnS.
case: (_ < _); last by rewrite mul0rn.
by rewrite /= mulr1n /= -[LHS]mulr_natr /= divrK.
Qed.

Implicit Types (f g : {tfps R n}).

Lemma prim_tfpsK : cancel (@prim_tfps R n) (@deriv_tfps R n.+1).
Proof.
move=> p; apply/tfpsP => i le_in.
rewrite coef_deriv_tfps coef_prim_tfps.
by rewrite -coef_deriv primK -coef_tfpsE.
Qed.

Lemma deriv_tfpsK :
  {in coeft0_eq0, cancel (@deriv_tfps R n.+1) (@prim_tfps R n)}.
Proof.
move=> f; rewrite coeft0_eq0E => /eqP f0_eq0.
apply/tfpsP => i _.
rewrite coef_prim_tfps coef_prim coef_deriv_tfps.
case: i => [|i]; first by rewrite eq_refl f0_eq0.
by rewrite [_.+1.-1]/= -[X in X / _]mulr_natr mulrK.
Qed.

End PrimitiveUnitRing.


Section ExpMorph.

Variable R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.


Lemma nat_unit_alg (A : unitAlgType R) i : i.+1%:R \is a @GRing.unit A.
Proof. by rewrite -scaler_nat scaler_unit ?unitr1 ?nat_unit. Qed.


Implicit Types (f g : {tfps R n}).

Lemma fact_unit m : m`!%:R \is a @GRing.unit R.
Proof. by have:= fact_gt0 m; rewrite lt0n; case: m`!. Qed.

Theorem expD : {in @coeft0_eq0 R n &, {morph exp : f g / f + g >-> f * g}}.
Proof.
move=> f g f0_eq0 g0_eq0 /=.
rewrite !exp_coeft0_eq0 ?rpredD //.
pose FG u v := (u`! * v`!)%:R ^-1 *: (g ^+ u * f ^+ v) : {tfps R n}.
rewrite (eq_bigr
           (fun i : 'I_n.+1 => \sum_(j < i.+1) FG j (i - j)%N)); first last.
  move => [i /= _] _; rewrite exprDn.
  rewrite scaler_sumr; apply: eq_bigr => [[j]]; rewrite /= ltnS => le_ji _.
  rewrite mulrC -mulrnAl scalerAl -scaler_nat scalerA -scalerAl; congr(_ *: _).
  case: i le_ji => [|i le_ji1].
    by rewrite leqn0 => /eqP ->; rewrite fact0 bin0 mulr1 muln1.
  rewrite bin_factd //.
  rewrite natr_div ?mulKr ?fact_unit // ?natrM ?unitrM ?fact_unit //.
  by apply/dvdnP; exists 'C(i.+1, j); rewrite bin_fact.
rewrite -(triangular_index_bigop _ FG (ltnSn n)) /= {}/FG.
rewrite mulrC (big_distrl _ _ _) /=; apply eq_bigr => i _.
rewrite [RHS]mulr_sumr [RHS](bigID (fun j : 'I_n.+1 => i + j < n.+1)) /=.
rewrite [X in _ + X]big1 ?addr0; first last.
  move => j; rewrite -ltnNge ltnS => lt_nij.
  by rewrite -scalerAr -scalerAl tfpsMX_eq0 // !scaler0.
apply eq_bigr => j _.
by rewrite -scalerAr -scalerAl scalerA natrM invrM // fact_unit.
Qed.

Lemma expN f : f \in coeft0_eq0 -> exp (- f) = (exp f)^-1.
Proof.
move=> f0_eq0; apply: (@mulrI _ (exp f)); rewrite ?divrr ?exp_unit //.
by rewrite -expD ?rpredN // subrr exp0.
Qed.

Lemma expB : {in @coeft0_eq0 R n &, {morph exp : f g / f - g >-> f / g}}.
Proof. by move=> f g hf hg; rewrite expD ?rpredN // expN. Qed.

Lemma exp_sum (I : eqType) (r : seq I) (P : pred I) (F : I -> {tfps R n}) :
  (forall i, P i -> F i \in coeft0_eq0) ->
  exp (\sum_(i <- r | P i) F i) = \prod_(i <- r | P i) exp (F i).
Proof.
move=> H; apply (big_morph_in (@coeft0_eq0D R n)
                   (zero_in_coeft0_eq0 R n) expD (exp0 R n)).
by apply/allP => /= f /mapP[i]; rewrite mem_filter => /andP[/H Fiin _ ->].
Qed.

End ExpMorph.


Section MoreDerivative.

Variable R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.

Implicit Types (f g : {tfps R n}).

Theorem derivXn_tfps m :
  m != 0%N ->  {in GRing.unit, forall f,
     (f ^- m)^`() = (trXnt n.-1 f) ^- m.+1 * f^`()%tfps *- m}.
Proof.
move=> Hm /= f fU; rewrite -exprVn derivX_tfps derivV_tfps //.
rewrite rmorphV ?leq_pred //= => _.
rewrite !exprVn rmorphXn ?leq_pred //= => _.
rewrite [_/_]mulrC mulrA mulrN mulNrn -!mulrnAr.
rewrite -!exprVn -exprD -addSnnS addn1.
by case: m Hm.
Qed.

Lemma deriv_tfps_eq0_cst f : f^`() = 0 -> {c : R | f = c %:S}.
Proof.
move: f; case: n => [f _| m f H]; exists (f`_0).
  by rewrite {1}[f]tfps_is_cst.
apply/tfpsP => [] [|i]; rewrite coeftC // ltnS [RHS]/= => le_im.
apply: (mulIr (nat_unit i)); rewrite mul0r.
move: H => /(congr1 (fun x : {tfps _ _ } => x`_i)).
by rewrite coef_deriv_tfps coef0 -[X in X = 0]mulr_natr.
Qed.

Lemma deriv_tfps_ex_eq0 f :
  f^`() = 0 -> {x : R | (tfps f).[x] = 0} -> f = 0.
Proof.
move=> /deriv_tfps_eq0_cst [c ->] [x].
rewrite val_tfpsC /= hornerC => ->.
by rewrite tfpsC0.
Qed.

Lemma deriv_tfps_eq0 f : f^`() = 0 -> f`_0 = 0 -> f = 0.
Proof.
move=> /deriv_tfps_ex_eq0 H f0_eq0; apply: H.
by exists 0; rewrite horner_coef0.
Qed.

Lemma deriv_tfps_ex_eq f g :
  f^`() = g^`() -> {x : R | (tfps f).[x] = (tfps g).[x]} -> f = g.
Proof.
move=> H [x Hx].
apply/eqP; rewrite -(subr_eq0 f g); apply/eqP.
apply: deriv_tfps_ex_eq0; first by rewrite linearB /= H subrr.
by exists x ; rewrite -horner_evalE rmorphB /= horner_evalE Hx subrr.
Qed.

Lemma deriv_tfps_eq f g : f^`() = g^`() -> f`_0 = g`_0 -> f = g.
Proof.
move=> /deriv_tfps_ex_eq H Heq0; apply: H.
by exists 0; rewrite !horner_coef0.
Qed.

End MoreDerivative.


Section DerivExpLog.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.

Lemma deriv_expt n : (@expt R n.+1)^`() = expt.
Proof.
apply/tfpsP => /= i le_in.
rewrite coef_deriv_tfps !coef_tfps_of_fun ltnS le_in.
rewrite factS natrM /= invrM ?fact_unit //.
by rewrite -[LHS]mulr_natr divrK.
Qed.

Lemma deriv_expE n a (f : {tfps R n.+1}) :
  f^`() = a *: trXnt n f -> f = f`_0 *: exp (a *: \X).
Proof.
rewrite /exp => devf; apply tfpsP => i le_in1.
rewrite coeftZ coef_comp_tfps_cX coef_tfps_of_fun le_in1.
elim: i le_in1 => [|i IHi]; first by rewrite fact0 divr1 expr0 mulr1.
rewrite ltnS => le_in.
have:= congr1 (fun f : {tfps _ _ } => f`_i / (i.+1)%:R) devf.
rewrite coef_deriv_tfps coeftZ coef_trXnt le_in.
rewrite {}IHi ?(leq_trans le_in) //.
rewrite -[X in X / _]mulr_natr mulrK // => ->.
rewrite mulrA [a * _]mulrC exprS -!mulrA.
by rewrite factS natrM invrM // ?mulrA // fact_unit.
Qed.

Lemma deriv_exptE n (f : {tfps R n.+1}) :
  f^`() = trXnt n f -> f = f`_0 *: expt.
Proof. by have:= @deriv_expE n 1 f; rewrite !scale1r /exp comp_tfpsXr. Qed.

Lemma deriv_logt n : (@logt R n.+1)^`() = (1 - \X)^-1.
Proof.
apply/tfpsP => /= i le_in.
rewrite coef_deriv_tfps !coef_tfps_of_fun ltnS le_in /=.
rewrite -[LHS]mulr_natr mulrC divrr //.
by rewrite -(scale1r \X) coef_geometrict_1cNV // expr1n.
Qed.

Theorem deriv_exp n (f : {tfps R n}) :
  f \in coeft0_eq0 -> (exp f)^`() = f^`()%tfps * trXnt n.-1 (exp f).
Proof.
case: n f => /= [| m] f f0_eq0.
  by rewrite [f]tfps_is_cst deriv_tfpsC mul0r expC deriv_tfps1.
rewrite /exp deriv_tfps_comp // mulrC deriv_expt /=.
by rewrite trXnt_comp // trXnt_expt.
Qed.

Theorem deriv_log n (f : {tfps R n}) :
  f \in coeft0_eq1 -> (log f)^`() = f^`()%tfps / trXnt n.-1 f.
Proof.
case: n f => [|m] f.
  rewrite [f]tfps_is_cst coeft0_eq1E coeftC => /eqP ->.
  by rewrite !deriv_tfps0p mul0r.
move => f0_eq1.
rewrite /log !raddfN /= deriv_tfps_comp -?coeft0_eq10 //= mulrC.
rewrite deriv_logt /= raddfB /= deriv_tfps1 sub0r mulNr opprK.
rewrite [X in _ * X = _ ]rmorphV /=; first last.
  apply: coeft0_eq1_unit; rewrite -coeft0_eq01 rpredN.
  by rewrite coeft0_eq0E coef_tfpsX /= mulr0.
congr (_ / _); rewrite raddfB /= comp_tfps1 comp_tfpsX.
  by rewrite raddfB /= trXnt1 opprB addrC subrK.
rewrite coeft0_eq0_trXnt.
by rewrite -rpredN coeft0_eq01 opprB addrC subrK.
Qed.


Variable n : nat.
Implicit Types (f g : {tfps R n}).

Lemma exptK : log expt = \X :> {tfps R n}.
Proof.
case: n => [|m].
  by apply tfpsP => [] [|i]// _; rewrite coeft0_log coef_tfpsX mulr0.
apply deriv_tfps_eq => //; last by rewrite coeft0_log coef_tfpsX mulr0.
rewrite deriv_log ?expt_in_coeft0_eq1 //.
rewrite deriv_tfpsX deriv_expt // trXnt_expt // divrr //.
by apply/coeft0_eq1_unit/expt_in_coeft0_eq1.
Qed.

Lemma expK : {in coeft0_eq0, cancel (@exp R n) (@log R n)}.
Proof.
move => f f0_eq0 /=.
have:= congr1 (fun g => g \oT f) exptK.
rewrite comp_tfpsX // => {2}<-.
rewrite /exp /log !raddfN /= -comp_tfpsA.
by rewrite [(1 - expt) \oT f]rmorphB /= comp_tfps1.
Qed.

Lemma exp_inj : {in coeft0_eq0 &, injective (@exp R n)}.
Proof. exact: (can_in_inj expK). Qed.

Lemma log_inj : {in coeft0_eq1 &, injective (@log R n)}.
Proof.
move=> f g f0_eq1 g0_eq1 /= Hlog.
suff : f / g = 1.
  by move/(congr1 (fun x => x * g)); rewrite divrK ?mul1r ?coeft0_eq1_unit.
apply deriv_tfps_eq => //; first last.
  by rewrite coeft0M (eqP f0_eq1) coeft0V (eqP g0_eq1) divr1 coeft1.
rewrite deriv_tfps1 deriv_div_tfps; last exact: coeft0_eq1_unit.
rewrite [X in X / _](_ : _ = 0) ?mul0r //.
apply/eqP; rewrite subr_eq0 [X in _ == X]mulrC.
rewrite -eq_divr ?trXnt_unitE -?unit_tfpsE ?coeft0_eq1_unit //.
by move/(congr1 (@deriv_tfps R n)): Hlog; rewrite !deriv_log // => ->.
Qed.

Lemma logK : {in coeft0_eq1 , cancel (@log R n) (@exp R n)}.
Proof.
move=> f f0_eq1 /=.
apply: log_inj => //; first by rewrite exp_in_coeft0_eq1.
by rewrite expK // log_in_coeft0_eq0.
Qed.

Lemma logM : {in coeft0_eq1 &, {morph (@log R n) : f g / f * g >-> f + g}}.
Proof.
move=> f g f0_eq1 g0_eq1 /=.
apply exp_inj; rewrite ?rpredD ?log_in_coeft0_eq0 //.
rewrite expD ?log_in_coeft0_eq0 //.
by rewrite !logK // rpredM.
Qed.

Lemma logV : {in coeft0_eq1, {morph (@log R n) : f / f^-1 >-> - f}}.
Proof.
move=> f f0_eq1 /=.
apply exp_inj; rewrite ?rpredN ?log_in_coeft0_eq0 //.
rewrite expN ?log_in_coeft0_eq0 //.
by rewrite !logK // rpredV.
Qed.

Lemma log_div : {in coeft0_eq1 &, {morph (@log R n) : f g / f / g >-> f - g}}.
Proof. by move=> f g f0_eq1 g0_eq1 /=; rewrite logM ?rpredV // logV. Qed.

Lemma log_prod (I : eqType) (r : seq I) (P : pred I) (F : I -> {tfps R n}) :
  (forall i, P i -> F i \in coeft0_eq1) ->
  log (\prod_(i <- r | P i) F i) = \sum_(i <- r | P i) log (F i).
Proof.
pose mulcl := mulr_closed_coeft0_eq1 R n.
move=> H; apply: (big_morph_in mulcl.2 mulcl.1 logM (log1 _ _)).
by apply/allP => /= f /mapP[i]; rewrite mem_filter => /andP[/H Fiin _ ->].
Qed.

Section ExprTfps.

Variable f : {tfps R n}.
Hypothesis f0_eq1 : f \in coeft0_eq1.


Local Lemma log_coeft0_eq0Z c : c *: log f \in coeft0_eq0.
Proof. by rewrite coeft0_eq0Z // log_in_coeft0_eq0. Qed.
Let tmp_log_coeft0_eq0Z := log_coeft0_eq0Z.

Lemma coeft0_eq1_expr c : f ^^ c \in coeft0_eq1.
Proof. by rewrite /expr_tfps exp_in_coeft0_eq1. Qed.

Lemma expr_tfps0 : f ^^ 0 = 1.
Proof. by rewrite /expr_tfps scale0r exp0. Qed.

Lemma expr_tfps1 : f ^^ 1 = f.
Proof. by rewrite /expr_tfps scale1r logK. Qed.

Lemma expr_tfpsn m : f ^^ m%:R = f ^+ m.
Proof.
elim: m => [|m IHm]; first exact: expr_tfps0.
rewrite /expr_tfps -{1}add1n natrD scalerDl scale1r expD ?log_in_coeft0_eq0 //.
by rewrite -/(expr_tfps _ _) {}IHm logK // exprS.
Qed.

Lemma expr_tfpsN a : f ^^ (- a) = (f ^^ a)^-1.
Proof. by rewrite /expr_tfps scaleNr expN. Qed.

Lemma expr_tfpsN1 : f ^^ (-1) = f ^-1.
Proof. by rewrite expr_tfpsN expr_tfps1. Qed.

Lemma expr_tfpsD a b : f ^^ (a + b) = (f ^^ a) * (f ^^ b).
Proof. by rewrite /expr_tfps scalerDl expD. Qed.

Lemma expr_tfpsB a b : f ^^ (a - b) = (f ^^ a) / (f ^^ b).
Proof. by rewrite expr_tfpsD expr_tfpsN. Qed.

Lemma expr_tfpsM a b : f ^^ (a * b) = (f ^^ a) ^^ b.
Proof. by rewrite /expr_tfps expK ?scalerA ?[b * a]mulrC. Qed.

Lemma deriv_expr_tfps a :
  (f ^^ a)^`() = a *: trXnt n.-1 (f ^^ (a - 1)) * f^`()%tfps.
Proof.
rewrite {1}/expr_tfps deriv_exp //.
rewrite linearZ /= deriv_log // -!scalerAl; congr (_ *: _).
rewrite -mulrA mulrC; congr (_ * _).
rewrite -trXntV ?leq_pred // -rmorphM ?leq_pred //= => _.
by rewrite mulrC expr_tfpsB expr_tfps1.
Qed.

End ExprTfps.

Lemma expr_tfpsNn f m : f \in coeft0_eq1 -> f ^^ (-m%:R) = f ^- m.
Proof.
move=> Hf.
by rewrite -mulN1r expr_tfpsM expr_tfpsN1 ?expr_tfpsn ?exprVn ?rpredV.
Qed.

Lemma expr_tfpsK a : a \is a GRing.unit ->
  {in coeft0_eq1, cancel (@expr_tfps R n a) (@expr_tfps R n a^-1)}.
Proof. by move=> aU f f0_eq1; rewrite -expr_tfpsM divrr ?expr_tfps1. Qed.

Lemma expr_tfps_inj a : a \is a GRing.unit ->
  {in coeft0_eq1 &, injective (@expr_tfps R n a)}.
Proof. by move=> /expr_tfpsK/can_in_inj. Qed.


Local Notation "\sqrt f" := (f ^^ (2%:R^-1)).

Lemma sqrrK f : f \in coeft0_eq1 -> \sqrt (f ^+ 2) = f.
Proof.
by move => Hh; rewrite -expr_tfpsn -?expr_tfpsM ?divrr ?expr_tfps1.
Qed.

Lemma sqrtK f : f \in coeft0_eq1 -> (\sqrt f) ^+ 2 = f.
Proof.
move => Hh; rewrite -expr_tfpsn ?coeft0_eq1_expr //.
by rewrite -?expr_tfpsM // mulrC divrr ?expr_tfps1.
Qed.

End DerivExpLog.

Notation "\sqrt f" := (f ^^ (2%:R^-1)) : tfps_scope.


Section CoefExpX.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.

Lemma coeft1cX n c : 1 + c *: \Xo(n) \in @coeft0_eq1 R n.
Proof.
rewrite coeft0_eq1E coeftD coeft1.
by rewrite coeftZ coef_tfpsE val_tfpsX coefZ coefX !mulr0 addr0.
Qed.

Lemma deriv1cX n c : (1 + c *: \Xo(n.+1))^`() = c%:S :> {tfps R n}.
Proof.
rewrite linearD /= deriv_tfps1 add0r linearZ /=.
rewrite -alg_tfpsC; congr (_ *: _); apply tfps_inj.
by rewrite (val_deriv_tfps \Xo(n.+1)) val_tfpsX scale1r derivX.
Qed.

Theorem coef_expr1cX n c a m : m <= n ->
  ((1 + c *: \Xo(n)) ^^ a)`_m = c ^+ m * \prod_(i < m) (a - i%:R) / m`!%:R :> R.
Proof.
elim: m n a => [|m IHm] n a lt_mn.
  rewrite big_ord0 /expr_tfps coeft0_exp ?coeft0_eq0Z ?log_in_coeft0_eq0 //.
  by rewrite expr0 mul1r fact0 divr1.
case: n lt_mn => [|n] //; rewrite ltnS => le_mn.
have:= coef_deriv_tfps ((1 + c *: \Xo(n.+1)) ^^ a) m.
rewrite -[X in _ = X -> _]mulr_natr => /(congr1 (fun x => x * m.+1%:R^-1)).
rewrite mulrK // => <-.
rewrite deriv_expr_tfps ?coeft1cX // deriv1cX.
rewrite [_ * c%:S]mulrC -alg_tfpsC mulr_algl exprS coefZ.
rewrite coefZ coef_trXn le_mn {}IHm ?(leq_trans le_mn) // {n le_mn}.
rewrite mulrA factS natrM invrM // ?fact_unit // !mulrA; congr (_ * _ * _).
rewrite -[_ * a * _]mulrA [a * _]mulrC -!mulrA; congr (_ * (_ * _)).
rewrite big_ord_recl /= subr0; congr (_ * _).
by apply eq_bigr => i /= _; rewrite /bump /= natrD -[1%:R]/1 opprD addrA.
Qed.

Lemma coef_expr1X n a m :
  m <= n -> ((1 + \Xo(n)) ^^ a)`_m = \prod_(i < m) (a - i%:R) / m`!%:R :> R.
Proof.
by move=> le_mp; rewrite -[\X]scale1r coef_expr1cX // expr1n mul1r.
Qed.

End CoefExpX.


Section SquareRoot.

Variables R : idomainType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.
Implicit Types (f g : {tfps R n}).


Lemma sqrtE f g : f \in coeft0_eq1 -> g ^+ 2 = f ->
  g = \sqrt f  \/  g = - \sqrt f.
Proof.
move=> /eqP f0_eq1 Heq.
have /eqP := (congr1 (fun f : {tfps R n} => f`_0) Heq).
rewrite -subr_eq0 {}f0_eq1 expr2 coeft0M -expr2 subr_sqr_1.
rewrite mulf_eq0 => /orP [].
- by rewrite subr_eq0 -coeft0_eq1E -{}Heq {f} => Hg0; left; rewrite sqrrK.
- rewrite addr_eq0 -eqr_oppLR -coefN -raddfN -coeft0_eq1E -{}Heq {f} => Hg0.
  by right; apply oppr_inj; rewrite opprK -sqrrN sqrrK.
Qed.

End SquareRoot.

End TFPSUnitRing.

Notation "\sqrt f" := (f ^^ (2%:R^-1)) : tfps_scope.


Module TFPSField.

Section TFPSField.

Variables K : fieldType.
Hypothesis char_K_is_zero : [pchar K] =i pred0.

Lemma nat_unit_field i : i.+1%:R \is a @GRing.unit K.
Proof. by rewrite unitfE; move: char_K_is_zero => /pcharf0P ->. Qed.

Local Notation nuf := nat_unit_field.

(* TODO : the three lemma below should be elsewhere *)
(* as they have nothing to do with power series     *)
Definition natmul_inj         := TFPSUnitRing.natmul_inj         nuf.
Definition nat_unit_alg       := TFPSUnitRing.nat_unit_alg       nuf.
Definition fact_unit          := TFPSUnitRing.fact_unit          nuf.

Definition pred_size_prim     := TFPSUnitRing.pred_size_prim     nuf.
Definition primK              := TFPSUnitRing.primK              nuf.
Definition prim_tfpsK         := TFPSUnitRing.prim_tfpsK         nuf.
Definition deriv_tfpsK        := TFPSUnitRing.deriv_tfpsK        nuf.
Definition derivXn_tfps       := TFPSUnitRing.derivXn_tfps.
Definition expD               := TFPSUnitRing.expD               nuf.
Definition expN               := TFPSUnitRing.expN               nuf.
Definition expB               := TFPSUnitRing.expB               nuf.
Definition exp_sum            := TFPSUnitRing.exp_sum            nuf.
Definition deriv_tfps_eq0_cst := TFPSUnitRing.deriv_tfps_eq0_cst nuf.
Definition deriv_tfps_ex_eq0  := TFPSUnitRing.deriv_tfps_ex_eq0  nuf.
Definition deriv_tfps_eq0     := TFPSUnitRing.deriv_tfps_eq0     nuf.
Definition deriv_tfps_ex_eq   := TFPSUnitRing.deriv_tfps_ex_eq   nuf.
Definition deriv_tfps_eq      := TFPSUnitRing.deriv_tfps_eq      nuf.
Definition deriv_exp          := TFPSUnitRing.deriv_exp          nuf.
Definition deriv_expt         := TFPSUnitRing.deriv_expt         nuf.
Definition deriv_expE         := TFPSUnitRing.deriv_expE         nuf.
Definition deriv_exptE        := TFPSUnitRing.deriv_exptE        nuf.
Definition deriv_log          := TFPSUnitRing.deriv_log          nuf.
Definition deriv_logt         := TFPSUnitRing.deriv_logt         nuf.
Definition expK               := TFPSUnitRing.expK               nuf.
Definition exp_inj            := TFPSUnitRing.exp_inj            nuf.
Definition logK               := TFPSUnitRing.logK               nuf.
Definition log_inj            := TFPSUnitRing.log_inj            nuf.
Definition logM               := TFPSUnitRing.logM               nuf.
Definition logV               := TFPSUnitRing.logV               nuf.
Definition log_div            := TFPSUnitRing.log_div            nuf.
Definition log_prod           := TFPSUnitRing.log_prod           nuf.
Definition coeft0_eq1_expr    := TFPSUnitRing.coeft0_eq1_expr.
Definition expr_tfpsn         := TFPSUnitRing.expr_tfpsn         nuf.
Definition expr_tfps0         := TFPSUnitRing.expr_tfps0.
Definition expr_tfps1         := TFPSUnitRing.expr_tfps1         nuf.
Definition expr_tfpsN         := TFPSUnitRing.expr_tfpsN         nuf.
Definition expr_tfpsN1        := TFPSUnitRing.expr_tfpsN1        nuf.
Definition expr_tfpsNn        := TFPSUnitRing.expr_tfpsNn        nuf.
Definition expr_tfpsD         := TFPSUnitRing.expr_tfpsD         nuf.
Definition expr_tfpsB         := TFPSUnitRing.expr_tfpsB         nuf.
Definition expr_tfpsM         := TFPSUnitRing.expr_tfpsM         nuf.
Definition sqrrK              := TFPSUnitRing.sqrrK              nuf.
Definition sqrtK              := TFPSUnitRing.sqrtK              nuf.
Definition coeft1cX           := TFPSUnitRing.coeft1cX.
Definition deriv1cX           := TFPSUnitRing.deriv1cX.
Definition coef_expr1cX       := TFPSUnitRing.coef_expr1cX       nuf.
Definition coef_expr1X        := TFPSUnitRing.coef_expr1X        nuf.
Definition sqrtE              := TFPSUnitRing.sqrtE              nuf.

End TFPSField.
End TFPSField.
Export TFPSField.


From mathcomp Require Import ssrint rat ssrnum.

Section FromRMorphism.

Variables R : unitRingType.

Fact ratr_rmorphism_nat_unit :
  (zmod_morphism (@ratr R) /\ monoid_morphism (@ratr R))
  <->
    (forall i, i.+1%:R \is a @GRing.unit R).
Proof.
split=> [[ratr_add ratr_mult] i | nat_unit].
- have ratrAM := GRing.isZmodMorphism.Build _ _ _ ratr_add.
  have ratrMM := GRing.isMonoidMorphism.Build _ _ _ ratr_mult.
  pose ratr_morph : {rmorphism rat -> R} := HB.pack (@ratr R) ratrAM ratrMM.
  rewrite -ratr_nat; apply: (rmorph_unit ratr_morph).
  by rewrite unitfE Num.Theory.pnatr_eq0.
- have injZtoQ: @injective rat int intr by apply: intr_inj.
  have den_unit x : ((denq x)%:~R : R) \is a GRing.unit.
    by case: (ratP x) => num den _ {num}; exact: nat_unit.
  do 2?split; rewrite /ratr ?divr1 // => x y; last first.
    rewrite -commr_int -!mulrA -[(denq x)%:~R^-1 * _](commrV (commr_int _ _)).
    apply: canLR (mulKr (den_unit _)) _; rewrite !mulrA.
    do 2!apply: canRL (mulrK (den_unit _)) _; rewrite -!rmorphM; congr _%:~R.
    apply: injZtoQ; rewrite !rmorphM [x * y]lock /= !numqE -lock.
    by rewrite -!mulrA mulrA mulrCA -!mulrA (mulrCA y).
  apply: (canLR (mulrK (den_unit _))); apply: (mulIr (den_unit x)).
  rewrite -!mulrA [(denq (x - y))%:~R * _]commr_int !mulrA.
  rewrite mulrBl divrK ?den_unit //.
  rewrite -[X in _ = (_ - X) * _]mulrA -[(denq y)%:~R^-1 * _](commrV (commr_int _ _)).
  rewrite [X in _ = (_ - X) * _]mulrA -!rmorphM.
  apply: (mulIr (den_unit y)).
  rewrite /= -!mulrA [(denq (x - y))%:~R * _]commr_int mulrA.
  rewrite mulrBl divrK ?den_unit //.
  rewrite -!(rmorphM, rmorphB); congr _%:~R; apply: injZtoQ.
  rewrite !(rmorphM, rmorphB) [_ - _]lock /= -lock !numqE.
  by rewrite (mulrAC y) -!mulrBl -mulrA mulrAC !mulrA.
Qed.

End FromRMorphism.


Section FromRatAlgType.

Variables R : unitAlgType rat.

Fact rat_algtype_nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Proof.
rewrite -ratr_rmorphism_nat_unit.
have eq_in_ratr := fmorph_eq_rat (in_alg R).
split => [x y|]; first by rewrite -!eq_in_ratr ?rmorphB.
by split => [|x y]; rewrite -!eq_in_ratr ?rmorphM ?rmorph1.
Qed.

End FromRatAlgType.
