(** * Combi.SymGroup.Bruhat_order : The Bruhat order on the Symmetric Group   *)
(******************************************************************************)
(*      Copyright (C) 2016-2021 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * The (strong) Bruhat order on the Symmetric Group

The goal of this file is to define the (strong) Bruhat order on the symmetric
group. We use the technique of growth matrices.

We define the following notations where the matrices [m] and [M] have types
[m : 'M[nat]_n] and [M : 'M[nat]_(n.+1)]:

Matrix sums:

- [mxsum m]   == matrix in ['M[nat]_(n.+1)] whose entries are the sum of the
                 entries strictly at its north-west in [m].
- [mxdiff M]  == the matrix in ['M[nat]_n] such that

           [mxdiff M i j =  M i.+1 j.+1 + M i j - M i j.+1 - M i.+1 j].

Matrix sum of permutation matrices:

- [is_pmxsum_row M] == for any [i] the i-th row of [M] is increassing
                 from [0] to [i].
- [is_pmxsum_pos M] == for any [i j] one have the following inegality

           [M i.+1 j.+1 + M i j >= M i j.+1 - M i.+1 j].

- [is_pmxsum M] == M is the matrix sum of a permutation matrix

Bruhat Order:

- [s <=B t]   == [s] is smaller than [t] for the right weak order.
- [s <B t]    == [s] is strictly smaller  than [t] for the right weak order.

***************************)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup perm morphism presentation.
From mathcomp Require Import ssralg matrix.

Require Import permcomp tools permuted combclass congr presentSn.
Require Import std ordtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Open Scope ring_scope.
#[local] Open Scope nat_scope.
Import GroupScope GRing.Theory.
Import Order.Theory.


Reserved Notation "s '<=B' t" (at level 70, t at next level).
Reserved Notation "s '<B' t"  (at level 70, t at next level).


#[local] Open Scope Combi_scope.


Lemma bounded_le_homo (m n : nat) f :
  (forall i, m <= i < n -> f i <= f i.+1) ->
  {in [pred i | m <= i & i <= n] &, {homo f : x y / x <= y}}.
Proof.
rewrite -!leEnat => H; apply Order.NatMonotonyTheory.nondecn_inP.
  move=> i j /[!inE] /andP[lemi _] /andP[_ lejn].
  move=> k /andP[/ltW/(le_trans lemi) lemk /ltW/le_trans/(_ lejn) lekn].
  by rewrite inE lemk lekn.
by move=> i /[!inE] /andP[lemi _] /andP[_ lein]; apply: H; rewrite lemi.
Qed.

Lemma telescope_sumn_in2 n m f : n <= m ->
  {in [pred i | n <= i <= m] &, {homo f : x y / x <= y}} ->
  \sum_(n <= k < m) (f k.+1 - f k) = f m - f n.
Proof.
move=> nm fle; rewrite (telescope_big (fun i j => f j - f i)).
  by case: ltngtP nm => // -> /[!subnn].
move=> k /andP[nk km] /=.
by rewrite addnBAC ?fle 1?ltnW// ?subnKC// ?fle//
     inE ?leqnn ltnW // ?(ltn_trans nk) //= ltnW.
Qed.


Section PermMX.

Variable (R : semiRingType) (n : nat).
Implicit Type (s t : 'S_n).

Lemma perm_mx_eq1 s : (@perm_mx R n s == 1%:M) = (s == 1).
Proof.
apply/eqP/eqP=> [| -> /[!perm_mx1] //].
rewrite /perm_mx row_permEsub => /esym Heq.
apply/permP=> /= i /[!perm1].
move/(congr1 (fun m : 'M__ => m i i)): Heq; rewrite !mxE eq_refl /=.
by case: eqP => //= _ /eqP /[!oner_eq0].
Qed.

Lemma perm_mx_inj : injective (@perm_mx R n).
Proof.
move=> s t /(congr1 (mulmx (perm_mx t^-1)))/eqP.
rewrite -!perm_mxM mulVg perm_mx1 perm_mx_eq1 => /eqP/(congr1 (mulg t)).
by rewrite mulgA mulgV mulg1 mul1g.
Qed.

Lemma is_perm_mx_sumP (m : 'M[nat]_n) :
  reflect ((forall (i : 'I_n), \sum_j m i j = 1%R) /\
           (forall (j : 'I_n), \sum_i m i j = 1%R))
    (is_perm_mx m).
Proof.
apply (iffP existsP) => /= [[/= s /eqP ->{m}]| [sum_row sum_col]].
  have byrow : forall s (i : 'I_n), \sum_(j < n) perm_mx s i j = 1%R.
    move=> {}s i; rewrite (bigD1 (s i)) //= !mxE eq_refl big1 ?addn0 // => j.
    by rewrite !mxE eq_sym => /negbTE ->.
  split => i; first exact: byrow.
  rewrite -[RHS](byrow s^-1 i); apply eq_bigr => j _.
  by rewrite !mxE -[in RHS](inj_eq (@perm_inj _ s)) permKV eq_sym.
have pex i : { j | (m i j == 1%N) && [forall k, (k != j) ==> (m i k == 0%N)] }.
  apply sigW; have /eqP/sum_nat_eq1[/= j [_ mij1 mi0]] := sum_row i.
  exists j; rewrite {}mij1 /=; apply/forallP => k.
  by apply/implyP => /mi0 ->.
have pex_inj : injective (fun i : 'I_n => proj1_sig (pex i)).
  move=> /= i j.
  case: (pex i) => k /= /andP[/eqP mik _].
  case: (pex j) => kj /= /[swap] <-{kj} /andP[/eqP mjk _].
  have /eqP/sum_nat_eq1[/= i0 [_ mi0k neqi0]] := sum_col k.
  have {neqi0} eqi0 l : m l k = 1%N -> l = i0.
    by move/eqP; apply/contraTeq => /neqi0 ->.
  by rewrite (eqi0 _ mik) (eqi0 _ mjk).
exists (perm pex_inj); apply/eqP/matrixP=> i j /[!mxE] /[!permE].
case: (pex i) => k /= /andP[/eqP mik /forallP/= neq0].
case: eqP => [<-{j} // | /eqP]; rewrite eq_sym.
by have /implyP/[apply]/eqP-> := neq0 j.
Qed.

End PermMX.

#[local] Lemma lti1 n (i : 'I_n) : i.+1 < n.+1. by rewrite ltnS. Qed.
#[local] Lemma lti  n (i : 'I_n) : i    < n.+1. exact: (ltnW (lti1 _)). Qed.
#[local] Lemma lei  n (i : 'I_n.+1) : i <= n. by rewrite -ltnS. Qed.
#[local] Lemma inord0 n : inord 0 = ord0 :> 'I_n.+1.
by apply val_inj; rewrite /= inordK. Qed.
#[local] Lemma inord_max n : inord n = ord_max :> 'I_n.+1.
by apply val_inj; rewrite /= inordK. Qed.
#[local] Hint Resolve lti1 lti perm_inj lei : core.

Lemma setIE (T : finType) (pA pB : pred T) :
  [set y | pA y & pB y] = [set y | pA y] :&: [set y | pB y].
Proof. by apply/setP=> x /[!inE]. Qed.

Lemma sum_lt1 n k : k <= n -> \sum_(i < n | i < k) 1 = k.
Proof.
move=> lekn.
rewrite -(big_ord_widen _ (fun => 1%N) lekn).
by rewrite big_const_ord iter_addn_0 mul1n.
Qed.


Definition mxsum {n : nat} (m : 'M[nat]_n) : 'M[nat]_n.+1 :=
  \matrix_(i, j) \sum_(k < n | k < i) \sum_(l < n | l < j) m k l.

Definition mxdiff {n : nat} (M : 'M[nat]_n.+1) : 'M[nat]_n :=
  \matrix_(i < n, j < n)
    (   M (inord i.+1) (inord j.+1) + M (inord i) (inord j)
      - M (inord i) (inord j.+1) - M (inord i.+1) (inord j) ).

Lemma mxsumE n0 (n := n0.+1) (m : 'M[nat]_n) (i j : nat) :
  i < n.+1 -> j < n.+1 ->
  @mxsum n m (inord i) (inord j) =
    \sum_(0 <= k < i) \sum_(0 <= l < j) m (inord k) (inord l).
Proof.
rewrite mxE !ltnS => lein lejn.
rewrite [RHS](big_nat_widen _ _ n) //= big_mkord inordK //.
apply eq_bigr => k _.
rewrite [RHS](big_nat_widen _ _ n) //= big_mkord inordK //.
by apply eq_bigr => l _; rewrite !inord_val.
Qed.


Section MatrixSum.

Context {n : nat}.
Implicit Type (m : 'M[nat]_n).
Implicit Type (M : 'M[nat]_n.+1).
Implicit Type (s : 'S_n).

#[local] Notation mxsum := (@mxsum n).

Lemma mxsum_tr m : mxsum m^T = (mxsum m)^T.
Proof.
apply matrixP=> i j /[!mxE]; rewrite exchange_big_idem //=.
by apply: eq_bigr => k ltkj; apply: eq_bigr => l ltli /[!mxE].
Qed.

Lemma mxdiff_tr M : mxdiff M^T = (mxdiff M)^T.
Proof. by apply matrixP=> i j /[!mxE]; rewrite -subnDAC subnDA. Qed.

Lemma mxsumK : cancel mxsum mxdiff.
Proof.
case: n => [| n0] m; first by apply matrixP => [[]] .
apply matrixP=> i j /[1!mxE] /[!mxsumE] //.
rewrite !big_nat_recr /= // !inord_val.
by rewrite -!addnA [X in X - _ - _]addnC addnK addnC -addnA addnK.
Qed.

Lemma perm_mxsum_inj : injective (mxsum \o perm_mx).
Proof. exact (inj_comp (can_inj mxsumK) (@perm_mx_inj _ _)). Qed.

Lemma perm_mxsumE s i j :
  (mxsum \o perm_mx) s i j = \sum_(k < n | (k < i) && (s k < j)) 1%N.
Proof.
rewrite !mxE big_mkcondr_idem //=; apply eq_bigr => k _.
under eq_bigr => l _ do rewrite !mxE /= eq_sym.
case: ltnP => [ltskj | lejsk].
  by rewrite (bigD1 (s k)) //= eq_refl big1 // => l /andP[_ /negbTE->].
rewrite big1 // => l /leq_trans/(_ lejsk) /ltn_eqF.
by rewrite -(val_eqE l (s k)) => ->.
Qed.

Lemma perm_mxsum1 i j : mxsum (perm_mx 1) i j = minn i j.
Proof.
rewrite perm_mxsumE (eq_bigl (fun k : 'I_n => k < minn i j)).
  exact (sum_lt1 (leq_trans (geq_minr i j) (ltn_ord j))).
by move=> k; rewrite perm1 ltn_min.
Qed.

Lemma perm_mxsum_maxperm i j : mxsum (perm_mx maxperm) i j = i + j - n.
Proof.
rewrite perm_mxsumE.
rewrite (eq_bigl (fun k : 'I_n => (k < i) && (n - j <= k))); first last.
  by move=> k; rewrite permE /= ltn_subCl // ltnS.
rewrite -(big_geq_mkord _ _ (gtn i) (fun => 1%N)) /=.
rewrite -(big_nat_widen _ _ _ predT) //=.
by rewrite big_const_nat iter_addn_0 mul1n subnBA.
Qed.

End MatrixSum.


Section IsPermMatrixSum.

Context {n : nat}.
Implicit Type (m : 'M[nat]_n).
Implicit Type (M : 'M[nat]_n.+1).
Implicit Type (s : 'S_n).

Definition is_pmxsum_row M :=
  [forall i : 'I_n.+1,
      [&& (M i ord0 == 0), (M i ord_max == i) &
          [forall j : 'I_n.+1, M i (inord j.-1) <= M i j]]].

Definition is_pmxsum_pos M :=
  [forall i : 'I_n, forall j : 'I_n,
      M (inord i.+1) (inord j.+1) + M (inord i) (inord j) >=
      M (inord i) (inord j.+1)    + M (inord i.+1) (inord j) ].

Definition is_pmxsum M :=
  [&& is_pmxsum_row M, is_pmxsum_row M^T & is_pmxsum_pos M].

Lemma is_pmxsum_rowP M :
  reflect
    [/\ (forall i : 'I_n.+1, M i ord0 = 0),
        (forall i : 'I_n.+1, M i ord_max = i) &
         forall i j : 'I_n.+1,  M i (inord j.-1) <= M i j]
    (is_pmxsum_row M).
Proof.
apply (iffP forallP) => /= [H | [H0 Hmax Hincr i]].
  by split => [i|i|i j]; move/(_ i): H => /and3P[/eqP H0 /eqP Hi /forallP].
by apply/and3P; split; try exact/eqP; apply/forallP.
Qed.

Lemma is_pmxsum_posP M :
  reflect (forall i j : 'I_n,
        M (inord i.+1) (inord j.+1) + M (inord i) (inord j) >=
        M (inord i) (inord j.+1)    + M (inord i.+1) (inord j))
    (is_pmxsum_pos M).
Proof.
apply (iffP forallP) => /= [H i j | H i]; last exact/forallP.
by move/(_ i)/forallP : H; apply.
Qed.

Lemma is_pmxsum_tr M : is_pmxsum M^T = is_pmxsum M.
Proof.
suff {M} impl M : is_pmxsum M -> is_pmxsum M^T.
  apply/idP/idP; last exact: impl.
  by rewrite -{2}(trmxK M); apply: impl.
rewrite /is_pmxsum trmxK => /and3P[-> -> /=] /is_pmxsum_posP H.
by apply/is_pmxsum_posP => i j /[!mxE] /[1!addnC].
Qed.

Lemma is_perm_mxsum_rowP s : is_pmxsum_row (mxsum (perm_mx s)).
Proof.
apply/is_pmxsum_rowP; split=> [i | i | i j]; rewrite !perm_mxsumE.
- by rewrite !big_mkcondr_idem //=; apply big1.
- rewrite (eq_bigl (fun k : 'I_n => k < i)) ?sum_lt1 // => k /=.
  by rewrite ltn_ord andbC.
- apply sub_le_big => //=; first by move=> a b; apply leq_addr.
  move=> k /andP[->] /= /leq_trans; apply.
  by rewrite inordK ?leq_pred // (leq_ltn_trans (leq_pred _)).
Qed.

End IsPermMatrixSum.


Lemma sum_mxdiff n0 (n := n0.+1) (M : 'M[nat]_n.+1) k j:
  is_pmxsum M -> k < n -> j <= n ->
  \sum_(0 <= l < j) mxdiff M (inord k) (inord l) =
    M (inord k.+1) (inord j) - M (inord k) (inord j).
Proof.
move=> /[dup] HM /and3P[/is_pmxsum_rowP[R0 _ _]
                        /is_pmxsum_rowP[_ _ Cincr]
                        /is_pmxsum_posP Mpos ] ltkn lejn.
have {}Cincr i l (ltin : i < n) :
    M (inord i) (inord l) <= M (inord i.+1) (inord l).
  by move/(_ (inord l) (inord i.+1)): Cincr; rewrite !mxE inordK // !ltnS.
pose F l := M (inord k.+1) (inord l) - M (inord k) (inord l).
transitivity (\sum_(0 <= l < j) (F l.+1 - F l)).
  rewrite !big_nat; apply eq_bigr => l /= /leq_trans/(_ lejn) ltln.
  rewrite mxE !inordK // subnBA; last exact: Cincr.
  by congr (_ - _); rewrite addnBAC //; exact: Cincr.
rewrite {}/F telescope_sumn_in2 //; first by rewrite !inord0 !R0 !subn0.
apply: bounded_le_homo => l /= /leq_trans/(_ lejn) ltln.
rewrite leq_subLR addnBA /=; last exact: Cincr.
move/(_ (Ordinal ltkn) (Ordinal ltln)): Mpos => /= Mpos.
rewrite leq_subRL [X in _ <= X]addnC //.
exact: (leq_trans (leq_addr _ _) Mpos).
Qed.


Section PermMatrixSum.

Context {n : nat}.
Implicit Types (s : 'S_n) (M : 'M[nat]_n.+1).

Lemma is_perm_mxsum_posP s : is_pmxsum_pos (mxsum (perm_mx s)).
Proof.
case: n s => [|n0] s; apply/is_pmxsum_posP => i j; first by case: i.
rewrite !mxsumE // !big_nat_recr //=.
by rewrite -!addnA leq_add2l addnC leq_add2l leq_addl.
Qed.

Lemma mxsum_perm_mx_is_pmxsum s : is_pmxsum (mxsum (perm_mx s)).
Proof.
rewrite /is_pmxsum -mxsum_tr tr_perm_mx.
by rewrite !is_perm_mxsum_rowP is_perm_mxsum_posP.
Qed.

Lemma is_pmxsum_mxdiff M : is_pmxsum M -> is_perm_mx (mxdiff M).
Proof.
case: n M => [|n0] M.
  by move=> _; apply/existsP; exists 1; apply/eqP/matrixP => [][].
suff {M} rowsum (M : 'M_n0.+2) i : is_pmxsum M -> \sum_j mxdiff M i j = 1%R.
  move=> H; apply/is_perm_mx_sumP; split => i; first exact: rowsum.
  transitivity (\sum_j mxdiff M^T i j).
    by apply eq_bigr => j _; rewrite mxdiff_tr [RHS]mxE.
  by apply: rowsum; rewrite is_pmxsum_tr.
move=> /[dup] HM /and3P[/is_pmxsum_rowP[_ Rmax _] _ _].
transitivity (\sum_(0 <= l < n0.+1) mxdiff M (inord i) (inord l)).
  by rewrite big_mkord; apply eq_bigr => j _; rewrite !inord_val.
by rewrite sum_mxdiff // inord_max !Rmax !inordK ?subSnn.
Qed.

Lemma mxdiffK : {in @is_pmxsum n, cancel (@mxdiff n) (@mxsum n)}.
Proof.
case: n => [|n0].
  move=> M /and3P[/is_pmxsum_rowP[C0 _ _] _ _].
  by apply/matrixP => i j; rewrite !mxE !big_ord0 !ord1 C0.
set n' := n0.+1 => M /[dup] HM /and3P[_ /is_pmxsum_rowP[C0 _ Cincr] _].
have {}C0 i : M ord0 i = 0 by move/(_ i): C0 => /[!mxE].
have {}Cincr i j (ltin : i < n') :
    M (inord i) (inord j) <= M (inord i.+1) (inord j).
  by move/(_ (inord j) (inord i.+1)): Cincr; rewrite !mxE inordK // ltnS.
apply matrixP=> i j; rewrite -{1}(inord_val i) -{1}(inord_val j) mxsumE //.
transitivity
    ( \sum_(0 <= k < i) (M (inord k.+1) (inord j) - M (inord k) (inord j)) ).
  rewrite !big_nat; apply: eq_bigr => k /= /leq_trans/(_ (ltn_ord i)) ltkn /=.
  exact: sum_mxdiff.
rewrite telescope_sumn_in2 //; first by rewrite !inord_val inord0 C0 subn0.
apply: bounded_le_homo => k /= ltki.
by apply/Cincr/(leq_trans ltki).
Qed.

Lemma is_pmxsumP M : reflect (exists s, M = mxsum (perm_mx s)) (is_pmxsum M).
Proof.
apply (iffP idP) => [H | [s ->]]; last exact: mxsum_perm_mx_is_pmxsum.
have/is_pmxsum_mxdiff/existsP[/= s /eqP Heq] := H.
by exists s; rewrite -{}Heq mxdiffK.
Qed.

End PermMatrixSum.


Fact Bruhat_display : Order.disp_t. Proof. by []. Qed.

Module BruhatOrder.
Section Def.

Context {n : nat}.
Implicit Type (s t u v : 'S_n).

#[local] Notation perm_mxsum := (@mxsum n \o (perm_mx (n := n))).

Definition Bruhat s t :=
  [forall i, forall j, perm_mxsum s i j >= perm_mxsum t i j].

Lemma BruhatP s t :
  reflect (forall i, forall j, perm_mxsum s i j >= perm_mxsum t i j)
    (Bruhat s t).
Proof. by apply (iffP forallP) => /= H i; apply/forallP. Qed.

Fact Bruhat_refl : reflexive Bruhat.
Proof. by move=> s; apply/BruhatP. Qed.
Fact Bruhat_anti : antisymmetric Bruhat.
Proof.
move=>s t /andP[/BruhatP lets /BruhatP lest].
apply perm_mxsum_inj; apply/matrixP=> i j; apply anti_leq.
by rewrite lest lets.
Qed.
Fact Bruhat_trans : transitive Bruhat.
Proof.
move=>t s u /BruhatP lets /BruhatP leut; apply/BruhatP=> i j.
exact: (leq_trans (leut i j) (lets i j)).
Qed.

#[export] HB.instance Definition _ := Finite.on 'S_n.
#[export] HB.instance Definition _ :=
  Order.Le_isPOrder.Build Bruhat_display 'S_n
    Bruhat_refl Bruhat_anti Bruhat_trans.

#[local] Notation "x <=B y" := (@Order.le Bruhat_display _ (x : 'S__) y).

Fact Bruhat1s s : 1 <=B s.
Proof.
suff lecoeff t i j : perm_mxsum t i j <= i.
  apply/BruhatP => i j; rewrite perm_mxsum1 leq_min lecoeff /=.
  rewrite [X in X <= _](_ : _ = (mxsum (perm_mx s))^T j i);
    last by rewrite !mxE.
  by rewrite -mxsum_tr tr_perm_mx lecoeff.
rewrite perm_mxsumE.
have /sum_lt1 {2}<- : i <= n by [].
rewrite [X in _ <= X](bigID (fun k => t k < j)) /=.
exact: leq_addr.
Qed.
#[export] HB.instance Definition _ :=
  Order.hasBottom.Build Bruhat_display 'S_n Bruhat1s.

Fact Bruhat_maxperm s : s <=B maxperm.
Proof.
apply/BruhatP => i j; rewrite perm_mxsum_maxperm perm_mxsumE.
rewrite sum1dep_card setIE cardsI.
rewrite -[X in _ <=_ + X - _](card_imset _ (@perm_inj _ s)) /=.
rewrite [imset _ _](_ : _ = [set x : 'I_n | x < j]); first last.
  apply/setP => /= k /[!inE].
  by rewrite -(permKV s k) mem_imset // inE permKV.
rewrite -![in X in _ <= X - _]sum1dep_card !sum_lt1 //; apply: leq_sub2l.
rewrite -[X in _ <= X](card_ord n) -cardsT /=.
exact/subset_leq_card/subsetT.
Qed.

#[export] HB.instance Definition _ :=
  Order.hasTop.Build Bruhat_display 'S_n Bruhat_maxperm.

End Def.

Module Exports.
HB.reexport BruhatOrder.

Notation "x <=B y" := (@Order.le Bruhat_display _ (x : 'S__) y) : Combi_scope.
Notation "x <B y" := (@Order.lt Bruhat_display _ (x : 'S__) y) : Combi_scope.

Section Exports.

Context {n : nat}.

Definition BruhatP (s t : 'S_n) :
  reflect
    (forall i j, mxsum (perm_mx s) i j >= mxsum (perm_mx t) i j) (s <=B t)
  := BruhatP s t.

Lemma bottom_Bruhat : Order.bottom = (1 : 'S_n). Proof. by []. Qed.
Lemma top_Bruhat : Order.top = (maxperm : 'S_n). Proof. by []. Qed.

End Exports.
End Exports.
End BruhatOrder.
HB.export BruhatOrder.Exports.


Section Symmetry.

Context {n : nat}.
Implicit Types (s t : 'S_n).

Lemma BruhatV s t : (s^-1 <=B t^-1) = (s <=B t).
Proof.
suff {s t} impl (s t : 'S_n) : (s <=B t) -> (s^-1 <=B t^-1).
  apply/idP/idP; last exact: impl.
  by move/impl; rewrite !invgK.
move/BruhatP=> H; apply/BruhatP=> i j.
by rewrite -!tr_perm_mx !mxsum_tr ![_^T _ _]mxE.
Qed.

Lemma Bruhat_maxM s t : (s * maxperm <=B t * maxperm) = (t <=B s).
Proof.
case: n s t => [|n0] s t; first by rewrite !permS0 lexx.
suff {s t} impl (s t : 'S_n0.+1) : (s <=B t) -> (t * maxperm<=B s * maxperm).
  apply/idP/idP; last exact: impl.
  by move/impl; rewrite -!mulgA -{2 4}maxpermV !mulgV !mulg1.
set N := n0.+1 in s t *.
suff {s t} mxsum_maxpermM i j (s : 'S_N) :
    mxsum (perm_mx (s * maxperm)) i j = i - mxsum (perm_mx s) i (rev_ord j).
  move/BruhatP=> HB; apply/BruhatP=> i j.
  by rewrite !{}mxsum_maxpermM; apply/leq_sub2l/HB.
have /[!ltnS]/sum_lt1 <- := ltn_ord i.
rewrite !perm_mxsumE !big_mkcondr_idem //=.
set S := (X in _ = _ - X); apply/eqP; rewrite -(eqn_add2r S) subnK; first last.
  by rewrite {}/S; apply leq_sum => k _; case: ltnP.
rewrite {}/S -big_split_idem //=.
apply/eqP/eq_bigr => k ltki; rewrite permM permE /=.
rewrite -subSn // !subSS leq_subCl leqNgt.
by case: ltnP => /= _; rewrite ?addn0 ?add0n.
Qed.

Lemma Bruhat_Mmax s t : (maxperm * s <=B maxperm * t) = (t <=B s).
Proof. by rewrite -[LHS]BruhatV !invMg !maxpermV Bruhat_maxM BruhatV. Qed.

Lemma Bruhat_conj_max s t : (s ^ maxperm <=B t ^ maxperm) = (s <=B t).
Proof. by rewrite /conjg maxpermV Bruhat_Mmax Bruhat_maxM. Qed.

End Symmetry.


Section RedWords.

Context {n0 : nat}.
#[local] Notation n := n0.+1.
Implicit Type (s t u v : 'S_n).


End RedWords.

(*
           0 0 0 0
            x
           0 1 1 1
              x
           0 1 2 2
0 0 0 0         x     0 0 0 0
 x         0 1 2 3       x
0 1 1 1               0 0 1 1
     x                 x
0 1 1 2               0 1 2 2
   x       0 0 0 0         x
0 1 2 3       x       0 1 2 3
           0 0 1 1
            x o x
           0 1 1 2
0 0 0 0       x       0 0 0 0
   x       0 1 2 3         x
0 0 1 1               0 0 0 1
     x                 x
0 0 1 2               0 1 1 2
 x         0 0 0 0       x
0 1 2 3         x     0 1 2 3
           0 0 0 1
              x
           0 0 1 2
            x
           0 1 2 3

 *)
