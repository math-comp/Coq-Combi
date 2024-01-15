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

We define the (strong) Bruhat order on the symmetric group.

We define the following notations:

- [s <=B t]   == [s] is smaller than [t] for the right weak order.
- [s <B t]    == [s] is strictly smaller  than [t] for the right weak order.

***************************)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup perm morphism presentation.
From mathcomp Require Import ssralg matrix ssrint.

Require Import permcomp tools permuted combclass congr presentSn.
Require Import std ordtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Import Order.Theory.

Reserved Notation "s '<=B' t" (at level 70, t at next level).
Reserved Notation "s '<B' t"  (at level 70, t at next level).


Section PermMX.

Variable (R : semiRingType) (n : nat).
Implicit Type (s t : 'S_n).

Lemma perm_mx1P s : (@perm_mx R n s == (1%:M)%R) = (s == 1).
Proof.
apply/eqP/eqP=> [| ->]; last by rewrite perm_mx1.
rewrite /perm_mx row_permEsub => Heq.
apply/permP=> /= i; rewrite perm1.
have:= erefl (rowsub s 1%:M i i : R)%R; rewrite {1}Heq !mxE eq_refl /=.
by case: eqP => //= _ /eqP; rewrite oner_eq0.
Qed.

Lemma perm_mx_inj  : injective (@perm_mx R n).
Proof.
move=> s t /(congr1 (mulmx (perm_mx t^-1))) /eqP.
rewrite -!perm_mxM gnorm perm_mx1 perm_mx1P => /eqP/(congr1 (mulg t)).
by rewrite !gnorm.
Qed.

End PermMX.

Lemma card_set_ord_leq_lt n i j :
  j < n.+1 -> #|[set k : 'I_n | i <= k < j]| = j - i.
Proof.
rewrite cardE /= /enum_mem size_filter -enumT /= => ltin.
rewrite (eq_count (a2 := preim val (fun k => i <= k < j)));
  last by move=> l; rewrite !inE.
rewrite -count_map val_enum_ord -size_filter.
by rewrite filter_predI iota_ltn // iota_geq size_iota.
Qed.

Lemma card_set_ord_lt n i :
  i < n.+1 -> #|[set k : 'I_n | k < i]| = i.
Proof.
rewrite [[set k : _ | _]](_ : _ = [set k : 'I_n | 0 <= k & k < i]).
  by move/card_set_ord_leq_lt => ->; rewrite subn0.
by apply/setP => /= k; rewrite inE.
Qed.

Fact Bruhat_display : unit. Proof. exact: tt. Qed.


Section GRMatrix.

Context {n0 : nat}.
#[local] Notation n := n0.+1.
Implicit Type (s t u v : 'S_n).


Definition grmx s : 'M_n.+1 :=
  \matrix_(i < n.+1, j < n.+1)
    #|[set k : 'I_n | k < j] :&: [set s k | k : 'I_n & k < i]|.

Lemma grmxV s : grmx s^-1 = ((grmx s)^T)%R.
Proof.
have sinj := perm_inj (s := s).
have s1inj := perm_inj (s := s^-1).
apply matrixP=> i j; rewrite !mxE.
rewrite -(card_imset _ sinj); congr (fun S : {set _} => #|S|).
rewrite -setP => /= k; rewrite inE.
rewrite -{1}(permKV s k) mem_imset // !inE mem_imset // inE.
rewrite andbC; congr andb.
by rewrite -{2}(permKV s k) mem_imset // inE.
Qed.

Lemma grmx_pairE s :
  grmx s = (\matrix_(i < n.+1, j < n.+1)
             #|[set p : 'I_n * 'I_n |
                 [&& \val p.1 < i, \val p.2 < j & (s p.1 == p.2)]]|)%R.
Proof.
apply/matrixP => i j; rewrite !mxE.
have mkpair_inj : injective (fun k : 'I_n => (s^-1 k, k)) by move=> k l [].
rewrite -(card_imset _ mkpair_inj); congr (fun s : {set _} => #|s|).
apply/setP => [][/= k l]; rewrite inE /=.
apply/imsetP/idP => [[/= m] |].
rewrite !inE => +[->{k} ->{l}] => /andP[-> /imsetP[k] /=].
  by rewrite inE => + ->; rewrite permKV eq_refl andbT permK.
rewrite andbA andbC  => /and3P[/eqP <-{l} leki leskj] /=.
exists (s k); last by rewrite permK.
by rewrite !inE {}leskj /=; apply/imsetP; exists k; rewrite // inE.
Qed.

(*
Lemma grmxV2 s : grmx s^-1 = ((grmx s)^T)%R.
Proof.
apply/matrixP => /= i j; rewrite !grmx_pairE !mxE /=.
pose swap p : 'I_n * 'I_n := (p.2, p.1).
have swapK : involutive swap by move=> [u v].
rewrite -(card_imset _ (inv_inj swapK)); congr (fun S : {set _} => #|S|).
apply/setP => /= [][k l]; rewrite !inE.
apply/imsetP/and3P => [[/= m] | /= [lej lei /eqP eqs]].
  by rewrite inE /= => + [-> ->] /= => /and3P[-> -> /eqP <- /=]; rewrite permKV.
by exists (l, k) => //; rewrite inE /= -{2}eqs permK lei lej /=.
Qed.
*)

Lemma grmxE s (i j : nat) :
  i < n.+1 -> j < n.+1 ->
  grmx s (inord i) (inord j) =
    (\sum_(k < i) \sum_(l < j) (s (inord k) == inord l)%:R)%R.
Proof.
rewrite grmx_pairE mxE !ltnS => lti ltj.
rewrite [RHS](big_ord_widen _
                (fun k => \sum_(l < j) (s (inord k) == inord l)%:R)%R lti).
under eq_bigr => k _ do
  rewrite (big_ord_widen _ (fun l => (s (inord k) == inord l)%:R)%R ltj).
rewrite pair_big_dep_idem //= -sum1dep_card.
rewrite -[LHS](eq_bigl (P1 := fun x : 'I_n * 'I_n =>
             (x.1 < i) && (x.2 < j) && (s x.1 == x.2))); first last.
  by move=> k; rewrite -andbA !inordK.
rewrite [LHS]big_mkcondr_idem //=.
apply eq_bigr => [][k l] /= /andP[ltki ltlj].
by rewrite !inord_val; case eqP.
Qed.

(** Unused ! Also this is not a characterisation of the grmx. It also
    include th growth matrix of alternating sign matrices             *)
Definition is_grmx_row (m : 'M[nat]_n.+1) :=
  [forall i : 'I_n.+1,
      [&& (m i ord0 == 0), (m i ord_max == i) &
          [forall j : 'I_n.+1,
              m i (inord j.-1) <= m i j <= (m i (inord j.-1)).+1]]].

Definition is_grmx (m : 'M[nat]_n.+1) := is_grmx_row m && is_grmx_row m^T.

Lemma is_grmx_rowP s : is_grmx_row (grmx s).
Proof.
have setlt0 : [set i : 'I_n | i < (@ord0 n)] = set0.
  by apply/setP => /= x; rewrite !inE.
apply/forallP => /= i; rewrite !mxE; apply/and3P; split.
- by rewrite setlt0 set0I cards0.
- have -> : [set i : 'I_n | i < (@ord_max n)] = [set: 'I_n].
    by apply/setP => /= x; rewrite !inE /= ltn_ord.
  by rewrite setTI (card_imset _ (perm_inj (s := s))) card_set_ord_lt.
- apply/forallP => /= j; rewrite !mxE.
  move: [set s k | k : 'I_n & _] => /= S.
  have /inordK -> : j.-1 < n.+1 by apply(leq_ltn_trans (leq_pred _)).
  case: j => [[|j] Hj] /=; first by rewrite setlt0 set0I cards0.
  have -> : [set i0 : 'I_n | i0 < j.+1] = inord j |: [set i0 : 'I_n | i0 < j].
    apply/setP => /= k; rewrite !inE -val_eqE /=.
    by rewrite inordK // ltnS leq_eqVlt.
  apply/andP; split.
  + apply/subset_leq_card/subsetP => /= k.
    by rewrite !inE => /andP[-> ->]; rewrite orbT.
  + have -> : (inord j |: [set i0 : 'I_n| i0 < j]) :&: S =
                [set inord j] :&: S :|: [set i0 : 'I_n | i0 < j] :&: S.
      by apply/setP => /= k; rewrite !inE Bool.andb_orb_distrib_l.
    apply (leq_trans (leq_card_setU _ _)); rewrite -[leqRHS]add1n leq_add2r.
    rewrite -[leqRHS](cards1 (@inord n0 j)).
    apply/subset_leq_card/subsetP => /= k.
    by rewrite !inE => /andP[].
Qed.

Lemma is_grmxP s : is_grmx (grmx s).
Proof. by rewrite /is_grmx -grmxV !is_grmx_rowP. Qed.


Definition perm_mx_of_grmx (m : 'M_n.+1) : 'M[int]_n :=
  \matrix_(i < n, j < n)
  (   (m (inord i.+1) (inord j.+1))%:Z - (m (inord i) (inord j.+1))%:Z
    - (m (inord i.+1) (inord j))%:Z    + (m (inord i) (inord j))%:Z )%R.

Lemma perm_mx_of_grmxP s : perm_mx_of_grmx (grmx s) = perm_mx s.
Proof.
apply/matrixP=> i j.
have lei1 : i.+1 < n.+1 by rewrite ltnS.
have lej1 : j.+1 < n.+1 by rewrite ltnS.
have lei : i < n.+1 by apply ltnW.
have lej : j < n.+1 by apply ltnW.
rewrite [LHS]mxE !grmxE // !mxE !big_ord_recr /= !inord_val.
rewrite !PoszD !opprD !addrA.
set S := (X in (_ + X)%R).
rewrite -/S -!addrA [(-S + _)%R]addrC !addrA addrK {S}.
set S := (X in (X + _ + _ + _ + _)%R).
rewrite -/S [(S +  _)%R]addrC addrC -!addrA [(S +  _)%R]addrC subrK {S}.
rewrite addrA addrC addrA subrK.
by case: eqP.
Qed.

Lemma grmx_inj : injective grmx.
Proof.
move=> s t /(congr1 perm_mx_of_grmx); rewrite !perm_mx_of_grmxP.
exact: perm_mx_inj.
Qed.

Lemma grmx1 i j : grmx 1 i j = minn i j.
Proof.
rewrite mxE (eq_imset (g := id)); last exact: perm1.
rewrite imset_id [_ :&: _](_ : _ = [set k : 'I_n | k < minn i j]); first last.
  by apply/setP => k; rewrite !inE ltn_min andbC.
rewrite card_set_ord_lt // ltnS.
exact: (leq_trans (geq_minr i j) (ltn_ord j)).
Qed.

Lemma grmx_maxperm i j : grmx maxperm i j = i + j - n.
Proof.
rewrite mxE.
rewrite [_ :&: _](_ : _ = [set k : 'I_n | n - i <= k < j]); first last.
  apply/setP => /= k; rewrite !inE -{2}(maxpermK k).
  rewrite mem_imset; last exact: (inv_inj (@maxpermK _)).
  rewrite inE permE /= ltn_subCl //; last exact: (ltn_ord i).
  by rewrite ltnS andbC.
by rewrite card_set_ord_leq_lt // subnCBA // -ltnS.
Qed.

End GRMatrix.


Module BruhatOrder.
Section Def.

Context {n0 : nat}.
#[local] Notation n := n0.+1.
Implicit Type (s t u v : 'S_n).

#[local] Notation grmx := (@grmx n0).

Definition Bruhat s t := [forall i, forall j, grmx s i j >= grmx t i j].

Lemma BruhatP s t :
  reflect (forall i, forall j, grmx s i j >= grmx t i j) (Bruhat s t).
Proof. by apply (iffP forallP) => /= H i; apply/forallP. Qed.

Fact Bruhat_refl : reflexive Bruhat.
Proof. by move=> s; apply/BruhatP. Qed.
Fact Bruhat_anti : antisymmetric Bruhat.
Proof.
move=>s t /andP[/BruhatP lets /BruhatP lest].
apply grmx_inj; apply/matrixP=> i j; apply anti_leq.
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

Local Notation "x <=B y" := (@Order.le Bruhat_display _ (x : 'S__) y).

Fact Bruhat1s s : (1 <=B s).
Proof.
apply/BruhatP => i j; rewrite grmx1 !mxE leq_min.
rewrite -{2}(card_set_ord_lt (ltn_ord i)) -{3}(card_set_ord_lt (ltn_ord j)).
apply/andP; split; last exact/subset_leq_card/subsetIl.
rewrite -[X in _ <= X](card_imset _ (@perm_inj _ s)).
exact/subset_leq_card/subsetIr.
Qed.
#[export] HB.instance Definition _ :=
  Order.hasBottom.Build Bruhat_display ('S_n) Bruhat1s.

Fact Bruhat_maxperm s : (s <=B maxperm).
Proof.
apply/BruhatP => i j; rewrite grmx_maxperm !mxE.
rewrite cardsI card_imset; last exact: perm_inj.
rewrite !card_set_ord_lt // addnC; apply: leq_sub2l.
rewrite -[X in _ <= X](card_ord n) -cardsT /=.
exact/subset_leq_card/subsetT.
Qed.

#[export] HB.instance Definition _ :=
  Order.hasTop.Build Bruhat_display ('S_n) Bruhat_maxperm.

End Def.

Module Exports.
HB.reexport BruhatOrder.

Notation "x <=B y" := (@Order.le Bruhat_display _ (x : 'S__) y).
Notation "x <B y" := (@Order.lt Bruhat_display _ (x : 'S__) y).

Definition BruhatP {n0} (s t : 'S_n0.+1) :
  reflect (forall i, forall j, grmx s i j >= grmx t i j) (s <=B t)
  := (BruhatP s t).

Lemma bottom_Bruhat n0 : Order.bottom = (1 : 'S_n0.+1). Proof. by []. Qed.
Lemma top_Bruhat n0 : Order.top = @maxperm n0. Proof. by []. Qed.

End Exports.
End BruhatOrder.
HB.export BruhatOrder.Exports.



(*
           0 0 0 0
            x
           0 1 1 1
              x
           0 1 2 2
                x
           0 1 2 3


0 0 0 0               0 0 0 0
 x                       x
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
 x                       x
0 1 2 3               0 1 2 3


           0 0 0 0
                x
           0 0 0 1
              x
           0 0 1 2
            x
           0 1 2 3

 *)
