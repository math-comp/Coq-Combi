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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import tuple finfun bigop finset binomial fingroup perm.
Require Import morphism presentation.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ieqi1F i : (i == i.+1) = false. Proof. apply: negbTE; by elim i. Qed.
Lemma ieqi2F i : (i == i.+2) = false. Proof. apply: negbTE; by elim i. Qed.
Lemma i1eqiF i : (i.+1 == i) = false. Proof. apply: negbTE; by elim i. Qed.
Lemma i2eqiF i : (i.+2 == i) = false. Proof. apply: negbTE; by elim i. Qed.

Definition trivSimpl := (eq_refl, eqSS, ieqi1F, ieqi2F, i1eqiF, i2eqiF).

Import GroupScope.


Section Transp.

Variable T : finType.
Implicit Types (x y z t : T).

Lemma tperm3 x y z :
  x != y -> y != z ->
  tperm x y * tperm y z * tperm x y = tperm y z * tperm x y * tperm y z.
Proof.
  move=> Hxy Hyz.
  rewrite -{1}(tpermV x y) -mulgA -/(conjg _ _) tpermJ tpermR.
  rewrite -{1}(tpermV y z) -mulgA -/(conjg _ _) tpermJ tpermL.
  case: (altP (x =P z)) => [-> | Hxz].
  - by rewrite tpermR tpermL tpermC.
  - rewrite (tpermD Hxz Hyz).
    rewrite eq_sym in Hxy.
    rewrite eq_sym in Hxz.
    by rewrite (tpermD Hxy Hxz).
Qed.

Lemma tperm4 x y a b :
  x != a -> y != a -> x != b -> y != b ->
  tperm x y * tperm a b = tperm a b * tperm x y.
Proof.
  move=> Hxa Hya Hxb Hyb.
  rewrite -permP => i; rewrite !permM.
  case: (tpermP a b i) => [-> | -> |].
  - by rewrite (tpermD Hxa Hya) tpermL (tpermD Hxb Hyb).
  - by rewrite (tpermD Hxa Hya) (tpermD Hxb Hyb) tpermR.
  case: (tpermP x y i) => [ _ _ _ | _ _ _ | _ _ ].
  - rewrite eq_sym in Hya.
    rewrite eq_sym in Hyb.
    by rewrite tpermD.
  - rewrite eq_sym in Hxa.
    rewrite eq_sym in Hxb.
    by rewrite tpermD.
  - move=> /eqP; rewrite eq_sym => Hai.
  - move=> /eqP; rewrite eq_sym => Hbi.
    by rewrite tpermD.
Qed.

End Transp.


Section Coxeter.

Variable n : nat.

Definition eltr i : 'S_(n.+1) := tperm (inord i) (inord i.+1).

Lemma eltr_braid i :
  i.+1 < n ->
  (eltr i) * (eltr i.+1) * (eltr i) = (eltr i.+1) * (eltr i) * (eltr i.+1).
Proof.
  rewrite /eltr => Hi.
  apply: tperm3; rewrite /eq_op /=.
  - rewrite inordK; last by rewrite ltnS; apply ltnW; apply ltnW.
    rewrite inordK; last by rewrite ltnS; apply ltnW.
    by rewrite !trivSimpl.
  - rewrite inordK; last by rewrite ltnS; apply ltnW.
    rewrite inordK; last by rewrite ltnS.
    by rewrite !trivSimpl.
Qed.

Lemma eltr_comm i j :
  i.+1 < j < n ->
  (eltr i) * (eltr j) = (eltr j) * (eltr i).
Proof.
  move => /andP [] Hij Hj.
  apply: tperm4; rewrite /eq_op /=.
  - rewrite inordK; last by apply (leq_trans (ltnW Hij)); apply ltnW; apply ltnW.
    rewrite inordK; last by apply ltnW.
    by rewrite (ltn_eqF (ltnW Hij)).
  - rewrite inordK; last by apply (leq_trans (ltnW Hij)); apply ltnW.
    rewrite inordK; last by apply ltnW.
    by rewrite (ltn_eqF Hij).
  - rewrite inordK; last by apply (leq_trans (ltnW Hij)); apply ltnW; apply ltnW.
    rewrite inordK; last exact Hj.
    by rewrite (ltn_eqF (leq_trans (ltnW Hij) (leqnSn j))).
  - rewrite inordK; last by apply (leq_trans (ltnW Hij)); apply ltnW.
    rewrite inordK; last exact Hj.
    by rewrite eqSS (ltn_eqF (ltnW Hij)).
Qed.

Lemma Tij_j (i j : 'I_(n.+1)) :
  i <= j -> (\prod_(t <- (iota i (j - i))) eltr t) i = j.
Proof.
  move=> Hij; rewrite -{3}(inord_val i) -{1 3}(subKn Hij).
  elim: (j - i) (leq_subr i j) {Hij} => [_ | d IHd] {i}.
    by rewrite subn0 /= big_nil perm1 inord_val.
  rewrite /= big_cons => Hd.
  by rewrite permM /eltr tpermL (subnSK Hd) (IHd (ltnW Hd)).
Qed.

Lemma perm_on_Tij (i j : 'I_(n.+1)) :
  perm_on [set k : 'I_n.+1 | k <= j] (\prod_(t <- (iota i (j - i))) eltr t).
Proof.
  rewrite /perm_on; apply/subsetP => k; rewrite !inE.
  apply contraR; rewrite -ltnNge => Hjk.
  case (ltnP j i) => [/ltnW | Hij].
  - rewrite /leq => /eqP -> /=; by rewrite big_nil perm1.
  - rewrite -{1}(subKn Hij).
    elim: (j - i) (leq_subr i j) {Hij} => [| d IHd] {i}; first by rewrite big_nil perm1.
    rewrite /= big_cons => Hd.
    rewrite permM {2}/eltr (subnSK Hd) tpermD; last first.
    + have:= Hjk; apply contraL => /eqP <-.
      rewrite -ltnNge inordK; first by rewrite ltnS; apply leq_subr.
      rewrite ltnS; apply (leq_trans (leq_subr _ j)).
      rewrite -ltnS; apply (leq_trans Hjk); apply ltnW; by apply ltn_ord.
    + have:= Hjk; apply contraL => /eqP <-.
      rewrite -ltnNge inordK; first by rewrite ltnS; apply leq_subr.
      rewrite ltnS; apply (leq_trans (leq_subr _ j)).
      rewrite -ltnS; apply (leq_trans Hjk); apply ltnW; by apply ltn_ord.
    by apply (IHd (ltnW Hd)).
Qed.

Lemma perm_on_prod_eltrP m s :
  perm_on [set k : 'I_n.+1 | k <= m] s ->
  { ts : seq nat | s = \prod_(t <- ts) eltr t & all (gtn m) ts }.
Proof.
  elim: m s => [| m IHm] s Hon.
  - exists [::]; last by [].
    rewrite big_nil -permP=> i; rewrite perm1.
    case: i => [[|i] Hi].
    + case Hsi : (s (Ordinal Hi)) => [[|res] Hres]; first by apply val_inj.
      exfalso.
      have /(out_perm Hon) Htmp :
        (Ordinal Hres) \notin [set k : 'I_n.+1 | k <= 0] by rewrite inE.
      rewrite -Htmp in Hsi.
      have Habs := @perm_inj _ s (Ordinal Hi) (Ordinal Hres) Hsi.
      have := eq_refl (val (Ordinal Hi)); by rewrite {2}Habs /=.
    + apply: (out_perm Hon); by rewrite inE.
  - case (leqP m.+1 n) => Hm.
    + have Hm1 : m.+1 < n.+1 by rewrite ltnS.
      pose m1 := Ordinal Hm1.
      have : m1 \in [set k : 'I_n.+1 | k <= m.+1] by rewrite inE.
      rewrite -(perm_closed _ Hon) inE => Hsm1.
      pose srec := s * (\prod_(t <- (iota (s m1) (m1 - (s m1)))) eltr t).
      have {IHm} /IHm [] : perm_on [set k : 'I_n.+1 | k <= m] srec.
        rewrite /srec /perm_on; apply/subsetP => k.
        rewrite !inE; apply contraR; rewrite -ltnNge permM => Hk.
        apply/eqP; case (leqP k m.+1) => Hkm.
        * have -> : k = m1 by apply val_inj; apply/eqP => /=; rewrite eqn_leq Hkm Hk.
          by apply Tij_j.
        * have -> : s k = k by apply (out_perm Hon); rewrite inE -ltnNge.
          apply: (out_perm (perm_on_Tij _ _)).
          by rewrite inE -ltnNge.
      move=> tsrec; rewrite /srec => Hrec /allP Hall.
      exists (tsrec ++ rev (iota (s m1) (m1 - s m1))).
      * rewrite big_cat /= -Hrec -mulgA -big_cat /=.
        rewrite -{1}(mulg1 s); congr (s * _).
        elim/last_ind: (iota _ _) => [| w wn IHw] /=; first by rewrite /rev /= big_nil.
        rewrite rev_rcons -cat1s -cats1 catA -[(w ++ _) ++ _]catA cat1s -catA.
        rewrite !big_cat /=.
        have -> : \prod_(i <- [:: wn; wn]) eltr i = 1.
          by rewrite !big_cons big_nil mulg1 tperm2.
        by rewrite mul1g -big_cat /=.
      * rewrite all_cat; apply/andP; split; first by apply/allP => i /Hall /leq_trans; apply.
        apply/allP => i /=.
        rewrite mem_rev mem_iota => /andP [] _.
        by rewrite (subnKC Hsm1) => /leq_trans; apply.
    + move: Hon; have -> : [set k : 'I_n.+1 | k <= m.+1] = [set k : 'I_n.+1 | k <= m].
        rewrite -setP => i; have Hi := leq_trans (ltn_ord i) Hm.
        rewrite !inE (ltnW Hi).
        move: Hi; by rewrite ltnS => ->.
      move/IHm => [] ts Hs /allP Hall.
      exists ts; first exact Hs.
      apply/allP => i /Hall /= /leq_trans; by apply.
Qed.

Theorem prod_eltrP s :
  { ts : seq nat | s = \prod_(t <- ts) eltr t & all (gtn n) ts }.
Proof.
  apply perm_on_prod_eltrP.
  rewrite /perm_on; apply/subsetP => k _; rewrite !inE.
  rewrite -ltnS; by apply ltn_ord.
Qed.

Lemma eltr_ind (P : 'S_n.+1 -> Type) :
  P 1 -> (forall s i, i < n -> P s -> P (eltr i * s)) ->
  forall s, P s.
Proof.
  move=> H1 IH s.
  have [] := prod_eltrP s => ts -> {s}.
  elim: ts => [_ | t0 t IHt] /=; first by rewrite big_nil.
  move=> /andP [] Ht0 /IHt.
  rewrite big_cons; by apply: IH.
Qed.

Lemma inordi1 i : i < n -> (@inord n i != @inord n i.+1).
Proof.
  move=> Hi.
  rewrite /eq_op /= inordK; last by apply (leq_trans Hi).
  rewrite inordK; last by apply Hi.
  by rewrite ieqi1F.
Qed.

Lemma odd_size_permE ts :
  all (gtn n) ts -> odd (size ts) = odd_perm (\prod_(t <- ts) eltr t).
Proof.
  elim: ts => [_ | t0 t IHt] /=; first by rewrite big_nil odd_perm1.
  move=> /andP [] Ht0 /IHt{IHt} ->.
  by rewrite big_cons odd_mul_tperm (inordi1 Ht0) addTb.
Qed.

End Coxeter.



Lemma homg_S_3 :
  [set: 'S_3] \homg Grp ( s0 : s1 : (s0^+2 = s1^+2 = 1, s0*s1*s0 = s1*s0*s1) ).
Proof.
  apply/existsP; exists (eltr 2 0, eltr 2 1).
  rewrite /= !xpair_eqE /=; apply/and4P; split.
  + rewrite eqEsubset subsetT /=.
    apply/subsetP => s _.
    have [] := prod_eltrP s => ts -> {s} /allP Hall.
    elim: ts Hall => [| t0 t IHt] /= Ht.
      rewrite big_nil; by apply group1.
    rewrite big_cons; apply groupM => /=.
    * apply/bigcapP => S /subsetP; apply => {S}.
      rewrite inE.
      have {Ht t IHt} /Ht : t0 \in t0 :: t by rewrite in_cons eq_refl.
      case: t0 => [| [| //=]] _; apply/orP; [left|right]; by apply cycle_id.
    * apply: IHt => i Hi /=.
     apply: Ht; by rewrite inE Hi orbT.
  + by rewrite expgS expg1 tperm2.
  + by rewrite expgS expg1 tperm2.
  + apply/eqP; rewrite /eltr; apply: tperm3; by rewrite /eq_op /= !inordK.
Qed.

Lemma homg_S4 :
  [set: 'S_4] \homg Grp (
                s1 : s2 : s3 :
                  (s1*s1, s2*s2, s3*s3,
                   s1*s2*s1=s2*s1*s2, s2*s3*s2=s3*s2*s3,
                   s1*s3= s3*s1
              ) ).
Proof.
  apply/existsP; exists (eltr 3 0, eltr 3 1, eltr 3 2).
  rewrite /= !xpair_eqE /=; apply/and5P; split; last apply/and3P; try split.
  - rewrite eqEsubset subsetT /=.
    apply/subsetP => s _.
    have [] := prod_eltrP s => ts -> {s} /allP Hall.
    elim: ts Hall => [| t0 t IHt] /= Ht.
      rewrite big_nil; by apply group1.
    rewrite big_cons; apply groupM => /=.
    + apply/bigcapP => S /subsetP; apply => {S}.
      rewrite inE.
      have {Ht t IHt} /Ht : t0 \in t0 :: t by rewrite in_cons eq_refl.
      case: t0 => [| [| [| //=]]] _.
      * apply/orP; left; apply/bigcapP => S /subsetP; apply => {S}.
        rewrite inE; apply/orP; left; by apply cycle_id.
      * apply/orP; left; apply/bigcapP => S /subsetP; apply => {S}.
        rewrite inE; apply/orP; right; by apply cycle_id.
      * apply/orP; right; apply cycle_id.
    + apply: IHt => i Hi /=.
      apply: Ht; by rewrite inE Hi orbT.
  - by rewrite tperm2.
  - by rewrite tperm2.
  - by rewrite tperm2.
  - apply/eqP; rewrite /eltr; apply: tperm3; by rewrite /eq_op /= !inordK.
  - apply/eqP; rewrite /eltr; apply: tperm3; by rewrite /eq_op /= !inordK.
  - apply/eqP; rewrite /eltr; apply: tperm4; by rewrite /eq_op /= !inordK.
Qed.
