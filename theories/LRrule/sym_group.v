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

Lemma tperm_braid x y z :
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

Lemma tpermC x y a b :
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
  apply: tperm_braid; rewrite /eq_op /=.
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
  apply: tpermC; rewrite /eq_op /=.
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
    rewrite permM {2}/eltr (subnSK Hd) tpermD; first exact: (IHd (ltnW Hd)).
    + have:= Hjk; apply contraL => /eqP <-.
      rewrite -ltnNge inordK; first by rewrite ltnS; apply leq_subr.
      rewrite ltnS; apply (leq_trans (leq_subr _ j)).
      rewrite -ltnS; apply (leq_trans Hjk); apply ltnW; exact: ltn_ord.
    + have:= Hjk; apply contraL => /eqP <-.
      rewrite -ltnNge inordK; first by rewrite ltnS; apply leq_subr.
      rewrite ltnS; apply (leq_trans (leq_subr _ j)).
      rewrite -ltnS; apply (leq_trans Hjk); apply ltnW; exact: ltn_ord.
Qed.

Lemma prod_eltrK w :
  (\prod_(t <- w) eltr t) * (\prod_(t <- rev w) eltr t) = 1.
Proof.
  elim/last_ind: w => [| w wn IHw] /=.
    by rewrite /rev /= !big_nil mulg1.
  rewrite rev_rcons -cat1s -cats1 -big_cat /=.
  rewrite -catA -[wn :: rev w]cat1s [X in w ++ X]catA cat1s !big_cat /=.
  have -> : \prod_(i <- [:: wn; wn]) eltr i = 1.
    by rewrite !big_cons big_nil mulg1 tperm2.
  by rewrite mul1g.
Qed.

Definition is_code (c : seq nat) :=
  all (fun i => nth 0 c i <= i) (iota 0 (size c)).
Definition word_of_code (c : seq nat) : seq nat :=
  flatten [seq rev (iota (i - nth 0 c i) (nth 0 c i)) |
           i <- iota 0 (size c)].

Fixpoint code_rec m c (s : 'S_n.+1) : seq nat :=
  if m is m'.+1 then
    let mo := inord m' in
    code_rec m' (mo - s mo :: c)
             (s * (\prod_(t <- (iota (s mo) (mo - s mo))) eltr t))
  else c.
Definition code s := code_rec n.+1 [::] s.

Lemma is_codeP c :
  reflect (forall i, i < size c -> nth 0 c i <= i) (is_code c).
Proof.
  rewrite /is_code; apply (iffP idP).
  - move=> /allP Hcode => // i Hi.
    apply Hcode; by rewrite mem_iota /= add0n.
  - move=> Hcode; apply/allP => i; rewrite mem_iota add0n /=; exact: Hcode.
Qed.

Lemma word_of_codeE c :
  \prod_(t <- word_of_code c) eltr t =
  \prod_(i <- iota 0 (size c))
     \prod_(t <- rev (iota (i - nth 0 c i) (nth 0 c i))) eltr t.
Proof. by rewrite big_flatten /= big_map. Qed.

Lemma word_of_code_ltn c :
  is_code c -> all (gtn (size c).-1) (word_of_code c).
Proof.
  move=> /is_codeP Hcode.
  apply/allP => i /flatten_mapP [] j; rewrite mem_iota /= add0n => Hc.
  rewrite mem_rev mem_iota subnK; last exact: Hcode.
  move=> /andP [] _ /leq_trans; apply.
  by case: (size c) Hc.
Qed.

Lemma size_code_rec m s c : size (code_rec m c s) = m + size c.
Proof. by elim: m s c => [| m IHm] //= s c; rewrite IHm /= addSnnS. Qed.

Lemma size_code s : size (code s) = n.+1.
Proof. by rewrite size_code_rec addn0. Qed.

Let is_partcode m c :=
  forall i, i < size c -> nth 0 c i <= i + m.
Let word_of_partcode m c : seq nat :=
  flatten [seq rev (iota (m + i - nth 0 c i) (nth 0 c i)) |
           i <- iota 0 (size c)].

Lemma perm_on_code_recP m c s0 s :
  m <= n.+1 ->
  is_partcode m c ->
  s0 = s * \prod_(t <- word_of_partcode m c) eltr t ->
  perm_on [set k : 'I_n.+1 | k < m] s ->
  let cf := code_rec m c s in
    is_code cf /\ s0 = \prod_(t <- word_of_code cf) eltr t.
Proof.
  move=> Hm Hcode -> {s0}.
  elim: m c s Hm Hcode => [| m IHm] c s Hm Hcode Hon /=.
    split; first by apply/is_codeP => i; rewrite -{3}(addn0 i); apply Hcode.
    suff -> : s = 1 by rewrite mul1g.
    rewrite -permP => i; rewrite perm1.
    apply: (out_perm Hon); by rewrite inE.
  pose mo := Ordinal Hm.
  have -> : inord m = mo by apply val_inj; rewrite /= inordK.
  have : mo \in [set k : 'I_n.+1 | k < m.+1] by rewrite inE.
  rewrite -(perm_closed _ Hon) inE ltnS => Hsm.
  move/(_ _ _ (ltnW Hm)): IHm => Hrec.
  have /Hrec{Hrec Hcode}Hrec: is_partcode m (mo - s mo :: c).
    rewrite /is_partcode {Hrec} => [[_ | i]] /=.
      rewrite add0n; exact: leq_subr.
    by rewrite ltnS addSnnS => /Hcode.
  set srec := s * _.
  have /Hrec{Hrec} /= : perm_on [set k : 'I_n.+1 | k < m] srec.
    rewrite {Hrec} /srec /perm_on; apply/subsetP => k.
    rewrite !inE; apply contraR; rewrite -ltnNge permM ltnS => Hmk.
    apply/eqP; case (leqP k m) => Hkm.
    + have -> : k = mo by apply val_inj; apply/eqP; rewrite /= eqn_leq Hmk Hkm.
      exact: Tij_j.
    + have -> : s k = k by apply (out_perm Hon); rewrite inE -ltnNge.
      apply: (out_perm (perm_on_Tij _ _)).
      by rewrite inE -ltnNge.
  move=> [] Hcode <-; split; first exact: Hcode.
  rewrite {Hcode}/srec -mulgA; congr (s * _).
  rewrite /word_of_partcode /= addn0 (subKn Hsm) big_cat /=.
  rewrite mulgA prod_eltrK mul1g; apply congr_big => //; congr flatten.
  rewrite -(addn0 1%N) iota_addl -map_comp.
  apply eq_map => i /=.
  by rewrite addnA addn1.
Qed.

Lemma perm_on_codeP s :
  let c := code s in is_code c /\ s = \prod_(t <- word_of_code c) eltr t.
Proof.
  rewrite /code; apply perm_on_code_recP => //.
  - by rewrite /word_of_partcode /= big_nil mulg1.
  - rewrite /perm_on; apply/subsetP => k _; rewrite !inE; exact: ltn_ord.
Qed.

Lemma codeP s : is_code (code s).
Proof. by have:= perm_on_codeP s => /= [] []. Qed.

Lemma codeE s : s = \prod_(t <- word_of_code (code s)) eltr t.
Proof. by have:= perm_on_codeP s => /= [] []. Qed.

Theorem prod_eltr_ordP s :
  let ts : seq 'I_n := pmap insub (word_of_code (code s)) in
  s = \prod_(t <- ts) eltr t.
Proof.
  rewrite /= {1}(codeE s).
  rewrite -(big_map (@nat_of_ord _) xpredT) /=; apply congr_big => //.
  rewrite pmap_filter; last by move=> j /=; rewrite insubK.
  rewrite (eq_in_filter (a2 := xpredT)); first last.
    move=> j /= /(allP (word_of_code_ltn (codeP s))) /=.
    rewrite size_code => Hj; by rewrite insubT.
  by rewrite filter_predT.
Qed.

Lemma eltr_ind (P : 'S_n.+1 -> Type) :
  P 1 -> (forall s i, i < n -> P s -> P (eltr i * s)) ->
  forall s, P s.
Proof.
  move=> H1 IH s.
  have /= -> := prod_eltr_ordP s.
  elim: (pmap _ _)  => [| t0 t IHt] /=; first by rewrite big_nil.
  rewrite big_cons; by apply IH; first exact: ltn_ord.
Qed.

Lemma inordi1 i : i < n -> (@inord n i != @inord n i.+1).
Proof.
  move=> Hi.
  rewrite /eq_op /= inordK; last by apply (leq_trans Hi).
  rewrite inordK; last exact: Hi.
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
  [set: 'S_3] \homg Grp ( s0 : s1 : (s0^+2, s1^+2, s0*s1*s0 = s1*s0*s1) ).
Proof.
  apply/existsP; exists (eltr 2 0, eltr 2 1).
  rewrite /= !xpair_eqE /=; apply/and4P; split.
  - rewrite eqEsubset subsetT /=.
    apply/subsetP => s _.
    have /= -> := prod_eltr_ordP s.
    elim: (pmap _ _) => [| t0 t IHt] /=.
      rewrite big_nil; exact: group1.
    rewrite big_cons; apply groupM => /=.
    + apply/bigcapP => S /subsetP; apply => {S t IHt}; rewrite inE.
      case: t0 => [] [| [| //=]] /= _; apply/orP; [left|right]; exact: cycle_id.
    + apply: IHt => i Hi /=.
  - by rewrite expgS expg1 tperm2.
  - by rewrite expgS expg1 tperm2.
  - apply/eqP; rewrite /eltr; apply: tperm_braid; by rewrite /eq_op /= !inordK.
Qed.

(*
Lemma presentation_S_3 :
  [set: 'S_3] \isog Grp ( s1 : s2 : (s1*s1 = s2*s2 = 1, s1*s2*s1 = s2*s1*s2) ).
Proof.
  apply intro_isoGrp; first exact homg_S_3.
  move=> Gt H; case/existsP => /= [] [x1 x2] /eqP [] Hgen Hx1 Hx2 H3.
  apply/homgP.

Qed.
*)

Lemma homg_S4 :
  [set: 'S_4] \homg Grp (
                s1 : s2 : s3 :
                  (s1^+2, s2^+2, s3^+2,
                   s1*s2*s1 = s2*s1*s2, s2*s3*s2 = s3*s2*s3,
                   s1*s3 = s3*s1
              ) ).
Proof.
  apply/existsP; exists (eltr 3 0, eltr 3 1, eltr 3 2).
  rewrite /= !xpair_eqE /=; apply/and5P; split; last apply/and3P; try split.
  - rewrite eqEsubset subsetT /=.
    apply/subsetP => s _.
    have /= -> := prod_eltr_ordP s.
    elim: (pmap _ _) => [| t0 t IHt] /=.
      rewrite big_nil; exact: group1.
    rewrite big_cons; apply groupM => /=.
    + apply/bigcapP => S /subsetP; apply => {S t IHt}; rewrite inE.
      case: t0 => [] [| [| [| //=]]] /= _.
      * apply/orP; left; apply/bigcapP => S /subsetP; apply => {S}.
        rewrite inE; apply/orP; left; by apply cycle_id.
      * apply/orP; left; apply/bigcapP => S /subsetP; apply => {S}.
        rewrite inE; apply/orP; right; by apply cycle_id.
      * apply/orP; right; apply cycle_id.
    + apply: IHt => i Hi /=.
  - by rewrite expgS expg1 tperm2.
  - by rewrite expgS expg1 tperm2.
  - by rewrite expgS expg1 tperm2.
  - apply/eqP; rewrite /eltr; apply: tperm_braid; by rewrite /eq_op /= !inordK.
  - apply/eqP; rewrite /eltr; apply: tperm_braid; by rewrite /eq_op /= !inordK.
  - apply/eqP; rewrite /eltr; apply: tpermC; by rewrite /eq_op /= !inordK.
Qed.
