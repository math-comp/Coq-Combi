(** * Combi.LRrule.sym_group : The symmetric group *)
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
(** * The symmetric group

The main goal is to show that elementary transpositions generate
the symmetric groups as a Coxeter group.

- eltr n i == the i-th elementary transposition in 'S_n.+1.
- cocode s == the recursively defined Lehmer code of s^-1.
***************************)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import tuple finfun bigop finset binomial fingroup perm.
Require Import morphism presentation.

Require Import tools.

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

Implicit Type s t : 'S_n.+1.

Definition eltr i : 'S_n.+1 := tperm (inord i) (inord i.+1).

Local Notation "''s_' i" := (eltr i) (at level 8, i at level 2).
Local Notation "''s_[' w ']'" := (\prod_(i <- w) 's_i) (at level 8, w at level 2).
Local Notation "''II_' n" := ('I_n * 'I_n)%type (at level 8, n at level 2).

Lemma eltr_braid i :
  i.+1 < n -> 's_i * 's_i.+1 * 's_i = 's_i.+1 * 's_i * 's_i.+1.
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
  i.+1 < j < n -> 's_i * 's_j = 's_j * 's_i.
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
  i <= j -> 's_[iota i (j - i)] i = j.
Proof.
  move=> Hij; rewrite -{3}(inord_val i) -{1 3}(subKn Hij).
  elim: (j - i) (leq_subr i j) {Hij} => [_ | d IHd] {i}.
    by rewrite subn0 /= big_nil perm1 inord_val.
  rewrite /= big_cons => Hd.
  by rewrite permM /eltr tpermL (subnSK Hd) (IHd (ltnW Hd)).
Qed.

Lemma perm_on_Tij (i j : 'I_(n.+1)) :
  perm_on [set k : 'I_n.+1 | k <= j] 's_[iota i (j - i)].
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
  's_[w] * 's_[rev w] = 1.
Proof.
  elim/last_ind: w => [| w wn IHw] /=.
    by rewrite /rev /= !big_nil mulg1.
  rewrite rev_rcons -cat1s -cats1 -big_cat /=.
  rewrite -catA -[wn :: rev w]cat1s [X in w ++ X]catA cat1s !big_cat /=.
  suff -> : 's_[[:: wn; wn]] = 1 by rewrite mul1g.
  by rewrite big_cons big_seq1 tperm2.
Qed.


Definition invset (s : 'S_n.+1) :=
  [set p : 'I_n.+1 * 'I_n.+1 | (p.1 < p.2) && (s p.1 > s p.2) ].
Definition length s := #|invset s|.

Lemma length1 : length 1 = 0.
Proof.
  rewrite /length /invset.
  apply/eqP; rewrite cards_eq0; apply/eqP.
  rewrite -setP => [[i j]]; rewrite !inE /= !perm1.
  apply (introF idP) => /andP [] /ltn_trans H/H{H}.
  by rewrite ltnn.
Qed.

Lemma length_permV s : length s^-1 = length s.
Proof.
  rewrite /length /invset.
  pose f t := fun p : 'II_n.+1 => (t p.2, t p.1) : 'II_n.+1.
  have fcan t : cancel (f t^-1) (f t).
    rewrite /f => [[i j]]; by rewrite !permKV.
  rewrite -(card_imset _ (can_inj (fcan s))).
  congr (card (mem (pred_of_set _))).
  rewrite -setP => [[i j]]; rewrite !inE /=.
  apply/idP/idP.
  - move/imsetP => [[u v]]; rewrite inE /= => /andP [] Huv Hsuv.
    rewrite /f /= => [] [] -> ->.
    by rewrite Hsuv !permKV Huv.
  - move=> /andP [] Hij Hsij.
    apply/imsetP; exists (s j, s i); last by rewrite /f !permK.
    by rewrite inE Hsij !permK Hij.
Qed.

Lemma eltr_exchange i (a b : 'I_(n.+1)) :
  i < n -> a < b -> 's_i a < 's_i b = (i != a) || (i.+1 != b).
Proof.
  rewrite -ltnS => Hi1n Hab.
  have : (inord i) = Ordinal (ltnW Hi1n).
    apply val_inj => /=; rewrite inordK //; exact: ltnW.
  set io  := Ordinal (ltnW Hi1n) => Hi.
  have : (inord i.+1) = Ordinal Hi1n by apply val_inj => /=; rewrite inordK.
  set i1o := Ordinal Hi1n => Hi1.
  move: Hab; rewrite /eltr Hi Hi1.
  case: tpermP => [-> | -> | /eqP Ha1 /eqP Hai1];
    case: tpermP => [-> | -> | /eqP Hb1 /eqP Hbi1];
    rewrite /= ?ltnn ?trivSimpl //=.
  - by move=> /ltnW; rewrite leqNgt => /negbTE ->.
  - rewrite (ltn_neqAle i.+1 b) => ->; by rewrite andbT.
  - by rewrite ltnS leqnn.
  - by rewrite ltn_neqAle eq_sym Hbi1 /= => ->.
  - by rewrite ltnS (ltn_neqAle a i) eq_sym => /andP [] -> ->.
  - rewrite ltnS ltn_neqAle => -> /=; by rewrite eq_sym andbT orbF.
  - by rewrite eq_sym Ha1 eq_sym Hbi1 => ->.
Qed.

Lemma length_add1L s (i : 'I_(n.+1)) :
  i < n -> s i < s (inord (i.+1)) -> length ('s_i * s) = (length s).+1.
Proof.
  rewrite -ltnS => Hi1n.
  have Hi : (inord i) = i by apply val_inj => /=; rewrite inordK.
  have : (inord i.+1) = Ordinal Hi1n by apply val_inj => /=; rewrite inordK.
  set i1 := Ordinal Hi1n => Hi1.
  rewrite /length /invset Hi1 => Hfwd.
  pose f t := fun p : 'II_n.+1 => (t p.1, t p.2) : 'II_n.+1.
  have fcan t : cancel (f t) (f t^-1).
    rewrite /f => [[u v]]; by rewrite !permK.
  set invsi := [set _ | _ _]; set invs := [set _ | _ _].
  suff -> : invsi = (i, Ordinal Hi1n) |: ((f 's_i) @: invs).
    rewrite cardsU1 (card_imset _ (can_inj (fcan _))) -(add1n #|_|); congr (_ + _).
    rewrite (_ : (_, _) \in _ = false) //.
    apply (introF idP) => /imsetP [[u v]].
    rewrite {fcan} /f inE /= => /andP [] Huv Hsvu [].
    move/(congr1 's_i); rewrite /eltr Hi Hi1 tpermK tpermL => Hu; subst u.
    move/(congr1 's_i); rewrite /eltr Hi Hi1 tpermK tpermR => Hv; subst v.
    move: Huv => /ltnW /=; by rewrite ltnn.
  rewrite {}/invs {}/invsi -setP {fcan} => [[u v]] /=; rewrite !inE /= !permM.
  apply/idP/idP.
  - move=> /andP [] Huv.
    rewrite /eltr Hi Hi1 -/i1; case: tpermP => /= [Hv | Hv | /eqP Hvi /eqP Hvi1].
    + subst v.
      have Htu : tperm i i1 u = u.
        rewrite tpermD // eq_sym; move: Huv; apply contraL => /eqP ->; by rewrite /= -leqNgt.
      rewrite Htu => Hs; apply/orP; right; apply/imsetP; exists (u, i1); first last.
        by rewrite {}/f /= tpermR Htu.
      rewrite inE /= Hs andbT; by apply/(ltn_trans Huv).
    + subst v; case: tpermP.
      * move=> ->; by rewrite eq_refl.
      * move=> Hu; move: Huv; by rewrite Hu ltnn.
      move=> /eqP Hiu /eqP Hi1u.
      have Htu : tperm i i1 u = u by rewrite tpermD // eq_sym.
      move=> Hsiu; apply/orP; right; apply/imsetP; exists (u, i); first last.
        by rewrite {}/f /= tpermL Htu.
      by rewrite inE /= Hsiu andbT ltn_neqAle Hiu -ltnS /= Huv.
    case: tpermP => [Hu | Hu | /eqP Hui /eqP Hui1].
    + subst u => Hsvi1.
      have Htv : tperm i i1 v = v by rewrite tpermD // eq_sym.
      apply/orP; right; apply/imsetP; exists (i1, v); first last.
        by rewrite {}/f /= Htv tpermR.
      by rewrite inE /= Hsvi1 ltn_neqAle Huv !andbT eq_sym Hvi1.
    + subst u => Hsvi1.
      have Htv : tperm i i1 v = v by rewrite tpermD // eq_sym.
      apply/orP; right; apply/imsetP; exists (i, v); first last.
        by rewrite {}/f /= Htv tpermL.
      rewrite inE /= Hsvi1 ltn_neqAle eq_sym Hvi !andbT /=.
      by apply: ltnW; apply ltnW.
    + move=> Hsvu.
      apply/orP; right; apply/imsetP; exists (u, v); first last.
        by rewrite {}/f /= !tpermD // eq_sym.
      by rewrite inE /= Huv Hsvu.
  - move/orP => [].
      move=> /eqP [] -> ->.
      by rewrite /eltr Hi Hi1 tpermL tpermR /= ltnS leqnn Hfwd.
    move=> /imsetP [[a b]]; rewrite inE /= => /andP [] Hab Hsba.
    rewrite {}/f /= => [] [] -> -> {u v}.
    rewrite !tpermK Hsba andbT (eltr_exchange Hi1n Hab) -negb_and.
    move: Hsba; apply contraL; rewrite -leqNgt => /andP [] /eqP Hia /eqP Hib.
    have -> : a = i by apply val_inj.
    have -> : b = i1 by apply val_inj.
    exact: ltnW.
Qed.

Lemma length_sub1L s (i : 'I_(n.+1)) :
  i < n -> s i > s (inord (i.+1)) -> length s = (length ('s_i * s)).+1.
Proof.
  move=> Hi Hs.
  rewrite -{1}(mul1g s) -(mulVg 's_i) -mulgA tpermV -/(eltr i).
  apply (length_add1L Hi).
  rewrite !permM /eltr.
  have -> : inord i = i by apply val_inj; rewrite /= inordK.
  by rewrite tpermL tpermR.
Qed.

Lemma length_add1R s (i : 'I_(n.+1)) :
  i < n -> s^-1 i < s^-1 (inord (i.+1)) -> length (s * 's_i) = (length s).+1.
Proof.
  move=> Hi Hdesc.
  rewrite -length_permV -[length s]length_permV invMg tpermV -/(eltr i).
  exact: length_add1L.
Qed.

Lemma length_sub1R s (i : 'I_(n.+1)) :
  i < n -> s^-1 i > s^-1 (inord (i.+1)) -> length s = (length (s * 's_i)).+1.
Proof.
  move=> Hi Hdesc.
  rewrite -length_permV -[length (s * _)]length_permV invMg tpermV -/(eltr i).
  exact: length_sub1L.
Qed.

Lemma length_wordm (w : seq 'I_n) : length 's_[w] <= size w.
Proof.
  elim: w => [/=| w0 w]; first by rewrite big_nil length1.
  rewrite big_cons /=; move: ('s_[w]) => s Hlen.
  pose w0' := inord (n' := n) w0.
  have Hw0' : w0' < n by rewrite /= inordK //; apply: ltnW; rewrite ltnS.
  have -> : w0 = w0' :> nat by rewrite inordK //; apply ltnW; rewrite ltnS.
  case (ltngtP (s w0') (s (inord w0'.+1))) => H.
  - rewrite (length_add1L Hw0' H); by rewrite ltnS.
  - move: Hlen; rewrite (length_sub1L Hw0' H) => /ltnW.
    by rewrite -ltnS => /ltnW.
  - exfalso; move: H => /val_inj/perm_inj => H.
    have {H} /= /eqP := (congr1 (@nat_of_ord _) H).
    by rewrite inordK // ieqi1F.
Qed.


Definition is_code (c : seq nat) :=
  all (fun i => nth 0 c i <= i) (iota 0 (size c)).
Definition word_of_cocode (c : seq nat) : seq nat :=
  flatten [seq rev (iota (i - nth 0 c i) (nth 0 c i)) |
           i <- iota 0 (size c)].

Fixpoint cocode_rec m c (s : 'S_n.+1) : seq nat :=
  if m is m'.+1 then
    let mo := inord m' in
    cocode_rec m' (mo - s mo :: c) (s * 's_[iota (s mo) (mo - s mo)])
  else c.
Definition cocode s := cocode_rec n.+1 [::] s.

Definition Lehmer (s : 'S_n.+1) (i : 'I_n.+1) :=
  #|[set j : 'I_n.+1 | (i < j) && (s i > s j)]|.

Lemma cocode_rec_cat m c s : cocode_rec m c s = (cocode_rec m [::] s ++ c).
Proof.
  elim: m c s => [//= | m IHm] c s /=.
  by rewrite IHm [X in _ = X ++ _]IHm -cat1s catA.
Qed.

Lemma size_word_of_cocode c : size (word_of_cocode c) = sumn c.
Proof.
  rewrite /word_of_cocode size_flatten; congr sumn.
  rewrite /shape -map_comp; apply (eq_from_nth (x0 := 0)); rewrite size_map size_iota //.
  move=> i Hi; rewrite (nth_map 0); last by rewrite size_iota.
  by rewrite /= size_rev size_iota (nth_iota _ Hi) add0n.
Qed.

Lemma is_codeP c :
  reflect (forall i, i < size c -> nth 0 c i <= i) (is_code c).
Proof.
  rewrite /is_code; apply (iffP idP).
  - move=> /allP Hcode => // i Hi.
    apply Hcode; by rewrite mem_iota /= add0n.
  - move=> Hcode; apply/allP => i; rewrite mem_iota add0n /=; exact: Hcode.
Qed.

Lemma word_of_cocodeE c :
  's_[word_of_cocode c] =
  \prod_(i <- iota 0 (size c)) 's_[rev (iota (i - nth 0 c i) (nth 0 c i))].
Proof. by rewrite big_flatten /= big_map. Qed.

Lemma word_of_cocode_ltn c :
  is_code c -> all (gtn (size c).-1) (word_of_cocode c).
Proof.
  move=> /is_codeP Hcode.
  apply/allP => i /flatten_mapP [] j; rewrite mem_iota /= add0n => Hc.
  rewrite mem_rev mem_iota subnK; last exact: Hcode.
  move=> /andP [] _ /leq_trans; apply.
  by case: (size c) Hc.
Qed.

Lemma size_cocode_rec m s c : size (cocode_rec m c s) = m + size c.
Proof. by elim: m s c => [| m IHm] //= s c; rewrite IHm /= addSnnS. Qed.

Lemma size_cocode s : size (cocode s) = n.+1.
Proof. by rewrite size_cocode_rec addn0. Qed.

Let is_partcode m c :=
  forall i, i < size c -> nth 0 c i <= i + m.
Let word_of_partcocode m c : seq nat :=
  flatten [seq rev (iota (m + i - nth 0 c i) (nth 0 c i)) |
           i <- iota 0 (size c)].

Lemma perm_on_cocode_recP m c s0 s :
  m <= n.+1 ->
  is_partcode m c ->
  s0 = s * 's_[word_of_partcocode m c] ->
  perm_on [set k : 'I_n.+1 | k < m] s ->
  let cf := cocode_rec m c s in is_code cf /\ s0 = 's_[word_of_cocode cf].
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
  rewrite /word_of_partcocode /= addn0 (subKn Hsm) big_cat /=.
  rewrite mulgA prod_eltrK mul1g; apply congr_big => //; congr flatten.
  rewrite -(addn0 1%N) iota_addl -map_comp.
  apply eq_map => i /=.
  by rewrite addnA addn1.
Qed.

Lemma perm_on_prods c m :
  is_code c -> m <= size c -> m <= n.+1 ->
  perm_on [set k : 'I_n.+1 | k < m]
          (\prod_(i <- iota 0 m) 's_[(rev (iota (i - nth 0 c i) (nth 0 c i)))]).
Proof.
  move=> /is_codeP Hc Hmsz Hm.
  rewrite big_seq; apply big_rec => [| i s]; first exact: perm_on1.
  rewrite mem_iota /= add0n => Him /(perm_onM _); apply => {s}.
  rewrite big_seq; apply big_rec => [| j s]; first exact: perm_on1.
  rewrite mem_rev mem_iota /= => /andP [] _.
  move/(_ _ (leq_trans Him Hmsz)): Hc => /subnK -> Hji /(perm_onM _); apply => {s}.
  have Hj1m := leq_ltn_trans Hji Him.
  have Hjm := ltn_trans Hji Him.
  rewrite /perm_on; apply/subsetP => u; rewrite inE unfold_in.
  apply contraR; rewrite -leqNgt => Hu; apply/eqP/tpermD.
  - apply/(introN idP) => /eqP/(congr1 (@nat_of_ord _)).
    rewrite (inordK (leq_trans Hjm Hm)) => Hju.
    by have := leq_trans Hjm Hu; rewrite Hju ltnn.
  - apply/(introN idP) => /eqP/(congr1 (@nat_of_ord _)).
    rewrite (inordK (leq_trans Hj1m Hm)) => Hju.
    by have := leq_trans Hj1m Hu; rewrite Hju ltnn.
Qed.

Lemma perm_onV H s : perm_on H s -> perm_on H s^-1.
Proof.
  rewrite /perm_on => /subsetP Hsub; apply/subsetP => i.
  rewrite inE => Hi; apply Hsub; rewrite inE.
  move: Hi; apply contra => /eqP {1}<-.
  by rewrite permK.
Qed.

Lemma prods_mi (m : 'I_n.+1) i : i <= m -> 's_[(iota (m - i) i)] (inord (m - i)) = m.
Proof.
  elim: i => [| i IHi] /= Hm.
    by rewrite subn0 inord_val big_nil perm1.
  rewrite big_cons permM tpermL.
  rewrite subnS prednK; last by rewrite subn_gt0.
  apply: IHi; exact: ltnW.
Qed.

Lemma prods_ltmi i (m u : 'I_n.+1) :
  i <= m -> u < m - i -> 's_[(iota (m - i) i)] u = u.
Proof.
  elim: i => [| i IHi] /= Hm Hu.
    by rewrite big_nil perm1.
  rewrite big_cons permM tpermD; first last.
  - apply (introN idP) => /eqP Hu1 {IHi}; subst u.
    move: Hu; rewrite subnS prednK; last by rewrite subn_gt0.
    rewrite inordK; last by apply: (leq_trans (leq_subr _ _)); rewrite -ltnS.
    by rewrite ltnNge leq_pred.
  - apply (introN idP) => /eqP Hu1 {IHi}; subst u.
    move: Hu; rewrite subnS.
    rewrite inordK; first last.
      apply: (leq_trans (leq_pred _)).
      apply: (leq_trans (leq_subr _ _)); by rewrite -ltnS.
    by rewrite ltnn.
  rewrite subnS prednK; last by rewrite subn_gt0.
  apply: (IHi (ltnW Hm) (leq_trans Hu _)).
  rewrite subnS.
  move: Hm; rewrite -subn_gt0; by case: (m - i).
Qed.

Lemma perm_on_prods_length_ord s i (m : 'I_n.+1) :
  i <= m -> perm_on [set k : 'I_n.+1 | k < m] s ->
  length (s * 's_[(rev (iota (m - i) i))]) = length s + i.
Proof.
  elim: i s => [/= | i IHi] /= s Hm Hon; first by rewrite big_nil mulg1 addn0.
  rewrite rev_cons -cats1 big_cat /= {1}subnS prednK; last by rewrite subn_gt0.
  rewrite big_seq1 mulgA.
  have H : m - i.+1 < n.
    rewrite -ltnS subnSK //; apply: (leq_trans _ (ltn_ord _)); rewrite ltnS; exact: leq_subr.
  have := H; rewrite -ltnS => /ltnW Ho.
  have -> : (m - i.+1) = Ordinal Ho by [].
  rewrite length_add1R.
  - by rewrite (IHi _ (ltnW Hm) Hon) addnS.
  - by [].
  - have -> : Ordinal Ho = inord (m - i.+1) by apply val_inj => /=; rewrite inordK.
    rewrite invMg !permM inordK // {IHi}.
    rewrite !subnS prednK; last by rewrite subn_gt0.
    have -> w : 's_[rev w]^-1 = 's_[w].
      apply/eqP; by rewrite eq_invg_mul -{2}(revK w) prod_eltrK.
    rewrite {H Ho} (prods_mi (ltnW Hm)).
    have : m \notin [set k : 'I_n.+1 | k < m] by rewrite inE ltnn.
    move/(out_perm (perm_onV Hon)) ->.
    rewrite (prods_ltmi (ltnW Hm)); first last.
      rewrite inordK; first by move: Hm; rewrite -subn_gt0; case: (m - i).
      apply: (leq_trans (leq_pred _)).
      apply: (leq_trans (leq_subr _ _)); by rewrite -ltnS.
    have := perm_closed (inord (m - i).-1) (perm_onV Hon).
    rewrite !inE => -> /=; rewrite inordK.
    - rewrite prednK; last by rewrite subn_gt0.
      exact: leq_subr.
    - rewrite prednK; last by rewrite subn_gt0.
      apply: (leq_trans (leq_subr _ _)); exact: ltnW.
Qed.

Lemma perm_on_prods_length s i m :
  m < n.+1 -> i <= m -> perm_on [set k : 'I_n.+1 | k < m] s ->
  length (s * 's_[(rev (iota (m - i) i))]) = length s + i.
Proof.
  move=> Hm; have -> : m = Ordinal Hm by [].
  exact: perm_on_prods_length_ord.
Qed.

Lemma lenght_perm_of_cocode c :
  is_code c -> size c = n.+1 -> length 's_[word_of_cocode c] = size (word_of_cocode c).
Proof.
  rewrite size_word_of_cocode word_of_cocodeE => Hcode.
  have:= Hcode => /is_codeP Hcd Hsz.
  rewrite -(sum_iota_sumnE (n := size c)) // /index_iota subn0.
  elim: {1 3 4}(size c) (leqnn (size c)) => [/= | m IHm] Hm.
    by rewrite !big_nil length1.
  rewrite -(addn1 m) iota_add !big_cat /= add0n !big_seq1.
  rewrite perm_on_prods_length /=; first by rewrite (IHm (ltnW Hm)).
  - by rewrite -Hsz.
  - by apply Hcd.
  - apply: (perm_on_prods Hcode (ltnW Hm)).
    rewrite -Hsz; exact: ltnW.
Qed.

Lemma cocode2P s :
  let c := cocode s in is_code c /\ s = 's_[word_of_cocode c].
Proof.
  rewrite /cocode; apply perm_on_cocode_recP => //.
  - by rewrite /word_of_partcocode /= big_nil mulg1.
  - rewrite /perm_on; apply/subsetP => k _; rewrite !inE; exact: ltn_ord.
Qed.

Lemma cocodeP s : is_code (cocode s).
Proof. by have:= cocode2P s => /= [] []. Qed.

Lemma cocodeE s : s = 's_[word_of_cocode (cocode s)].
Proof. by have:= cocode2P s => /= [] []. Qed.

Definition canword s : seq 'I_n := pmap insub (word_of_cocode (cocode s)).

Lemma canwordE s : [seq nat_of_ord i | i <- canword s] = word_of_cocode (cocode s).
Proof.
  rewrite pmap_filter; last by move=> j /=; rewrite insubK.
  rewrite (eq_in_filter (a2 := xpredT)); first last.
    move=> j /= /(allP (word_of_cocode_ltn (cocodeP s))) /=.
    rewrite size_cocode => Hj; by rewrite insubT.
  by rewrite filter_predT.
Qed.

Theorem canwordP s : s = 's_[canword s].
Proof.
  rewrite /= {1}(cocodeE s).
  rewrite -(big_map (@nat_of_ord _) xpredT) /=; apply congr_big => //.
  by rewrite canwordE.
Qed.

Definition is_reduced (w : seq 'I_n) := length 's_[w] = size w.

Theorem can_word_reduced s : is_reduced (canword s).
Proof.
  rewrite /is_reduced -(big_map (@nat_of_ord _) xpredT) /= canwordE.
  rewrite (lenght_perm_of_cocode (cocodeP _) (size_cocode _)).
  by rewrite -canwordE size_map.
Qed.

Lemma eltr_ind (P : 'S_n.+1 -> Type) :
  P 1 -> (forall s i, i < n -> P s -> P ('s_i * s)) ->
  forall s, P s.
Proof.
  move=> H1 IH s.
  have /= -> := canwordP s.
  elim: (canword s)  => [| t0 t IHt] /=; first by rewrite big_nil.
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
  all (gtn n) ts -> odd (size ts) = odd_perm 's_[ts].
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
    have /= -> := canwordP s.
    elim: (canword s) => [| t0 t IHt] /=.
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
    have /= -> := canwordP s.
    elim: (canword s) => [| t0 t IHt] /=.
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
