(** * Combi.SymGroup.symgroup : The symmetric group *)
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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import tuple finfun bigop finset binomial fingroup perm.
Require Import morphism presentation.

Require Import tools permuted combclass congr.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma ieqi1F i : (i == i.+1) = false. Proof. apply: negbTE; by elim i. Qed.
Lemma ieqi2F i : (i == i.+2) = false. Proof. apply: negbTE; by elim i. Qed.
Lemma i1eqiF i : (i.+1 == i) = false. Proof. apply: negbTE; by elim i. Qed.
Lemma i2eqiF i : (i.+2 == i) = false. Proof. apply: negbTE; by elim i. Qed.

Definition trivSimpl := (eq_refl, eqSS, ieqi1F, ieqi2F, i1eqiF, i2eqiF).

Lemma inordi1 n i : i < n -> (@inord n i != @inord n i.+1).
Proof.
  move=> Hi.
  rewrite /eq_op /= inordK; last by apply (leq_trans Hi).
  rewrite inordK; last exact: Hi.
  by rewrite ieqi1F.
Qed.

Section Codes.

Definition code := [qualify a c : seq nat |
  all (fun i => nth 0 c i <= i) (iota 0 (size c)) ].

Definition wordcd (c : seq nat) : seq nat :=
  flatten [seq rev (iota (i - nth 0 c i) (nth 0 c i)) |
           i <- iota 0 (size c)].

Lemma size_wordcd c : size (wordcd c) = sumn c.
Proof.
  rewrite /wordcd size_flatten; congr sumn.
  rewrite /shape -map_comp; apply (eq_from_nth (x0 := 0)); rewrite size_map size_iota //.
  move=> i Hi; rewrite (nth_map 0); last by rewrite size_iota.
  by rewrite /= size_rev size_iota (nth_iota _ Hi) add0n.
Qed.

Lemma is_codeP c :
  reflect (forall i, i < size c -> nth 0 c i <= i) (c \is a code).
Proof.
  rewrite /unfold_in; apply (iffP idP).
  - move=> /allP Hcode => // i Hi.
    apply Hcode; by rewrite mem_iota /= add0n.
  - move=> Hcode; apply/allP => i; rewrite mem_iota add0n /=; exact: Hcode.
Qed.

Lemma is_code_rcons c i : i <= size c -> c \is a code -> rcons c i \is a code.
Proof.
  move=> Hi /is_codeP Hcode; apply/is_codeP => j.
  rewrite size_rcons ltnS leq_eqVlt => /orP [/eqP ->| Hj]; rewrite nth_rcons.
  - by rewrite ltnn eq_refl.
  - by rewrite Hj; apply Hcode.
Qed.

Lemma is_code_rconsK c i : rcons c i \is a code -> c \is a code.
Proof.
  move/is_codeP; rewrite size_rcons => Hcode.
  apply/is_codeP => j Hj; have:= Hj; rewrite -ltnS => /ltnW/Hcode.
  by rewrite nth_rcons Hj.
Qed.

Lemma code_ltn_size c : c \is a code -> all (gtn (size c)) c.
Proof.
  move=> /is_codeP Hcode.
  apply/allP => v Hv; rewrite -(nth_index 0 Hv).
  move: Hv; rewrite -index_mem => Hv.
  have:= Hv => /Hcode/leq_ltn_trans; by apply.
Qed.

Lemma wordcd_ltn c :
  c \is a code -> all (gtn (size c).-1) (wordcd c).
Proof.
  move=> /is_codeP Hcode.
  apply/allP => i /flatten_mapP [] j; rewrite mem_iota /= add0n => Hc.
  rewrite mem_rev mem_iota subnK; last exact: Hcode.
  move=> /andP [] _ /leq_trans; apply.
  by case: (size c) Hc.
Qed.

Lemma insub_wordcdK n c :
  c \is a code -> size c <= n.+1 ->
  [seq @nat_of_ord n i | i <- pmap insub (wordcd c)] = wordcd c.
Proof.
  move=> /wordcd_ltn/allP Hall Hsz.
  rewrite pmap_filter; last by move=> j /=; rewrite insubK.
  rewrite (eq_in_filter (a2 := xpredT)); first by rewrite filter_predT.
  move=> j /= /Hall /= Hj.
  have {Hj} Hj : j < n by case: (size c) Hj Hsz => [//= | sz] /=; exact: leq_trans.
  by rewrite insubT.
Qed.


Definition is_code_of_size n c := (c \is a code) && (size c == n).

Fixpoint enum_codesz n :=
  if n is n'.+1 then
    flatten [seq [seq rcons c i | c <- enum_codesz n'] | i <- iota 0 n]
  else [:: [::]].

Lemma enum_codeszP n : all (is_code_of_size n) (enum_codesz n).
Proof.
  rewrite /is_code_of_size; elim: n => [| n IHn] //.
  apply/allP => cn /flatten_mapP [] i.
  rewrite -/enum_codesz mem_iota /= add0n ltnS => Hi.
  move=> /mapP [] c /(allP IHn) {IHn} /andP [] Hcode /eqP Hsz -> {cn}.
  rewrite size_rcons Hsz eq_refl andbT.
  by apply is_code_rcons; first by rewrite Hsz.
Qed.

Lemma enum_codesz_countE n c :
  is_code_of_size n c -> count_mem c (enum_codesz n) = 1.
Proof.
  elim: n c => [//= | n IHn] c /andP [].
    move=> _ /nilP ->; by rewrite eq_refl addn0.
  case/lastP: c => [// | c cn] Hcode.
  rewrite size_rcons eqSS => /eqP Hsz.
  have /IHn{IHn} Hcount : is_code_of_size n c.
    rewrite /is_code_of_size Hsz eq_refl andbT.
    exact: (is_code_rconsK Hcode).
  rewrite count_flatten -map_comp -/enum_codesz.
  rewrite (eq_map (f2 := fun i => i == cn : nat)); first last.
    move=> i /=; rewrite count_map /=.
    case (altP (i =P cn)) => [Heq | /negbTE Hneq].
    + subst i; rewrite (eq_count (a2 := xpred1 c)); first exact: Hcount.
      move=> s /=; by apply/idP/idP => [/eqP/rconsK ->| /eqP ->].
    + rewrite (eq_count (a2 := pred0)); first by rewrite count_pred0.
      move=> s /=; apply (introF idP) => /eqP/(congr1 rev).
      rewrite !rev_rcons => [] [] /eqP; by rewrite Hneq.
  rewrite sumn_iota //= add0n.
  move/is_codeP: Hcode; rewrite size_rcons ltnS => /(_ _ (ltnSn _)).
  by rewrite nth_rcons ltnn eq_refl Hsz.
Qed.

Section FinType.

Variable n : nat.

Structure codesz : predArgType :=
  CodeSZ {cdval :> seq nat; _ : (cdval \is a code) && (size cdval == n)}.
Canonical codesz_subType := Eval hnf in [subType for cdval].
Definition codesz_eqMixin := Eval hnf in [eqMixin of codesz by <:].
Canonical codesz_eqType := Eval hnf in EqType codesz codesz_eqMixin.
Definition codesz_choiceMixin := Eval hnf in [choiceMixin of codesz by <:].
Canonical codesz_choiceType := Eval hnf in ChoiceType codesz codesz_choiceMixin.
Definition codesz_countMixin := Eval hnf in [countMixin of codesz by <:].
Canonical codesz_countType := Eval hnf in CountType codesz codesz_countMixin.
Canonical codesz_subCountType := Eval hnf in [subCountType of codesz].
Let type := sub_finType codesz_subCountType
                        (enum_codeszP n) (@enum_codesz_countE n).
Canonical codesz_finType := Eval hnf in [finType of codesz for type].
Canonical codesz_subFinType := Eval hnf in [subFinType of codesz].

Implicit Type (c : codesz).

Lemma codeszP c : val c \is a code.
Proof. by case: c => c /= /andP []. Qed.

Lemma size_codesz c : size c = n.
Proof. by case: c => c /= /andP [] _ /eqP. Qed.

Lemma enum_codeszE : map val (enum codesz) = enum_codesz n.
Proof. rewrite /=; exact: enum_subE. Qed.

End FinType.

Lemma card_codesz n : #|codesz n| = n`!.
Proof.
  rewrite factE /= cardE -(size_map val) enum_codeszE.
  elim: n => [//=| n IHn].
  rewrite size_flatten -/enum_codesz /shape -map_comp.
  rewrite (eq_map (f2 := fun _ => fact_rec n)); first last.
    by move=> i /=; rewrite size_map.
  by rewrite -sumnE big_map big_const_seq count_predT size_iota iter_addn_0 mulnC /=.
Qed.

End Codes.

Hint Resolve codeszP.


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


Section ElemTransp.

Variable n : nat.

Definition eltr i : 'S_n.+1 := tperm (inord i) (inord i.+1).

Local Notation "''s_' i" := (eltr i) (at level 8, i at level 2).
Local Notation "''s_[' w ']'" := (\prod_(i <- w) 's_i) (at level 8, w at level 2).

Implicit Type s t : 'S_n.+1.

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

Lemma prodsK w :
  's_[w] * 's_[rev w] = 1.
Proof.
  elim/last_ind: w => [| w wn IHw] /=.
    by rewrite /rev /= !big_nil mulg1.
  rewrite rev_rcons -cat1s -cats1 -big_cat /=.
  rewrite -catA -[wn :: rev w]cat1s [X in w ++ X]catA cat1s !big_cat /=.
  suff -> : 's_[[:: wn; wn]] = 1 by rewrite mul1g.
  by rewrite big_cons big_seq1 tperm2.
Qed.

Lemma prodsV w : 's_[rev w] = 's_[w]^-1.
Proof. apply/eqP; by rewrite eq_sym eq_invg_mul prodsK. Qed.

End ElemTransp.


Section Length.

Variable n : nat.

Implicit Type s t : 'S_n.+1.

Local Notation "''s_' i" := (eltr n i) (at level 8, i at level 2).
Local Notation "''s_[' w ']'" := (\prod_(i <- w) 's_i) (at level 8, w at level 2).
Local Notation "''II_' n" := ('I_n * 'I_n)%type (at level 8, n at level 2).

(** * Length of a permutation *)
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
  rewrite /length Hi1 => Hfwd.
  suff -> : invset ('s_i * s) =
            (i, Ordinal Hi1n) |: [set ('s_i p.1, 's_i p.2) | p in invset s].
    rewrite cardsU1 (card_imset _ (@inv_inj _ _ _)); first last.
      move=> [u v] /=; by rewrite !tpermK.
    rewrite (_ : (_, _) \in _ = false) //.
    apply (introF idP) => /imsetP [[u v]].
    rewrite inE /= => /andP [] Huv Hsvu [].
    move/(congr1 's_i); rewrite /eltr Hi Hi1 tpermK tpermL => Hu; subst u.
    move/(congr1 's_i); rewrite /eltr Hi Hi1 tpermK tpermR => Hv; subst v.
    move: Huv => /ltnW /=; by rewrite ltnn.
  rewrite -setP => [[u v]] /=; rewrite !inE /= !permM.
  apply/idP/idP.
  - move=> /andP [] Huv.
    rewrite /eltr Hi Hi1 -/i1; case: tpermP => /= [Hv | Hv | /eqP Hvi /eqP Hvi1].
    + subst v.
      have Htu : tperm i i1 u = u.
        rewrite tpermD // eq_sym; move: Huv; apply contraL => /eqP ->; by rewrite /= -leqNgt.
      rewrite Htu => Hs; apply/orP; right; apply/imsetP; exists (u, i1); first last.
        by rewrite /= tpermR Htu.
      rewrite inE /= Hs andbT; by apply/(ltn_trans Huv).
    + subst v; case: tpermP.
      * move=> ->; by rewrite eq_refl.
      * move=> Hu; move: Huv; by rewrite Hu ltnn.
      move=> /eqP Hiu /eqP Hi1u.
      have Htu : tperm i i1 u = u by rewrite tpermD // eq_sym.
      move=> Hsiu; apply/orP; right; apply/imsetP; exists (u, i); first last.
        by rewrite tpermL Htu.
      by rewrite inE /= Hsiu andbT ltn_neqAle Hiu -ltnS /= Huv.
    case: tpermP => [Hu | Hu | /eqP Hui /eqP Hui1].
    + subst u => Hsvi1.
      have Htv : tperm i i1 v = v by rewrite tpermD // eq_sym.
      apply/orP; right; apply/imsetP; exists (i1, v); first last.
        by rewrite Htv tpermR.
      by rewrite inE /= Hsvi1 ltn_neqAle Huv !andbT eq_sym Hvi1.
    + subst u => Hsvi1.
      have Htv : tperm i i1 v = v by rewrite tpermD // eq_sym.
      apply/orP; right; apply/imsetP; exists (i, v); first last.
        by rewrite Htv tpermL.
      rewrite inE /= Hsvi1 ltn_neqAle eq_sym Hvi !andbT /=.
      by apply: ltnW; apply ltnW.
    + move=> Hsvu.
      apply/orP; right; apply/imsetP; exists (u, v); first last.
        by rewrite !tpermD // eq_sym.
      by rewrite inE /= Huv Hsvu.
  - move/orP => [].
      move=> /eqP [] -> ->.
      by rewrite /eltr Hi Hi1 tpermL tpermR /= ltnS leqnn Hfwd.
    move=> /imsetP [[a b]]; rewrite inE /= => /andP [] Hab Hsba [] -> -> {u v}.
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

Lemma length_prods (w : seq 'I_n) : length 's_[w] <= size w.
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


(** * Dual code of a permutation *)
Fixpoint cocode_rec m c (s : 'S_n.+1) : seq nat :=
  if m is m'.+1 then
    let mo := inord m' in
    cocode_rec m' (mo - s mo :: c) (s * 's_[iota (s mo) (mo - s mo)])
  else c.
Definition cocode s := cocode_rec n.+1 [::] s.

(*
Definition Lehmer (s : 'S_n.+1) (i : 'I_n.+1) :=
  #|[set j : 'I_n.+1 | (i < j) && (s i > s j)]|.
*)

Lemma cocode_rec_cat m c s : cocode_rec m c s = (cocode_rec m [::] s ++ c).
Proof.
  elim: m c s => [//= | m IHm] c s /=.
  by rewrite IHm [X in _ = X ++ _]IHm -cat1s catA.
Qed.

Lemma wordcdE c :
  's_[wordcd c] =
  \prod_(i <- iota 0 (size c)) 's_[rev (iota (i - nth 0 c i) (nth 0 c i))].
Proof. by rewrite big_flatten /= big_map. Qed.

Lemma size_cocode_rec m s c : size (cocode_rec m c s) = m + size c.
Proof. by elim: m s c => [| m IHm] //= s c; rewrite IHm /= addSnnS. Qed.

Lemma size_cocode s : size (cocode s) = n.+1.
Proof. by rewrite size_cocode_rec addn0. Qed.


(** ** Partial codes *)
Section PartCode.

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
  let cf := cocode_rec m c s in cf \is a code /\ s0 = 's_[wordcd cf].
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
  rewrite mulgA prodsK mul1g; apply congr_big => //; congr flatten.
  rewrite -(addn0 1%N) iota_addl -map_comp.
  apply eq_map => i /=.
  by rewrite addnA addn1.
Qed.

End PartCode.

Lemma perm_on_prods c m :
  c \is a code -> m <= size c -> m <= n.+1 ->
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
    by have:= leq_trans Hjm Hu; rewrite Hju ltnn.
  - apply/(introN idP) => /eqP/(congr1 (@nat_of_ord _)).
    rewrite (inordK (leq_trans Hj1m Hm)) => Hju.
    by have:= leq_trans Hj1m Hu; rewrite Hju ltnn.
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
  have:= H; rewrite -ltnS => /ltnW Ho.
  have -> : (m - i.+1) = Ordinal Ho by [].
  rewrite length_add1R.
  - by rewrite (IHi _ (ltnW Hm) Hon) addnS.
  - by [].
  - have -> : Ordinal Ho = inord (m - i.+1) by apply val_inj => /=; rewrite inordK.
    rewrite invMg !permM inordK // {IHi}.
    rewrite !subnS prednK; last by rewrite subn_gt0.
    rewrite {H Ho} prodsV invgK (prods_mi (ltnW Hm)).
    have : m \notin [set k : 'I_n.+1 | k < m] by rewrite inE ltnn.
    move/(out_perm (perm_onV Hon)) ->.
    rewrite (prods_ltmi (ltnW Hm)); first last.
      rewrite inordK; first by move: Hm; rewrite -subn_gt0; case: (m - i).
      apply: (leq_trans (leq_pred _)).
      apply: (leq_trans (leq_subr _ _)); by rewrite -ltnS.
    have:= perm_closed (inord (m - i).-1) (perm_onV Hon).
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

Lemma length_permcd c :
  c \is a code -> size c <= n.+1 -> length 's_[wordcd c] = sumn c.
Proof.
  rewrite wordcdE => Hcode.
  have:= Hcode => /is_codeP Hcd Hsz.
  rewrite -(sum_iota_sumnE (n := size c)) // /index_iota subn0.
  elim: {1 3 4}(size c) (leqnn (size c)) => [/= | m IHm] Hm.
    by rewrite !big_nil length1.
  rewrite -(addn1 m) iota_add !big_cat /= add0n !big_seq1.
  rewrite perm_on_prods_length /=; first by rewrite (IHm (ltnW Hm)).
  - exact: leq_trans Hm Hsz.
  - by apply Hcd.
  - apply: (perm_on_prods Hcode (ltnW Hm)).
    apply ltnW; exact: leq_trans Hm Hsz.
Qed.

Lemma cocode2P s :
  let c := cocode s in c \is a code /\ s = 's_[wordcd c].
Proof.
  rewrite /cocode; apply perm_on_cocode_recP => //.
  - by rewrite /= big_nil mulg1.
  - rewrite /perm_on; apply/subsetP => k _; rewrite !inE; exact: ltn_ord.
Qed.

Lemma cocodeP s : cocode s \is a code.
Proof. by have:= cocode2P s => /= [] []. Qed.

Lemma cocodeE s : s = 's_[wordcd (cocode s)].
Proof. by have:= cocode2P s => /= [] []. Qed.

Definition canword s : seq 'I_n := pmap insub (wordcd (cocode s)).

Lemma canwordE s : [seq nat_of_ord i | i <- canword s] = wordcd (cocode s).
Proof. apply (insub_wordcdK (cocodeP _)); by rewrite size_cocode. Qed.

Theorem canwordP s : s = 's_[canword s].
Proof.
  rewrite /= {1}(cocodeE s).
  rewrite -(big_map (@nat_of_ord _) xpredT) /=; apply congr_big => //.
  by rewrite canwordE.
Qed.

Theorem size_canword s : length s = size (canword s).
Proof.
  rewrite -(size_map val) canwordE size_wordcd.
  have /= := cocode2P s => [] [] Hcode {1}->.
  by rewrite -length_permcd // size_cocode.
Qed.

Definition prods_codesz (c : codesz n.+1) : 'S_n.+1 := 's_[wordcd c].

Lemma prods_codesz_bij : bijective prods_codesz.
Proof.
  apply inj_card_bij; last by rewrite card_codesz card_Sn.
  move=> c1 c2 Heq.
  suff /image_injP Hinj :
    (#|image prods_codesz (codesz n.+1)| == #|(codesz n.+1)|) by exact: (Hinj c1 c2).
  rewrite {c1 c2 Heq} card_codesz (eq_card (B := 'S_n.+1)) ?card_Sn //.
  move=> s; rewrite !inE; apply/mapP.
  have Hcode : is_code_of_size n.+1 (cocode s).
    by rewrite /is_code_of_size cocodeP size_cocode /=.
  exists (CodeSZ Hcode); first by rewrite enumT.
  by rewrite /prods_codesz /= -cocodeE.
Qed.

Lemma prods_wordcd_inj c1 c2 :
  c1 \is a code -> c2 \is a code -> size c1 = n.+1 -> size c2 = n.+1 ->
  's_[wordcd c1] = 's_[wordcd c2] -> c1 = c2.
Proof.
  move=> Hc1 Hc2 Hsz1 Hsz2.
  have HC1 : is_code_of_size n.+1 c1 by rewrite /is_code_of_size Hc1 Hsz1 /=.
  have HC2 : is_code_of_size n.+1 c2 by rewrite /is_code_of_size Hc2 Hsz2 /=.
  by move/((bij_inj prods_codesz_bij) (CodeSZ HC1) (CodeSZ HC2))/(congr1 val).
Qed.

End Length.

Hint Resolve cocodeP.


(** * Reduced words *)
Section Reduced.

Variable n : nat.

Local Notation "''s_' i" := (eltr n i) (at level 8, i at level 2).
Local Notation "''s_[' w ']'" := (\prod_(i <- w) 's_i) (at level 8, w at level 2).
Local Notation length := (length (n := n)).

Definition reduced_word := [qualify w : seq 'I_n | length 's_[w] == size w ].
Notation reduced := reduced_word.

Lemma reduced_nil : [::] \is reduced.
Proof. by rewrite unfold_in big_nil length1. Qed.

Hint Resolve reduced_nil.

Lemma reduced_iiF i : [:: i; i] \is reduced = false.
Proof. by rewrite unfold_in /= big_cons big_seq1 tperm2 length1. Qed.

Lemma reduced_rev w : w \is reduced -> rev w \is reduced.
Proof.
  rewrite !unfold_in size_rev => /eqP <-.
  rewrite -length_permV.
  by rewrite -!(big_map (@nat_of_ord _) xpredT) -prodsV map_rev revK.
Qed.

Lemma reduced_revE w : w \is reduced = (rev w \is reduced).
Proof.
  apply/idP/idP; first exact: reduced_rev.
  move/reduced_rev; by rewrite revK.
Qed.

Lemma reduced_sprod_code c :
  c \is a code -> size c <= n.+1 -> pmap insub (wordcd c) \is reduced.
Proof.
  move=> Hcode Hsz.
  have:= Hsz => /(length_permcd Hcode) Hlength.
  rewrite unfold_in -(big_map (@nat_of_ord _) xpredT) /=.
  by rewrite -(size_map val) /= insub_wordcdK // Hlength size_wordcd.
Qed.

Theorem canword_reduced s : canword s \is reduced.
Proof. apply: (reduced_sprod_code (cocodeP _)); by rewrite size_cocode. Qed.

Corollary lengthM u v : length (u * v) <= length u + length v.
Proof.
  have:= canword_reduced u; have:= canword_reduced v.
  rewrite !unfold_in -!canwordP => /eqP -> /eqP ->.
  rewrite {1}(canwordP u) {1}(canwordP v) -big_cat /=.
  apply: (leq_trans (length_prods _)); by rewrite size_cat.
Qed.

Lemma reduced_catr u v : u ++ v \is reduced -> v \is reduced.
Proof.
  rewrite !unfold_in size_cat => /eqP H.
  have {H} Huv : length 's_[u] + length 's_[v] =size u + size v.
    apply/eqP; rewrite eqn_leq (leq_add (length_prods u) (length_prods v)).
    have:= lengthM 's_[u] 's_[v]; by rewrite -big_cat /= H => ->.
  by have:= leq_addE (length_prods u) (length_prods v) Huv => [] [] _ ->.
Qed.

Lemma reduced_catl u v : u ++ v \is reduced -> u \is reduced.
Proof.
  move/reduced_rev; rewrite rev_cat => /reduced_catr.
  by rewrite -reduced_revE.
Qed.

Lemma reduced_consK i u : i :: u \is reduced -> u \is reduced.
Proof. rewrite -cat1s; exact: reduced_catr. Qed.

Lemma reduced_rconsK u i : rcons u i \is reduced -> u \is reduced.
Proof. rewrite -cats1; exact: reduced_catl. Qed.

Lemma canword1 : canword (1 : 'S_n.+1) = [::].
Proof.
  have:= canword_reduced 1; by rewrite unfold_in -canwordP length1 eq_sym => /nilP.
Qed.

Theorem eltr_ind (P : 'S_n.+1 -> Type) :
  P 1 -> (forall s i, i < n -> P s -> P ('s_i * s)) ->
  forall s, P s.
Proof.
  move=> H1 IH s; rewrite (canwordP s).
  elim: (canword s)  => [| t0 t IHt] /=; first by rewrite big_nil.
  rewrite big_cons; by apply IH; first exact: ltn_ord.
Qed.

Lemma odd_size_permE ts :
  all (gtn n) ts -> odd (size ts) = odd_perm 's_[ts].
Proof.
  elim: ts => [_ | t0 t IHt] /=; first by rewrite big_nil odd_perm1.
  move=> /andP [] Ht0 /IHt{IHt} ->.
  by rewrite big_cons odd_mul_tperm (inordi1 Ht0) addTb.
Qed.


(** * Braid monoid relations *)
Definition braid_aba :=
  fun s : seq 'I_n => match s with
             | [:: a; b; c] => if (a == c) && ((a.+1 == b) || (b.+1 == a))
                               then [:: [:: b; a; b]] else [::]
             | _ => [::]
           end.

Definition braidC :=
  fun s : seq 'I_n => match s with
             | [:: a; b] => if (a.+1 < b) || (b.+1 < a) then [:: [:: b; a]] else [::]
             | _ => [::]
           end.

Definition braidrule := [fun s => braid_aba s ++ braidC s].

Lemma braid_abaP (u v : seq 'I_n) :
  reflect (exists a b : 'I_n,
             [/\ ((a.+1 == b) || (b.+1 == a)), u = [:: a; b; a] & v = [:: b; a; b] ] )
          (v \in braid_aba u).
Proof.
  rewrite /braid_aba /=; apply: (iffP idP).
  + case: u => [//=|u0[//=|u1[//=|u2[]//=]]].
    case H : ((u0 == u2) && ((u0.+1 == u1) || (u1.+1 == u0))).
    - move: H => /andP [] /eqP <- Heq.
      rewrite mem_seq1 => /eqP ->.
      by exists u0; exists u1.
    - by rewrite in_nil.
  + move=> [] a [] b [] H -> ->.
    by rewrite unfold_in H eq_refl /= eq_refl.
Qed.

Lemma braidCP (u v : seq 'I_n) :
  reflect (exists a b : 'I_n,
             [/\ ((a.+1 < b) || (b.+1 < a)), u = [:: a; b] & v = [:: b; a] ] )
          (v \in braidC u).
Proof.
  rewrite /braidC /=; apply: (iffP idP).
  + case: u => [//=|u0[//=|u1[]//=]].
    case H : ((u0.+1 < u1) || (u1.+1 < u0)).
    - rewrite mem_seq1 => /eqP ->.
      by exists u0; exists u1.
    - by rewrite in_nil.
  + move=> [] a [] b [] H -> ->.
    by rewrite H mem_seq1 eq_refl.
Qed.

Lemma braidrule_sym (u v : seq 'I_n) : v \in (braidrule u) -> u \in (braidrule v).
Proof.
  rewrite !mem_cat => /orP [] /= Hbr; apply/orP.
  - left; move: Hbr => /braid_abaP [] a [] b [] Hab -> -> .
    by rewrite /braid_aba /= eq_refl orbC Hab /= mem_seq1 eq_refl.
  - right; move: Hbr => /braidCP [] a [] b [] Hab -> -> .
    by rewrite /braidC /= orbC Hab /= mem_seq1 eq_refl.
Qed.

Lemma braidrule_homog (u : seq 'I_n) :
  all [pred v | size v == size u] (braidrule u).
Proof.
  apply/allP => /= v.
  by rewrite mem_cat => /orP [/braid_abaP | /braidCP] [] a [] b [] _ -> ->.
Qed.

Definition braidcongr := gencongr_hom braidrule_homog.
Definition braidclass := genclass_hom braidrule_homog.

Local Notation "a =Br b" := (braidcongr a b) (at level 70).

Lemma braid_equiv : equivalence_rel braidcongr.
Proof. apply: gencongr_equiv; exact: braidrule_sym. Qed.

Lemma braid_refl : reflexive braidcongr.
Proof. have:= braid_equiv; by rewrite equivalence_relP => [] [] Hrefl Hltr. Qed.

Lemma braidww w : braidcongr w w.
Proof. exact: braid_refl. Qed.

Lemma braid_sym : symmetric braidcongr.
Proof.
  have:= braid_equiv; rewrite equivalence_relP => [] [] Hrefl Hltr.
  by move=> i j; apply/idP/idP => /Hltr <-.
Qed.

Lemma braid_ltrans : left_transitive braidcongr.
Proof. have:= braid_equiv; by rewrite equivalence_relP => [] [] Hrefl Hltr. Qed.

Lemma braid_trans : transitive braidcongr.
Proof.
  have:= braid_equiv; rewrite equivalence_relP => [] [] Hrefl Hltr.
  by move=> i j k => /Hltr <-.
Qed.

Lemma braid_is_congr : congruence_rel braidcongr.
Proof. apply: gencongr_is_congr; exact: braidrule_sym. Qed.

Definition braid_cons := congr_cons braid_is_congr.
Definition braid_rcons := congr_rcons braid_is_congr.
Definition braid_catl := congr_catl braid_is_congr.
Definition braid_catr := congr_catr braid_is_congr.
Definition braid_cat := congr_cat braid_is_congr braid_equiv.

Lemma size_braid u v : u =Br v -> size u = size v.
Proof. by move=> /gencongr_invar /= /eqP ->. Qed.

Lemma braid_rev u v : u =Br v -> rev u =Br rev v.
Proof.
  move: v; apply gencongr_ind; first exact: braid_refl.
  move=> a b1 c b2 /braid_ltrans -> {u} Hrule.
  rewrite !rev_cat -!catA; apply braid_is_congr; apply rule_gencongr.
  move: Hrule; rewrite /braidrule /= !mem_cat => /orP [].
  - move/braid_abaP => [] x [] y [] Hxy -> ->.
    by rewrite /rev /= eq_refl Hxy /= inE eq_refl.
  - move/braidCP => [] x [] y [] Hxy -> ->.
    by rewrite /rev /= orbC Hxy mem_seq1 eq_refl.
Qed.

Theorem braid_prods (v w : seq 'I_n) : v =Br w -> 's_[v] = 's_[w].
Proof.
  move=> H; apply/esym; move: w H; apply gencongr_ind => // a b1 c b2 <- Hrule.
  rewrite !big_cat /=; congr (_ * (_ * _)).
  move: Hrule; rewrite {a c} /braidrule /= mem_cat => /orP [].
  - move/braid_abaP => [] x [] y [] Hxy -> ->.
    do 2 (rewrite 2!big_cons big_seq1 mulgA).
    by move: Hxy => /orP [] /eqP Hxy; rewrite -Hxy eltr_braid // Hxy.
  - move/braidCP => [] x [] y [] Hxy -> ->.
    do 2 (rewrite big_cons big_seq1).
    move: Hxy => /orP [] Hxy.
    + by rewrite [RHS]eltr_comm // Hxy /=.
    + by rewrite [LHS]eltr_comm // Hxy /=.
Qed.

Corollary braid_reduced (v w : seq 'I_n) :
  v =Br w -> v \is reduced -> w \is reduced.
Proof.
  rewrite unfold_in => Hbr.
  by rewrite (braid_prods Hbr) (size_braid Hbr).
Qed.

Fixpoint reduces (u v : seq 'I_n) :=
  match u with
    | [::] | [:: _] => false
    | [:: a, b & l] =>
      ((a == b) && (l == v))
        || if v is v0 :: v' then (a == v0) && reduces (b :: l) v'
           else false
  end.

Lemma reducesP (u v : seq 'I_n) :
  reflect
    (exists x i y, u = x ++ [:: i; i] ++ y /\ v = x ++ y)
    (reduces u v).
Proof.
  elim: u v => [| a u IHu] v.
    apply (iffP idP) => /=; first by case v.
    move=> [] x [] i [] y []; by case x.
  case: u IHu => [| b l] IHu.
    apply (iffP idP) => /=; first by case v.
    move=> [] x [] i [] y []; by case: x => [| x0 [|x1 x]].
  case: v => [| v0 v] /=.
    rewrite orbF; apply (iffP idP).
    - move=> /andP [] /eqP Ha /eqP Hl; subst a l.
      by exists [::], b, [::].
    - move=> [] x [] i [] y []; case: x => [| x0 x] //.
      case: y => //= [] [] -> -> ->; by rewrite eq_refl.
  apply (iffP idP).
  - move=> /orP [] /andP [] /eqP -> {a}.
    + move=> /eqP Hl; subst l.
      by exists [::], b, (v0 :: v).
    + move/IHu => {IHu} [] x [] i [] y [] Hbl -> {v}.
      exists (v0 :: x), i, y => /=; by rewrite Hbl.
  - move=> [] x [] i [] y []; case: x => [| x0 x] /=.
    + move=> [] -> -> -> <-; by rewrite !eq_refl.
    + move=> [] Ha H1 [] H0 H2; subst a v0.
      apply/orP; right; rewrite eq_refl /=.
      apply/IHu; by exists x, i, y.
Qed.

Lemma reduces_catl u v w : reduces u v -> reduces (u ++ w) (v ++ w).
Proof.
  move/reducesP => [] x [] i [] y [] -> ->.
  apply/reducesP; exists x, i, (y ++ w); by rewrite -!catA.
Qed.

Lemma prods_reducesE u v : reduces u v -> 's_[u] = 's_[v].
Proof.
  move/reducesP => [] x [] i [] y [] -> {u} -> {v}.
  by rewrite !big_cat big_cons !big_seq1 /= tperm2 mul1g.
Qed.

Definition braid_reduces (u v : seq 'I_n) := (u =Br v) || (reduces u v).

Lemma braidred_catl (u v w : seq 'I_n) :
  braid_reduces u v -> braid_reduces (u ++ w) (v ++ w).
Proof.
  rewrite /braid_reduces => /orP [/braid_catl -> // |] /reduces_catl ->.
  by rewrite orbT.
Qed.

Lemma braidredE u v : braid_reduces u v -> 's_[u] = 's_[v].
Proof. by move=> /orP []; [apply braid_prods|apply prods_reducesE]. Qed.

End Reduced.

Notation reduced := (reduced_word _).
Notation braidred := (@braid_reduces _).

Hint Resolve braidww.


(** * Cocode insertion algorithm *)
Section Nnon0.

Variable (n0 : nat).
Local Notation n := n0.+1.

Local Notation "a =Br b" := (braidcongr a b) (at level 70).
Local Notation "''s_' i" := (eltr n i) (at level 8, i at level 2).
Local Notation "''s_[' w ']'" :=
  (\prod_(i <- w) 's_i) (at level 8, w at level 2).

Fixpoint inscode (c : seq nat) (i : 'I_n) :=
  if c is c0 :: c' then
    let m := size c' in
    if i > m - c0 then c0 :: inscode c' (inord i.-1)
    else if i == m - c0 :> nat then c0.-1 :: c'
    else if i.+1 == m - c0 :> nat then c0.+1 :: c'
    else c0 :: inscode c' i
  else [::].

Lemma size_inscode c i : size (inscode c i) = size c.
Proof.
  elim: c i => [| c0 c IHc] //= i.
  case: ltnP => _ /=; first by rewrite IHc.
  case: eqP => _ //=.
  case: eqP => _ //=; by rewrite IHc.
Qed.

Lemma head_revcode c0 c : rev (c0 :: c) \is a code -> c0 <= size c.
Proof.
  have H : size c < size (rev (c0 :: c)) by rewrite size_rev /= ltnS.
  move=> /is_codeP/(_ _ H).
  by rewrite rev_cons nth_rcons size_rev ltnn eq_refl.
Qed.

Lemma inord_predS (i : 'I_n) a b : a < i -> i < b -> (inord (n' := n0) i.-1).+1 < b.
Proof.
  move=> Ha Hb; rewrite inordK; last by apply (leq_ltn_trans (leq_pred _)).
  by rewrite (ltn_predK Ha).
Qed.

Lemma inscodeP c (i : 'I_n) :
  rev c \is a code -> i.+1 < size c -> rev (inscode c i) \is a code.
Proof.
  elim: c i => [//= | c0 c IHc] i /= => Hcode.
  have:= Hcode; rewrite rev_cons => /is_code_rconsK Hcd.
  move/(_ _ Hcd): IHc => Hrec.
  have /head_revcode := Hcode => Hc0.
  move/is_codeP : Hcode; rewrite size_rev /= => Hcode.
  rewrite !ltnS => Hisz.
  case: ltnP => Hi.
    rewrite rev_cons.
    move/(_ _ (inord_predS Hi Hisz)) : Hrec => /= /is_code_rcons; apply.
    by rewrite size_rev size_inscode.
  case: eqP => [Hi1 | /eqP Hi1].
    rewrite rev_cons; apply: (is_code_rcons _ Hcd).
    rewrite size_rev; apply (leq_trans (leq_pred _)).
    have := Hcode (size c) (ltnSn (size c)).
    by rewrite rev_cons nth_rcons size_rev ltnn eq_refl.
  have {Hi Hi1} Hi : i < size c - c0 by rewrite ltn_neqAle Hi Hi1.
  case: eqP => [Hi1 | /eqP Hi1].
    rewrite rev_cons; apply: (is_code_rcons _ Hcd).
    by rewrite size_rev -subn_gt0 -Hi1.
  have {Hi Hi1} Hi : i.+1 < size c - c0 by rewrite ltn_neqAle Hi Hi1.
    rewrite rev_cons.
    have /Hrec : i.+1 < size c by apply (leq_trans Hi); exact: leq_subr.
    move/is_code_rcons; apply.
    by rewrite size_rev size_inscode.
Qed.


Let wcord c : seq 'I_n := map inord (wordcd (rev c)).

Lemma wcordE c :
  rev c \is a code -> size c <= n.+1 -> wcord c = pmap insub (wordcd (rev c)).
Proof.
  rewrite /wcord => Hcode; have:= Hcode => /wordcd_ltn/allP.
  rewrite size_rev => Hall Hsz.
  apply (inj_map (@val_inj _ _ _)) => /=.
  rewrite insub_wordcdK //; last by rewrite size_rev.
  rewrite -map_comp -[RHS]map_id -eq_in_map => j /Hall /= Hj.
  rewrite inordK //.
  by case: (size c) Hj Hsz => [//= | sz] /=; exact: leq_trans.
Qed.

Lemma reduced_wcord c :
  rev c \is a code -> size c <= n.+1 -> wcord c \is reduced.
Proof.
  move=> Hc Hsz; rewrite wcordE //.
  by apply reduced_sprod_code; last by rewrite size_rev.
Qed.

Lemma wcord_cons c i : wcord (i :: c) = wcord c ++ map inord (rev (iota (size c - i) i)).
Proof.
  rewrite /wcord /wordcd -map_cat; congr (map _ _).
  rewrite size_rev [size (_ :: _)]/= -(addn1 (size c)) iota_add.
  rewrite !map_cat !flatten_cat /= cats0 !add0n !rev_cons.
  rewrite nth_rcons size_rev ltnn eq_refl.
  congr ((flatten _) ++ _); apply eq_in_map => j.
  by rewrite mem_iota /= add0n nth_rcons size_rev => ->.
Qed.


Lemma ltn_braidC (s : seq 'I_n) (i : 'I_n) :
  (forall u, u \in s -> u.+1 < i) -> [:: i] ++ s =Br s ++ [:: i].
Proof.
  rewrite cat1s cats1.
  move=> Hs; elim: s Hs => [| s0 s IHs] //= Hs.
  apply (braid_trans (y := [:: s0, i & s])).
  - rewrite -[[:: i, s0 & s]]/([:: i; s0] ++ s) -[[:: s0, i & s]]/([:: s0; i] ++ s).
    apply braid_catl; apply rule_gencongr => /=.
    have /Hs -> : s0 \in s0 :: s by rewrite inE eq_refl.
    by rewrite orbT mem_seq1 eq_refl.
  rewrite -[s0 :: _]cat1s -[s0 :: rcons _ _]cat1s.
  apply braid_catr; apply IHs => u Hu; apply Hs; by rewrite inE Hu orbT.
Qed.

Lemma gtn_braidC (s : seq 'I_n) (i : 'I_n) :
  (forall u, u \in s -> i.+1 < u) -> [:: i] ++ s =Br s ++ [:: i].
Proof.
  rewrite cat1s cats1.
  move=> Hs; elim: s Hs => [| s0 s IHs] //= Hs.
  apply (braid_trans (y := [:: s0, i & s])).
  - rewrite -[[:: i, s0 & s]]/([:: i; s0] ++ s) -[[:: s0, i & s]]/([:: s0; i] ++ s).
    apply braid_catl; apply rule_gencongr => /=.
    have /Hs -> : s0 \in s0 :: s by rewrite inE eq_refl.
    by rewrite orTb mem_seq1 eq_refl.
  rewrite -[s0 :: _]cat1s -[s0 :: rcons _ _]cat1s.
  apply braid_catr; apply IHs => u Hu; apply Hs; by rewrite inE Hu orbT.
Qed.

Lemma iota_cut_i (l b : nat) (i : 'I_n) :
  l <= b -> b - l < i -> i < b -> iota (b - l) l =
  (iota (b - l) (i.-1 - (b - l))) ++ [:: i.-1; nat_of_ord i] ++ (iota i.+1 (b - i.+1)).
Proof.
  move=> Hbl Hi1 Hi2.
  have Hbli : b - l <= i.-1 by rewrite -ltnS (ltn_predK Hi1).
  have -> : [:: i.-1; nat_of_ord i] = iota i.-1 2 by rewrite /= (ltn_predK Hi1).
  rewrite -{2}(subnKC Hbli) catA -iota_add.
  rewrite -addSnnS addn1 -subSn // (ltn_predK Hi1) -subSn; last by apply ltnW.
  have Hbli1 := leq_trans (ltnW Hi1) (leqnSn _).
  rewrite -{2}(subnKC Hbli1) -iota_add addnC (addnBA _ Hbli1).
  by rewrite (subnK Hi2) (subKn Hbl).
Qed.

Reserved Notation "''I[' a '..' b ']'" (at level 0, a, b at level 2).
Local Notation "''I[' a '..' b ']'" :=  [seq inord i | i <- rev (iota (b - a) a)].

Lemma braid_pred_lineC (i : 'I_n) (sz c : nat) :
  sz <= n -> i < sz -> c <= sz -> sz - c < i ->
  ([:: inord i.-1] ++ 'I[c .. sz]) =Br ('I[c .. sz] ++ [:: i]).
Proof.
  rewrite /= cats1 => Hsz Hisz Hc0 Hi.
  rewrite (iota_cut_i Hc0 Hi Hisz) !rev_cat !map_cat -cats1 -!catA.
  set A := map _ _; rewrite {1 3}/rev [map _ _]/= inord_val; set B := map _ _.
  apply (braid_trans (y := A ++ [:: i; inord i.-1] ++ (i :: B))); first last.
    do 2 apply braid_catr; rewrite -cat1s; apply ltn_braidC => u.
    rewrite {}/B {A} => /mapP [] x.
    rewrite mem_rev mem_iota => /andP [] _.
    case: i Hisz Hi (inord_predS Hi Hisz) => [[| i] Hi] //= Hisz.
    rewrite !ltnS => /subnKC -> Hszi Hx ->.
    by rewrite inordK //; apply (ltn_trans Hx); apply ltnW.
  rewrite -[i :: B]cat1s -cat1s !catA; apply: braid_catl => {B}.
  apply (braid_trans (y := A ++ [:: inord i.-1; i; inord i.-1])); first last.
    rewrite -catA /=; apply braid_catr; apply rule_gencongr => /=.
    rewrite eq_refl /=.
    suff -> : (inord (n' := n0) i.-1).+1 = i by rewrite eq_refl /= mem_seq1 eq_refl.
    rewrite inordK; last by apply (leq_ltn_trans (leq_pred _)).
    by rewrite (ltn_predK Hi).
  rewrite -[inord i.-1 :: i :: _]cat1s catA; apply braid_catl.
  rewrite /A; case: (ltnP i sz) => Hi'.
    apply gtn_braidC => u.
    rewrite {}/A => /mapP [] x.
    rewrite mem_rev mem_iota => /andP [] Hix Hx -> {u} /=.
    rewrite subnKC // in Hx.
    rewrite inordK; last by apply (leq_ltn_trans (leq_pred _)).
    rewrite (ltn_predK Hi).
    by rewrite inordK; last apply: (leq_trans Hx).
  move: Hi'; rewrite -ltnS => /ltnW.
  by rewrite /leq => /eqP ->.
Qed.

Lemma braid_ltn_lineC (i : 'I_n) (sz c : nat) :
  sz <= n -> i.+1 < sz - c -> c <= sz ->
  [:: i] ++ 'I[c .. sz] =Br 'I[c .. sz] ++ [:: i].
Proof.
  move=> Hsz Hi Hc0; apply gtn_braidC => u /mapP [] x.
  rewrite mem_rev mem_iota => /andP [] Hix Hx -> {u} /=.
  rewrite subnK // in Hx.
  rewrite inordK; last by apply (leq_trans Hx).
  exact: (leq_trans Hi).
Qed.


Require Import path.

Implicit Type (u v w : seq 'I_n).

Definition path_catl p w := [seq v ++ w | v <- p].

Lemma path_catlP p u w :
  path braidred u p -> path braidred (u ++ w) (path_catl p w).
Proof.
  elim: p u => [//= | p0 p IHp] u /= /andP [] Hbr /IHp ->.
  by rewrite braidred_catl.
Qed.

Lemma braidred_inscode_path c (i : 'I_n) :
  rev c \is a code -> size c <= n.+1 -> i.+1 < size c ->
  { p | path braidred ((wcord c) ++ [:: i]) p /\
        last ((wcord c) ++ [:: i]) p = wcord (inscode c i) }.
Proof.
  elim: c i => [//= | c0 c IHc] i /= Hcode.
  have:= Hcode; rewrite rev_cons => /is_code_rconsK /IHc{IHc} Hrec.
  move/head_revcode : Hcode => Hc0.
  rewrite !ltnS wcord_cons -catA => Hsz Hisz.
  case: ltnP => Hi.
    have:= Hsz; rewrite -ltnS => /ltnW/(Hrec _)/(_ (inord_predS Hi Hisz)){Hrec} /=.
    rewrite !wcord_cons -cat1s size_inscode cats0.
    move=> [] pth [] Hpath <-.
    exists ((wcord c ++ [:: inord i.-1] ++ 'I[c0 .. (size c)]) ::
            path_catl pth 'I[c0 .. (size c)]); split => [| {Hpath}].
    - have /= := path_catlP 'I[c0 .. (size c)] Hpath.
      rewrite -catA /= => ->; rewrite andbT.
      rewrite /braidred braid_catr // braid_sym.
      exact: braid_pred_lineC.
    - rewrite /path_catl !catA; case: pth => [//= | p0 p] /=.
      by rewrite (last_map (fun v => v ++ 'I[c0 .. (size c)])).
  case: eqP => [{Hi Hrec} Hi | /eqP Hi1].
    case: c0 Hc0 Hi Hisz => [Hc0 | c0 Hc0 Hi Hisz /=].
      rewrite subn0 => ->; by rewrite ltnn.
    rewrite -{1 3}Hi /= subnS prednK ?subn_gt0 //.
    rewrite rev_cons map_rcons inord_val -!cats1 -catA.
    exists [:: wcord (c0 :: c)]; split; last by [].
    rewrite /= andbT; rewrite /braidred; apply/orP; right.
    apply/reducesP; exists (wcord c ++ 'I[c0 .. (size c)]), i, [::].
    rewrite !cats0 -catA; split; first by [].
    exact: wcord_cons.
  have {Hi Hi1} Hi : i < size c - c0 by rewrite ltn_neqAle Hi Hi1.
  case: eqP => [Hi1 | /eqP Hi1].
    exists [::]; split; first by [].
    by rewrite /= wcord_cons rev_cons map_rcons subnS -Hi1 /= inord_val cats1.
  have {Hi Hi1} Hi : i.+1 < size c - c0 by rewrite ltn_neqAle Hi Hi1.
    have:= Hsz; rewrite -ltnS => /ltnW/(Hrec _)/(_ (leq_trans Hi (leq_subr _ _))) {Hrec} /=.
    rewrite wcord_cons size_inscode.
    move=> [] pth [] Hpath <-.
    exists ((wcord c ++ [:: i] ++ 'I[c0 .. (size c)]) ::
            path_catl pth 'I[c0 .. (size c)]); split => [| {Hpath}].
    - have /= := path_catlP 'I[c0 .. (size c)] Hpath.
      rewrite -catA /= => ->; rewrite andbT.
      rewrite /braidred braid_catr // braid_sym.
      exact: braid_ltn_lineC.
    - rewrite /path_catl !catA; case: pth => [//= | p0 p] /=.
      by rewrite (last_map (fun v => v ++ 'I[c0 .. (size c)])).
Qed.

Fixpoint straighten_rev w :=
  if w is w0 :: w then inscode (straighten_rev w) w0 else (nseq n.+1 0).
Definition straighten w := straighten_rev (rev w).

Lemma size_straighten w : size (straighten w) = n.+1.
Proof.
  rewrite /straighten; elim/last_ind: w => [//= | w wn IHw] /=.
    by rewrite size_nseq.
  by rewrite rev_rcons /= size_inscode.
Qed.

Lemma is_code_straighten w : rev (straighten w) \is a code.
Proof.
  rewrite /straighten; elim/last_ind: w => [| w wn IHw /=].
    rewrite {2}/rev /=.
    have -> : [:: 0, 0 & nseq n0 0] = nseq n.+1 0 by [].
    apply/is_codeP => i; rewrite size_rev size_nseq ltnS => Hi.
    rewrite nth_rev size_nseq ?ltnS //.
    by rewrite nth_nseq if_same.
  rewrite rev_rcons => /=.
  apply (inscodeP IHw).
  by rewrite size_straighten ltnS.
Qed.

Lemma straighten_path_npos w :
  { p | path braidred w p /\ last w p = wcord (straighten w) }.
Proof.
  rewrite /straighten; elim/last_ind: w => [| w wn].
    exists [::]; split; first by [].
    rewrite [LHS]/=; apply esym; apply/nilP.
    rewrite /wcord /nilp size_map size_wordcd sumn_rev /= !add0n; by elim: n0.
  rewrite rev_rcons /= -/(straighten w) -cats1 => [] [] prec [] Hpath Hlast.
  have : size (straighten w) <= n0.+2 by rewrite size_straighten.
  move=> /(braidred_inscode_path (is_code_straighten w)) => Hins.
  have : wn.+1 < size (straighten w) by rewrite size_straighten ltnS.
  move=> /Hins{Hins} [] pins [] Hpathins Hlastins.
  exists (path_catl prec [:: wn] ++ pins); split => [| {Hpath Hpathins}].
  - rewrite cat_path (last_map (fun v => v ++ [:: wn])) Hlast Hpathins andbT.
    exact: path_catlP.
  - by rewrite last_cat (last_map (fun v => v ++ [:: wn])) Hlast.
Qed.

Theorem prods_straighten w : 's_[wcord (straighten w)] = 's_[w].
Proof.
  move: (straighten_path_npos w) => [] p [] Hpath <-.
  elim: p w Hpath => [| p0 p IHp] //= w /andP [] /braidredE -> {w}.
  exact: IHp.
Qed.

Corollary cocode_straightenE w :
  rev (straighten w) = cocode 's_[w].
Proof.
  have:= (prods_straighten w); rewrite {1}(canwordP 's_[w]).
  rewrite -!(big_map (@nat_of_ord _) xpredT) /= canwordE /wcord -map_comp.
  rewrite [map _ _](_ : _ = wordcd (rev (straighten w))); first last.
    rewrite -[RHS](map_id) -eq_in_map => i.
    rewrite /= /wordcd => /flatten_mapP [] j.
    rewrite mem_rev !mem_iota /= add0n size_rev size_straighten ltnS => Hj.
    move=> /andP [] _; rewrite subnK => [Hij | ].
      by rewrite inordK // (leq_trans Hij Hj).
    have /is_codeP := is_code_straighten w.
    rewrite size_rev size_straighten; apply; by rewrite ltnS.
  apply (prods_wordcd_inj (is_code_straighten _) (cocodeP _)).
  - by rewrite size_rev size_straighten.
  - exact: size_cocode.
Qed.

Corollary canword_straightenE w : wcord (straighten w) = canword 's_[w].
Proof.
  rewrite /canword -cocode_straightenE -(wcordE (is_code_straighten w)) //.
  by rewrite size_straighten.
Qed.

Corollary canword_path_npos w :
  { p | path braidred w p /\ last w p = canword 's_[w] }.
Proof. rewrite -canword_straightenE; exact: straighten_path_npos. Qed.

End Nnon0.

Local Notation "''s_' i" := (eltr _ i) (at level 8, i at level 2).
Local Notation "''s_[' w ']'" := (\prod_(i <- w) 's_i) (at level 8, w at level 2).
Local Notation "''II_' n" := ('I_n * 'I_n)%type (at level 8, n at level 2).
Local Notation "a =Br b" := (braidcongr a b) (at level 70) : bool_scope.

Theorem braidred_to_canword n (w : seq 'I_n) :
  { p | path braidred w p /\ last w p = canword 's_[w] }.
Proof.
  case: (altP (n =P 0)) => Hn.
    subst n; case: w => [| [w0 Hw0] w] //=.
    rewrite big_nil canword1; by exists [::].
  move: Hn; case H : {1}(n) => _ //=; subst n.
  exact: canword_path_npos.
Qed.

Lemma braidred_size_decr n (w : seq 'I_n) p :
  path braidred w p -> size w >= size (last w p).
Proof.
  elim: p w => [| p0 p IHp] //= w /andP [] HBr /IHp/leq_trans; apply.
  move: HBr => /orP [ /size_braid -> // |].
  move/reducesP => [] x [] i [] y [] -> ->.
  rewrite !size_cat [size [:: i; i] + _]addnC addnA; exact: leq_addr.
Qed.

Theorem braid_to_canword n (w : seq 'I_n) :
  w \is reduced -> w =Br canword 's_[w].
Proof.
  rewrite unfold_in size_canword braid_sym.
  case: (braidred_to_canword w) => p [] Hpath <- /eqP.
  elim: p w Hpath => [| p0 p IHp] //= w /andP [].
  rewrite {1}/braidred => /orP [] HBr.
  - move/IHp; rewrite (size_braid HBr) => H/H{H} /braid_ltrans ->.
    by rewrite braid_sym.
  - move=> {IHp} /braidred_size_decr Hsz Heq; exfalso.
    move: Hsz; rewrite {}Heq.
    move/reducesP: HBr => [] x [] i [] y [] -> ->.
  rewrite !size_cat [size [:: i; i] + _]addnC addnA /=.
  by rewrite leqNgt addnS ltnS addn1 leqnSn.
Qed.

Theorem reduceP n (u : seq 'I_n) :
  u \isn't reduced -> exists v w, u =Br v /\ reduces v w.
Proof.
  rewrite unfold_in => Hnred.
  have {Hnred} : length ((\prod_(i <- u) 's_ i) : 'S_n.+1) < size u.
    by rewrite ltn_neqAle Hnred length_prods.
  rewrite size_canword.
  case: (braidred_to_canword u) => p [] Hpath <-.
  elim: p u Hpath => [| p0 p IHp] u //=; first by rewrite ltnn.
  rewrite {1}/braidred => /andP [] /orP [] HBr.
  - move/IHp; rewrite (size_braid HBr) => H/H{H}.
    move=> [] v [] w [] /(braid_trans HBr) {HBr} HBr Hred.
    by exists v, w.
  - by exists u, p0.
Qed.

Corollary reduced_braid n (v w : seq 'I_n) :
  v \is reduced -> w \is reduced -> 's_[v] == 's_[w] :> 'S_n.+1 = (v =Br w).
Proof.
  move=> Hv Hw; apply/idP/idP => [/eqP H|].
  - apply (braid_trans (y := canword 's_[v])).
    + exact: braid_to_canword.
    + rewrite H braid_sym; exact: braid_to_canword.
  - by move/braid_prods ->.
Qed.


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
