Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm tuple path bigop.
Require Import subseq partition ordtype schensted congr plactic.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bool.

Section Tools.

Variable T : finType.

Lemma set1_disjoint (i j : T) : [set i] != [set j] -> [disjoint [set i] & [set j]].
Proof.
  move=> Hneq; rewrite /disjoint; apply/pred0P => l /=; apply negbTE.
  rewrite !in_set1; move: Hneq; by apply contra => /andP [] /eqP -> /eqP ->.
Qed.

End Tools.

Lemma enum0 : enum 'I_0 = [::].
Proof. apply/nilP; by rewrite /nilp size_enum_ord. Qed.

Section GreenDef.

Variable Alph : ordType.
Definition extractpred n (wt : n.-tuple Alph) (P : pred 'I_n) :=
  [seq tnth wt i | i <- enum 'I_n & P i].

Lemma extractE n (wt : n.-tuple Alph) P :
  extractpred wt P = mask [seq P i | i <- enum 'I_n] wt.
Proof.
  rewrite /extractpred.
  elim: n wt P => [//= | n IHn].
  + by rewrite enum0.
  + case/tupleP=> w0 w P; rewrite enum_ordS /=.
    set lft := map (lift ord0) _.
    suff : [seq tnth [tuple of w0 :: w] i | i <- lft & P i] = mask [seq P i | i <- lft] w
      by case: (P ord0) => /= -> //=.
    rewrite /lft {lft} filter_map -map_comp -map_comp /= -(IHn w _) /=.
    by rewrite (eq_map (f2 := tnth w));
      last by move=> i /=; rewrite !(tnth_nth (inhabitant Alph)) /=.
Qed.

Lemma extsubsIm n wt (P1 P2 : pred 'I_n) :
  subpred P1 P2 -> subseq (extractpred wt P1) (extractpred wt P2).
Proof.
  rewrite !extractE; case: wt => w /= _.
  elim: n w P1 P2 => [//= | n IHn] w P1 P2 H; first by rewrite enum0.
  case: w => [//= | w0 w]; first by rewrite !mask0.
  rewrite enum_ordS /= -map_comp -map_comp.
  case (boolP (P1 ord0)) => H1.
  + rewrite (H ord0 H1) /= eq_refl; by apply IHn => i /=; apply H.
  + case (boolP (P2 ord0)) => H2.
    rewrite -cat1s.
    set ss := (X in subseq _ (_ ++ X)).
    apply (@subseq_trans _ ([::] ++ ss)); last by apply suffix_subseq.
    rewrite cat0s /ss {ss}; by apply IHn => i /=; apply H.
  by apply IHn => i /=; apply H.
Qed.

Lemma extsubsm n (w : n.-tuple Alph) (P : pred 'I_n) : subseq (extractpred w P) w.
Proof.
  suff -> /= : tval w = mask [seq predT i | i <- enum 'I_n] w
    by rewrite -extractE; apply extsubsIm.
  have -> : [seq true | _ <- enum 'I_n] = nseq n true.
    apply (eq_from_nth (x0 := false)); first by rewrite size_nseq size_map size_enum_ord.
    move=> i; rewrite size_map size_enum_ord => Hi.
    rewrite nth_nseq Hi nth_map => //=; last by rewrite size_enum_ord.
    by move: Hi; case n => [//= | n0]; apply /Ordinal.
  by rewrite mask_true //= size_tuple.
Qed.

Variable N : nat.
Variable wt : N.-tuple Alph.

Definition extract := [fun s : {set 'I_N} => extractpred wt (mem s)].

Lemma size_extract s : size (extract s) = #|s|.
Proof.
  rewrite /extractpred size_map cardE; congr (size (filter (mem s) _)).
  by apply/all_filterP/allP.
Qed.

Lemma extsubsI (s1 s2 : {set 'I_N}) :
  s1 \subset s2 -> subseq (extract s1) (extract s2).
Proof. move/subsetP=> Hincl; apply extsubsIm=> i /=; by apply Hincl. Qed.

Notation is_col r := (sorted (@gtnX Alph) r).

Lemma is_col_extract_cond s P :
  is_col (extract s) -> is_col (extract (s :&: P)).
Proof.
  apply subseq_sorted; first by move=> a b c /= H1 H2; apply (ltnX_trans H2 H1).
  apply extsubsI; rewrite -{2}[s]setIT; apply setIS; by apply subsetT.
Qed.

Definition kseq k (P : {set {set 'I_N}}) :=
  [&& #|P| <= k, trivIset P & [forall (s | s \in P), is_col (extract s)]].

Lemma kseq0 k : kseq k set0.
Proof.
  rewrite /kseq cards0 leq0n /=; apply/andP; split.
  + apply/trivIsetP => A B; by rewrite in_set0.
  + apply/forallP => A; by rewrite in_set0.
Qed.

Definition scover := [fun P : {set {set 'I_N}} => #|cover P|].
Definition greent k := \max_(P | kseq k P) scover P.

Notation Ik k := [set i : 'I_N | i < k].

Lemma iotagtnk k : [seq x <- iota 0 N | gtn k x] = iota 0 (minn N k).
Proof.
  rewrite /minn; case ltnP => Hn.
  + rewrite (eq_in_filter (a2 := predT)); first by rewrite filter_predT.
    move=> i; rewrite mem_iota add0n /= => Hi.
    by rewrite (ltn_trans Hi Hn).
  + rewrite -{1}[k]addn0; move: (0) => i.
    elim: k i N Hn => [//= | k IHk] i n Hn.
    * rewrite (eq_in_filter (a2 := pred0)); first by rewrite filter_pred0.
      move=> j; by rewrite mem_iota leqNgt add0n => /andP [] /negbTE ->.
    * have:= ltn_predK Hn => H; rewrite -H in Hn.
      have:= IHk i.+1 _ Hn => /= <-.
      by rewrite -{1}H /= -{1}[i]add0n ltn_add2r /= addSnnS.
Qed.

Lemma sizeIk k : #|Ik k| = minn N k.
Proof.
  rewrite !cardE size_filter.
  have/eq_count -> : (mem [set i : 'I_N | i < k]) =1 (gtn k) \o val
    by move=> i /=; rewrite in_set.
  by rewrite -count_map /enum_mem -enumT /= val_enum_ord -size_filter iotagtnk size_iota.
Qed.

Lemma extract1 i : (extract [set i]) = [:: tnth wt i].
Proof.
  rewrite /= /extractpred.
  set s := filter _ _; suff -> : s = [:: i] by [].
  have : uniq s by apply filter_uniq; apply enum_uniq.
  have : i \in s by rewrite /s mem_filter /= in_set1 eq_refl mem_enum inE.
  have Hj j : j \in s -> j = i by rewrite /s mem_filter /= in_set1 => /andP [] /eqP ->.
  case: s Hj => [//= | s0 [| s1 s]]; first by rewrite mem_seq1 => _ /eqP ->.
  move=> Hj Hin Huniq; exfalso.
  have Hs0 : s0 = i by apply Hj; rewrite inE eq_refl.
  have Hs1 : s1 = i by apply Hj; rewrite !inE eq_refl orbT.
  move: Huniq; by rewrite Hs0 Hs1 /= inE eq_refl.
Qed.

Lemma greent_inf k : greent k >= minn N k.
Proof.
  pose P := [set [set i ] | i in Ik k].
  have <- : scover P = minn N k.
    rewrite /=; suff -> : cover P = Ik k by apply sizeIk.
    rewrite /cover /P {P}.
    apply setP => i; apply/(sameP idP); apply(iffP idP).
    + move => Hi; apply/bigcupP; exists [set i]; last by rewrite in_set1.
      apply/imsetP; by exists i.
    + move/bigcupP => [] St /imsetP [] j Hj -> {St}.
      by rewrite in_set1 => /eqP ->.
  have HP : kseq k P.
    rewrite /kseq; apply/and3P; split.
    + rewrite card_imset; last by apply set1_inj.
      rewrite sizeIk; by apply geq_minr.
    + apply/trivIsetP => A B /imsetP [] i Hi -> {A} /imsetP [] j Hj -> {B}.
      rewrite inE in Hi; rewrite inE in Hj => Hneq.
      by apply set1_disjoint.
    + apply/forallP => s; apply/implyP => /imsetP [] i Hi ->; rewrite inE in Hi.
      by rewrite extract1 /sorted.
  rewrite /greent; by apply leq_bigmax_cond.
Qed.

Lemma greent_sup k : greent k <= N.
Proof.
  rewrite /greent /=; apply/bigmax_leqP => P _.
  move: (cover P) => cover {P}; rewrite -{5}[N]card_ord.
  by apply max_card.
Qed.

End GreenDef.

Arguments scover [N].

Lemma greentcast (Alph : ordType) (M N : nat) (Heq : M = N) k (V : M.-tuple Alph) :
  greent (tcast Heq V) k = greent V k.
Proof. by subst M. Qed.

Section GreenCat.

Variable Alph : ordType.
Variable M N : nat.
Variable V : M.-tuple Alph.
Variable W : N.-tuple Alph.

Local Notation linj := (@lshift M N).
Local Notation rinj := (@rshift M N).

Lemma enumIMN : enum 'I_(M + N) = map linj (enum 'I_M) ++ map rinj (enum 'I_N).
Proof.
  apply (inj_map (@ord_inj (M + N))).
  rewrite map_cat -map_comp -map_comp !val_enum_ord.
  rewrite (eq_map (f2 := (addn M) \o val)); last by [].
  by rewrite map_comp !val_enum_ord -iota_addl [M + 0]addnC iota_add.
Qed.

Definition lsplit := [fun s : {set 'I_(M+N)} => linj @^-1: s].
Definition rsplit := [fun s : {set 'I_(M+N)} => rinj @^-1: s].

Lemma linjP : injective linj.
Proof.
  move=> [] i Hi [] j Hj /eqP H; apply /eqP; move: H; by rewrite !/eq_op /=.
Qed.
Lemma rinjP : injective rinj.
Proof.
  move=> [] i Hi [] j Hj /eqP H; apply /eqP; move: H; by rewrite !/eq_op /= eqn_add2l.
Qed.

Lemma disjoint_inj (sM : {set 'I_M}) (sN : {set 'I_N}) :
  [disjoint linj @: sM & rinj @: sN].
Proof.
  rewrite /disjoint; apply/pred0P=> i /=; apply negbTE; apply (introN idP) => /andP [].
  move/imsetP=> [] [] l HlM Hl -> {i} /imsetP [] [] r HrN Hr /eqP.
  rewrite /lshift /rshift /eq_op /= => /eqP Heq.
  have:= HlM; by rewrite Heq ltnNge leq_addr.
Qed.

Lemma splitsetK (s : {set 'I_(M+N)}) : s = (linj @: lsplit s) :|: (rinj @: rsplit s).
Proof.
  apply/setP/subset_eqP/andP; split; apply/subsetP=> i Hi.
  + apply/setUP.
    have:= splitK i; case: fintype.splitP => j Hj; rewrite /unsplit => Hinj.
    * left; apply/imsetP; exists j => /=; last by rewrite Hinj.
      by rewrite inE Hinj.
    * right; apply/imsetP; exists j => /=; last by rewrite Hinj.
      by rewrite inE Hinj.
  + move: Hi; rewrite inE => /orP []; move/imsetP => [] j; by rewrite inE => H ->.
Qed.

Lemma cutcover (p : {set {set 'I_(M + N)}}) :
  cover p = linj @: (cover (lsplit @: p)) :|: rinj @: (cover (rsplit @: p)).
Proof.
  rewrite /cover.
  apply/setP/subset_eqP/andP; split; apply/subsetP=> i.
  * move/bigcupP=> [] part Hpart Hi.
    have:= splitK i; case: fintype.splitP => j Hj; rewrite /unsplit => Hinj.
    - rewrite -Hinj; apply/setUP; left.
      apply mem_imset; apply/bigcupP; exists (lsplit part); first by apply mem_imset.
      by rewrite inE Hinj.
    - rewrite -Hinj; apply/setUP; right.
      apply mem_imset; apply/bigcupP; exists (rsplit part); first by apply mem_imset.
      by rewrite inE Hinj.
  * move/setUP => [] /imsetP [] j /bigcupP [] part /imsetP [] prt Hprt Hcut Hj ->;
      apply/bigcupP; exists prt => //=; move: Hj; by rewrite Hcut inE.
Qed.

Lemma preimset_trivIset (T1 : finType) (T2 : finType) (P : {set {set T2}}) (F : T1 -> T2) :
  trivIset P -> injective F -> trivIset ((fun s : {set T2}=> F @^-1: s) @: P).
Proof.
  move/trivIsetP => Htriv Hinj.
  apply/trivIsetP => A B /imsetP [] FA FAP -> {A} /imsetP [] FB FBP -> Hneq.
  have {Hneq} Hneq : FA != FB by move: Hneq; apply contra => /eqP ->.
  have := Htriv _ _ FAP FBP Hneq; rewrite -!setI_eq0 -preimsetI => /eqP ->.
  by rewrite preimset0.
Qed.


Lemma extlsplit s :
   extract V (lsplit s) = extract [tuple of V ++ W] (s :&: [set i : 'I_(M+N)| i < M]).
Proof.
  rewrite /= !extractE enumIMN map_cat.
  rewrite mask_cat; last by rewrite 2!size_map size_enum_ord size_tuple.
  set sl := map _ (map rinj _).
  have -> : sl = (nseq N false).
    rewrite /sl -map_comp.
    apply (@eq_from_nth _ false); first by rewrite size_map size_enum_ord size_nseq.
    move => i; rewrite size_map size_enum_ord => Hi.
    rewrite nth_nseq Hi /= (nth_map (Ordinal Hi)) /=; last by rewrite size_enum_ord.
    by rewrite inE /rinj inE /= -{9}[M]addn0 ltn_add2l ltn0 andbF.
  rewrite mask_false cats0 -[in RHS]map_comp; congr (mask _ V).
  apply eq_map => i /=; rewrite inE in_setI.
  suff -> : linj i \in [set i0 : 'I_(M+N) | i0 < M] by rewrite andbT.
  rewrite inE /=; by apply ltn_ord.
Qed.

Lemma extrsplit s :
   extract W (rsplit s) = extract [tuple of V ++ W] (s :&: [set i : 'I_(M+N)| i >= M]).
Proof.
  rewrite /= !extractE enumIMN map_cat.
  rewrite mask_cat; last by rewrite 2!size_map size_enum_ord size_tuple.
  set sl := map _ (map linj _).
  have -> : sl = (nseq M false).
    rewrite /sl -map_comp.
    apply (@eq_from_nth _ false); first by rewrite size_map size_enum_ord size_nseq.
    move => i; rewrite size_map size_enum_ord => Hi.
    rewrite nth_nseq Hi /= (nth_map (Ordinal Hi)) /=; last by rewrite size_enum_ord.
    by rewrite inE /linj inE /= {2}(nth_enum_ord _ Hi) leqNgt Hi /= andbF.
  rewrite mask_false cat0s -[in RHS]map_comp; congr (mask _ W).
  apply eq_map => i /=; rewrite inE in_setI.
  suff -> : rinj i \in [set i0 : 'I_(M+N) | M <= i0] by rewrite andbT.
  rewrite inE /=; by apply leq_addr.
Qed.

Lemma greent_cat k : greent [tuple of V ++ W] k <= greent V k + greent W k.
Proof.
  rewrite /greent; set tc := [tuple of V ++ W].
  have H : 0 < #|kseq tc k| by apply/card_gt0P; exists set0; apply kseq0.
  case: (@eq_bigmax_cond _ (kseq tc k) scover H) => ks Hks ->.
  pose PV := lsplit @: ks; pose PW := rsplit @: ks.
  move: Hks => /and3P [] Hcard Htriv /forallP Hcol.
  have HV : kseq V k PV.
    rewrite /kseq; apply/and3P; split; first by apply (leq_trans (leq_imset_card _ _) Hcard).
    - by apply preimset_trivIset; last by apply linjP.
    - apply/forallP=> stmp; apply/implyP => /imsetP [] s Hs -> {stmp}.
      rewrite extlsplit; apply is_col_extract_cond; have:= Hcol s; by rewrite Hs.
  have HleqV := (@leq_bigmax_cond _ _ scover _ HV).
  have HW : kseq W k PW.
    rewrite /kseq; apply/and3P; split; first by apply (leq_trans (leq_imset_card _ _) Hcard).
    - by apply preimset_trivIset; last by apply rinjP.
    - apply/forallP=> stmp; apply/implyP => /imsetP [] s Hs -> {stmp}.
      rewrite extrsplit; apply is_col_extract_cond; have:= Hcol s; by rewrite Hs.
  have HleqW := (@leq_bigmax_cond _ _ scover _ HW).
  have -> : scover ks = scover PV + scover PW.
    rewrite /= cutcover.
    have:= disjoint_inj (cover PV) (cover PW); rewrite -((leq_card_setU _ _).2) => /eqP ->.
    by rewrite (card_imset _ linjP) (card_imset _ rinjP).
  by apply leq_add.
Qed.

End GreenCat.


Section GreenSeq.

Variable Alph : ordType.
Implicit Type u v w : seq Alph.

Definition green u := [fun k => greent (in_tuple u) k].

Lemma green_cat k v w : green (v ++ w) k <= green v k + green w k.
Proof.
  rewrite /disjoint /=.
  suff -> : greent (in_tuple (v ++ w)) k = greent [tuple of (in_tuple v) ++ (in_tuple w)] k
    by apply greent_cat.
  have Hsz : size (v ++ w) = (size v + size w) by rewrite size_cat.
  rewrite -(greentcast Hsz); congr (greent _ k).
  apply eq_from_tnth => i; by rewrite tcastE !(tnth_nth (inhabitant Alph)).
Qed.

Lemma green_row r k : is_row r -> green r k = minn (size r) k.
Proof.
  move=> Hrow /=.
  apply/eqP; rewrite eqn_leq; apply/andP; split; last by apply greent_inf.
  rewrite leq_min greent_sup /= /greent /=; apply/bigmax_leqP => s.
  rewrite /kseq /trivIset => /and3P [] Hcard /eqP /= <- /forallP Hsort.
  suff {Hcard} H B : B \in s -> #|B| <= 1.
    apply (@leq_trans (\sum_(B in s) 1)); last by rewrite sum1_card.
    by apply leq_sum.
  rewrite -(size_extract (in_tuple r)) /=.
  move=> HB; have {Hsort} := Hsort B; rewrite HB {HB s} /=.
  set s := (extractpred _ _) => Hsort.
  have : sorted (leqX Alph) s.
    move: Hrow; apply subseq_sorted; last by apply extsubsm.
    move=> x y z; apply leqX_trans.
  case H : s Hsort => [//= | s0 [//= | s1 tls]] /= /andP [] Hgt _ /andP [] Hle _.
  have := leqX_ltnX_trans Hle Hgt; by rewrite ltnXnn.
Qed.

Corollary green_inf_tab k t :
  is_tableau t -> green (to_word t) k <= \sum_(l <- (shape t)) minn l k.
Proof.
  rewrite /to_word; elim: t => [_ | t0 t IHt] /=.
  + apply (@leq_trans 0); last by [].
    by apply greent_sup.
  + move=> /and4P [] _ Hrow _ /IHt => {IHt} Ht.
    rewrite rev_cons flatten_rcons; apply (leq_trans (green_cat _ _ _)).
    rewrite big_cons addnC; apply leq_add; last exact Ht.
    by rewrite green_row.
Qed.

End GreenSeq.

