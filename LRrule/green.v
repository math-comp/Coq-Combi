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

Lemma mem_imset_inj (T1 T2 : finType) (f : T1 -> T2) (i : T1) (s : {set T1}) :
  injective f -> (f i) \in f @: s = (i \in s).
Proof.
  move=> H; apply/(sameP idP); apply(iffP idP); first by apply mem_imset.
  by move/imsetP => [] j Hj /H ->.
Qed.

Lemma subset_imsetK (T1 T2: finType) (f : T1 -> T2) (s t : {set T1}):
  injective f -> f @: s \subset f @: t -> s \subset t.
Proof.
  move=> Hinj /subsetP H; apply/subsetP => x /(mem_imset f) Hfx.
  by have:= H _ Hfx => /imsetP [] y Hy /Hinj ->.
Qed.

Lemma imset_inj (T1 T2: finType) (f : T1 -> T2) :
  injective f -> injective (fun s : {set T1} => (imset f (mem s))).
Proof.
  move=> Hinj s1 s2 /eqP; rewrite eqEsubset => /andP [] H12 H21.
  have {Hinj} Hinj := (subset_imsetK Hinj).
  apply /eqP; rewrite eqEsubset.
  by rewrite (Hinj _ _ H12) (Hinj _ _ H21).
Qed.

Lemma card_seq (s : seq T) : #|[set i in s]| <= size s.
Proof.
  elim: s => [//= | s0 s IHs]; set t := [set i | i \in _].
  - suff -> : t = set0 by rewrite cards0.
    rewrite -setP => i /=; by rewrite inE.
  - rewrite /t set_cons cardsU1 /= -add1n.
    by apply leq_add; first by case: (s0 \notin [set i in s]).
Qed.

Lemma take_iota i k n : take k (iota i n) = iota i (minn k n).
Proof.
  rewrite /minn; case: (ltnP k n) => H; last by apply take_oversize; rewrite size_iota.
  elim: k n H i => [//= | k IHk]; first by case.
  case=> //= n H i; congr (i :: _); by apply IHk.
Qed.

Lemma take_enumI n (i : 'I_n) k : i \in take k (enum 'I_n) = (i < k).
Proof.
  case: i => i Hi /=.
  rewrite -(mem_map val_inj) map_take val_enum_ord /= take_iota mem_iota /= add0n.
  rewrite /minn; case: (ltnP k n) => //= H.
  by rewrite Hi (leq_trans Hi H).
Qed.

Definition trivIseq (S : seq {set T}) : Prop :=
  forall i j, i < j < size S -> [disjoint (nth set0 S i) & (nth set0 S j)].

Lemma trivIseq_consK u0 (u : seq {set T}) : trivIseq (u0 :: u) -> trivIseq u.
Proof. rewrite /trivIseq => H i j Hij; apply (H i.+1 j.+1); by rewrite /= !ltnS. Qed.

Lemma trivIsubseq (u v : seq {set T}) :
  subseq u v -> trivIseq v -> trivIseq u.
Proof.
  elim: v u => [/= v1 /eqP -> //=| v1 v IHv] u.
  case: u => [/= _ _|u1 u /=]; first by move=> i j /= /andP [] _.
  case eqP => [->|_] Hsubs Htriv i j Hij.
  + have {IHv} IHv := (IHv _ Hsubs (trivIseq_consK Htriv)).
    case: i Hij => [|i]; case: j => [//=| j] /=; rewrite !ltnS; last by apply IHv.
    move/(mem_nth set0)/(mem_subseq Hsubs); set x := nth set0 u j => Hv.
    rewrite -(nth_index set0 Hv); move: Hv; rewrite -index_mem; set i := index x v => Hi.
    have -> : v1 = nth set0 (v1 :: v) 0 by [].
    have -> : nth set0 v i = nth set0 (v1 :: v) i.+1 by [].
    by apply Htriv.
  + apply IHv => //=; by apply (trivIseq_consK Htriv).
Qed.

Lemma trivIs S : trivIseq S -> trivIset [set i | i \in S].
Proof.
  rewrite /trivIseq => H; apply/trivIsetP => A B.
  rewrite !inE => HAin HBin.
  have:= HAin; have:= HBin; rewrite -!index_mem.
  rewrite -{2 3}(nth_index set0 HAin) -{2 3}(nth_index set0 HBin).
  set iA := index A S; set iB := index B S.
  wlog leqAB: iA iB / iA <= iB.
    move=> Hwlog HA HB; case (leqP iA iB) => HAB.
      by apply (Hwlog iA iB HAB).
      rewrite eq_sym disjoint_sym; by apply (Hwlog iB iA (ltnW HAB)).
  move=> HiA HiB HAB.
  apply H; rewrite HiA andbT ltn_neqAle leqAB andbT.
  by move: HAB; apply contra => /eqP ->.
Qed.

End Tools.

Lemma trivIseq_map (T1 T2 : finType) (f : T1 -> T2) (S : seq {set T1}) :
  injective f -> trivIseq S -> trivIseq (map (fun s : {set T1} => f @: s) S).
Proof.
  move=> Hinj; rewrite /trivIseq => H i j /andP [].
  rewrite size_map => Hij Hj; have Hi := (ltn_trans Hij Hj).
  rewrite /disjoint; apply/pred0P => l /=; apply (introF idP) => /andP [].
  rewrite !(nth_map set0) //=.
  move/imsetP => [] li Hli -> {l} /imsetP [] l Hlj /Hinj Heq; subst li.
  have : i < j < size S by rewrite Hij Hj.
  move/(H i j); rewrite /disjoint => /pred0P => Hd.
  have:= Hd l; by rewrite /= Hli Hlj.
Qed.

Lemma enum0 : enum 'I_0 = [::].
Proof. apply/nilP; by rewrite /nilp size_enum_ord. Qed.

Section GreenDef.

Variable Alph : ordType.
Definition extractpred n (wt : n.-tuple Alph) (P : pred 'I_n) :=
  [seq tnth wt i | i <- enum 'I_n & P i].

Lemma extract_cast n m (wt : n.-tuple Alph) (P : pred 'I_n) (H : n = m) :
  extractpred wt P = extractpred (tcast H wt) (P \o (cast_ord (esym H))).
Proof.
  subst n; rewrite tcast_id /extractpred.
  congr (map (tnth wt) _); apply eq_filter => [] [] i Hi /=.
  suff -> : cast_ord (erefl m) (Ordinal Hi) = (Ordinal Hi) by [].
  apply/eqP; by rewrite /eq_op /=.
Qed.

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

Definition ksupp k (P : {set {set 'I_N}}) :=
  [&& #|P| <= k, trivIset P & [forall (s | s \in P), is_col (extract s)]].

Lemma ksupp0 k : ksupp k set0.
Proof.
  rewrite /ksupp cards0 leq0n /=; apply/andP; split.
  + apply/trivIsetP => A B; by rewrite in_set0.
  + apply/forallP => A; by rewrite in_set0.
Qed.

Definition scover := [fun P : {set {set 'I_N}} => #|cover P|].
Definition greent k := \max_(P | ksupp k P) scover P.

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

Lemma extract0 : extract set0 = [::].
Proof.
  rewrite /= /extractpred.
  have /eq_filter -> : mem set0 =1 (@pred0 'I_N) by move=> i /=; rewrite in_set0.
  by rewrite filter_pred0.
Qed.

Lemma extract1 i : extract [set i] = [:: tnth wt i].
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
  have HP : ksupp k P.
    rewrite /ksupp; apply/and3P; split.
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

Lemma lrinjF i j : (linj i == rinj j) = false.
Proof.
  apply (introF idP); case: i j => [] i Hi [] j Hj.
  rewrite /eq_op /= => /eqP H.
  move: Hi; by rewrite H ltnNge leq_addr.
Qed.

Lemma rinj_in_linjF i (s : {set 'I_M}) :
  rinj i \in [set linj x | x in s] = false.
Proof. apply negbTE; apply (introN idP) => /imsetP [] j _ /eqP; by rewrite eq_sym lrinjF. Qed.

Lemma disjoint_inj (sM : {set 'I_M}) (sN : {set 'I_N}) :
  [disjoint linj @: sM & rinj @: sN].
Proof.
  rewrite /disjoint; apply/pred0P=> i /=; apply negbTE; apply (introN idP) => /andP [].
  move/imsetP=> [] [] l HlM Hl -> {i} /imsetP [] [] r HrN Hr /eqP.
  by rewrite lrinjF.
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
  have H : 0 < #|ksupp tc k| by apply/card_gt0P; exists set0; apply ksupp0.
  case: (@eq_bigmax_cond _ (ksupp tc k) scover H) => ks Hks ->.
  pose PV := lsplit @: ks; pose PW := rsplit @: ks.
  move: Hks => /and3P [] Hcard Htriv /forallP Hcol.
  have HV : ksupp V k PV.
    rewrite /ksupp; apply/and3P; split; first by apply (leq_trans (leq_imset_card _ _) Hcard).
    - by apply preimset_trivIset; last by apply linjP.
    - apply/forallP=> stmp; apply/implyP => /imsetP [] s Hs -> {stmp}.
      rewrite extlsplit; apply is_col_extract_cond; have:= Hcol s; by rewrite Hs.
  have HleqV := (@leq_bigmax_cond _ _ scover _ HV).
  have HW : ksupp W k PW.
    rewrite /ksupp; apply/and3P; split; first by apply (leq_trans (leq_imset_card _ _) Hcard).
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
  rewrite /ksupp /trivIset => /and3P [] Hcard /eqP /= <- /forallP Hsort.
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
  elim: t => [_ | t0 t IHt] /=.
  + rewrite /to_word; by apply (@leq_trans 0); first apply greent_sup.
  + move=> /and4P [] _ Hrow _ /IHt => {IHt} Ht.
    rewrite to_word_cons; apply (leq_trans (green_cat _ _ _)).
    rewrite big_cons addnC; apply leq_add; last exact Ht.
    by rewrite green_row.
Qed.

Definition sym_cast m n (i : 'I_(m + n)) : 'I_(n + m) := cast_ord (addnC m n) i.

Lemma cast_eq m n i j (H : m = n):
  ((cast_ord H i) == (cast_ord H j)) = (i == j).
Proof. by apply/(sameP idP); apply(iffP idP) => [/eqP -> //= | ] /eqP /cast_ord_inj ->. Qed.

Lemma sym_cast_eq m n i j : ((@sym_cast m n i) == sym_cast j) = (i == j).
Proof. by apply cast_eq. Qed.

Lemma cast_map n m (P : pred 'I_n) (H : m = n) :
  [seq P i | i <- enum 'I_n] = [seq P ((cast_ord H) i) | i <- enum 'I_m].
Proof.
  apply (eq_from_nth (x0 := false)).
  + do 2 rewrite size_map size_enum_ord; by rewrite H.
  + move=> i; rewrite size_map size_enum_ord => Hn. have := Hn; rewrite -{1}H => Hm.
    rewrite (nth_map (Ordinal Hn)); last by rewrite size_enum_ord.
    rewrite (nth_map (Ordinal Hm)); last by rewrite size_enum_ord.
    set i1 := (X in P X); have -> : i1 = Ordinal Hn.
      by apply/eqP; rewrite /eq_op /= nth_enum_ord.
    set i2 := (X in _ = P X); have -> : i2 = Ordinal Hn.
      by apply/eqP; rewrite /eq_op /= nth_enum_ord.
    by [].
Qed.

Lemma cast_mapC n m (P : pred 'I_(n + m)) :
  [seq P i | i <- enum 'I_(n + m)] = [seq P (sym_cast i) | i <- enum 'I_(m + n)].
Proof. by apply cast_map. Qed.


Lemma mem_cast m n (H : m = n) (i : 'I_m) (S : {set 'I_m}) :
  ((cast_ord H) i) \in [set (cast_ord H) i | i in S] = (i \in S).
Proof.
  apply/(sameP idP); apply(iffP idP).
  + move=> Hin; apply/imsetP; by exists i.
  + by move/imsetP => [] j Hin /cast_ord_inj ->.
Qed.

Fixpoint tabextr_rec sh : seq {set 'I_(sumn sh)} :=
  if sh is s0 :: sh then
    [seq (sym_cast (@rshift (sumn sh) s0 i)) |:
         (((@sym_cast _ _)\o (@lshift (sumn sh) s0)) @: (nth set0 (tabextr_rec sh) i))
    | i <- enum 'I_s0]
  else [::].

Lemma size_tabextr_rec_cons s0 sh : size (tabextr_rec (s0 :: sh)) = s0.
Proof. by rewrite /= size_map size_enum_ord. Qed.

Lemma size_tabextr_rec sh : size (tabextr_rec sh) = head 0 sh.
Proof. by case sh => [//= | s0 s]; apply size_tabextr_rec_cons. Qed.

Lemma size_tabextr_tab (t : seq (seq Alph)) :
  (size (head [::] t)) = size (tabextr_rec (shape t)).
Proof.
  by rewrite size_tabextr_rec (_: head 0 (shape t) = size (head [::] t)); last by case t.
Qed.

Definition cast_set_tab (t : seq (seq Alph)) :=
  [fun s : {set 'I_(sumn (shape t))} => (cast_ord (size_to_word t)) @: s].

Definition tabextr (t : seq (seq Alph)) :=
  [fun k => [seq (cast_set_tab t s) | s <- take k (tabextr_rec (shape t))]].

Lemma trivIseq_tabextr_rec sh : trivIseq (tabextr_rec sh).
Proof.
  elim: sh => [/= | s0 sh /= IHsh]; first by rewrite /trivIseq => i j /= /andP [].
  rewrite /trivIseq size_tabextr_rec_cons => i j /andP [] Hij Hj.
  have Hi := (ltn_trans Hij Hj).
  rewrite /disjoint; apply/pred0P => l /=; apply (introF idP) => /andP [].
  rewrite (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
  rewrite (nth_map (Ordinal Hj)); last by rewrite size_enum_ord.
  rewrite !nth_enum_ord //=.
  rewrite in_setU1 => /orP [].
  + move/eqP => ->; rewrite in_setU1 => /orP []; rewrite /sym_cast /=.
    * by rewrite /eq_op /= !nth_enum_ord //= eqn_add2l (ltn_eqF Hij).
    * move/imsetP => [] k _ /= /cast_ord_inj /eqP; by rewrite eq_sym lrinjF.
  + move/imsetP => [] li Hli -> {l}.
    rewrite in_setU1 => /orP [].
    * by rewrite sym_cast_eq lrinjF.
    * move/imsetP => [] l Hlj /= /cast_ord_inj /linjP H; move: H Hli => -> Hli.
      case: (ltnP j (size (tabextr_rec sh))) => Hj1;
        last by move: Hlj; rewrite (nth_default _ Hj1) in_set0.
      have : i < j < size (tabextr_rec sh) by rewrite Hij Hj1.
      move/(IHsh i j); rewrite /disjoint => /pred0P => H.
      have:= H l; by rewrite /= Hli Hlj.
Qed.


Lemma trivIset_tabextr k (t : seq (seq Alph)) : trivIset [set s | s \in (tabextr t k)].
Proof.
  apply trivIs; rewrite /tabextr /=.
  apply trivIseq_map; first by apply cast_ord_inj.
  apply (trivIsubseq (v := (tabextr_rec (shape t)))).
  + rewrite -{2}[tabextr_rec (shape t)](cat_take_drop k).
    by apply prefix_subseq.
  + by apply trivIseq_tabextr_rec.
Qed.

Lemma extract_rec t0 (t : seq (seq Alph)) i :
  i < size t0 ->
  ((extract (in_tuple (to_word (t0 :: t))))
     [set cast_ord (size_to_word (t0 :: t)) x
     | x in nth set0 (tabextr_rec (shape (t0 :: t))) i]) =
  rcons ((extract (in_tuple (to_word t)))
           [set cast_ord (size_to_word t) x
           | x in nth set0 (tabextr_rec (shape t)) i])
        (nth (inhabitant Alph) t0 i).
Proof.
  move => Hi; rewrite /= !extractE /=.
  set cst := cast_ord (size_to_word (t0 :: t)).
  rewrite (nth_map (Ordinal Hi) _ _); last by rewrite size_enum_ord.
  rewrite !nth_enum_ord //=.
  have -> : (nth (Ordinal Hi) (enum 'I_(size t0)) i) = (Ordinal Hi)
    by apply: val_inj => //=; rewrite nth_enum_ord.
  rewrite (cast_map _ (size_to_word (t0 :: t))) -/cst.
  rewrite /size_tab /= -[sumn (shape t)]/(size_tab t) cast_mapC.
  set f1 := (X in map X _).
  have {f1} /eq_map -> : f1 =1 mem ((rshift (size_tab t) (Ordinal Hi))
                  |: [set lshift (size t0) x | x in nth set0 (tabextr_rec (shape t)) i]).
    by rewrite /f1 => j; rewrite mem_cast imset_comp -imsetU1 mem_cast /=.
  rewrite {1}to_word_cons enumIMN map_cat.
  rewrite mask_cat;
    last by rewrite 2!size_map size_enum_ord -size_to_word.
  rewrite -2!map_comp.
  set f1 := (X in map X _).
  have {f1} /eq_map -> : f1 =1 mem (nth set0 (tabextr_rec (shape t)) i).
    move=> j; rewrite /f1 /= !inE lrinjF /=.
    by rewrite mem_imset_inj; last by apply linjP.
  set f2 := (X in _ ++ mask (map X _) _).
  have {f2} /eq_map -> : f2 =1 mem [set (Ordinal Hi)].
    move=> j; rewrite /f2 /= !inE.
    set b := (X in _ || X); have {b} -> : b = false.
      rewrite /b; apply/imsetP => [] [] k _ /eqP; by rewrite eq_sym lrinjF.
    rewrite orbF.
    by apply/(sameP idP); apply(iffP idP) => [/eqP -> //=|] /eqP/rinjP ->.
  have := extract1 (in_tuple t0) (Ordinal Hi); rewrite /extract /= extractE /= => ->.
  rewrite {cst} cats1 (tnth_nth (inhabitant Alph)) /=.

  rewrite (cast_map _ (size_to_word t)) /=.
  set f1 := (X in map X _).
  set f2 := (X in _ = rcons (mask (map X _) _) _).
  by have /eq_map -> : f1 =1 f2 by rewrite /f1 /f2 /inE => j /=; rewrite mem_cast.
Qed.

Lemma sorted_tabextr (t : seq (seq Alph)) i :
  is_tableau t -> i < size (tabextr_rec (shape t)) ->
  sorted (gtnX Alph)
         (extract (in_tuple (to_word t))
                  [set cast_ord (size_to_word t) x
                  | x in nth set0 (tabextr_rec (shape t)) i]).
Proof.
  elim: t => [//= | t0 t IHt].
  rewrite [X in X -> _]/=; move=> /and4P [] _ _ /dominateP [] Hsz Hdom Htab.
  rewrite size_map size_enum_ord => Hi.
  rewrite (extract_rec _ Hi).
  case (ltnP i (size (head [::] t))) => Hit.
  + have:= Hit; rewrite size_tabextr_tab; move/(IHt Htab) => {IHt}.
    move Hrec : (extract _ _) => ext.
    case: ext Hrec => [//= | a0 ext] Hext.
    rewrite rcons_cons /= rcons_path => -> /=.
    suff {Hdom} -> : last a0 ext = nth (inhabitant Alph) (head [::] t) i by apply Hdom.
    rewrite -[last a0 ext]/(last (inhabitant Alph) (a0 :: ext)) -Hext {a0 ext Hext}.
    case: t Hsz Htab Hit => [//= | t1 t] Hsz Htab Hit.
    by rewrite (extract_rec _ Hit) last_rcons.
  + rewrite nth_default; last by rewrite -size_tabextr_tab.
    by rewrite imset0 extract0.
Qed.

Lemma ksupp_tabextr k t :
  is_tableau t -> ksupp (in_tuple (to_word t)) k [set s | s \in (tabextr t k)].
Proof.
  move=> Htab; rewrite /ksupp /tabextr; apply/and3P; split.
  + apply (leq_trans (card_seq ((tabextr t) k))).
    rewrite /tabextr /= size_map size_take; by apply geq_minl.
  + apply trivIset_tabextr.
  + apply/forallP => s; apply/implyP.
    rewrite /= inE map_take => /mem_take /mapP [] S Hin ->.
    rewrite -(nth_index set0 Hin); move: Hin; rewrite -index_mem; set i := index _ _ => Hi.
    by apply (sorted_tabextr Htab).
Qed.

Lemma scover_tabextr_rec k t t0 :
  (cast_ord (esym (size_to_word (t0 :: t)))) @:
    cover [set s in (tabextr (t0 :: t) k)] =
  ((@sym_cast _ _)\o (@rshift _ _)) @:
    [set s : 'I_(size t0) | s < k]
  :|:
  ((@sym_cast _ _)\o (@lshift _ _) \o cast_ord (esym (size_to_word t))) @:
    cover [set s in (tabextr t k)].
Proof.
  apply/setP/subset_eqP/andP; split; apply/subsetP => i.
  + move: i; rewrite -[size_tab (t0 :: t)]/(size t0 + size_tab t) => i.
    have <- := cast_ordKV (addnC (size_tab t) (size t0)) i.
    move H : (cast_ord (esym (addnC (size_tab t) (size t0))) i) => j {i H} Hj.
    rewrite in_setU; apply/orP.
    have:= splitK j; case: fintype.splitP => i _; rewrite /unsplit=> Hinj.
    * right; rewrite 2!imset_comp mem_cast.
      move: Hj; set jsym := cast_ord _ j.
      have <- := cast_ordK (size_to_word (t0 :: t)) jsym.
      rewrite mem_cast; set jtab := cast_ord _ jsym.
      rewrite /cover => /bigcupP [] sj; rewrite inE /tabextr /=.
      move/mapP => [] sj1; rewrite -map_take => /mapP => [] [] icol.
      rewrite take_enumI => Hicol -> -> {sj1 sj}.
      rewrite /jtab {jtab} mem_cast /jsym {jsym} /size_tab /sym_cast imset_comp.
      rewrite -imsetU1 mem_cast -Hinj in_setU1 lrinjF /=.
      rewrite !(mem_imset_inj _ _ (@linjP _ _)).
      set S : {set 'I_(size_tab t)} := nth _ _ _ => Hi.
      have <- := cast_ordK (size_to_word t) i; rewrite mem_cast.
      apply/bigcupP; set f := (X in map X _); exists (f S); last by rewrite mem_cast.
      rewrite inE; apply map_f; rewrite /S {f}.
      have <- := nth_take set0 Hicol (tabextr_rec (shape t)).
      apply mem_nth; rewrite size_take size_tabextr_rec.
      case (ltnP k (head 0 (shape t))) => _; first by [].
      case (ltnP icol (head 0 (shape t))) => H; first by [].
      move: Hi; rewrite /S nth_default; last by rewrite size_tabextr_rec.
      by rewrite in_set0.
    * left; rewrite imset_comp mem_cast -Hinj.
      rewrite !(mem_imset_inj _ _ (@rinjP _ _)) inE.
      move: Hj => /imsetP [] i1 Hin1 Hi1.
      move: Hin1; rewrite /cover => /bigcupP [] sj.
      rewrite /tabextr inE /= => /mapP [] s.
      rewrite -map_take => /mapP [] i2; rewrite take_enumI => Hi2 -> -> {s sj}.
      have <- := cast_ordKV (size_to_word (t0 :: t)) i1.
      rewrite mem_cast -Hi1 {i1 Hi1} imset_comp -imsetU1 mem_cast -Hinj in_setU1.
      by rewrite rinj_in_linjF orbF => /eqP/rinjP ->.
  + rewrite inE => /orP [].
    * move/imsetP => [] i1; rewrite inE => Hi1 Hi; rewrite /= in Hi.
      have <- := cast_ordK (size_to_word (t0 :: t)) i; rewrite mem_cast /cover.
      rewrite /tabextr /= -map_take -!map_comp /=; set f := (X in map X _).
      apply/bigcupP; exists (f i1); rewrite /f {f}.
      - rewrite inE; rewrite mem_map; first by rewrite take_enumI.
        apply inj_comp; first by apply imset_inj; apply cast_ord_inj.
        admit.
      - rewrite /= mem_cast Hi imset_comp -imsetU1 mem_cast in_setU1.
        by rewrite rinj_in_linjF orbF.
    * move/imsetP => [] i1; rewrite /cover => /bigcupP [] s.
      rewrite inE /tabextr /= => /mapP [] st Hst -> {s} /imsetP [] i2 Hi2 -> -> {i1 i}.
      rewrite /= /sym_cast; set i := (X in X \in _).
      have <- := cast_ordK (size_to_word (t0 :: t)) i; rewrite mem_cast /cover.
      apply/bigcupP.
      admit.
Qed.

Lemma scover_tabextr k t :
  scover [set s | s \in (tabextr t k)] = \sum_(l <- (shape t)) minn l k.
Proof.
  elim: t => [//= | t0 t IHt] /=.
  - set s := (X in cover X); have -> : s = set0 by rewrite /s -setP => i; rewrite inE.
    rewrite /cover /= big_pred0; last by move=> i /=; rewrite inE.
    by rewrite cards0 big_nil.
  - rewrite big_cons -IHt {IHt} /=.
    have := scover_tabextr_rec k t t0; rewrite /tabextr /=.
    set s := (X in X = _); set sl := (X in _ = X :|: _); set sr := (X in _ = _ :|: X).
    move => Hcov; have := erefl #|s|; rewrite {2} Hcov {Hcov} cardsU.
    have /disjoint_setI0 -> : [disjoint sl & sr].
      rewrite /sl /sr {sl sr s} !imset_comp /disjoint /=.
      apply/pred0P => l /=; apply (introF idP) => /andP [].
      (* TODO : simplify or lemmize *)
      move=> /imsetP [] l1 Hl1 {l} -> /imsetP [] l Hl /cast_ord_inj H; subst l1.
      move: Hl Hl1 => /imsetP [] l1 Hl1 {l} -> /imsetP [] l Hl H; subst l1.
      move: Hl Hl1 => /imsetP [] l1 Hl1 {l} -> /imsetP [] l Hl /eqP.
      by rewrite eq_sym lrinjF.
    rewrite cards0 subn0 /s {s} card_imset; last by apply cast_ord_inj.
    move ->. have -> : #|sl| = minn (size t0) k.
      rewrite /sl imset_comp card_imset; last by apply cast_ord_inj.
      rewrite card_imset; last by apply rinjP.
      by rewrite sizeIk.
    apply/eqP; rewrite eqn_add2l {sl} /sr.
    move: (map _ (take k _)) => S.
    rewrite 2!imset_comp card_imset; last by apply cast_ord_inj.
    rewrite card_imset; last by apply linjP.
    by rewrite card_imset; last by apply cast_ord_inj.
Qed.

Theorem green_tab k t :
  is_tableau t -> green (to_word t) k = \sum_(l <- (shape t)) minn l k.
Proof.
  move=> Ht; apply/eqP; rewrite eqn_leq (green_inf_tab _ Ht) /=.
  rewrite /greent /= -scover_tabextr.
  apply leq_bigmax_cond; by apply ksupp_tabextr.
Qed.

End GreenSeq.

