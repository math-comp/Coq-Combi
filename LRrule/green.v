Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm tuple path bigop.
Require Import subseq partition ordtype schensted congr plactic ordcast.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bool.


Section TrivISeq.

Variable T : finType.

Lemma card_seq (s : seq T) : #|[set i in s]| <= size s.
Proof.
  elim: s => [//= | s0 s IHs]; set t := [set i | i \in _].
  - suff -> : t = set0 by rewrite cards0.
    rewrite -setP => i /=; by rewrite inE.
  - rewrite /t set_cons cardsU1 /= -add1n.
    by apply leq_add; first by case: (s0 \notin [set i in s]).
Qed.

Definition trivIseq (u : seq {set T}) : Prop :=
  forall i j, i < j < size u -> [disjoint (nth set0 u i) & (nth set0 u j)].

Lemma trivIseq_consK u0 u : trivIseq (u0 :: u) -> trivIseq u.
Proof. rewrite /trivIseq => H i j Hij; apply (H i.+1 j.+1); by rewrite /= !ltnS. Qed.

Lemma trivIsubseq u v :
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

Lemma trivIs u : trivIseq u -> trivIset [set i | i \in u].
Proof.
  rewrite /trivIseq => H; apply/trivIsetP => A B.
  rewrite !inE => HAin HBin.
  have:= HAin; have:= HBin; rewrite -!index_mem.
  rewrite -{2 3}(nth_index set0 HAin) -{2 3}(nth_index set0 HBin).
  set iA := index A u; set iB := index B u.
  wlog leqAB: iA iB / iA <= iB.
    move=> Hwlog HA HB; case (leqP iA iB) => HAB.
      by apply (Hwlog iA iB HAB).
      rewrite eq_sym disjoint_sym; by apply (Hwlog iB iA (ltnW HAB)).
  move=> HiA HiB HAB.
  apply H; rewrite HiA andbT ltn_neqAle leqAB andbT.
  by move: HAB; apply contra => /eqP ->.
Qed.

End TrivISeq.

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

Variable comp : rel Alph.
Hypothesis Hcomp : transitive comp.

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

Definition is_seq := [fun r => (sorted comp r)].

Lemma is_seq_extract_cond s P :
  is_seq (extract s) -> is_seq (extract (s :&: P)).
Proof.
  apply subseq_sorted; first by move=> a b c /= H1 H2; apply (Hcomp H1 H2).
  apply extsubsI; rewrite -{2}[s]setIT; apply setIS; by apply subsetT.
Qed.

Definition ksupp k (P : {set {set 'I_N}}) :=
  [&& #|P| <= k, trivIset P & [forall (s | s \in P), is_seq (extract s)]].

Lemma ksupp0 k : ksupp k set0.
Proof.
  rewrite /ksupp cards0 leq0n /=; apply/andP; split.
  + apply/trivIsetP => A B; by rewrite in_set0.
  + apply/forallP => A; by rewrite in_set0.
Qed.

Definition scover := [fun P : {set {set 'I_N}} => #|cover P|].
Definition green_rel_t k := \max_(P | ksupp k P) scover P.

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

Lemma green_rel_t_inf k : green_rel_t k >= minn N k.
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
  rewrite /green_rel_t; by apply leq_bigmax_cond.
Qed.

Lemma green_rel_t_sup k : green_rel_t k <= N.
Proof.
  rewrite /green_rel_t /=; apply/bigmax_leqP => P _.
  move: (cover P) => cover {P}; rewrite -{5}[N]card_ord.
  by apply max_card.
Qed.

End GreenDef.

Arguments scover [N].

Lemma green_rel_t_cast (Alph : ordType) R M N (Heq : M = N) k (V : M.-tuple Alph) :
  green_rel_t R (tcast Heq V) k = green_rel_t R V k.
Proof. by subst M. Qed.

Section GreenCat.

Variable Alph : ordType.

Variable comp : rel Alph.
Hypothesis Hcomp : transitive comp.

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

Let lsplit := [fun s : {set 'I_(M+N)} => linj @^-1: s].
Let rsplit := [fun s : {set 'I_(M+N)} => rinj @^-1: s].

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

Lemma disjoint_inj (sM : {set 'I_M}) (sN : {set 'I_N}) :
  [disjoint linj @: sM & rinj @: sN].
Proof.
  rewrite /disjoint; apply/pred0P=> i /=; apply negbTE; apply (introN idP) => /andP [].
  move/imsetP=> [] [] l HlM Hl -> {i} /imsetP [] [] r HrN Hr /eqP.
  by rewrite lrinjF.
Qed.

Lemma splitsetK (s : {set 'I_(M+N)}) : s = (linj @: lsplit s) :|: (rinj @: rsplit s).
Proof.
  rewrite /=; apply/setP/subset_eqP/andP; split; apply/subsetP=> i Hi.
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
  rewrite /cover /=.
  apply/setP/subset_eqP/andP; split; apply/subsetP=> i.
  * move/bigcupP=> [] part Hpart Hi.
    have:= splitK i; case: fintype.splitP => j Hj; rewrite /unsplit => Hinj.
    - rewrite -Hinj; apply/setUP; left.
      apply mem_imset; apply/bigcupP; exists (lsplit part); first by apply mem_imset.
      by rewrite /= inE Hinj.
    - rewrite -Hinj; apply/setUP; right.
      apply mem_imset; apply/bigcupP; exists (rsplit part); first by apply mem_imset.
      by rewrite /= inE Hinj.
  * move/setUP => [] /imsetP [] j /bigcupP [] part /imsetP [] prt Hprt Hcut Hj ->;
      apply/bigcupP; exists prt => //=; move: Hj; by rewrite Hcut inE.
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
    by rewrite inE inE /= -{7}[M]addn0 ltn_add2l ltn0 andbF.
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
    by rewrite inE inE /= (nth_enum_ord _ Hi) leqNgt Hi /= andbF.
  rewrite mask_false cat0s -[in RHS]map_comp; congr (mask _ W).
  apply eq_map => i /=; rewrite inE in_setI.
  suff -> : rinj i \in [set i0 : 'I_(M+N) | M <= i0] by rewrite andbT.
  rewrite inE /=; by apply leq_addr.
Qed.

Lemma green_rel_t_cat k :
  green_rel_t comp [tuple of V ++ W] k <= green_rel_t comp V k + green_rel_t comp W k.
Proof.
  rewrite /green_rel_t; set tc := [tuple of V ++ W].
  have H : 0 < #|ksupp comp tc k| by apply/card_gt0P; exists set0; apply ksupp0.
  case: (@eq_bigmax_cond _ (ksupp comp tc k) scover H) => ks Hks ->.
  pose PV := lsplit @: ks; pose PW := rsplit @: ks.
  move: Hks => /and3P [] Hcard Htriv /forallP Hcol.
  have HV : ksupp comp V k PV.
    rewrite /ksupp; apply/and3P; split; first by apply (leq_trans (leq_imset_card _ _) Hcard).
    - by apply preimset_trivIset; first by apply linjP.
    - apply/forallP=> stmp; apply/implyP => /imsetP [] s Hs -> {stmp}.
      rewrite extlsplit; apply is_seq_extract_cond; have:= Hcol s; by rewrite Hs.
  have HleqV := (@leq_bigmax_cond _ _ scover _ HV).
  have HW : ksupp comp W k PW.
    rewrite /ksupp; apply/and3P; split; first by apply (leq_trans (leq_imset_card _ _) Hcard).
    - by apply preimset_trivIset; first by apply rinjP.
    - apply/forallP=> stmp; apply/implyP => /imsetP [] s Hs -> {stmp}.
      rewrite extrsplit; apply is_seq_extract_cond; have:= Hcol s; by rewrite Hs.
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

Variable comp : rel Alph.
Hypothesis Hcomp : transitive comp.

Local Notation greent := (green_rel_t comp).

Definition green_rel u := [fun k => greent (in_tuple u) k].

Lemma green_rel_cat k v w : green_rel (v ++ w) k <= green_rel v k + green_rel w k.
Proof.
  rewrite /disjoint /=.
  suff -> : greent (in_tuple (v ++ w)) k = greent [tuple of (in_tuple v) ++ (in_tuple w)] k
    by apply green_rel_t_cat.
  have Hsz : size (v ++ w) = (size v + size w) by rewrite size_cat.
  rewrite -(green_rel_t_cast _ Hsz); congr (greent _ k).
  apply eq_from_tnth => i; by rewrite tcastE !(tnth_nth (inhabitant Alph)).
Qed.

Let negcomp := (fun a b => ~~(comp a b)).
Hypothesis Hnegcomp : transitive negcomp.

Lemma green_rel_seq r k : is_seq negcomp r -> green_rel r k = minn (size r) k.
Proof.
  move=> Hrow /=.
  apply/eqP; rewrite eqn_leq; apply/andP; split; last by apply green_rel_t_inf.
  rewrite leq_min green_rel_t_sup /=; apply/bigmax_leqP => s.
  rewrite /ksupp /trivIset => /and3P [] Hcard /eqP /= <- /forallP Hsort.
  suff {Hcard} H B : B \in s -> #|B| <= 1.
    apply (@leq_trans (\sum_(B in s) 1)); last by rewrite sum1_card.
    by apply leq_sum.
  rewrite -(size_extract (in_tuple r)) /=.
  move=> HB; have {Hsort} := Hsort B; rewrite HB {HB s} /=.
  set s := (extractpred _ _) => Hsort.
  have : sorted negcomp s.
    move: Hrow; apply (subseq_sorted Hnegcomp); last by apply extsubsm.
  case H : s Hsort => [//= | s0 [//= | s1 tls]] /= /andP [] Hgt _ /andP [].
  by rewrite /negcomp Hgt.
Qed.

End GreenSeq.

Section GreenTab.

Variable Alph : ordType.
Implicit Type u v w : seq Alph.
Implicit Type t : seq (seq Alph).

Let sym_cast m n (i : 'I_(m + n)) : 'I_(n + m) := cast_ord (addnC m n) i.

Fixpoint shextr sh : seq {set 'I_(sumn sh)} :=
  if sh is s0 :: sh then
    [seq (sym_cast (@rshift (sumn sh) s0 i)) |:
         (((@sym_cast _ _) \o (@lshift (sumn sh) s0)) @: (nth set0 (shextr sh) i))
    | i <- enum 'I_s0]
  else [::].

Let cast_set_tab t :=
  [fun s : {set 'I_(sumn (shape t))} => (cast_ord (size_to_word t)) @: s].

Definition tabextr t := map (cast_set_tab t) (shextr (shape t)).

Definition tabextrk t := [fun k => take k (tabextr t)].

Lemma size_shextr_cons s0 sh : size (shextr (s0 :: sh)) = s0.
Proof. by rewrite /= size_map size_enum_ord. Qed.

Lemma size_shextr sh : size (shextr sh) = head 0 sh.
Proof. by case sh => [//= | s0 s]; apply size_shextr_cons. Qed.

Lemma size_tabextr t : size (tabextr t) = size (head [::] t).
Proof. rewrite /tabextr /= size_map size_shextr. by case t. Qed.


Lemma trivIseq_shextr sh : trivIseq (shextr sh).
Proof.
  elim: sh => [/= | s0 sh /= IHsh]; first by rewrite /trivIseq => i j /= /andP [].
  rewrite /trivIseq size_shextr_cons => i j /andP [] Hij Hj.
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
      case: (ltnP j (size (shextr sh))) => Hj1;
        last by move: Hlj; rewrite (nth_default _ Hj1) in_set0.
      have : i < j < size (shextr sh) by rewrite Hij Hj1.
      move/(IHsh i j); rewrite /disjoint => /pred0P => H.
      have:= H l; by rewrite /= Hli Hlj.
Qed.

Lemma trivIset_tabextrk k t : trivIset [set s | s \in (tabextrk t k)].
Proof.
  apply trivIs; rewrite /tabextrk /tabextr /= -map_take.
  apply trivIseq_map; first by apply cast_ord_inj.
  apply (trivIsubseq (v := (shextr (shape t)))).
  + rewrite -{2}[shextr (shape t)](cat_take_drop k).
    by apply prefix_subseq.
  + by apply trivIseq_shextr.
Qed.


Section Induction.

Variable (t0 : seq Alph) (t : seq (seq Alph)).

Lemma size_to_word_cons : size (to_word t) + size t0 = size (to_word (t0 :: t)).
Proof. by rewrite -!size_to_word /size_tab /= addnC. Qed.

Let cast_cons := cast_ord size_to_word_cons.
Let rinj_rec := (cast_cons \o (@rshift (size (to_word t)) (size t0))).
Let linj_rec := (cast_cons \o (@lshift (size (to_word t)) (size t0))).

Lemma linj_recP : injective linj_rec.
Proof.
  move=> [] i Hi [] j Hj /eqP H; apply /eqP; move: H; by rewrite !/eq_op /=.
Qed.
Lemma rinj_recP : injective rinj_rec.
Proof.
  move=> [] i Hi [] j Hj /eqP H; apply /eqP; move: H; by rewrite !/eq_op /= eqn_add2l.
Qed.

Lemma lrinj_recF i j : (linj_rec i == rinj_rec j) = false.
Proof.
  apply (introF idP); case: i j => [] i Hi [] j Hj.
  rewrite /eq_op /= => /eqP H.
  move: Hi; by rewrite H ltnNge leq_addr.
Qed.

Lemma rinj_in_linj_recF i (s : {set 'I_(size (to_word t))}) :
  rinj_rec i \in [set linj_rec x | x in s] = false.
Proof.
  apply negbTE; apply (introN idP) => /imsetP [] j _ /eqP; by rewrite eq_sym lrinj_recF.
Qed.

Lemma linj_in_rinj_recF i (s : {set 'I_(size t0)}) :
  linj_rec i \in [set rinj_rec x | x in s] = false.
Proof. apply negbTE; apply (introN idP) => /imsetP [] j _ /eqP; by rewrite lrinj_recF. Qed.

Lemma disjoint_inj_rec (st : {set 'I_(size (to_word t))}) (s0 : {set 'I_(size t0)}) :
  [disjoint linj_rec @: st & rinj_rec @: s0].
Proof.
  rewrite /linj_rec /rinj_rec !imset_comp.
  rewrite -setI_eq0 -imsetI; last by move=> i j _ _ /= /cast_ord_inj.
  have := (disjoint_inj st s0); rewrite -setI_eq0 => /eqP ->.
  by rewrite imset0.
Qed.

Let lsplit_rec := [fun s : {set 'I_(size (to_word (t0 :: t)))} => linj_rec @^-1: s].
Let rsplit_rec := [fun s : {set 'I_(size (to_word (t0 :: t)))} => rinj_rec @^-1: s].

(* I didn't manage to use this lemma getting it pass through \bigcup *)
Lemma split_recabK (s : {set 'I_(size (to_word (t0 :: t)))}) :
  s = (linj_rec @: lsplit_rec s) :|: (rinj_rec @: rsplit_rec s).
Proof.
  rewrite /lsplit_rec /rsplit_rec /linj_rec /rinj_rec.
  apply/setP/subset_eqP/andP; split; apply/subsetP=> i Hi.
  + apply/setUP; rewrite -(cast_ordKV size_to_word_cons i) !imset_comp !mem_cast.
    have:= splitK (cast_ord (esym size_to_word_cons) i).
    case: fintype.splitP => j Hj; rewrite /unsplit => Hinj.
    * left; apply/imsetP; exists j => /=; last by rewrite Hinj.
      by rewrite inE /= Hinj /cast_cons cast_ordKV.
    * right; apply/imsetP; exists j => /=; last by rewrite Hinj.
      by rewrite inE /= Hinj /cast_cons cast_ordKV.
  + move: Hi; rewrite inE => /orP []; move/imsetP => [] j; by rewrite inE => H ->.
Qed.

Lemma split_rec_cover (p : {set {set 'I_(size (to_word (t0 :: t)))}}) :
  cover p = linj_rec @: (cover (lsplit_rec @: p)) :|: rinj_rec @: (cover (rsplit_rec @: p)).
Proof.
  rewrite /lsplit_rec /rsplit_rec /linj_rec /rinj_rec /cover.
  apply/setP/subset_eqP/andP; split; apply/subsetP=> i.
  * move/bigcupP=> [] part Hpart Hi.
    rewrite -(cast_ordKV size_to_word_cons i).
    have:= splitK (cast_ord (esym size_to_word_cons) i).
    case: fintype.splitP => j Hj; rewrite /unsplit => Hinj.
    - rewrite -Hinj; apply/setUP; left.
      rewrite /cast_cons imset_comp mem_cast; apply mem_imset; apply/bigcupP.
      exists (lsplit_rec part); first by apply mem_imset.
      by rewrite inE /linj_rec /= Hinj /cast_cons cast_ordKV.
    - rewrite -Hinj; apply/setUP; right.
      rewrite /cast_cons imset_comp mem_cast; apply mem_imset; apply/bigcupP.
      exists (rsplit_rec part); first by apply mem_imset.
      by rewrite inE /rinj_rec /= Hinj /cast_cons cast_ordKV.
  * move/setUP => [] /imsetP [] j /bigcupP [] part /imsetP [] prt Hprt Hcut Hj ->;
      apply/bigcupP; exists prt => //=; move: Hj; by rewrite Hcut inE.
Qed.

Lemma lcast_com :
  (cast_ord (size_to_word (t0 :: t)))
    \o (@sym_cast _ _) \o (@lshift (sumn (shape t)) (size t0))
  =1  linj_rec \o (cast_ord (size_to_word t)).
Proof. move=> i; apply /eqP; by rewrite /rinj_rec /= /eq_op /=. Qed.

Lemma rcast_com :
 (cast_ord (size_to_word (t0 :: t)))
   \o (@sym_cast _ _) \o (@rshift (sumn (shape t)) (size t0))  =1  rinj_rec.
Proof. move=> i; apply /eqP; rewrite /rinj_rec /= /eq_op /=; by rewrite -size_to_word. Qed.


Lemma tabextr_cons:
  tabextr (t0 :: t) =
    [seq rinj_rec i |: (linj_rec @: (nth set0 (tabextr t) i)) | i <- enum 'I_(size t0)].
Proof.
  rewrite /tabextr /cast_cons /=.
  apply (@eq_from_nth _ set0); first by rewrite !size_map.
  move=> i; rewrite 2!size_map => Hienum; have:= Hienum; rewrite size_enum_ord => Hi.
  rewrite -map_comp (nth_map (Ordinal Hi)) //= !(nth_enum_ord _ Hi).
  rewrite (nth_map (Ordinal Hi)) //= !(nth_enum_ord _ Hi).
  rewrite imsetU1 -!imset_comp.
  case (ltnP i (size (shextr (shape t)))) => Hish.
  + rewrite (nth_map set0 _ _ Hish).
    have:= (rcast_com (nth (Ordinal Hi) (enum 'I_(size t0)) i)) => /= ->.
    by rewrite -!imset_comp (eq_imset _ lcast_com).
  + set empty := (nth set0 (map _ _)) i.
    have {empty} -> : empty = set0 by rewrite /empty nth_default //= size_map.
    set ii := nth _ _ i.
    have {ii} -> : ii = Ordinal Hi by rewrite /ii; apply val_inj; rewrite /= nth_enum_ord.
    by rewrite nth_default //= !imset0 -(rcast_com (Ordinal Hi)).
Qed.

Lemma size_tabextr_cons: size (tabextr (t0 :: t)) = size t0.
Proof. by rewrite tabextr_cons /= size_map size_enum_ord. Qed.

Lemma enumIsize_to_word :
  enum 'I_(size (to_word (t0 :: t))) =
  map linj_rec (enum 'I_(size (to_word t)))  ++  map rinj_rec (enum 'I_(size t0)).
Proof.
  rewrite /rinj_rec /linj_rec (enum_cast_ord size_to_word_cons).
  rewrite !map_comp /cast_cons -map_cat; congr (map (cast_ord size_to_word_cons) _).
  by rewrite map_id enumIMN.
Qed.

Lemma extract_rec i :
  i < size t0 ->
  extract (in_tuple (to_word (t0 :: t))) (nth set0 (tabextr (t0 :: t)) i) =
  rcons (extract (in_tuple (to_word t)) (nth set0 (tabextr t) i))
        (nth (inhabitant Alph) t0 i).
Proof.
  move => Hi; rewrite /= !extractE tabextr_cons enumIsize_to_word /=.
  rewrite (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
  rewrite nth_enum_ord //= {13}to_word_cons.
  rewrite nth_ord_ltn map_cat mask_cat; last by rewrite 2!size_map size_enum_ord.
  rewrite -map_comp.
  set f1 := (X in map X _); set fr := (X in rcons (mask (map X _) _)).
  have {f1} /eq_map -> : f1 =1 fr.
    rewrite /f1 => j /=; rewrite inE in_set1 lrinj_recF /=.
    by rewrite (mem_imset_inj _ _ linj_recP).
  rewrite -map_comp; set f2 := (X in _ ++ mask (map X _) _).
  have {f2} /eq_map -> : f2 =1 mem ([set (Ordinal Hi)]).
    move=> j; rewrite /f2 /= !inE.
    set b := (X in _ || X); have {b} -> : b = false.
      rewrite /b; apply/imsetP => [] [] k _ /eqP; by rewrite eq_sym lrinj_recF.
    rewrite orbF.
    by apply/(sameP idP); apply(iffP idP) => [/eqP -> //=|] /eqP/rinj_recP ->.
  have := extract1 (in_tuple t0) (Ordinal Hi); rewrite /extract /= extractE /= => ->.
  by rewrite cats1 (tnth_nth (inhabitant Alph)) /=.
Qed.

Lemma lsplit_rec_tab k :
  head 0 (shape t) <= size t0 ->
  cover [set lsplit_rec x | x in [set s in tabextrk (t0 :: t) k]] =
  cover [set s in tabextrk t k].
Proof.
  move => Hsize; rewrite cover_imset /tabextrk /= tabextr_cons /cover /preimset.
  apply/setP/subset_eqP/andP; split; apply/subsetP => i.
  - move/bigcupP => [] S0; rewrite !inE.
    move/(mem_takeP set0) => [] pos [].
    rewrite size_map size_enum_ord leq_min => /andP [] Hpos Hpos0 ->.
    rewrite (nth_map (Ordinal Hpos0)); last by rewrite size_enum_ord.
    rewrite !inE lrinj_recF /= (mem_imset_inj _ _ linj_recP) nth_ord_ltn => Hi.
    apply/bigcupP; exists (nth set0 (tabextr t) (Ordinal Hpos0)); last exact Hi.
    rewrite inE; apply/(mem_takeP set0).
    exists pos; split; last by [].
    rewrite leq_min Hpos /=.
    case: (ltnP pos (size (tabextr t))) => //= H.
    move: Hi; by rewrite (nth_default _ H) in_set0.
  - move/bigcupP => [] S0; rewrite !inE => /(mem_takeP set0) [] pos [].
    rewrite leq_min => [] /andP [] Hpos Hpossz -> Hi.
    have Hpos0 : pos < size t0.
      apply (leq_trans Hpossz). rewrite size_tabextr.
      move: Hsize; rewrite /shape; by case t.
    apply/bigcupP.
    exists (rinj_rec (Ordinal Hpos0)
                  |: [set linj_rec x | x in nth set0 (tabextr t) (Ordinal Hpos0)]).
    * rewrite inE; apply/(mem_takeP set0).
      exists pos; rewrite size_map size_enum_ord leq_min; split; first by rewrite Hpos.
      rewrite (nth_map (Ordinal Hpos0)); last by rewrite size_enum_ord.
      by rewrite nth_ord_ltn.
    * rewrite !inE lrinj_recF /=; apply/imsetP; by exists i.
Qed.

Lemma rsplit_rec_tab k :
  cover [set rsplit_rec x | x in [set s in (tabextrk (t0 :: t)) k]] =
  [set i : 'I_(size t0) | i < k].
Proof.
  rewrite /tabextrk /= tabextr_cons.
  apply/setP/subset_eqP/andP; split; apply/subsetP => i.
  - rewrite in_set /= /preimset.
    rewrite /cover => /bigcupP [] sj /imsetP [] stk.
    rewrite inE => /(mem_takeP set0) [] j.
    rewrite size_map size_enum_ord leq_min => [] [] /andP [] Hjk Hjt0.
    rewrite (nth_map (Ordinal Hjt0)); last by rewrite size_enum_ord.
    rewrite (nth_enum_ord _ Hjt0).
    have -> : nth (Ordinal Hjt0) (enum 'I_(size t0)) j = (Ordinal Hjt0).
      by apply /eqP; rewrite /eq_op /= nth_enum_ord.
    move=> -> -> {sj stk}; rewrite inE in_setU1 rinj_in_linj_recF orbF.
    by move=> /eqP/rinj_recP ->.
  - rewrite inE /cover /preimset => Hi.
    apply/bigcupP; exists [set i]; last by rewrite in_set1.
    apply/imsetP; exists ((rinj_rec i) |: [set linj_rec x | x in nth set0 (tabextr t) i]).
    + rewrite inE; apply/(mem_takeP set0).
      exists i; rewrite size_map size_enum_ord leq_min Hi; split; first by apply ltn_ord.
      rewrite (nth_map i); last by rewrite size_enum_ord; apply ltn_ord.
      rewrite nth_enum_ord; last by apply ltn_ord.
      by rewrite nth_ord_enum.
    +  apply/setP/subset_eqP/andP; split; apply/subsetP => j; rewrite in_set1.
      * move/eqP=> -> {j}; by rewrite !inE eq_refl.
      * by rewrite !inE rinj_in_linj_recF orbF => /eqP/rinj_recP ->.
Qed.

Lemma cover_tabextr_rec k :
  head 0 (shape t) <= size t0 ->
  cover [set s in (tabextrk (t0 :: t) k)] =
  rinj_rec @: [set s : 'I_(size t0) | s < k]
           :|:  linj_rec @: cover [set s in (tabextrk t k)].
Proof.
  move => Hsize; by rewrite split_rec_cover setUC rsplit_rec_tab (lsplit_rec_tab _ Hsize).
Qed.

End Induction.


Lemma scover_tabextr k t :
  is_part (shape t) ->
  scover [set s | s \in (tabextrk t k)] = \sum_(l <- (shape t)) minn l k.
Proof.
  elim: t => [//= | t0 t IHt] /=.
  - set s := (X in cover X); have -> : s = set0 by rewrite /s -setP => i; rewrite inE.
    rewrite /cover /= big_pred0; last by move=> i /=; rewrite inE.
    by rewrite cards0 big_nil.
  - move/andP => [] Hhead /IHt {IHt} IHt.
    have {Hhead} Hhead : head 0 (shape t) <= size t0.
      apply (@leq_trans (head 1 (shape t))); last exact Hhead.
      by case t.
    rewrite big_cons -IHt {IHt} /=.
    have := cover_tabextr_rec k Hhead; rewrite /tabextr /=.
    set s := (X in X = _); set sl := (X in _ = X :|: _); set sr := (X in _ = _ :|: X).
    move => Hcov; have := erefl #|s|; rewrite {2} Hcov {Hcov} cardsU.
    have /disjoint_setI0 -> : [disjoint sl & sr].
      rewrite /sl /sr {sl sr s} !imset_comp /disjoint /=.
      apply/pred0P => l /=; apply (introF idP) => /andP [].
      move=> /imsetP [] l1 Hl1 {l} -> /imsetP [] l Hl /cast_ord_inj H; subst l1.
      move: Hl Hl1 => /imsetP [] l1 Hl1 {l} -> /imsetP [] l Hl /eqP.
      by rewrite lrinjF.
    rewrite cards0 subn0 /s {s} => ->.
    have -> : #|sl| = minn (size t0) k.
      rewrite /sl imset_comp card_imset; last by apply cast_ord_inj.
      rewrite card_imset; last by apply rinjP.
      by rewrite sizeIk.
    apply/eqP; rewrite eqn_add2l {sl} /sr.
    rewrite imset_comp card_imset; last by apply cast_ord_inj.
    rewrite card_imset; last by apply linjP.
    by rewrite -map_take.
Qed.

Lemma sorted_gtnX_tabextr t i :
  is_tableau t -> i < size (tabextr t) ->
  sorted (gtnX Alph)
         (extract (in_tuple (to_word t)) (nth set0 (tabextr t) i)).
Proof.
  elim: t => [//= | t0 t IHt].
  rewrite [X in X -> _]/=; move=> /and4P [] _ _ /dominateP [] Hsz Hdom Htab.
  rewrite size_tabextr_cons => Hi; rewrite (extract_rec _ Hi).
  case (ltnP i (size (head [::] t))) => Hit.
  + have:= Hit; rewrite -size_tabextr; move/(IHt Htab) => {IHt}.
    move Hrec : (extract _ _) => ext.
    case: ext Hrec => [//= | a0 ext] Hext.
    rewrite rcons_cons /= rcons_path => -> /=.
    suff {Hdom} -> : last a0 ext = nth (inhabitant Alph) (head [::] t) i by apply Hdom.
    rewrite -[last a0 ext]/(last (inhabitant Alph) (a0 :: ext)) -Hext {a0 ext Hext}.
    case: t Hsz Htab Hit => [//= | t1 t] Hsz Htab Hit.
    by rewrite (extract_rec _ Hit) last_rcons.
  + rewrite nth_default; last by rewrite size_tabextr.
    by rewrite extract0.
Qed.

Lemma ksupp_gtnX_tabextr k t :
  is_tableau t -> ksupp (gtnX Alph) (in_tuple (to_word t)) k [set s | s \in (tabextrk t k)].
Proof.
  move=> Htab; rewrite /ksupp /tabextrk; apply/and3P; split.
  + apply (leq_trans (card_seq (tabextrk t k))).
    rewrite /tabextrk /= size_take; by apply geq_minl.
  + apply trivIset_tabextrk.
  + apply/forallP => s; apply/implyP.
    rewrite /= inE => /mem_take Hin.
    rewrite -(nth_index set0 Hin).
    move: Hin; rewrite -index_mem; set i := index _ _ => Hi.
    by apply (sorted_gtnX_tabextr Htab).
Qed.

Definition greenRow := green_rel (leqX Alph).
Definition greenCol := green_rel (gtnX Alph).

Lemma greenCol_inf_tab k t :
  is_tableau t -> greenCol (to_word t) k <= \sum_(l <- (shape t)) minn l k.
Proof.
  elim: t => [_ | t0 t IHt] /=;
    first by rewrite /to_word; apply (@leq_trans 0); first by apply green_rel_t_sup.
  move=> /and4P [] _ Hrow _ /IHt => {IHt} Ht; rewrite to_word_cons.
  apply (@leq_trans (greenCol (in_tuple (to_word t)) k + greenCol (in_tuple t0) k)).
  - apply green_rel_cat; by move=> a b c /= H1 H2; apply (ltnX_trans H2 H1).
  - rewrite big_cons addnC; apply leq_add; last exact Ht.
    have:= (@green_rel_seq _ (gtnX Alph) _ t0 k).
    rewrite /green_rel /= => -> //=.
    * move=> a b c /=; rewrite -!leqXNgtnX; by apply leqX_trans.
    * move: Hrow; rewrite /sorted; case: t0 => [//=| l t0].
      have Req : leqX_op =2 (fun a b : Alph => ~~ (b <A a))
        by move=> i j /=; apply leqXNgtnX.
      by rewrite (eq_path Req).
Qed.

Theorem greenCol_tab_min k t :
  is_tableau t -> greenCol (to_word t) k = \sum_(l <- (shape t)) minn l k.
Proof.
  move=> Ht; apply/eqP; rewrite eqn_leq (greenCol_inf_tab _ Ht) /=.
  rewrite /greenCol /green_rel_t /= -(scover_tabextr _ (is_part_sht Ht)).
  apply leq_bigmax_cond; by apply ksupp_gtnX_tabextr.
Qed.

Theorem greenCol_tab k t :
  is_tableau t -> greenCol (to_word t) k = part_sum (conj_part (shape t)) k.
Proof. move/greenCol_tab_min ->; by apply sum_conj. Qed.

Theorem greenCol_tab_eq_shape t1 t2 :
  is_tableau t1 -> is_tableau t2 ->
  (forall k, greenCol (to_word t1) k = greenCol (to_word t2) k) -> (shape t1 = shape t2).
Proof.
  move=> Htab1 Htab2 Heq.
  have Hsh1 := is_part_sht Htab1; have Hsh2 := is_part_sht Htab2.
  suff : conj_part (shape t1) = conj_part (shape t2).
    move=> H; rewrite -(conj_partK Hsh1) -(conj_partK Hsh2).
    by rewrite H (conj_partK Hsh2).
  apply (part_sum_inj (is_part_conj Hsh1) (is_part_conj Hsh2)).
  move=> k. rewrite -(greenCol_tab k Htab1) -(greenCol_tab k Htab2).
  by apply Heq.
Qed.

End GreenTab.

