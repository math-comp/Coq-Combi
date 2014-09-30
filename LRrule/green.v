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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm tuple path bigop.
Require Import subseq partition ordtype schensted congr plactic ordcast.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bool.

Lemma unlift_seqE n (l : seq 'I_n.+1) :
  sorted (fun i j : 'I_n.+1 => i < j) (ord0 :: l) ->
  exists l1 : seq 'I_n,
    sorted (fun i j : 'I_n => i < j) l1 /\ l = map (lift ord0) l1.
Proof.
  elim: l => [_ | l0 l IHl] /=.
  + exists [::] => /=; by split.
  + move=> /andP [] H0 Hl.
    have: sorted (fun i j : 'I_n.+1 => i < j) (ord0 :: l).
      rewrite /sorted; move: l Hl {IHl}; case => [//= | l1 l] /= /andP [] Hl1 ->.
      by rewrite (ltn_trans H0 Hl1).
    move/IHl => {IHl} [] r [] Hr Heq; rewrite Heq.
    case: l0 H0 Hl => [[//= | r0 /= Hr0 _]] Hl.
    have := Hr0; rewrite ltnS => Hr0'.
    exists ((Ordinal Hr0') :: r); split.
    + move: Hr; rewrite /sorted; case: r Heq => [//= | r1 r] /= Heq.
      case: r1 Heq => r1 Hr1 /= Heq.
      move: Hl; rewrite Heq /= => /andP [].
      by rewrite /fintype.bump leq0n /= add1n ltnS => -> /=.
    + rewrite /=; congr (_ :: _); by apply val_inj.
Qed.

Lemma ord0_in_map_liftF n (l : seq 'I_n) :
  ord0 \in [seq lift ord0 i | i <- l] = false.
Proof.
  elim: l => [| l0 l] /=; first by rewrite in_nil.
  rewrite in_cons; have:= neq_lift ord0 l0; by rewrite eq_sym => /negbTE -> /=.
Qed.

Lemma mem_enum_seqE n (l : seq 'I_n) :
  sorted (fun i j : 'I_n => val i < val j) l -> [seq i <- enum 'I_n | i \in l] = l.
Proof.
  elim: n l => [|n IHn] [| l0 l].
  + set f := (X in filter X _); have /eq_filter -> : f =1 pred0.
      rewrite /f; move=> i /=; by rewrite in_nil.
    by rewrite filter_pred0.
  + move=> _; have:= ltn_ord l0; by rewrite ltn0.
  + set f := (X in filter X _); have /eq_filter -> : f =1 pred0.
      rewrite /f; move=> i /=; by rewrite in_nil.
    by rewrite filter_pred0.
  + rewrite (enum_ordS n) /=.
    case: l0 => [[/=| l0] Hl0].
    * have -> : (Ordinal Hl0) = ord0 by apply val_inj.
      move/unlift_seqE => [] l1 [] /IHn {IHn} <- Hl.
      rewrite {2}Hl; congr (_ :: _).
      rewrite filter_map (eq_in_filter (a2 := (fun i => i \in l1))) //=.
      move=> i _ /=; rewrite Hl in_cons.
      have:= neq_lift ord0 i; rewrite eq_sym => /negbTE -> /=.
      rewrite mem_map; last by apply lift_inj.
      apply/(sameP idP); apply(iffP idP); last by rewrite mem_filter => /andP [].
      by move=> Hi; rewrite mem_filter Hi /= mem_enum inE.
    * move=> Hpath; have H0 : (@ord0 n.+1) < (Ordinal Hl0) by [].
      have Hsort : sorted (fun i j : 'I_n.+1 => i < j) (ord0 :: (Ordinal Hl0) :: l) by [].
      have {Hpath Hsort} := unlift_seqE Hsort => [] [] l1 [] Hsort1 ->.
      rewrite ord0_in_map_liftF -(IHn l1 Hsort1) filter_map /=.
      set f := (X in filter X _); suff /eq_filter -> : f =1 mem l1 by [].
      rewrite /f {f}; move=> i /=.
      rewrite mem_map; last by apply lift_inj.
      apply/(sameP idP); apply(iffP idP); last by rewrite mem_filter => /andP [].
      by move=> /= Hi; rewrite mem_filter Hi /= mem_enum inE.
Qed.

Section TrivISeq.

Variable T : finType.

Lemma bigcup_seq_cover (u : seq {set T}) :
  \bigcup_(s <- u) s = cover [set s in u].
Proof. rewrite /cover bigcup_seq; apply eq_bigl => i; by rewrite inE. Qed.

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

Lemma trivIseq_cover S : trivIseq S -> \sum_(i <- S) #|i| = #|\bigcup_(i <- S) i|.
Proof.
  elim: S => [_ | s0 s IHs] /=; first by rewrite !big_nil cards0.
  move=> Htriv; have {IHs} IHs := IHs (trivIseq_consK Htriv).
  move: Htriv; rewrite !big_cons /trivIseq => Htriv.
  rewrite cardsU -IHs.
  suff -> : #|s0 :&: \big[setU (T:=T)/set0]_(j <- s) j| = 0 by rewrite subn0.
  apply/eqP; rewrite cards_eq0; apply/eqP; rewrite -setP => i.
  rewrite !inE; apply/(sameP idP); apply(iffP idP) => //= /andP [] Hi.
  rewrite bigcup_seq => /bigcupP [] X HX HiX.
  have:= HX; rewrite -!index_mem => Hind.
  have: 0 < (index X s).+1 < size (s0 :: s) by rewrite /= ltnS Hind.
  move/Htriv => /=; rewrite (nth_index set0 HX).
  move/disjoint_setI0; rewrite -setP => H.
  have := H i; by rewrite !inE Hi HiX.
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

Lemma set_nil (T : finType) : [set s : T in [::]] = set0.
Proof. by rewrite -setP => i; rewrite inE. Qed.

Lemma cover_nil (T : finType) : #|cover [set s : {set T} in [::]]| = 0.
Proof.
  rewrite set_nil /cover /= big_pred0; last by move=> i /=; rewrite inE.
  by rewrite cards0.
Qed.

Lemma subseq_take (T : eqType) k (l : seq T) : subseq (take k l) l.
Proof. rewrite -{2}[l](cat_take_drop k); by apply prefix_subseq. Qed.

Section BigTrivISeq.

Variable T : finType.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx).

Lemma bigop_trivIseq (S : seq {set T}) F :
  all (fun s => s != set0) S ->
  trivIseq S -> \big[op/idx]_(i in [set x in S]) F i  =  \big[op/idx]_(i <- S) F i.
Proof.
  elim: S => [//= _| S0 S IHS] /=.
  - rewrite set_nil big_nil big_pred0 //=.
    move => i /=; by rewrite in_set0.
  - move/andP => [] HS0 Hall; rewrite /trivIseq => Htriv.
    rewrite set_cons big_cons big_setU1.
    + by rewrite (IHS Hall (trivIseq_consK Htriv)).
    + move: HS0 => /set0Pn [] x Hx.
      rewrite negbT //=; apply/(sameP idP); apply(iffP idP) => //=.
      rewrite inE => HS; have:= HS; rewrite -index_mem => HS1.
      set j := index S0 S; have H : 0 < j.+1 < size (S0 :: S) by [].
      have:= Htriv 0 j.+1 H.
      rewrite /= /j nth_index //= -setI_eq0 => /eqP; rewrite -setP => HH.
      have := HH x; by rewrite !inE Hx.
Qed.

End BigTrivISeq.

Section GreenDef.

Variable Alph : ordType.

Definition extractpred n (wt : n.-tuple Alph) (P : pred 'I_n) :=
  [seq tnth wt i | i <- enum P].

Lemma extractIE n (wt : n.-tuple Alph) P :
  extractpred wt P = [seq tnth wt i | i <- enum 'I_n & P i].
Proof. by rewrite /extractpred {1}/enum_mem -enumT /=. Qed.

Lemma extractmaskE n (wt : n.-tuple Alph) P :
  extractpred wt P = mask [seq P i | i <- enum 'I_n] wt.
Proof.
  rewrite extractIE.
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
  rewrite !extractmaskE; case: wt => w /= _.
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
    by rewrite -extractmaskE; apply extsubsIm.
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
Proof. by rewrite /extractpred size_map cardE. Qed.

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
  rewrite /= extractIE /=.
  have /eq_filter -> : mem set0 =1 (@pred0 'I_N) by move=> i /=; rewrite in_set0.
  by rewrite filter_pred0.
Qed.

Lemma extract1 i : extract [set i] = [:: tnth wt i].
Proof.
  rewrite /= extractIE.
  set s := filter _ _; suff -> : s = [:: i] by [].
  rewrite /s {s}.
  have /eq_filter -> : (mem [set i]) =1 pred1 i by move=> j /=; rewrite in_set1.
  apply filter_pred1_uniq; first by apply enum_uniq.
  by rewrite mem_enum inE.
Qed.

Lemma extractS (l : seq 'I_N) :
  sorted (fun i j : 'I_N => val i < val j) l ->
  extract [set i in l] = [seq tnth wt i | i <- l].
Proof.
  move=> HS; rewrite /= extractIE.
  congr ([seq tnth wt i | i <- _]).
  set f := (X in filter X _).
  have /eq_filter -> : f =1 mem l by move => i; rewrite /f !inE.
  by rewrite mem_enum_seqE.
Qed.

Lemma extract2 i j : val i < val j -> extract [set i; j] = [:: tnth wt i; tnth wt j].
Proof.
  move=> Hij.
  have : sorted (fun i j : 'I_N => val i < val j) [:: i; j] by rewrite /sorted /path Hij.
  move/extractS => /= <-; congr (extractpred wt (mem (pred_of_set _))).
  apply/setP/subset_eqP/andP; split; apply/subsetP=> k; by rewrite !inE.
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

Lemma green_rel_t_0 : green_rel_t 0 = 0.
Proof.
  rewrite /green_rel_t /=.
  apply /eqP; rewrite eqn_leq; apply /andP; split; last by [].
  apply/bigmax_leqP => S.
  rewrite /ksupp => /and3P [] HS _ _.
  have -> : S = set0 by apply /eqP; rewrite -cards_eq0 eqn_leq HS.
  by rewrite /cover big_set0 cards0.
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
  rewrite /= !extractmaskE enumIMN map_cat.
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
  rewrite /= !extractmaskE enumIMN map_cat.
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

Definition green_rel u := [fun k => green_rel_t comp (in_tuple u) k].

Lemma green_rel_cat k v w : green_rel (v ++ w) k <= green_rel v k + green_rel w k.
Proof.
  rewrite /disjoint /=.
  suff -> : green_rel_t comp (in_tuple (v ++ w)) k =
            green_rel_t comp [tuple of (in_tuple v) ++ (in_tuple w)] k
    by apply green_rel_t_cat.
  have Hsz : size (v ++ w) = (size v + size w) by rewrite size_cat.
  rewrite -(green_rel_t_cast _ Hsz); congr (green_rel_t comp _ k).
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

Section GreenRec.

Variable Alph : ordType.
Implicit Type u v w : seq Alph.
Implicit Type t : seq (seq Alph).

Let sym_cast m n (i : 'I_(m + n)) : 'I_(n + m) := cast_ord (addnC m n) i.

Definition shiftset s0 sh :=
  [fun s : {set 'I_(sumn sh)} => ((@sym_cast _ _) \o (@lshift (sumn sh) s0)) @: s].

Fixpoint shrows sh : seq {set 'I_(sumn sh)} :=
  if sh is s0 :: sh then
    [set ((@sym_cast _ _) \o (@rshift (sumn sh) s0)) i | i in 'I_s0] ::
    map (@shiftset s0 sh) (shrows sh)
  else [::].
Fixpoint shcols sh : seq {set 'I_(sumn sh)} :=
  if sh is s0 :: sh then
    [seq (sym_cast (@rshift (sumn sh) s0 i)) |:
         (@shiftset s0 sh (nth set0 (shcols sh) i))
    | i <- enum 'I_s0]
  else [::].

Let cast_set_tab t :=
  [fun s : {set 'I_(sumn (shape t))} => (cast_ord (size_to_word t)) @: s].

Definition tabrows t := map (cast_set_tab t) (shrows (shape t)).
Definition tabcols t := map (cast_set_tab t) (shcols (shape t)).
Definition tabrowsk t := [fun k => take k (tabrows t)].
Definition tabcolsk t := [fun k => take k (tabcols t)].

Lemma size_shcols_cons s0 sh : size (shcols (s0 :: sh)) = s0.
Proof. by rewrite /= size_map size_enum_ord. Qed.

Lemma size_shcols sh : size (shcols sh) = head 0 sh.
Proof. by case sh => [//= | s0 s]; apply size_shcols_cons. Qed.

Lemma size_tabcols t : size (tabcols t) = size (head [::] t).
Proof. rewrite /tabcols /= size_map size_shcols. by case t. Qed.

Lemma size_shrows sh : size (shrows sh) = size sh.
Proof. elim: sh => [//= | sh0 sh] /=; by rewrite !size_map => ->. Qed.

Lemma size_tabrows t : size (tabrows t) = size t.
Proof. by rewrite /tabrows /= size_map size_shrows size_map. Qed.

Lemma shcol_cards sh :
  is_part sh ->
  map (fun S : {set 'I_(sumn sh)} => #|S|) (shcols sh) = conj_part sh.
Proof.
  elim: sh => [//= | s0 sh IHsh] /= /andP [] Hhead Hpart.
  rewrite -map_comp; set F := (X in map X _).
  have {F} /eq_map -> : F =1 fun i => (nth 0 (conj_part sh) i).+1.
    move=> i; rewrite /F {F} /= cardsU.
    rewrite cards1 imset_comp card_imset; last by apply cast_ord_inj.
    rewrite card_imset; last by apply linjP.
    rewrite add1n -(IHsh Hpart).
    set S := (X in _ - #|pred_of_set X|); have -> : S = set0.
      rewrite /S {S} -setP => j; rewrite !inE.
      apply/(sameP idP); apply(iffP idP) => //= /andP [] /eqP -> {j}.
      rewrite mem_imset_inj; last by apply cast_ord_inj.
      move/imsetP => [] j _ /eqP; by rewrite eq_sym lrinjF.
    rewrite cards0 subn0.
    case (ltnP i (size (shcols sh))) => Hi.
    - by rewrite (nth_map set0 _ _ Hi).
    - rewrite (nth_default _ Hi) nth_default; last by rewrite size_map.
      by rewrite cards0.
  elim: sh s0 Hhead Hpart {IHsh} => [//= | s1 sh IHsh] /=.
  - move=> s0 Hs0 _; apply (@eq_from_nth _ 0).
    + by rewrite size_map size_nseq size_enum_ord.
    + move=> i; rewrite size_map size_enum_ord => Hi.
      rewrite nth_nseq Hi (nth_map (Ordinal Hs0)); last by rewrite size_enum_ord.
      by rewrite nth_nil.
  - move=> s0 Hs1 /andP [] Hhead Hpart.
    rewrite -(IHsh s1 Hhead Hpart) {IHsh}.
    move HS : (map _ (enum 'I_s1)) => S.
    have : size S <= s0 by rewrite -HS size_map size_enum_ord.
    elim: S {HS s1 Hhead Hpart sh Hs1} s0 => [//= s0 _| l0 l IHl] /=.
    + apply (@eq_from_nth _ 0); first by rewrite size_map size_nseq size_enum_ord.
      move=> i; rewrite size_map size_enum_ord => Hi.
      rewrite nth_nseq Hi (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
      by rewrite nth_nil.
    + case => [//= | s0]; rewrite ltnS => /IHl <- {IHl}.
      set f := (X in map X _).
      have {f} /eq_map -> : f =1 (fun i => (nth 0 (l0 :: l) i).+1) \o val by [].
      rewrite map_comp val_enum_ord /=.
      rewrite -[1]addn0 iota_addl -map_comp.
      set f := (X in map X _).
      have {f} /eq_map -> : f =1 (fun i => (nth 0 l i).+1) by [].
      set f := (X in _ = _ :: map X _).
      have {f} /eq_map -> : f =1 (fun i => (nth 0 l i).+1) \o val by [].
      by rewrite [map _ (enum _)]map_comp val_enum_ord /=.
Qed.

Lemma shrows_cards sh :
  map (fun S : {set 'I_(sumn sh)} => #|S|) (shrows sh) = sh.
Proof.
  elim: sh => [//= | s0 sh IHsh] /=.
  rewrite imset_comp card_imset; last by apply cast_ord_inj.
  rewrite card_imset; last by apply rinjP.
  rewrite card_ord; congr (_ :: _).
  rewrite -map_comp -{19}IHsh; apply eq_map.
  move=> S /=; rewrite imset_comp.
  rewrite card_imset; last by apply cast_ord_inj.
  by rewrite card_imset; last by apply linjP.
Qed.

Lemma tabrows_non0 t :
  is_part (shape t) -> forall s, s \in tabrows t -> s != set0.
Proof.
  move=> Hpart S'.
  rewrite /tabrows => /mapP [] S HS -> {S'}.
  rewrite -card_gt0 card_imset; last by apply cast_ord_inj.
  pose crd := (fun S : {set 'I_(sumn (shape t))} => #|S|).
  have: crd S \in map crd (shrows (shape t)) by apply/mapP; exists S.
  rewrite /crd {crd} /= shrows_cards.
  move: (#|S|) => i {S HS}.
  elim: t Hpart i => [//= | t0 t IHt] Hpart i /=.
  rewrite inE => /orP [/eqP -> |].
  + have:= (part_head_non0 Hpart) => /=; by case (size t0).
  + apply IHt; by apply (is_part_tl Hpart).
Qed.

Lemma trivIseq_shrows sh : trivIseq (shrows sh).
Proof.
  elim: sh => [/= | s0 sh /= IHsh]; first by rewrite /trivIseq => i j /= /andP [].
  rewrite /trivIseq /= size_map => i j /andP [] Hij Hj.
  rewrite /disjoint; apply/pred0P => l /=; apply (introF idP) => /andP [].
  case: i j Hj Hij => [| i] [//= | j] /=; rewrite !ltnS => Hj.
  + move=> _ /imsetP [] i Hi ->.
    rewrite (nth_map set0 _ _ Hj) /shiftset /= imset_comp.
    rewrite mem_imset_inj; last by apply cast_ord_inj.
    move/imsetP => [] j' _ /eqP; by rewrite eq_sym lrinjF.
  + move=> Hij; have Hi := (ltn_trans Hij Hj).
    rewrite (nth_map set0 _ _ Hj) (nth_map set0 _ _ Hi) /shiftset /=.
    move=> /imsetP [] k Hk ->.
    rewrite mem_imset_inj => Hk'; last apply (inj_comp (@cast_ord_inj _ _ _) (@linjP _ _)).
    have /IHsh : i < j < size (shrows sh) by rewrite Hij Hj.
    rewrite /disjoint => /pred0P H.
    have:= H k; by rewrite /= Hk Hk'.
Qed.

Lemma trivIset_tabrowsk k t : trivIset [set s | s \in (tabrowsk t k)].
Proof.
  apply trivIs; rewrite /tabrowsk /tabrows /= -map_take.
  apply trivIseq_map; first by apply cast_ord_inj.
  apply (trivIsubseq (v := (shrows (shape t)))).
  + rewrite -{2}[shrows (shape t)](cat_take_drop k).
    by apply prefix_subseq.
  + by apply trivIseq_shrows.
Qed.

Lemma trivIseq_shcols sh : trivIseq (shcols sh).
Proof.
  elim: sh => [/= | s0 sh /= IHsh]; first by rewrite /trivIseq => i j /= /andP [].
  rewrite /trivIseq size_shcols_cons => i j /andP [] Hij Hj.
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
      case: (ltnP j (size (shcols sh))) => Hj1;
        last by move: Hlj; rewrite (nth_default _ Hj1) in_set0.
      have : i < j < size (shcols sh) by rewrite Hij Hj1.
      move/(IHsh i j); rewrite /disjoint => /pred0P H.
      have:= H l; by rewrite /= Hli Hlj.
Qed.

Lemma trivIseq_tabcols (t : seq (seq Alph)) : trivIseq (tabcols t).
Proof. apply trivIseq_map; first by apply cast_ord_inj. by apply trivIseq_shcols. Qed.

Lemma trivIset_tabcolsk k t : trivIset [set s | s \in (tabcolsk t k)].
Proof.
  apply trivIs; rewrite /tabcolsk /=.
  apply (trivIsubseq (v := (tabcols t))); last by apply trivIseq_tabcols.
  rewrite -{2}[tabcols t](cat_take_drop k).
  by apply prefix_subseq.
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


Lemma enumIsize_to_word :
  enum 'I_(size (to_word (t0 :: t))) =
  map linj_rec (enum 'I_(size (to_word t)))  ++  map rinj_rec (enum 'I_(size t0)).
Proof.
  rewrite /rinj_rec /linj_rec (enum_cast_ord size_to_word_cons).
  rewrite !map_comp /cast_cons -map_cat; congr (map (cast_ord size_to_word_cons) _).
  by rewrite map_id enumIMN.
Qed.

Lemma compA (T1 T2 T3 T4: eqType)
      (f : T3 -> T4) (g : T2 -> T3) (h : T1 -> T2) : (f \o g) \o h =1 f \o (g \o h).
Proof. by move=> i. Qed.

Lemma extract_tabrows_0 :
  extract (in_tuple (to_word (t0 :: t))) (nth set0 (tabrows (t0 :: t)) 0) = t0.
Proof.
  rewrite /tabrows /= imset_comp -!imset_comp extractIE.
  set S := imset _ _; have -> : S = [set rinj_rec i | i in 'I_(size t0)].
    rewrite /S {S} -setP => i; apply/(sameP idP); apply(iffP idP).
    * move/imsetP => [] x _ ->; apply/imsetP; exists x => //=.
      by rewrite -rcast_com /=.
    * move/imsetP => [] x _ ->; apply/imsetP; exists x => //=.
      by rewrite -rcast_com /=.
  rewrite {S} enumIsize_to_word filter_cat map_cat -[RHS]cat0s; congr (_ ++ _).
  - rewrite (eq_in_filter (a2 := pred0)); first by rewrite filter_pred0.
    move=> i /mapP [] j Hj /= -> {i}.
    apply (introF idP) => /imsetP [] k _ /eqP; by rewrite lrinj_recF.
  - rewrite (eq_in_filter (a2 := predT)); first last.
      move=> i /= /mapP [] j _ -> {i}; by rewrite mem_imset.
    rewrite filter_predT -map_comp.
    rewrite (eq_map (f2 := nth (inhabitant Alph) t0 \o val)); first last.
    + move=> i /=; rewrite (tnth_nth (inhabitant Alph)) /to_word /=.
      rewrite rev_cons flatten_rcons nth_cat.
      rewrite /to_word -{2}[size (flatten (rev t))]addn0 ltn_add2l /=.
      by rewrite addnC addnK.
    + apply (eq_from_nth (x0 := inhabitant Alph)); first by rewrite size_map size_enum_ord.
      move=> i; rewrite size_map size_enum_ord => Hi.
      rewrite (nth_map (Ordinal Hi)) /=; last by rewrite size_enum_ord.
      by rewrite nth_enum_ord //=.
Qed.

Lemma extract_tabrows_rec i :
  i < size t ->
  extract (in_tuple (to_word (t0 :: t))) (nth set0 (tabrows (t0 :: t)) i.+1) =
  extract (in_tuple (to_word t)) (nth set0 (tabrows t) i).
Proof.
  move=> Hi.
  rewrite /tabrows /= /shiftset /= map_comp -!map_comp !extractIE.
  set f := (X in nth _ (map X _)).
  have /eq_map -> /= :
    f =1 (fun s => [set linj_rec x | x in s]) \o (fun s => cast_set_tab t s).
    move=> S /=; rewrite /f {f} -setP => j.
    by apply/(sameP idP); apply(iffP idP);
      rewrite -!imset_comp /= -(eq_imset _ lcast_com) -!imset_comp.
  rewrite {f} /= enumIsize_to_word filter_cat map_cat -[RHS]cats0; congr (_ ++ _).
  - rewrite (nth_map set0) /=; last by rewrite size_shrows size_map.
    rewrite filter_map /= -map_comp.
    set f1 := (X in map X _ = _); set f2 := (X in _ = map X _).
    have /eq_map -> : f1 =1 f2.
      rewrite /f1 /f2 {f1 f2} => j /=; rewrite !(tnth_nth (inhabitant Alph)) /=.
      by rewrite to_word_cons nth_cat ltn_ord.
    congr (map f2 _) => {f1 f2}.
    apply eq_filter => j /=; rewrite mem_imset_inj; last exact linj_recP.
    rewrite (nth_map set0) /cast_set_tab //=.
    by rewrite size_shrows size_map.
  - rewrite (eq_in_filter (a2 := pred0)); first by rewrite filter_pred0.
    move=> j' /mapP [] j Hj /= -> {j'}.
    apply (introF idP); rewrite (nth_map set0); last by rewrite size_shrows size_map.
    move=> /imsetP [] k _ /eqP; by rewrite eq_sym lrinj_recF.
Qed.


Lemma tabcols_cons:
  tabcols (t0 :: t) =
    [seq rinj_rec i |: (linj_rec @: (nth set0 (tabcols t) i)) | i <- enum 'I_(size t0)].
Proof.
  rewrite /tabcols /cast_cons /=.
  apply (@eq_from_nth _ set0); first by rewrite !size_map.
  move=> i; rewrite 2!size_map => Hienum; have:= Hienum; rewrite size_enum_ord => Hi.
  rewrite -map_comp (nth_map (Ordinal Hi)) //= !(nth_enum_ord _ Hi).
  rewrite (nth_map (Ordinal Hi)) //= !(nth_enum_ord _ Hi).
  rewrite imsetU1 -!imset_comp.
  case (ltnP i (size (shcols (shape t)))) => Hish.
  + rewrite (nth_map set0 _ _ Hish).
    have:= (rcast_com (nth (Ordinal Hi) (enum 'I_(size t0)) i)) => /= ->.
    by rewrite -!imset_comp (eq_imset _ lcast_com).
  + set empty := (nth set0 (map _ _)) i.
    have {empty} -> : empty = set0 by rewrite /empty nth_default //= size_map.
    set ii := nth _ _ i.
    have {ii} -> : ii = Ordinal Hi by rewrite /ii; apply val_inj; rewrite /= nth_enum_ord.
    by rewrite nth_default //= !imset0 -(rcast_com (Ordinal Hi)).
Qed.

Lemma size_tabcols_cons: size (tabcols (t0 :: t)) = size t0.
Proof. by rewrite tabcols_cons /= size_map size_enum_ord. Qed.

Lemma extract_tabcols_rec i :
  i < size t0 ->
  extract (in_tuple (to_word (t0 :: t))) (nth set0 (tabcols (t0 :: t)) i) =
  rcons (extract (in_tuple (to_word t)) (nth set0 (tabcols t) i))
        (nth (inhabitant Alph) t0 i).
Proof.
  move => Hi; rewrite /= !extractmaskE tabcols_cons enumIsize_to_word /=.
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
  have := extract1 (in_tuple t0) (Ordinal Hi); rewrite /extract /= extractmaskE /= => ->.
  by rewrite cats1 (tnth_nth (inhabitant Alph)) /=.
Qed.

Lemma lsplit_rec_tab k :
  head 0 (shape t) <= size t0 ->
  cover [set lsplit_rec x | x in [set s in tabcolsk (t0 :: t) k]] =
  cover [set s in tabcolsk t k].
Proof.
  move => Hsize; rewrite cover_imset /tabcolsk /= tabcols_cons /cover /preimset.
  apply/setP/subset_eqP/andP; split; apply/subsetP => i.
  - move/bigcupP => [] S0; rewrite !inE.
    move/(mem_takeP set0) => [] pos [].
    rewrite size_map size_enum_ord leq_min => /andP [] Hpos Hpos0 ->.
    rewrite (nth_map (Ordinal Hpos0)); last by rewrite size_enum_ord.
    rewrite !inE lrinj_recF /= (mem_imset_inj _ _ linj_recP) nth_ord_ltn => Hi.
    apply/bigcupP; exists (nth set0 (tabcols t) (Ordinal Hpos0)); last exact Hi.
    rewrite inE; apply/(mem_takeP set0).
    exists pos; split; last by [].
    rewrite leq_min Hpos /=.
    case: (ltnP pos (size (tabcols t))) => //= H.
    move: Hi; by rewrite (nth_default _ H) in_set0.
  - move/bigcupP => [] S0; rewrite !inE => /(mem_takeP set0) [] pos [].
    rewrite leq_min => [] /andP [] Hpos Hpossz -> Hi.
    have Hpos0 : pos < size t0.
      apply (leq_trans Hpossz). rewrite size_tabcols.
      move: Hsize; rewrite /shape; by case t.
    apply/bigcupP.
    exists (rinj_rec (Ordinal Hpos0)
                  |: [set linj_rec x | x in nth set0 (tabcols t) (Ordinal Hpos0)]).
    * rewrite inE; apply/(mem_takeP set0).
      exists pos; rewrite size_map size_enum_ord leq_min; split; first by rewrite Hpos.
      rewrite (nth_map (Ordinal Hpos0)); last by rewrite size_enum_ord.
      by rewrite nth_ord_ltn.
    * rewrite !inE lrinj_recF /=; apply/imsetP; by exists i.
Qed.

Lemma rsplit_rec_tab k :
  cover [set rsplit_rec x | x in [set s in (tabcolsk (t0 :: t)) k]] =
  [set i : 'I_(size t0) | i < k].
Proof.
  rewrite /tabcolsk /= tabcols_cons.
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
    apply/imsetP; exists ((rinj_rec i) |: [set linj_rec x | x in nth set0 (tabcols t) i]).
    + rewrite inE; apply/(mem_takeP set0).
      exists i; rewrite size_map size_enum_ord leq_min Hi; split; first by apply ltn_ord.
      rewrite (nth_map i); last by rewrite size_enum_ord; apply ltn_ord.
      rewrite nth_enum_ord; last by apply ltn_ord.
      by rewrite nth_ord_enum.
    +  apply/setP/subset_eqP/andP; split; apply/subsetP => j; rewrite in_set1.
      * move/eqP=> -> {j}; by rewrite !inE eq_refl.
      * by rewrite !inE rinj_in_linj_recF orbF => /eqP/rinj_recP ->.
Qed.

Lemma cover_tabcols_rec k :
  head 0 (shape t) <= size t0 ->
  cover [set s in (tabcolsk (t0 :: t) k)] =
  rinj_rec @: [set s : 'I_(size t0) | s < k]
           :|:  linj_rec @: cover [set s in (tabcolsk t k)].
Proof.
  move => Hsize; by rewrite split_rec_cover setUC rsplit_rec_tab (lsplit_rec_tab _ Hsize).
Qed.

End Induction.

Lemma scover_tabrows k t :
  is_part (shape t) ->
  scover [set s | s \in (tabrowsk t k)] = part_sum (shape t) k.
Proof.
  move=> Hpart.
  have:= trivIset_tabrowsk k t; rewrite /trivIset /scover /= => /eqP <-.
  rewrite /scover /cover /= bigop_trivIseq; first last.
  + apply (trivIsubseq (v := tabrows t)); first by apply subseq_take.
    rewrite /tabrows; apply trivIseq_map; first by apply cast_ord_inj.
    by apply trivIseq_shrows.
  + apply/allP => S /mem_take HS; by apply tabrows_non0.
  rewrite /part_sum.
  elim: t k {Hpart} => [//= | t0 t IHt] /= k; first by rewrite !big_nil.
  case: k => [//= | k]; first by rewrite !big_nil.
  have:= IHt k; rewrite !big_cons => <- {IHt}.
  rewrite /sym_cast imset_comp card_imset; last by apply cast_ord_inj.
  rewrite card_imset; last by apply cast_ord_inj.
  rewrite card_imset; last by apply rinjP.
  rewrite card_ord; congr (_ + _).
  rewrite /tabrows -!map_take /shiftset /=.
  move: (take _ _) => S.
  elim: S => [| s0 S IHS] /=; first by rewrite !big_nil.
  rewrite !big_cons.
  rewrite /sym_cast imset_comp card_imset; last by apply cast_ord_inj.
  rewrite card_imset; last by apply cast_ord_inj.
  rewrite card_imset; last by apply linjP.
  rewrite card_imset; last by apply cast_ord_inj.
  congr (_ + _); by apply IHS.
Qed.

Lemma sorted_leqX_tabrows t i :
  is_tableau t -> i < size (tabrows t) ->
  sorted (leqX Alph)
         (extract (in_tuple (to_word t)) (nth set0 (tabrows t) i)).
Proof.
  rewrite size_tabrows.
  elim: t i => [//= | t0 t IHt] i.
  rewrite [X in X -> _]/=; move=> /and4P [] _ Hrow _ Htab.
  case: i IHt => [_ _ | i IHt Hi].
  + rewrite extract_tabrows_0; exact Hrow.
  + rewrite extract_tabrows_rec; last by apply Hi.
    by apply (IHt _ Htab).
Qed.

Lemma ksupp_leqX_tabrowsk k t :
  is_tableau t -> ksupp (leqX Alph) (in_tuple (to_word t)) k [set s | s \in (tabrowsk t k)].
Proof.
  move=> Htab; rewrite /ksupp /tabrowsk; apply/and3P; split.
  + apply (leq_trans (card_seq (tabrowsk t k))).
    rewrite /tabrowsk /= size_take; by apply geq_minl.
  + apply trivIset_tabrowsk.
  + apply/forallP => s; apply/implyP.
    rewrite /= inE => /mem_take Hin.
    rewrite -(nth_index set0 Hin).
    move: Hin; rewrite -index_mem; set i := index _ _ => Hi.
    by apply (sorted_leqX_tabrows Htab).
Qed.


Lemma scover_tabcolsk k t :
  is_part (shape t) ->
  scover [set s | s \in (tabcolsk t k)] = \sum_(l <- (shape t)) minn l k.
Proof.
  elim: t => [//= | t0 t IHt] /=; first by rewrite cover_nil big_nil.
  move/andP => [] Hhead /IHt {IHt} IHt.
  have {Hhead} Hhead : head 0 (shape t) <= size t0.
    apply (@leq_trans (head 1 (shape t))); last exact Hhead.
    by case t.
  rewrite big_cons -IHt {IHt} /=.
  have := cover_tabcols_rec k Hhead; rewrite /tabcols /=.
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

Lemma cover_tabcols t :
  is_part (shape t) -> cover [set s | s \in tabcols t] = setT.
Proof.
  move=> Hpart.
  apply/eqP; rewrite eqEcard; apply/andP; split; first by apply subsetT.
  have -> : tabcols t = tabcolsk t (size (head [::] t)).
    by rewrite /tabcolsk /= -size_tabcols take_size.
  have := (scover_tabcolsk _ Hpart); rewrite /scover /= => ->.
  rewrite cardsT card_ord -size_to_word /size_tab.
  have : head 0 (shape t) <= (size (head [::] t)) by case t.
  elim: (shape t) Hpart => [//= | p0 p IHp] /= /andP [] Hhead Hpart Hp0.
  rewrite big_cons; apply leq_add.
  - by rewrite minnC /minn ltnNge Hp0 /=.
  - apply (IHp Hpart).
    have:= leq_trans Hhead Hp0; by case p.
Qed.

Lemma sorted_gtnX_tabcols t i :
  is_tableau t -> i < size (tabcols t) ->
  sorted (gtnX Alph)
         (extract (in_tuple (to_word t)) (nth set0 (tabcols t) i)).
Proof.
  elim: t => [//= | t0 t IHt].
  rewrite [X in X -> _]/=; move=> /and4P [] _ _ /dominateP [] Hsz Hdom Htab.
  rewrite size_tabcols_cons => Hi; rewrite (extract_tabcols_rec _ Hi).
  case (ltnP i (size (head [::] t))) => Hit.
  + have:= Hit; rewrite -size_tabcols; move/(IHt Htab) => {IHt}.
    move Hrec : (extract _ _) => ext.
    case: ext Hrec => [//= | a0 ext] Hext.
    rewrite rcons_cons /= rcons_path => -> /=.
    suff {Hdom} -> : last a0 ext = nth (inhabitant Alph) (head [::] t) i by apply Hdom.
    rewrite -[last a0 ext]/(last (inhabitant Alph) (a0 :: ext)) -Hext {a0 ext Hext}.
    case: t Hsz Htab Hit => [//= | t1 t] Hsz Htab Hit.
    by rewrite (extract_tabcols_rec _ Hit) last_rcons.
  + rewrite nth_default; last by rewrite size_tabcols.
    by rewrite extract0.
Qed.

Lemma ksupp_gtnX_tabcolsk k t :
  is_tableau t -> ksupp (gtnX Alph) (in_tuple (to_word t)) k [set s | s \in (tabcolsk t k)].
Proof.
  move=> Htab; rewrite /ksupp /tabcolsk; apply/and3P; split.
  + apply (leq_trans (card_seq (tabcolsk t k))).
    rewrite /tabcolsk /= size_take; by apply geq_minl.
  + apply trivIset_tabcolsk.
  + apply/forallP => s; apply/implyP.
    rewrite /= inE => /mem_take Hin.
    rewrite -(nth_index set0 Hin).
    move: Hin; rewrite -index_mem; set i := index _ _ => Hi.
    by apply (sorted_gtnX_tabcols Htab).
Qed.

End GreenRec.



Section GreenTab.

Variable Alph : ordType.

Implicit Type t : seq (seq Alph).

Definition greenRow := green_rel (leqX Alph).
Definition greenCol := green_rel (gtnX Alph).

Lemma size_row_extract t S i :
  is_tableau t ->
  sorted (leqX Alph) (extract (in_tuple (to_word t)) S) ->
  #|S :&: (nth set0 (tabcols t) i)| <= 1.
Proof.
  move=> Htab Hleq.
  case (ltnP i (size (tabcols t))) => Hi; last by rewrite (nth_default _ Hi) setI0 cards0.
  set T := nth _ _ _.
  have: S :&: T \subset S by apply/subsetP => j; rewrite !inE=> /andP [].
  move/(extsubsI (in_tuple (to_word t)))/(subseq_sorted (@leqX_trans _)) => Htmp.
  have {Htmp Hleq} Hleq := Htmp Hleq.
  have Hgtn:= sorted_gtnX_tabcols Htab Hi.
  have: S :&: T \subset T by apply/subsetP => j; rewrite !inE=> /andP [].
  move/(extsubsI (in_tuple (to_word t)))/(subseq_sorted (@gtnX_trans _)) => Htmp.
  have {Htmp Hgtn} Hgtn := Htmp Hgtn.
  rewrite -(size_extract (in_tuple (to_word t))).
  case: (extract _ _) Hleq Hgtn => [//= | l0 [//=| l1 s]] /=.
  move=> /andP []; by rewrite ltnXNgeqX => -> /=.
Qed.

Lemma tabcol_cut t :
  is_part (shape t) -> forall B, \sum_(S <- tabcols t) #|B :&: S| = #|B|.
Proof.
  move=> Hpart B.
  have -> : \sum_(S <- tabcols t) #|B :&: S| =
            \sum_(S <- [seq B :&: S | S <- tabcols t]) #|S| by rewrite big_map.
  have Htriv := @trivIseq_tabcols _ t.
  have : trivIseq [seq B :&: S | S <- tabcols t].
    rewrite /trivIseq => i j; rewrite size_map => Hijs; have:= Hijs => /andP [] Hij Hj.
    have Hi := ltn_trans Hij Hj.
    rewrite -setI_eq0 (nth_map set0 _ _ Hi) (nth_map set0 _ _ Hj).
    rewrite setIACA setIid.
    have := Htriv _ _ Hijs; rewrite -setI_eq0 => /eqP ->.
    by rewrite setI0.
  move/trivIseq_cover ->; congr #|_|.
  rewrite big_map.
  pose F := (fun S => B :&: S).
  have : \bigcup_(j <- tabcols t) F j = F (\bigcup_(j <- tabcols t) j).
    apply esym; apply big_morph; last by rewrite /F setI0.
    move=> i j /=; by rewrite /F setIUr.
  rewrite /F {F} /= => ->.
  by rewrite bigcup_seq_cover (cover_tabcols Hpart) setIT.
Qed.

Lemma scoverI (T: finType) (S : {set {set T}}) B :
  trivIset S -> \sum_(i in S) #|i :&: B| = #|cover S :&: B|.
Proof.
  move=> /trivIsetP Htriv.
  have : trivIset [set i :&: B | i in S].
    apply /trivIsetP => U1 V1 /imsetP [] U HU -> /imsetP [] V HV -> {U1 V1} Hneq.
    rewrite -setI_eq0 setIACA setIid.
    have : U != V by move: Hneq; apply contra => /eqP ->.
    move/(Htriv _ _ HU HV); rewrite -setI_eq0 => /eqP ->.
    by rewrite set0I.
  rewrite /trivIset.
  pose F := (fun S => S :&: B).
  have -> : cover [set F i | i in S] = F (cover S).
    rewrite cover_imset /cover.
    apply esym; apply big_morph; last by rewrite /F set0I.
    move=> i j /=; by rewrite /F setIUl.
  rewrite /F {F} /= => /eqP <-.
  apply esym.
  rewrite (bigID (fun S => S :&: B == set0)) /=.
  rewrite (eq_bigr (fun B => 0)); first last.
    move=> i /andP [] /imsetP [] j _ ->.
    by rewrite -setIA setIid => /eqP ->; rewrite cards0.
  rewrite sum_nat_dep_const muln0 add0n.
  rewrite (eq_bigl (mem ([set i :&: B | i in S & i :&: B != set0]))); first last.
    move=> i /=; apply/(sameP idP); apply(iffP idP).
    - move/imsetP => [] j; rewrite inE => /andP [] Hj Hint -> {i}.
      rewrite -setIA setIid Hint andbT.
      apply/imsetP; by exists j.
    - move/andP => [] /imsetP [] j Hj -> {i}.
      rewrite -setIA setIid => Hint.
      apply/imsetP; exists j => //=.
      by rewrite inE Hj Hint.
  rewrite big_imset /=; first last.
    move=> i j /=; rewrite !inE => /andP [] HiS HiB /andP [] HjS HjB /eqP H.
    apply /eqP; move: H; apply contraLR => H.
    have := Htriv _ _ HiS HjS H.
    rewrite -setI_eq0 => /eqP; rewrite -setP => Hneq.
    move: HiB => /set0Pn [] x; rewrite inE => /andP [] Hx HxB.
    have:= Hneq x; rewrite !inE Hx /= => Hxj.
    apply /eqP; rewrite -setP => H0.
    have:= H0 x; by rewrite !inE Hx Hxj HxB.
  apply esym; rewrite (bigID (fun S => S :&: B == set0)) /=.
  rewrite (eq_bigr (fun B => 0)); first last.
    move=> i /andP [] _ /eqP ->.
    by rewrite cards0.
  rewrite sum_nat_dep_const muln0 add0n.
  apply eq_bigl => i /=; by rewrite inE.
Qed.

Lemma trivIset_I (T: finType) (S : {set {set T}}) B :
  trivIset S -> \sum_(i in S) #|i :&: B| <= #|B|.
Proof.
  move/scoverI ->; apply subset_leq_card.
  apply/subsetP => i; by rewrite !inE => /andP [].
Qed.

Lemma shape_tabcols t:
  is_tableau t ->
  conj_part (shape t) =
  [seq #|nth set0 (tabcols t) i| | i <- iota 0 (size (head [::] t))].
Proof.
  move=> Htab.
  rewrite -shcol_cards; last by apply is_part_sht.
  rewrite /tabcols; apply (@eq_from_nth _ 0).
  + rewrite !size_map size_shcols /shape size_iota; by case t.
  + move => i; rewrite size_map => Hi.
    have Hihead : i < size (head [::] t).
      move: Hi; rewrite size_shcols /shape /=; by case t.
    rewrite (nth_map set0 _ _ Hi).
    rewrite (nth_map 0); last by rewrite size_iota.
    rewrite (nth_iota _ Hihead) add0n.
    rewrite (nth_map set0 _ _ Hi) /=.
    by rewrite card_imset; last by apply cast_ord_inj.
Qed.

Lemma greenRow_extract k t :
  is_tableau t -> greenRow (to_word t) k <= \sum_(l <- conj_part (shape t)) minn l k.
Proof.
  move=> Htab.
  rewrite /greenRow /green_rel /= /green_rel_t /scover /=.
  apply/bigmax_leqP => S; rewrite /ksupp => /and3P [] Hsz Htriv.
  have:= Htriv; rewrite /trivIset => /eqP <- /forallP Hall.
  rewrite (eq_bigr (fun B => \sum_(S <- tabcols t) #|B :&: S|));
    last by move=> B _; rewrite (tabcol_cut (is_part_sht Htab)).
  rewrite exchange_big /=.
  have -> : tabcols t = [seq nth set0 (tabcols t) i | i <- iota 0 (size (head [::] t))].
    apply (eq_from_nth (x0 := set0)); first by rewrite size_tabcols size_map size_iota.
    move=> i Hi; rewrite (nth_map 0); last by rewrite size_iota -size_tabcols.
    rewrite nth_iota; last by rewrite-size_tabcols.
    by rewrite add0n.
  rewrite (shape_tabcols Htab) !big_map.
  apply leq_sum => i _; rewrite leq_min; apply /andP; split.
  - by apply trivIset_I.
  - apply (@leq_trans #|S|); last exact Hsz.
    rewrite -sum1_card; apply leq_sum.
    move=> P HP; apply size_row_extract; first exact Htab.
    have:= Hall P; by rewrite HP.
Qed.

Lemma greenRow_inf_tab k t :
  is_tableau t -> greenRow (to_word t) k <= part_sum (shape t) k.
Proof.
  move=> Htab.
  have:= greenRow_extract k Htab; by rewrite sum_conj (conj_partK (is_part_sht Htab)).
Qed.

Theorem greenRow_tab k t :
  is_tableau t -> greenRow (to_word t) k = part_sum (shape t) k.
Proof.
  move=> Ht; apply/eqP; rewrite eqn_leq (greenRow_inf_tab _ Ht) /=.
  rewrite /greenRow /green_rel_t /= -(scover_tabrows _ (is_part_sht Ht)).
  apply leq_bigmax_cond; by apply ksupp_leqX_tabrowsk.
Qed.

Theorem greenRow_tab_eq_shape t1 t2 :
  is_tableau t1 -> is_tableau t2 ->
  (forall k, greenRow (to_word t1) k = greenRow (to_word t2) k) -> (shape t1 = shape t2).
Proof.
  move=> Htab1 Htab2 Heq.
  have Hsh1 := is_part_sht Htab1; have Hsh2 := is_part_sht Htab2.
  apply (part_sum_inj Hsh1 Hsh2).
  move=> k. rewrite -(greenRow_tab k Htab1) -(greenRow_tab k Htab2).
  by apply Heq.
Qed.



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
  rewrite /greenCol /green_rel_t /= -(scover_tabcolsk _ (is_part_sht Ht)).
  apply leq_bigmax_cond; by apply ksupp_gtnX_tabcolsk.
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

