Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm tuple path bigop.
Require Import subseq partition ordtype schensted congr plactic ordcast green.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma size_cover_inj (T1 T2 : finType) (F : T1 -> T2) (P : {set {set T1}}):
  let FSet := fun S : {set T1} => F @: S in
  injective F -> #|cover P| = #|cover [set FSet S | S in P]|.
Proof.
  move=> FSet Hinj; have -> : cover [set FSet S | S in P] = FSet (cover P).
  rewrite cover_imset /cover; apply esym; apply big_morph.
  + move=> i j /=; by apply imsetU.
  + by apply imset0.
  by rewrite card_imset.
Qed.

Lemma bigcup_set1 (T1 : finType) (S : {set T1}) :
  \bigcup_(i in [set S]) i = S.
Proof.
  apply/setP/subset_eqP/andP; split; apply/subsetP=> i.
  + by move/bigcupP => [] T; rewrite in_set1 => /eqP ->.
  + move=> Hi; apply/bigcupP; exists S => //=; by rewrite in_set1.
Qed.

Open Scope bool.

(* We make a module here to avoid poluting the global namespace *)
Module Swap.
Section Swap.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Variable R : rel Alph.

Variable u v : word.
Variable l0 l1 : Alph.
Let x := u ++ [:: l0; l1] ++ v.

Lemma ult : size u < size x.
Proof. by rewrite /= size_cat /= addnS ltnS -{1}[size u]addn0 leq_add2l. Qed.
Definition pos0 := Ordinal ult.
Lemma u1lt : (size u).+1 < size x.
Proof. by rewrite /= size_cat /= addnS ltnS -{1}[size u]addn0 ltn_add2l. Qed.
Definition pos1 := Ordinal u1lt.

Lemma tnth_pos0 : tnth (in_tuple x) pos0 = l0.
Proof.
  rewrite (tnth_nth l0) nth_cat.
  have -> /= : pos0 < size u = false by rewrite /= ltnn.
  by rewrite subnn.
Qed.
Lemma tnth_pos1 : tnth (in_tuple x) pos1 = l1.
Proof.
  rewrite (tnth_nth l1) nth_cat.
  have -> /= : pos1 < size u = false.
    have : size u <= (size u).+1 by [].
    by rewrite leqNgt => /negbTE ->.
  by rewrite subSn //= subnn.
Qed.

Lemma pos01F : (pos0 == pos1) = false.
Proof. by rewrite /eq_op /= ieqi1F. Qed.

Definition swap i : 'I_(size x) :=
  if i == pos0 then pos1 else if i == pos1 then pos0 else i.

Lemma swap_invol : involutive swap.
Proof.
  rewrite /swap => i.
  case: (altP (i =P pos0)) => [->|H0]; first by rewrite eq_sym pos01F eq_refl.
  case: (altP (i =P pos1)) => [->|H1]; first by rewrite eq_refl.
  by rewrite (negbTE H0) (negbTE H1).
Qed.
Lemma swap_inj : injective swap.
Proof. exact (can_inj swap_invol). Qed.

Lemma swap0 : swap pos0 = pos1. Proof. by rewrite /swap pos01F eq_refl. Qed.
Lemma swap1 : swap pos1 = pos0. Proof. by rewrite /swap eq_sym pos01F eq_refl. Qed.
Lemma swapL (i : 'I_(size x)) : i < size u -> swap i = i.
Proof.
  move=> Hi; by rewrite /swap /eq_op /= (ltn_eqF Hi) (ltn_eqF (ltn_trans (Hi) (ltnSn _))).
Qed.
Lemma swapR (i : 'I_(size x)) : i > (size u).+1 -> swap i = i.
Proof.
  move=> Hi; rewrite /swap /eq_op /= eq_sym.
  have:= ltn_eqF (ltn_trans (Hi) (ltnSn _)); rewrite eqSS => ->.
  by rewrite eq_sym (ltn_eqF Hi).
Qed.

Definition swapSet := [fun s : {set 'I_(size x)} => swap @: s].
Lemma swapSet_invol : involutive swapSet.
Proof.
  move=> S; rewrite -setP => i; rewrite -{1}[i]swap_invol.
  by rewrite !(mem_imset_inj _ _ swap_inj).
Qed.
Lemma swapSet_inj : injective swapSet.
Proof. apply imset_inj; exact (can_inj swap_invol). Qed.

Lemma swap_cover (P : {set {set 'I_(size x)}}) :
  cover (swapSet @: P) = swapSet (cover P).
Proof.
  rewrite cover_imset /cover; apply esym; apply big_morph.
  + move=> i j /=; by apply imsetU.
  + by apply imset0.
Qed.

Lemma swap_scover (P : {set {set 'I_(size x)}}) : scover (swapSet @: P) = scover P.
Proof. by rewrite /scover /= swap_cover card_imset; last exact swap_inj. Qed.

Lemma enum_cut : enum 'I_(size x) =
                 [seq i | i <- enum 'I_(size x) & val i < size u]
                   ++ [:: pos0; pos1]
                   ++ [seq i | i <- enum 'I_(size x) & val i >= (size u) + 2].
Proof.
  rewrite [RHS]catA -{1}[enum 'I_(size x)](cat_take_drop ((size u) + 2)).
  rewrite -drop_enumI !map_id; congr (_ ++ _).
  rewrite take_enumI -{1}[enum 'I_(size x)](cat_take_drop (size u)).
  rewrite filter_cat //=; congr (_ ++ _).
  + rewrite take_enumI -filter_predI.
    set pr := (X in filter X _).
    suff /eq_filter -> : pr =1 (gtn (size u)) by [].
    rewrite /pr; move=> i /=; apply andb_idl => /ltn_trans; apply.
    rewrite -{1}[size u](addn0); by rewrite ltn_add2l.
  + apply (inj_map val_inj) => /=.
    rewrite map_filter_comp map_drop val_enum_ord drop_iota add0n /x !size_cat.
    rewrite addKn !iota_add map_id filter_cat. rewrite -[RHS]cats0.
    congr (_ ++ _).
    * by rewrite /= !addnS addn0 ltnSn (ltn_trans (ltnSn _) (ltnSn _)).
    * rewrite (eq_in_filter (a2 := pred0)); first by rewrite filter_pred0.
      by move=> i; rewrite mem_iota /= leqNgt => /andP [] /negbTE => ->.
Qed.

Lemma size_cut_sizeu :
  size [seq i | i <- enum 'I_(size x) & val i < size u] = size u.
Proof.
  suff -> : [seq i | i <- enum 'I_(size x) & val i < size u]
            = take (size u) (enum 'I_(size x)).
    by rewrite size_take size_enum_ord size_cat addnS ltnS -{1}[size u]addn0 leq_add2l leq0n.
  apply (inj_map val_inj); rewrite -!map_comp map_take val_enum_ord take_iota.
  set f := (X in map X _); have {f} /eq_map -> : f =1 val by [].
  set f := (X in filter X _); have /eq_filter -> : f =1 gtn ((size u))\o val by [].
  by rewrite map_filter_comp /= val_enum_ord iotagtnk minnC map_id.
Qed.

End Swap.
End Swap.

Module NoSetContainingBoth.

Section Case.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Variable R : rel Alph.

Variable u v : word.
Variable a b : Alph.
Variable k : nat.
Let x := u ++ [:: a; b] ++ v.
Let y := u ++ [:: b; a] ++ v.

Variable P : {set {set 'I_(size x)}}.
Hypothesis Px : ksupp R (in_tuple x) k P.

Local Notation posa := (Swap.pos0 u v a b).
Local Notation posb := (Swap.pos1 u v a b).
Local Notation swapX := (@Swap.swap _ u v a b).
Local Notation swapSetX := (Swap.swapSet u v a b).

Hypothesis HnoBoth :
  forall S, S \in P -> ~ ((posa \in S) && ((posb \in S))).

Lemma Hcast : size x = size y. Proof. by rewrite !size_cat. Qed.
Definition castSet : {set 'I_(size x)} -> {set 'I_(size y)} :=
  (imset (cast_ord Hcast)) \o mem.
Let swap := (cast_ord Hcast) \o swapX.
Definition swapSet := castSet \o swapSetX .
Definition Q := imset swapSet (mem P).

Lemma swapSet_inj : injective swapSet.
Proof.
  rewrite /swapSet /castSet.
  apply inj_comp; last by apply Swap.swapSet_inj.
  apply imset_inj; by apply cast_ord_inj.
Qed.

Lemma extract_swapSet S :
  S \in P -> extract (in_tuple y) (swapSet S) = extract (in_tuple x) S.
Proof.
  move=> HS; rewrite /extract /= !extractE /=.
  rewrite (enum_cast_ord Hcast) -map_comp.
  rewrite Swap.enum_cut /x /y !map_cat !mask_cat //=; first last.
    + rewrite size_map; by apply Swap.size_cut_sizeu.
    + rewrite size_map; by apply Swap.size_cut_sizeu.
  rewrite !mem_cast.
  set s1 := (X in mask X _ ++ _); set s2 := (X in _ = mask X _ ++ _).
  have -> : s1 = s2.
    rewrite /s1 /s2 {s1 s2} -!map_comp; apply eq_in_map => i /=.
    rewrite mem_filter => /andP [] Hi _.
    by rewrite mem_cast -{1}[i](Swap.swapL Hi) /Swap.swapSet /= mem_imset_inj;
      last by apply Swap.swap_inj.
  congr (mask s2 u ++ _) => {s1 s2}.
  set s1 := (X in _ ++ mask X _); set s2 := (X in _ = _ ++ mask X _).
  have -> : s1 = s2.
    rewrite /s1 /s2 {s1 s2} -!map_comp; apply eq_in_map => i /=.
    rewrite mem_filter => /andP []; rewrite addnS addn1 => Hi _.
    by rewrite mem_cast -{1}[i](Swap.swapR Hi) /Swap.swapSet /= mem_imset_inj;
      last by apply Swap.swap_inj.
  congr (_ ++ mask s2 v) => {s1 s2}.
  have -> : posa \in [set swapX x | x in S] = (posb \in S).
    rewrite -Swap.swap1 mem_imset_inj //=; last by apply Swap.swap_inj.
  have -> : posb \in [set swapX x | x in S] = (posa \in S).
    rewrite -Swap.swap0 mem_imset_inj //=; last by apply Swap.swap_inj.
  have:= HnoBoth HS.
  by case: (posa \in S); case: (posb \in S).
Qed.

Lemma ksupp_noBoth : ksupp R (in_tuple y) k Q.
Proof.
  move: Px => /and3P [] HszP HtrivP /forallP HallP.
  apply/and3P; split.
  - by rewrite card_imset; last exact swapSet_inj.
  - rewrite /Q /swapSet imset_comp.
    apply imset_trivIset; first by apply cast_ord_inj.
    apply imset_trivIset; first by apply Swap.swap_inj.
    exact HtrivP.
  - apply/forallP => S2; apply/implyP => /imsetP [] S HS -> {S2}.
    rewrite (extract_swapSet HS).
    have:= (HallP S); by rewrite HS.
Qed.

Lemma scover_noBoth : scover P == scover Q.
Proof.
  rewrite -Swap.swap_scover.
  rewrite /Q /swapSet imset_comp /scover /=.
  apply /eqP; apply size_cover_inj.
  by apply cast_ord_inj.
Qed.

End Case.

End NoSetContainingBoth.

Lemma setU1E (T : finType) (x : T) (S : {set T}) : x \in S -> x |: S = S.
Proof.
  move=> Hx; apply/setP/subset_eqP/andP; split; apply/subsetP=> i.
  + by move/setU1P => [] ->.
  + by move=> H; apply/setU1P; right.
Qed.

Section CoverSurgery.

Variable N : nat.
Variable S : {set 'I_N}.
Variable P Q : {set {set 'I_N}}.

Lemma trivIset_coverU1 : trivIset P -> [disjoint S & cover P] -> trivIset (S |: P).
Proof.
  move=> Htriv Hdis; case (set_0Vmem S) => [-> | [] s Hs].
  + case (boolP (set0 \in P)); first by move/setU1E ->.
    apply (@trivIsetU1 _ set0 P) => //= T _.
    by rewrite -setI_eq0 set0I.
  + have HS : S \notin P.
      move: Hdis; rewrite -setI_eq0; apply contraLR => /negbNE HS.
      have {Hs} Hs : s \in S :&: cover P.
        by rewrite in_setI Hs /= /cover; apply /bigcupP; exists S.
      by apply/eqP; rewrite -setP => H; have := H s; rewrite Hs in_set0.
    move: Htriv; rewrite /trivIset big_setU1 //=.
    * move/eqP ->; rewrite {2}/cover big_setU1 //=.
      rewrite cardsU; move: Hdis; rewrite -setI_eq0 => /eqP ->.
      by rewrite cards0 subn0.
Qed.

Lemma disjoint_cover (A B : {set 'I_N}) :
  [disjoint cover P & cover Q] -> A \in P -> B \in Q -> [disjoint A & B].
Proof.
  rewrite -!setI_eq0 => /eqP; rewrite -setP => Hcov HA HB.
  apply/eqP; rewrite -setP => i; rewrite in_set0.
  apply/(sameP idP); apply(iffP idP) => //=.
  rewrite inE => /andP [] HiA HiB.
  have:= Hcov i; rewrite !inE => <-; rewrite /cover.
  apply/andP; split; apply/bigcupP.
  + by exists A.
  + by exists B.
Qed.

Lemma trivIset_coverU :
  trivIset P -> trivIset Q -> [disjoint cover P & cover Q] -> trivIset (P :|: Q).
Proof.
  move=> /trivIsetP HtrivP /trivIsetP HtrivQ Hdis; apply/trivIsetP => A B; rewrite !inE.
  move=> /orP [] HA /orP [] HB Hneq.
  + by apply HtrivP.
  + by apply disjoint_cover.
  + rewrite disjoint_sym; by apply disjoint_cover.
  + by apply HtrivQ.
Qed.

Lemma trivIset_coverD1 : trivIset P -> S \in P -> [disjoint S & cover (P :\ S)].
Proof.
  move=> /trivIsetP Htriv HS; rewrite /cover bigcup_disjoint //=.
  move=> T; rewrite inE in_set1 eq_sym => /andP [] Hneq HT.
  by apply Htriv.
Qed.

End CoverSurgery.


Section ExtractCuti.

Variable Alph : ordType.
Let word := seq Alph.
Variable N : nat.
Variable wt : N.-tuple Alph.
Variable i : 'I_N.


Lemma extract_cuti (S : {set 'I_N}) : i \in S ->
  extract wt S =
  extract wt (S :&: [set j : 'I_N | j < i]) ++
          (tnth wt i) ::
          extract wt (S :&: [set j : 'I_N | j > i]).
Proof.
  move=> Hi. admit.
Qed.

End ExtractCuti.


Module SetContainingBothLeft.

Section Case.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type u v w r : word.

Variable R : rel Alph.

Hypothesis Rtrans : transitive R.
Hypothesis NRtrans : transitive (fun a b => ~~ R a b).

Variable u v : word.
Variable a b c : Alph.

Hypothesis Hbc : R b c.
Hypothesis Hba : ~~ R b a.
Hypothesis Hxba : forall l, R l a -> R l b.

Let x := u ++ [:: b; a; c] ++ v.

Variable k : nat.
Variable P : {set {set 'I_(size x)}}.
Hypothesis Px : ksupp R (in_tuple x) k P.

Local Notation posb := (Swap.pos0 u (c :: v) b a).
Local Notation posa := (Swap.pos1 u (c :: v) b a).
Local Notation swap := (@Swap.swap _ u (c :: v) b a).
Local Notation swapSet := (Swap.swapSet u (c :: v) b a).
Lemma u2lt : (size u).+2 < size x.
Proof. by rewrite /= size_cat /= 2!addnS 2!ltnS -{1}[size u]addn0 ltn_add2l. Qed.
Let posc := Ordinal u2lt.

Lemma tnth_posc : tnth (in_tuple x) posc = c.
Proof.
  rewrite /x (tnth_nth c) nth_cat /=.
  have -> : (size u).+2 < size u = false.
    have : size u <= (size u).+2 by apply (@leq_trans (size u).+1).
    by rewrite leqNgt => /negbTE ->.
  by rewrite -add1n addnS -addSn addnK.
Qed.

Variable S : {set 'I_(size x)}.
Hypothesis HS : S \in P.
Hypothesis Hposa : (posa \in S).
Hypothesis Hposc : (posc \in S).

Lemma posbinSwap : posb \in (swapSet S).
Proof. by rewrite /swapSet /= -Swap.swap1; apply mem_imset. Qed.

Section BNotIn.

Hypothesis HbNin : posb \notin (cover P).

Lemma posbinSF : posb \in S = false.
Proof.
  apply/(sameP idP); apply(iffP idP) => //= Hb.
  move: HbNin; rewrite /cover => /bigcupP []; by exists S.
Qed.

Definition Qbnotin := imset swapSet (mem P).

Lemma scover_bnotin : scover P == scover Qbnotin.
Proof. by rewrite Swap.swap_scover. Qed.

Lemma inPQE T : T != swapSet S -> T \in Qbnotin -> T \in P.
Proof.
  rewrite /Qbnotin => Hneq /imsetP [] TP HTP Hswap; subst T.
  have {Hneq} Hneq : TP != S by move: Hneq; apply contra => /eqP ->.
  suff -> : swapSet TP = TP by [].
  rewrite /swapSet /= -setP /swap => i.
  rewrite (eq_in_imset (g := id)); first by rewrite imset_id.
  move=> {i} i /= Hi.
  have -> : (i == posb) = false.
    apply/(sameP idP); apply(iffP idP) => //= /eqP Hib; subst i.
    have Hcov : posb \in cover P by rewrite /cover; apply/bigcupP; exists TP.
    by have:= HbNin; rewrite Hcov.
  have -> : (i == posa) = false.
    apply/(sameP idP); apply(iffP idP) => //= /eqP Hib; subst i.
    move: Px; rewrite /ksupp => /and3P [] _ /trivIsetP Htriv _.
    have:= (Htriv _ _ HTP HS Hneq) => /disjoint_setI0 {Htriv}; rewrite -setP => Hdisj.
    have:= (Hdisj posa); rewrite in_set0 in_setI Hi.
    by rewrite Hposa.
  by [].
Qed.

Lemma extract_swapSet T :
  T != swapSet S -> T \in Qbnotin -> is_seq R (extract (in_tuple x) T).
Proof.
  move/inPQE => H/H{H} HT. move: Px => /and3P [] _ _ /forallP Hall.
  by have:= Hall T; rewrite HT.
Qed.

Lemma extract_SE :
  extract (in_tuple x) S =
  (extract (in_tuple x) (S :&: [set j : 'I_(size x) | j < size u])) ++
    a :: c ::
    extract (in_tuple x) (S :&: [set j : 'I_(size x) | (size u).+2 < j]).
Proof.
  rewrite (extract_cuti (in_tuple x) Hposa) /= Swap.tnth_pos1.
  set LS := (setI _ _); have {LS} -> : LS = S :&: [set j : 'I_(size x) | j < size u].
    rewrite /LS {LS} -!setIdE -setP => i; rewrite !inE.
    case: (ltnP i (size u)) => Hi; first by rewrite (ltn_trans Hi).
    case (ltnP i (size u).+1) => Hi2; last by rewrite andbF.
    have -> : i = posb by apply val_inj => /=; apply /eqP; rewrite eqn_leq Hi andbT -ltnS.
    by rewrite posbinSF.
  congr (_ ++ _ :: _).
  set LS := (setI _ _); have HposcLS : posc \in LS.
    rewrite /LS !inE /=; apply/andP; by split. 
  have /= -> :=  (extract_cuti (in_tuple x) HposcLS).
  have -> : LS :&: [set j : 'I_(size x) | j < (size u).+2] = set0.
    rewrite /LS -setP => i; rewrite !inE /=.
    apply/(sameP idP); apply(iffP idP) => //= /andP [] /andP [] Hi H1 H2.
    have := leq_ltn_trans H1 H2; by rewrite ltnn.
  have /= -> :=  (extract0 (in_tuple x)); rewrite cat0s.
  rewrite tnth_posc; congr (_ :: extractpred (in_tuple x) (mem (pred_of_set _))).
  rewrite /LS {LS HposcLS} -setP => i; rewrite !inE.
  case (ltnP (size u).+2 i) => Hi2; last by rewrite !andbF.
  by rewrite (ltn_trans (ltnSn _) Hi2) !andbT.
Qed.

Lemma extract_swapSetSE :
  extract (in_tuple x) (swapSet S) =
  (extract (in_tuple x) (S :&: [set j : 'I_(size x) | j < size u])) ++
    b :: c ::
    extract (in_tuple x) (S :&: [set j : 'I_(size x) | (size u).+2 < j]).
Proof.
  rewrite (extract_cuti (in_tuple x) posbinSwap) /=.
  set LS := (setI _ _); have {LS} -> : LS = S :&: [set j : 'I_(size x) | j < size u].
    rewrite /LS {LS} -!setIdE -setP => i; rewrite !inE.
    case: (ltnP i (size u)) => Hi; last by rewrite !andbF.
    rewrite !andbT -{1}(Swap.swapL Hi) mem_imset_inj //=.
    by apply Swap.swap_inj.
  congr (_ ++ _ :: _); first by rewrite (tnth_nth b) /= nth_cat ltnn subnn.
  set LS := (setI (imset _ _) _).
  have HposcLS : posc \in LS.
    rewrite /LS !inE /=; apply/andP; split; last by [].
    have <- : Swap.swap posc = posc by apply Swap.swapR.
    rewrite mem_imset_inj //=; by apply Swap.swap_inj.
  have /= -> :=  (extract_cuti (in_tuple x) HposcLS).
  have -> : LS :&: [set j : 'I_(size x) | j < (size u).+2] = set0.
    rewrite /LS -setP => i; rewrite !inE /=.
    case (ltnP (size u) i) => Hi; last by rewrite andbF.
    case (ltnP i (size u).+2) => Hi2; last by rewrite andbF.
    have -> : i = posa by apply val_inj => /=; apply /eqP; rewrite eqn_leq Hi andbT -ltnS.
    rewrite -Swap.swap0 mem_imset_inj //=; last by apply Swap.swap_inj.
    by rewrite posbinSF.
  have /= -> :=  (extract0 (in_tuple x)); rewrite cat0s.
  rewrite tnth_posc; congr (_ :: extractpred (in_tuple x) (mem (pred_of_set _))).
  rewrite /LS {LS HposcLS} -setP => i; rewrite !inE.
  case (ltnP (size u).+2 i) => Hi; last by rewrite !andbF.
  rewrite -{1}(Swap.swapR (ltnW Hi)) mem_imset_inj //=; last by apply Swap.swap_inj.
  rewrite andbT; congr (_ && _).
  have H2 : size u < (size u).+2 by [].
  by rewrite (ltn_trans H2 Hi).
Qed.

Lemma extract_swapSet_S : is_seq R (extract (in_tuple x) (swapSet S)).
Proof.
  rewrite extract_swapSetSE.
  have : is_seq R (extract (in_tuple x) S).
    move: Px; rewrite /ksupp => /and3P [] _ _ /forallP Hall.
    have := Hall S; by rewrite HS.
  rewrite extract_SE.
  set LL := extract _ _; set LR := extract _ _; rewrite /= => Hsort.
  have HacR := (subseq_sorted Rtrans (suffix_subseq _ _) Hsort).
  have HbcR : sorted R [:: b, c & LR] by move: HacR; rewrite /= Hbc => /andP [] _ ->.
  case: LL Hsort => [//= | LL0 LL] /=.
  rewrite !cat_path => /andP [] -> /= /and3P [] /Hxba -> _ ->.
  by rewrite Hbc.
Qed.

Lemma ksupp_bnotin : ksupp R (in_tuple x) k Qbnotin.
Proof.
  move: Px => /and3P [] HszP HtrivP /forallP HallP.
  apply/and3P; split.
  - by rewrite card_imset; last apply Swap.swapSet_inj.
  - rewrite /Qbnotin /swapSet.
    apply imset_trivIset; first by apply Swap.swap_inj.
    exact HtrivP.
  - apply/forallP => T2; apply/implyP => /imsetP [] T HT -> {T2}.
    case: (altP (T =P S)) => Heq.
    + subst T; by apply extract_swapSet_S.
    + apply extract_swapSet.
      * move: Heq; apply contra => /eqP H; apply/eqP; by apply Swap.swapSet_inj.
      * by rewrite /Qbnotin mem_imset_inj; last by apply Swap.swapSet_inj.
Qed.

Lemma Qbnotin_noboth T : T \in Qbnotin -> ~ ((posa \in T) && ((posb \in T))).
Proof.
  rewrite /Qbnotin => /imsetP [] U HU -> {T}.
  case: (altP (U =P S)) => Heq.
  + subst U; rewrite -Swap.swap0 /swapSet /=.
    rewrite mem_imset_inj; last apply Swap.swap_inj.
    by rewrite posbinSF.
  + rewrite -Swap.swap1 /swapSet /=.
    rewrite mem_imset_inj; last apply Swap.swap_inj.
    move/andP => [] _ HinU.
    move: Px => /and3P [] _ /trivIsetP Htriv _.
    have {Htriv} /disjoint_setI0 := Htriv _ _ HU HS Heq; rewrite -setP => Hdisj.
    have:= Hdisj posa; by rewrite !inE Hposa HinU.
Qed.

End BNotIn.

Section BIn.

Variable T : {set 'I_(size x)}.
Hypothesis HT : T \in P.
Hypothesis Hposb : (posb \in T).

Lemma TSneq : T != S.
Proof.
  apply/eqP=> Heq; subst T.
  move: Hba; suff -> : R b a by [].
  move: Px; rewrite /ksupp => /and3P [] _ _ /forallP Hall.
  have {Hall} := Hall S; rewrite HS => Hsort.
  have {Hsort} := is_seq_extract_cond Rtrans [set posb; posa] Hsort.
  have -> : S :&: [set posb; posa] = [set posb; posa].
    apply/setP/subset_eqP/andP; split; apply/subsetP=> i; first by rewrite inE => /andP [].
    rewrite !inE => /orP [] => /eqP ->; rewrite eq_refl /=; first by rewrite Hposb.
    by rewrite Hposa orbT.
  have /extract2 -> : posb < posa by [].
  by rewrite Swap.tnth_pos0 Swap.tnth_pos1 /= andbT.
Qed.

Lemma TS_disjoint : [disjoint S & T].
Proof.
  move: Px => /and3P [] _ /trivIsetP Hdisj _.
  have:= (Hdisj _ _ HT HS TSneq); by rewrite disjoint_sym.
Qed.

Definition S1 := (S :&: [set j : 'I_(size x) | j <= posa])
                   :|: (T :&: [set j : 'I_(size x) | j > posc]).
Definition T1 := (T :&: [set j : 'I_(size x) | j <= posb])
                   :|: (S :&: [set j : 'I_(size x) | j >= posc]).

Lemma S1_subsST : S1 \subset (S :|: T).
Proof.
  apply/subsetP=> i; by rewrite /S1 !inE => /orP [] /andP [] -> _; last by rewrite orbT.
Qed.

Lemma T1_subsST : T1 \subset (S :|: T).
Proof.
  apply/subsetP=> i; by rewrite /S1 !inE => /orP [] /andP [] -> _; first by rewrite orbT.
Qed.

Lemma coverS1T1 : cover [set S1; T1] =  (S :|: T).
Proof.
  rewrite /cover bigcup_setU !bigcup_set1.
  apply/setP/subset_eqP/andP; split; apply/subsetP=> i; rewrite !inE.
  - move/or3P => [/orP [] | | ] /andP [] -> _ //=; by rewrite orbT.
  - move/orP => [] Hi; rewrite Hi /=.
    + by case (ltnP (size u).+1 i); first rewrite !orbT.
    + case (leqP i (size u)) => Hiu; first by rewrite orbT.
      rewrite /=; apply/orP; left; apply/orP; right.
      have:= TS_disjoint => /disjoint_setI0; rewrite -setP => Hdisj.
      case: (ltnP (size u).+2 i) => //= Hi2.
      case: (ltnP (size u).+1 i) => Hi1.
      - have Htmp : i = posc by apply val_inj => /=; apply /eqP; rewrite eqn_leq Hi2 Hi1.
        subst i => {Hi1 Hi2 Hiu}.
        have:= (Hdisj posc); by rewrite in_set0 in_setI Hi Hposc.
      - have Htmp : i = posa by apply val_inj => /=; apply /eqP; rewrite eqn_leq Hiu Hi1.
        subst i => {Hi1 Hi2 Hiu}.
        have:= (Hdisj posa); by rewrite in_set0 in_setI Hi Hposa.
Qed.

Lemma disjointS1T1 : [disjoint S1 & T1].
Proof.
  rewrite -setI_eq0; apply/eqP; rewrite -setP => i; rewrite in_set0.
  apply/(sameP idP); apply(iffP idP) => //=.
  rewrite /S1 /T1 !inE => /andP [].
  have:= TS_disjoint => /disjoint_setI0; rewrite -setP => Hdisj.
  move=> /orP [] /andP [] Hi1 /= H1 /orP [] /andP [] Hi2 /= H2.
  + have:= Hdisj i; by rewrite inE Hi1 Hi2 in_set0.
  + have:= leq_trans H2 H1; by rewrite ltnn.
  + have Hu2:= ltn_trans (ltnSn (size u)) (ltnSn _).
    have:= leq_ltn_trans H2 (ltn_trans Hu2 H1); by rewrite ltnn.
  + have:= Hdisj i; by rewrite inE Hi1 Hi2 in_set0.
Qed.

Lemma ST_cover_disjoint : [disjoint S :|: T & cover (P :\: [set S; T])].
Proof.
  rewrite -setI_eq0; apply/eqP; rewrite -setP => i; rewrite in_set0.
  apply/(sameP idP); apply(iffP idP) => //=.
  move: Px; rewrite /ksupp => /and3P [] _ /trivIsetP Htriv _.
  rewrite !inE => /andP [] /orP [] Hi /bigcupP [] U;
    rewrite !inE negb_or => /andP [] /andP [] HUS HUT HU HiU.
  + have:= Htriv _ _ HU HS HUS; rewrite -setI_eq0 => /eqP; rewrite -setP => Hdisj.
    have:= Hdisj i; by rewrite in_set0 !inE Hi HiU.
  + have:= Htriv _ _ HU HT HUT; rewrite -setI_eq0 => /eqP; rewrite -setP => Hdisj.
    have:= Hdisj i; by rewrite in_set0 !inE Hi HiU.
Qed.

Definition Qbin :=  [set S1; T1] :|: (P :\: [set S; T]).

Lemma trivIset_Qbin : trivIset Qbin.
Proof.
  apply trivIset_coverU.
  + apply/trivIsetP => A B; rewrite !inE => /orP [] /eqP -> /orP [] /eqP -> //=.
    * by rewrite eq_refl.
    * move=> _; by apply disjointS1T1.
    * move=> _; rewrite disjoint_sym; by apply disjointS1T1.
    * by rewrite eq_refl.
  + apply (@trivIsetS _ _ P); first by apply subsetDl.
    move: Px; by rewrite /ksupp => /and3P [] _.
  + rewrite coverS1T1; apply ST_cover_disjoint.
Qed.

Lemma cover_bin : cover Qbin = cover P.
Proof.
  have:= coverS1T1; rewrite /Qbin /cover !bigcup_setU => ->.
  apply/setP/subset_eqP/andP; split; apply/subsetP=> i.
  - rewrite !inE => /orP []; first move=> /orP [].
    + move=> Hi; apply/bigcupP; by exists S.
    + move=> Hi; apply/bigcupP; by exists T.
    + move/bigcupP => [] U; rewrite inE => /andP [] _ HU Hi.
      apply/bigcupP; by exists U.
  - move/bigcupP => [] U HU Hi; rewrite !inE.
    case (altP (U =P S)) => HUS; last case (altP (U =P T)) => HUT.
    + subst U; by rewrite Hi.
    + subst U; by rewrite Hi orbT.
    + apply/orP; right; apply/bigcupP.
      exists U; last exact Hi.
      by rewrite !inE negb_or HUS HUT HU.
Qed.

Lemma extract_S1 : is_seq R (extract (in_tuple x) S1).
Proof.
  admit.
Qed.

Lemma extract_T1 : is_seq R (extract (in_tuple x) T1).
Proof.
  admit.
Qed.

Lemma ksupp_bin : ksupp R (in_tuple x) k Qbin.
Proof.
  move: Px => /and3P [] HszP HtrivP /forallP HallP.
  rewrite /Qbin; apply/and3P; split.
  - move: HszP.
    rewrite -setDDl (cardsD1 S P) (cardsD1 T (P :\ S)) HS /=.
    have -> /= : T \in P :\ S by rewrite !inE TSneq HT.
    apply leq_trans; rewrite addnA add1n.
    apply (leq_trans (leq_card_setU _ _)); rewrite leq_add2r.
    apply (leq_trans (leq_card_setU _ _)); by rewrite !cards1.
  - by apply trivIset_Qbin.
  - apply/forallP => U; apply/implyP; rewrite !inE => /orP []; first move => /orP [].
    + move/eqP => H; subst U; by apply extract_S1.
    + move/eqP => H; subst U; by apply extract_T1.
    + rewrite negb_or => /andP [] _ HU; have := HallP U; by rewrite HU /=.
Qed.

Lemma Qbin_noboth U : U \in Qbnotin -> ~ ((posa \in U) && ((posb \in U))).
Proof.
  admit.
Qed.

End BIn.
End Case.
End SetContainingBothLeft.







Section GreenInvariants.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Notation "a =Pl b" := (plactcongr a b) (at level 70).

Definition ksupp_inj R k u1 u2 :=
  forall s1, ksupp R (in_tuple (u1)) k s1 ->
             exists s2, (scover s1 == scover s2) && ksupp R (in_tuple (u2)) k s2.

Lemma leq_green R k u1 u2 : ksupp_inj R k u1 u2 -> green_rel R u1 k <= green_rel R u2 k.
Proof.
  move=> Hinj; rewrite /= /green_rel /green_rel_t.
  set P1 := ksupp R (in_tuple u1) k.
  have : #|P1| > 0.
    rewrite -cardsE card_gt0; apply/set0Pn.
    exists set0; rewrite in_set; by apply ksupp0.
  move/(eq_bigmax_cond scover) => [] ks1 Hks1 ->.
  have := Hinj _ Hks1 => [] [] ks2 /andP [] /eqP -> Hks2.
  by apply leq_bigmax_cond.
Qed.

Lemma ksupp_inj_plact1 u v1 w v2 k :
  v2 \in plact1 v1 -> ksupp_inj (gtnX Alph) k (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof.
  move/plact1P => [] a [] b [] c [] Hord -> -> {v1 v2}.
  rewrite /ksupp_inj  => S1 Hsupp.
(*  set t1 := (u ++ [:: a; c; b] ++ w); set t2 := (u ++ [:: c; a; b] ++ w). *)
  pose posa := Ordinal (Swap.ult u (b :: w) a c).
  pose posc := Ordinal (Swap.u1lt u (b :: w) a c).
  case (boolP [exists S, [&& S \in S1, posa \in S & posc \in S] ]).
  + move/existsP => [] S /and3P [] HSin HSa HSb.
    exfalso; move: Hsupp; rewrite /ksupp => /and3P [] _ _ /forallP Hall.
    have Htrans: transitive (gtnX Alph) by move=> d e f /= H1 H2; apply (ltnX_trans H2 H1).
    have:= Hall S; rewrite HSin /= {Hall} => Hsort.
    have:= is_seq_extract_cond Htrans [set posa; posc] Hsort.
    have -> : S :&: [set posa; posc] = [set posa; posc].
      apply/setP/subset_eqP/andP; split; apply/subsetP=> i; first by rewrite inE => /andP [].
      rewrite !inE => /orP [] => /eqP ->; rewrite eq_refl /=; first by rewrite HSa.
      by rewrite HSb orbT.
    have /extract2 -> : posa < posc by [].
    rewrite !(tnth_nth b) /= andbT.
    elim u => [| u0 u'] /=.
    - move: Hord => /andP [] /leqX_ltnX_trans H/H{H} /ltnXW.
      by rewrite leqXNgtnX => /negbTE ->.
    - by apply.
  + rewrite negb_exists => /forallP Hall.
    exists (NoSetContainingBoth.Q S1); rewrite NoSetContainingBoth.scover_noBoth /=.
    apply NoSetContainingBoth.ksupp_noBoth; first exact Hsupp.
    move=> S HS; have:= Hall S; by rewrite HS /= => /negbTE ->.
Qed.

Lemma ksupp_inj_plact1i u v1 w v2 k :
  v2 \in plact1i v1 -> ksupp_inj (gtnX Alph) k (in_tuple (u ++ v1 ++ w)) (in_tuple (u ++ v2 ++ w)).
Proof.
  admit.
Qed.

Lemma ksupp_inj_plact2 u v1 w v2 k :
  v2 \in plact2 v1 -> ksupp_inj (gtnX Alph) k (in_tuple (u ++ v1 ++ w)) (in_tuple (u ++ v2 ++ w)).
Proof.
  admit.
Qed.
Lemma ksupp_inj_plact2i u v1 w v2 k :
  v2 \in plact2i v1 -> ksupp_inj (gtnX Alph) k (in_tuple (u ++ v1 ++ w)) (in_tuple (u ++ v2 ++ w)).
Proof.
  admit.
Qed.

Lemma invar_plact1 u v1 w v2 k :
  v2 \in plact1 v1 -> (greenCol (u ++ v1 ++ w)) k = (greenCol (u ++ v2 ++ w)) k.
Proof.
  move=> Hpl; apply/eqP; rewrite eqn_leq; apply/andP; split; apply leq_green.
  + by apply ksupp_inj_plact1.
  + apply ksupp_inj_plact1i; by rewrite -plact1I.
Qed.

Lemma invar_plact1i u v1 w v2 k :
  v2 \in plact1i v1 -> (greenCol (u ++ v1 ++ w)) k = (greenCol (u ++ v2 ++ w)) k.
Proof. by rewrite -plact1I => H; apply esym; apply invar_plact1. Qed.

Lemma invar_plact2 u v1 w v2 k :
  v2 \in plact2 v1 -> (greenCol (u ++ v1 ++ w)) k = (greenCol (u ++ v2 ++ w)) k.
Proof.
  move=> Hpl; apply/eqP; rewrite eqn_leq; apply/andP; split; apply leq_green.
  + by apply ksupp_inj_plact2.
  + apply ksupp_inj_plact2i; by rewrite -plact2I.
Qed.

Lemma invar_plact2i u v1 w v2 k :
  v2 \in plact2i v1 -> (greenCol (u ++ v1 ++ w)) k = (greenCol (u ++ v2 ++ w)) k.
Proof. by rewrite -plact2I => H; apply esym; apply invar_plact2. Qed.

Theorem plactic_greenCol_inv u v : u =Pl v -> forall k, greenCol u k = greenCol v k.
Proof.
  move=> Hpl k.
  move: v Hpl; apply gencongr_ind; first by apply erefl.
  move=> a b1 c b2 -> {u} /plactruleP [].
  + apply invar_plact1.
  + apply invar_plact1i.
  + apply invar_plact2.
  + apply invar_plact2i.
Qed.

Corollary plactic_shapeRS u v : u =Pl v -> shape (RS u) = shape (RS v).
Proof.
  move=> Hpl.
  suff HeqRS k : greenCol (to_word (RS u)) k = greenCol (to_word (RS v)) k
    by apply (greenCol_tab_eq_shape (is_tableau_RS u) (is_tableau_RS v) HeqRS).
  have <- := plactic_greenCol_inv (congr_Sch u) k.
  have <- := plactic_greenCol_inv (congr_Sch v) k.
  by apply plactic_greenCol_inv.
Qed.

Theorem plact_Sch u v : plactcongr u v <-> RS u == RS v.
Proof.
  split; last by apply Sch_plact.
  move Hu : (size u) => n Hpl.
  have:= perm_eq_size (gencongr_homog Hpl) => /esym; rewrite Hu.
  elim: n u v Hpl Hu => [| n IHn] u v;
    first by move=> _ /eqP/nilP -> /eqP/nilP ->; rewrite /RS.
  move=> Hpl Hu Hv.
  have:= size_rembig u; rewrite Hu /= => Hszu.
  have:= size_rembig v; rewrite Hv /= => Hszv.
  have {IHn} := IHn _ _ (rembig_plactcongr Hpl) Hszu Hszv => /eqP {Hszu Hszv}.
  case: u Hu Hpl => [//= | u0 u'] _.
  case: v Hv     => [//= | v0 v'] _ => Hpl Hplrem.
  have:= rembig_RS u0 u' => [] [] iu Hiu.
  have:= rembig_RS v0 v' => [] [] iv; rewrite -Hplrem {Hplrem} => Hiv.
  rewrite -(maxL_perm_eq (gencongr_homog Hpl)) in Hiv.
  have:= plactic_shapeRS Hpl.
  rewrite Hiu Hiv {Hiu Hiv} !shape_append_nth => H.
  by rewrite -(incr_nth_inj H).
Qed.

End GreenInvariants.
