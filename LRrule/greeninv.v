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


Lemma eq_size (T : Type) (w1 w2 : seq T) : w1 = w2 -> size w1 = size w2.
Proof. by move->. Qed.

Lemma ksupp_cast (T : ordType) R (w1 w2 : seq T) (H : w1 = w2) k Q :
  ksupp R (in_tuple w1) k Q ->
  ksupp R (in_tuple w2) k ((cast_set (eq_size H)) @: Q).
Proof.
  subst w1; rewrite /=.
  suff /eq_imset -> : cast_set (eq_size (erefl w2)) =1 id by rewrite imset_id.
  move=> U; rewrite /cast_set /=.
  suff /eq_imset -> : cast_ord (eq_size (erefl w2)) =1 id by rewrite imset_id.
  move=> i; by rewrite cast_ord_id.
Qed.

Open Scope bool.

Section GreenInj.

Variable T1 T2 : ordType.
Variable R1 : rel T1.
Variable R2 : rel T2.

Definition ksupp_inj k (u1 : seq T1) (u2 : seq T2) :=
  forall s1, ksupp R1 (in_tuple u1) k s1 ->
             exists s2, (scover s1 == scover s2) && ksupp R2 (in_tuple u2) k s2.

Lemma leq_green k (u1 : seq T1) (u2 : seq T2) :
  ksupp_inj k u1 u2 -> green_rel R1 u1 k <= green_rel R2 u2 k.
Proof.
  move=> Hinj; rewrite /= /green_rel /green_rel_t.
  set P1 := ksupp R1 (in_tuple u1) k.
  have : #|P1| > 0.
    rewrite -cardsE card_gt0; apply/set0Pn.
    exists set0; rewrite in_set; by apply ksupp0.
  move/(eq_bigmax_cond scover) => [] ks1 Hks1 ->.
  have := Hinj _ Hks1 => [] [] ks2 /andP [] /eqP -> Hks2.
  by apply leq_bigmax_cond.
Qed.

End GreenInj.

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
  move=> Hi; rewrite /extract /= extractIE.
  rewrite -{1}[enum 'I_N](cat_take_drop i.+1) drop_enumI take_enumI filter_cat map_cat.
  rewrite -{1}[enum 'I_N](cat_take_drop i) drop_enumI take_enumI !filter_cat map_cat.
  rewrite -cat1s catA -!filter_predI; congr (((map (tnth wt) _) ++ _) ++ (map (tnth wt) _)).
  + set pl := (X in filter X _); set pr := (X in _ = filter X _).
    suff /eq_filter -> : pl =1 pr by [].
    rewrite /pl /pr {pl pr} => j /=; rewrite !inE !andbT.
    congr ((j \in S) && _); case (ltnP j i) => H; last by rewrite andbF.
    by rewrite (ltn_trans H (ltnSn i)).
  + set l := (X in map _ X); suff -> : l = [:: i] by [].
    rewrite /l {l}; set pl := (X in filter X _).
    have {pl} /eq_filter -> : pl =1 (pred1 i).
      rewrite /pl {pl} => j /=; rewrite ltnS -eqn_leq inE andbT.
      case: (altP (j =P i)) => [-> | H]; first by rewrite eq_refl Hi.
      suff -> : (val j == val i) = false by rewrite andbF.
        apply/negbTE; move: H; apply contra; by move/eqP/val_inj ->.
    apply filter_pred1_uniq; first by rewrite -enumT; apply enum_uniq.
    by rewrite -enumT mem_enum inE.
  + set pl := (X in filter X _); set pr := (X in _ = filter X _).
    suff /eq_filter -> : pl =1 pr by [].
    rewrite /pl /pr {pl pr} => j /=; by rewrite !inE !andbT.
Qed.

End ExtractCuti.


Section Duality.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Variable w : word.
Variable k : nat.

Definition rev_ord_cast : 'I_(size w) -> 'I_(size (revdual _ w)) :=
  (cast_ord (size_revdual w)) \o (@rev_ord _).
Definition revSet (s : {set 'I_(size w)}) : {set 'I_(size (revdual _ w))} :=
  [set rev_ord_cast i | i in s].
Definition rev_ksupp (P : {set {set 'I_(size w)}}) : {set {set 'I_(size (revdual _ w))}} :=
  [set revSet u | u in P].

Definition rev_ksupp_inv (S : {set {set 'I_(size (revdual _ w))}}) :=
  [set rev_ord_cast @^-1: s | s : {set 'I_(size (revdual _ w))} in S].

Lemma rev_ord_cast_inj : injective rev_ord_cast.
Proof. move=> i j; by rewrite /rev_ord_cast /= => /cast_ord_inj/rev_ord_inj. Qed.

Lemma revSet_inj : injective revSet.
Proof. move=> i j /=; rewrite /revSet; apply imset_inj; exact rev_ord_cast_inj. Qed.


Lemma rev_ksuppK S : S = rev_ksupp_inv (rev_ksupp S).
Proof.
  rewrite /rev_ksupp_inv /rev_ksupp -imset_comp; set f := (X in imset X _).
  suff /eq_imset -> : f =1 id by rewrite imset_id.
  rewrite /f {f} /revSet => s /=.
  apply/setP/subset_eqP/andP; split; apply/subsetP=> i; rewrite inE;
   by rewrite mem_imset_inj; last exact rev_ord_cast_inj.
Qed.

Lemma rev_ksuppKV S : S = rev_ksupp (rev_ksupp_inv S).
Proof.
  rewrite /rev_ksupp_inv /rev_ksupp -imset_comp; set f := (X in imset X _).
  suff /eq_imset -> : f =1 id by rewrite imset_id.
  rewrite /f {f} /revSet => s /=.
  apply/setP/subset_eqP/andP; split; apply/subsetP=> i.
  + move=> /imsetP [] t; rewrite inE => Ht Hi; by subst i.
  + move=> Hi; apply/imsetP.
    exists (rev_ord ((cast_ord (esym (size_revdual w))) i)).
    * by rewrite /rev_ord_cast inE /= rev_ordK cast_ordKV.
    * by rewrite /rev_ord_cast /= rev_ordK cast_ordKV.
Qed.

Lemma irev_w i : i < size w -> size w - i.+1 < size w.
Proof. move/subnSK ->; by apply leq_subr. Qed.

Lemma rev_enum :
  enum 'I_(size (revdual _ w)) = rev [seq rev_ord_cast i | i <- enum 'I_(size w)].
Proof.
  apply (inj_map val_inj); rewrite /=.
  rewrite val_enum_ord map_rev -map_comp.
  set f := (_ \o _);  have /eq_map -> : f =1 (fun i => size w - i.+1) \o val by [].
  rewrite {f} map_comp val_enum_ord size_rev size_map.
  apply (eq_from_nth (x0 := 0)); first by rewrite size_rev size_map.
  move=> i; rewrite size_iota => Hi; rewrite nth_rev; last by rewrite size_map size_iota.
  rewrite (nth_iota _ Hi) add0n size_map (nth_map 0);
    last by rewrite size_iota; apply irev_w.
  rewrite size_iota (nth_iota _ (irev_w Hi)).
  rewrite add0n (subnSK Hi); by rewrite subKn; last by apply ltnW.
Qed.

Lemma extract_revSet S :
  (extract (in_tuple (revdual Alph w))) (revSet S) = revdual Alph (extract (in_tuple w) S).
Proof.
  rewrite !/extract /= !extractIE /revSet rev_enum.
  rewrite filter_rev filter_map.
  set f := (X in filter X _); have /eq_filter -> : f =1 (fun i => i \in S).
    by move=> i; rewrite /f {f} /= mem_imset_inj; last exact rev_ord_cast_inj.
  rewrite {f} map_rev -!map_comp; congr (rev _).
  apply eq_map => i /=; rewrite !(tnth_nth (inhabitant Alph)) /=.
  rewrite -map_rev -{4}[w]revK nth_rev size_rev; last by apply ltn_ord.
  rewrite (nth_map (inhabitant Alph)); first by [].
  rewrite size_rev; apply irev_w; by apply ltn_ord.
Qed.

Lemma is_row_dual T :
  is_seq (leqX Alph) (extract (in_tuple w) T) <->
  is_seq (leqX (dual_ordType Alph)) (extract (in_tuple (revdual Alph w)) (revSet T)).
Proof.
  rewrite extract_revSet.
  case: (extract _ _) => [//= | l0 l] /=.
  rewrite -rev_sorted revK /sorted.
  suff <- : l = [seq to_dual i | i <- l] by [].
  by rewrite map_id.
Qed.

Lemma is_col_dual T :
  is_seq (gtnX Alph) ((extract (in_tuple w)) T) <->
  is_seq (gtnX (dual_ordType Alph)) (extract (in_tuple (revdual Alph w)) (revSet T)).
Proof.
  rewrite extract_revSet.
  case: (extract _ _) => [//= | l0 l] /=.
  rewrite -rev_sorted revK /sorted /=.
  rewrite (map_path (e' := (gtnX Alph)) (b := pred0)); first by [].
  + rewrite /rel_base => x y _.
    by rewrite /gtnX /= dual_ltnX.
  + by rewrite has_pred0.
Qed.

Lemma size_rev_ksupp P : #|rev_ksupp P| = #|P|.
Proof. by rewrite card_imset; last by apply revSet_inj. Qed.

Lemma trivIset_setrev P : trivIset P = trivIset [set revSet u | u in P].
Proof.
  apply/(sameP idP); apply(iffP idP).
  + move/(preimset_trivIset rev_ord_cast_inj).
    by rewrite {2}[P]rev_ksuppK.
  + by apply imset_trivIset; exact rev_ord_cast_inj.
Qed.

Lemma rev_is_ksupp_row P :
  ksupp (leqX Alph) (in_tuple w) k P =
  ksupp (leqX (dual_ordType Alph)) (in_tuple (revdual _ w)) k (rev_ksupp P).
Proof.
  rewrite /ksupp size_rev_ksupp trivIset_setrev; congr [&& _, _ & _].
  apply/(sameP idP); apply(iffP idP) => /forallP Hall; apply/forallP => S; apply/implyP.
  * move=> HS; have:= Hall (revSet S).
    have -> : (revSet S \in [set revSet u | u in P])
      by rewrite mem_imset_inj; last exact revSet_inj.
    by rewrite is_row_dual.
  * move=> /imsetP [] T HT -> {S}.
    rewrite -is_row_dual.
    have:= Hall T; by rewrite HT.
Qed.

Lemma rev_is_ksupp_col P :
  ksupp (gtnX Alph) (in_tuple w) k P =
  ksupp (gtnX (dual_ordType Alph)) (in_tuple (revdual _ w)) k (rev_ksupp P).
Proof.
  rewrite /ksupp size_rev_ksupp trivIset_setrev; congr [&& _, _ & _].
  apply/(sameP idP); apply(iffP idP) => /forallP Hall; apply/forallP => S; apply/implyP.
  * move=> HS; have:= Hall (revSet S).
    have -> : (revSet S \in [set revSet u | u in P])
      by rewrite mem_imset_inj; last exact revSet_inj.
    by rewrite is_col_dual.
  * move=> /imsetP [] T HT -> {S}.
    rewrite -is_col_dual.
    have:= Hall T; by rewrite HT.
Qed.

Lemma scover_rev P : scover (rev_ksupp P) = scover P.
Proof. by rewrite !/scover /= -size_cover_inj; last exact rev_ord_cast_inj. Qed.

Lemma greenCol_dual : greenCol w k = greenCol (revdual _ w) k.
Proof.
  rewrite /greenCol /=.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - apply (@leq_green _ (dual_ordType _)).
    rewrite /ksupp_inj => S HS; exists (rev_ksupp S).
    by rewrite scover_rev eq_refl /= -rev_is_ksupp_col.
  - apply (@leq_green (dual_ordType _) _).
    rewrite /ksupp_inj => S HS.
    pose U := rev_ksupp_inv S.
    exists U; rewrite [S]rev_ksuppKV /U scover_rev eq_refl /=.
    by move: HS; rewrite {1}[S]rev_ksuppKV -rev_is_ksupp_col.
Qed.

Lemma greenRow_dual : greenRow w k = greenRow (revdual _ w) k.
Proof.
  rewrite /greenCol /=.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - apply (@leq_green _ (dual_ordType _)).
    rewrite /ksupp_inj => S HS; exists (rev_ksupp S).
    by rewrite scover_rev eq_refl /= -rev_is_ksupp_row.
  - apply (@leq_green (dual_ordType _) _).
    rewrite /ksupp_inj => S HS.
    pose U := rev_ksupp_inv S.
    exists U; rewrite [S]rev_ksuppKV /U scover_rev eq_refl /=.
    by move: HS; rewrite {1}[S]rev_ksuppKV -rev_is_ksupp_row.
Qed.

End Duality.

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
    rewrite addKn !iota_add map_id filter_cat -[RHS]cats0.
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
  forall S, S \in P -> ~ ((posa \in S) && (posb \in S)).

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
  move=> HS; rewrite /extract /= !extractmaskE /=.
  rewrite (enum_cast_ord Hcast) -map_comp.
  rewrite Swap.enum_cut /x /y !map_cat !mask_cat //=; first last.
    + rewrite size_map; by apply Swap.size_cut_sizeu.
    + rewrite size_map; by apply Swap.size_cut_sizeu.
  rewrite !mem_cast.
  congr (mask _ u ++ _ ++ mask _ v).
  + rewrite -!map_comp; apply eq_in_map => i /=.
    rewrite mem_filter => /andP [] Hi _.
    by rewrite mem_cast -{1}[i](Swap.swapL Hi) /Swap.swapSet /= mem_imset_inj;
      last by apply Swap.swap_inj.
  + rewrite -{1}Swap.swap1 mem_imset_inj //=; last by apply Swap.swap_inj.
    rewrite -{2 3}Swap.swap0 mem_imset_inj //=; last by apply Swap.swap_inj.
    have:= HnoBoth HS; by case: (posa \in S); case: (posb \in S).
  + rewrite -!map_comp; apply eq_in_map => i /=.
    rewrite mem_filter => /andP []; rewrite addnS addn1 => Hi _.
    by rewrite mem_cast -{1}[i](Swap.swapR Hi) /Swap.swapSet /= mem_imset_inj;
      last by apply Swap.swap_inj.
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


Module SetContainingBothLeft.

Section Case.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type u v w r : word.

Variable R : rel Alph.
Variable u v : word.
Variable a b c : Alph.

Record hypRabc := HypRabc {
                      Rtrans : transitive R;
                      Hbc : R b c;
                      Hba : ~~ R b a;
                      Hxba : forall l, R l a -> R l b;
                      Hbax : forall l, R b l -> R a l
                  }.

Hypothesis HRabc : hypRabc.

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
  have HacR := subseq_sorted (Rtrans HRabc) (suffix_subseq _ _) Hsort.
  have HbcR : sorted R [:: b, c & LR] by move: HacR; rewrite /= (Hbc HRabc)=> /andP [] _ ->.
  case: LL Hsort => [//= | LL0 LL] /=.
  rewrite !cat_path => /andP [] -> /= /and3P [] /(Hxba HRabc) -> _ ->.
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

Lemma Qbnotin_noboth T : T \in Qbnotin -> ~ ((posa \in T) && (posc \in T)).
Proof.
  rewrite /Qbnotin => /imsetP [] U HU -> {T}.
  case: (altP (U =P S)) => Heq.
  + subst U; rewrite -Swap.swap0 /swapSet /=.
    rewrite mem_imset_inj; last apply Swap.swap_inj.
    by rewrite posbinSF.
  + rewrite -Swap.swap0 /swapSet /=.
    rewrite mem_imset_inj; last apply Swap.swap_inj.
    move/andP => [] Hb _; move: HbNin.
    by have -> : posb \in cover P by rewrite /cover; apply/bigcupP; exists U.
Qed.

End BNotIn.

Section BIn.

Variable T : {set 'I_(size x)}.
Hypothesis HT : T \in P.
Hypothesis Hposb : (posb \in T).

Lemma TSneq : T != S.
Proof.
  apply/eqP=> Heq; subst T.
  have:= Hba HRabc; suff -> : R b a by [].
  move: Px; rewrite /ksupp => /and3P [] _ _ /forallP Hall.
  have {Hall} := Hall S; rewrite HS => Hsort.
  have {Hsort} := is_seq_extract_cond (Rtrans HRabc) [set posb; posa] Hsort.
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

Lemma posb_inSF : (posb \in S) = false.
Proof.
  have:= TS_disjoint; rewrite -setI_eq0 => /eqP; rewrite -setP => H.
  have:= H posb; by rewrite in_set0 !inE Hposb andbT.
Qed.

Lemma posa_inTF : (posa \in T) = false.
Proof.
  have:= TS_disjoint; rewrite -setI_eq0 => /eqP; rewrite -setP => H.
  have:= H posa; by rewrite in_set0 !inE Hposa.
Qed.

Lemma posc_inTF : (posc \in T) = false.
Proof.
  have:= TS_disjoint; rewrite -setI_eq0 => /eqP; rewrite -setP => H.
  have:= H posc; by rewrite in_set0 !inE Hposc.
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

Lemma enumUltV (U V : {set 'I_(size x)}) d :
  (forall l, l \in U -> l <= d) ->
  (forall l, l \in V -> l > d) ->
  enum (mem (U :|: V)) = enum U ++ enum V.
Proof.
  move => HU HV; rewrite /enum_mem /= -enumT /=.
  rewrite -{1}[enum 'I_(size x)](cat_take_drop d.+1) drop_enumI take_enumI filter_cat.
  congr (_ ++ _); rewrite -filter_predI; apply eq_filter => i /=; rewrite !inE.
  + rewrite ltnS; case: (boolP (i \in U)) => HiU /=; first by rewrite HU.
    case: (boolP (i \in V)) => HiV //=.
    have:= HV _ HiV; by rewrite ltnNge => /negbTE ->.
  + case: (boolP (i \in V)) => HiV /=; first by rewrite orbT HV.
    case: (boolP (i \in U)) => HiU //=.
    have:= HU _ HiU; by rewrite ltnNge => ->.
Qed.

Lemma extract_S1E :
  extract (in_tuple x) S1 =
  extract (in_tuple x) (S :&: [set j : 'I_(size x) | j <= posa]) ++
  extract (in_tuple x) (T :&: [set j : 'I_(size x) | j > posc]).
Proof.
  rewrite /S1 /extract /= /extractpred (enumUltV (d := posa)); first by rewrite map_cat.
  + by move=> i; rewrite !inE => /andP [] _ Hi.
  + move=> i; rewrite !inE => /andP [] _ Hi /=.
    by apply (ltn_trans (ltnSn _)).
Qed.

Lemma extract_T1E :
  extract (in_tuple x) T1 =
  extract (in_tuple x) (T :&: [set j : 'I_(size x) | j <= posb]) ++
  extract (in_tuple x) (S :&: [set j : 'I_(size x) | j >= posc]).
Proof.
  rewrite /T1 /extract /= /extractpred (enumUltV (d := posb)); first by rewrite map_cat.
  + by move=> i; rewrite !inE => /andP [] _ Hi.
  + move=> i; rewrite !inE => /andP [] _ Hi /=.
    by apply (ltn_trans (ltnSn _)).
Qed.

Lemma extract_Sa:
  extract (in_tuple x) (S :&: [set j : 'I_(size x) | j <= posa]) =
  rcons (extract (in_tuple x) (S :&: [set j : 'I_(size x) | j < posa])) a.
Proof.
  set S' := (X in extract _ X).
  have : posa \in S' by rewrite /S' !inE leqnn Hposa.
  rewrite /S'; move /extract_cuti ->; rewrite -cats1 -{21}[[:: a]]cats0 -[tnth _ _ :: _]cat1s.
  congr ((extract (in_tuple x) _) ++ _ ++ _).
  + rewrite -setP => i; rewrite !inE.
    case (boolP (i \in S)) => //= _.
    case: (ltnP i (size u).+1); last by rewrite andbF.
    by move/ltnW ->.
  + rewrite (tnth_nth a) /x /=; by elim: u.
  + set s := (X in extract _ X); suff -> : s = set0 by rewrite extract0.
    rewrite /s {s} -setP => i; rewrite !inE -andbA.
    apply/(sameP idP); apply(iffP idP) => //= /and3P [] _ H1 H2.
    have:= leq_trans H2 H1; by rewrite ltnn.
Qed.

Lemma extract_cS:
  extract (in_tuple x) (S :&: [set j : 'I_(size x) | j >= posc]) =
  c :: extract (in_tuple x) (S :&: [set j : 'I_(size x) | j > posc]).
Proof.
  set S' := (X in extract _ X).
  have : posc \in S' by rewrite !inE leqnn Hposc.
  move /extract_cuti ->; rewrite -cat1s -[RHS]cat1s -[RHS]cat0s.
  congr (_ ++ _ ++ (extract (in_tuple x) _)).
  + set s := (X in extract _ X); suff -> : s = set0 by rewrite extract0.
    rewrite /s {s} -setP => i; rewrite !inE -andbA.
    apply/(sameP idP); apply(iffP idP) => //= /and3P [] _ H1 H2.
    have:= leq_trans H2 H1; by rewrite ltnn.
  + rewrite (tnth_nth a) /x /=; by elim: u.
  + rewrite -setP => i; rewrite !inE.
    case (boolP (i \in S)) => //= _.
    case: (ltnP (size u).+2 i); last by rewrite andbF.
    by move/ltnW ->.
Qed.

Lemma extract_Tb:
  extract (in_tuple x) (T :&: [set j : 'I_(size x) | j <= posb]) =
  rcons (extract (in_tuple x) (T :&: [set j : 'I_(size x) | j < posb])) b.
Proof.
  set T' := (X in extract _ X).
  have : posb \in T' by rewrite /T' !inE leqnn Hposb.
  move /extract_cuti ->; rewrite -cats1 -[[:: b]]cats0 -[tnth _ _ :: _]cat1s.
  congr ((extract (in_tuple x) _) ++ _ ++ _).
  + rewrite -setP => i; rewrite !inE.
    case (boolP (i \in T)) => //= _.
    case: (ltnP i (size u)); last by rewrite andbF.
    by move/ltnW ->.
  + rewrite (tnth_nth a) /x /=; by elim: u.
  + set s := (X in extract _ X); suff -> : s = set0 by rewrite extract0.
    rewrite /s {s} -setP => i; rewrite !inE -andbA.
    apply/(sameP idP); apply(iffP idP) => //= /and3P [] _ H1 H2.
    have:= leq_trans H2 H1; by rewrite ltnn.
Qed.

Lemma extract_bT:
  extract (in_tuple x) (T :&: [set j : 'I_(size x) | j >= posb]) =
  b :: extract (in_tuple x) (T :&: [set j : 'I_(size x) | j > posc]).
Proof.
  set T' := (X in extract _ X).
  have : posb \in T' by rewrite !inE leqnn Hposb.
  move /extract_cuti ->. rewrite -[tnth _ _ :: _ ]cat1s -[RHS]cat1s -[RHS]cat0s.
  congr (_ ++ _ ++ (extract (in_tuple x) _)).
  + set s := (X in extract _ X); suff -> : s = set0 by rewrite extract0.
    rewrite /s {s} -setP => i; rewrite !inE -andbA.
    apply/(sameP idP); apply(iffP idP) => //= /and3P [] _ H1 H2.
    have:= leq_trans H2 H1; by rewrite ltnn.
  + rewrite (tnth_nth a) /x /=; by elim: u.
  + rewrite -setP => i; rewrite !inE.
    case (boolP (i \in T)) => //= Hi.
    case: (ltnP (size u).+2 i).
    * move/ltnW/ltnW => H; by rewrite H (ltnW H).
    * move=> Hi1; apply/(sameP idP); apply(iffP idP) => //= /andP [] _ H2.
      have:= TS_disjoint => /disjoint_setI0; rewrite -setP => Hdisj.
      case: (ltnP (size u).+1 i) => Hi2.
      - have Htmp : i = posc by apply val_inj => /=; apply /eqP; rewrite eqn_leq Hi2 Hi1.
        subst i => {Hi1 H2 Hi2}.
        have:= (Hdisj posc); by rewrite in_set0 in_setI Hi Hposc.
      - have Htmp : i = posa by apply val_inj => /=; apply /eqP; rewrite eqn_leq Hi2 H2.
        subst i => {Hi1 H2 Hi2}.
        have:= (Hdisj posa); by rewrite in_set0 in_setI Hi Hposa.
Qed.

Lemma extract_S1 : is_seq R (extract (in_tuple x) S1).
Proof.
  move: Px => /and3P [] _ _ /forallP Hall.
  rewrite extract_S1E; set lL := (X in X ++ _); set lR := (X in _ ++ X).
  have:= Hall S; rewrite HS => /= HseqS.
  have:= Hall T; rewrite HT => /= HseqT.
  have : is_seq R lR by apply (is_seq_extract_cond (Rtrans HRabc) _ HseqT).
  have : is_seq R lL by apply (is_seq_extract_cond (Rtrans HRabc) _ HseqS).
  rewrite /=; case HlL: lL => [|l0 lL']; first by rewrite cat0s.
  rewrite /sorted /= cat_path => -> /=.
  case HlR : lR => [//=| r0 lR'] /= ->; rewrite andbT.
  have -> : (last l0 lL') = a.
    have := extract_Sa; rewrite -/lL HlL.
    case: (extract _ _) => [/= [] -> -> //=| y z [] -> ->].
    by rewrite last_rcons.
  apply (Hbax HRabc).
  have := (is_seq_extract_cond (Rtrans HRabc) [set j : 'I_(size x) | j >= posb] HseqT).
  by rewrite extract_bT -/lR HlR /= => /andP [] ->.
Qed.

Lemma extract_T1 : is_seq R (extract (in_tuple x) T1).
Proof.
  move: Px => /and3P [] _ _ /forallP Hall.
  rewrite extract_T1E; set lL := (X in X ++ _); set lR := (X in _ ++ X).
  have:= Hall S; rewrite HS => /= HseqS.
  have {Hall} := Hall T; rewrite HT => /= HseqT.
  have : is_seq R lR by apply (is_seq_extract_cond (Rtrans HRabc) _ HseqS).
  have : is_seq R lL by apply (is_seq_extract_cond (Rtrans HRabc) _ HseqT).
  rewrite /=; case HlL: lL => [|l0 lL']; first by rewrite cat0s.
  rewrite /sorted /= cat_path => -> /=.
  rewrite /lR extract_cS /= => ->; rewrite andbT.
  have -> : (last l0 lL') = b.
    have := extract_Tb; rewrite -/lL HlL.
    case: (extract _ _) => [/= [] -> -> //=| y z [] -> ->].
    by rewrite last_rcons.
  exact (Hbc HRabc).
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

Lemma posaS1_bin : posa \in S1.
Proof. by rewrite /S1 !inE Hposa leqnn. Qed.

Lemma posaT1_bin : posb \in T1.
Proof. by rewrite /T1 !inE Hposb leqnn. Qed.

Lemma Qbin_noboth U : U \in Qbin -> ~ ((posa \in U) && ((posc \in U))).
Proof.
  rewrite /Qbin !inE.
  case (altP (U =P S1)) => [-> _ |HneqS1] /=.
  + by rewrite /S1 !inE Hposa /= !ltnn !andbF.
  case (altP (U =P T1)) => [-> _ |HneqT1] /=.
  + by rewrite /T1 !inE Hposa /= posa_inTF /= ltnn.
  + move/andP => []; rewrite negb_or => /andP [] HUS HUT HU.
    move: Px => /and3P [] _ /trivIsetP Htriv _.
    have {Htriv} /disjoint_setI0 := Htriv _ _ HU HS HUS; rewrite -setP => Hdisj.
    have:= (Hdisj posa); by rewrite in_set0 in_setI Hposa andbT => ->.
Qed.

End BIn.

Theorem exists_Q_noboth :
  exists Q : {set {set 'I_(size x)}},
    [/\ ksupp R (in_tuple x) k Q, scover Q = scover P &
      forall S, S \in Q -> ~ ((posa \in S) && ((posc \in S)))].
Proof.
  case (boolP (posb \in (cover P))) => [|Hcov].
  - rewrite /cover => /bigcupP [] T HT HbT.
    exists (Qbin T); split.
    + by apply ksupp_bin.
    + by rewrite /scover /= cover_bin.
    + move=> S0; by apply Qbin_noboth.
  - exists Qbnotin; split.
    + by apply ksupp_bnotin.
    + by rewrite (eqP (scover_bnotin)).
    + move=> S0; by apply Qbnotin_noboth.
Qed.

Let x' := (u ++ [:: b]) ++ [:: a; c] ++ v.
Let y  := (u ++ [:: b]) ++ [:: c; a] ++ v.

Lemma eq_xx' : x = x'. Proof. by rewrite /x /x' -catA. Qed.

Theorem exists_Qy :
  exists Q : {set {set 'I_(size y)}},
    scover Q = scover P /\ ksupp R (in_tuple y) k Q .
Proof.
  have:= exists_Q_noboth => [] [] Q [] Hsupp Hcover Hnoboth.
  move HcastP : ((cast_set (eq_size eq_xx')) @: Q) => Q'.
  exists (@NoSetContainingBoth.Q _ (u ++ [:: b]) v a c Q'); split.
  - rewrite -(eqP (@NoSetContainingBoth.scover_noBoth _ (u ++ [:: b]) v a c Q')).
    rewrite /scover /= -HcastP cover_cast /cast_set /=.
    by rewrite card_imset; last by apply cast_ord_inj.
  - apply NoSetContainingBoth.ksupp_noBoth.
    rewrite -HcastP; by apply ksupp_cast.
  - move=> S1; rewrite -HcastP => /imsetP [] S0 HS0 -> {S1}.
    rewrite /cast_set /=. set x0 := (Swap.pos0 _ _ _ _); set x1 := (Swap.pos1 _ _ _ _).
    have:= Hnoboth S0 HS0.
    rewrite -(cast_ordKV (eq_size eq_xx') x0) -(cast_ordKV (eq_size eq_xx') x1).
    rewrite !(mem_imset_inj _ _ (@cast_ord_inj _ _ _)).
    have -> : cast_ord (esym (eq_size eq_xx')) x0 = posa.
      by apply val_inj; rewrite /= size_cat /= addn1.
    have -> : cast_ord (esym (eq_size eq_xx')) x1 = posc.
      by apply val_inj; rewrite /= size_cat /= addn1.
    by [].
Qed.

End Case.
End SetContainingBothLeft.

Lemma RabcLeqX (Alph : ordType) (a b c : Alph) :
  (a < b <= c)%Ord -> SetContainingBothLeft.hypRabc (leqX Alph) a b c.
Proof.
  move=> H; constructor.
  + move=> x y z; by apply leqX_trans.
  + by move: H => /andP /= [].
  + move: H => /andP /= []; by rewrite ltnXNgeqX.
  + move: H => /andP /= [] H1 _ /= x H2; by apply (leqX_trans H2 (ltnXW H1)).
  + move: H => /andP /= [] H1 _ /= x H2; by apply (leqX_trans (ltnXW H1) H2).
Qed.

Lemma RabcGtnX (Alph : ordType) (a b c : Alph) :
  (a < b <= c)%Ord -> SetContainingBothLeft.hypRabc (gtnX Alph) c b a.
Proof.
  move=> H; constructor.
  + by apply gtnX_trans.
  + by move: H => /andP /= [].
  + move: H => /andP /= [] _; by rewrite -!leqXNgtnX.
  + move: H => /andP /= [] _ H1 /= x H2; by apply (leqX_ltnX_trans H1 H2).
  + move: H => /andP /= [] _ H1 /= x H2; by apply (ltnX_leqX_trans H2 H1).
Qed.

Section GreenInvariantsRule.

Variable Alph : ordType.
Let word := seq Alph.

Variable u v1 w v2 : word.
Variable k : nat.


(* | [:: c; a; b] => if (a <= b < c)%Ord then [:: [:: a; c; b]] else [::] *)
Lemma ksuppRow_inj_plact1i :
  v2 \in plact1i v1 -> ksupp_inj (leqX Alph) (leqX Alph) k (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof.
  move/plact1iP => [] a [] b [] c [] Hord -> ->.
  rewrite /ksupp_inj  => S1 Hsupp.
  pose posa := (Swap.pos0 u (b :: w) c a).
  pose posc := (Swap.pos1 u (b :: w) c a).
  case (boolP [exists S, [&& S \in S1, posa \in S & posc \in S] ]).
  + move/existsP => [] S /and3P [] HSin HSa HSb.
    exfalso; move: Hsupp; rewrite /ksupp => /and3P [] _ _ /forallP Hall.
    have Htrans: transitive (leqX Alph) by move=> d e f /= H1 H2; apply (leqX_trans H1 H2).
    have:= Hall S; rewrite HSin /= {Hall} => Hsort.
    have:= is_seq_extract_cond Htrans [set posa; posc] Hsort.
    have -> : S :&: [set posa; posc] = [set posa; posc].
      apply/setP/subset_eqP/andP; split; apply/subsetP=> i; first by rewrite inE => /andP [].
      rewrite !inE => /orP [] => /eqP ->; rewrite eq_refl /=; first by rewrite HSa.
      by rewrite HSb orbT.
    have /extract2 -> : posa < posc by [].
    rewrite !(tnth_nth b) /= andbT.
    elim u => [| u0 u'] /=.
    - move: Hord => /andP [] /leqX_ltnX_trans H/H{H}.
      by rewrite leqXNgtnX => ->.
    - by apply.
  + rewrite negb_exists => /forallP Hall.
    exists (NoSetContainingBoth.Q S1); rewrite NoSetContainingBoth.scover_noBoth /=.
    apply NoSetContainingBoth.ksupp_noBoth; first exact Hsupp.
    move=> S HS; have:= Hall S; by rewrite HS /= => /negbTE ->.
Qed.

Corollary greenRow_leq_plact1i :
  v2 \in plact1i v1 -> greenRow (u ++ v1 ++ w) k <= greenRow (u ++ v2 ++ w) k.
Proof. by move /ksuppRow_inj_plact1i; apply leq_green. Qed.

(* | [:: b; a; c] => if (a < b <= c)%Ord then [:: [:: b; c; a]] else [::] *)
Lemma ksuppRow_inj_plact2 :
  v2 \in plact2 v1 -> ksupp_inj (leqX Alph) (leqX Alph) k (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof.
  move/plact2P => [] a [] b [] c [] Hord -> ->.
  have Hyp := RabcLeqX Hord.
  have Hbac : ((u ++ [:: b]) ++ [:: a; c] ++ w) = (u ++ [:: b; a; c] ++ w) by rewrite -catA.
  have Hbca : ((u ++ [:: b]) ++ [:: c; a] ++ w) = (u ++ [:: b; c; a] ++ w) by rewrite -catA.
  rewrite -Hbca -Hbac /ksupp_inj  => P Hsupp.
  pose posa := (Swap.pos0 (u ++ [:: b]) w a c).
  pose posc := (Swap.pos1 (u ++ [:: b]) w a c).
  case (boolP [exists S, [&& S \in P, posa \in S & posc \in S] ]).
  - move/existsP => [] S /and3P [] HSin HSa HSc.
    move HcastP : ((cast_set (eq_size Hbac)) @: P) => P'.
    have Hsupp' : ksupp (leqX Alph) (in_tuple (u ++ [:: b; a; c] ++ w)) k P'.
      rewrite -HcastP; by apply ksupp_cast.
    move HcastS : (cast_set (eq_size Hbac) S) => S'.
    have HS'in : S' \in P' by rewrite -HcastP -HcastS; apply mem_imset.
    set pos1 := Swap.pos1 u (c :: w) b a; have Hpos1 : pos1 \in S'.
       rewrite -(cast_ordKV (eq_size Hbac) pos1) -HcastS /cast_set /=; apply mem_imset.
       suff -> //= : cast_ord (esym (eq_size Hbac)) pos1 = posa by [].
       by apply val_inj; rewrite /= size_cat /= addn1.
    set pos2 := Ordinal (SetContainingBothLeft.u2lt u w a b c); have Hpos2 : pos2 \in S'.
       rewrite -(cast_ordKV (eq_size Hbac) pos2) -HcastS /cast_set /=; apply mem_imset.
       suff -> //= : cast_ord (esym (eq_size Hbac)) pos2 = posc by [].
       by apply val_inj; rewrite /= size_cat /= addn1.
    have:= SetContainingBothLeft.exists_Qy Hyp Hsupp' HS'in Hpos1 Hpos2.
    move=> [] Q [] Hcover HsuppQ.
    exists Q; apply /andP; split; last exact HsuppQ.
    rewrite Hcover -HcastP /scover /= -size_cover_inj //=; by apply cast_ord_inj.
  - rewrite negb_exists => /forallP Hall.
    exists (NoSetContainingBoth.Q P); rewrite NoSetContainingBoth.scover_noBoth /=.
    apply NoSetContainingBoth.ksupp_noBoth; first exact Hsupp.
    move=> S HS; have:= Hall S; by rewrite HS /= => /negbTE ->.
Qed.

Corollary greenRow_leq_plact2 :
  v2 \in plact2 v1 -> greenRow (u ++ v1 ++ w) k <= greenRow (u ++ v2 ++ w) k.
Proof. by move /ksuppRow_inj_plact2; apply leq_green. Qed.


(* [:: a; c; b] => if (a <= b < c)%Ord then [:: [:: c; a; b]] else [::] *)
Lemma ksuppCol_inj_plact1 :
  v2 \in plact1 v1 -> ksupp_inj (gtnX Alph) (gtnX Alph) k (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof.
  move/plact1P => [] a [] b [] c [] Hord -> ->.
  rewrite /ksupp_inj  => S1 Hsupp.
  pose posa := (Swap.pos0 u (b :: w) a c).
  pose posc := (Swap.pos1 u (b :: w) a c).
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

Corollary greenCol_leq_plact1 :
  v2 \in plact1 v1 -> greenCol (u ++ v1 ++ w) k <= greenCol (u ++ v2 ++ w) k.
Proof. by move /ksuppCol_inj_plact1; apply leq_green. Qed.

(* [:: b; c; a] => if (a < b <= c)%Ord then [:: [:: b; a; c]] else [::] *)
Lemma ksuppCol_inj_plact2i :
  v2 \in plact2i v1 -> ksupp_inj (gtnX Alph) (gtnX Alph) k (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof.
  move/plact2iP => [] a [] b [] c [] Hord -> ->.
  have Hyp := RabcGtnX Hord.
  have Hbca : ((u ++ [:: b]) ++ [:: c; a] ++ w) = (u ++ [:: b; c; a] ++ w) by rewrite -catA.
  have Hbac : ((u ++ [:: b]) ++ [:: a; c] ++ w) = (u ++ [:: b; a; c] ++ w) by rewrite -catA.
  rewrite -Hbca -Hbac /ksupp_inj  => P Hsupp.
  pose posa := (Swap.pos0 (u ++ [:: b]) w c a).
  pose posc := (Swap.pos1 (u ++ [:: b]) w c a).
  case (boolP [exists S, [&& S \in P, posa \in S & posc \in S] ]).
  - move/existsP => [] S /and3P [] HSin HSa HSc.
    move HcastP : ((cast_set (eq_size Hbca)) @: P) => P'.
    have Hsupp' : ksupp (gtnX Alph) (in_tuple (u ++ [:: b; c; a] ++ w)) k P'.
      rewrite -HcastP; by apply ksupp_cast.
    move HcastS : (cast_set (eq_size Hbca) S) => S'.
    have HS'in : S' \in P' by rewrite -HcastP -HcastS; apply mem_imset.
    set pos1 := Swap.pos1 u (a :: w) b c; have Hpos1 : pos1 \in S'.
       rewrite -(cast_ordKV (eq_size Hbca) pos1) -HcastS /cast_set /=; apply mem_imset.
       suff -> //= : cast_ord (esym (eq_size Hbca)) pos1 = posa by [].
       by apply val_inj; rewrite /= size_cat /= addn1.
    set pos2 := Ordinal (SetContainingBothLeft.u2lt u w c b a); have Hpos2 : pos2 \in S'.
       rewrite -(cast_ordKV (eq_size Hbca) pos2) -HcastS /cast_set /=; apply mem_imset.
       suff -> //= : cast_ord (esym (eq_size Hbca)) pos2 = posc by [].
       by apply val_inj; rewrite /= size_cat /= addn1.
    have:= SetContainingBothLeft.exists_Qy Hyp Hsupp' HS'in Hpos1 Hpos2.
    move=> [] Q [] Hcover HsuppQ.
    exists Q; apply /andP; split; last exact HsuppQ.
    rewrite Hcover -HcastP /scover /= -size_cover_inj //=; by apply cast_ord_inj.
  - rewrite negb_exists => /forallP Hall.
    exists (NoSetContainingBoth.Q P); rewrite NoSetContainingBoth.scover_noBoth /=.
    apply NoSetContainingBoth.ksupp_noBoth; first exact Hsupp.
    move=> S HS; have:= Hall S; by rewrite HS /= => /negbTE ->.
Qed.

Corollary greenCol_leq_plact2i :
  v2 \in plact2i v1 -> greenCol (u ++ v1 ++ w) k <= greenCol (u ++ v2 ++ w) k.
Proof. by move /ksuppCol_inj_plact2i; apply leq_green. Qed.

End GreenInvariantsRule.


Section GreenInvariantsDual.

Variable Alph : ordType.
Let word := seq Alph.
Implicit Type u v w : word.

Lemma greenRow_leq_plact2i u v1 w v2 k :
  v2 \in plact2i v1 -> greenRow (u ++ v1 ++ w) k <= greenRow (u ++ v2 ++ w) k.
Proof.
  rewrite plact2idual => /greenRow_leq_plact1i H.
  rewrite [greenRow (_ ++ v1 ++ _) k]greenRow_dual.
  rewrite [greenRow (_ ++ v2 ++ _) k]greenRow_dual.
  have:= H (revdual Alph w) (revdual Alph u) k.
  by rewrite /revdual /= -!rev_cat -!map_cat -!catA.
Qed.

Lemma greenRow_leq_plact1 u v1 w v2 k :
  v2 \in plact1 v1 -> greenRow (u ++ v1 ++ w) k <= greenRow (u ++ v2 ++ w) k.
Proof.
  rewrite plact1dual => /greenRow_leq_plact2 H.
  rewrite [greenRow (_ ++ v1 ++ _) k]greenRow_dual.
  rewrite [greenRow (_ ++ v2 ++ _) k]greenRow_dual.
  have:= H (revdual Alph w) (revdual Alph u) k.
  by rewrite /revdual /= -!rev_cat -!map_cat -!catA.
Qed.

Lemma greenRow_invar_plact1 u v1 w v2 k :
  v2 \in plact1 v1 -> greenRow (u ++ v1 ++ w) k = greenRow (u ++ v2 ++ w) k.
Proof.
  move=> H; apply/eqP; rewrite eqn_leq; apply/andP; split.
  + by apply greenRow_leq_plact1.
  + apply greenRow_leq_plact1i; by rewrite -plact1I.
Qed.

Lemma greenRow_invar_plact1i u v1 w v2 k :
  v2 \in plact1i v1 -> greenRow (u ++ v1 ++ w) k = greenRow (u ++ v2 ++ w) k.
Proof. by rewrite -plact1I => H; apply esym; apply greenRow_invar_plact1. Qed.

Lemma greenRow_invar_plact2 u v1 w v2 k :
  v2 \in plact2 v1 -> greenRow (u ++ v1 ++ w) k = greenRow (u ++ v2 ++ w) k.
Proof.
  move=> H; apply/eqP; rewrite eqn_leq; apply/andP; split.
  + by apply greenRow_leq_plact2.
  + apply greenRow_leq_plact2i; by rewrite -plact2I.
Qed.

Lemma greenRow_invar_plact2i u v1 w v2 k :
  v2 \in plact2i v1 -> greenRow (u ++ v1 ++ w) k = greenRow (u ++ v2 ++ w) k.
Proof. by rewrite -plact2I => H; apply esym; apply greenRow_invar_plact2. Qed.


Lemma greenCol_leq_plact1i u v1 w v2 k :
  v2 \in plact1i v1 -> greenCol (u ++ v1 ++ w) k <= greenCol (u ++ v2 ++ w) k.
Proof.
  rewrite plact1idual => /greenCol_leq_plact2i H.
  rewrite [greenCol (_ ++ v1 ++ _) k]greenCol_dual.
  rewrite [greenCol (_ ++ v2 ++ _) k]greenCol_dual.
  have:= H (revdual Alph w) (revdual Alph u) k.
  by rewrite /revdual /= -!rev_cat -!map_cat -!catA.
Qed.

Lemma greenCol_leq_plact2 u v1 w v2 k :
  v2 \in plact2 v1 -> greenCol (u ++ v1 ++ w) k <= greenCol (u ++ v2 ++ w) k.
Proof.
  rewrite plact2dual => /greenCol_leq_plact1 H.
  rewrite [greenCol (_ ++ v1 ++ _) k]greenCol_dual.
  rewrite [greenCol (_ ++ v2 ++ _) k]greenCol_dual.
  have:= H (revdual Alph w) (revdual Alph u) k.
  by rewrite /revdual /= -!rev_cat -!map_cat -!catA.
Qed.

Lemma greenCol_invar_plact1 u v1 w v2 k :
  v2 \in plact1 v1 -> greenCol (u ++ v1 ++ w) k = greenCol (u ++ v2 ++ w) k.
Proof.
  move=> H; apply/eqP; rewrite eqn_leq; apply/andP; split.
  + by apply greenCol_leq_plact1.
  + apply greenCol_leq_plact1i; by rewrite -plact1I.
Qed.

Lemma greenCol_invar_plact1i u v1 w v2 k :
  v2 \in plact1i v1 -> greenCol (u ++ v1 ++ w) k = greenCol (u ++ v2 ++ w) k.
Proof. by rewrite -plact1I => H; apply esym; apply greenCol_invar_plact1. Qed.

Lemma greenCol_invar_plact2 u v1 w v2 k :
  v2 \in plact2 v1 -> greenCol (u ++ v1 ++ w) k = greenCol (u ++ v2 ++ w) k.
Proof.
  move=> H; apply/eqP; rewrite eqn_leq; apply/andP; split.
  + by apply greenCol_leq_plact2.
  + apply greenCol_leq_plact2i; by rewrite -plact2I.
Qed.

Lemma greenCol_invar_plact2i u v1 w v2 k :
  v2 \in plact2i v1 -> greenCol (u ++ v1 ++ w) k = greenCol (u ++ v2 ++ w) k.
Proof. by rewrite -plact2I => H; apply esym; apply greenCol_invar_plact2. Qed.

End GreenInvariantsDual.


Section GreenInvariants.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Notation "a =Pl b" := (plactcongr a b) (at level 70).

Theorem greenRow_invar_plactic u v : u =Pl v -> forall k, greenRow u k = greenRow v k.
Proof.
  move=> Hpl k.
  move: v Hpl; apply gencongr_ind; first by apply erefl.
  move=> a b1 c b2 -> {u} /plactruleP [].
  + apply greenRow_invar_plact1.
  + apply greenRow_invar_plact1i.
  + apply greenRow_invar_plact2.
  + apply greenRow_invar_plact2i.
Qed.

Corollary greenRow_RS k w : greenRow w k = part_sum (shape (RS w)) k.
Proof.
  rewrite -greenRow_tab; last by apply is_tableau_RS.
  apply greenRow_invar_plactic; by apply congr_RS.
Qed.


Corollary plactic_shapeRS_row_proof u v : u =Pl v -> shape (RS u) = shape (RS v).
Proof.
  move=> Hpl.
  suff HeqRS k : greenRow (to_word (RS u)) k = greenRow (to_word (RS v)) k
    by apply (greenRow_tab_eq_shape (is_tableau_RS u) (is_tableau_RS v) HeqRS).
  have <- := greenRow_invar_plactic (congr_RS u) k.
  have <- := greenRow_invar_plactic (congr_RS v) k.
  by apply greenRow_invar_plactic.
Qed.


Theorem greenCol_invar_plactic u v : u =Pl v -> forall k, greenCol u k = greenCol v k.
Proof.
  move=> Hpl k.
  move: v Hpl; apply gencongr_ind; first by apply erefl.
  move=> a b1 c b2 -> {u} /plactruleP [].
  + apply greenCol_invar_plact1.
  + apply greenCol_invar_plact1i.
  + apply greenCol_invar_plact2.
  + apply greenCol_invar_plact2i.
Qed.

Corollary greenCol_RS k w : greenCol w k = part_sum (conj_part (shape (RS w))) k.
Proof.
  rewrite -greenCol_tab; last by apply is_tableau_RS.
  apply greenCol_invar_plactic; by apply congr_RS.
Qed.

Corollary plactic_shapeRS u v : u =Pl v -> shape (RS u) = shape (RS v).
Proof.
  move=> Hpl.
  suff HeqRS k : greenCol (to_word (RS u)) k = greenCol (to_word (RS v)) k
    by apply (greenCol_tab_eq_shape (is_tableau_RS u) (is_tableau_RS v) HeqRS).
  have <- := greenCol_invar_plactic (congr_RS u) k.
  have <- := greenCol_invar_plactic (congr_RS v) k.
  by apply greenCol_invar_plactic.
Qed.

Theorem plactic_RS u v : u =Pl v <-> RS u == RS v.
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
