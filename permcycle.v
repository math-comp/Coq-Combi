Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial fingroup perm automorphism action.

From Combi Require Import symgroup partition Greene.

Set Implicit Arguments.
Unset Strict Implicit.

Section Definitions.

Variable T : finType.
Implicit Type s : {perm T}.

Lemma pcycleP s x y : reflect (exists i, y = (s ^+ i)%g x) (y \in pcycle s x).
Proof.
  apply (iffP idP).
  - rewrite pcycle_traject => H.
    have:= H; rewrite -index_mem size_traject => Hlt.
    exists (index y (traject s x #|pcycle s x|)).
    have {Hlt} := nth_traject s Hlt x; rewrite (nth_index _ H) => {H} {1}->.
    elim: (index _ _) => [|n IHn] /=; first by rewrite expg0 perm1.
    by rewrite expgSr permM IHn.
  - move => [i ->]; exact: mem_pcycle.
Qed.

Lemma pcycleV s x : pcycle s^-1 x = pcycle s x.
Proof. rewrite -setP => y; by rewrite /pcycle cycleV. Qed.

Lemma pcycle_s s x y : y \in pcycle s x -> s y \in pcycle s x.
Proof.
  rewrite -!eq_pcycle_mem => /eqP <-.
  by have:= mem_pcycle s 1 y; rewrite eq_pcycle_mem expg1 => ->.
Qed.

Lemma pcycle1 s x : s x = x <-> pcycle s x = [set x].
Proof.
  split => [Heq | Hcy].
  - rewrite -setP => y; rewrite !inE.
    apply/pcycleP/idP=> [[i ->] | /eqP ->]; last by exists 0; rewrite expg0 perm1.
    elim: i => [//=| i /eqP IHi]; first by rewrite expg0 perm1.
    by rewrite expgSr permM IHi Heq.
  - by have := mem_pcycle s 1 x; rewrite expg1 Hcy inE => /eqP.
Qed.

Definition support s := [set x | s x != x].

Lemma support0 s : support s = set0 -> s = 1%g.
Proof.
  move=> H; rewrite -permP => y; rewrite perm1.
  suff : y \notin support s by rewrite inE negbK => /eqP.
  by rewrite H inE.
Qed.

Lemma support_stable s x : x \in support s = (s x \in support s).
Proof.
  rewrite !inE; congr negb; apply/idP/idP => [/eqP -> // | /eqP H].
  by rewrite -[s x](permK s) H permK.
Qed.

Lemma pcycle_subset_support s x :
  x \in support s -> pcycle s x \subset support s.
Proof.
  move=> H; apply/subsetP => y; rewrite -eq_pcycle_mem => /eqP Heq.
  move: H; rewrite !inE; apply contra => /eqP Hy.
  have:= Hy => /pcycle1; rewrite {}Heq => Hyx.
  have:= pcycle_id s x; rewrite {}Hyx inE => /eqP ->.
  by rewrite Hy.
Qed.

Lemma support_card s x : x \in support s = (#|pcycle s x| != 1).
Proof.
  rewrite neq_ltn ltnS leqn0 cards_eq0.
  have /negbTE -> /= : pcycle s x != set0.
    apply/set0Pn; exists x; exact: pcycle_id.
  rewrite inE; apply/idP/idP.
  - apply contraR; rewrite -leqNgt => Hcard.
    apply/eqP/pcycle1/eqP; rewrite eq_sym eqEcard cards1 Hcard andbT.
    apply/subsetP => y; rewrite inE => /eqP ->; exact: pcycle_id.
  - apply contraL => /eqP/pcycle1 ->.
    by rewrite cards1.
Qed.

Lemma support_disjointC s t :
  [disjoint support s & support t] -> (s * t = t * s)%g.
Proof.
  rewrite -permP => Hdisj x; rewrite !permM.
  case: (boolP (x \in support s)) => [Hs |].
  - have:= Hdisj; rewrite disjoints_subset => /subsetP H.
    have:= H x Hs; rewrite !inE negbK => /eqP ->.
    by move: Hs; rewrite support_stable => /H; rewrite !inE negbK => /eqP ->.
  - rewrite inE negbK => /eqP Hs; rewrite Hs.
    case: (boolP (x \in support t)) => [Ht |].
    + move: Ht; rewrite support_stable.
      move: Hdisj; rewrite -setI_eq0 setIC setI_eq0 disjoints_subset => /subsetP.
      by move=> H/H{H}; rewrite !inE negbK => /eqP ->.
    + by rewrite inE negbK => /eqP ->; rewrite Hs.
Qed.

Lemma trivIset_supportC (A B : seq {perm T}) :
  trivIseq [seq support s | s <- A] -> perm_eq A B ->
  (\prod_(s <- A) s = \prod_(s <- B) s)%g.
Proof.
  move=> Htriv Hperm.
  apply: (catCA_perm_ind
            (P := fun S => (\prod_(s <- A) s = \prod_(s <- S) s)%g)
            _ Hperm (erefl _)).
Admitted.

Definition cyclefun_of s x := [fun y => if y \in pcycle s x then s y else y].

Lemma cyclefun_ofP s x : injective (finfun (cyclefun_of s x)).
Proof.
  move=> y z; rewrite !ffunE /=.
  case: (boolP (y \in pcycle s x)) => Hy;
    case: (boolP (z \in pcycle s x)) => Hz // Heq.
  - exact: (perm_inj Heq).
  - by exfalso; move: Heq Hz => <-; rewrite pcycle_s.
  - by exfalso; move: Heq Hy => ->; rewrite pcycle_s.
Qed.

Definition cycle_of s x : {perm T} := perm (@cyclefun_ofP s x).

Lemma cycle_ofE s x : cycle_of s x =1 cyclefun_of s x.
Proof. by move=> y; rewrite permE ffunE. Qed.

Lemma cycle_ofK s x y : (cycle_of s^-1 x) ((cycle_of s x) y) = y.
Proof.
  rewrite !cycle_ofE /=.
  case: (boolP (y \in pcycle s x)); rewrite pcycleV.
  - by move=> /pcycle_s ->; rewrite permK.
  - by move=> /negbTE ->.
Qed.

Lemma cycle_ofV s x : ((cycle_of s x)^-1)%g = cycle_of s^-1 x.
Proof.
  rewrite -permP => y.
  by rewrite -{2}(permKV (cycle_of s x) y) cycle_ofK.
Qed.

Lemma cycle_of_nsupp s x :
  x \notin support s -> cycle_of s x = 1%g.
Proof.
  rewrite inE negbK => /eqP/pcycle1 Hx.
  rewrite -permP => y.
  rewrite cycle_ofE /= Hx inE perm1.
  by case: eqP => [-> | //]; rewrite pcycle1.
Qed.

Lemma support_cycle_of s x :
  x \in support s -> support (cycle_of s x) = pcycle s x.
Proof.
  move=> H; rewrite -setP => y.
  rewrite /support inE cycle_ofE /=.
  case: (boolP (y \in pcycle s x)); last by rewrite eq_refl.
  rewrite pcycle_sym=> Hcy; move: H; rewrite /support inE.
  apply contra => /eqP; rewrite pcycle1 => Hy.
  move: Hcy; rewrite Hy inE => /eqP ->.
  by apply/eqP; rewrite pcycle1.
Qed.

Lemma exp_cycle_of s x n : (cycle_of s x ^+ n)%g x = (s ^+ n)%g x.
Proof.
  elim: n => [// | n IHn].
  by rewrite !expgSr !permM {}IHn cycle_ofE /= mem_pcycle.
Qed.

Lemma pcycle_cycle_ofE s x : pcycle (cycle_of s x) x = pcycle s x.
Proof.
  rewrite -setP => y.
  by apply/pcycleP/pcycleP => [] [i Hi]; exists i; rewrite {}Hi exp_cycle_of.
Qed.


Definition is_cycle s := #|[set C in pcycles s | #|C| != 1 ]| == 1.

Lemma is_cycleP s :
  reflect (exists x, x \in support s /\ cycle_of s x = s) (is_cycle s).
Proof.
  rewrite /is_cycle; apply (iffP idP).
  - move=> /cards1P [] C HC.
    have:= eq_refl C; rewrite -in_set1 -HC inE => /andP [] /imsetP [x _] HCC.
    subst C; rewrite -support_card => Hx.
    exists x; split; first exact Hx.
    suff Heq : support s = pcycle s x.
      by rewrite -permP => y; rewrite cycle_ofE /= -Heq inE; case: eqP.
    rewrite -setP => y.
    by rewrite -eq_pcycle_mem -in_set1 -HC inE mem_imset //= support_card.
  - move=> [x [Hx Hcy]].
    suff -> : [set C in pcycles s | #|C| != 1] = [set pcycle s x] by rewrite cards1.
    rewrite -setP => C; rewrite /pcycles !inE; apply/idP/idP.
    + move=> /andP [] /imsetP [x0 _ -> {C}].
      by rewrite -support_card -{1}Hcy (support_cycle_of Hx) eq_pcycle_mem.
    + move=> /eqP ->.
      by rewrite mem_imset // -support_card Hx.
Qed.

Lemma cycle_ofP s x : x \in support s -> is_cycle (cycle_of s x).
Proof.
  move=> H; apply/is_cycleP; exists x; split.
  - by move: H; rewrite !inE cycle_ofE /= pcycle_id.
  - rewrite -permP => y; rewrite cycle_ofE /=.
    by rewrite pcycle_cycle_ofE cycle_ofE /=; case: (y \in _).
Qed.

Lemma perm_cycle_ofK s x :
  support ((cycle_of s x)^-1 * s) = support s :\: pcycle s x.
Proof.
  rewrite -setP => y; rewrite !inE -negb_or orbC; congr negb.
  case: (altP (s y =P y)) => /= Hy.
  - have Hcy : cycle_of s x y = y.
      by rewrite cycle_ofE /= Hy if_same.
    by rewrite -{1}Hcy permM permK Hy eq_refl.
  - rewrite cycle_ofV permM cycle_ofE /= pcycleV.
    case: (y \in pcycle s x).
    + by rewrite permKV eq_refl.
    + exact: negbTE.
Qed.

Lemma supp_decr s x :
  x \in support s -> #|support ((cycle_of s x)^-1 * s)| < #|support s|.
Proof.
  rewrite perm_cycle_ofK cardsD => Hsupp.
  rewrite -subSn; last by apply subset_leqif_cards; exact: subsetIl.
  rewrite leq_subLR.
  rewrite -{1}(add0n #|_|) ltn_add2r lt0n cards_eq0.
  by apply/set0Pn; exists x; rewrite inE Hsupp pcycle_id.
Qed.

Fixpoint dec_cycles_rec n s : seq {perm T} :=
  if n is n'.+1 then
    if pick (mem (support s)) is Some x then
      (cycle_of s x) :: (dec_cycles_rec n' ((cycle_of s x)^-1 * s))
    else [::]
  else [::].
Definition dec_cycles s := dec_cycles_rec #|support s| s.

Lemma dec_cycles_recE s : (\prod_(c <- dec_cycles s) c = s)%g.
Proof.
  rewrite /dec_cycles.
  move: {2 3}#|support s| (leqnn #|support s|) => n.
  elim: n s => [| n IHn] s /=.
    rewrite leqn0 cards_eq0 => /eqP /support0 ->.
    by rewrite big_nil.
  move=> Hcard.
  case: pickP => [x /= Hx |]/=.
  - rewrite big_cons {}IHn; first by rewrite mulgA mulgV mul1g.
    rewrite -ltnS; apply: (leq_trans _ Hcard); exact: supp_decr.
  - rewrite big_nil => H; apply esym; apply support0.
    by rewrite -setP => x; have /= -> := (H x); rewrite inE.
Qed.

Lemma all_dec_cyclesP s : all is_cycle (dec_cycles s).
Proof.
  rewrite /dec_cycles.
  move: {2 3}#|support s| (leqnn #|support s|) => n.
  elim: n s => [// | n IHn] s /=.
  case: pickP => [x /= Hx Hcard | //].
  rewrite cycle_ofP //=; apply: IHn.
  rewrite -ltnS; apply: (leq_trans _ Hcard); exact: supp_decr.
Qed.

Lemma support_dec_cycles_rec s n :
  all (fun C => support C \subset support s) (dec_cycles_rec n s).
Proof.
  elim: n s => [// | n IHn] s /=.
  case: pickP => [x /= Hx | //]; apply /andP; split.
  - rewrite (support_cycle_of Hx).
    exact: pcycle_subset_support.
  - have:= IHn ((cycle_of s x)^-1 * s)%g.
    apply sub_all => mu /subset_trans; apply.
    apply/subsetP => y; rewrite !inE.
    apply contra => /eqP.
    rewrite permM cycle_ofV cycle_ofE /= pcycleV.
    case: (y \in _) => [|-> //];  by rewrite permKV.
Qed.

Lemma trivIseq_dec s : trivIseq [seq support C | C <- dec_cycles s].
Proof.
  rewrite /dec_cycles.
  move: {2 3}#|support s| (leqnn #|support s|) => n.
  elim: n s => [| n IHn] s /=.
    by move=> _ i j /= /andP [].
  case: pickP => [x /= Hx Hcard | Hsupp0 _ /=].
  - case=> [ |i] [| j] //=; rewrite !ltnS.
    + move=> /(mem_nth set0).
      move: (nth _ _ _) => S /mapP [] mu.
      move=> /(allP (support_dec_cycles_rec ((cycle_of s x)^-1 * s) n)).
      rewrite perm_cycle_ofK support_cycle_of // => Hsubs -> {S}.
      rewrite disjoint_sym disjoints_subset.
      apply (subset_trans Hsubs); rewrite setDE; exact: subsetIr.
    + apply IHn.
      rewrite -ltnS; apply: (leq_trans _ Hcard); exact: supp_decr.
  - by move=> i j /= /andP [].
Qed.

End Definitions.

