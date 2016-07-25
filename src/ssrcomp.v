Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial.
From mathcomp Require Import fingroup perm automorphism action ssralg.
From mathcomp Require finmodule.

From Combi Require Import symgroup partition Greene tools sorted.

Set Implicit Arguments.
Unset Strict Implicit.


Module LeqGeqOrder.

Definition geq_total : total geq :=
  fun x y => leq_total y x.
Definition geq_trans : transitive geq :=
  fun x y z H1 H2 => leq_trans H2 H1.
Definition anti_geq : antisymmetric geq :=
  fun x y H => esym (anti_leq H).

Hint Resolve leq_total leq_trans anti_leq geq_total geq_trans anti_geq.

End LeqGeqOrder.

Import LeqGeqOrder.

Section SSRComplements.

Variable T: finType.
Variables (R : Type) (idx : R) (op : R -> R -> R) (F : T -> R).

Lemma partition_of0 (P : {set {set T}}):
  reflect (P = set0) (partition P set0).
Proof.
  apply (iffP and3P) => [[/eqP Hcov _ H0] | ->].
  - case: (set_0Vmem P) => [// | [X HXP]].
    exfalso; suff HX : X = set0 by subst X; rewrite HXP in H0.
    by apply/eqP; rewrite -subset0; rewrite -Hcov (bigcup_max X).
  - by split; rewrite ?inE // /trivIset /cover !big_set0 ?cards0.
Qed.

Lemma pcycleP (s: {perm T}) x y :
  reflect (exists i, y = (s ^+ i)%g x) (y \in pcycle s x).
Proof.
  apply (iffP idP) => [| [i ->]]; last exact: mem_pcycle.
  rewrite pcycle_traject => H.
  have:= H; rewrite -index_mem size_traject => Hlt.
  exists (index y (traject s x #|pcycle s x|)).
  move: Hlt => /(nth_traject s)/(_ x); rewrite (nth_index _ H) => {H} {1}->.
  elim: (index _ _) => [|n IHn] /=; first by rewrite expg0 perm1.
  by rewrite expgSr permM IHn.
Qed.

End SSRComplements.


Lemma sumn_sort l S : sumn (sort S l) = sumn l.
Proof. by have:= perm_sort S l => /perm_eqlP/perm_sumn. Qed.
  
From mathcomp Require Import binomial.

Section SetPartitionShape.


Variable T : finType.
Implicit Types (s t : {perm T}) (n : nat).

Definition parts_shape (s : {set {set T}}) :=
  sort geq [seq #|(x: {set T})| | x <- enum s].

Lemma parts_shapeP (s : {set {set T}}) D :
  partition s D -> is_part_of_n #|D| (parts_shape s).
Proof.
rewrite /parts_shape => /and3P [/eqP Hcov Htriv Hnon0].
rewrite /is_part_of_n /= is_part_sortedE.
apply/and3P; split.
- by rewrite sumn_sort -sumnE big_map -big_enum -Hcov.
- by apply sort_sorted => m n.
- move: Hnon0; apply contra.
  rewrite mem_sort => /mapP [] x.
  by rewrite mem_enum => Hx /esym/cards0_eq <-.
Qed.

Lemma ex_subset_card (B : {set T}) k :
  k <= #|B| -> exists2 A : {set T}, A \subset B & #|A| == k.
Proof.
rewrite -bin_gt0 -(cards_draws B k) card_gt0 => /set0Pn [x].
rewrite inE => /andP [H1 H2]; by exists x.
Qed.

Lemma ex_parts_shape (s : seq nat) (A : {set T}) :
  sumn s = #|A| -> 0 \notin s ->
  exists P : seq {set T},
    [/\ uniq P,
     partition [set X in P] A &
     [seq #|(X : {set T})| | X <- P] = s].
Proof.
elim: s A => [| i s IHs] A /=.
  move=> /esym/cards0_eq -> _; exists [::]; split => //.
  apply/partition_of0; apply/setP => x.
  by rewrite !inE in_nil.
rewrite inE eq_sym => Hi /norP [Bne0 /IHs{IHs} Hrec].
have: i <= #|A| by rewrite -Hi; apply: leq_addr.
move=> /ex_subset_card [B BsubA /eqP cardB]; subst i.
have /Hrec{Hrec} [P [Puniq]] : sumn s = #|A :\: B|.
  by rewrite cardsD (setIidPr BsubA) -Hi addKn.
move=> /and3P [/eqP covP trivP set0P] Ps; rewrite inE in set0P.
have BninP : B \notin P.
  move: Bne0; apply contra => BinP; rewrite cards_eq0.
  have : B \subset A :\: B.
    by rewrite -covP /cover; apply (bigcup_max B); rewrite // inE.
  rewrite setDE => /subsetIP [_].
  by rewrite -disjoints_subset -setI_eq0 setIid.
rewrite -lt0n card_gt0 in Bne0.
have Hcons : [set X in B :: P] = B |: [set X in P].
  by apply/setP => X; rewrite !inE.
exists (B :: P); split => /=; [|apply/and3P; split|].
- by rewrite Puniq BninP.
- rewrite Hcons /cover big_setU1 /= ?inE // -/(cover _) covP.
  by rewrite -{1}(setIidPr BsubA) setID.
- move: trivP; rewrite /trivIset Hcons.
  rewrite /cover !big_setU1 ?inE //= -/(cover _) => /eqP ->.
  rewrite covP cardsU (_ : B :&: (A :\: B) = set0) ?cards0 ?subn0 //.
  by rewrite setDE setIC -setIA [X in A :&: X]setIC setICr setI0.
- by rewrite !inE negb_or eq_sym Bne0.
- by rewrite Ps.
Qed.

Lemma ex_set_parts_shape (A : {set T}) sh :
  is_part_of_n #|A| sh ->
  exists2 P, partition P A & parts_shape P = sh.
Proof.
rewrite /is_part_of_n /= is_part_sortedE => /andP [/eqP shsum /andP [shsort]].
move=> /(ex_parts_shape shsum) [P [Puniq Ppart Psh]].
exists [set X in P]; first exact: Ppart.
apply (eq_sorted (leT := geq)) => //.
- exact: sort_sorted.
- rewrite /parts_shape -Psh perm_sort; apply: perm_map.
  apply: (uniq_perm_eq (enum_uniq _) Puniq) => x.
  by rewrite mem_enum inE.
Qed.

End SetPartitionShape.
