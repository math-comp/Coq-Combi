Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial.
From mathcomp Require Import fingroup perm morphism action ssralg.
From mathcomp Require finmodule.

From Combi Require Import symgroup partition Greene tools sorted.

From Combi Require Import ordcast. (* TODO : for imset_inj *)

Reserved Notation "#{ x }" (at level 0, x at level 10, format "#{ x }").

Set Implicit Arguments.
Unset Strict Implicit.

Import GroupScope.

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

Notation "#{ x }" :=  #|(x: {set _})|
                      (at level 0, x at level 10, format "#{ x }").

Lemma imset1 (T : finType) (S : {set T}) : [set fun_of_perm 1 x | x in S] = S.
Proof using.
by rewrite -[RHS]imset_id; apply eq_imset => x; rewrite perm1.
Qed.

Lemma disjoint_imset (T1 T2 : finType) (f : T1 -> T2) (A B : {set T1}) :
  injective f ->
  [disjoint A & B] -> [disjoint [set f x | x in A] & [set f x | x in B]].
Proof using.
rewrite -!setI_eq0 => Hinj /eqP Hdisj.
rewrite -imsetI; last by move=> x y _ _; exact: Hinj.
by rewrite imset_eq0 Hdisj.
Qed.

Lemma uniq_next (T : eqType) (p : seq T) : uniq p -> injective (next p).
Proof using.
move=> Huniq x y Heq.
by rewrite -(prev_next Huniq x) Heq prev_next.
Qed.


Section CastSn.

Definition cast_perm_val m n (eq_m_n : m = n) (s : 'S_m) :=
  fun x : 'I_n => cast_ord eq_m_n (s (cast_ord (esym eq_m_n) x)).

Fact cast_perm_proof m n eq_m_n s : injective (@cast_perm_val m n eq_m_n s).
Proof using. by move=> x y /cast_ord_inj/perm_inj/cast_ord_inj. Qed.
Definition cast_perm m n eq_m_n s : 'S_n :=
  perm (@cast_perm_proof m n eq_m_n s).

Lemma cast_permE m n eq_m_n (s : 'S_m) i :
  @cast_ord m n eq_m_n (s i) = (cast_perm eq_m_n s) (cast_ord eq_m_n i).
Proof using. by rewrite permE /cast_perm_val cast_ordK. Qed.

Lemma cast_perm_id n eq_n s : cast_perm eq_n s = s :> 'S_n.
Proof using.
by apply/permP => i /=; rewrite permE /cast_perm_val !cast_ord_id.
Qed.

Lemma cast_permK m n eq_m_n :
  cancel (@cast_perm m n eq_m_n) (cast_perm (esym eq_m_n)).
Proof using.
move=> s /=; apply/permP => i /=; do 2 rewrite permE /cast_perm_val.
by rewrite esymK !cast_ordK.
Qed.

Lemma cast_permKV m n eq_m_n :
  cancel (cast_perm (esym eq_m_n)) (@cast_perm m n eq_m_n).
Proof using. move=> s /=; rewrite -{1}(esymK eq_m_n); exact: cast_permK. Qed.

Lemma cast_perm_inj m n eq_m_n : injective (@cast_perm m n eq_m_n).
Proof using. exact: can_inj (cast_permK eq_m_n). Qed.

Lemma cast_perm_morphM m n eq_m_n :
  {morph @cast_perm m n eq_m_n : x y / x * y >-> x * y}.
Proof using.
rewrite /cast_perm => /= s1 s2; apply /permP => /= i.
apply val_inj => /=.
by rewrite permM /= !permE /cast_perm_val cast_ordK permM.
Qed.
Canonical morph_of_cast_perm m n eq_m_n :=
  Morphism (D := setT) (in2W (@cast_perm_morphM m n eq_m_n)).

Lemma isom_cast_perm m n eq_m_n : isom setT setT (@cast_perm m n eq_m_n).
Proof using.
apply/isomP; split.
- apply/injmP=> i j _ _; exact: cast_perm_inj.
- apply/setP => /= s; rewrite inE.
  apply/imsetP; exists (cast_perm (esym eq_m_n) s); first by rewrite !inE.
  by rewrite /= cast_permKV.
Qed.

End CastSn.

Section SSRComplements.

Variable T : finType.
Variables (R : Type) (idx : R) (op : R -> R -> R) (F : T -> R).
Implicit Type (s : {perm T}) (X : {set T}) (P : {set {set T}}).

Lemma partition0P P : reflect (P = set0) (partition P set0).
Proof using.
  apply (iffP and3P) => [[/eqP Hcov _ H0] | ->].
  - case: (set_0Vmem P) => [// | [X HXP]].
    exfalso; suff HX : X = set0 by subst X; rewrite HXP in H0.
    by apply/eqP; rewrite -subset0; rewrite -Hcov (bigcup_max X).
  - by split; rewrite ?inE // /trivIset /cover !big_set0 ?cards0.
Qed.

Lemma triv_part P X : X \in P -> partition P X -> P = [set X].
Proof using.
move=> HXP /and3P [/eqP Hcov /trivIsetP /(_ X _ HXP) H H0].
apply/setP => Y; rewrite inE; apply/idP/idP => [HYP | /eqP -> //].
rewrite eq_sym; move/(_ Y HYP): H => /contraR; apply.
have /set0Pn [y Hy] : Y != set0
  by apply/negP => /eqP HY; move: H0; rewrite -HY HYP.
apply/negP => /disjoint_setI0/setP/(_ y).
by rewrite !inE Hy -Hcov andbT => /bigcupP; apply; exists Y.
Qed.

Lemma permX_fix s x n : s x = x -> (s ^+ n) x = x.
Proof using.
move=> Hs; elim: n => [|n IHn]; first by rewrite expg0 perm1.
by rewrite expgS permM Hs.
Qed.

Lemma setactC (aT : finGroupType) (D : {set aT})
      (rT : finType) (to : action D rT) S a :
  to^* (~: S) a = ~: to^* S a.
Proof using.
apply/eqP; rewrite eqEcard; apply/andP; split.
- apply/subsetP => x /imsetP [y]; rewrite !inE => Hy -> {x}.
  by move: Hy; apply contra => /imsetP [z Hz] /act_inj ->.
- rewrite card_setact [X in _ <= X]cardsCs setCK.
  by rewrite cardsCs setCK card_setact.
Qed.

Lemma card_pcycle_neq0 s x : #|pcycle s x| != 0.
Proof using.
by rewrite -lt0n card_gt0; apply/set0Pn; exists x; exact: pcycle_id.
Qed.

Lemma pcyclePmin s x y :
  y \in pcycle s x -> exists2 i, i < (#[s])%g & y = (s ^+ i)%g x.
Proof using. by move=> /imsetP [z /cyclePmin[ i Hi ->{z}] ->{y}]; exists i. Qed.

Lemma pcycleP s x y :
  reflect (exists i, y = (s ^+ i)%g x) (y \in pcycle s x).
Proof using.
  apply (iffP idP) => [/pcyclePmin [i _ ->]| [i ->]]; last exact: mem_pcycle.
  by exists i.
Qed.

End SSRComplements.


Lemma sumn_sort l S : sumn (sort S l) = sumn l.
Proof using. by have:= perm_sort S l => /perm_eqlP/perm_sumn. Qed.

Lemma count_set_of_card (T : finType) (p : pred nat) (s : {set {set T}}) :
  count p [seq #{x} | x <- enum s] = #|s :&: [set x | p #{x}]|.
Proof using.
  rewrite cardE -size_filter /enum_mem -enumT /=.
  rewrite filter_map size_map; congr size.
  rewrite -filter_predI; apply eq_filter.
  by move=> S; rewrite !inE andbC.
Qed.

From mathcomp Require Import binomial.

Section SetPartitionShape.

Variable T : finType.
Implicit Types (s t : {perm T}) (n : nat).
Implicit Types (A B X : {set T}) (P Q : {set {set T}}).

Definition parts_shape P := sort geq [seq #{X} | X <- enum P].

Lemma parts_shapeP P D :
  partition P D -> is_part_of_n #|D| (parts_shape P).
Proof using.
rewrite /parts_shape => /and3P [/eqP Hcov Htriv Hnon0].
rewrite /is_part_of_n /= is_part_sortedE.
apply/and3P; split.
- by rewrite sumn_sort -sumnE big_map -big_enum -Hcov.
- by apply sort_sorted => m n.
- move: Hnon0; apply contra.
  rewrite mem_sort => /mapP [] x.
  by rewrite mem_enum => Hx /esym/cards0_eq <-.
Qed.

Lemma ex_subset_card B k :
 k <= #{B} -> exists2 A : {set T}, A \subset B & #{A} == k.
Proof using.
rewrite -bin_gt0 -(cards_draws B k) card_gt0 => /set0Pn [x].
rewrite inE => /andP [H1 H2]; by exists x.
Qed.

Lemma ex_parts_shape (s : seq nat) (A : {set T}) :
  sumn s = #|A| -> 0 \notin s ->
  exists P : seq {set T},
    [/\ uniq P, partition [set X in P] A & [seq #{X} | X <- P] = s].
Proof using.
elim: s A => [| i s IHs] A /=.
  move=> /esym/cards0_eq -> _; exists [::]; split => //.
  apply/partition0P; apply/setP => x.
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

Lemma ex_set_parts_shape A (sh : intpartn #|A|) :
  exists2 P, partition P A & parts_shape P = sh.
Proof using.
case: sh => sh.
rewrite /is_part_of_n /= is_part_sortedE => /andP [/eqP shsum /andP [shsort]].
move=> /(ex_parts_shape shsum) [P [Puniq Ppart Psh]].
exists [set X in P]; first exact: Ppart.
apply (eq_sorted (leT := geq)) => //.
- exact: sort_sorted.
- rewrite /parts_shape -Psh perm_sort; apply: perm_map.
  apply: (uniq_perm_eq (enum_uniq _) Puniq) => x.
  by rewrite mem_enum inE.
Qed.

(* TODO rewrite using union_part *)
Lemma parts_shape_union P Q :
  [disjoint P & Q] ->
  parts_shape (P :|: Q) = sort geq (parts_shape P ++ parts_shape Q).
Proof using.
rewrite /parts_shape -setI_eq0 => /eqP disj.
apply/perm_sortP/perm_eqP => // Prd.
have count_sort l : count ^~ (sort geq l) =1 count ^~ l.
  by apply/perm_eqP; rewrite perm_sort perm_eq_refl.
rewrite count_cat !count_sort !count_set_of_card.
rewrite setIUl cardsU -[RHS]subn0; congr(_ - _).
apply/eqP; rewrite cards_eq0 -subset0 -disj.
by apply/subsetP => x; rewrite !inE => /andP [/andP [-> _] /andP [-> _]].
Qed.

End SetPartitionShape.

Lemma parts_shape_inj
      (T1 T2 : finType) (f : T1 -> T2) (A : {set {set T1}}) :
  injective f -> parts_shape [set f @: (x : {set T1}) | x in A] = parts_shape A.
Proof using.
rewrite /parts_shape /= => Hinj.
apply/perm_sortP/perm_eqP => // P.
rewrite !count_set_of_card -(card_imset _ (imset_inj Hinj)).
rewrite imsetI; last by move=> B C _ _; exact: imset_inj.
congr #{_}; apply/setP => S; rewrite !inE.
case: (boolP (S \in (imset _ _))) => //= /imsetP [U _ -> {S}].
rewrite (card_imset _ Hinj).
apply/idP/imsetP => [| [] V].
- by exists U; rewrite // inE.
- by rewrite inE => HP /(imset_inj Hinj) ->.
Qed.
