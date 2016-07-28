Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple path bigop finset.
From mathcomp Require Import fingroup perm action ssralg.
From mathcomp Require finmodule.

From Combi Require Import tools.


Local Notation "''SC_' i " := (finset (fun x : {set _} => #|x| == i))
    (at level 0).

Require Import ssrcomp cycles cycletype.

Set Implicit Arguments.
Unset Strict Implicit.

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

Section PermCycles.

Variable T : finType.
Implicit Type (s t c : {perm T}).

Lemma triv_part (P : {set {set T}}) (X : {set T}) :
  X \in P -> partition P X -> P = [set X].
Proof using.
move=> HXP /and3P [/eqP Hcov /trivIsetP /(_ X _ HXP) H H0].
apply/eqP; rewrite eqEsubset.
apply/andP; split; apply/subsetP => Y; rewrite !inE; last by move/eqP ->.
move=> HYP; rewrite eq_sym; move/(_ Y HYP): H => /contraR; apply.
have /set0Pn [y Hy] : Y != set0
  by apply/negP => /eqP HY; move: H0; rewrite -HY HYP.
apply/negP => /disjoint_setI0/setP/(_ y).
rewrite !inE Hy -Hcov andbT => /bigcupP; apply; by exists Y.
Qed.

Lemma cyclicP c :
  reflect (exists2 x, x \in support c & support c = pcycle c x)
          (cyclic c).
Proof using.
apply (iffP cards1P) => [[sc Hsc]|[x Hx Hsc]].
- have:= partition_support c; rewrite Hsc => /cover_partition.
  rewrite /cover big_set1 => Hsupp; subst sc.
  have : support c != set0.
    rewrite -support_eq0 psupport_eq0 Hsc.
    apply/negP => /eqP Habs.
    by have:= set11 (support c); rewrite Habs in_set0.
  move=> /set0Pn [x Hx]; exists x; first by [].
  have : pcycle c x \in psupport c.
    by rewrite inE mem_imset //= support_card_pcycle.
  by rewrite Hsc in_set1 => /eqP ->.
- exists (pcycle c x); apply triv_part.
  + by rewrite inE mem_imset //= support_card_pcycle.
  + by rewrite -Hsc; exact: partition_support.
Qed.

Lemma commute_cyclic c s :
  cyclic c -> commute c s -> perm_on (support c) s ->
  exists i, s = (c ^+ i)%g.
Proof using.
  move=> /cyclicP [x Hx Hsupp].
  rewrite Hsupp => /commute_sym Hcomm Hon.
  have cx_stable : setact ('P) (pcycle c x) s = (pcycle c x).
    rewrite -Hsupp; apply setC_inj.
    rewrite /support setactC !setCK.
    apply/setP => z; apply/imsetP/afix1P => /= [[y]| /afix1P Hz].
    - move=> /afix1P /= => Hy ->.
      by rewrite -actM Hcomm actM /= Hy.
    - exists z; first by [].
      apply/eqP; move: Hz => /afix1P /= /eqP.
      rewrite -[_ == _]negbK -in_support Hsupp eq_sym; apply contraR => H.
      by move: Hon => /subsetP/(_ z); rewrite inE; apply.
  have /= := mem_setact ('P) s (pcycle_id c x).
  rewrite cx_stable => /pcycleP [i Hi].
  exists i; apply/permP => z.
  case: (boolP (z \in (pcycle c x))) => [/pcycleP [j -> {z}]|].
  - by rewrite -!permM -(commuteX j Hcomm) -expgD addnC expgD !permM -{}Hi.
  - move=> Hz; move: Hon => /subsetP/(_ z)/contra/(_ Hz).
    rewrite inE negbK => /eqP ->.
    move: Hz; rewrite -Hsupp in_support negbK => /eqP Hz.
    elim: i {Hi} => [/=|i IHi]; first by rewrite expg0 perm1.
    by rewrite expgS permM Hz.
Qed.

Lemma commute_pcycle_stable s t :
  commute s t -> t \in ('N(pcycles s | ('P)^*))%g.
Proof using.
  rewrite /astabs !inE /= => /commute_sym Hcomm.
  apply/subsetP => C; rewrite inE => /imsetP [x _ -> {C}].
  apply/imsetP; exists (t x); first by [].
  apply/setP => y; apply/imsetP/pcycleP.
  - move=> [z /pcycleP [i -> {z}] -> {y}].
    by exists i => /=; rewrite -!permM (commuteX i Hcomm) permM.
  - move=> [i -> {y}].
    exists ((s ^+ i) x)%g; first exact: mem_pcycle.
    by rewrite -!permM (commuteX i Hcomm) permM.
Qed.

Lemma commute_pcycle_card_stable s t :
  commute s t ->
  forall i : nat, t \in ('N(pcycles s :&: 'SC_i | ('P)^*))%g.
Proof using.
  move=> /commute_pcycle_stable Hcom i.
  apply (subsetP (astabsI _ _ _)); rewrite inE Hcom /=.
  rewrite /astabs !inE /=; apply/subsetP => P; rewrite !inE.
  by rewrite card_setact.
Qed.

Definition on_pcycles s t : {perm {set T}} :=
  restr_perm (pcycles s) (actperm ('P^*) t).

