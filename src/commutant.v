Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple path bigop finset.
From mathcomp Require Import fingroup perm action ssralg.
From mathcomp Require finmodule.

From Combi Require Import tools.

Require Import ssrcomp cycles cycletype.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* TODO : Look at the proof of astabsC *)
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

Lemma imset1 (T : finType) (S : {set T}) : [set fun_of_perm 1 x | x in S] = S.
Proof. by rewrite -[RHS]imset_id; apply eq_imset => x; rewrite perm1. Qed.

Local Notation "''SC_' i " := (finset (fun x : {set _} => #|x| == i))
    (at level 0).

Open Scope group_scope.

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
  exists i, s = c ^+ i.
Proof using.
  move=> /cyclicP [x Hx Hsupp].
  rewrite Hsupp => /commute_sym Hcomm Hon.
  have cx_stable : ('P)^* (pcycle c x) s = (pcycle c x).
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

Variable s : {perm T}.

Lemma cent1_act_pcycle t x :
  t \in 'C[s] -> ('P)^* (pcycle s x) t = pcycle s (t x).
Proof.
  move=> /cent1P Hcom.
  apply/setP => y; apply/imsetP/pcycleP.
  - move=> [z /pcycleP [i -> {z}] -> {y}].
    by exists i => /=; rewrite -!permM (commuteX i Hcom) permM.
  - move=> [i -> {y}].
    exists ((s ^+ i) x)%g; first exact: mem_pcycle.
    by rewrite -!permM (commuteX i Hcom) permM.
Qed.

(* Rewriting of 'C[s] \subset 'N(pcycles s | ('P)^* *)
Lemma cent1_act_on_pcycles : [acts 'C[s], on pcycles s | ('P)^*].
Proof using.
  apply/subsetP => t Hcent; rewrite /astabs !inE /=.
  apply/subsetP => C; rewrite inE => /imsetP [x _ -> {C}].
  apply/imsetP; exists (t x); first by [].
  exact: cent1_act_pcycle.
Qed.

Lemma cent1_act_on_pcyclesi i :
  [acts 'C[s], on pcycles s :&: 'SC_i | ('P)^*].
Proof using.
  apply/subsetP => t Ht; apply (subsetP (astabsI _ _ _)).
  rewrite inE (subsetP cent1_act_on_pcycles) //=.
  rewrite /astabs !inE /=; apply/subsetP => P; rewrite !inE.
  by rewrite card_setact.
Qed.

Section CM.

Variable t : {perm T}.

Definition setact_cent1 : {perm {set T}} :=
  if t \in 'C[s] then actperm ('P^*) t else 1.

Lemma on_pcycles_stab : setact_cent1 @: pcycles s \subset pcycles s.
Proof using.
rewrite /setact_cent1.
case: (boolP (t \in 'C[s])) => Ht; last by rewrite imset1.
apply/subsetP => X /imsetP [Y HY -> {X}].
move: Ht => /groupVr/(acts_act cent1_act_on_pcycles) <-.
by rewrite actpermE -actM mulgV act1.
Qed.

Lemma on_pcycles_homog :
  {in pcycles s, forall C, #|setact_cent1 C| = #|C| }.
Proof using.
rewrite /setact_cent1 => C _.
case: (boolP (t \in 'C[s])) => Ht; last by rewrite perm1.
rewrite actpermE; apply: card_imset; exact: act_inj.
Qed.

Definition comm_on_pcycles_map := PCycleMap on_pcycles_stab on_pcycles_homog.
Definition comm_cymap := cymap comm_on_pcycles_map.

Lemma comm_cymap_inj : injective comm_cymap.
Proof.
apply: cymap_inj; rewrite /= /setact_cent1.
by case: (t \in 'C[s]); apply perm_inj.
Qed.
Definition cyperm := perm comm_cymap_inj.

End CM.

Lemma cypermP t :
  t \in 'C[s] -> t * (cyperm t^-1) \in 'C(pcycles s | ('P)^*).
Proof.
move=> Ht; have:= Ht; rewrite -groupV => HtV.
apply/astabP => X /imsetP [x _ -> {X}].
apply /setP => y; apply/imsetP/idP => [[z Hz -> {y}] | Hy] /=.
- rewrite apermE permM -eq_pcycle_mem /cyperm permE /comm_cymap /=.
  rewrite pcycle_cymap /= /setact_cent1 HtV actpermE /=.
  by rewrite cent1_act_pcycle // permK eq_pcycle_mem.
- exists (((cyperm t) * t^-1) y).
  + rewrite -eq_pcycle_mem permM -cent1_act_pcycle //.
    rewrite /cyperm permE /comm_cymap /= pcycle_cymap /=.
    by rewrite /setact_cent1 Ht actpermE -actM mulgV act1 eq_pcycle_mem.
  + rewrite apermE !permE /= permKV.
    rewrite /cyperm /= !permE /comm_cymap /=.
    rewrite -[RHS]/((_ \o _) y) (cymap_comp (CMuw := CMid s)) ?cymap_id //.
    by move=> C HC; rewrite /= /setact_cent1 Ht HtV !actpermE -actM mulgV act1.
Qed.

Definition bijbla t : {perm {set T}} * {perm T} :=
  (setact_cent1 t,  t * (cyperm t^-1)).


End PermCycles.

(*
Definition cyact := (fun S => comm_cymap^~ S).

Lemma cyact_is_action : is_action 'C[s] cyact.
Proof.
rewrite /cyact; split => [t X Y | X].
- case: (boolP (t \in 'C[s])) => Ht.
  + 
case: boolP.

have Cact t : t\in 'C[s] -> actperm ('P)^* t \in 'N(pcycles s | 'P).
  by rewrite actpermset_normE; exact: (subsetP cent1_act_on_pcycles).
rewrite /act_on_pcycles /on_pcycles => u v Hu Hv.
case: (boolP (X \in pcycles s)) => HX.
- rewrite !(restr_permE _ HX); first last.
    + by apply: Cact; apply: groupM.
    + exact: Cact.
  rewrite actpermM // permM restr_permE //; first exact: Cact.
  by rewrite (astabs_act _ (Cact u Hu)).
- by rewrite !(out_perm (restr_perm_on _ _)).
Qed.
Canonical pcyact := Action act_on_pcyclesP.

Lemma actpermset_normE (X : {set {set T}}) t :
  (actperm ('P)^* t \in 'N(X | 'P)) = (t \in 'N(X | ('P)^* )).
Proof.
  by apply/idP/idP => /astabsP H; apply/astabsP => Y;
     rewrite -[RHS]H /= apermE actpermE.
Qed.

Definition on_pcycles t : {perm {set T}} :=
  restr_perm (pcycles s) (actperm ('P^* ) t).
Definition act_on_pcycles := (fun S => on_pcycles^~ S).

Lemma on_pcycles1 : on_pcycles 1 = 1.
Proof.
have actsetid (X : {set T}) : actperm ('P^* ) 1 X = X.
  rewrite actpermE /= setactE /=.
  rewrite (eq_imset (g := id)) ?imset_id // => x.
  by rewrite apermE perm1.
apply/permP=> X /=; case: (boolP (X \in pcycles s)) => HX.
- rewrite (restr_permE _ HX); first by rewrite perm1 actsetid.
  rewrite actpermset_normE.
  apply (subsetP (astab_sub _ _)); exact: group1.
- by rewrite perm1 /on_pcycles (out_perm (restr_perm_on _ _)).
Qed.

Lemma act_on_pcyclesP : is_action 'C[s] act_on_pcycles.
Proof.
split => [t X Y /perm_inj //| X].
have Cact t : t\in 'C[s] -> actperm ('P)^* t \in 'N(pcycles s | 'P).
  by rewrite actpermset_normE; exact: (subsetP cent1_act_on_pcycles).
rewrite /act_on_pcycles /on_pcycles => u v Hu Hv.
case: (boolP (X \in pcycles s)) => HX.
- rewrite !(restr_permE _ HX); first last.
    + by apply: Cact; apply: groupM.
    + exact: Cact.
  rewrite actpermM // permM restr_permE //; first exact: Cact.
  by rewrite (astabs_act _ (Cact u Hu)).
- by rewrite !(out_perm (restr_perm_on _ _)).
Qed.
Canonical pcyact := Action act_on_pcyclesP.

Lemma acts_pcyact : [acts 'C[s], on pcycles s | pcyact].
Proof.
  apply/subsetP => t.
  
Lemma on_pcycle_stab t : t \in 'C[s] -> on_pcycles t @: pcycles s \subset pcycles s.
Proof.
  move=> Ht; apply/subsetP => X.
  have := acts_act act_on_pcycles.
  acts_on
  have := act_on_pcycles t.
  rewrite /on_pcycles;                           apply/subsetP => Ctmp /imsetP [C HC -> {Ctmp}].
  rewrite restr_permE //=.
  - by rewrite actpermE (astabs_act C commute_pcycle_stable).
  - rewrite -astab1_set !inE /= {C HC}.
    apply/subsetP => Ctmp; rewrite !inE => /eqP -> {Ctmp}.
    apply/eqP/setP => C; apply/imsetP/idP => [[D HD -> {C}] | HC] /=.
    + by rewrite actpermK /= (astabs_act D commute_pcycle_stable).
    + exists ((('P)^* )%act C (t^-1)%g).
      * by rewrite (astabs_act C (groupVr commute_pcycle_stable)).
      * by rewrite actpermK -actM mulVg act1.
Qed.

              fs_homog : {in pcycles s, forall C, #|fs C| = #|C| }
*)
