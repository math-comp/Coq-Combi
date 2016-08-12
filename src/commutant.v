Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple path bigop finset div.
From mathcomp Require Import fingroup perm action gproduct morphism.
From mathcomp Require finmodule.

From Combi Require Import tools partition.

Require Import ssrcomp cycles cycletype.

Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
Proof using. by rewrite -[RHS]imset_id; apply eq_imset => x; rewrite perm1. Qed.

Local Notation "''SC_' i " := (finset (fun x : {set _} => #|x| == i))
    (at level 0).

(* In fingroup.v, this is only defined for fintype bigop
Section Nary.

Variable gT : finGroupType.
Variables (I : Type) (S : seq I) (P : pred I) (F : I -> {group gT}).

Lemma group_set_bigcap : group_set (\bigcap_(i <- S | P i) F i).
Proof using.
by elim/big_rec: _ => [|i G _ gG]; rewrite -1?(insubdK 1%G gG) groupP.
Qed.

Canonical bigcap_group_seq := group group_set_bigcap.

End Nary.
 *)

Section PermOnG.

Variable T : finType.

Definition perm_ong S : {set {perm T}} := [set s | perm_on S s].
Lemma group_set_perm_ong S : group_set (perm_ong S).
Proof using.
  apply/group_setP; split => [| s t]; rewrite !inE;
    [exact: perm_on1 | exact: perm_onM].
Qed.
Canonical perm_ong_group S : {group {perm T}} := Group (group_set_perm_ong S).
Lemma card_perm_ong S : #|perm_ong S| = #|S|`!.
Proof using. by rewrite cardsE /= card_perm. Qed.

End PermOnG.


Section PermCycles.

Variable T : finType.
Implicit Type (s t c : {perm T}).

Lemma triv_part (P : {set {set T}}) (X : {set T}) :
  X \in P -> partition P X -> P = [set X].
Proof using.
move=> HXP /and3P [/eqP Hcov /trivIsetP /(_ X _ HXP) H H0].
apply/setP => Y; rewrite inE; apply/idP/idP => [HYP | /eqP -> //].
rewrite eq_sym; move/(_ Y HYP): H => /contraR; apply.
have /set0Pn [y Hy] : Y != set0
  by apply/negP => /eqP HY; move: H0; rewrite -HY HYP.
apply/negP => /disjoint_setI0/setP/(_ y).
by rewrite !inE Hy -Hcov andbT => /bigcupP; apply; exists Y.
Qed.


Lemma cyclicP c :
  reflect (exists2 x, x \in support c & support c = pcycle c x)
          (cyclic c).
Proof using.
apply (iffP cards1P) => [[sc Hsc] | [x Hx Hsc]].
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

Lemma permX_fix s x n : s x = x -> (s ^+ n) x = x.
Proof using.
move=> Hs; elim: n => [|n IHn]; first by rewrite expg0 perm1.
by rewrite expgS permM Hs.
Qed.

Lemma cycle_cyclic t :
  cyclic t -> cycle t = [set t ^+ i | i : 'I_#|support t|].
Proof using.
move/cyclicP => [x Hx Hsupp]; rewrite Hsupp.
apply/setP => C; apply/cycleP/imsetP => [[i -> {C}] | [i Hi -> {C}]].
- have /(ltn_pmod i) Hmod : 0 < #|pcycle t x|.
    by rewrite card_gt0; apply/set0Pn; exists x; apply: pcycle_id.
  exists (Ordinal Hmod) => //=; apply/permP => y /=.
  case: (boolP (y \in pcycle t x)).
  + by rewrite -eq_pcycle_mem => /eqP <-; exact: pcycle_mod.
  + rewrite -Hsupp in_support negbK => /eqP Ht.
    by rewrite !permX_fix.
- by exists i.
Qed.

Lemma order_cyclic t : cyclic t -> #[t] = #|support t|.
Proof using.
  rewrite /order => Hcy.
  rewrite (cycle_cyclic Hcy) card_imset ?card_ord //.
  move: Hcy => /cyclicP [x Hx Hsupp].
  move=> [i Hi] [j Hj] /= /(congr1 (fun s => s x)) Hij.
  apply val_inj => /=; apply/eqP.
  rewrite -(nth_uniq x _ _ (uniq_traject_pcycle t x)) ?size_traject -?Hsupp //.
  by rewrite !nth_traject // -!permX Hij.
Qed.

Lemma disjoint_support_subset (S1 S2 : {set {perm T}}) :
  S1 \subset S2 -> disjoint_supports S2 -> disjoint_supports S1.
Proof using.
rewrite /disjoint_supports => Hsubs [Htriv Hinj].
split.
- exact: (trivIsetS (imsetS _ Hsubs) Htriv).
- move/subsetP in Hsubs.
  by move=> s t /Hsubs Hs /Hsubs; exact: Hinj.
Qed.

Lemma support_expg s n : support (s ^+ n) \subset support s.
Proof using.
by apply/subsetP => x; rewrite !in_support; apply contra => /eqP/permX_fix ->.
Qed.

Lemma cent1_act_pcycle s t x :
  t \in 'C[s] -> ('P)^* (pcycle s x) t = pcycle s (t x).
Proof using.
  move=> /cent1P Hcom.
  apply/setP => y; apply/imsetP/pcycleP.
  - move=> [z /pcycleP [i -> {z}] -> {y}].
    by exists i => /=; rewrite -!permM (commuteX i Hcom) permM.
  - move=> [i -> {y}].
    exists ((s ^+ i) x)%g; first exact: mem_pcycle.
    by rewrite -!permM (commuteX i Hcom) permM.
Qed.

(* Rewriting of 'C[s] \subset 'N(pcycles s | ('P)^* *)
Lemma cent1_act_on_pcycles s : [acts 'C[s], on pcycles s | ('P)^*].
Proof using.
  apply/subsetP => t Hcent; rewrite /astabs !inE /=.
  apply/subsetP => C; rewrite inE => /imsetP [x _ -> {C}].
  by apply/imsetP; exists (t x); [| apply: cent1_act_pcycle].
Qed.

Lemma cent1_act_on_ipcycles s i :
  [acts 'C[s], on pcycles s :&: 'SC_i | ('P)^*].
Proof using.
  apply/subsetP => t Ht; apply (subsetP (astabsI _ _ _)).
  rewrite inE (subsetP (cent1_act_on_pcycles s)) //=.
  rewrite /astabs !inE /=; apply/subsetP => P; rewrite !inE.
  by rewrite card_setact.
Qed.

Lemma commute_cyclic c t :
  cyclic c -> t \in 'C[c] -> perm_on (support c) t -> exists i, t = c ^+ i.
Proof using.
  move=> /cyclicP [x Hx Hsupp] Hcent1 Hon.
  have /= := cent1_act_pcycle x Hcent1.
  have:= Hx; rewrite -(perm_closed _ Hon).
  move: Hon; rewrite Hsupp -eq_pcycle_mem => Hon /eqP -> cx_stable.
  move: Hcent1 => /cent1P Hcomm.
  have /= := mem_setact ('P) t (pcycle_id c x).
  rewrite cx_stable => /pcycleP [i]; rewrite apermE => Hi.
  exists i; apply/permP => z.
  case: (boolP (z \in (pcycle c x))) => [/pcycleP [j -> {z}]|].
  - by rewrite -!permM -(commuteX j Hcomm) -expgD addnC expgD !permM Hi.
  - move=> Hz; move: Hon => /subsetP/(_ z)/contra/(_ Hz).
    rewrite inE negbK => /eqP ->.
    by move: Hz; rewrite -Hsupp in_support negbK => /eqP /permX_fix ->.
Qed.

Lemma restr_perm_genC C s t :
  C \in psupport s -> t \in 'C[s] -> t \in 'C(pcycles s | ('P)^*) ->
  restr_perm C t \in <[restr_perm C s]>%G.
Proof using.
move=> HC /cent1P Hcomm /astabP Hstab.
apply/cycleP; apply commute_cyclic.
- have: restr_perm C s \in cycle_dec s by apply/imsetP; exists C.
  by move/cyclic_dec.
- apply/cent1P; rewrite /commute.
  have HS := psupport_astabs HC.
  have Ht : t \in 'N(C | 'P).
    rewrite -astab1_set; apply/astab1P; apply Hstab.
    by move: HC; rewrite inE => /andP [].
  rewrite -((morphM (restr_perm_morphism C)) t s) //.
  rewrite -((morphM (restr_perm_morphism C)) s t) //.
  by rewrite Hcomm.
- rewrite support_perm_on (support_restr_perm HC).
  exact: support_restr_perm_incl.
Qed.

Lemma disjoint_support_dprodE (S : {set {perm T}}) :
  disjoint_supports S -> \big[dprod/1]_(s in S) <[s]> = (\prod_(s in S) <[s]>)%G.
Proof using.
move=> [/trivIsetP Htriv Hinj]; apply/eqP/bigdprodYP => /= s Hs.
apply/subsetP => t; rewrite !inE negb_and negbK.
rewrite bigprodGEgen => /gen_prodgP [n [/= f Hf ->{t}]].
apply/andP; split.
- case: (altP (_ =P _)) => //=; apply contra => Hin.
  rewrite support_eq0 -subset0; apply/subsetP => x Hx.
  have [i Hxf] : exists i : 'I_n, x \in support (f i).
    apply/existsP; move: Hx; apply contraLR => /=.
    rewrite negb_exists => /forallP Hall.
    rewrite in_support negbK /index_enum /=.
    elim: (Finite.enum _) => [| i l IHl]; first by rewrite big_nil perm1.
    rewrite big_cons permM.
    by have := Hall i; rewrite in_support negbK => /eqP ->.
  move/(_ i): Hf => /bigcupP [/= t /andP [tinS tneqs]].
  rewrite inE => /eqP Hfi; rewrite {}Hfi in Hxf.
  move: Hin Hx => /cycleP [j ->] /(subsetP (support_expg _ _)) Hxs.
  suff : [disjoint support t & support s].
    by rewrite -setI_eq0 => /eqP/setP/(_ x) <-; rewrite inE Hxf Hxs.
  apply Htriv; try exact: mem_imset.
  by move: tneqs; apply contra => /eqP/Hinj ->.
- apply group_prod => i _.
  have:= Hf i => /bigcupP [/= t /andP [tinS sneqt]].
  rewrite inE cent_cycle => /eqP -> {i f Hf}.
  apply/cent1P; apply: support_disjointC.
  apply Htriv; try exact: mem_imset.
  by move: sneqt; apply contra => /eqP/Hinj ->.
Qed.


Lemma restr_perm_commute C s : commute (restr_perm C s) s.
Proof using.
case: (boolP (s \in 'N(C | 'P))) =>
    [HC | /triv_restr_perm ->]; last exact: (commute_sym (commute1 _)).
apply/permP => x; case: (boolP (x \in C)) => Hx; rewrite !permM.
- by rewrite !restr_permE //; move: HC => /astabsP/(_ x)/= ->.
- have:= restr_perm_on C s => /out_perm Hout.
  rewrite (Hout _ Hx) {}Hout //.
  by move: Hx; apply contra; move: HC => /astabsP/(_ x)/= ->.
Qed.

(* TODO: The Hypothesis should not be necessary here *)
Lemma restr_perm_cent_pcycles C s :
  C \in pcycles s -> restr_perm C s \in 'C(pcycles s | ('P)^*).
Proof using.
move=> HC; apply/astabP => X HX.
case: (altP (X =P C)) => [-> |] /=.
- exact: im_restr_perm.
- move: HX => /imsetP [x _ ->{X}] HxC.
  rewrite cent1_act_pcycle; last by apply/cent1P; apply: restr_perm_commute.
  congr pcycle; have:= restr_perm_on C s => /out_perm; apply.
  move: HxC; apply contra; move: HC => /imsetP [y _ ->{C}].
  by rewrite eq_pcycle_mem.
Qed.

Lemma pcyclegrpE s :
  'C_('C[s])(pcycles s | ('P)^* ) = \big[dprod/1]_(c in cycle_dec s) <[c]>.
Proof using.
rewrite disjoint_support_dprodE; last exact: disjoint_cycle_dec.
apply/setP => /= t; apply/idP/idP.
- rewrite inE => /andP [Hcomm Hstab].
  have:= partition_support s => /and3P [/eqP Hcov Htriv _].
  rewrite -(perm_decE (S := psupport s) (s := t)) //; first last.
  + by apply/astabP => C; rewrite /psupport inE => /andP [] /(astabP Hstab).
  + rewrite Hcov; apply/subsetP => x.
    rewrite !in_support (pcycle_fix s); apply contra => /eqP Hx.
    have /(astabP Hstab) : pcycle s x \in pcycles s by apply: mem_imset.
    rewrite Hx => /setP/(_ x).
    rewrite inE eq_refl /= => /imsetP [y].
    by rewrite inE => /eqP -> /=; rewrite apermE => <-.
  + rewrite /cycle_dec bigprodGE.
    apply/group_prod => c /imsetP [C HC ->{c}].
    apply mem_gen; apply/bigcupP; exists (restr_perm C s).
    * by rewrite /perm_dec; apply/imsetP; exists C.
    * exact: restr_perm_genC.
- rewrite bigprodGEgen; apply /subsetP; rewrite gen_subG.
  apply/subsetP => x /bigcupP [/= c /imsetP [C HC ->{c}]].
  move: HC; rewrite 3!inE => /andP [HC _] /eqP -> {x}.
  apply/andP; split.
  + by apply/cent1P; apply: restr_perm_commute.
  + exact: restr_perm_cent_pcycles.
Qed.

Lemma card_pcyclegrpE s :
  #|'C_('C[s])(pcycles s | ('P)^*)| = (\prod_(i <- cycle_type s) i)%N.
Proof using.
  rewrite -(bigdprod_card (esym (pcyclegrpE s))).
  rewrite /cycle_type /= /parts_shape /cycle_dec big_imset /=; first last.
    by move=> u v /support_restr_perm {2}<- /support_restr_perm {2}<- ->.
  rewrite [RHS](eq_big_perm [seq #|(x : {set _})| | x <- enum (pcycles s)]);
    last by apply/perm_eqlP; apply perm_sort.
  rewrite /= [RHS]big_map -big_enum.
  rewrite [RHS](bigID (fun X : {set T} => #|X| == 1%N)) /=.
  rewrite [X in _ = (X * _)%N]big1 ?mul1n; last by move=> i /andP [_ /eqP].
  rewrite [RHS](eq_bigl (mem (psupport s))) /=; first last.
    by move=> C; rewrite /psupport !inE.
  apply eq_bigr => X HX; rewrite -orderE.
  rewrite order_cyclic; last by rewrite /cyclic (psupport_restr HX) cards1.
  by rewrite support_restr_perm.
Qed.

Definition stab_ipcycles s : {set {perm {set T}}} :=
  perm_ong (pcycles s) :&:
    \bigcap_(i : 'I_#|T|.+1) 'N(pcycles s :&: 'SC_i | 'P).
(* stab_ipcycles is canonicaly a group *)
Definition stab_ipcycles_group s := [group of (stab_ipcycles s)].

Definition inpcycles s := restr_perm (pcycles s) \o actperm ('P^*).
(* inpcycles is canonicaly a morphism *)
Definition inpcycles_morph s := [morphism of (inpcycles s)].

Lemma inpcyclesP s t : t \in 'C[s] -> inpcycles s t \in stab_ipcycles s.
Proof using.
move=> Ht; rewrite inE; apply/andP; split.
- by rewrite inE; apply: restr_perm_on.
- apply/bigcapP => [[i Hi] _] /=; apply/astabsP => X.
  have/actsP/(_ t Ht X)/= := cent1_act_on_ipcycles s i.
  rewrite !inE !apermE; case: (boolP (X \in pcycles s)) => /= [HX| HX _].
  + rewrite restr_permE // ?actpermE // {X HX}.
    apply/astabsP => X /=; rewrite apermE actpermE /=.
    exact: (actsP (cent1_act_on_pcycles s)).
  + rewrite (out_perm (restr_perm_on _ _) HX).
    by move: HX => /negbTE ->.
Qed.

Section CM.

Variables (s : {perm T}) (P : {perm {set T}}).

Lemma stab_ipcycles_stab :
  (if P \in stab_ipcycles s then P else 1) @: pcycles s \subset pcycles s.
Proof using.
case: (boolP (_ \in _)) => [|_].
- by rewrite !inE => /andP [] /im_perm_on -> _.
- by rewrite (eq_imset (g := id)) ?imset_id // => x; rewrite perm1.
Qed.

Lemma stab_ipcycles_homog :
  {in pcycles s, forall C,
       #|(if P \in stab_ipcycles s then P else 1) C| = #|C| }.
Proof using.
case: (boolP (_ \in _)) => [|_].
- rewrite inE => /andP [_ /bigcapP HP] C HC; rewrite /inpcycles /=.
  have:= subsetT C => /subset_leqif_cards []; rewrite -ltnS cardsT => cardC _.
  move/(_ (Ordinal cardC) isT): HP => /= /astabsP/(_ C).
  by rewrite !inE HC eq_refl /= => /andP [_ /eqP].
- by move=> C _; rewrite perm1.
Qed.

Local Definition stab_ipcycles_pcyclemap :=
  PCycleMap stab_ipcycles_stab stab_ipcycles_homog.
Local Definition stab_ipcycles_map := cymap stab_ipcycles_pcyclemap.

Lemma stab_ipcycles_map_inj : injective stab_ipcycles_map.
Proof using. by apply: cymap_inj => X Y /=; case: (P \in _); apply perm_inj. Qed.
Definition permcycles := perm stab_ipcycles_map_inj.

Lemma permcyclesC : commute permcycles s.
Proof using. apply esym; apply/permP => x; rewrite !permM !permE; exact: cymapP. Qed.

Lemma permcyclesP : permcycles \in 'C[s].
Proof using. apply/cent1P; exact: permcyclesC. Qed.

Lemma pcycle_permcycles x :
  P \in stab_ipcycles s ->
  pcycle s (permcycles x) = P (pcycle s x).
Proof using. by rewrite permE pcycle_cymap /= => ->. Qed.

End CM.

Lemma permcyclesM s :
  {in stab_ipcycles s &, {morph permcycles s : x y / x * y}}.
Proof using.
move=> /= P Q HP HQ /=; apply/permP => X.
rewrite permM !permE -[RHS]/((_ \o _) X).
apply esym; apply cymap_comp => C HC /=.
by rewrite groupM // HP HQ permM.
Qed.
Canonical permpcycles_morphism s := Morphism (permcyclesM (s := s)).

Lemma permcyclesK s :
  {in stab_ipcycles s, cancel (permcycles s) (inpcycles s)}.
Proof using.
move=> /= P HP; apply/permP => C /=.
rewrite /inpcycles /=.
case: (boolP (C \in pcycles s)) => HC.
- rewrite !restr_permE // ?actpermE /=; first last.
    apply/astabsP => {C HC} C; rewrite /= apermE actpermE /=.
    apply (actsP (cent1_act_on_pcycles s)).
    exact: permcyclesP.
  move: HC => /imsetP [x _ ->{C}].
  rewrite cent1_act_pcycle; last exact: permcyclesP.
  exact: pcycle_permcycles.
- rewrite (out_perm (restr_perm_on _ _) HC).
  by move: HP; rewrite inE => /andP []; rewrite inE => /out_perm ->.
Qed.

Lemma permcycles_inj s : 'injm (permcycles s).
Proof using. apply/injmP; apply: can_in_inj; exact: permcyclesK. Qed.

Lemma inpcycles_im s : inpcycles s @: 'C[s] = stab_ipcycles s.
Proof using.
apply/setP => /= P.
apply/imsetP/idP => /= [[/= x Hx ->] | HP]; first exact: inpcyclesP.
by exists (permcycles s P); [apply: permcyclesP | rewrite permcyclesK].
Qed.

Lemma trivIset_ipcycles s : trivIset [set pcycles s :&: 'SC_i | i : 'I_#|T|.+1].
Proof using.
apply/trivIsetP => A B /imsetP [i _ ->{A}] /imsetP [j _ ->{B}] Hij.
have {Hij} Hij : i != j by move: Hij; apply contra => /eqP -> .
rewrite -setI_eq0; apply/eqP/setP => x.
rewrite !inE -!andbA; apply/negP => /and4P [_ /eqP -> _] /eqP /val_inj Hieqj.
by rewrite Hieqj eq_refl in Hij.
Qed.

Lemma cover_ipcycles s :
  cover [set pcycles s :&: 'SC_i | i : 'I_#|T|.+1] = pcycles s.
Proof using.
apply/setP => C; apply/bigcupP/idP => [[/= X] | Hx].
- by move/imsetP => [/= i _ ->{X}]; rewrite inE => /andP [].
- have:= subsetT C => /subset_leqif_cards []; rewrite -ltnS cardsT => cardC _.
  exists (pcycles s :&: 'SC_(Ordinal cardC)); first exact: mem_imset.
  by rewrite !inE Hx /=.
Qed.

Lemma stab_ipcyclesE_prod s :
  stab_ipcycles s = (\prod_(i : 'I_#|T|.+1) perm_ong_group (pcycles s :&: 'SC_i))%G.
Proof using.
apply/setP => t.
rewrite inE bigprodGE; apply/andP/idP => [| Ht].
- move=> [Ht /bigcapP Hcyi].
  rewrite -(perm_decE (s := t) (trivIset_ipcycles s)); first last.
  + apply/astabP => /= CS /imsetP [/= i _ ->{CS}].
    apply/astab1P; rewrite astab1_set; exact: Hcyi.
  + by move: Ht; rewrite inE -support_perm_on cover_ipcycles.
  apply group_prod => u /imsetP [/= X /imsetP [/= i _ ->{X}] ->{u}].
  apply mem_gen; apply/bigcupP; exists i; first by [].
  by rewrite inE; exact: restr_perm_on.
split; move: t Ht; apply/subsetP; rewrite gen_subG;
  apply/subsetP => /= P /bigcupP [/= i _]; rewrite inE => HP.
- move: HP; rewrite !inE !support_perm_on => /subset_trans; apply.
  exact: subsetIl.
- (* TODO: check here *)
  apply/bigcapP => /= j _; apply/astabsP => /= X; rewrite apermE.
  case: (altP (P X =P X)) => [-> //| HPX].
  have:= HP => /subsetP/(_ X); rewrite inE => /(_ HPX) H.
  have:= H; rewrite -(perm_closed _ HP).
  by move: H; rewrite !inE => /andP [-> /eqP ->] /andP [-> /eqP ->].
Qed.

Lemma stab_ipcyclesE s :
  stab_ipcycles s = \big[dprod/1]_(i : 'I_#|T|.+1) perm_ong (pcycles s :&: 'SC_i).
Proof using.
rewrite stab_ipcyclesE_prod; apply/esym/eqP/bigdprodYP => i /= _.
apply/subsetP => /= t Ht; rewrite !inE negb_and negbK.
have {Ht} : t \in perm_ong (pcycles s :&: [set x : {set T} | #|x| != i]).
  move: Ht; rewrite bigprodGE => /gen_prodgP [n [/= f Hf ->{t}]].
  apply group_prod => j _; move/(_ j): Hf => /bigcupP [k Hk].
  rewrite !inE /perm_on => /subset_trans; apply; apply setIS.
  by apply/subsetP => C; rewrite !inE => /eqP ->.
rewrite inE => on_neqi; apply/andP; split.
- case: (altP (_ =P _)) => //=; apply contra => on_eqi.
  apply/eqP/permP => C; rewrite perm1.
  case: (boolP (#|C| == i)) => [HC | /negbTE HC].
  + by rewrite (out_perm on_neqi) // !inE HC andbF.
  + by rewrite (out_perm on_eqi) // !inE HC andbF.
- apply/centP => /= u; rewrite inE support_perm_on => /subsetP on_eqi.
  move: on_neqi; rewrite support_perm_on => /subsetP => on_neqi.
  apply support_disjointC; rewrite -setI_eq0; apply/eqP/setP => x.
  rewrite inE [RHS]inE; apply/negP => /andP [].
  move=> /on_neqi; rewrite 2!inE => /andP [_ /negbTE Hcard].
  move=> /on_eqi; rewrite 2!inE => /andP [_].
  by rewrite Hcard.
Qed.

Lemma card_stab_ipcycles s :
  #|stab_ipcycles s| =
    (\prod_(i <- iota 1 #|T|) (count_mem i (cycle_type s))`!)%N.
Proof using.
rewrite -(bigdprod_card (esym (stab_ipcyclesE s))).
rewrite [RHS](_ : _ =
              (\prod_(i <- iota 0 #|T|.+1) (count_mem i (cycle_type s))`!)%N).
- rewrite -val_enum_ord big_map /index_enum enumT.
  apply eq_bigr => [[i Hi]] _ /=.
  rewrite card_perm_ong /parts_shape; congr (_)`!.
  have:= perm_sort geq [seq #|(x : {set T})| | x <- enum (pcycles s)].
  move/perm_eqlP/perm_eqP ->.
  rewrite !cardE -size_filter /= /enum_mem.
  rewrite filter_map size_map -filter_predI; congr size.
  by apply eq_filter => C; rewrite !inE andbC.
- rewrite /= big_cons.
  suff /count_memPn -> : 0 \notin (parts_shape (pcycles s))
      by rewrite fact0 mul1n.
  rewrite mem_sort /parts_shape.
  apply/negP => /mapP [C]; rewrite mem_enum => /imsetP [x _ ->{C}] /eqP.
  (* TODO Make a lemma here *)
  apply/negP; rewrite eq_sym -lt0n.
  by rewrite card_gt0; apply/set0Pn; exists x; exact: pcycle_id.
Qed.

Lemma conj_pcyclegrp s y z :
  y \in 'C[s] ->
    z \in 'C_('C[s])(pcycles s | ('P)^*) ->
    z ^ y \in 'C_('C[s])(pcycles s | ('P)^*).
Proof using.
move=> Hy; rewrite inE => /andP [zC /astabP zCpcycles].
have /= HyV := groupVr Hy.
rewrite inE; apply/andP; split.
- by apply groupM; last exact: groupM.
- apply/astabP => C /imsetP [x _ ->{C}].
  rewrite !actM /= cent1_act_pcycle // zCpcycles; last exact: mem_imset.
  by rewrite -cent1_act_pcycle // -!actM mulVg act1.
Qed.

Lemma inpcycles1 s t : t \in 'C(pcycles s | ('P)^*) -> inpcycles s t = 1.
Proof using.
move=> Ht; have tfix := astab_act Ht.
apply/permP => /= X; rewrite /inpcycles perm1.
case: (boolP (X \in pcycles s)) => HX.
- rewrite restr_permE //= ?actpermE ?tfix // {X HX}.
  apply/astabsP => X /=; rewrite actpermK.
  apply astabs_act; move: Ht; apply/subsetP; exact: astab_sub.
- exact: (out_perm (restr_perm_on _ _ ) HX).
Qed.

Lemma cent1_permE s :
  'C_('C[s])(pcycles s | ('P)^* ) ><| (permcycles s) @* (stab_ipcycles s) = 'C[s].
Proof using.
apply/sdprod_normal_complP.
- apply/normalP; split; first exact: subsetIl.
  move=> /= y Hy; apply/setP => /= x; have /= HyV := groupVr Hy.
  apply/imsetP/idP => [[/= z Hz] ->{x} | Hx].
  + exact: conj_pcyclegrp.
  + exists (x ^ (y^-1)); last by rewrite conjgKV.
    exact: conj_pcyclegrp.
set GP := bigcap_group _ _.
rewrite inE; apply/andP; split.
- apply/eqP/trivgP; apply/subsetP => t.
  rewrite 2!inE => /andP [/imsetP [/= P]] {GP}.
  rewrite setIid => HP Ht /andP [] tC tCpcycles; rewrite inE.
  suff : P = 1 by rewrite Ht => ->; rewrite morphism.morph1.
  rewrite -(permcyclesK HP) -Ht {P HP Ht}.
  exact: inpcycles1.
- rewrite /=; apply/eqP/setP => /= t.
  apply/idP/idP => [/mulsgP [/= t' u /imsetP [P]] | Ht].
  + rewrite setIid => HP ->{t'} Hu ->{t}.
    apply groupM; first exact: permcyclesP.
    by move: Hu; rewrite inE => /andP [].
  + pose str := permcycles s (inpcycles s t^-1).
    have Hstr : str \in 'C[s] by apply: permcyclesP.
    rewrite -(mulKg str t); apply mem_mulg.
    * rewrite groupV; apply mem_imset; rewrite setIid.
      by apply: inpcyclesP; apply groupVr.
    * rewrite inE; apply/andP.
      split; first exact: groupM.
      apply/astabP => C /imsetP [x _ ->{C}].
      rewrite !actM /= cent1_act_pcycle //=.
      rewrite pcycle_permcycles; last by apply inpcyclesP; apply groupVr.
      rewrite /inpcycles /= restr_permE; first last.
      - exact: mem_imset.
      - apply/astabsP => X /=; rewrite actpermK.
        apply astabs_act; move: Ht => /groupVr; apply/subsetP => /=.
        exact: cent1_act_on_pcycles.
      by rewrite actpermE /= -actM mulVg act1.
Qed.

Lemma card_cent1_perm s :
  #|'C[s]| = (\prod_(i <- cycle_type s) i *
                  \prod_(i <- iota 1 #|T|) (count_mem i (cycle_type s))`!)%N.
Proof using.
have /sdprod_card <- := cent1_permE s.
rewrite card_pcyclegrpE card_in_imset ?setIid ?card_stab_ipcycles //.
apply: can_in_inj; exact: permcyclesK.
Qed.

Lemma card_class_perm s :
  #|class s [set: {perm T}]| =
  (#|T|`! %/
    (\prod_(i <- cycle_type s) i *
     \prod_(i <- iota 1 #|T|) (count_mem i (cycle_type s))`!))%N.
Proof using.
rewrite -card_cent1_perm -index_cent1 /= -divgI.
rewrite (eq_card (B := perm_on setT)); first last.
  move=> p; rewrite inE unfold_in /perm_on /=.
  apply/esym/subsetP => i _; by rewrite in_set.
rewrite card_perm cardsE setTI; congr (_ %/ #|_|)%N.
by rewrite /= setTI.
Qed.

End PermCycles.

Require Import cycletype.

Lemma card_class_of_part n (l : intpartn n) :
  #|class_of_partCT l| =
    (n`! %/ (\prod_(i <- l) i * \prod_(i <- iota 1 n) (count_mem i l)`!))%N.
Proof using.
rewrite /class_of_partCT card_class_perm perm_of_partCTP /=.
by rewrite intpartn_castE /= card_ord.
Qed.


(* NOTE : astabs_act !!!! TODO check if this cannot simplify proofs *)
