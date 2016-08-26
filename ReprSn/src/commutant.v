Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple path bigop finset div.
From mathcomp Require Import fingroup perm action gproduct morphism.

From Combi Require Import tools partition.

Require Import ssrcomp cycles cycletype.

Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Hint Resolve pcycle_id.

Local Notation "''SC_' i " := (finset (fun x => #{x} == i))
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
Implicit Type (s t c : {perm T}).

Definition perm_ong S : {set {perm T}} := [set s | perm_on S s].
Lemma group_set_perm_ong S : group_set (perm_ong S).
Proof using.
  apply/group_setP; split => [| s t]; rewrite !inE;
    [exact: perm_on1 | exact: perm_onM].
Qed.
Canonical perm_ong_group S : {group {perm T}} := Group (group_set_perm_ong S).
Lemma card_perm_ong S : #|perm_ong S| = #|S|`!.
Proof using. by rewrite cardsE /= card_perm. Qed.

Lemma perm_ongE S : perm_ong S = 'C(~:S | 'P).
Proof using.
apply/setP => s; rewrite inE; apply/idP/astabP => [Hperm x | Hstab].
- by rewrite inE /= apermE => /out_perm; apply.
- apply/subsetP => x; rewrite unfold_in; apply contraR => H.
  by move/(_ x): Hstab; rewrite inE /= apermE => ->.
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

End PermOnG.


Section PermCycles.

Variable T : finType.
Implicit Type (s t c : {perm T}).

Lemma disjoint_support_dprodE (S : {set {perm T}}) :
  disjoint_supports S ->
  (\big[dprod/1]_(s in S) <[s]>) = (\prod_(s in S) <[s]>)%G.
Proof using.
move=> [/trivIsetP Htriv Hinj]; apply/eqP/bigdprodYP => /= s Hs.
apply/subsetP => t; rewrite !inE negb_and negbK.
rewrite bigprodGEgen => /gen_prodgP [n [/= f Hf ->{t}]].
apply/andP; split.
- case: (altP (_ =P _)) => //=; apply contra => Hin.
  rewrite support_eq0 -subset0; apply/subsetP => x Hx.
  have [i Hxf] : exists i : 'I_n, x \in support (f i).
    apply/existsP; move: Hx; apply contraLR => /=.
    rewrite negb_exists => /forallP /= Hall; rewrite in_support negbK.
    apply big_rec => [ | i rec _ Hrec]; first by rewrite perm1.
    by have := Hall i; rewrite permM in_support negbK => /eqP ->.
  move/(_ i): Hf => /bigcupP [/= t /andP [tinS tneqs]].
  rewrite inE => /eqP Hfi; rewrite {}Hfi in Hxf.
  move: Hin Hx => /cycleP [j ->] {f} /(subsetP (support_expg _ _)) Hxs.
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

Lemma cent1_act_pcycle s t x :
  t \in 'C[s] -> ('P)^* (pcycle s x) t = pcycle s (t x).
Proof using.
move=> /cent1P Hcom.
apply/setP => y; apply/imsetP/pcycleP.
- move=> [z /pcycleP [i -> {z}] -> {y}].
  by exists i => /=; rewrite -!permM (commuteX i Hcom) permM.
- move=> [i -> {y}].
  exists ((s ^+ i) x); first exact: mem_pcycle.
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

Notation "''CC' ( s )" :=
  'C_('C[s])(pcycles s | ('P)^* ) (format "''CC' ( s )") : group_scope.

Lemma restr_perm_genC C s t :
  C \in psupport s -> t \in 'CC(s) -> restr_perm C t \in <[restr_perm C s]>%G.
Proof using.
move=> HC; rewrite inE => /andP [/cent1P Hcomm /astabP Hstab].
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

Lemma stab_pcycle S s :
  s \in 'N(S | 'P) -> forall x, (x \in S) = (pcycle s x \subset S).
Proof using.
move=> Hs x; apply/idP/subsetP => [Hx y /pcycleP [i ->{y}] | Hsubs].
- elim: i => [|i]; first by rewrite expg0 perm1.
  by rewrite expgSr permM; move: Hs => /astabsP <- /=.
- exact: Hsubs (pcycle_id s x).
Qed.

Lemma restr_perm_pcycles S s :
  restr_perm S s \in 'C(pcycles s | ('P)^* ).
Proof using.
case: (boolP (s \in 'N(S | 'P))) => [nSs | /triv_restr_perm -> //].
apply/astabP => /= X /imsetP [x _ ->{X}].
case: (boolP (x \in S)) => Hx.
- apply/setP => y; apply/imsetP/idP => [[z Hz ->{y}] /= | Hy].
  + have:= Hz; rewrite -eq_pcycle_mem => /eqP Hsz.
    rewrite apermE restr_permE //.
    - rewrite -Hsz -{1}(expg1 s); exact: mem_pcycle.
    - by rewrite (stab_pcycle nSs) // Hsz -stab_pcycle.
  + have HsVy : s^-1 y \in pcycle s x.
      by rewrite pcycle_sym -(pcycle_perm _ 1) expg1 permKV pcycle_sym.
    exists ((s ^-1) y); first exact: HsVy.
    rewrite /= apermE restr_permE => //; first by rewrite permKV.
    by move: Hx; rewrite (stab_pcycle nSs) => /subsetP; apply.
- move: nSs; rewrite -astabsC => nSs.
  have: x \in ~: S by rewrite inE.
  rewrite (stab_pcycle nSs) => Hsubs.
  apply/setP => y; apply/imsetP/idP => [[z Hz ->{y}] /= | Hy].
  + rewrite apermE (out_perm (restr_perm_on _ _)) //.
    by have:= subsetP Hsubs z Hz; rewrite inE.
  + exists y; first exact Hy.
    rewrite /= apermE (out_perm (restr_perm_on _ _)) //.
    by have:= subsetP Hsubs y Hy; rewrite inE.
Qed.

Lemma pcyclegrpE s : 'CC(s) = \big[dprod/1]_(c in cycle_dec s) <[c]>.
Proof using.
rewrite disjoint_support_dprodE; last exact: disjoint_cycle_dec.
apply/setP => /= t; apply/idP/idP.
- rewrite inE => /andP [Hcomm Hstab].
  have:= partition_support s => /and3P [/eqP Hcov Htriv _].
  rewrite -(perm_decE (S := psupport s) (s := t)) //; first last.
  + by apply/astabP => C; rewrite /psupport inE => /andP [] /(astabP Hstab).
  + rewrite {}Hcov; apply/subsetP => x.
    rewrite !in_support (pcycle_fix s); apply contra => /eqP Hx.
    have /(astabP Hstab) : pcycle s x \in pcycles s by apply: mem_imset.
    rewrite Hx => /setP/(_ x).
    rewrite inE eq_refl /= => /imsetP [y].
    by rewrite inE => /eqP -> /=; rewrite apermE => <-.
  + rewrite /cycle_dec bigprodGE.
    apply/group_prod => c /imsetP [C HC ->{c}].
    apply mem_gen; apply/bigcupP; exists (restr_perm C s).
    * by rewrite /perm_dec; apply/imsetP; exists C.
    * by apply: restr_perm_genC; rewrite // inE Hcomm Hstab.
- rewrite bigprodGEgen; apply /subsetP; rewrite gen_subG.
  apply/subsetP => x /bigcupP [/= c /imsetP [C HC ->{c}]].
  move: HC; rewrite 3!inE => /andP [HC _] /eqP -> {x}.
  apply/andP; split.
  + by apply/cent1P; apply: restr_perm_commute.
  + exact: restr_perm_pcycles.
Qed.

Lemma card_pcyclegrpE s : #|'CC(s)| = (\prod_(i <- cycle_type s) i)%N.
Proof using.
rewrite -(bigdprod_card (esym (pcyclegrpE s))).
rewrite /cycle_type /= /parts_shape /cycle_dec.
rewrite big_imset /=; last exact: restr_perm_inj.
rewrite [RHS](eq_big_perm [seq #{x} | x <- enum (pcycles s)]);
  last by apply/perm_eqlP; apply perm_sort.
rewrite /= [RHS]big_map -big_enum.
rewrite [RHS](bigID (fun X => #{X} == 1%N)) /=.
rewrite [X in _ = (X * _)%N]big1 ?mul1n; last by move=> i /andP [_ /eqP].
rewrite [RHS](eq_bigl (mem (psupport s))) /=;
  last by move=> C; rewrite /psupport !inE.
apply eq_bigr => X HX; rewrite -orderE.
rewrite order_cyclic; last by rewrite /cyclic (psupport_restr HX) cards1.
by rewrite support_restr_perm.
Qed.

Definition stab_ipcycles s : {set {perm {set T}}} :=
  perm_ong (pcycles s) :&:
    \bigcap_(i : 'I_#|T|.+1) 'N(pcycles s :&: 'SC_i | 'P).
(* stab_ipcycles is canonicaly a group *)

Definition inpcycles s := restr_perm (pcycles s) \o actperm 'P^*.
(* inpcycles is canonicaly a group morphism *)

Section CM.

Variable s : {perm T}.
Implicit Type P : {perm {set T}}.

Lemma stab_ipcycles_stab P :
  (if P \in stab_ipcycles s then P else 1) @: pcycles s \subset pcycles s.
Proof using.
case: (boolP (_ \in _)) => [|_].
- by rewrite !inE => /andP [] /im_perm_on -> _.
- by rewrite (eq_imset (g := id)) ?imset_id // => x; rewrite perm1.
Qed.

Lemma stab_ipcycles_homog P :
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

Local Definition stab_ipcycles_pcyclemap P :=
  PCycleMap (stab_ipcycles_stab P) (stab_ipcycles_homog P).
Local Definition stab_ipcycles_map P := cymap (stab_ipcycles_pcyclemap P).

Lemma stab_ipcycles_map_inj P : injective (stab_ipcycles_map P).
Proof using.
apply (can_inj (g := stab_ipcycles_map P^-1)) => X /=.
rewrite /stab_ipcycles_map cymapK //= {X} => C HC.
rewrite groupV /= -/(stab_ipcycles s).
by case: (boolP (P \in _)) => [| HP]; rewrite ?perm1 ?permK.
Qed.
Definition permcycles P := perm (@stab_ipcycles_map_inj P).

Lemma permcyclesC P : commute (permcycles P) s.
Proof using.
apply esym; apply/permP => x; rewrite !permM !permE; exact: cymapP.
Qed.

Lemma permcyclesP P : (permcycles P) \in 'C[s].
Proof using. apply/cent1P; exact: permcyclesC. Qed.

Lemma pcycle_permcycles P x :
  P \in stab_ipcycles s -> pcycle s (permcycles P x) = P (pcycle s x).
Proof using. by rewrite permE pcycle_cymap /= => ->. Qed.

End CM.

Lemma permcyclesM s :
  {in stab_ipcycles s &, {morph permcycles s : P Q / P * Q}}.
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
apply/setP => /= P; apply/imsetP/idP => /= [[/= x Hx ->] | HP].
- rewrite inE; apply/andP; split.
  + by rewrite inE; apply: restr_perm_on.
  + apply/bigcapP => [[i Hi] _] /=; apply/astabsP => X.
    have/actsP/(_ _ Hx X)/= := cent1_act_on_ipcycles s i.
    rewrite !inE !apermE; case: (boolP (X \in pcycles s)) => /= [HX| HX _].
    * rewrite restr_permE // ?actpermE // {X HX}.
      apply/astabsP => X /=; rewrite apermE actpermE /=.
      exact: (actsP (cent1_act_on_pcycles s)).
    * rewrite (out_perm (restr_perm_on _ _) HX).
      by move: HX => /negbTE ->.
- by exists (permcycles s P); [apply: permcyclesP | rewrite permcyclesK].
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
  stab_ipcycles s =
  (\prod_(i : 'I_#|T|.+1) perm_ong_group (pcycles s :&: 'SC_i))%G.
Proof using.
apply/setP => t.
rewrite inE bigprodGE; apply/andP/idP => [[Ht /bigcapP/(_ _ isT) Hcyi] | Ht].
- rewrite -(perm_decE (s := t) (trivIset_ipcycles s)); first last.
  + apply/astabP => /= CS /imsetP [/= i _ ->{CS}].
    apply/astab1P; rewrite astab1_set; exact: Hcyi.
  + by move: Ht; rewrite inE -support_perm_on cover_ipcycles.
  apply group_prod => u /imsetP [/= X /imsetP [/= i _ ->{X}] ->{u}].
  apply mem_gen; apply/bigcupP; exists i; first by [].
  by rewrite inE; exact: restr_perm_on.
split; move: t Ht; apply/subsetP; rewrite gen_subG;
  apply/subsetP => /= P /bigcupP [/= i _].
- rewrite !inE !support_perm_on => /subset_trans; apply.
  exact: subsetIl.
- rewrite inE => HP.
  apply/bigcapP => /= j _; apply/astabsP => /= X; rewrite apermE.
  case: (altP (P X =P X)) => [-> //| HPX].
  have:= HP => /subsetP/(_ X); rewrite inE => /(_ HPX) H.
  have:= H; rewrite -(perm_closed _ HP).
  by move: H; rewrite !inE => /andP [-> /eqP ->] /andP [-> /eqP ->].
Qed.

Theorem stab_ipcyclesE s :
  stab_ipcycles s = \big[dprod/1]_(i : 'I_#|T|.+1) perm_ong (pcycles s :&: 'SC_i).
Proof using.
rewrite stab_ipcyclesE_prod; apply/esym/eqP/bigdprodYP => i /= _.
apply/subsetP => /= t Ht; rewrite !inE negb_and negbK.
have {Ht} : t \in perm_ong (pcycles s :&: [set x | #{x} != i]).
  move: Ht; rewrite bigprodGE => /gen_prodgP [n [/= f Hf ->{t}]].
  apply group_prod => j _; move/(_ j): Hf => /bigcupP [k Hk].
  rewrite !inE /perm_on => /subset_trans; apply; apply setIS.
  by apply/subsetP => C; rewrite !inE => /eqP ->.
rewrite inE => on_neqi; apply/andP; split.
- case: (altP (t =P 1)) => //=; apply contra => on_eqi.
  apply/eqP/permP => C; rewrite perm1.
  case: (boolP (#|C| == i)) => [HC | /negbTE HC].
  + by rewrite (out_perm on_neqi) // !inE HC andbF.
  + by rewrite (out_perm on_eqi) // !inE HC andbF.
- apply/centP => /= u; move: on_neqi.
  rewrite inE !support_perm_on -[support u \subset _]setCS => on_neqi on_eqi.
  apply support_disjointC; rewrite disjoints_subset.
  apply: (subset_trans on_neqi); apply: (subset_trans _ on_eqi).
  by apply/subsetP => X; rewrite !inE => /andP [ -> ->].
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
  have:= perm_sort geq [seq #{x} | x <- enum (pcycles s)].
  move/perm_eqlP/perm_eqP ->.
  rewrite !cardE -size_filter /= /enum_mem.
  rewrite filter_map size_map -filter_predI; congr size.
  by apply eq_filter => C; rewrite !inE andbC.
- rewrite /= big_cons.
  suff /count_memPn -> : 0 \notin (parts_shape (pcycles s))
    by rewrite fact0 mul1n.
  rewrite mem_sort /parts_shape.
  apply/negP => /mapP [C]; rewrite mem_enum => /imsetP [x _ ->{C}] /eqP.
  by apply/negP; rewrite eq_sym; apply card_pcycle_neq0.
Qed.

Lemma conj_pcyclegrp s y z :
  y \in 'C[s] -> z \in 'CC(s) -> z ^ y \in 'CC(s).
Proof using.
move=> Hy; rewrite inE => /andP [zC /astabP zCpcycles].
have /= HyV := groupVr Hy.
rewrite inE; apply/andP; split.
- by apply groupM; last exact: groupM.
- apply/astabP => C /imsetP [x _ ->{C}].
  rewrite !actM /= cent1_act_pcycle // zCpcycles; last exact: mem_imset.
  by rewrite -cent1_act_pcycle // -!actM mulVg act1.
Qed.

Lemma inpcycles1 s t : t \in 'C(pcycles s | ('P)^* ) -> inpcycles s t = 1.
Proof using.
move=> Ht; have tfix := astab_act Ht.
apply/permP => /= X; rewrite /inpcycles perm1.
case: (boolP (X \in pcycles s)) => HX.
- rewrite restr_permE //= ?actpermE ?tfix // {X HX}.
  apply/astabsP => X /=; rewrite actpermK.
  apply astabs_act; move: Ht; apply/subsetP; exact: astab_sub.
- exact: (out_perm (restr_perm_on _ _ ) HX).
Qed.

Lemma cent1_stab_ipcycle_pcyclegrpS s :
  'C[s] \subset permcycles s @* stab_ipcycles s * 'CC(s).
Proof using.
apply/subsetP => t Ht.
pose str := permcycles s (inpcycles s t^-1).
have Hstr : str \in 'C[s] by apply: permcyclesP.
rewrite -(mulKg str t); apply mem_mulg.
- rewrite groupV /= -/(stab_ipcycles s); apply mem_imset.
  by rewrite setIid -inpcycles_im; apply mem_imset; apply groupVr.
- rewrite inE; apply/andP.
  split; first exact: groupM.
  apply/astabP => C /imsetP [x _ ->{C}].
  rewrite !actM /= cent1_act_pcycle //=.
  rewrite pcycle_permcycles; first last.
    by rewrite -inpcycles_im; apply mem_imset; apply groupVr.
  rewrite /inpcycles /= restr_permE; first last.
  + exact: mem_imset.
  + apply/astabsP => X /=; rewrite actpermK.
    apply astabs_act; move: Ht => /groupVr; apply/subsetP => /=.
    exact: cent1_act_on_pcycles.
  by rewrite actpermE /= -actM mulVg act1.
Qed.

Theorem cent1_permE s :
  'CC(s) ><| (permcycles s) @* (stab_ipcycles s) = 'C[s].
Proof using.
apply/sdprod_normal_complP.
- apply/normalP; split; first exact: subsetIl.
  move=> /= y Hy; apply/setP => /= x; have /= HyV := groupVr Hy.
  apply/imsetP/idP => [[/= z Hz] ->{x} | Hx].
  + exact: conj_pcyclegrp.
  + exists (x ^ (y^-1)); last by rewrite conjgKV.
    exact: conj_pcyclegrp.
rewrite /= -/(stab_ipcycles s).
rewrite inE; apply/andP; split.
- apply/eqP/trivgP; apply/subsetP => t.
  rewrite 2!inE => /andP [/imsetP [/= P]].
  rewrite setIid => HP Ht /andP [] tC tCpcycles; rewrite inE.
  suff : P = 1 by rewrite Ht => ->; rewrite morphism.morph1.
  by rewrite -(permcyclesK HP) -Ht; apply: inpcycles1.
- rewrite /=; apply/eqP/setP => /= t.
  apply/idP/idP => [/mulsgP [/= t' u /imsetP [P]] | Ht].
  + rewrite setIid => HP ->{t'} Hu ->{t}.
    apply groupM; first exact: permcyclesP.
    by move: Hu; rewrite inE => /andP [].
  + exact: (subsetP (cent1_stab_ipcycle_pcyclegrpS s)).
Qed.

Local Open Scope nat_scope.

Definition zcard l :=
  \prod_(i <- l) i * \prod_(i <- iota 1 (sumn l)) (count_mem i l)`!.

Corollary card_cent1_perm s : #|'C[s]| = zcard (cycle_type s).
Proof using.
have /sdprod_card <- := cent1_permE s.
rewrite card_pcyclegrpE card_in_imset // ?setIid; first last.
  apply: can_in_inj; exact: permcyclesK.
by rewrite /zcard card_stab_ipcycles // intpartn_sumn.
Qed.

Theorem card_class_perm s :
  #|class s [set: {perm T}]| = #|T|`! %/ zcard (cycle_type s).
Proof using.
rewrite -card_cent1_perm -index_cent1 /= -divgI.
rewrite (eq_card (B := perm_on setT)); first last.
  move=> p; rewrite inE unfold_in /perm_on /=.
  apply/esym/subsetP => i _; by rewrite in_set.
rewrite card_perm cardsE setTI; congr (_ %/ #|_|).
by rewrite /= setTI.
Qed.

End PermCycles.

From Combi Require Import permuted.

Lemma dvdn_zcard_fact n (l : intpartn n) : zcard l %| n`!.
Proof.
pose l' := (partCT_of_partn l).
have -> : zcard l = zcard l' by rewrite intpartn_castE /=.
rewrite -(perm_of_partCTP l') -(card_cent1_perm (perm_of_partCT l')).
rewrite -card_Sn -cardsT; apply cardSg.
exact: subsetT.
Qed.

Theorem card_class_of_part n (l : intpartn n) :
  #|class_of_partCT l| = n`! %/ zcard l.
Proof using.
rewrite /class_of_partCT card_class_perm perm_of_partCTP /=.
by rewrite intpartn_castE /= card_ord.
Qed.


From mathcomp Require Import ssralg ssrnum algC.
Import GRing.Theory Num.Theory.
Require Import cycletype towerSn.

Lemma zcoeffE n (l : intpartn n) : zcoeff l = ((zcard l)%:R)%R.
Proof.
rewrite /zcoeff card_class_of_part card_Sn.
rewrite char0_natf_div; [| exact: Cchar | exact: dvdn_zcard_fact].
rewrite invf_div mulrC mulfVK //.
by rewrite pnatr_eq0 -lt0n; apply: fact_gt0.
Qed.
