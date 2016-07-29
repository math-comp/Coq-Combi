Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial.
From mathcomp Require Import fingroup perm automorphism action ssralg.
From mathcomp Require finmodule.

From Combi Require Import symgroup partition Greene tools sorted.

Require Import ssrcomp slicedbij cycles.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

Import LeqGeqOrder.

Reserved Notation "''1_[' G ]"
         (at level 8, G at level 2, format "''1_[' G ]").




(* TODO: Move elsewhere *)
Lemma disjoint_imset (T : finType) (f : T -> T) (A B : {set T}) :
  injective f ->
  [disjoint A & B] -> [disjoint [set f x | x in A] & [set f x | x in B]].
Proof using.
  rewrite -!setI_eq0 => Hinj /eqP Hdisj.
  rewrite -imsetI; last by move=> x y _ _; exact: Hinj.
  by rewrite imset_eq0 Hdisj.
Qed.


Section CanPCycle.

Variable T : finType.
Variable s : {perm T}.

Definition canpcycle x := odflt x [pick y in pcycle s x].

Lemma canpcycleP x : x \in pcycle s (canpcycle x).
Proof using.
  rewrite /canpcycle /= pcycle_sym.
  case: pickP => [x0 //|].
  by move => /(_ x) /=; rewrite pcycle_id.
Qed.

Lemma canpcycleE x y :
  (pcycle s x == pcycle s y) = (canpcycle x == canpcycle y).
Proof using.
  apply/eqP/eqP => [| H].
  - rewrite /canpcycle => ->; case: pickP => [x0 //|].
    by move => /(_ y) /=; rewrite pcycle_id.
  - have:= canpcycleP x; rewrite H.
    rewrite -eq_pcycle_mem => /eqP ->.
    apply esym; apply/eqP; rewrite eq_pcycle_mem.
    exact: canpcycleP.
Qed.

Lemma pcyclePb x y :
  y \in pcycle s x -> exists i, y == (s ^+ i)%g x.
Proof using.
  move=> /pcycleP H.
  move: H => [i Hi]; exists i; by rewrite Hi.
Qed.

Definition indpcycle (x : T) : nat := ex_minn (pcyclePb (canpcycleP x)).

Lemma indpcycleP x : ((s ^+ (indpcycle x)) (canpcycle x))%g = x.
Proof using. rewrite /indpcycle; by case: ex_minnP => i /eqP. Qed.

From mathcomp Require Import div.

Lemma pcycle_mod x i :
  (s ^+ i)%g x = (s ^+ (i %% #|pcycle s x|))%g x.
Proof using.
  rewrite {1}(divn_eq i #|pcycle s x|) expgD permM; congr aperm.
  elim: (i %/ #|pcycle s x|) => [| {i} i IHi].
  - by rewrite mul0n expg0 perm1.
  - by rewrite mulSnr expgD permM IHi permX; exact: iter_pcycle.
Qed.

Lemma eq_in_pcycle x i j :
  ((s ^+ i)%g x == (s ^+ j)%g x) = (i == j %[mod #|pcycle s x|]).
Proof using.
  apply/idP/idP.
  - rewrite [X in X == _]pcycle_mod [X in _ == X]pcycle_mod !permX.
    have HC : 0 < #|pcycle s x|.
      rewrite card_gt0; apply/set0Pn; exists x; exact: pcycle_id.
    rewrite -!(nth_traject _ (ltn_pmod _ HC)).
    rewrite nth_uniq // ?size_traject ?ltn_pmod //.
    exact: uniq_traject_pcycle.
  - by move=> /eqP H; apply/eqP; rewrite [LHS]pcycle_mod [RHS]pcycle_mod H.
Qed.

End CanPCycle.

Section PCycleBijection.

Variables (U V : finType).
Variables (s : {perm U}) (t : {perm V}).

Record pcycles_map := PCycleMap {
                          fs :> {set U} -> {set V};
                          fs_stab : fs @: pcycles s \subset pcycles t;
                          fs_homog : {in pcycles s, forall C, #|fs C| = #|C| }
                        }.

Variable CM : pcycles_map.

Lemma aux (x : U) : V.
Proof using CM.
have : fs CM (pcycle s x) != set0.
  rewrite -card_gt0 fs_homog ?mem_imset // card_gt0.
  by apply/set0Pn; exists x; exact: pcycle_id.
by move/set0Pn/sigW => H; apply H.
Qed.

Definition cymapcan x := odflt (aux x) [pick y in CM (pcycle s x)].
Definition cymap x := ((t ^+ (indpcycle s x)) (cymapcan x))%g.

Lemma fs_pcycleP x : CM (pcycle s x) \in pcycles t.
Proof using.
    by apply (subsetP (fs_stab CM)); apply mem_imset; apply mem_imset.
Qed.

Lemma pcycle_cymapcan x : pcycle t (cymapcan x) = CM (pcycle s x).
Proof using.
  rewrite /cymapcan /=.
  have:= fs_pcycleP x => /imsetP [y0 _ ->].
  case: pickP => [/= y|].
  - by rewrite -eq_pcycle_mem => /eqP ->.
  - by move=> /(_ y0); rewrite pcycle_id.
Qed.

Lemma cymapcan_perm i x : cymapcan ((s ^+ i)%g x) = cymapcan x.
Proof using CM.
  rewrite /cymapcan pcycle_perm.
  have:= fs_pcycleP x => /imsetP [y0 _ ->].
  by case: pickP => // /(_ y0); rewrite pcycle_id.
Qed.

Lemma cymapP x : cymap (s x) = t (cymap x).
Proof using CM.
  rewrite /cymap -{3}(expg1 s) cymapcan_perm.
  have:= fs_homog CM (mem_imset (x := x) _ isT); rewrite -pcycle_cymapcan.
  move: (cymapcan x) => y H.
  apply/eqP; rewrite -permM -expgSr eq_in_pcycle {}H.
  have:= canpcycleP s x; rewrite -eq_pcycle_mem => /eqP ->.
  rewrite -eq_in_pcycle.
  rewrite expgSr permM indpcycleP.
  have:= mem_pcycle s 1 x; rewrite expg1 -eq_pcycle_mem canpcycleE => /eqP <-.
  by rewrite indpcycleP.
Qed.

Lemma canpcycle_cymap x : canpcycle t (cymap x) = cymapcan x.
Proof using CM.
  rewrite /cymap /cymapcan /canpcycle pcycle_perm.
  have := erefl (cymapcan x).
  rewrite {1}/cymapcan.
  case: pickP => [im Him /= Hdefim | Habs] /=.
  - rewrite /canpcycle (_ : [pick y in  _] = some im) //.
    rewrite [LHS](_ : _ = [pick y in CM (pcycle s x)]); first last.
      apply eq_pick => y /=; congr (y \in _).
      have:= fs_pcycleP x => /imsetP [y0 _ Hy0].
      by move: Him; rewrite Hy0 /= -eq_pcycle_mem => /eqP ->.
    rewrite Hdefim /cymapcan.
    by case: pickP => // /(_ im); rewrite Him.
  - exfalso; move: Habs.
    have:= fs_pcycleP x => /imsetP [y _ ->] /(_ y).
    by rewrite pcycle_id.
Qed.

Lemma indpcycle_cymap x : indpcycle t (cymap x) = indpcycle s x.
Proof using CM.
  apply eq_ex_minn => i.
  rewrite {1}/cymap canpcycle_cymap eq_in_pcycle pcycle_cymapcan.
  rewrite (fs_homog CM (mem_imset _ isT)) -{4}(indpcycleP s x) eq_in_pcycle.
  suff -> : pcycle s x = pcycle s (canpcycle s x) by [].
  apply/eqP; rewrite eq_pcycle_mem; exact: canpcycleP.
Qed.

End PCycleBijection.

Fact pcycles_stab_id (U : finType) (s : {perm U}) :
  id @: pcycles s \subset pcycles s.
Proof. by rewrite imset_id. Qed.
Definition CMid (U : finType) (s : {perm U}) :=
  @PCycleMap U U s s id (pcycles_stab_id s) (fun x _ => erefl #|x|).

Lemma cymapE (U V : finType) (s : {perm U}) (t : {perm V})
      (CM1 CM2 : pcycles_map s t) :
   {in pcycles s, CM1 =1 CM2} -> cymap CM1 =1 cymap CM2.
Proof.
move=> Heq x; rewrite /cymap /cymapcan /=.
rewrite -Heq; last exact: mem_imset.
case: pickP => // Habs.
exfalso; move: Habs.
have:= fs_pcycleP CM1 x => /imsetP [y _ ->] /(_ y).
by rewrite pcycle_id.
Qed.

Lemma cymap_id (U : finType) (s : {perm U}) (CM : pcycles_map s s) :
  {in pcycles s, CM =1 id} -> cymap CM =1 id.
Proof.
move=> H x; rewrite /cymap /=.
rewrite -[RHS](indpcycleP s).
rewrite /cymapcan /canpcycle H ?mem_imset //.
by case: pickP => // /(_ x); rewrite pcycle_id.
Qed.

Lemma cymap_comp (U V W: finType)
      (u : {perm U}) (v : {perm V}) (w : {perm W})
      (CMuv : pcycles_map u v) (CMvw : pcycles_map v w) (CMuw : pcycles_map u w) :
  {in pcycles u, CMvw \o CMuv =1 CMuw} ->
  (cymap CMvw) \o (cymap CMuv) =1 (cymap CMuw).
Proof.
move=> Hcomp x; rewrite /cymap /=.
rewrite /cymapcan /= pcycle_perm pcycle_cymapcan indpcycle_cymap; congr (_ _).
have /= -> := (Hcomp (pcycle u x)); last exact: mem_imset.
case: (pickP (mem (CMuw _))) => // Habs; exfalso.
have:= fs_pcycleP CMuw x => /imsetP [z _ Hz].
by have:= Habs z; rewrite Hz /= pcycle_id.
Qed.

Section CycleTypeConj.

Variable T : finType.
Implicit Types (s t : {perm T}) (n : nat).

Fact cycle_type_partCT (s : {perm T}) :
  is_part_of_n #|T| (parts_shape (pcycles s)).
Proof using.
  rewrite -cardsT; apply parts_shapeP.
  exact: partition_pcycles.
Qed.
Definition cycle_type (s : {perm T}) := IntPartN (cycle_type_partCT s).

Lemma conjg_cycle s a : (<[s]> :^ a = <[s ^ a]>)%g.
Proof using.
  apply /setP => x.
  apply /imsetP/cycleP => [[x0 /cycleP [i] ->] ->|[i] ->].
  - by exists i; exact: conjXg.
  - by exists (s ^+i)%g; [apply /cycleP; exists i|rewrite conjXg].
Qed.

Lemma pcycle_conjg s a x :
  pcycle ((s ^ a)%g) (a x) = [set a y | y in pcycle s x].
Proof using.
  rewrite !pcycleE; apply /setP => y.
  apply /idP/imsetP => [|[x0] Hx0 ->].
  - rewrite -conjg_cycle => Hy.
    exists ((a ^-1)%g y); last by rewrite permKV.
    move: Hy; rewrite {1}(_: y = a ((a ^-1)%g (y))); last by rewrite permKV.
    by rewrite -{1}apermE orbit_conjsg.
  - by rewrite -conjg_cycle -apermE orbit_conjsg.
Qed.


Lemma pcycles_conjg s a :
  pcycles (s ^ a)%g = [set [set a y | y in (X : {set T})] | X in pcycles s].
Proof using.
  apply /setP => X0.
  apply /imsetP/imsetP => [[x _]|[x /imsetP [x0 _] ->] ->].
  - rewrite (_: x = a ((a ^-1)%g (x))); last by rewrite permKV.
    rewrite pcycle_conjg => ->.
    exists (pcycle s ((a^-1)%g x)) => //.
    by apply /imsetP; exists ((a^-1)%g x).
  - exists (a x0) => //.
    by rewrite pcycle_conjg.
Qed.

Require Import ordcast. (* for imset_inj TODO : move in tools *)

Lemma cycle_type_of_conjg s a : cycle_type (s ^ a)%g = cycle_type s.
Proof using.
  apply esym; apply val_inj => /=.
  rewrite pcycles_conjg; apply/perm_sortP => //.
  have -> : [seq #|(x : {set T})| | x <- enum (pcycles s)] =
            [seq #|[set a y | y in (x : {set T})]| | x <- enum (pcycles s)].
    by apply eq_map => x;  apply esym; apply card_imset; exact: perm_inj.
  rewrite (map_comp (fun x : {set T} => #|x|)); apply perm_map.
  apply uniq_perm_eq.
  - rewrite map_inj_uniq; first exact: enum_uniq.
    apply imset_inj; exact: perm_inj.
  - exact: enum_uniq.
  - move=> x; rewrite mem_enum.
    apply/mapP/imsetP => [] [x0].
    + by rewrite mem_enum => Hx0 -> {x}; exists x0.
    + by move=> Hx0 -> {x}; exists x0; rewrite ?mem_enum.
Qed.

Lemma conjg_of_cycle s a : cyclic s -> cyclic (s ^ a)%g.
Proof using.
  move => /cards1P [X] HX.
  apply /cards1P; exists [set a x | x in X].
  apply /setP => y.
  rewrite !inE.
  apply /andP/eqP => [| -> ]; rewrite pcycles_conjg.
  - move => [/imsetP [Y HY ->]].
    rewrite card_imset => Hcard; last by exact: perm_inj.
    have: Y \in psupport s by  rewrite inE; apply /andP.
    by rewrite HX inE => /eqP ->.
  - have: X \in [set X] by rewrite inE.
    rewrite -{}HX inE => /andP [HX1 HX2].
    split; first by apply /imsetP; exists X.
    by rewrite card_imset //; exact: perm_inj.
Qed.

Lemma support_conjg s a : support (s ^ a) = [set a x | x in support s].
Proof using.
  apply /setP => x.
  rewrite in_support; apply /idP/imsetP => [|[x0]].
  - rewrite conjgE !permM => /eqP Hx.
    exists (a^-1 x)%g; last by rewrite -permM mulVg perm1.
    rewrite in_support; apply /eqP => Hx'.
    by move : Hx; rewrite Hx'; rewrite -permM mulVg perm1.
  - rewrite in_support => Hx0 ->.
    rewrite conjgE -!permM mulKVg permM.
    move: Hx0; apply contra => /eqP Hx0.
    by apply /eqP; apply (perm_inj Hx0).
Qed.

Lemma card_support_conjg s a : #|support s| = #|support (s ^ a)%g|.
Proof using.
  rewrite support_conjg.
  apply esym; apply card_imset.
  by exact: perm_inj.
Qed.

Lemma conjg_of_disjoint_supports (A : {set {perm T}}) a :
  disjoint_supports A -> disjoint_supports [set (s ^ a)%g | s in A].
Proof using.
  move => [/trivIsetP Hdisj Hinj].
  split => [|x1 x2 /imsetP [s1 Hs1 ->] /imsetP [s2 Hs2 ->]].
  - apply /trivIsetP => B1 B2.
    move => /imsetP [x1 /imsetP [s1 Hs1 ->] -> {x1}].
    move => /imsetP [x2 /imsetP [s2 Hs2 ->] -> {x2}].
    rewrite !support_conjg => Hdiff.
    apply disjoint_imset; first exact: perm_inj.
    apply: Hdisj; try exact: mem_imset.
    by move: Hdiff; apply contra => /eqP ->.
  - rewrite !support_conjg => Hsupp.
    rewrite (_ : s1 = s2) //; apply Hinj => //.
    apply /setP => x; apply /idP/idP => Hx.
    + have:= mem_imset a Hx.
      by rewrite Hsupp => /imsetP [y] Hy /perm_inj ->.
    + have:= mem_imset a Hx.
      by rewrite -Hsupp => /imsetP [y] Hy /perm_inj ->.
Qed.

Import finmodule.FiniteModule morphism.

Lemma cycle_dec_of_conjg s a:
  [set (c ^ a)%g | c in cycle_dec s] = cycle_dec (s ^ a)%g.
Proof using.
  have abel : abelian <<[set (c ^ a)%g | c in cycle_dec s]>>.
    apply abelian_disjoint_supports.
    apply: conjg_of_disjoint_supports.
    exact: disjoint_cycle_dec.
  apply: uniqueness_cycle_dec; constructor => [x /imsetP [x0 Hx0 ->]||].
  - apply: conjg_of_cycle; apply: cyclic_dec.
    exact: Hx0.
  - apply: conjg_of_disjoint_supports.
    exact: disjoint_cycle_dec.
  - rewrite [LHS](_ : _ =
      val (\sum_(i in [set (c ^ a)%g | c in cycle_dec s]) fmod abel i)%R);
      first last.
      rewrite -(morph_prod [morphism of fmod abel]);
        last by move=> i; exact: mem_gen.
      rewrite -[LHS](fmodK abel) //.
      by apply group_prod => i; exact: mem_gen.
    rewrite big_imset /=; last by move=> x y _ _; exact: conjg_inj.
    rewrite -(morph_prod [morphism of fmod abel]); first last.
      move=> i Hi; apply mem_gen; exact: mem_imset.
    rewrite fmodK; first last.
      apply group_prod => i Hi; apply mem_gen; exact: mem_imset.
    by rewrite -conjg_prod cycle_decE.
Qed.

(* Ici il faut ayant supposé cycle_type s = cycle_type t, construire un
bijection entre pcycles s et pcycles t *)

Definition slice_part (P : {set {set T}}) :=
 SlicedSet set0 P (fun x : {set T} => #|x|).

Definition slpcycles s := slice_part (pcycles s).

Lemma slice_slpcycleE s i :
  #|slice (slpcycles s) i| = count_mem i (cycle_type s).
Proof using.
  rewrite /cycle_type /slice /parts_shape /=.
  rewrite [RHS](_ : _ =
      (count_mem i) [seq #|(x : {set _})| | x <- enum (pcycles s)]);
      last by apply/perm_eqP/perm_eqlP; exact: perm_sort.
  rewrite cardE /enum_mem -enumT /=.
  rewrite size_filter count_map count_filter.
  apply eq_count => C /=; apply/imsetP/idP => [[X] | HC].
  - by rewrite inE andbC => H ->.
  - by exists C => //; rewrite inE andbC.
Qed.

End CycleTypeConj.

Section Defs.

Variables (U V : finType).
Variables (s : {perm U}) (t : {perm V}).
Hypothesis eqct : cycle_type s = cycle_type t :> seq nat.

Lemma cycle_type_eq :
  forall i, #|slice (slpcycles s) i| = #|slice (slpcycles t) i|.
Proof using eqct. by move=> i; rewrite !slice_slpcycleE eqct. Qed.

Fact conjg_pcycles_stab :
  [set bij (slpcycles t) x | x in (slpcycles s)] \subset slpcycles t.
Proof using eqct. by have := bijP cycle_type_eq => [] [] _ ->. Qed.
Fact conjg_pcycles_homog :
  {in pcycles s, forall C, #|bij (U := slpcycles s) (slpcycles t) C| = #|C| }.
Proof using eqct. by have := bijP cycle_type_eq => [] []. Qed.
Definition CMbij := PCycleMap conjg_pcycles_stab conjg_pcycles_homog.
Definition conjbij := cymap CMbij.

End Defs.

Lemma conjbijK
      (U V : finType) (s : {perm U}) (t : {perm V})
      (eqct : cycle_type s = cycle_type t :> seq nat) :
  cancel (conjbij eqct) (conjbij (esym eqct)).
Proof using.
  rewrite /conjbij => x /=.
  rewrite [LHS](cymap_comp (CMuw := (CMid s))); first exact: cymap_id.
  move=> y Hy /=; rewrite bijK //.
  exact: cycle_type_eq.
Qed.


Section CycleType.

Variable T : finType.
Implicit Types (s t : {perm T}).

Theorem conj_permP s t :
  reflect (exists c, t = (s ^ c)%g) (cycle_type s == cycle_type t).
Proof using.
  apply (iffP eqP) => [/(congr1 val)/= eqct | [x ->]].
  - have conjbij_inj := can_inj (conjbijK eqct).
    exists (perm conjbij_inj); rewrite -permP => x.
    rewrite !permM permE /= /conjbij cymapP.
    by rewrite -/(conjbij eqct) -(permE conjbij_inj) permKV.
  - by rewrite cycle_type_of_conjg.
Qed.

Lemma classes_of_permP s t:
  reflect (t \in (s ^: [set: {perm T}])%g) (cycle_type s == cycle_type t).
Proof using.
  apply (iffP (conj_permP s t)) => [[c ->] |].
  - by apply: mem_imset; rewrite inE.
  - by move=> /imsetP [c Hc ->]; exists c.
Qed.

Section Permofcycletype.

Implicit Types (l : nat) (ct : intpartn #|T|).


Lemma uniq_next (p : seq T) : uniq p -> injective (next p).
Proof using.
  move=> Huniq x y Heq.
  by rewrite -(prev_next Huniq x) Heq prev_next.
Qed.

Fact cycle_of_set_subproof (s : {set T}) : injective (next (enum s)).
Proof using. by apply uniq_next; exact: enum_uniq. Qed.
Definition cycle_of_set (s : {set T}) := perm (@cycle_of_set_subproof s).

Lemma support_cycle_of_set (s : {set T}) :
  #|s| > 1 -> support (cycle_of_set s) = s.
Proof using.
  move => Hsize; apply /setP => x.
  rewrite in_support permE.
  apply /idP/idP => [|Hx]; rewrite next_nth.
  - by apply contraR; rewrite -mem_enum => /negbTE ->.
  - rewrite mem_enum Hx.
    move: Hsize Hx; rewrite -mem_enum cardE.
    case: (enum s) (enum_uniq (pred_of_set s)) => // a [// | b l] /=.
    move=> /and3P []; rewrite inE => /norP [/negbTE Hab Ha] Hb Huniq _.
    rewrite !inE => /orP [/eqP -> |/orP [/eqP -> |Hx]].
    + by rewrite eq_refl /= eq_sym Hab.
    + rewrite Hab eq_refl /=.
      case: {2 3}l (erefl l) => [|c l0 Hl]; first by rewrite Hab.
      by apply /eqP => Heq; move: Hb; rewrite -Heq Hl mem_head.
    + have /negbTE Hbx: (b != x).
        by apply /eqP => Heq; move: Hb; rewrite Heq Hx.
      have /negbTE Hax: (a != x).
        by apply /eqP => Heq; move: Ha; rewrite Heq Hx.
      have Hxb: x \in (b :: l) by rewrite inE Hx orbT.
      rewrite Hax Hbx.
      case (ltnP (index x l).+2 (size (b :: l))) => Hindex.
      * have:= Hxb; rewrite -index_mem => Hindex1.
        rewrite -{2}(nth_index a Hxb) nth_uniq //=; last by apply /andP.
        by rewrite Hbx gtn_eqF.
      * by rewrite nth_default ?Hax.
Qed.


Lemma cycle_of_setE (s : {set T}) (x : T):
  x \in s -> s = pcycle (cycle_of_set s) (head x (enum s)).
Proof using.
  rewrite -mem_enum; have:= erefl (enum s).
  case: {2 3 4}(enum s) => [|a l Hs _ /=]; first by rewrite in_nil.
  apply /setP => y; apply /idP/pcycleP => [| [n ->]].
  - rewrite -mem_enum => Hy; exists (index y (enum s)).
    elim: (index y _) {1 2 4}y Hy (erefl (index y (enum s))) =>
                                        [| m IHm] {y} y Hy Hind.
      have:= nth_index y Hy; rewrite Hind Hs /= => <-.
      by rewrite expg0 perm1.
    have Hm : m < size (enum s).
      by move: Hy; rewrite -index_mem Hind; apply leq_trans.
    have Hnth : index (nth y (enum s) m) (enum s) = m.
      by rewrite index_uniq // enum_uniq.
    have Hnthin : (nth y (enum s) m) \in enum s.
      by rewrite -index_mem Hnth.
    rewrite expgSr permM -(IHm (nth y (enum s) m)) //.
    rewrite permE next_nth Hnthin {1}Hs Hnth.
    have /negbTE Hya : y != a.
      by apply /eqP => Heq; move: Hind; rewrite Heq Hs index_head.
    move: Hind; rewrite Hs -cat1s index_cat.
    rewrite inE Hya /= add1n => [[]] <-.
    rewrite nth_index //.
    by move: Hy; rewrite Hs inE Hya.
  - elim: n => [|m IHm].
    + by rewrite expg0 perm1 -mem_enum Hs mem_head.
    + by rewrite expgSr permM permE -mem_enum mem_next mem_enum.
Qed.

Lemma pcycles_of_set (s : {set T}):
  #|s| > 1 -> s \in pcycles (cycle_of_set s).
Proof using.
  case: (set_0Vmem s) => [->|]; first by rewrite cards0.
  move=> [x Hx] Hsize.
  apply /imsetP; exists (head x (enum s)) => //.
  exact: cycle_of_setE.
Qed.

Lemma psupport_of_set (s : {set T}):
  #|s| > 1 -> psupport (cycle_of_set s) = [set s].
Proof using.
  move=> Hsize; apply /setP => X.
  rewrite !inE.
  apply/andP/eqP => [[/imsetP [x _ ->]]|->].
  - rewrite support_card_pcycle support_cycle_of_set // => Hx.
    rewrite [RHS](cycle_of_setE Hx).
    by apply/eqP; rewrite eq_pcycle_mem -cycle_of_setE.
  - split; first exact: pcycles_of_set.
    by rewrite -(support_cycle_of_set Hsize) card_support_noteq1.
Qed.


Lemma iscycle_of_set (s : {set T}): #|s| > 1 -> cyclic (cycle_of_set s).
Proof using.
  move => Hsize.
  apply /cards1P; exists s.
  exact: psupport_of_set.
Qed.


Definition perm_of_parts (P : {set {set T}}) :=
  (\prod_(C in [set cycle_of_set s | s in [set X in P |#|X|>1]]) C)%g.

Lemma supports_cycle_of_set (P : {set {set T}}) :
  [set support (cycle_of_set s) | s in [set X in P | 1 < #|X| ]] =
  [set X in P | 1 < #|X|].
Proof using.
  rewrite -[RHS]imset_id.
  apply eq_in_imset => i; rewrite inE => /andP [_ Hi].
  by rewrite support_cycle_of_set.
Qed.

Lemma disj_perm_of_parts (P : {set {set T}}):
  partition P [set: T] ->
  disjoint_supports (T:=T) [set cycle_of_set s| s in [set X0 in P | 1 < #|X0|]].
Proof using.
  move => Hpart; split => [|C D].
  - rewrite -imset_comp supports_cycle_of_set.
    apply /trivIsetP => A B; rewrite !inE.
    move => /andP [AinP _] /andP [BinP _].
    by move: Hpart => /and3P [_ /trivIsetP /(_ A B AinP BinP) ].
  - move => /imsetP [A]; rewrite inE => /andP [_ cardA] ->.
    move => /imsetP [B]; rewrite inE => /andP [_ cardB] ->.
    by rewrite !support_cycle_of_set // => ->.
Qed.

Lemma pcycles_perm_of_parts P :
  partition P [set: T] -> pcycles (perm_of_parts P) = P.
Proof using.
  move=> Hpart; apply /setP => X.
  apply /idP/idP => HX.
  - case: (boolP (X \in psupport (perm_of_parts P))).
    + rewrite psupport_of_disjoint; last exact: disj_perm_of_parts.
      move => /bigcupP [C] /imsetP [X0].
      rewrite inE => /andP [H HX0] ->.
      by rewrite psupport_of_set // inE => /eqP ->.
    + rewrite inE => /nandP []; first by rewrite HX.
      move: HX => /imsetP [x _ ->].
      rewrite support_card_pcycle => Hsupp.
      have:= Hsupp; rewrite in_support negbK pcycle_fix => /eqP ->.
      move: Hsupp; rewrite support_of_disjoint; last exact: disj_perm_of_parts.
      rewrite -(big_imset id) /=; first last.
        move=> C D /imsetP [c]; rewrite inE => /andP [_ cardc ->{C}].
        move=>     /imsetP [d]; rewrite inE => /andP [_ cardd ->{D}].
        by rewrite !support_cycle_of_set // => ->.
      rewrite -imset_comp supports_cycle_of_set => /bigcupP.
      move=> /exists_inP; rewrite -[X in (is_true X) -> _]negbK.
      have xinP : x \in cover P by rewrite (cover_partition Hpart).
      have:= xinP; rewrite -mem_pblock => xPblock.
      rewrite negb_exists_in => /forall_inP/(_ (pblock P x))/contraL/(_ xPblock).
      rewrite inE => /nandP []; first by rewrite pblock_mem.
      rewrite -leqNgt leq_eqVlt => /orP [/cards1P [y Hy]|].
      * move: xPblock; rewrite Hy inE => /eqP ->.
        by rewrite -Hy; apply pblock_mem.
      * rewrite ltnS leqn0 cards_eq0 => /eqP H.
        by move: xPblock; rewrite H inE.
  - case: (boolP (#|X| == 1)).
    + move => /cards1P [x Hx]; subst X.
      apply /imsetP; exists x => //.
      apply esym; apply/eqP; rewrite -pcycle_fix.
      rewrite -[_ == x]negbK -in_support support_of_disjoint; last exact: disj_perm_of_parts.
      apply /bigcupP => /exists_inP; apply /negP; rewrite negb_exists_in.
      apply /forall_inP => C /imsetP [x0]; rewrite inE => /andP [Hx0 Hcard] ->.
      rewrite support_cycle_of_set //.
      move: Hpart => /and3P [_ /trivIsetP /(_ [set x] x0) Hxx0 _].
      move: Hxx0 => /(_ HX Hx0) Htmp.
      have {Htmp} /eqP/Htmp : [set x] <> x0
        by move => Heq; move: Hcard; rewrite -Heq cards1.
      rewrite -setI_eq0 => /eqP Hxx0.
      apply /negP => Hx.
      suff: x \in set0 by rewrite inE.
      by rewrite -Hxx0 inE Hx andbT inE.
    + have:= Hpart => /and3P [_ _ Hset0].
      move=> H; move: H HX Hset0.
      rewrite neq_ltn => /orP [|Hcard HX Hset0].
        by rewrite ltnS leqn0 cards_eq0 => /eqP -> ->.
      suff: X \in psupport (perm_of_parts P) by rewrite inE => /andP [].
      rewrite psupport_of_disjoint; last exact: disj_perm_of_parts.
      apply /bigcupP; exists (cycle_of_set X); last by rewrite psupport_of_set ?inE.
      apply /imsetP; exists X => //.
      by rewrite inE; apply /andP; split.
Qed.

Lemma perm_of_partsE P :
  partition P [set: T] -> (cycle_type (perm_of_parts P): seq nat) = parts_shape P.
Proof using. by move=> /pcycles_perm_of_parts pcy; rewrite /= pcy. Qed.

End Permofcycletype.


Section Classes.

Variable tc : intpartn #|T|.

Lemma perm_of_partCT_exists : exists s, cycle_type s = tc.
Proof using.
  move: (valP (intpartn_cast (esym (cardsT T)) tc)).
  rewrite intpartn_castE => /ex_set_parts_shape [P /perm_of_partsE /= ct shape].
  exists (perm_of_parts P); apply val_inj => /=; rewrite ct.
  by exact: shape.
Qed.

Lemma perm_of_partCT_set : {s | cycle_type s == tc}.
Proof using. by apply sigW; have:= perm_of_partCT_exists => [[p <-]]; exists p. Qed.

Definition perm_of_partCT := val perm_of_partCT_set.
Lemma perm_of_partCTP : cycle_type perm_of_partCT = tc.
Proof using.
  rewrite /perm_of_partCT.
  by case: perm_of_partCT_set => s /= /eqP ->.
Qed.

Definition class_of_partCT := class (perm_of_partCT) [set: {perm T}].

Lemma class_of_partCTP s :
  (cycle_type s == tc) = (s \in class_of_partCT).
Proof using.
  rewrite /class_of_partCT -perm_of_partCTP /class eq_sym.
  by apply/classes_of_permP/idP.
Qed.

End Classes.

Lemma class_of_partCT_inj : injective class_of_partCT.
Proof using.
  rewrite /class_of_partCT => t1 t2 /class_eqP.
  rewrite -class_of_partCTP => /eqP <-.
  by rewrite perm_of_partCTP.
Qed.

Lemma imset_class_of_partCT :
  [set class_of_partCT p | p in setT] = classes [set: {perm T}].
Proof using.
  rewrite -setP => C.
  apply/imsetP/imsetP => [] [s _ Hs].
  - by exists (perm_of_partCT s); rewrite // inE.
  - exists (cycle_type s) => //.
    by rewrite Hs; apply /class_eqP; rewrite -class_of_partCTP.
Qed.

Lemma card_class_perm :
  #|classes [set: {perm T}]| = #|{: intpartn #|T| }|.
Proof using.
  rewrite -imset_class_of_partCT card_imset; last exact: class_of_partCT_inj.
  by apply eq_card => s; rewrite !inE.
Qed.

From mathcomp Require Import matrix vector mxalgebra falgebra ssrnum algC algnum.
From mathcomp Require Import presentation all_character.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CFunIndicator.

Variable tc : intpartn #|T|.

Definition cfuni_part :=
  cfun_indicator [set: {perm T}] (class_of_partCT tc).

Local Notation "''1_[' p ]" := (cfuni_part p) : ring_scope.

Lemma cfuni_partE s :
  ('1_[s]) = (cycle_type s == tc)%:R.
Proof using.
  rewrite /cfuni_part cfunElock genGid inE /=.
  congr ((nat_of_bool _) %:R).  
  apply/idP/idP.
  - rewrite class_of_partCTP => /subsetP; apply.
    apply /imsetP; exists 1%g; first by rewrite inE.
    by rewrite conjg1.
  - move=> /eqP <-; apply/subsetP => t /imsetP [c] _ -> {t}.
    by rewrite -class_of_partCTP cycle_type_of_conjg.
Qed.


End CFunIndicator.
End CycleType.
Notation "''1_[' p ]" := (cfuni_part p) : ring_scope.


Coercion partCT_of_partn n := intpartn_cast (esym (card_ord n)).

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.


Section Sn.

Variable n : nat.
Definition partn_of_partCT :=
  intpartn_cast (card_ord n) : intpartn #|'I_n| -> intpartn n .
Definition cycle_typeSN (s : 'S_n) : intpartn n :=
  partn_of_partCT (cycle_type s).

Lemma partCT_of_partnK (p : intpartn n) :
  partn_of_partCT p = p.
Proof using.
  rewrite /partn_of_partCT; apply val_inj => /=.
  by rewrite !intpartn_castE.
Qed.

Lemma partn_of_partCTE p1 p2 :
  (p1 == p2) = (partn_of_partCT p1 == partn_of_partCT p2).
Proof using.
  rewrite /partn_of_partCT.
  apply/eqP/eqP => [-> //|].
  case: p1 p2 => [p1 Hp1] [p2 Hp2].
  move/(congr1 val); rewrite !intpartn_castE /= => Hp.
  exact: val_inj.
Qed.

Lemma partn_of_partCTK (p : intpartn #|'I_n|) :
  p = partn_of_partCT p.
Proof using.
  rewrite /partCT_of_partn; apply val_inj => /=.
  by rewrite !intpartn_castE.
Qed.

Lemma partn_of_partCT_congr p1 (p2 : intpartn n) :
  (partn_of_partCT p1 == p2) = (p1 == p2).
Proof using.
  apply/eqP/eqP => [<-|->].
  - by rewrite -partn_of_partCTK.
  - by rewrite partCT_of_partnK.
Qed.

Lemma cfuni_partnE (tc : intpartn n) (s : 'S_n) :
  '1_[tc] s = (cycle_typeSN s == tc)%:R.
Proof using.
  rewrite cfuni_partE /cycle_typeSN /=.
  by rewrite partn_of_partCTE partCT_of_partnK.
Qed.

End Sn.

