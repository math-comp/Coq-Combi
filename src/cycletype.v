Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial.
From mathcomp Require Import fingroup perm automorphism action ssralg.
From mathcomp Require finmodule.

From Combi Require Import symgroup partition Greene tools sorted.

Require Import ssrcomp bij cycles.

Set Implicit Arguments.
Unset Strict Implicit.



Section cycle_type.

Local Definition geq_total : total geq :=
  fun x y => leq_total y x.
Local Definition geq_trans : transitive geq :=
  fun x y z H1 H2 => leq_trans H2 H1.
Local Definition anti_geq : antisymmetric geq :=
  fun x y H => esym (anti_leq H).
Local Definition perm_sort_geq :=
  perm_sortP geq_total geq_trans anti_geq.

Variable T : finType.
Implicit Types (s t : {perm T}) (n : nat).

Definition set_partition_shape (s : {set {set T}}) :=
  sort geq [seq #|(x: {set T})| | x <- enum s].

Lemma is_part_sortedE sh :
  (is_part sh) = (sorted geq sh) && (0 \notin sh).
Proof.
  apply/idP/andP => [Hpart|].
  - split.
    + apply/sorted1P => i _.
      by move: Hpart=> /is_partP [_]; apply.
    + move: Hpart; elim: sh => [// | s0 sh IHsh] Hpart.
      rewrite inE negb_or eq_sym.
      have /= -> /= := (part_head_non0 Hpart).
      by apply IHsh; move: Hpart => /andP [].
  - move=> [/sorted1P Hsort Hnotin].
    apply/is_partP; split => [| i].
    + case: sh Hnotin {Hsort} => [// | s0 sh].
      rewrite inE negb_or eq_sym => /andP [Hs0 Hnot] /=.
      elim: sh s0 Hs0 Hnot => [// | s1 sh IHsh] s0 _.
      rewrite inE negb_or eq_sym /= => /andP [].
      exact: IHsh.
    + case: (ltnP i.+1 (size sh)) => Hsz; first exact: Hsort.
      by rewrite (nth_default _ Hsz).
Qed.

Lemma set_partition_shapeP (s : {set {set T}}) D :
  partition s D -> is_part_of_n #|D| (set_partition_shape s).
Proof.
  rewrite /set_partition_shape => /and3P [/eqP Hcov Htriv Hnon0].
  rewrite /is_part_of_n /= is_part_sortedE.
  apply/and3P; split.
  - have:= perm_sort geq  [seq #|(x: {set T})| | x <- enum s].
    move=> /perm_eqlP/perm_sumn ->.
    rewrite -sumnE big_map -big_enum.
    move: Htriv; rewrite /trivIset => /eqP ->.
    by rewrite Hcov.
  - apply sort_sorted => m n /=; exact: leq_total.
  - move: Hnon0; apply contra.
    rewrite mem_sort => /mapP [] x.
    by rewrite mem_enum => Hx /esym/cards0_eq <-.
Qed.

Lemma ex_set_partition_shape (A : {set T}) sh :
  is_part_of_n #|A| sh ->
  exists2 P, partition P A & set_partition_shape P = sh.
Proof.
rewrite /is_part_of_n /= is_part_sortedE => /andP [/eqP shsum /andP [shsort]].
move=> /(ex_partition_shape shsum) [P [Puniq Ppart Psh]].
exists [set X in P]; first exact: Ppart.
apply/(eq_sorted geq_trans anti_geq).
- exact: (sort_sorted geq_total).
- exact: shsort.
- rewrite /set_partition_shape -Psh perm_sort; apply: perm_map.
  apply: (uniq_perm_eq (enum_uniq _) Puniq) => x.
  by rewrite mem_enum inE.
Qed.

Definition cycle_type_seq (s : {perm T}) := set_partition_shape (pcycles s).

Lemma cycle_type_partn s:
  is_part_of_n #|T| (cycle_type_seq s).
Proof.
  rewrite /cycle_type_seq -cardsT; apply set_partition_shapeP.
  exact: partition_pcycles.
Qed.


Definition cycle_type (s : {perm T}) := IntPartN (cycle_type_partn s).


(* Are the following definition and two lemmas really useful ? *)
Definition card_support_cycles (s : {perm T}) :=
  [seq #|(C : {set T})| | C in support_cycles s].

Lemma cycle_type_dec (s : {perm T}) :
  let l := sort geq (card_support_cycles s) in
  cycle_type_seq (s : {perm T}) = l ++ (nseq (#|T| - sumn l) 1).
Proof.
  rewrite /=.
  have := perm_sort geq (card_support_cycles s) => /perm_eqlP /perm_sumn ->.
  rewrite /card_support_cycles support_cycle_dec.
  rewrite /cycle_type_seq/set_partition_shape.
Admitted.

Lemma support_cycle_type s t :
  perm_eq (card_support_cycles s) (card_support_cycles t) ->
    cycle_type s = cycle_type t.
Proof.
  move=> Heq; apply val_inj; rewrite /= !cycle_type_dec.
  rewrite (_ : sort geq (card_support_cycles s) =
               sort geq (card_support_cycles t)) //.
  by apply/perm_sort_geq.
Qed.


Lemma conjg_cycle s a :
  (<[s]> :^ a = <[s ^ a]>)%g.
Proof.
  apply /setP => x.
  apply /imsetP/cycleP => [[x0 /cycleP [i] ->] ->|[i] ->].
  - by exists i; exact: conjXg.
  - by exists (s ^+i)%g; [apply /cycleP; exists i|rewrite conjXg].
Qed.

Lemma pcycle_conjg s a x :
  pcycle ((s ^ a)%g) (a x) = [set a y | y in pcycle s x].
Proof.
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
Proof.
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

Lemma cycle_type_of_conjg s a:
  cycle_type (s ^ a)%g = cycle_type s.
Proof.
  apply esym; apply val_inj => /=.
  rewrite /cycle_type_seq.
  rewrite pcycles_conjg; apply/perm_sort_geq.
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

Lemma conjg_of_cycle s a:
  is_cycle s -> is_cycle (s ^ a)%g.
Proof.
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

Lemma support_conjg s a:
  support (s ^ a) = [set a x | x in support s].
Proof.
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


Lemma card_support_conjg s a:
  #|support s| = #|support (s ^ a)%g|.
Proof.
  rewrite support_conjg.
  apply esym; apply card_imset.
  by exact: perm_inj.
Qed.

Lemma disjoint_imset (f: T -> T) (A B : {set T}):
  injective f ->
  [disjoint A & B] -> [disjoint [set f x | x in A] & [set f x | x in B]].
Proof.
  rewrite -!setI_eq0 => Hinj /eqP Hdisj.
  rewrite -imsetI; last by move=> x y _ _; exact: Hinj.
  by rewrite imset_eq0 Hdisj.
Qed.

Lemma conjg_of_disjoint_supports (A : {set {perm T}}) a:
  disjoint_supports A -> disjoint_supports [set (s ^ a)%g | s in A].
Proof.
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
Proof.
  have abel : abelian <<[set (c ^ a)%g | c in cycle_dec s]>>.
    apply abelian_disjoint_supports.
    apply: conjg_of_disjoint_supports.
    exact: disjoint_cycle_dec.
  apply: uniqueness_cycle_dec; constructor => [x /imsetP [x0 Hx0 ->]||].
  - apply: conjg_of_cycle; apply: is_cycle_dec.
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
Proof.
  rewrite /cycle_type /slice /cycle_type_seq /set_partition_shape /=.
  rewrite [RHS](_ : _ =
      (count_mem i) [seq #|(x : {set _})| | x <- enum (pcycles s)]);
      last by apply/perm_eqP/perm_eqlP; exact: perm_sort.
  rewrite cardE /enum_mem -enumT /=.
  rewrite size_filter count_map count_filter.
  apply eq_count => C /=; apply/imsetP/idP => [[X] | HC].
  - by rewrite inE andbC => H ->.
  - by exists C => //; rewrite inE andbC.
Qed.

Lemma cycle_type_eq s t:
  cycle_type s = cycle_type t ->
    forall i, #|slice (slpcycles s) i| = #|slice (slpcycles t) i|.
Proof. by move=> H i; rewrite !slice_slpcycleE H. Qed.

Definition conjg_pcycles s t :=
  bij (U := slpcycles s) (slpcycles t).

Lemma conjg_pcyclesP s t:
  cycle_type s = cycle_type t ->
  [/\ {in slpcycles s &, injective (conjg_pcycles (s := s) t)},
   [set (conjg_pcycles t x) | x in (slpcycles s)] = slpcycles t &
   {in (slpcycles s), forall x, #|(conjg_pcycles t x)| = #|x| } ].
Proof. by move => /cycle_type_eq; exact: bijP. Qed.

From mathcomp Require Import div.

Lemma pcycle_mod s x i:
  (s ^+ i)%g x = (s ^+ (i %% #|pcycle s x|))%g x.
Proof.
  rewrite {1}(divn_eq i #|pcycle s x|) expgD permM; congr aperm.
  elim: (i %/ #|pcycle s x|) => [| {i} i IHi].
  - by rewrite mul0n expg0 perm1.
  - by rewrite mulSnr expgD permM IHi permX; exact: iter_pcycle.
Qed.

Lemma eq_in_pcycle s x i j :
  ((s ^+ i)%g x == (s ^+ j)%g x) = (i == j %[mod #|pcycle s x|]).
Proof.
  apply/idP/idP.
  - rewrite [X in X == _]pcycle_mod [X in _ == X]pcycle_mod !permX.
    have HC : 0 < #|pcycle s x|.
      rewrite card_gt0; apply/set0Pn; exists x; exact: pcycle_id.
    rewrite -!(nth_traject _ (ltn_pmod _ HC)).
    rewrite nth_uniq // ?size_traject ?ltn_pmod //.
    exact: uniq_traject_pcycle.
  - by move=> /eqP H; apply/eqP; rewrite [LHS]pcycle_mod [RHS]pcycle_mod H.
Qed.

Definition canpcycle s x := odflt x [pick y in pcycle s x].

Lemma canpcycleP s x : x \in pcycle s (canpcycle s x).
Proof.
  rewrite /canpcycle /= pcycle_sym.
  case: pickP => [x0 //|].
  by move => /(_ x) /=; rewrite pcycle_id.
Qed.

Lemma canpcycleE s x y :
  x \in pcycle s y -> canpcycle s x = canpcycle s y.
Proof.
  move=> H; have:= H; rewrite /canpcycle -eq_pcycle_mem => /eqP ->.
  case: pickP => [x0 //|].
  by move => /(_ y) /=; rewrite pcycle_id.
Qed.

Lemma pcycleE (s: {perm T}) x y :
  y \in pcycle s x -> exists i, y == (s ^+ i)%g x.
Proof.
  move=> /pcycleP H.
  move: H => [i Hi]; exists i; by rewrite Hi.
Qed.

Definition indpcycle s (x : T) : nat := ex_minn (pcycleE (canpcycleP s x)).

Lemma indpcycleP s x : ((s ^+ (indpcycle s x)) (canpcycle s x))%g = x.
Proof. rewrite /indpcycle; by case: ex_minnP => i /eqP. Qed.

(* The image of the cycle of x *)
Definition imcycle s t :=
  let pbij := (@conjg_pcycles s t) in
  fun (x : T) => pbij (pcycle s x).

(* The canonical element of the image of the cycle of x *)
Definition conjbijcan s t x :=
    odflt x [pick y in imcycle s t x].

Definition conjbij s t x :=
    ((t ^+ (indpcycle s x)) (conjbijcan s t x))%g.

Section EqCycleType.

Variable s t : {perm T}.
Hypothesis Heq : cycle_type s = cycle_type t.

Lemma mem_imcycle x : imcycle s t x \in pcycles t.
Proof.
  move: Heq => /conjg_pcyclesP [] /= _ Himage _.
  by rewrite -Himage /imcycle; apply mem_imset; apply mem_imset.
Qed.

Lemma imcycle_perm i x : imcycle s t ((s ^+ i)%g x) = imcycle s t x.
Proof. by rewrite /imcycle pcycle_perm. Qed.

Lemma pcycle_conjbijcan x : pcycle t (conjbijcan s t x) = imcycle s t x.
Proof.
  rewrite /conjbijcan /=.
  have:= mem_imcycle x => /imsetP [y0 _ ->].
  case: pickP => [/= y|].
  - by rewrite -eq_pcycle_mem => /eqP ->.
  - by move=> /(_ y0); rewrite pcycle_id.
Qed.

Lemma card_imcycle x : #|imcycle s t x| = #|pcycle s x|.
Proof.
  rewrite /imcycle.
  move: Heq => /conjg_pcyclesP [_ _ /=]; apply.
  exact: mem_imset.
Qed.


Lemma conjbijcan_perm i x :
  conjbijcan s t ((s ^+ i)%g x) = conjbijcan s t x.
Proof.
  rewrite /conjbijcan imcycle_perm.
  have:= mem_imcycle x => /imsetP [y0 _ ->].
  by case: pickP => // /(_ y0); rewrite pcycle_id.
Qed.


Lemma conjbijP x : conjbij s t (s x) = t (conjbij s t x).
Proof.
  rewrite /conjbij -{4}(expg1 s) conjbijcan_perm.
  have := card_imcycle x; rewrite -pcycle_conjbijcan.
  move: (conjbijcan s t x) => y H.
  apply/eqP; rewrite -permM -expgSr eq_in_pcycle {}H.
  have:= canpcycleP s x; rewrite -eq_pcycle_mem => /eqP ->.
  rewrite -eq_in_pcycle.
  rewrite expgSr permM indpcycleP.
  have:= mem_pcycle s 1 x; rewrite expg1 => /canpcycleE <-.
  by rewrite indpcycleP.
Qed.


Lemma canpcycle_conjbij x : canpcycle t (conjbij s t x) = conjbijcan s t x.
Proof.
  rewrite /conjbij /conjbijcan /canpcycle pcycle_perm.
  set defim := odflt x [pick y in imcycle s t x ].
  have:= erefl defim; rewrite {1 3 4 5}/defim.
  case: pickP => [im Him | Habs] /=.
  - rewrite {}/defim => Hdefim.
    rewrite /canpcycle (_ : [pick y in  _] = some im) //.
    rewrite [LHS](_ : _ = [pick y in imcycle s t x]); first last.
      apply eq_pick => y /=; congr (y \in _).
      have:= mem_imcycle x => /imsetP [y0 _ Hy0].
      by move: Him; rewrite Hy0 /= -eq_pcycle_mem => /eqP ->.
    rewrite Hdefim.
    by case: pickP => // /(_ im); rewrite Him.
  - exfalso; move: Habs.
    have:= mem_imcycle x => /imsetP [y _ ->] /(_ y).
    by rewrite pcycle_id.
Qed.

Lemma indpcycle_conjbij x :
   indpcycle t (conjbij s t x) = indpcycle s x.
Proof.
  apply eq_ex_minn => i.
  rewrite {1}/conjbij canpcycle_conjbij eq_in_pcycle pcycle_conjbijcan.
  rewrite card_imcycle -{4}(indpcycleP s x) eq_in_pcycle.
  suff -> : pcycle s x = pcycle s (canpcycle s x) by [].
  apply/eqP; rewrite eq_pcycle_mem; exact: canpcycleP.
Qed.

End EqCycleType.


Lemma conjbijK s t :
  cycle_type s = cycle_type t -> cancel (conjbij s t) (conjbij t s).
Proof.
  rewrite /conjbij => Heq x; have Heqs := esym Heq.
  rewrite conjbijcan_perm //.
  have -> : (conjbijcan t s (conjbijcan s t x)) = canpcycle s x.
    rewrite -canpcycle_conjbij //; apply canpcycleE.
    rewrite /conjbij -eq_pcycle_mem pcycle_perm.
    rewrite pcycle_conjbijcan //.
    rewrite /imcycle pcycle_conjbijcan // /imcycle.
    rewrite /conjg_pcycles bijK //=.
    - move=> i; exact: cycle_type_eq.
    - exact: mem_imset.
  suff -> : indpcycle t ((t ^+ indpcycle s x)%g (conjbijcan s t x)) =
            indpcycle s x.
    by rewrite indpcycleP.
  by rewrite -/(conjbij s t x) indpcycle_conjbij.
Qed.

Lemma conjbij_inj s t : cycle_type s = cycle_type t -> injective (conjbij s t).
Proof. move=> /conjbijK H; exact: can_inj. Qed.

Theorem conj_permP s t :
  reflect (exists c, t = (s ^ c)%g) (cycle_type s == cycle_type t).
Proof.
  apply (iffP eqP) => [Heq | [x ->]].
  - pose c := perm (conjbij_inj Heq); exists c.
    rewrite -permP => x.
    by rewrite !permM permE conjbijP // -(permE (conjbij_inj Heq)) permKV.
  - by rewrite cycle_type_of_conjg.
Qed.

Lemma classes_of_permP s t:
  reflect (t \in (s ^: [set: {perm T}])%g) (cycle_type s == cycle_type t).
Proof.
  apply (iffP (conj_permP s t)) => [[c ->] |].
  - by apply: mem_imset; rewrite inE.
  - by move=> /imsetP [c Hc ->]; exists c.
Qed.
      
Section Permofcycletype.

Implicit Types (l : nat) (ct : intpartn #|T|).

Definition parts_of_partn ct : {set {set T}} :=
  [set C in [seq [set x in X] | X <- reshape ct (enum T)]].

Lemma parts_of_partnE ct :
  partition (parts_of_partn ct) [set: T].
Proof.
  have Hsumn : sumn ct = size (enum T) by rewrite -cardT intpartn_sumn.
  apply /and3P; split.
  - apply /eqP /setP => x; rewrite inE; apply /bigcupP.
    have := nth_flatten x (reshape ct (enum T)) (index x (enum T)).
    have : x \in (enum T) by rewrite mem_enum.
    rewrite -index_mem -Hsumn => /reshape_coordP.
    rewrite reshapeKl ?Hsumn //.
    set eT := flatten _.
    have HeT : eT = enum T.
      by rewrite /eT reshapeKr ?mem_enum ?Hsumn.
    have Hx: x \in eT by rewrite HeT mem_enum.
    case: (reshape_coord _ _) => r c [Hr Hc].
    rewrite HeT nth_index; last by rewrite mem_enum //.
    move=> Hxnth.
    exists [set x in nth [::] (reshape ct (enum T)) r].
    + rewrite /parts_of_partn inE; apply/mapP.
      exists (nth [::] (reshape ct (enum T)) r); last by [].
      by apply: mem_nth; first rewrite size_reshape.
    + rewrite Hxnth inE; apply mem_nth.
      rewrite -(nth_map _ 0); last by rewrite size_reshape.
      by rewrite -/(shape _) reshapeKl ?Hsumn.
  - apply /trivIsetP.
    admit.
  - rewrite inE; apply /mapP => [][X HX].
    move => /setP.
    case: (set_0Vmem [set: T]).
    + admit.
    + move=> [x _] => /(_ x); rewrite !inE.
      
      
    admit.
Admitted.

Definition cyclefun_of (s : {set T}) := next (enum s).

Lemma cyclefun_inj (s : {set T}) : injective (cyclefun_of s). 
Proof.
  admit.
Admitted.

Definition cycle_of_set (s : {set T}) := perm (@cyclefun_inj s).

Lemma support_cycle_of_set (s : {set T}) : #|s| > 1 -> support (cycle_of_set s) = s.
Proof.
  admit.
Admitted.
  
Lemma cycle_of_setE (s : {set T}): #|s| > 1 -> is_cycle (cycle_of_set s). 
Proof.
  admit.
Admitted.

Definition cycle_of_part ct := (\prod_(C in [set cycle_of_set s | s in parts_of_partn ct]) C)%g.


(********************************************
IL FAUT CHOISIR UN LEMME PARMI LES 2 SUIVANTS
*********************************************)

(*Sans les identites (a reformuler, cette formulation est fausse) *)
Lemma cycle_of_dec ct :
  cycle_dec (cycle_of_part ct) = [set cycle_of_set s | s in parts_of_partn ct].
Proof.
  admit.
Admitted.

(*Avec les identites*)
Lemma pcycles_cycle_of ct :
  pcycles (cycle_of_part ct) = parts_of_partn ct.
Proof.
  admit.
Admitted.


Lemma cycle_of_partE ct :
  cycle_type (cycle_of_part ct) = ct.
  
(*
Definition cyclefun_of (n l : nat) : T -> T :=
  let C := take l (drop n (enum T)) in next C.

Definition cyclefun_of (n l : nat) : T -> T :=
  let a := take l (drop n (enum T)) in
  (fun x => nth x (rot 1 a) (index x a)).

Lemma injective_cyclefun_of n l:
  injective (cyclefun_of n l).
Proof.
  move => x1 x2.
  rewrite /cyclefun_of; set a := take l (drop n (enum T)).
  case: (boolP (x1 \in a)); case (boolP (x2 \in a)).
  - rewrite -!index_mem -(size_rot 1) => Hx2 Hx1 /eqP.
    rewrite (set_nth_default x2) ?nth_uniq // ?/index => [/eqP Hind|]. 
    + rewrite size_rot -has_find in Hx2; rewrite size_rot index_mem in Hx1.
      have := (nth_find _ Hx2) => /(_ x1) /=; rewrite -Hind.
      rewrite - (_ : index x1 a = find (pred1 x1) a) // nth_index //.
      by move => /eqP.
    + rewrite rot_uniq.
      apply take_uniq; apply drop_uniq.
      by exact: enum_uniq.
  - rewrite -!index_mem ltnNge negbK -(size_rot 1) => Hx2 Hx1.
    rewrite [RHS]nth_default // => Heq.
    contradict Hx2; rewrite size_rot leqNgt index_mem.
    apply /negP; rewrite negbK -Heq -(mem_rot 1).        
    by exact:  mem_nth.
  - rewrite -!index_mem -(size_rot 1) => Hx2.
    rewrite ltnNge negbK => Hx1.
    rewrite nth_default // => Heq.
    contradict Hx1; rewrite size_rot leqNgt index_mem.    
    apply /negP; rewrite negbK Heq -(mem_rot 1).        
    by exact:  mem_nth.
  - rewrite -!index_mem !ltnNge !negbK -(size_rot 1) => Hx1 Hx2.
    by rewrite !nth_default. 
Qed.

Definition cycle_of n l : {perm T} :=
  perm (@injective_cyclefun_of n l).

Lemma cycle_ofP n l : n + l <= #|T| -> is_cycle (cycle_of n l).
Proof.
  admit.
Admitted.

Lemma support_cycle_of n l :
  n + l <= #|T| ->
    (support (cycle_of n l) = [set x | n <= index x (enum T) <= n+l-1]).
Proof.
  admit.
Admitted.

Definition cycle_dec_of_part (part : seq nat) : seq {perm T} :=
  let pp := [seq i | i <- part & i > 1] in
  mkseq (fun i => cycle_of (part_sum pp i) (nth 0 pp i)) (size pp).
(*
Fixpoint perm_of_part_rec (part : seq nat) (n : nat) : seq {perm T} :=
  match part with
  | [::] => [::]
  | a :: l1 =>
    if a == 1 then (perm_of_part_rec l1 n.+1)
    else (cycle_of n a) :: (perm_of_part_rec l1 (a + n))
  end.

*)

Definition parts_of_part (part : seq nat) : {set {set T}} :=
  [set C in [seq [set x in X] | X <- reshape part (enum T)]].

(*
Definition parts_of_part (part : seq nat) : {set {set T}} :=
  \bigcup_(S in [seq [set x in X] | X <- reshape part (enum T)]) [set S].

Definition parts_of_part (part : seq nat) : {set {set T}} :=
  \bigcup_(X <- reshape part (enum T)) [set [set x in X]].

Definition parts_of_part (part : seq nat) : {set {set T}} :=
  [set [set x in (X : seq T)] | X in reshape part (enum T)].
  \prod_(c <- cycle_dec_of_part part) c.
*)

Definition perm_of_part (part : seq nat) : {perm T} :=
  \prod_(c <- cycle_dec_of_part part) c.

(*
Lemma perm_of_part_recP (part : intpartn #|T|) c :
  c \in perm_of_part_rec part 0 -> exists n l, n+l <= #|T| /\ c = cycle_of n l.
Proof.
  admit.
Admitted.


Lemma blabla (part : intpartn #|T|) :
  [set i in perm_of_part_rec part 0] = cycle_dec (perm_of_part part).
Proof.
  apply uniqueness_cycle_dec => [C||]; last rewrite /perm_of_part.
  - by rewrite inE => /perm_of_part_recP [n [l [/cycle_ofP Hcy] ->]].
  - split.
    + apply /trivIsetP => A B.
      move => /imsetP [CA]; rewrite inE => /perm_of_part_recP [n1 [l1 [H1 ->] ->]].
      move => /imsetP [CB]; rewrite inE => /perm_of_part_recP [n2 [l2 [H2 ->] ->]].
      rewrite !support_cycle_of //.
      admit. (*besoin de plus de précisions sur qui sont n et l, par rapport a la partition initiale*)
    + move => C1 C2.
      rewrite inE => /perm_of_part_recP [n1 [l1 [H1 ->]]]. 
      rewrite inE => /perm_of_part_recP [n2 [l2 [H2 ->]]]. 
      rewrite !support_cycle_of // => /setP Heq.
      have : n1 = n2 /\ l1 = l2.
        admit.
      by move => [-> ->].
  - admit. (*big_imset, encore ...*)
Admitted.

Lemma perm_of_partE (part : intpartn #|T|) : cycle_type (perm_of_part part) = part.
Proof.
  admit.
Admitted.
*)*)
End Permofcycletype.

End cycle_type.
