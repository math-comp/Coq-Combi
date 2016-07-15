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

Definition cycle_type_seq (s : {perm T}) := parts_shape (pcycles s).

Lemma cycle_type_partn s:
  is_part_of_n #|T| (cycle_type_seq s).
Proof.
  rewrite /cycle_type_seq -cardsT; apply parts_shapeP.
  exact: partition_pcycles.
Qed.


Definition cycle_type (s : {perm T}) := IntPartN (cycle_type_partn s).


(* Are the following definition and two lemmas really useful ? *)
(*Definition card_support_cycles (s : {perm T}) :=
  [seq #|(C : {set T})| | C in support_cycles s].

Lemma cycle_type_dec (s : {perm T}) :
  let l := sort geq (card_support_cycles s) in
  cycle_type_seq (s : {perm T}) = l ++ (nseq (#|T| - sumn l) 1).
Proof.
  rewrite /=.
  have := perm_sort geq (card_support_cycles s) => /perm_eqlP /perm_sumn ->.
  rewrite /card_support_cycles support_cycle_dec.
  rewrite /cycle_type_seq/parts_shape.
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
*)

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
  rewrite /cycle_type /slice /cycle_type_seq /parts_shape /=.
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

Lemma pcyclePb (s: {perm T}) x y :
  y \in pcycle s x -> exists i, y == (s ^+ i)%g x.
Proof.
  move=> /pcycleP H.
  move: H => [i Hi]; exists i; by rewrite Hi.
Qed.

Definition indpcycle s (x : T) : nat := ex_minn (pcyclePb (canpcycleP s x)).

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

Definition cyclefun_of (s : {set T}) := next (enum s).

Lemma uniq_next (p : seq T) : uniq p -> injective (next p).
Proof.
  move=> Huniq x y Heq.
  by rewrite -(prev_next Huniq x) Heq prev_next.
Qed.


Lemma cyclefun_inj (s : {set T}) : injective (cyclefun_of s).
Proof. by apply uniq_next; exact: enum_uniq. Qed.

Definition cycle_of_set (s : {set T}) := perm (@cyclefun_inj s).

Lemma support_cycle_of_set (s : {set T}) :
  #|s| > 1 -> support (cycle_of_set s) = s.
Proof.
  move => Hsize; apply /setP => x.
  rewrite in_support permE.
  apply /idP/idP => [|Hx]; rewrite /cyclefun_of next_nth.
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
Proof.
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
    rewrite permE /cyclefun_of next_nth Hnthin {1}Hs Hnth.
    have /negbTE Hya : y != a.
      by apply /eqP => Heq; move: Hind; rewrite Heq Hs index_head.
    move: Hind; rewrite Hs -cat1s index_cat.
    rewrite inE Hya /= add1n => [[]] <-.
    rewrite nth_index //.
    by move: Hy; rewrite Hs inE Hya.
  - elim: n => [|m IHm].
    + by rewrite expg0 perm1 -mem_enum Hs mem_head.
    + by rewrite expgSr permM permE /cyclefun_of -mem_enum mem_next mem_enum.
Qed.

Lemma pcycles_of_set (s : {set T}):
  #|s| > 1 -> s \in pcycles (cycle_of_set s).
Proof.
  case: (set_0Vmem s) => [->|]; first by rewrite cards0.
  move=> [x Hx] Hsize.
  apply /imsetP; exists (head x (enum s)) => //.
  exact: cycle_of_setE.
Qed.

Lemma psupport_of_set (s : {set T}):
  #|s| > 1 -> psupport (cycle_of_set s) = [set s].
Proof.
  move=> Hsize; apply /setP => X.
  rewrite !inE.
  apply/andP/eqP => [[/imsetP [x _ ->]]|->].
  - rewrite support_card_pcycle support_cycle_of_set // => Hx.
    rewrite [RHS](cycle_of_setE Hx).
    by apply/eqP; rewrite eq_pcycle_mem -cycle_of_setE.
  - split; first exact: pcycles_of_set.
    by rewrite -(support_cycle_of_set Hsize) card_support_noteq1.
Qed.


Lemma iscycle_of_set (s : {set T}): #|s| > 1 -> is_cycle (cycle_of_set s).
Proof.
  move => Hsize.
  apply /cards1P; exists s.
  exact: psupport_of_set.
Qed.


Definition perm_of_parts (P : {set {set T}}) :=
  (\prod_(C in [set cycle_of_set s | s in [set X in P |#|X|>1]]) C)%g.

Lemma bla (P : {set {set T}}) :
  [set support (cycle_of_set s) | s in [set X in P | 1 < #|X| ]] =
  [set X in P | 1 < #|X|].
Proof.
  rewrite -[RHS]imset_id.
  apply eq_in_imset => i; rewrite inE => /andP [_ Hi].
  by rewrite support_cycle_of_set.
Qed.

Lemma disj_perm_of_parts (P : {set {set T}}):
  partition P [set: T] ->
  disjoint_supports (T:=T) [set cycle_of_set s| s in [set X0 in P | 1 < #|X0|]].
Proof.
  move => Hpart; split => [|C D].
  - rewrite -imset_comp bla.
    apply /trivIsetP => A B; rewrite !inE.
    move => /andP [AinP _] /andP [BinP _].
    by move: Hpart => /and3P [_ /trivIsetP /(_ A B AinP BinP) ].
  - move => /imsetP [A]; rewrite inE => /andP [_ cardA] ->.
    move => /imsetP [B]; rewrite inE => /andP [_ cardB] ->.
    by rewrite !support_cycle_of_set // => ->.
Qed.
    
Lemma pcycles_perm_of_parts P :
  partition P [set: T] -> pcycles (perm_of_parts P) = P.
Proof.
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
      rewrite -imset_comp bla => /bigcupP.
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
Proof.
  move => /pcycles_perm_of_parts pcy.
  by rewrite /= /cycle_type_seq pcy.
Qed.

End Permofcycletype.


Section Classes.

Variable tc : intpartn #|T|.

Lemma perm_of_partn_exists : exists s, cycle_type s = tc.
Proof.
  move: (valP (intpartn_cast (esym (cardsT T)) tc)).
  rewrite intpartn_castE => /ex_set_parts_shape [P /perm_of_partsE /= ct shape].
  exists (perm_of_parts P); apply val_inj => /=; rewrite ct.
  by exact: shape.
Qed.

Lemma perm_of_partn_set : {s | cycle_type s == tc}.
Proof. by apply sigW; have:= perm_of_partn_exists => [[p <-]]; exists p. Qed.

Definition perm_of_partn := val perm_of_partn_set.
Lemma perm_of_partnP : cycle_type perm_of_partn = tc.
Proof.
  rewrite /perm_of_partn.
  by case: perm_of_partn_set => s /= /eqP ->.
Qed.

Definition class_of_partn := class (perm_of_partn) [set: {perm T}].

Lemma class_of_partnP s :
  (cycle_type s == tc) = (s \in class_of_partn).
Proof.
  rewrite /class_of_partn -perm_of_partnP /class eq_sym.
  by apply/classes_of_permP/idP.
Qed.

End Classes.

Lemma class_of_partn_inj : injective class_of_partn.
Proof.
  rewrite /class_of_partn => t1 t2 /class_eqP.
  rewrite -class_of_partnP => /eqP <-.
  by rewrite perm_of_partnP.
Qed.

Lemma imset_class_of_partn :
  [set class_of_partn p | p in setT] = classes [set: {perm T}].
Proof.
  rewrite -setP => C.
  apply/imsetP/imsetP => [] [s _ Hs].
  - by exists (perm_of_partn s); rewrite // inE.
  - exists (cycle_type s) => //.
    by rewrite Hs; apply /class_eqP; rewrite -class_of_partnP.
Qed.

Lemma card_class_perm :
  #|classes [set: {perm T}]| = #|{: intpartn #|T| }|.
Proof.
  rewrite -imset_class_of_partn card_imset; last exact: class_of_partn_inj.
  by apply eq_card => s; rewrite !inE.
Qed.

From mathcomp Require Import matrix vector mxalgebra falgebra ssrnum algC algnum.
From mathcomp Require Import presentation all_character.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section ClassFun.

Variable tc : intpartn #|T|.

Definition classfun_part :=
  cfun_indicator [set: {perm T}] (class_of_partn tc).

Lemma classfun_partE s :
  (classfun_part s) = (cycle_type s == tc)%:R.
Proof.
  rewrite /classfun_part cfunElock genGid inE /=.
  suff -> : s ^: [set: {perm T}] \subset class_of_partn tc = (cycle_type s == tc).
    by []. (* Better way to write that ? *)
  apply/idP/idP.
  - rewrite class_of_partnP => /subsetP; apply.
    apply /imsetP; exists 1%g; first by rewrite inE.
    by rewrite conjg1.
  - move=> /eqP <-; apply/subsetP => t /imsetP [c] _ -> {t}.
    by rewrite -class_of_partnP cycle_type_of_conjg.
Qed.


End cycle_type.

