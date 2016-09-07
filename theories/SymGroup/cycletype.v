(** * Combi.SymGroup.cycletype : The Cycle Type of a Permutation *)
(******************************************************************************)
(*       Copyright (C) 2014 Florent Hivert <florent.hivert@lri.fr>            *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial.
From mathcomp Require Import fingroup perm automorphism action ssralg.
From mathcomp Require finmodule.

Require Import partition tools sorted.
Require Import permcomp fibered_set cycles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import LeqGeqOrder.

Hint Resolve pcycle_id.

Reserved Notation "''1_[' G ]"
         (at level 8, G at level 2, format "''1_[' G ]").


Section CanPCycle.

Variable T : finType.
Variable s : {perm T}.

Definition canpcycle x := odflt x [pick y in pcycle s x].

Lemma canpcycleP x : x \in pcycle s (canpcycle x).
Proof using.
rewrite /canpcycle /= pcycle_sym.
case: pickP => [x0 //|].
by move => /(_ x) /= _.
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
  by apply/set0Pn; exists x.
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

Lemma pcycle_cymap x :  pcycle t (cymap x) = CM (pcycle s x).
Proof using. by rewrite /cymap pcycle_perm pcycle_cymapcan. Qed.

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
have:= erefl (cymapcan x); rewrite {1}/cymapcan.
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
by apply/eqP; rewrite eq_pcycle_mem; apply: canpcycleP.
Qed.

End PCycleBijection.


Fact pcycles_stab_id (U : finType) (s : {perm U}) :
  id @: pcycles s \subset pcycles s.
Proof using. by rewrite imset_id. Qed.
Definition CMid (U : finType) (s : {perm U}) :=
  @PCycleMap U U s s id (pcycles_stab_id s) (fun x _ => erefl #|x|).

Lemma cymapE (U V : finType) (s : {perm U}) (t : {perm V})
      (CM1 CM2 : pcycles_map s t) :
   {in pcycles s, CM1 =1 CM2} -> cymap CM1 =1 cymap CM2.
Proof using.
move=> Heq x; rewrite /cymap /cymapcan /=.
rewrite -Heq; last exact: mem_imset.
case: pickP => // Habs.
exfalso; move: Habs.
have:= fs_pcycleP CM1 x => /imsetP [y _ ->] /(_ y).
by rewrite pcycle_id.
Qed.

Lemma cymap_id (U : finType) (s : {perm U}) (CM : pcycles_map s s) :
  {in pcycles s, CM =1 id} -> cymap CM =1 id.
Proof using.
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
Proof using.
move=> Hcomp x; rewrite /cymap /=.
rewrite /cymapcan /= pcycle_perm pcycle_cymapcan indpcycle_cymap; congr (_ _).
have /= -> := (Hcomp (pcycle u x)); last exact: mem_imset.
case: (pickP (mem (CMuw _))) => // Habs; exfalso.
have:= fs_pcycleP CMuw x => /imsetP [z _ Hz].
by have:= Habs z; rewrite Hz /= pcycle_id.
Qed.

Lemma cymapK (U V : finType)
      (u : {perm U}) (v : {perm V})
      (CM : pcycles_map u v) (CMi : pcycles_map v u) :
  {in pcycles u, cancel CM CMi} -> cancel (cymap CM) (cymap CMi).
Proof using.
move=> H x /=.
rewrite [LHS](cymap_comp (CMuw := (CMid u))); first exact: cymap_id.
move=> y Hy /=; exact: H.
Qed.


Section CycleTypeConj.

Variable T : finType.
Implicit Types (s t : {perm T}) (n : nat).

Fact cycle_type_subproof (s : {perm T}) :
  is_part_of_n #|T| (parts_shape (pcycles s)).
Proof using.
rewrite -cardsT; apply parts_shapeP.
exact: partition_pcycles.
Qed.
Definition cycle_type (s : {perm T}) := IntPartN (cycle_type_subproof s).

Lemma conjg_cycle s a : (<[s]> :^ a = <[s ^ a]>)%g.
Proof using.
apply /setP => x.
apply /imsetP/cycleP => [[x0 /cycleP [i] ->] -> | [i] ->].
- by exists i; apply: conjXg.
- by exists (s ^+i)%g; [apply /cycleP; exists i | rewrite conjXg].
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

Lemma cycle_type_conjg s a : cycle_type (s ^ a)%g = cycle_type s.
Proof using.
apply esym; apply val_inj => /=.
rewrite pcycles_conjg; apply/perm_sortP => //.
rewrite (eq_map (f2 := fun X : {set T} => #|a @: X|)); first last.
  by move => x;  apply esym; apply card_imset; exact: perm_inj.
rewrite (map_comp (fun x => #{x})); apply perm_map.
apply uniq_perm_eq.
- rewrite map_inj_uniq; first exact: enum_uniq.
  by apply imset_inj; apply: perm_inj.
- exact: enum_uniq.
- move=> x; rewrite mem_enum.
  apply/mapP/imsetP => [] [x0].
  + by rewrite mem_enum => Hx0 -> {x}; exists x0.
  + by move=> Hx0 -> {x}; exists x0; rewrite ?mem_enum.
Qed.

Lemma card_pred_card_pcycles s (P : pred nat) :
  #|[set x in pcycles s | P #|x| ]| = count P (cycle_type s).
Proof using.
rewrite /cycle_type /= /psupport /parts_shape.
have /perm_eqlP/perm_eqP -> := perm_sort geq [seq #{x} | x <- enum (pcycles s)].
rewrite cardE /enum_mem size_filter /= count_map count_filter.
by apply eq_count => X; rewrite !inE andbC.
Qed.

Lemma cycle_type_cyclic s :
  (cyclic s) = (count (fun x => x != 1) (cycle_type s) == 1).
Proof using. by rewrite -card_pred_card_pcycles /psupport. Qed.

Lemma cyclic_conjg s a : cyclic s -> cyclic (s ^ a)%g.
Proof using. by rewrite !cycle_type_cyclic cycle_type_conjg. Qed.

Lemma support_conjg s a : support (s ^ a) = [set a x | x in support s].
Proof using.
rewrite -!(cover_partition (partition_support _)) /psupport.
rewrite pcycles_conjg /cover (big_morph _ (imsetU _) (imset0 _)).
rewrite -[RHS](big_imset id) /=; first last.
  by move=> X Y _ _; apply: imset_inj; apply perm_inj.
apply/eq_bigl => X; rewrite !inE.
apply/andP/imsetP => [[/imsetP [/= C HC ->{X}]] | [/= C]].
- rewrite card_imset; last exact: perm_inj.
  by move=> cardC; exists C; rewrite // inE HC cardC.
- rewrite inE => /andP [HC cardC] ->{X}; split; first exact: mem_imset.
  by rewrite card_imset; last exact: perm_inj.
Qed.

Lemma card_support_conjg s a : #|support s| = #|support (s ^ a)%g|.
Proof using.
rewrite support_conjg.
apply esym; apply card_imset.
exact: perm_inj.
Qed.

Lemma disjoint_supports_conjg (A : {set {perm T}}) a :
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

Lemma cycle_dec_conjg s a:
  [set (c ^ a)%g | c in cycle_dec s] = cycle_dec (s ^ a)%g.
Proof using.
have abel : abelian <<[set (c ^ a)%g | c in cycle_dec s]>>.
  apply abelian_disjoint_supports; apply: disjoint_supports_conjg.
  exact: disjoint_cycle_dec.
apply esym; apply cycle_decP; constructor => [x /imsetP [x0 Hx0 ->]||].
- by apply: cyclic_conjg; apply: cyclic_dec; apply: Hx0.
- by apply: disjoint_supports_conjg; apply disjoint_cycle_dec.
- rewrite [LHS](_ : _ =
    val (\sum_(i in [set (c ^ a)%g | c in cycle_dec s]) fmod abel i)%R);
      first last.
    rewrite -(morph_prod [morphism of fmod abel]);
      last by move=> i; apply: mem_gen.
    rewrite -[LHS](fmodK abel) //.
    by apply group_prod => i; apply: mem_gen.
  rewrite big_imset /=; last by move=> x y _ _; apply: conjg_inj.
  rewrite -(morph_prod [morphism of fmod abel]); first last.
    by move=> i Hi; apply mem_gen; apply: mem_imset.
  rewrite fmodK; first last.
    by apply group_prod => i Hi; apply mem_gen; apply: mem_imset.
  by rewrite -conjg_prod cycle_decE.
Qed.

End CycleTypeConj.


Definition fibered_part (T : finType) (P : {set {set T}}) :=
  FiberedSet set0 P (fun x => #{x}).

Definition slpcycles (T : finType) (s : {perm T}) := fibered_part (pcycles s).

Lemma fiber_slpcycleE (T : finType) (s : {perm T}) i :
  #|fiber (slpcycles s) i| = count_mem i (cycle_type s).
Proof using. by rewrite -card_pred_card_pcycles /fiber /= imset_id. Qed.

Section DefsFiber.

Variables (U V : finType).
Variables (s : {perm U}) (t : {perm V}).
Hypothesis eqct : cycle_type s = cycle_type t :> seq nat.

Lemma cycle_type_eq :
  forall i, #|fiber (slpcycles s) i| = #|fiber (slpcycles t) i|.
Proof using eqct. by move=> i; rewrite !fiber_slpcycleE eqct. Qed.

Fact conjg_pcycles_stab :
  [set fbbij (slpcycles t) x | x in (slpcycles s)] \subset slpcycles t.
Proof using eqct. by have := fbbijP cycle_type_eq => [] [] _ ->. Qed.
Fact conjg_pcycles_homog :
  {in pcycles s, forall C, #|fbbij (U := slpcycles s) (slpcycles t) C| = #|C| }.
Proof using eqct. by have := fbbijP cycle_type_eq => [] []. Qed.
Definition CMbij := PCycleMap conjg_pcycles_stab conjg_pcycles_homog.
Definition conjbij := cymap CMbij.

End DefsFiber.

Lemma conjbijK
      (U V : finType) (s : {perm U}) (t : {perm V})
      (eqct : cycle_type s = cycle_type t :> seq nat) :
  cancel (conjbij eqct) (conjbij (esym eqct)).
Proof using.
apply cymapK => C HC; rewrite /= fbbijK //; exact: cycle_type_eq.
Qed.


Section CycleType.

Variable T : finType.
Implicit Types (s t : {perm T}) (C : {set T}) (P : {set {set T}}).

Theorem conj_permP s t :
  reflect (exists c, t = (s ^ c)%g) (cycle_type s == cycle_type t).
Proof using.
apply (iffP eqP) => [/(congr1 val)/= eqct | [x ->]].
- have conjbij_inj := can_inj (conjbijK eqct).
  exists (perm conjbij_inj); rewrite -permP => x.
  rewrite !permM permE /= /conjbij cymapP.
  by rewrite -/(conjbij eqct) -(permE conjbij_inj) permKV.
- by rewrite cycle_type_conjg.
Qed.

Lemma classes_of_permP s t :
  (t \in (s ^: [set: {perm T}])%g) = (cycle_type s == cycle_type t).
Proof using.
apply /idP/conj_permP => [| [c ->]].
- by move=> /imsetP [c Hc ->]; exists c.
- by apply: mem_imset; rewrite inE.
Qed.

Section Permofcycletype.

Implicit Types (l : nat) (ct : intpartn #|T|).

Fact perm_of_pcycle_subproof C : injective (next (enum C)).
Proof using. by apply uniq_next; exact: enum_uniq. Qed.
Definition perm_of_pcycle C := perm (@perm_of_pcycle_subproof C).

Lemma support_perm_of_pcycle C :
  #|C| > 1 -> support (perm_of_pcycle C) = C.
Proof using.
move=> Hsize; apply /setP => x.
rewrite in_support permE.
apply/idP/idP => [|Hx]; rewrite next_nth.
- by apply contraR; rewrite -mem_enum => /negbTE ->.
- rewrite mem_enum Hx.
  move: Hsize Hx; rewrite -mem_enum cardE.
  case: (enum C) (enum_uniq (pred_of_set C)) => // a [// | b l] /=.
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

Lemma perm_of_pcycleE C x :
  x \in C -> C = pcycle (perm_of_pcycle C) (head x (enum C)).
Proof using.
rewrite -mem_enum; have:= erefl (enum C).
case: {2 3 4}(enum C) => [|a l HC _ /=]; first by rewrite in_nil.
apply /setP => y; apply /idP/pcycleP => [| [n ->]].
- rewrite -mem_enum => Hy; exists (index y (enum C)).
  elim: (index y _) {1 2 4}y Hy (erefl (index y (enum C))) =>
                                      [| m IHm] {y} y Hy Hind.
    have:= nth_index y Hy; rewrite Hind HC /= => <-.
    by rewrite expg0 perm1.
  have Hm : m < size (enum C).
    by move: Hy; rewrite -index_mem Hind; apply leq_trans.
  have Hnth : index (nth y (enum C) m) (enum C) = m.
    by rewrite index_uniq // enum_uniq.
  have Hnthin : (nth y (enum C) m) \in enum C.
    by rewrite -index_mem Hnth.
  rewrite expgSr permM -(IHm (nth y (enum C) m)) //.
  rewrite permE next_nth Hnthin {1}HC Hnth.
  have /negbTE Hya : y != a.
    by apply /eqP => Heq; move: Hind; rewrite Heq HC index_head.
  move: Hind; rewrite HC -cat1s index_cat.
  rewrite inE Hya /= add1n => [[]] <-.
  rewrite nth_index //.
  by move: Hy; rewrite HC inE Hya.
- elim: n => [|m IHm].
  + by rewrite expg0 perm1 -mem_enum HC mem_head.
  + by rewrite expgSr permM permE -mem_enum mem_next mem_enum.
Qed.

Lemma pcycles_of_set C : #|C| > 1 -> C \in pcycles (perm_of_pcycle C).
Proof using.
case: (set_0Vmem C) => [->|]; first by rewrite cards0.
move=> [x Hx] Hsize.
apply /imsetP; exists (head x (enum C)) => //.
exact: perm_of_pcycleE.
Qed.

Lemma psupport_of_set C : #|C| > 1 -> psupport (perm_of_pcycle C) = [set C].
Proof using.
move=> Hsize; apply /setP => X.
rewrite !inE.
apply/andP/eqP => [[/imsetP [x _ ->]]|->].
- rewrite support_card_pcycle support_perm_of_pcycle // => Hx.
  rewrite [RHS](perm_of_pcycleE Hx).
  by apply/eqP; rewrite eq_pcycle_mem -perm_of_pcycleE.
- split; first exact: pcycles_of_set.
  by rewrite -(support_perm_of_pcycle Hsize) card_support_noteq1.
Qed.

Lemma isperm_of_pcycle C : #|C| > 1 -> cyclic (perm_of_pcycle C).
Proof using.
move => Hsize.
apply /cards1P; exists C.
exact: psupport_of_set.
Qed.


Definition perm_of_parts P : {perm T} :=
  (\prod_(C in [set perm_of_pcycle s | s in [set X in P |#|X|>1]]) C)%g.

Lemma supports_perm_of_pcycle P :
  [set support (perm_of_pcycle s) | s in [set X in P | 1 < #|X| ]] =
  [set X in P | 1 < #|X|].
Proof using.
rewrite -[RHS]imset_id.
apply eq_in_imset => i; rewrite inE => /andP [_ Hi].
by rewrite support_perm_of_pcycle.
Qed.

Lemma disj_perm_of_parts P :
  partition P [set: T] ->
  disjoint_supports [set perm_of_pcycle s| s in [set X0 in P | 1 < #|X0|]].
Proof using.
move => Hpart; split => [|C D].
- rewrite -imset_comp supports_perm_of_pcycle.
  apply /trivIsetP => A B; rewrite !inE.
  move => /andP [AinP _] /andP [BinP _].
  by move: Hpart => /and3P [_ /trivIsetP /(_ A B AinP BinP) ].
- move => /imsetP [A]; rewrite inE => /andP [_ cardA] ->.
  move => /imsetP [B]; rewrite inE => /andP [_ cardB] ->.
  by rewrite !support_perm_of_pcycle // => ->.
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
      by rewrite !support_perm_of_pcycle // => ->.
    rewrite -imset_comp supports_perm_of_pcycle => /bigcupP.
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
    rewrite -[_ == x]negbK -in_support support_of_disjoint;
      last exact: disj_perm_of_parts.
    apply /bigcupP => /exists_inP; apply /negP; rewrite negb_exists_in.
    apply /forall_inP => C /imsetP [x0]; rewrite inE => /andP [Hx0 Hcard] ->.
    rewrite support_perm_of_pcycle //.
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
    apply /bigcupP; exists (perm_of_pcycle X);
      last by rewrite psupport_of_set ?inE.
    apply /imsetP; exists X => //.
    by rewrite inE; apply /andP; split.
Qed.

Lemma perm_of_partsE P :
  partition P [set: T] ->
  cycle_type (perm_of_parts P) = parts_shape P :> seq nat.
Proof using. by move=> /pcycles_perm_of_parts pcy; rewrite /= pcy. Qed.

End Permofcycletype.


Section Classes.

Variable ct : intpartn #|T|.

Lemma permCT_exists : {s | cycle_type s == ct}.
Proof using.
apply sigW => /=.
have:= ex_set_parts_shape (intpartn_cast (esym (cardsT T)) ct).
move=> [P /perm_of_partsE /= Hct shape].
exists (perm_of_parts P); apply/eqP/val_inj => /=; rewrite Hct.
by rewrite shape intpartn_castE.
Qed.
Definition permCT := val permCT_exists.
Lemma permCTP : cycle_type permCT = ct.
Proof. by rewrite /permCT; case: permCT_exists => s /= /eqP ->. Qed.

Definition classCT : {set {perm T}} := class permCT [set: {perm T}].

Lemma classCTP s :
  (cycle_type s == ct) = (s \in classCT).
Proof using. by rewrite eq_sym /classCT classes_of_permP permCTP. Qed.

Lemma card_classCT_neq0 : #|classCT| != 0%N.
Proof using.
by rewrite cards_eq0; apply /set0Pn; exists permCT; apply: class_refl.
Qed.

End Classes.

Lemma classCT_inj : injective classCT.
Proof using.
rewrite /classCT => t1 t2 /class_eqP.
by rewrite -classCTP permCTP => /eqP <-.
Qed.

Lemma imset_classCT :
  [set classCT p | p in setT] = classes [set: {perm T}].
Proof using.
rewrite -setP => C.
apply/imsetP/imsetP => [] [/= p _ Hp].
- by exists (permCT p); rewrite // inE.
- exists (cycle_type p) => //.
  by rewrite Hp; apply /class_eqP; rewrite -classCTP.
Qed.

Lemma card_classes_perm :
  #|classes [set: {perm T}]| = #|{: intpartn #|T| }|.
Proof using.
rewrite -imset_classCT card_imset; last exact: classCT_inj.
by apply eq_card => s; rewrite !inE.
Qed.

From mathcomp Require Import matrix vector mxalgebra falgebra ssrnum algC algnum.
From mathcomp Require Import presentation all_character.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CFunIndicator.

Variable ct : intpartn #|T|.

Definition cfuniCT :=
  cfun_indicator [set: {perm T}] (classCT ct).

Local Notation "''1_[' p ]" := (cfuniCT p) : ring_scope.

Lemma cfuniCTE s :
  ('1_[s]) = (cycle_type s == ct)%:R.
Proof using.
rewrite /cfuniCT cfunElock genGid inE /=.
congr ((nat_of_bool _) %:R); apply/idP/idP.
- rewrite classCTP => /subsetP; apply.
  apply /imsetP; exists 1%g; first by rewrite inE.
  by rewrite conjg1.
- move=> /eqP <-; apply/subsetP => t /imsetP [c] _ -> {t}.
  by rewrite -classCTP cycle_type_conjg.
Qed.

End CFunIndicator.
End CycleType.

Notation "''1_[' p ]" := (cfuniCT p) : ring_scope.

Coercion CTpartn n := intpartn_cast (esym (card_ord n)).

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.


Section Sn.

Variable n : nat.

Definition partnCT : intpartn #|'I_n| -> intpartn n :=
  intpartn_cast (card_ord n).
Definition cycle_typeSn (s : 'S_n) : intpartn n := partnCT (cycle_type s).

Lemma CTpartnK (p : intpartn n) : partnCT p = p.
Proof using.
rewrite /partnCT; apply val_inj => /=.
by rewrite !intpartn_castE.
Qed.

Lemma partnCTE p1 p2 : (p1 == p2) = (partnCT p1 == partnCT p2).
Proof using.
rewrite /partnCT.
apply/eqP/eqP => [-> //|].
case: p1 p2 => [p1 Hp1] [p2 Hp2].
move/(congr1 val); rewrite !intpartn_castE /= => Hp.
exact: val_inj.
Qed.

Lemma partnCTK (p : intpartn #|'I_n|) : p = partnCT p.
Proof using.
rewrite /CTpartn; apply val_inj => /=.
by rewrite !intpartn_castE.
Qed.

Lemma partnCT_congr p1 (p2 : intpartn n) : (partnCT p1 == p2) = (p1 == p2).
Proof using.
by apply/eqP/eqP => [<- | ->]; [rewrite -partnCTK | rewrite CTpartnK].
Qed.

Lemma cfuniCTnE (ct : intpartn n) (s : 'S_n) :
  '1_[ct] s = (cycle_typeSn s == ct)%:R.
Proof using.
rewrite cfuniCTE /cycle_typeSn /=.
by rewrite partnCTE CTpartnK.
Qed.

End Sn.

