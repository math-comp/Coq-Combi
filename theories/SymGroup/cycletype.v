(** * Combi.SymGroup.cycletype : The Cycle Type of a Permutation *)
(******************************************************************************)
(*      Copyright (C) 2016-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * Cycle type and conjugacy classes in the symmetric groups

This files deals with cycle type of permutations. We define the following
notions, where [s] is a permutation over a finite type [T]:

- [canporbit s x] == a chosen canonical element in the cycle of [x]
- [indporbit s x] == the position of [x] in its cycle wrt [canporbit s x]

Cycle maps:

- [porbits_map s t] == if [s] and [t] are respectively two permutations of
              two fintype [U] and [V], then [porbits_map s t] is a record for
              maps [{set U} -> {set V}], sending cycles of [s] of a given size
              to cycles of [t] of the same size.
- [cymap P] == if [P : porbits_map s t] then [cymap P] is a map [U -> V]
              which commute with [s] and [t]:

              [ Lemma cymapP x : cymap (s x) = t (cymap x). ]

              moreover, [cymap P] sends canonical to canonical [canporbit_cymap].

Cycle Type:

- [cycle_type s] == the cycle typle of [s] as a ['P_#|T|].
- [conjbij s t pf] == if [pf : cycle_type s = cycle_type t], a bijection [U -> V]
              which commute with [s] and [t]

The main results here is Theorem [conj_permP] which says that
two permutations are conjugate if and only if they have the same cycle type:

 [ reflect (exists c, t = (s ^ c)%g) (cycle_type s == cycle_type t). ]

We moreover show that there exists permutations in each partitions:

- [perm_of_porbit C] == a cyclic permutation with support [C]
- [perm_of_setpart P] == a permutation whose cycle supports are the part of
              the set partition [P]
- [permCT p] == a permutation of cycle type [p : P_#|T|].
- [classCT p] == the set of permutations of cycle type [p : P_#|T|].

Central functions:

- ['1_[p]] == the class function associated to [p : P_#|T|].
- [partnCT p] == cast a [p : 'P_#|'I_n|] to a ['P_n].
- [cycle_typeSn s] == the cycle type in ['P_n] of a permutations in ['S_n].

**********)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun finset path bigop.
From mathcomp Require Import fingroup perm action.
From mathcomp Require Import ssralg matrix mxalgebra algC classfun.


Require Import partition tools sorted.
Require Import permcomp fibered_set cycles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import LeqGeqOrder.

#[local] Hint Resolve porbit_id : core.

Reserved Notation "''1_[' G ]"
         (at level 8, G at level 2, format "''1_[' G ]").


Section CanPorbit.

Variable T : finType.
Variable s : {perm T}.

Definition canporbit x := odflt x [pick y in porbit s x].

Lemma canporbitP x : x \in porbit s (canporbit x).
Proof using.
rewrite /canporbit /= porbit_sym.
case: pickP => [x0 //|].
by move => /(_ x) /= _.
Qed.

Lemma canporbitE x y :
  (porbit s x == porbit s y) = (canporbit x == canporbit y).
Proof using.
apply/eqP/eqP => [| H].
- rewrite /canporbit => ->; case: pickP => [x0 //|].
  by move => /(_ y) /=; rewrite porbit_id.
- have:= canporbitP x; rewrite H.
  rewrite -eq_porbit_mem => /eqP ->.
  apply esym; apply/eqP; rewrite eq_porbit_mem.
  exact: canporbitP.
Qed.

Lemma porbitPb x y :
  y \in porbit s x -> exists i, y == (s ^+ i)%g x.
Proof using.
move=> /porbitP H.
by move: H => [i Hi]; exists i; rewrite Hi.
Qed.

Definition indporbit (x : T) : nat := ex_minn (porbitPb (canporbitP x)).

Lemma indporbitP x : ((s ^+ (indporbit x)) (canporbit x))%g = x.
Proof using. by rewrite /indporbit; case: ex_minnP => i /eqP. Qed.

End CanPorbit.

(** * Cycle maps *)
Section PorbitBijection.

Variables (U V : finType).
Variables (s : {perm U}) (t : {perm V}).

Record porbits_map := PorbitMap {
                          fs :> {set U} -> {set V};
                          fs_stab : fs @: porbits s \subset porbits t;
                          fs_homog : {in porbits s, forall C, #|fs C| = #|C| }
                        }.

Variable CM : porbits_map.

Lemma aux (x : U) : V.
Proof using CM.
have : fs CM (porbit s x) != set0.
  rewrite -card_gt0 fs_homog ?imset_f // card_gt0.
  by apply/set0Pn; exists x.
by move/set0Pn/sigW => H; apply H.
Qed.

Local Definition cymapcan x := odflt (aux x) [pick y in CM (porbit s x)].
Definition cymap x := ((t ^+ (indporbit s x)) (cymapcan x))%g.

Lemma fs_porbitP x : CM (porbit s x) \in porbits t.
Proof using.
by apply (subsetP (fs_stab CM)); apply imset_f; apply imset_f.
Qed.

Lemma porbit_cymapcan x : porbit t (cymapcan x) = CM (porbit s x).
Proof using.
rewrite /cymapcan /=.
have:= fs_porbitP x => /imsetP [y0 _ ->].
case: pickP => [/= y|].
- by rewrite -eq_porbit_mem => /eqP ->.
- by move=> /(_ y0); rewrite porbit_id.
Qed.

Lemma porbit_cymap x :  porbit t (cymap x) = CM (porbit s x).
Proof using. by rewrite /cymap porbit_perm porbit_cymapcan. Qed.

Lemma cymapcan_perm i x : cymapcan ((s ^+ i)%g x) = cymapcan x.
Proof using CM.
rewrite /cymapcan porbit_perm.
have:= fs_porbitP x => /imsetP [y0 _ ->].
by case: pickP => // /(_ y0); rewrite porbit_id.
Qed.

Lemma cymapP x : cymap (s x) = t (cymap x).
Proof using CM.
rewrite /cymap -{3}(expg1 s) cymapcan_perm.
have:= fs_homog CM (imset_f (x := x) _ isT); rewrite -porbit_cymapcan.
move: (cymapcan x) => y H.
apply/eqP; rewrite -permM -expgSr eq_in_porbit {}H.
have:= canporbitP s x; rewrite -eq_porbit_mem => /eqP ->.
rewrite -eq_in_porbit.
rewrite expgSr permM indporbitP.
have:= mem_porbit s 1 x; rewrite expg1 -eq_porbit_mem canporbitE => /eqP <-.
by rewrite indporbitP.
Qed.

Lemma canporbit_cymap x : canporbit t (cymap x) = cymapcan x.
Proof using CM.
rewrite /cymap /cymapcan /canporbit porbit_perm.
have:= erefl (cymapcan x); rewrite {1}/cymapcan.
case: pickP => [im Him /= Hdefim | Habs] /=.
- rewrite /canporbit (_ : [pick y in  _] = some im) //.
  rewrite [LHS](_ : _ = [pick y in CM (porbit s x)]); first last.
  apply eq_pick => y /=; congr (y \in _).
  have:= fs_porbitP x => /imsetP [y0 _ Hy0].
    by move: Him; rewrite Hy0 /= -eq_porbit_mem => /eqP ->.
  rewrite Hdefim /cymapcan.
  by case: pickP => // /(_ im); rewrite Him.
- exfalso; move: Habs.
  have:= fs_porbitP x => /imsetP [y _ ->] /(_ y).
  by rewrite porbit_id.
Qed.

Lemma indporbit_cymap x : indporbit t (cymap x) = indporbit s x.
Proof using CM.
apply eq_ex_minn => i.
rewrite {1}/cymap canporbit_cymap eq_in_porbit porbit_cymapcan.
rewrite (fs_homog CM (imset_f _ isT)) -{4}(indporbitP s x) eq_in_porbit.
suff -> : porbit s x = porbit s (canporbit s x) by [].
by apply/eqP; rewrite eq_porbit_mem; apply: canporbitP.
Qed.

End PorbitBijection.

Lemma cymapE (U V : finType) (s : {perm U}) (t : {perm V})
      (CM1 CM2 : porbits_map s t) :
   {in porbits s, CM1 =1 CM2} -> cymap CM1 =1 cymap CM2.
Proof using.
move=> Heq x; rewrite /cymap /cymapcan /=.
rewrite -Heq; last exact: imset_f.
case: pickP => // Habs.
exfalso; move: Habs.
have:= fs_porbitP CM1 x => /imsetP [y _ ->] /(_ y).
by rewrite porbit_id.
Qed.

Lemma cymap_id (U : finType) (s : {perm U}) (CM : porbits_map s s) :
  {in porbits s, CM =1 id} -> cymap CM =1 id.
Proof using.
move=> H x; rewrite /cymap /=.
rewrite -[RHS](indporbitP s).
rewrite /cymapcan /canporbit H ?imset_f //.
by case: pickP => // /(_ x); rewrite porbit_id.
Qed.

Lemma cymap_comp (U V W: finType)
      (u : {perm U}) (v : {perm V}) (w : {perm W})
      (CMuv : porbits_map u v) (CMvw : porbits_map v w) (CMuw : porbits_map u w) :
  {in porbits u, CMvw \o CMuv =1 CMuw} ->
  (cymap CMvw) \o (cymap CMuv) =1 (cymap CMuw).
Proof using.
move=> Hcomp x; rewrite /cymap /=.
rewrite /cymapcan /= porbit_perm porbit_cymapcan indporbit_cymap; congr (_ _).
have /= -> := (Hcomp (porbit u x)); last exact: imset_f.
case: (pickP (mem (CMuw _))) => // Habs; exfalso.
have:= fs_porbitP CMuw x => /imsetP [z _ Hz].
by have:= Habs z; rewrite Hz /= porbit_id.
Qed.

Lemma cymapK (U V : finType)
      (u : {perm U}) (v : {perm V})
      (CM : porbits_map u v) (CMi : porbits_map v u) :
  {in porbits u, cancel CM CMi} -> cancel (cymap CM) (cymap CMi).
Proof using.
move=> H x /=.
have porbits_stab_id (s : {perm U}) : id @: porbits s \subset porbits s.
  by rewrite imset_id.
pose CMid s := PorbitMap (porbits_stab_id s) (fun x _ => erefl #|x|).
rewrite [LHS](cymap_comp (CMuw := (CMid u))); first exact: cymap_id.
by move=> y Hy /=; exact: H.
Qed.

(** * Cycle type and conjugacy classes *)
Section CycleTypeConj.

Variable T : finType.
Implicit Types (s t : {perm T}) (n : nat).

Fact cycle_type_subproof s : is_part_of_n #|T| (setpart_shape (porbits s)).
Proof using.
rewrite -cardsT; apply setpart_shapeP.
exact: partition_porbits.
Qed.
Definition cycle_type s := IntPartN (cycle_type_subproof s).

Lemma size_cycle_type s : size (cycle_type s) = #|porbits s|.
Proof. by rewrite /cycle_type /setpart_shape size_sort size_map -cardE. Qed.

Lemma odd_cycle_type s :
  odd_perm s = odd (sumn (cycle_type s) - size (cycle_type s)).
Proof.
have:= size_part (intpartnP (cycle_type s)).
rewrite sumn_intpartn size_cycle_type => lept.
by rewrite oddB.
Qed.

Lemma cycle_type1 : cycle_type 1%g = colpartn #|T|.
Proof.
apply (colpartnP (x0 := 1)); rewrite /= /setpart_shape.
set l := sort _ _; case: (ltnP 0 (size l)) => [|];
  last by rewrite leqn0 => /nilP ->.
rewrite -nth0 {}/l => /(mem_nth 1).
rewrite mem_sort => /mapP [/= S].
rewrite mem_enum => /imsetP [x _ ->{S}] ->.
have /eqP : (1%g : {perm T}) x = x by rewrite perm1.
rewrite porbit_fix => /eqP ->.
by rewrite cards1.
Qed.

Lemma cycle_typeV s : cycle_type s^-1 = cycle_type s.
Proof. by apply val_inj; rewrite /= porbitsV. Qed.

Lemma conjg_cycle s a : (<[s]> :^ a = <[s ^ a]>)%g.
Proof using.
apply /setP => x.
apply /imsetP/cycleP => [[x0 /cycleP [i] ->] -> | [i] ->].
- by exists i; apply: conjXg.
- by exists (s ^+i)%g; [apply /cycleP; exists i | rewrite conjXg].
Qed.

Lemma porbit_conjg s a x :
  porbit ((s ^ a)%g) (a x) = [set a y | y in porbit s x].
Proof using.
rewrite !porbitE; apply /setP => y.
apply /idP/imsetP => [|[x0] Hx0 ->].
- rewrite -conjg_cycle => Hy.
  exists ((a ^-1)%g y); last by rewrite permKV.
  move: Hy; rewrite {1}(_: y = a ((a ^-1)%g (y))); last by rewrite permKV.
  by rewrite -{1}apermE orbit_conjsg.
- by rewrite -conjg_cycle -apermE orbit_conjsg.
Qed.

Lemma porbits_conjg s a :
  porbits (s ^ a)%g = [set [set a y | y in (X : {set T})] | X in porbits s].
Proof using.
apply /setP => X0.
apply /imsetP/imsetP => [[x _]|[x /imsetP [x0 _] ->] ->].
- rewrite (_: x = a ((a ^-1)%g (x))); last by rewrite permKV.
  rewrite porbit_conjg => ->.
  exists (porbit s ((a^-1)%g x)) => //.
  by apply /imsetP; exists ((a^-1)%g x).
- exists (a x0) => //.
  by rewrite porbit_conjg.
Qed.

Lemma cycle_type_conjg s a : cycle_type (s ^ a)%g = cycle_type s.
Proof using.
apply esym; apply val_inj => /=.
rewrite porbits_conjg; apply/perm_sortP => //=.
rewrite [X in perm_eq X _](eq_map (f2 := fun X : {set T} => #|a @: X|)); first last.
  by move => x;  apply esym; apply card_imset; exact: perm_inj.
rewrite (map_comp (fun x => #{x})); apply: perm_map.
apply uniq_perm.
- rewrite map_inj_uniq; first exact: enum_uniq.
  by apply imset_inj; apply: perm_inj.
- exact: enum_uniq.
- move=> x; rewrite mem_enum.
  apply/mapP/imsetP => [] [x0].
  + by rewrite mem_enum => Hx0 -> {x}; exists x0.
  + by move=> Hx0 -> {x}; exists x0; rewrite ?mem_enum.
Qed.

Lemma card_pred_card_porbits s (P : pred nat) :
  #|[set x in porbits s | P #|x| ]| = count P (cycle_type s).
Proof using.
rewrite /cycle_type /= /porbit_set /setpart_shape.
have /permPl/seq.permP -> := perm_sort geq [seq #{x} | x in porbits s].
rewrite cardE /enum_mem size_filter /= count_map count_filter.
by apply eq_count => X; rewrite !inE andbC.
Qed.

Lemma cycle_type_cyclic s :
  (s \is cyclic) = (count (fun x => x != 1) (cycle_type s) == 1).
Proof using. by rewrite -card_pred_card_porbits /porbit_set. Qed.

Lemma cyclic_conjg s a : s \is cyclic -> (s ^ a)%g \is cyclic.
Proof using. by rewrite !cycle_type_cyclic cycle_type_conjg. Qed.

Lemma psupport_conjg s a : psupport (s ^ a) = [set a x | x in psupport s].
Proof using.
rewrite -!(cover_partition (partition_psupport _)) /porbit_set.
rewrite porbits_conjg /cover (big_morph _ (imsetU _) (imset0 _)).
rewrite -[RHS](big_imset id) /=; first last.
  by move=> X Y _ _; apply: imset_inj; apply perm_inj.
apply/eq_bigl => X; rewrite !inE.
apply/andP/imsetP => [[/imsetP [/= C HC ->{X}]] | [/= C]].
- rewrite card_imset; last exact: perm_inj.
  by move=> cardC; exists C; rewrite // inE HC cardC.
- rewrite inE => /andP [HC cardC] ->{X}; split; first exact: imset_f.
  by rewrite card_imset; last exact: perm_inj.
Qed.

Lemma card_psupport_conjg s a : #|psupport s| = #|psupport (s ^ a)%g|.
Proof using.
rewrite psupport_conjg.
apply esym; apply card_imset.
exact: perm_inj.
Qed.

Lemma disjoint_psupports_conjg (A : {set {perm T}}) a :
  disjoint_psupports A -> disjoint_psupports [set (s ^ a)%g | s in A].
Proof using.
move => [/trivIsetP Hdisj Hinj].
split => [|x1 x2 /imsetP [s1 Hs1 ->] /imsetP [s2 Hs2 ->]].
- apply /trivIsetP => B1 B2.
  move => /imsetP [x1 /imsetP [s1 Hs1 ->] -> {x1}].
  move => /imsetP [x2 /imsetP [s2 Hs2 ->] -> {x2}].
  rewrite !psupport_conjg => Hdiff.
  apply disjoint_imset; first exact: perm_inj.
  apply: Hdisj; try exact: imset_f.
  by move: Hdiff; apply contra => /eqP ->.
- rewrite !psupport_conjg => Hsupp.
  rewrite (_ : s1 = s2) //; apply Hinj => //.
  apply /setP => x; apply /idP/idP => Hx.
  + have:= imset_f a Hx.
    by rewrite Hsupp => /imsetP [y] Hy /perm_inj ->.
  + have:= imset_f a Hx.
    by rewrite -Hsupp => /imsetP [y] Hy /perm_inj ->.
Qed.

Import finmodule.FiniteModule morphism.

Lemma cycle_dec_conjg s a:
  [set (c ^ a)%g | c in cycle_dec s] = cycle_dec (s ^ a)%g.
Proof using.
apply esym; apply cycle_decP; constructor => [x /imsetP [x0 Hx0 ->]||].
- by apply: cyclic_conjg; apply: cyclic_dec; apply: Hx0.
- by apply: disjoint_psupports_conjg; apply disjoint_cycle_dec.
- have abel : abelian <<[set (c ^ a)%g | c in cycle_dec s]>>.
  apply abelian_disjoint_psupports; apply: disjoint_psupports_conjg.
  exact: disjoint_cycle_dec.
 (* We tranfert the computation in the Z-module associated [abel] *)
 (* Product in the group become commutative sum in the Z-module   *)
  rewrite [LHS](_ : _ =
    val (\sum_(i in [set (c ^ a)%g | c in cycle_dec s]) fmod abel i)%R);
      first last.
    rewrite -(morph_prod [morphism of fmod abel]);
      last by move=> i; apply: mem_gen.
    rewrite -[LHS](fmodK abel) //.
    by apply group_prod => i; apply: mem_gen.
  rewrite big_imset /=; last by move=> x y _ _; apply: conjg_inj.
  rewrite -(morph_prod [morphism of fmod abel]); first last.
    by move=> i Hi; apply mem_gen; apply: imset_f.
  rewrite fmodK; first last.
    by apply group_prod => i Hi; apply mem_gen; apply: imset_f.
  by rewrite -conjg_prod cycle_decE.
Qed.

End CycleTypeConj.

Local Definition slporbits (T : finType) (s : {perm T}) :=
  FiberedSet set0 (porbits s) (fun x => #{x}).

Lemma fiber_slporbitE (T : finType) (s : {perm T}) i :
  #|fiber (slporbits s) i| = count_mem i (cycle_type s).
Proof using. by rewrite -card_pred_card_porbits /fiber /= imset_id. Qed.

Section DefsFiber.

Variables (U V : finType).
Variables (s : {perm U}) (t : {perm V}).
Hypothesis eqct : cycle_type s = cycle_type t :> seq nat.

Lemma cycle_type_eq :
  forall i, #|fiber (slporbits s) i| = #|fiber (slporbits t) i|.
Proof using eqct. by move=> i; rewrite !fiber_slporbitE eqct. Qed.

Fact conjg_porbits_stab :
  [set fbbij (slporbits t) x | x in (slporbits s)] \subset slporbits t.
Proof using eqct. by have := fbbijP cycle_type_eq => [] [] _ ->. Qed.
Fact conjg_porbits_homog :
  {in porbits s, forall C, #|fbbij (U := slporbits s) (slporbits t) C| = #|C| }.
Proof using eqct. by have := fbbijP cycle_type_eq => [] []. Qed.
Local Definition CMbij := PorbitMap conjg_porbits_stab conjg_porbits_homog.
Definition conjbij := cymap CMbij.

Lemma conjbijP x : conjbij (s x) = t (conjbij x).
Proof. exact: cymapP. Qed.

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
  rewrite !permM permE /= conjbijP.
  by rewrite -/(conjbij eqct) -(permE conjbij_inj) permKV.
- by rewrite cycle_type_conjg.
Qed.

Lemma classes_of_permP s t :
  (t \in (s ^: [set: {perm T}])%g) = (cycle_type s == cycle_type t).
Proof using.
apply /idP/conj_permP => [| [c ->]].
- by move=> /imsetP [c Hc ->]; exists c.
- by apply: imset_f; rewrite inE.
Qed.

Section Permofcycletype.

Implicit Types (l : nat) (ct : 'P_#|T|).

Fact perm_of_porbit_subproof C : injective (next (enum C)).
Proof using. by apply uniq_next; exact: enum_uniq. Qed.
Definition perm_of_porbit C := perm (@perm_of_porbit_subproof C).

Lemma psupport_perm_of_porbit C :
  #|C| > 1 -> psupport (perm_of_porbit C) = C.
Proof using.
move=> Hsize; apply /setP => x.
rewrite in_psupport permE.
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

Lemma perm_of_porbitE C x :
  x \in C -> C = porbit (perm_of_porbit C) (head x (enum C)).
Proof using.
rewrite -mem_enum; have:= erefl (enum C).
case: {2 3 4}(enum C) => [|a l HC _ /=]; first by rewrite in_nil.
apply /setP => y; apply /idP/porbitP => [| [n ->]].
- rewrite -mem_enum => Hy; exists (index y (enum C)).
  elim: (index y _) {1 2 4}y Hy (erefl (index y (enum C))) =>
                                      [| m IHm] {}y Hy Hind.
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

Lemma porbits_of_set C : #|C| > 1 -> C \in porbits (perm_of_porbit C).
Proof using.
case: (set_0Vmem C) => [->|]; first by rewrite cards0.
move=> [x Hx] Hsize.
apply /imsetP; exists (head x (enum C)) => //.
exact: perm_of_porbitE.
Qed.

Lemma porbit_set_of_set C : #|C| > 1 -> porbit_set (perm_of_porbit C) = [set C].
Proof using.
move=> Hsize; apply /setP => X.
rewrite !inE.
apply/andP/eqP => [[/imsetP [x _ ->]]|->].
- rewrite psupport_card_porbit psupport_perm_of_porbit // => Hx.
  rewrite [RHS](perm_of_porbitE Hx).
  by apply/eqP; rewrite eq_porbit_mem -perm_of_porbitE.
- split; first exact: porbits_of_set.
  by rewrite -(psupport_perm_of_porbit Hsize) card_psupport_noteq1.
Qed.

Lemma isperm_of_porbit C : #|C| > 1 -> perm_of_porbit C \is cyclic.
Proof using.
move => Hsize; apply /cards1P; exists C.
exact: porbit_set_of_set.
Qed.


Definition perm_of_setpart P : {perm T} :=
  (\prod_(C in [set perm_of_porbit s | s in [set X in P |#|X|>1]]) C)%g.

Lemma psupports_perm_of_porbit P :
  [set psupport (perm_of_porbit s) | s in [set X in P | 1 < #|X| ]] =
  [set X in P | 1 < #|X|].
Proof using.
rewrite -[RHS]imset_id.
apply eq_in_imset => i; rewrite inE => /andP [_ Hi].
by rewrite psupport_perm_of_porbit.
Qed.

Lemma disj_perm_of_setpart P :
  partition P [set: T] ->
  disjoint_psupports [set perm_of_porbit s| s in [set X0 in P | 1 < #|X0|]].
Proof using.
move => Hpart; split => [|C D].
- rewrite -imset_comp psupports_perm_of_porbit.
  apply /trivIsetP => A B; rewrite !inE.
  move => /andP [AinP _] /andP [BinP _].
  by move: Hpart => /and3P [_ /trivIsetP /(_ A B AinP BinP) ].
- move => /imsetP [A]; rewrite inE => /andP [_ cardA] ->.
  move => /imsetP [B]; rewrite inE => /andP [_ cardB] ->.
  by rewrite !psupport_perm_of_porbit // => ->.
Qed.

Lemma porbits_perm_of_setpart P :
  partition P [set: T] -> porbits (perm_of_setpart P) = P.
Proof using.
move=> Hpart; apply /setP => X.
apply /idP/idP => HX.
- case: (boolP (X \in porbit_set (perm_of_setpart P))).
  + rewrite porbit_set_of_disjoint; last exact: disj_perm_of_setpart.
    move => /bigcupP [C] /imsetP [X0].
    rewrite inE => /andP [H HX0] ->.
    by rewrite porbit_set_of_set // inE => /eqP ->.
  + rewrite inE => /nandP []; first by rewrite HX.
    move: HX => /imsetP [x _ ->].
    rewrite psupport_card_porbit => Hsupp.
    have:= Hsupp; rewrite in_psupport negbK porbit_fix => /eqP ->.
    move: Hsupp; rewrite psupport_of_disjoint; last exact: disj_perm_of_setpart.
    rewrite -(big_imset id) /=; first last.
      move=> C D /imsetP [c]; rewrite inE => /andP [_ cardc ->{C}].
      move=>     /imsetP [d]; rewrite inE => /andP [_ cardd ->{D}].
      by rewrite !psupport_perm_of_porbit // => ->.
    rewrite -imset_comp psupports_perm_of_porbit => /bigcupP.
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
    apply esym; apply/eqP; rewrite -porbit_fix.
    rewrite -[_ == x]negbK -in_psupport psupport_of_disjoint;
      last exact: disj_perm_of_setpart.
    apply /bigcupP => /exists_inP; apply /negP; rewrite negb_exists_in.
    apply /forall_inP => C /imsetP [x0]; rewrite inE => /andP [Hx0 Hcard] ->.
    rewrite psupport_perm_of_porbit //.
    move: Hpart => /and3P [_ /trivIsetP /(_ [set x] x0) Hxx0 _].
    move: Hxx0 => /(_ HX Hx0) Htmp.
    have /eqP {}/Htmp : [set x] <> x0
      by move => Heq; move: Hcard; rewrite -Heq cards1.
    rewrite -setI_eq0 => /eqP Hxx0.
    apply /negP => Hx.
    suff: x \in set0 by rewrite inE.
    by rewrite -Hxx0 inE Hx andbT inE.
  + have:= Hpart => /and3P [_ _ Hset0].
    move=> H; move: H HX Hset0.
    rewrite neq_ltn => /orP [|Hcard HX Hset0].
      by rewrite ltnS leqn0 cards_eq0 => /eqP -> ->.
    suff: X \in porbit_set (perm_of_setpart P) by rewrite inE => /andP [].
    rewrite porbit_set_of_disjoint; last exact: disj_perm_of_setpart.
    apply /bigcupP; exists (perm_of_porbit X);
      last by rewrite porbit_set_of_set ?inE.
    apply /imsetP; exists X => //.
    by rewrite inE; apply /andP; split.
Qed.

Lemma perm_of_setpartE P :
  partition P [set: T] ->
  cycle_type (perm_of_setpart P) = setpart_shape P :> seq nat.
Proof using. by move=> /porbits_perm_of_setpart pcy; rewrite /= pcy. Qed.

End Permofcycletype.


Section TPerm.

Implicit Types (x y z : T).

Lemma porbit_tpermD x y z :
  x != z -> y != z -> porbit (tperm x y) z = [set z].
Proof. by move=> xz yz; apply/eqP; rewrite -porbit_fix tpermD. Qed.

Lemma porbit_tpermL x y : porbit (tperm x y) x = [set x; y].
Proof.
apply/setP => t; rewrite !inE.
apply/porbitP/idP => [[n ->{t}] | /orP []/eqP ->{t}].
- rewrite -(odd_double_half n) expgD -mul2n expgM expgS expg1 tperm2 expg1n mulg1.
  case: (odd n) => /=; apply/orP; first by right; rewrite expg1 tpermL.
  by left; rewrite expg0 perm1.
- by exists 0; rewrite expg0 perm1.
- by exists 1; rewrite expg1 tpermL.
Qed.
Lemma porbit_tpermR x y : porbit (tperm x y) y = [set x; y].
Proof.
by rewrite tpermC porbit_tpermL; apply/setP => t; rewrite !in_set2 orbC.
Qed.
Lemma porbits_tperm x y :
  porbits (tperm x y) =
  [set x; y] |: [set [set z] | z : T & (x != z) && (y != z)].
Proof.
rewrite /porbits; apply/setP => S; rewrite !inE.
apply/imsetP/idP => [[z _ ->{S}] | /orP [/eqP->{S} | /imsetP[z]]].
- case: (altP (x =P z)) => [<-{z} | xz]; first by rewrite porbit_tpermL eqxx.
  case: (altP (y =P z)) => [{xz} <-{z} | yz]; first by rewrite porbit_tpermR eqxx.
  rewrite porbit_tpermD //; apply/orP; right.
  by apply/imsetP; exists z => //; rewrite inE xz yz.
- by exists x => //; rewrite porbit_tpermL.
- rewrite inE => /andP [xz yz] ->{S}.
  by exists z => //; rewrite porbit_tpermD.
Qed.

Lemma cycle_type_tperm x y :
  x != y -> cycle_type (tperm x y) = hookpartn #|T| 1.
Proof.
move=> Neq; set ct := cycle_type _.
have /(hookpartnPE 0) -> : nth 0 ct 1 <= 1.
  rewrite -intpartn_count_leq2E {}/ct /cycle_type /= /setpart_shape.
  set s := (X in sort geq X); have /permPl/seq.permP -> := perm_sort geq s.
  rewrite {}/s count_map /= -size_filter.
  rewrite (perm_size (s2 := [:: [set x; y]])) //; apply uniq_perm => //.
    by apply: filter_uniq; apply enum_uniq.
  rewrite porbits_tperm => S; rewrite inE mem_filter /= mem_enum.
  apply/idP/eqP => [ | ->]; last by rewrite !inE eqxx /= andbT cards2 Neq.
  rewrite andbC !inE => /andP [/orP [/eqP -> // | /imsetP [z _ ->{S}]]].
  by rewrite cards1 ltnn.
congr hookpartn.
rewrite intpartn_nth0 /ct /cycle_type /= /setpart_shape.
set s := (X in sort geq X); have /permPl/(perm_big _) -> /= := perm_sort geq s.
rewrite {}/s big_map big_enum /=.
suff -> : \max_(i in porbits (tperm x y)) #|i| = 2 by [].
rewrite porbits_tperm; apply anti_leq; apply/andP; split.
  apply/bigmax_leqP => /= S.
  by rewrite !inE=> /orP [/eqP->//| /imsetP[z _ ->{S}]];
     rewrite ?cards1 ?cards2 ?Neq.
apply: (bigmax_sup [set x; y]); last by rewrite cards2 Neq.
by rewrite !inE eqxx.
Qed.

Lemma tperm_conj x1 y1 x2 y2 :
  x1 != y1 -> x2 != y2 -> exists t, tperm x2 y2 = ((tperm x1 y1) ^ t)%g.
Proof.
move=> /cycle_type_tperm H1 /cycle_type_tperm H2.
by apply/conj_permP; rewrite H1 H2.
Qed.

Lemma cycle_type_tpermP (s : {perm T}) :
  #|T| > 1 ->
  cycle_type s = hookpartn #|T| 1 ->
  exists x y, x != y /\ s = tperm x y.
Proof.
rewrite {1}cardE.
have:= enum_uniq T; case: (enum _) => [|x[|y en]]//= /andP[].
rewrite !inE negb_or => /andP [xy _] _ _ {en}.
rewrite -(cycle_type_tperm xy) => /esym/eqP/conj_permP [/= t ->{s}].
exists (t x), (t y); split; first by rewrite (inj_eq perm_inj).
exact: tpermJ.
Qed.

End TPerm.


Section Classes.

Variable ct : 'P_#|T|.

Lemma permCT_exists : {s | cycle_type s == ct}.
Proof using.
apply sigW => /=.
have:= ex_set_setpart_shape (cast_intpartn (esym (cardsT T)) ct).
move=> [P /perm_of_setpartE /= Hct Hshape].
exists (perm_of_setpart P); apply/eqP/val_inj => /=; rewrite Hct.
by rewrite Hshape cast_intpartnE.
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

Lemma permCT_colpartn_card : permCT (colpartn #|T|) = 1%g.
Proof.
have /conj_permP [s ->] : cycle_type 1 == cycle_type (permCT (colpartn #|T|)).
  by rewrite permCTP cycle_type1.
by rewrite conj1g.
Qed.

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
  #|classes [set: {perm T}]| = #|{: 'P_#|T| }|.
Proof using.
rewrite -imset_classCT card_imset; last exact: classCT_inj.
by apply eq_card => s; rewrite !inE.
Qed.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(** * Cycle indicator *)
Section CFunIndicator.

Variable ct : 'P_#|T|.

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

Coercion CTpartn n := cast_intpartn (esym (card_ord n)).

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.


(** ** Central function for ['S_n] *)
Section Sn.

Variable n : nat.

Definition partnCT : 'P_#|'I_n| -> 'P_n := cast_intpartn (card_ord n).
Definition cycle_typeSn (s : 'S_n) : 'P_n := partnCT (cycle_type s).

Lemma CTpartnK (p : 'P_n) : partnCT p = p.
Proof using.
rewrite /partnCT; apply val_inj => /=.
by rewrite !cast_intpartnE.
Qed.

Lemma partnCTE p1 p2 : (p1 == p2) = (partnCT p1 == partnCT p2).
Proof using.
rewrite /partnCT.
apply/eqP/eqP => [-> //|].
case: p1 p2 => [p1 Hp1] [p2 Hp2].
move/(congr1 val); rewrite !cast_intpartnE /= => Hp.
exact: val_inj.
Qed.

Lemma partnCTK (p : 'P_#|'I_n|) : p = partnCT p.
Proof using.
rewrite /CTpartn; apply val_inj => /=.
by rewrite !cast_intpartnE.
Qed.

Lemma partnCT_congr p1 (p2 : 'P_n) : (partnCT p1 == p2) = (p1 == p2).
Proof using.
by apply/eqP/eqP => [<- | ->]; [rewrite -partnCTK | rewrite CTpartnK].
Qed.

Lemma CTpartn_colpartn : CTpartn (colpartn n) = colpartn #|'I_n|.
Proof. by apply val_inj; rewrite cast_intpartnE /= card_ord. Qed.

Lemma cycle_typeSn1 : cycle_typeSn 1%g = colpartn n.
Proof. by rewrite /cycle_typeSn cycle_type1 -CTpartn_colpartn CTpartnK. Qed.

Lemma permCT_colpartn : permCT (colpartn n) = 1%g.
Proof. by rewrite CTpartn_colpartn permCT_colpartn_card. Qed.

Lemma cfuniCTnE (ct : 'P_n) (s : 'S_n) :
  '1_[ct] s = (cycle_typeSn s == ct)%:R.
Proof using.
rewrite cfuniCTE /cycle_typeSn /=.
by rewrite partnCTE CTpartnK.
Qed.

Lemma cycle_typeSn_permCT (ct : 'P_n) : cycle_typeSn (permCT ct) = ct.
Proof. by rewrite /cycle_typeSn permCTP CTpartnK. Qed.

End Sn.

Lemma cast_cycle_typeSN m n (s : 'S_m) (eq_mn : m = n) :
  cycle_typeSn (cast_perm eq_mn s) = cast_intpartn eq_mn (cycle_typeSn s).
Proof. by subst n. Qed.
