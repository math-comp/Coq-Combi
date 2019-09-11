(** * Combi.SymGroup.cycles : The Cycle Decomposition of a Permutation *)
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
(** * The Cycle Decomposition of a Permutation

This files deals with decomposition of permutation into cycles. We define the
following notions, where [s] is a permutation over a finite type [T]:

- [support s] == the set of non fixed points for [s]
- [psupport s] == the set of the supports of the cycles of [s]
- [s \is cyclic] == [s] is a cyclic permutation
- [perm_dec E s] == for [E : {set {set T}}] the set of the restriction of [s]
                    to the elements of [E].
- [cycle_dec s] == the decomposition of [s] in cyclic permutations.
- [disjoint_supports A] == For [A : {set {perm T}}], the element of [A]
                    have pairwise dijoint supports.
- [cycle_dec_spec s A] == [A] is a decomposition of [s] into disjoint cycles.

The main result is Theorem [cycle_decP] which asserts that [cycle_dec s] is
the unique decomposition of [s] into disjoint cycles:

  [ unique (cycle_dec_spec s) (cycle_dec s). ]

**)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple path bigop finset div.
From mathcomp Require Import fingroup perm action ssralg.
From mathcomp Require finmodule.

Require Import tools permcomp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GroupScope.

Hint Resolve pcycle_id.

Section PermCycles.
Variable T : finType.
Implicit Type (s : {perm T}).
Implicit Type (X : {set T}).
Implicit Type (A : {set {perm T}}).

(** ** Support of a permutation *)
Definition support s := ~: 'Fix_('P)([set s]).

Lemma in_support s x : (x \in support s) = (s x != x).
Proof using. by rewrite inE; apply/afix1P; case: eqP. Qed.

Lemma support_expg s n : support (s ^+ n) \subset support s.
Proof using.
by apply/subsetP => x; rewrite !in_support; apply contra => /eqP/permX_fix ->.
Qed.

Lemma support_perm_on S s : (perm_on S s) = (support s \subset S).
Proof using.
apply/subsetP/subsetP => H x.
- rewrite in_support; exact: H.
- rewrite inE -in_support; exact: H.
Qed.

Lemma support1 : support (perm_one T) = set0.
Proof using. by apply/setP => x; rewrite in_support inE perm1 eq_refl. Qed.

Lemma support_eq0 s : (s == 1) = (support s == set0).
Proof using.
apply/eqP/eqP => [ -> |]; first exact: support1.
move/setP => Heq; rewrite -permP => x.
by move/(_ x): Heq; rewrite in_support inE perm1 => /eqP.
Qed.

Lemma support_stable s x : (x \in support s) = (s x \in support s).
Proof using.
rewrite !in_support; congr negb; apply/idP/idP => [/eqP -> // | /eqP H].
by rewrite -[s x](permK s) H permK.
Qed.

Lemma card_support_noteq1 s : #|support s| != 1%N.
Proof using.
apply/cards1P => [[x] Hsupp].
have: s x == x by rewrite -in_set1 -Hsupp -support_stable Hsupp inE.
by move => /eqP; apply/eqP; rewrite -in_support Hsupp inE.
Qed.

Lemma support_card_pcycle s x : (#|pcycle s x| != 1%N) = (x \in support s).
Proof using.
rewrite inE; congr negb; apply/eqP/idP => [H|].
- by apply/afix1P => /=; rewrite -{2}(iter_pcycle s x) H.
- rewrite /pcycle -afix_cycle_in; last by rewrite inE.
  by move/orbit1P; rewrite /orbit /= => ->; rewrite cards1.
Qed.


(* Complement on pcycle *)
Lemma pcycle_fix s x : (s x == x) = (pcycle s x == [set x]).
Proof using.
rewrite -[LHS]negbK -in_support -support_card_pcycle negbK.
apply/eqP/eqP => [|->]; last by rewrite cards1.
by move/card_orbit1.
Qed.

Lemma pcycle_mod s x i :
  (s ^+ i)%g x = (s ^+ (i %% #|pcycle s x|))%g x.
Proof using.
rewrite {1}(divn_eq i #|pcycle s x|) expgD permM; congr aperm.
elim: (i %/ #|pcycle s x|) => [| {i} i IHi].
- by rewrite mul0n expg0 perm1.
- by rewrite mulSnr expgD permM IHi permX; exact: iter_pcycle.
Qed.

Lemma eq_in_pcycle s x i j :
  ((s ^+ i)%g x == (s ^+ j)%g x) = (i == j %[mod #|pcycle s x|]).
Proof using.
apply/idP/idP.
- rewrite [X in X == _]pcycle_mod [X in _ == X]pcycle_mod !permX.
  have HC : 0 < #|pcycle s x|.
    by rewrite card_gt0; apply/set0Pn; exists x.
  rewrite -!(nth_traject _ (ltn_pmod _ HC)).
  rewrite nth_uniq // ?size_traject ?ltn_pmod //.
  exact: uniq_traject_pcycle.
- by move=> /eqP H; apply/eqP; rewrite [LHS]pcycle_mod [RHS]pcycle_mod H.
Qed.


(** ** psupport of a permutation *)
Definition psupport s : {set {set T}} := [set x in pcycles s | #|x| != 1%N].

Lemma in_psupportP s X x:
  reflect (exists2 X, X \in psupport s & x \in X) (s x != x).
Proof using.
rewrite -in_support; apply (iffP idP) => [Hy | [Y]].
- by exists (pcycle s x); first by rewrite inE mem_imset ?support_card_pcycle.
- rewrite inE => /andP [/imsetP [y _ -> {Y}] Hcard].
  by rewrite -support_card_pcycle -eq_pcycle_mem => /eqP ->.
Qed.

Lemma partition_pcycles s : partition (pcycles s) setT.
Proof using.
rewrite /pcycles pcycleE.
have /orbit_partition : [acts <[s]>, on [set: T] | 'P].
  by apply/actsP => x _ t; rewrite !inE.
congr partition; apply/setP => x.
by apply/imsetP/imsetP => [] [y _ Hy]; exists y.
Qed.

Lemma partition_support s : partition (psupport s) (support s).
Proof using.
rewrite /psupport /pcycles pcycleE.
have /orbit_partition : [acts <[s]>, on support s | 'P].
  apply/actsP => t /cycleP [i -> {t}] x; rewrite !in_support /=.
  rewrite -permM -expgSr expgS permM; congr negb.
  by apply/eqP/eqP => [/perm_inj| ->].
congr partition; apply/setP => x.
rewrite !inE; apply/imsetP/andP => [[y Hy -> {x}] | [/imsetP [y _ -> {x}]]].
- split; first exact: mem_imset.
  by rewrite -pcycleE support_card_pcycle.
- rewrite -pcycleE support_card_pcycle => Hy.
  by exists y.
Qed.

Lemma psupport_eq0 s : (s == perm_one T) = (psupport s == set0).
Proof using.
rewrite -subset0 /psupport; apply/eqP/subsetP => [-> C| H].
- rewrite !inE => /andP [/imsetP [x _ ->]].
  by rewrite support_card_pcycle in_support permE eq_refl.
- apply/permP => x; rewrite permE; apply/eqP.
  have:= H (pcycle s x); rewrite !inE mem_imset //= => /contraT.
  by apply contraLR; rewrite -in_support support_card_pcycle.
Qed.

Lemma psupport_astabs s X : X \in psupport s -> s \in 'N(X | 'P).
Proof using.
rewrite /astabs !inE /= => /andP [/imsetP [x0 _ -> {X} _]].
apply/subsetP => x; rewrite inE apermE.
rewrite -!eq_pcycle_mem => /eqP <-.
by rewrite -{2}(expg1 s) pcycle_perm.
Qed.

(** ** Cyclic permutations *)
Definition cyclic := [qualify s | #|psupport s| == 1%N].

Lemma cyclicP c :
  reflect (exists2 x, x \in support c & support c = pcycle c x)
          (c \is cyclic).
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
  + by rewrite -Hsc; apply: partition_support.
Qed.

Lemma cycle_cyclic t :
  t \is cyclic -> cycle t = [set t ^+ i | i : 'I_#|support t|].
Proof using.
move/cyclicP => [x Hx Hsupp]; rewrite Hsupp.
apply/setP => C; apply/cycleP/imsetP => [[i -> {C}] | [i Hi -> {C}]].
- have /(ltn_pmod i) Hmod : 0 < #|pcycle t x|.
    by rewrite card_gt0; apply/set0Pn; exists x.
  exists (Ordinal Hmod) => //=; apply/permP => y /=.
  case: (boolP (y \in pcycle t x)).
  + by rewrite -eq_pcycle_mem => /eqP <-; exact: pcycle_mod.
  + rewrite -Hsupp in_support negbK => /eqP Ht.
    by rewrite !permX_fix.
- by exists i.
Qed.

Lemma order_cyclic t : t \is cyclic -> #[t] = #|support t|.
Proof using.
rewrite /order => Hcy.
rewrite (cycle_cyclic Hcy) card_imset ?card_ord //.
move: Hcy => /cyclicP [x Hx Hsupp].
move=> [i Hi] [j Hj] /= /(congr1 (fun s => s x)) Hij.
apply val_inj => /=; apply/eqP.
rewrite -(nth_uniq x _ _ (uniq_traject_pcycle t x)) ?size_traject -?Hsupp //.
by rewrite !nth_traject // -!permX Hij.
Qed.



(** Complement about restr_perm *)
Lemma support_restr_perm_incl X s :
  support (restr_perm X s) \subset X.
Proof using.
apply/subsetP => x; rewrite in_support.
by apply contraR => /out_perm -> //; apply: restr_perm_on.
Qed.

Lemma restr_perm_neq X s x :
  restr_perm X s x != x -> restr_perm X s x = s x.
Proof using.
move=> Hx; rewrite restr_permE //; move: Hx; apply contraR.
- by move=> /triv_restr_perm ->; rewrite perm1.
- by move/(out_perm (restr_perm_on X s)) ->.
Qed.

Lemma support_restr_perm X s :
  X \in psupport s -> support (restr_perm X s) = X.
Proof using.
move => HX; apply/eqP; rewrite eqEsubset support_restr_perm_incl /=.
apply/subsetP => y Hin; rewrite in_support.
rewrite restr_permE ?psupport_astabs // -in_support.
rewrite -(cover_partition (partition_support s)).
by apply/bigcupP; exists X.
Qed.

Lemma restr_perm_supportE X s :
  restr_perm (support (restr_perm X s)) s = restr_perm X s.
Proof using.
case: (boolP (s \in 'N(X | 'P))) => [Hs|]; first last.
  move/triv_restr_perm ->; rewrite support1; apply/permP => x.
  by rewrite perm1 (out_perm (restr_perm_on _ _)) ?inE.
apply/permP => x.
case: (altP (restr_perm X s x =P x)) => Hx.
- rewrite Hx; move: Hx => /eqP.
  rewrite -[_ == _]negbK -in_support => /out_perm -> //.
  exact: restr_perm_on.
- rewrite (restr_perm_neq Hx).
  move: Hx; rewrite -in_support => Hxsupp.
  rewrite restr_permE //.
  apply/astabsP => y /=; rewrite apermE.
  case: (boolP (y \in support (restr_perm X s))) => [|Hy].
  + rewrite !in_support => Hy; have:= Hy => /restr_perm_neq => Hy2.
    move: Hy; apply contra => /eqP; rewrite -{2}Hy2 => /perm_inj.
    by rewrite Hy2 => ->.
  + apply negbTE; move: Hy; apply contra => Hsy.
    have bla i :
        (s ^+ i.+1) y \in support (restr_perm (T:=T) X s) /\
        (restr_perm (T:=T) X s ^+ i) (s y) = (s ^+ i.+1) y.
      elim: i => [|i [IHi1 IHi2]]; first by rewrite expg0 expg1 perm1.
      have := IHi1; rewrite in_support => /restr_perm_neq.
      rewrite -[RHS]permM -expgSr => <-.
      split; first by rewrite -support_stable.
      by rewrite !expgSr !permM IHi2 expgSr permM.
    have {bla} [] := bla #[s].-1 => [H _].
    move: H; rewrite prednK; last exact: order_gt0.
    by rewrite expg_order perm1.
Qed.

Lemma pcycle_restr_perm s x :
  pcycle (restr_perm (pcycle s x) s) x = pcycle s x.
Proof using.
case: (boolP (pcycle s x \in psupport s)) => [Hx|].
- have Hiter (i : nat) : (restr_perm (pcycle s x) s ^+ i) x = (s^+i) x.
    elim: i => [|n Hn]; first by rewrite !expg0 !perm1.
    rewrite !expgSr !permM {}Hn (restr_permE (psupport_astabs _)) //.
    by rewrite -eq_pcycle_mem pcycle_perm eq_pcycle_mem.
  apply/setP => z; apply/pcycleP/pcycleP => [] [n].
  + by rewrite Hiter => ->; exists n.
  + by rewrite -Hiter => ->; exists n.
- rewrite inE mem_imset //= support_card_pcycle in_support negbK => H.
  apply/eqP; have:= H; rewrite pcycle_fix => /eqP ->; rewrite -pcycle_fix.
  by rewrite restr_permE ?inE //=; apply/subsetP => y; rewrite !inE => /eqP ->.
Qed.

Lemma psupport_restr s X :
  X \in psupport s -> psupport (restr_perm X s) = [set X].
Proof using.
move=> H; have:= H; rewrite inE => /andP [/imsetP [x _ Hx] HX]; subst X.
apply/setP => Y; rewrite [RHS]inE.
apply/idP/idP => [HY | /eqP -> {Y}].
- have HYX : Y \subset (pcycle s x).
    rewrite -(support_restr_perm H).
    rewrite -(cover_partition (partition_support _)).
    by apply (bigcup_max _ HY).
  rewrite eqEsubset; apply/andP; split => //.
  move: HYX => /subsetP HYX.
  move: HY; rewrite inE => /andP [/imsetP [y _ Hy] _].
  have:= pcycle_id (restr_perm (T:=T) (pcycle s x) s) y.
  rewrite -Hy => /HYX; rewrite -eq_pcycle_mem => /eqP Heq.
  by rewrite Hy -Heq pcycle_restr_perm.
- rewrite inE HX andbT.
  apply/imsetP; exists x => //.
  by apply esym; apply pcycle_restr_perm.
Qed.


(** * Decomposition of a permutation by restriction to disjoint stable subsets *)
Definition perm_dec (S : {set {set T}}) s : {set {perm T}} :=
  [set restr_perm X s | X in S].
Definition cycle_dec s : {set {perm T}} := perm_dec (psupport s) s.

Lemma cyclic_dec s : {in (cycle_dec s), forall C, C \is cyclic}.
Proof using.
move => C /imsetP [X HX ->].
by rewrite unfold_in psupport_restr ?cards1.
Qed.

Lemma support_cycle_dec s :
  [set support C | C in cycle_dec s] = psupport s.
Proof using.
apply/setP => X; apply/imsetP/idP.
- move => [x /imsetP[x0 Hx0 ->] ->].
  by rewrite support_restr_perm.
- rewrite inE => /andP [HX1 HX2].
  have HX: X \in psupport s by rewrite inE HX1 HX2.
  exists (restr_perm X s); last by rewrite support_restr_perm.
  by apply/imsetP; exists X.
Qed.

(** ** Disjoint support and commutation *)
Definition disjoint_supports A :=
  trivIset [set support C| C in A] /\ {in A &, injective support}.

Lemma disjoint_support_subset (S1 S2 : {set {perm T}}) :
  S1 \subset S2 -> disjoint_supports S2 -> disjoint_supports S1.
Proof using.
rewrite /disjoint_supports => Hsubs [Htriv Hinj].
split.
- exact: (trivIsetS (imsetS _ Hsubs) Htriv).
- move/subsetP in Hsubs.
  by move=> s t /Hsubs Hs /Hsubs; exact: Hinj.
Qed.

Lemma disjoint_perm_dec S s :
  trivIset S -> disjoint_supports (perm_dec S s).
Proof using.
move=> Htriv.
have Hinj : {in perm_dec S s &, injective support}.
  move => C1 C2 /imsetP [c1 Hc1 ->] /imsetP [c2 HC2 ->] H.
  by rewrite -(restr_perm_supportE c1 s) H restr_perm_supportE.
split; last exact: Hinj.
apply/trivIsetP.
move=> C1 C2 /imsetP [c1 /imsetP [S1 HS1 -> ->]].
move=>       /imsetP [c2 /imsetP [S2 HS2 -> ->]] Hs12.
rewrite -setI_eq0 -subset0; apply/subsetP => x.
rewrite inE in_set0 => /andP [].
move=> /(subsetP (support_restr_perm_incl _ _)) => HxS1.
move=> /(subsetP (support_restr_perm_incl _ _)) => HxS2.
move: Htriv => /trivIsetP/(_ S1 S2 HS1 HS2) H.
have {H} /H : S1 != S2 by move: Hs12; apply contra => /eqP ->.
rewrite -setI_eq0 => /eqP/setP/(_ x).
by rewrite !inE HxS1 HxS2.
Qed.

Lemma disjoint_cycle_dec s :
  disjoint_supports (cycle_dec s).
Proof using.
apply: disjoint_perm_dec.
by have /and3P [] := partition_support s.
Qed.

Lemma support_disjointC s t :
  [disjoint support s & support t] -> commute s t.
Proof using.
move=> Hdisj; apply/permP => x; rewrite !permM.
case: (boolP (x \in support s)) => [Hs |].
- have:= Hdisj; rewrite disjoints_subset => /subsetP H.
  have:= H x Hs; rewrite inE in_support negbK => /eqP ->.
  move: Hs; rewrite support_stable => /H.
  by rewrite inE in_support negbK => /eqP ->.
- rewrite in_support negbK => /eqP Hs; rewrite Hs.
  case: (boolP (x \in support t)) => [Ht |].
  + move: Ht; rewrite support_stable.
    move: Hdisj; rewrite -setI_eq0 setIC setI_eq0 disjoints_subset => /subsetP.
    by move=> H{}/H; rewrite inE in_support negbK => /eqP ->.
  + by rewrite in_support negbK => /eqP ->; rewrite Hs.
Qed.

Lemma abelian_disjoint_supports A : disjoint_supports A -> abelian <<A>>.
Proof using.
move=> [] /trivIsetP Htriv Hinj.
rewrite abelian_gen abelianE; apply/subsetP => C HC.
apply/centP => D HD.
case: (altP (C =P D)) => [-> // | HCD].
apply support_disjointC.
apply Htriv; try exact: mem_imset.
move: HCD; apply contra => /eqP Hsupp; apply/eqP.
exact: Hinj.
Qed.

Lemma abelian_perm_dec S s : trivIset S -> abelian <<perm_dec S s>>.
Proof using.
by move=> /disjoint_perm_dec Htriv; apply abelian_disjoint_supports.
Qed.

Lemma abelian_cycle_dec s : abelian <<cycle_dec s>>.
Proof using.
by apply abelian_disjoint_supports; apply disjoint_cycle_dec.
Qed.

Lemma restr_perm_inj s :
  {in psupport s &, injective ((restr_perm (T:=T))^~ s)}.
Proof using.
by move=> C D /support_restr_perm {2}<- /support_restr_perm {2}<- ->.
Qed.

Lemma out_perm_prod_seq (S : seq {perm T}) x :
  {in S, forall C, x \notin support C} -> (\prod_(C <- S) C) x = x.
Proof using.
elim: S => [_ | a S HS HaS]; first by rewrite big_nil perm1.
rewrite big_cons permM.
have:= HaS _ (mem_head a S); rewrite in_support negbK => /eqP ->.
rewrite HS // => C HC.
by apply HaS; rewrite in_cons HC orbT.
Qed.

Lemma out_perm_prod A x :
  {in A, forall C, x \notin support C} -> (\prod_(C in A) C) x = x.
Proof using.
move=> H; rewrite big_enum; apply out_perm_prod_seq.
move=> C; rewrite mem_enum; exact: H.
Qed.

Import finmodule.FiniteModule morphism.

Lemma prod_of_disjoint A C x:
  disjoint_supports A -> C \in A ->
  x \in support C -> (\prod_(C0 in A) C0) x = C x.
Proof using.
move=> Hdisj HC Hx.
have {Hx} Hnotin : {in A :\ C, forall C0 : {perm T}, x \notin support C0}.
  move: Hdisj => [/trivIsetP Hdisj Hinj] C0.
  rewrite 2!inE => /andP [HC0 HC0A].
  move/(_ _ _ (mem_imset _ HC) (mem_imset _ HC0A)): Hdisj.
  have Hdiff: support C != support C0.
    by move: HC0; apply contra => /eqP/Hinj ->.
  move=> /(_ Hdiff) /disjoint_setI0 /setP /(_ x).
  rewrite inE in_set0 => /nandP [] //.
  by move => /negbTE; rewrite Hx.
have Hin : forall i : {perm T}, (i \in A) && (i != C) -> i \in <<A>>.
  by move => c /andP [Hi _]; apply: mem_gen.
have abel := abelian_disjoint_supports Hdisj.
(* We tranfert the computation in the Z-module associated [abel] *)
(* Product in the group become commutative sum in the Z-module   *)
rewrite [X in fun_of_perm X](_ :
           _ = val (\sum_(C0 in A) fmod abel C0)%R); first last.
  rewrite -morph_prod /=; last by move=> i; apply: mem_gen.
  rewrite -[LHS](fmodK abel) //.
  by apply group_prod => i; apply: mem_gen.
rewrite (bigD1 C) //= GRing.addrC -morph_prod //=.
rewrite -fmodM /=; [ | exact: group_prod | exact: mem_gen].
rewrite fmodK; first last.
  apply groupM; last exact: mem_gen.
  exact: group_prod.
(* Back in symmetric group computation *)
rewrite {abel Hin Hdisj HC} permM; congr fun_of_perm.
apply big_rec; first by rewrite perm1.
move=> i S Hi {2}<-; rewrite permM; congr fun_of_perm.
apply/eqP; rewrite -[_ == _]negbK -in_support.
by apply Hnotin; rewrite !inE andbC.
Qed.

Lemma expg_prod_of_disjoint A C x i:
  disjoint_supports A -> C \in A ->
  x \in support C -> ((\prod_(C0 in A) C0) ^+ i) x = (C ^+ i) x.
Proof using.
move => Hdisj HC Hx.
have Hin j : (C ^+ j) x \in support C.
  elim j => [|k Hk]; first by rewrite expg0 perm1.
  by rewrite expgSr permM -support_stable.
elim: i => [|j Hj].
- by rewrite !expg0 perm1.
- by rewrite !expgSr !permM Hj (prod_of_disjoint Hdisj HC (Hin j)).
Qed.

Lemma support_of_disjoint A :
  disjoint_supports A ->
  support (\prod_(C0 in A) C0) = \bigcup_(C0 in A) support C0.
Proof using.
move=> Hdisj; apply/setP => x.
rewrite in_support; apply/idP/bigcupP => [| [C] HC Hx].
- move=> H; apply/ exists_inP; move: H.
  apply contraR; rewrite negb_exists_in => /forallP Hsupp.
  apply/eqP; apply out_perm_prod => C.
  by move: (Hsupp C)=> /implyP.
- by rewrite (prod_of_disjoint Hdisj HC Hx) -in_support.
Qed.

Lemma psupport_of_disjoint A :
  disjoint_supports A ->
  psupport (\prod_(C0 in A) C0) = \bigcup_(C0 in A) psupport C0.
Proof using.
move=> Hdisj; apply/setP => X; rewrite inE.
apply/andP/bigcupP => [[]/imsetP [x _ ->] Hcard|[C] HC].
- have:= Hcard; rewrite support_card_pcycle support_of_disjoint //.
  move=> /bigcupP => [][C HC Hx]; exists C => //.
  rewrite inE; apply/andP; split => //.
  apply/imsetP; exists x => //.
  apply/setP => y.
  by apply/pcycleP/pcycleP =>[][i ->];
    exists i; rewrite (expg_prod_of_disjoint _ _ HC).
- rewrite inE => /andP [/imsetP[x _ ->] Hcard].
  split =>//.
  apply/imsetP; exists x => //.
  apply/setP=> y; rewrite support_card_pcycle in Hcard.
  by apply/pcycleP/pcycleP =>[][i ->];
    exists i; rewrite (expg_prod_of_disjoint _ _ HC).
Qed.

Lemma perm_decE S s :
  trivIset S -> support s \subset cover S ->
  s \in 'C(S | ('P)^* ) ->
  \prod_(C in perm_dec S s) C = s.
Proof using.
move=> Htriv /subsetP Hcover Hact.
apply/permP => x.
case: (boolP (x \in support s)) => Hx; first last.
  rewrite out_perm_prod.
  + by move: Hx; rewrite in_support negbK => /eqP ->.
  + move=> Ctmp /imsetP [C] HC -> {Ctmp}.
    move: Hx; apply contra; rewrite !in_support => H.
    by have:= H; rewrite (restr_perm_neq H).
have:= Hcover x Hx => /bigcupP => [[C HC HxC]].
have Hrestr : (restr_perm (T:=T) C s) x = s x.
  rewrite restr_permE // -astab1_set.
  move: Hact => /astab_act/(_ HC) Hact.
  by apply/astabP => D; rewrite inE => /eqP ->{D}.
rewrite (prod_of_disjoint (C := restr_perm C s)).
- exact: Hrestr.
- exact: disjoint_perm_dec.
- exact: mem_imset.
- by move: Hx; rewrite !in_support Hrestr.
Qed.

Lemma cycle_decE s : \prod_(C in cycle_dec s) C = s.
Proof using.
have /and3P [/eqP Hcov Htriv _] := partition_support s.
apply perm_decE => //; first by rewrite Hcov.
apply/astabP => C /psupport_astabs.
rewrite -astab1_set => /astabP; apply.
by rewrite inE.
Qed.

Lemma disjoint_supports_of_decomp A B :
  disjoint_supports A -> disjoint_supports B ->
    \prod_(C in A) C = \prod_(C in B) C ->
    {in A & B, forall c1 c2, support c1 = support c2 -> c1 = c2}.
Proof using.
move=> HdisjA HdisjB /permP Heq c1 c2 Hc1 Hc2 /setP Hsupp.
apply/permP => x.
case: (boolP (x \in support c1)) => H0;
  have:= H0; rewrite {}Hsupp; move: H0.
- move => Hx1 Hx2; move/(_ x): Heq.
  by rewrite (prod_of_disjoint _ Hc1) ?(prod_of_disjoint _ Hc2).
- by rewrite !in_support !negbK => /eqP -> /eqP ->.
Qed.


Lemma disjoint_supports_cycles A :
  {in A, forall C, C \is cyclic} ->
  disjoint_supports A ->
  {in A, forall C, support C \in pcycles (\prod_(C in A) C)}.
Proof using.
move=> Hcycle Hdisj C HC; move/(_ C HC): Hcycle.
rewrite /cyclic => /cards1P [X] Hpsupp.
have:= eq_refl X; rewrite -in_set1 -Hpsupp inE => /andP [/imsetP [x _] Hx].
subst X; rewrite pcycleE=> Hcard.
have:= cover_partition (partition_support C); rewrite Hpsupp.
rewrite /cover big_set1 => <-; apply/imsetP; exists x => //.
have Hx : x \in support C.
  rewrite in_support; apply/eqP; rewrite -apermE => /afix1P.
  rewrite -afix_cycle => /orbit1P Hcontra.
  by move: Hcard; rewrite Hcontra cards1.
by apply/setP => y; apply/pcycleP/pcycleP => [] [i] ->;
  exists i; apply esym; rewrite (expg_prod_of_disjoint i Hdisj HC).
Qed.


Lemma disjoint_supports_pcycles A :
  {in A, forall C, C \is cyclic} ->
  disjoint_supports A ->
  {in psupport (\prod_(C in A) C),
    forall X, exists2 C, C \in A & support C = X}.
Proof using.
move => Hcycle Hdisj X; rewrite inE => /andP [/imsetP [x] _ -> {X} Hcard].
case: (boolP (x \in support (\prod_(C in A) C))) => [Hin|].
- have: exists2 C0, (C0 \in A) & (x \in support C0).
    apply/exists_inP.
    move: Hin; apply contraLR; rewrite negb_exists => /forallP Hnotin.
    rewrite in_support negbK; apply/eqP; apply out_perm_prod => C HC.
    by have:= Hnotin C; rewrite HC andTb.
  move => [C0] HC0 Hx.
  exists C0 => //; move: Hx.
  have: support C0 \in (pcycles (\prod_(C in A) C)).
    exact: disjoint_supports_cycles.
  move => /imsetP [y] _ ->.
  by rewrite -eq_pcycle_mem => /eqP.
- rewrite in_support negbK pcycleE -apermE => /eqP /afix1P.
  rewrite -afix_cycle => /orbit1P.
  rewrite -pcycleE => Hcontra; move: Hcard.
  by rewrite Hcontra cards1.
Qed.

(** ** Cycle decomposition of a permutation *)
Variant cycle_dec_spec s A : Prop :=
  CycleDecSpec of
    {in A, forall C, C \is cyclic} &
    disjoint_supports A &
    \prod_(C in A) C = s : cycle_dec_spec s A.

Theorem cycle_decP s : unique (cycle_dec_spec s) (cycle_dec s).
Proof using.
split; first by constructor;
    [ exact: cyclic_dec |  exact: disjoint_cycle_dec | exact: cycle_decE].
move=> A [Hcy Hdisj Hprod].
apply/setP => /= C; apply/imsetP/idP=> /= [| HC].
- rewrite -{1}Hprod => [] [X HX1] ->.
  have:= disjoint_supports_pcycles Hcy Hdisj HX1 => [] [x Hx].
  rewrite -{1}(support_restr_perm HX1).
  move=> /(disjoint_supports_of_decomp Hdisj (disjoint_cycle_dec s)).
  rewrite Hprod cycle_decE => /(_ erefl Hx) <- //.
  by apply/imsetP; exists X; rewrite -Hprod.
- have:= HC => /disjoint_supports_cycles /= /(_ Hcy Hdisj) /imsetP [x _].
  rewrite Hprod => Hsupp.
  have Hx: pcycle s x \in psupport s.
    rewrite inE; apply/andP; split.
    + by apply/imsetP; exists x.
    + by rewrite -Hsupp; rewrite card_support_noteq1.
  exists (pcycle s x) => //.
  have:= disjoint_supports_of_decomp Hdisj (disjoint_cycle_dec s).
  rewrite Hprod cycle_decE => /(_ erefl C (restr_perm (pcycle s x) s) HC).
  apply; last by rewrite support_restr_perm.
  by apply/imsetP; exists (pcycle s x).
Qed.

End PermCycles.

Arguments cyclic {T}.
