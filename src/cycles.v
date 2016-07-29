Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple path bigop finset.
From mathcomp Require Import fingroup perm action ssralg.
From mathcomp Require finmodule.

From Combi Require Import tools.

Require Import ssrcomp.

Set Implicit Arguments.
Unset Strict Implicit.


Section PermCycles.
Variable T : finType.
Implicit Type (s : {perm T}).
Implicit Type (X : {set T}).
Implicit Type (A : {set {perm T}}).

Definition support s := ~: 'Fix_('P)([set s])%g.

Lemma in_support s x : (x \in support s) = (s x != x).
Proof. by rewrite inE; apply/afix1P; case: eqP. Qed.

Lemma support_perm_on S s : (perm_on S s) = (support s \subset S).
Proof.
  apply/subsetP/subsetP => H x.
  - rewrite in_support; exact: H.
  - rewrite inE -in_support; exact: H.
Qed.

Lemma support1 : support (perm_one T) = set0.
Proof. by apply/setP => x; rewrite in_support inE perm1 eq_refl. Qed.

Lemma support_eq0 s : (s == perm_one T) = (support s == set0).
Proof.
  apply/eqP/eqP => [ -> |]; first exact: support1.
  move/setP => Heq; rewrite -permP => x.
  by move/(_ x): Heq; rewrite in_support inE perm1 => /eqP.
Qed.

Lemma support_stable s x : (x \in support s) = (s x \in support s).
Proof.
  rewrite !in_support; congr negb; apply/idP/idP => [/eqP -> // | /eqP H].
  by rewrite -[s x](permK s) H permK.
Qed.

Lemma card_support_noteq1 s : #|support s| != 1.
Proof.
  apply/cards1P => [[x] Hsupp].
  have: s x == x by rewrite -in_set1 -Hsupp -support_stable Hsupp inE.
  by move => /eqP; apply/eqP; rewrite -in_support Hsupp inE.
Qed.

Lemma support_card_pcycle s x : (#|pcycle s x| != 1) = (x \in support s).
Proof.
  rewrite inE; congr negb; apply/eqP/idP => [H|].
  - apply/afix1P => /=; by rewrite -{2}(iter_pcycle s x) H.
  - rewrite /pcycle -afix_cycle_in; last by rewrite inE.
    by move/orbit1P; rewrite /orbit /= => ->; rewrite cards1.
Qed.

Lemma pcycle_fix s x : (s x == x) = (pcycle s x == [set x]).
Proof.
  rewrite -[LHS]negbK -in_support -support_card_pcycle negbK.
  apply/eqP/eqP => [|->]; last by rewrite cards1.
  by move/card_orbit1.
Qed.

Definition psupport s := [set x in pcycles s | #|x| != 1].

Lemma in_psupportP s X x:
  reflect (exists2 X, X \in psupport s & x \in X) (s x != x).
Proof.
  rewrite -in_support; apply (iffP idP) => [Hy | [Y]].
  - exists (pcycle s x); last by apply: pcycle_id.
    by rewrite inE mem_imset //= support_card_pcycle.
  - rewrite inE => /andP [] /imsetP [y _ -> {Y}] Hcard.
    by rewrite -support_card_pcycle -eq_pcycle_mem => /eqP ->.
Qed.

Lemma partition_pcycles s : partition (pcycles s) setT.
Proof.
  rewrite /pcycles pcycleE.
  have /orbit_partition : [acts (<[s]>)%g, on [set: T] | 'P].
    by apply/actsP => x _ t; rewrite !inE.
  congr partition; apply/setP => x.
  by apply/imsetP/imsetP => [] [y _ Hy]; exists y.
Qed.

Lemma partition_support s : partition (psupport s) (support s).
Proof.
  rewrite /psupport /pcycles pcycleE.
  have /orbit_partition : [acts (<[s]>)%g, on support s | 'P].
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
Proof.
  rewrite -subset0 /psupport; apply/eqP/subsetP => [-> C| H].
  - rewrite !inE => /andP [/imsetP [x _ ->]].
    by rewrite support_card_pcycle in_support permE eq_refl.
  - apply/permP => x; rewrite permE; apply/eqP.
    have:= H (pcycle s x); rewrite !inE mem_imset //= => /contraT.
    by apply contraLR; rewrite -in_support support_card_pcycle.
Qed.

Lemma psupport_astabs s X : X \in psupport s -> s \in ('N(X | 'P))%g.
Proof.
  rewrite /astabs !inE /= => /andP [/imsetP [x0 _ -> {X} _]].
  apply/subsetP => x; rewrite inE apermE.
  rewrite -!eq_pcycle_mem => /eqP <-.
  by rewrite -{2}(expg1 s) pcycle_perm.
Qed.


Definition cyclic s := #|psupport s| == 1.
Definition cycle_dec s : {set {perm T}} :=
  [set restr_perm X s | X in psupport s].

Lemma out_restr s X x : x \notin X -> restr_perm X s x = x.
Proof. apply: out_perm; exact: restr_perm_on. Qed.

Lemma support_restr_perm s X :
  X \in psupport s -> support (restr_perm X s) = X.
Proof.
  move => HX.
  apply/setP => y; apply/idP/idP => [|Hin]; rewrite in_support.
  - by apply contraR => /out_restr /eqP.
  - rewrite restr_permE ?psupport_astabs // -in_support.
    rewrite -(cover_partition (partition_support s)).
    by apply/bigcupP; exists X.
Qed.

Lemma pcycle_restr_perm s x y :
  y \in pcycle s x -> pcycle (restr_perm (pcycle s x) s) y = pcycle s y.
Proof.
  case: (boolP (pcycle s x \in psupport s)) => [Hx Hy |].
  - have Hiter (i : nat) : (((restr_perm (pcycle s x) s)^+i) y = (s^+i) y)%g.
      elim: i => [|n Hn]; first by rewrite !expg0 !perm1.
      rewrite !expgSr !permM {}Hn (restr_permE (psupport_astabs _)) //.
      by rewrite -eq_pcycle_mem pcycle_perm eq_pcycle_mem.
    apply/setP => z; apply/pcycleP/pcycleP => [] [n].
    + by rewrite Hiter => ->; exists n.
    + by rewrite -Hiter => ->; exists n.
  - (* This case is still complicated and actually not needed *)
    rewrite inE mem_imset //= support_card_pcycle in_support negbK => H.
    have:= H; rewrite pcycle_fix => /eqP Hpcycle.
    rewrite Hpcycle inE => /eqP -> {y}.
    apply/eqP; rewrite Hpcycle -pcycle_fix restr_permE ?inE //=.
    by apply/subsetP => y; rewrite !inE => /eqP ->.
Qed.

Lemma psupport_restr s X :
  X \in psupport s -> psupport (restr_perm X s) = [set X].
Proof.
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
    (* TODO: check proof here *)
    have {Hy} Hy : Y = pcycle s y.
      rewrite Hy; apply pcycle_restr_perm.
      by apply HYX; rewrite Hy; exact: pcycle_id.
    subst Y; apply/subsetP => z.
    have:= pcycle_id s y => /HYX.
    by rewrite -eq_pcycle_mem => /eqP <-.
 -  rewrite inE HX andbT.
    apply/imsetP; exists x => //.
    apply esym; apply pcycle_restr_perm; exact: pcycle_id.
Qed.

Lemma cyclic_dec s : {in (cycle_dec s), forall C, cyclic C}.
Proof.
  move => C /imsetP [X HX ->].
  by rewrite /cyclic psupport_restr ?cards1.
Qed.

Lemma support_cycle_dec s :
  [set support C | C in cycle_dec s] = psupport s.
Proof.
  apply/setP => X; apply/imsetP/idP.
  - move => [x /imsetP[x0 Hx0 ->] ->].
    by rewrite support_restr_perm.
  - rewrite inE => /andP [HX1 HX2].
    have HX: X \in psupport s by rewrite inE HX1 HX2.
    exists (restr_perm X s); last by rewrite support_restr_perm.
    by apply/imsetP; exists X.
Qed.

Definition disjoint_supports A :=
  trivIset [set support C| C in A] /\ {in A &, injective support}.

Lemma disjoint_cycle_dec s :
  disjoint_supports (cycle_dec s).
Proof.
  split.
  - have:= partition_support s; rewrite -support_cycle_dec.
    by rewrite /partition => /and3P [].
  - move => C1 C2 /imsetP [c1 Hc1 ->] /imsetP [c2 HC2 ->].
    by rewrite !support_restr_perm // => ->.
Qed.

Lemma support_disjointC s t :
  [disjoint support s & support t] -> (s * t = t * s)%g.
Proof.
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
      by move=> H/H{H}; rewrite inE in_support negbK => /eqP ->.
    + by rewrite in_support negbK => /eqP ->; rewrite Hs.
Qed.

Lemma abelian_disjoint_supports A : disjoint_supports A -> abelian <<A>>.
Proof.
  move=> [] /trivIsetP Htriv Hinj.
  rewrite abelian_gen abelianE; apply/subsetP => C HC.
  apply/centP => D HD.
  case: (altP (C =P D)) => [-> // | HCD].
  apply support_disjointC.
  apply Htriv; try exact: mem_imset.
  move: HCD; apply contra => /eqP Hsupp; apply/eqP.
  exact: Hinj.
Qed.

Lemma abelian_cycle_dec s : abelian <<cycle_dec s>>.
Proof.
  apply abelian_disjoint_supports.
  exact: disjoint_cycle_dec.
Qed.

(*This lemma is not used later*)
Lemma restr_perm_inj s :
  {in psupport s &, injective ((restr_perm (T:=T))^~ s)}.
Proof.
  by move=> C D /support_restr_perm {2}<- /support_restr_perm {2}<- ->.
Qed.

Lemma out_perm_prod_seq (S : seq {perm T}) x :
  {in S, forall C, x \notin support C} -> (\prod_(C <- S) C)%g x = x.
Proof.
  elim: S => [_ | a S HS HaS]; first by rewrite big_nil perm1.
  rewrite big_cons permM.
  have:= HaS _ (mem_head a S); rewrite in_support negbK => /eqP ->.
  rewrite HS // => C HC.
  by apply HaS; rewrite in_cons HC orbT.
Qed.

Lemma out_perm_prod A x :
  {in A, forall C, x \notin support C} -> (\prod_(C in A) C)%g x = x.
Proof.
  move=> H; rewrite big_enum; apply out_perm_prod_seq.
  move=> C; rewrite mem_enum; exact: H.
Qed.

Import finmodule.FiniteModule morphism.

Lemma prod_of_disjoint A C x:
  disjoint_supports A -> C \in A ->
  x \in support C -> (\prod_(C0 in A) C0)%g x = C x.
Proof.
  move=> Hdisj HC Hx.
  have {Hx} Hnotin : {in A :\ C, forall C0 : {perm T}, x \notin support C0}.
    move: Hdisj => [/trivIsetP Hdisj Hinj] C0.
    rewrite 2!inE => /andP [] HC0 HC0A.
    move/(_ _ _ (mem_imset _ HC) (mem_imset _ HC0A)): Hdisj.
    have Hdiff: support C != support C0.
      by move: HC0; apply contra => /eqP/Hinj ->.
    move=> /(_ Hdiff) /disjoint_setI0 /setP /(_ x).
    rewrite inE in_set0 => /nandP [] //.
    by move => /negbTE; rewrite Hx.
  have Hin : forall i : {perm T}, (i \in A) && (i != C) -> i \in <<A>>%g.
    move => c /andP [Hi _]; exact: mem_gen.
  have abel := abelian_disjoint_supports Hdisj.
  rewrite [X in fun_of_perm X](_ :
      _ = val (\sum_(C0 in A) fmod abel C0)%R); first last.
    rewrite -morph_prod; last by move=> i; exact: mem_gen.
    rewrite -[LHS](fmodK abel) //.
    by apply group_prod => i; exact: mem_gen.
  rewrite (bigD1 C) //= GRing.addrC -morph_prod //=.
  rewrite -fmodM /=; [ | exact: group_prod | exact: mem_gen].
  rewrite fmodK; first last.
    apply groupM; last exact: mem_gen.
    exact: group_prod.
  rewrite {abel Hin Hdisj HC} permM; congr fun_of_perm.
  apply big_rec; first by rewrite perm1.
  move=> i S Hi {2}<-; rewrite permM; congr fun_of_perm.
  apply/eqP; rewrite -[_ == _]negbK -in_support.
  by apply Hnotin; rewrite !inE andbC.
Qed.

Lemma expg_prod_of_disjoint A C x i:
  disjoint_supports A -> C \in A ->
  x \in support C -> ((\prod_(C0 in A) C0) ^+ i)%g x = (C ^+ i)%g x.
Proof.
  move => Hdisj HC Hx.
  have Hin j : (C ^+ j)%g x \in support C.
    elim j => [|k Hk]; first by rewrite expg0 perm1.
    by rewrite expgSr permM -support_stable.
  elim: i => [|j Hj].
  - by rewrite !expg0 perm1.
  - by rewrite !expgSr !permM Hj (prod_of_disjoint Hdisj HC (Hin j)).
Qed.

Lemma support_of_disjoint A :
  disjoint_supports A ->
  support (\prod_(C0 in A) C0) = \bigcup_(C0 in A) support C0.
Proof.
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
Proof.
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

Lemma cycle_decE s : (\prod_(C in cycle_dec s) C)%g = s.
Proof.
  apply/permP => x.
  case: (boolP (x \in support s)) => Hx; first last.
  - rewrite out_perm_prod.
    + by move: Hx; rewrite in_support negbK => /eqP ->.
    + move=> Ctmp /imsetP [C] HC -> {Ctmp}.
      rewrite (support_restr_perm HC).
      move: Hx; apply contra => Hx.
      have:= partition_support s => /and3P [] /eqP <- _ _.
      by apply/bigcupP; exists C.
  have Hcy : pcycle s x \in psupport s.
    by rewrite inE mem_imset //= support_card_pcycle.
  rewrite (prod_of_disjoint (C := restr_perm (pcycle s x) s)).
  - rewrite restr_permE //; last exact: pcycle_id.
    exact: psupport_astabs.
  - exact: disjoint_cycle_dec.
  - by apply/imsetP; exists (pcycle s x).
  - rewrite support_restr_perm //; exact: pcycle_id.
Qed.

Lemma disjoint_supports_of_decomp A B :
  disjoint_supports A -> disjoint_supports B ->
    (\prod_(C in A) C)%g = (\prod_(C in B) C)%g ->
    {in A, forall c1, {in B, forall c2, support c1 = support c2 -> c1 = c2}}.
Proof.
  move=> HdisjA HdisjB /permP Heq c1 Hc1 c2 Hc2 /setP Hsupp.
  apply/permP => x.
  case (boolP (x \in support c1)) => H0;
  have := H0; rewrite {}Hsupp;  have := H0 => {H0}.
  - move => Hx1 Hx2; move/(_ x): Heq.
    by rewrite (prod_of_disjoint _ Hc1) ?(prod_of_disjoint _ Hc2).
  - by rewrite !in_support !negbK => /eqP -> /eqP ->.
Qed.


Lemma disjoint_supports_cycles A :
  {in A, forall C, cyclic C} ->
  disjoint_supports A ->
  {in A, forall C, support C \in pcycles (\prod_(C in A) C)%g}.
Proof.
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
  {in A, forall C, cyclic C} ->
  disjoint_supports A ->
  {in psupport (\prod_(C in A) C)%g,
    forall X, exists2 C, C \in A & support C = X}.
Proof.
  move => Hcycle Hdisj X; rewrite inE => /andP [/imsetP [x] _ -> {X} Hcard].
  case: (boolP (x \in (support (\prod_(C in A) C)%g))) => [Hin|].
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

CoInductive cycle_dec_spec s A : Prop :=
  CycleDecSpec of
    {in A, forall C, cyclic C} &
    disjoint_supports A &
    (\prod_(C in A) C)%g = s : cycle_dec_spec s A.

Theorem cycle_decP s : cycle_dec_spec s (cycle_dec s).
Proof.
  constructor.
  - exact: cyclic_dec.
  - exact: disjoint_cycle_dec s.
  - exact: cycle_decE.
Qed.

Theorem uniqueness_cycle_dec s A :
  cycle_dec_spec s A -> A = cycle_dec s.
Proof.
  move=> [Hcy Hdisj Hprod].
  apply/setP => C; apply/idP/imsetP => [HC |].
  - have:= HC => /disjoint_supports_cycles /= /(_ Hcy Hdisj) /imsetP [x _].
    rewrite Hprod => Hsupp.
    have Hx: pcycle s x \in psupport s.
      rewrite inE; apply/andP; split.
      + by apply/imsetP; exists x.
      + by rewrite -Hsupp; rewrite card_support_noteq1.
    exists (pcycle s x) => //.
    have:= disjoint_supports_of_decomp Hdisj (disjoint_cycle_dec s).
    rewrite Hprod cycle_decE => /(_ erefl C HC (restr_perm (pcycle s x) s)).
    apply; last by rewrite support_restr_perm.
    by apply/imsetP; exists (pcycle s x).
  - rewrite -{1}Hprod => [] [X HX1] ->.
    have:= disjoint_supports_pcycles Hcy Hdisj HX1 => [] [x Hx].
    rewrite -{1}(support_restr_perm HX1).
    move=> /(disjoint_supports_of_decomp Hdisj (disjoint_cycle_dec s)).
    rewrite Hprod cycle_decE => /(_ erefl Hx) <- //.
    by apply/imsetP; exists X; rewrite -Hprod.
Qed.

End PermCycles.
