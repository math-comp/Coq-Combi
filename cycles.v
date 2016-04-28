Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial.
From mathcomp Require Import fingroup perm automorphism action.

From Combi Require Import symgroup partition Greene sorted.

Set Implicit Arguments.
Unset Strict Implicit.

Section SSRComplements.
Variable T: finType.

Variables (R : Type) (idx : R) (op : R -> R -> R) (F : T -> R).

Lemma big_enum (S : {set T}) :
  \big[op/idx]_(s in S) F s = \big[op/idx]_(s <- enum S) F s.
Proof. by rewrite /index_enum big_filter; apply congr_big. Qed.

Lemma triv_part (P:{set {set T}}) (X:{set T}) (D:{set T}):
  partition P D -> X \in P -> D \subset X -> P = [set X].
Proof.
  rewrite /partition => /and3P [] /eqP Hcov /trivIsetP H H0 HXP /subsetP HD.
  have:= H X; clear H => H.
  case: (set_0Vmem (P:\ X)) => [/eqP|].
  - rewrite setD_eq0 subset1 => /orP [] /eqP // Hcontra.
    by move: HXP; rewrite Hcontra inE.
  - move => [] Y.
    rewrite in_setD1 => /andP [].
    rewrite eq_sym => Hdiff HYP.
    have:= H Y HXP HYP Hdiff; clear H.
    move => /disjoint_setI0 HXY.
    case: (set_0Vmem Y) => [HY|[] x HxY]; first by move: H0; rewrite -HY => /negP.
    have: x \in cover P.
      by apply /bigcupP; exists Y.
    rewrite Hcov => HxD.
    have:= HD x HxD => HxX.
    have: x \in X :&: Y.
      by rewrite inE; apply /andP.
    by rewrite HXY inE.
Qed.

Lemma partition_of0 (P:{set {set T}}):
  partition P set0 -> P = set0.
Proof.
  rewrite /partition => /and3P [] /eqP H1 _ H2.
  case: (set_0Vmem P) => [//|[] X].
  case: (set_0Vmem X) => [-> H3|[] x Hx HX]; first by move: H2 => /negP.
  have: x \in cover P by apply /bigcupP; exists X.
  by rewrite H1 inE.
Qed.

Lemma pcycleP (s: {perm T}) x y : reflect (exists i, y = (s ^+ i)%g x) (y \in pcycle s x).
Proof.
  apply (iffP idP).
  - rewrite pcycle_traject => H.
    have:= H; rewrite -index_mem size_traject => Hlt.
    exists (index y (traject s x #|pcycle s x|)).
    have {Hlt} := nth_traject s Hlt x; rewrite (nth_index _ H) => {H} {1}->.
    elim: (index _ _) => [|n IHn] /=; first by rewrite expg0 perm1.
    by rewrite expgSr permM IHn.
  - move => [i ->]; exact: mem_pcycle.
Qed.

Lemma in_seq (l : seq T) (x : T) :
 x \in l -> exists l1 l2, l = l1 ++ (x :: l2).
Proof.
  elim: l => [|a l Hl]; first by rewrite in_nil.
  rewrite in_cons => /orP [/eqP ->| /Hl]; first by exists [::]; exists l.
  move => {Hl} [l1] [l2] ->.
  by exists (a :: l1); exists l2.
Qed.

Lemma enum_eq0P (s : {set T}):
  reflect (enum s = [::]) (s == set0).
Proof.
  apply (iffP idP) => [/eqP -> | ]; first by rewrite enum_set0.
  case: (set_0Vmem s) => [-> //| [x]].
  rewrite -mem_enum => Hx Hnil.
  by rewrite Hnil in_nil in Hx.
Qed.

End SSRComplements.


Section PermCycles.
Variable T: finType.
Implicit Type (s: {perm T}).

Definition support s := ~:'Fix_('P)([set s])%g.

Lemma in_support s x : (x \in support s) = (s x != x).
Proof.
  apply /idP/idP => [| /eqP H]; rewrite inE.
  - by move => /afix1P /= /eqP.
  - by apply /afix1P => /=; rewrite apermE.
Qed.

Lemma support_perm_on S s : (perm_on S s) = (support s \subset S).
Proof.
  apply/subsetP/subsetP => H x.
  - rewrite in_support; exact: H.
  - rewrite inE -in_support; exact: H.
Qed.

Lemma support_eq0 s:
  (s == perm_one T) = (support s == set0).
Proof.
  apply/eqP/eqP => [ -> |].
  - case: (set_0Vmem (support (perm_one T))) => [//|[] x].
    rewrite inE => /afix1P /=; rewrite apermE.
    by rewrite perm1.
  - rewrite -setCT => /setC_inj /= H.
    rewrite -permP => x.
    by rewrite perm1 -apermE; apply /afix1P; rewrite H.
Qed.

Lemma support1 : (support (perm_one T)) = set0.
Proof. by apply /eqP; rewrite -support_eq0. Qed.

Lemma support_stable s x : (x \in support s) = (s x \in support s).
Proof.
  rewrite !in_support; congr negb; apply/idP/idP => [/eqP -> // | /eqP H].
  by rewrite -[s x](permK s) H permK.
Qed.

Lemma card_support_noteq1 s:
  #|support s| != 1.
Proof.
  apply /cards1P => [] [x] Hsupp.
  have: s x == x.
  - by rewrite -in_set1 -Hsupp -support_stable Hsupp inE.
  - by move => /eqP; apply /eqP; rewrite -in_support Hsupp inE.
Qed.

Definition psupport s := [set x in pcycles s | #|x| != 1 ].

Lemma in_psupportP s (X: {set T}) x:
  reflect (exists2 X, X \in psupport s & x \in X) (s x != x).
Proof.
  rewrite -in_support; apply (iffP idP) => [/setCP Hy | [Y]].
  - exists (pcycle s x); last by apply: pcycle_id.
    rewrite inE; apply /andP; split.
    + by rewrite /pcycles; apply /imsetP; exists x.
    + apply /negP; rewrite pcycleE => /eqP /card_orbit1 /orbit1P.
      by rewrite afix_cycle // inE.
  - rewrite inE => /andP [] /imsetP [y _ ->{Y}] Hcard.
    rewrite in_support -eq_pcycle_mem => /eqP Heq.
    move: Hcard; rewrite -Heq pcycleE; apply contra => /eqP.
    rewrite -apermE => /afix1P.
    rewrite -afix_cycle => /orbit1P ->.
    by rewrite cards1.
Qed.

Lemma partition_support s :
  partition (psupport s) (support s).
Proof.
  apply /and3P; split.
  - rewrite /cover; apply/eqP/setP => y.
    rewrite (_ : (y \in \bigcup_(B in psupport s) B) = (s y != y)).
    + by rewrite in_support.
    + by apply /bigcupP/in_psupportP => //; exact: support s.
  - apply /trivIsetP => A B.
    rewrite !inE => /andP [] /imsetP [] x1 _ -> _
                    /andP [] /imsetP [] x2 _ -> _ Hdiff.
    rewrite -setI_eq0; apply /set0Pn => [] [y].
    rewrite inE => /andP [].
    by rewrite -!eq_pcycle_mem => /eqP ->; apply /negP.
  - apply /negP; rewrite inE => /andP [] H _.
    move: H => /imsetP [] x _ Heq.
    have:= pcycle_id s x.
    by rewrite -Heq inE.
Qed.

Lemma psupport_astabs s X:
   X \in psupport s -> s \in ('N(X | 'P))%g.
Proof.
  rewrite /astabs => HX.
  rewrite inE; apply /andP; split; rewrite inE //.
  apply /subsetP => x /= Hx.
  move: HX; rewrite !inE apermE => /andP [] /imsetP [] x0 _ HX _.
  move: Hx; rewrite HX -!eq_pcycle_mem => /eqP <-.
  by have:= mem_pcycle s 1 x; rewrite -eq_pcycle_mem expg1.
Qed.


Definition is_cycle s := #|psupport s| == 1.
Definition cycle_dec s : {set {perm T}}
  := [set restr_perm X s | X in psupport s].

Lemma out_restr s (X: {set T}) x : x \notin X -> restr_perm X s x = x.
Proof. apply: out_perm; exact: restr_perm_on. Qed.

Lemma support_restr_perm s X:
  X \in psupport s -> support (restr_perm X s) = X.
Proof.
  move => HX.
  apply /setP => y; apply /idP/idP => [|Hin].
  - rewrite in_support.
    by apply contraR => /out_restr /eqP.
  - rewrite in_support restr_permE ?psupport_astabs // -?in_support.
    have <- := cover_partition (partition_support s).
    by apply /bigcupP; exists X.
Qed.

Lemma psupport_restr s X:
  X \in psupport s -> psupport (restr_perm X s) = [set X].
Proof.
  move => H; have:= H.
  rewrite inE => /andP [/imsetP [x _ Hx] HX].
  apply /setP => Y; rewrite [RHS]inE.
  apply /idP/idP.
  - move => HY.
    have HYX: Y \subset X.
      have <- := (support_restr_perm H).
      have <- := cover_partition(partition_support (restr_perm X s)).
      by apply (bigcup_max _ HY).
    rewrite eqEsubset; apply /andP; split => //.
    move: HYX => /subsetP => HYX.
    move: HY; rewrite inE => /andP [/imsetP[y _ Hy] HY].
    have Hiter (i:nat): ((restr_perm X s)^+i)%g y = (s^+i)%g y.
      elim: i => [|n Hn]; first by rewrite !expg0 !perm1.
      rewrite !expgSr !permM Hn restr_permE //; first exact: psupport_astabs.
      apply HYX; rewrite Hy -Hn -(pcycle_perm _ n); exact: pcycle_id.
    have Hrew: pcycle (restr_perm X s) y = pcycle s y.
      apply /setP => z; apply /pcycleP/pcycleP => [[] n| [] n].
      + by rewrite Hiter => ->; exists n.
      + by rewrite -Hiter => ->; exists n.
    rewrite {}Hrew {Hiter} in Hy.
    rewrite Hy Hx; apply /subsetP => z.
    have:= HYX y; rewrite Hy pcycle_id Hx.
    rewrite -!eq_pcycle_mem => Heq /eqP ->.
    rewrite eq_sym; exact: Heq.
 -  move => /eqP -> {Y}.
    rewrite inE HX andbT.
    apply /imsetP; exists x => //.
    rewrite Hx; apply /setP => y.
    have Hiter (i:nat) : ((restr_perm X s)^+i)%g x = (s^+i)%g x.
      elim: i => [|n Hn]; first by rewrite !expg0 !perm1.
      rewrite !expgSr !permM Hn restr_permE //; first exact: psupport_astabs.
      rewrite Hx -(pcycle_perm _ n); exact: pcycle_id.
    apply /pcycleP/pcycleP => [[n]|[n]].
    + by rewrite -Hiter Hx => H0; exists n.
    + by rewrite -Hx Hiter => H0; exists n.
Qed.

Lemma psupport_eq0 s :
  (s == perm_one T) = (psupport s == set0).
Proof.
  apply /idP/idP.
  - rewrite support_eq0 => /eqP Hsup.
    have:= partition_support s; rewrite {}Hsup.
    by move => /partition_of0 ->.
  - move => /eqP Hpsup.
    have:= partition_support s; rewrite {}Hpsup.
    rewrite /partition => /and3P [].
    by rewrite /cover big_set0 eq_sym -support_eq0.
Qed.



Lemma is_cycle_dec s : {in (cycle_dec s), forall C, is_cycle C}.
Proof.
  move => C /imsetP [X HX ->].
  by rewrite /is_cycle psupport_restr ?cards1.
Qed.

Definition support_cycles (s : {perm T}) :=
  [set support C | C in cycle_dec s].

Lemma support_cycle_dec s :
  support_cycles s = psupport s.
Proof.
  apply /setP => X.
  apply /imsetP/idP.
  - move => [x /imsetP[x0 Hx0 ->] ->].
    by rewrite support_restr_perm //.
  - rewrite inE => /andP [HX1 HX2].
    have HX: X \in psupport s by rewrite inE; apply /andP.
    exists (restr_perm X s); last by rewrite support_restr_perm.
    by apply /imsetP; exists X.
Qed.

Definition disjoint_supports (l: {set {perm T}}):=
  trivIset [set support C| C in l] /\ {in l &, injective support}.

Lemma disjoint_cycle_dec s:
  disjoint_supports (cycle_dec s).
Proof.
  split.
  - have:= partition_support s.
    rewrite -support_cycle_dec.
    by rewrite /partition => /and3P [].
  - move => C1 C2 /imsetP [c1 Hc1 ->] /imsetP [c2 HC2 ->].
    by rewrite !support_restr_perm // => ->.
Qed.


Lemma out_perm_prod (A: seq {perm T}) x:
  {in A, forall C, x \notin support C} -> (\prod_(C <- A) C)%g x = x.
Proof.
  elim: A => [_|a l Hl Hal]; first by rewrite big_nil perm1.
  rewrite big_cons permM.
  have:= (Hal a); rewrite mem_head in_support negbK => Ha.
  have:= (Ha isT) => /eqP ->.
  rewrite Hl // => C HC.
  by apply (Hal C); rewrite in_cons; apply /orP; right.
Qed.


Lemma out_of_disjoint y (A : {set {perm T}}) C l1 l2:
  disjoint_supports A->
  C \in A ->
  enum A = l1 ++ C :: l2 ->
  y \in support C ->
  {in l1++l2, forall C0, y \notin support C0}.
Proof.
  rewrite /disjoint_supports =>[] [Htriv Hinj] HC Hdecomp Hy C0.
  rewrite mem_cat => /orP HC0.
  have HC01 : C0 \in A.
    rewrite -mem_enum Hdecomp mem_cat; apply /orP.
    move: HC0 => []; first by left.
    by right; rewrite inE; apply/orP; right.
  move: Htriv => /trivIsetP Hdisj.
  have {Hdisj} := Hdisj (support C) (support C0).
  move=> /(_ (mem_imset _ HC) (mem_imset _ HC01)).
  have Hdiff: support C != support C0.
    apply /eqP => /Hinj /= /(_ HC HC01).
    have/= := enum_uniq (mem A).
    rewrite Hdecomp cat_uniq => /and3P [_ Hl1 Hl2] Heq.
    move: HC0 => [HC0l1 | HC0l2].
    - move: Hl1; apply /negP; rewrite negbK.
      apply /hasP; exists C0 => //.
      by rewrite -Heq; apply mem_head.
    - move: Hl2; rewrite cons_uniq andbC => /andP [_].
      by rewrite Heq HC0l2.
  move => /(_ Hdiff) /disjoint_setI0 /setP /(_ y).
  rewrite inE in_set0 => /nandP [] //.
  by move => /negbTE; rewrite Hy.
Qed.

Lemma prod_of_disjoint (A : {set {perm T}}) C0 x:
  C0 \in A ->
  disjoint_supports A -> x \in support C0 -> (\prod_(C in A) C)%g x = C0 x.
Proof.
  move => HC0; have:= HC0.
  rewrite -mem_enum => /in_seq [l1] [l2] Hdecomp Hdisj Hx.
  rewrite big_enum Hdecomp big_cat big_cons /=.
  rewrite permM out_perm_prod ?permM ?out_perm_prod => // C HC.
  - rewrite support_stable in Hx.
    apply: (out_of_disjoint Hdisj HC0 Hdecomp Hx).
    by rewrite mem_cat; apply /orP; right.
  - apply: (out_of_disjoint Hdisj HC0 Hdecomp Hx).
    by rewrite mem_cat; apply /orP; left.
Qed.

Lemma expg_prod_of_disjoint (A : {set {perm T}}) C0 x i:
  C0 \in A ->
  disjoint_supports A -> x \in support C0 ->
  ((\prod_(C in A) C)^+i)%g x = (C0^+i)%g x.
Proof.
  move => HC0 Hdisj Hx.
  have Hin j : (C0 ^+j)%g x \in support C0.
    elim j => [|k Hk]; first by rewrite expg0 perm1. 
    by rewrite expgSr permM -support_stable.
  elim: i => [|j Hj].
  - by rewrite !expg0 perm1.
  - by rewrite !expgSr !permM Hj (prod_of_disjoint HC0 Hdisj (Hin j)).
Qed.



Lemma cycle_decE s : (\prod_(C in cycle_dec s) C)%g = s.
Proof.
  apply /permP => x.
  case: (boolP (x \in support s)) => [|].
  - have:= partition_support s.
    rewrite /partition => /and3P [/eqP <- _ _].
    rewrite /cover => /bigcupP [c] => Hc.
    have:= Hc; rewrite -support_cycle_dec => /imsetP [C HC HcC] Hx; subst c.
    rewrite (prod_of_disjoint HC (disjoint_cycle_dec s) Hx).
    move: HC Hx => /imsetP [X0 HX0 ->].
    rewrite support_restr_perm // => Hx.
    by rewrite restr_permE //; by apply psupport_astabs.
  - rewrite in_support negbK big_enum => /eqP Heq.
    rewrite out_perm_prod // => C.
    rewrite mem_enum => /imsetP [X HX -> {C}].
    rewrite support_restr_perm //.
    apply /negP => Hx; move: Heq => /eqP.
    apply /negP/in_psupportP; first exact: support s.
  by exists X.
Qed.


Lemma disjoint_supports_of_decomp (A : {set {perm T}}) (B : {set {perm T}}):
  disjoint_supports A -> disjoint_supports B ->
    (\prod_(C in A) C)%g = (\prod_(C in B) C)%g ->
    {in A, forall c1, {in B, forall c2, support c1 = support c2 -> c1 = c2}}.
Proof.
  move => HdisjA HdisjB  /permP Heq c1 Hc1 c2 Hc2 /setP Hsupp.
  apply /permP => x.
  case (boolP (x \in support c1)) => H0;
  have := H0; rewrite {}Hsupp;  have := H0 => {H0}.
  - move => Hx1 Hx2; have := (Heq x) => {Heq}.
    by rewrite (prod_of_disjoint Hc1) ?(prod_of_disjoint Hc2).
  - by rewrite !in_support !negbK => /eqP -> /eqP ->.
Qed.


Lemma disjoint_supports_cycles (A: {set {perm T}}):
  {in A, forall C, is_cycle C} ->
    disjoint_supports A ->
    {in A, forall C, support C \in pcycles (\prod_(C in A) C)%g}.
Proof.
  move => Hcycle Hdisj C HC.
  have := (Hcycle C HC) => {Hcycle}.
  rewrite /is_cycle => /cards1P [X] Hpsupp.
  have := eqxx X; rewrite -in_set1 -Hpsupp inE => /andP.
  move => [/imsetP [x _] Hx]; subst X; rewrite pcycleE=> Hcard.
  have := cover_partition (partition_support C); rewrite Hpsupp.
  rewrite /cover big_set1 => <-; apply /imsetP; exists x => //.
  have Hx : x \in support C.                       
    rewrite in_support; apply /eqP; rewrite -apermE => /afix1P.
    rewrite -afix_cycle => /orbit1P => Hcontra.
    by move: Hcard; rewrite Hcontra cards1.
  apply /setP => y; apply /pcycleP/pcycleP;  
  move => [i] ->; exists i; apply /eqP; rewrite eq_sym; apply /eqP;
  by rewrite (expg_prod_of_disjoint i HC) //.                       
Qed.


Lemma disjoint_supports_pcycles (A: {set {perm T}}):
  {in A, forall C, is_cycle C} ->
    disjoint_supports A ->
    {in psupport (\prod_(C in A) C)%g, forall X, exists C, C \in A /\ support C = X}.
Proof.
  move => Hcycle Hdisj X. rewrite inE => /andP [/imsetP [x] _ -> {X} Hcard].
  case: (boolP (x \in (support (\prod_(C in A) C)%g))) => [Hin|].
  - have: exists2 C0, (C0 \in A) & (x \in support C0).
      apply /exists_inP.
      move: Hin; apply contraLR; rewrite negb_exists => /forallP Hnotin.
      rewrite in_support negbK big_enum; apply /eqP; apply out_perm_prod.
      move => C; rewrite mem_enum => HC.
      by have:= Hnotin C; rewrite HC andTb.
    move => [C0] [HC0 Hx].
    exists C0; split => //; move: Hx.
    have: support C0 \in (pcycles (\prod_(C in A) C)).
      exact: disjoint_supports_cycles.
    move => /imsetP [y] _ ->.
    by rewrite -eq_pcycle_mem => /eqP.
  - rewrite in_support negbK pcycleE -apermE => /eqP /afix1P.
    rewrite -afix_cycle => /orbit1P.
    rewrite -pcycleE => Hcontra; move: Hcard.
    by rewrite Hcontra cards1.
Qed.


Lemma uniqueness_cycle_dec (A : {set {perm T}}) s:
  {in A, forall C, is_cycle C} ->
    disjoint_supports A ->
    (\prod_(C in A) C)%g = s ->
    A = cycle_dec s.
Proof.
  move => Hcy Hdisj Hprod.
  apply /setP => C.
  apply /sameP/imsetP.
  apply (iffP idP).
  - move => HC; have := HC => /disjoint_supports_cycles.
    move => /(_ Hcy Hdisj) /imsetP [x _]; rewrite Hprod => Hsupp.
    have Hx: pcycle s x \in psupport s.
      rewrite inE; apply /andP; split.
      + by apply /imsetP; exists x.
      + by rewrite -Hsupp; rewrite card_support_noteq1.
    exists (pcycle s x) => //.
    have:= (disjoint_supports_of_decomp Hdisj (disjoint_cycle_dec s)).
    rewrite Hprod cycle_decE; have Heq : s=s by done.
    move => /(_ Heq C HC (restr_perm (pcycle s x) s)).
    apply; last by rewrite support_restr_perm.
    by apply /imsetP; exists (pcycle s x).
  - rewrite -{1}Hprod => [] [X HX1] ->.
    have := disjoint_supports_pcycles Hcy Hdisj HX1.
    move => [x] [] Hx; rewrite -{1}(support_restr_perm HX1).
    move => /(disjoint_supports_of_decomp Hdisj (disjoint_cycle_dec s)).
    rewrite Hprod cycle_decE; have Heq : s=s by done.
    move => /(_ Heq Hx) <- //.
    by apply /imsetP; exists X; rewrite -?Hprod.
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

End PermCycles.
  
Section Ordergeq.
  
Lemma geq_total : total geq.
Proof.
  admit.
Admitted.

Lemma geq_trans : transitive geq.
Proof.
  admit.
Admitted.

Lemma anti_geq : antisymmetric geq.
Proof.
  admit.
Admitted.
End Ordergeq.

Section cycle_type.
Variable T : finType.
Implicit Types (s t : {perm T}) (n : nat).

Definition cycle_type_seq (s : {perm T}) :=
  sort geq [seq #|(x: {set T})| |x <- enum (pcycles s)].

Definition card_support_cycles (s : {perm T}) :=
  [seq #|(C : {set T})| | C in (support_cycles s)].

Lemma cycle_type_dec (s : {perm T}) :
  let l := sort geq (card_support_cycles s) in
  cycle_type_seq (s : {perm T}) = l ++ (nseq (#|T| - sumn l) 1).
Proof.
  move => l. 
  admit.
Admitted.

Lemma support_cycle_type_seq s t :
  perm_eq (card_support_cycles s) (card_support_cycles t) ->
    cycle_type_seq s = cycle_type_seq t.
Proof. 
  move => /(perm_sortP geq_total geq_trans anti_geq).
  by rewrite !cycle_type_dec => ->.
Qed.

Lemma is_part_sortedP l:
  reflect (sorted (geq) l /\ {in l, forall x, x >= 1}) (is_part l).
Proof.
  admit.
Admitted.

Lemma cycle_type_part s:
  is_part (cycle_type_seq s).
Proof.
  apply /is_part_sortedP.
  split; first exact: (sort_sorted geq_total).
  move => n; rewrite mem_sort => /mapP [X].
  rewrite mem_enum => /imsetP [x] _ => -> -> {X}.
  case: posnP => // => /eqP; rewrite cards_eq0 => /eqP/setP /(_ x).
  by rewrite pcycle_id inE.
Qed.

Lemma big_sum_sumn (l: seq nat):
  \sum_(k <- l) k = sumn l.
Proof.
  rewrite /sumn.
  admit.
Admitted.

Lemma cycle_type_partn s:
  is_part_of_n #|T| (cycle_type_seq s).
Proof.
  apply /andP; split; last exact: cycle_type_part.
  rewrite cycle_type_dec sumn_cat sumn_nseq mul1n subnKC //.
  rewrite -big_sum_sumn.
  have /perm_eqlE Heq:= perm_sort geq (card_support_cycles s).
  rewrite (eq_big_perm _ Heq) /=.  
  rewrite big_map -big_enum.
  rewrite (support_cycle_dec s) -(card_partition (partition_support s)). 
  by apply: subset_leq_card; apply /subsetP => x.
Qed.

Definition cycle_type (s : {perm T}) := IntPartN (cycle_type_partn s).

Lemma congr_intpart (n : nat )(l1 l2 : seq nat) (H1 : is_part_of_n n l1) (H2 : is_part_of_n n l2):
  l1 = l2 -> IntPartN H1 = IntPartN H2.
Proof.
  admit.
Admitted.
  
Lemma support_cycle_type s t :
  perm_eq (card_support_cycles s) (card_support_cycles t) ->
    cycle_type s = cycle_type t.
Proof.
  move => Heq.
  apply congr_intpart; rewrite !cycle_type_dec.
  suff ->: sort (T:=nat_eqType) geq (card_support_cycles s) =  sort (T:=nat_eqType) geq (card_support_cycles t) => //.
  apply /perm_sortP => //.
  - exact: geq_total.
  - exact: geq_trans.
  - exact: anti_geq.
Qed.
  
Lemma pcycle_conjg s a x :
  pcycle ((s ^ a)%g) x = [set a y | y in pcycle s x].
Proof.
  rewrite !pcycleE; apply /setP => y.
  apply /idP/imsetP => [|[x0] Hx0 ->].
  admit.
  (*apply orbit_conjsg.*)
Admitted.

Lemma pcycles_conjg s a :
  pcycles (s ^ a)%g = [set [set a y | y in (X : {set T})] | X in pcycles s].
Proof.
  apply /setP => X0.
  apply /imsetP/imsetP => [[x _]|[x /imsetP [x0 _] ->] ->]. 
  - rewrite pcycle_conjg => ->.
    exists (pcycle s x) => //.
    by apply /imsetP; exists x.
  - exists x0 => //.
    by rewrite pcycle_conjg.
Qed.


Lemma cycle_type_of_conjg s t a:
  (s ^ a)%g = t -> cycle_type s = cycle_type t.
Proof.
  move => <-; apply congr_intpart.
  rewrite /cycle_type_seq.
  rewrite pcycles_conjg; apply /(perm_sortP geq_total geq_trans anti_geq).
  apply /perm_eqP => y.
  rewrite !count_map.
  admit.
Admitted.


Lemma conjg_of_cycle s a:
  is_cycle s -> is_cycle (s ^ a)%g.
Proof.
  move => /cards1P [X] HX.
  apply /cards1P; exists [set a x | x in X].
  apply /setP => y.
  rewrite !inE.
  apply /andP/eqP => [| -> ]; rewrite pcycles_conjg.
  - move => [][/imsetP [Y HY ->]].
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
  admit.
Admitted.

Lemma conjg_of_disjoint_supports (A : {set {perm T}}) a:
  disjoint_supports A -> disjoint_supports [set (s ^ a)%g | s in A].
Proof.
  move => [/trivIsetP Hdisj Hinj].
  split => [|x1 x2 /imsetP [s1 Hs1 ->] /imsetP [s2 Hs2 ->]].
  - apply /trivIsetP => B1 B2.
    move => /imsetP [x1 /imsetP [s1 Hs1 ->] ->].
    move => /imsetP [x2 /imsetP [s2 Hs2 ->] ->].
    rewrite !support_conjg => Hdiff.
    apply disjoint_imset; first by exact: perm_inj.
    apply: Hdisj.
    + by apply /imsetP; exists s1.
    + by apply /imsetP; exists s2.
    + by move: Hdiff; apply contra => /eqP ->.
  - rewrite !support_conjg => Hsupp.
    have -> //: s1 = s2; apply Hinj => //.
    apply /setP => x.
    apply /idP/idP.
    + move => Hx.
      have: a x \in [set a x | x in support s1] by apply /imsetP; exists x.
      rewrite Hsupp => /imsetP [y] Hy.
      by move => /perm_inj ->.
    + move => Hx.
      have: a x \in [set a x | x in support s2] by apply /imsetP; exists x.
      rewrite -Hsupp => /imsetP [y] Hy.
      by move => /perm_inj ->.
Qed. 

Lemma cycle_dec_of_conjg s a:
  [set (c ^ a)%g | c in cycle_dec s] = cycle_dec (s ^ a)%g.
Proof.
  apply: uniqueness_cycle_dec => [x /imsetP [x0 Hx0 ->]||].
  - apply: conjg_of_cycle; apply: (is_cycle_dec).
    exact: Hx0.
  - apply : conjg_of_disjoint_supports.
    exact: disjoint_cycle_dec.
  - (*rewrite big_imset. ??*)
    admit.
Admitted.

(* Ici il faut ayant supposé cycle_type s = cycle_type t, construire un
bijection entre pcycles s et pcycle t *)


Lemma bla s t :
  cycle_type s = cycle_type t ->
  exists f : {set T} -> {set T},
    {in pcycles s, injective f} /\ [set f x | x in pcycles s] = (pcycles t).
Proof.
Admitted.

Lemma classes_of_permP s t:
  reflect (t \in (s ^: [set: {perm T}])%g) (cycle_type s == cycle_type t).
Proof.
  admit.
Admitted.


(* Lemma cycle_type réalise une bijection de classes [set: {perm T}] sur enum_partn (#|T|) *)

(*
The action of the permutation (n, n+1, ... ,n+l-1) on (enum T)
*)

Definition cyclefun_of (n l : nat) : T -> T :=
  fun x =>
    let i := index x (enum T) in
    if n <= i < n+l-1 then (nth x (enum T) (i+1))
    else if i == n+l-1 then (nth x (enum T) n)
         else x.

Lemma injective_cyclefun_of n l:
  injective (cyclefun_of n l).
Proof.
  move => x1 x2.
  rewrite /cyclefun_of.
  case: (boolP (n <= index x1 (enum T) < n+l-1));
      case: (boolP (n <= index x2 (enum T) < n+l-1)).
  admit.
Admitted.

Definition cycle_of n l : {perm T} :=
  perm (@injective_cyclefun_of n l).

Lemma cycle_ofP n l : n + l <= #|T| -> is_cycle (cycle_of n l).
Proof.
  admit.
Admitted.

Fixpoint perm_of_part_rec (part : seq nat) (n : nat) : seq {perm T} :=
  match part with
  | [::] => [::]
  | a :: l1 =>
    if a == 1 then (perm_of_part_rec l1 n.+1)
    else (cycle_of n a) :: (perm_of_part_rec l1 (a + n))
  end.

Definition perm_of_part l : {perm T} :=
  \prod_(c <- perm_of_part_rec l 0) c.

Lemma blabla l : cycle_dec (perm_of_part l) = [set i in perm_of_part_rec l 0].
Proof.
  admit.
Admitted.

Lemma perm_of_partE (l : intpartn #|T|) : cycle_type (perm_of_part l) = l.
Proof.
  admit.
Admitted.

End cycle_type.
