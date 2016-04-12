Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial.
From mathcomp Require Import fingroup perm automorphism action.

From Combi Require Import symgroup partition Greene.

Set Implicit Arguments.
Unset Strict Implicit.

Section SSRComplements.
Variable T: finType.
  
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

End SSRComplements.
  

Section PermCycles.
Variable T: finType.
Implicit Type (s: {perm T}).

Definition support s :=
  ~:'Fix_('P)([set s])%g.

Lemma in_support s x:
  (x \in support s) = (s x != x).
Proof.
  apply /idP/idP => [| /eqP H]; rewrite inE.
  - by move => /afix1P /= /eqP.
  - by apply /afix1P => /=; rewrite apermE.  
Qed.

Lemma support_perm_on S s:
  (perm_on S s) = (support s \subset S).
Proof.
  apply /idP/idP.
  - rewrite /perm_on => /subsetP H.
    apply /subsetP => x.
    rewrite in_support.
    exact: H.
  - rewrite /perm_on => /subsetP H.
    apply /subsetP => x; rewrite inE.
    rewrite -in_support.
    exact: H.
Qed.

Lemma triv_supportP s:
  (s == perm_one T) = (support s == set0).
Proof.
  apply /idP/idP => [/eqP -> |/eqP ].
  - apply /eqP; case: (set_0Vmem (support (perm_one T))) => [//|[] x]. 
    rewrite inE => /afix1P /=; rewrite apermE.
    by rewrite perm1.
  - rewrite -setCT => /setC_inj /= H.
    apply /eqP; rewrite -permP => x.
    by rewrite perm1 -apermE; apply /afix1P; rewrite H.    
Qed.

Lemma support1 :
  (support (perm_one T)) = set0.
Proof. by apply /eqP; rewrite -triv_supportP. Qed.

Definition psupport s := [set x in pcycles s | #|x| != 1 ].

Lemma in_psupportP s (X: {set T}) x:
  reflect  (exists2 i, i \in psupport s & x \in i) (s x != x).
Proof.
  rewrite -in_support.
  apply (iffP idP).
  - move=> /setCP Hy.
    exists (pcycle s x); last by apply: pcycle_id.
    rewrite inE; apply /andP; split.
    + by rewrite /pcycles; apply /imsetP; exists x.
    + apply /negP; rewrite pcycleE => /eqP /card_orbit1 /orbit1P.
      by rewrite afix_cycle //; rewrite inE.
  - move=> [Y]; rewrite inE => /andP [] /imsetP [y _ ->{Y}] Hcard.
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
  - rewrite /cover.
    apply /eqP /setP => y.
    have -> : (y \in \bigcup_(B in psupport s) B) = (s y != y).
    + by apply /bigcupP/in_psupportP => //; exact: support s.
    + by rewrite in_support.
  - apply /trivIsetP => A B.
    rewrite !inE => /andP [] /imsetP [] x1 _ -> _ /andP [] /imsetP [] x2 _ -> _ Hdiff.
    rewrite -setI_eq0; apply /set0Pn => [] [y].
    rewrite inE => /andP [].
    by rewrite -!eq_pcycle_mem => /eqP ->; apply /negP.
  - apply /negP; rewrite inE.
    move => /andP [] H _.
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

Definition is_cycle s :=
  #|psupport s| == 1.

Definition cycle_dec s := [set restr_perm X s | X in psupport s].

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
      rewrite !expgSr !permM Hn restr_permE //.
      exact: psupport_astabs.
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
    have Hiter (i:nat): ((restr_perm X s)^+i)%g x = (s^+i)%g x.
      elim: i => [|n Hn]; first by rewrite !expg0 !perm1.
      rewrite !expgSr !permM Hn restr_permE //.
      exact: psupport_astabs.
      rewrite Hx -(pcycle_perm _ n); exact: pcycle_id.
    apply /pcycleP/pcycleP => [[n]|[n]].
    + by rewrite -Hiter Hx => H0; exists n. 
    + by rewrite -Hx Hiter => H0; exists n.
Qed.
  
Lemma is_cycle_dec s : {in (cycle_dec s), forall C, is_cycle C}.
Proof.
  move => C /imsetP [X HX ->].
  by rewrite /is_cycle psupport_restr ?cards1.
Qed.

Lemma disjoint_cycle_dec s :
  trivIset [set support C| C in cycle_dec s].
Proof.
  apply /trivIsetP => A B /imsetP [a /imsetP [X HX ->] ->].
  move => /imsetP [b /imsetP [Y HY ->] ->].
  rewrite !support_restr_perm //.
  have:= partition_support s.
  rewrite /partition => /and3P [_ /trivIsetP H _]. 
  exact: H.
Qed.

Lemma cycle_decE s : (\prod_(C in cycle_dec s) C)%g = s.
Proof.
  apply /permP => x.
  case: (boolP (x \in support s)).
Admitted.

Lemma uniqueness_cycle_dec A s:
  {in A, forall C, is_cycle C} ->
    trivIset [set support C| C in A] ->
    (\prod_(C in A) C)%g = s ->
    A = cycle_dec s.
Proof.
Admitted.

Lemma support_disjointC s t :
  [disjoint support s & support t] -> (s * t = t * s)%g.
Proof.
Admitted.

