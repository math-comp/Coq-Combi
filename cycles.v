Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial fingroup perm automorphism action.

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

Lemma partition_support s :
  partition (psupport s) (support s).
Proof.
  apply /and3P; split.
  - rewrite /cover.
    apply /eqP /setP => y; apply /bigcupP.
    case: (boolP (y \in support s)) => [/setCP Hy|].
    + exists (pcycle s y); last by apply: pcycle_id.
      rewrite inE; apply /andP; split; first by rewrite /pcycles; apply /imsetP; exists y.
      apply /negP; rewrite pcycleE => /eqP /card_orbit1 /orbit1P.
      by rewrite afix_cycle //; rewrite inE.
    + rewrite inE negbK -afix_cycle => /orbit1P Hy [] X.
      rewrite inE => /andP [] /imsetP [] z _ -> Hz.
      rewrite -eq_pcycle_mem => /eqP Heq.
      by move: Hz; rewrite -Heq pcycleE Hy cards1.
  - apply /trivIsetP => A B.
    rewrite !inE => /andP [] /imsetP [] x1 _ -> _ /andP [] /imsetP [] x2 _ -> _ Hdiff.
    rewrite -setI_eq0.
    apply /set0Pn => Hy; destruct Hy as (y,Hy).
    move: Hy; rewrite inE => /andP [].
    by rewrite -!eq_pcycle_mem => /eqP ->; apply /negP.
  - apply /negP; rewrite inE.
    move => /andP [] H _.
    move: H => /imsetP [] x _ Heq.
    have:= (pcycle_id s x).
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

Lemma in_psupportP s (X: {set T}) x:
  reflect  (exists2 i, i \in psupport s & x \in i) (s x != x).
Proof.
  rewrite -in_support.
  have:= cover_partition (partition_support s); rewrite /cover => Heq.
  apply (iffP idP).
  - by rewrite -Heq => /bigcupP.
  - by move => /bigcupP; rewrite Heq.
Qed.

Definition is_cycle s :=
  #|psupport s| == 1.

Definition pickcycle s :=
  odflt set0 [pick X in psupport s].

Definition cycle_of s : {perm T} :=
  let C := pickcycle s in restr_perm C s.

Lemma perm_on_cycle_of s: perm_on (pickcycle s) (cycle_of s).
Proof. by exact: restr_perm_on. Qed.

Lemma out_cycle_of s x : x \notin (pickcycle s) -> cycle_of s x = x.
Proof. apply: out_perm; exact: perm_on_cycle_of. Qed.

Lemma in_cycle_of s x : x \in (pickcycle s) -> cycle_of s x = s x.
Proof.
  apply: restr_permE; rewrite /pickcycle.
  case: pickP => [X|_] /=.
  - by apply: psupport_astabs.
  - by rewrite /astabs !inE; apply /andP; split => //; apply: sub0set.
Qed.

Lemma cycle_of_comp s x:
  cycle_of s x = (if x \in pickcycle s then s x else x).
Proof. by case: (boolP (x \in _)) => H; [rewrite in_cycle_of|rewrite out_cycle_of]. Qed.

Lemma support_cycle_of s:
  support (cycle_of s) = pickcycle s.
Proof.
  apply /setP => x; rewrite in_support cycle_of_comp /pickcycle.
  case: (boolP (x \in _)); last by rewrite eqxx.
  case: pickP => [/= X H1 H2|/=]; last by rewrite in_set0.
  by apply /in_psupportP => //; exists X.
Qed.

Lemma pickcycle_stab s x n:
  x \in pickcycle s -> (s^+n)%g x \in pickcycle s.
Proof.
  rewrite /pickcycle. 
  case: pickP => [X /=|_ /=]; last by rewrite inE.
  rewrite inE => /andP [] /imsetP [] y _ -> _.
  rewrite -!eq_pcycle_mem => /eqP <-.
  by rewrite pcycle_perm.
Qed.
  
Lemma pcycle_cycle_of s x :
  x \in pickcycle s -> pcycle (cycle_of s) x = pcycle s x.
Proof.
  rewrite -setP => H y.
  apply /pcycleP/pcycleP.
  - move => [] n H0; exists n; rewrite {}H0; move: n; elim => [|n Hn].
    + by rewrite expg0 perm1.
    + rewrite !expgSr !permM Hn in_cycle_of //.
      by apply: pickcycle_stab.
  - move => [] n H0; exists n; rewrite {}H0; move: n; elim => [|n Hn].
    + by rewrite expg0 perm1.
    + rewrite !expgSr !permM -Hn in_cycle_of //.
      by apply: pickcycle_stab.
Qed.

Lemma psupport_cycle_of s:
  support (cycle_of s) != set0 -> psupport (cycle_of s) = [set (support (cycle_of s))]. 
Proof.
  rewrite support_cycle_of => H0.
  rewrite /psupport; apply /setP => X.
  rewrite !inE.
  apply /andP/idP.
  - move => [] /imsetP [] x0 _ -> HX.
    apply /eqP.
    case: (boolP (x0 \in pickcycle s)) => [Hx0|/out_cycle_of Hx0].
    + rewrite pcycle_cycle_of //.
      move: H0 Hx0; rewrite  /pickcycle.  
      case: pickP => [Y/=| /=]; last by rewrite eqxx.
      rewrite inE => /andP [] /imsetP [] y0 _ -> _ _.
      by rewrite -eq_pcycle_mem => /eqP.
    + exfalso.
      move: HX; rewrite pcycleE; apply /negP; rewrite negbK.
      apply /cards1P; exists x0; apply /orbit1P.
      by rewrite afix_cycle; apply /afix1P => /=.
  - move => /eqP ->; move: H0; rewrite /cycle_of /pickcycle.      
    case pickP => [Y| ]/=; last by rewrite eqxx.
    rewrite inE => /andP [] => H ->.
    case: (set_0Vmem Y); first by move => ->; rewrite eqxx.
    move => [] x Hx _; split => //.
    apply /imsetP; exists x => //.
    
Qed.


Lemma cycle_ofE s :
  is_cycle s -> cycle_of s = s.
Proof.
  rewrite /is_cycle => /cards1P [] X H.
  apply /permP => x.
  case: (boolP (x \in odflt set0 [pick X0 in psupport s])).
  - apply: restr_permE => //.
    case: pickP =>[x0|_]; first by apply psupport_astabs.
    rewrite /astabs inE; apply /andP; split => //.
    by rewrite inE /=; apply sub0set.
  - move => Hx; rewrite out_cycle_of => //.
    move: Hx; rewrite H.
    case: pickP => [X0|Habs]; last by move: (Habs X); rewrite inE eqxx.
    rewrite inE => /eqP -> /= Hx.
    rewrite -apermE; apply /eqP; rewrite eq_sym. apply/eqP /afix1P.
    rewrite -afix_cycle; apply /orbit1P.
    rewrite -pcycleE.
    case (boolP (pcycle s x \in psupport s)).
    + rewrite H inE => /eqP Hc; exfalso.
      by have:= pcycle_id s x; rewrite Hc; apply /negP.
    + rewrite inE => /nandP.
      case => [/imsetP []|]; first by exists x.
      rewrite negbK pcycleE => /eqP.                                           
      exact: card_orbit1.      
Qed.

Lemma is_cycleP s :
  (cycle_of s == s) = ((is_cycle s)||(s == perm_one T)).
Proof.
  apply /idP/idP => [|/orP [H|/eqP ->]].
  - rewrite /is_cycle.
    move => /eqP Heq; have:= perm_on_cycle_of s; rewrite Heq.
    case: pickP => [X|_ H0] /=.
    + rewrite support_perm_on => H1 H2.
      have: psupport s = [set X].
        by apply: (triv_part (partition_support s)).
      by move => ->; rewrite cards1.
    + apply /orP; right; apply /eqP.
      rewrite -permP => x; rewrite perm1.
      by apply (out_perm H0); rewrite inE.
  - apply /eqP.
    exact: cycle_ofE.
  - apply /eqP; rewrite -permP => x; rewrite perm1.
    apply: out_cycle_of.
    have ->: (psupport (perm_one T)) = set0.
      apply partition_of0.
      by have:= partition_support (perm_one T); rewrite support1.
    case: pickP=> [X|_ /=]; by rewrite inE.
Qed.

Lemma cycle_ofP s: s != 1%g -> is_cycle (cycle_of s).
Proof.
  rewrite triv_supportP => /negP.
  case: (set_0Vmem (support s)) => [/eqP //|[] x Hx _].  
  have: cycle_of (cycle_of s) = cycle_of s.
  rewrite -permP => y.
  rewrite !cycle_of_comp.
  



  
  (*
  rewrite triv_supportP => /negP.
  case: (set_0Vmem (support s)) => [/eqP //|[] x Hx _].  
  have []: exists Y, [pick X in psupport s] = some Y /\ Y \in psupport s.
    case: pickP => [Z HZ|/=]; first by exists Z.
    move: Hx.                                       
    case: (set_0Vmem (psupport s)) => [H|[] X0 HX0 _ H]; last by have:= H X0 => /negbT /negP.
    have:= partition_support s; rewrite H => /cover_partition <-.
    by move => /bigcupP [] x0; rewrite inE.
  move => X0 [] HX0 HX00.
  rewrite /is_cycle; apply /cards1P; exists X0.
  have Hsup : support (cycle_of s) = X0.
    apply /setP /subset_eqP /andP; split.
    + rewrite -support_perm_on. 
      by have:= perm_on_cycle_of s; rewrite HX0 /=. 
    + apply /subsetP => y Hy.
      rewrite inE; apply /afix1P => /=; rewrite apermE.
      rewrite /cycle_of HX0 /= restr_permE; [|apply psupport_astabs|] => //.
      have: y \in (cover (psupport s)).
        apply /bigcupP.
        exists X0 => //.
      by rewrite (cover_partition (partition_support s)); rewrite inE => /afix1P.
  move: HX00; rewrite inE => /andP [] /imsetP [] x0 _ HX1 HX2.
  have: X0 \in psupport (cycle_of s).
    rewrite inE; apply /andP; split => //.
    apply /imsetP; exists x0 => //.*)
Admitted.

Lemma supp_decr s:
  s != 1%g -> #|support ((cycle_of s)^-1 * s)| < #|support s|.
Proof.

Admitted.

Lemma perm_cycle_ofK s :
  (support (s * (cycle_of s)^-1)) = (support s :\: support (cycle_of s)^-1).
Proof.
  apply /setP => x. 
  rewrite !in_support inE !in_support permM.
  apply /idP/idP.
  - apply /contraR => /nandP []; rewrite negbK.
    + Focus 2. 
      move => /eqP Hs.
      rewrite Hs.
      have: (cycle_of s) x = x.
      apply out_cycle_of. 
      case pickP => X /=; last by rewrite inE.
      move: Hs => /eqP /in_psupportP Hs.
      have:= Hs set0; clear Hs => Hs.
      
      
  - apply /andP; split.
    + rewrite negbK.



Admitted.

Lemma support_disjointC s t :
  [disjoint support s & support t] -> (s * t = t * s)%g.
Proof.
Admitted.
