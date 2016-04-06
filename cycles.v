Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial fingroup perm automorphism action.

From Combi Require Import symgroup partition Greene.

Set Implicit Arguments.
Unset Strict Implicit.

Section PermCycles.
Variable T: finType.
Implicit Type (s: {perm T}).

Definition support s :=
  ~:'Fix_('P)([set s])%g.

Lemma support_perm_on S s:
  (perm_on S s) = (support s \subset S).
Proof.
  apply /idP/idP.
  rewrite /perm_on => /subsetP H.
  apply /subsetP => x.
  rewrite inE => /afixP /=.
Admitted.
 
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

Definition is_cycle s :=
  #|psupport s| == 1.

Definition cycle_of s : {perm T} :=
  let C := odflt set0 [pick X in psupport s]
  in restr_perm C s.

Lemma perm_on_cycle_of s: perm_on (odflt set0 [pick X in psupport s]) (cycle_of s).
Proof. by exact: restr_perm_on. Qed.

Lemma out_cycle_of s x : x \notin (odflt set0 [pick X in psupport s]) -> cycle_of s x = x.
Proof. apply: out_perm; exact: perm_on_cycle_of. Qed.

Lemma cycle_ofE s :
  is_cycle s -> cycle_of s = s.
Proof.
  rewrite /is_cycle => /cards1P [] X H.
  apply /permP => x.
  case: (boolP (x \in odflt set0 [pick X0 in psupport s])).
  - apply: restr_permE => //.
    rewrite /astabs inE; apply /andP.
    split => //.
    rewrite inE.
    case: pickP => /=; last by move => _; apply: sub0set.
    move => x0; rewrite inE => /andP [] /imsetP [] z _ -> _.
    apply /subsetP => y; rewrite inE apermE -!eq_pcycle_mem.
    move => /eqP <-.
    by have:= mem_pcycle s 1 y; rewrite -eq_pcycle_mem expg1 eq_sym.
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
  reflect (cycle_of s = s) (is_cycle s).
Proof.
  apply (iffP idP); first by apply cycle_ofE.
  rewrite /is_cycle.
  move => Heq; have:= perm_on_cycle_of s; rewrite Heq.
  case: pickP => [X| ] /=.

  move => /permP.
Admitted.

Lemma cycle_ofP s: s != 1%g -> is_cycle (cycle_of s).
Proof.
  move => Hid; apply /is_cycleP.
  apply /permP => x.
  rewrite permE /cyclefun_of.

Admitted.

Lemma supp_decr s x :
  s != 1%g -> #|support ((cycle_of s)^-1 * s)| < #|support s|.
Proof.
Admitted.

Lemma perm_cycle_ofK s :
  (support (s * cycle_of s)^-1) = (support s :\: support (cycle_of s)^-1).
Proof.
Admitted.

Lemma support_disjointC s t :
  [disjoint support s & support t] -> (s * t = t * s)%g.
Proof.
Admitted.


(*
Definition cyclefun_of s: T->T :=
  let C := odflt set0 [pick X in (pcycles s) | #|X| != 1] in
  [fun x => if x \in C then s x else x].
  
Lemma pcycle_stab (s:{perm T}) (C:{set T}) (x: T):
  (C \in pcycles s) -> (x \in C) = ((s x) \in C).
Proof.
  move => /imsetP [] y _ ->.
  rewrite -!eq_pcycle_mem.
  by apply /idP/idP => /eqP <-;
  have:= mem_pcycle s 1 x; rewrite -eq_pcycle_mem expg1 // eq_sym.
Qed.

  
Lemma cyclefun_ofP s: injective (cyclefun_of s).
Proof.
  move => x1 x2.
  rewrite /cyclefun_of.
  case: pickP => /=; last by move => _; rewrite !inE.
  move => X /andP [] Hc _.
  case: (boolP (x1 \in X)) => Hx1; case: (boolP (x2 \in X)) => Hx2.
  - by apply perm_inj.
  - by move => Heq; move: Hx2 Hx1; rewrite (pcycle_stab x1 Hc) Heq => /negP.
  - by move => Heq; move: Hx1 Hx2; rewrite (pcycle_stab x2 Hc) Heq => /negP.
  - done.  
Qed.

Definition cycle_of s : {perm T} :=
  perm (@cyclefun_ofP s).

Lemma cycle_ofE s :
  is_cycle s -> cycle_of s = s.
Proof.
  rewrite /is_cycle => /cards1P [] X H.
  apply /permP => x.
  rewrite permE /cyclefun_of /=.
  case: pickP => /=.
  - move => X0 HX.
    have: X0 \in [set x in pcycles s | #|x| != 1].
      by rewrite inE.
    rewrite H inE => /eqP HX0.
    move: HX; rewrite HX0 => /andP [] HX _.
    case: (boolP (x \in X)) => // Hx.
    case: (boolP (#|pcycle s x| == 1)).
    + move => /eqP /card_orbit1 /orbit1P /afixP H0.
      have := H0 s; rewrite cycle_id /= /aperm => Hfin.
      by apply /eqP; rewrite eq_sym; apply /eqP; apply Hfin. 
    + have: pcycle s x \in pcycles s.
        by rewrite /pcycles; apply /imsetP; exists x.
      move => H1 H2. 
      have: pcycle s x \in [set x in pcycles s | #|x| != 1].
        by rewrite inE; apply /andP.
      rewrite H inE => /eqP Heq.
      exfalso.
      move: Hx; rewrite -Heq; apply /negP; rewrite negbK.
      exact: pcycle_id.
  - move => Hfun.
    have Hcontra := Hfun X.
    have: X \in [set X] by rewrite inE.
    by rewrite -H inE Hcontra.
Qed.

Lemma is_cycleP s :
  reflect (cycle_of s = s) (is_cycle s).
Proof.
  apply (iffP idP); first by apply cycle_ofE.
  rewrite /is_cycle.
  move => /permP.
Admitted.

Lemma cycle_ofP s: s != 1%g -> is_cycle (cycle_of s).
Proof.
  move => Hid; apply /is_cycleP.
  apply /permP => x.
  rewrite permE /cyclefun_of.

Admitted.

Lemma supp_decr s x :
  s != 1%g -> #|support ((cycle_of s)^-1 * s)| < #|support s|.
Proof.
Admitted.

Lemma perm_cycle_ofK s :
  (support (s * cycle_of s)^-1) = (support s :\: support (cycle_of s)^-1).
Proof.
Admitted.

Lemma support_disjointC s t :
  [disjoint support s & support t] -> (s * t = t * s)%g.
Proof.
Admitted.

End PermCycles.
*)

Definition support s :=
  [set: T] :\: 'Fix_('P)([set s])%g.

Definition is_cycle s :=
  #|[set x in pcycles s | #|x| != 1 ]| == 1.



