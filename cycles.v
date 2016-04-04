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
  [set: T] :\: 'Fix_('P)([set s])%g.

Definition is_cycle s :=
  #|[set x in pcycles s | #|x| != 1 ]| == 1.

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
Admitted.

Lemma cycle_ofP s: s != 1%g -> is_cycle (cycle_of s).
Proof.
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
