Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial.
From mathcomp Require Import fingroup perm automorphism action.

From Combi Require Import symgroup partition Greene.

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

Lemma support_cycle_dec s :
  [set support C| C in cycle_dec s] = psupport s.
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

  (*
Lemma disjoint_cycle_dec s :
  trivIset [set support C| C in cycle_dec s].
Proof.
  have:= partition_support s.
  rewrite -support_cycle_dec.
  by rewrite /partition => /and3P [].
Qed.

Lemma support_inj s:
  {in cycle_dec s &, injective support}.
Proof.
  move => C1 C2 /imsetP [c1 Hc1 ->] /imsetP [c2 HC2 ->].
  by rewrite !support_restr_perm // => ->.
Qed.
 *)

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

Lemma out_of_cycle y s C l1 l2:
  C \in cycle_dec s ->
  enum (cycle_dec s) = l1 ++ C :: l2 ->
  y \in support C ->
  {in l1++l2, forall C0, y \notin support C0}.
Proof.
  move=> /out_of_disjoint; apply.
  exact: disjoint_cycle_dec.
Qed.

Lemma cycle_decE s : (\prod_(C in cycle_dec s) C)%g = s.
Proof.
  rewrite big_enum; apply /permP => x.
  case: (boolP (x \in support s)) => [|].
  - have:= partition_support s.
    rewrite /partition => /and3P [/eqP <- _ _].
    rewrite /cover => /bigcupP [c] => Hc.
    have:= Hc; rewrite -support_cycle_dec => /imsetP [C HC HcC] Hx; subst c.
    have:= HC; rewrite -mem_enum => /in_seq.
    move => [l1] [l2] Hdecomp; rewrite Hdecomp.
    rewrite big_cat /= big_cons /=.
    rewrite permM out_perm_prod ?permM ?out_perm_prod.
    + move: HC Hx => /imsetP [X0 HX0 ->].
      rewrite support_restr_perm // => Hx.
      by rewrite restr_permE //; by apply psupport_astabs.
    + move => C0 HC0.
      rewrite support_stable in Hx.
      have:= (out_of_cycle HC Hdecomp Hx) => /(_ C0).
      by rewrite mem_cat HC0 orbT => /(_ isT).
    + move => C0 HC0.
      have:= (out_of_cycle HC Hdecomp Hx) => /(_ C0).
      by rewrite mem_cat HC0 orTb => /(_ isT).
  - rewrite in_support negbK => /eqP Heq.
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
  admit.
Admitted.

Lemma disjoint_supports_cycles (A: {set {perm T}}):
  {in A, forall C, is_cycle C} ->
    disjoint_supports A ->
    {in A, forall C, support C \in pcycles (\prod_(C in A) C)%g}.
Proof.
  admit.
Admitted.

Lemma disjoint_supports_pcycles (A: {set {perm T}}) s:
  {in A, forall C, is_cycle C} ->
    disjoint_supports A ->
    (\prod_(C in A) C)%g = s ->
    {in pcycles s, forall X, exists C, C \in A /\ support C = X}.
Proof.
  admit.
Admitted.


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
  - move => [X HX1]; have:= HX1;  rewrite inE =>/andP [HX2 _] ->.
    have := disjoint_supports_pcycles Hcy Hdisj Hprod HX2.
    move => [x] [] Hx; rewrite -{1}(support_restr_perm HX1).
    move => /(disjoint_supports_of_decomp Hdisj (disjoint_cycle_dec s)).
    rewrite Hprod cycle_decE; have Heq : s=s by done.
    move => /(_ Heq Hx) <- //.
    by apply /imsetP; exists X.
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

Section cycle_type.
Variable T : finType.
Implicit Types (s t : {perm T}) (n : nat).  
  
Definition cycle_type (s:{perm T}):=
  sort geq [seq #|(x: {set T})| |x <- enum (pcycles s)].

Lemma cycle_type_part s:
  is_part (cycle_type s).
Proof.
  apply /is_partP.
  case (boolP(#|T| == 0)) => [/eqP/card0_eq HT|HT].
  - rewrite (_: cycle_type s = [::]) // /cycle_type /pcycles.
    rewrite (_ :[set pcycle s x | x : T] = set0) ?enum_set0 /= //.
    apply /setP => X; rewrite inE.
    by apply /imsetP => [] [] x; rewrite HT inE.    
  - admit.
Admitted.

Lemma cycle_type_of_conjugate s t:
  (exists a, (s ^ a)%g = t) -> cycle_type s = cycle_type t.
Proof.
  rewrite /conjg => [][a] <-.
  rewrite /cycle_type; congr (sort).
  rewrite (_: pcycles s = pcycles (a^-1 * (s * a))) //.
  apply /setP => C.
Admitted.

Lemma classes_of_permP s t:
  reflect (t \in (s ^: [set: {perm T}])%g) (cycle_type s == cycle_type t).
Proof.
  admit.
Admitted.


(* Lemma cycle_type réalise une bijection de classes [set: {perm T}] sur enum_partn (#|T|) *)

(*
The action of the permutation (n, n+1, ... ,n+l) on (enum T) 
*)

Definition cyclefun_of n l: T -> T:=
  if l == 1
  then (fun x => x)
  else (fun x => match (index x (enum T)) with
                 |i => if n <= i < n+l-1 then (nth x (enum T) (i+1))
                            else if i == n+l-1 then (nth x (enum T) n)
                                 else x
                 end).

Lemma injective_cyclefun_of n l:
  injective(cyclefun_of n l).
Proof.
  admit.
Admitted.

Definition cycle_of n l :{perm T} :=
  perm (@injective_cyclefun_of n l).
                
Fixpoint perm_of_part_rec l n: {perm T}:=
  match l with
  |[::] => perm_one T
  |a::l1 => (cycle_of (a + n) a) * (perm_of_part_rec l1 n.+1)
  end.

Definition perm_of_part l: {perm T}:=
  perm_of_part_rec l 0.

Lemma perm_of_partE l:
  is_part_of_n (#|T|) l -> cycle_type (perm_of_part l) = l.
Proof.
  admit.
Admitted.


End cycle_type.
