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

Lemma support_eq0 s:
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
Proof. by apply /eqP; rewrite -support_eq0. Qed.

Definition psupport s := [set x in pcycles s | #|x| != 1 ].

Lemma in_psupportP s (X: {set T}) x:
  reflect  (exists2 X, X \in psupport s & x \in X) (s x != x).
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
    rewrite !inE => /andP [] /imsetP [] x1 _ -> _
                    /andP [] /imsetP [] x2 _ -> _ Hdiff.
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

Lemma psupport_eq0 s:
  (s == perm_one T) = (psupport s == set0).
Proof.
  admit.
Admitted.

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
    have Hiter (i:nat): ((restr_perm X s)^+i)%g x = (s^+i)%g x.
      elim: i => [|n Hn]; first by rewrite !expg0 !perm1.
      rewrite !expgSr !permM Hn restr_permE //; first exact: psupport_astabs.
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

Lemma support_inj s:
  {in cycle_dec s &, injective support}.
Proof.
  move => C1 C2 /imsetP [c1 Hc1 ->] /imsetP [c2 HC2 ->].
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


(*A peut être supprimer:
Pas moyen d'écrire simplement exists!
{in P, exists! ...}
*)

Lemma partitionP (P : {set {set T}}) (D : {set T}) :
  reflect
    (forall x, x \in D ->
       exists X, [/\ X \in P, x \in X &
                  forall Y, Y \in P -> (X != Y) -> x \notin Y])
    (partition P D).
Proof.
  admit.
Admitted.

(*
Lemma partitionP (P: {set {set T}}) (D:{set T}):
  [forall x in D, [exists X in P,
     (x \in X) && [forall Y in P, (X != Y) ==> (x \notin Y)]]] =
  (partition P D).
Proof.
  admit.
Admitted.
 *)

Lemma cycle_dec_eq0 s:
  (cycle_dec s == set0) = (s == perm_one T).
Proof.
  apply /idP/idP => [/eqP Heq| /eqP ->].
  - have:= support_cycle_dec s.
    rewrite Heq support_eq0.
  - Focus 2.
    rewrite /cycle_dec; apply /eqP/setP => x.
    rewrite inE; apply /imsetP.
Admitted.

Lemma cycle_dec_cons s a l:
  enum(cycle_dec s) = (a::l) -> enum(cycle_dec (a ^-1 * s)) = l.
Proof.
  move => Hs.
  

Admitted.


Lemma cycle_decE s:
  forall (l : seq {perm T}), enum (cycle_dec s) = l -> (\prod_(C <- l) C)%g = s.
Proof.
  move => l; move: s.
  elim: l => [s /enum_eq0P| a l Hl s /cycle_dec_cons Henum].
  - by rewrite cycle_dec_eq0 big_nil => /eqP ->.
  - apply /permP => x.
    rewrite big_cons permM.
    have -> := Hl (a^-1 * s)%g Henum.
    by rewrite -permM mulgA mulgV mul1g.
Qed.


Lemma cycle_decE s : (\prod_(C <- enum(cycle_dec s)) C)%g = s.
Proof.
  apply /permP => x.
  case: (boolP (x \in support s)) => [Hx |].
  - have /partitionP /(_ x) := partition_support s.
    rewrite -support_cycle_dec {}Hx.
    (*move => /(_ isT) [X] [/imsetP [C HC ->] Hx] Hnotin.*)
    move => /(_ isT) [X] [/imsetP [C]].
    rewrite -mem_enum => HC -> Hx Hnotin.
    have:= in_seq HC.
    move => [l1] [l2] Hdecomp; rewrite Hdecomp.
    rewrite big_cat /= big_cons /=.
    rewrite permM out_perm_prod ?permM ?out_perm_prod.
    + move: HC Hx => /imsetP [X0 HX0 ->]; rewrite support_restr_perm // => Hx.
      by rewrite restr_permE //; by apply psupport_astabs.
      (*Pour les 2 prochains sous-buts utiliser Hnotin*)
    + move => C0.
      admit.
    + move => C0 HC0.
      have HC01 : C0 \in (cycle_dec s).
        by rewrite -mem_enum Hdecomp mem_cat; apply /orP; left.
      have {Hnotin} := Hnotin (support C0).
      rewrite (_ : support C0 \in _ = true) /=; last by apply /imsetP; exists C0.
      move=> /implyP; apply.
      apply /negP => /eqP /(support_inj HC HC01) {HC01} Heq.
      move: HC0; rewrite -{}Heq => Hcontra.
      have := enum_uniq (mem (cycle_dec s)); rewrite Hdecomp.
      rewrite cat_uniq => /and3P [_ H _]; move: H.
      apply /negP; rewrite negbK.
      by apply /hasP; exists C => //; apply mem_head.
  - rewrite in_support negbK => /eqP Heq.
    rewrite out_perm_prod // => C.
    rewrite mem_enum => /imsetP [X HX -> {C}].
    rewrite support_restr_perm //.
    apply /negP => Hx; move: Heq => /eqP.
    apply /negP/in_psupportP; first exact: support s.
  by exists X.
Admitted.


(* TODO: Florent : try to remove the enum here *)
(*
Lemma cycle_decE s : (\prod_(C <- enum(cycle_dec s)) C)%g = s.
Proof.
  apply /permP => x.
  case: (boolP (x \in support s)) => [Hx |].
  - have /partitionP /forallP /(_ x) := partition_support s.
    rewrite -support_cycle_dec {}Hx /=.
    move => /existsP [X] /and3P [/imsetP [C HC ->] Hx].
    move => /forallP Hnotin.
    (* Faire un lemme a part a contribuer *)
    have: exists l1 l2, enum (cycle_dec s) = l1 ++ (C :: l2).
      move: HC; rewrite -mem_enum.
      elim: (enum (cycle_dec s)) => [|a l Hl]; first by rewrite in_nil.
      rewrite in_cons => /orP [/eqP ->| /Hl]; first by exists [::]; exists l.
      move => {Hl} [l1] [l2] ->.
      by exists (a :: l1); exists l2.
    move=> [l1] [l2] Hdecomp; rewrite Hdecomp.
    rewrite big_cat /= big_cons /=.
    rewrite permM out_perm_prod ?permM ?out_perm_prod.


    + move: HC Hx => /imsetP [X0 HX0 ->]; rewrite support_restr_perm // => Hx.
      by rewrite restr_permE //; by apply psupport_astabs.
      (*Pour les 2 prochains sous-buts utiliser Hnotin*)
    + move => C0.
      admit.
    + move => C0 HC0.
      have HC01 : C0 \in (cycle_dec s).
        by rewrite -mem_enum Hdecomp mem_cat; apply /orP; left.
      have {Hnotin} := Hnotin (support C0).
      rewrite (_ : support C0 \in _ = true) /=; last by apply /imsetP; exists C0.
      move=> /implyP; apply.
      apply /negP => /eqP /(support_inj HC HC01) {HC01} Heq.
      move: HC0; rewrite -{}Heq => Hcontra.
      have := enum_uniq (mem (cycle_dec s)); rewrite Hdecomp.
      rewrite cat_uniq => /and3P [_ H _]; move: H.
      apply /negP; rewrite negbK.
      by apply /hasP; exists C => //; apply mem_head.
  - rewrite in_support negbK => /eqP Heq.
    rewrite out_perm_prod // => C.
    rewrite mem_enum => /imsetP [X HX -> {C}].
    rewrite support_restr_perm //.
    apply /negP => Hx; move: Heq => /eqP.
    apply /negP/in_psupportP; first exact: support s.
  by exists X.
Admitted.
*)

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

Definition cycle_type (s:{perm T}):=
  sort (geq) [seq #|(x: {set T})| |x <- enum(pcycles s)].
