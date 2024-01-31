(** * Combi.Combi.setpartition : Set Partitions *)
(******************************************************************************)
(*      Copyright (C) 2014-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * Set Partitions and refinment lattice

In what follows [T] is a [finType] and [S : {set T}].

- [setpart S]     == a sigma type for partition of [S]. [setpart S] bears a
                     canonical structure of an inhabited finite lattice type.
- [setpart1 S]    == the partition of [S] made only of singleton
- [trivsetpart S] == the partition whose only block is [S] itself
                     if [S] is non empty
- [setpart_set0 T]  == the trivial empty partition of [set0] in [setpart set0]
- [setpart_set1 x]  == the trivial partition of [[set x]] in [setpart [set x]]

- [join_finer_eq P Q] == the equivalence relation obtained as the join of
                     the one of P and Q.
 ******)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import div ssralg ssrint ssrnum binomial.
Require Import tools combclass sorted ordtype partition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import LeqGeqOrder.
Import Order.TTheory.


Lemma pblock_in (T : finType) (P : {set {set T}}) (x : T) :
  set0 \notin P -> (pblock P x \in P) = (x \in cover P).
Proof.
move=> set0nP; rewrite /pblock; apply/esym/bigcupP.
case: pickP=> /= [A /andP[PA Ax]| noA]; first by rewrite PA; exists A.
by rewrite (negbTE set0nP)=> [[A PA Ax]]; case/andP: (noA A).
Qed.

Lemma mem_pblockC (T : finType) (P : {set {set T}}) :
  trivIset P -> forall x y : T, (x \in pblock P y) = (y \in pblock P x).
Proof.
move=> Htriv.
suff refl x y : x \in pblock P y -> y \in pblock P x.
  by move=> x y; apply/(sameP idP)/(iffP idP); apply refl.
move=> /[dup] /(same_pblock Htriv) eqPxy.
rewrite -eqPxy mem_pblock => Hcov.
by rewrite -eq_pblock // eqPxy.
Qed.

Lemma equivalence_partitionE (T : finType) (R S : rel T) (D : {set T}) :
  R =2 S -> equivalence_partition R D = equivalence_partition S D.
Proof.
rewrite /equivalence_partition=> eq_RS.
by apply eq_imset=> x; apply/setP=> y; rewrite !inE eq_RS.
Qed.

Section Defs.

Variable T : finType.
Variable S : {set T}.

Structure setpart : predArgType :=
  SetPart {setpartval :> {set {set T}}; _ : partition setpartval S}.
HB.instance Definition _ := [isSub of setpart for setpartval].
HB.instance Definition _ := [Finite of setpart by <:].

Implicit Type (P Q : setpart) (A B : {set T}).

Lemma setpartP P : partition P S.
Proof. by case: P. Qed.

Lemma trivIsetpart P : trivIset P.
Proof. by case: P => P /= /and3P[]. Qed.

Lemma cover_setpart P : cover P = S.
Proof. by case: P => P /= /and3P[/eqP ->]. Qed.

Lemma setpart_non0 P : set0 \notin P.
Proof. by case: P => P /= /and3P[]. Qed.

Hint Resolve setpartP trivIsetpart setpart_non0 : core.

Lemma setpart_subset P A : A \in P -> A \subset S.
Proof.
have /and3P[/eqP <- _ _ AinP] := setpartP P.
rewrite /cover; apply/subsetP=> x xinA.
by apply/bigcupP=> /=; exists A.
Qed.

Lemma setpart_eq P x A B :
  A \in P -> B \in P -> x \in A -> x \in B -> A = B.
Proof.
move=> AinP BinP xinA xinB; apply/eqP.
have /contraR := trivIsetP (trivIsetpart P) A B AinP BinP; apply.
rewrite -setI_eq0; apply/set0Pn; exists x.
by rewrite inE xinA xinB.
Qed.

Lemma mem_eq_pblock P A : A \in P -> forall x, x \in A -> pblock P x = A.
Proof.
move=> AinP x xinA.
exact: (def_pblock (partition_trivIset (setpartP P)) AinP).
Qed.

Lemma mem_setpart_pblock P A : A \in P -> exists x, x \in A.
Proof.
move=> AinP.
have /set0Pn[x xinA] : A != set0.
  by move: (setpart_non0 P); apply contra=> /eqP <-.
by exists x.
Qed.

Lemma mem_pblock_setpart P x y : x \in pblock P y -> x \in S.
Proof.
move=> /[dup] xPy.
by rewrite -(same_pblock (trivIsetpart P) xPy) mem_pblock cover_setpart.
Qed.

Lemma pblock_notin P x : (pblock P x != set0) = (x \in S).
Proof.
apply/idP/idP => [/set0Pn[y]|].
  by rewrite mem_pblockC // => /mem_pblock_setpart.
rewrite -{1}(cover_setpart P) => /pblock_mem H.
by have:= setpart_non0 P; apply contra=> /eqP <-.
Qed.

Fact setpart1_subproof : partition [set [set x] | x in S] S.
Proof.
apply/and3P; split.
- rewrite eqEsubset /cover; apply/andP; split; apply/subsetP=> x.
  + move/bigcupP=> [/= P /imsetP[y yinS ->{P}]].
    by rewrite inE=> /eqP->.
  + move=> xinS; apply/bigcupP=> /=; exists [set x]; last exact: set11.
    exact: imset_f.
- apply/trivIsetP=> A B /imsetP[x _ ->{A}] /imsetP[y _ ->{B}].
  by rewrite disjoints1 inE; apply contra=> /eqP ->.
- apply/imsetP=> [][x _] /(congr1 (fun A : {set T} => x \in A)).
  by rewrite !inE eqxx.
Qed.
Canonical setpart1 := SetPart setpart1_subproof.
HB.instance Definition _ := isInhabitedType.Build setpart setpart1.

Lemma pblock_setpart1 x : x \in S -> pblock setpart1 x = [set x].
Proof.
move=> xinS; apply: (def_pblock (trivIsetpart _)); rewrite ?inE //.
by rewrite /setpart1 /= imset_f.
Qed.

Fact trivsetpart_subproof :
  partition (T := T) (if S == set0 then set0 else [set S]) S.
Proof.
case: (S =P set0) => [-> | /eqP/set0Pn[x xinS]/=].
  by rewrite partition_set0.
rewrite /partition cover1 eq_refl trivIset1 /=.
by rewrite inE eq_sym; apply/set0Pn; exists x.
Qed.
Canonical trivsetpart := SetPart trivsetpart_subproof.

Lemma pblock_trivsetpart x : x \in S -> pblock trivsetpart x = S.
Proof.
move=> xinS.
apply: (def_pblock (trivIsetpart _)); rewrite ?inE //.
rewrite /trivsetpart /=.
suff /negbTE -> : S != set0 by rewrite inE.
by apply/set0Pn; exists x.
Qed.

End Defs.
#[export] Hint Resolve setpartP trivIsetpart setpart_non0 : core.


Section Empty.

Variable T : finType.

Fact part_ordinal0 : partition (T := T) set0 set0.
Proof.
apply/and3P; split.
- by rewrite /cover big_set0.
- by rewrite /trivIset /cover !big_set0 cards0.
- by rewrite in_set0.
Qed.
Definition setpart_set0 := SetPart part_ordinal0.

Lemma setpart_set0_eq_set0 (p : setpart set0) : p = setpart_set0.
Proof.
case: p=> p Hp; apply/eqP.
by rewrite eqE /= -partition_set0.
Qed.

Lemma enum_setpart_set0 : enum (setpart (@set0 T)) = [:: setpart_set0 ].
Proof.
move Hl : (enum _)=> l.
case: l Hl=> /= [|p0 [|p1 l]] Hl.
- exfalso; have:= mem_enum (setpart set0) setpart_set0.
  by rewrite Hl inE in_nil.
- by rewrite (setpart_set0_eq_set0 p0).
- exfalso; rewrite (setpart_set0_eq_set0 p0) (setpart_set0_eq_set0 p1) in Hl.
  by have:= enum_uniq (setpart (@set0 T)); rewrite Hl /= inE eq_refl /=.
Qed.

End Empty.


Section Singleton.

Variable T : finType.
Variable x : T.

Implicit Type (A B : {set T}).

Fact part_ordinal1 : partition [set [set x]] [set x].
Proof.
rewrite /partition cover1 eq_refl trivIset1 /= in_set1.
apply/(introN idP)=> /eqP/setP/(_ x).
by rewrite !inE eq_refl.
Qed.
Definition setpart_set1 := SetPart part_ordinal1.

Lemma subset_set1 A :
  A \subset [set x] -> (A = set0) \/ (A = [set x]).
Proof. by rewrite -powersetE powerset1 !inE=> /orP[]/eqP->; [left|right]. Qed.

Lemma part_set1_eq (P : {set {set T}}) :
  partition P [set x] -> P = [set [set x]].
Proof.
move=> /[dup] /and3P[H1 _ Hn0] /triv_part; apply.
move: H1; rewrite eqEsubset=> /andP[subPx /subsetP/(_ x)].
rewrite inE=> /(_ (eq_refl _))/bigcupP[/= A AinP xinA].
suff <- : A = [set x] by [].
apply/eqP; rewrite eqEsubset.
apply/andP; split; last by apply/subsetP=> y; rewrite inE=> /eqP->{y}.
exact: (subset_trans (bigcup_sup _ _) subPx).
Qed.

Lemma setpart_set1_eq_set1 (p : setpart [set x]) : p = setpart_set1.
Proof. by case: p=> p Hp; apply/val_inj/part_set1_eq. Qed.

Lemma enum_setpart_set1 : enum (setpart [set x]) = [:: setpart_set1].
Proof.
move Hl : (enum _)=> l.
case: l Hl=> [|p0 [|p1 l]] Hl.
- exfalso; have:= mem_enum (setpart [set x]) setpart_set1.
  by rewrite Hl inE in_nil.
- by rewrite (setpart_set1_eq_set1 p0).
- exfalso; rewrite (setpart_set1_eq_set1 p0) (setpart_set1_eq_set1 p1) in Hl.
  by have:= enum_uniq (setpart [set x]); rewrite Hl /= inE eq_refl /=.
Qed.

End Singleton.


Module RefinmentOrder.
Section RefinmentOrder.

Import LeqGeqOrder.

Context {T : finType} (S : {set T}).

Implicit Type (P Q R : setpart S) (A B X Y : {set T}).

Definition is_finer P Q :=
  [forall (x | x \in S), pblock P x \subset pblock Q x].

Lemma is_finer_pblockP P Q :
  reflect (forall x, x \in S -> pblock P x \subset pblock Q x) (is_finer P Q).
Proof. exact: (iffP forall_inP). Qed.

Lemma is_finer_refl : reflexive is_finer.
Proof. by move=> P; apply/is_finer_pblockP=> x _. Qed.

Lemma is_finer_trans : transitive is_finer.
Proof.
move=> P1 P2 P3 /is_finer_pblockP P12 /is_finer_pblockP P23.
apply/is_finer_pblockP=> x xinS.
exact: (subset_trans (P12 _ xinS) (P23 _ xinS)).
Qed.

Fact is_finer_setpart_anti : antisymmetric is_finer.
Proof.
suff finsub P Q : is_finer P Q -> is_finer Q P -> P \subset Q.
  move=> P Q /andP[finPQ finQP].
  apply/eqP; rewrite eqE /=; rewrite eqEsubset.
  by apply/andP; split; apply: finsub.
move=> /is_finer_pblockP PsQ /is_finer_pblockP QsP.
apply/subsetP=> /= A AinP.
have [x xinA] := mem_setpart_pblock AinP.
have Aeq := mem_eq_pblock AinP xinA; subst A.
have xinS : x \in S by apply: (subsetP (setpart_subset AinP)).
have -> : pblock P x = pblock Q x.
  by apply/eqP; rewrite eqEsubset ?PsQ ?QsP.
by apply pblock_mem; rewrite (cover_setpart Q).
Qed.
Lemma setpartfiner_display : unit. Proof. exact: tt. Qed.
#[export]
HB.instance Definition _ :=
  Order.Le_isPOrder.Build setpartfiner_display (setpart S)
    is_finer_refl is_finer_setpart_anti is_finer_trans.

Lemma is_finerP P Q :
  reflect
    (forall A, A \in P -> exists2 B : {set T}, B \in Q & A \subset B)
    (P <= Q)%O.
Proof.
apply (iffP (is_finer_pblockP P Q)) => [subPQ A AinP | H x xinS].
  have [x xinA] := mem_setpart_pblock AinP.
  have Aeq := mem_eq_pblock AinP xinA; subst A.
  exists (pblock Q x); last exact/subPQ/(subsetP (setpart_subset AinP)).
  by rewrite pblock_in // (cover_setpart Q) (subsetP (setpart_subset AinP)).
apply/subsetP => y yPx.
have eqPxy := same_pblock (trivIsetpart P) yPx.
have:= yPx; rewrite -eqPxy mem_pblock=> /pblock_mem{}/H[A AinQ /subsetP PsA].
suff -> : pblock Q x = A by apply: PsA; rewrite eqPxy.
apply: (def_pblock (trivIsetpart Q) AinQ).
by apply: PsA; rewrite eqPxy mem_pblock cover_setpart.
Qed.

Fact setpart1_bottom P : (setpart1 S <= P)%O.
Proof.
apply/is_finer_pblockP=> x xinS.
rewrite pblock_setpart1 //; apply/subsetP=> y.
by rewrite inE => /eqP->; rewrite mem_pblock cover_setpart.
Qed.
Fact trivsetpart_top P : (P <= trivsetpart S)%O.
Proof.
apply/is_finer_pblockP=> x xinS.
apply/subsetP=> y; rewrite pblock_trivsetpart //.
move: xinS; rewrite -{1}(cover_setpart P).
by move/pblock_mem/setpart_subset/subsetP; apply.
Qed.
#[export]
HB.instance Definition _ :=
  Order.hasBottom.Build setpartfiner_display (setpart S) setpart1_bottom.
#[export]
HB.instance Definition _ :=
  Order.hasTop.Build setpartfiner_display (setpart S) trivsetpart_top.

Fact meet_finer_subproof P Q :
  partition [set A :&: B | A in P, B in Q & A :&: B != set0] S.
Proof.
apply/and3P; split.
- apply/eqP/setP=> x; apply/bigcupP/idP=> [| xinS /=].
  + move=> [/= y /imset2P[/= A B AinP]].
    rewrite inE=> /andP[BinQ _ ->{y}]; rewrite inE=> /andP[_].
    exact/subsetP/(setpart_subset BinQ).
  + have xinU : x \in pblock P x :&: pblock Q x.
      by rewrite inE !mem_pblock !cover_setpart xinS.
    exists (pblock P x :&: pblock Q x); last exact xinU.
    apply: imset2_f; first by apply pblock_mem; rewrite cover_setpart.
    rewrite inE pblock_mem ?cover_setpart //=.
    by apply/set0Pn; exists x.
- apply/trivIsetP=> AB1 AB2.
  move=> /imset2P[/= A1 B1 A1inP]; rewrite inE=> /andP[B1inQ _ ->{AB1}].
  move=> /imset2P[/= A2 B2 A2inP]; rewrite inE=> /andP[B2inQ _ ->{AB2}].
  apply contraR; rewrite -setI_eq0=> /set0Pn[x].
  rewrite !inE=> /andP[/andP[xinA1 xinB1] /andP[xinA2 xinB2]].
  suff [-> ->] : A1 = A2 /\ B1 = B2 by [].
  split; first exact: (setpart_eq A1inP A2inP xinA1 xinA2).
  exact: (setpart_eq B1inQ B2inQ xinB1 xinB2).
- apply/negP=> /imset2P[/= A B _].
  by rewrite inE=> /andP[_] + H; rewrite H eq_refl.
Qed.
Definition meet_finer P Q := SetPart (meet_finer_subproof P Q).

Variant meet_spec P Q X : Prop :=
  MeetSpec A B of A \in P & B \in Q & A :&: B != set0 & X = A :&: B.
Lemma mem_meet_finerP P Q X :
  reflect (meet_spec P Q X) (X \in meet_finer P Q).
Proof.
apply (iffP imset2P)=> [[/= A B AinP]|].
  rewrite inE=> /andP[BinQ ABneq0 ->{X}].
  exact: (MeetSpec AinP BinQ).
move=> [A B AinP BinQ ABneq0 ->{X}].
by exists A B=> //; rewrite inE; apply/andP.
Qed.

Lemma meet_finerC : commutative meet_finer.
Proof.
suff incl P Q : meet_finer P Q \subset meet_finer Q P.
  by move=> P Q; apply/val_inj/eqP; rewrite eqEsubset !incl.
apply/subsetP=> AB /mem_meet_finerP[A B AinP BinQ Ineq0 ->{AB}].
rewrite setIC; apply/mem_meet_finerP/(MeetSpec BinQ AinP)=> //.
by rewrite setIC.
Qed.

Lemma le_meet_finer P Q : (meet_finer P Q <= P)%O.
Proof.
apply/is_finerP=> AB /mem_meet_finerP[/= A B ainP BinQ Ineq0 ->{AB}].
by exists A; last exact: subsetIl.
Qed.

Fact meet_finerP R P Q : (R <= meet_finer P Q)%O = (R <= P)%O && (R <= Q)%O.
Proof.
apply/idP/andP=> [Hmeet | [/is_finerP RA /is_finerP RB]].
  split; apply: (le_trans Hmeet); first exact: le_meet_finer.
  by rewrite meet_finerC le_meet_finer.
apply/is_finerP=> X XinR.
move/(_ X XinR): RA=> [A AinP XsA].
move/(_ X XinR): RB=> [B BinQ XsB].
exists (A :&: B); last by rewrite subsetI XsA XsB.
apply/mem_meet_finerP/(MeetSpec AinP BinQ)=> //.
have {XsA XsB} XsAB : X \subset A :&: B by rewrite subsetI XsA XsB.
apply: (subset_neq0 XsAB).
by have /and3P[_ _]:= setpartP R; apply contra=> /eqP <-.
Qed.

Lemma setpart_conn P : connect_sym (fun x y : T => y \in (pblock P x)).
Proof.
suff impl x y : x \in pblock P y -> y \in pblock P x.
  by apply: sym_connect_sym=> x y; apply/idP/idP; apply impl.
move=> /[dup] /(same_pblock (trivIsetpart P)) peq.
rewrite -peq mem_pblock=> /pblock_mem; rewrite {x}peq.
by rewrite mem_pblock pblock_in.
Qed.

Definition join_finer_eq P Q :=
  connect (relU (fun x y => y \in pblock P x) (fun x y => y \in pblock Q x)).

Lemma join_finer_equivalence P Q :
  {in S & &, equivalence_rel (join_finer_eq P Q)}.
Proof.
split; first exact: connect0.
rewrite /join_finer_eq=> cxy.
rewrite -(same_connect _ cxy) // {cxy H H0 H1 x y z}.
by apply: relU_sym; apply: setpart_conn.
Qed.

Definition join_finer P Q :=
  SetPart (equivalence_partitionP (join_finer_equivalence P Q)).

Lemma join_finerC : commutative join_finer.
Proof.
rewrite /join_finer=> P Q; apply val_inj=> /=.
apply equivalence_partitionE => x y; apply eq_connect => {}x {}y /=.
exact: orbC.
Qed.

Lemma le_join_finer P Q : (P <= join_finer P Q)%O.
Proof.
apply/is_finer_pblockP=> x xinS; apply/subsetP => y yPx.
have yinS := mem_pblock_setpart yPx.
rewrite (pblock_equivalence_partition (join_finer_equivalence P Q)) //.
by rewrite /join_finer_eq /=; apply: connect1; rewrite /= yPx.
Qed.

Fact join_finerP P Q R : (join_finer P Q <= R)%O = (P <= R)%O && (Q <= R)%O.
Proof.
apply/idP/andP=> [Hjoin | [/is_finer_pblockP RA /is_finer_pblockP RB]].
  split; apply: (le_trans _ Hjoin); first exact: le_join_finer.
  by rewrite join_finerC le_join_finer.
apply/is_finer_pblockP => x xinS.
apply/subsetP=> y /[dup]/mem_pblock_setpart yinS.
rewrite (pblock_equivalence_partition (join_finer_equivalence P Q)) //.
rewrite {yinS} /join_finer_eq => /closed_connect <-{y}.
  by rewrite mem_pblock (cover_setpart R).
move=> y z /= Hrel; rewrite -!eq_pblock ?(cover_setpart R) //.
suff {x xinS} -> : pblock R y = pblock R z by [].
move: Hrel=> /orP[zPy | zQy]; apply: same_pblock => //.
- have /RA/subsetP := mem_pblock_setpart zPy; apply.
  by rewrite mem_pblockC.
- have /RB/subsetP := mem_pblock_setpart zQy; apply.
  by rewrite mem_pblockC.
Qed.
#[export]
HB.instance Definition _ :=
  Order.POrder_MeetJoin_isLattice.Build setpartfiner_display (setpart S)
    meet_finerP join_finerP.

End RefinmentOrder.


Module Exports.
HB.reexport RefinmentOrder.

Section Finer.

Context {T : finType} (S : {set T}).
Implicit Type (P Q R : setpart S) (A B X Y : {set T}).

Definition is_finerP P := is_finerP P.
Definition is_finer_pblockP P Q :
  reflect (forall x, x \in S -> pblock P x \subset pblock Q x) (P <= Q)%O
  := is_finer_pblockP P Q.

Lemma is_finer_subpartP P Q :
  reflect
    (exists2 subpart : {set T} -> {set {set T}},
        forall B, B \in Q -> partition (subpart B) B
        & \bigcup_(B in Q) subpart B = P)
    (P <= Q)%O.
Proof.
apply (iffP idP) => [PfinQ | [f partf UeqP]]; first last.
  apply/is_finerP=> A; rewrite -UeqP=> /bigcupP[/= B BinQ AinfB].
  exists B; first exact: BinQ.
  move/(_ B BinQ): partf=> /cover_partition <-.
  exact: (bigcup_max _ AinfB).
exists (fun B => [set A | (A \in P) && (A \subset B)]).
- move=> B BinQ; apply/and3P; split.
  + rewrite eqEsubset; apply/andP; split.
      by apply/bigcupsP=> C; rewrite inE=> /andP[].
    apply/subsetP=> x xinB.
    have xinS : x \in S by apply: (subsetP (setpart_subset BinQ)).
    apply/bigcupP; exists (pblock P x); first last.
      by rewrite mem_pblock cover_setpart.
    rewrite inE (pblock_in _ (setpart_non0 _)) cover_setpart xinS /=.
    suff <- : pblock Q x = B by apply: (is_finer_pblockP P Q PfinQ).
    exact: def_pblock.
  + apply: (trivIsetS _ (trivIsetpart P)).
    by apply/subsetP=> x; rewrite inE=> /andP[].
  + by have:= setpart_non0 P; apply contra; rewrite inE=> /andP[].
- apply/setP=> /= A; apply/bigcupP/idP=> /= [[B BinQ] | AinP].
  + by rewrite inE=> /andP[].
  + move/is_finerP: PfinQ=> /(_ A AinP) [B BinQ AsB].
    by exists B=> //; rewrite inE AinP AsB.
Qed.

Lemma setpart_bottomE : 0%O = setpart1 S.
Proof. by []. Qed.
Lemma setpart_topE : 1%O = trivsetpart S.
Proof. by []. Qed.

Definition mem_meet_finerP P Q X : reflect (meet_spec P Q X) (X \in P `&` Q)%O
  := mem_meet_finerP P Q X.

Lemma join_finer_eq_in_S P Q x y :
  x \in S -> join_finer_eq P Q x y -> y \in S.
Proof.
move=> xinS /connectP => [[pth Hpth Hlast]].
elim: pth x Hpth Hlast xinS => [x /= _ -> // | x p0 IH xn /=].
case/andP=> [H1 {}/IH/[apply]/[swap] xninS]; apply.
by move: H1=> /orP[]; apply: mem_pblock_setpart.
Qed.

Lemma join_finerE P Q x y :
  x \in S -> y \in pblock (P `|` Q)%O x = join_finer_eq P Q x y.
Proof.
move=> xinS; case/boolP: (y \in S) => [yinS | yninS].
  by rewrite -(pblock_equivalence_partition (join_finer_equivalence P Q)).
have:= yninS; rewrite -(pblock_notin (P `|` Q)%O) negbK.
rewrite mem_pblockC // => /eqP ->.
rewrite inE; apply/esym/negbTE.
by move: yninS; apply contra; exact: join_finer_eq_in_S.
Qed.

End Finer.

Notation join_finer_eq := join_finer_eq.

End Exports.
End RefinmentOrder.
HB.export RefinmentOrder.Exports.


Section FinerCard.

Context {T : finType} (S : {set T})
  (P Q : setpart S) (finPQ : (P <= Q)%O).

Implicit Types (A B : {set T}).

Definition map_finer A : {set T} :=
    if (boolP (A \in P)) is AltTrue pin then
      let: exist2 B _ _ := sig2W (is_finerP P Q finPQ A pin) in B
    else set0.

Lemma map_finer_subset A : A \in P -> A \subset map_finer A.
Proof.
rewrite /map_finer; case (boolP (A \in P)) => [H _ |//].
by case: (sig2W _) => /= B.
Qed.

Lemma map_finer_in A : A \in P -> map_finer A \in Q.
Proof.
move=> AinP; rewrite /map_finer.
case (boolP (A \in P)) => [H |]; last by rewrite AinP.
by case: (sig2W _) => /= B.
Qed.

Lemma map_finer_pblock x : map_finer (pblock P x) = pblock Q x.
Proof.
rewrite /map_finer; case (boolP (pblock P x \in P)) => [H |]; first last.
  rewrite (pblock_in _ (setpart_non0 P)) (cover_setpart P).
  by rewrite -(pblock_notin Q) negbK => /eqP->.
case: (sig2W _) => /= B BinQ /subsetP PxB.
apply esym; apply def_pblock => //.
by apply PxB; rewrite mem_pblock -pblock_in.
Qed.

Lemma image_map_finer : [set map_finer x | x in P] = Q.
Proof.
apply/setP=> /= B; apply/imsetP/idP=> /=[[A /map_finer_in H ->{B}] // |].
move=> /[dup] BinQ /mem_setpart_pblock=> -[x xinB]; exists (pblock P x).
  apply pblock_mem; rewrite cover_setpart.
  exact: (subsetP (setpart_subset BinQ)).
by apply esym; rewrite map_finer_pblock; apply: def_pblock.
Qed.

Lemma is_finer_card : #|Q| <= #|P| ?= iff (P == Q).
Proof.
split; first by rewrite -image_map_finer leq_imset_card.
apply/eqP/eqP=> [|-> //].
rewrite -image_map_finer => /eqP/imset_injP map_finer_inj.
apply val_inj => /=; rewrite -image_map_finer.
suff : {in P, map_finer =1 id} by move/eq_in_imset => ->; rewrite imset_id.
move=> /= A /[dup] AinP /mem_setpart_pblock [x xinA].
apply/eqP; rewrite eqEsubset map_finer_subset // andbT.
rewrite -(mem_eq_pblock AinP xinA) map_finer_pblock.
apply/subsetP => y /(same_pblock (trivIsetpart Q)) Qxy.
have xinS : x \in S by apply: (subsetP (setpart_subset AinP)).
have yinS : y \in S.
  rewrite -(cover_setpart Q) -mem_pblock Qxy.
  by rewrite -eq_pblock ?cover_setpart ?Qxy.
rewrite -eq_pblock ?cover_setpart //.
apply/eqP/esym; move: Qxy; rewrite -!map_finer_pblock.
by apply: map_finer_inj; apply: pblock_mem; rewrite cover_setpart.
Qed.

End FinerCard.
