(** * Combi.SymGroup.weak_order : The weak order on the Symmetric Group *)
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
(** * The weak order on the Symmetric Group

We define the right (with the mathcomp convention of product of permutation)
weak order on the symmetric group. We show that it is equivalent to inclusion
of sets of inversions and that it is a lattice.

Here are the notion defined is this file:

- [s <=R t]     == [s] is smaller for the right weak order than [t].
- [supperm s t] == the supremum of [s] and [t] for the right weak order.
- [inferm s t]  == the infimum of [s] and [t] for the right weak order.

***************************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup perm morphism presentation.

Require Import permcomp tools permuted combclass congr presentSn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation "''s_' i" := (eltr _ i)
      (at level 8, i at level 2, format "''s_' i").

Reserved Notation "x '<=R' y" (at level 70, y at next level).

Import GroupScope.

Section Def.

Variable (n0 : nat).
Local Notation n := n0.+1.
Implicit Type (s t u v : 'S_n).


Definition leperm s t :=
  [exists u, (t == s * u) && (length t == length s + length u)].
Notation "s '<=R' t" := (leperm s t).

Lemma lepermP s t :
  reflect (exists2 u, t = s * u & length t = length s + length u)
          (s <=R t).
Proof.
apply (iffP existsP) => [] /= [u].
- by move/andP => [/eqP Heq /eqP Hlen]; exists u.
- by move=> /eqP Heq /eqP Hlen; exists u; apply/andP.
Qed.

Lemma leperm_refl s : s <=R s.
Proof. by apply/lepermP; exists 1; rewrite ?mulg1 // length1 addn0. Qed.

Lemma leperm_trans : transitive leperm.
Proof.
move=> t s u /lepermP/= [st ->{t} Hsst] /lepermP/= [stu ->{u} Hstu].
apply/lepermP; exists (st * stu); first by rewrite mulgA.
rewrite Hstu Hsst -addnA; congr (_ + _).
by rewrite {}Hsst in Hstu; rewrite (lengthKR Hstu).
Qed.

Lemma leperm_anti : antisymmetric leperm.
Proof.
move=> s t /andP [/lepermP [/= st Hst Hlst] /lepermP [/= ts Hts Hlts]].
have eql: length s = length t.
  by apply/eqP; rewrite eqn_leq {1}Hlst {3}Hlts !leq_addr.
move: Hlts; rewrite eql => /(congr1 (fun x => x - (length t)))/esym.
rewrite addKn subnn Hts => /length_eq0 ->.
exact: mulg1.
Qed.

Lemma leperm1p s : 1 <=R s.
Proof.
apply/lepermP; exists s; first by rewrite mul1g.
by rewrite length1 add0n.
Qed.

Lemma leperm_maxpermMl s t : (maxperm * t <=R maxperm * s) = (s <=R t).
Proof.
suff {s t} impl u v : u <=R v -> maxperm * v <=R maxperm * u.
  apply/idP/idP; last exact: impl.
  rewrite -{2}(mulKg maxperm s) -{2}(mulKg maxperm t) maxpermV.
  exact: impl.
move/lepermP => /= [s ->{v} Hlen].
apply/lepermP; exists s^-1; first by rewrite -!mulgA mulgV mulg1.
rewrite !length_maxpermMl Hlen lengthV subnDA subnK //.
by rewrite -(leq_add2l (length u)) -Hlen subnKC length_max.
Qed.

Lemma leperm_maxperm s : s <=R maxperm.
Proof. by rewrite -leperm_maxpermMl -{1}maxpermV mulVg leperm1p. Qed.


Lemma leperm_invset s t : s <=R t -> invset s \subset invset t.
Proof.
move/lepermP => /= [u]->{t}.
rewrite -{-2}(canwordP u) -(size_canword u).
elim/last_ind: (canword u) (canword_reduced u) => [| w i IHw].
  by rewrite big_nil /= mulg1 => _.
rewrite size_rcons -cats1 big_cat /= big_cons big_nil mulg1.
move/reduced_catl => Hred; have:= Hred; rewrite unfold_in => /eqP <-.
move/(_ Hred): IHw; move: Hred; rewrite unfold_in => /eqP <-.
move: (\prod_(i <- w) _) => /= P IHP.
rewrite mulgA -(addn1 (length P)) addnA -(length_eltr i) => Hlen.
move/(_ (lengthKL Hlen)): IHP => /subset_trans; apply.
pose il := lift ord_max i.
have Hi : il < n0 by rewrite /il lift_max ltn_ord.
have Hsi : 's_i = 's_il :> 'S_n by rewrite lift_max.
rewrite Hsi invset_eltrR //; first exact: subsetU1.
by rewrite length_descR // -{}Hsi Hlen (lengthKL Hlen) length_eltr addn1 ltnS.
Qed.


Lemma leperm_eltrR s (i : 'I_n) :
  i < n0 -> s^-1 i < s^-1 (inord (i.+1)) -> s <=R (s * 's_i).
Proof.
move=> Hi Hnrec; apply/lepermP; exists 's_i => //.
by rewrite length_add1R // -[val i]/(val (Ordinal Hi)) length_eltr addn1.
Qed.

Lemma invset_leperm s t : invset s \subset invset t -> s <=R t.
Proof.
move=> H.
have /subnKC: length s <= length t by rewrite /length subset_leq_card.
move: (length t - length s) => d Hd.
elim: d s t Hd H => [|d IHd] s t Hd H.
  move: Hd; rewrite addn0 /length => /eqP.
  rewrite (subset_leqif_cards H) => /eqP/invset_inj ->.
  exact: leperm_refl.
move: H; rewrite subEproper => /orP [/eqP/invset_inj->|]; first exact: leperm_refl.
move/properP => /= [incl ex].
have {ex} /ex_minnP [m] : exists n : nat,
    [exists p, [&& p \in invset t, p \notin invset s & t p.1 - t p.2 == n]].
  move: ex => [[i j]] ijt ijNs; exists (t i - t j).
  by apply/existsP => /=; exists (i, j) => /=; apply/and3P.
move=> /existsP /=[[i j]] /=.
rewrite [in X in (X-> _ -> _)]/invset !inE /= => /and3P [/andP [iltj tjltti]].
rewrite iltj /= -leqNgt leq_eqVlt (inj_eq val_inj) (inj_eq perm_inj).
rewrite -[i == j](inj_eq val_inj) (ltn_eqF iltj) /= => siltsj /eqP eqm Hm.
have m0 : 0 < m.
  by case: m eqm {Hm} => // /eqP; rewrite subn_eq0 leqNgt tjltti.
have Hti : t i = t j + m :> nat.
  rewrite -eqm {Hm} in m0; rewrite -eqm subnKC //.
  by apply ltnW; rewrite -subn_gt0.
have {Hm} Hm (k l : 'I_n) :
    (k, l) \in invset t -> (k, l) \notin invset s -> m <= t k - t l.
  move=> pIt pNIs; apply Hm; apply/existsP; exists (k, l).
  by rewrite pIt pNIs eq_refl.
have {Hm m0 eqm tjltti} Heq : m = 1%N.
  have {incl} incl (k l : 'I_n) : k < l -> s k > s l -> t k > t l.
    by move=> kltl; move: incl => /subsetP/(_ (k, l)); rewrite !inE kltl.
  apply anti_leq; rewrite {}m0 andbT {Hd IHd}.
  rewrite leqNgt; apply (introN idP) => Habs.
  pose k := (t^-1 (inord (t j).+1)).
  have tk : t k = (t j).+1 :> nat.
    by rewrite /k permKV inordK // ltnS (leq_trans tjltti _) // -ltnS.
  case: (ltngtP k i) => [klti|iltk|/val_inj Hk]; last 1 first.
  - by move: Habs; rewrite -eqm -Hk tk subSn // ?subnn ltnn.
  - have kltj := ltn_trans klti iltj.
    suff : m <= t k - t j.
      by rewrite tk subSn // subnn => /(leq_trans Habs); rewrite ltnn.
    apply: Hm; rewrite inE /= kltj /= ?tk //.
    rewrite -leqNgt; apply ltnW; apply: (leq_trans _ siltsj).
    rewrite leqNgt ltnS; apply (introN idP) => siltsk.
    have:= incl k i klti siltsk.
    by rewrite tk ltnS leqNgt tjltti.
  case: (ltngtP k j) => [kltj|jltk|/val_inj]; last first.
  - by move/(congr1 t)/(congr1 val); rewrite /= tk => /eqP; elim: (val (t j)).
  - suff : m <= t i - t k.
      rewrite tk; rewrite -eqm.
      case: (val (t i)) tjltti => //= u; rewrite ltnS => Hu.
      by rewrite subSS subSn // ltnn.
    apply: Hm; rewrite inE /= iltk /= ?tk.
    + rewrite {}Hti {eqm}; case: m Habs => [|[|m]]// _.
      by rewrite !addnS !ltnS leq_addr.
    + move: incl => /(_ j k jltk)/contra; rewrite -!leqNgt => incl.
      have {}/incl : t j <= t k by rewrite tk.
      exact: leq_trans (ltnW siltsj).
  case: (ltnP (s i) (s k)) => [siltsk|sklesi].
  - suff : m <= t i - t k. (* duplicate code *)
      rewrite tk; rewrite -eqm.
      case: (val (t i)) tjltti => //= u; rewrite ltnS => Hu.
      by rewrite subSS subSn // ltnn.
    apply: Hm; rewrite inE /= iltk /= ?tk.
    + rewrite {}Hti {eqm}; case: m Habs => [|[|m]]// _.
      by rewrite !addnS !ltnS leq_addr.
    + rewrite -leqNgt; exact: ltnW.
  case: (ltnP (s k) (s j)) => [skltsj|sjlesk].
  - suff : m <= t k - t j.
      by rewrite tk subSn // subnn => /(leq_trans Habs); rewrite ltnn.
    apply: Hm; rewrite inE /= kltj /= ?tk //.
    by rewrite -leqNgt; apply ltnW.
  - by have:= leq_trans siltsj (leq_trans sjlesk sklesi); rewrite ltnn.
subst m; rewrite addn1 in Hti.
have tjn0 : t j < n0 by rewrite -ltnS -Hti.
have {Hti} Himj : (t * 's_(t j))^-1 (t j) = i.
  by rewrite invMg !permM eltrV /eltr inord_val tpermL -Hti inord_val !permK.
have Himi : (t * 's_(t j))^-1 (inord (succn (t j))) = j.
  by rewrite invMg !permM eltrV /eltr tpermR inord_val !permK.
have Hdesc : (t * 's_(t j))^-1 (t j) < (t * 's_(t j))^-1 (inord (succn (t j))).
  by rewrite Himi Himj.
have Hln : (length (t * 's_(t j))).+1 = length t.
  by rewrite -[in RHS](mulgK 's_(t j) t) eltrV [RHS]length_add1R.
have {Hd Hln} {}/IHd IHd : length s + d = length (t * 's_(t j)).
  by move: Hd; rewrite -Hln addnS => [] [].
have {Himi Himj} {}/IHd : invset s \subset invset (t * 's_(t j)).
  have:= invset_eltrR tjn0 Hdesc.
  rewrite -{2}eltrV mulgK {}Himi {}Himj => invsett.
  move: incl; rewrite invsett => /subsetP Hsubs.
  apply/subsetP => /= [[k l] H].
  move/(_ _ H): Hsubs; rewrite !inE /= => /orP [] // /eqP Heq.
  exfalso; move: H; rewrite {}Heq /invset !inE /= iltj /=.
  by rewrite ltnNge (ltnW siltsj).
move/leperm_trans; apply.
rewrite -{3}(mulgK 's_(t j) t) eltrV.
exact: leperm_eltrR.
Qed.

End Def.

Notation "s '<=R' t" := (leperm s t).


Section Closure.

Variable (n0 : nat).
Local Notation n := n0.+1.
Implicit Type (A B C : {set 'I_n * 'I_n}).

Definition tclosure A : {set 'I_n * 'I_n} :=
  [set p | (p.1 != p.2) && (connect (srel A) p.1 p.2)].

Lemma tclosure_sub A B :
  A \subset B -> transitive (srel B) -> tclosure A \subset B.
Proof.
move=> /subsetP AB trB.
apply/subsetP => /= [[i j]]; rewrite /tclosure inE /= => /andP [Hneq].
move/connectP => /= [p]; elim: p i Hneq => [| p0 p IHp] i Hneq /=.
  by move => _ Heq; rewrite Heq eqxx in Hneq.
case: (altP (p0 =P j)) => [<- /= /andP[/AB ->] // | {}/IHp IHp].
by move=> /andP [/AB {}/trB trB {}/IHp H{}/H]; apply: trB.
Qed.

Lemma tclosure_Delta A :
  A \subset Delta -> tclosure A \subset Delta.
Proof.
move/tclosure_sub; apply => j k i; rewrite /= !mem_Delta.
exact: ltn_trans.
Qed.

Lemma tclosureP A :
  A \subset Delta -> transitive (srel (tclosure A)).
Proof.
move/tclosure_Delta => /subsetP subs.
rewrite /prod_uncurry => j i k /= Hij Hjk.
move: (subs _ Hij) (subs _ Hjk); rewrite 2!inE /= => iltj jltk.
move: iltj jltk (ltn_trans iltj jltk); rewrite !ltn_neqAle.
move=> /andP [inj _] /andP [jnk _] /andP [ink _].
move: Hij Hjk; rewrite !inE /= inj ink jnk /=.
exact: connect_trans.
Qed.

End Closure.


Section PermutoSupInf.

Variable (n0 : nat).
Local Notation n := n0.+1.
Implicit Type (s t u v : 'S_n) (A B : {set 'I_n * 'I_n}).

Lemma is_invset_tclosureU A B :
  is_invset A -> is_invset B -> is_invset (tclosure (A :|: B)).
Proof.
move=> isA isB.
have ABD : A :|: B \subset Delta.
  by rewrite subUset; apply/andP; split; apply is_invset_Delta.
constructor; rewrite /=.
- exact: tclosure_Delta.
- exact: tclosureP.
- move=> j i k; rewrite /= !inE /= ![~~ _ && _]andbC ![connect _ _ _ && _]andbC.
  move=> /andP [iltj]; have:= iltj; rewrite ltn_neqAle => /andP [-> _] /= cij.
  move=> /andP [jltk]; have:= jltk; rewrite ltn_neqAle => /andP [-> _] /= cjk.
  have iltk := ltn_trans iltj jltk; rewrite iltk /=.
  have:= iltk; rewrite ltn_neqAle => /andP [-> _] /=.
  have {cij cjk} /andP := conj cij cjk; apply contraL; rewrite negb_and !negbK.

  (* Idea: in the path from i to k, there is a step u v which goes over j.
     This step is connected either by A or B. Then j is connected to u or v. *)

  move=> /connectP /=[p Hp Hk].
  elim: p i Hp Hk iltj {iltk} => [|p0 p IHp] /= i Hp Hk iltj.
    by exfalso; have:= ltn_trans iltj jltk; rewrite Hk ltnn.
  move: Hp => /andP [ip0AB Hp]; apply /orP.
  case: (ltngtP p0 j) => [p0ltj | jltp0 | /val_inj Heq]; last 1 first.
  - by left; apply/connectP; exists [:: p0]; rewrite /= ?ip0AB ?Heq.
  - move/(_ _ Hp Hk p0ltj): IHp => {p Hk Hp} /orP [|->]; last by right.
    move/connectP => /=[p Hp ->].
    by left; apply/connectP; exists (p0::p); rewrite //= ip0AB Hp.
  - wlog ip0 : A B ip0AB isA isB ABD IHp Hp / (i, p0) \in A.
      move=> Hlog; move: ip0AB; rewrite inE => /orP [] Hip0.
      + have /Hlog : (i, p0) \in A :|: B by rewrite inE Hip0 /=.
        exact.
      + have /Hlog : (i, p0) \in B :|: A by rewrite inE Hip0 /=.
        by rewrite setUC; apply.
    suff : ((i, j) \in A :|: B) || ((j, p0) \in A :|: B).
      move/orP=> [ijAB|jp0AB]; [left|right]; apply/connectP.
      + by exists [:: j]; rewrite //= ijAB.
      + by exists (p0 :: p); rewrite //= jp0AB Hp.
    rewrite !inE -!orbA [((i, j) \in B) || _]orbC -!orbA orbA.
    apply/or3P; apply Or31; apply/orP => {p IHp Hp k jltk Hk}.
    move: isA => [_ _]; rewrite transitive_DeltaI1 => H.
    have /H/(_ ip0) : i < j < p0 by rewrite iltj jltp0.
    by move=> [|] -> /=; [left | right].
Qed.

Definition supperm s t :=
  let: exist sup _ := is_invsetP (is_invset_tclosureU (invsetP s) (invsetP t))
  in sup.

Lemma invset_supperm s t :
  invset (supperm s t) = tclosure (invset s :|: invset t).
Proof. by rewrite /supperm; case: is_invsetP => sup pf. Qed.
Lemma suppermC s t : supperm s t = supperm t s.
Proof. by apply invset_inj; rewrite !invset_supperm setUC. Qed.


Lemma suppermPr s t : s <=R (supperm s t).
Proof.
apply invset_leperm; rewrite invset_supperm /tclosure.
apply/subsetP => /= [[i j] Hinv]; rewrite !inE /=.
rewrite neq_ltn (DeltaP ((subsetP (invset_Delta s)) _ Hinv)) /=.
by apply/connectP; exists [:: j]; rewrite //= inE Hinv /=.
Qed.

Lemma suppermPl s t : t <=R (supperm s t).
Proof. by rewrite suppermC; exact: suppermPr. Qed.

Lemma suppermP s t w : s <=R w -> t <=R w -> (supperm s t) <=R w.
Proof.
move=>/leperm_invset Hsw /leperm_invset Htw.
apply/invset_leperm; rewrite invset_supperm; apply tclosure_sub.
- by rewrite subUset Hsw Htw.
- by move: (invsetP w) => [].
Qed.


Definition infperm s t : 'S_n :=
  maxperm * (supperm (maxperm * s) (maxperm * t)).

Lemma infpermC s t : infperm s t = infperm t s.
Proof. by rewrite /infperm suppermC. Qed.

Lemma infpermPr s t : (infperm s t) <=R s.
Proof. by rewrite -leperm_maxpermMl /infperm -{2}maxpermV mulKg suppermPr. Qed.

Lemma infpermPl s t : (infperm s t) <=R t.
Proof. by rewrite infpermC; exact: infpermPr. Qed.

Lemma infpermP s t w : w <=R s -> w <=R t -> w <=R (infperm s t).
Proof.
rewrite -![w <=R _]leperm_maxpermMl /infperm -{5}maxpermV mulKg.
exact: suppermP.
Qed.

End PermutoSupInf.

