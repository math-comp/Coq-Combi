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

Import GroupScope.
Import Order.Theory.


Module InfSupMixin.
Section InfSupMixin.
Variable (disp : unit) (T : porderType disp).
Open Scope order_scope.

Record of_ := Build {
  meet : T -> T -> T;
  join : T -> T -> T;
  meetP : forall x y z, (x <= meet y z) = (x <= y) && (x <= z);
  joinP : forall x y z, (join x y <= z) = (x <= z) && (y <= z);
}.

Fact meet_lel (m : of_) x y : meet m x y <= meet m y x.
Proof.
have:= le_refl (meet m x y); rewrite meetP => /andP [mlex mley].
by rewrite (meetP m) mlex mley.
Qed.
Fact meetC (m : of_) : commutative (meet m).
Proof. by move=> x y; apply le_anti; rewrite !meet_lel. Qed.
Fact meet_leL (m : of_) x y : (meet m x y) <= x.
Proof. by have:= le_refl (meet m x y); rewrite (meetP m) => /andP []. Qed.
Fact meet_leR (m : of_) x y : (meet m x y) <= y.
Proof. by have:= le_refl (meet m x y); rewrite (meetP m) => /andP []. Qed.

Fact join_lel (m : of_) x y : join m x y <= join m y x.
Proof.
have:= le_refl (join m y x); rewrite joinP => /andP [ylej xlej].
by rewrite (joinP m) ylej xlej.
Qed.
Fact joinC (m : of_) : commutative (join m).
Proof. by move=> x y; apply le_anti; rewrite !join_lel. Qed.
Fact join_leL (m : of_) x y : x <= (join m x y).
Proof. by have:= le_refl (join m x y); rewrite (joinP m) => /andP []. Qed.
Fact join_leR (m : of_) x y : y <= (join m x y).
Proof. by have:= le_refl (join m x y); rewrite (joinP m) => /andP []. Qed.

Program Definition latticeMixin (m : of_) :=
  @LatticeMixin disp _ (meet m) (join m) (meetC m) (joinC m) _ _ _ _ _.
Next Obligation.
move=> x y z; apply le_anti.
apply/andP; split; rewrite !meetP -?andbA; apply/and3P; split.
- exact: meet_leL.
- exact: (le_trans (meet_leR m _ _) (meet_leL m _ _)).
- exact: (le_trans (meet_leR m _ _) (meet_leR m _ _)).
- exact: (le_trans (meet_leL m _ _) (meet_leL m _ _)).
- exact: (le_trans (meet_leL m _ _) (meet_leR m _ _)).
- exact: meet_leR.
Qed.
Next Obligation.
move=> x y z; apply le_anti.
apply/andP; split; rewrite !joinP -?andbA; apply/and3P; split.
- exact: (le_trans (join_leL m _ _) (join_leL m _ _)).
- exact: (le_trans (join_leR m _ _) (join_leL m _ _)).
- exact: join_leR.
- exact: join_leL.
- exact: (le_trans (join_leL m _ _) (join_leR m _ _)).
- exact: (le_trans (join_leR m _ _) (join_leR m _ _)).
Qed.
Next Obligation.
apply le_anti.
apply/andP; split; first exact: meet_leL.
by rewrite meetP le_refl join_leL.
Qed.
Next Obligation.
apply le_anti.
apply/andP; split; last exact: join_leL.
by rewrite joinP le_refl meet_leL.
Qed.
Next Obligation. by rewrite eq_le meetP meet_leL le_refl. Qed.

End InfSupMixin.

Module Exports.
Coercion latticeMixin : of_ >-> Order.LatticeMixin.of_.
Notation infsupMixin := of_.
Notation InfSupMixin := Build.
End Exports.

End InfSupMixin.
Import InfSupMixin.Exports.


Reserved Notation "s '<=R' t" (at level 70, t at next level).
Reserved Notation "s '<R' t"  (at level 70, t at next level).


Fact perm_display : unit. Proof. exact: tt. Qed.


Module WeakOrder.
Section Def.

Variable (n0 : nat).
Local Notation n := n0.+1.
Implicit Type (s t u v : 'S_n).

Definition leperm s t :=
  [exists u, (t == s * u) && (length t == length s + length u)].
Definition ltperm s t := (t != s) && (leperm s t).

Local Notation "s '<=R' t" := (leperm s t).
Local Notation "s '<R' t" := (ltperm s t).

Lemma ltperm_def s t : (s <R t) = ((t != s) && (s <=R t)).
Proof. by []. Qed.

Lemma lepermP s t :
  reflect (exists2 u, t = s * u & length t = length s + length u)
          (s <=R t).
Proof.
apply (iffP existsP) => [] /= [u].
- by move/andP => [/eqP Heq /eqP Hlen]; exists u.
- by move=> /eqP Heq /eqP Hlen; exists u; apply/andP.
Qed.

Lemma leperm_length s t : s <=R t -> length s <= length t.
Proof. by move/lepermP => [u _ ->]; apply leq_addr. Qed.

Lemma leperm_lengthE s t : s <=R t -> length s = length t -> s = t.
Proof.
move/lepermP => /= [u -> ->] /eqP.
rewrite -{1}(addn0 (length s)) eqn_add2l eq_sym => /eqP/length_eq0 ->.
by rewrite mulg1.
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
move=> s t /andP [Hst Hts]; apply: (leperm_lengthE Hst).
by apply anti_leq; apply/andP; split; apply leperm_length.
Qed.

Definition perm_porderMixin :=
  LePOrderMixin ltperm_def leperm_refl leperm_anti leperm_trans.

End Def.
End WeakOrder.

Notation "x <=R y" := (@Order.le perm_display _ x y).
Notation "x <R y" := (@Order.lt perm_display _ x y).


Section Def.

Variable (n0 : nat).
Local Notation n := n0.+1.
Implicit Type (s t u v : 'S_n).

Canonical perm_porderType :=
  POrderType perm_display ('S_n) (WeakOrder.perm_porderMixin n0).

Lemma lepermP s t :
  reflect (exists2 u : 'S_n, t = s * u & length t = length s + length u)
          (s <=R t).
Proof. exact: WeakOrder.lepermP. Qed.

Lemma leperm_length s t : s <=R t -> length s <= length t.
Proof. exact: WeakOrder.leperm_length. Qed.

Lemma leperm_lengthE s t : s <=R t -> length s = length t -> s = t.
Proof. exact: WeakOrder.leperm_lengthE. Qed.

Lemma leperm1p s : (1%g : 'S__) <=R s.
Proof.
apply/lepermP; exists s; first by rewrite mul1g.
by rewrite length1 add0n.
Qed.

Lemma leperm_maxpermMl s t : (maxperm * t <= maxperm * s)%O = (s <= t)%O.
Proof.
suffices {s t} impl u v : (u <= v)%O -> (maxperm * v <= maxperm * u)%O.
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

Lemma leperm_eltrR s (i : 'I_n) :
  i < n0 -> s^-1 i < s^-1 (inord (i.+1)) -> s <=R (s * 's_i).
Proof.
move=> Hi Hnrec; apply/lepermP; exists 's_i => //.
by rewrite length_add1R // -[val i]/(val (Ordinal Hi)) length_eltr addn1.
Qed.


Lemma leperm_factorP s t :
  reflect (exists2 w : seq 'I_n0, w \is reduced &
              exists2 l : nat, t = 's_[w] & s = 's_[take l w])
          (s <=R t).
Proof.
apply (iffP (lepermP s t)) => /= [[u] ->{t} Hlen | [w] Hred [l] Ht Hs].
- exists (canword s ++ canword u).
    apply/reducedP; rewrite size_cat !size_canword -Hlen.
    by rewrite big_cat /= !canwordP.
  exists (length s).
  + by rewrite big_cat /= !canwordP.
  + by rewrite take_size_cat ?size_canword // canwordP.
- exists (\prod_(i <- drop l w) 's_i).
  + by rewrite Ht Hs -big_cat /= cat_take_drop.
  + rewrite {}Hs {}Ht (reducedP Hred).
    rewrite -{1}(cat_take_drop l w) in Hred.
    rewrite (reducedP (reduced_catl Hred)) (reducedP (reduced_catr Hred)).
    by rewrite -size_cat cat_take_drop.
Qed.

Lemma leperm_succ s t :
  s <R t -> exists2 i : 'I_n0, (s <R s * 's_i) & (s * 's_i <=R t).
Proof.
move=> /andP[sNt /leperm_factorP[w wred [l Ht Hs]]].
have : l < size w.
  by move: sNt; apply contraR; rewrite Ht Hs -leqNgt => /take_oversize ->.
case Hw : w => // [w0 wtl]; rewrite -{}Hw {wtl} => Hl.
have lens : length s = l.
  have := size_take l w; rewrite Hl => <-.
  rewrite Hs; apply/reducedP.
  by move: wred; rewrite -{1}(cat_take_drop l w) => /reduced_catl.
have eqs1 : s * 's_(nth w0 w l) = \prod_(i <- take l.+1 w) 's_i.
  by rewrite (take_nth w0 Hl) -cats1 big_cat /= big_seq1 -Hs.
have lens1 : length  (s * 's_(nth w0 w l)) = l.+1.
  rewrite -(size_takel Hl) eqs1; apply/reducedP.
  by move: wred; rewrite -{1}(cat_take_drop l.+1 w) => /reduced_catl.
exists (nth w0 w l).
- rewrite lt_neqAle; apply/andP; split.
  + by apply/negP=> /eqP/(congr1 length)/eqP; rewrite lens lens1; elim l.
  + apply/lepermP; exists ('s_(nth w0 w l)) => //.
    by rewrite lens lens1 length_eltr addn1.
- apply/lepermP; exists (\prod_(i <- drop l.+1 w) 's_i).
  + by rewrite eqs1 -big_cat cat_take_drop /= -Ht.
  + have:= wred; rewrite -{1}(cat_take_drop l.+1 w)=>/reduced_catr/reducedP->.
    rewrite lens1 size_drop subnKC // Ht.
    exact/reducedP.
Qed.


Theorem leperm_invset s t : (s <=R t) = (invset s \subset invset t).
Proof.
apply/idP/idP => [/lepermP/= [u]->{t} | H].
  rewrite -{-2}(canwordP u) -(size_canword u).
  elim/last_ind: (canword u) (canword_reduced u) => [| w i IHw].
    by rewrite big_nil /= mulg1 => _.
  rewrite size_rcons -cats1 big_cat /= big_cons big_nil mulg1.
  move/reduced_catl => Hred; rewrite -(reducedP Hred).
  move/(_ Hred): IHw; move: Hred => /reducedP <-.
  move: (\prod_(i <- w) _) => /= P IHP.
  rewrite mulgA -(addn1 (length P)) addnA -(length_eltr i) => Hlen.
  move/(_ (lengthKL Hlen)): IHP => /subset_trans; apply.
  pose il := lift ord_max i.
  have Hi : il < n0 by rewrite /il lift_max ltn_ord.
  have Hsi : 's_i = 's_il :> 'S_n by rewrite lift_max.
  rewrite Hsi invset_eltrR //; first exact: subsetU1.
  by rewrite length_descR // -{}Hsi Hlen (lengthKL Hlen) length_eltr addn1 ltnS.

have /subnKC: length s <= length t by rewrite /length subset_leq_card.
move: (length t - length s) => d Hd.
move: H; elim: d => [|d IHd] in t Hd *.
  move=> H; move: Hd; rewrite addn0 /length => /eqP.
  rewrite (subset_leqif_cards H) => /eqP/invset_inj ->.
  exact: le_refl.
rewrite subEproper=> /orP[/eqP/invset_inj->|]; first exact: le_refl.
move/properP => /= [incl ex].
have {ex} /ex_minnP [m /existsP /=[[i j]] /=] : exists n : nat,
    [exists p, [&& p \in invset t, p \notin invset s & t p.1 - t p.2 == n]].
  move: ex => [[i j]] ijt ijNs; exists (t i - t j).
  by apply/existsP => /=; exists (i, j) => /=; apply/and3P.
rewrite [in X in (X-> _ -> _)]/invset !inE /= => /and3P [/andP [iltj tjltti]].
rewrite iltj /= -leqNgt leq_eqVlt (inj_eq val_inj) (inj_eq perm_inj).
rewrite -[i == j](inj_eq val_inj) (ltn_eqF iltj) /= => siltsj /eqP eqm Hm.
have m0 : 0 < m by case: m eqm {Hm} => // /eqP; rewrite subn_eq0 leqNgt tjltti.
have Hti : t i = t j + m :> nat.
  rewrite -eqm {Hm} in m0; rewrite -eqm subnKC //.
  by apply ltnW; rewrite -subn_gt0.
have {}Hm (k l : 'I_n) :
    (k, l) \in invset t -> (k, l) \notin invset s -> m <= t k - t l.
  move=> pIt pNIs; apply Hm; apply/existsP; exists (k, l).
  by rewrite pIt pNIs eq_refl.
have {Hm m0 eqm tjltti} Heq : m = 1%N.
  have {}incl (k l : 'I_n) : k < l -> s k > s l -> t k > t l.
    by move=> kltl; move: incl => /subsetP/(_ (k, l)); rewrite !inE kltl.
  apply anti_leq; rewrite {}m0 andbT {Hd IHd}.
  rewrite leqNgt; apply/negP => Habs.
  pose k := (t^-1 (inord (t j).+1)).
  have tk : t k = (t j).+1 :> nat.
    by rewrite /k permKV inordK // ltnS (leq_trans tjltti _) // -ltnS.
  suffices []: (m <= t k - t j) \/ (m <= t i - t k).
    - by rewrite tk subSn // subnn => /(leq_trans Habs); rewrite ltnn.
    - rewrite tk; rewrite -eqm.
      case: (val (t i)) tjltti => //= u; rewrite ltnS => Hu.
      by rewrite subSS subSn // ltnn.
  case: (ltngtP k i) => [klti|iltk|/val_inj Hk]; last 1 first.
  - by move: Habs; rewrite -eqm -Hk tk subSn // ?subnn ltnn.
  - left; have kltj := ltn_trans klti iltj.
    apply: Hm; rewrite inE /= kltj /= ?tk //.
    rewrite -leqNgt; apply ltnW; apply: (leq_trans _ siltsj).
    rewrite leqNgt ltnS; apply/negP => siltsk.
    have:= incl k i klti siltsk.
    by rewrite tk ltnS leqNgt tjltti.
  have {tjltti} tkltti : t k < t i.
    rewrite tk {}Hti {eqm Hm}; case: m Habs => [|[|m]]// _.
    by rewrite !addnS !ltnS leq_addr.
  case: (ltngtP k j) => [kltj|jltk|/val_inj Hkj]; last first.
  - exfalso; move: Hkj => /(congr1 t)/(congr1 val)/=/eqP.
    by rewrite tk eqn_leq ltnn.
  - right; apply: Hm; rewrite inE /= iltk //=.
    move: incl => /(_ j k jltk)/contra; rewrite -!leqNgt => incl.
    have {}/incl : t j <= t k by rewrite tk.
    exact: leq_trans (ltnW siltsj).
  case: (ltnP (s i) (s k)) => [siltsk|sklesi].
  - right; apply: Hm; rewrite inE /= iltk //=.
    by rewrite -leqNgt; exact: ltnW.
  case: (ltnP (s k) (s j)) => [skltsj|sjlesk].
  - left; apply: Hm; rewrite inE /= kltj /= ?tk //.
    by rewrite -leqNgt; apply ltnW.
  - by have:= leq_trans siltsj (leq_trans sjlesk sklesi); rewrite ltnn.
rewrite {}Heq addn1 in Hti.
have tjn0 : t j < n0 by rewrite -ltnS -Hti.
have {Hti} Himj : (t * 's_(t j))^-1 (t j) = i.
  by rewrite invMg !permM eltrV eltrL -Hti inord_val !permK.
have Himi : (t * 's_(t j))^-1 (inord (succn (t j))) = j.
  by rewrite invMg !permM eltrV eltrR !permK.
have Hdesc : (t * 's_(t j))^-1 (t j) < (t * 's_(t j))^-1 (inord (succn (t j))).
  by rewrite Himi Himj.
have Hln : (length (t * 's_(t j))).+1 = length t.
  by rewrite -[in RHS](mulgK 's_(t j) t) eltrV [RHS]length_add1R.
have {Hd Hln} {}/IHd IHd : length s + d = length (t * 's_(t j)).
  by move: Hd; rewrite -Hln addnS => [] [].
have {Himi Himj} invsett : invset t = (i, j) |: invset (t * 's_(t j)).
  by rewrite -{1}Himi -Himj -(invset_eltrR tjn0 Hdesc) -{2}eltrV mulgK.
have {invsett} {}/IHd : invset s \subset invset (t * 's_(t j)).
  move: incl; rewrite {}invsett => /subsetP Hsubs.
  apply/subsetP => /= [[k l] H].
  move/(_ _ H): Hsubs; rewrite !inE /= => /orP [] // /eqP Heq.
  exfalso; move: H; rewrite {}Heq /invset !inE /= iltj /=.
  by rewrite ltnNge (ltnW siltsj).
move/le_trans; apply.
rewrite -{3}(mulgK 's_(t j) t) eltrV.
exact: leperm_eltrR.
Qed.

Corollary ltperm_invset s t : (s <R t) = (invset s \proper invset t).
Proof.
rewrite lt_neqAle leperm_invset properEneq; congr ((negb _) && _).
by apply/eqP/eqP => [-> | /invset_inj].
Qed.

End Def.


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
move/connectP => /= [p]; elim: p => [| p0 p IHp] /= in i Hneq *.
  by move => _ Heq; rewrite Heq eqxx in Hneq.
case: (altP (p0 =P j)) => [<- /= /andP[/AB ->] // | {}/IHp IHp].
by move=> /andP [/AB {}/trB trB {}/IHp H{}/H]; apply: trB.
Qed.

Lemma tclosure_Delta A : A \subset Delta -> tclosure A \subset Delta.
Proof.
move/tclosure_sub; apply => j k i; rewrite /= !mem_Delta.
exact: ltn_trans.
Qed.

Lemma tclosureP A : A \subset Delta -> transitive (srel (tclosure A)).
Proof.
move/tclosure_Delta => /subsetP subs.
rewrite /= => j i k /= ijA jkA.
move: (subs _ ijA) (subs _ jkA); rewrite 2!inE /= => iltj jltk.
move: iltj jltk (ltn_trans iltj jltk); rewrite !ltn_neqAle.
move=> /andP [inj _] /andP [jnk _] /andP [ink _].
move: ijA jkA; rewrite !inE /= inj ink jnk /=.
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
have : A :|: B \subset Delta.
  by rewrite subUset; apply/andP; split; apply is_invset_Delta.
move: {-1}(A :|: B) (erefl (A :|: B)) => /= AUB HAUB AUBD.
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
  move=> /connectP /=[p Hp Hk] {iltk}.
  elim: p => [|p0 p IHp] /= in i Hp Hk iltj *.
    by exfalso; have:= ltn_trans iltj jltk; rewrite Hk ltnn.
  move: Hp => /andP [ip0AB Hp]; apply /orP.
  case: (ltngtP p0 j) => [p0ltj | jltp0 | /val_inj Heq]; last 1 first.
  + by left; apply: connect1; rewrite -Heq.
  + move/(_ _ Hp Hk p0ltj): IHp => {p Hk Hp} /orP [|->]; last by right.
    by move/(connect_trans (connect1 (e := srel AUB) ip0AB)); left.
  + wlog ip0 : A B HAUB isA isB ip0AB / (i, p0) \in A.
      subst AUB; move=> Hlog; move: ip0AB; rewrite inE => /orP [] Hip0.
      * by have:= Hip0 => {}/(Hlog A B); apply; rewrite //= inE Hip0.
      * by have:= Hip0 => {}/(Hlog B A); apply; rewrite // setUC // inE Hip0.
    suffices: ((i, j) \in AUB) || ((j, p0) \in AUB).
      move/orP=> [ijAB|jp0AB]; [left|right].
      * exact: connect1.
      * by apply/connectP; exists (p0 :: p); rewrite //= jp0AB Hp.
    rewrite -HAUB !inE -!orbA [((i, j) \in B) || _]orbC -!orbA orbA.
    apply/or3P; apply Or31; apply/orP.
    move: isA => [_ _]; rewrite transitive_DeltaI1 => H.
    have /H/(_ ip0) : i < j < p0 by rewrite iltj jltp0.
    by move=> [|] -> /=; [left | right].
Qed.

Definition supperm s t : 'S_n :=
  perm_of_invset (tclosure (invset s :|: invset t)).
Definition infperm s t : 'S_n :=
  maxperm * (supperm (maxperm * s) (maxperm * t)).

Lemma invset_supperm s t :
  invset (supperm s t) = tclosure (invset s :|: invset t).
Proof.
rewrite /supperm perm_of_invsetK //.
exact: is_invset_tclosureU (invsetP _) (invsetP _).
Qed.

Lemma suppermC s t : supperm s t = supperm t s.
Proof. by apply invset_inj; rewrite !invset_supperm setUC. Qed.

Lemma suppermPr s t : s <=R (supperm s t).
Proof.
rewrite !leperm_invset; rewrite invset_supperm /tclosure.
apply/subsetP => /= [[i j] Hinv]; rewrite !inE /=.
rewrite neq_ltn (DeltaP ((subsetP (invset_Delta s)) _ Hinv)) /=.
by apply/connectP; exists [:: j]; rewrite //= inE Hinv /=.
Qed.

Lemma suppermPl s t : t <=R (supperm s t).
Proof. by rewrite suppermC; exact: suppermPr. Qed.

Lemma suppermP s t w : s <=R w -> t <=R w -> (supperm s t) <=R w.
Proof.
rewrite !leperm_invset invset_supperm => Hsw Htw; apply tclosure_sub.
- by rewrite subUset Hsw Htw.
- by move: (invsetP w) => [].
Qed.

Lemma supperm_is_sup x y z : (supperm x y <=R z) = (x <=R z) && (y <=R z).
Proof.
apply/idP/idP => [leinf | /andP [xley xlez]]; last exact: suppermP.
by apply/andP; split; apply: (le_trans _ leinf);
  [apply: suppermPr | apply: suppermPl].
Qed.
Lemma infperm_is_inf x y z : (x <=R infperm y z) = (x <=R y) && (x <=R z).
Proof.
rewrite /infperm -![x <=R _]leperm_maxpermMl.
by rewrite mulgA -{1}maxpermV mulVg mul1g supperm_is_sup.
Qed.

Definition perm_latticeMixin := InfSupMixin infperm_is_inf supperm_is_sup.
Canonical perm_latticeType := LatticeType 'S_n perm_latticeMixin.

Definition perm_bottomMixin := BottomMixin (@leperm1p n0).
Canonical perm_blatticeType := BLatticeType 'S_n perm_bottomMixin.

Definition perm_topMixin := TopMixin (@leperm_maxperm n0).
Canonical perm_tblatticeType := TBLatticeType 'S_n perm_topMixin.
Canonical perm_finLatticeType := Eval hnf in [finLatticeType of 'S_n].

Lemma bottom_perm : Order.bottom = (1 : 'S__).
Proof. by []. Qed.
Lemma top_perm : Order.top = maxperm.
Proof. by []. Qed.

Lemma invset_join s t : invset (s `|` t)%O = tclosure (invset s :|: invset t).
Proof. by rewrite /Order.join invset_supperm. Qed.

End PermutoSupInf.
