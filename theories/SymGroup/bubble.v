(** * Combi.SymGroup.Bubble : The symmetric group *)
(******************************************************************************)
(*       Copyright (C) 2014 Florent Hivert <florent.hivert@lri.fr>            *)
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
(** * 0-Hecke Monoid
***************************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun bigop finset binomial fingroup perm tuple.
From mathcomp Require Import morphism presentation.
From SsrMultinomials Require Import ssrcomplements poset freeg bigenough mpoly.

From Combi Require Import tools permuted combclass congr symgroup.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Reserved Notation "\funcomp_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \funcomp_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\funcomp_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \funcomp_ ( i  <-  r ) '/  '  F ']'").

Section BigComp.

Variable T : Type.
Variable I : Type.

Implicit Type F : I -> T -> T.

Lemma funcompA : associative (@funcomp T T T tt).
Proof. by []. Qed.

Lemma funcompfI : right_id id (@funcomp T T T tt).
Proof. by []. Qed.

Lemma funcompIf : left_id id (@funcomp T T T tt).
Proof. by []. Qed.

Canonical funcompMonoid := Monoid.Law funcompA funcompIf funcompfI.

Local Notation "\c" := (funcomp tt).

Lemma eqfun_bigr r (P : pred I) (F1 F2 : I -> T -> T) :
  (forall i, P i -> F1 i =1 F2 i) ->
  \big[\c/id]_(i <- r | P i) F1 i =1 \big[\c/id]_(i <- r | P i) F2 i.
Proof. by apply big_ind2; last exact: eq_comp. Qed.

Lemma eqfun_big r (P1 P2 : pred I) F1 F2 :
    P1 =1 P2 -> (forall i, P1 i -> F1 i =1 F2 i) ->
  \big[\c/id]_(i <- r | P1 i) F1 i =1 \big[\c/id]_(i <- r | P2 i) F2 i.
Proof. move=> H; rewrite -(eq_bigl _ _ H); exact: eqfun_bigr. Qed.

Lemma congr_eqbigfun r1 r2 (P1 P2 : pred I) F1 F2 :
    r1 = r2 -> P1 =1 P2 -> (forall i, P1 i -> F1 i =1 F2 i) ->
  \big[\c/id]_(i <- r1 | P1 i) F1 i =1 \big[\c/id]_(i <- r2 | P2 i) F2 i.
Proof. by move=> <-{r2}; exact: eqfun_big. Qed.

End BigComp.

Notation "\funcomp_ ( i <- r | P ) F" :=
  (\big[(funcomp tt)/id]_(i <- r | P%B) F).
Notation "\funcomp_ ( i <- r ) F" :=
  (\big[(funcomp tt)/id]_(i <- r ) F).


Section Bubble.

Variable n : nat.
Local Notation array := 'X_{1..n.+1}.

Local Notation "m # s" := [multinom m (s i) | i < n.+1]
  (at level 40, left associativity, format "m # s").

Lemma inord1K (i : 'I_n) : inord (n' := n) i = i :> nat.
Proof. rewrite inordK //; exact: (leq_trans (ltn_ord _)). Qed.
Lemma inord1SK (i : 'I_n) : inord (n' := n) i.+1 = i.+1 :> nat.
Proof. rewrite inordK //; exact: (leq_trans (ltn_ord _)). Qed.

Lemma eltrAi1 i (a : array) : (a#eltr n i) (inord i.+1) = a (inord i).
Proof. by rewrite mnmE /eltr tpermR. Qed.
Lemma eltrAi i (a : array) : (a#eltr n i) (inord i) = a (inord i.+1).
Proof. by rewrite mnmE /eltr tpermL. Qed.
Lemma eltrAD i j (a : array) :
  inord (n' := n) i != inord j ->
  inord (n' := n) i.+1 != inord j -> (a#eltr n i) (inord j) = a (inord j).
Proof. by move=> H1 H2; rewrite mnmE /eltr tpermD //. Qed.

Definition bubble i (a : array) : array :=
  let ai := nth 0 a i in let ai1 := nth 0 a i.+1 in
  if a (inord i) > a (inord i.+1) then a # (eltr n i)
  else a.

Import GroupScope.

Local Notation "''s_' i" := (eltr n i) (at level 8, i at level 2).
Local Notation "''s_[' w ']'" := (\prod_(i <- w) 's_i) (at level 8, w at level 2).
Local Notation "a =Br b" := (braidcongr a b) (at level 70).
Local Notation "''pi_' i" := (bubble i) (at level 8, i at level 2).
Local Notation "''pi_[' w ']'" := (\funcomp_(i <- w) 'pi_i) (at level 8, w at level 2).
Local Notation "''pi_{' s '}'" := ('pi_[canword s]) (at level 8, s at level 2).

Lemma bubbleK (i : 'I_n) : 'pi_i \o 'pi_i =1 'pi_i.
Proof.
  rewrite /bubble => a /=; apply val_inj => /=.
  case: (ssrnat.ltnP (a (inord i.+1)) (a (inord i))).
  - rewrite eltrAi1 eltrAi => /ltnW.
    by rewrite leqNgt => /negbTE ->.
  - by rewrite leqNgt => /negbTE ->.
Qed.

Lemma bubbleC i j :
  i.+1 < j < n -> 'pi_i \o 'pi_j =1 'pi_j \o 'pi_i.
Proof.
  move=> /andP [] Hij Hj.
  have Hi : i < n.
    move: Hij => /ltnW/ltn_trans; by apply.
  have Hj1i1 : inord (n' := n) j.+1 != inord i.+1.
    rewrite /eq_op /= !inordK // eq_sym ltn_eqF //.
    by rewrite ltnS; apply ltnW.
  have Hji1 : inord (n' := n) j != inord i.+1.
    rewrite /eq_op /= !inordK ?ltnS //; last exact: ltnW.
    by rewrite eq_sym ltn_eqF.
  have Hj1i : inord (n' := n) j.+1 != inord i.
    rewrite /eq_op /= !inordK ?ltnS //; last exact: ltnW.
    by rewrite eq_sym ltn_eqF // ltnS; apply ltnW; apply ltnW.
  have Hji : inord (n' := n) j != inord i.
    rewrite /eq_op /= !inordK ?ltnS //; try exact: ltnW.
    by rewrite eq_sym ltn_eqF //; by apply ltnW.
  rewrite /bubble => a /=.
  case: (ssrnat.ltnP (a (inord j.+1)) (a (inord j))) => Haj.
  - rewrite !eltrAD //.
    rewrite eq_sym in Hj1i1; rewrite eq_sym in Hj1i.
    rewrite eq_sym in Hji1; rewrite eq_sym in Hji.
    case: (ssrnat.ltnP (a (inord i.+1)) (a (inord i))) => Hai.
    + rewrite !eltrAD // Haj.
      rewrite mnmP => k.
      rewrite !mnmE -!permM eltr_comm //.
      by rewrite Hij Hj.
    + by rewrite Haj.
  - rewrite eq_sym in Hj1i1; rewrite eq_sym in Hj1i.
    rewrite eq_sym in Hji1; rewrite eq_sym in Hji.
    case: (ssrnat.ltnP (a (inord i.+1)) (a (inord i))) => Hai.
    + rewrite !eltrAD //.
      move: Haj; by rewrite leqNgt => /negbTE ->.
    + move: Haj; by rewrite leqNgt => /negbTE ->.
Qed.

Lemma bubbleBr i :
  i.+1 < n -> 'pi_i \o 'pi_i.+1 \o 'pi_i =1 'pi_i.+1 \o 'pi_i \o 'pi_i.+1.
Proof.
  move=> Hi; rewrite /bubble => a /=.
  set oi := inord i; set oi1 := inord i.+1; set oi2 := inord i.+2.
  have Hoii1 : oi != oi1.
    rewrite /eq_op /= !inordK ?trivSimpl //; apply ltnW => //; exact: ltnW.
  have Hoii2 : oi != oi2.
    rewrite /eq_op /= !inordK ?trivSimpl //; apply ltnW => //; exact: ltnW.
  have Hoi1i2 : oi1 != oi2.
    rewrite /eq_op /= !inordK ?trivSimpl //; apply ltnW => //; exact: ltnW.
  case: (ssrnat.ltnP (a oi1) (a oi)) => Hi1i.
  - rewrite eltrAD // eltrAi1 -/oi -/oi2.
    case: (ssrnat.ltnP (a oi2) (a oi1)) => Hi2i1.
    + rewrite !eltrAi eltrAD; try by rewrite eq_sym.
      rewrite (ltn_trans Hi2i1 Hi1i).
      rewrite mnmE tpermL eltrAD //.
      rewrite mnmE tpermD; try by rewrite eq_sym.
      rewrite eltrAi Hi2i1.
      rewrite mnmE tpermD // eltrAi1.
      rewrite mnmE tpermR //.
      rewrite eltrAD; try by rewrite eq_sym.
      rewrite Hi1i mnmP => k.
      by rewrite !mnmE -!permM !mulgA eltr_braid.
    + case: (ssrnat.ltnP (a oi2) (a oi)) => Hi2i.
      * rewrite Hi1i.
        rewrite mnmE tpermL eltrAD //.
        rewrite mnmE tpermD; try by rewrite eq_sym.
        rewrite eltrAi eltrAi1 Hi2i.
        by move: Hi2i1; rewrite leqNgt => /negbTE ->.
      * rewrite Hi1i eltrAi eltrAi1.
        have:= ltnW Hi1i; rewrite leqNgt => /negbTE ->.
        rewrite eltrAD //.
        by move: Hi2i; rewrite leqNgt => /negbTE ->.
  - case: (ssrnat.ltnP (a oi2) (a oi1)) => Hi2i1.
    + rewrite eltrAi eltrAD; try by rewrite eq_sym.
      case: (ssrnat.ltnP (a oi2) (a oi)) => Hi2i.
      * rewrite mnmE tpermD // eltrAi1 //.
        rewrite mnmE tpermR eltrAD; try by rewrite eq_sym.
        by move: Hi1i; rewrite leqNgt => /negbTE ->.
      * rewrite eltrAi1 eltrAi.
        by have:= ltnW Hi2i1; rewrite leqNgt => /negbTE ->.
    + have:= Hi1i; rewrite leqNgt => /negbTE ->.
      by move: Hi2i1; rewrite leqNgt => /negbTE ->.
Qed.


Lemma bubble_braid_congr (u v : seq 'I_n) : u =Br v -> 'pi_[u] =1 'pi_[v].
Proof.
  move: v; apply: gencongr_ind; first by [].
  move=> a b1 c b2 Heq Hrule x; rewrite {}Heq.
  rewrite !big_cat /=; apply eq_comp => // {x}.
  move: Hrule; rewrite /braidrule /= !mem_cat => /orP [].
  - move/braid_abaP => [] i [] j [] Hij -> ->.
    rewrite !big_cons !big_nil /=.
    move/orP: Hij => [] /eqP H.
    + rewrite -H !funcompA !funcompfI => x; by rewrite bubbleBr // H.
    + rewrite -H !funcompA !funcompfI => x; by rewrite bubbleBr // H.
  - move/braidCP => [] i [] j [] Hij -> ->.
    rewrite !big_cons !big_nil /=.
    move/orP: Hij => [] H.
    + rewrite !funcompA !funcompfI => x; by rewrite bubbleC // H /=.
    + rewrite !funcompA !funcompfI => x; by rewrite -bubbleC // H /=.
Qed.

Corollary bubble_red (u : seq 'I_n) : u \is reduced -> 'pi_[u] =1 'pi_{ 's_[u] }.
Proof. by move/braid_to_canword/bubble_braid_congr. Qed.

Corollary reduced_bubbleM (s t : 'S_(n.+1)) :
  length (s * t) = length s + length t -> 'pi_{ s } \o 'pi_{ t } =1 'pi_{ s * t }.
Proof.
  rewrite -big_cat /= => /reducedM/bubble_red => H i.
  by rewrite H big_cat /= !canwordP.
Qed.

Corollary bubble_perm (u : seq 'I_n) : exists s : 'S_(n.+1), 'pi_[u] =1 'pi_{ s }.
Proof.
  move Hsz : {2}(size u) => l.
  elim: l u Hsz => [| l IHl] u Hsz.
    move: Hsz => /eqP/nilP ->.
    exists 1; by rewrite canword1.
  case (boolP (u \is reduced)).
    by move=> Hu; exists 's_[u]; exact: bubble_red.
  move/reduceP => [] v [] r [] HBr.
  move/reducesP => [] a [] i [] b [] Hv Hr.
  have {IHl Hsz} /IHl : size (a ++ [:: i] ++ b) = l.
    move: Hsz; rewrite (size_braid HBr) Hv !size_cat /= !addnS => /eqP.
    by rewrite eqSS => /eqP.
  move=> [] s Hred; exists s => x.
  rewrite -{}Hred (bubble_braid_congr HBr) {}Hv {HBr u v Hr r}.
  rewrite !big_cat big_cons big_seq1.
  apply eq_comp => //=; apply eq_comp => //=.
  exact: bubbleK.
Qed.


End Bubble.
