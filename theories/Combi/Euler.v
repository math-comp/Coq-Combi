(** * Combi.Combi.Euler : Euler integer partitions identity *)
(******************************************************************************)
(*        Copyright (C) 2024- Florent Hivert <florent.hivert@lri.fr>          *)
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
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly binomial rat ssrnum.
From Combi Require Import tfps auxresults.

Require Import sorted partition.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import LeqGeqOrder.


Section ConsPart.

Variables n : nat.

Definition cons_intpartn a (sh : 'P_n) := rowpartn a.+1 +|+ sh.

Lemma val_cons_intpartn z a (sh : 'P_n) :
  head z sh <= a.+1 -> val (cons_intpartn a sh) = a.+1 :: val sh.
Proof.
rewrite /cons_intpartn => Hsh; rewrite /= -cat1s.
rewrite rowpartnSE sorted_merge // cat1s /=.
case: sh Hsh => /= sh /andP[_] /[!is_part_sortedE] /andP[Hsort _].
by case: sh Hsort => [|b l]//= -> ->.
Qed.

Lemma cons_intpartnK a (sh : 'P_(a.+1 + n)) :
  head 0 sh = a.+1 ->
  exists2 shb : 'P_n, cons_intpartn a shb = sh & head 0 shb <= a.+1.
Proof.
case: sh => [[|s0 sh] //= Hsh] Hs0; subst s0.
have partsh : is_part_of_n n sh.
  rewrite /is_part_of_n /= -(eqn_add2l a.+1).
  by move/and3P: Hsh => [/eqP <- _ ->]; rewrite andbT.
exists (IntPartN partsh).
  apply val_inj; rewrite (val_cons_intpartn (z := 0)) //= {partsh}.
  move: Hsh => /and3P[_ /[swap] _].
  by case: sh.
by move/and3P: Hsh => [/= _]; case: sh {partsh}.
Qed.

End ConsPart.


Section Euler.

Definition cBSpart n b := #|[set sh : 'P_n | uniq sh & head 0 sh <= b]|.
Definition cSpart n := #|[set sh : 'P_n | uniq sh]|.


Lemma cBSpart_rec n b :
  (n >= b.+1)%N -> cBSpart n b.+1 = cBSpart n b + cBSpart (n - b.+1) b.
Proof.
move=> gt_n_b1.
pose consb1 := fun sh => cast_intpartn (subnKC gt_n_b1) (cons_intpartn b sh).
have val_consb1 (sh : 'P_(n - b.+1)) :
    head 0 sh <= b.+1 -> val (consb1 sh) = b.+1 :: val sh.
  by move=> H; rewrite /consb1 !cast_intpartnE !(val_cons_intpartn (z := 0)).
rewrite /cBSpart -(card_in_imset (f := consb1)); first last.
  move=> /= sh1 sh2; rewrite !inE => /andP[_ Hsh1] /andP[_ Hsh2].
  move=> /(congr1 val) /=; rewrite !val_consb1 /= => [[] | |]; try exact: ltnW.
  exact: val_inj.
suff -> : [set consb1 x | x : 'P_(n - b.+1) & uniq x && (head 0 x <= b)]
          = [set sh  : 'P_n | uniq sh && (head 0 sh == b.+1) ].
  rewrite -cardsUI [_ :&: _](_ : _ = set0) ?cards0 ?addn0; first last.
    apply/eqP; rewrite -subset0; apply/subsetP => /= sh.
    rewrite !inE => /andP[/[swap]] /andP[-> /eqP ->].
    by rewrite ltnn.
  congr #|pred_of_set _|; apply/setP => sh /[!inE].
  case: (boolP (uniq sh)) => [Huniq|] //=.
  by rewrite leq_eqVlt ltnS orbC.
apply/setP => /= sh; rewrite !inE /=.
apply/imsetP/idP => [[/= shb /[!inE] /andP[Huniq Hhead ->{sh}] ] |] /=.
  rewrite val_consb1 /=; last exact: ltnW.
  rewrite eqxx /= Huniq !andbT.
  apply/negP => /(part_leq_head (intpartnP shb)).
  by rewrite ltnNge Hhead.
have <- /= := cast_intpartnE (esym (subnKC gt_n_b1)) sh.
move/andP => [Huniq /eqP Hhead].
have [tl eqtl headtl] := cons_intpartnK Hhead.
exists tl; last by rewrite /consb1 {}eqtl cast_intpartnKV.
move: Huniq Hhead; rewrite inE !cast_intpartnE /= => Huniq _.
move/(congr1 val): eqtl.
rewrite (val_cons_intpartn (z := 0)) // cast_intpartnE /= => eqsh.
move: Huniq; rewrite -{sh}eqsh => /= => /andP [b1notin -> /=].
rewrite -ltnS ltn_neqAle {}headtl andbT eq_sym.
case: tl b1notin => [[|s0 s] //= _].
by rewrite inE negb_or => /andP[].
Qed.

Lemma cBSpart_leq n b :
  (n <= b)%N -> cBSpart n b.+1 = cBSpart n b.
Proof.
rewrite /cBSpart => le_n_b.
congr #|pred_of_set _|; apply/setP => /= sh /[!inE]; congr andb.
have := leq_head_sumn sh; rewrite sumn_intpartn => lt_head.
by rewrite !(leq_trans lt_head) // ltnW.
Qed.

Lemma cBSpartE n b : (n <= b)%N -> cBSpart n b = cSpart n.
Proof.
rewrite /cBSpart /cSpart => le_n_b.
congr #|pred_of_set _|; apply/setP => /= sh /[!inE].
have := leq_head_sumn sh; rewrite sumn_intpartn => lt_head.
by rewrite !(leq_trans lt_head) // andbT.
Qed.


Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope tfps_scope.

Lemma sg_strict_part_bound n b :
  [tfps i => (cBSpart i b)%:R] =
    \prod_(1 <= i < b.+1) (1 + \X ^+ i) :> {tfps rat n}.
Proof.
elim: b => [| b IHb].
  rewrite big_geq //; apply/tfpsP => i le_i_n.
  rewrite coeft1 coef_tfps_of_fun le_i_n.
  case: i {le_i_n} => [| i].
    rewrite /cBSpart [[set sh : _ | _]](_ : _ = [set rowpartn 0]); first last.
      by apply/setP => /= sh; rewrite !inE intpartn0 /= eqxx rowpartn0E.
    by rewrite cards1 eqxx.
  rewrite /cBSpart [[set sh : _ | _]](_ : _ = set0); first last.
    apply/setP => /= [sh] /=; rewrite !inE.
    apply/negbTE; rewrite negb_and; apply/orP; right.
    case: sh => /= [[// | s0 sh]] /andP[_ /part_head_non0 /=].
    by rewrite leqn0 => /negbTE ->.
  by rewrite cards0 eqn0Ngt.
rewrite big_nat_recr //= -{}IHb; apply/tfpsP => i le_i_n.
rewrite mulrDr mulr1 !coeft_simpl le_i_n !coef_tfps_of_fun le_i_n.
case: ltnP => [lt_i_b1 | lt_b_i].
  by rewrite cBSpart_leq ?addr0.
rewrite cBSpart_rec // natrD; congr (_ + _).
by rewrite (leq_trans _ le_i_n) ?leq_subr.
Qed.

Lemma sg_strict_part n :
  [tfps i => (cSpart i)%:R] =
    \prod_(1 <= i < n.+1) (1 + \X ^+ i) :> {tfps rat n}.
Proof.
rewrite -sg_strict_part_bound; apply/tfpsP => i le_i_n.
by rewrite !coef_tfps_of_fun le_i_n cBSpartE.
Qed.


Implicit Type (sh : seq nat).

Variable n : nat.

Definition cSP n := #|[set sh : 'P_n | uniq sh]|.
Definition FSP : {tfps rat n} := [tfps i => (cSP i)%:R].

Definition cOP n := #|[set sh : 'P_n | all odd sh]|.
Definition FOP : {tfps rat n} := [tfps i => (cOP i)%:R].


Variable (R : ringType) (n : nat).
Variable f : {tfps R 3}.


Theorem Euler_partition n :
  #|[set sh : 'P_n | uniq sh]| = #|[set sh : 'P_n | all odd sh]|.


End.
