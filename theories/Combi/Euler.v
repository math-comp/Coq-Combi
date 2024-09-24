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
From mathcomp Require Import all_ssreflect ssralg ssrint.
From Combi Require Import tfps auxresults.

Require Import tools sorted partition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section ConsPart.

Variables n : nat.

Definition cons_intpartn a (sh : 'P_n) := rowpartn a.+1 +|+ sh.

Lemma val_cons_intpartn z a (sh : 'P_n) :
  head z sh <= a.+1 -> val (cons_intpartn a sh) = a.+1 :: val sh.
Proof.
rewrite /cons_intpartn => Hsh; rewrite /= -cat1s.
rewrite rowpartnSE (sorted_merge LeqGeqOrder.geq_trans) // cat1s /=.
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

Definition cBOpart n b := #|[set sh : 'P_n | all odd sh & head 0 sh <= b]|.
Definition cOpart n := #|[set sh : 'P_n | all odd sh]|.

Lemma cBSpart_rec n b :
  (n >= b.+1)%N -> cBSpart n b.+1 = cBSpart n b + cBSpart (n - b.+1) b.
Proof.
move=> lt_b_n.
pose consb1 := fun sh => cast_intpartn (subnKC lt_b_n) (cons_intpartn b sh).
have val_consb1 (sh : 'P_(n - b.+1)) :
    head 0 sh <= b.+1 -> val (consb1 sh) = b.+1 :: val sh.
  by move=> H; rewrite /consb1 !cast_intpartnE !(val_cons_intpartn (z := 0)).
rewrite /cBSpart -(card_in_imset (f := consb1)); first last.
  move=> /= sh1 sh2; rewrite !inE => /andP[_ Hsh1] /andP[_ Hsh2].
  move=> /(congr1 val) /=; rewrite !val_consb1 /= => [[] | |]; try exact: ltnW.
  exact: val_inj.
suff -> : [set consb1 x | x : 'P_(n - b.+1) & uniq x && (head 0 x <= b)]
          = [set sh  : 'P_n | uniq sh && (head 0 sh == b.+1)].
  rewrite -cardsUI [_ :&: _](_ : _ = set0) ?cards0 ?addn0; first last.
    apply/eqP; rewrite -subset0; apply/subsetP => /= sh.
    rewrite !inE => /andP[/[swap]] /andP[-> /eqP ->].
    by rewrite ltnn.
  congr #|pred_of_set _|; apply/setP => /= sh /[!inE].
  case: (boolP (uniq sh)) => [Huniq|] //=.
  by rewrite leq_eqVlt ltnS orbC.
apply/setP => /= sh; rewrite !inE /=.
apply/imsetP/idP => [[/= shb /[!inE] /andP[Huniq Hhead ->{sh}] ] |] /=.
  rewrite val_consb1 /=; last exact: ltnW.
  rewrite eqxx /= Huniq !andbT.
  apply/negP => /(part_leq_head (intpartnP shb)).
  by rewrite ltnNge Hhead.
have <- /= := cast_intpartnE (esym (subnKC lt_b_n)) sh.
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


Lemma cBOpart_odd_rec n b :
  odd b -> (n >= b)%N -> cBOpart n b = cBOpart n b.-2 + cBOpart (n - b) b.
Proof.
case: b => [//| b] /= nodd_b lt_b_n.
pose consb1 := fun sh => cast_intpartn (subnKC lt_b_n) (cons_intpartn b sh).
have val_consb1 (sh : 'P_(n - b.+1)) :
    head 0 sh <= b.+1 -> val (consb1 sh) = b.+1 :: val sh.
  by move=> H; rewrite /consb1 !cast_intpartnE !(val_cons_intpartn (z := 0)).
rewrite /cBOpart -(card_in_imset (f := consb1)); first last.
  move=> /= sh1 sh2; rewrite !inE => /andP[_ Hsh1] /andP[_ Hsh2].
  move=> /(congr1 val) /=; rewrite !val_consb1 /= => [[] | |] //=.
  exact: val_inj.
suff -> : [set consb1 x | x : 'P_(n - b.+1) & all odd x && (head 0 x <= b.+1)]
          = [set sh  : 'P_n | all odd sh && (head 0 sh == b.+1)].
  rewrite -cardsUI [_ :&: _](_ : _ = set0) ?cards0 ?addn0; first last.
    apply/eqP; rewrite -subset0; apply/subsetP => /= sh.
    rewrite !inE => /andP[/[swap]] /andP[-> /eqP ->] /=.
    by rewrite ltnNge leq_pred.
  congr #|pred_of_set _|; apply/setP => /= sh /[!inE].
  case: allP => //=.
  case: sh => [[| s0 sh]] //= _ Hodd.
  have {}/Hodd Hodd : s0 \in s0 :: sh by rewrite inE eqxx.
  case: s0 Hodd => //= s0 /negbTE nodd_s0.
  rewrite ltn_predRL leq_eqVlt orbC; congr (_ || _).
  rewrite ltnS leq_eqVlt.
  suff /negbTE -> : s0.+1 != b by [].
  apply/negP => /eqP/(congr1 odd) /=.
  by rewrite (negbTE nodd_b) nodd_s0.
apply/setP => /= sh; rewrite !inE /=.
apply/imsetP/idP => [[/= shb /[!inE] /andP[Hodd Hhead ->{sh}] ] |] /=.
  by rewrite val_consb1 //= nodd_b /= Hodd /=.
have <- /= := cast_intpartnE (esym (subnKC lt_b_n)) sh.
move/andP => [Huniq /eqP Hhead].
have [tl eqtl headtl] := cons_intpartnK Hhead.
exists tl; last by rewrite /consb1 {}eqtl cast_intpartnKV.
move: Huniq Hhead; rewrite inE !cast_intpartnE /= headtl andbT => Hodd _.
move/(congr1 val): eqtl.
rewrite (val_cons_intpartn (z := 0)) // cast_intpartnE /= => eqsh.
by move: Hodd; rewrite -{sh}eqsh => /= => /andP[].
Qed.

Lemma cBOpart_even_rec n b :
  ~~ odd b -> cBOpart n b = cBOpart n b.-1.
Proof.
case: b => //= b; rewrite negbK /cBOpart => odd_b.
congr #|pred_of_set _|; apply/setP => /= sh /[!inE].
case: allP => //=.
case: sh => [[| s0 sh]] //= _ Hodd.
have {}/Hodd Hodd : s0 \in s0 :: sh by rewrite inE eqxx.
case: s0 Hodd => //= s0 /negbTE nodd_s0.
rewrite leq_eqVlt ltnS eqSS.
suff /negbTE -> : s0 != b by [].
apply/negP => /eqP/(congr1 odd) /=.
by rewrite odd_b nodd_s0.
Qed.

Lemma cBOpart_leq n b :
  (n <= b)%N -> cBOpart n b.+1 = cBOpart n b.
Proof.
rewrite /cBOpart => le_n_b.
congr #|pred_of_set _|; apply/setP => /= sh /[!inE]; congr andb.
have := leq_head_sumn sh; rewrite sumn_intpartn => lt_head.
by rewrite !(leq_trans lt_head) // ltnW.
Qed.

Lemma cBOpartE n b : (n <= b)%N -> cBOpart n b = cOpart n.
Proof.
rewrite /cBOpart /cSpart => le_n_b.
congr #|pred_of_set _|; apply/setP => /= sh /[!inE].
have := leq_head_sumn sh; rewrite sumn_intpartn => lt_head.
by rewrite !(leq_trans lt_head) // andbT.
Qed.


Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope tfps_scope.

Lemma sg_strict_part_bound n b :
  [tfps i => (cBSpart i b)%:R] =
    \prod_(1 <= i < b.+1) (1 + \X ^+ i) :> {tfps int n}.
Proof.
elim: b => [| b IHb].
  rewrite big_geq //; apply/tfpsP => i le_i_n.
  rewrite coeft1 coef_tfps_of_fun le_i_n.
  case: i {le_i_n} => [| i].
    rewrite /cBSpart [[set sh : _ | _]](_ : _ = [set rowpartn 0]); first last.
      by apply/setP => /= sh; rewrite !inE intpartn0 /= eqxx rowpartn0E.
    by rewrite cards1 eqxx.
  rewrite /cBSpart [[set sh : _ | _]](_ : _ = set0).
    by rewrite cards0 eqn0Ngt.
  apply/setP => /= [sh] /=; rewrite !inE.
  apply/negbTE; rewrite negb_and; apply/orP; right.
  case: sh => /= [[// | s0 sh]] /andP[_ /part_head_non0 /=].
  by rewrite leqn0 => /negbTE ->.
rewrite big_nat_recr //= -{}IHb; apply/tfpsP => i le_i_n.
rewrite mulrDr mulr1 !coeft_simpl le_i_n !coef_tfps_of_fun le_i_n.
case: ltnP => [lt_i_b1 | lt_b_i].
  by rewrite cBSpart_leq ?addr0.
rewrite cBSpart_rec // natrD; congr (_ + _).
by rewrite (leq_trans _ le_i_n) ?leq_subr.
Qed.

Lemma sg_strict_part n :
  [tfps i => (cSpart i)%:R] =
    \prod_(1 <= i < n.+1) (1 + \X ^+ i) :> {tfps int n}.
Proof.
rewrite -sg_strict_part_bound; apply/tfpsP => i le_i_n.
by rewrite !coef_tfps_of_fun le_i_n cBSpartE.
Qed.


Lemma sg_odd_part_bound n b :
  [tfps i => (cBOpart i b)%:R] =
    \prod_(1 <= i < b.+1 | odd i) (1 - \X ^+ i)^-1 :> {tfps int n}.
Proof.
elim: b => [| b IHb].
  rewrite big_geq //; apply/tfpsP => i le_i_n.
  rewrite coeft1 coef_tfps_of_fun le_i_n.
  case: i {le_i_n} => [| i].
    rewrite /cBOpart [[set sh : _ | _]](_ : _ = [set rowpartn 0]); first last.
      by apply/setP => /= sh; rewrite !inE intpartn0 /= eqxx rowpartn0E.
    by rewrite cards1 eqxx.
  rewrite /cBOpart [[set sh : _ | _]](_ : _ = set0).
    by rewrite cards0 eqn0Ngt.
  apply/setP => /= [sh] /=; rewrite !inE.
  apply/negbTE; rewrite negb_and; apply/orP; right.
  case: sh => /= [[// | s0 sh]] /andP[_ /part_head_non0 /=].
  by rewrite leqn0 => /negbTE ->.
rewrite big_mkcond big_nat_recr //= -big_mkcond /= -{}IHb.
case: (boolP (odd b)) => [odd_b | nodd_b] /=.
  rewrite mulr1; apply/tfpsP => i le_i_n.
  by rewrite !coef_tfps_of_fun {}le_i_n cBOpart_even_rec //= odd_b.
rewrite -[LHS]divr1; apply/eqP; rewrite eq_divr ?unitr1 //; first last.
  by rewrite unit_tfpsE !coeft_simpl eqxx /= subr0.
rewrite mulrBr !mulr1 subr_eq; apply/eqP/tfpsP => i le_i_n.
rewrite !coeft_simpl !coef_tfps_of_fun le_i_n ltnS.
case: leqP => [le_i_b | lt_b_i].
  rewrite addr0 [in RHS]cBOpart_even_rec //=.
  by rewrite cBOpart_leq // cBOpart_even_rec.
rewrite (leq_trans (leq_subr _ _) le_i_n) cBOpart_odd_rec //=.
rewrite natrD; congr (_ + _).
by rewrite [in RHS]cBOpart_even_rec.
Qed.

Lemma sg_odd_part n :
  [tfps i => (cOpart i)%:R] =
    \prod_(1 <= i < n.+1 | odd i) (1 - \X ^+ i)^-1 :> {tfps int n}.
Proof.
rewrite -sg_odd_part_bound; apply/tfpsP => i le_i_n.
by rewrite !coef_tfps_of_fun le_i_n cBOpartE.
Qed.

Theorem Euler_identity n :
  \prod_(1 <= i < n.+1) (1 + \X ^+ i)
  = \prod_(1 <= i < n.+1 | odd i) (1 - \X ^+ i)^-1 :> {tfps int n}.
Proof.
have unit_tfps1 := unitr1 {tfps int n}.
have unit_1X i : (1 - \X ^+ i.+1) \is a (@GRing.unit {tfps int n}).
  by rewrite unit_tfpsE !coeft_simpl eqxx /= subr0.
have unit_prod P :
    \prod_(1 <= i < n.+1 | P i) (1 - \X ^+ i) \is a (@GRing.unit {tfps int n}).
  by rewrite big_add1; apply: rpred_prod => i _ /=.
rewrite -[RHS](divrK (unit_prod (fun i => ~~ odd i))) prodrV /=; last by case.
rewrite {unit_1X} -[X in _ = X * _]invrM // [X in X^-1]mulrC.
have:= erefl (\prod_(1 <= i < n.+1) (1 - \X ^+ i) : {tfps int n}).
rewrite {1}(bigID odd) /= => ->; rewrite mulrC.
rewrite -[LHS]divr1; apply/eqP; rewrite eq_divr //.
rewrite -big_split /=; apply/eqP {unit_prod unit_tfps1}.
under eq_bigr => i _.
  rewrite !(mulrDl, mulrDr, mul1r, mulr1).
  by rewrite addrA subrK mulrN -exprD addnn over.
rewrite /= (bigID (fun i => i.*2 < n.+1)%N) /=.
rewrite [X in _ * X]big1 ?mulr1; first last.
  move=> i; rewrite -ltnNge => lt_n_i2; apply/tfpsP => k le_k_n.
  rewrite !coeft_simpl le_k_n /=.
  have /ltn_eqF -> := leq_ltn_trans le_k_n lt_n_i2.
  by rewrite subr0.
rewrite [LHS](reindex_big_double (fun i => i < n.+1) (fun i => 1 - \X ^+ i)).
rewrite -big_nat_widen; last by rewrite ltnS -addnn leq_addr.
rewrite -addnn addn1.
by case: n => [|n]; [rewrite big_geq | rewrite [RHS]big_ltn_cond].
Qed.

Corollary Euler_strict_odd_partition n :
  #|[set sh : 'P_n | uniq sh]| = #|[set sh : 'P_n | all odd sh]|.
Proof.
have /(congr1 (coeftfps n)) /= := Euler_identity n.
rewrite -sg_odd_part -sg_strict_part !coef_tfps_of_fun leqnn => /eqP.
by rewrite !natz eqz_nat => /eqP.
Qed.

End Euler.

