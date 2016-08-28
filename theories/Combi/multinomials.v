(** * Combi.Combi.multinomials : Multinomial coefficients *)
(******************************************************************************)
(*       Copyright (C) 2016 Florent Hivert <florent.hivert@lri.fr>            *)
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
(** * Multinomial coefficients

******)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import tuple bigop path div finset.
From mathcomp Require Import perm fingroup action gproduct.
Require Import tools combclass sorted partition composition permuted.
Require Import permcomp cycles cycletype symgroup.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section ActOnTuple.

Variables (T : countType) (n : nat) (w : n.-tuple T).
Implicit Type (t : permuted w).

Let wp := (Permuted (perm_eq_refl w)).

Lemma perm_eq_act_tuple t (s : 'S_n) :
  perm_eq w [tuple tnth t (s^-1 i) | i < n].
Proof.
  apply: (perm_eq_trans (permutedP t)).
  by rewrite /= perm_eq_sym; apply/tuple_perm_eqP; exists s^-1.
Qed.
Definition permutedact t s := Permuted (perm_eq_act_tuple t s).

Local Notation "t # s" := (permutedact t s)
  (at level 40, left associativity, format "t # s").

Lemma permutedact_is_action : is_action 'SG_n permutedact.
Proof.
split.
- move=> /= s t1 t2 Heq; apply val_inj; apply eq_from_tnth => i.
  move: Heq => /(congr1 (fun t => tnth t (s i))).
  by rewrite !tnth_mktuple permK.
- move=> t /= s1 s2 _ _; apply val_inj; apply eq_from_tnth => /= i.
  by rewrite !tnth_mktuple invMg permM.
Qed.
Canonical permuted_action := Action permutedact_is_action.
Local Notation pact := permuted_action.

Lemma permuted_action_trans :
  [transitive 'SG_n, on [set: permuted w] | pact].
Proof.
apply/imsetP; exists (Permuted (perm_eq_refl w)); first by [].
apply/setP => /= t; rewrite !inE; apply/esym/orbitP => /=.
have:= permutedP t => /tuple_perm_eqP [s /val_inj Hs].
exists s; first by rewrite inE.
apply val_inj => /=; apply eq_from_tnth => /= i.
by rewrite {1}Hs !tnth_mktuple permKV.
Qed.

Lemma stab_tuple_prod :
  'C[wp | pact] =
  (\prod_(x : seq_sub w) perm_ong_group [set i : 'I_n | tnth w i == val x])%G.
Proof.
have Htriv : trivIset [set [set i : 'I_n | tnth w i == val x] | x : seq_sub w].
  apply/trivIsetP => /= X Y.
  move=> /imsetP [/= [x Hx _ /= ->{X}]].
  move=> /imsetP [/= [y Hy _ /= ->{Y}]] Hneq.
  rewrite -setI_eq0; apply/eqP/setP => /= i.
  rewrite !inE; apply (introF idP) => /andP [/eqP ->] /eqP Hxy.
  by move: Hneq; rewrite Hxy eq_refl.
apply/eqP; rewrite bigprodGE eqEsubset; apply/andP; split.
- apply/subsetP => /= s.
  move/astabP/(_ wp); rewrite inE eq_refl => /(_ isT) Ht.
  rewrite -(perm_decE (s := s) Htriv); first last.
  + apply/astabP => /= CS /imsetP [/= x _ ->{CS}].
    apply/astab1P; rewrite astab1_set.
    rewrite !inE /=; apply/subsetP => j.
    rewrite !inE => /eqP <-.
    by rewrite -{1}[w]/(val wp) -Ht tnth_mktuple permK.
  + apply/subsetP => /= i _; apply/bigcupP => /=.
    exists [set i0 | tnth w i0 == tnth w i]; last by rewrite inE.
    by apply/imsetP => /=; exists (SeqSub (mem_tnth i w)) => //=.
  apply group_prod => /= u /imsetP [/= X].
  move=> /imsetP [x Hx ->{X} ->{u}]; apply/mem_gen.
  apply/bigcupP; exists x => //.
  by rewrite inE; exact: restr_perm_on.
- rewrite gen_subG; apply/subsetP => /= s /bigcupP [/= x _] Hs.
  rewrite !inE /=; apply/subsetP => j; rewrite !inE => /eqP ->{j}.
  apply/eqP/val_inj/eq_from_tnth => /= i.
  rewrite tnth_mktuple.
  case: (boolP (tnth w i == val x)) => Hl0.
  + move: Hs; rewrite inE => /im_perm_on/setP/(_ i).
    rewrite !inE Hl0 => /imsetP [/= j].
    rewrite inE => /eqP H {1}->.
    by rewrite (eqP Hl0) permK.
  + move: Hs => /groupVr; rewrite inE /= => /out_perm -> //.
    by rewrite inE.
Qed.

Lemma stab_tuple_dprod :
  'C[wp | pact] =
  \big[dprod/1]_(x : seq_sub w) perm_ong [set i : 'I_n | tnth w i == val x].
Proof.
rewrite stab_tuple_prod; apply/esym/eqP/bigdprodYP => x /= _.
apply/subsetP => /= s; rewrite !inE negb_and negbK => Ht.
have {Ht} : s \in perm_ong [set i | tnth w i != val x].
  move: Ht; rewrite bigprodGE => /gen_prodgP [u [/= f Hf ->{s}]].
  apply group_prod => j _; move/(_ j): Hf => /bigcupP [k Hk].
  rewrite !inE /perm_on => /subset_trans; apply.
  by apply/subsetP => C; rewrite !inE => /eqP ->.
rewrite inE => on_neqi; apply/andP; split.
- case: (altP (s =P 1)) => //=; apply contra => on_eqi.
  apply/eqP/permP => /= i; rewrite perm1.
  case: (boolP (tnth w i == val x)) => [HC | /negbTE HC].
  + by rewrite (out_perm on_neqi) // !inE HC.
  + by rewrite (out_perm on_eqi) // !inE HC.
- apply/centP => /= u; move: on_neqi.
  rewrite inE !support_perm_on -[support u \subset _]setCS => on_neqi on_eqi.
  apply support_disjointC; rewrite disjoints_subset.
  apply: (subset_trans on_neqi); apply: (subset_trans _ on_eqi).
  by apply/subsetP => X; rewrite !inE.
Qed.


Lemma card_stab_ipcycles :
  #|'C[wp | pact]| = (\prod_(x : seq_sub w) (count_mem (val x) w)`!)%N.
Proof using.
rewrite -(bigdprod_card (esym stab_tuple_dprod)).
apply eq_bigr => [[i _]] _ /=.
rewrite card_perm_ong; congr (_)`!.
rewrite -map_tnth_enum.
rewrite cardE /enum_mem size_filter /= count_map count_filter.
by apply eq_count => X; rewrite !inE andbC.
Qed.

Lemma card_permuted_prodE :
  (#|[set: permuted w]| * \prod_(x : seq_sub w) (count_mem (val x) w)`!)%N = n`!.
Proof.
rewrite -card_Sn -card_stab_ipcycles.
rewrite -(atransPin (subxx _) permuted_action_trans (x := wp)) ?inE //.
by rewrite -cardsT /= -(card_orbit_in_stab pact wp (subxx _)) /= setTI.
Qed.

Lemma dvdn_card_permuted :
  (\prod_(x : seq_sub w) (count_mem (val x) w)`! %| n`!)%N.
Proof.
by apply/dvdnP; exists #|[set: permuted w]|; rewrite card_permuted_prodE.
Qed.

Lemma card_permuted_seq_subE :
  #|[set: permuted w]| = (n`! %/ \prod_(x : seq_sub w) (count_mem (val x) w)`!)%N.
Proof.
rewrite -card_permuted_prodE mulnK //.
by apply prodn_gt0 => i; apply: fact_gt0.
Qed.

Lemma prod_gact_count_memE (s : seq T) :
  uniq s -> all (mem s) w ->
  (\prod_(x : seq_sub w) (count_mem (val x) w)`! =
   \prod_(x <- s)        (count_mem      x  w)`!)%N.
Proof.
move=> Huniq /allP H.
rewrite [RHS](bigID (fun x => x \in w)) /= [X in (_ * X)%N]big1 ?muln1; first last.
  by move=> i /count_memPn ->.
rewrite /index_enum.
rewrite -[LHS](big_map (ssval (s := w)) xpredT (fun x : T => (count_mem x w)`!)).
rewrite -[RHS]big_filter; apply eq_big_perm; apply uniq_perm_eq.
- rewrite map_inj_uniq; last exact: val_inj.
  by rewrite -enumT; exact: enum_uniq.
- exact: filter_uniq.
- move=> x; rewrite mem_filter; apply/mapP/idP => [/= [y _ ->] | /andP [Hx Hxs]].
  + by case: y => y /= Hy; rewrite Hy /=; apply: H.
  + exists (SeqSub Hx) => //.
    by rewrite -enumT mem_enum.
Qed.

Lemma prod_gact_count_undupE :
  (\prod_(x : seq_sub w) (count_mem (val x) w)`! =
   \prod_(x <- undup w)  (count_mem      x  w)`!)%N.
Proof.
apply prod_gact_count_memE; first exact: undup_uniq.
rewrite (eq_in_all (a2 := predT)); first exact: all_predT.
by move=> i /=; rewrite mem_undup => ->.
Qed.

Lemma card_permutedE :
  #|[set: permuted w]| = (n`! %/ \prod_(x <- undup w) (count_mem x w)`!)%N.
Proof. by rewrite card_permuted_seq_subE prod_gact_count_undupE. Qed.

End ActOnTuple.

