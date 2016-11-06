(** * Combi.Combi.partition : Integer Partitions *)
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
(** * Integer Compositions

******)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import bigop path.
Require Import tools combclass sorted partition.

Set Implicit Arguments.
Unset Strict Implicit.


(** * Integer Composition *)
(** ** Definitions and basic properties *)
Section Defs.

Implicit Type s : seq nat.

Definition is_comp s := 0 \notin s.

  (** Compositions and sumn *)
Lemma comp0 s : is_comp s -> sumn s = 0 -> s = [::].
Proof. by rewrite /is_comp; case: s => //= [[|a] l]. Qed.

Lemma size_comp s : is_comp s -> size s <= sumn s.
Proof.
rewrite /is_comp; elim: s => [//= | [|s0] s IHs] //.
rewrite negb_or /= => /IHs/leq_ltn_trans; apply.
by rewrite addSnnS; apply leq_addl.
Qed.

End Defs.


(** * Sigma Types for Compositions *)

Structure intcomp : Type := IntComp {cval :> seq nat; _ : is_comp cval}.
Canonical intcomp_subType := Eval hnf in [subType for cval].
Definition intcomp_eqMixin := Eval hnf in [eqMixin of intcomp by <:].
Canonical intcomp_eqType := Eval hnf in EqType intcomp intcomp_eqMixin.
Definition intcomp_choiceMixin := Eval hnf in [choiceMixin of intcomp by <:].
Canonical intcomp_choiceType :=
  Eval hnf in ChoiceType intcomp intcomp_choiceMixin.
Definition intcomp_countMixin := Eval hnf in [countMixin of intcomp by <:].
Canonical intcomp_countType :=
  Eval hnf in CountType intcomp intcomp_countMixin.

Lemma intcompP (p : intcomp) : is_comp p.
Proof. by case: p. Qed.

Hint Resolve intcompP.

Fixpoint enum_compn_rec aux n : (seq (seq nat)) :=
  if aux is aux'.+1 then
    if n == 0 then [:: [::]]
    else
      flatten [seq [seq i :: p | p <- enum_compn_rec aux' (n - i) ] |
               i <- iota 1 n]
  else [:: [::]].
Definition enum_compn n := enum_compn_rec n n.

Definition is_comp_of_n sm := [pred s | (sumn s == sm) & is_comp s].

Lemma enum_compn_rec_any aux1 aux2 n :
  n <= aux1 -> n <= aux2 -> enum_compn_rec aux1 n = enum_compn_rec aux2 n.
Proof.
elim: aux1 aux2 n => [| aux1 IHaux1] aux2 n /=.
  rewrite leqn0 => /eqP -> //=; by case aux2.
case: (altP (n =P 0)) => [-> | Hn Haux1] //=; first by case aux2.
case: aux2 => [| aux2 /= Haux2].
  by rewrite leqn0 => /eqP H; rewrite H eq_refl in Hn.
rewrite (negbTE Hn); congr flatten; apply eq_in_map => i.
rewrite mem_iota add1n ltnS => /andP [Hi _].
congr map; apply: IHaux1; rewrite leq_subLR.
- by apply: (leq_trans Haux1); rewrite -{1}(add0n aux1) ltn_add2r.
- by apply: (leq_trans Haux2); rewrite -{1}(add0n aux2) ltn_add2r.
Qed.

Lemma enum_compn_any aux n :
  n <= aux -> enum_compn_rec aux n = enum_compn n.
Proof. by rewrite /enum_compn => Hn; apply enum_compn_rec_any. Qed.

Lemma enum_compnE n :
  n != 0 ->
  enum_compn n = flatten [seq [seq i :: p | p <- enum_compn (n - i) ] |
                          i <- iota 1 n].
Proof.
rewrite -(enum_compn_any (leqnSn n)) /= => /negbTE ->.
congr flatten; apply eq_in_map => i.
rewrite mem_iota add1n ltnS => /andP [Hi _].
congr map; apply enum_compn_any.
by rewrite leq_subLR; apply: leq_addl.
Qed.

Lemma enum_compn_allP n : all (is_comp_of_n n) (enum_compn n).
Proof.
rewrite /is_comp_of_n /is_comp /enum_compn.
elim: n {1 3 5}n (leqnn n) => [|aux IHaux] //= n.
  by rewrite leqn0 !andbT => /eqP ->.
move=> Hn.
case: (altP (n =P 0)) => [-> //| neq0].
apply/allP => /= lst /flatten_mapP [/= i].
rewrite mem_iota add1n ltnS => /andP [lt0i lein] /mapP [/= s Hs] ->{lst}.
have {IHaux} /IHaux/allP/(_ s Hs)/= : n - i <= aux.
  rewrite leq_subLR; apply (leq_trans Hn).
  case: i lt0i {lein Hs} => // i _.
  by rewrite addSnnS; apply leq_addl.
rewrite negb_or => /andP [/eqP ->] ->.
rewrite subnKC // eq_refl /= andbT.
by rewrite eq_sym -lt0n.
Qed.

Lemma enum_compn_countE n :
  forall s, is_comp_of_n n s -> count_mem s (enum_compn n) = 1.
Proof.
rewrite /is_comp_of_n /is_comp /enum_compn.
elim: n {1 3 5}n (leqnn n) => [|aux IHaux] //= n.
  rewrite leqn0 => /eqP -> s.
  rewrite andbC => /andP [/comp0 H /eqP /H{H} ->].
  by rewrite eq_refl.
move=> Hn [|s0 s] /andP [/= ]; first by move=> /eqP <-.
rewrite negb_or => Hsum /andP [s0neq0] Hs.
have /negbTE -> : n != 0.
  move: s0neq0; apply contra => /eqP Hn0.
  by move: Hsum; rewrite Hn0 addn_eq0 => /andP [/eqP ->].
rewrite count_flatten -map_comp.
rewrite (eq_map (f2 := fun i => i == s0 : nat)); first last.
  move=> /= i; rewrite count_map /=.
  case (altP (i =P s0)) => [Heq | /negbTE Hneq].
  - subst s0; rewrite (eq_count (a2 := xpred1 s)); first last.
      by move=> x; rewrite /= -eqseqE /= eq_refl /=.
    rewrite {}IHaux //=.
    + rewrite leq_subLR; apply (leq_trans Hn).
      case: i s0neq0 {Hsum} => // i _.
      by rewrite addSnnS; apply leq_addl.
    + by rewrite Hs andbT -(eqP Hsum) addKn.
  - rewrite (eq_count (a2 := pred0)); first by rewrite count_pred0.
    by move=> t; rewrite /= -eqseqE /= Hneq.
rewrite sumn_iota //= add1n ltnS -(eqP Hsum) leq_addr andbT.
by rewrite lt0n eq_sym.
Qed.

Lemma enum_compnP n s : (is_comp_of_n n s) = (s \in enum_compn n).
Proof.
apply/idP/idP; last by move/(allP (enum_compn_allP n)).
rewrite -has_pred1 has_count; by move/enum_compn_countE ->.
Qed.


Section CompOfn.

Variable n : nat.

Structure intcompn : Set :=
  IntCompN {cnval :> seq nat; _ : is_comp_of_n n cnval}.
Canonical intcompn_subType := Eval hnf in [subType for cnval].
Definition intcompn_eqMixin := Eval hnf in [eqMixin of intcompn by <:].
Canonical intcompn_eqType := Eval hnf in EqType intcompn intcompn_eqMixin.
Definition intcompn_choiceMixin :=
  Eval hnf in [choiceMixin of intcompn by <:].
Canonical intcompn_choiceType :=
  Eval hnf in ChoiceType intcompn intcompn_choiceMixin.
Definition intcompn_countMixin := Eval hnf in [countMixin of intcompn by <:].
Canonical intcompn_countType :=
  Eval hnf in CountType intcompn intcompn_countMixin.
Canonical intcompn_subCountType := Eval hnf in [subCountType of intcompn].

Let type := sub_finType intcompn_subCountType
                        (enum_compn_allP n) (@enum_compn_countE n).
Canonical intcompn_finType := Eval hnf in [finType of intcompn for type].
Canonical intcompn_subFinType := Eval hnf in [subFinType of intcompn].

Lemma intcompnP (p : intcompn) : is_comp p.
Proof using . by case: p => /= p /andP []. Qed.

Hint Resolve intcompnP.

Definition intcomp_of_intcompn (p : intcompn) := IntComp (intcompnP p).
Coercion intcomp_of_intcompn : intcompn >-> intcomp.

Lemma intcompn_sumn (p : intcompn) : sumn p = n.
Proof using . by case: p => /= p /andP [] /eqP. Qed.

Lemma enum_intcompnE : map val (enum {:intcompn}) = enum_compn n.
Proof using . rewrite /=; exact: enum_subE. Qed.

End CompOfn.

Lemma intcompn0 (sh : intcompn 0) : sh = [::] :> seq nat.
Proof.
case: sh => sh Hsh /=; move: Hsh; rewrite enum_compnP.
by rewrite /enum_compn /= inE => /eqP.
Qed.

Lemma intcompn1 (sh : intcompn 1) : sh = [:: 1] :> seq nat.
Proof.
case: sh => sh Hsh /=; move: Hsh; rewrite enum_compnP.
by rewrite /enum_compn /= inE => /eqP.
Qed.

Lemma intcompn2 (sh : intcompn 2) :
  sh = [:: 2]  :> seq nat \/ sh = [:: 1; 1] :> seq nat.
Proof.
case: sh => sh Hsh /=; move: Hsh; rewrite enum_compnP.
rewrite /enum_compn /= !inE => /orP [] /eqP ->; by [left | right].
Qed.

Definition intcompn_cast m n (eq_mn : m = n) p :=
  let: erefl in _ = n := eq_mn return intcompn n in p.

Lemma intcompn_castE m n (eq_mn : m = n) p : val (intcompn_cast eq_mn p) = val p.
Proof. subst m; by case: p. Qed.

Definition rowcomp d := if d is _.+1 then [:: d] else [::].
Fact rowcompnP d : is_comp_of_n d (rowcomp d).
Proof. case: d => [//= | d]; by rewrite /is_comp_of_n /= addn0 eq_refl. Qed.
Definition rowcompn d : intcompn d := IntCompN (rowcompnP d).

Definition colcomp d := nseq d 1%N.
Fact colcompnP d : is_comp_of_n d (colcomp d).
Proof. by elim: d => [| d ]. Qed.
Definition colcompn d : intcompn d := IntCompN (colcompnP d).

(* TODO : bijection with set and cardinality 
Lemma card_intcompn n : #|{:intcompn n}| = 2 ^ (n.-1).
*)

Hint Resolve intcompP intcompnP.

Lemma part_of_comp_subproof n (c : intcompn n) :
  is_part_of_n n (sort geq c).
Proof.
rewrite /is_part_of_n /= sumn_sort intcompn_sumn eq_refl /=.
rewrite is_part_sortedE; apply/andP; split.
- apply sort_sorted => x y; exact: leq_total.
- by rewrite mem_sort -/(is_comp c).
Qed.
Definition partn_of_compn n (c : intcompn n) :=
  IntPartN (part_of_comp_subproof c).

Lemma perm_partn_of_compn n (c : intcompn n) : perm_eq (partn_of_compn c) c.
Proof. by rewrite /= perm_sort. Qed.

(*
From mathcomp Require Import finset div.

Lemma card_preim_part_of_compn n (sh : 'P_n) :
  #|[set c | partn_of_compn c == sh]| =
  n`! %/ \prod_(i <- iota 1 n) (count_mem i sh)`!.
Proof.
*)

