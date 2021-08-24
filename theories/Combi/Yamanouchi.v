(** * Combi.Combi.Yamanouchi : Yamanouchi Words *)
(******************************************************************************)
(*      Copyright (C) 2014-2021 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * Yamanouchi words.

A Yamanouchi word [w] is a [seq nat] such as for all [i] in any suffix of [w],
the number of occurence of [i] is larger than the number of occurence of [i+1].
Yamanouchi words are in bijection with standard tableaux.

We define the following notions and notations:

- [evalseq s] == the evaluation of the sequence [s] stored as a sequence,
                 that is the sequence whose [i]-th entry is the number
                 of occurences of [i] in [s]; the final zeroes are not stored
                 so that the sequence ends with a non zero entry.
- [evalseq_count] == an alternate definition of the previous sequence
- [is_yam s] == s is a Yamanouchi word
- [is_yam_of_eval ev s] == s is a Yamanouchi word of evaluation ev.
- [decr_yam s] == the Yamanouchi word obtained by removing the zero and
                 decrassing all the other entries by 1
- [hyper_yam ev] == the hyperstandard (decreasing) Yamanouchi word of
                 evaluation [ev] such as 33 2222 11111 0000000

Enumeration of Yamanouchi words:

- [is_yam_of_eval ev y] == y is a yamanouchi word of evalutation ev
- [is_yam_of_size n y] == y is a yamanouchi word of size n
- [enum_yameval ev] == the lists of all yamanouchi word of evalutation ev


Sigma types for Yamanouchi words:

- [yameval ev] == a type for [seq nat] which are Yamanouchi words of
                 evaluation ev; it is canonically a [finType]
- [yamn n] == a type for [seq nat] which are Yamanouchi words of
                 size n; it is canonically a [finType]
- [hyper_yameval ev] == the the hyperstandard (decreasing) Yamanouchi word of
                 evaluation ev such as 33 2222 11111 0000000 as a [yameval]

******)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import bigop.
Require Import tools combclass partition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section Yama.

Implicit Type s : seq nat.

(** * Evaluation of a sequence of integer (mostly Yamanouchi word) *)
Fixpoint evalseq s :=
  if s is s0 :: s'
  then incr_nth (evalseq s') s0
  else [::].

(** equivalent definition *)
Definition evalseq_count :=
  [fun s => [seq (count_mem i) s | i <- iota 0 (foldr maxn 0 (map S s))]].

Lemma foldr_maxn s : foldr maxn 0 [seq i.+1 | i <- s] = \max_(i <- s) S i.
Proof.
elim: s => [| s0 s IHs] /=; first by rewrite big_nil.
by rewrite big_cons IHs.
Qed.

Lemma evalseq_countE : evalseq_count =1 evalseq.
Proof.
elim => [//| l0 s /= <-]; apply: (@eq_from_nth _ 0).
  rewrite size_incr_nth !size_map !size_iota /= {1}maxnC {1}/maxn.
  by case (ltngtP l0.+1 (foldr _ _ _)).
move=> i; rewrite nth_incr_nth size_map => Hsz.
rewrite (nth_map 0 _ _ Hsz); rewrite size_iota in Hsz.
rewrite (nth_iota _ _ Hsz) add0n.
case (ltnP i (foldr maxn 0 [seq i.+1 | i <- s])) => Hi.
- rewrite (nth_map 0 _ _); last by rewrite size_iota.
  by rewrite (nth_iota _ _ Hi) /= add0n.
- rewrite (nth_default 0) /=; last by rewrite size_map size_iota.
  congr ((l0 == i) + _).
  elim: s Hi {Hsz} => [//| s0 s /=].
  move: (foldr _ _ _) => m IHs; rewrite /maxn.
  case (ltnP s0.+1 m) => Hs Hi.
  + by rewrite (IHs Hi) (ltn_eqF (leq_ltn_trans (leqnSn s0) (leq_trans Hs Hi))).
  + by rewrite (IHs (leq_trans Hs Hi)) (ltn_eqF Hi).
Qed.

Lemma nth_evalseq s i : nth 0 (evalseq s) i = count_mem i s.
Proof.
rewrite -evalseq_countE /evalseq_count.
case: (ltnP i (foldr maxn 0 [seq i.+1 | i <- s])) => Hi.
- rewrite (nth_map 0); last by rewrite size_iota.
  by rewrite nth_iota.
- rewrite nth_default; last by rewrite size_map size_iota.
  elim: s Hi => [| s0 s IHs] //=.
  by rewrite geq_max => /andP [/ltn_eqF -> /= /IHs <-].
Qed.

Lemma perm_evalseq s t : perm_eq s t = (evalseq s == evalseq t).
Proof.
apply/idP/idP => [Hperm | /eqP].
- rewrite -!evalseq_countE /evalseq_count /=.
  rewrite !foldr_maxn (perm_big _ Hperm) /=.
  apply/eqP; apply eq_map => i.
  by move: Hperm => /permP ->.
- rewrite -!evalseq_countE /evalseq_count /=.
  set mx := foldr _ _ _ => H.
  have:= congr1 size H; rewrite !size_map !size_iota => Hmax.
  rewrite /perm_eq; apply /allP => i /= Hi.
  have {}Hi : i < mx.
  move: Hi; rewrite mem_cat => /orP [].
  + rewrite /mx; elim s => [//= | s0 s' IHs] /=.
    rewrite inE => /orP [/eqP -> | Hi]; first exact: leq_maxl.
    rewrite leq_max; apply/orP; right.
    exact: IHs.
  + rewrite Hmax; elim t => [//= | t0 t' IHt] /=.
    rewrite inE => /orP [/eqP -> | Hi]; first exact: leq_maxl.
    rewrite leq_max; apply/orP; right.
    exact: IHt.
  move/(congr1 (fun s => nth 0 s i)) : H.
  rewrite (nth_map 0); last by rewrite size_iota.
  rewrite (nth_map 0); last by rewrite -Hmax size_iota.
  rewrite (nth_iota _ _ Hi) nth_iota; last by rewrite -Hmax.
  by rewrite !add0n => ->.
Qed.

Lemma evalseq0 y : evalseq y = [::] -> y = [::].
Proof. by case: y => [//= | [|y0] y] /=; case: (evalseq y). Qed.

Lemma evalseq_cons l s : evalseq (l :: s) = incr_nth (evalseq s) l.
Proof. by []. Qed.

Lemma evalseq_eq_size y : sumn (evalseq y) = size y.
Proof. by elim: y => [//= | y0 y] /=; rewrite sumn_incr_nth => ->. Qed.

(** * Yamanouchi words:                                                       *)
(** Sequence of rows of the corners for an increasing sequence of partitions. *)
(** They are in bijection with standard tableaux                              *)
Fixpoint is_yam s :=
  if s is s0 :: s'
  then is_part (evalseq s) && is_yam s'
  else true.
Definition is_yam_of_eval ev y := (is_yam y) && (evalseq y == ev).

Lemma is_yamP s :
  reflect
    (forall i n, count_mem n (drop i s) >= count_mem n.+1 (drop i s))
    (is_yam s).
Proof.
apply (iffP idP).
- elim: s => [| s0 s IHs] //= /andP [] /is_partP [] _ Hpart /IHs Hrec {IHs}.
  case => [| i] n //=.
  case: (altP (s0 =P n)) => Hns0.
  + subst s0; rewrite ltn_eqF // add0n add1n.
    by move/(_ 0 n) : Hrec; rewrite drop0 => /leq_trans; apply.
  + case: (altP (s0 =P n.+1)) => Hn1s0.
    move/(_ n) : Hpart; rewrite !nth_incr_nth Hn1s0 eq_refl eq_sym ltn_eqF //.
    by rewrite !add0n !add1n !nth_evalseq.
  + by move/(_ 0 n) : Hrec; rewrite !add0n drop0.
- elim: s => [//= | s0 s IHs] H.
  apply/andP; split.
  + move: (s0 :: s) {IHs} H => {s0}s /(_ 0); rewrite drop0 => Hs.
    apply /is_partP; split; last by move=> i; rewrite !nth_evalseq.
    elim: s {Hs} => [//= | s0 s IHs] /=.
    exact: last_incr_nth_non0.
  + apply: IHs => i n; exact (H i.+1 n).
Qed.

Lemma is_yam_ijP s :
  reflect
    (forall d i j, i <= j -> count_mem i (drop d s) >= count_mem j (drop d s))
    (is_yam s).
Proof.
apply (iffP idP).
- move=> /is_yamP Hyam d i j Hij.
  move/(_ d) : Hyam => Hsuff.
  rewrite -(subnKC Hij).
  elim: (j-i) => [| r IHr]; first by rewrite addn0.
  apply: (leq_trans _ IHr).
  by rewrite addnS; exact: Hsuff.
- by move=> H; apply/is_yamP => i d; exact: H.
Qed.

Lemma is_part_eval_yam s : is_yam s -> is_part (evalseq s).
Proof. by case: s => [//= | s0 s] /= /andP []. Qed.

Lemma is_yam_tl l0 s : is_yam (l0 :: s) -> is_yam s.
Proof. by move=> /= /andP []. Qed.

Lemma is_yam_catr s t : is_yam (s ++ t) -> is_yam t.
Proof. by elim: s => [//= | s0 s IHs] /= /andP [] _. Qed.

Lemma last_yam y : is_yam y -> last 0 y = 0.
Proof.
case/lastP: y => [//= | y yn].
rewrite last_rcons.
elim: y => [//= | y0 y IHy] /=.
  case: yn => [//= | y] /= /andP [] H _.
  by elim: y H => [//= | yn IHy] /= /IHy.
by move=> /andP [] _; exact IHy.
Qed.

(** Remove the zeroes from a yam and decrease all the other entries by 1 *)
Fixpoint decr_yam s :=
  if s is s0 :: s'
  then if s0 is s0'.+1
       then s0' :: (decr_yam s')
       else (decr_yam s')
  else [::].

Lemma evalseq_decr_yam s : evalseq (decr_yam s) = behead (evalseq s).
Proof.
elim: s => [//= | s0 s /= IHs].
case s0 => [ | s0' /=].
- by rewrite IHs /=; case (evalseq s).
- rewrite IHs /=; case (evalseq s) => [|sh0 sh //=].
  by case: s0'.
Qed.

Lemma is_yam_decr s : is_yam s -> is_yam (decr_yam s).
Proof.
elim: s => [//= | s0 s IHs] /= /andP [] Hpart.
move/IHs {IHs} => Hyam; case: s0 Hpart=> [//= | s0'] /=.
rewrite Hyam andbT evalseq_decr_yam.
case H : (evalseq s) => [| sh0 sh] /= /andP [] _ //=.
by case s0'.
Qed.

Lemma is_rem_corner_yam l0 s :
  is_yam (l0 :: s) -> is_rem_corner (evalseq (l0 :: s)) l0.
Proof.
move/is_yam_tl/is_part_eval_yam/is_partP => [] _ Hpart.
rewrite /is_rem_corner !nth_incr_nth ltn_eqF // eq_refl add0n add1n ltnS.
exact: Hpart.
Qed.

Lemma is_add_corner_yam l0 s :
  is_yam (l0 :: s) -> is_add_corner (evalseq s) l0.
Proof.
rewrite /is_add_corner /=; case: l0 => [//= | l0] /=.
case: (evalseq s) => [| sh0 sh] /andP [].
  move=> /andP [] H1 H2 _; exfalso.
  by case: l0 H1 H2 => //= l0 _; elim: l0.
move=> /is_partP [] _ /( _ l0) /=.
rewrite -/(incr_nth (sh0 :: sh) l0.+1) !nth_incr_nth eq_refl add1n.
by rewrite eq_sym ltn_eqF // add0n.
Qed.

(** ** Hyperstandard Yamanouchi word : 33 2222 11111 0000000 *)
Fixpoint hyper_yam_rev ev :=
  if ev is s0 :: s then
    nseq s0 (size s) ++ hyper_yam_rev s
  else [::].
Definition hyper_yam ev := hyper_yam_rev (rev ev).

Lemma size_hyper_yam ev : size (hyper_yam ev) = sumn ev.
Proof.
elim/last_ind: ev => [//= | sh sn] /=.
rewrite /hyper_yam -(sumn_rev (rcons _ _)) rev_rcons /= size_cat => ->.
by rewrite size_nseq sumn_rev.
Qed.

Lemma incr_nth_size s : incr_nth s (size s) = rcons s 1.
Proof. by elim: s => [| s0 s /= ->]. Qed.

Lemma part_rcons_ind s sn : is_part (rcons s sn.+2) -> is_part (rcons s sn.+1).
Proof.
elim: s => [//= | s0 s IHs] /=.
move => /andP [] Hhead {}/IHs ->; rewrite andbT.
case: s Hhead => [//= | s1 s]; first exact: ltn_trans.
by rewrite !rcons_cons.
Qed.

(** "is_part ev" is just here to ensure that sh doesn't ends with a 0 *)
Lemma evalseq_hyper_yam ev : is_part ev -> evalseq (hyper_yam ev) = ev.
Proof.
rewrite /hyper_yam; elim/last_ind: ev => [//= | s sn IHs].
rewrite rev_rcons /=; case: sn => [/= | sn].
  by move/is_partP; rewrite last_rcons /= => [] [].
elim: sn => [/= | sn /= IHsn].
  by move/is_part_rconsK/IHs ->; rewrite size_rev incr_nth_size.
move=> Hpart; rewrite IHsn {IHsn IHs}.
- rewrite size_rev {Hpart}; elim: s => [//= | s0 s IHs] /=.
  by rewrite IHs.
- exact: part_rcons_ind.
Qed.

Lemma hyper_yamP ev : is_part ev -> is_yam (hyper_yam ev).
Proof.
elim/last_ind: ev => [//= | s sn IHs].
rewrite /hyper_yam rev_rcons /=; case: sn => [| sn].
  by move/is_partP; rewrite last_rcons /= => [] [].
elim: sn => [/= | sn /= IHsn].
  move=> Hpart1; have Hpart := is_part_rconsK Hpart1.
  by rewrite (IHs Hpart) size_rev (evalseq_hyper_yam Hpart) incr_nth_size Hpart1.
move=> Hpart2.
move/(_ (part_rcons_ind Hpart2))/andP : IHsn => [] -> ->; rewrite !andbT.
by have:= Hpart2; rewrite -{1}(evalseq_hyper_yam Hpart2) /hyper_yam rev_rcons.
Qed.

Lemma hyper_yam_of_eval ev : is_part ev -> is_yam_of_eval ev (hyper_yam ev).
Proof.
by move=> H; rewrite /is_yam_of_eval (hyper_yamP H) (evalseq_hyper_yam H) /=.
Qed.

End Yama.

Lemma is_yam_cat_any y0 y1 z :
  is_yam y0 -> is_yam y1 -> evalseq y0 = evalseq y1 ->
  is_yam (z ++ y0) -> is_yam (z ++ y1).
Proof.
elim: z => [//= | z0 z IHz] /= Hy0 Hy1 H /andP [] Hpart Hyam.
apply/andP; split; last exact: IHz.
suff <- : evalseq (z ++ y0) = evalseq (z ++ y1) by [].
apply /eqP; rewrite -perm_evalseq.
by rewrite perm_cat2l perm_evalseq H.
Qed.


(** * Enumeration of Yamanouchi words *)
Fixpoint enum_yamevaln n ev :=
  if n is n'.+1 then
    flatten [seq [seq i :: y | y <- enum_yamevaln n' (decr_nth ev i)] |
                  i <- iota 0 (size ev) & is_rem_corner ev i]
  else [:: [::]].
Definition enum_yameval ev := enum_yamevaln (sumn ev) ev.
Definition is_yam_of_size n y := (is_yam y) && (size y == n).

Lemma enum_yamevalP ev:
  is_part ev -> all (is_yam_of_eval ev) (enum_yameval ev).
Proof.
move=> Hpart; apply/allP => y.
rewrite /enum_yameval /is_yam_of_eval; move Hn: (sumn ev) => n.
elim: n ev Hpart Hn y => [| n IHn] /= .
  by move=> ev Hsh /part0 H0 y; rewrite mem_seq1 H0 //= => /eqP ->.
move=> ev Hpart Hev [/= | y0 y] /=.
- have -> : [::] == ev = false by move: Hev; case ev.
  by move=> /flattenP [] ltmp /mapP [i _ ->] /mapP [].
- move/flatten_mapP => [i].
  rewrite mem_filter mem_iota add0n => /and3P [Hcorn _ Hi].
  move/mapP => [x Hx [Hitmp Hxtmp]]; subst i x.
  have Hsum : sumn (decr_nth ev y0) = n by rewrite sumn_decr_nth //= Hev.
  move/(_ _ (is_part_decr_nth Hpart Hcorn) Hsum _ Hx): IHn => /andP[-> /eqP ->].
  by rewrite decr_nthK //= Hpart /=.
Qed.

Lemma enum_yameval_countE ev :
  is_part ev ->
  forall y, is_yam_of_eval ev y -> count_mem y (enum_yameval ev) = 1.
Proof.
rewrite /enum_yameval /is_yam_of_eval; move Hn: (sumn ev) => n.
elim: n ev Hn => [| n IHn] /= .
  move=> ev Hev /part0 H0 y.
  by rewrite (H0 Hev) => /andP [] _ /eqP/evalseq0 ->.
move=> ev Hev Hpart [/= | y0 y] /=.
  by have -> : [::] == ev = false by move: Hev; case ev.
move => /andP [] /andP [] _ Hyam /eqP Htmp; subst ev.
rewrite count_flatten -map_comp.
rewrite (eq_map (f2 := fun i => i == y0 : nat)); first last.
  move=> i /=; rewrite count_map /=.
  case (altP (i =P y0)) => [Heq | /negbTE Hneq].
  - subst i; rewrite (eq_count (a2 := xpred1 y)); first last.
      by move=> s; rewrite /= -eqseqE /= eq_refl /=.
    rewrite (incr_nthK (is_part_eval_yam Hyam) Hpart) IHn //=.
    + by move: Hev; rewrite sumn_incr_nth => /eqP; rewrite eqSS => /eqP.
    + exact: is_part_eval_yam.
    + by rewrite Hyam eq_refl.
  - rewrite (eq_count (a2 := pred0)); first by rewrite count_pred0.
    by move=> s; rewrite /= -eqseqE /= Hneq.
rewrite sumn_count count_filter.
rewrite (eq_count (a2 := xpred1 y0)); first last.
  move=> i /=; case (altP (i =P y0)) => //= ->.
  by apply: is_rem_corner_yam; rewrite /= Hpart Hyam.
rewrite -sumn_count /=.
rewrite sumn_pred1_iota add0n size_incr_nth.
case: (ltnP y0 (size (evalseq y))) => [->// | _].
by rewrite ltnSn leq0n.
Qed.


(** * Sigma types for Yamanouchi words *)
Section YamOfEval.

Variable ev : intpart.

Structure yameval : Set :=
  YamEval {yamevalval :> seq nat; _ : is_yam_of_eval ev yamevalval}.
Canonical yameval_subType := Eval hnf in [subType for yamevalval].
Definition yameval_eqMixin := Eval hnf in [eqMixin of yameval by <:].
Canonical yameval_eqType := Eval hnf in EqType yameval yameval_eqMixin.
Definition yameval_choiceMixin := Eval hnf in [choiceMixin of yameval by <:].
Canonical yameval_choiceType :=
  Eval hnf in ChoiceType yameval yameval_choiceMixin.
Definition yameval_countMixin := Eval hnf in [countMixin of yameval by <:].
Canonical yameval_countType :=
  Eval hnf in CountType yameval yameval_countMixin.
Canonical yameval_subCountType := Eval hnf in [subCountType of yameval].
Let type := sub_finType yameval_subCountType
                        (enum_yamevalP (intpartP ev))
                        (enum_yameval_countE (intpartP ev)).
Canonical yameval_finType := Eval hnf in [finType of yameval for type].
Canonical yameval_subFinType := Eval hnf in [subFinType of yameval].

Lemma yamevalP (y : yameval) : is_yam y.
Proof using. by case: y => /= y /andP[]. Qed.

Lemma eval_yameval (y : yameval) : evalseq y = ev.
Proof using. by case: y => /= y /andP[_ /eqP]. Qed.

Lemma size_yameval (y : yameval) : size y = sumn ev.
Proof using. by rewrite -evalseq_eq_size eval_yameval. Qed.

Lemma enum_yamevalE : map val (enum {:yameval}) = enum_yameval ev.
Proof using. by rewrite /=; exact: enum_subE. Qed.

Definition hyper_yameval := YamEval (hyper_yam_of_eval (intpartP ev)).

End YamOfEval.
#[export] Hint Resolve yamevalP : core.


Section YamOfSize.

Variable n : nat.

Lemma yamn_PredEq (ev : intpartn_subFinType n) :
  predI (is_yam_of_size n) (pred1 (val ev) \o evalseq)
  =1 is_yam_of_eval (val ev).
Proof using.
move=> y; rewrite /is_yam_of_size /is_yam_of_eval /= -andbA; congr (_ && _).
case: (altP (evalseq y =P ev)) => /=; last by rewrite andbF.
rewrite -evalseq_eq_size => ->.
by rewrite (sumn_intpartn ev) eq_refl.
Qed.

Lemma yamn_partition_evalseq yam :
  is_yam_of_size n yam -> (is_part_of_n n) (evalseq yam).
Proof using.
by rewrite /is_yam_of_size /= evalseq_eq_size => /andP[/is_part_eval_yam -> ->].
Qed.

Structure yamn : Set :=
  Yamn {yamnval :> seq nat; _ : is_yam_of_size n yamnval}.
Canonical yamn_subType := Eval hnf in [subType for yamnval].
Definition yamn_eqMixin := Eval hnf in [eqMixin of yamn by <:].
Canonical yamn_eqType := Eval hnf in EqType yamn yamn_eqMixin.
Definition yamn_choiceMixin := Eval hnf in [choiceMixin of yamn by <:].
Canonical yamn_choiceType := Eval hnf in ChoiceType yamn yamn_choiceMixin.
Definition yamn_countMixin := Eval hnf in [countMixin of yamn by <:].
Canonical yamn_countType := Eval hnf in CountType yamn yamn_countMixin.
Canonical yamn_subCountType := Eval hnf in [subCountType of yamn].
Let type := union_finType
              yamn_subCountType
              (fun p : intpartn_subFinType n => (yameval_subFinType p))
              yamn_PredEq yamn_partition_evalseq.
Canonical yamn_finType := Eval hnf in [finType of yamn for type].
Canonical yamn_subFinType := Eval hnf in [subFinType of yamn].

Lemma yamnP (y : yamn) : is_yam y.
Proof using. by case: y => /= y /andP []. Qed.

Lemma size_yamn (y : yamn) : size y = n.
Proof using. by case: y => /= y /andP [] _ /eqP. Qed.

(** Check of disjoint union enumeration *)
Lemma enum_yamnE :
  map val (enum {:yamn}) = flatten [seq enum_yameval p | p <- enum_partn n].
Proof using.
rewrite enum_unionE /=; congr flatten.
rewrite [LHS](eq_map (f2 := enum_yameval \o val)).
- by rewrite map_comp enum_intpartnE.
- by move=> i /=; rewrite enum_yamevalE.
Qed.

End YamOfSize.

#[export] Hint Resolve yamnP yamevalP : core.
Prenex Implicits yamnP yamevalP yamn_PredEq.
