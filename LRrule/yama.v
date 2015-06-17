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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop.
Require Import tools combclass partition.

Set Implicit Arguments.
Unset Strict Implicit.

Section Yama.

  Implicit Type s : seq nat.


  (* Shape of a sequence of row index (mostly Yamanouchi word) *)
  Fixpoint shape_rowseq s :=
    if s is s0 :: s'
    then incr_nth (shape_rowseq s') s0
    else [::].

  (* equivalent definition *)
  Definition shape_rowseq_count :=
    [fun s => [seq (count_mem i) s | i <- iota 0 (foldr maxn 0 (map S s))]].

  Lemma shape_rowseq_countE : shape_rowseq_count =1 shape_rowseq.
  Proof.
    elim=>[//= | l0 s /= <-]; apply: (@eq_from_nth _ 0).
    - rewrite size_incr_nth !size_map !size_iota /= {1}maxnC {1}/maxn.
      set m := foldr _ _ _; case (ltngtP l0.+1 m) => [H||->].
      * by rewrite (leq_ltn_trans (leqnSn l0) H).
      * by rewrite ltnNge => /negbTE ->.
      * by rewrite leqnn.
    - move=> i; rewrite nth_incr_nth size_map => Hsz.
      rewrite (nth_map 0 _ _ Hsz); rewrite size_iota in Hsz; rewrite (nth_iota _ Hsz).
      rewrite add0n.
      case (ltnP i (foldr maxn 0 [seq i.+1 | i <- s])) => Hi.
      * rewrite (nth_map 0 _ _); last by rewrite size_iota.
        by rewrite (nth_iota _ Hi) /= add0n.
      * rewrite (nth_default 0) /=; last by rewrite size_map size_iota.
        congr ((l0 == i) + _).
        elim: s Hi {Hsz} => [//=| s0 s /=].
        set m := foldr _ _ _ => IHs; rewrite /maxn.
        case (ltnP s0.+1 m) => Hs Hi.
        - by rewrite (IHs Hi) (ltn_eqF (leq_ltn_trans (leqnSn s0) (leq_trans Hs Hi))).
        - by rewrite (IHs (leq_trans Hs Hi)) (ltn_eqF Hi).
  Qed.

  Lemma nth_shape_rowseq s i : nth 0 (shape_rowseq s) i = count_mem i s.
  Proof.
    rewrite -shape_rowseq_countE /shape_rowseq_count.
    case: (ltnP i (foldr maxn 0 [seq i.+1 | i <- s])) => Hi.
    - rewrite (nth_map 0); last by rewrite size_iota.
      by rewrite nth_iota.
    - rewrite nth_default; last by rewrite size_map size_iota.
      elim: s Hi => [| s0 s IHs] //=.
      by rewrite geq_max => /andP [] /ltn_eqF -> /= /IHs <-.
  Qed.

  Lemma foldr_maxn s : foldr maxn 0 [seq i.+1 | i <- s] = (\max_(i <- s) S i).
  Proof.
    elim: s => [| s0 s IHs] /=; first by rewrite big_nil.
    by rewrite big_cons IHs.
  Qed.

  Lemma perm_eq_shape_rowseq s t : perm_eq s t = (shape_rowseq s == shape_rowseq t).
  Proof.
    apply/(sameP idP); apply(iffP idP).
    - move/eqP.
      rewrite -!shape_rowseq_countE /shape_rowseq_count /=.
      set mx := foldr _ _ _ => H.
      have := erefl (size [seq (count_mem i) s | i <- iota 0 mx]).
      rewrite {2}H !size_map !size_iota => Hmax.
      rewrite /perm_eq; apply /allP => i /= Hi.
      have {Hi} Hi : i < mx.
        move: Hi; rewrite mem_cat => /orP [].
        + rewrite /mx; elim s => [//= | s0 s' IHs] /=.
          rewrite inE => /orP [/eqP -> | Hi]; first by apply leq_maxl.
          rewrite leq_max; apply/orP; right.
          by apply IHs.
        + rewrite Hmax; elim t => [//= | t0 t' IHt] /=.
          rewrite inE => /orP [/eqP -> | Hi]; first by apply leq_maxl.
          rewrite leq_max; apply/orP; right.
          by apply IHt.
      have := erefl (nth 0 [seq (count_mem i) s | i <- iota 0 mx] i).
      rewrite {2}H (nth_map 0); last by rewrite -Hmax size_iota.
      rewrite (nth_map 0); last by rewrite size_iota.
      rewrite (nth_iota _ Hi) nth_iota; last by rewrite -Hmax.
      by rewrite !add0n => ->.
    - move=> Hperm.
      rewrite -!shape_rowseq_countE /shape_rowseq_count /=.
      rewrite !foldr_maxn (eq_big_perm _ Hperm) /=.
      apply/eqP; apply eq_map => i.
      by move: Hperm => /perm_eqP ->.
  Qed.

  Lemma shape_rowshape_cons l s : shape_rowseq (l :: s) = incr_nth (shape_rowseq s) l.
  Proof. by []. Qed.

  Lemma shape_rowseq_eq_size y : sumn (shape_rowseq y) = size y.
  Proof. elim: y => [//= | y0 y] /=; by rewrite sumn_incr_nth => ->. Qed.

  (* Yamanouchi word:                                                            *)
  (*   sequence of rows of the corners for an increasing sequence of partitions. *)
  (*   they are in bijection with standard tableaux                              *)
  Fixpoint is_yam s :=
    if s is s0 :: s'
    then is_part (shape_rowseq s) && is_yam s'
    else true.
  Definition is_yam_of_shape sh y := (is_yam y) && (shape_rowseq y == sh).

  Lemma is_yamP s :
    reflect
      (forall i n, count_mem n (drop i s) >= count_mem n.+1 (drop i s))
      (is_yam s).
  Proof.
    apply (iffP idP).
    - elim: s => [| s0 s IHs] //= /andP [] /is_partP [] _ Hpart /IHs Hrec {IHs}.
      case => [| i] n //=.
      + case: (altP (s0 =P n)) => Hns0.
        subst s0; rewrite ieqi1F add0n add1n.
        have:= Hrec 0 n; rewrite drop0 => /leq_trans; by apply.
      + case: (altP (s0 =P n.+1)) => Hn1s0.
        have:= Hpart n; rewrite !nth_incr_nth Hn1s0 eq_refl eq_sym ieqi1F.
        by rewrite !add0n !add1n !nth_shape_rowseq.
      + rewrite !add0n.
        have:= Hrec 0 n; by rewrite drop0.
    - elim: s => [//= | s0 s IHs] H.
      apply/andP; split.
      + move: H {IHs}. move: (s0 :: s) => {s0 s} s Hs.
        have {Hs} := Hs 0; rewrite drop0 => Hs.
        apply /is_partP; split; last by move=> i; rewrite !nth_shape_rowseq.
        * elim: s {Hs} => [//= | s0 s IHs] /=.
          by apply last_incr_nth_non0.
      + apply: IHs => i n; exact (H i.+1 n).
  Qed.

  Lemma is_part_shyam s : is_yam s -> is_part (shape_rowseq s).
  Proof. by case: s => [//= | s0 s] /= /andP []. Qed.

  Lemma yam0 y : is_yam y -> shape_rowseq y = [::] -> y = [::].
  Proof.
    case: y => [//= | y0 y] /= _.
    case: y0 => [| y0] /=; by case (shape_rowseq y).
  Qed.

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
    move=> /andP [] _; exact IHy.
  Qed.

  (* Remove the zeroes from a yam and decrease all the other entries by 1 *)
  Fixpoint decr_yam s :=
    if s is s0 :: s'
    then if s0 is s0'.+1
         then s0' :: (decr_yam s')
         else (decr_yam s')
    else [::].

  Lemma shape_decr_yam s : shape_rowseq (decr_yam s) = behead (shape_rowseq s).
  Proof.
    elim: s => [//= | s0 s /= IHs].
    case s0 => [ | s0' /=].
    - rewrite IHs /=; by case (shape_rowseq s).
    - rewrite IHs /=; case (shape_rowseq s) => [|sh0 sh //=].
      by case: s0'.
  Qed.

  Lemma is_yam_decr s : is_yam s -> (is_yam (decr_yam s)).
  Proof.
    elim: s => [//= | s0 s IHs] /= /andP [] Hpart.
    move/IHs {IHs} => Hyam; case: s0 Hpart=> [//= | s0'] /=.
    rewrite Hyam andbT shape_decr_yam.
    case H : (shape_rowseq s) => [| sh0 sh] /= /andP [] _ //=.
    by case s0'.
  Qed.

  Lemma is_out_corner_yam l0 s :
    is_yam (l0 :: s) -> is_out_corner (shape_rowseq (l0 :: s)) l0.
  Proof.
    move=> Hyam; have:= is_part_shyam (is_yam_tl Hyam) => /is_partP [] _ Hpart.
    rewrite /is_out_corner !nth_incr_nth ieqi1F eq_refl add0n add1n ltnS.
    by apply: Hpart.
  Qed.

  Lemma is_in_corner_yam l0 s :
    is_yam (l0 :: s) -> is_in_corner (shape_rowseq s) l0.
  Proof.
    rewrite /is_in_corner /=; case: l0 => [//= | l0] /=.
    case: (shape_rowseq s) => [//= | sh0 sh].
      move=> /andP [] /andP [] H1 H2 _; exfalso.
      case: l0 H1 H2 => //= l0 _; by elim: l0.
    move=> /andP [] /is_partP [] _ Hpart _.
    have /= {Hpart} := Hpart l0.
    rewrite -/(incr_nth (sh0 :: sh) l0.+1) !nth_incr_nth eq_refl add1n.
    by rewrite eq_sym ieqi1F add0n.
  Qed.

  (* Hyperstandard Yamanouchi word : 33 2222 11111 0000000 *)
  Fixpoint hyper_yam_rev sh :=
    if sh is s0 :: s then
      nseq s0 (size s) ++ hyper_yam_rev s
    else [::].
  Definition hyper_yam sh := hyper_yam_rev (rev sh).

  Lemma size_hyper_yam sh : size (hyper_yam sh) = sumn sh.
  Proof.
    elim/last_ind: sh => [//= | sh sn] /=.
    rewrite /hyper_yam -(sumn_rev (rcons _ _)) rev_rcons /= size_cat => ->.
    by rewrite size_nseq sumn_rev.
  Qed.

  Lemma incr_nth_size s : incr_nth s (size s) = rcons s 1.
  Proof.  by elim: s => [| s0 s /= ->]. Qed.

  Lemma part_rcons_ind s sn : is_part (rcons s sn.+2) -> is_part (rcons s sn.+1).
  Proof.
    elim: s => [//= | s0 s IHs] /=.
    move => /andP [] Hhead /IHs {IHs} ->; rewrite andbT.
    case: s Hhead => [//= | s1 s]; first by apply: ltn_trans.
    by rewrite !rcons_cons.
  Qed.

  (* "is_part sh" is just here to ensure that sh doesn't ends with a 0 *)
  Lemma shape_rowseq_hyper_yam sh : is_part sh -> shape_rowseq (hyper_yam sh) = sh.
  Proof.
    rewrite /hyper_yam; elim/last_ind: sh => [//= | s sn IHs].
    rewrite rev_rcons /=; case: sn => [/= | sn].
      move/is_partP; by rewrite last_rcons /= => [] [].
    elim: sn => [/= | sn /= IHsn].
      move/is_part_rconsK/IHs ->; by rewrite size_rev incr_nth_size.
    move=> Hpart; rewrite IHsn {IHsn IHs}.
    - rewrite size_rev {Hpart}; elim: s => [//= | s0 s IHs] /=.
      by rewrite IHs.
    - by apply: part_rcons_ind.
  Qed.

  Lemma hyper_yamP sh : is_part sh -> is_yam (hyper_yam sh).
  Proof.
    elim/last_ind: sh => [//= | s sn IHs].
    rewrite /hyper_yam rev_rcons /=; case: sn => [//= | sn].
      move/is_partP; by rewrite last_rcons /= => [] [].
    elim: sn => [/= | sn /= IHsn].
      move=> Hpart1; have Hpart := is_part_rconsK Hpart1.
      by rewrite (IHs Hpart) size_rev (shape_rowseq_hyper_yam Hpart) incr_nth_size Hpart1.
    move=> Hpart2; have {IHsn} /andP [] := IHsn (part_rcons_ind Hpart2).
    move=> -> ->; rewrite !andbT.
    have:= Hpart2; by rewrite -{1}(shape_rowseq_hyper_yam Hpart2) /hyper_yam rev_rcons.
  Qed.

  Lemma hyper_yam_of_shape sh : is_part sh -> is_yam_of_shape sh (hyper_yam sh).
  Proof.
    move=> H; by rewrite /is_yam_of_shape (hyper_yamP H) (shape_rowseq_hyper_yam H) /=.
  Qed.

End Yama.

Lemma is_yam_cat_any y0 y1 z :
  is_yam y0 -> is_yam y1 -> shape_rowseq y0 = shape_rowseq y1 ->
  is_yam (z ++ y0) -> is_yam (z ++ y1).
Proof.
  elim: z => [//= | z0 z IHz] /= Hy0 Hy1 H /andP [] Hpart Hyam.
  apply/andP; split; last by apply IHz.
  suff <- : shape_rowseq (z ++ y0) = shape_rowseq (z ++ y1) by [].
  apply /eqP; rewrite -perm_eq_shape_rowseq.
  by rewrite perm_cat2l perm_eq_shape_rowseq H.
Qed.

Fixpoint enum_yamshn n sh :=
  if n is n'.+1 then
    flatten [seq [seq i :: y | y <- enum_yamshn n' (decr_nth sh i)] |
                  i <- iota 0 (size sh) & is_out_corner sh i]
  else [:: [::]].
Definition enum_yamsh sh := enum_yamshn (sumn sh) sh.
Definition is_yam_of_size n y := (is_yam y) && (size y == n).

Lemma enum_yamshP sh:
  is_part sh -> all (is_yam_of_shape sh) (enum_yamsh sh).
Proof.
  move=> Hpart; apply/allP => y.
  rewrite /enum_yamsh /is_yam_of_shape; move Hn: (sumn sh) => n.
  elim: n sh Hpart Hn y => [| n IHn] /= .
    by move=> sh Hsh /part0 H0 y; rewrite mem_seq1 H0 //= => /eqP ->.
  move=> sh Hpart Hsh [/= | y0 y] /=.
  - have -> : [::] == sh = false by move: Hsh; case sh.
    by move=> /flattenP [] ltmp /mapP [] i _ -> /mapP [].
  - move/flatten_mapP => [] i; rewrite mem_filter mem_iota add0n => /and3P [] Hcorn _ Hi.
    move/mapP => [] x Hx [] Hitmp Hxtmp; subst i x.
    have Hsum : sumn (decr_nth sh y0) = n by rewrite sumn_decr_nth //= Hsh.
    have:= IHn _ (is_part_decr_nth Hpart Hcorn) Hsum _ Hx =>  /andP [] -> /eqP ->.
    by rewrite decr_nthK //= Hpart /=.
Qed.

Lemma enum_yamsh_countE sh :
  is_part sh -> forall y, is_yam_of_shape sh y -> count_mem y (enum_yamsh sh) = 1.
Proof.
  rewrite /enum_yamsh /is_yam_of_shape; move Hn: (sumn sh) => n.
  elim: n sh Hn => [| n IHn] /= .
    move=> sh Hsh /part0 H0 y.
    by rewrite (H0 Hsh) => /andP [] /yam0 H /eqP /H{H} ->.
  move=> sh Hsh  Hpart [/= | y0 y] /=.
  - by have -> : [::] == sh = false by move: Hsh; case sh.
  - move => /andP [] /andP [] _ Hyam /eqP Htmp; subst sh.
    rewrite count_flatten -map_comp; set ci := (X in map X _).
    have {ci} /eq_map -> : ci =1 fun i => i == y0.
      rewrite /ci {ci} => i /=; rewrite count_map /=.
      case (altP (i =P y0)) => [Heq | /negbTE Hneq].
      + subst i; rewrite (eq_count (a2 := pred_of_simpl (pred1 y))); first last.
          move=> s; by rewrite /= -eqseqE /= eq_refl /=.
        rewrite (incr_nthK (is_part_shyam Hyam) Hpart) IHn //=.
        * move: Hsh; rewrite sumn_incr_nth => /eqP; by rewrite eqSS => /eqP.
        * by apply: is_part_shyam.
        * by rewrite Hyam eq_refl.
      + rewrite (eq_count (a2 := pred0)); first by rewrite count_pred0.
        move=> s; by rewrite /= -eqseqE /= Hneq.
    rewrite sumn_count count_filter.
    rewrite (eq_count (a2 := pred_of_simpl (pred1 y0))); first last.
      move=> i /=; case (altP (i =P y0)) => //= ->.
      apply: is_out_corner_yam; by rewrite /= Hpart Hyam.
    rewrite -sumn_count /=.
    rewrite sumn_iota //= add0n size_incr_nth.
    by case: (ltnP y0 (size (shape_rowseq y))).
Qed.

Section YamOfShape.

Variable sh : seq nat.
Hypothesis Hpart : is_part sh.

Structure yamsh : predArgType :=
  YamSh {yamshval :> seq nat; _ : is_yam_of_shape sh yamshval}.
Canonical yamsh_subType := Eval hnf in [subType for yamshval].
Definition yamsh_eqMixin := Eval hnf in [eqMixin of yamsh by <:].
Canonical yamsh_eqType := Eval hnf in EqType yamsh yamsh_eqMixin.
Definition yamsh_choiceMixin := Eval hnf in [choiceMixin of yamsh by <:].
Canonical yamsh_choiceType := Eval hnf in ChoiceType yamsh yamsh_choiceMixin.
Definition yamsh_countMixin := Eval hnf in [countMixin of yamsh by <:].
Canonical yamsh_countType := Eval hnf in CountType yamsh yamsh_countMixin.
Canonical yamsh_subCountType := Eval hnf in [subCountType of yamsh].
Let type := sub_finType yamsh_subCountType (enum_yamshP Hpart) (enum_yamsh_countE Hpart).
Canonical yamsh_finType := Eval hnf in [finType of yamsh for type].
Canonical yamsh_subFinType := Eval hnf in [subFinType of yamsh].

Lemma yamshP (y : yamsh) : is_yam y.
Proof. by case: y => /= y /andP []. Qed.

Lemma shape_yamsh (y : yamsh) : shape_rowseq y = sh.
Proof. by case: y => /= y /andP [] _ /eqP. Qed.

Lemma enum_yamshE : map val (enum yamsh) = enum_yamsh sh.
Proof. rewrite /=; by apply enum_subP. Qed.

End YamOfShape.


Section YamOfSize.

Variable n : nat.

Lemma yamn_PredEq (sh : intpartn_subFinType n) :
  predI (is_yam_of_size n) (pred1 (val sh) \o shape_rowseq) =1 is_yam_of_shape (val sh).
Proof.
  move=> y; rewrite /is_yam_of_size /is_yam_of_shape /= -andbA; congr (_ && _).
  case: (altP (shape_rowseq y =P sh)) => /=; last by rewrite andbF.
  rewrite -shape_rowseq_eq_size => ->.
  by rewrite (intpartn_sumn sh) eq_refl.
Qed.

Lemma yamn_partition_shape_rowseq x :
  is_yam_of_size n x -> (is_part_of_n n) (shape_rowseq x).
Proof.
  by rewrite /is_yam_of_size /= shape_rowseq_eq_size => /andP [] /is_part_shyam -> ->.
Qed.

Structure yamn : predArgType :=
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
    (fun p : intpartn_subFinType n => (yamsh_subFinType (intpartnP p)))
    yamn_PredEq yamn_partition_shape_rowseq yamn_subCountType.
Canonical yamn_finType := Eval hnf in [finType of yamn for type].
Canonical yamn_subFinType := Eval hnf in [subFinType of yamn].

Lemma yamnP (y : yamn) : is_yam y.
Proof. by case: y => /= y /andP []. Qed.

Lemma yamn_sumn (y : yamn) : size y = n.
Proof. by case: y => /= y /andP [] _ /eqP. Qed.

(* Check of disjoint union enumeration *)
Lemma enum_yamnE :
  map val (enum yamn) = flatten [seq enum_yamsh p | p <- enum_partn n].
Proof.
  rewrite enum_union_finTypeE /=; congr flatten.
  rewrite (eq_map (f2 := enum_yamsh \o val)).
  - by rewrite map_comp enum_intpartnE.
  - move=> i /=; by rewrite enum_yamshE.
Qed.

End YamOfSize.

