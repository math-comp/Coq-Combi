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
Add Rec LoadPath "ALEA/src" as ALEA.
Add Rec LoadPath "../Combi/LRrule".

Require Import Misc Ccpo Qmeasure.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat seq
        ssrint div rat fintype bigop path ssralg ssrnum.
(* Import bigop before ssralg/ssrnum to get correct printing of \sum \prod*)

Require Import tools subseq partition stdtab.
Require Import rat_coerce distr shape bigallpairs recyama.

Import GRing.Theory.
Import Num.Theory.

Lemma big_nat_0cond (R : Type) (idx : R) op n f :
  \big[op/idx]_(0 <= i < n) f i = \big[op/idx]_(0 <= i < n | (i < n)%N) f i.
Proof.
  rewrite big_seq_cond /=.
  rewrite (eq_bigl (fun i => (i < n)%N)); first by [].
  move=> i; by rewrite /= mem_index_iota leq0n /= andbT.
Qed.

Local Open Scope nat_scope.

(* TODO : move in LRrule/tools *)
Lemma filter_flatten (T : eqType) (s : seq (seq T)) (P : pred T) :
  filter P (flatten s) = flatten [seq filter P i | i <- s].
Proof. elim: s => [//= | s0 s /= <-]; exact: filter_cat. Qed.

Lemma cons_head_behead (T : eqType) x (s : seq T) :
  (s != [::]) -> head x s :: behead s = s.
Proof. by case s. Qed.

Lemma belast_behead_rcons (T : eqType) x l (s : seq T) :
  belast (head x (rcons s l)) (behead (rcons s l)) = s.
Proof. case: s => [//= | s0 s]; by rewrite rcons_cons /= belast_rcons. Qed.

Lemma last_behead_rcons (T : eqType) x l (s : seq T) :
  last (head x (rcons s l)) (behead (rcons s l)) = l.
Proof. case: s => [//= | s0 s]; by rewrite rcons_cons /= last_rcons. Qed.


(* TODO : move in LRrule/tools *)
Lemma sorted_subseq_iota_rcons s n : subseq s (iota 0 n) = sorted ltn (rcons s n).
Proof.
  apply (sameP idP); apply (iffP idP).
  - elim: n s => [/= [//=| s0 s]| n IHn s].
      rewrite rcons_cons /= => /(order_path_min ltn_trans) /= /allP Hall.
      exfalso.
      suff /Hall : 0 \in rcons s 0 by [].
      by rewrite mem_rcons inE eq_refl.
    case/lastP: s => [_| s sn]; first exact: sub0seq.
    case: (ltnP sn n) => Hsn Hsort.
    + have {Hsort} Hsort : sorted ltn (rcons s sn).
        case: s Hsort => [//= | s0 s].
        by rewrite !rcons_cons /= rcons_path => /andP [].
      have /IHn : sorted ltn (rcons (rcons s sn) n).
        case: s Hsort => [_ /= | s0 s]; first by rewrite andbT.
        rewrite !rcons_cons /=.
        by rewrite (rcons_path ltn s0 (rcons s sn) n) /= last_rcons Hsn => ->.
      move/subseq_trans; apply.
      rewrite -addn1 iota_add add0n cats1.
      exact: subseq_rcons.
    + have H : sn = n.
        apply anti_leq; rewrite Hsn andbT.
        move: Hsort.
        case: s => [/= /andP []| s0 s]/=; first by rewrite ltnS.
        by rewrite rcons_path /= last_rcons ltnS => /andP [].
      subst sn.
      rewrite -addn1 iota_add add0n /= cats1.
      rewrite -subseq_rcons_eq; apply IHn.
      case: s Hsort => [//= | s0 s].
      by rewrite !rcons_cons /= rcons_path => /andP [].
  - move=> Hsubs.
    apply: (subseq_sorted ltn_trans (s2 := (iota 0 n.+1))).
    + by rewrite -addn1 iota_add add0n /= cats1 -subseq_rcons_eq.
    + exact: iota_ltn_sorted.
Qed.


(* TODO : move in LRrule/partition.v *)
Lemma is_in_part_le (sh : seq nat) r c j k :
  is_part sh -> is_in_shape sh r c -> j <= r -> k <= c -> is_in_shape sh j k.
Proof.
  rewrite /is_in_shape => /is_part_ijP [] _ Hpart Hcr /Hpart Hrj Hkc.
  exact: leq_ltn_trans Hkc (leq_trans Hcr Hrj).
Qed.


(* TODO : move in LRrule/partition.v *)
Lemma incr_first_n_nthC sh i j :
  incr_first_n (incr_nth sh i) j = incr_nth (incr_first_n sh j) i.
Proof.
  elim: sh i j => [| s0 sh IHsh].
    elim=> [| i IHi] [|j] //=.
    have {IHi} /= <- := IHi j.
    by case: i.
  case=> [| i] [| j] //=.
  by rewrite IHsh.
Qed.

(* TODO : move in LRrule/partition.v *)
Lemma incr_nth_conj_part sh i :
  is_part sh -> is_in_corner sh i ->
  conj_part (incr_nth sh i) = incr_nth (conj_part sh) (nth 0 sh i).
Proof.
  elim: sh i => [| s0 sh IHsh] i /=.
    by rewrite /is_in_corner /= !nth_nil => _ /orP [] // /eqP ->.
  move=> /= /andP [] H0 Hpart.
  case: i => [_ | i Hcrn]/=.
    have Hszconj: (size (conj_part sh) <= s0)%N.
      rewrite (size_conj_part Hpart).
      move: H0; case sh => [| n _] //=; exact: ltnW.
    have Hszn : size (incr_first_n (conj_part sh) s0.+1) = s0.+1.
      by rewrite size_incr_first_n; last exact: (leq_trans Hszconj).
    apply (eq_from_nth (x0 := 0)).
    - rewrite Hszn.
      by rewrite size_incr_nth ltnNge (size_incr_first_n Hszconj) leqnn /=.
    - move=> i; rewrite Hszn => Hi.
      rewrite nth_incr_nth !nth_incr_first_n Hi ltn_neqAle.
      move: Hi; rewrite ltnS eq_sym => ->.
      case: eqP => /= _; by rewrite ?add0n ?add1n.
  rewrite (IHsh _ Hpart); first exact: incr_first_n_nthC.
  move: Hcrn => /=; by case: i.
Qed.

(* TODO : move in LRrule/partition.v *)
Lemma is_in_corner_conj_part sh r :
  is_part sh -> is_in_corner sh r -> is_in_corner (conj_part sh) (nth 0 sh r).
Proof.
  case: (altP ( r =P 0)) => Hr; rewrite /is_in_corner /= => Hpart /orP [].
  - move=> /eqP ->.
    have := part_head_non0 Hpart.
    case: sh Hpart => [//= | s0 sh] /= /andP [] Hs0 Hpart Hs0n0.
    apply/orP; right.
    rewrite !nth_incr_first_n ltnn.
    have -> /= : s0.-1 < s0 by move: Hs0n0; case s0.
    rewrite ltnS {Hs0}.
    case: s0 Hs0n0 => [//= | s0] _.
    have := is_part_conj Hpart => /is_partP [] _; by apply.
 - by rewrite Hr ltnn.
 - by rewrite (negbTE Hr).
 - move=> Hnthr.
   case: eqP => //= /eqP H.
   have : nth 0 sh r <= nth 0 sh r < nth 0 sh r.-1 by rewrite leqnn Hnthr.
   rewrite -(nth_conjE _ Hpart Hr) => /eqP.
   rewrite -(conj_ltnE Hpart) => ->.
   move: H; by case: (nth 0 sh r).
Qed.

(* TODO : move in LRrule/partition.v *)
Lemma out_corner_incr_nth sh i :
  is_part sh -> is_in_corner sh i -> is_out_corner (incr_nth sh i) i.
Proof.
  rewrite /is_in_corner /is_out_corner /= nth_incr_nth eq_refl add1n.
  case: i => [/= | i].
    case: sh => [// | s0 [// | s1 s]] /= /andP [].
    by rewrite ltnS.
  move=> Hpart /orP [] //; rewrite [i.+1.-1]/=.
  elim: sh i Hpart => [| s0 sh IHsh] i /=; first by rewrite !nth_nil.
  move=> /andP [] Hhead Hpart.
  case: i => [_|i].
    move: Hhead; case: sh Hpart {IHsh} => [//= | s1 [//= | s2 sh]] /= /andP [].
    by rewrite ltnS.
  by move=> /(IHsh i Hpart).
Qed.

(* TODO : move in LRrule/partition.v *)
Lemma nth_decr_nth sh i :
  nth 0 (decr_nth sh i) i = (nth 0 sh i).-1.
Proof. by elim: i sh => [| i IHi] [| [|[|s0]] sh] /=. Qed.

(* TODO : move in LRrule/partition.v *)
Lemma nth_decr_nth_neq sh i j :
  is_part sh -> is_out_corner sh i -> i != j -> nth 0 (decr_nth sh i) j = nth 0 sh j.
Proof.
  move=> Hpart Hcrn /negbTE Hij.
  rewrite -{2}(decr_nthK Hpart Hcrn).
  by rewrite nth_incr_nth Hij add0n.
Qed.

(* TODO : move in LRrule/partition.v *)
Lemma in_corner_decr_nth sh i :
  is_part sh -> is_out_corner sh i -> is_in_corner (decr_nth sh i) i.
Proof.
  move=> Hpart Hout.
  rewrite /is_in_corner /=.
  case: i Hout => [//=|i] Hout; rewrite [i.+1.-1]/=.
  apply/orP; right.
  rewrite nth_decr_nth nth_decr_nth_neq //; last by rewrite eq_sym ieqi1F.
  move: Hout; rewrite /is_out_corner => Hi2.
  have:= is_partP _ Hpart => [] [] _ Hdecr.
  apply: leq_trans _ (Hdecr i).
  move: Hi2; by case: (nth 0 sh i.+1).
Qed.


(* Corner Box ***********************************)

Definition is_corner_box sh r c := (is_out_corner sh r && (c == (nth 0 sh r).-1)).

Lemma is_corner_box_in_part sh r c :
  is_corner_box sh r c -> is_in_shape sh r c.
Proof.
  rewrite /is_corner_box /is_in_shape /is_out_corner => /andP [] Hr /eqP ->.
  move: Hr; by case (nth 0 sh r).
Qed.

Lemma is_corner_box_conj_part sh u v :
  is_part sh -> is_corner_box sh u v -> is_corner_box (conj_part sh) v u.
Proof.
  rewrite /is_corner_box {1}/is_out_corner => Hpart /andP [] Hcorn /eqP Hv.
  subst.
  rewrite (out_corner_conj_part Hpart Hcorn) /= eq_sym.
  have : nth 0 sh u.+1 <= (nth 0 sh u).-1 < (nth 0 sh u).
    move: Hcorn; case: (nth 0 sh u) => [//= | shu].
    by rewrite ltnS [shu.+1.-1]/= => -> /=.
  by rewrite -nth_conjE // => /eqP -> /=.
Qed.


(* Arm/Leg/Hook length ***********************************)

Definition arm_length  sh r c := ((nth 0 sh r) - c).-1.
Definition leg_length  sh r c := (arm_length (conj_part sh) c r).
Definition al_length   sh r c := ((arm_length sh r c) + (leg_length sh r c)).
Definition hook_length sh r c := (al_length sh r c).+1.

Lemma al_length_conj_part sh r c :
  is_part sh -> al_length (conj_part sh) r c = al_length sh c r.
Proof. by rewrite /al_length /leg_length addnC => /conj_partK ->. Qed.

Lemma arm_length_ler sh r c j :
  is_part sh -> r < j -> is_in_shape sh j c -> arm_length sh j c <= arm_length sh r c.
Proof.
  rewrite /al_length /is_in_shape /leg_length /arm_length => /is_part_ijP [] _ Hpart Hr Hc.
  have Hshjr := Hpart _ _ (ltnW Hr).
  rewrite -ltnS !prednK; first by apply leq_sub2r.
  - rewrite subn_gt0; exact: leq_trans Hc Hshjr.
  - rewrite subn_gt0; exact: Hc.
Qed.

Lemma arm_length_ltl sh r c j :
  is_part sh -> c < j -> is_in_shape sh r j -> arm_length sh r j < arm_length sh r c.
Proof.
  rewrite /al_length /is_in_shape /leg_length /arm_length => /is_part_ijP [] _ Hpart Hc Hr.
  have Hshjr := Hpart _ _ (ltnW Hr).
  have Hcr := ltn_trans Hc Hr.
  rewrite -ltnS !prednK; first by apply ltn_sub2l.
  - rewrite subn_gt0; exact: Hcr.
  - rewrite subn_gt0; exact: Hr.
Qed.

Lemma leg_length_ltr sh r c j :
  is_part sh -> r < j -> is_in_shape sh j c -> leg_length sh j c < leg_length sh r c.
Proof.
  rewrite /leg_length => Hpart Hr.
  rewrite (is_in_conj_part Hpart).
  exact: (arm_length_ltl (is_part_conj _)).
Qed.

Lemma leg_length_lel sh r c j :
  is_part sh -> c < j -> is_in_shape sh r j -> leg_length sh r j <= leg_length sh r c.
Proof.
  rewrite /leg_length => Hpart Hr.
  rewrite (is_in_conj_part Hpart).
  exact: (arm_length_ler (is_part_conj _)).
Qed.

Lemma al_length_ltl sh r c j :
  is_part sh -> c < j -> is_in_shape sh r j -> al_length sh r j < al_length sh r c.
Proof.
  rewrite /al_length => Hpart Hr Hc.
  rewrite -addSn; apply leq_add.
  exact: arm_length_ltl.
  exact: leg_length_lel.
Qed.

Lemma al_length_ltr sh r c j :
  is_part sh -> r < j -> is_in_shape sh j c -> al_length sh j c < al_length sh r c.
Proof.
  rewrite /al_length => Hpart Hr Hc.
  rewrite -addnS; apply leq_add.
  exact: arm_length_ler.
  exact: leg_length_ltr.
Qed.

Lemma al_length0_corner sh r c :
  is_part sh -> is_in_shape sh r c -> al_length sh r c = 0 -> is_corner_box sh r c.
Proof.
  move => Hpart.
  rewrite /is_in_shape => Hin_part /eqP.
  rewrite addn_eq0 => /andP [Hnth Hhaut].
  apply /andP; split.
  - rewrite /is_out_corner.
    apply: (leq_trans _ Hin_part).
    rewrite ltnS (conj_leqE Hpart).
    by rewrite -subn_eq0 subnS.
  - rewrite eqn_leq; apply /andP; split.
    + rewrite -ltnS; apply (leq_trans Hin_part).
      exact: leqSpred.
    + by rewrite -subn_eq0 -subn1 -subnAC subn1.
Qed.

Lemma corner_arm_length0 sh r c :
  is_part sh -> is_corner_box sh r c -> arm_length sh r c = 0.
Proof.
  rewrite /is_corner_box /is_out_corner /arm_length => Hpart /andP [] _ /eqP ->.
  case: (nth 0 sh r) => [//= | n]; by rewrite subSn //= subnn.
Qed.

Lemma corner_leg_length0 sh r c :
  is_part sh -> is_corner_box sh r c -> leg_length sh r c = 0.
Proof.
  rewrite /leg_length => Hpart Hcorn.
  apply (corner_arm_length0 (is_part_conj Hpart)).
  exact: is_corner_box_conj_part.
Qed.

Lemma corner_al_length0 sh r c :
  is_part sh -> is_corner_box sh r c -> al_length sh r c = 0.
Proof.
  rewrite /al_length => Hpart Hcorn.
  by rewrite corner_arm_length0 // corner_leg_length0 //.
Qed.

Lemma arm_length_corner_box sh r c u v :
  is_part sh ->
  r <= u -> c <= v -> is_corner_box sh u v ->
  arm_length sh r c = arm_length sh u c + arm_length sh r v.
Proof.
  move=> /is_part_ijP [] _ Hpart.
  rewrite /is_corner_box /is_out_corner => Hr Hc /andP [] Hcorn /eqP Hv.
  subst v.
  rewrite /arm_length.
  have {Hpart Hr} := Hpart _ _ Hr.
  move: Hc Hcorn; case: (nth 0 sh u) => [//= | pu].
  rewrite [_.+1.-1]/= => Hcpu; rewrite (subSn Hcpu) => _ Hpu.
  have := leq_ltn_trans Hcpu Hpu.
  case: (nth 0 sh r) Hpu => [//= | pr].
  rewrite !ltnS => Hpu Hcpr.
  by rewrite !subSn //= addnC addnBA // subnK.
Qed.

Lemma leg_length_corner_box sh r c u v :
  is_part sh ->
  r <= u -> c <= v -> is_corner_box sh u v ->
  leg_length sh r c = leg_length sh u c + leg_length sh r v.
Proof.
  rewrite /leg_length addnC => Hpart Hru Hcv Hcorn.
  apply: (arm_length_corner_box (is_part_conj Hpart) Hcv Hru).
  exact: is_corner_box_conj_part.
Qed.

Lemma al_length_corner_box sh r c u v :
  is_part sh -> r <= u -> c <= v -> is_corner_box sh u v ->
  al_length sh r c = al_length sh u c + al_length sh r v.
Proof.
  move=> Hpart Hru Hcv Hcorn.
  rewrite /al_length (arm_length_corner_box Hpart Hru Hcv Hcorn).
  rewrite /al_length (leg_length_corner_box Hpart Hru Hcv Hcorn).
  rewrite !addnA; congr (_ + _); rewrite -!addnA; congr (_ + _); by rewrite addnC.
Qed.

Lemma arm_length_incr_nth_row sh r c :
  is_in_shape sh r c -> arm_length (incr_nth sh r) r c = (arm_length sh r c).+1.
Proof.
  rewrite /is_in_shape /arm_length nth_incr_nth eq_refl add1n => Hc.
  rewrite prednK; last by rewrite subn_gt0.
  by rewrite subSn; last by apply ltnW.
Qed.

Lemma arm_length_incr_nth_nrow sh r c i :
  i != r -> arm_length (incr_nth sh i) r c = (arm_length sh r c).
Proof.
  rewrite /arm_length nth_incr_nth => /negbTE ->.
  by rewrite add0n.
Qed.

Lemma al_length_incr_nth_row sh r c :
  is_part sh -> is_in_corner sh r ->
  is_in_shape sh r c -> al_length (incr_nth sh r) r c = (al_length sh r c).+1.
Proof.
  rewrite /hook_length /al_length => Hpart Hcrn Hin.
  rewrite (arm_length_incr_nth_row Hin) addSn.
  congr (_ + _).+1.
  rewrite /leg_length /arm_length (incr_nth_conj_part Hpart Hcrn) nth_incr_nth.
  move: Hin; rewrite /is_in_shape eq_sym ltn_neqAle => /andP [] /negbTE -> _.
  by rewrite add0n.
Qed.

Lemma al_length_incr_nth_col sh r i :
  is_part sh -> is_in_corner sh r ->
  is_in_shape sh i (nth 0 sh r) ->
  al_length (incr_nth sh r) i (nth 0 sh r) = (al_length sh i (nth 0 sh r)).+1.
Proof.
  move=> Hpart Hcorn Hin.
  rewrite -al_length_conj_part; last exact: is_part_incr_nth.
  rewrite incr_nth_conj_part // al_length_incr_nth_row; first last.
    - by rewrite -is_in_conj_part.
    - exact: is_in_corner_conj_part.
    - exact: is_part_conj.
  by rewrite al_length_conj_part.
Qed.

Lemma al_length_incr_nth sh i r c :
  is_part sh -> is_in_corner sh i ->
  is_in_shape sh r c ->
  i != r -> nth 0 sh i != c ->
  al_length (incr_nth sh i) r c = al_length sh r c.
Proof.
  rewrite /al_length => Hpart Hcorn Hin Hr Hc.
  congr (_ + _).
  - exact: arm_length_incr_nth_nrow.
  - rewrite /leg_length incr_nth_conj_part //.
    exact: arm_length_incr_nth_nrow.
Qed.


Open Scope ring_scope.

Lemma prod_al_length_quot_row p Alpha Beta :
  is_part p -> is_corner_box p Alpha Beta ->
  \prod_(i <- enum_box_in (decr_nth p Alpha) | i.1 == Alpha)
   ((al_length p i.1 i.2).+1%:Q / (al_length (decr_nth p Alpha) i.1 i.2).+1%:Q) =
  \prod_(0 <= j < Beta) (1 + (al_length p Alpha j)%:Q^-1).
Proof.
  move=> Hpart Hcorn.
  have := Hcorn => /andP [] Hcrn /eqP HBeta.
  have:= (decr_nthK Hpart Hcrn); set p' := decr_nth p Alpha => Hp.
  rewrite big_seq_cond.
  rewrite (eq_bigr (fun i => (1 + (al_length p Alpha i.2)%:Q^-1))); first last.
    move=> [r c] /= /andP []; rewrite mem_enum_box_in unfold_in /= => Hin /eqP Hr.
    subst r.
    rewrite -Hp al_length_incr_nth_row; first last.
    - exact: Hin.
    - rewrite /p'.
    - by apply in_corner_decr_nth.
    - by apply is_part_decr_nth.
    move: (al_length p' Alpha c) => n.
    have Hn : n.+1%:Q != 0 by rewrite intr_eq0.
    rewrite -{3}(divff Hn) -{3}div1r -mulrDl; congr (_ / _).
    by rewrite -addn1 PoszD mulrzDl.
  rewrite -big_seq_cond.
  set f := (X in _ = \prod_(i <- _) X i).
  transitivity (\prod_(i <- [seq i.2 | i <- enum_box_in p' & i.1 == Alpha]) f i).
    rewrite big_map big_filter; exact: eq_bigr.
  move: (f) => F {f}.
  rewrite big_map /enum_box_in filter_flatten big_flatten /= -map_comp big_map.
  case: (ltnP Alpha (size p')) => Halpha.
  + rewrite (bigD1_seq Alpha) /=; first last.
    - exact: iota_uniq.
    - rewrite mem_iota add0n.
    - by rewrite Halpha.
    rewrite big_filter big_map (eq_bigl (fun _ => true));
      last by move=> i; rewrite /= eq_refl.
    rewrite /p' nth_decr_nth -HBeta (eq_bigr F); last by [].
    rewrite /index_iota subn0 mulrC.
    rewrite (eq_bigr (fun _ => 1)); first by rewrite big1 // mul1r.
    move=> i /negbTE Hi.
    by rewrite big_filter big_map big_pred0.
  + move: HBeta; rewrite -nth_decr_nth (nth_default _ Halpha) => ->.
    rewrite /index_iota /= big_nil.
    rewrite big_seq_cond.
    apply big1 => i; rewrite andbT mem_iota /= add0n => Hi.
    rewrite big_filter big_map big_pred0 // => j /=.
    exact: ltn_eqF (leq_trans Hi Halpha).
Qed.

Close Scope ring_scope.

Section FindCorner.

Variable p : intpart.

Fact is_part_p : is_part p. Proof. by apply intpartP. Qed.
Hint Resolve is_part_p.

(* Hook Seq ****************************************)

Local Notation conj := (conj_part p).

Definition is_in_hook (r c : nat) (k l : nat) :=
  ((r == k) && (c < l < nth 0 p r)) ||
  ((c == l) && (r < k < nth 0 conj c)).

Lemma is_in_hook_shape (r c : nat) (k l : nat) :
   is_in_shape p r c -> is_in_hook r c k l -> is_in_shape p k l.
Proof.
  rewrite /is_in_shape /is_in_hook => Hj /orP [] /and3P [] /eqP <- // H1 H2.
  by rewrite conj_ltnE.
Qed.

Definition hook_next_seq r c : seq (nat+nat) :=
  [seq inl k | k <- iota r.+1 ((nth 0 conj c).-1 - r)] ++
  [seq inr k | k <- iota c.+1 ((nth 0 p r).-1 - c)].
Definition hook_next r c n : nat * nat :=
    match n with inl k => (k,c) | inr k => (r,k) end.
Definition hook_seq r c := [seq hook_next r c n | n <- hook_next_seq r c].

Lemma size_hook_next_seq r c : size (hook_next_seq r c) = al_length p r c.
Proof.
  rewrite size_cat !size_map !size_iota.
  by rewrite /al_length /leg_length /arm_length -!subn1 -!subnDA !add1n !addn1 addnC.
Qed.

Lemma size_hook_seq r c : size (hook_seq r c) = al_length p r c.
Proof. by rewrite size_map size_hook_next_seq. Qed.

Lemma ltnPred a b : a < b -> (a <= b.-1).
Proof. by case: b. Qed.

Lemma iota_hookE a b c : a < b -> b < a.+1 + (c.-1 - a) = (b < c).
Proof.
  move => Hab; rewrite addSn.
  case: (ltnP b c) => Hbc.
  - have:= ltn_trans Hab Hbc => /ltnPred/subnKC ->.
    exact: (leq_trans Hbc (leqSpred _)).
  - case: c Hbc => [_ | c Hbc] /=.
    + by rewrite sub0n addn0 ltnS leqNgt Hab.
    + rewrite ltnS.
       case: (leqP a c).
      * move/subnKC ->; by rewrite leqNgt Hbc.
      * move=> /ltnW; rewrite {1}/leq => /eqP ->.
        by rewrite addn0 leqNgt Hab.
Qed.

Lemma in_hook_seqP (r c : nat) (k l : nat) :
   (k,l) \in (hook_seq r c) = is_in_hook r c k l.
Proof.
  apply/(sameP idP); apply(iffP idP).
  - rewrite /is_in_hook => /orP [] /and3P [] /eqP <-.
    + move => {k} Hc Hr.
      apply/mapP; exists (inr l); last by [].
      rewrite mem_cat; apply/orP; right; rewrite mem_map; last by move=> u v [].
      by rewrite mem_iota Hc /= iota_hookE.
    + move => {l} Hr Hc.
      apply/mapP; exists (inl k); last by [].
      rewrite mem_cat; apply/orP; left; rewrite mem_map; last by move=> u v [].
      by rewrite mem_iota Hr /= iota_hookE.
  - move=> /mapP [] [] x; rewrite mem_cat => /orP [] /=.
    + rewrite mem_map; last by move=> u v [].
      rewrite mem_iota => /andP [] Hrx Hxr /= [] -> -> {k l}.
      rewrite /is_in_hook; apply/orP; right.
      by rewrite eq_refl Hrx /= -(iota_hookE _ Hrx).
    + move=> /mapP [] y _; discriminate.
    + move=> /mapP [] y _; discriminate.
    + rewrite mem_map; last by move=> u v [].
      rewrite mem_iota => /andP [] Hcx Hxc /= [] -> -> {k l}.
      rewrite /is_in_hook; apply/orP; left.
      by rewrite eq_refl Hcx /= -(iota_hookE _ Hcx).
Qed.

Lemma hook_seq_empty (r c : nat) :
  is_in_shape p r c -> hook_seq r c = [::] -> is_corner_box p r c.
Proof.
  move=> Hpart Hhl; by apply al_length0_corner; last by rewrite -size_hook_seq Hhl.
Qed.


(* Traces ****************************************)

Definition is_trace (A B : seq nat) :=
      [&& (A != [::]), (B != [::]),
          sorted ltn A, sorted ltn B &
          is_corner_box p (last 0 A) (last 0 B) ].

Lemma is_trace_tll (a:nat) (A B : seq nat) : A != [::] -> is_trace (a::A) B -> is_trace A B.
Proof.
  rewrite /is_trace => HA /and5P [] _ -> /path_sorted -> ->.
  rewrite HA /=; by case: A HA.
Qed.

Lemma is_trace_tlr (b:nat) (A B : seq nat) : B != [::] -> is_trace A (b::B) -> is_trace A B.
Proof.
  rewrite /is_trace => HB /and5P [] -> _ -> /path_sorted ->.
  rewrite HB /=; by case: B HB.
Qed.

Lemma is_trace_lastr (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> is_trace (a :: A) [:: last b B].
Proof.
  elim: B b => [//= | B0 B IHB] b /= /is_trace_tlr H.
  have {H} /H : B0 :: B != [::] by [].
  exact: IHB.
Qed.

Lemma is_trace_lastl (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> is_trace [:: last a A] (b :: B).
Proof.
  elim: A a => [//= | A0 A IHA] a /= /is_trace_tll H.
  have {H} /H : A0 :: A != [::] by [].
  exact: IHA.
Qed.

Lemma sorted_in_leq_last A a : sorted ltn A -> a \in A -> a <= last 0 A.
Proof.
  elim: A a => [//= | A0 A IHA] a /= Hpart.
  rewrite inE => /orP [/eqP |] Ha.
  - subst a => {IHA}.
    elim: A A0 Hpart => [//= | A1 A IHA] A0 /= /andP [] /ltnW H01 /IHA{IHA}.
    exact: leq_trans H01.
  - have {IHA Hpart} := IHA _ (path_sorted Hpart) Ha.
    by case: A Ha.
Qed.

Lemma sorted_leq_last A a : sorted ltn (a :: A) -> a <= last a A.
Proof.
  move=> /sorted_in_leq_last H.
  by have /H /= : a \in (a :: A) by rewrite inE eq_refl.
Qed.

Lemma is_trace_in_in_shape (A B : seq nat) : is_trace A B ->
  forall a b, a \in A -> b \in B -> is_in_shape p a b.
Proof.
  rewrite /is_trace => /and5P [] _ _ HltnA HltnB /is_corner_box_in_part Hpart a b Ha Hb.
  apply: (@is_in_part_le p (last 0 A) (last 0 B) _ _ (intpartP p) Hpart);
    exact: sorted_in_leq_last.
Qed.

Lemma is_trace_in_shape (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> is_in_shape p a b.
Proof. move/is_trace_in_in_shape; apply; by rewrite inE eq_refl. Qed.

Lemma trace_size_arm_length (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> size B <= arm_length p a b.
Proof.
  elim: B b => [//= | B0 B IHB] b /= Htrace.
  apply: (leq_ltn_trans (IHB _ (is_trace_tlr _ Htrace))); first by [].
  have:= Htrace => /and5P [] _ _ _ /= /andP [] Hb _ _.
  rewrite {IHB} /arm_length.
  suff HB0 : B0 < nth 0 p a.
    rewrite -ltnS prednK; last by rewrite subn_gt0.
    rewrite -ltnS prednK //; last by rewrite subn_gt0; exact: (ltn_trans Hb HB0).
    rewrite ltnS; apply ltn_sub2l; last exact Hb.
    exact: (ltn_trans Hb HB0).
  rewrite -/(is_in_shape _ _ _).
  by apply (is_trace_in_in_shape Htrace); rewrite !inE eq_refl /= ?orbT.
Qed.

Lemma trace_size_leg_length (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> size A <= leg_length p a b.
Proof.
  elim: A a => [//= | A0 A IHA] a /= Htrace.
  apply: (leq_ltn_trans (IHA _ (is_trace_tll _ Htrace))); first by [].
  have:= Htrace => /and5P [] _ _ /= /andP [] Ha _ _ _.
  rewrite {IHA} /leg_length.
  suff HA0 : A0 < nth 0 conj b.
    rewrite -ltnS prednK; last by rewrite subn_gt0.
    rewrite -ltnS prednK //; last by rewrite subn_gt0; exact: (ltn_trans Ha HA0).
    rewrite ltnS; apply ltn_sub2l; last exact Ha.
    exact: (ltn_trans Ha HA0).
  rewrite -/(is_in_shape _ _ _).
  rewrite -is_in_conj_part //.
  by apply (is_trace_in_in_shape Htrace); rewrite !inE eq_refl /= ?orbT.
Qed.

Lemma size_tracer (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> size B <= al_length p a b.
Proof.
  move=> /trace_size_arm_length/leq_trans; apply.
  by rewrite leq_addr.
Qed.

Lemma size_tracel (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> size A <= al_length p a b.
Proof.
  move=> /trace_size_leg_length/leq_trans; apply.
  by rewrite leq_addl.
Qed.

Lemma is_trace_corner_nil (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) ->
  (size (hook_next_seq a b) == 0) = (A == [::]) && (B == [::]).
Proof.
  rewrite size_hook_next_seq.
  move=> Htrace; apply (sameP idP); apply (iffP idP).
  - move=> /andP [] /eqP HA /eqP HB; subst.
    move: Htrace => /and5P [] _ _ _ _ /=.
    rewrite /is_corner_box /al_length /leg_length /arm_length /is_out_corner.
    move => /andP [] Ha /eqP Hb; subst.
    have -> : (nth 0 p a - (nth 0 p a).-1) = 1.
      move: Ha; case: (nth 0 p a) => [//= | pa] _.
      by rewrite /= subSn // subnn.
    rewrite /= add0n.
    suff -> : nth 0 conj (nth 0 p a).-1 = a.+1 by rewrite subSn // subnn.
    apply/eqP; rewrite nth_conjE //.
    move: Ha; case: (nth 0 p a) => [//= | pa].
    by rewrite !ltnS => -> /=.
  - move=> /eqP Hal.
    have := size_tracel Htrace; have := size_tracer Htrace.
    by rewrite Hal !leqn0 => /nilP -> /nilP ->.
Qed.

Lemma al_length_last_rectangle (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) ->
  al_length p a b = al_length p (last a A) b + al_length p a (last b B).
Proof.
  rewrite /is_trace => /and5P [] _ _ HA HB /=.
  exact: al_length_corner_box (sorted_leq_last HA) (sorted_leq_last HB).
Qed.


Definition trace_seq (last : nat) : seq (seq nat) :=
  [seq rcons tr last | tr <- enum_subseqs (iota 0 last)].

Definition enum_trace (Alpha Beta : nat) : seq ((seq nat) * (seq nat)) :=
  [seq (A, B) | A <- trace_seq Alpha, B <- trace_seq Beta].

(* TODO : move in subseq *)
Lemma cons_in_enum_subseq (T : countType) x0 (x s : seq T) :
  x0 :: x \in enum_subseqs (T:=T) s -> x0 \in s.
Proof.
  elim: s => [//= | s0 s IHs] /=.
  rewrite inE mem_cat => /orP [].
  - move=> /mapP [] x1 _ [] -> _.
    by rewrite eq_refl.
  - move/IHs ->; by rewrite orbT.
Qed.

(* TODO : move in subseq *)
Lemma enum_subseqs_uniq (T : countType) (s : seq T) : uniq s -> uniq (enum_subseqs s).
Proof.
  elim: s => [//= | s0 s IHs] /= /andP [] Hs0 /IHs{IHs} Huniq.
  rewrite cat_uniq; apply/and3P; split.
  - by rewrite map_inj_uniq // => i j [].
  - apply/hasP => [] [] x.
    case: x => [_| x0 x] /=; first by move=> /mapP [] y _.
    move=> /cons_in_enum_subseq Hs0' /mapP [] y _ [] Hx0 _.
    move: Hs0; by rewrite -Hx0 Hs0'.
  - exact: Huniq.
Qed.

Lemma trace_seq_uniq l : uniq (trace_seq l).
Proof.
  rewrite map_inj_uniq; last exact: rconsK.
  apply enum_subseqs_uniq; exact: iota_uniq.
Qed.

Lemma enum_trace_uniq (Alpha Beta : nat) : uniq (enum_trace Alpha Beta).
Proof.
  rewrite /enum_trace; apply allpairs_uniq.
  - exact: trace_seq_uniq.
  - exact: trace_seq_uniq.
  - by move=> [i1 i2] [j1 j2].
Qed.

Lemma trace_corner_box (Alpha Beta : nat) :
  is_corner_box p Alpha Beta ->
  forall A B, A \in trace_seq Alpha -> B \in trace_seq Beta -> is_trace A B.
Proof.
  move=> Hcorn A B.
  move=> /mapP [] A' /(allP (enum_subseqsP (iota 0 Alpha))) HsubA -> {A}.
  move=> /mapP [] B' /(allP (enum_subseqsP (iota 0 Beta)))  HsubB -> {B}.
  by rewrite /is_trace !rcons_nilF /= -!sorted_subseq_iota_rcons HsubA HsubB !last_rcons.
Qed.

Lemma trace_seqlP (A B : seq nat) :
  is_trace A B -> A \in trace_seq (last 0 A).
Proof.
  move=> /and5P [].
  case/lastP: A => [//= | A lA] _ _ Hsort _ /= _.
  rewrite last_rcons /trace_seq.
  apply/mapP; exists A; last by [].
  apply: mem_enum_subseqs.
  by rewrite sorted_subseq_iota_rcons.
Qed.

Lemma trace_seqrP (A B : seq nat) :
  is_trace A B -> B \in trace_seq (last 0 B).
Proof.
  move=> /and5P [].
  case/lastP: B => [//= | B lB] _ _ _ Hsort /= _.
  rewrite last_rcons /trace_seq.
  apply/mapP; exists B; last by [].
  apply: mem_enum_subseqs.
  by rewrite sorted_subseq_iota_rcons.
Qed.

Lemma enum_traceP (Alpha Beta : nat) :
  is_corner_box p Alpha Beta ->
  forall A B,
    (A, B) \in enum_trace Alpha Beta =
    [&& (is_trace A B), (last 0 A == Alpha) & (last 0 B == Beta)].
Proof.
  move=> Hcorn A B.
  apply (sameP idP); apply (iffP idP).
  - move=> /and3P [] Htrace /eqP HlA /eqP HlB.
    apply/allpairsP; exists (A, B) => /=; split.
    + rewrite -HlA; exact: (trace_seqlP Htrace).
    + rewrite -HlB; exact: (trace_seqrP Htrace).
    + by [].
  - move=> /allpairsP [] [eA eB] /= [] HA HB [] H1 H2; subst eA eB.
    apply/and3P; split.
    + exact: (trace_corner_box Hcorn).
    + move: HA => /mapP [] A' _ ->; by rewrite last_rcons.
    + move: HB => /mapP [] B' _ ->; by rewrite last_rcons.
Qed.


(* Probabilistic algorithm ****************************************)

Fixpoint walk_to_corner (m : nat) (i j : nat) : distr ((seq nat) * (seq nat)) :=
   if m is m'.+1 then
     let s := hook_next_seq i j in
     (if size s is _.+1
     then Mlet (Uniform (unif_def (inl (0 : nat)) s))
          (fun n => match n with inl k =>
               Mlet (walk_to_corner m' k j) (fun X => Munit (i::X.1,X.2))
                               | inr k =>
               Mlet (walk_to_corner m' i k) (fun X => Munit (X.1,j::X.2))
                    end)
     else Munit ([::i],[::j]))
   else Munit ([::i],[::j]).

Lemma walk_to_corner0_simpl r c : walk_to_corner 0 r c = Munit ([:: r],[:: c]).
Proof. by []. Qed.

Lemma walk_to_corner_end_simpl m r c :
  (size (hook_next_seq r c) = 0) -> walk_to_corner m r c = Munit ([:: r],[:: c]).
Proof. by case m => [| n] //= ->. Qed.

Lemma walk_to_corner_rec_simpl m r c :
  forall (Hs : (size (hook_next_seq r c) != 0)),
    walk_to_corner (m.+1) r c = Mlet (Uniform (mkunif (hook_next_seq r c) Hs))
      (fun n => match n with
                  | inl k => Mlet (walk_to_corner m k c) (fun X => Munit (r::X.1, X.2))
                  | inr k => Mlet (walk_to_corner m r k) (fun X => Munit (X.1, c::X.2))
                end).
Proof. rewrite /=; by case (hook_next_seq r c). Qed.

Open Scope ring_scope.

Lemma walk_to_corner_inv m r c :
  mu (walk_to_corner m r c)
     (fun HS => [&& (size   HS.1 != 0), (size   HS.2 != 0),
                    (head 0 HS.1 == r)& (head 0 HS.2 == c)]%N)
      = 1.
Proof.
  elim: m r c => [| n Hn] r c.
    by rewrite /= 2!eq_refl.
  case (altP (size (hook_next_seq r c) =P 0%N)) => [H0|Hs].
  - by rewrite walk_to_corner_end_simpl //= !eq_refl.
  - rewrite (walk_to_corner_rec_simpl _ Hs).
    rewrite Mlet_simpl mu_one_eq //.
    move => [] k /=.
    + apply: (mu_bool_impl1 _ _ _ _ (Hn k c)) => [] [A B] /=.
      apply /implyP => /and4P [H1 H2 H3 H4].
      by rewrite H2 H4 eq_refl.
    + apply: (mu_bool_impl1 _ _ _ _ (Hn r k)) => [] [A B] /=.
      apply /implyP => /and4P [H1 H2 H3 H4].
      by rewrite H1 H3 eq_refl.
Qed.

Definition charfun (A B : seq nat) := (fun x : seq nat * seq nat => (x == (A, B))%:Q).

Lemma walk_to_corner_emptyl m r c (A B : seq nat) :
  (A == [::])%B -> mu (walk_to_corner m r c) (charfun A B) = 0.
Proof.
  move => HA.
  apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv _ _ _)) => [] [X Y] /=.
  apply /implyP => /and4P [] SX SY _ _.
  move: SX; apply contra.
  by rewrite /charfun size_eq0 xpair_eqE (eqP HA); move => /andP [].
Qed.

Lemma walk_to_corner_emptyr m i j (A B : seq nat) :
  (B == [::])%B -> mu (walk_to_corner m i j) (charfun A B) = 0.
Proof.
  move => HB.
  apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m i j)) => [] [X Y] /=.
  apply /implyP => /and4P [] SX SY _ _.
  move: SY; apply contra.
  by rewrite /charfun size_eq0 xpair_eqE (eqP HB); move => /andP [].
Qed.

Lemma charfun_simpll a A B :
  (fun x => charfun (a :: A) B (a :: x.1, x.2)) == charfun A B.
Proof.
  move => [X Y] /=.
  by rewrite /charfun /eq_op /= {1}/eq_op /= eq_refl.
Qed.

Lemma charfun_simplr b A B :
  (fun x => charfun A (b :: B) (x.1, b :: x.2)) == charfun A B.
Proof.
  move => [X Y] /=.
  by rewrite /charfun /eq_op /= {2}/eq_op /= eq_refl.
Qed.


Lemma walk_to_corner_decomp m a b (A B : seq nat) :
  (size (hook_next_seq a b) != 0)%N ->
  is_trace (a::A) (b::B) ->
  mu (walk_to_corner m.+1 a b) (charfun (a :: A) (b :: B))
  =
  ( mu (walk_to_corner m  a (head O B)) (charfun (a :: A) B) +
    mu (walk_to_corner m  (head O A) b) (charfun A (b :: B))
  ) / (size (hook_next_seq a b))%:Q.
Proof.
  move => Hs Ht.
  rewrite (walk_to_corner_rec_simpl _ Hs) Mlet_simpl.
  rewrite mu_uniform_sum /=.
  congr (_ / _).
  rewrite /hook_next_seq big_cat /= !big_map /= addrC.
  congr (_ + _).
  - case (boolP (size B == 0%N)) => HB.
    + rewrite big1.
      * apply esym.
        apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m a (head O B))) => [] [X Y] /=.
        apply/implyP => /and4P [] _ SY _ _.
        move: SY; by apply contra => /eqP [] _ ->.
      * move => i _; rewrite charfun_simplr.
        apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m a i)) => [] [X Y] /=.
        apply/implyP => /and4P [] _ SY _ _.
        move: SY; by apply contra => /eqP [] _ ->.
    + rewrite (bigD1_seq (head O B) _ (iota_uniq _ _)) /=.
      * rewrite -{1}(@charfun_simplr b (a :: A) B) -[RHS]addr0.
        congr (_ + _).
        apply: big1 => i Hi.
        rewrite charfun_simplr.
        apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m a i)) => [] [X Y] /=.
        apply/implyP => /and4P [] _ _ _ SH.
        move: Hi; apply contra => /eqP [] _ <-.
        by rewrite eq_sym.
      * have:= Ht => /and5P [] _ _ _ HsortB _.
        have Hb : (b < head 0 B)%N by move: HsortB HB; case B => [//= | b0 B'] /= /andP [].
        rewrite mem_iota (iota_hookE _ Hb) Hb /=.
        have Hh : (head O B \in b :: B).
          move: HB; case B => [//= | n l] _; by rewrite !inE eq_refl orbT.
        exact: (is_trace_in_in_shape Ht (mem_head _ _) Hh).
  - case (boolP (size A == O)) => HA.
    + rewrite big1.
      * apply esym.
        apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m (head O A) b)) => [] [X Y] /=.
        apply /implyP => /andP [] SX _.
        move: SX; by apply contra => /eqP [] ->.
      * move => i _; rewrite charfun_simpll.
        apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m i b)) => [] [X Y] /=.
        apply /implyP => /andP [] SX _.
        move: SX; by apply contra => /eqP [] ->.
    + rewrite (bigD1_seq (head O A) _ (iota_uniq _ _)) /=.
      * rewrite -{1}(@charfun_simpll a A (b :: B)) -[RHS]addr0.
        congr (_ + _).
        apply: big1 => i Hi.
        rewrite charfun_simpll.
        apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m i b)) => [] [X Y] /=.
        apply /implyP => /and4P [] _ _ HX _.
        move: Hi; apply contra => /eqP [] <- _.
        by rewrite eq_sym.
      * have:= Ht => /and5P [] _ _ HsortA _ _.
        have Ha : (a < head 0 A)%N by move: HsortA HA; case A => [//= | a0 A'] /= /andP [].
        rewrite mem_iota (iota_hookE _ Ha) Ha /=.
        have Hh : (head O A \in a :: A).
          move: HA; case A => [//= | n l] _; by rewrite !inE eq_refl orbT.
        have:= (is_trace_in_in_shape Ht Hh (mem_head _ _)).
        case: p => /= part Hpart.
        by rewrite is_in_conj_part.
Qed.

Lemma mu_walk_to_corner_is_trace r c m :
  is_in_shape p r c ->
  ((al_length p r c) <= m)%N ->
  mu (walk_to_corner m r c) (fun X => is_trace X.1 X.2) = 1.
Proof.
  elim: m r c => [| m IHm] r c Hrc /=.
    by rewrite leqn0 /is_trace /= => /eqP /(al_length0_corner is_part_p Hrc) ->.
  move=> Hal; rewrite size_hook_next_seq.
  case H : (al_length p r c) => [/= | n].
    by rewrite /is_trace /= (al_length0_corner is_part_p Hrc H).
  rewrite Mlet_simpl mu_uniform_sum.
  have -> : upoints (unif_def (inl O) (hook_next_seq r c)) = (hook_next_seq r c).
    rewrite /unif_def.
    move: H; rewrite -size_hook_next_seq.
    by case: (hook_next_seq r c).
  rewrite -weight1_size /weight; rat_to_ring.
  rewrite [X in (_ / X)](eq_bigl predT) //=.
  set num := (X in (X / _)); set den := (X in (_ / X)).
  suff -> : num = den.
    rewrite divff // /den {num den}.
    rewrite big_const_seq count_predT size_hook_next_seq H iter_plus1.
    by rewrite intr_eq0.
  rewrite /num /den {num den}.
  apply eq_big_seq => i.
  rewrite mem_cat => /orP [] /mapP [] j; rewrite mem_iota => /andP [] H1 H2 -> {i};
    move: H2; rewrite (iota_hookE _ H1) Mlet_simpl.
  - rewrite -/(is_in_shape _ _ _) -(is_in_conj_part is_part_p) => Hj.
    have Hlen : (al_length p j c <= m)%N.
      rewrite -ltnS; apply: (leq_trans _ Hal).
      exact: al_length_ltr.
    rewrite -(IHm _ _ Hj Hlen).
    rewrite (mu_pos_cond _ (walk_to_corner_inv m j c)); first last.
      move=> [A B]; apply /andP; by split; first apply mu_bool_0le.
    rewrite [RHS](mu_pos_cond _ (walk_to_corner_inv m j c)); first last.
      move=> [A B]; by case: (is_trace _ _).
    apply Mstable_eq => [] [A B] /=.
    case: eqP => /=; first by rewrite !mul0r.
    case: eqP => /=; first by rewrite !mul0r.
    case: eqP => /=; last by rewrite !mul0r.
    case: eqP => /=; last by rewrite !mul0r.
    rewrite !mul1r /is_trace /=.
    case: A B => [//= | a0 A] [//= | b0 B] /= _ -> _ _.
    by rewrite H1.
  - rewrite -/(is_in_shape _ _ _) => Hj.
    have Hlen : (al_length p r j <= m)%N.
      rewrite -ltnS; apply: (leq_trans _ Hal).
      exact: al_length_ltl.
    rewrite -(IHm _ _ Hj Hlen).
    rewrite (mu_pos_cond _ (walk_to_corner_inv m r j)); first last.
      move=> [A B]; apply /andP; by split; first apply mu_bool_0le.
    rewrite [RHS](mu_pos_cond _ (walk_to_corner_inv m r j)); first last.
      move=> [A B]; by case: (is_trace _ _).
    apply Mstable_eq => [] [A B].
    case: eqP => /=; first by rewrite !mul0r.
    case: eqP => /=; first by rewrite !mul0r.
    case: eqP => /=; last by rewrite !mul0r.
    case: eqP => /=; last by rewrite !mul0r.
    rewrite !mul1r /is_trace /=.
    case: A B => [//= | a0 A] [//= | b0 B] /= -> _ _ _.
    by rewrite H1.
Qed.


(* Formula of Lemma 3. *)
Definition PI (a b : nat) (A B : seq nat) : rat :=
  \prod_(i <- belast a A) (1 / (al_length p i (last b (b :: B)))%:Q) *
  \prod_(j <- belast b B) (1 / (al_length p (last a (a :: A)) j)%:Q).

(* Lemma 3. *)
Lemma PIprog m a b (A B : seq nat) :
  (size A + size B <= m)%N -> is_trace (a :: A) (b :: B) ->
  mu (walk_to_corner m a b) (charfun (a :: A) (b :: B)) = PI a b A B.
Proof.
  elim: m a b A B => [/= | m IHm] /= a b A B.
    rewrite leqn0 addn_eq0 size_eq0 size_eq0 => /andP []/eqP HA /eqP HB; subst.
    move => HT; by rewrite /charfun eq_refl /= /PI /belast /= !big_nil.
  case: (boolP (size (hook_next_seq a b) == O)) => [HO|Hn0].
    move=> _ Htrace; rewrite (eqP HO).
    move: HO; rewrite (is_trace_corner_nil Htrace) => /andP [] /eqP Ha /eqP Hb.
    subst A B; by rewrite /charfun /= eq_refl /= /PI /= !big_nil.
  move=> Hs Ht; rewrite walk_to_corner_decomp //.
  have:= Hn0; rewrite (is_trace_corner_nil Ht) negb_and.
  have -> (u v : bool) : ~~u || ~~v = [|| (~~u && ~~v), (u && ~~v) | (~~ u && v)].
    by case: u; case: v.
  move=> /or3P [] /andP [] HA HB.
  - case: A B HA HB Hs Ht => [//= | A0 A] [//= | B0 B] _ _ Hsize Htrace /=.
    rewrite (IHm a B0 (A0 :: A) B); first last.
      * exact: (is_trace_tlr _ Htrace).
      * move: Hsize => /=; by rewrite addnS ltnS.
    rewrite (IHm A0 b A (B0 :: B)); first last.
      * exact: (is_trace_tll _ Htrace).
      * move: Hsize => /=; by rewrite addSn ltnS.
    rewrite {IHm Hsize Hn0} size_hook_next_seq.
    rewrite /PI /= !big_cons.
    set lA := (last A0 A); set lB := (last B0 B).
    set A' := (belast A0 A); set B' := (belast B0 B).
    set PjlB := (\prod_(j <- A') (1 / (al_length p j lB)%:Q)).
    set PlAj := (\prod_(j <- B') (1 / (al_length p lA j)%:Q)).
    rewrite -![(_ * PjlB)]mulrC !mulrA -![(_ * PlAj)%R]mulrC.
    rewrite !mulrA -!mulrDr mulr1 -!mulrA.
    congr (_ * (_ * _)).
    rewrite !mulrA mulr1.
    have /= := al_length_last_rectangle Htrace.
    rewrite -/lA -/lB => ->.
    rewrite (PoszD (al_length p lA b) (al_length p a lB)) mulrzDl.
    set Alen := (al_length p lA b); set Blen := (al_length p a lB).
    have Alen0 : Alen != O.
      rewrite /Alen /lA -size_hook_next_seq.
      by rewrite (is_trace_corner_nil (is_trace_lastl Htrace)).
    have Blen0 : Blen != O.
      rewrite /Blen /lB -size_hook_next_seq.
      by rewrite (is_trace_corner_nil (is_trace_lastr Htrace)).
    have := @addf_div rat_fieldType 1 Alen%:Q 1 Blen%:~R.
    rewrite addrC !div1r !mul1r => ->; rewrite ?intr_eq0 ?eqz_nat //.
    rewrite addrC [LHS]mulrC mulrA mulVf; first by rewrite mul1r invfM mulrC.
    rewrite -mulrzDl /= intr_eq0 eqz_nat.
    by rewrite addn_eq0 negb_and Alen0 Blen0.
  - move: HA => /eqP HA; subst A.
    rewrite [X in (_ + X)]walk_to_corner_emptyl // addr0.
    have HBd := esym (cons_head_behead O HB).
    rewrite {2}HBd.
    rewrite (IHm a (head O B) [::] (behead B)); first last.
      * rewrite -HBd; exact: (is_trace_tlr HB Ht).
      * rewrite size_behead; move: HB Hs.
        case B => [//= | B0 B'] _ /=.
        by rewrite !add0n.
    rewrite /PI !big_nil /=.
    rewrite {3}HBd (belast_cat b [:: head O B] (behead B)) big_cat big_seq1 /=.
    rewrite size_hook_next_seq.
    by rewrite !mul1r mulrC.
  - move: HB => /eqP HB; subst B.
    rewrite walk_to_corner_emptyr  // add0r.
    have HAd := esym (cons_head_behead O HA).
    rewrite {2}HAd.
    rewrite (IHm (head O A) b (behead A) [::]); first last.
      * rewrite -HAd; exact: (is_trace_tll HA Ht).
      * rewrite size_behead; move: HA Hs.
        case A => [//= | A0 A'] _ /=.
        by rewrite !addn0.
    rewrite /PI !big_nil /=.
    rewrite {3}HAd (belast_cat a [:: head O A] (behead A)) big_cat big_seq1 /=.
    rewrite size_hook_next_seq.
    by rewrite mul1r !mulr1 mulrC.
Qed.


(* Choose BOX in part *)

Definition choose_corner : distr ((seq nat) * (seq nat)) :=
  Mlet (Random (sumn p).-1)
       (fun n => let (r, c) := reshape_coord p n in
                 walk_to_corner (al_length p r c) r c).

Section EndsAt.

Variable (Alpha Beta : nat).
Hypothesis Hcorn : is_corner_box p Alpha Beta.

Definition starts_at r c := (fun R => (head O R.1 == r) && (head O R.2 == c)).
Definition ends_at   r c := (fun R => (last O R.1 == r) && (last O R.2 == c)).
Definition PI_trace X := (PI (head O X.1) (head O X.2) (behead X.1) (behead X.2)).

Lemma sumnpSPE : (sumn p).-1.+1 = sumn p.
Proof.
  have Hszp : (Alpha < size p)%N.
    move: Hcorn; rewrite /is_corner_box /is_out_corner => /andP [] H _.
    move: H; apply contraLR; rewrite -!ltnNge ltnS => H.
    by rewrite (nth_default _ H).
  move: Hszp; case: p => /= [] [//= | p0 p'].
  move=> /part_head_non0 /= => Hp0 _.
  case: p0 Hp0 => [//= | p0] _.
  by rewrite !addSn.
Qed.


Definition F_deno (sh : seq nat) := (\prod_(b : box_in sh) hook_length sh b.1 b.2)%N.
Definition HLF sh :=  (((sumn sh)`!)%:Q / (F_deno sh)%:Q)%R.


Lemma reshape_coord_walk_to :
  forall i, (i < sumn p)%N ->
  (mu (let (r, c) := reshape_coord p i in
       walk_to_corner (al_length p r c) r c)) (ends_at Alpha Beta) =
  \sum_(X <- enum_trace Alpha Beta | let (r, c) := reshape_coord p i in starts_at r c X)
   PI_trace X.
Proof.
  move=> i /reshape_coordP.
  case: (reshape_coord p i) => [r c] [] _.
  rewrite -/(is_in_shape p _ _) => Hin.
  rewrite big_seq_cond.
  pose F := (fun X => mu (walk_to_corner (al_length p r c) r c) (charfun X.1 X.2)).
  rewrite (eq_bigr F); first last.
    move=> [A B] /= /and3P [].
    rewrite /F (enum_traceP Hcorn).
    move => /and3P [] Htrace HAlpha HBeta /eqP <- /eqP <- {F r c Hin}.
    rewrite /PI_trace -(PIprog (m := al_length p (head O A) (head O B))) /=; first last.
    - have:= Htrace => /and3P [] HA HB _; by rewrite !cons_head_behead.
    - have:= Htrace => /and3P [] HA HB _.
      case: A B HA HB Htrace {HAlpha HBeta} => [//= | a A] [//= | b B] /= _ _ Htrace.
      rewrite addnC.
      exact: (leq_add (trace_size_arm_length Htrace) (trace_size_leg_length Htrace)).
    apply: Mstable_eq => [] [X1 X2].
    have:= Htrace => /and3P [] HA HB _; by rewrite !cons_head_behead.
  rewrite -big_seq_cond.
  transitivity (\sum_(i0 <- enum_trace Alpha Beta) F i0).
  - rewrite /F {F} -mu_stable_sum /ends_at.
    have H := mu_walk_to_corner_is_trace Hin (leqnn _).
    rewrite (mu_bool_cond _ H).
    apply Mstable_eq => [[A B]] /=.
    rewrite /charfun -in_seq_sum; last exact: enum_trace_uniq.
    by rewrite enum_traceP.
  - rewrite (bigID (starts_at r c)) /= -[RHS]addr0; congr (_ + _).
    apply big1 => [[A B]]; rewrite /starts_at /F {F} /= => H.
    apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv _ _ _)) => [] [X Y] /=.
    apply /implyP => /and4P [] _ _ /eqP Hr /eqP Hc.
    subst r c.
    move: H; apply contra => /eqP [] -> -> .
    by rewrite !eq_refl.
Qed.

Lemma prob_choose_corner_ends_at :
  mu choose_corner (ends_at Alpha Beta) =
  1 / (sumn p)%:Q * \sum_(X <- enum_trace Alpha Beta) PI_trace X.
Proof.
  rewrite /choose_corner MLet_simpl mu_random_sum sumnpSPE.
  rewrite mulrC mul1r; congr (_ / _).
  rewrite big_nat_0cond (eq_bigr _ reshape_coord_walk_to) -big_nat_0cond.
  rewrite (exchange_big_dep (@predT _)) //=.
  apply eq_big_seq => [[A B]]; rewrite (enum_traceP Hcorn) => /and3P [] Htrace HA HB.
  have Hin : (head O B < nth O p (head O A))%N.
    have:= Htrace => /and3P [] HA0 HB0 _.
    case: A B HA0 HB0 Htrace {HA HB} => [//= | a A] [//= | b B] /= _ _ Htrace.
    exact: (is_trace_in_shape Htrace).
  rewrite -big_filter (bigD1_seq (flatten_coord p (head O A) (head O B))) /=; first last.
  - apply filter_uniq; exact: iota_uniq.
  - rewrite mem_filter (flatten_coordK Hin) /starts_at !eq_refl /=.
    rewrite mem_iota add0n subn0 /=.
    exact: flatten_coordP.
  rewrite -[RHS]addr0; congr (_ + _).
  rewrite big_filter_cond; apply big_pred0 => i.
  have:= (reshape_coordK p i); case: (reshape_coord p i) => [r c] <-.
  rewrite /starts_at.
  case: (boolP ((head 0 A) == r)%N) => //= /eqP <-.
  case: (boolP ((head 0 B) == c)%N) => //= /eqP <-.
  by rewrite eq_refl.
Qed.


Section Formule.

  Variable T : countType.
  Variable R : comRingType.
  Variable alpha : T -> R.

  Lemma expand_prod_add1_seq (S : seq T) :
    \prod_(i <- S) (1 + alpha i) = \sum_(s <- enum_subseqs S) \prod_(i <- s) alpha i.
  Proof.
    elim: S => [| n S IHs] //=.
      by rewrite /= big_nil big_cons 2! big_nil addr0.
    rewrite big_cons IHs {IHs}.
    move: (enum_subseqs _) => sub.
    rewrite big_cat /= mulrDl mul1r addrC.
    congr ( _ + _ ).
    rewrite big_distrr /= big_map.
    apply eq_bigr => i _.
    by rewrite big_cons.
  Qed.

End Formule.


Let p' := decr_nth p Alpha.

Fact Hcrn : is_out_corner p Alpha.
Proof. by have := Hcorn => /andP [] Hcrn /eqP HBeta. Qed.
Hint Resolve Hcrn.

Fact Hp : incr_nth p' Alpha = p. Proof. exact: decr_nthK. Qed.
Fact Hpart' : is_part p'. Proof. exact: is_part_decr_nth. Qed.
Let Hpartc' : is_part (conj_part p') := is_part_conj Hpart'.
Hint Resolve Hpart' Hpartc'.

Fact HBeta : Beta = (nth O p Alpha).-1.
Proof. by have := Hcorn => /andP [] Hcrn /eqP HBeta. Qed.
Fact HBeta' : Beta = (nth O p' Alpha).
Proof. by rewrite HBeta -Hp nth_incr_nth eq_refl add1n. Qed.



Lemma Formula1 :
  (F_deno p)%:Q / (F_deno p')%:Q =
  ( \prod_(0 <= i < Alpha) (1 + (al_length p i Beta )%:Q^-1) ) *
  ( \prod_(0 <= j < Beta)  (1 + (al_length p Alpha j)%:Q^-1) ).
Proof.
  rewrite /F_deno !big_box_in /= /hook_length.
  rewrite -{1}Hp -(eq_big_perm _ (box_in_incr_nth _ _)) /= big_cons.
  rewrite !PoszM /= !intrM /=.
  rewrite !(big_morph Posz PoszM (id1 := Posz 1%N)) //=.
  rewrite !(big_morph intr (@intrM _) (id1 := 1)) //=.
  rewrite -mulrA.
  rewrite -HBeta' (corner_al_length0 is_part_p Hcorn) mul1r.
  rewrite -prodf_div /=.
  rewrite (bigID (fun i => i.1 == Alpha)) /=.
  rewrite mulrC (bigID (fun i => i.2 == Beta)) /= mulrC mulrA.
  rewrite [RHS]mulrC -[RHS]mulr1; congr (_ * _ * _).

  (* Hooks on the row of (Alpha, Beta) *)
  - exact: prod_al_length_quot_row.

  (* Hooks on the column of (Alpha, Beta) *)
  - have Hpartconj := is_part_conj is_part_p.
    have Hcornconj := is_corner_box_conj_part is_part_p Hcorn.
    have Hconj' : (decr_nth (conj_part p) Beta) = conj_part p'.
      rewrite -Hp incr_nth_conj_part //; last exact: in_corner_decr_nth.
      rewrite -HBeta' incr_nthK //.
      apply (is_part_incr_nth Hpartc').
      rewrite HBeta'; apply (is_in_corner_conj_part Hpart').
      exact: in_corner_decr_nth.

    transitivity (\prod_(0 <= j < Alpha) (1 + (al_length (conj_part p) Beta j)%:Q^-1));
      last by apply eq_bigr => i _; rewrite al_length_conj_part.
    rewrite -(prod_al_length_quot_row Hpartconj Hcornconj) Hconj'.
    pose swap i : nat * nat := (i.2, i.1).
    have swap_inj : injective swap by apply (can_inj (g := swap)) => [] [r c].
    rewrite -[RHS]big_filter; set f := (X in \prod_(i <- _) X i).
    rewrite -[X in \prod_(i <- X) _]map_id.
    rewrite (eq_map (f2 := swap \o swap)); last by move=> [r c].
    rewrite map_comp big_map.
    transitivity (\prod_(i <- enum_box_in p' | (i.1 != Alpha) && (i.2 == Beta)) f (swap i)).
      apply eq_bigr => [[r c]] _.
      by rewrite /swap /f {f} /= !al_length_conj_part.
    rewrite -big_filter; apply eq_big_perm.
    apply uniq_perm_eq.
    + apply filter_uniq; exact: enum_box_in_uniq.
    + rewrite (map_inj_uniq swap_inj).
      apply filter_uniq; exact: enum_box_in_uniq.
    + move=> [r c] /=.
      have {2}-> : (r, c) = swap (c, r) by [].
      rewrite (mem_map swap_inj) !mem_filter /=.
      rewrite !mem_enum_box_in !unfold_in /= /is_in_shape -!/(is_in_shape _ _ _).
      rewrite -is_in_conj_part //.
      case: (boolP (is_in_shape p' r c)) => Hrc; last by rewrite !andbF.
      case: (altP (c =P Beta)) => /= Hc; last by rewrite !andbF.
      rewrite !andbT.
      move: Hrc; rewrite /is_in_shape Hc HBeta'.
      rewrite ltnNge; by apply contra => /eqP ->.

  (* Hooks neither on the row or column of (Alpha, Beta) *)
  - rewrite big_seq_cond; apply big1 => [[r c]] /= /and3P [].
    rewrite mem_enum_box_in /is_box_in_shape unfold_in => Hrc Hr Hc.
    rewrite -Hp al_length_incr_nth.
    + by rewrite divff // intr_eq0.
    + exact: is_part_decr_nth.
    + exact: in_corner_decr_nth.
    + exact: Hrc.
    + by rewrite eq_sym.
    + move: Hc; rewrite eq_sym HBeta -Hp.
      by rewrite nth_incr_nth eq_refl add1n.
Qed.

Lemma SimpleCalculation :
  \sum_(X <- enum_trace Alpha Beta) PI_trace X = (F_deno p)%:Q / (F_deno p')%:Q.
Proof.
  rewrite /enum_trace /trace_seq /PI_trace /PI.
  rewrite big_allpairs /=.
  rewrite Formula1 !expand_prod_add1_seq.
  rewrite /index_iota subn0 big_map big_distrl /=; apply eq_big_seq => A HA.
  rewrite /index_iota subn0 big_map big_distrr /=; apply eq_big_seq => B HB.
  rewrite !belast_behead_rcons !last_behead_rcons.
  congr (_ * _); apply eq_big_seq => L _; by rewrite mul1r.
Qed.


Theorem Theorem2 :
  mu choose_corner (ends_at Alpha Beta) = (HLF p') / (HLF p).
Proof.
  rewrite prob_choose_corner_ends_at /HLF -{1 2}Hp sumn_incr_nth.
  rewrite factS PoszM -!ratzE ratzM !ratzE.
  rat_to_ring.
  set Rhs := (RHS).
  have -> : Rhs = ((1 / (sumn p').+1%:Q) * (F_deno p)%:Q / (F_deno p')%:Q).
    rewrite /Rhs -!mulrA [(((F_deno p')%:Q)^-1 / _)%R]mulrC !invfM !mul1r.
    rewrite !mulrA [X in (X / _ / _ / _)]mulrC.
    congr (_ * _); rewrite -!mulrA; congr (_ * _).
    rewrite mulrA divff; first by rewrite invrK mul1r.
    rewrite intr_eq0 eqz_nat -lt0n.
    exact: fact_gt0.
  rewrite {Rhs} !mul1r -[RHS]mulrA; congr (_ * _).
  exact: SimpleCalculation.
Qed.

End EndsAt.

Open Scope ring_scope.

(* TODO: move in partition.v *)
Lemma  out_corners_uniq sh : uniq (out_corners sh).
Proof. rewrite /out_corners; apply filter_uniq; exact: iota_uniq. Qed.

Lemma ends_at_out_cornerE :
  (fun X : seq nat * seq nat =>
     \sum_(i0 <- out_corners p) (ends_at i0 (nth O p i0).-1 X)%:Q)
    == (fun X => is_corner_box p (last O X.1) (last O X.2)).
Proof.
  rewrite /ends_at => [] [A B] /=.
  case (boolP (is_corner_box p (last O A) (last O B))) => Hcorn.
  - rewrite (bigD1_seq (last O A) _ (out_corners_uniq p)) /=; first last.
      move: Hcorn; rewrite /out_corners /is_corner_box => /andP [] Hcorn _.
      rewrite mem_filter Hcorn mem_iota add0n leq0n /=.
      move: Hcorn; rewrite /is_out_corner.
      apply contraLR; by rewrite -!ltnNge ltnS => /(nth_default O) ->.
    move: Hcorn; rewrite /is_corner_box eq_refl => /andP [] _ -> /=.
    rewrite big1 // => i; by rewrite eq_sym => /negbTE ->.
  - rewrite big_seq_cond big1 // => i.
    rewrite mem_filter andbT => /andP [] Hout _.
    suff /negbTE -> : ~~ ((last O A == i) && (last O B == (nth O p i).-1)) by [].
    move: Hcorn; rewrite /is_corner_box; apply contra => /andP [] /eqP Hi.
    subst i => ->; by rewrite Hout.
Qed.

Corollary Corollary4 :
  p != [::] :> seq nat -> \sum_(i <- out_corners p) (HLF (decr_nth p i)) / (HLF p) = 1.
Proof.
  rewrite big_seq_cond => Hp.
  rewrite (eq_bigr (fun i => (mu choose_corner (ends_at i (nth O p i).-1)))); first last.
    move => i /andP [].
    rewrite /out_corners mem_filter => /andP [] Hcorn _ _.
    apply esym. apply Theorem2.
    by rewrite /is_corner_box Hcorn eq_refl.
  rewrite -big_seq_cond -mu_stable_sum.
  rewrite /choose_corner Mlet_simpl mu_random_sum.
  have Hsum : ((sumn p) != 0)%N by  move: Hp; apply contra => /eqP/(part0 is_part_p) ->.
  have -> : (sumn p).-1.+1 = (sumn p) by case: (sumn p) Hsum.
  rewrite big_nat_0cond.
  rewrite (eq_bigr (fun _ => 1)).
    rewrite -big_nat_0cond big_const_seq count_predT size_iota subn0 iter_plus1.
    rat_to_ring; by rewrite divff // intr_eq0.
  move=> i /reshape_coordP.
  case: (reshape_coord p i) => [r c] [].
  rewrite -/(is_in_shape p _ _) => Hr Hc.
  rewrite (Mstable_eq _ ends_at_out_cornerE).
  apply: (mu_bool_impl1 _ (fun X => is_trace X.1 X.2)).
    move=> [A B] /=; by apply/implyP => /and5P [].
  exact: mu_walk_to_corner_is_trace.
Qed.

Corollary Corollary4_intpart :
  p != [::] :> seq nat -> \sum_(i <- out_corners p) (HLF (decr_nth_part p i)) = HLF p.
Proof.
  move=> /Corollary4; rewrite -mulr_suml => /quot_eq1 <-.
  apply eq_big_seq => i; rewrite mem_filter => /andP [] Hi _.
  by rewrite /= /decr_nth_part_def Hi.
Qed.

End FindCorner.

Theorem HookLengthFormula_rat (p : intpart) : HLF p = #|stdtabsh_finType p|.
Proof.
  move: p; apply card_stdtabsh_rat_rec.
  - by rewrite /HLF /= /F_deno /= big_box_in /enum_box_in /= big_nil factE.
  - move=> p Hp; apply esym.
    rewrite /= /decr_nth_part_def /=. exact: Corollary4_intpart.
Qed.


Lemma F_deno_non0 (p : intpart) : (F_deno p) != 0.
Proof.
  rewrite /F_deno -eqz_nat !(big_morph Posz PoszM (id1 := Posz 1%N)) //.
  by apply/prodf_neq0 => [] [] [r c].
Qed.

Lemma HLprod_nat (p : intpart) : #|stdtabsh_finType p| * (F_deno p) = (sumn p)`!.
Proof.
  apply /eqP; rewrite -eqz_nat PoszM.
  rewrite -(@eqr_int rat_numDomainType) intrM /=.
  have /= := (HookLengthFormula_rat p).
  rewrite /int_to_rat /= => <-.
  apply/eqP; rewrite /HLF -mulrA -[RHS]mulr1; congr (_ * _)%R.
  rewrite mulrC divff // intr_eq0.
  rewrite eqz_nat; exact: F_deno_non0.
Qed.

Lemma divF_deno (p : intpart) : (F_deno p) %| (sumn p)`!.
Proof. apply/dvdnP; exists #|stdtabsh_finType p|; by rewrite HLprod_nat. Qed.

Theorem HookLengthFormula (p : intpart) :
  #|stdtabsh_finType p| = (sumn p)`! %/ (F_deno p).
Proof. rewrite -HLprod_nat mulnK // lt0n; exact: F_deno_non0. Qed.

