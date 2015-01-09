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
Require Import tools partition.

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

  Lemma sumn_incr_nth s i : sumn (incr_nth s i) = (sumn s).+1.
  Proof.
    elim: i s => [/= | i IHi]; first by case=> [| s0 s].
    case=> [/= | s0 s /=]; first by rewrite /sumn add0n; elim i.
    by rewrite (IHi s) addnS.
  Qed.

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

  Lemma is_part_shyam s : is_yam s -> is_part (shape_rowseq s).
  Proof. by case: s => [//= | s0 s] /= /andP []. Qed.

  Lemma yam0 y : is_yam y -> shape_rowseq y = [::] -> y = [::].
  Proof.
    case: y => [//= | y0 y] /= _.
    case: y0 => [| y0] /=; by case (shape_rowseq y).
  Qed.

  Lemma is_yam_tl l0 s : is_yam (l0 :: s) -> is_yam s.
  Proof. by move=> /= /andP []. Qed.

  Lemma is_yam_suffix s t : is_yam (s ++ t) -> is_yam t.
  Proof. by elim: s => [//= | s0 s IHs] /= /andP [] _ /IHs. Qed.

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


Fixpoint decr_nth v i {struct i} :=
  if v is n :: v' then
    if i is i'.+1 then n :: decr_nth v' i'
    else if n is n'.+1 then
           if n' is _.+1 then
             n' :: v'
           else [::]
         else [::]
  else [::].

Lemma incr_nthK sh i :
  is_part sh -> is_part (incr_nth sh i) -> decr_nth (incr_nth sh i) i = sh.
Proof.
  elim: sh i => [| s0 sh IHsh] /=.
    case=> [| i] //= _ /andP []; by rewrite leqn0 => /part_head0F ->.
  case=> [| i] //=.
    case: s0 => //= /andP []; by rewrite leqn0 => /part_head0F ->.
  move=> /andP [] Head Hpart /andP [] Headincr Hpartincr.
  by rewrite IHsh.
Qed.

Lemma decr_nthK sh i :
  is_part sh -> is_out_corner sh i -> incr_nth (decr_nth sh i) i = sh.
Proof.
  rewrite /is_out_corner.
  elim: sh i => [| s0 sh IHsh] /=; first by case.
  case=> [| i] /=; case: s0 => [| s0] //= /andP [].
    - move=> {IHsh} Hs0 /part_head_non0 Hhead H ; case: s0 Hs0 H Hhead => //= _.
      case: sh => //= s1 sh; by rewrite ltnS leqn0 => /eqP ->.
    - by rewrite leqn0 => /part_head0F ->.
  move=> Hhead Hpart Hnth; by rewrite IHsh.
Qed.

Lemma is_part_decr_nth sh i :
  is_part sh -> is_out_corner sh i -> is_part (decr_nth sh i).
Proof.
  rewrite /is_out_corner.
  elim: sh i => [| s0 sh IHsh] /=; first by case.
  case=> [| i] /=.
  - case: s0 => [| [| s0]] //= /andP [] _ ->.
    case sh => //= s1 _; by rewrite ltnS => ->.
  move=> /andP [] Hhead Hpart Hnth.
  apply/andP; split; last by apply: IHsh.
  apply: (@leq_trans (head 1 sh)); last exact Hhead.
  case: sh {IHsh Hhead Hnth s0} Hpart => [//= | s1 s]; first by case i.
  case i => //= /andP [].
  case: s1 => [| [| s1]] //=.
  by rewrite leqn0 => /part_head0F ->.
Qed.

Lemma sumn_decr_nth sh i :
  is_part sh -> is_out_corner sh i -> (sumn (decr_nth sh i)) = (sumn sh).-1.
Proof.
  move=> Hpart Hcorn. rewrite -{2}[sh](decr_nthK Hpart Hcorn).
  by rewrite sumn_incr_nth /=.
Qed.

Definition out_corners sh := filter (is_out_corner sh) (iota 0 (size sh)).

Fixpoint list_yamshn n sh :=
  if n is n'.+1 then
    flatten [seq [seq i :: y | y <- list_yamshn n' (decr_nth sh i)] |
                  i <- iota 0 (size sh) & is_out_corner sh i]
  else [:: [::]].
Definition list_yamsh sh := list_yamshn (sumn sh) sh.
Definition is_yam_of_size n y := (is_yam y) && (size y == n).

Lemma list_yamshP sh:
  is_part sh -> all (is_yam_of_shape sh) (list_yamsh sh).
Proof.
  move=> Hpart; apply/allP => y.
  rewrite /list_yamsh /is_yam_of_shape; move Hn: (sumn sh) => n.
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

Lemma list_yamsh_countE sh y :
  is_part sh -> is_yam_of_shape sh y -> count_mem y (list_yamsh sh) = 1.
Proof.
  rewrite /list_yamsh /is_yam_of_shape; move Hn: (sumn sh) => n.
  elim: n sh Hn y => [| n IHn] /= .
    move=> sh Hsh y /part0 H0.
    by rewrite (H0 Hsh) => /andP [] /yam0 H /eqP /H{H} ->.
  move=> sh Hsh [/= | y0 y] /= Hpart.
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

Definition list_yamn n : seq (seq nat) :=
  flatten [seq list_yamsh sh | sh <- list_partn n].

Lemma list_yamnP n :
  all (is_yam_of_size n) (list_yamn n).
Proof.
  rewrite /is_yam_of_size /list_yamn; apply/allP => y.
  - move/flatten_mapP => [] p.
    move /(allP (list_partn_allP n)) => /= /andP [] /eqP <- /list_yamshP /allP H/H{H}.
    rewrite /is_yam_of_shape => /andP [] -> /eqP <- /=.
    by rewrite shape_rowseq_eq_size.
Qed.

Lemma list_yamn_countE n y :
  is_yam_of_size n y -> count_mem y (list_yamn n) = 1.
Proof.
  rewrite /is_yam_of_size => /andP [] Hyam /eqP Hsz.
  rewrite /list_yamn count_flatten -map_comp.
  set ci := (X in map X _).
  have {ci} /eq_in_map -> : {in list_partn n, ci =1 fun i => i == (shape_rowseq y)}.
    rewrite /ci {ci} => i /=.
    case (altP (i =P shape_rowseq y)) => [-> | Hneq].
    - rewrite list_yamsh_countE //=; first by apply: is_part_shyam.
      by rewrite /is_yam_of_shape Hyam eq_refl.
    - rewrite -list_partnP /= => /andP [] /eqP Hsum Hpart.
      apply/count_memPn; move: Hneq; apply: contra.
      move/(allP (list_yamshP Hpart)).
      by rewrite /is_yam_of_shape => /andP [] _ /eqP ->.
  rewrite sumn_count /=.
  rewrite (eq_count (a2 := (pred1 (shape_rowseq y)))); last by [].
  apply: list_partn_countE.
  by rewrite /= -Hsz shape_rowseq_eq_size eq_refl is_part_shyam.
Qed.

Section YamOfShape.

Variable sh : seq nat.
Hypothesis Hpart : is_part sh.

Structure yamsh : Type :=
  YamSh {yamshval :> seq nat; _ : is_yam_of_shape sh yamshval}.
Canonical yamsh_subType := Eval hnf in [subType for yamshval].
Definition yamsh_eqMixin := Eval hnf in [eqMixin of yamsh by <:].
Canonical yamsh_eqType := Eval hnf in EqType yamsh yamsh_eqMixin.
Definition yamsh_choiceMixin := Eval hnf in [choiceMixin of yamsh by <:].
Canonical yamsh_choiceType := Eval hnf in ChoiceType yamsh yamsh_choiceMixin.
Definition yamsh_countMixin := Eval hnf in [countMixin of yamsh by <:].
Canonical yamsh_countType := Eval hnf in CountType yamsh yamsh_countMixin.
Canonical yamsh_subCountType := Eval hnf in [subCountType of yamsh].

Definition yamsh_enum : seq yamsh := pmap insub (list_yamsh sh).

Lemma finite_yamsh : Finite.axiom yamsh_enum.
Proof.
  case=> /= p Hp; rewrite -(count_map _ (pred1 p)) (pmap_filter (@insubK _ _ _)).
  rewrite count_filter -(@eq_count _ (pred1 p)) => [|s /=]; last first.
    by rewrite isSome_insub; case: eqP=> // ->.
  by apply: list_yamsh_countE.
Qed.

Canonical yamsh_finMixin := Eval hnf in FinMixin finite_yamsh.
Canonical yamsh_finType := Eval hnf in FinType yamsh yamsh_finMixin.
Canonical yamsh_subFinType := Eval hnf in [subFinType of yamsh_countType].

Lemma yamshP (y : yamsh) : is_yam y.
Proof. by case: y => /= y /andP []. Qed.

Lemma shape_yamsh (y : yamsh) : shape_rowseq y = sh.
Proof. by case: y => /= y /andP [] _ /eqP. Qed.

End YamOfShape.


Section YamOfSize.

Variable n : nat.

Structure yamn : Type :=
  Yamn {yamnval :> seq nat; _ : is_yam_of_size n yamnval}.
Canonical yamn_subType := Eval hnf in [subType for yamnval].
Definition yamn_eqMixin := Eval hnf in [eqMixin of yamn by <:].
Canonical yamn_eqType := Eval hnf in EqType yamn yamn_eqMixin.
Definition yamn_choiceMixin := Eval hnf in [choiceMixin of yamn by <:].
Canonical yamn_choiceType := Eval hnf in ChoiceType yamn yamn_choiceMixin.
Definition yamn_countMixin := Eval hnf in [countMixin of yamn by <:].
Canonical yamn_countType := Eval hnf in CountType yamn yamn_countMixin.
Canonical yamn_subCountType := Eval hnf in [subCountType of yamn].


Definition yamn_enum : seq yamn := pmap insub (list_yamn n).

Lemma finite_yamn : Finite.axiom yamn_enum.
Proof.
  case=> /= y Hy; rewrite -(count_map _ (pred1 y)) (pmap_filter (@insubK _ _ _)).
  rewrite count_filter -(@eq_count _ (pred1 y)) => [|s /=]; last first.
    by rewrite isSome_insub; case: eqP=> // ->.
  by apply: list_yamn_countE.
Qed.

Canonical yamn_finMixin := Eval hnf in FinMixin finite_yamn.
Canonical yamn_finType := Eval hnf in FinType yamn yamn_finMixin.
Canonical yamn_subFinType := Eval hnf in [subFinType of yamn_countType].

Lemma yamnP (y : yamn) : is_yam y.
Proof. by case: y => /= y /andP []. Qed.

Lemma yamn_sumn (y : yamn) : size y = n.
Proof. by case: y => /= y /andP [] _ /eqP. Qed.

End YamOfSize.
