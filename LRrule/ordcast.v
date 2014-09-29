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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset tuple bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section ImsetInj.

Implicit Type T : finType.

Lemma set1_disjoint T (i j : T) : [set i] != [set j] -> [disjoint [set i] & [set j]].
Proof.
  move=> Hneq; rewrite /disjoint; apply/pred0P => l /=; apply negbTE.
  rewrite !in_set1; move: Hneq; by apply contra => /andP [] /eqP -> /eqP ->.
Qed.

Lemma mem_imset_inj T1 T2 (f : T1 -> T2) (i : T1) (s : {set T1}) :
  injective f -> (f i) \in f @: s = (i \in s).
Proof.
  move=> H; apply/(sameP idP); apply(iffP idP); first by apply mem_imset.
  by move/imsetP => [] j Hj /H ->.
Qed.

Lemma map_filter_comp (T1 T2: Type) (l : seq T1) (PP : pred T2) (F : T1 -> T2) :
  [seq F i | i <- l & PP (F i)] = [seq i | i <- map F l & PP i ].
Proof.
  rewrite filter_map /= -map_comp.
  have /eq_filter -> : (preim F [eta PP]) =1 (fun i => PP (F i)) by [].
  by rewrite map_comp.
Qed.

Lemma subset_imsetK T1 T2 (f : T1 -> T2) (s t : {set T1}):
  injective f -> f @: s \subset f @: t -> s \subset t.
Proof.
  move=> Hinj /subsetP H; apply/subsetP => x /(mem_imset f) Hfx.
  by have:= H _ Hfx => /imsetP [] y Hy /Hinj ->.
Qed.

Lemma imset_inj T1 T2 (f : T1 -> T2) :
  injective f -> injective (fun s : {set T1} => (imset f (mem s))).
Proof.
  move=> Hinj s1 s2 /eqP; rewrite eqEsubset => /andP [] H12 H21.
  have {Hinj} Hinj := (subset_imsetK Hinj).
  apply /eqP; rewrite eqEsubset.
  by rewrite (Hinj _ _ H12) (Hinj _ _ H21).
Qed.

Lemma imset_trivIset (T1 : finType) (T2 : finType) (F : T1 -> T2) (P : {set {set T1}}) :
  injective F -> trivIset P -> trivIset ((fun s : {set T1} => F @: s) @: P).
Proof.
  move=> Hinj /trivIsetP Htriv.
  apply/trivIsetP => A B /imsetP [] FA FAP -> {A} /imsetP [] FB FBP -> Hneq.
  have {Hneq} Hneq : FA != FB by move: Hneq; apply contra => /eqP ->.
  have := Htriv _ _ FAP FBP Hneq; rewrite -!setI_eq0 -imsetI.
  * move=> /eqP ->; by rewrite imset0.
  * move=> i j _ _ /=; by apply Hinj.
Qed.

Lemma preimset_trivIset (T1 : finType) (T2 : finType) (F : T1 -> T2) (P : {set {set T2}}) :
  injective F -> trivIset P -> trivIset ((fun s : {set T2} => F @^-1: s) @: P).
Proof.
  move=> Hinj /trivIsetP Htriv.
  apply/trivIsetP => A B /imsetP [] FA FAP -> {A} /imsetP [] FB FBP -> Hneq.
  have {Hneq} Hneq : FA != FB by move: Hneq; apply contra => /eqP ->.
  have := Htriv _ _ FAP FBP Hneq; rewrite -!setI_eq0 -preimsetI => /eqP ->.
  by rewrite preimset0.
Qed.

End ImsetInj.


Lemma mem_takeP (T : eqType) x0 x k (s : seq T) :
  reflect (exists i, i < minn k (size s) /\ x = nth x0 s i) (x \in take k s).
Proof.
  apply (iffP idP).
  + move=> Hx; pose ix := index x (take k s).
    have Hix : ix < size s.
      have:= Hx; rewrite /ix -index_mem size_take.
      case: (ltnP k (size s)) => //= H1 H2; by apply (ltn_trans H2 H1).
    have Hix2: ix < k.
      have:= Hx; rewrite /ix -index_mem size_take /=.
      by case: (ltnP k (size s)) => H; last by move/leq_trans; apply.
    exists ix; split; first by rewrite leq_min Hix Hix2.
    by rewrite -{1}(nth_index x0 Hx) nth_take.
  + move=> [] i [] Hi ->.
    have Hik := leq_trans Hi (geq_minl k (size s)).
    have Hsz := leq_trans Hi (geq_minr k (size s)).
    rewrite -(nth_take _ Hik); apply mem_nth; rewrite size_take.
    by case (ltnP k (size s)).
Qed.

Lemma take_iota i k n : take k (iota i n) = iota i (minn k n).
Proof.
  rewrite /minn; case: (ltnP k n) => H; last by apply take_oversize; rewrite size_iota.
  elim: k n H i => [//= | k IHk]; first by case.
  case=> //= n H i; congr (i :: _); by apply IHk.
Qed.

Lemma drop_iota i k n : drop k (iota i n) = iota (i + k) (n - k).
Proof.
  elim: k i n => [/= | k IHk] i n /=; first by rewrite addn0; case: n.
  case: n => [//= | n] /=; by rewrite IHk addSn addnS subSS.
Qed.

Lemma mem_take_enumI n (i : 'I_n) k : i \in take k (enum 'I_n) = (i < k).
Proof.
  case: i => i Hi /=.
  rewrite -(mem_map val_inj) map_take val_enum_ord /= take_iota mem_iota /= add0n.
  rewrite /minn; case: (ltnP k n) => //= H.
  by rewrite Hi (leq_trans Hi H).
Qed.

Lemma take_enumI n k : take k (enum 'I_n) = filter ((gtn k) \o val) (enum 'I_n).
Proof.
  apply (inj_map val_inj); rewrite map_take map_filter_comp val_enum_ord.
  rewrite take_iota /minn.
  case: (ltnP k n) => Hk.
  + elim: k n Hk => [//= | k IHk] n Hk /=.
    * set f := (X in filter X _); have /eq_filter -> : f =1 pred0 by [].
      by rewrite filter_pred0.
    * case: n Hk => [//= | n] Hk /=.
      rewrite -[1]addn0 !iota_addl (IHk _ Hk).
      by rewrite filter_map /= -!map_comp.
  + rewrite (eq_in_filter (a2 := predT)); first by rewrite filter_predT map_id.
    move=> i /=; rewrite mem_iota add0n => /andP [] _ H2.
    by rewrite (leq_trans H2 Hk).
Qed.

Lemma mem_drop_enumI n (i : 'I_n) k : i \in drop k (enum 'I_n) = (i >= k).
Proof.
  case (leqP k n) => Hkn.
  + case: i => i Hi /=.
    rewrite -(mem_map val_inj) map_drop val_enum_ord /= drop_iota mem_iota /= add0n.
    have -> : i < k + (n - k) by rewrite subnKC.
    by rewrite andbT.
  + rewrite drop_oversize; last by rewrite size_enum_ord; apply ltnW.
    have:= ltn_trans (ltn_ord i) Hkn.
    by rewrite in_nil ltnNge => /negbTE => ->.
Qed.

Lemma drop_enumI n k : drop k (enum 'I_n) = filter ((leq k) \o val) (enum 'I_n).
Proof.
  apply (inj_map val_inj); rewrite map_drop map_filter_comp val_enum_ord.
  rewrite drop_iota add0n.
  case: (leqP n k) => Hk.
  + have:= Hk; rewrite -subn_eq0 => /eqP -> /=.
    rewrite (eq_in_filter (a2 := pred0)); first by rewrite filter_pred0.
    move=> i; rewrite mem_iota add0n => /andP [] _ Hi.
    have:= leq_trans Hi Hk.
    by rewrite ltnNge => /negbTE => ->.
  + move Hdiff : (n - k) => d; move: Hdiff => /eqP.
    rewrite -(eqn_add2r k) subnK; last by apply ltnW.
    move/eqP -> => {n Hk}.
    rewrite addnC iota_add filter_cat map_id add0n.
    rewrite (eq_in_filter (a2 := pred0)); first last.
      move=> i; rewrite mem_iota add0n => /andP [] _ Hi.
      move: Hi; by rewrite ltnNge => /negbTE => ->.
    rewrite filter_pred0 cat0s.
    rewrite (eq_in_filter (a2 := predT)); first by rewrite filter_predT.
    by move=> i; rewrite mem_iota => /andP [] ->.
Qed.

Lemma enum0 : enum 'I_0 = [::].
Proof. apply/nilP; by rewrite /nilp size_enum_ord. Qed.

Lemma enum_cast_ord m n (H : n = m):
  enum 'I_m = [seq cast_ord H i | i <- enum 'I_n].
Proof.
  subst m; rewrite /=.
  have /eq_map -> : cast_ord (erefl n) =1 id by move=> i; apply val_inj.
  by rewrite map_id.
Qed.

Lemma nth_ord_ltn i n (H : i < n) x0 : nth x0 (enum 'I_n) i = (Ordinal H).
Proof. by apply: val_inj => //=; rewrite nth_enum_ord. Qed.

Section Casts.

Lemma cast_erefl n : cast_ord (erefl n) =1 id.
Proof. by move=> i; apply/eqP; rewrite /eq_op /=. Qed.

Lemma cast_eq m n i j (H : m = n) : ((cast_ord H i) == (cast_ord H j)) = (i == j).
Proof. subst m; by rewrite !cast_erefl. Qed.

Lemma sym_cast_eq m n i j : ((cast_ord (addnC m n) i) == cast_ord (addnC m n) j) = (i == j).
Proof. by apply cast_eq. Qed.

Lemma cast_map (T: Type) n m (F : 'I_n -> T) (H : m = n) :
  [seq F i | i <- enum 'I_n] = [seq F ((cast_ord H) i) | i <- enum 'I_m].
Proof.
  subst m; by have /eq_map -> : (fun i : 'I_n => F (cast_ord (erefl n) i)) =1 F
    by move=> i; rewrite /= cast_erefl.
Qed.

Lemma cast_map_cond (T: Type) n m (P : pred 'I_n) (F : 'I_n -> T) (H : m = n) :
  [seq F i | i <- enum 'I_n & P i] =
  [seq F ((cast_ord H) i) | i <- enum 'I_m & P ((cast_ord H) i) ].
Proof.
  subst m; have /eq_filter -> : (fun i : 'I_n => P (cast_ord (erefl n) i)) =1 P
    by move=> i; rewrite /= cast_erefl.
  by have /eq_map -> : (fun i : 'I_n => F (cast_ord (erefl n) i)) =1 F
    by move=> i; rewrite /= cast_erefl.
Qed.

Lemma mem_cast m n (H : m = n) (i : 'I_m) (S : {set 'I_m}) :
  ((cast_ord H) i) \in [set (cast_ord H) i | i in S] = (i \in S).
Proof.
  apply/(sameP idP); apply(iffP idP).
  + move=> Hin; apply/imsetP; by exists i.
  + by move/imsetP => [] j Hin /cast_ord_inj ->.
Qed.

Definition cast_set n m (H : n = m) : {set 'I_n} -> {set 'I_m} :=
  [fun s : {set 'I_n} => (cast_ord H) @: s].

Lemma cast_set_inj n m (H : n = m) : injective (cast_set H).
Proof. move=> S1 S2; rewrite /cast_set /=; apply imset_inj; apply cast_ord_inj. Qed.

Lemma cover_cast m n (P : {set {set 'I_n}}) (H : n = m) :
  cover (imset (cast_set H) (mem P)) = (cast_set H) (cover P).
Proof.
  rewrite /= cover_imset /cover; apply esym; apply big_morph.
  + move=> i j /=; by apply imsetU.
  + by apply imset0.
Qed.

End Casts.

