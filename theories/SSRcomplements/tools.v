(** * Combi.SSRcomplements.tools : Missing SSReflect sequence and set lemmas *)
(******************************************************************************)
(*      Copyright (C) 2015-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * A bunch of lemmas about seqs and sets which are missing in SSReflect

No new notions are defined here.

TODO: these probably should be contributed to SSReflect itself
****************************************************************************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import finset bigop path binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Prenex Implicits nat_of_ord.

#[export] Hint Resolve nth_nil addn0 : core.

Lemma leq_addE m1 m2 n1 n2 :
  m1 <= m2 -> n1 <= n2 -> m1 + n1 = m2 + n2 -> m1 = m2 /\ n1 = n2.
Proof.
move=> lem len eqD; have [_] := leqif_add (leqif_eq lem) (leqif_eq len).
by rewrite eqD eqxx => /esym/andP[/eqP->/eqP->].
Qed.


(** ** [rcons] and [cons] related lemmas *)
Section SeqLemmas.

Variable (T : eqType).
Implicit Type s w : seq T.
Implicit Type a b : T.

Lemma drop_nilE s m :
  (drop m s == [::]) = (size s <= m).
Proof. by elim: m s => [|m IHm] [|s0 s] //=; rewrite IHm ltnS. Qed.

Lemma cons_head_behead x s : (s != [::]) -> head x s :: behead s = s.
Proof using. by case s. Qed.

Lemma belast_behead_rcons x l s :
  belast (head x (rcons s l)) (behead (rcons s l)) = s.
Proof using. by case: s => // s0 s; rewrite rcons_cons belast_rcons. Qed.

Lemma last_behead_rcons x l s :
  last (head x (rcons s l)) (behead (rcons s l)) = l.
Proof using. by case: s => // s0 s; rewrite rcons_cons last_rcons. Qed.

Lemma set_head_default b a s : s != [::] -> head a s = head b s.
Proof using. by case: s. Qed.

Lemma rcons_set_nth a s l : set_nth a s (size s) l = rcons s l.
Proof using. by elim: s => // l0 s IHs; rewrite rcons_cons -IHs. Qed.

Lemma set_nth_rcons x0 s x n y :
  set_nth x0 (rcons s x) n y =
  if n < size s then rcons (set_nth x0 s n y) x
  else if n == size s then rcons s y
       else (rcons s x) ++ ncons (n - size s).-1 x0 [:: y].
Proof using.
elim: s n => [// | s0 s IHs] n.
- by case eqP => [-> // |]; case: n => [| []].
- rewrite rcons_cons /=; case: n => //= n.
  move/(_ n) : IHs; rewrite eqSS ltnS.
  by case (ltngtP n (size s)) => _ <-.
Qed.

Lemma rconsK a b u v : rcons u a = rcons v b -> u = v.
Proof using.
by move/(congr1 rev); rewrite !rev_rcons => [[_ /(inv_inj revK)]].
Qed.

Lemma rcons_nilF s l : ((rcons s l) == [::]) = false.
Proof using.
by apply/negbTE/negP => /eqP/(congr1 size); rewrite size_rcons.
Qed.

Lemma cons_in_map_cons a b s w (l : seq (seq T)) :
  a :: s \in [seq b :: s1 | s1 <- l] -> a == b.
Proof using.
elim: l => // l0 l IHl; rewrite map_cons in_cons => /orP[]; last exact: IHl.
by move=> /eqP [->].
Qed.

Lemma count_rcons w P l :
  count P (rcons w l) = count P w + P l.
Proof using. by rewrite -count_rev rev_rcons /= count_rev addnC. Qed.

(** ** [set_nth] related lemmas *)
Lemma set_nth_non_nil d s n y : set_nth d s n y != [::].
Proof using. by elim: s => [|s0 s]; case n. Qed.

Lemma nth_set_nth_expand a b l i c j :
  (size l <= j < i) -> nth a (set_nth b l i c) j = b.
Proof using.
elim: l i j => [/= | l0 l IHl].
- elim => [// | i' Hi] /=.
  by case => [// | j /=]; rewrite nth_ncons /leq subSS => ->.
- elim => [// | i' Hi] j /=; first by rewrite ltn0 andbF.
  case: j Hi => [// | j /=] Hi /andP [H1 H2].
  by apply: IHl; move: H1 H2; rewrite !/leq !subSS => -> ->.
Qed.

Lemma nth_set_nth_any a b l i c j :
  nth a (set_nth b l i c) j =
  if j == i then c else
    if j < size l then nth a l j else
      if j <= i then b else a.
Proof using.
case eqP => [<- | /eqP Hneq].
- have Hj : j < size (set_nth b l j c) by rewrite size_set_nth; apply: leq_maxl.
  by rewrite (set_nth_default b a Hj) nth_set_nth /= eq_refl.
- case (ltnP j (size l)) => Hjsz.
  + have Hj : j < size (set_nth b l i c)
      by rewrite size_set_nth; apply: (leq_trans Hjsz); apply: leq_maxr.
    rewrite (set_nth_default b a Hj) nth_set_nth /= (negbTE Hneq).
    exact: set_nth_default.
  + case (leqP j i) => Hij.
    * by apply: nth_set_nth_expand; rewrite Hjsz /= ltn_neqAle Hneq Hij.
    * rewrite nth_default; first by [].
      by rewrite size_set_nth /maxn; case (ltnP i.+1 (size l)).
Qed.

Lemma eq_from_nth_notin x0 s1 s2 :
  x0 \notin s1 -> x0 \notin s2 ->
  (forall i : nat, nth x0 s1 i = nth x0 s2 i) -> s1 = s2.
Proof.
wlog Hpq : s1 s2 / (size s1) <= (size s2).
  move=> Hwlog; case: (leqP (size s1) (size s2)); first exact: Hwlog.
  by move=> /ltnW/Hwlog H +{}/H => +H => {}/H Heq Hnth; rewrite Heq.
move=> x0s1 x0s2 Heq; apply: (eq_from_nth (x0 := x0))=> [|i _ //].
apply anti_leq; rewrite {}Hpq/=.
case: s2 x0s2 Heq => [//|h2 s2'] Hnotin Heq.
apply/contraR: Hnotin; rewrite -ltnNge => Habs.
move/(_ (size (h2 :: s2')).-1): Heq; rewrite nth_last.
rewrite nth_default => [-> /=|]; first exact: mem_last.
by move: Habs; rewrite /= ltnS.
Qed.

End SeqLemmas.


(** ** [minn] related lemmas *)
Lemma minSS i j : minn i.+1 j.+1 = (minn i j).+1.
Proof. by rewrite /minn ltnS; case ltnP. Qed.


(** ** [sumn] related lemmas *)
Lemma leq_sumn_in (sh : seq nat) i : i \in sh -> i <= sumn sh.
Proof.
elim: sh => [//| s0 sh IHsh].
rewrite inE /= => /orP[/eqP->|/IHsh]; first exact: leq_addr.
move/leq_trans; apply; exact: leq_addl.
Qed.

Lemma sumn_map_condE (T : Type) (s : seq T) (f : T -> nat) (P : pred T) :
  sumn [seq f i | i <- s & P i] = \sum_(i <- s | P i) f i.
Proof. by rewrite /sumn foldrE big_map big_filter. Qed.

Lemma sumn_mapE (T : Type) (s : seq T) (f : T -> nat) :
  sumn [seq f i | i <- s] = \sum_(i <- s) f i.
Proof. by rewrite -sumn_map_condE filter_predT. Qed.

Lemma sum_minn s b :
  \sum_(l <- s) minn l b = sumn s - \sum_(l <- s) (l - b).
Proof.
elim: s => [|s0 s IHs] /=; first by rewrite !big_nil !sub0n.
rewrite !big_cons {}IHs minnE.
case: (leqP s0 b) => [le_s0_b | /ltnW le_b_s0].
- have:= le_s0_b; rewrite -subn_eq0 => /eqP ->; rewrite add0n subn0.
  by rewrite addnBA // sumnE; apply: leq_sum => n _; apply: leq_subr.
- rewrite subKn // subnDA subnBA // -addnA [s0 + _]addnC addnK [_ + b]addnC.
  by rewrite addnBA // sumnE; apply: leq_sum => n _; apply: leq_subr.
Qed.

Lemma sum_take r s F :
  F 0 = 0 -> \sum_(l <- take r s) F l = \sum_(0 <= i < r) F (nth 0 s i).
Proof.
move => F0; elim: r s => [|r IHr] s /=.
  by rewrite take0 /index_iota /= !big_nil.
case: s => [{IHr}| s0 s] /=.
  by rewrite big_nil; apply/esym/big1 => i _; rewrite nth_default.
by rewrite big_nat_recl //= big_cons -IHr.
Qed.

Lemma sumn_take r s : sumn (take r s) = \sum_(0 <= i < r) nth 0 s i.
Proof. by rewrite sumnE sum_take. Qed.
Lemma sumn_drop r s : sumn (drop r s) = \sum_(r <= i < size s) nth 0 s i.
Proof.
case: (ltnP r (size s)) => [/ltnW ltrsz | leszr]; first last.
  by rewrite drop_oversize // big_geq.
rewrite sumnE (big_nth 0) size_drop -{3}(add0n r) big_addn.
by apply eq_bigr => i _; rewrite nth_drop addnC.
Qed.

Lemma sumn_nth_le l n :
  size l <= n -> sumn l = \sum_(0 <= i < n) nth 0 l i.
Proof. by rewrite -sumn_take => /take_oversize ->. Qed.

(** ** [iota] related lemmas *)
Lemma binomial_sumn_iota n : 'C(n, 2) = sumn (iota 0 n).
Proof. by rewrite -triangular_sum sumnE /index_iota subn0. Qed.

Lemma sumn_pred1_iota a b x :
  sumn [seq ((i == x) : nat) | i <- iota a b] = (a <= x < a + b).
Proof.
elim: b a => [/=| b IHb] a.
  by case: andP => [|//] [/leq_ltn_trans H{}/H]; rewrite addn0 ltnn.
rewrite addnS ltnS -add1n iotaD map_cat /= leq_eqVlt addn1 {}IHb addSn ltnS.
by case: eqP => [->|_]//=; rewrite ltnn addn0 leq_addr.
Qed.

Lemma count_mem_iota a b i :
  count_mem i (iota a b) = (a <= i < a + b).
Proof. by rewrite count_uniq_mem ?iota_uniq // mem_iota. Qed.

Lemma iota_ltn a b : b <= a -> [seq i <- iota 0 a | i < b] = iota 0 b.
Proof.
move=> Hab.
rewrite -(subnKC Hab) iota_add add0n filter_cat.
rewrite -[RHS]cats0; congr (_ ++ _).
- rewrite (eq_in_filter (a2 := predT)) ?filter_predT //.
  by move=> i /=; rewrite mem_iota add0n /= => ->.
- rewrite (eq_in_filter (a2 := pred0)) ?filter_pred0 //.
  move=> i /=; rewrite mem_iota (subnKC Hab) => /andP [].
  by rewrite leqNgt => /negbTE.
Qed.

Lemma iota_geq a b : [seq i <- iota 0 a | b <= i] = iota b (a - b).
Proof.
(* Note: The equational proof is longer *)
elim: a => [//=| n IHn].
rewrite -addn1 iota_add add0n /= filter_cat IHn {IHn} /=.
case: leqP => Hb.
- by rewrite addn1 (subSn Hb) -addn1 iota_add /= subnKC.
- rewrite addn1 cats0.
  have := Hb; rewrite /leq => /eqP ->.
  by have := ltnW Hb; rewrite /leq => /eqP ->.
Qed.


Section FinSet.

Variable T : finType.

Lemma setU1E (x : T) (S : {set T}) : x \in S -> x |: S = S.
Proof.
move=> Hx; apply/setP/subset_eqP/andP; split; apply/subsetP=> i.
- by move/setU1P => [] ->.
- by move=> H; apply/setU1P; right.
Qed.

End FinSet.

(** TODO: Merged in mathcomp-1.13 *)
Section SSRComplUndup.

Variables (S T : eqType) (f : S -> T).

Hypothesis Hf : injective f.

Lemma undup_map_inj s : undup (map f s) = map f (undup s).
Proof. by elim: s => //= s0 s ->; rewrite mem_map //; case: (_ \in _). Qed.

End SSRComplUndup.


Lemma uniq_sum_count_mem (T : eqType) (P : pred T) l s :
  uniq s ->
  \sum_(i <- s | P i) (count_mem i) l = count (predI (mem s) P) l.
Proof.
move=> suniq; rewrite -big_filter -size_filter.
have /eq_filter -> : predI (mem s) P =i [seq x <- s | P x].
  by move=> i; rewrite inE mem_filter andbC.
have {suniq} : uniq [seq x <- s | P x] by exact: filter_uniq.
elim: filter => [_ | s0 {}s IHs].
  by rewrite big_nil (eq_filter (a2 := pred0)); first by rewrite filter_pred0.
rewrite big_cons => /= /andP[s0s {}/IHs ->].
rewrite !size_filter -[RHS]addn0.
rewrite [in RHS](eq_count (a2 := predU (pred1 s0) (mem s))); first last.
  by move => i; rewrite /= in_cons.
have /eq_count/(_ l) : predI (pred1 s0) (mem s) =1 pred0.
  move=> i /=; apply/negP => /andP [/eqP -> s0s'].
  by rewrite s0s' in s0s.
rewrite count_pred0 => <-.
by rewrite count_predUI.
Qed.

(* New lemmas *)
Lemma sumn_sort l S : sumn (sort S l) = sumn l.
Proof using. by have:= perm_sort S l => /permPl/perm_sumn. Qed.

Lemma map_filter_comp (T1 T2: Type) (l : seq T1) (PP : pred T2) (F : T1 -> T2) :
  [seq F i | i <- l & PP (F i)] = [seq i | i <- map F l & PP i ].
Proof.
rewrite filter_map /= -map_comp.
have /eq_filter -> : (preim F [eta PP]) =1 (fun i => PP (F i)) by [].
by rewrite map_comp.
Qed.

Lemma set1_disjoint (T : finType) (i j : T) :
  [set i] != [set j] -> [disjoint [set i] & [set j]].
Proof.
move=> Hneq; rewrite /disjoint; apply/pred0P => l /=; apply: negbTE.
by rewrite !in_set1; move: Hneq; apply: contra => /andP [/eqP -> /eqP ->].
Qed.

Lemma subset_imsetK (T1 T2 : finType) (f : T1 -> T2) (s t : {set T1}):
  injective f -> f @: s \subset f @: t -> s \subset t.
Proof.
move=> f_inj /subsetP H.
by apply/subsetP => x /(imset_f f) /(H _) /imsetP [y Hy /f_inj ->].
Qed.


Section SSRComplFinset.

Variables aT rT : finType.
Variables (f : aT -> rT).

Lemma imsetD (A B : {set aT}) :
  {in A :|: B &, injective f} -> f @: (B :\: A) = (f @: B) :\: (f @: A).
Proof.
move=> injf; apply/setP=> y; rewrite inE.
apply/imsetP/andP => [[x] | [yNfA] /imsetP[x xB Hy]].
- rewrite inE => /andP [xNA xB ->{y}]; split; last exact: imset_f.
  move: xNA; apply contra.
  by move=> /imsetP[x1 x1A] /injf->; rewrite ?inE ?xB ?x1A ?orbT.
- subst y; exists x; rewrite // inE xB andbT.
  by move: yNfA; apply contra; apply imset_f.
Qed.

End SSRComplFinset.


Section ImsetInj.

Variables (T T1 T2 : finType) (f : T1 -> T2).

Lemma preimset_trivIset (P : {set {set T2}}) :
  trivIset P -> trivIset ((fun s : {set T2} => f @^-1: s) @: P).
Proof  using.
move=> /trivIsetP Htriv.
apply/trivIsetP => A B /imsetP [FA FAP -> {A}] /imsetP [FB FBP -> {B}] Hneq.
have {Hneq} neqFAFB : FA != FB by move: Hneq; apply: contra => /eqP ->.
have:= Htriv _ _ FAP FBP neqFAFB; rewrite -!setI_eq0 -preimsetI => /eqP ->.
by rewrite preimset0.
Qed.

Hypothesis (f_inj : injective f).

Lemma imset_inj : injective (fun s : {set T1} => imset f (mem s)).
Proof.
move=> s1 s2 /eqP; rewrite eqEsubset => /andP [H12 H21].
move: f_inj => /subset_imsetK Hinj.
apply/eqP; rewrite eqEsubset.
by rewrite (Hinj _ _ H12) (Hinj _ _ H21).
Qed.

Lemma imset_trivIset (P : {set {set T1}}) :
  trivIset P -> trivIset ((fun s : {set T1} => f @: s) @: P).
Proof.
move=> /trivIsetP Htriv.
apply/trivIsetP => A B /imsetP [FA FAP -> {A}] /imsetP [FB FBP -> {B}] Hneq.
have {Hneq} neqFAFB : FA != FB by move: Hneq; apply: contra => /eqP ->.
have:= Htriv _ _ FAP FBP neqFAFB; rewrite -!setI_eq0 -imsetI.
- by move=> /eqP ->; rewrite imset0.
- by move=> i j _ _ /=; exact: f_inj.
Qed.

Lemma disjoint_imset (A B : {set T1}) :
  [disjoint A & B] -> [disjoint [set f x | x in A] & [set f x | x in B]].
Proof.
rewrite -!setI_eq0 => /eqP Hdisj.
rewrite -imsetI; last by move=> x y _ _; exact: f_inj.
by rewrite imset_eq0 Hdisj.
Qed.

End ImsetInj.

Lemma uniq_next (T : eqType) (p : seq T) : uniq p -> injective (next p).
Proof using.
move=> Huniq x y Heq.
by rewrite -(prev_next Huniq x) Heq prev_next.
Qed.

Lemma mem_takeP (T : eqType) x0 x k (s : seq T) :
  reflect (exists2 i, i < minn k (size s) & x = nth x0 s i) (x \in take k s).
Proof.
by apply: (iffP (@nthP _ _ _ x0)) => [] [i];
  rewrite size_take -/(minn _ _) => isz; do [move <-|move ->];
  exists i => //; rewrite nth_take //;
  exact: leq_trans isz (geq_minl _ _).
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
apply: (inj_map val_inj); rewrite map_take map_filter_comp val_enum_ord.
rewrite take_iota /minn.
case: (ltnP k n) => Hk.
- elim: k n Hk => [//= | k IHk] n Hk /=.
  + by rewrite (eq_filter (a2 := pred0)) // filter_pred0.
  + case: n Hk => [//= | n] Hk /=.
    rewrite -[1]addn0 !iotaDl (IHk _ Hk).
    by rewrite filter_map /= -!map_comp.
- rewrite (eq_in_filter (a2 := predT)); first by rewrite filter_predT map_id.
  move=> i /=; rewrite mem_iota add0n => /andP [_ H2].
  by rewrite (leq_trans H2 Hk).
Qed.

Lemma mem_drop_enumI n (i : 'I_n) k : i \in drop k (enum 'I_n) = (i >= k).
Proof.
case (leqP k n) => Hkn.
- case: i => i Hi /=.
  rewrite -(mem_map val_inj) map_drop val_enum_ord /= drop_iota mem_iota /= add0n.
  by rewrite (subnKC Hkn) Hi andbT.
- rewrite drop_oversize; last by rewrite size_enum_ord; apply: ltnW.
  have:= ltn_trans (ltn_ord i) Hkn.
  by rewrite in_nil ltnNge => /negbTE => ->.
Qed.

Lemma drop_enumI n k : drop k (enum 'I_n) = filter ((leq k) \o val) (enum 'I_n).
Proof.
apply: (inj_map val_inj); rewrite map_drop map_filter_comp val_enum_ord.
rewrite drop_iota add0n.
case: (leqP n k) => Hk.
- have:= Hk; rewrite -subn_eq0 => /eqP -> /=.
  rewrite (eq_in_filter (a2 := pred0)); first by rewrite filter_pred0.
  move=> i; rewrite mem_iota add0n => /andP [_ Hi].
  have:= leq_trans Hi Hk.
  by rewrite ltnNge => /negbTE => ->.
- move Hdiff : (n - k) => d; move: Hdiff => /eqP.
  rewrite -(eqn_add2r k) subnK; last exact: ltnW.
  move/eqP -> => {n Hk}.
  rewrite addnC iota_add filter_cat map_id add0n.
  rewrite (eq_in_filter (a2 := pred0)); first last.
    move=> i; rewrite mem_iota add0n => /andP [_ Hi].
    by move: Hi; rewrite ltnNge => /negbTE => ->.
  rewrite filter_pred0 cat0s.
  rewrite (eq_in_filter (a2 := predT)); first by rewrite filter_predT.
  by move=> i; rewrite mem_iota => /andP [->].
Qed.

Lemma enum0 : enum 'I_0 = [::].
Proof. by apply/nilP; rewrite /nilp size_enum_ord. Qed.


Section BigOp.

Import Monoid.Theory.

Variable R : Type.
Variable idx : R.
Local Notation "1" := idx.
Variable op : Monoid.law 1.
Local Notation "'*%M'" := op (at level 0).
Local Notation "x * y" := (op x y).

Lemma big_pmap (J I : Type) (h : J -> option I) r F :
  \big[*%M/1]_(i <- pmap h r) F i = \big[*%M/1]_(j <- r) oapp F idx (h j).
Proof.
elim: r => [| r0 r IHr]/=; first by rewrite !big_nil.
rewrite /= big_cons; case: (h r0) => [i|] /=; last by rewrite Monoid.mul1m.
by rewrite big_cons IHr.
Qed.

End BigOp.


Section AbelianBigOp.

Import Monoid.Theory.

Variable R : Type.
Variable idx : R.
Local Notation "1" := idx.
Variable op : Monoid.com_law 1.
Local Notation "'*%M'" := op (at level 0).
Local Notation "x * y" := (op x y).

(** mathcomp version is restrcticted to [s == enum I] for [I : finType] *)
Lemma partition_big I (s : seq I)
      (J : finType) (P : pred I) (p : I -> J) (Q : pred J) F :
  (forall i, P i -> Q (p i)) ->
  \big[*%M/1]_(i <- s | P i) F i =
  \big[*%M/1]_(j : J | Q j) \big[*%M/1]_(i <- s | (P i) && (p i == j)) F i.
Proof.
move=> Qp; transitivity (\big[*%M/1]_(i <- s | P i && Q (p i)) F i).
  by apply: eq_bigl => i; case Pi: (P i); rewrite // Qp.
have [n leQn] := ubnP #|Q|; elim: n => // n IHn in Q {Qp} leQn *.
case: (pickP Q) => [j Qj | Q0]; last first.
  by rewrite !big_pred0 // => i; rewrite Q0 andbF.
rewrite (bigD1 j) // -IHn; last by rewrite ltnS (cardD1x Qj) add1n in leQn.
rewrite (bigID (fun i => p i == j)); congr (_ * _); apply: eq_bigl => i.
  by case: eqP => [-> | _]; rewrite !(Qj, simpm).
by rewrite andbA.
Qed.

Lemma big_seq_sub (T : countType) (s : seq T) F :
  \big[op/idx]_(x : seq_sub s) F (ssval x) = \big[op/idx]_(x <- undup s) F x.
Proof.
rewrite -[LHS](big_map (ssval (s := s)) xpredT (fun x : T => F x)).
apply perm_big; apply uniq_perm.
- rewrite map_inj_uniq; last exact: val_inj.
  exact: index_enum_uniq.
- exact: undup_uniq.
- move=> x; rewrite mem_undup; apply/mapP/idP => [/= [y _ ->] | Hx].
  + by case: y => y /= Hy.
  + by exists (SeqSub Hx); rewrite // mem_index_enum.
Qed.

End AbelianBigOp.
Arguments partition_big [R idx op I s J P] p Q [F].


Section SetPartition.

Variable T : finType.
Implicit Types (X : {set T}) (P : {set {set T}}).

Lemma partition0P P : reflect (P = set0) (partition P set0).
Proof using.
apply (iffP and3P) => [[/eqP Hcov _ H0] | ->].
- case: (set_0Vmem P) => [// | [X HXP]].
  exfalso; suff HX : X = set0 by subst X; rewrite HXP in H0.
  by apply/eqP; rewrite -subset0; rewrite -Hcov (bigcup_max X).
- by split; rewrite ?inE // /trivIset /cover !big_set0 ?cards0.
Qed.

Lemma triv_part P X : X \in P -> partition P X -> P = [set X].
Proof using.
move=> HXP /and3P [/eqP Hcov /trivIsetP /(_ X _ HXP) H H0].
apply/setP => Y; rewrite inE; apply/idP/idP => [HYP | /eqP -> //].
rewrite eq_sym; move/(_ Y HYP): H => /contraR; apply.
have /set0Pn [y Hy] : Y != set0
  by apply/negP => /eqP HY; move: H0; rewrite -HY HYP.
apply/negP => /disjoint_setI0/setP/(_ y).
by rewrite !inE Hy -Hcov andbT => /bigcupP; apply; exists Y.
Qed.

End SetPartition.

Notation "#{ x }" :=  #|(x : {set _})|
                      (at level 0, x at level 10, format "#{ x }").
