(** * Combi.SSRcomplements.tools : Missing SSReflect sequence related lemmas *)
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
(** * A bunch of lemmas about seqs which are missing in SSReflect             *)
(*                                                                            *)
(** TODO: these probably should be contributed to SSReflect itself            *)
(******************************************************************************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import finset bigop path.

Set Implicit Arguments.
Unset Strict Implicit.

Prenex Implicits nat_of_ord.

Hint Resolve nth_nil.

Lemma leq_addE m1 m2 n1 n2 :
  m1 <= m2 -> n1 <= n2 -> m1 + n1 = m2 + n2 -> m1 = m2 /\ n1 = n2.
Proof.
  move=> Hm Hn H.
  suff Hmeq : m1 = m2 by split => //; move: H; rewrite Hmeq => /addnI.
  apply anti_leq; rewrite Hm /=.
  have:= leq_sub2l (m1 + n1) Hn; by rewrite {1}H !addnK.
Qed.

Lemma nseqD T n1 n2 (x : T):
  nseq (n1 + n2) x = nseq n1 x ++ nseq n2 x.
Proof. by rewrite cat_nseq /nseq /ncons iter_add. Qed.

Lemma rev_nseq (T : eqType) (x : T) d : rev (nseq d x) = nseq d x.
Proof.
  elim: d => [//= | d IHd].
  by rewrite -{1}(addn1 d) nseqD rev_cat IHd /=.
Qed.

(** ** [rcons] and [cons] related lemmas *)
Section SeqLemmas.

Variable (T : eqType).
Implicit Type s w : seq T.
Implicit Type a b : T.

Lemma flatten_rcons s t : flatten (rcons t s) = flatten t ++ s.
Proof using .
  elim: t => [//= | t0 t IHt /=]; first by rewrite cats0.
  by rewrite IHt catA.
Qed.

Lemma cons_head_behead x s : (s != [::]) -> head x s :: behead s = s.
Proof using . by case s. Qed.

Lemma belast_behead_rcons x l s :
  belast (head x (rcons s l)) (behead (rcons s l)) = s.
Proof using . case: s => [//= | s0 s]; by rewrite rcons_cons /= belast_rcons. Qed.

Lemma last_behead_rcons x l s :
  last (head x (rcons s l)) (behead (rcons s l)) = l.
Proof using . case: s => [//= | s0 s]; by rewrite rcons_cons /= last_rcons. Qed.

Lemma set_head_default s b a : s != [::] -> head a s = head b s.
Proof using . by elim: s. Qed.

Lemma rcons_set_nth a s l : set_nth a s (size s) l = rcons s l.
Proof using . elim: s => [//=| l0 s IHs]. by rewrite rcons_cons -IHs /=. Qed.

Lemma set_nth_rcons x0 s x n y :
  set_nth x0 (rcons s x) n y =
  if n < size s then rcons (set_nth x0 s n y) x
  else if n == size s then rcons s y else (rcons s x) ++ ncons (n - size s).-1 x0 [:: y].
Proof using .
  elim: s n => [//= | s0 s IHs] n.
  + case eqP => [-> //= |]; by case: n => [| []].
  + rewrite rcons_cons /=; case: n => [//= | n] /=.
    move/(_ n) : IHs; rewrite eqSS ltnS.
    by case (ltngtP n (size s)) => _ <-.
Qed.

Lemma rconsK a u v : rcons u a = rcons v a -> u = v.
Proof using .
  elim: u v => [| u0 u IHu]; case=> [|v0 v] //= [].
  + move=> _; by case v.
  + move=> _; by case u.
  + by move=> -> /IHu ->.
Qed.

Lemma cons_in_map_cons a b s w :
  forall l : seq (seq T), a :: s \in [seq b :: s1 | s1 <- l] -> a == b.
Proof using .
  elim=> [//=| l0 l H]; rewrite map_cons in_cons; move/orP => []; last by exact H.
  by move=> /eqP [] ->.
Qed.

Lemma rcons_nilF s l : ((rcons s l) == [::]) = false.
Proof using . case eqP=>//= H; have:= eq_refl (size (rcons s l)). by rewrite {2}H size_rcons. Qed.

Lemma count_mem_rcons w l i : count_mem i (rcons w l) = count_mem i w + (l == i).
Proof using . by rewrite -count_rev rev_rcons /= count_rev addnC. Qed.

(** ** [set_nth] related lemmas *)
Lemma set_nth_non_nil d s n y : set_nth d s n y != [::].
Proof using . elim: s => [|s0 s]; by case n. Qed.

Lemma nth_set_nth_expand a b l i c j :
  (size l <= j < i) -> nth a (set_nth b l i c) j = b.
Proof using .
  elim: l i j => [/= | l0 l IHl].
  - elim => [//= | i' Hi] /=.
    case => [//= | j /=]; by rewrite nth_ncons /leq subSS => ->.
  - elim => [//= | i' Hi] j /=; first by rewrite ltn0 andbF.
    case: j Hi => [//= | j /=] Hi /andP [] H1 H2.
    apply: IHl; by move: H1 H2; rewrite !/leq !subSS => -> ->.
Qed.

Lemma nth_set_nth_any a b l i c j :
  nth a (set_nth b l i c) j =
  if j == i then c else
    if j < size l then nth a l j else
      if j <= i then b else a.
Proof using .
  case eqP => [<- | /eqP Hneq].
  - have Hj : j < size (set_nth b l j c) by rewrite size_set_nth; apply: leq_maxl.
    by rewrite (set_nth_default b a Hj) nth_set_nth /= eq_refl.
  - case (ltnP j (size l)) => Hjsz.
    + have Hj : j < size (set_nth b l i c)
        by rewrite size_set_nth; apply: (leq_trans Hjsz); apply: leq_maxr.
      rewrite (set_nth_default b a Hj) nth_set_nth /= (negbTE Hneq).
      exact: set_nth_default.
    + case (leqP j i) => Hij.
      * apply: nth_set_nth_expand; by rewrite Hjsz /= ltn_neqAle Hneq Hij.
      * rewrite nth_default; first by [].
        rewrite size_set_nth /maxn; by case (ltnP i.+1 (size l)).
Qed.

End SeqLemmas.

(** ** [sumn] related lemmas *)
Lemma sumn_count (T : eqType) (s : seq T) (P : T -> bool) :
  sumn [seq nat_of_bool (P i) | i <- s] = count P s.
Proof. by elim: s => //= s0 s /= ->. Qed.

Lemma sumn_rev (s : seq nat) : sumn (rev s) = sumn s.
Proof.
  elim: s => [//= | s0 s /= <-].
  by rewrite rev_cons -cats1 sumn_cat /= addn0 addnC.
Qed.

Lemma sumn_map_condE (T : Type) (s : seq T) (f : T -> nat) (P : pred T) :
  \sum_(i <- s | P i) f i = sumn [seq f i | i <- s & P i].
Proof.
  elim: s => [//= | s0 s IHs] /=; first by rewrite big_nil.
  rewrite big_cons IHs.
  by case: (P s0).
Qed.

Lemma sumn_mapE (T : Type) (s : seq T) (f : T -> nat) :
  \sum_(i <- s) f i = sumn [seq f i | i <- s].
Proof. by rewrite sumn_map_condE filter_predT. Qed.

Lemma sumnE s : \sum_(i <- s) i = sumn s.
Proof. by rewrite sumn_mapE map_id. Qed.

Lemma perm_sumn l1 l2 : perm_eq l1 l2 -> sumn l1 = sumn l2.
Proof. rewrite -!sumnE; exact: eq_big_perm. Qed.

Lemma sumn_take r s : sumn (take r s) = \sum_(0 <= i < r) nth 0 s i.
Proof.
  elim: r s => [|r IHr] s /=.
    by rewrite take0 /index_iota /= big_nil.
  case: s => [| s0 s] /=.
    rewrite {IHr} (eq_bigr (fun _ => 0)) //.
    rewrite big_const_nat subn0.
    by elim: r.
  rewrite IHr /index_iota !subn0 /= big_cons /=.
  congr (_ + _); rewrite -add1n iota_addl big_map.
  exact: eq_bigr.
Qed.

Lemma sum_iota_sumnE l n :
  size l <= n -> \sum_(0 <= i < n) nth 0 l i = sumn l.
Proof. by rewrite -sumn_take => /take_oversize ->. Qed.


Lemma size_take_leq (T : Type) n0 (s : seq T) :
  size (take n0 s) = (if n0 <= size s then n0 else size s).
Proof.
  rewrite size_take (leq_eqVlt n0).
  by case: eqP => [->| _]/=; first by rewrite ltnn.
Qed.

Section TakeDropFlatten.
(** ** [take] and [drop] related lemmas *)
Variable T : eqType.
Implicit Type l s w : seq T.
Implicit Type t : seq (seq T).

Lemma take_rev l i : take i (rev l) = rev (drop (size l - i) l).
Proof using .
  elim: i l => [| i IHi] l.
    by rewrite take0 subn0 drop_size.
  case/lastP: l => [//= | l' ln].
  rewrite rev_rcons /= IHi -rev_rcons.
  congr (rev _).
  rewrite size_rcons subSS.
  rewrite -(cats1 l') drop_cat.
  case: ltnP; first by rewrite cats1.
  move=> /drop_oversize -> /=.
  suff -> : size l' - i - size l' = 0 by [].
  by rewrite subnAC subnn sub0n.
Qed.

Lemma drop_rev l i : drop i (rev l) = rev (take (size l - i) l).
Proof using .
  elim: i l => [| i IHi] l.
    by rewrite drop0 subn0 take_size.
  case/lastP: l => [//= | l' ln].
  rewrite rev_rcons /= IHi; congr (rev _).
  rewrite size_rcons subSS -cats1 take_cat.
  case: ltnP => //= /take_oversize ->.
  suff -> : size l' - i - size l' = 0 by rewrite cats0.
  by rewrite subnAC subnn sub0n.
Qed.

Lemma drop_drop s n1 n2 : drop n1 (drop n2 s) = drop (n1 + n2) s.
Proof using .
  elim: s n1 n2 => [| s0 s IHs] //=.
  case=> [//= | n1] n2; first by rewrite drop0 add0n.
  rewrite addSn; case: n2 => [//=| n2]; first by rewrite addn0.
  by rewrite -addSnnS.
Qed.

(** ** [flatten], [shape] and [reshape] related lemmas *)

Lemma flatten_seq1 s : flatten [seq [:: x] | x <- s] = s.
Proof using . by elim: s => [//= | s0 s /= ->]. Qed.

Lemma count_flatten t P :
  count P (flatten t) = sumn [seq count P x | x <- t].
Proof using . elim: t => [//= | t0 t IHt /=]. by rewrite count_cat IHt. Qed.

Lemma map_flatten (T1 T2 : eqType) (f : T1 -> T2) (t : seq (seq T1)) :
  map f (flatten t) = flatten (map (map f) t).
Proof using . elim: t => [//= | t0 t /= <-]; exact: map_cat. Qed.

Lemma filter_flatten t (P : pred T) :
  filter P (flatten t) = flatten [seq filter P i | i <- t].
Proof using . elim: t => [//= | t0 t /= <-]; exact: filter_cat. Qed.

Lemma sumn_flatten (t : seq (seq nat)) :
  sumn (flatten t) = sumn (map sumn t).
Proof using . elim: t => [//= | t0 t /= <-]; exact: sumn_cat. Qed.


Lemma nth_shape t i : nth 0 (shape t) i = size (nth [::] t i).
Proof using .
  rewrite /shape; case: (ltnP i (size t)) => Hi; first exact: nth_map.
  by rewrite !nth_default // size_map.
Qed.

Lemma shape_rev t : shape (rev t) = rev (shape t).
Proof using . rewrite /shape; elim: t => [//= | t0 t IHt] /=; by rewrite map_rev. Qed.

Lemma eq_from_flatten_shape (u v : seq (seq T)) :
  (u = v) <-> ((flatten u = flatten v) /\ (shape u = shape v)).
Proof using .
  split; first by move ->.
  move=> [] Hflat Hshape.
  by rewrite -(flattenK u) -(flattenK v) Hflat Hshape.
Qed.

Lemma rev_flatten (t : seq (seq T)) :
  rev (flatten t) = flatten (rev (map rev t)).
Proof using .
  elim: t => [| t0 t IHt] //=.
  by rewrite rev_cons flatten_rcons -IHt rev_cat.
Qed.

Lemma rev_reshape (s : seq nat) (l : seq T) :
  size l = sumn s -> rev (map rev (reshape (rev s) (rev l))) = reshape s l.
Proof using .
  move=> H; apply eq_from_flatten_shape; split.
  - rewrite reshapeKr; last by rewrite H.
    rewrite -rev_flatten reshapeKr; first by rewrite revK.
    by rewrite size_rev H sumn_rev.
  - rewrite shape_rev /shape -map_comp.
    rewrite (eq_map (f2 := size)); last by move=> v; rewrite /= size_rev.
    rewrite -/(shape _) reshapeKl; last by rewrite size_rev sumn_rev H.
    rewrite -/(shape _) reshapeKl; last by rewrite H.
    by rewrite revK.
Qed.

Lemma nth_reshape (s : seq nat) (l : seq T) n :
  nth [::] (reshape s l) n = take (nth 0 s n) (drop (sumn (take n s)) l).
Proof using .
  elim: n s l => [| n IHn] [| s0 s] l; rewrite ?take0 ?drop0 //=.
  rewrite addnC -drop_drop; exact: IHn.
Qed.

End TakeDropFlatten.

Lemma map_reshape (T1 T2 : Type) (f : T1 -> T2) sh (s : seq T1) :
  map (map f) (reshape sh s) = reshape sh (map f s).
Proof. elim: sh s => [//= | sh0 sh IHsh] /= s;  by rewrite map_take IHsh map_drop. Qed.

Lemma size_reshape (T : Type) sh (s : seq T) : size (reshape sh s) = size sh.
Proof. elim: sh s => [//= | s0 sh IHsh] /= s; by rewrite IHsh. Qed.

Lemma reshape_rcons (T : Type) (s : seq T) sh sn :
  sumn sh + sn = size s ->
  reshape (rcons sh sn) s = rcons (reshape sh (take (sumn sh) s)) (drop (sumn sh) s).
Proof.
  elim: sh s => [//= | s0 sh IHsh] /= s.
    rewrite add0n => Hsz.
    by rewrite drop0 take_oversize; last by rewrite Hsz.
  move=> Hsize.
  rewrite (_ : take (s0 + sumn sh) s = take s0 s ++ take (sumn sh) (drop s0 s));
    first last.
    rewrite -{1 3}[s](cat_take_drop s0) drop_cat take_cat.
    rewrite  size_take_leq -Hsize -addnA leq_addr.
    by rewrite ltnNge leq_addr /= addKn ltnn subnn drop0.
  rewrite take_cat drop_cat.
  rewrite size_take_leq -Hsize -addnA leq_addr.
  rewrite ltnn subnn take0 cats0 drop0.
  rewrite (_ : drop (s0 + sumn sh) s = drop (sumn sh) (drop s0 s)); first last.
    rewrite -[s](cat_take_drop s0) !drop_cat.
    rewrite size_take_leq -Hsize -addnA leq_addr.
    by rewrite ltnNge leq_addr /= addKn ltnn subnn drop0.
  by rewrite -IHsh; last by rewrite size_drop -Hsize -addnA addKn.
Qed.

(** ** converting coordinate in a [seq [seq T]] and its flatten version *)
Fixpoint reshape_coord sh i :=
  if sh is s0 :: s then
    if i < s0 then (0, i)
    else let (r, c) := reshape_coord s (i - s0) in (r.+1, c)
  else (0, i).

Definition flatten_coord sh r c := (\sum_(0 <= j < r) nth 0 sh j) + c.

Lemma flatten_coordP sh r c :
  c < nth 0 sh r -> flatten_coord sh r c < sumn sh.
Proof.
  case: (ltnP r (size sh)) => Hr; last by rewrite (nth_default _ Hr).
  rewrite -(sum_iota_sumnE (n := size sh)) // => Hc.
  rewrite (big_cat_nat _ _ _ _ (ltnW Hr)) //= ltn_add2l.
  rewrite (big_ltn Hr); exact: ltn_addr.
Qed.

Lemma reshape_coordP sh i :
  i < sumn sh -> let (r, c) := (reshape_coord sh i) in r < size sh /\ c < nth 0 sh r.
Proof.
  elim: sh i => [| s0 s IHs] i //= Hi.
  case: (ltnP i s0) => His0 //=.
  move/(_ (i - s0)) : IHs; case: (reshape_coord s (i - s0)) => r c /=.
  rewrite ltnS; apply.
  by rewrite -(subSn His0) leq_subLR.
Qed.

Lemma reshape_coordK sh i :
  let (r, c) := reshape_coord sh i in flatten_coord sh r c = i.
Proof.
  rewrite /flatten_coord.
  elim: sh i => [| s0 s IHs] i //=; first by rewrite /index_iota /= big_nil.
  case: (ltnP i s0) => His0 //=; first by rewrite /index_iota /= big_nil.
  move/(_ (i - s0)) : IHs; case: (reshape_coord s (i - s0)) => r c.
  rewrite big_nat_recl //= -addnA => ->.
  exact: subnKC.
Qed.

Lemma flatten_coordK sh r c :
  c < nth 0 sh r -> reshape_coord sh (flatten_coord sh r c) = (r, c).
Proof.
  rewrite /flatten_coord.
  elim: r c sh => [| r IHr] /= c [//= | s0 s] /=.
    by rewrite /index_iota subn0 /= big_nil add0n => ->.
  rewrite (_ : \sum_(0 <= j < r.+1) nth 0 (s0 :: s) j
               = s0 + \sum_(0 <= j < r) nth 0 s j); last by rewrite big_nat_recl.
  rewrite [X in if X then _ else _]ltnNge -addnA leq_addr /=.
  by rewrite addKn => /IHr ->.
Qed.

Lemma nth_flatten T (x : T) tab i :
  nth x (flatten tab) i = let (r, c) := (reshape_coord (shape tab) i) in
                          nth x (nth [::] tab r) c.
Proof.
  elim: tab i => [| t0 t IHt] //= i.
  rewrite nth_cat; case: ltnP => //= Hi.
  rewrite IHt {IHt}; by case: (reshape_coord (shape t) (i - size t0)) => r c.
Qed.

(** ** [iota] related lemmas *)
Lemma sumn_iota a b x :
  a <= x < a + b -> sumn [seq ((i == x) : nat) | i <- iota a b] = 1.
Proof.
  elim: b a => [/=| b IHb] a.
    rewrite addn0 => /andP [] /leq_ltn_trans H/H{H}.
    by rewrite ltnn.
  move/(_ a.+1) : IHb => /= IHb.
  case (ltnP a x) => H1 /andP [] H2 H3.
  + rewrite IHb; first by rewrite (ltn_eqF H1).
    by rewrite H1 addSnnS.
  + rewrite eqn_leq H1 H2 /= {H2 H3 IHb}.
    apply/eqP; rewrite eqSS; apply/eqP => /=.
    elim: b a H1 => [//= | b IHb] a Ha /=.
    rewrite IHb; first by rewrite gtn_eqF; last by rewrite ltnS.
    by rewrite leqW.
Qed.

Lemma iota_ltn a b : b <= a -> [seq i <- iota 0 a | i < b] = iota 0 b.
Proof.
  move=> Hab.
  rewrite -(subnKC Hab) iota_add add0n filter_cat.
  rewrite -[RHS]cats0; congr (_ ++ _).
  - rewrite (eq_in_filter (a2 := predT)) ?filter_predT //.
    move=> i /=; by rewrite mem_iota add0n => /andP [] _ ->.
  - rewrite (eq_in_filter (a2 := pred0)) ?filter_pred0 //.
    move=> i /=. rewrite mem_iota (subnKC Hab) => /andP [].
    by rewrite leqNgt => /negbTE.
Qed.

Lemma iota_geq a b : [seq i <- iota 0 a | b <= i] = iota b (a - b).
Proof.
  elim: a => [//=| n IHn].
  rewrite -addn1 iota_add add0n /= filter_cat IHn {IHn} /=.
  case: leqP => Hb.
  - by rewrite addn1 (subSn Hb) -addn1 iota_add /= subnKC.
  - rewrite addn1 cats0.
    have := Hb; rewrite /leq => /eqP ->.
    by have := ltnW Hb; rewrite /leq => /eqP ->.
Qed.


(** ** [incr_nth] related lemmas *)
Lemma incr_nth_inj sh : injective (incr_nth sh).
Proof.
  move=> i j Hsh.
  case (altP (i =P j)) => [//= | /negbTE Hdiff].
  move/(congr1 (fun s => nth 0 s j)) : Hsh => /eqP.
  by rewrite !nth_incr_nth eq_refl Hdiff eqn_add2r.
Qed.

Lemma incr_nthC (s : seq nat) i j :
  incr_nth (incr_nth s i) j = incr_nth (incr_nth s j) i.
Proof.
  apply (eq_from_nth (x0 := 0)).
  - rewrite !size_incr_nth.
    case (ltnP i (size s)) => Hi.
    + case (ltnP j (size s)) => Hj; first by rewrite Hi.
      by rewrite ltnS (ltnW (leq_trans Hi Hj)).
    + case (ltnP j (size s)) => Hj.
      * by rewrite ltnS (ltnW (leq_trans Hj Hi)) ltnNge Hi.
      * rewrite !ltnS; case: (ltngtP i j) => Hij; last by rewrite Hij.
        - by rewrite (ltnW Hij) leqNgt Hij.
        - by rewrite (ltnW Hij) leqNgt Hij.
  - move=> k Hk; by rewrite !nth_incr_nth !addnA [(_ == _) + _]addnC.
Qed.


(** ** [perm_eq] related lemmas *)
Lemma perm_eq_rev (T : eqType) (u : seq T) : perm_eq u (rev u).
Proof.
  elim: u => [//= | u0 u]; rewrite rev_cons -(perm_cons u0).
  move /perm_eq_trans; apply.
  rewrite perm_eq_sym; apply/perm_eqlP; exact: perm_rcons.
Qed.

Lemma filter_perm_eq (T : eqType) (u v : seq T) P :
  perm_eq u v -> perm_eq (filter P u) (filter P v).
Proof.
  move=> /perm_eqP Hcount.
  apply/perm_eqP => Q; rewrite !count_filter.
  exact: Hcount.
Qed.

Lemma all_perm_eq (T : eqType) (u v : seq T) P : perm_eq u v -> all P u -> all P v.
Proof.
  move=> /perm_eq_mem Hperm /allP Hall; apply/allP => x.
  by rewrite -Hperm => /Hall.
Qed.

(** ** Unicity related lemmas *)
Lemma notuniq_witnessP (T : eqType) (x0 : T) (s : seq T) :
  reflect (exists i j, i < j < size s /\ nth x0 s i = nth x0 s j)
  (~~ uniq s).
Proof.
  apply (iffP idP).
  - elim: s => [//= | s0 s IHs] /=.
    rewrite negb_and => /orP [].
    + rewrite negbK => Hin.
      exists 0, (index s0 s).+1 => /=; split; first by rewrite ltnS index_mem.
      by rewrite nth_index.
    + move/IHs => {IHs} [] i [] j [] Hij Hnth.
      by exists i.+1, j.+1; split; first by rewrite !ltnS.
  - elim: s => [| s0 s IHs ] /= [] i [] j [] /andP [] //=.
    rewrite negb_and negbK; case: i => [| i].
    + case: j => [//= | j _]; rewrite ltnS /= => Hj ->; by rewrite mem_nth.
    + case: j => [//= | j]; rewrite !ltnS /= => Hi Hj Hnth.
      apply/orP; right; apply IHs.
      exists i, j; by rewrite Hi Hj Hnth.
Qed.


(** ** Bigop lemmas *)
Section BigInterv.

Variable R : Type.
Variable idx : R.
Variable op : Monoid.law idx.

Lemma big_nat_widen0 a b c F :
  b <= c -> \big[op/idx]_(a <= i < b) F i = \big[op/idx]_(0 <= i < c | a <= i < b) F i.
Proof using .
  move=> Hbc.
  rewrite {1}/index_iota -iota_geq -{1}(subn0 b) big_filter -/(index_iota 0 b).
  by rewrite (big_nat_widen _ _ _ _ _ Hbc).
Qed.

End BigInterv.

Lemma sum_nth_rev s a b :
   \sum_(a <= i < b) nth 0 (rev s) i = \sum_(size s - b <= i < size s - a) nth 0 s i.
Proof.
  have sum0 u v : size s <= u -> \sum_(u <= i < v) nth 0 (rev s) i = 0.
    move=> Hu; rewrite big_seq_cond [LHS](eq_bigr (fun i => 0)); first last.
      move=> i; rewrite mem_iota => /andP [] /andP [] Hai _ _.
      rewrite nth_default // size_rev; exact: leq_trans Hu Hai.
    by rewrite -big_seq_cond -/(index_iota _ _) /= sum_nat_const_nat muln0.
  wlog Hbs: b / b <= (size s).
    move=> Hwlog; case: (leqP b (size s)) => [| /ltnW Hbs]; first exact: Hwlog.
    move/(_ (size s) (leqnn (size s))) : Hwlog.
    have:= Hbs; rewrite subnn {1}/leq => /eqP -> <-.
    case: (ltnP a (size s)) => Has.
    - by rewrite (big_cat_nat _ _ _ (ltnW Has) Hbs) /= (sum0 _ _ (leqnn (size s))) addn0.
    - rewrite {2}/index_iota; have:= Has; rewrite /leq => /eqP -> /=.
      by rewrite (sum0 _ _ Has) big_nil.
  case: (ltnP a b) => Hab; first last.
  - rewrite /index_iota; have:= Hab; rewrite /leq => /eqP -> /=.
    have := leq_sub2l (size s) Hab; rewrite /leq => /eqP -> /=.
    by rewrite !big_nil.
  - rewrite (big_nat_widen0 _ _ _ Hbs) big_nat_rev /= add0n.
    rewrite big_seq_cond [LHS](eq_bigr (fun i => nth 0 s i)); first last.
      move=> i /and3P []; rewrite mem_iota add0n subn0 => /andP [] _ Hi Hi1 Hi2.
      rewrite nth_rev; last exact (leq_trans Hi2 Hbs).
      congr nth; by rewrite subnS subKn.
    rewrite (eq_bigl (fun i => size s - b <= i < size s - a)); first last.
      move=> i /=; rewrite mem_iota add0n subn0 leq0n /=.
        rewrite leq_subLR addnC -leq_subLR ltn_subRL addnC -ltn_subRL [RHS]andbC.
        case: (size s) => [//= | n]; rewrite subSS ltnS.
        case: (leqP i n) => [Hn | /=]; first by rewrite (subSn Hn) ltnS.
        rewrite {1}/leq => /eqP ->.
        by rewrite ltn0.
    rewrite -big_nat_widen0 //; exact: leq_subr.
Qed.



Section Enum.

Variable T: finType.

Variables (R : Type) (idx : R) (op : R -> R -> R) (F : T -> R).

Lemma enum_eq0P (s : {set T}):
  reflect (enum s = [::]) (s == set0).
Proof.
  apply (iffP eqP) => [-> |]; first exact: enum_set0.
  case: (set_0Vmem s) => [-> //| [x]].
  rewrite -mem_enum => Hx Hnil.
  by rewrite Hnil in_nil in Hx.
Qed.

Lemma big_enum (S : {set T}) :
  \big[op/idx]_(s in S) F s = \big[op/idx]_(s <- enum S) F s.
Proof. by rewrite /index_enum big_filter; apply congr_big. Qed.

End Enum.




(* New lemmas *)
Lemma sumn_sort l S : sumn (sort S l) = sumn l.
Proof using. by have:= perm_sort S l => /perm_eqlP/perm_sumn. Qed.

Section ImsetInj.

Implicit Type T : finType.

Lemma set1_disjoint T (i j : T) : [set i] != [set j] -> [disjoint [set i] & [set j]].
Proof.
  move=> Hneq; rewrite /disjoint; apply/pred0P => l /=; apply: negbTE.
  rewrite !in_set1; move: Hneq; by apply: contra => /andP [] /eqP -> /eqP ->.
Qed.

Lemma mem_imset_inj T1 T2 (f : T1 -> T2) (i : T1) (s : {set T1}) :
  injective f -> (f i) \in f @: s = (i \in s).
Proof.
  move=> H; apply/idP/idP; last exact: mem_imset.
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
  move=> Hinj /subsetP H.
  by apply/subsetP => x /(mem_imset f) /(H _) /imsetP [] y Hy /Hinj ->.
Qed.

Lemma imset_inj T1 T2 (f : T1 -> T2) :
  injective f -> injective (fun s : {set T1} => (imset f (mem s))).
Proof.
  move=> Hinj s1 s2 /eqP; rewrite eqEsubset => /andP [] H12 H21.
  move: Hinj => /subset_imsetK Hinj.
  apply/eqP; rewrite eqEsubset.
  by rewrite (Hinj _ _ H12) (Hinj _ _ H21).
Qed.

Lemma imset_trivIset T1 T2 (F : T1 -> T2) (P : {set {set T1}}) :
  injective F -> trivIset P -> trivIset ((fun s : {set T1} => F @: s) @: P).
Proof.
  move=> Hinj /trivIsetP Htriv.
  apply/trivIsetP => A B /imsetP [] FA FAP -> {A} /imsetP [] FB FBP -> Hneq.
  have {Hneq} Hneq : FA != FB by move: Hneq; apply: contra => /eqP ->.
  have:= Htriv _ _ FAP FBP Hneq; rewrite -!setI_eq0 -imsetI.
  * move=> /eqP ->; by rewrite imset0.
  * move=> i j _ _ /=; exact: Hinj.
Qed.

Lemma preimset_trivIset T1 T2 (F : T1 -> T2) (P : {set {set T2}}) :
  injective F -> trivIset P -> trivIset ((fun s : {set T2} => F @^-1: s) @: P).
Proof.
  move=> Hinj /trivIsetP Htriv.
  apply/trivIsetP => A B /imsetP [] FA FAP -> {A} /imsetP [] FB FBP -> Hneq.
  have {Hneq} Hneq : FA != FB by move: Hneq; apply: contra => /eqP ->.
  have:= Htriv _ _ FAP FBP Hneq; rewrite -!setI_eq0 -preimsetI => /eqP ->.
  by rewrite preimset0.
Qed.

Lemma disjoint_imset T1 T2 (f : T1 -> T2) (A B : {set T1}) :
  injective f ->
  [disjoint A & B] -> [disjoint [set f x | x in A] & [set f x | x in B]].
Proof using.
rewrite -!setI_eq0 => Hinj /eqP Hdisj.
rewrite -imsetI; last by move=> x y _ _; exact: Hinj.
by rewrite imset_eq0 Hdisj.
Qed.

End ImsetInj.

Lemma uniq_next (T : eqType) (p : seq T) : uniq p -> injective (next p).
Proof using.
move=> Huniq x y Heq.
by rewrite -(prev_next Huniq x) Heq prev_next.
Qed.


Reserved Notation "#{ x }" (at level 0, x at level 10, format "#{ x }").
Notation "#{ x }" :=  #|(x : {set _})|
                      (at level 0, x at level 10, format "#{ x }").


Module LeqGeqOrder.

Definition geq_total : total geq :=
  fun x y => leq_total y x.
Definition geq_trans : transitive geq :=
  fun x y z H1 H2 => leq_trans H2 H1.
Definition anti_geq : antisymmetric geq :=
  fun x y H => esym (anti_leq H).

Hint Resolve leq_total leq_trans anti_leq geq_total geq_trans anti_geq.

End LeqGeqOrder.

Import LeqGeqOrder.

Lemma mem_takeP (T : eqType) x0 x k (s : seq T) :
  reflect (exists i, i < minn k (size s) /\ x = nth x0 s i) (x \in take k s).
Proof.
  apply: (iffP idP).
  - move=> Hx; pose ix := index x (take k s).
    have Hix : ix < size s.
      move: Hx; rewrite /ix -index_mem size_take.
      case: (ltnP k (size s)) => //= H1 H2; exact: (ltn_trans H2 H1).
    have Hix2: ix < k.
      move: Hx; rewrite /ix -index_mem size_take /=.
      by case: (ltnP k (size s)) => H; last by move/leq_trans; apply.
    exists ix; split; first by rewrite leq_min Hix Hix2.
    by rewrite -{1}(nth_index x0 Hx) nth_take.
  - move=> [] i [] Hi ->.
    have Hik := leq_trans Hi (geq_minl k (size s)).
    have Hsz := leq_trans Hi (geq_minr k (size s)).
    rewrite -(nth_take _ Hik); apply: mem_nth; rewrite size_take.
    by case (ltnP k (size s)).
Qed.

Lemma take_iota i k n : take k (iota i n) = iota i (minn k n).
Proof.
  rewrite /minn; case: (ltnP k n) => H; last by apply: take_oversize; rewrite size_iota.
  elim: k n H i => [//= | k IHk]; first by case.
  case=> //= n H i; congr (i :: _); exact: IHk.
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
  apply: (inj_map val_inj); rewrite map_take map_filter_comp val_enum_ord.
  rewrite take_iota /minn.
  case: (ltnP k n) => Hk.
  - elim: k n Hk => [//= | k IHk] n Hk /=.
    + by rewrite (eq_filter (a2 := pred0)) // filter_pred0.
    + case: n Hk => [//= | n] Hk /=.
      rewrite -[1]addn0 !iota_addl (IHk _ Hk).
      by rewrite filter_map /= -!map_comp.
  - rewrite (eq_in_filter (a2 := predT)); first by rewrite filter_predT map_id.
    move=> i /=; rewrite mem_iota add0n => /andP [] _ H2.
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
    move=> i; rewrite mem_iota add0n => /andP [] _ Hi.
    have:= leq_trans Hi Hk.
    by rewrite ltnNge => /negbTE => ->.
  - move Hdiff : (n - k) => d; move: Hdiff => /eqP.
    rewrite -(eqn_add2r k) subnK; last exact: ltnW.
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
