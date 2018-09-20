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
From mathcomp Require Import finset bigop path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


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
    rewrite {IHr} (eq_bigr (fun => 0)) //.
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

(** ** Bigop lemmas *)
Section BigInterv.

Variable R : Type.
Variable idx : R.
Variable op : Monoid.law idx.

Lemma big_nat_widen0 a b c F :
  b <= c ->
  \big[op/idx]_(a <= i < b) F i =
  \big[op/idx]_(0 <= i < c | a <= i < b) F i.
Proof using .
  move=> Hbc.
  rewrite {1}/index_iota -iota_geq -{1}(subn0 b) big_filter -/(index_iota 0 b).
  by rewrite (big_nat_widen _ _ _ _ _ Hbc).
Qed.

Lemma big_nat_0cond n f :
  \big[op/idx]_(0 <= i < n) f i =
  \big[op/idx]_(0 <= i < n | (i < n)%N) f i.
Proof.
rewrite big_seq_cond /=.
rewrite (eq_bigl (fun i => (i < n)%N)); first by [].
by move=> i; rewrite /= mem_index_iota leq0n /= andbT.
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

Variable T : finType.

Lemma setU1E (x : T) (S : {set T}) : x \in S -> x |: S = S.
Proof.
move=> Hx; apply/setP/subset_eqP/andP; split; apply/subsetP=> i.
- by move/setU1P => [] ->.
- by move=> H; apply/setU1P; right.
Qed.

Lemma enum_eq0P (S : {set T}):
  reflect (enum S = [::]) (S == set0).
Proof.
  apply (iffP eqP) => [-> |]; first exact: enum_set0.
  case: (set_0Vmem S) => [-> //| [x]].
  rewrite -mem_enum => Hx Hnil.
  by rewrite Hnil in_nil in Hx.
Qed.

Variables (R : Type) (idx : R) (op : R -> R -> R) (F : T -> R).

Lemma big_enum (P : pred T) :
  \big[op/idx]_(x in P) F x = \big[op/idx]_(x <- enum P) F x.
Proof. by rewrite /index_enum big_filter; apply congr_big. Qed.

End Enum.




(* New lemmas *)
Lemma sumn_sort l S : sumn (sort S l) = sumn l.
Proof using. by have:= perm_sort S l => /perm_eqlP/perm_sumn. Qed.


Lemma count_nseq (T : eqType) (P : pred T) n x :
  count P (nseq n x) = (P x) * n.
Proof.
rewrite (eq_in_count (a2 := fun => P x)); last by move=> i /nseqP [->].
case: (boolP (P x)) => HPx; rewrite /= ?mul0n ?count_pred0 //.
by rewrite ?mul1n ?0count_predT size_nseq.
Qed.

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


Notation "#{ x }" :=  #|(x : {set _})|
                      (at level 0, x at level 10, format "#{ x }").

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

Section LRShift.

Variables (m n : nat).

Lemma lshift_inj : injective (@lshift m n).
Proof using .
  move=> [] i Hi [] j Hj /eqP H; apply/eqP; move: H; by rewrite !/eq_op /=.
Qed.
Lemma rshift_inj : injective (@rshift m n).
Proof using .
  move=> [] i Hi [] j Hj /eqP H; apply/eqP; move: H; by rewrite !/eq_op /= eqn_add2l.
Qed.

Lemma lrshiftF i j : ((@lshift m n i) == (@rshift m n j)) = false.
Proof using .
  apply: (introF idP); case: i j => [] i Hi [] j Hj.
  rewrite /eq_op /= => /eqP H.
  move: Hi; by rewrite H ltnNge leq_addr.
Qed.

End LRShift.

Section SeqSub.

Variables (T : countType) (R : Type).

Variable idx : R.
Variable op : Monoid.com_law idx.

Lemma big_seq_sub (s : seq T) F :
  \big[op/idx]_(x : seq_sub s) F (ssval x) = \big[op/idx]_(x <- undup s) F x.
Proof.
rewrite /index_enum.
rewrite -[LHS](big_map (ssval (s := s)) xpredT (fun x : T => F x)).
apply eq_big_perm; apply uniq_perm_eq.
- rewrite map_inj_uniq; last exact: val_inj.
  by rewrite -enumT; exact: enum_uniq.
- exact: undup_uniq.
- move=> x; rewrite mem_undup; apply/mapP/idP => [/= [y _ ->] | Hx].
  + by case: y => y /= Hy.
  + by exists (SeqSub Hx); rewrite // -enumT mem_enum.
Qed.

End SeqSub.

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

From mathcomp Require Import ssralg ssrint rat ssrnum.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Lemma iter_plus1 n : (iter n (+%R (1 : rat)) 0 = n%:~R)%R.
Proof.
  elim: n => [//= | n IHn] /=.
  by rewrite -add1n PoszD IHn mulrzDl.
Qed.
