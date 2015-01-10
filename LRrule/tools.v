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

Set Implicit Arguments.
Unset Strict Implicit.

Section RCons.

  Variable (T : eqType).
  Implicit Type s w : seq T.
  Implicit Type a b : T.

  Lemma flatten_rcons s t : flatten (rcons t s) = flatten t ++ s.
  Proof.
    elim: t => [//= | t0 t IHt /=]; first by rewrite cats0.
    by rewrite IHt catA.
  Qed.

  Lemma head_any s a b : s != [::] -> head a s = head b s.
  Proof. by elim: s. Qed.

  Lemma nth_any s a b i : i < size s -> nth a s i = nth b s i.
  Proof. elim: s i => //= s0 s IHs [//=|i] Hsize /=. by apply: IHs. Qed.

  Lemma rcons_set_nth a s l : set_nth a s (size s) l = rcons s l.
  Proof. elim: s => [//=| l0 s IHs]. by rewrite rcons_cons -IHs /=. Qed.

  Lemma set_nth_non_nil d s n y : set_nth d s n y != [::].
  Proof. elim: s => [|s0 s]; by case n. Qed.

  Lemma set_nth_rcons x0 s x n y :
    set_nth x0 (rcons s x) n y =
    if n < size s then rcons (set_nth x0 s n y) x
    else if n == size s then rcons s y else (rcons s x) ++ ncons (n - size s).-1 x0 [:: y].
  Proof.
    elim: s n => [//= | s0 s IHs] n.
    + case eqP => [-> //= |]; by case: n => [| []].
    + rewrite rcons_cons /=; case: n => [//= | n] /=.
      have {IHs} := (IHs n). rewrite eqSS -[n.+1 < (size s).+1]/(n < (size s)).
      by case (ltngtP n (size s)) => _ <-.
  Qed.

  Lemma rconsK a u v : rcons u a = rcons v a -> u = v.
  Proof.
    elim: u v => [| u0 u IHu]; case=> [|v0 v] //= [].
    + move=> _; by case v.
    + move=> _; by case u.
    + by move=> -> /IHu ->.
  Qed.

  Lemma nth_set_nth_expand a b l i c j :
    (size l <= j < i) ->  nth a (set_nth b l i c) j = b.
  Proof.
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
  Proof.
    case eqP => [<- | /eqP Hneq].
    - have Hj : j < size (set_nth b l j c) by rewrite size_set_nth; apply: leq_maxl.
      by rewrite (nth_any a b Hj) nth_set_nth /= eq_refl.
    - case (ltnP j (size l)) => Hjsz.
      + have Hj : j < size (set_nth b l i c)
          by rewrite size_set_nth; apply: (leq_trans Hjsz); apply: leq_maxr.
        by rewrite (nth_any a b Hj) nth_set_nth /= (negbTE Hneq) (nth_any a b Hjsz).
      + case (leqP j i) => Hij.
        * apply: nth_set_nth_expand; by rewrite Hjsz /= ltn_neqAle Hneq Hij.
        * rewrite nth_default; first by [].
          rewrite size_set_nth /maxn; by case (ltnP i.+1 (size l)).
  Qed.

  Lemma cons_in_map_cons a b s w :
    forall l : seq (seq T), a :: s \in [seq b :: s1 | s1 <- l] -> a == b.
  Proof.
    elim=> [//=| l0 l H]; rewrite map_cons in_cons; move/orP => []; last by exact H.
    by move=> /eqP [] ->.
  Qed.

  Lemma count_flatten (s : seq (seq T)) P :
    count P (flatten s) = sumn [seq count P x | x <- s].
  Proof. elim: s => [//= | s0 s IHs /=]. by rewrite count_cat IHs. Qed.

  Lemma rcons_nilF s l : ((rcons s l) == [::]) = false.
  Proof. case eqP=>//= H; have:= eq_refl (size (rcons s l)). by rewrite {2}H size_rcons. Qed.

  Lemma count_mem_rcons w l i : count_mem i (rcons w l) = count_mem i w + (l == i).
  Proof. by rewrite -count_rev rev_rcons /= count_rev addnC. Qed.

  Lemma sumn_count s P :
    sumn [seq nat_of_bool (P i) | i <- s] = count P s.
  Proof. by elim: s => //= s0 s /= ->. Qed.

End RCons.

Lemma map_flatten (T1 T2 : eqType) (f : T1 -> T2) s :
  map f (flatten s) = flatten (map (map f) s).
Proof. elim: s => [//= | s0 s /= <-]; by apply map_cat. Qed.

Lemma sumn_flatten s :
  sumn (flatten s) = sumn (map sumn s).
Proof. elim: s => [//= | s0 s /= <-]; by apply sumn_cat. Qed.

Lemma sumn_rev s : sumn (rev s) = sumn s.
Proof.
  elim: s => [//= | s0 s /= <-].
  by rewrite rev_cons -cats1 sumn_cat /= addn0 addnC.
Qed.

Lemma shape_rev T (s : seq (seq T)) : shape (rev s) = rev (shape s).
Proof. rewrite /shape; elim: s => [//= | s0 s IHs] /=; by rewrite map_rev. Qed.

Lemma sumn_iota a b x :
  a <= x < a + b -> sumn [seq ((i == x) : nat) | i <- iota a b] = 1.
Proof.
  elim: b a => [/=| b IHb] a.
    rewrite addn0 => /andP [] /leq_ltn_trans H/H{H}.
    by rewrite ltnn.
  have:= IHb a.+1 => /= {IHb} IHb.
  case (ltnP a x) => H1 /andP [] H2 H3.
  + rewrite IHb; first by rewrite (ltn_eqF H1).
    by rewrite H1 addSnnS.
  + rewrite eqn_leq H1 H2 /= {H2 H3 IHb}.
    apply/eqP; rewrite eqSS; apply/eqP.
    elim: b a H1 => [//= | b IHb] a Ha /=.
    rewrite IHb; first by rewrite gtn_eqF; last by rewrite ltnS.
    by rewrite leqW.
Qed.

Lemma incr_nth_inj sh : injective (incr_nth sh).
Proof.
  move=> i j Hsh.
  case (altP (i =P j)) => [//= | /negbTE Hdiff].
  have:= eq_refl (nth 0 (incr_nth sh i) j).
  by rewrite {2}Hsh !nth_incr_nth eq_refl Hdiff eqn_add2r.
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


Lemma filter_perm_eq (T : eqType) (u v : seq T) P :
  perm_eq u v -> perm_eq (filter P u) (filter P v).
Proof.
  move=> /perm_eqP Hcount.
  apply/perm_eqP => Q; rewrite !count_filter.
  by apply Hcount.
Qed.
