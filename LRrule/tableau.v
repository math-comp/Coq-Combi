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
Require Import path.
Require Import tools partition ordtype.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope N.

Section Rows.

  Variable T : ordType.
  Variable Z : T.

  Implicit Type l : T.
  Implicit Type r : seq T.

  Notation is_row r := (sorted (@leqX_op T) r).

  Lemma is_row1P r :
    reflect
      (forall (i : nat), i.+1 < (size r) -> (nth Z r i <= nth Z r i.+1)%Ord)
      (is_row r).
  Proof. case: r => [| r0 r] /=; first by apply/(iffP idP). by apply/pathP. Qed.

  Lemma non_decr_equiv r :
    (forall (i j : nat), i <= j < (size r) -> (nth Z r i <= nth Z r j)%Ord)
    <->
    (forall (i : nat), i.+1 < (size r) -> (nth Z r i <= nth Z r i.+1)%Ord).
  Proof.
    split => H.
    - move=> i Hi.
      have : i <= i.+1 < size r by rewrite Hi andbT.
      by apply: H.
    - move=> i j; move Hdiff : (j - i) => diff.
      elim: diff i j Hdiff => [| diff IHdiff] i j /=.
      + move/eqP; rewrite -/(leq j i) => H1 /andP [] H2 Hj.
        have -> : i = j by apply/eqP; rewrite eqn_leq H1 H2.
        by [].
      + move=> Hdiff => /andP [] _ Hj.
        have Hiltj : i < j by rewrite -subn_gt0 Hdiff.
        apply: (leqX_trans (n := nth Z r i.+1)).
        * apply: H; by apply: (leq_ltn_trans Hiltj).
        * apply: IHdiff => //=; first by rewrite subnS Hdiff.
          by rewrite Hiltj Hj.
  Qed.

  Lemma is_rowP r :
    reflect
      (forall (i j : nat), i <= j < (size r) -> (nth Z r i <= nth Z r j)%Ord)
      (is_row r).
  Proof. apply/(iffP idP); by rewrite non_decr_equiv => /is_row1P. Qed.

  Lemma is_row_cons l r : is_row (cons l r) -> (l <= head l r)%Ord /\ is_row r.
  Proof. case: r => [//=| r0 r]; by move => /andP [] /= ->. Qed.

  Lemma is_row_consK l r : is_row (cons l r) -> is_row r.
  Proof. by case: r => [//=| r0 r] => /andP []. Qed.

  Lemma is_row_rconsK l r : is_row (rcons r l) -> is_row r.
  Proof. case: r => [//=| r0 r] /=; by rewrite rcons_path => /andP []. Qed.

  Lemma is_row_last l r : is_row (rcons r l) -> (last l r <= l)%Ord.
  Proof. case: r => [//=| r0 r] /=; by rewrite rcons_path => /andP []. Qed.

  Lemma is_row_take r n : is_row r -> is_row (take n r).
  Proof.
    elim: r n => [//= | r0 r IHr] [//=| n] /= H.
    case: r r0 H IHr => [//=| r1 r] r0 /= /andP [] H Hp IHr.
    have:= IHr n Hp. case: n => [//=|n] /= ->; by rewrite H.
  Qed.

  Lemma is_row_drop r n : is_row r -> is_row (drop n r).
  Proof.
    elim: n r => [//= | n IHn ]; first by case.
    case => [//= | r0 r /=] H; apply IHn => {IHn}.
    by case: r H => [//=|r1 r] /andP [].
  Qed.

  Lemma is_row_rcons l r : is_row r -> (last l r <= l)%Ord -> is_row (rcons r l).
  Proof. case: r => [//=| r0 r] /=; by rewrite rcons_path => -> ->. Qed.

  Lemma head_leq_last_row l r : is_row (l :: r) -> (l <= last l r)%Ord.
  Proof.
    elim: r l => [//=| t0 r IHr] l /= /andP [] Hl.
    move/IHr {IHr}; by apply: (leqX_trans Hl).
  Qed.

  Lemma row_lt_by_pos r p q :
    is_row r -> p < size r -> q < size r -> (nth Z r p < nth Z r q)%Ord -> p < q.
  Proof.
    move/is_rowP => Hrow Hp Hq Hlt.
    have H : q <= p -> (nth Z r q <= nth Z r p)%Ord.
      by move=> H; apply Hrow; rewrite H Hp.
    by have:= contra H; rewrite -ltnXNgeqX ltnNge; apply.
  Qed.

End Rows.

Notation is_row r := (sorted (@leqX_op _) r).

Section Dominate.

  Variable T : ordType.
  Notation Z := (inhabitant T).

  Implicit Type l : T.
  Implicit Type r u v : seq T.

Lemma is_row_set_nth l r pos :
  is_row r -> (l < nth l r pos)%Ord ->
  (forall n : nat, (l < nth l r n)%Ord -> pos <= n) -> is_row (set_nth l r pos l).
Proof.
  move=> /is_row1P Hrow Hl Hmin. apply/(is_row1P l) => i.
  rewrite (lock (i.+1)) !nth_set_nth /=; unlock.
  case: (ltnP pos (size r)) Hl => [Hpos Hl |HH]; last by rewrite (nth_default l HH) ltnXnn.
  rewrite size_set_nth maxnC /maxn; have:= Hpos; rewrite leqNgt; move/negbTE => -> Hi1lt.
  case eqP => Hipos; case eqP => Hi1pos.
  - by apply: leqXnn.
  - apply: ltnXW; apply: (ltnX_leqX_trans Hl); rewrite -Hipos; by apply: Hrow.
  - move: {Hmin} (contra (Hmin i)); rewrite -leqXNgtnX -ltnNge; apply.
    by rewrite Hi1pos leqnn.
  - by apply: Hrow.
Qed.

  Definition dominate u v :=
    ((size u) <= (size v)) && (all (fun i => (nth Z u i > nth Z v i)%Ord) (iota 0 (size u))).

  Lemma dominateP u v :
    reflect ((size u) <= (size v) /\ forall i, i < size u -> (nth Z u i > nth Z v i)%Ord)
            (dominate u v).
  Proof.
    rewrite /dominate /mkseq ; apply/(iffP idP).
    - move=> /andP [] Hsz /allP Hall; split; first by exact Hsz.
      move=> i Hi; apply: Hall; by rewrite mem_iota add0n.
    - move=> [] -> /= H; apply/allP => i; rewrite mem_iota add0n; by apply: H.
  Qed.

  Lemma dominate_nil u : dominate [::] u.
  Proof. apply/dominateP => /=; by split. Qed.

  Lemma dominate_trans r0 r1 r2 :
    dominate r0 r1 -> dominate r1 r2 -> dominate r0 r2.
  Proof.
    move=> /dominateP [] Hsz0 Hdom0 /dominateP [] Hsz1 Hdom1.
    apply/dominateP; split; first by apply (leq_trans Hsz0 Hsz1).
    move => i Hi.
    apply (ltnX_trans (Hdom1 i (leq_trans Hi Hsz0))).
    by apply Hdom0.
  Qed.

  Lemma dominate_rcons v u l : dominate u v -> dominate u (rcons v l).
  Proof.
    move /dominateP => [] Hsz Hlt.
    apply/dominateP; split => [|i Hi]; first by rewrite size_rcons; apply: leqW.
    have H := Hlt _ Hi; rewrite nth_rcons.
    case (ltnP i (size v)) => Hcomp //= {H}.
    move: {Hsz Hlt Hcomp} (leq_trans Hsz Hcomp) => Hs.
    have:= leq_ltn_trans Hs Hi; by rewrite ltnn.
  Qed.

  Lemma dominate_rconsK u v l :
    size u <= size v -> dominate u (rcons v l) -> dominate u v.
  Proof.
    move=> Hsz /dominateP [] _ Hlt.
    apply/dominateP; split => [|i Hi]; first exact Hsz.
    have Hiv := leq_trans Hi Hsz.
    by have:= Hlt _ Hi; rewrite nth_rcons Hiv.
  Qed.

  Lemma dominate_head u v : u != [::] -> dominate u v -> (head Z v < head Z u)%Ord.
  Proof.
    move=> Hu /dominateP []; case: u Hu => [//=|u0 u _]; case: v => [|v0 v _] /=.
    - by rewrite ltn0.
    - move=> Hdom; by apply: (Hdom 0 (ltn0Sn _)).
  Qed.

  Lemma dominate_tl a u b v :
    dominate (a :: u) (b :: v) -> dominate u v.
  Proof.
    move=> /dominateP [] /=; rewrite ltnS => Hsize Hdom.
    apply/dominateP; split; first exact Hsize.
    move=> i Hi; by apply (Hdom i.+1 Hi).
  Qed.

End Dominate.


Section Tableau.

  Variable T : ordType.
  Notation Z := (inhabitant T).

  Implicit Type l : T.
  Implicit Type r w : seq T.
  Implicit Type t : seq (seq T).

  Fixpoint is_tableau t :=
    if t is t0 :: t'
    then [&& (t0 != [::]), is_row t0, dominate (head [::] t') t0 & is_tableau t']
    else true.

  Definition to_word t := flatten (rev t).

  Lemma to_word_cons r t : to_word (r :: t) = to_word t ++ r.
  Proof. by rewrite /to_word rev_cons flatten_rcons. Qed.
  Lemma to_word_rcons r t : to_word (rcons t r) = r ++ to_word t.
  Proof. by rewrite /to_word rev_rcons /=. Qed.

  (* Shape is defined in seq.v *)
  (* Definition shape t := map size t. *)

  Lemma tableau_is_row r t : is_tableau (r :: t) -> is_row r.
  Proof. by move=> /= /and4P []. Qed.

  Lemma  is_tableau_rconsK t (tn : seq T) :
    is_tableau (rcons t tn) -> is_tableau t.
  Proof.
    elim: t => [//= | t0 t IHt] /= /and4P [] -> -> Hdom /IHt -> /= {IHt}.
    case: t Hdom => [//=| t1 t]; by rewrite rcons_cons /= => ->.
  Qed.

  Lemma is_part_sht t : is_tableau t -> is_part (shape t).
  Proof.
    elim: t => [//= | t0 t IHt] /= /and4P [] Ht0 _ /dominateP [] Hdom _ Htab.
    rewrite (IHt Htab) andbT {IHt Htab} /shape.
    case: t Hdom => //=; by case: t0 Ht0.
  Qed.

Lemma filter_gtnX_row r n :
  is_row r -> filter (gtnX n) r = take (count (gtnX n) r) r.
Proof.
  elim: r => [//= | r0 r IHr] Hrow /=.
  case: (ltnXP r0 n) => Hr0.
  - by rewrite add1n (IHr (is_row_consK Hrow)).
  - rewrite add0n; have Hcount : count (gtnX n) r = 0.
      elim: r r0 Hr0 Hrow {IHr} => [//= | r1 r /= IHr] r0 Hr0 /andP [] Hr0r1 Hpath.
      have Hr1 := leqX_trans Hr0 Hr0r1.
      by rewrite ltnXNgeqX Hr1 (IHr r1 Hr1 Hpath).
    rewrite Hcount.
    by apply/nilP; rewrite /nilp size_filter Hcount.
Qed.

Lemma count_gtnX_dominate r1 r0 n :
  dominate r1 r0 -> (count (gtnX n) r1) <= (count (gtnX n) r0).
Proof.
  move=> /dominateP [] Hsz Hdom.
  rewrite -[r0](mkseq_nth Z) -[r1](mkseq_nth Z) /mkseq !count_map.
  rewrite -(subnKC Hsz).
  rewrite iota_add count_cat.
  set s0 := (X in X + _).
  apply (@leq_trans s0); last by apply leq_addr.
  rewrite /s0 {s0} -!size_filter.
  set f1 := (X in filter X ); set f0 := (X in _ <= size (filter X _)).
  rewrite (eq_in_filter (a1 := f1) (a2 := predI f1 (gtn (size r1)))); first last.
    move=> i; rewrite mem_iota /= add0n => ->; by rewrite andbT.
  rewrite (eq_in_filter (a1 := f0) (a2 := predI f0 (gtn (size r1)))); first last.
    move=> i; rewrite mem_iota /= add0n => ->; by rewrite andbT.
  rewrite !size_filter; apply sub_count => i /=.
  rewrite /f1 /f0 {f1 f0} /= => /andP [] Hn Hi.
  rewrite Hi andbT.
  by apply (ltnX_trans (Hdom i Hi) Hn).
Qed.

Lemma filter_gtnX_dominate r1 r0 n :
    is_row r0 -> is_row r1 -> dominate r1 r0 ->
    dominate (filter (gtnX n) r1) (filter (gtnX n) r0).
Proof.
  move=> Hrow0 Hrow1 Hdom.
  have Hsize := count_gtnX_dominate n Hdom.
  move: Hdom => /dominateP [] Hsz Hdom.
  apply/dominateP; rewrite !size_filter.
  split; first exact Hsize.
  move=> i Hi.
  rewrite (filter_gtnX_row _ Hrow0) (filter_gtnX_row _ Hrow1) !nth_take.
  - apply Hdom; apply (leq_trans Hi); by apply count_size.
  - exact Hi.
  - by apply (leq_trans Hi).
Qed.

Definition filter_gtnX_tab n :=
  [fun t : (seq (seq T)) => filter (fun r => r != [::])
                                   [seq [seq x <- i | gtnX n x] | i <- t]].

Lemma to_word_filter_nnil t : to_word (filter (fun r => r != [::]) t) = to_word t.
Proof.
  elim: t => [//= | t0 t IHt] /=.
  rewrite to_word_cons -IHt.
  case: (altP (t0 =P [::])) => [-> | _] /=; first by rewrite cats0.
  by rewrite to_word_cons.
Qed.

Lemma filter_to_word t p : filter p (to_word t) = to_word (map (filter p) t).
Proof.
    elim: t => [//= | t0 t IHt] /=.
    by rewrite !to_word_cons -IHt filter_cat.
Qed.

Lemma head_filter_gtnX_tab n t :
  is_tableau t ->
  head [::] (filter_gtnX_tab n t) = [seq x <- head [::] t | (x < n)%Ord].
Proof.
  elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil0 Hrow0 Hdom Htab.
  case: (altP ([seq x <- t0 | (x < n)%Ord] =P [::])) => Ht0 //=.
  rewrite (IHt Htab) Ht0 {IHt}.
  case: t Hdom Htab => [//= | t1 t] /= Hdom /and3P [] Hnnil1 Hrow1 _.
  have /dominateP := filter_gtnX_dominate n Hrow0 Hrow1 Hdom => [] [].
  by rewrite Ht0 /= leqn0 => /nilP ->.
Qed.

Lemma is_tableau_filter_gtnX t n : is_tableau t -> is_tableau (filter_gtnX_tab n t).
Proof.
  elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil Hrow Hdom Htab.
  case: (altP ([seq x <- t0 | (x < n)%Ord] =P [::])) => Ht0 /=; first by apply IHt.
  rewrite Ht0 /=; apply/and3P; split; last by apply IHt.
  - apply sorted_filter; last exact Hrow.
    move=> a b c; by apply leqX_trans.
  - rewrite (head_filter_gtnX_tab _ Htab).
    apply filter_gtnX_dominate => //=.
    move: Htab; by case t => [//= | t1 t'] /= /and3P [].
Qed.


Definition size_tab t := sumn (shape t).

Lemma tab0 t : is_tableau t -> size_tab t = 0 -> t = [::].
Proof.
  move/is_part_sht; rewrite /size_tab => /part0 H/H {H}.
  rewrite /shape; by case t.
Qed.

Lemma size_to_word t : size_tab t = size (to_word t).
Proof.
  rewrite /size_tab; elim: t => [//= | t0 t IHt] /=.
  by rewrite to_word_cons size_cat IHt addnC.
Qed.

End Tableau.
