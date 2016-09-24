(** * Combi.Combi.tableau : Young Tableaux *)
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
(** * Young Tableaux over an [ordtype]

We define the notion of (semistandard) Young tableau over an [ordType]
denoted [T].

- [is_row r] == r is sorted
- [dominate u v] == u dominate v, that is v is longer than u and
            the i-th letter of u is strictly larger than the i-th letter of v.
            this is a order.
- [is_tableau t] == t of type [(seq (seq T))] is a tableau that is a sequence
                    of non empty rows which is sorted for the dominate order.
- [get_tab t r c] == the element of t of coordinate (r c), or [inhabitant T]
                    if (r, c) is not is the tableau
- [to_word t] == the row reading of the tableau t
- [size_tab t] == the size (number of boxes) of t
- [filter_gtnX_tab n t] == the sub-tableau of t formed by the element smaller
                   than [n].

- [tabsh_reading sh w] == w is the row reading of a tableau of shape sh
*****)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import path tuple.
Require Import tools partition ordtype sorted.

Set Implicit Arguments.
Unset Strict Implicit.

Import OrdNotations.

Open Scope N.

(** ** Specialization of sorted Lemmas *)
Section Rows.

Variable T : inhOrdType.

Implicit Type l : T.
Implicit Type r : seq T.

Notation is_row r := (sorted leqX_op r).

Definition is_row1P Z r := sorted1P Z leqX_op r.
Definition is_rowP Z r := sortedP Z (@leqX_trans T) (@leqXnn T) r.
Definition is_row_cons := sorted_cons (@leqXnn T).
Definition is_row_consK := sorted_consK (R := @leqX_op T).
Definition is_row_rcons := sorted_rcons (R := @leqX_op T).
Definition is_row_rconsK := sorted_rconsK (R := @leqX_op T).
Definition is_row_last := sorted_last (@leqXnn T).
Definition is_row_take := sorted_take (R := @leqX_op T).
Definition is_row_drop := sorted_drop (R := @leqX_op T).
Definition is_row_catL := sorted_catL (R := @leqX_op T).
Definition is_row_catR := sorted_catR (R := @leqX_op T).
Definition head_leq_last_row := head_leq_last_sorted (@leqX_trans T) (@leqXnn T).
Lemma row_lt_by_pos Z r p q:
  is_row r -> p < size r -> q < size r -> nth Z r p <A nth Z r q -> p < q.
Proof using.
rewrite /ltnX_op.
by apply: (sorted_lt_by_pos (@leqX_trans T) (@leqXnn T) (@anti_leqX T)). 
Qed.

End Rows.

Notation is_row r := (sorted leqX_op r).

(** ** Dominance order for rows *)
Section Dominate.

Variable T : inhOrdType.
Notation Z := (inhabitant T).

Implicit Type l : T.
Implicit Type r u v : seq T.

Lemma is_row_set_nth l r pos :
  is_row r -> l <A nth l r pos ->
  (forall n : nat, l <A nth l r n -> pos <= n) -> is_row (set_nth l r pos l).
Proof using.
move=> /is_row1P Hrow Hl Hmin. apply/(is_row1P l) => i.
rewrite (lock (i.+1)) !nth_set_nth /=; unlock.
case: (ltnP pos (size r)) Hl => [Hpos Hl |HH]; first last.
  by rewrite (nth_default l HH) ltnXnn.
rewrite size_set_nth maxnC /maxn.
move: Hpos; rewrite leqNgt; move/negbTE => -> Hi1lt.
case eqP => Hipos; case eqP => Hi1pos.
- exact: leqXnn.
- by apply: ltnXW; apply: (ltnX_leqX_trans Hl); rewrite -Hipos; apply: Hrow.
- move: {Hmin} (contra (Hmin i)); rewrite -leqXNgtnX -ltnNge; apply.
  by rewrite Hi1pos leqnn.
- exact: Hrow.
Qed.

Definition dominate u v :=
  ((size u) <= (size v)) &&
   (all (fun i => nth Z u i >A nth Z v i) (iota 0 (size u))).

Lemma dominateP u v :
  reflect ((size u) <= (size v) /\ forall i, i < size u -> nth Z u i >A nth Z v i)
          (dominate u v).
Proof using.
rewrite /dominate /mkseq ; apply/(iffP idP).
- move=> /andP [] Hsz /allP Hall; split; first exact Hsz.
  by move=> i Hi; apply: Hall; rewrite mem_iota add0n.
- by move=> [] -> /= H; apply/allP => i; rewrite mem_iota add0n; apply: H.
Qed.

Lemma dominate_nil u : dominate [::] u.
Proof using. by apply/dominateP. Qed.

Lemma dominate_trans r0 r1 r2 :
  dominate r0 r1 -> dominate r1 r2 -> dominate r0 r2.
Proof using.
move=> /dominateP [] Hsz0 Hdom0 /dominateP [] Hsz1 Hdom1.
apply/dominateP; split; first exact: (leq_trans Hsz0 Hsz1).
move => i Hi.
apply (ltnX_trans (Hdom1 i (leq_trans Hi Hsz0))).
exact: Hdom0.
Qed.

Lemma dominate_rcons v u l : dominate u v -> dominate u (rcons v l).
Proof using.
move/dominateP => [] Hsz Hlt.
apply/dominateP; split => [|i Hi]; first by rewrite size_rcons; apply: leqW.
move/(_ _ Hi) : Hlt; rewrite nth_rcons.
case: (ltnP i (size v)) => //= /(leq_trans Hsz)/leq_ltn_trans/(_ Hi).
by rewrite ltnn.
Qed.

Lemma dominate_rconsK u v l :
  size u <= size v -> dominate u (rcons v l) -> dominate u v.
Proof using.
move=> Hsz /dominateP [] _ Hlt.
apply/dominateP; split => [|i Hi]; first exact Hsz.
by move/(_ _ Hi) : Hlt; rewrite nth_rcons (leq_trans Hi Hsz).
Qed.

Lemma dominate_head u v : u != [::] -> dominate u v -> head Z v <A head Z u.
Proof using.
move=> Hu /dominateP []; case: u Hu => [//=|u0 u _]; case: v => [|v0 v _] /=.
- by rewrite ltn0.
- by move=> Hdom; apply: (Hdom 0 (ltn0Sn _)).
Qed.

Lemma dominate_tl a u b v :
  dominate (a :: u) (b :: v) -> dominate u v.
Proof using.
move=> /dominateP [] /=; rewrite ltnS => Hsize Hdom.
apply/dominateP; split; first exact Hsize.
  by move=> i Hi; apply: (Hdom i.+1 Hi).
Qed.

End Dominate.


(** * Tableaux : definition and basic properties *)
Section Tableau.

Variable T : inhOrdType.
Notation Z := (inhabitant T).

Implicit Type l : T.
Implicit Type r w : seq T.
Implicit Type t : seq (seq T).

Fixpoint is_tableau t :=
  if t is t0 :: t'
  then [&& (t0 != [::]), is_row t0, dominate (head [::] t') t0 & is_tableau t']
  else true.

Definition get_tab (t : seq (seq T)) (r c : nat) :=
  nth (inhabitant T) (nth [::] t r) c.

Definition to_word t := flatten (rev t).

(* Shape is defined in seq.v *)
(* Definition shape t := map size t. *)

Lemma is_tableauP t :
  reflect
    [/\ forall i, i < size t -> (nth [::] t i) != [::], (* forbid empty lines *)
        forall i, is_row (nth [::] t i) &
        forall i j, i < j -> dominate (nth [::] t j) (nth [::] t i)]
    (is_tableau t).
Proof using.
apply (iffP idP).
- elim: t => [_ | t0 t IHt] /=.
    split=> i //=; first by rewrite nth_default.
    by move=> j; rewrite !nth_default.
  move=> /and4P [] Ht0 Hrow0 Hdom0 /IHt {IHt} [] Hnnil Hrow Hdom.
  split; try by case.
  case=> [| i] [| j] //=.
  + case: j => [|j] _; first by rewrite nth0.
    apply: (dominate_trans _ Hdom0).
    by rewrite -nth0; apply: Hdom.
  + by rewrite ltnS; apply: Hdom.
- elim: t => [| t0 t IHt] //= [] Hnnil Hrow Hdom.
  apply/and4P; split.
  + exact: (Hnnil 0).
  + exact: (Hrow 0).
  + move: Hdom; case t => [| t1 tt] //= H.
    rewrite -/(nth [::] (t0 :: t1 :: tt) 0) -/(nth [::] (t0 :: t1 :: tt) 1).
    exact: H.
  + apply IHt; split => [i H | i | i j H].
    * exact: (Hnnil i.+1).
    * exact: (Hrow i.+1).
    * exact: (Hdom i.+1 j.+1).
Qed.

Lemma get_tab_default t (r c : nat) :
  ~~ is_in_shape (shape t) r c -> get_tab t r c = Z.
Proof using.
rewrite /is_in_shape /get_tab -leqNgt nth_shape => Hc.
exact: nth_default.
Qed.

Lemma to_word_cons r t : to_word (r :: t) = to_word t ++ r.
Proof using. by rewrite /to_word rev_cons flatten_rcons. Qed.
Lemma to_word_rcons r t : to_word (rcons t r) = r ++ to_word t.
Proof using. by rewrite /to_word rev_rcons /=. Qed.

Lemma mem_to_word t (r c : nat) :
  is_in_shape (shape t) r c -> (get_tab t r c) \in (to_word t).
Proof using.
rewrite /is_in_shape /get_tab.
elim: t r c => [//= | t0 t IHt] /= r c; first by rewrite nth_default.
rewrite to_word_cons mem_cat => H.
case: r H => [/mem_nth ->| r] /=; first by rewrite orbT.
by move/IHt ->.
Qed.

Lemma to_wordK t : rev (reshape (rev (shape t)) (to_word t)) = t.
Proof using. by rewrite -shape_rev /to_word flattenK revK. Qed.

Lemma tableau_is_row r t : is_tableau (r :: t) -> is_row r.
Proof using. by move=> /= /and4P []. Qed.

Lemma  is_tableau_rconsK t (tn : seq T) :
  is_tableau (rcons t tn) -> is_tableau t.
Proof using.
elim: t => [//= | t0 t IHt] /= /and4P [] -> -> Hdom /IHt -> /= {IHt}.
by case: t Hdom => [//=| t1 t]; rewrite rcons_cons /= => ->.
Qed.

Lemma is_tableau_catl t1 t2 :
  is_tableau (t1 ++ t2) -> is_tableau t1.
Proof.
elim: t1 => [//= | t t1 IHt1] /= /and4P [] -> -> /= Hdom /IHt1 {IHt1} ->.
by rewrite andbT; case: t1 Hdom => [//= | r1 t1].
Qed.

Lemma is_tableau_catr t1 t2 :
  is_tableau (t1 ++ t2) -> is_tableau t2.
Proof. by elim: t1 => [//= | r t1 IHt1] /= /and4P [] _ _ _. Qed.

Lemma is_part_sht t : is_tableau t -> is_part (shape t).
Proof using.
elim: t => [//= | t0 t IHt] /= /and4P [] Ht0 _ /dominateP [] Hdom _ Htab.
rewrite (IHt Htab) andbT {IHt Htab} /shape.
by case: t Hdom => //=; case: t0 Ht0.
Qed.

Lemma tab_eqP p q :
  is_tableau p -> is_tableau q ->
  reflect (forall i, nth [::] p i = nth [::] q i) (p == q).
Proof using.
move=> Hp Hq.
apply (iffP idP) => [/eqP -> //| H].
have Hnth t i : nth 0 (shape t) i = size (nth [::] t i).
  case: (ltnP i (size t)) => Hi.
  - by rewrite /shape (nth_map [::] _ _ Hi).
  - by rewrite !nth_default // size_map.
have Hsz : size p = size q.
  rewrite -!(size_map size); congr (size _).
  apply/eqP/(part_eqP (is_part_sht Hp) (is_part_sht Hq)) => i.
  by rewrite !Hnth H.
by apply/eqP; apply (eq_from_nth (x0 := [::]) Hsz) => i _.
Qed.

Lemma is_tableau_sorted_dominate (t : seq (seq T)) :
  is_tableau t =
  [&& is_part (shape t),
   all (sorted leqX_op) t &
   sorted (fun x y => dominate y x) t].
Proof using.
apply/idP/idP; elim: t => [//= | t0 t IHt].
- move=> /=/and4P [] Hnnil Hrow0 Hdom /IHt /and3P [] Hpart Hall Hsort.
  rewrite Hpart Hrow0 Hall {Hpart Hrow0 Hall IHt} !andbT /=; apply/andP; split.
  + case: t Hdom {Hsort} => [_ | t1 t] /=; first by case: t0 Hnnil.
    by move => /dominateP [].
  + by case: t Hdom Hsort => [//=| t1 t]/= -> ->.
- move=>/and3P [] Hpart.
  have:= part_head_non0 Hpart.
  rewrite [head _ _]/= [all _ _]/= [is_tableau _]/=.
  move=> /nilP /eqP -> /andP [] -> Hall Hsort /=.
  apply/andP; split.
  + by case: t Hsort {Hpart Hall IHt} => [//= | t1 t] /= /andP [].
  + apply: IHt; rewrite (is_part_consK Hpart) Hall /=.
    exact: (sorted_consK Hsort).
Qed.

Lemma is_tableau_getP (t : seq (seq T)) :
  reflect
    [/\ is_part (shape t),
     (forall (r c : nat), is_in_shape (shape t) r c.+1 ->
                          get_tab t r c <=A get_tab t r c.+1) &
     (forall (r c : nat), is_in_shape (shape t) r.+1 c ->
                          get_tab t r c <A get_tab t r.+1 c)]
    (is_tableau t).
Proof using.
apply/(iffP idP).
- move=> Htab; split.
  + exact: is_part_sht.
  + rewrite /is_in_shape /get_tab => r c Hrc.
    move: Htab => /is_tableauP [] _ Hrow _.
    by apply: (is_row1P _ _ (Hrow r)); rewrite -nth_shape.
  + rewrite /is_in_shape /get_tab => r c Hrc.
    move: Htab => /is_tableauP [] _ _ Hdom.
    have := dominateP _ _ (Hdom _ _ (ltnSn r)) => [] [] _; apply.
    by rewrite -nth_shape.
- move=> [] Hpart Hrow Hcol.
  apply/is_tableauP; split.
  + move=> i Hi.
    have:= nth_part_non0 Hpart; rewrite size_map => H.
    have {H} := H _ Hi.
    apply contra => /eqP.
    by rewrite nth_shape => ->.
  + move=> r; apply/(is_row1P (inhabitant T)) => c.
    by rewrite -nth_shape => /Hrow; apply.
  + move=> i j Hij; case: (ltnP j (size t)) => Hjr.
    * have H : i < j < size t by rewrite Hij Hjr.
      have Htrans : transitive (fun x : seq T => (@dominate T)^~ x).
        by move=> a b c /= Hab Hca; apply: dominate_trans Hca Hab.
      move: i j H {Hij Hjr}; rewrite (incr_equiv [::] Htrans t) => i Hi.
      apply/dominateP; rewrite -!nth_shape.
      split; first by have:= is_partP _ Hpart => [] [] _; apply.
      by move=> j; rewrite -/(is_in_shape _ _ _) -!/(get_tab _ _ _) => /Hcol ->.
    * by rewrite (nth_default _ Hjr); apply: dominate_nil.
Qed.

Lemma filter_gtnX_row r n :
  is_row r -> filter (gtnX n) r = take (count (gtnX n) r) r.
Proof using.
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
Proof using.
move=> /dominateP [] Hsz Hdom.
rewrite -[r0](mkseq_nth Z) -[r1](mkseq_nth Z) /mkseq !count_map.
rewrite -(subnKC Hsz).
rewrite iota_add count_cat.
set s0 := (X in X + _).
apply (@leq_trans s0); last exact: leq_addr.
rewrite /s0 {s0} -!size_filter.
set f1 := (X in filter X ); set f0 := (X in _ <= size (filter X _)).
rewrite (eq_in_filter (a1 := f1) (a2 := predI f1 (gtn (size r1)))); first last.
  by move=> i; rewrite mem_iota /= add0n => ->; rewrite andbT.
rewrite (eq_in_filter (a1 := f0) (a2 := predI f0 (gtn (size r1)))); first last.
  by move=> i; rewrite mem_iota /= add0n => ->; rewrite andbT.
rewrite !size_filter; apply sub_count => i /=.
rewrite /f1 /f0 {f1 f0} /= => /andP [] Hn Hi.
rewrite Hi andbT.
exact: ltnX_trans (Hdom i Hi) Hn.
Qed.

Lemma filter_gtnX_dominate r1 r0 n :
  is_row r0 -> is_row r1 -> dominate r1 r0 ->
  dominate (filter (gtnX n) r1) (filter (gtnX n) r0).
Proof using.
move=> Hrow0 Hrow1 Hdom.
have Hsize := count_gtnX_dominate n Hdom.
move: Hdom => /dominateP [] Hsz Hdom.
apply/dominateP; rewrite !size_filter.
split; first exact Hsize.
move=> i Hi.
rewrite (filter_gtnX_row _ Hrow0) (filter_gtnX_row _ Hrow1) !nth_take.
- by apply Hdom; apply (leq_trans Hi); apply: count_size.
- exact: Hi.
- exact: (leq_trans Hi).
Qed.

Definition filter_gtnX_tab n :=
  [fun t : (seq (seq T)) => filter (fun r => r != [::])
                                   [seq [seq x <- i | gtnX n x] | i <- t]].

Lemma to_word_filter_nnil t : to_word (filter (fun r => r != [::]) t) = to_word t.
Proof using.
elim: t => [//= | t0 t IHt] /=.
rewrite to_word_cons -IHt.
case: (altP (t0 =P [::])) => [-> | _] /=; first by rewrite cats0.
by rewrite to_word_cons.
Qed.

Lemma filter_to_word t p : filter p (to_word t) = to_word (map (filter p) t).
Proof using.
elim: t => [//= | t0 t IHt] /=.
by rewrite !to_word_cons -IHt filter_cat.
Qed.

Lemma head_filter_gtnX_tab n t :
  is_tableau t ->
  head [::] (filter_gtnX_tab n t) = [seq x <- head [::] t | x <A n].
Proof using.
elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil0 Hrow0 Hdom Htab.
case: (altP ([seq x <- t0 | x <A n] =P [::])) => Ht0 //=.
rewrite (IHt Htab) Ht0 {IHt}.
case: t Hdom Htab => [//= | t1 t] /= Hdom /and3P [] Hnnil1 Hrow1 _.
have /dominateP := filter_gtnX_dominate n Hrow0 Hrow1 Hdom => [] [].
by rewrite Ht0 /= leqn0 => /nilP ->.
Qed.

Lemma is_tableau_filter_gtnX t n :
  is_tableau t -> is_tableau (filter_gtnX_tab n t).
Proof using.
elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil Hrow Hdom Htab.
case: (altP ([seq x <- t0 | x <A n] =P [::])) => Ht0 /=; first exact: IHt.
rewrite Ht0 /=; apply/and3P; split; last exact: IHt.
- apply sorted_filter; last exact Hrow.
  by move=> a b c; apply: leqX_trans.
- rewrite (head_filter_gtnX_tab _ Htab).
  apply filter_gtnX_dominate => //=.
  by move: Htab; case t => [//= | t1 t'] /= /and3P [].
Qed.

Definition size_tab t := sumn (shape t).

Lemma tab0 t : is_tableau t -> size_tab t = 0 -> t = [::].
Proof using.
move/is_part_sht; rewrite /size_tab => /part0 H/H{H}.
by rewrite /shape; case t.
Qed.

Lemma size_to_word t : size (to_word t) = size_tab t.
Proof using.
rewrite /size_tab; elim: t => [//= | t0 t IHt] /=.
by rewrite to_word_cons size_cat IHt addnC.
Qed.

End Tableau.

Prenex Implicits is_tableau to_word size_tab.

Section TableauReading.

Variable A : inhOrdType.

Definition tabsh_reading (sh : seq nat) (w : seq A) :=
  (size w == sumn sh) && (is_tableau (rev (reshape (rev sh) w))).

Lemma tabsh_readingP (sh : seq nat) (w : seq A) :
  reflect
    (exists tab, [/\ is_tableau tab, shape tab = sh & to_word tab = w])
    (tabsh_reading sh w).
Proof using.
apply (iffP idP).
- move=> /andP [] /eqP Hsz Htab.
  exists (rev (reshape (rev sh) w)); split => //.
  + rewrite shape_rev -{2}(revK sh); congr (rev _).
    by apply: reshapeKl; rewrite sumn_rev Hsz.
  + by rewrite /to_word revK; apply: reshapeKr; rewrite sumn_rev Hsz.
- move=> [] tab [] Htab Hsh Hw; apply/andP; split.
  + by rewrite -Hw size_to_word /size_tab Hsh.
  + rewrite -Hw /to_word -Hsh.
    by rewrite /shape -map_rev -/(shape _) flattenK revK.
Qed.

End TableauReading.


Section FinType.

Variable n : nat.
(* Should be Variable A : finOrdType *)

Section TabSZ.

Variable sz : nat.

Definition is_tab_of_size :=
  [pred t | (is_tableau (T := [inhOrdType of 'I_n.+1]) t) && (size_tab t == sz) ].

Structure tabsz : predArgType :=
  TabSz {tabszval :> seq (seq 'I_n.+1); _ : is_tab_of_size tabszval}.
Canonical tabsz_subType := Eval hnf in [subType for tabszval].
Definition tabsz_eqMixin := Eval hnf in [eqMixin of tabsz by <:].
Canonical tabsz_eqType := Eval hnf in EqType tabsz tabsz_eqMixin.
Definition tabsz_choiceMixin := Eval hnf in [choiceMixin of tabsz by <:].
Canonical tabsz_choiceType := Eval hnf in ChoiceType tabsz tabsz_choiceMixin.
Definition tabsz_countMixin := Eval hnf in [countMixin of tabsz by <:].
Canonical tabsz_countType := Eval hnf in CountType tabsz tabsz_countMixin.
Canonical tabsz_subCountType := Eval hnf in [subCountType of tabsz].

Implicit Type (t : tabsz).

Lemma tabszP t : is_tableau t.
Proof using. by case: t => t /= /andP []. Qed.

Lemma size_tabsz t : size_tab t = sz.
Proof using. by case: t => t /= /andP [] _ /eqP. Qed.

Lemma shape_tabsz_subproof t : is_part_of_n sz (shape t).
Proof.
rewrite /= -(size_tabsz t) /size_tab eq_refl /=.
exact: (is_part_sht (tabszP t)).
Qed.
Definition shape_tabsz t := IntPartN (shape_tabsz_subproof t).

Lemma size_to_word_tabsz t : size (to_word t) == sz.
Proof. by rewrite size_to_word size_tabsz. Qed.
Definition to_word_tuple_tabsz t := Tuple (size_to_word_tabsz t).

Definition tabszpair t := (shape_tabsz t, to_word_tuple_tabsz t).
Lemma tabszpairK :
  pcancel tabszpair (fun p => insub (rev (reshape (rev p.1) p.2))).
Proof.
rewrite /tabszpair => [[t Ht]] /=.
by rewrite to_wordK (insubT _ Ht) /=.
Qed.

Definition tabsz_finMixin := Eval hnf in PcanFinMixin tabszpairK.
Canonical tabsz_finType := Eval hnf in FinType tabsz tabsz_finMixin.

Lemma rowtabsz_subproof :
  is_tab_of_size (if sz == 0 then [::] else [:: nseq sz ord0]).
Proof.
rewrite /=; case: (altP (sz =P 0)) => [-> | Hsz]//=.
rewrite andbT /size_tab /shape /= size_nseq addn0 eq_refl andbT.
apply/andP; split.
- move: Hsz; apply contra => /eqP/nilP.
  by rewrite /nilp size_nseq.
- case: sz Hsz => //= s _ /=; by elim: s.
Qed.
Definition rowtabsz := TabSz rowtabsz_subproof.

End TabSZ.

Variable d : nat.
Variable sh : intpartn d.

Definition is_tab_of_shape sh :=
  [pred t | (is_tableau (T := [inhOrdType of 'I_n.+1]) t) && (shape t == sh) ].

Structure tabsh : predArgType :=
  TabSh {tabshval :> seq (seq 'I_n.+1); _ : is_tab_of_shape sh tabshval}.
Canonical tabsh_subType := Eval hnf in [subType for tabshval].
Definition tabsh_eqMixin := Eval hnf in [eqMixin of tabsh by <:].
Canonical tabsh_eqType := Eval hnf in EqType tabsh tabsh_eqMixin.
Definition tabsh_choiceMixin := Eval hnf in [choiceMixin of tabsh by <:].
Canonical tabsh_choiceType := Eval hnf in ChoiceType tabsh tabsh_choiceMixin.
Definition tabsh_countMixin := Eval hnf in [countMixin of tabsh by <:].
Canonical tabsh_countType := Eval hnf in CountType tabsh tabsh_countMixin.
Canonical tabsh_subCountType := Eval hnf in [subCountType of tabsh].

Implicit Type (t : tabsh).

Lemma tabshP t : is_tableau t.
Proof using. by case: t => t /= /andP []. Qed.

Lemma shape_tabsh t : shape t = sh.
Proof using. by case: t => t /= /andP [] _ /eqP. Qed.

From mathcomp Require Import tuple.

Lemma tabsh_to_wordK t : rev (reshape (rev sh) (to_word (val t))) = t.
Proof using. by rewrite /= -(shape_tabsh t); apply: to_wordK. Qed.

Let tabsh_enum :
  seq tabsh :=
  pmap insub [seq rev (reshape (rev sh) (val w)) |
              w in [finType of d.-tuple 'I_n.+1]].

Lemma finite_tabsh : Finite.axiom tabsh_enum.
Proof using.
case=> /= t Ht; rewrite -(count_map _ (pred1 t)) (pmap_filter (@insubK _ _ _)).
rewrite count_filter -(@eq_count _ (pred1 t)) => [|s /=]; last first.
  by rewrite isSome_insub; case: eqP=> // ->.
move: Ht => /andP [] Htab /eqP Hsh.
rewrite count_map.
have Htw : size (to_word t) == d.
  by rewrite size_to_word /size_tab Hsh intpartn_sumn.
rewrite (eq_in_count (a2 := pred1 (Tuple Htw))).
  by rewrite enumT; apply: enumP (Tuple Htw).
move=> w _ /=; apply/idP/idP.
- move=> /eqP Ht; subst t.
  apply/eqP/val_inj => /=; rewrite /to_word revK.
  by apply esym; apply: reshapeKr; rewrite sumn_rev size_tuple intpartn_sumn.
- move=> /eqP Hw; subst w; rewrite /=.
  by rewrite /to_word -Hsh -shape_rev flattenK revK.
Qed.

Canonical tabsh_finMixin := Eval hnf in FinMixin finite_tabsh.
Canonical tabsh_finType := Eval hnf in FinType tabsh tabsh_finMixin.
Canonical tabsh_subFinType := Eval hnf in [subFinType of tabsh_countType].


Lemma to_word_enum_tabsh :
  perm_eq
    [seq to_word (tabshval t) | t <- enum tabsh]
    [seq x <- [seq val i | i <- enum [finType of d.-tuple 'I_n.+1]]
    | tabsh_reading sh x].
Proof using.
apply uniq_perm_eq.
- rewrite map_inj_in_uniq; first exact: enum_uniq.
  move=> t u _ _ /= Heq; apply val_inj.
  by rewrite /= -(tabsh_to_wordK t) -(tabsh_to_wordK u) Heq /=.
- apply filter_uniq; rewrite map_inj_uniq; last exact: val_inj.
  exact: enum_uniq.
move=> w /=; rewrite /tabsh_reading mem_filter; apply/idP/idP.
- move=> /mapP [] t _ -> {w}.
  rewrite size_to_word /size_tab shape_tabsh eq_refl /=.
  rewrite tabsh_to_wordK tabshP /=.
  have Ht : size (to_word (val t)) == d.
    by rewrite size_to_word /size_tab shape_tabsh intpartn_sumn.
  have -> : to_word (val t) = val (Tuple Ht) by [].
  rewrite mem_map; last exact: val_inj.
  exact: mem_enum.
- move=> /andP [] /andP [] /eqP Hsz Htab /mapP [] tpl _ hw; subst w.
  have Htsh : is_tab_of_shape sh (rev (reshape (rev sh) tpl)).
    rewrite /is_tab_of_shape /= Htab /= shape_rev reshapeKl ?revK //.
    by rewrite sumn_rev Hsz.
  suff -> : val tpl = to_word (TabSh Htsh).
    by apply/mapP; exists (TabSh Htsh) => //; apply: mem_enum.
  rewrite /= /to_word revK reshapeKr //.
  by rewrite sumn_rev Hsz.
Qed.

Lemma all_ltn_nth_tabsh t i : all (fun x : 'I_n.+1 => i <= x) (nth [::] t i).
Proof.
have:= tabshP t => /is_tableauP [_ _ Hdom].
elim: i => [|i /allP IHi]; apply/allP => x //.
move/(_ _ _ (ltnSn i)): Hdom => /dominateP [Hsz]; move: (inhabitant _) => Z.
move: (nth [::] t i) (nth [::] t i.+1) Hsz IHi => Ri Ri1 Hsz IHi Hdom Hx.
have:= Hx; rewrite -index_mem => Hxind.
have:= Hxind => /leq_trans/(_ Hsz)/(mem_nth Z)/IHi{IHi}/leq_ltn_trans; apply.
move/(_ _ Hxind): Hdom; rewrite sub_pord_ltnXE ltnXnatE /=.
by rewrite nth_index.
Qed.

Lemma size_tabsh t : size t <= n.+1.
Proof.
have Hall := all_ltn_nth_tabsh t.
have:= tabshP t => /is_tableauP [Hnnil _ _].
apply contraT; rewrite -ltnNge => Hn.
move/(_ n.+1): Hall; move/(_ _ Hn): Hnnil => {Hn}.
case: (nth [::] t n.+1) => //= x s _ /andP [Hn _ {s}].
have:= ltn_ord x; rewrite ltnS => /(leq_trans Hn).
by rewrite ltnn.
Qed.

Lemma tabszsh_subproof t : is_tab_of_size d t.
Proof. by rewrite /= tabshP /= /size_tab shape_tabsh intpartn_sumn. Qed.
Definition tabszsh t := TabSz (tabszsh_subproof t).

Lemma tabszsh_inj : injective tabszsh.
Proof. by move=> [t1 Ht1] [t2 Ht2] /(congr1 val) /= H; apply val_inj. Qed.

End FinType.

Hint Resolve tabszP.
Hint Resolve tabshP.

Definition cast_tabsz v m n (eq_mn : m = n) t :=
  let: erefl in _ = n := eq_mn return tabsz v n in t.

Lemma cast_tabszE v m n (eq_mn : m = n) (t : tabsz v m) :
  val (cast_tabsz eq_mn t) = val t.
Proof. subst m; by case: t. Qed.

Lemma cast_tabsz_id v n eq_n (t : tabsz v n) : cast_tabsz eq_n t = t.
Proof using. by apply val_inj => /=; rewrite cast_tabszE. Qed.

Lemma cast_tabszK v m n eq_m_n :
  cancel (@cast_tabsz v m n eq_m_n) (cast_tabsz (esym eq_m_n)).
Proof using. by subst m. Qed.

Lemma cast_tabszKV v m n eq_m_n :
  cancel (cast_tabsz (esym eq_m_n)) (@cast_tabsz v m n eq_m_n).
Proof using. by subst m. Qed.

Lemma cast_tabsz_inj v m n eq_m_n : injective (@cast_tabsz v m n eq_m_n).
Proof using. exact: can_inj (cast_tabszK eq_m_n). Qed.


Section IncrMap.

Variable T1 T2 : inhOrdType.
Variable F : T1 -> T2.

Lemma shape_incr_tab (t : seq (seq T1)) :
  shape [seq map F r | r <- t] = shape t.
Proof.
by rewrite /shape -map_comp; apply eq_map => s /=; rewrite size_map.
Qed.

Lemma get_incr_tab (t : seq (seq T1)) r c :
  is_in_shape (shape t) r c ->
  get_tab [seq [seq F i | i <- r0] | r0 <- t] r c = F (get_tab t r c).
Proof.
move=> Hin; have:= is_in_shape_size Hin; rewrite size_map => Hr.
move: Hin; rewrite /is_in_shape (nth_map [::]) // /get_tab => Hc.
by rewrite (nth_map [::] _ _ Hr) (nth_map (inhabitant T1)).
Qed.

Lemma incr_tab (t : seq (seq T1)) :
  {in (to_word t) &, forall x y, x <A y -> F x <A F y} ->
  (is_tableau t) = (is_tableau [seq map F r | r <- t]).
Proof.
move=> Hincr.
have Hndecr := in_incrX_nondecrXE Hincr.
have {Hincr} Hincr := in_incrXE Hincr.
apply/is_tableau_getP/is_tableau_getP;
  rewrite ?shape_incr_tab=> [] [H1 H2 H3]; split => // r c Hrc1.
- have Hrc : is_in_shape (shape t) r c.
    by move: Hrc1; rewrite /is_in_shape => /ltnW.
  rewrite !get_incr_tab //.
  rewrite -Hndecr; [exact: H2 | exact: mem_to_word | exact: mem_to_word].
- have Hrc : is_in_shape (shape t) r c.
    move: Hrc1; rewrite /is_in_shape => /leq_trans; apply.
    by move: H1 => /is_partP [] _; apply.
  rewrite !get_incr_tab //.
  rewrite -Hincr; [exact: H3 | exact: mem_to_word | exact: mem_to_word].
- have Hrc : is_in_shape (shape t) r c.
    by move: Hrc1; rewrite /is_in_shape => /ltnW.
  rewrite Hndecr; [|exact: mem_to_word | exact: mem_to_word].
  by rewrite -!get_incr_tab //; apply: H2.
- have Hrc : is_in_shape (shape t) r c.
    move: Hrc1; rewrite /is_in_shape => /leq_trans; apply.
    by move: H1 => /is_partP [] _; apply.
  rewrite Hincr; [|exact: mem_to_word | exact: mem_to_word].
  by rewrite -!get_incr_tab //; apply: H3.
Qed.

End IncrMap.
