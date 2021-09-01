(** * Combi.Combi.tableau : Young Tableaux *)
(******************************************************************************)
(*      Copyright (C) 2014-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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

- [is_row r] == [r] is sorted
- [dominate u v] == [u] dominate [v], that is [v] is longer than [u] and
            the i-th letter of [u] is strictly larger than the i-th letter of [v].
            this is an order relation on [seq T].
- [is_tableau t] == [t] of type [(seq (seq T))] is a tableau that is a sequence
            of non empty rows which is sorted for the dominate order.
- [get_tab t (r, c)] == the element of [t] of coordinate [(r, c)],
            or [inhabitant T] if [(r, c)] is not is the tableau
- [to_word t] == the row reading of the tableau [t]
- [size_tab t] == the size (number of boxes) of [t]
- [filter_gtnX_tab n t] == the sub-tableau of [t] formed by the element smaller
            than [n].

- [tabsh_reading sh w] == [w] is the row reading of a tableau of shape [sh]

In the following tableaux are considered on ['I_n.+1] for a given [n].

- [is_tab_of_shape sh t] == [t] is a tableau of shape [sh].
- [tabsh sh] == a sigma-type for the predicate [is_tab_of_shape sh] where
            [sh] is a partition of [d] (type ['P_d]). This is canonically
            a [subFinType].
- [tabrowconst pf] == if [pf] is a proof that [size sh <= n.+1] then
            construct the tableau (of type [tabsh sh]) whose i-th row
            contains only [i]'s as elements of ['I_n.+1].
*****)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype fintype choice seq.
From mathcomp Require Import path tuple order.
Require Import tools partition ordtype sorted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N.

Import Order.Theory.

(** ** Specialization of sorted Lemmas *)
Section Rows.

Variables (disp : unit) (T : inhOrderType disp).

Implicit Type l : T.
Implicit Type r : seq T.

Notation is_row := (sorted <=%O).

Definition is_row1P Z r := sorted1P Z <=%O r.
Definition is_rowP Z r := sortedP Z (@le_trans _ T) (@le_refl _ T) r.
Definition is_row_cons := sorted_cons (@le_refl _ T).
Definition is_row_consK := sorted_consK (T := T) (R := <=%O).
Definition is_row_rcons := sorted_rcons (T := T) (R := <=%O).
Definition is_row_rconsK := sorted_rconsK (T := T) (R := <=%O).
Definition is_row_last := sorted_last (@le_refl _ T).
Definition is_row_take := sorted_take (T := T) (R := <=%O).
Definition is_row_drop := sorted_drop (T := T) (R := <=%O).
Definition is_row_catL := sorted_catL (T := T) (R := <=%O).
Definition is_row_catR := sorted_catR (T := T) (R := <=%O).
Definition head_leq_last_row :=
  head_leq_last_sorted (@le_trans _ T) (@le_refl _ T).
Lemma row_lt_by_pos Z r p q:
  is_row r -> p < size r -> q < size r ->
  (nth Z r p < nth Z r q)%O -> p < q.
Proof using.
rewrite lt_neqAle.
exact: (sorted_lt_by_pos (@le_trans _ T) (@le_refl _ T) (@le_anti _ T)).
Qed.

End Rows.

Notation is_row := (sorted <=%O).

(** ** Dominance order for rows *)
Section Dominate.

Context {disp : unit} {T : inhOrderType disp}.

Implicit Type l : T.
Implicit Type r u v : seq T.
Implicit Type t : seq (seq T).

Lemma in_shape_tab_size t i j :
  in_shape (shape t) (i, j) -> i < size t.
Proof. by rewrite -(size_map size) -/shape; exact: in_shape_size. Qed.
Lemma in_shape_tab i j t :
  in_shape (shape t) (i, j) -> j < size (nth [::] t i).
Proof.
move=> Hin; have:= Hin; rewrite /in_shape /shape (nth_map [::]) //.
exact: (in_shape_tab_size Hin).
Qed.

Lemma is_row_set_nth l r pos :
  is_row r -> (l < nth l r pos)%O ->
  (forall n : nat, (l < nth l r n)%O -> pos <= n) ->
  is_row (set_nth l r pos l).
Proof using.
move=> /is_row1P Hrow Hl Hmin. apply/(is_row1P l) => i.
rewrite (lock (i.+1)) !nth_set_nth /=; unlock.
case: (ltnP pos (size r)) Hl => [Hpos Hl |HH]; first last.
  by rewrite (nth_default l HH) ltxx.
rewrite size_set_nth maxnC /maxn.
move: Hpos; rewrite leqNgt; move/negbTE => -> Hi1lt.
case eqP => Hipos; case eqP => Hi1pos.
- exact: le_refl.
- by apply: ltW; apply: (lt_le_trans Hl); rewrite -Hipos; apply: Hrow.
- move: {Hmin} (contra (Hmin i)); rewrite -leNgt -ltnNge; apply.
  by rewrite Hi1pos leqnn.
- exact: Hrow.
Qed.

Fixpoint dominate_rec u v :=
  if u is u0 :: u' then
    if v is v0 :: v' then (u0 > v0)%O && (dominate_rec u' v')
    else false
  else true.

Definition dominate u v :=
  (size u <= size v) &&
   (all (fun i => nth inh u i > nth inh v i)%O (iota 0 (size u))).

Lemma dominate_recE : dominate =2 dominate_rec.
Proof using.
rewrite /dominate; elim=> [//| u0 u IHu] [//| v0 v] /=.
rewrite -IHu ltnS [RHS]andbA [LHS]andbA [_&& (v0 < u0)%O]andbC; congr (_ && _).
by rewrite -add1n iotaDl all_map; apply eq_all => i.
Qed.

Lemma dominateP u v :
  reflect (size u <= size v /\
           forall i, i < size u -> (nth inh u i > nth inh v i)%O)
          (dominate u v).
Proof using.
rewrite /dominate /mkseq ; apply/(iffP idP).
- move=> /andP [] Hsz /allP Hall; split; first exact Hsz.
  by move=> i Hi; apply: Hall; rewrite mem_iota add0n.
- by move=> [] -> /= H; apply/allP => i; rewrite mem_iota add0n; apply: H.
Qed.

Lemma dominate_trans : transitive dominate.
Proof using.
move=> r2 r1 r3; rewrite !dominate_recE.
elim: r1 r2 r3 => [//| a1 l1] IHl [|a2 l2] [|a3 l3] //=.
by move=> /andP [/(lt_trans _) Ha21 /IHl{IHl}Hrec] /andP [/Ha21 -> /Hrec ->].
Qed.

Definition dominate_rev_trans := rev_trans dominate_trans.

Lemma dominate_rcons v u l : dominate u v -> dominate u (rcons v l).
Proof using.
rewrite !dominate_recE.
by elim: u v => [//| u0 u IHu] [|v0 v] //= /andP [-> /IHu ->].
Qed.

Lemma dominate_take v u n : dominate u (take n v) -> dominate u v.
Proof.
rewrite !dominate_recE -{2}(cat_take_drop n v).
elim/last_ind: {v} (drop n v) (take n v) => [| v vn IHv]/= w.
  by rewrite cats0.
move=> /IHv {IHv}.
by rewrite -cats1 catA cats1 -!dominate_recE; exact: dominate_rcons.
Qed.

Lemma dominate_cut u v w:
  size u <= size v -> dominate u (v ++ w) -> dominate u v.
Proof using.
rewrite !dominate_recE.
elim: u v => [//| u0 u IHu] [|v0 v] //=.
by rewrite ltnS => /IHu{IHu}Hrec /andP [-> /Hrec ->].
Qed.

Lemma dominate_head u v :
  u != [::] -> dominate u v -> (head inh v < head inh u)%O.
Proof using.
by rewrite !dominate_recE; case: u v => [//| u0 u] [|v0 v] //= _ /andP [].
Qed.

Lemma dominate_tl a u b v :
  dominate (a :: u) (b :: v) -> dominate u v.
Proof using. by rewrite !dominate_recE => /= /andP []. Qed.

End Dominate.
Arguments dominate_trans {disp T}.
Arguments dominate_rev_trans {disp T}.


(** * Tableaux : definition and basic properties *)
Section Tableau.

Variables (disp : unit) (T : inhOrderType disp).

Implicit Type l : T.
Implicit Type r w : seq T.
Implicit Type t : seq (seq T).

Fixpoint is_tableau t :=
  if t is t0 :: t'
  then [&& (t0 != [::]), is_row t0, dominate (head [::] t') t0 & is_tableau t']
  else true.

Definition get_tab t (rc : nat * nat) := nth inh (nth [::] t rc.1) rc.2.

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
    apply: (dominate_trans _ _ _ _ Hdom0).
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

Lemma get_tab_default t rc :
  ~~ in_shape (shape t) rc -> get_tab t rc = inh.
Proof using.
rewrite /in_shape /get_tab -leqNgt nth_shape => Hc.
exact: nth_default.
Qed.

Lemma to_word_cons r t : to_word (r :: t) = to_word t ++ r.
Proof using. by rewrite /to_word rev_cons flatten_rcons. Qed.
Lemma to_word_rcons r t : to_word (rcons t r) = r ++ to_word t.
Proof using. by rewrite /to_word rev_rcons /=. Qed.

Lemma mem_to_word t rc :
  in_shape (shape t) rc -> get_tab t rc \in (to_word t).
Proof using.
move: rc => [r c]; rewrite /in_shape /get_tab.
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

Lemma is_tableau_sorted_dominate t :
  is_tableau t =
  [&& is_part (shape t),
   all (sorted <=%O) t &
   sorted (fun (r s : seq T) => dominate s r) t].
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

Lemma is_tableau_getP t :
  reflect
    [/\ is_part (shape t),
     (forall (r c : nat), in_shape (shape t) (r, c.+1) ->
                          (get_tab t (r, c) <= get_tab t (r, c.+1))%O) &
     (forall (r c : nat), in_shape (shape t) (r.+1, c) ->
                          (get_tab t (r, c) < get_tab t (r.+1, c))%O)]
    (is_tableau t).
Proof using.
rewrite is_tableau_sorted_dominate.
apply/(iffP idP) => [|[Hpart]].
- move=> /and3P [Hpart /allP Hrow /(sorted_strictP _ dominate_rev_trans)] Hdom.
  split; rewrite /get_tab => // r c Hin.
  + have/Hrow/is_row1P : (nth [::] t r) \in t.
      by apply/mem_nth/in_shape_tab_size/Hin.
    by apply; exact: in_shape_tab.
  + have/(Hdom [::])/dominateP [_] : r < r.+1 < size t.
      by rewrite ltnSn (in_shape_tab_size Hin).
    by apply; exact: in_shape_tab.
- rewrite /get_tab Hpart => Hrow Hcol /=; apply/andP; split.
  + apply/allP => /= c Hrin.
    have Hr := nth_index [::] Hrin.
    move: Hrin Hr; rewrite -index_mem; move: (index c t) => r Hr Hc; subst c.
    apply/is_row1P => i Hi; apply Hrow.
    by rewrite /in_shape (nth_map [::]).
  + apply/(sorted_strictP [::] dominate_rev_trans).
    rewrite (incr_equiv _ dominate_rev_trans) => r Hr.
    apply/dominateP; split.
    * rewrite -!(nth_map _ 0) -/shape //; last by move: Hr; apply ltnW.
      by move/is_partP: Hpart => [_].
    * move=> i Hi; apply Hcol.
      by rewrite /in_shape (nth_map [::]).
Qed.

(** ** Cuting rows and tableaux *)
Lemma row_dominate (u v : seq T) :
  is_row (u ++ v) -> dominate u v -> u = [::].
Proof using.
case: u => [//= | u0 u] /=.
case: v => [//= | v0 v] /= /order_path_min -/(_ le_trans)/allP Hall.
rewrite dominate_recE /= => /andP [Habs]; exfalso.
have /Hall : v0 \in u ++ v0 :: v by rewrite mem_cat in_cons eq_refl /= orbT.
by rewrite leNgt Habs.
Qed.


Lemma filter_gt_row r n :
  is_row r -> filter (>%O n) r = take (count (>%O n) r) r.
Proof using.
elim: r => [//= | r0 r IHr] Hrow /=.
case: (ltP r0 n) => Hr0.
- by rewrite add1n (IHr (is_row_consK Hrow)).
- rewrite add0n; have Hcount : count (>%O n) r = 0.
  elim: r r0 Hr0 Hrow {IHr} => [//= | r1 r /= IHr] r0 Hr0 /andP [] Hr0r1 Hpath.
  have Hr1 := le_trans Hr0 Hr0r1.
    by rewrite ltNge Hr1 (IHr r1 Hr1 Hpath).
  rewrite Hcount.
  by apply/nilP; rewrite /nilp size_filter Hcount.
Qed.

Lemma filter_le_row n r :
  is_row r -> filter (<=%O n) r = drop (count (>%O n) r) r.
Proof using.
elim: r => //= r0 r IHr Hrow /=.
case: (leP n r0) => Hr0.
- rewrite add0n; have Hcount : count (>%O n) r = 0.
  elim: r r0 Hr0 Hrow {IHr} => //= r1 r IHr r0 Hr0 /andP [] Hr0r1 Hpath.
  have Hr1 := le_trans Hr0 Hr0r1.
    by rewrite ltNge Hr1 (IHr r1 Hr1 Hpath).
  by rewrite Hcount (IHr (is_row_consK Hrow)) Hcount drop0.
- by rewrite add1n (IHr (is_row_consK Hrow)).
Qed.

Lemma count_gt_dominate r1 r0 n :
  dominate r1 r0 -> (count (>%O n) r1) <= (count (>%O n) r0).
Proof using.
move=> /dominateP [] Hsz Hdom.
rewrite -[r0](mkseq_nth inh) -[r1](mkseq_nth inh) /mkseq !count_map.
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
exact: lt_trans (Hdom i Hi) Hn.
Qed.

Lemma filter_gt_dominate r1 r0 n :
  is_row r0 -> is_row r1 -> dominate r1 r0 ->
  dominate (filter (>%O n) r1) (filter (>%O n) r0).
Proof using.
move=> Hrow0 Hrow1 Hdom.
have Hsize := count_gt_dominate n Hdom.
move: Hdom => /dominateP [] Hsz Hdom.
apply/dominateP; rewrite !size_filter.
split; first exact Hsize.
move=> i Hi.
rewrite (filter_gt_row _ Hrow0) (filter_gt_row _ Hrow1) !nth_take.
- by apply Hdom; apply (leq_trans Hi); apply: count_size.
- exact: Hi.
- exact: (leq_trans Hi).
Qed.

Definition filter_gt_tab n :=
  [fun t : (seq (seq T)) => filter (fun r => r != [::])
                                   [seq [seq x <- i | (n > x)%O] | i <- t]].

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

Lemma head_filter_gt_tab n t :
  is_tableau t ->
  head [::] (filter_gt_tab n t) = [seq x <- head [::] t | (x < n)%O].
Proof using.
elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil0 Hrow0 Hdom Htab.
case: (altP ([seq x <- t0 | (x < n)%O] =P [::])) => Ht0 //=.
rewrite (IHt Htab) Ht0 {IHt}.
case: t Hdom Htab => [//= | t1 t] /= Hdom /and3P [] Hnnil1 Hrow1 _.
have /dominateP := filter_gt_dominate n Hrow0 Hrow1 Hdom => [] [].
by rewrite Ht0 /= leqn0 => /nilP ->.
Qed.

Lemma is_tableau_filter_gt t n :
  is_tableau t -> is_tableau (filter_gt_tab n t).
Proof using.
elim: t => [//= | t0 t /= IHt] /and4P [] Hnnil Hrow Hdom Htab.
case: (altP ([seq x <- t0 | (x < n)%O] =P [::])) => Ht0 /=; first exact: IHt.
rewrite Ht0 /=; apply/and3P; split; last exact: IHt.
- apply sorted_filter; last exact Hrow.
  by move=> a b c; apply: le_trans.
- rewrite (head_filter_gt_tab _ Htab).
  apply filter_gt_dominate => //=.
  by move: Htab; case t => [//= | t1 t'] /= /and3P [].
Qed.

(** ** The size of a tableau *)
Definition size_tab t := sumn (shape t).

Lemma tab0 t : is_tableau t -> size_tab t = 0 -> t = [::].
Proof using.
move/is_part_sht; rewrite /size_tab => /part0 H{}/H.
by rewrite /shape; case t.
Qed.

Lemma size_to_word t : size (to_word t) = size_tab t.
Proof using.
rewrite /size_tab; elim: t => [//= | t0 t IHt] /=.
by rewrite to_word_cons size_cat IHt addnC.
Qed.

End Tableau.

Prenex Implicits is_tableau to_word size_tab.


(** ** Tableaux from their row reading *)
Section TableauReading.

Variables (disp : unit) (A : inhOrderType disp).

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


(** ** Sigma type for tableaux *)
Section FinType.

Context {disp : unit} {T : inhFinOrderType disp}.
Variables (d : nat) (sh : 'P_d).

Definition is_tab_of_shape (sh : seq nat) :=
  [pred t : seq (seq T) | (is_tableau t) && (shape t == sh) ].

Structure tabsh : predArgType :=
  TabSh {tabshval :> seq (seq T); _ : is_tab_of_shape sh tabshval}.
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

Lemma tabsh_to_wordK t : rev (reshape (rev sh) (to_word (val t))) = t.
Proof using. by rewrite /= -(shape_tabsh t); apply: to_wordK. Qed.

Let tabsh_enum :
  seq tabsh := pmap insub
              [seq rev (reshape (rev sh) (val w)) | w in {:d.-tuple T}].

Lemma finite_tabsh : Finite.axiom tabsh_enum.
Proof using.
case=> /= t Ht; rewrite -(count_map _ (pred1 t)) (pmap_filter (@insubK _ _ _)).
rewrite count_filter -(@eq_count _ (pred1 t)) => [|s /=]; last first.
  by rewrite isSome_insub; case: eqP=> // ->.
move: Ht => /andP [] Htab /eqP Hsh.
rewrite count_map.
have Htw : size (to_word t) == d.
  by rewrite size_to_word /size_tab Hsh sumn_intpartn.
rewrite (eq_in_count (a2 := pred1 (Tuple Htw))).
  by rewrite enumT; apply: enumP (Tuple Htw).
move=> w _ /=; apply/idP/idP.
- move=> /eqP Ht; subst t.
  apply/eqP/val_inj => /=; rewrite /to_word revK.
  by apply esym; apply: reshapeKr; rewrite sumn_rev size_tuple sumn_intpartn.
- move=> /eqP Hw; subst w; rewrite /=.
  by rewrite /to_word -Hsh -shape_rev flattenK revK.
Qed.

Definition tabsh_finMixin := Eval hnf in FinMixin finite_tabsh.
Canonical tabsh_finType := Eval hnf in FinType tabsh tabsh_finMixin.
Canonical tabsh_subFinType := Eval hnf in [subFinType of tabsh_countType].

Lemma to_word_enum_tabsh :
  perm_eq
    [seq to_word (tabshval t) | t : tabsh]
    [seq x <- [seq (i : seq _) | i : d.-tuple T]  | tabsh_reading sh x].
Proof using.
apply uniq_perm.
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
    by rewrite size_to_word /size_tab shape_tabsh sumn_intpartn.
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

End FinType.

Notation "'tabsh[' T ']' mu" :=
  (tabsh (T := [inhFinOrderType of T]) mu) (at level 10).

#[export] Hint Resolve tabshP : core.


(** TODO : Generalise to any finite order using Order.enum_val when released *)
Section OrdTableau.

Variable n : nat.
Variables (d : nat) (sh : 'P_d).

Implicit Type (t : tabsh['I_n.+1] sh).

Lemma all_ltn_nth_tabsh t (i : nat) :
  all (fun x : 'I_n.+1 => (i <= x)%O) (nth [::] t i).
Proof.
have:= tabshP t => /is_tableauP [_ _ Hdom].
elim: i => [|i /allP IHi]; apply/allP => x //.
move/(_ _ _ (ltnSn i)): Hdom => /dominateP [Hsz]; move: inh => Z.
move: (nth [::] t i) (nth [::] t i.+1) Hsz IHi => Ri Ri1 Hsz IHi Hdom Hx.
have:= Hx; rewrite -index_mem => Hxind.
have:= Hxind => /leq_trans/(_ Hsz)/(mem_nth Z)/IHi{IHi}/leq_ltn_trans; apply.
by move/(_ _ Hxind): Hdom; rewrite nth_index.
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

Hypothesis Hszs : size sh <= n.+1.
Lemma tabrowconst_subproof :
  is_tab_of_shape
    sh (take (size sh) [tuple nseq (nth 0 sh (i : 'I_n.+1)) i | i < n.+1]).
Proof.
have Hsz : size (take (size sh) [tuple nseq (nth 0 sh i0) i0  | i0 < n.+1]) =
           size sh.
  by rewrite size_take size_tuple -/(minn _ _) (minn_idPl Hszs).
have Hnth j (Hj : j < size sh) :
              nth [::] [tuple nseq (nth 0 sh i) i | i < n.+1] j =
              nseq (nth 0 sh j) (Ordinal (leq_trans Hj Hszs)).
  by rewrite -/(nat_of_ord (Ordinal (leq_trans Hj Hszs))) -tnth_nth tnth_mktuple.
apply/andP; split; first apply/is_tableauP; try split.
- move=> i; rewrite Hsz => Hi; rewrite nth_take //.
  rewrite (Hnth _ Hi) /=; apply/negP => /eqP/nilP.
  by rewrite /nilp size_nseq; apply/negP/nth_part_non0.
- move=> r; case: (ltnP r (size sh)) => Hr; last by rewrite nth_default // Hsz.
  apply/(is_rowP (ord0)) => i j; rewrite nth_take // (Hnth _ Hr) /=.
  rewrite size_nseq => /andP [Hij Hj].
  by rewrite !nth_nseq (leq_ltn_trans Hij Hj) Hj.
- move=> i j Hij; apply/dominateP.
  case: (ltnP j (size sh)) => Hj; last by rewrite nth_default // Hsz.
  have Hi := ltn_trans Hij Hj; rewrite !nth_take //.
  rewrite (Hnth _ Hi) (Hnth _ Hj) !size_nseq.
  have:= (is_part_ijP _ (intpartnP sh)) => [] [_] /(_ _ _ (ltnW Hij)) => Hleq.
  split; first exact: Hleq.
  by move=> c Hc; rewrite !nth_nseq Hc (leq_trans Hc Hleq).
- apply/eqP/(eq_from_nth (x0 := 0)); rewrite size_map // => i.
  by rewrite Hsz => Hi; rewrite nth_shape nth_take // Hnth size_nseq.
Qed.
Definition tabrowconst := TabSh (tabrowconst_subproof).

End OrdTableau.


(** ** Tableaux and increasing maps *)
Section IncrMap.

Context (disp1 disp2 : unit)
        (T1 : inhOrderType disp1)
        (T2 : inhOrderType disp2).
Variable F : T1 -> T2.

Lemma shape_map_tab (t : seq (seq T1)) :
  shape [seq map F r | r <- t] = shape t.
Proof.
by rewrite /shape -map_comp; apply eq_map => s /=; rewrite size_map.
Qed.

Lemma get_map_tab (t : seq (seq T1)) rc :
  in_shape (shape t) rc ->
  get_tab [seq [seq F i | i <- r0] | r0 <- t] rc = F (get_tab t rc).
Proof.
move=> Hin; have:= in_shape_size Hin; rewrite size_map => Hr.
move: Hin; rewrite /in_shape (nth_map [::]) // /get_tab => Hc.
by rewrite (nth_map [::] _ _ Hr) (nth_map inh).
Qed.

Lemma to_word_map_tab (t : seq (seq T1)) :
  to_word [seq map F r | r <- t] = map F (to_word t).
Proof. by rewrite /to_word map_flatten map_rev. Qed.

Lemma incr_tab (t : seq (seq T1)) :
  {in (to_word t) &, {homo F : x y / (x < y)%O}} ->
  (is_tableau t) = (is_tableau [seq map F r | r <- t]).
Proof.
move=> Hincr.
have Hndecr := in_incr_nondecrE Hincr.
move/in_incrE in Hincr.
apply/is_tableau_getP/is_tableau_getP;
  rewrite ?shape_map_tab=> [] [H1 H2 H3]; split => // r c Hrc1;
  have Hrc : in_shape (shape t) (r, c) by apply: (in_part_le H1 Hrc1).
- rewrite !get_map_tab //.
  rewrite Hndecr; [exact: H2 | exact: mem_to_word | exact: mem_to_word].
- rewrite !get_map_tab //.
  rewrite Hincr; [exact: H3 | exact: mem_to_word | exact: mem_to_word].
- rewrite -Hndecr; [|exact: mem_to_word | exact: mem_to_word].
  by rewrite -!get_map_tab //; apply: H2.
- rewrite -Hincr; [|exact: mem_to_word | exact: mem_to_word].
  by rewrite -!get_map_tab //; apply: H3.
Qed.

End IncrMap.
