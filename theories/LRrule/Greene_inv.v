(** * Combi.LRrule.Greene_inv : Greene subsequence theorem *)
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
(** * Greene subsequence theorem

The goal of this file is to show that row and column Greene numbers are plactic
invariants. As a consequence, for any word [w], the Greene numbers of [w] are
equal to the Greene numbers of the row reading of its insertion tableau. This
ultimately allows to prove the reciprocal of [Sch_plact], that is

   [ Theorem plactic_RS u v : u =Pl v <-> RS u == RS v. ]

The main tool of the proof is surgery of [k]-supports along plactic rewriting.
As a consequence, the whole file is rather technical with no external use except
for the final theorems. To keep notation short while avoiding to pollute the
global namespace we enclosed the different cases into Coq modules.


-------------------------------------------------------------------------------

Here is the content of the file:

Greene numbers and duality:

The following function allows to transfer k-support through duality:
- [rev_ord_cast w i] == [size w - i : 'I_(size (revdual w))]
- [rev_set w S] == the image of [S] by [rev_ord_cast w]
- [rev_ksupp w P] == the image of [P] by [rev_set w]
- [rev_ksupp_inv w] == the inverse of [rev_ksupp w]

The Greene numbers of a word and its reversed dual agrees: Lemmas
[Greene_col_dual] and [Greene_row_dual].

-------------------------------------------------------------------------------

Swapping two letters:

In Module [Swap], we fix two words [u] [v] and two letters [l0] [l1].
We denote [x] the word [x := u l0 l1 v]. Then we define:
- [pos0 u v l0 l1] == the position of [l0] in [x] as a ['I_(size x)]
- [pos1 u v l0 l1] == the position of [l1] in [x] as a ['I_(size x)]
- [swap i] == exchange [l0] and [l1] and fixes all the other positions.
- [swap_set S] == then image of [S] by [swap]
We prove then various lemmas such as [swap_size_cover] asserting that swaping
keep the size of the cover.

-------------------------------------------------------------------------------

In Module [NoSetContainingBoth], we consider [x := u a b v].
We assume that (the position of) [a] and [b] are not in the same set of a
given k-support [P]. We construct a k-support [Q] for [y := u b a v] of the
same cover size:
- [swap_set S] == exchange the position of [a] and [b] in
        [S : {set 'I_(size x)}] and return the result as a [{set 'I_(size y)}]
- [Q P] == for a k-support [P] for [x], then [Q P] is a k-support for [y]
        of the same cardinality, assuming that [a] and [b] are not in the
        same set of [P].
The main results are lemmas [ksupp_Q] and [size_cover_Q].

-------------------------------------------------------------------------------

In Module [SetContainingBothLeft], we denote [x := u b a c v] and consider
a given k-support [P] containing both [a] and [c]. We want to deal at once with
the case where [a < b <= c] and [R := <=] and [c < b <= a] and [R := >].
So we encaspulate the hypothesis in a record [hypRabc] which contains among
other that [R b c] holds but not [R b a]. Specifically:
- [hypRabc R a b c] == a record encapsulating that [a R b R c] for a total
        strict or non strict order [R].
We construct in lemmas [RabcLeqX] and [RabcGtnX] the two records dealing with
the two preceding cases.

We are looking for a k-support for [y := u b c a v] of the same size. To be
able to apply the preceding module, we need to construct another k-support [Q]
for [x] with the same cover than [P], but such that [a] and [c] are not in the
same set. There are two cases:

1- if [b] is not in [cover P]: We define:

  [Qbnotin P] == [P] with [a] replaced by [b]. This is a still a k-support
        for [x] of the same cardinality by lemmas [ksupp_bnotin] and
        [size_cover_bnotin].

2- if [b] is in [cover P]: Due to monotonic condition, [b] must be in a
  different set [T] in [P] than the set [S] which contains [a] and [b]. The
  idea is that [S] and [T] should exchange their part in [c :: v]. We
  therefore define:

  [S1 S T] == the elements of [S] which are on the left of [a] +
              the elements of [T] which are in [v]
  [S1 S T] == the elements of [T] which are on the left of [b] +
              the elements of [S] which are in [c :: v]
  [Qbin P S T] == [P] where we have replaced [S] and [T] by [S1] and [T1].
              It is a k-support for [x] (Lemma [ksupp_bin]) with the same cover
              than [p] (Lemma [cover_bin]).

Then we prove consecutively two theorems:
- [SetContainingBothLeft.exists_Q_noboth] which allows to to assume that there
  is a k-support where no set contains both [a] and [c].
- [SetContainingBothLeft.exists_Qy] which find a k-support for
  [y := u b c a v] of the same size of cover.

This allow to show that each plactic rewriting rule leave the Greene numbers
invariant.

-------------------------------------------------------------------------------

We conclude by the main results:
- [Greene_row_invar_plactic] and [Greene_col_invar_plactic] asserting than
  Greene numbers are plactic invariants.
- [plactic_RS] which shows that the plactic classes are the fiber of the
  Robinson-Schensted map.
- [RS_rev_uniq] asserting that reverting a uniq word conjugate its insertion
  tableau.

 ****************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype finfun fintype choice.
From mathcomp Require Import seq tuple finset perm tuple path bigop order.
Require Import tools ordcast ordtype subseq partition tableau Yamanouchi stdtab.
Require Import Schensted congr plactic Greene.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.

Open Scope bool.

Section Duality.

Context {disp : unit} {Alph : inhOrderType disp}.
Let word := seq Alph.

Lemma extract_cut (N : nat) (wt : N.-tuple Alph) (i : 'I_N) (S : {set 'I_N}) :
  i \in S ->
  extract wt S =
  extract wt (S :&: [set j : 'I_N | j < i]) ++
          (tnth wt i) :: extract wt (S :&: [set j : 'I_N | j > i]).
Proof using.
move=> Hi; rewrite /extract /= extractIE.
rewrite -{1}[enum _](cat_take_drop i.+1) drop_enumI take_enumI !filter_cat map_cat.
rewrite -{1}[enum _](cat_take_drop i)    drop_enumI take_enumI !filter_cat map_cat.
rewrite -cat1s catA -!filter_predI.
congr (((map (tnth wt) _) ++ _) ++ (map (tnth wt) _)).
- apply eq_filter => j /=; rewrite !inE !andbT.
  congr ((j \in S) && _); case (ltnP j i) => H; last by rewrite andbF.
  by rewrite (ltn_trans H (ltnSn i)).
- rewrite [X in map _ X](_ : _ = [:: i]) //.
  rewrite (eq_filter (a2 := xpred1 i)); first last.
    move=> j /=; rewrite ltnS -eqn_leq inE andbT.
    case: (altP (j =P i)) => [-> | H]; first by rewrite eq_refl Hi.
    suff -> : (val j == val i) = false by rewrite andbF.
    by apply/negbTE; move: H; apply: contra; move/eqP/val_inj ->.
  apply: filter_pred1_uniq; first by rewrite -enumT; apply: enum_uniq.
  by rewrite -enumT mem_enum inE.
- by apply eq_filter => j /=; rewrite !inE !andbT.
Qed.

(** ** k-Support and order duality *)
Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Variable w : word.
Variable k : nat.

Local Definition rev_ord_cast : 'I_(size w) -> 'I_(size (revdual w)) :=
  (cast_ord (size_revdual w)) \o (@rev_ord _).
Local Definition rev_set (s : {set 'I_(size w)}) : {set 'I_(size (revdual w))} :=
  [set rev_ord_cast i | i in s].

Local Definition rev_ksupp (P : {set {set 'I_(size w)}}) :
  {set {set 'I_(size (revdual w))}} :=
  [set rev_set u | u in P].
Local Definition rev_ksupp_inv (S : {set {set 'I_(size (revdual w))}}) :
  {set {set 'I_(size w)}}  :=
  [set rev_ord_cast @^-1: s | s : {set 'I_(_)} in S].

Lemma rev_ord_cast_inj : injective rev_ord_cast.
Proof using.
by move=> i j; rewrite /rev_ord_cast /= => /cast_ord_inj/rev_ord_inj.
Qed.

Lemma rev_set_inj : injective rev_set.
Proof using.
by move=> i j /=; rewrite /rev_set; apply: imset_inj; exact rev_ord_cast_inj.
Qed.

Lemma rev_ksuppK : cancel rev_ksupp rev_ksupp_inv.
Proof using.
move=> S; rewrite /rev_ksupp_inv /rev_ksupp -imset_comp /=.
set f := (X in imset X _).
suff /eq_imset -> : f =1 id by rewrite imset_id.
rewrite /f {f} /rev_set => s /=.
apply/setP/subset_eqP/andP.
by split; apply/subsetP=> i; rewrite inE;
  by rewrite mem_imset_eq; last exact rev_ord_cast_inj.
Qed.

Lemma rev_ksuppKV : cancel rev_ksupp_inv rev_ksupp.
Proof using.
move=> S; rewrite /rev_ksupp_inv /rev_ksupp -imset_comp /=.
set f := (X in imset X _).
suff /eq_imset -> : f =1 id by rewrite imset_id.
rewrite /f {f} /rev_set => s /=.
apply/setP/subset_eqP/andP; split; apply/subsetP=> i.
- by move=> /imsetP [t]; rewrite inE => Ht Hi; subst i.
- move=> Hi; apply/imsetP.
  exists (rev_ord ((cast_ord (esym (size_revdual w))) i)).
  + by rewrite /rev_ord_cast inE /= rev_ordK cast_ordKV.
  + by rewrite /rev_ord_cast /= rev_ordK cast_ordKV.
Qed.

Local Lemma irev_w i : i < size w -> size w - i.+1 < size w.
Proof using. move/subnSK ->; exact: leq_subr. Qed.

Lemma rev_enum :
  enum 'I_(size (revdual w)) = rev [seq rev_ord_cast i | i : 'I_(size w)].
Proof using.
apply: (inj_map val_inj); rewrite /=.
rewrite val_enum_ord map_rev -map_comp.
rewrite [map (_ \o _) _](eq_map (f2 := (fun i => size w - i.+1) \o val)) //.
rewrite map_comp val_enum_ord size_rev.
apply: (eq_from_nth (x0 := 0)); first by rewrite size_rev size_map.
move=> i; rewrite size_iota => Hi.
rewrite nth_rev; last by rewrite size_map size_iota.
rewrite (nth_iota _ _ Hi) add0n size_map (nth_map 0);
  last by rewrite size_iota; apply: irev_w.
rewrite size_iota (nth_iota _ _ (irev_w Hi)).
by rewrite add0n (subnSK Hi); rewrite subKn; last exact: ltnW.
Qed.

Lemma extract_rev_set S :
  (extract (in_tuple (revdual w))) (rev_set S) = revdual (extract (in_tuple w) S).
Proof using.
rewrite !/extract /= !extractIE /rev_set rev_enum.
rewrite filter_rev filter_map.
rewrite (eq_filter (a2 := mem S)); first last.
  by move=> i /=; rewrite mem_imset_eq; last exact rev_ord_cast_inj.
rewrite map_rev -!map_comp; congr (rev _).
apply: eq_map => i /=; rewrite !(tnth_nth inh) /=.
rewrite nth_rev; last exact: irev_w.
by rewrite subnSK // subKn; last exact: ltnW.
Qed.

Lemma is_row_dual T :
  sorted <=%O (extract (in_tuple w) T) =
  sorted <=%O (extract (in_tuple (revdual w)) (rev_set T)).
Proof using.
rewrite extract_rev_set.
case: (extract _ _) => [//= | l0 l] /=.
rewrite -rev_sorted revK /sorted.
by apply eq_path.
Qed.

Lemma is_col_dual T :
  sorted >%O (extract (in_tuple w) T) =
  sorted >%O (extract (in_tuple (revdual w)) (rev_set T)).
Proof using.
rewrite extract_rev_set.
case: (extract _ _) => [//= | l0 l] /=.
rewrite -rev_sorted revK /sorted /=.
apply eq_path => i j /=.
by rewrite -ltEdual.
Qed.

Lemma size_rev_ksupp P : #|rev_ksupp P| = #|P|.
Proof using. by rewrite card_imset; last exact: rev_set_inj. Qed.

Lemma trivIset_setrev P : trivIset P = trivIset (rev_ksupp P).
Proof using.
apply/idP/idP.
- by apply: imset_trivIset; exact rev_ord_cast_inj.
- by rewrite -{2}(rev_ksuppK P); apply: preimset_trivIset.
Qed.

Lemma rev_is_ksupp_row P :
  (P \is a k.-supp[<=%O, in_tuple w]) =
  (rev_ksupp P \is a k.-supp[<=%O, in_tuple (revdual w)]).
Proof using.
rewrite !unfold_in size_rev_ksupp trivIset_setrev; congr [&& _, _ & _].
apply/forallP/forallP => Hall S; apply/implyP.
- move=> /imsetP [T HT -> {S}].
  rewrite -is_row_dual.
  by move/(_ T) : Hall; rewrite HT.
- move=> HS; move/(_ (rev_set S)) : Hall.
  rewrite (_ : _ \in _); last by rewrite mem_imset_eq; last exact rev_set_inj.
  by rewrite is_row_dual.
Qed.

Lemma rev_is_ksupp_col P :
  (P \is a k.-supp[>%O, in_tuple w]) =
  (rev_ksupp P \is a k.-supp[>%O, in_tuple (revdual w)]).
Proof using.
rewrite !unfold_in size_rev_ksupp trivIset_setrev; congr [&& _, _ & _].
apply/forallP/forallP => Hall S; apply/implyP.
- move=> /imsetP [T HT -> {S}].
  rewrite -is_col_dual.
  by move/(_ T): Hall; rewrite HT.
- move=> HS; move/(_ (rev_set S)): Hall.
  rewrite (_ : _ \in _) /=; first last.
    by rewrite mem_imset_eq; last exact rev_set_inj.
  by have /= -> := is_col_dual S.
Qed.

Lemma size_cover_rev P : #|cover (rev_ksupp P)| = #|cover P|.
Proof using. by rewrite -size_cover_inj; last exact rev_ord_cast_inj. Qed.

Lemma Greene_col_dual : Greene_col w k = Greene_col (revdual w) k.
Proof using.
rewrite /Greene_col.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- apply: leq_Greene; rewrite /ksupp_inj => S HS; exists (rev_ksupp S).
  rewrite size_cover_rev eq_refl /=.
  by rewrite (rev_is_ksupp_col S) in HS.
- apply: leq_Greene; rewrite /ksupp_inj => S HS.
  exists (rev_ksupp_inv S); rewrite -{1}[S]rev_ksuppKV size_cover_rev eq_refl /=.
  by move: HS; rewrite -{1}[S]rev_ksuppKV rev_is_ksupp_col.
Qed.

Lemma Greene_row_dual : Greene_row w k = Greene_row (revdual w) k.
Proof using.
rewrite /Greene_col.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- apply: leq_Greene; rewrite /ksupp_inj => S HS; exists (rev_ksupp S).
  rewrite size_cover_rev eq_refl /=.
  by rewrite rev_is_ksupp_row in HS.
- apply: leq_Greene; rewrite /ksupp_inj => S HS.
  exists (rev_ksupp_inv S); rewrite -{1}[S]rev_ksuppKV size_cover_rev eq_refl /=.
  by move: HS; rewrite -{1}[S]rev_ksuppKV rev_is_ksupp_row.
Qed.

End Duality.

(** * Swaping two letters in a word and its k-supports *)
Module Swap.
Section Swap.

Context {disp : unit} {Alph : inhOrderType disp}.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Variable R : rel Alph.

Variable u v : word.
Variable l0 l1 : Alph.
Let x := u ++ [:: l0; l1] ++ v.

Lemma ult : size u < size x.
Proof using l0 l1 v.
by rewrite /= size_cat /= addnS ltnS -{1}[size u]addn0 leq_add2l.
Qed.
Definition pos0 := Ordinal ult.
Lemma u1lt : (size u).+1 < size x.
Proof using l0 l1 v.
by rewrite /= size_cat /= addnS ltnS -{1}[size u]addn0 ltn_add2l.
Qed.
Definition pos1 := Ordinal u1lt.

Lemma tnth_pos0 : tnth (in_tuple x) pos0 = l0.
Proof using.
by rewrite (tnth_nth l0) nth_cat (_ : pos0 < size u = false) ?ltnn // subnn.
Qed.

Lemma tnth_pos1 : tnth (in_tuple x) pos1 = l1.
Proof using.
rewrite (tnth_nth l1) nth_cat.
have -> : pos1 < size u = false.
  by have:= leqnSn (size u); rewrite leqNgt => /negbTE ->.
by rewrite subSn //= subnn.
Qed.

Lemma pos01F : (pos0 == pos1) = false.
Proof using. by rewrite /eq_op /= ltn_eqF. Qed.

Definition swap (i : 'I_(size x)) : 'I_(size x) :=
  if i == pos0 then pos1 else if i == pos1 then pos0 else i.

Lemma swap_invol : involutive swap.
Proof using.
rewrite /swap => i.
case: (altP (i =P pos0)) => [->|H0]; first by rewrite eq_sym pos01F eq_refl.
case: (altP (i =P pos1)) => [->|H1]; first by rewrite eq_refl.
by rewrite (negbTE H0) (negbTE H1).
Qed.
Lemma swap_inj : injective swap.
Proof using. exact (can_inj swap_invol). Qed.

Lemma swap0 : swap pos0 = pos1.
Proof using. by rewrite /swap pos01F eq_refl. Qed.
Lemma swap1 : swap pos1 = pos0.
Proof using. by rewrite /swap eq_sym pos01F eq_refl. Qed.
Lemma swapL (i : 'I_(size x)) : i < size u -> swap i = i.
Proof using.
move=> Hi.
by rewrite /swap /eq_op /= (ltn_eqF Hi) (ltn_eqF (ltn_trans (Hi) (ltnSn _))).
Qed.
Lemma swapR (i : 'I_(size x)) : i > (size u).+1 -> swap i = i.
Proof using.
move=> Hi; rewrite /swap /eq_op /= eq_sym.
have:= ltn_eqF (ltn_trans (Hi) (ltnSn _)); rewrite eqSS => ->.
by rewrite eq_sym (ltn_eqF Hi).
Qed.

Definition swap_set :=
  [fun s : {set 'I_(size x)} => swap @: s : {set 'I_(size x)}].
Lemma swap_set_invol : involutive swap_set.
Proof using.
move=> S; apply/setP => i; rewrite -{1}[i]swap_invol.
by rewrite !(mem_imset_eq _ _ swap_inj).
Qed.
Lemma swap_set_inj : injective swap_set.
Proof using. apply: imset_inj; exact (can_inj swap_invol). Qed.

Lemma swap_cover (P : {set {set 'I_(size x)}}) :
  cover (swap_set @: P) = swap_set (cover P).
Proof using.
rewrite cover_imset /cover; apply: esym; apply: big_morph.
- move=> i j /=; exact: imsetU.
- exact: imset0.
Qed.

Lemma swap_size_cover (P : {set {set 'I_(size x)}}) :
  #|cover (swap_set @: P)| = #|cover P|.
Proof using. by rewrite swap_cover card_imset; last exact swap_inj. Qed.

Lemma enum_cut : enum 'I_(size x) =
                 [seq i <- enum 'I_(size x) | val i < size u]
                   ++ [:: pos0; pos1]
                   ++ [seq i <- enum 'I_(size x) | val i >= (size u) + 2].
Proof using.
rewrite [RHS]catA -{1}[enum 'I_(size x)](cat_take_drop ((size u) + 2)).
rewrite -drop_enumI; congr (_ ++ _).
rewrite take_enumI -{1}[enum 'I_(size x)](cat_take_drop (size u)).
rewrite filter_cat //=; congr (_ ++ _).
- rewrite take_enumI -filter_predI.
  apply eq_filter=> i /=; apply: andb_idl => /ltn_trans; apply.
  by rewrite -{1}[size u](addn0); rewrite ltn_add2l.
- apply: (inj_map val_inj) => /=.
  rewrite map_filter_comp map_drop val_enum_ord drop_iota add0n /x !size_cat.
  rewrite addKn !iota_add map_id filter_cat -[RHS]cats0.
  congr (_ ++ _).
  + by rewrite /= !addnS addn0 ltnSn (ltn_trans (ltnSn _) (ltnSn _)).
  + rewrite (eq_in_filter (a2 := pred0)); first by rewrite filter_pred0.
    by move=> i; rewrite mem_iota /= leqNgt => /andP [/negbTE ->].
Qed.

Lemma size_cut_sizeu :
  size [seq i <- enum 'I_(size x) | val i < size u] = size u.
Proof using l0 l1 v.
suff -> : [seq i <- enum 'I_(size x) | val i < size u]
          = take (size u) (enum 'I_(size x)).
  rewrite size_take size_enum_ord size_cat.
  by rewrite addnS ltnS -{1}[size u]addn0 leq_add2l leq0n.
apply: (inj_map val_inj); rewrite map_take val_enum_ord take_iota.
rewrite (eq_filter (a2 := gtn ((size u))\o val)) //.
by rewrite map_filter_comp /= val_enum_ord iotagtnk minnC map_id.
Qed.

End Swap.
End Swap.


(** ** Case where no sets contains both

The goal of this module is the following: given a k-support P for the word
[u ++ [:: a; b] ++ v] which doesn't have as subsequence containing both
[a] and [b] to construct a k-support [Q] for [u ++ [:: b; a] ++ v] with
the same cover size. These statements are Lemmas [ksupp_Q] and [size_cover_Q]
 ******)
Module NoSetContainingBoth.

Section Case.

Context {disp : unit} {Alph : inhOrderType disp}.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Variable R : rel Alph.

Variable u v : word.
Variable a b : Alph.
Variable k : nat.
Let x := u ++ [:: a; b] ++ v.
Let y := u ++ [:: b; a] ++ v.

Variable P : {set {set 'I_(size x)}}.
Hypothesis Px : P \is a k.-supp[R, in_tuple x].

Notation posa := (Swap.pos0 u v a b).
Notation posb := (Swap.pos1 u v a b).
Notation swapX := (@Swap.swap _ u v a b).
Notation swap_setX := (Swap.swap_set u v a b).

Hypothesis HnoBoth :
  forall S : {set 'I_(size x)}, S \in P -> ~ ((posa \in S) && (posb \in S)).

Lemma Hcast : size x = size y. Proof using a b u v. by rewrite !size_cat. Qed.

(** This is essentially : [set cast_ord Hcast x | x in swap_setX S]. *)
Definition swap_set : {set 'I_(size x)} -> {set 'I_(size y)} :=
  (fun S : {set 'I_(size x)} => [set cast_ord Hcast x | x in S]) \o swap_setX.
(** This is essentially : [set swap_set x | x in P] *)
Definition Q : {set {set 'I_(size y)}} := imset swap_set (mem P).

Lemma swap_set_inj : injective swap_set.
Proof using.
rewrite /swap_set.
apply: inj_comp; last exact: Swap.swap_set_inj.
apply: imset_inj; exact: cast_ord_inj.
Qed.

Lemma extract_swap_set S :
  S \in P -> extract (in_tuple y) (swap_set S) = extract (in_tuple x) S.
Proof using HnoBoth.
move=> HS; rewrite /extract /= !extractmaskE /=.
rewrite (enum_cast_ord Hcast) -map_comp.
rewrite Swap.enum_cut /x /y !map_cat !mask_cat //=; first last.
  - rewrite size_map; exact: Swap.size_cut_sizeu.
  - rewrite size_map; exact: Swap.size_cut_sizeu.
rewrite !mem_cast.
congr (mask _ u ++ _ ++ mask _ v).
- apply eq_in_map => i /=.
  rewrite mem_filter => /andP [Hi _].
  by rewrite mem_cast -{1}[i](Swap.swapL Hi) /Swap.swap_set /= mem_imset_eq;
    last exact: Swap.swap_inj.
- rewrite -{1}Swap.swap1 mem_imset_eq //=; last exact: Swap.swap_inj.
  rewrite -{2 3}Swap.swap0 mem_imset_eq //=; last exact: Swap.swap_inj.
  by move/(_ _ HS): HnoBoth; case: (posa \in S); case: (posb \in S).
- apply eq_in_map => i /=.
  rewrite mem_filter => /andP []; rewrite addnS addn1 => Hi _.
  by rewrite mem_cast -{1}[i](Swap.swapR Hi) /Swap.swap_set /= mem_imset_eq;
    last exact: Swap.swap_inj.
Qed.

Lemma ksupp_Q : Q \is a k.-supp[R, in_tuple y].
Proof using HnoBoth Px.
move: Px => /and3P [HszP HtrivP /forallP /= HallP].
apply/and3P; split.
- by rewrite card_imset; last exact swap_set_inj.
- rewrite /Q /swap_set imset_comp.
  apply: imset_trivIset; first exact: cast_ord_inj.
  apply: imset_trivIset; first exact: Swap.swap_inj.
  exact HtrivP.
- apply/forallP => S2; apply/implyP => /imsetP [S HS -> {S2}].
  rewrite (extract_swap_set HS).
  by move/(_ S): HallP; rewrite HS.
Qed.

Lemma size_cover_Q : #|cover P| == #|cover Q|.
Proof using.
rewrite -Swap.swap_size_cover.
rewrite /Q /swap_set imset_comp.
apply/eqP; apply: size_cover_inj.
exact: cast_ord_inj.
Qed.

End Case.

End NoSetContainingBoth.



(** ** Cover surgery *)
Section CoverSurgery.

Variable N : nat.
Variable S : {set 'I_N}.
Variable P Q : {set {set 'I_N}}.

Lemma trivIset_coverU1 :
  trivIset P -> [disjoint S & cover P] -> trivIset (S |: P).
Proof using.
move=> Htriv Hdis; case (set_0Vmem S) => [-> | [s Hs]].
- case (boolP (set0 \in P)); first by move/setU1E ->.
  apply (@trivIsetU1 _ set0 P) => //= T _.
  by rewrite -setI_eq0 set0I.
- have HS : S \notin P.
    move: Hdis; rewrite -setI_eq0; apply: contraLR => /negbNE HS.
    have {}Hs : s \in S :&: cover P.
      by rewrite in_setI Hs /= /cover; apply/bigcupP; exists S.
    by apply/eqP/setP => H; have := H s; rewrite Hs in_set0.
  move: Htriv; rewrite /trivIset big_setU1 //=.
  + move/eqP ->; rewrite {2}/cover big_setU1 //=.
    rewrite cardsU; move: Hdis; rewrite -setI_eq0 => /eqP ->.
    by rewrite cards0 subn0.
Qed.

Lemma disjoint_cover (A B : {set 'I_N}) :
  [disjoint cover P & cover Q] -> A \in P -> B \in Q -> [disjoint A & B].
Proof using.
rewrite -!setI_eq0 => /eqP; rewrite -setP => Hcov HA HB.
apply/eqP/setP => i; rewrite in_set0.
apply/idP/idP; move/(_ i): Hcov; rewrite !inE /cover => /negbT.
apply contra => /andP [HiA HiB].
by apply/andP; split; apply/bigcupP; [exists A | exists B].
Qed.

Lemma trivIset_coverU :
  trivIset P -> trivIset Q -> [disjoint cover P & cover Q] -> trivIset (P :|: Q).
Proof using.
move=> /trivIsetP HtrivP /trivIsetP HtrivQ Hdis.
apply/trivIsetP => A B; rewrite !inE.
move=> /orP [] HA /orP [] HB Hneq.
- exact: HtrivP.
- exact: disjoint_cover.
- by rewrite disjoint_sym; exact: disjoint_cover.
- exact: HtrivQ.
Qed.

Lemma trivIset_coverD1 : trivIset P -> S \in P -> [disjoint S & cover (P :\ S)].
Proof using.
move=> /trivIsetP Htriv HS; rewrite /cover bigcup_disjoint //=.
move=> T; rewrite inE in_set1 eq_sym => /andP [Hneq HT].
exact: Htriv.
Qed.

End CoverSurgery.


(** ** Case where a set in [P] contains both [a] and [c]

In Module [SetContainingBothLeft], we denote [x := u b a c v] and consider
a given k-support [P] containing both [a] and [c]. We construct another
k-support [Q] for [x] with the same cover than [P], but such that [a] and [c]
are not in the same set. *)
Module SetContainingBothLeft.

(** *** Generic order hypothesis *)
Section RelHypothesis.

Context {disp : unit} {Alph : inhOrderType disp}.
Implicit Type a b c : Alph.

Record hypRabc  R a b c := HypRabc {
                      Rtrans : transitive R;
                      Hbc : R b c;
                      Hba : ~~ R b a;
                      Hxba : forall l, R l a -> R l b;
                      Hbax : forall l, R b l -> R a l
                  }.

Lemma RabcLeqX a b c :
  (a < b <= c)%O -> hypRabc <=%O a b c.
Proof.
move=> H; constructor.
- move=> x y z; exact: le_trans.
- by move: H => /andP /= [].
- by move: H => /andP /= []; rewrite ltNge.
- by move: H => /andP /= [H1 _] /= x H2; exact: (le_trans H2 (ltW H1)).
- by move: H => /andP /= [H1 _] /= x H2; exact: (le_trans (ltW H1) H2).
Qed.

Lemma RabcGtnX a b c :
  (a < b <= c)%O -> hypRabc >%O c b a.
Proof.
move=> H; constructor.
- exact: gt_trans.
- by move: H => /andP /= [].
- by move: H => /andP /= [] _; rewrite -!leNgt.
- by move: H => /andP /= [_ H1] /= x H2; exact: (le_lt_trans H1 H2).
- by move: H => /andP /= [_ H1] /= x H2; exact: (lt_le_trans H2 H1).
Qed.

End RelHypothesis.


Section Case.

Context {disp : unit} {Alph : inhOrderType disp}.
Let word := seq Alph.

Implicit Type u v w r : word.

Variable R : rel Alph.
Variable u v : word.
Variable a b c : Alph.

Hypothesis HRabc : hypRabc R a b c.

Let x := u ++ [:: b; a; c] ++ v.

Variable k : nat.
Variable P : {set {set 'I_(size x)}}.
Hypothesis Px : P \is a k.-supp[R, in_tuple x].

Notation posb := (Swap.pos0 u (c :: v) b a).
Notation posa := (Swap.pos1 u (c :: v) b a).
Notation swap := (@Swap.swap _ u (c :: v) b a).
Notation swap_set := (Swap.swap_set u (c :: v) b a).

Lemma u2lt : (size u).+2 < size x.
Proof using a b c v.
by rewrite /= size_cat /= 2!addnS 2!ltnS -{1}[size u]addn0 ltn_add2l.
Qed.
Definition posc := Ordinal u2lt.

Lemma tnth_posc : tnth (in_tuple x) posc = c.
Proof using a b u v.
rewrite /x (tnth_nth c) nth_cat /=.
have -> : (size u).+2 < size u = false.
  have:= leq_trans (leqnSn (size u)) (leqnSn _).
  by rewrite leqNgt => /negbTE ->.
by rewrite -add1n addnS -addSn addnK.
Qed.

Variable S : {set 'I_(size x)}.
Hypothesis HS : S \in P.
Hypothesis Hposa : (posa \in S).
Hypothesis Hposc : (posc \in S).

(** *** Case where [b] is not in [cover P]

Replacing [a] by [b] gives another k-support.
 *)
Section BNotIn.

Hypothesis HbNin : posb \notin (cover P).

Lemma posbinSF : posb \in S = false.
Proof using HS HbNin.
apply/negP => Hb.
by move: HbNin; rewrite /cover => /bigcupP []; exists S.
Qed.

Definition Qbnotin : {set {set 'I_(size x)}} := imset swap_set (mem P).

Lemma size_cover_bnotin : #|cover P| == #|cover Qbnotin|.
Proof using. by rewrite Swap.swap_size_cover. Qed.

Lemma inPQE T : T != swap_set S -> T \in Qbnotin -> T \in P.
Proof using HS HbNin Hposa Px.
rewrite /Qbnotin => Hneq /imsetP [TP HTP Hswap]; subst T.
have {}Hneq : TP != S by move: Hneq; apply: contra => /eqP ->.
suff -> : swap_set TP = TP by [].
rewrite /swap_set /= -setP /Swap.swap => i.
rewrite (eq_in_imset (g := id)); first by rewrite imset_id.
move=> {}i /= Hi.
have -> : (i == posb) = false.
  apply/negP => /eqP //= Hib; subst i.
  have Hcov : posb \in cover P by rewrite /cover; apply/bigcupP; exists TP.
  by move: HbNin; rewrite Hcov.
suff -> : (i == posa) = false by [].
apply/negP => /eqP //= Hib; subst i.
move: Px => /and3P [_ /trivIsetP Htriv _].
move/(_  _ _ HTP HS Hneq) : Htriv => /disjoint_setI0.
apply/setP => /(_ posa); rewrite in_set0 in_setI Hi.
by rewrite Hposa.
Qed.

Lemma extract_swap_set T :
  T != swap_set S -> T \in Qbnotin -> sorted R (extract (in_tuple x) T).
Proof using HS HbNin Hposa Px.
move/inPQE => H{}/H HT; move: Px => /and3P [_ _ /forallP/(_ T)].
by rewrite HT.
Qed.

Lemma extract_SE :
  extract (in_tuple x) S =
  (extract (in_tuple x) (S :&: [set j : 'I_(size x) | j < size u])) ++
    a :: c ::
    extract (in_tuple x) (S :&: [set j : 'I_(size x) | (size u).+2 < j]).
Proof using HS HbNin Hposa Hposc.
rewrite (extract_cut (in_tuple x) Hposa) /= Swap.tnth_pos1.
rewrite (_ : setI _ _ = S :&: [set j : 'I_(size x) | j < size u]); first last.
  rewrite -!setIdE -setP => i; rewrite !inE.
  case: (ltnP i (size u)) => Hi; first by rewrite (ltn_trans Hi).
  case: (ltnP i (size u).+1) => Hi2; last by rewrite andbF.
  have -> : i = posb.
    by apply: val_inj => /=; apply/eqP; rewrite eqn_leq Hi andbT -ltnS.
  by rewrite posbinSF.
congr (_ ++ _ :: _).
set LS := (setI _ _); have HposcLS : posc \in LS.
  by rewrite /LS !inE /=; apply/andP; split.
have /= -> := (extract_cut (in_tuple x) HposcLS).
have -> : LS :&: [set j : 'I_(size x) | j < (size u).+2] = set0.
  rewrite /LS -setP => i; rewrite !inE /=.
  apply/negP=> /andP //= [/andP [Hi H1] H2].
  by have:= leq_ltn_trans H1 H2; rewrite ltnn.
have /= -> := (extract0 (in_tuple x)); rewrite cat0s.
rewrite tnth_posc; congr (_ :: extractpred (in_tuple x) (mem (pred_of_set _))).
rewrite /LS {LS HposcLS} -setP => i; rewrite !inE.
case: (ltnP (size u).+2 i) => Hi2; last by rewrite !andbF.
by rewrite (ltn_trans (ltnSn _) Hi2) !andbT.
Qed.

Lemma extract_swap_setSE :
  extract (in_tuple x) (swap_set S) =
  (extract (in_tuple x) (S :&: [set j : 'I_(size x) | j < size u])) ++
    b :: c ::
    extract (in_tuple x) (S :&: [set j : 'I_(size x) | (size u).+2 < j]).
Proof using HS HbNin Hposa Hposc.
have /extract_cut -> /= : posb \in (swap_set S).
  by rewrite /swap_set /= -Swap.swap1; apply: imset_f.
rewrite (_ : setI _ _ = S :&: [set j : 'I_(size x) | j < size u]); first last.
  rewrite -!setIdE -setP => i; rewrite !inE.
  case: (ltnP i (size u)) => Hi; last by rewrite !andbF.
  rewrite !andbT -{1}(Swap.swapL Hi) mem_imset_eq //=.
  exact: Swap.swap_inj.
congr (_ ++ _ :: _); first by rewrite (tnth_nth b) /= nth_cat ltnn subnn.
set LS := (setI (imset _ _) _).
have HposcLS : posc \in LS.
  rewrite /LS !inE /=; apply/andP; split; last by [].
  rewrite -(Swap.swapR (i := posc)) //.
  rewrite mem_imset_eq //=; exact: Swap.swap_inj.
have /= -> :=  (extract_cut (in_tuple x) HposcLS).
have -> : LS :&: [set j : 'I_(size x) | j < (size u).+2] = set0.
  rewrite /LS -setP => i; rewrite !inE /=.
  case: (ltnP (size u) i) => Hi; last by rewrite andbF.
  case: (ltnP i (size u).+2) => Hi2; last by rewrite andbF.
  rewrite (_ : i = posa); first last.
    by apply: val_inj => /=; apply/eqP; rewrite eqn_leq Hi andbT -ltnS.
  rewrite -Swap.swap0 mem_imset_eq //=; last exact: Swap.swap_inj.
  by rewrite posbinSF.
have /= -> :=  (extract0 (in_tuple x)); rewrite cat0s.
rewrite tnth_posc; congr (_ :: extractpred (in_tuple x) (mem (pred_of_set _))).
rewrite /LS {LS HposcLS} -setP => i; rewrite !inE.
case: (ltnP (size u).+2 i) => Hi; last by rewrite !andbF.
rewrite -{1}(Swap.swapR (ltnW Hi)) mem_imset_eq //=; last exact: Swap.swap_inj.
rewrite andbT; congr (_ && _).
exact: (ltn_trans (ltn_trans (ltnSn _) (ltnSn _)) Hi).
Qed.

Lemma extract_swap_set_S : sorted R (extract (in_tuple x) (swap_set S)).
Proof using HRabc HS HbNin Hposa Hposc Px.
rewrite extract_swap_setSE.
have : sorted R (extract (in_tuple x) S).
  move: Px => /and3P [_ _ /forallP Hall].
  by have := Hall S; rewrite HS.
rewrite extract_SE.
set LL := extract _ _; set LR := extract _ _; rewrite /= => Hsort.
have HacR := subseq_sorted (Rtrans HRabc) (suffix_subseq _ _) Hsort.
have HbcR : sorted R [:: b, c & LR].
  by move: HacR; rewrite /= (Hbc HRabc)=> /andP [_ ->].
case: LL Hsort => [//= | LL0 LL] /=.
rewrite !cat_path => /andP [-> /= /and3P [/(Hxba HRabc) -> _ ->]].
by rewrite (Hbc HRabc).
Qed.

Lemma ksupp_bnotin : Qbnotin \is a k.-supp[R, in_tuple x].
Proof using HRabc HS HbNin Hposa Hposc Px.
move: Px => /and3P [HszP HtrivP /forallP HallP].
apply/and3P; split.
- by rewrite card_imset; last apply: Swap.swap_set_inj.
- rewrite /Qbnotin /swap_set.
  apply: imset_trivIset; first exact: Swap.swap_inj.
  exact HtrivP.
- apply/forallP => T2; apply/implyP => /imsetP [T HT -> {T2}].
  case: (altP (T =P S)) => Heq.
  + subst T; exact: extract_swap_set_S.
  + apply: extract_swap_set.
    * move: Heq; apply: contra => /eqP H; apply/eqP; exact: Swap.swap_set_inj.
    * by rewrite /Qbnotin mem_imset_eq; last exact: Swap.swap_set_inj.
Qed.

Lemma Qbnotin_noboth T : T \in Qbnotin -> ~ ((posa \in T) && (posc \in T)).
Proof using HS HbNin.
rewrite /Qbnotin => /imsetP [U HU -> {T}].
case: (altP (U =P S)) => Heq.
- subst U; rewrite -Swap.swap0 /swap_set /=.
  rewrite mem_imset_eq; last apply: Swap.swap_inj.
  by rewrite posbinSF.
- rewrite -Swap.swap0 /swap_set /=.
  rewrite mem_imset_eq; last apply: Swap.swap_inj.
  move/andP => [Hb _]; move: HbNin.
  by rewrite (_ : _ \in _); last by rewrite /cover; apply/bigcupP; exists U.
Qed.

End BNotIn.

(** *** Case where [b] is in [cover P]

We assume that is is in a set [T] and switch the right part of [S] and [T]
 *)
Section BIn.

Variable T : {set 'I_(size x)}.
Hypothesis HT : T \in P.
Hypothesis Hposb : posb \in T.

Lemma TSneq : T != S.
Proof using HRabc HS HT Hposa Hposb Px.
apply/eqP=> Heq; subst T.
have:= Hba HRabc; suff -> : R b a by [].
move: Px => /and3P [_ _ /forallP Hall].
move/(_ S): Hall; rewrite HS.
move/(sorted_extract_cond (Rtrans HRabc) [set posb; posa]).
have -> : S :&: [set posb; posa] = [set posb; posa].
  apply/setP/subset_eqP/andP.
  split; apply/subsetP=> i; first by rewrite inE => /andP [].
  rewrite !inE => /orP [] => /eqP ->; rewrite eq_refl /=; first by rewrite Hposb.
  by rewrite Hposa orbT.
have /extract2 -> : posb < posa by [].
by rewrite Swap.tnth_pos0 Swap.tnth_pos1 /= andbT.
Qed.

Lemma TS_disjoint : [disjoint S & T].
Proof using HRabc HS HT Hposa Hposb Px.
move: Px => /and3P [_ /trivIsetP Hdisj _].
by move/(_ _ _ HT HS TSneq): Hdisj; rewrite disjoint_sym.
Qed.

Lemma posb_inSF : (posb \in S) = false.
Proof using HRabc HS HT Hposa Hposb Px.
have:= TS_disjoint; rewrite -setI_eq0 => /eqP/setP => /(_ posb).
by rewrite in_set0 !inE Hposb andbT.
Qed.

Lemma posa_inTF : (posa \in T) = false.
Proof using HRabc HS HT Hposa Hposb Px.
have:= TS_disjoint; rewrite -setI_eq0 => /eqP/setP => /(_ posa).
by rewrite in_set0 !inE Hposa.
Qed.

Lemma posc_inTF : (posc \in T) = false.
Proof using HRabc HS HT Hposa Hposb Hposc Px.
have:= TS_disjoint; rewrite -setI_eq0 => /eqP/setP => /(_ posc).
by rewrite in_set0 !inE Hposc.
Qed.

Definition S1 := (S :&: [set j : 'I_(size x) | j <= posa])
                   :|: (T :&: [set j : 'I_(size x) | j > posc]).
Definition T1 := (T :&: [set j : 'I_(size x) | j <= posb])
                   :|: (S :&: [set j : 'I_(size x) | j >= posc]).

Lemma S1_subsST : S1 \subset (S :|: T).
Proof using.
by apply/subsetP=> i; rewrite !inE => /orP [] /andP [-> _]; last rewrite orbT.
Qed.

Lemma T1_subsST : T1 \subset (S :|: T).
Proof using.
by apply/subsetP=> i; rewrite !inE => /orP [] /andP [-> _]; first rewrite orbT.
Qed.

Lemma coverS1T1 : cover [set S1; T1] =  (S :|: T).
Proof using HRabc HS HT Hposa Hposb Hposc Px.
rewrite /cover bigcup_setU !big_set1.
apply/setP/subset_eqP/andP; split; apply/subsetP=> i; rewrite !inE.
- by move/or3P => [/orP [] | | ] /andP [-> _] //=; rewrite orbT.
- move/orP => [] Hi; rewrite Hi /=.
  + by case: (ltnP (size u).+1 i); first rewrite !orbT.
  + case: (leqP i (size u)) => Hiu; first by rewrite orbT.
    rewrite /=; apply/orP; left; apply/orP; right.
    have:= TS_disjoint => /disjoint_setI0/setP => Hdisj.
    case: (ltnP (size u).+2 i) => //= Hi2.
    case: (ltnP (size u).+1 i) => Hi1.
    * have Htmp : i = posc.
        by apply: val_inj => /=; apply/eqP; rewrite eqn_leq Hi2 Hi1.
      subst i => {Hi1 Hi2 Hiu}.
      by move/(_ posc): Hdisj; rewrite in_set0 in_setI Hi Hposc.
    * have Htmp : i = posa.
        by apply: val_inj => /=; apply/eqP; rewrite eqn_leq Hiu Hi1.
      subst i => {Hi1 Hi2 Hiu}.
      by move/(_ posa): Hdisj; rewrite in_set0 in_setI Hi Hposa.
Qed.

Lemma disjointS1T1 : [disjoint S1 & T1].
Proof using HRabc HS HT Hposa Hposb Px.
rewrite -setI_eq0; apply/eqP/setP => i; rewrite in_set0.
apply/negP; rewrite /S1 /T1 !inE => /andP [].
have:= TS_disjoint => /disjoint_setI0/setP => Hdisj.
move=> /orP [] /andP [Hi1 /= H1] /orP [] /andP [Hi2 /= H2].
- by move/(_ i): Hdisj; rewrite inE Hi1 Hi2 in_set0.
- by have:= leq_trans H2 H1; rewrite ltnn.
- have Hu2 := ltn_trans (ltnSn (size u)) (ltnSn _).
  by have:= leq_ltn_trans H2 (ltn_trans Hu2 H1); rewrite ltnn.
- by move/(_ i): Hdisj; rewrite inE Hi1 Hi2 in_set0.
Qed.

Lemma ST_cover_disjoint : [disjoint S :|: T & cover (P :\: [set S; T])].
Proof using HS HT Px.
rewrite -setI_eq0; apply/eqP/setP => i; rewrite in_set0.
apply/negP; move: Px => /and3P [_ /trivIsetP Htriv _].
rewrite !inE => /andP [] /orP [] Hi /bigcupP [U];
  rewrite !inE negb_or => /andP [/andP [HUS HUT] HU] HiU.
- move/(_ _ _ HU HS HUS): Htriv; rewrite -setI_eq0 => /eqP.
  by apply/setP => /(_ i); rewrite in_set0 !inE Hi HiU.
- move/(_ _ _ HU HT HUT): Htriv; rewrite -setI_eq0 => /eqP.
  by apply/setP => /(_ i); rewrite in_set0 !inE Hi HiU.
Qed.

Definition Qbin : {set {set 'I_(size x)}} :=
  [set S1; T1] :|: (P :\: [set S; T]).

Lemma trivIset_Qbin : trivIset Qbin.
Proof using HRabc HS HT Hposa Hposb Hposc Px.
apply: trivIset_coverU.
- apply/trivIsetP => A B; rewrite !inE => /orP [] /eqP -> /orP [] /eqP -> //=.
  + by rewrite eq_refl.
  + by move=> _; exact: disjointS1T1.
  + by move=> _; rewrite disjoint_sym; exact: disjointS1T1.
  + by rewrite eq_refl.
- apply: (@trivIsetS _ _ P); first exact: subsetDl.
  by move: Px => /and3P [_].
- by rewrite coverS1T1; apply: ST_cover_disjoint.
Qed.

Lemma cover_bin : cover Qbin = cover P.
Proof using HRabc HS HT Hposa Hposb Hposc Px.
have:= coverS1T1; rewrite /Qbin /cover !bigcup_setU => ->.
apply/setP/subset_eqP/andP; split; apply/subsetP=> i.
- rewrite !inE => /orP []; first move=> /orP [].
  + by move=> Hi; apply/bigcupP; exists S.
  + by move=> Hi; apply/bigcupP; exists T.
  + move/bigcupP => [U]; rewrite inE => /andP [_ HU Hi].
    by apply/bigcupP; exists U.
- move/bigcupP => [U HU Hi]; rewrite !inE.
  case (altP (U =P S)) => HUS; last case (altP (U =P T)) => HUT.
  + by subst U; rewrite Hi.
  + by subst U; rewrite Hi orbT.
  + apply/orP; right; apply/bigcupP.
    exists U; last exact Hi.
    by rewrite !inE negb_or HUS HUT HU.
Qed.

Lemma enumUltV (U V : {set 'I_(size x)}) d :
  (forall l, l \in U -> l <= d) ->
  (forall l, l \in V -> l > d) ->
  enum (mem (U :|: V)) = enum U ++ enum V.
Proof using.
move => HU HV; rewrite /enum_mem /= -enumT /=.
rewrite -{1}[enum 'I_(size x)](cat_take_drop d.+1) drop_enumI take_enumI filter_cat.
congr (_ ++ _); rewrite -filter_predI; apply: eq_filter => i /=; rewrite !inE.
- rewrite ltnS; case: (boolP (i \in U)) => HiU /=; first by rewrite HU.
  case: (boolP (i \in V)) => //= /(HV _).
  by rewrite ltnNge => /negbTE ->.
- case: (boolP (i \in V)) => HiV /=; first by rewrite orbT HV.
  case: (boolP (i \in U)) => //= /(HU _).
  by rewrite ltnNge => ->.
Qed.

Lemma extract_S1E :
  extract (in_tuple x) S1 =
  extract (in_tuple x) (S :&: [set j : 'I_(size x) | j <= posa]) ++
  extract (in_tuple x) (T :&: [set j : 'I_(size x) | j > posc]).
Proof using.
rewrite /S1 /extract /= /extractpred (enumUltV (d := posa)); first by rewrite map_cat.
- by move=> i; rewrite !inE => /andP [_ Hi].
- move=> i; rewrite !inE => /andP [_ Hi] /=.
  exact: (ltn_trans (ltnSn _)).
Qed.

Lemma extract_T1E :
  extract (in_tuple x) T1 =
  extract (in_tuple x) (T :&: [set j : 'I_(size x) | j <= posb]) ++
  extract (in_tuple x) (S :&: [set j : 'I_(size x) | j >= posc]).
Proof using.
rewrite /T1 /extract /= /extractpred (enumUltV (d := posb)); first by rewrite map_cat.
- by move=> i; rewrite !inE => /andP [_ Hi].
- move=> i; rewrite !inE => /andP [_ Hi] /=.
  exact: (ltn_trans (ltnSn _)).
Qed.

Lemma extract_Sa :
  extract (in_tuple x) (S :&: [set j : 'I_(size x) | j <= posa]) =
  rcons (extract (in_tuple x) (S :&: [set j : 'I_(size x) | j < posa])) a.
Proof using Hposa.
set S' := (X in extract _ X).
have : posa \in S' by rewrite /S' !inE leqnn Hposa.
rewrite /S'; move /extract_cut ->; rewrite -cats1 -{21}[[:: a]]cats0 -[tnth _ _ :: _]cat1s.
congr ((extract (in_tuple x) _) ++ _ ++ _).
- apply/setP => i; rewrite !inE.
  case (boolP (i \in S)) => //= _.
  case: (ltnP i (size u).+1); last by rewrite andbF.
  by move/ltnW ->.
- by rewrite (tnth_nth a) /x /=; elim: u.
- set s := (X in extract _ X); suff -> : s = set0 by rewrite extract0.
  rewrite /s {s} -setP => i; rewrite !inE -andbA.
  apply/negP=> /and3P [_ H1 H2].
  by have:= leq_trans H2 H1; rewrite ltnn.
Qed.

Lemma extract_cS :
  extract (in_tuple x) (S :&: [set j : 'I_(size x) | j >= posc]) =
  c :: extract (in_tuple x) (S :&: [set j : 'I_(size x) | j > posc]).
Proof using Hposc.
set S' := (X in extract _ X).
have : posc \in S' by rewrite !inE leqnn Hposc.
move /extract_cut ->; rewrite -cat1s -[RHS]cat1s -[RHS]cat0s.
congr (_ ++ _ ++ (extract (in_tuple x) _)).
- set s := (X in extract _ X); suff -> : s = set0 by rewrite extract0.
  rewrite /s {s} -setP => i; rewrite !inE -andbA.
  apply/negP => /and3P [_ H1 H2].
  by have:= leq_trans H2 H1; rewrite ltnn.
- by rewrite (tnth_nth a) /x /=; elim: u.
- apply/setP => i; rewrite !inE.
  case (boolP (i \in S)) => //= _.
  case: (ltnP (size u).+2 i); last by rewrite andbF.
  by move/ltnW ->.
Qed.

Lemma extract_Tb :
  extract (in_tuple x) (T :&: [set j : 'I_(size x) | j <= posb]) =
  rcons (extract (in_tuple x) (T :&: [set j : 'I_(size x) | j < posb])) b.
Proof using Hposb.
set T' := (X in extract _ X).
have : posb \in T' by rewrite /T' !inE leqnn Hposb.
move /extract_cut ->; rewrite -cats1 -[[:: b]]cats0 -[tnth _ _ :: _]cat1s.
congr ((extract (in_tuple x) _) ++ _ ++ _).
- apply/setP => i; rewrite !inE.
  case (boolP (i \in T)) => //= _.
  case: (ltnP i (size u)); last by rewrite andbF.
  by move/ltnW ->.
- by rewrite (tnth_nth a) /x /=; elim: u.
- set s := (X in extract _ X); suff -> : s = set0 by rewrite extract0.
  rewrite /s {s} -setP => i; rewrite !inE -andbA.
  apply/negP => /and3P [_ H1 H2].
  by have:= leq_trans H2 H1; rewrite ltnn.
Qed.

Lemma extract_bT :
  extract (in_tuple x) (T :&: [set j : 'I_(size x) | j >= posb]) =
  b :: extract (in_tuple x) (T :&: [set j : 'I_(size x) | j > posc]).
Proof using HRabc HS HT Hposa Hposb Hposc Px.
set T' := (X in extract _ X).
have : posb \in T' by rewrite !inE leqnn Hposb.
move /extract_cut ->. rewrite -[tnth _ _ :: _ ]cat1s -[RHS]cat1s -[RHS]cat0s.
congr (_ ++ _ ++ (extract (in_tuple x) _)).
- set s := (X in extract _ X); suff -> : s = set0 by rewrite extract0.
  rewrite /s {s} -setP => i; rewrite !inE -andbA.
  apply/negP => /and3P [_ H1 H2].
  by have:= leq_trans H2 H1; rewrite ltnn.
- by rewrite (tnth_nth a) /x /=; elim: u.
- apply/setP => i; rewrite !inE.
  case (boolP (i \in T)) => //= Hi.
  case: (ltnP (size u).+2 i).
  + by move/ltnW/ltnW => H; rewrite H (ltnW H).
  + move=> Hi1; apply/negP => /andP [_ H2].
    have:= TS_disjoint => /disjoint_setI0; apply/setP => Hdisj.
    case: (ltnP (size u).+1 i) => Hi2.
    * have Htmp : i = posc.
        by apply: val_inj => /=; apply/eqP; rewrite eqn_leq Hi2 Hi1.
      subst i => {Hi1 H2 Hi2}.
      by move/(_ posc): Hdisj; rewrite in_set0 in_setI Hi Hposc.
    * have Htmp : i = posa.
        by apply: val_inj => /=; apply/eqP; rewrite eqn_leq Hi2 H2.
      subst i => {Hi1 H2 Hi2}.
      by move/(_ posa): Hdisj; rewrite in_set0 in_setI Hi Hposa.
Qed.

Lemma extract_S1 : sorted R (extract (in_tuple x) S1).
Proof using HRabc HS HT Hposa Hposb Hposc Px.
move: Px => /and3P [_ _ /forallP Hall].
rewrite extract_S1E; set lL := (X in X ++ _); set lR := (X in _ ++ X).
have:= Hall S; rewrite HS => /= HseqS.
have:= Hall T; rewrite HT => /= HseqT {Hall}.
have : sorted R lR by apply: (sorted_extract_cond (Rtrans HRabc) _ HseqT).
have : sorted R lL by apply: (sorted_extract_cond (Rtrans HRabc) _ HseqS).
rewrite /=; case HlL: lL => [|l0 lL']; first by rewrite cat0s.
rewrite /sorted /= cat_path => -> /=.
case HlR : lR => [//=| r0 lR'] /= ->; rewrite andbT.
have -> : last l0 lL' = a.
  have := extract_Sa; rewrite -/lL HlL.
  case: (extract _ _) => [/= [-> ->] //=| y z [-> ->]].
  by rewrite last_rcons.
apply: (Hbax HRabc).
have:= sorted_extract_cond (Rtrans HRabc) [set j : 'I_(size x) | j >= posb] HseqT.
by rewrite extract_bT -/lR HlR /= => /andP [-> _].
Qed.

Lemma extract_T1 : sorted R (extract (in_tuple x) T1).
Proof using HRabc HS HT Hposb Hposc Px.
move: Px => /and3P [_ _ /forallP Hall].
rewrite extract_T1E; set lL := (X in X ++ _); set lR := (X in _ ++ X).
have:= Hall S; rewrite HS => /= HseqS.
have:= Hall T; rewrite HT => /= HseqT {Hall}.
have : sorted R lR by apply: (sorted_extract_cond (Rtrans HRabc) _ HseqS).
have : sorted R lL by apply: (sorted_extract_cond (Rtrans HRabc) _ HseqT).
rewrite /=; case HlL: lL => [|l0 lL']; first by rewrite cat0s.
rewrite /sorted /= cat_path => -> /=.
rewrite /lR extract_cS /= => ->; rewrite andbT.
have -> : last l0 lL' = b.
  have := extract_Tb; rewrite -/lL HlL.
  case: (extract _ _) => [/= [-> ->] //=| y z [-> ->]].
  by rewrite last_rcons.
exact: (Hbc HRabc).
Qed.

Lemma ksupp_bin : Qbin \is a k.-supp[R, in_tuple x].
Proof using HRabc HS HT Hposa Hposb Hposc Px.
move: Px => /and3P [HszP HtrivP /forallP HallP].
rewrite /Qbin; apply/and3P; split.
- move: HszP.
  rewrite -setDDl (cardsD1 S P) (cardsD1 T (P :\ S)) HS /=.
  have -> /= : T \in P :\ S by rewrite !inE TSneq HT.
  apply: leq_trans; rewrite addnA add1n.
  apply: (leq_trans (leq_card_setU _ _)); rewrite leq_add2r.
  by apply: (leq_trans (leq_card_setU _ _)); rewrite !cards1.
- exact: trivIset_Qbin.
- apply/forallP => U; apply/implyP; rewrite !inE => /orP []; first move => /orP [].
  + by move/eqP => H; subst U; exact: extract_S1.
  + by move/eqP => H; subst U; exact: extract_T1.
  + by rewrite negb_or => /andP [_ HU]; have := HallP U; rewrite HU /=.
Qed.

Lemma posaS1_bin : posa \in S1.
Proof using Hposa. by rewrite /S1 !inE Hposa leqnn. Qed.

Lemma posaT1_bin : posb \in T1.
Proof using Hposb. by rewrite /T1 !inE Hposb leqnn. Qed.

Lemma Qbin_noboth U : U \in Qbin -> ~ ((posa \in U) && ((posc \in U))).
Proof using HRabc HS HT Hposa Hposb Px.
rewrite /Qbin !inE.
case: (altP (U =P S1)) => [-> _ |HneqS1] /=.
- by rewrite /S1 !inE Hposa /= !ltnn !andbF.
case: (altP (U =P T1)) => [-> _ |HneqT1] /=.
- by rewrite /T1 !inE Hposa /= posa_inTF /= ltnn.
- move/andP => []; rewrite negb_or => /andP [HUS HUT] HU.
  move: Px => /and3P [_ /trivIsetP Htriv _].
  move/(_  _ _ HU HS HUS)/disjoint_setI0/setP/(_ posa) : Htriv.
  by rewrite in_set0 in_setI Hposa andbT => ->.
Qed.

End BIn.

(** *** Existence theorem for k-supports *)
Theorem exists_Q_noboth :
  exists Q : {set {set 'I_(size x)}},
    [/\ Q \is a k.-supp[R, in_tuple x], #|cover Q| = #|cover P| &
      forall S, S \in Q -> ~ ((posa \in S) && ((posc \in S)))].
Proof using HRabc HS Hposa Hposc Px.
case (boolP (posb \in (cover P))) => [/bigcupP [T HT HbT] | Hcov].
- exists (Qbin T); split => [||S0].
  + exact: ksupp_bin.
  + by rewrite cover_bin.
  + exact: Qbin_noboth.
- exists Qbnotin; split => [||S0].
  + exact: ksupp_bnotin.
  + by rewrite (eqP (size_cover_bnotin)).
  + exact: Qbnotin_noboth.
Qed.

Let x' := (u ++ [:: b]) ++ [:: a; c] ++ v.
Let y  := (u ++ [:: b]) ++ [:: c; a] ++ v.

Theorem exists_Qy :
  exists Q : {set {set 'I_(size y)}},
    #|cover Q| = #|cover P| /\ Q \is a k.-supp[R, in_tuple y].
Proof using HRabc HS Hposa Hposc Px x'.
have eqxx' : x = x' by rewrite /x /x' -catA.
pose eqsz := congr1 size eqxx'.
have:= exists_Q_noboth => [] [Q [/= Hsupp Hcover Hnoboth]].
move HcastP : ((cast_set eqsz) @: Q) => Q'.
exists (@NoSetContainingBoth.Q _ _ (u ++ [:: b]) v a c Q'); split.
- rewrite -(eqP (@NoSetContainingBoth.size_cover_Q _ _ (u ++ [:: b]) v a c Q')).
  rewrite -HcastP cover_cast /cast_set /=.
  by rewrite card_imset; last exact: cast_ord_inj.
- apply: NoSetContainingBoth.ksupp_Q.
  by rewrite -HcastP; apply: ksupp_cast.
- move=> S1; rewrite -HcastP => /imsetP [S0 HS0 -> {S1}].
  rewrite /cast_set /=.
  set x0 := (Swap.pos0 _ _ _ _); set x1 := (Swap.pos1 _ _ _ _).
  have:= Hnoboth S0 HS0.
  rewrite -(cast_ordKV eqsz x0) -(cast_ordKV eqsz x1).
  rewrite !(mem_imset_eq _ _ (@cast_ord_inj _ _ _)).
  have -> : cast_ord (esym eqsz) x0 = posa.
    by apply: val_inj; rewrite /= size_cat /= addn1.
  suff -> : cast_ord (esym eqsz) x1 = posc by [].
  by apply: val_inj; rewrite /= size_cat /= addn1.
Qed.

End Case.
End SetContainingBothLeft.


(** * Greene numbers are invariant by each plactic rules *)
Section GreeneInvariantsRule.

Context {disp : unit} {Alph : inhOrderType disp}.
Let word := seq Alph.

Variable u v1 w v2 : word.
Variable k : nat.


(** Rule: [[:: c; a; b] => if (a <= b < c)%Ord then [:: [:: a; c; b]] else [::]] *)
Lemma ksuppRow_inj_plact1i :
  v2 \in plact1i v1 -> ksupp_inj <=%O <=%O k (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof using.
move/plact1iP => [a] [b] [c] [Hord -> ->].
rewrite /ksupp_inj  => S1 Hsupp.
pose posa := (Swap.pos0 u (b :: w) c a).
pose posc := (Swap.pos1 u (b :: w) c a).
case (boolP [exists S, [&& S \in S1, posa \in S & posc \in S] ]).
- move/existsP => [S /and3P [HSin HSa HSb]].
  exfalso; move: Hsupp => /and3P [_ _ /forallP Hall].
  move/(_ S): Hall; rewrite HSin /=.
  move/(sorted_extract_cond le_trans [set posa; posc]).
  have -> : S :&: [set posa; posc] = [set posa; posc].
    apply/setP/subset_eqP/andP.
    split; apply/subsetP=> i; first by rewrite inE => /andP [].
    rewrite !inE => /orP [] /eqP ->; rewrite eq_refl /=; first by rewrite HSa.
    by rewrite HSb orbT.
  have /extract2 -> : posa < posc by [].
  rewrite !(tnth_nth b) /= andbT.
  elim u => [| u0 u'] /=.
  + move: Hord => /andP [/le_lt_trans H{}/H].
    by rewrite leNgt => ->.
  + by apply.
- rewrite negb_exists => /forallP Hall.
  exists (NoSetContainingBoth.Q S1);
    rewrite NoSetContainingBoth.size_cover_Q /=.
  apply: NoSetContainingBoth.ksupp_Q; first exact Hsupp.
  by move=> S HS; have:= Hall S; rewrite HS /= => /negbTE ->.
Qed.

Corollary Greene_row_leq_plact1i :
  v2 \in plact1i v1 -> Greene_row (u ++ v1 ++ w) k <= Greene_row (u ++ v2 ++ w) k.
Proof using. by move /ksuppRow_inj_plact1i; apply: leq_Greene. Qed.

(** Rule: [[:: b; a; c] => if (a < b <= c)%Ord then [:: [:: b; c; a]] else [::]] *)
Lemma ksuppRow_inj_plact2 :
  v2 \in plact2 v1 -> ksupp_inj <=%O <=%O k (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof using.
move/plact2P => [a] [b] [c] [Hord -> ->].
have Hyp := SetContainingBothLeft.RabcLeqX Hord.
have Hbac : ((u ++ [:: b]) ++ [:: a; c] ++ w) = (u ++ [:: b; a; c] ++ w).
  by rewrite -catA.
have Hbca : ((u ++ [:: b]) ++ [:: c; a] ++ w) = (u ++ [:: b; c; a] ++ w).
  by rewrite -catA.
rewrite -Hbca -Hbac /ksupp_inj  => P Hsupp.
pose posa := (Swap.pos0 (u ++ [:: b]) w a c).
pose posc := (Swap.pos1 (u ++ [:: b]) w a c).
case (boolP [exists S, [&& S \in P, posa \in S & posc \in S] ]).
- move/existsP => [S /and3P [HSin HSa HSc]].
  move HcastP : ((cast_set (congr1 size Hbac)) @: P) => P'.
  have Hsupp' :  P' \is a k.-supp[<=%O, in_tuple (u ++ [:: b; a; c] ++ w)].
    rewrite -HcastP; exact: ksupp_cast.
  move HcastS : (cast_set (congr1 size Hbac) S) => S'.
  have HS'in : S' \in P' by rewrite -HcastP -HcastS; apply: imset_f.
  set pos1 := Swap.pos1 u (c :: w) b a.
  have Hpos1 : pos1 \in S'.
    rewrite -(cast_ordKV (congr1 size Hbac) pos1) -HcastS /cast_set /=.
    apply: imset_f.
    suff -> //= : cast_ord (esym (congr1 size Hbac)) pos1 = posa by [].
    by apply: val_inj; rewrite /= size_cat /= addn1.
  set pos2 := SetContainingBothLeft.posc u w a b c.
  have Hpos2 : pos2 \in S'.
    rewrite -(cast_ordKV (congr1 size Hbac) pos2) -HcastS /cast_set /=.
    apply: imset_f.
    suff -> //= : cast_ord (esym (congr1 size Hbac)) pos2 = posc by [].
    by apply: val_inj; rewrite /= size_cat /= addn1.
  have:= SetContainingBothLeft.exists_Qy Hyp Hsupp' HS'in Hpos1 Hpos2.
  move=> [Q [Hcover HsuppQ]].
  exists Q; apply/andP; split; last exact HsuppQ.
  by rewrite Hcover -HcastP -size_cover_inj //=; exact: cast_ord_inj.
- rewrite negb_exists => /forallP Hall.
  exists (NoSetContainingBoth.Q P);
    rewrite NoSetContainingBoth.size_cover_Q /=.
  apply: NoSetContainingBoth.ksupp_Q; first exact Hsupp.
  by move=> S HS; have:= Hall S; rewrite HS /= => /negbTE ->.
Qed.

Corollary Greene_row_leq_plact2 :
  v2 \in plact2 v1 -> Greene_row (u ++ v1 ++ w) k <= Greene_row (u ++ v2 ++ w) k.
Proof using. by move /ksuppRow_inj_plact2; apply: leq_Greene. Qed.


(** Rule: [[:: a; c; b] => if (a <= b < c)%Ord then [:: [:: c; a; b]] else [::]] *)
Lemma ksuppCol_inj_plact1 :
  v2 \in plact1 v1 -> ksupp_inj >%O >%O k (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof using.
move/plact1P => [a] [b] [c] [Hord -> ->].
rewrite /ksupp_inj  => S1 Hsupp.
pose posa := (Swap.pos0 u (b :: w) a c).
pose posc := (Swap.pos1 u (b :: w) a c).
case (boolP [exists S, [&& S \in S1, posa \in S & posc \in S] ]).
- move/existsP => [S /and3P [HSin HSa HSb]].
  exfalso; move: Hsupp => /and3P [_ _ /forallP Hall].
  move/(_ S): Hall; rewrite HSin /= => Hsort.
  have:= sorted_extract_cond gt_trans [set posa; posc] Hsort.
  have -> : S :&: [set posa; posc] = [set posa; posc].
    apply/setP/subset_eqP/andP.
    split; apply/subsetP=> i; first by rewrite inE => /andP [].
    rewrite !inE => /orP [] => /eqP ->; rewrite eq_refl /=; first by rewrite HSa.
    by rewrite HSb orbT.
  have /extract2 -> : posa < posc by [].
  rewrite !(tnth_nth b) /= andbT.
  elim u => [| u0 u'] /=.
  + move: Hord => /andP [/le_lt_trans H{}/H /ltW].
    by rewrite leNgt => /negbTE ->.
  + by apply.
- rewrite negb_exists => /forallP Hall.
  exists (NoSetContainingBoth.Q S1);
    rewrite NoSetContainingBoth.size_cover_Q /=.
  apply: NoSetContainingBoth.ksupp_Q; first exact Hsupp.
  by move=> S HS; have:= Hall S; rewrite HS /= => /negbTE ->.
Qed.

Corollary Greene_col_leq_plact1 :
  v2 \in plact1 v1 -> Greene_col (u ++ v1 ++ w) k <= Greene_col (u ++ v2 ++ w) k.
Proof using. by move /ksuppCol_inj_plact1; apply: leq_Greene. Qed.

(** Rule: [[:: b; c; a] => if (a < b <= c)%Ord then [:: [:: b; a; c]] else [::]] *)
Lemma ksuppCol_inj_plact2i :
  v2 \in plact2i v1 -> ksupp_inj >%O >%O k (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof using.
move/plact2iP => [a] [b] [c] [Hord -> ->].
have Hyp := SetContainingBothLeft.RabcGtnX Hord.
have Hbca : ((u ++ [:: b]) ++ [:: c; a] ++ w) =
            (u ++ [:: b; c; a] ++ w) by rewrite -catA.
have Hbac : ((u ++ [:: b]) ++ [:: a; c] ++ w) =
            (u ++ [:: b; a; c] ++ w) by rewrite -catA.
rewrite -Hbca -Hbac /ksupp_inj  => P Hsupp.
pose posa := (Swap.pos0 (u ++ [:: b]) w c a).
pose posc := (Swap.pos1 (u ++ [:: b]) w c a).
case (boolP [exists S, [&& S \in P, posa \in S & posc \in S] ]).
- move/existsP => [S /and3P [HSin HSa HSc]].
  move HcastP : ((cast_set (congr1 size Hbca)) @: P) => P'.
  have Hsupp' : P' \is a k.-supp[>%O, in_tuple (u ++ [:: b; c; a] ++ w)]
    by rewrite -HcastP; exact: ksupp_cast.
  move HcastS : (cast_set (congr1 size Hbca) S) => S'.
  have HS'in : S' \in P' by rewrite -HcastP -HcastS; apply: imset_f.
  set pos1 := Swap.pos1 u (a :: w) b c.
  have Hpos1 : pos1 \in S'.
    rewrite -(cast_ordKV (congr1 size Hbca) pos1) -HcastS /cast_set /=.
    apply: imset_f.
    suff -> //= : cast_ord (esym (congr1 size Hbca)) pos1 = posa by [].
    by apply: val_inj; rewrite /= size_cat /= addn1.
  set pos2 := Ordinal (SetContainingBothLeft.u2lt u w c b a).
  have Hpos2 : pos2 \in S'.
    rewrite -(cast_ordKV (congr1 size Hbca) pos2) -HcastS /cast_set /=.
    apply: imset_f.
    suff -> //= : cast_ord (esym (congr1 size Hbca)) pos2 = posc by [].
    by apply: val_inj; rewrite /= size_cat /= addn1.
  have:= SetContainingBothLeft.exists_Qy Hyp Hsupp' HS'in Hpos1 Hpos2.
  move=> [Q [Hcover HsuppQ]].
  exists Q; apply/andP; split; last exact HsuppQ.
  by rewrite Hcover -HcastP -size_cover_inj //=; exact: cast_ord_inj.
- rewrite negb_exists => /forallP Hall.
  exists (NoSetContainingBoth.Q P);
    rewrite NoSetContainingBoth.size_cover_Q /=.
  apply: NoSetContainingBoth.ksupp_Q; first exact Hsupp.
  by move=> S HS; have:= Hall S; rewrite HS /= => /negbTE ->.
Qed.

Corollary Greene_col_leq_plact2i :
  v2 \in plact2i v1 -> Greene_col (u ++ v1 ++ w) k <= Greene_col (u ++ v2 ++ w) k.
Proof using. by move /ksuppCol_inj_plact2i; apply: leq_Greene. Qed.

End GreeneInvariantsRule.

(** ** Deducing the other comparisons by duality *)
Section GreeneInvariantsDual.

Context {disp : unit} {Alph : inhOrderType disp}.
Let word := seq Alph.
Implicit Type u v w : word.

Lemma Greene_row_leq_plact2i u v1 w v2 k :
  v2 \in plact2i v1 -> Greene_row (u ++ v1 ++ w) k <= Greene_row (u ++ v2 ++ w) k.
Proof using.
rewrite plact2idual => /Greene_row_leq_plact1i H.
rewrite [Greene_row (_ ++ v1 ++ _) k]Greene_row_dual.
rewrite [Greene_row (_ ++ v2 ++ _) k]Greene_row_dual.
move/(_ (revdual w) (revdual u) k): H.
by rewrite /revdual -!rev_cat !catA.
Qed.

Lemma Greene_row_leq_plact1 u v1 w v2 k :
  v2 \in plact1 v1 -> Greene_row (u ++ v1 ++ w) k <= Greene_row (u ++ v2 ++ w) k.
Proof using.
rewrite plact1dual => /Greene_row_leq_plact2 H.
rewrite [Greene_row (_ ++ v1 ++ _) k]Greene_row_dual.
rewrite [Greene_row (_ ++ v2 ++ _) k]Greene_row_dual.
move/(_ (revdual w) (revdual u) k): H.
by rewrite /revdual -!rev_cat -!catA.
Qed.

Lemma Greene_col_leq_plact1i u v1 w v2 k :
  v2 \in plact1i v1 -> Greene_col (u ++ v1 ++ w) k <= Greene_col (u ++ v2 ++ w) k.
Proof using.
rewrite plact1idual => /Greene_col_leq_plact2i H.
rewrite [Greene_col (_ ++ v1 ++ _) k]Greene_col_dual.
rewrite [Greene_col (_ ++ v2 ++ _) k]Greene_col_dual.
move/(_ (revdual w) (revdual u) k): H.
by rewrite /revdual -!rev_cat -!catA.
Qed.

Lemma Greene_col_leq_plact2 u v1 w v2 k :
  v2 \in plact2 v1 -> Greene_col (u ++ v1 ++ w) k <= Greene_col (u ++ v2 ++ w) k.
Proof using.
rewrite plact2dual => /Greene_col_leq_plact1 H.
rewrite [Greene_col (_ ++ v1 ++ _) k]Greene_col_dual.
rewrite [Greene_col (_ ++ v2 ++ _) k]Greene_col_dual.
move/(_ (revdual w) (revdual u) k): H.
by rewrite /revdual -!rev_cat -!catA.
Qed.


(** ** Invariance by the rules *)
Lemma Greene_row_invar_plact1 u v1 w v2 k :
  v2 \in plact1 v1 -> Greene_row (u ++ v1 ++ w) k = Greene_row (u ++ v2 ++ w) k.
Proof using.
move=> H; apply/eqP; rewrite eqn_leq; apply/andP; split.
- exact: Greene_row_leq_plact1.
- by apply: Greene_row_leq_plact1i; rewrite -plact1I.
Qed.

Lemma Greene_row_invar_plact1i u v1 w v2 k :
  v2 \in plact1i v1 -> Greene_row (u ++ v1 ++ w) k = Greene_row (u ++ v2 ++ w) k.
Proof using.
by rewrite -plact1I => H; apply: esym; apply: Greene_row_invar_plact1.
Qed.

Lemma Greene_row_invar_plact2 u v1 w v2 k :
  v2 \in plact2 v1 -> Greene_row (u ++ v1 ++ w) k = Greene_row (u ++ v2 ++ w) k.
Proof using.
move=> H; apply/eqP; rewrite eqn_leq; apply/andP; split.
- exact: Greene_row_leq_plact2.
- by apply: Greene_row_leq_plact2i; rewrite -plact2I.
Qed.

Lemma Greene_row_invar_plact2i u v1 w v2 k :
  v2 \in plact2i v1 -> Greene_row (u ++ v1 ++ w) k = Greene_row (u ++ v2 ++ w) k.
Proof using.
by rewrite -plact2I => H; apply: esym; apply: Greene_row_invar_plact2.
Qed.

Lemma Greene_col_invar_plact1 u v1 w v2 k :
  v2 \in plact1 v1 -> Greene_col (u ++ v1 ++ w) k = Greene_col (u ++ v2 ++ w) k.
Proof using.
move=> H; apply/eqP; rewrite eqn_leq; apply/andP; split.
- exact: Greene_col_leq_plact1.
- by apply: Greene_col_leq_plact1i; rewrite -plact1I.
Qed.

Lemma Greene_col_invar_plact1i u v1 w v2 k :
  v2 \in plact1i v1 -> Greene_col (u ++ v1 ++ w) k = Greene_col (u ++ v2 ++ w) k.
Proof using.
by rewrite -plact1I => H; apply: esym; apply: Greene_col_invar_plact1.
Qed.

Lemma Greene_col_invar_plact2 u v1 w v2 k :
  v2 \in plact2 v1 -> Greene_col (u ++ v1 ++ w) k = Greene_col (u ++ v2 ++ w) k.
Proof using.
move=> H; apply/eqP; rewrite eqn_leq; apply/andP; split.
- exact: Greene_col_leq_plact2.
- by apply: Greene_col_leq_plact2i; rewrite -plact2I.
Qed.

Lemma Greene_col_invar_plact2i u v1 w v2 k :
  v2 \in plact2i v1 -> Greene_col (u ++ v1 ++ w) k = Greene_col (u ++ v2 ++ w) k.
Proof using.
by rewrite -plact2I => H; apply: esym; apply: Greene_col_invar_plact2.
Qed.

End GreeneInvariantsDual.


(** * Main theorem *)
Section GreeneInvariants.

Context {disp : unit} {Alph : inhOrderType disp}.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

(** ** Row Greene number *)
Theorem Greene_row_invar_plactic u v :
  u =Pl v -> forall k, Greene_row u k = Greene_row v k.
Proof using.
move=> Hpl k.
move: v Hpl; apply: gencongr_ind; first exact: erefl.
move=> a b1 c b2 -> {u} /plactruleP [].
- exact: Greene_row_invar_plact1.
- exact: Greene_row_invar_plact1i.
- exact: Greene_row_invar_plact2.
- exact: Greene_row_invar_plact2i.
Qed.

Corollary Greene_row_RS k w : Greene_row w k = sumn (take k (shape (RS w))).
Proof using.
rewrite -Greene_row_tab; last exact: is_tableau_RS.
by apply: Greene_row_invar_plactic; exact: congr_RS.
Qed.

Corollary plactic_shapeRS_row_proof u v : u =Pl v -> shape (RS u) = shape (RS v).
Proof using.
move=> Hpl.
suff HeqRS k : Greene_row (to_word (RS u)) k = Greene_row (to_word (RS v)) k
  by apply: (Greene_row_tab_eq_shape (is_tableau_RS u) (is_tableau_RS v) HeqRS).
rewrite -!(Greene_row_invar_plactic (congr_RS _) k).
exact: Greene_row_invar_plactic.
Qed.


(** ** Column Greene number *)
Theorem Greene_col_invar_plactic u v :
  u =Pl v -> forall k, Greene_col u k = Greene_col v k.
Proof using.
move=> Hpl k.
move: v Hpl; apply: gencongr_ind; first exact: erefl.
move=> a b1 c b2 -> {u} /plactruleP [].
- exact: Greene_col_invar_plact1.
- exact: Greene_col_invar_plact1i.
- exact: Greene_col_invar_plact2.
- exact: Greene_col_invar_plact2i.
Qed.

Corollary Greene_col_RS k w :
  Greene_col w k = sumn (take k (conj_part (shape (RS w)))).
Proof using.
rewrite -Greene_col_tab; last exact: is_tableau_RS.
by apply: Greene_col_invar_plactic; exact: congr_RS.
Qed.

Corollary plactic_shapeRS u v : u =Pl v -> shape (RS u) = shape (RS v).
Proof using.
move=> Hpl.
suff HeqRS k : Greene_col (to_word (RS u)) k = Greene_col (to_word (RS v)) k
  by apply: (Greene_col_tab_eq_shape (is_tableau_RS u) (is_tableau_RS v) HeqRS).
rewrite -!(Greene_col_invar_plactic (congr_RS _) k).
exact: Greene_col_invar_plactic.
Qed.


(** ** Robinson-Schensted and the plactic monoid *)
Theorem plactic_RS u v : u =Pl v <-> RS u == RS v.
Proof using.
split; last exact: Sch_plact.
move Hu : (size u) => n Hpl.
have:= perm_size (plact_homog Hpl) => /esym; rewrite Hu.
elim: n u v Hpl Hu => [| n IHn] u v.
  by move=> _ /eqP/nilP -> /eqP/nilP ->; rewrite /RS.
move=> Hpl Hu Hv.
have:= size_rembig u; rewrite Hu /= => Hszu.
have:= size_rembig v; rewrite Hv /= => Hszv.
move/(_ _ _ (rembig_plactcongr Hpl) Hszu Hszv): IHn => /eqP {Hszu Hszv}.
case: u Hu Hpl => [//= | u0 u'] _.
case: v Hv     => [//= | v0 v'] _ => Hpl Hplrem.
have:= rembig_RS u0 u' => [] [iu Hiu].
have:= rembig_RS v0 v' => [] [iv]; rewrite -Hplrem {Hplrem} => Hiv.
rewrite -(maxL_perm (plact_homog Hpl)) in Hiv.
have:= plactic_shapeRS Hpl.
rewrite Hiu Hiv {Hiu Hiv} !shape_append_nth => H.
by rewrite -(incr_nth_inj H).
Qed.

Corollary RS_tabE (t : seq (seq Alph)) : is_tableau t -> RS (to_word t) = t.
Proof using.
move=> Htab.
have : is_RSpair (t, hyper_yam (shape t)).
  rewrite /is_RSpair Htab (hyper_yamP (is_part_sht Htab)) /=.
  by rewrite (evalseq_hyper_yam (is_part_sht Htab)).
move/RSmapinv2K; set w := (X in RSmap X); move=> Hw.
have:= RSmapE w; rewrite Hw /= => ->.
have:= congr_RS w.
by rewrite plactic_RS => /eqP <-.
Qed.

End GreeneInvariants.

Corollary Greene_row_eq_shape_RS
          (d1 d2 : unit) (S : inhOrderType d1) (T : inhOrderType d2)
          (s : seq S) (t : seq T) :
  (forall k, Greene_row s k = Greene_row t k) -> (shape (RS s) = shape (RS t)).
Proof.
move=> HGreene; apply: Greene_row_tab_eq_shape; try apply: is_tableau_RS.
move=> k.
rewrite -(Greene_row_invar_plactic (u := s)); last exact: congr_RS.
rewrite -(Greene_row_invar_plactic (u := t)); last exact: congr_RS.
exact: HGreene.
Qed.

Corollary Greene_col_eq_shape_RS
          (d1 d2 : unit) (S : inhOrderType d1) (T : inhOrderType d2)
          (s : seq S) (t : seq T) :
  (forall k, Greene_col s k = Greene_col t k) -> (shape (RS s) = shape (RS t)).
Proof.
move=> HGreene; apply: Greene_col_tab_eq_shape; try apply: is_tableau_RS.
move=> k.
rewrite -(Greene_col_invar_plactic (u := s)); last exact: congr_RS.
rewrite -(Greene_col_invar_plactic (u := t)); last exact: congr_RS.
exact: HGreene.
Qed.


(** ** Reverting uniq words *)
Section RevConj.

Context {disp : unit} {Alph : inhOrderType disp}.
Implicit Type s : seq Alph.

Theorem RS_rev_uniq s : uniq s -> RS (rev s) = conj_tab (RS s).
Proof using.
move Hsz : (size s) => n.
elim: n s Hsz => [| n IHn] s.
  by rewrite /RS /conj_tab; move=> /eqP/nilP -> _ /=.
move=> Hsz Huniq.
have:= size_rembig s; rewrite Hsz /= => /IHn/(_ (rembig_uniq Huniq)){IHn}.
rewrite (rembig_rev_uniq Huniq).

have: shape (RS (rev s)) = conj_part (shape (RS s)).
  have Htr := is_tableau_RS (rev s); have Ht := is_tableau_RS s.
  apply: sumn_take_inj.
    exact: is_part_sht.
    exact: is_part_conj (is_part_sht _).
  move=> k.
  rewrite -Greene_col_RS -Greene_row_RS /Greene_col /Greene_row.
  rewrite Greene_rel_rev revK (Greene_rel_uniq _ Huniq).
  apply eq_Greene_rel => x y /=.
  by rewrite lt_def.

case Hs: s Hsz => [//= | s0 s'] Hsz.
have:= rembig_RS s0 s' => [] [iu]; rewrite -Hs => Hrem; rewrite Hrem.
case/lastP Hrs: s Hsz Hs => [//= | t tn] _ Hs; rewrite -Hrs => Hsh Heq.
have:= rembig_RS tn (rev t) => [] [iv]; rewrite -rev_rcons -Hrs => HRSr.
move: Hsh; rewrite HRSr {HRSr}.
have Hpart := is_part_sht (is_tableau_RS (rembig s)).
have: is_add_corner (shape (RS (rembig s))) iu.
  have := is_part_sht (is_tableau_RS s); rewrite Hrem shape_append_nth => Hparti.
  rewrite -(incr_nthK Hpart Hparti); apply (add_corner_decr_nth Hparti).
  rewrite del_rem_corner => //.
  by move: Hpart => /is_partP [].
move: Heq Hpart.
move: (RS (rembig (rev s))) (RS (rembig s)) => tabr tab Hr.
subst tabr => Hpart Hcorn Hsh.
apply eq_from_shape_get_tab; first by rewrite shape_conj_tab.
move => [r c].
rewrite (append_nth_conj_tab _ Hpart Hcorn).
congr (get_tab (append_nth _ _ _) _).
- apply maxL_perm; rewrite -Hs -rev_rcons.
  by rewrite perm_sym -perm_rev.
- move: Hsh.
  rewrite !shape_append_nth shape_conj_tab.
  rewrite conj_part_incr_nth //.
  exact: incr_nth_inj.
Qed.

End RevConj.
