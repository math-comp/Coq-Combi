(** * Combi.LRrule.Schensted : The Robinson-Schensted correspondence *)
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
(** * The Robinson-Schensted correspondence

This file is a formalization of Schensted's algorithm and the Robinson-Schensted
correspondence. In the latter, it is easier to first store record the insertion
as a Yamanouchi word, that is the reverted sequence of the index of the rows where
the elements were inserted. In a second step, we translate the Yamanouchi word
in a standard tableau.

Note: There is some duplication is this file, essentially for pedagogical purpose.
And also because it was my first serious Coq/Mathcomp development ;-)

Here are the contents:

Insertion in a row:

- [inspred r l i] == [l] bump the [i] letter of [r]
- [bump r l] == [l] bump when inserted in [r]

- [mininspred r l] == the position of the letter bumped by [l]
- [inspos r l] == the position of the letter bumped by [l] defined recursively

- [insmin r l] == the insertion of [l] in [r] defined using [mininspred]
- [insrow r l] == the insertion of [l] in [r] defined resursively
- [ins r l]    == the insertion of [l] in [r] defined using [inspos]


Schensted algorithm:

- [Sch w] == Schented algorithm applied to [w]
- [subseqrow s w] == [s] is a nondeceasing subsequence of [w]
- [subseqrow_n s w n] == [s] is a nondeceasing subsequence of [w] of size [n]
The two main results are
- [Corollary size_ndec_Sch : subseqrow s w -> (size s) <= size (Sch w).]
- [Corollary exist_size_Sch w : exists s : seq T, subseqrow_n s w (size (Sch w)).]


Robinson-Schensted bumping:

- [bumped r l] == the letter bumped by [l] when inserted in [r], [l] itself
             if there is no bumping
- [bumprow r l] == bump [l] in [r] of type [(option T) * (seq T)]

- [instab t l] == insert the letter [l] in the tableau [t]
- [RS w] == the insertion tableau (P-symbol) of [w]. It is a tableau as stated
           in Theorem [is_tableau_RS].


Inverting the Robinson-Schensted map:

- [invbump b s] == [b] has been bumped by [s] that is [head b s < b]
- [invbumprow b s] == the inverse bumping of [b] in the row [s]. The result is
           a pair [(r, l)] such that [bumprow r l] give back [(some b, s)].
           This is lemma [bumprowinvK].
- [invins b s] == the [r] in [(r, l) := invbumprow b s]
- [invbumped b s] the [l] in [(r, l) := invbumprow b s].

- [instabnrow t l] == a pair [(s, n)] where [s] is the result of the insertion
           of [l] in [t] and [n] is the index of the row where the insertion
           stopped. As stated in Lemma [instabnrowE] [s = instab t l].
- [invinstabnrow s n] == the inverse insertion, that the pair [(t, l)] such that
           [instabnrow t l = (s, n)]. This is Theorem [invinstabnrowK]. See also
           Theorem [instabnrowinvK].

- [RSmap w] == the Robinson-Schensted map where the recording tableau is returned
           as a Yamanouchi word.
- [is_RSpair (P, Q)] == [P] is a tableau, [Q] is a Yammanouchi word and the shape
           of [P] is equal to the evaluation of [Q].
The main result is of course [Theorem RSmap_spec w : is_RSpair (RSmap w).]

- [RSmapinv tab yam] == the Robinson-Schensted inverse map of the pair [(tab, yam)]
- [RSmapinv2 p] == the uncurrying of [RSmapinv].
The bijectivity of [RSmap] and [RSmapinv2] are stated in
- Theorem [RSmapK] stated as [RSmapinv2 (RSmap w) = w.]
- and Theorem [RSmapinv2K] as [RSmap (RSmapinv2 pair) = pair.]
Moreover [RS] preserve the content:
- [Theorem perm_RS w : perm_eq w (to_word (RS w)).]


A sigma type for Robinson-Schensted pairs:

- [rspair T] == a sigma type for RS pair with tableau in type [T].
- [RSbij w] == the [rspair T] associated to [w : seq T]
- [RSbijinv p] == the [seq T] associated to [p : rspair T]
On has [Lemma bijRS : bijective RSbij.]


Robinson-Schensted classes:

- [RSclass t] == the list of word [w] having [t] as RS tableau. This is stated
          in Lemma [RSclassE] which says [w \in RSclass tab = (RS w == tab)].


Robinson-Schensted with standard recording tableau:

- [is_RStabpair (P, Q)] == [P] and [Q] are two tableau of the same shape,
          and [Q] is standard.
- [rstabpair T] == a sigma type for [is_RStabpair].

- [RStabmap w] == the RS map applied to [w] is is a RS pair as stated in
          Theorem [RStabmap_spec].

- [RStab w] == the RS map applied to [w] as a [rstabpair T].
- [RStabinv pair] == the word [w] associated to a [rstabpair]
Again, one has [Lemma bijRStab : bijective RStab.]
**************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype.
From mathcomp Require Import choice seq path bigop finset perm fingroup order.
Require Import tools partition Yamanouchi ordtype subseq tableau std stdtab.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N.

Import Order.Theory.

Section NonEmpty.

Variables (disp : unit) (T : inhOrderType disp).
(** * Schensted's algorithm *)

(** ** Row insertion *)
Section Insert.

Variable Row : seq T.
Hypothesis HRow : is_row Row.
Variable l : T.

Definition inspred i := (l < nth l Row i)%O.
Definition bump := (l < (last l Row))%O.

Lemma notbump : ~~bump = (l >= (last l Row))%O.
Proof using. by rewrite /bump /= -leNgt. Qed.

Lemma transf : bump -> (l < (nth l Row (size Row).-1))%O.
Proof using. by rewrite nth_last. Qed.

Lemma inspred_any_bump i : inspred i -> bump.
Proof using HRow.
rewrite /inspred /= /bump; have:= HRow.
elim: Row i => [/= | l0 r IHr] i /=; first by case: i.
case: i => [|i] /= /is_row_cons [] Hhead Hrow.
- case: r {IHr} Hhead Hrow => [//=|l1 r] /= Hl0l1.
  move/head_leq_last_row => Hlast Hll0.
  exact: lt_le_trans Hll0 (le_trans Hl0l1 Hlast).
- by move/(IHr _ Hrow); case r => //; rewrite ltxx.
Qed.

Definition mininspred : nat :=
  if ltP l (last l Row) is Order.LtlNotGe Hlast
  then ex_minn (ex_intro inspred (size Row).-1 (transf Hlast))
  else size Row.
Definition insmin := set_nth l Row mininspred l.

Lemma bump_mininspredE (Hbump : bump) :
  mininspred = ex_minn (ex_intro inspred (size Row).-1 (transf Hbump)).
Proof using.
rewrite /mininspred /inspred; apply/eqP.
case (ltP l (last l Row)) => Hlast.
- case (ex_minnP (ex_intro _ _ _)) => pos1 Hl1 Hpos1.
  case (ex_minnP (ex_intro _ _ _)) => pos2 Hl2 Hpos2.
  by rewrite eqn_leq (Hpos1 _ Hl2) (Hpos2 _ Hl1).
- by exfalso; move: Hbump; rewrite /bump /= ltNge Hlast.
Qed.

Lemma nbump_mininspredE : ~~bump -> mininspred = size Row.
Proof using.
rewrite notbump /mininspred /inspred => H.
case (ltP l (last l Row)) => [Hlt |//].
exfalso; have:= lt_le_trans Hlt H.
by rewrite ltxx.
Qed.

Fixpoint insrow r l : seq T :=
  if r is l0 :: r then
    if (l < l0)%O then l :: r
    else l0 :: (insrow r l)
  else [:: l].

Fixpoint inspos r (l : T) : nat :=
  if r is l0 :: r' then
    if (l < l0)%O then 0
    else (inspos r' l).+1
  else 0.

Notation pos := (inspos Row l).
Definition ins := set_nth l Row pos l.

Lemma inspos_leq_size : pos <= size Row.
Proof using. by elim: Row => [//= | l0 r IHr] /=; case: (ltP l l0). Qed.

Lemma inspos_lt_size_ins : pos < size ins.
Proof using.
rewrite /ins size_set_nth /maxn.
by case (ltnP pos.+1 (size Row)); first exact: ltnW.
Qed.

Lemma nth_inspos_ins : nth l ins pos = l.
Proof using. by rewrite /ins nth_set_nth /= eq_refl. Qed.

Lemma nbump_insposE : ~~bump -> mininspred = pos.
Proof using HRow.
move=> Hbump; rewrite (nbump_mininspredE Hbump).
move: Hbump; rewrite notbump.
elim: Row HRow => [//=|l0 r IHr] Hrow /= Hlast.
case: (ltP l l0) => [Hll0|_].
* exfalso => {IHr}.
  have:= le_lt_trans (le_trans (head_leq_last_row Hrow) Hlast) Hll0.
  by rewrite ltxx.
* move: Hrow=> /is_row_consK/IHr{IHr}.
  case: r Hlast => [//=| l1 r] /= Hlast.
  by case: (ltP l l1) => _ /(_ Hlast) ->.
Qed.

Lemma inspred_inspos : bump -> inspred pos.
Proof using.
rewrite /inspred /bump; elim: Row => [//=| l0 [_ /= H| l1 r /= IHr]].
- by rewrite H /= H.
- by move/IHr; case: (ltP l l0).
Qed.

Lemma inspred_mininspred : bump -> inspred mininspred.
Proof using.
move=> Hbump; rewrite (bump_mininspredE Hbump).
by case (ex_minnP (ex_intro _ _ _)).
Qed.

Lemma nth_lt_inspos i : i < pos -> (nth l Row i <= l)%O.
Proof using.
elim: Row i => [//=|t0 r IHr] /=; case: (ltP l t0) => //= Ht.
by case=> [//=|i] /=; exact: IHr.
Qed.

Lemma inspredN_lt_inspos i : i < pos -> ~~ (inspred i).
Proof using. by rewrite /inspred -leNgt; apply: nth_lt_inspos. Qed.

Lemma bump_insposE : bump -> mininspred = pos.
Proof using.
move=> Hbump; rewrite (bump_mininspredE Hbump).
case: (ex_minnP (ex_intro _ _ _)) => pos Hl Hpos.
move/(_ _ (inspred_inspos Hbump)): Hpos => Hleq.
case (ltnP pos (inspos Row l)) => H2.
- by exfalso; move: Hl; rewrite (negbTE (inspredN_lt_inspos H2)).
- by apply/eqP; rewrite eqn_leq Hleq H2.
Qed.

Lemma insposE : mininspred = pos.
Proof using HRow.
by case (boolP bump); [exact: bump_insposE | exact: nbump_insposE].
Qed.

Lemma inspos_leq_exP i : inspred i -> pos <= i.
Proof using HRow.
move=> HlPred.
rewrite -insposE (bump_mininspredE (inspred_any_bump HlPred)).
case (ex_minnP (ex_intro _ _ _)) => pos _ Hpos.
exact: Hpos.
Qed.

Lemma insE : insmin = ins.
Proof using HRow. by rewrite /insmin /ins insposE. Qed.

Lemma insrowE : insmin = insrow Row l.
Proof using HRow.
rewrite /insmin insposE.
elim: Row HRow => [//=| l0 r IHr] Hrow /=.
by case: (ltP l l0) => _ //=; rewrite (IHr (is_row_consK Hrow)).
Qed.

Lemma bump_inspos_lt_size : bump -> pos < size Row.
Proof using HRow.
rewrite -insposE /bump; move=> Hbump; rewrite (bump_mininspredE Hbump).
case (ex_minnP (ex_intro _ _ _)) => pos _ /(_ _ (transf Hbump)).
case: Row Hbump; first by rewrite /= ltxx.
by move=> l0 r _ /=; rewrite ltnS.
Qed.

Lemma nbump_inspos_eq_size : ~~bump -> pos = size Row.
Proof using HRow. by move=> Hnbump; rewrite -insposE nbump_mininspredE. Qed.

Lemma lt_inspos_nth i : i < size Row -> (nth l Row i <= l)%O -> i < pos.
Proof using HRow.
move: HRow; move=> /is_rowP Hrow Hi Hnthi; rewrite -insposE /mininspred /inspred.
case (ltP l (last l Row)) => [Hlt |//=].
case (ex_minnP (ex_intro _ _ _)) => pos /(le_lt_trans Hnthi) H1 _.
move/(_ l pos i): Hrow => H2.
have {H2} /contra : pos <= i -> (nth l Row pos <= nth l Row i)%O.
  by move=> H; apply: H2; apply/andP.
by rewrite -ltnNge -ltNge; apply.
Qed.

Lemma insrow_head_lt : (head l (insrow Row l) <= l)%O.
Proof using. by case: Row => [//=|l0 r] /=; case: (ltP l l0). Qed.

Lemma ins_head_lt : (head l ins <= l)%O.
Proof using HRow. by rewrite -insE insrowE; exact: insrow_head_lt. Qed.

Lemma is_row_ins : is_row ins.
Proof using HRow.
move: HRow; rewrite -insE /insmin /mininspred => Hrow.
case (ltP l (last l Row)) => Hlast.
- case (ex_minnP (ex_intro _ _ _)) => pos.
  by rewrite /inspred; exact: is_row_set_nth.
- by rewrite rcons_set_nth; exact: is_row_rcons.
Qed.

Lemma bump_size_ins : bump -> size ins = size Row.
Proof using HRow.
move/bump_inspos_lt_size; rewrite /insE /insmin size_set_nth maxnC /maxn leqNgt.
by move/negbTE => ->.
Qed.

Lemma nbump_size_ins : ~~bump -> size ins = (size Row).+1.
Proof using HRow.
move/nbump_mininspredE => H.
by rewrite -insE /insmin size_set_nth maxnC /maxn H ltnSn.
Qed.

Lemma nbump_ins_rconsE : ~~bump -> ins = rcons Row l.
Proof using HRow.
by move/nbump_mininspredE => H; rewrite -insE /insmin H rcons_set_nth.
Qed.

Lemma size_ins_inf : (size Row) <= size ins.
Proof using HRow.
rewrite -insE /insmin size_set_nth /maxn.
by case (ltnP mininspred.+1 (size Row)).
Qed.

Lemma size_ins_sup : size ins <= (size Row).+1.
Proof using.
rewrite /ins size_set_nth maxnC /maxn ltnS.
case (leqP (size Row) pos) => [H | _]; last exact: leqnSn.
exact: inspos_leq_size.
Qed.

Lemma ins_leq i : i < size Row -> (nth l ins i <= nth l Row i)%O.
Proof using HRow.
rewrite -insE /insmin nth_set_nth /=.
case eqP => [->|_ _ //].
rewrite /mininspred /inspred; case (ltP l (last l Row)) => [Hcase | Hcase].
- by case (ex_minnP (ex_intro _ _ _)) => pos Hl _ _; exact: ltW.
- by rewrite ltnn.
Qed.

Lemma ins_non_nil : ins != [::].
Proof using. by rewrite /ins; exact: set_nth_non_nil. Qed.

Lemma size_ins_non_0 : 0 < size ins.
Proof using. by move: ins_non_nil; case ins. Qed.

End Insert.


Lemma bump_nil l : bump [::] l = false.
Proof using. by rewrite /bump /= ltxx. Qed.

Lemma bump_tail l0 r l : bump (l0 :: r) l -> (l0 <= l -> bump r l)%O.
Proof using.
rewrite /bump /= => Hbump Hll0.
case: r Hbump => [/= H1 | //=].
by exfalso; have:= lt_le_trans H1 Hll0; rewrite ltxx.
Qed.


(** ** The algorithm *)
Section Schensted.

Implicit Type l : T.
Implicit Type r w s : seq T.

Fixpoint Sch_rev w := if w is l0 :: w' then ins (Sch_rev w') l0 else [::].
Definition Sch w := Sch_rev (rev w).

Lemma Sch_rcons l w : Sch (rcons w l) = ins (Sch w) l.
Proof using. by rewrite /Sch rev_rcons. Qed.

Lemma is_row_Sch w : is_row (Sch w).
Proof using.
by elim/last_ind: w => [//= | w wn IHw]; rewrite Sch_rcons is_row_ins.
Qed.

Lemma Sch_size w : size (Sch w) <= size w.
Proof using.
elim/last_ind: w => [//= | w wn IHw]; rewrite Sch_rcons size_rcons.
exact: (leq_trans (size_ins_sup _ wn)).
Qed.

(** ** Schensted's algorithem specifications *)
Definition subseqrow s w := subseq s w && is_row s.
Definition subseqrow_n s w n := [&& subseq s w , (size s == n) & is_row s].

Theorem Sch_exists w i :
  i < size (Sch w) ->
  exists s : seq T, (last inh s == nth inh (Sch w) i) && subseqrow_n s w i.+1.
Proof using.
rewrite /subseqrow_n.
elim/last_ind: w i => [//=| w wn IHw] i.
rewrite Sch_rcons {2}/ins.
case (altP (i =P (inspos (Sch w) wn))) =>[|Hineq Hileq].
- case: i => [<-|i Hieq ] _.
  + by exists [:: wn] => /=; case (Sch w) => /= [|_ _];
        rewrite -cats1 suffix_subseq; apply/and3P; repeat split.
  + have:= inspos_leq_size (Sch w) wn; rewrite -Hieq.
    case/IHw => {IHw} s => /and4P [/eqP Hlast Hsubs /eqP Hsz Hrow].
    exists (rcons s wn); apply/and4P; repeat split.
    + by rewrite last_rcons nth_set_nth_any eq_refl.
    + by rewrite -subseq_rcons_eq.
    + by rewrite size_rcons Hsz.
    + apply: (is_row_rcons Hrow).
      have Hany : (size s).-1 < size s by rewrite Hsz.
      rewrite -nth_last (set_nth_default inh wn Hany) {Hany} nth_last Hlast.
      have:= inspos_leq_size (Sch w) wn; rewrite -Hieq => Hany.
      rewrite (set_nth_default wn inh Hany).
      by apply: nth_lt_inspos; rewrite -Hieq ltnSn.
- have Hi : (i < size (Sch w)); have HrowSch := is_row_Sch w.
    move: Hineq Hileq; case (boolP (bump (Sch w) wn )) => Hcase.
    + by rewrite (bump_size_ins HrowSch Hcase).
    + rewrite (nbump_inspos_eq_size HrowSch Hcase) (nbump_size_ins HrowSch Hcase).
      by rewrite ltnS ltn_neqAle => -> ->.
  case (IHw _ Hi) => {IHw} s => /and4P [/eqP Hlast Hsubs /eqP Hsz Hrow].
  exists s; apply/and4P; repeat split.
    + by rewrite /ins in Hileq; rewrite nth_set_nth_any (negbTE Hineq) Hi Hlast.
    + apply: (subseq_trans Hsubs); exact: subseq_rcons.
    + by rewrite Hsz.
    + exact Hrow.
Qed.

Theorem Sch_leq_last w s si:
  subseqrow (rcons s si) w ->
  size s < size (Sch w) /\ (nth inh (Sch w) (size s) <= si)%O.
Proof using.
rewrite /subseqrow => /andP [].
elim/last_ind: w s si => [| w wn IHw] s si; first by rewrite subseq0 rcons_nilF.
rewrite Sch_rcons  /=; have HSch := is_row_Sch w.
case (altP (si =P wn)) => [-> {si} | Hsiwn Hsubs Hrow].

(* The subseqence s ends by wn *)
- rewrite -subseq_rcons_eq.
  case/lastP: s => [ _ _ {IHw} | s si Hsubs Hrow].
  (* s = wn *)
  + split; first by rewrite size_ins_non_0.
    have:= size_ins_non_0 (Sch w) wn => Hany.
    rewrite -[size [::]]/(0) (set_nth_default wn inh Hany) nth0; apply: ins_head_lt.
    exact: is_row_Sch.
  (* s = [s] si wn *)
  move/(_ _ _ Hsubs (is_row_rconsK Hrow)): IHw => [] Hszlt Hlt.
  have:= is_row_last Hrow; rewrite last_rcons => Hsiwn.

  case (boolP (bump (Sch w) wn )) => [Hbump | Hnbump].
  (* Wn bump a letter *)
  + have Hszpos: (size s < inspos (Sch w) wn).
      apply: (lt_inspos_nth (is_row_Sch w) Hszlt).
      by rewrite (set_nth_default inh wn Hszlt); exact: (le_trans Hlt Hsiwn).
    rewrite size_rcons (bump_size_ins HSch Hbump); split.
    * exact: (leq_ltn_trans Hszpos (bump_inspos_lt_size HSch Hbump)).
    * rewrite {2}(_: wn = nth inh (ins (Sch w) wn) (inspos (Sch w) wn));
        last by rewrite /ins nth_set_nth_any eq_refl.
      apply (is_rowP _ _ (is_row_ins HSch wn)).
      by rewrite Hszpos size_set_nth leq_max ltnSn.

  (* Insertion add a new [wn] box *)
  + rewrite (nbump_ins_rconsE HSch Hnbump) !size_rcons nth_rcons.
    split; first by [].
    case: (leqP (size s).+2 (size (Sch w))) => Hsz.
    * apply: (@le_trans _ T (last inh (Sch w)) _ wn); first last.
        rewrite -nth_last (set_nth_default wn inh);
          first by rewrite nth_last -notbump.
        by rewrite -{2}(ltn_predK Hsz).
      rewrite -(nth_last inh).
      apply: (is_rowP _ _ HSch).
      have:= Hsz; rewrite -{1}(ltn_predK Hsz) ltnS => -> /=.
      by rewrite -{2}(ltn_predK Hsz); exact: ltnSn.
    * case eqP => [// | Habs].
      exfalso; rewrite ltnS in Hsz; move: Habs => /eqP.
      by rewrite eqn_leq Hsz Hszlt.

(* The subsequence doesn't end by wn *)
- move: Hsubs; rewrite subseq_rcons_neq // => /(IHw _ _)/(_ Hrow) {Hsiwn Hrow}.
  move=> [Hsize Hleq]; split.
  * by apply: (leq_trans Hsize); exact: size_ins_inf.
  * rewrite (set_nth_default wn inh Hsize) in Hleq.
    rewrite (set_nth_default wn inh (leq_trans Hsize (size_ins_inf HSch wn))).
    exact: (le_trans (ins_leq HSch wn Hsize) Hleq).
Qed.

Corollary size_ndec_Sch w s : subseqrow s w -> (size s) <= size (Sch w).
Proof using.
case/lastP: s => [//=| s si].
move/Sch_leq_last => [] H _.
by rewrite size_rcons.
Qed.

Corollary exist_size_Sch w : exists s : seq T, subseqrow_n s w (size (Sch w)).
Proof using.
case/lastP: w => [| w wn]; first by exists [::].
have:= size_ins_non_0 (Sch w) wn; rewrite -Sch_rcons.
case Hn : (size _) => [_ //=| n] _.
have:= ltnSn n; rewrite -{2}Hn => H.
elim (Sch_exists H) => s /andP [] _ Hrsq.
by exists s.
Qed.

End Schensted.


Theorem Sch_max_size (w : seq T) :
  size (Sch w) = \max_(s : subseqs w | is_row s) size s.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- case: (exist_size_Sch w) => s;
    rewrite /subseqrow_n => /and3P [Hsubs /eqP Hsz Hrow].
  pose witness  := Subseqs Hsubs.
  have -> : size (Sch w) = size witness by rewrite /= Hsz.
  exact: (@leq_bigmax_cond _ _ (size \o (@subseqsval _ w)) witness Hrow).
- apply/bigmax_leqP => s Hs.
  by apply: size_ndec_Sch; rewrite /subseqrow Hs andbT; apply: subseqsP s.
Qed.


(** * Robinson-Schensted bumping *)

(** ** bumping a letter *)
Section Bump.

Variable Row : seq T.
Hypothesis HRow : is_row Row.
Variable l : T.

Definition bumped := nth l Row (inspos Row l).
Notation ins := (ins Row l).
Notation inspos := (inspos Row l).
Notation insRow := (insrow Row l).
Notation bump := (bump Row l).

Lemma lt_bumped : bump -> (l < bumped)%O.
Proof using. by move/inspred_inspos. Qed.

Fixpoint bumprow r l : (option T) * (seq T) :=
  if r is l0 :: r then
    if (l < l0)%O then (Some l0, l :: r)
    else let: (lr, rr) := bumprow r l in (lr, l0 :: rr)
  else (None, [:: l]).

Notation bumpRow := (bumprow Row l).

Lemma ins_bumprowE : insRow = bumpRow.2.
Proof using.
elim: Row => [//= | t0 r IHr /=].
case: (ltP l t0) => _ //=.
by move: IHr; case (bumprow r l) => [lr tr] /= ->.
Qed.

Lemma bump_bumprowE : bump -> bumpRow = (Some bumped, ins).
Proof using HRow.
rewrite /bumped -(insE HRow) (insrowE HRow).
elim: Row HRow => [//= | t0 r IHr] Hrow /= Hlast;
  first by rewrite bump_nil in Hlast.
case: (ltP l t0) => //=.
move: Hlast => /bump_tail H{}/H Hlast.
by rewrite (IHr (is_row_consK Hrow) Hlast).
Qed.

Lemma nbump_bumprowE : ~~bump -> bumpRow = (None, ins).
Proof using HRow.
rewrite notbump -(insE HRow) (insrowE HRow).
elim: Row HRow => [//= | t0 r IHr] Hrow Hlast /=.
case: (ltP l t0) => //= Ht0.
- exfalso.
  have:= le_lt_trans (le_trans (head_leq_last_row Hrow) Hlast) Ht0.
  by rewrite ltxx.
- have {}Hlast : (last l r <= l)%O by case: r Hlast {IHr Hrow}.
  by rewrite (IHr (is_row_consK Hrow) Hlast).
Qed.

Lemma head_ins_lt_bumped i : bump -> (head i ins < bumped)%O.
Proof using HRow.
move=> Hbump; have:= is_row_ins HRow l => /is_rowP Hrowins.
rewrite -nth0 (set_nth_default l i (size_ins_non_0 _ _)).
apply: (@le_lt_trans _ T (nth l ins inspos)).
+ apply: Hrowins.
  rewrite /= (bump_size_ins HRow Hbump).
  exact: bump_inspos_lt_size.
+ rewrite /ins nth_set_nth /= eq_refl.
  exact: lt_bumped.
Qed.

(* Unused lemma *)
Lemma bumprow_size :
  let: (lr, tr) := bumpRow in
  (size Row).+1 == (size tr) + if lr is Some _ then 1 else 0.
Proof using.
elim: Row => [//= | t0 r IHr /=].
case: (ltP l t0) => _ /=; first by rewrite -addn1.
by move: IHr; case (bumprow r l) => [lr tr] /= /eqP ->.
Qed.

Lemma bumprow_count p :
  let: (lr, tr) := bumpRow in
  count p Row + (p l) == count p tr + if lr is Some ll then (p ll) else 0.
Proof using.
elim: Row => [| t0 r IHr] /=; first by rewrite !addn0.
case: (ltP l t0) => _ /=.
- by rewrite addnC -addnA eqn_add2l addnC eqn_add2l.
- move: IHr; case (bumprow r l) => [tr lr] /= IHr.
  by rewrite -!addnA eqn_add2l.
Qed.

End Bump.


Lemma bumprow_rcons r l : is_row (rcons r l) -> bumprow r l = (None, rcons r l).
Proof using.
move=> Hrow; have:= is_row_last Hrow; rewrite leNgt => Hnbump.
move/is_row_rconsK: Hrow => Hr.
by rewrite (nbump_bumprowE Hr Hnbump) (nbump_ins_rconsE Hr Hnbump).
Qed.


Section Dominate.

Implicit Type l : T.
Implicit Type r u v : seq T.

Lemma dominate_inspos r1 r0 l :
  is_row r0 -> is_row r1 -> dominate r1 r0 ->
  bump r0 l -> inspos r0 l >= inspos r1 (bumped r0 l).
Proof using.
move=> Hrow0 Hrow1 /dominateP [] Hsz Hdom /= Hbump.
case (ltnP (inspos r0 l) (size r1)) => Hpossz.
- move/(_ _ Hpossz): Hdom; rewrite -/(bumped r0 l) => Hl1.
  apply: (inspos_leq_exP Hrow1).
  by rewrite /inspred /bumped (set_nth_default inh _ Hpossz)
             (set_nth_default inh _ (leq_trans Hpossz Hsz)).
- by apply: (@leq_trans (size r1)); first exact: inspos_leq_size.
Qed.

Lemma bump_dominate r1 r0 l :
  is_row r0 -> is_row r1 -> bump r0 l ->
  dominate r1 r0 -> dominate (ins r1 (bumped r0 l)) (ins r0 l).
Proof using.
move=> Hrow0 Hrow1 Hbump Hdom; have:= Hdom => /dominateP [] Hsize Hlt.
have Hsize' : size (ins r1 (bumped r0 l)) <= size (ins r0 l).
  rewrite (bump_size_ins Hrow0 Hbump) {1}/ins size_set_nth /maxn.
  case (ltnP (inspos r1 (bumped r0 l)).+1 (size r1)) => [//=|_].
  apply: (@leq_ltn_trans (inspos r0 l)); first exact: dominate_inspos.
  exact: bump_inspos_lt_size.
apply/dominateP; split; first exact Hsize'.
move=> i Hi; rewrite (set_nth_default (bumped r0 l) inh Hi)
                     (set_nth_default l inh (leq_trans Hi Hsize')).
rewrite /ins; have:= dominate_inspos Hrow0 Hrow1 Hdom Hbump.
set pos0 := inspos r0 _; set pos1 := inspos r1 _.
move=> Hpos; rewrite !nth_set_nth /=.
case eqP => [Hipos0 | /eqP Hipos0]; case eqP => [Hipos1 | /eqP Hipos1].
- exact: lt_bumped.
- apply: (lt_le_trans (lt_bumped Hbump)); move Hl0 : (bumped r0 l) => l0.
  rewrite -Hipos0 in Hpos => {Hrow0 Hlt Hdom Hsize Hbump Hipos0}.
  rewrite /pos1 in Hipos1 Hpos; rewrite Hl0 in Hipos1 Hi Hpos => {pos1 pos0 Hl0}.
  have:= is_row_ins Hrow1 l0 => /is_rowP Hrowins.
  have {1}-> : l0 = nth l0 (ins r1 l0) (inspos r1 l0)
    by rewrite nth_set_nth /= eq_refl.
  have -> : nth l0 r1 i = nth l0 (ins r1 l0) i
    by rewrite nth_set_nth /= (negbTE Hipos1).
  by apply: Hrowins; rewrite Hpos.
- apply: (@le_lt_trans _ T l); last exact: lt_bumped.
  by subst pos0; apply: nth_lt_inspos; rewrite ltn_neqAle Hipos0 /= Hipos1.
- case (ltnP i (size r1)) => Hsz.
  * rewrite (set_nth_default inh _ Hsz) (set_nth_default inh _ (leq_trans Hsz Hsize)).
    exact: Hlt.
  * exfalso; case (boolP (bump r1 (bumped r0 l))) => [|Hnbump].
    - move/bump_size_ins => H; rewrite (H Hrow1) in Hi.
      by have:= leq_ltn_trans Hsz Hi; rewrite ltnn.
    - have:= Hnbump; move/nbump_ins_rconsE => Heq.
      rewrite (Heq Hrow1) size_rcons ltnS in Hi.
      have {Hsz}Hi : (i == size r1) by rewrite eqn_leq Hi Hsz.
      rewrite /pos1 (nbump_inspos_eq_size Hrow1 Hnbump) in Hipos1.
      by rewrite Hi in Hipos1.
Qed.

Lemma dominateK_inspos r1 r0 l0 :
  is_row r0 -> is_row r1 -> dominate (ins r1 (bumped r0 l0)) (ins r0 l0) ->
  bump r0 l0 -> inspos r0 l0 >= inspos r1 (bumped r0 l0).
Proof using.
move Hl1 : (bumped r0 l0) => l1; rewrite /bumped in Hl1.
move=> Hrow0 Hrow1 /dominateP [] Hsz Hdom /= Hbump.
case (leqP (inspos r1 l1) (inspos r0 l0)) => [//= | Habs].
have Hpos1 := inspos_lt_size_ins r1 l1.
have:= leq_trans Hpos1 Hsz; rewrite (bump_size_ins Hrow0 Hbump) => Hpos0.
move: Hrow0 => /is_rowP Hrow0.
have: inspos r0 l0 <= inspos r1 l1 < size r0 by rewrite (ltnW Habs).
move/(Hrow0 l0); rewrite {Hrow0} Hl1 => H1.
move/(_ _ Hpos1): Hdom.
rewrite (set_nth_default l1 inh Hpos1) (set_nth_default l0 inh (leq_trans Hpos1 Hsz)).
rewrite /ins !nth_set_nth /= (gtn_eqF Habs) eq_refl.
by move/(le_lt_trans H1); rewrite ltxx.
Qed.

Lemma bump_dominateK r1 r0 l0 :
  is_row r0 -> is_row r1 -> bump r0 l0 ->
  dominate (ins r1 (bumped r0 l0)) (ins r0 l0) -> dominate r1 r0.
Proof using.
move=> Hrow0 Hrow1 Hbump0 Hdom; have:= Hdom => /dominateP [] Hsize Hlt.
have:= dominateK_inspos Hrow0 Hrow1 Hdom Hbump0 => Hpos.
move Hl1 : (bumped r0 l0) => l1; rewrite Hl1 in Hdom Hsize Hlt Hpos.
rewrite /bumped in Hl1.
have Hsize' : size r1 <= size r0.
  move: Hsize; rewrite (bump_size_ins Hrow0 Hbump0).
  by apply/leq_trans; exact: size_ins_inf.
apply/dominateP; split; first exact: Hsize'.
move=> i Hi; have Hi' := leq_trans Hi (size_ins_inf Hrow1 l1).
rewrite (set_nth_default l1 inh Hi) (set_nth_default l0 inh (leq_trans Hi Hsize')).
case (altP (i =P inspos r1 l1)) => Hipos1.
- have:= nth_inspos_ins r1 l1; rewrite -Hipos1.
  have:= Hlt i Hi'.
  rewrite (set_nth_default l0 inh (leq_trans Hi' Hsize)) (set_nth_default l1 inh Hi').
  rewrite {1}Hipos1 {1}/ins nth_set_nth {1}Hipos1 /=.
  case (altP (i =P inspos r0 l0)) => [Hipos0 _| Hipos0].
  * rewrite {2}Hipos0 Hl1 => <-; rewrite Hipos1 nth_inspos_ins.
    case (boolP (bump r1 l1)) => Hbump;
      last by move: Hi; rewrite Hipos1 (nbump_inspos_eq_size Hrow1 Hbump) ltnn.
    by have:= inspred_mininspred Hbump; rewrite (insposE Hrow1) /inspred.
  * rewrite -{1}Hipos1 (negbTE Hipos0) nth_inspos_ins => Hlt1 Heqins.
    rewrite -Hipos1 in Hlt1.
    apply: (lt_le_trans Hlt1); rewrite -{1}Heqins.
    exact: ins_leq.
- case (altP (i =P inspos r0 l0)) => [Hipos0 | Hipos0].
  * rewrite Hipos0 Hl1.
    have:= contra (@lt_inspos_nth r1 Hrow1 l1 _ Hi).
    by rewrite -leqNgt -ltNge Hipos0; apply.
  * have:= Hlt _ Hi'.
    rewrite (set_nth_default l0 inh (leq_trans Hi' Hsize)) (set_nth_default l1 inh Hi').
    by rewrite !/ins !nth_set_nth /= (negbTE Hipos0) (negbTE Hipos1).
Qed.

End Dominate.

(** ** The insertion tableau *)
Section Tableaux.

Implicit Type l : T.
Implicit Type r w : seq T.
Implicit Type t : seq (seq T).

Fixpoint instab t l : seq (seq T) :=
  if t is t0 :: t' then
    let: (lr, rr) := bumprow t0 l in
    if lr is Some ll then rr :: (instab t' ll) else rr :: t'
  else [:: [:: l]].

Lemma head_instab (t0 : seq T) t l :
  is_row t0 -> head [::] (instab (t0 :: t) l) = ins t0 l.
Proof using.
move=> Hrow; rewrite -(insE Hrow) (insrowE Hrow).
by rewrite ins_bumprowE /=; case (bumprow t0 l) => [[l'|]] b.
Qed.

Theorem is_tableau_instab t l : is_tableau t -> is_tableau (instab t l).
Proof using.
elim: t l => [l _ //=| t0 t IHt l Htab].
move: Htab => /= /and4P [] Ht0 Hrow0 Hdom Htab.
case (boolP (bump t0 l)) => [Hbump0 | Hnbump0].
- rewrite /= (bump_bumprowE Hrow0 Hbump0).
  case: t IHt Hdom Htab => [_ _ _ | t1 t IHt Hdom Htab] /=.
  * rewrite ins_non_nil (is_row_ins Hrow0) andbT /=.
    rewrite -[[:: bumped t0 l]]/(ins [::] ( bumped t0 l)).
    exact: bump_dominate.
  * have Hrow1 := tableau_is_row Htab.
    rewrite (head_instab _ _ Hrow1).
    move/(_ (bumped t0 l) Htab) : IHt => /= ->.
    rewrite ins_non_nil (is_row_ins Hrow0) /= andbT.
    exact: bump_dominate.
- rewrite /= (nbump_bumprowE Hrow0 Hnbump0) /= Htab.
  rewrite ins_non_nil (is_row_ins Hrow0) /= andbT.
  by rewrite (nbump_ins_rconsE Hrow0 Hnbump0); exact: dominate_rcons.
Qed.

Lemma instab_non_nil t l : instab t l != [::].
Proof using.
by case: t => [//=| t0 t /=]; case (bumprow t0 l) => [[ll|]] l0.
Qed.

Fixpoint RS_rev w : seq (seq T) :=
  if w is w0 :: wr then instab (RS_rev wr) w0 else [::].
Definition RS w := RS_rev (rev w).

Theorem is_tableau_RS w : is_tableau (RS w).
Proof using.
elim/last_ind: w => [//= | w l0 /=].
rewrite /RS rev_rcons /=.
exact: is_tableau_instab.
Qed.

End Tableaux.



(** ** Inverting a bump *)
Section InverseBump.

Implicit Type a b l : T.
Implicit Type r s w : seq T.
Implicit Type t : seq (seq T).

Definition invbump b s := ((head b s) < b)%O.

Fixpoint invbumprow b s : (seq T) * T :=
  if s is l0 :: s then
    if (b <= head b s)%O
    then (b :: s, l0)
    else let: (rr, lr) := invbumprow b s in (l0 :: rr, lr)
  else (* unused case *) ([::], b).

Definition invins b s := (invbumprow b s).1.
Definition invbumped b s := (invbumprow b s).2.

Lemma head_lt_invins b s i :
  s != [::] -> invbump b s -> (head i s <= head i (invins b s))%O.
Proof using.
rewrite /invins /invbump; case: s => [//=| l0 s /= _].
case (invbumprow b s) => r a.
case: (leP b (head b s)) => _ //=.
exact: ltW.
Qed.

Lemma is_row_invins b s : is_row s -> is_row (invins b s).
Proof using.
rewrite /invins.
elim: s => [_ //=|l0 s IHs] /= /is_row_cons [] Hhead Hrow.
case: (leP b (head b s)) => [| Hb] /=;
  first by move: Hrow; case s => [//= | s0 s'] /= -> ->.
move/(_ Hrow): IHs.
case H : (invbumprow b s) => [[//=|r0 r] a] /= ->; rewrite andbT.
apply: (le_trans Hhead).
have -> : r0 = head l0 (invins b s) by rewrite /invins H.
case (altP (s =P [::])) => [-> //=|Hnnil].
apply: (head_lt_invins _ Hnnil).
by rewrite /invbump Hb.
Qed.

Lemma head_leq_invbumped b s :
  s != [::] -> is_row s -> (head inh s <= (invbumped b s))%O.
Proof using.
rewrite /invbumped.
elim: s => [_ //=|l0 s IHs] /= _ /is_row_cons [] Hhead Hrow.
case (altP (s =P [::])) => [-> /=| Hnnil]; first by rewrite lexx.
rewrite (set_head_default inh _ Hnnil).
case: (leP b (head inh s)) => [/= |_]; first by rewrite lexx.
move: {IHs} (IHs Hnnil Hrow).
case H : (invbumprow b s) => [r a] /= Hb.
apply: (le_trans Hhead).
by rewrite (set_head_default inh _ Hnnil).
Qed.

Lemma invbumprowK r a :
  is_row r -> bump r a ->
  (invbumprow (bumped r a) (ins r a)) = (r, a).
Proof using.
rewrite /bump; move=> Hrow Hbump; have:= bump_bumprowE Hrow Hbump.
elim: r Hrow Hbump => [_ /= |l0 r IHr /= /is_row_cons [] Hl0 Hrow Hbump];
  first by rewrite ltxx.
case: (ltP a l0) => Hal0.
- by move=> [] <- <- /=; rewrite Hl0.
- have {}Hbump: (a < last a r)%O.
    case: r {IHr Hl0 Hrow} Hbump Hal0 => [/=|//=]; first exact: lt_le_trans.
  have H := bump_bumprowE Hrow Hbump.
  rewrite H => [] [] <- <- /=.
  have:= head_ins_lt_bumped Hrow (bumped r a) Hbump; rewrite ltNge => /negbTE ->.
  by rewrite (IHr Hrow Hbump H).
Qed.

Lemma bumprowinvK b s :
  s != [::] -> is_row s -> invbump b s ->
  (bumprow (invins b s) (invbumped b s)) = (Some b, s).
Proof using.
rewrite /invbump /invins /invbumped.
elim: s => [//= | s0 s IHs] /= _ /is_row_cons [] Hhead Hrows Hs0.
case (altP (s =P [::])) => [-> /=| Hnnil]; first by rewrite lexx /= Hs0.
rewrite (set_head_default s0 _ Hnnil).
case: (leP b (head s0 s)) => [/=|]; first by rewrite Hs0.
rewrite (set_head_default b s0 Hnnil).
move/(IHs Hnnil Hrows) {IHs}.
case H : (invbumprow b s) => [r a] /= Hb; rewrite Hb.
suff: (s0 <= a)%O; first by rewrite leNgt => /negbTE ->.
apply: (le_trans Hhead); rewrite (set_head_default inh _ Hnnil).
by have:= head_leq_invbumped b Hnnil Hrows; rewrite /invbumped H /=.
Qed.

(** ** The Robinson-Schensted insertion with recording *)
Fixpoint instabnrow t l : seq (seq T) * nat :=
  if t is t0 :: t then
    let: (lr, rr) := bumprow t0 l
    in if lr is Some ll then
         let: (tres, nres) := instabnrow t ll
         in (rr :: tres, nres.+1)
       else (rr :: t, 0)
  else ([:: [:: l]], 0).

Lemma instabnrowE t l : (instabnrow t l).1 = instab t l.
Proof using.
elim: t l => [//=| t0 t IHt] l /=.
case (bumprow t0 l) => [[ll|//=] rr].
by move/(_ ll): IHt; case (instabnrow t ll) => [tres nres] /= ->.
Qed.

Lemma shape_instabnrow t l :
  is_tableau t ->
  let: (tr, nrow) := instabnrow t l in shape tr = incr_nth (shape t) nrow.
Proof using.
case H : (instabnrow t l) => [tr nrow] Htab.
elim: t Htab l tr nrow H => [/= _| t0 t IHt /= /and4P [] _ Hrow _ Htab] l tr nrow /=;
    first by move=> [] <- <-.
case (boolP (bump t0 l)) => [Hbump | Hnbump].
- rewrite (bump_bumprowE Hrow Hbump).
  case: nrow => [|nrow]; first by case (instabnrow t (bumped t0 l)).
  case Hins: (instabnrow t (bumped t0 l)) => [tres nres] [] <- <- /=.
  move/(_ Htab (bumped t0 l) tres nres Hins): IHt => ->.
  by rewrite (bump_size_ins Hrow Hbump).
- have:= nbump_bumprowE Hrow Hnbump => -> [] <- <- /=.
  by rewrite (nbump_size_ins Hrow Hnbump).
Qed.

End InverseBump.


Section Inverse.

Implicit Type a b l : T.
Implicit Type r s w : seq T.
Implicit Type t u : seq (seq T).

(* unused lemma *)
Lemma is_rem_corner_instabnrow t l : is_tableau t ->
    let: (res, nrow) := instabnrow t l in is_rem_corner (shape res) nrow.
Proof using.
rewrite /is_rem_corner.
elim: t l => [l _|t0 t IHt l /and4P [Hnnil Hrow /dominateP [Hdom _] Htab]] //=.
case (boolP (bump t0 l)) => [Hbump | Hnbump].
- rewrite (bump_bumprowE Hrow Hbump) /=.
  move/(_ (bumped t0 l) Htab): IHt.
  by case (instabnrow t (bumped t0 l)) => [res nrow].
- rewrite (nbump_bumprowE Hrow Hnbump) (nbump_ins_rconsE Hrow Hnbump) /= size_rcons.
  by move: Hdom; rewrite -nth0 /=; case t.
Qed.

(** ** Invertion a Robinson-Schensted step *)
Fixpoint invinstabnrow t nrow : seq (seq T) * T :=
  if t is t0 :: t
  then if nrow is nrow.+1
       then let: (tr, lr) := invinstabnrow t nrow in
            let: (t0r, l0r) := invbumprow lr t0 in
            (t0r :: tr, l0r)
       else if t0 is l0 :: t0
            then if t0 == [::]
                 then (t, l0)
                 else ((belast l0 t0) :: t, last l0 t0)
            else (* unused case *) ([::], inh)
  else (* unused case *) ([::], inh).

Theorem invinstabnrowK t l :
  is_tableau t -> invinstabnrow (instab t l) (instabnrow t l).2 = (t, l).
Proof using.
elim: t l => [l //=| t0 t IHt] l /= /and4P [] Hnnil Hrow0 Hdom Htab.
case (boolP (bump t0 l)) => [Hbump | Hnbump].
- rewrite (bump_bumprowE Hrow0 Hbump) /=.
  move/(_ (bumped t0 l) Htab): IHt.
  case Hres : (instabnrow t (bumped t0 l)) => [tres nres] /= ->.
  by rewrite (invbumprowK Hrow0 Hbump).
- rewrite (nbump_bumprowE Hrow0 Hnbump) (nbump_ins_rconsE Hrow0 Hnbump) /=.
  case Hres : (rcons t0 l) => [| ares tres]; first by move: Hres; case t0.
  case eqP => Htres.
  * exfalso; move: Hnnil; have:= eq_refl (size (rcons t0 l)).
    by rewrite {2}Hres Htres size_rcons /= => /nilP ->.
  * have -> : (belast ares tres) = t0
      by have:= eq_refl (belast l (rcons t0 l));
               rewrite {2}belast_rcons Hres /= => /eqP [].
    by have -> : (last ares tres) = l
      by have:= eq_refl (last l (rcons t0 l));
               rewrite {2}last_rcons Hres /= => /eqP.
Qed.

Lemma invbump_geq_head t tin l nrow :
  t != [::] -> is_tableau t -> invinstabnrow t nrow = (tin, l) ->
  (l >= head l (head [::] t))%O.
Proof using.
case: t => [//= | r0 t] /= _ /and4P [] Hnnil0 Hrow0 _ _.
case: nrow => [| nrow].
- case: r0 Hnnil0 Hrow0 => [//= | l0 [| l1 tl0]] _ H /= [] _ <- //=.
  exact: head_leq_last_row H.
- case (invinstabnrow t nrow) => [tr lr].
  have:= head_leq_invbumped lr Hnnil0 Hrow0.
  rewrite /invbumped.
  case (invbumprow lr r0) => [t0r l0r] /= H [] _ <-.
  by rewrite (set_head_default inh l0r Hnnil0).
Qed.

Lemma invbump_dom r0 t tin l nrow :
  t != [::] -> is_tableau t -> invinstabnrow t nrow = (tin, l) ->
  r0 != [::] -> dominate (head [::] t) r0 -> invbump l r0.
Proof using.
rewrite /invbump => Htnnil Ht /(invbump_geq_head Htnnil Ht).
case: t Htnnil Ht => [//= | r1 t] /= _ /and4P [] Hnnil1 _ _ _.
case: r1 Hnnil1 => [//= | l1 r1 ] /= _ Hl1.
case: r0 => [//= | l0 r0 ] /= _ /dominateP [ ] _ /(_ 0 (ltn0Sn _)) => /= Hl0.
exact: lt_le_trans Hl0 Hl1.
Qed.

Theorem instabnrowinvK t nrow :
  is_tableau t -> t != [::] -> is_rem_corner (shape t) nrow ->
  let: (tin, l) := invinstabnrow t nrow in (instabnrow tin l) = (t, nrow).
Proof using.
elim: t nrow => [//= | t0 t IHt] nrow /= /and4P [] Hnnil0 Hrow0 Hdom Htab _.
rewrite /is_rem_corner.
case: nrow => [{IHt} /= Hcorn | nrow Hcorn].
+ case: t0 Hnnil0 Hrow0 Hdom Hcorn => [//= | l0 t0 _].
  case eqP => [/= -> _ _ | Hnnil0 Hrow0 _ _].
  * case: t Htab => [//= |t1 t] /= /and4P [] Ht _ _ _ Hsz.
    by exfalso; move: Ht Hsz; case t1.
  * elim/last_ind: t0 Hnnil0 Hrow0 => [//= | tt0 ln IHtt0] _ Hrow0.
    (* t0 = l0 :: [tt0] :: ln *)
    have:= head_leq_last_row Hrow0.
    rewrite belast_rcons last_rcons /= leNgt => /negbTE ->.
    move: Hrow0 => /= /is_row_cons [] _ Hrow0.
    by rewrite (bumprow_rcons Hrow0).
+ have Hnnil : (t != [::]) by move: Hcorn; case t => //=; rewrite nth_nil.
  move/(_ nrow Htab Hnnil Hcorn): IHt => {Hcorn} /=.
  case H: (invinstabnrow t nrow) => [tin l].
  have Hinvbump: (invbump l t0) by apply: (@invbump_dom t0 t tin l nrow).
  have:= bumprowinvK Hnnil0 Hrow0 Hinvbump.
  rewrite /invins /invbumped.
  by case (invbumprow l t0) => [t0r l0r] /= -> ->.
Qed.

(** * Robinson-Schensted correspondence *)

(** ** The Robinson-Schensted map *)
Fixpoint RSmap_rev w : (seq (seq T)) * (seq nat) :=
  if w is w0 :: wtl
  then let: (t, rows) := RSmap_rev wtl in
       let: (tr, nrow) := instabnrow t w0 in
       (tr, nrow :: rows)
  else ([::], [::]).
Definition RSmap w := RSmap_rev (rev w).

Lemma RSmapE w : (RSmap w).1 = RS w.
Proof using.
elim/last_ind: w => [//= | w wn /=]; rewrite /RSmap /RS rev_rcons /= -instabnrowE.
case: (RSmap_rev (rev w)) => [t rows] /= ->.
by case: (instabnrow (RS_rev (rev w)) wn).
Qed.

Lemma size_RSmap2 w : size ((RSmap w).2) = size w.
Proof using.
elim/last_ind: w => [//= | w wn].
rewrite /RSmap rev_rcons /=.
case: (RSmap_rev (rev w)) => [t rows] /=.
case: (instabnrow t wn) => [tr nrow] /= ->.
by rewrite size_rcons.
Qed.

Lemma is_tableau_RSmap1 w : is_tableau (RSmap w).1.
Proof using. rewrite /RSmap RSmapE; apply: is_tableau_RS. Qed.

Lemma shape_RSmap_eq w : shape (RSmap w).1 = evalseq (RSmap w).2.
Proof using.
elim/last_ind: w => [//=| w l0]; rewrite /RSmap rev_rcons /=.
have:= is_tableau_RSmap1 w; rewrite /RSmap.
case: (RSmap_rev (rev w)) => [t rows] /= Htab.
have:= shape_instabnrow l0 Htab.
case: (instabnrow t l0) => [tr row].
by rewrite /= => -> ->.
Qed.

Lemma is_yam_RSmap2 w : is_yam (RSmap w).2.
Proof using.
elim/last_ind: w => [//=| w l0].
have:= is_part_sht (is_tableau_RSmap1 (rcons w l0)).
rewrite shape_RSmap_eq /RSmap rev_rcons /=.
case Hbij : (RSmap_rev (rev w)) => [t rows] /=.
by case Hins: (instabnrow t l0) => [tr row] /= -> ->.
Qed.

Definition is_RSpair pair :=
  let: (P, Q) := pair in [&& is_tableau (T:=T) P, is_yam Q & (shape P == evalseq Q)].

Theorem RSmap_spec w : is_RSpair (RSmap w).
Proof using.
rewrite /is_RSpair.
case H : (RSmap w) => [P Q]; apply/and3P; repeat split.
- by have:= is_tableau_RSmap1 w; rewrite H.
- by have:= is_yam_RSmap2 w; rewrite H.
- by have:= shape_RSmap_eq w; rewrite H => ->.
Qed.

(** ** The inverse Robinson-Schensted inverse map *)
Fixpoint RSmapinv tab yam :=
  if yam is nrow :: yam'
  then let: (tr, lr) := invinstabnrow tab nrow in
       rcons (RSmapinv tr yam') lr
  else [::].
Definition RSmapinv2 pair := RSmapinv (pair.1) (pair.2).

Theorem RSmapK w : RSmapinv2 (RSmap w) = w.
Proof using.
rewrite /RSmapinv2.
elim/last_ind: w => [//=| w wn]; rewrite /RSmap /RS rev_rcons /=.
have:= is_tableau_RSmap1 w; rewrite /RSmap.
case Hbij : (RSmap_rev (rev w)) => [t rows] /= Htab IHw.
have:= invinstabnrowK wn Htab; rewrite -(instabnrowE t wn).
case (instabnrow t wn) => [tr row] /= ->.
by rewrite IHw.
Qed.

Lemma behead_incr_nth (s : seq nat) nrow :
  behead (incr_nth s nrow.+1) = incr_nth (behead s) nrow.
Proof using. by elim: s => //=; case nrow. Qed.

Lemma size_invins b s : size (invins b s) = (size s).
Proof using.
rewrite /invins; elim: s => [//= | s0 s] /=.
case H : (invbumprow b s) => [r a] /=.
by case: (leP b (head b s)) => _ //= ->.
Qed.

Lemma yam_tail_non_nil (l : nat) (s : seq nat) : is_yam (l.+1 :: s) -> s != [::].
Proof using.
case: s => [|//=] Hyam.
by have:= is_part_eval_yam Hyam; rewrite part_head0F.
Qed.

Lemma shape_instabnrowinv1 t nrow yam :
  is_yam (nrow :: yam) -> shape t == evalseq (nrow :: yam) ->
  shape (invinstabnrow t nrow).1 == evalseq yam.
Proof using.
elim: nrow yam t => [|nrow IHnrow] yam t Hyam.
- case: t => [//= | r0 t]; first by case (evalseq yam).
  rewrite evalseq_cons => Hshape.
  move/is_yam_tl : Hyam => /is_part_eval_yam Hpart.
  case: r0 Hpart Hshape => [/= | l0 [| l1 r0'] ] Hpart Hshape /=.
  * by case: (evalseq yam) Hshape.
  * case: (evalseq yam) Hpart Hshape => //=.
    case => [|//=] l /andP []; rewrite leqn0.
    by move/part_head0F => ->.
  * move: Hshape; rewrite size_belast /=.
    by case (evalseq yam).
- case: t => [//= | r0 t]; first by case (evalseq yam).
  rewrite evalseq_cons => /eqP Hshape.
  have Hsz0 : (size r0) = head 0 (evalseq yam).
    by move: Hshape => /=; case (evalseq yam) => [|s0 s] [] ->.
  move/(congr1 behead): Hshape.
  rewrite behead_incr_nth -evalseq_decr_yam /= => /eqP/IHnrow{IHnrow} Hrec.
  have Hnnilyam := yam_tail_non_nil Hyam.
  move: Hyam => /is_yam_decr; rewrite [decr_yam _]/= => /Hrec{Hrec} /=.
  case Hinv: (invinstabnrow t nrow) => [tin l] /=.
  have:= size_invins l r0; rewrite /invins.
  case Hbump: (invbumprow l r0) => [t0r l0r] /= -> /eqP ->.
  rewrite {Hbump t0r l0r Hinv tin l} evalseq_decr_yam Hsz0 {Hsz0 r0}.
  case: yam Hnnilyam => [//= | a b _].
  have: evalseq (a :: b) != [::] by case: a => [/= | a /=]; case (evalseq b).
  by case (evalseq (a :: b)).
Qed.

Lemma head_tableau_non_nil h t : is_tableau (h :: t) -> h != [::].
Proof using. by move/and4P => [] ->. Qed.

Lemma is_tableau_instabnrowinv1 (s : seq (seq T)) nrow :
  is_tableau s -> is_rem_corner (shape s) nrow -> is_tableau (invinstabnrow s nrow).1.
Proof using.
rewrite /is_rem_corner.
elim: s nrow => [/= |s0 s IHs] nrow; first by case nrow.
case: nrow => [/= | nrow].
- move=> {IHs} /and4P []; case: s0 => [//= | s0h s0t] _.
  case eqP => [-> /= _ _ | /eqP Hnnil]; first by case s.
  case/lastP: s0t Hnnil => [//= | s0t s0l] _; rewrite -!rcons_cons => Hrow.
  rewrite belast_rcons.
  case Ht : s => [/= | s1 s']; first by have:= is_row_rconsK Hrow => /= ->.
  rewrite -Ht /= => Hdom -> Hshape.
  have:= is_row_rconsK Hrow => /= -> /=; rewrite andbT.
  rewrite -rcons_cons in Hdom.
  move: Hdom; rewrite -cats1; apply: dominate_cut.
  by move: Hshape; rewrite Ht /= size_rcons ltnS.
- case Hs : s => [//= | s1 s']; first by rewrite nth_nil.
  rewrite -Hs => /= /and4P [] Hnnil0 Hrows0 Hdom Htabs Hcorn.
  have:= Htabs; rewrite {1}Hs; move/head_tableau_non_nil => Hnnil1.
  move/(_ _ Htabs Hcorn): IHs.
  have Hnnils : (s != [::]) by rewrite Hs.
  move/(instabnrowinvK Htabs Hnnils): Hcorn.
  case Hinv1 : (invinstabnrow s nrow) => [t l0] /= Hins1 Htabt.
  move: {Hnnils Htabs Hinv1} (invbump_geq_head Hnnils Htabs Hinv1).
  have:= instabnrowE t l0; rewrite Hins1 /= Hs => {}Hins1.
  move: Hdom; rewrite {s}Hs /= => Hdom.
  have:= dominate_head Hnnil1 Hdom.
  rewrite (set_head_default l0 inh Hnnil0) (set_head_default l0 inh Hnnil1).
  move=> /lt_le_trans H{}/H /(bumprowinvK Hnnil0 Hrows0).
  have:= is_row_invins l0 Hrows0; have:= size_invins l0 s0;
  rewrite /invins /invbumped.
  case Hinv0: (invbumprow l0 s0) => [t0 l] /= Hsize Hrowt0 Hins0.
  have Hnnilt0: (t0 != [::]) by move: Hnnil0 Hsize; case t0 => [//=|]; case s0.
  rewrite Hnnilt0 Hrowt0 Htabt andbT /=.
  case Ht : t Htabt => [//=| t1 t'] /tableau_is_row Hrowt1 /=.
  have:= @head_instab t1 t' l0 Hrowt1; rewrite -{}Ht -{}Hins1 /= => Hins {t t' s'}.
  have Hbump : (bump t0 l).
    case (boolP (bump t0 l)) => [//= | Hnbump].
    by have:= nbump_bumprowE Hrowt0 Hnbump; rewrite Hins0.
  apply: (bump_dominateK Hrowt0 Hrowt1 Hbump).
  have:= bump_bumprowE Hrowt0 Hbump.
  by rewrite /bumped Hins0 => [] [] <- <-; rewrite -Hins.
Qed.

Theorem RSmapinv2K pair : is_RSpair pair -> RSmap (RSmapinv2 pair) = pair.
Proof using.
rewrite /is_RSpair /RSmap /RSmapinv2; case: pair => [tab yam] /and3P [].
elim: yam tab => [[] //= _ _ | row yam IHyam] tab Htab Hyam Hshape /=.
have:= is_rem_corner_yam Hyam; rewrite -(eqP Hshape) => Hcorn.
have Hnnil : (tab != [::]).
  move: Hshape; case tab => //= /eqP /(congr1 size).
  rewrite /= size_incr_nth.
  move: (size (evalseq yam)) => n.
  by case (ltnP row n) => //= /ltn_predK <-.
have:= instabnrowinvK Htab Hnnil Hcorn.
have:= is_tableau_instabnrowinv1 Htab Hcorn.
have:= shape_instabnrowinv1 Hyam Hshape.
case Hinvins: (invinstabnrow tab row) => [tin l] /= Hshapetin Htabtin.
rewrite rev_rcons /=.
move: Hyam => /= /andP [] Hincr Hyam.
by have:= IHyam tin Htabtin Hyam Hshapetin => /= -> ->.
Qed.

End Inverse.

(** ** Statistics preserved by the Robinson-Schensted map *)
Section Statistics.

Implicit Type t : seq (seq T).

Lemma size_instab t l : is_tableau t -> size_tab (instab t l) = (size_tab t).+1.
Proof using.
rewrite /size_tab -instabnrowE => /(shape_instabnrow l).
case (instabnrow t l) => [tr row] /= -> {tr l}.
by rewrite sumn_incr_nth.
Qed.

Theorem size_RS w : size_tab (RS w) = size w.
Proof using.
elim/last_ind: w => [//= | w0 w].
rewrite /RS rev_rcons /= -[(RS_rev (rev w0))]/(RS w0).
by rewrite (size_instab _ (is_tableau_RS _)) size_rcons => ->.
Qed.

Lemma count_instab t l p :
  is_tableau t -> count p (to_word (instab t l)) = (p l) + count p (to_word t).
Proof using.
elim: t l => [//= _ | r t IHt] l /= /and4P [] _ _ _ Htab.
have:= bumprow_count r l p.
case (bumprow r l) => [[ll|] lr] /= /eqP Hbump; rewrite addnC in Hbump;
  rewrite !to_word_cons !count_cat [_ + (count p r)]addnC addnA Hbump.
- by rewrite (IHt ll Htab) -addnA addnC -addnA addnC.
- by rewrite addn0 addnC.
Qed.

Theorem count_RS w p : count p w = count p (to_word (RS w)).
Proof using.
elim/last_ind: w => [//= | w0 w]; rewrite /RS !rev_rcons /= -[(RS_rev (rev w0))]/(RS w0).
rewrite (count_instab _ _ (is_tableau_RS _)) => <-.
by rewrite -[rcons _ _](revK) rev_rcons count_rev /= count_rev.
Qed.

Theorem perm_RS w : perm_eq w (to_word (RS w)).
Proof using. by apply/seq.permP => l; exact: count_RS. Qed.

End Statistics.

(** ** Sigma types and bijections *)
Section Bijection.

Notation Pair := (seq (seq T) * seq nat : Type).

Structure rspair : predArgType := RSpair { pyampair :> Pair; _ : is_RSpair pyampair }.

Canonical rspair_subType := Eval hnf in [subType for pyampair].
Definition rspair_eqMixin := Eval hnf in [eqMixin of rspair by <:].
Canonical rspair_eqType := Eval hnf in EqType rspair rspair_eqMixin.
(*  Definition rspair_choiceMixin := [choiceMixin of rspair by <:].
Canonical rspair_choiceType :=
  Eval hnf in ChoiceType rspair rspair_choiceMixin.
*)

Lemma pyampair_inj : injective pyampair. Proof using. exact: val_inj. Qed.

Definition RSbij w := RSpair (RSmap_spec w).
Definition RSbijinv (ps : rspair) := RSmapinv2 ps.

Lemma bijRS : bijective RSbij.
Proof using.
split with (g := RSbijinv); rewrite /RSbij /RSbijinv.
- by move=> w /=; rewrite (RSmapK w).
- by move=> [pq H]; apply: pyampair_inj => /=; exact (RSmapinv2K H).
Qed.

End Bijection.

(** ** Robinson-Schensted classes *)
Section Classes.

Definition RSclass := [fun tab =>
[seq RSmapinv2 (tab, y) | y <- enum_yameval (shape tab)] ].

Lemma RSclassP tab : is_tableau tab -> all (fun w => RS w == tab) (RSclass tab).
Proof using.
move=> Htab /=; apply/allP => w /mapP [] Q.
move /(allP (enum_yamevalP (is_part_sht Htab))).
rewrite /is_yam_of_eval => /andP [] Hyam /eqP Hsh -> {w}.
by rewrite -RSmapE RSmapinv2K //= Htab Hyam Hsh /=.
Qed.

Lemma RSclass_countE w : count_mem w (RSclass (RS w)) = 1.
Proof using.
rewrite count_map.
rewrite (eq_in_count (a2 := pred1 ((RSmap w).2))); first last.
  move=> y /= /(allP (enum_yamevalP (is_part_sht (is_tableau_RS _)))).
  rewrite /is_yam_of_eval => /andP [] Hyam /eqP Hsh.
  apply/idP/idP => /eqP H.
  - by rewrite -{}H RSmapinv2K //= (is_tableau_RS _) Hyam Hsh /=.
  - rewrite {}H -RSmapE.
    have -> : ((RSmap w).1, (RSmap w).2) = RSmap w by case RSmap.
    by rewrite RSmapK.
apply: (enum_yameval_countE (is_part_sht (is_tableau_RS _))).
rewrite /is_yam_of_eval -shape_RSmap_eq RSmapE eq_refl andbT.
exact: is_yam_RSmap2.
Qed.

Lemma mem_RSclass w : w \in (RSclass (RS w)).
Proof using. apply negbNE; apply/count_memPn. by rewrite RSclass_countE. Qed.

Lemma RSclassE tab w :
is_tableau tab -> w \in RSclass tab = (RS w == tab).
Proof using.
move=> Htab /=; apply/idP/idP.
- by move: Htab=> /RSclassP/allP H{}/H.
- move/eqP => Hw.
  apply/mapP; exists (RSmap w).2.
  + apply/count_memPn.
    rewrite (enum_yameval_countE (is_part_sht Htab)) //=.
    rewrite /is_yam_of_eval is_yam_RSmap2 /=.
    by rewrite -shape_RSmap_eq RSmapE Hw.
  + rewrite -Hw -RSmapE.
    rewrite (_ : ((RSmap w).1, (RSmap w).2) = RSmap w); last by case RSmap.
    by rewrite RSmapK.
Qed.

End Classes.

End NonEmpty.

(** * The Robinson-Schensted map with standard recording tableau *)
Lemma RSperm n (p : 'S_n) : is_stdtab (RS (wordperm p)).
Proof.
rewrite /is_stdtab; apply/andP; split; first exact: is_tableau_RS.
apply: (perm_std (wordperm_std p)).
by rewrite perm_sym; apply: (perm_RS (wordperm p)).
Qed.

Lemma RSstdE (p : seq nat) : is_stdtab (RS p) = is_std p.
Proof.
rewrite /is_stdtab is_tableau_RS /=.
by apply/idP/idP => Hstd; apply: (perm_std Hstd);
  last rewrite perm_sym; apply: perm_RS.
Qed.

Section QTableau.
Variables (disp : unit) (T : inhOrderType disp).

Notation TabPair := (seq (seq T) * seq (seq nat) : Type).

Definition is_RStabpair (pair : TabPair) :=
  let: (P, Q) := pair in [&& is_tableau P, is_stdtab Q & (shape P == shape Q)].

Structure rstabpair : predArgType :=
  RSTabPair { pqpair :> TabPair; _ : is_RStabpair pqpair }.

Canonical rstabpair_subType := Eval hnf in [subType for pqpair].
Definition rstabpair_eqMixin := Eval hnf in [eqMixin of rstabpair by <:].
Canonical rstabpair_eqType := Eval hnf in EqType rstabpair rstabpair_eqMixin.

Lemma pqpair_inj : injective pqpair. Proof using. exact: val_inj. Qed.

Definition RStabmap (w : seq T) := let (p, q) := (RSmap w) in (p, stdtab_of_yam q).

Lemma RStabmapE (w : seq T) : (RStabmap w).1 = RS w.
Proof using. by rewrite /RStabmap -RSmapE; case RSmap. Qed.

Theorem RStabmap_spec w : is_RStabpair (RStabmap w).
Proof using.
have:= RSmap_spec w; rewrite /is_RStabpair /is_RSpair /RStabmap.
case H : (RSmap w) => [P Q] /and3P [] -> /stdtab_of_yamP -> /eqP -> /=.
by rewrite shape_stdtab_of_yam.
Qed.

Lemma shape_RStabmapE (w : seq T) : shape (RStabmap w).1 = shape (RStabmap w).2.
Proof using.
have:= RStabmap_spec w; rewrite /is_RStabpair.
by case: (RStabmap w) => [P Q] /and3P [] /= _ _ /eqP.
Qed.

Lemma is_stdtab_RStabmap2 (w : seq T) : is_stdtab (RStabmap w).2.
Proof using.
have:= RStabmap_spec w; rewrite /is_RStabpair.
by case: (RStabmap w) => [P Q] /and3P [] /=.
Qed.

Definition RStab w := RSTabPair (RStabmap_spec w).
Definition RStabinv (pair : rstabpair) :=
  let: (P, Q) := pqpair pair in RSmapinv2 (P, yam_of_stdtab Q).

Lemma RStabK : cancel RStab RStabinv.
Proof using.
rewrite /RStab /RStabinv /RStabmap.
move=> w /=; have:= is_yam_RSmap2 w.
case H : (RSmap w) => [P Q] /= Hyam.
by rewrite stdtab_of_yamK; first by rewrite -H (RSmapK w).
Qed.
Lemma RStabinvK : cancel RStabinv RStab.
Proof using.
rewrite /RStab /RStabinv /RStabmap.
move=> [[P Q] H] /=; apply: pqpair_inj => /=.
move: H; rewrite /is_RStabpair => /and3P [] Htab Hstdtab Hshape //=.
rewrite RSmapinv2K.
+ by rewrite (yam_of_stdtabK Hstdtab).
+ by rewrite /is_RSpair Htab yam_of_stdtabP //= shape_yam_of_stdtab.
Qed.
Lemma bijRStab : bijective RStab.
Proof using.
by split with (g := RStabinv); [exact: RStabK | exact: RStabinvK].
Qed.

End QTableau.



Section Tests.

Goal (insrow [:: 1; 1; 2; 3; 5] 2) = [:: 1; 1; 2; 2; 5].
Proof. by compute. Qed.

Goal (insrow [:: 1; 1; 2; 3; 5] 2) = [:: 1; 1; 2; 2; 5].
Proof. by compute. Qed.

Goal (ins [:: 1; 1; 2; 3; 5] 2) = [:: 1; 1; 2; 2; 5].
Proof. by compute. Qed.

Goal (Sch [:: 2; 5; 1; 6; 4; 3]) = [:: 1; 3; 6].
Proof. by compute. Qed.

Goal (RS [:: 2; 5; 1; 6; 4; 3]) = [:: [:: 1; 3; 6]; [:: 2; 4]; [:: 5]].
Proof. by compute. Qed.

Goal (to_word (RS [:: 2; 5; 1; 6; 4; 3])) = [:: 5; 2; 4; 1; 3; 6].
Proof. by compute. Qed.

Goal is_tableau (RS [:: 2; 5; 1; 6; 4; 3]).
Proof. by compute. Qed.

Goal (invbumprow 3 [:: 1; 1; 2; 2; 5]) = ([:: 1; 1; 2; 3; 5], 2).
Proof. by compute. Qed.

Goal (invbumprow 3 [:: 1; 1; 2; 2; 3]) = ([:: 1; 1; 2; 3; 3], 2).
Proof. by compute. Qed.

Goal instabnrow [:: [:: 1; 3; 6]; [:: 2; 4];    [:: 5]] 3 =
               ([:: [:: 1; 3; 3]; [:: 2; 4; 6]; [:: 5]], 1).
Proof. by compute. Qed.

Goal invinstabnrow [:: [:: 1; 3; 3]; [:: 2; 4; 6]; [:: 5]] 1  =
                  ([:: [:: 1; 3; 6]; [:: 2; 4];    [:: 5]], 3).
Proof. by compute. Qed.

Goal is_part [:: 0] = false.
Proof. by compute. Qed.

Goal evalseq [::] = [::].
Proof. by compute. Qed.

Goal evalseq [:: 0; 1; 2; 0; 1; 3] = [:: 2; 2; 1; 1].
Proof. by compute. Qed.

Goal (RSmapinv2 (RSmap [:: 4; 1; 2; 1; 3; 2])) = [:: 4; 1; 2; 1; 3; 2].
Proof. by compute. Qed.

End Tests.


