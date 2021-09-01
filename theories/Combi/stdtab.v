(** * Combi.Combi.stdtab : Standard Tableaux *)
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
(** * Standard Tableaux

We define the following notions:

- [append_nth t b i] == [t] with [b] appended to its [i]-th row

- [is_stdtab t] == [t] is a *standard tableau* that is a tableau whose
            row reading is a standard word
- [last_big t b] == the index of the first row of [t] which ends with [b]
- [remn t] == remove the largest entry ie [n] from a standard tableau of size [n]
- [conj_tab t] == the conjugate standard tableau of [t] (this is indeed a tableau
            when [t] is itself a standard tableau.

Bijection between Yamanouchi words and standard tableau

- [stdtab_of_yam y] == the standard tableau associated to [y]
- [yam_of_stdtab t] == the Yamanouchi words associated to [t]

Sigma type for standard tableaux:

- [is_stdtab_of_shape sh] == a predicate for standard tableau of shape [sh].
- [stdtabsh sh] == a sigma type for [is_stdtab_of_shape sh] where [sh] is an
             integer partition (of type [intpart]). This is canonically a
             [finType].

- [is_stdtab_of_n n] == a predicate for standard tableau of size [n]
- [stdtabn n] == a sigma type for [is_stdtab_of_n n].  This is canonically a
             [finType].

- [shape_deg t] == if t is of type [stdtabn n], the shape of [t] in the
             sigma type ['P_n]

- [hyper_stdtabsh sh] == the hyperstandard tableau of shape [sh : intpart],
             that is the tableau obtained by filling the rows with consecutive
             numbers, from bottom to top (in French conventions)

- [conj_stdtabn t] == the conjugate of [t : stdtabn n] in type [stdtabn n]
- [conj_stdtabsh t] == the conjugate of [t : stdtabsh sh]
             in type [stdtabsh (conj_intpart sh)]


Among the main results are the fact that [stdtab_of_yam] and [yam_of_stdtab]
are two converse bijections. That is:

- [Lemma stdtab_of_yamP y : is_yam y -> is_stdtab (stdtab_of_yam y).]

- [Theorem stdtab_of_yamK y : is_yam y -> yam_of_stdtab (stdtab_of_yam y) = y.]

- [Lemma yam_of_stdtabP t : is_stdtab t -> is_yam (yam_of_stdtab t).]

- [Theorem yam_of_stdtabK t : is_stdtab t -> stdtab_of_yam (yam_of_stdtab t) =
t.]

Moreover, these bijections preserve the shape and therefore the size:

- [Lemma shape_stdtab_of_yam y : shape (stdtab_of_yam y) = evalseq y.]

- [Lemma shape_yam_of_stdtab t : is_stdtab t -> evalseq (yam_of_stdtab t) =
shape t.]

- [Lemma size_stdtab_of_yam y : size_tab (stdtab_of_yam y) = size y.]

- [Lemma size_yam_of_stdtab t : is_stdtab t -> size (yam_of_stdtab t) = size_tab
t.]

                                                                              *)
(******************************************************************************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype finfun fintype choice.
From mathcomp Require Import seq tuple order finset perm fingroup.
Require Import tools combclass partition Yamanouchi ordtype std tableau.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.


(** ** Appending on the n-th row *)
Section AppendNth.

Variables (disp :unit) (T : inhOrderType disp).
Implicit Type b : T.
Implicit Type t : seq (seq T).

Definition append_nth t b i := set_nth [::] t i (rcons (nth [::] t i) b).

Lemma perm_append_nth t x pos :
  perm_eq (to_word (append_nth t x pos)) (x :: to_word t).
Proof using.
rewrite /append_nth; elim: t pos => [//= | t0 t IHt] /=.
- elim => [//= | pos IHpos].
  move: IHpos; rewrite /= to_word_cons cats0.
  by rewrite nth_default //= set_nth_nil.
- case => [//= | pos].
  + rewrite !to_word_cons -cats1 -[x :: (_ ++ _)]cat1s.
    rewrite [flatten _ ++ _ ++ _]catA.
    by apply: permEl; apply: perm_catC.
  + move/(_ pos) : IHt; rewrite /= !to_word_cons.
    by rewrite -/((x :: to_word t) ++ t0) perm_cat2r.
Qed.

Lemma shape_append_nth t b i : shape (append_nth t b i) = incr_nth (shape t) i.
Proof using.
rewrite /shape /=; apply: (@eq_from_nth _ 0).
- rewrite size_map size_set_nth size_incr_nth size_map /maxn.
  by case: (ltngtP i.+1 (size t)).
- move=> j Hi.
  rewrite nth_incr_nth (nth_map [::]) /=; last by move: Hi; rewrite size_map.
  rewrite nth_set_nth /= eq_sym.
  have -> : nth 0 [seq size i | i <- t] j = size (nth [::] t j).
    case: (ltnP j (size t)) => Hcase.
    + by rewrite (nth_map [::] _ _ Hcase).
    + by rewrite (nth_default _ Hcase) nth_default; last by rewrite size_map.
  case eqP => [->|].
  + by rewrite size_rcons add1n.
  + by rewrite add0n.
Qed.

Lemma size_append_nth t b i : size_tab (append_nth t b i) = (size_tab t).+1.
Proof using. by rewrite /size_tab shape_append_nth sumn_incr_nth. Qed.

Lemma get_tab_append_nth (t : seq (seq T)) l i r c :
  get_tab (append_nth t l i) (r, c) =
  if (r == i) && (c == nth 0 (shape t) i) then l else get_tab t (r, c).
Proof using.
rewrite /get_tab /append_nth nth_set_nth /=.
case: (altP (r =P i)) => [-> | //=] /=.
rewrite nth_rcons nth_shape.
case: (ltnP c (size (nth [::] t i))) => Hc; first by rewrite (ltn_eqF Hc).
case: (altP (c =P (size (nth [::] t i)))) => [// | Hc'].
by rewrite nth_default.
Qed.

(** ** Finding the largest entry *)
Fixpoint last_big t b :=
  if t is t0 :: t' then
    if last b t0 == b then 0
    else (last_big t' b).+1
  else 0.

Lemma allLeq_to_word_hd r t b : allLeq (to_word (r :: t)) b -> allLeq r b.
Proof using. by rewrite to_word_cons allLeq_catE => /andP []. Qed.
Lemma allLeq_to_word_tl r t b : allLeq (to_word (r :: t)) b -> allLeq (to_word t) b.
Proof using. by rewrite to_word_cons allLeq_catE => /andP []. Qed.

Lemma last_bigP t b i :
  is_tableau t -> allLeq (to_word t) b ->
  reflect (last b (nth [::] t i) = b /\
           forall j, j < i -> (last b (nth [::] t j) < b)%O)
          (i == last_big t b).
Proof using.
move=> Htab Hmax; apply: (iffP eqP) => [ -> | []]; first split.
- elim: t Htab {Hmax} => [//= | t0 t IHt] /= /and4P [] _ _ _ Htab.
  by case eqP => [//= | _]; apply: IHt.
- elim: t Htab Hmax => [//= | t0 t IHt] /= /and4P [] Hnnil _ _ Htab Hmax.
  case eqP => [//= | /eqP H].
  case=> [/= _ | j].
  + rewrite lt_neqAle {}H /=; move/allLeq_to_word_hd : Hmax.
    by case/lastP: t0 Hnnil => [//= | t0 tn] _; rewrite last_rcons => /allLeq_last.
  + by rewrite /=; apply IHt; last exact: (allLeq_to_word_tl Hmax).
- elim: t i Htab Hmax => [/= i _ _| t0 t IHt].
  + by case: i => [//= | i] /= _ /(_ 0 (ltn0Sn _)) /=; rewrite ltxx.
  + case=> [/= _ _ -> _| i]; first by rewrite eq_refl.
    move=> /= /and4P [] _ _ _ Htab Hmax Hlast Hj.
    have:= Hj 0 (ltn0Sn _) => /= /lt_eqF ->.
    rewrite (IHt _ Htab (allLeq_to_word_tl Hmax) Hlast) //.
    by move=> j; apply: (Hj j.+1).
Qed.

Lemma last_big_append_nth t b lb :
  (forall j : nat, j < lb -> (last b (nth [::] t j) < b)%O) ->
  last_big (append_nth t b lb) b = lb.
Proof using.
elim: t lb =>[/= | t0 t IHt /=].
- case => [/= _| lb Hj /=]; first by rewrite eq_refl.
  by exfalso; have:= Hj 0 (ltn0Sn _); rewrite ltxx.
- case => [/= _| lb Hj /=]; first by rewrite last_rcons eq_refl.
  rewrite (lt_eqF (Hj 0 (ltn0Sn _))).
  have {}Hj j : j < lb -> (last b (nth [::] t j) < b)%O by apply (Hj j.+1).
  by rewrite (IHt _ Hj).
Qed.

End AppendNth.

(** * Bijection standard tableau <-> Yamanouchi words *)
Section Bijection.

Implicit Type y : seq nat.
Implicit Type t : seq (seq nat).

Definition is_stdtab t := is_tableau t && is_std (to_word t).

Lemma stdtabP t : is_stdtab t -> is_tableau t.
Proof. by move=> /andP []. Qed.

Fixpoint stdtab_of_yam y :=
  if y is y0 :: y' then
    append_nth (stdtab_of_yam y') (size y') y0
  else [::].

Lemma shape_stdtab_of_yam y : shape (stdtab_of_yam y) = evalseq y.
Proof. elim: y => [//= | y0 y IHy] /=. by rewrite shape_append_nth IHy. Qed.

Lemma size_stdtab_of_yam y : size_tab (stdtab_of_yam y) = size y.
Proof.
elim: y => [//= | y0 y IHy] /=.
by rewrite -IHy {IHy} /size_tab shape_append_nth sumn_incr_nth.
Qed.

Lemma std_of_yam y : is_std (to_word (stdtab_of_yam y)).
Proof.
rewrite /is_std size_to_word size_stdtab_of_yam.
elim: y => [//= | y0 y IHy].
have -> : iota 0 (size (y0 :: y)) = rcons (iota 0 (size y)) (size y).
  rewrite [size (y0 :: y)]/= -addn1 iota_add add0n /=.
  exact: cats1.
apply: (perm_trans (perm_append_nth _ _ _)).
move: IHy; rewrite -(perm_cons (size y)) => /perm_trans; apply.
by rewrite perm_sym; apply/permPl; apply: perm_rcons.
Qed.

(** The following proof is an experiment to see if proof using get_tab are
    easier than proof by induction on the structure of tableaux *)
Lemma is_tab_append_nth_size_alternative_proof r T n :
   all (gtn n) (to_word T) ->
   is_part (incr_nth (shape T) r) ->
   is_tableau T -> is_tableau (append_nth T n r).
Proof.
have get_append_nth_in rc :
    in_shape (shape T) rc -> get_tab (append_nth T n r) rc = get_tab T rc.
  move: rc => [rn c].
  rewrite /get_tab /append_nth nth_set_nth /=.
  case (altP (rn =P r)) => // -> {rn} /in_shape_tab.
  by rewrite nth_rcons => ->.
have get_append_nth_eq :
  get_tab (append_nth T n r) (r, nth 0 (shape T) r) = n.
  rewrite nth_shape /get_tab /append_nth nth_set_nth /= eq_refl /=.
  by rewrite nth_rcons eq_refl ltnn.
move=> /allP Hw Hparti /is_tableau_getP [Hpart Hrow Hcol].
apply/is_tableau_getP; split => [| rn c Hini | rn c Hini].
- by rewrite shape_append_nth.
- case: (boolP (in_shape (shape T) (rn, c.+1))) => Hin.
  + rewrite !get_append_nth_in //; first exact: Hrow.
    by apply (in_part_le Hpart Hin).
  + move: Hini Hin {Hcol Hpart Hparti}; rewrite /in_shape.
    rewrite shape_append_nth nth_incr_nth /=.
    case eqP => [<- {rn} /= | _]; last by rewrite add0n => ->.
    rewrite add1n ltnS -leqNgt => H1 H2.
    have {H1 H2} H : c.+1 = nth 0 (shape T) r.
      by apply anti_leq; rewrite H1 H2.
    rewrite H get_append_nth_eq get_append_nth_in ?/in_shape ?H //.
    rewrite leEnat; apply/ltnW/Hw.
    by apply mem_to_word; rewrite /in_shape H.
- case: (boolP (in_shape (shape T) (rn.+1, c))) => Hin.
  + rewrite !get_append_nth_in //; first exact: Hcol.
    by apply (in_part_le Hpart Hin).
  + move: Hini Hin {Hcol Hrow}; rewrite /in_shape.
    rewrite shape_append_nth nth_incr_nth.
    case eqP => [/= Hrn | _]; last by rewrite add0n => ->.
    rewrite -Hrn add1n ltnS -leqNgt => H1 H2.
    have {H1 H2} H : c = nth 0 (shape T) r.
      by apply anti_leq; rewrite H1 H2.
    have {Hpart Hparti} Hshape : nth 0 (shape T) r < nth 0 (shape T) rn.
      move: Hparti => /is_partP => [] [_] /(_ rn).
      by rewrite !nth_incr_nth {}Hrn eq_refl add1n eq_sym ltn_eqF.
    rewrite H get_append_nth_eq get_append_nth_in ?/in_shape ?H //.
    rewrite ltEnat; apply Hw.
    by apply mem_to_word; rewrite /in_shape.
Qed.

Lemma is_tab_append_nth_size r T n :
   all (gtn n) (to_word T) ->
   is_part (incr_nth (shape T) r) ->
   is_tableau T -> is_tableau (append_nth T n r).
Proof.
elim: T r => [//= | T0 T IHT] r /=; first by case: r => [//= | r] /=; elim: r.
rewrite to_word_cons all_cat.
move=> /andP [] Hall Hall0.
case: r => [/= _ | r] /=.
- move=> {IHT Hall} /and4P [] Hnnil Hrow Hdom ->.
  rewrite (dominate_rcons _ Hdom) {Hdom} !andbT.
  apply/andP; split; first by case T0.
  apply: (is_row_rcons Hrow); rewrite {Hrow} leEnat.
  case/lastP: T0 Hall0 {Hnnil} => [//= | T0 T0n].
  rewrite all_rcons last_rcons /= andbC => /andP [] _.
  exact: ltnW.
- move => /andP [] Hhead Hpart /and4P [] -> -> Hdom Htab /=.
  rewrite IHT //= andbT {IHT Hall Hpart Htab}.
  case: r Hhead => [| r]; last by case: T Hdom => [//= | T1 T].
  case: T Hdom => [_ | T1 T] /=.
  + case: T0 Hall0 => [//= | hT0 T0] /= /andP [] Hn _ _.
    by rewrite /dominate /= andbT.
  + move/dominateP => [] _ Hdom Hsize.
    apply/dominateP; split; rewrite size_rcons; first by [].
    move=> i Hi; rewrite nth_rcons; case: (ltnP i (size T1)) => Hi1.
    * exact: Hdom.
    * have -> : i == size T1 by rewrite eqn_leq Hi1 andbT -ltnS.
      move: Hall0 => /allP Hall0.
      by have /Hall0 /= := mem_nth inh (leq_trans Hi Hsize).
Qed.

Lemma stdtab_of_yamP y : is_yam y -> is_stdtab (stdtab_of_yam y).
Proof.
rewrite /is_stdtab std_of_yam andbT.
elim: y => [//= | y0 y IHy] /= /andP [] Hpart /IHy {IHy}.
move: Hpart; rewrite -shape_stdtab_of_yam.
suff : all (gtn (size y)) (to_word (stdtab_of_yam y))
  by apply: is_tab_append_nth_size.
have:= std_of_yam y; rewrite /is_std size_to_word size_stdtab_of_yam.
move=> /perm_mem Hperm.
apply/allP => x Hx /=.
by move/(_ x) : Hperm; rewrite mem_iota /= add0n Hx => /esym ->.
Qed.


Section StdTabInd.

Fixpoint remn_rec t n :=
  if t is t0 :: t' then
    match t0 with
      | [::] => [::] (* unused case *)
      | l0 :: t0' => if last l0 t0' == n then
                       if t0' == [::] then [::]
                       else (belast l0 t0') :: t'
                     else t0 :: remn_rec t' n
    end
  else [::] (* unused case *).
Definition remn t := remn_rec t (size_tab t).-1.

Lemma remnP t :
  is_stdtab t -> t != [::] ->
  is_tableau (remn t) /\
  append_nth (remn t) (size_tab t).-1 (last_big t (size_tab t).-1) = t.
Proof.
rewrite /remn; move Hn : (size_tab t) => n.
case: n Hn => [| n Hsize Hstdtab _]; first by move=> /tab0 H /andP [] /H ->.
have:= Hstdtab => /andP [Htab Hstd].
have Hperm : perm_eq (to_word t) (iota 0 n.+1) by rewrite -Hsize -size_to_word.
have:= std_uniq Hstd.
have {Hsize Hstdtab Hstd} : allLeq (to_word t) n.
  have:= Hstd => /perm_allLeqE ->.
  apply/allP => x.
  by rewrite mem_iota add0n size_to_word Hsize /= leEnat.
have {Hperm} : n \in to_word t.
  move: Hperm => /perm_mem ->.
  by rewrite mem_iota /= add0n.
elim: t Htab => [//= | t0 t' /= IHt] /and4P [].
case: t0 => [| l0 t0] _ //.
case: (altP ((last l0 t0) =P n)).
- case/lastP: t0 {IHt} => [ /= Hl0 _ | t0 tn].
    rewrite !dominate_recE; subst l0.
    case: t' => [//=| t1 t'] /= Hdom /and4P [] Hnnil _ _ _ _.
    rewrite !to_word_cons !allLeq_catE => /andP [] /andP [] _ Ht1 _ _.
    exfalso.
    case: t1 Hnnil Ht1 Hdom => [//=| l1 t1] _ /= /andP [] Hl1 _.
    case: t1 => /=; rewrite ?andbF ?andbT //.
    by rewrite ltNge Hl1.
  rewrite rcons_nilF belast_rcons last_rcons => Hl0.
  subst tn => Hrow Hdom Htab' _ /=.
  rewrite to_word_cons cat_uniq allLeq_catE => /andP [] Ht' _ /and3P [] _.
  rewrite -all_predC => /allP /= Hall _.
  have {}/Hall Hn : n \in l0 :: rcons t0 n.
    by rewrite inE mem_rcons inE eq_refl orbT.
  move: Hrow; rewrite -rcons_cons Htab' andbT => /is_row_rconsK /= -> /=.
  split; last by rewrite /append_nth /=.
  case: t' Ht' Hn Hdom Htab' => [//= | t1 t'].
  rewrite to_word_cons allLeq_catE => /andP [] _ Ht1.
  rewrite mem_cat negb_or => /andP [] _ Hn /=.
  have {Hn}Ht1 : allLtn t1 n.
    elim: t1 Ht1 Hn => [//= | l1 t1 IHt1] /= /andP [] Hl1 /IHt1{IHt1} Hrec.
    rewrite inE negb_or => /andP [] Hl1n /Hrec ->.
    by rewrite andbT lt_def Hl1n Hl1.
  rewrite -rcons_cons; move: (l0 :: t0) => {l0}t0.
  rewrite !dominate_recE => Hdom _.
  elim: t1 t0 Ht1 Hdom => [| l1 t1 IHt1] [|l0 t0] //=.
    by move=> /andP [/ltW]; rewrite leNgt => /negbTE ->.
  by move=> /andP [_ /IHt1{IHt1} Hrec] /andP [-> /Hrec].
- move=> Hlast /= Hrow Hdom Htab'.
  rewrite to_word_cons mem_cat cat_uniq allLeq_catE.
  case: (boolP (n \in to_word t')) => [Hn _ | _ Hn] /andP [] Hall Hall0.
  + move => /andP [] Huniq _ {Hall0 Hlast}.
    rewrite {}Hrow /=.
    have {IHt Htab' Hn Hall Huniq} := IHt Htab' Hn Hall Huniq => [] [] -> Happ.
    split; last by move: Happ; rewrite /append_nth /= => ->.
    move: Hdom; rewrite andbT {Happ} !dominate_recE.
    case: t' => [//= | t1 t'] /=.
    case: t1 => [//= | l1 t1] /=.
    case: eqP => //= _.
    case/lastP: t1 => [//= | t1 tl1].
    rewrite rcons_nilF belast_rcons /= => /andP [->]/= {l1 l0 t'}.
    elim: t1 t0 => [//=| l1 t1 IHl1] [|l0 t0] //= /andP [->].
    exact: IHl1.
  + exfalso => {IHt Hdom t' Htab' Hall}.
    case/lastP: t0 Hn Hlast Hrow Hall0 => [/= | t0 tn].
      by rewrite inE => /eqP ->; rewrite eq_refl.
    rewrite orFb -/(is_row (l0 :: _)).
    rewrite -rcons_cons last_rcons.
    move: (l0 :: t0) => {l0}t0 /= Hn Htnn /is_rowP Hrow.
    have Hind := nth_index 0 Hn.
    move: Hn; rewrite -index_mem size_rcons ltnS => Hsz.
    have {Hrow} /(Hrow 0) : index n (rcons t0 tn) <= size t0 < size (rcons t0 tn).
      by rewrite Hsz size_rcons ltnS /=.
    rewrite Hind nth_rcons ltnn eq_refl {Hind Hsz} => Hn /allLeq_last.
    by rewrite leNgt lt_def Htnn Hn.
Qed.

Lemma is_stdtab_remn t : is_stdtab t -> is_stdtab (remn t).
Proof.
move Hn : (size_tab t) => n.
case: n Hn => [| n]; first by move=> /tab0 H /andP [] /H ->.
move=> Hsize Hstdtab.
case: (altP (t =P [::])) => [-> |] //= /(remnP Hstdtab).
rewrite Hsize /= => [] [] Htab Happ.
move: Hstdtab; rewrite /is_stdtab Htab /= /is_std.
rewrite !size_to_word {1}Hsize => /andP [] _ Hperm.
have/(congr1 size_tab) := Happ.
rewrite size_append_nth Hsize => /eqP; rewrite eqSS => /eqP Hsz.
have:= perm_append_nth (remn t) n (last_big t n).
rewrite {}Happ Hsz (permPl Hperm) perm_sym.
rewrite -(addn1 n) iota_add /= add0n cats1.
by rewrite perm_sym perm_rcons perm_sym perm_cons.
Qed.

Lemma append_nth_remn t :
  is_stdtab t -> t != [::] ->
  append_nth (remn t) (size_tab t).-1 (last_big t (size_tab t).-1) = t.
Proof. by move=> H1 H2; have [] := remnP H1 H2. Qed.

Lemma size_tab_remn t :
  is_stdtab t -> t != [::] -> size_tab (remn t) = (size_tab t).-1.
Proof. by move=> /append_nth_remn H{}/H {2}<-; rewrite size_append_nth. Qed.

End StdTabInd.


Fixpoint yam_of_stdtab_rec n t :=
  if n is n'.+1 then
    (last_big t n') :: yam_of_stdtab_rec n' (remn t)
  else [::].
Definition yam_of_stdtab t := yam_of_stdtab_rec (size_tab t) t.

Lemma size_yam_of_stdtab_rec n t : size (yam_of_stdtab_rec n t) = n.
Proof. by elim: n t => [//= | n IHn] /= t; rewrite IHn. Qed.

Theorem yam_of_stdtabK t : is_stdtab t -> stdtab_of_yam (yam_of_stdtab t) = t.
Proof.
rewrite /yam_of_stdtab.
move H : (size_tab t) => n.
elim: n t H => [| n IHn] t.
  by rewrite /is_stdtab => /= /tab0 H /andP [] /H ->.
move=> Hsize Hstdtab /=.
have Hnnil : t != [::] by move: Hsize => /eqP; apply contraL => /eqP ->.
have:= size_tab_remn Hstdtab Hnnil; rewrite Hsize /= => /(IHn (remn t)) {IHn} Hrec.
rewrite (Hrec (is_stdtab_remn Hstdtab)) size_yam_of_stdtab_rec.
by have:= append_nth_remn Hstdtab Hnnil; rewrite Hsize /=.
Qed.

Lemma find_append_nth (l : nat) t r :
  l \notin (to_word t) ->
  find (fun x : seq nat => l \in x) (append_nth t l r) = r.
Proof.
rewrite /append_nth.
elim: r t => [/= | r IHr] t /=; case: t => [_ | t0 t] /=.
- by rewrite inE eq_refl.
- by rewrite mem_rcons inE eq_refl.
- apply/eqP; rewrite eqSS.
  elim: r {IHr} => [//= | r]; first by rewrite inE eq_refl.
  by rewrite /ncons /= => /eqP ->.
- by rewrite to_word_cons mem_cat negb_or => /andP [] /IHr {IHr} -> /negbTE ->.
Qed.

Lemma size_notin_stdtab_of_yam y : (size y) \notin (to_word (stdtab_of_yam y)).
Proof.
have:= std_of_yam y.
rewrite /is_std size_to_word size_stdtab_of_yam => /perm_mem ->.
by rewrite mem_iota add0n /= ltnn.
Qed.

Lemma incr_nth_injl u v i :
  0 \notin u -> 0 \notin v -> incr_nth u i = incr_nth v i -> u = v.
Proof.
move=> Hu Hv /eqP.
elim: u v Hu Hv i => [/= v _ | u0 u IHu v] /=; case: v => [//= | v0 v].
- rewrite inE negb_or => /andP [] Hv0 _.
  by case=> [| i] /= /eqP [] H; rewrite H eq_refl in Hv0.
- move=> {IHu}.
  rewrite inE negb_or => /andP [] Hu0 _ _.
  by case=> [| i] /= /eqP [] H; rewrite H eq_refl in Hu0.
- rewrite !inE !negb_or => /andP [] Hu0 Hu /andP [] Hv0 Hv.
  case=> [| i] /= /eqP [] ->; first by move ->.
  by move/eqP/(IHu _ Hu Hv) ->.
Qed.

Lemma shape0 (d : unit) (T : orderType d) (u : seq (seq T)) :
  [::] \notin u -> 0 \notin (shape u).
Proof.
apply: contra; rewrite /shape; elim: u => [//=| u0 u IHu] /=.
rewrite !inE => /orP [].
- by rewrite eq_sym => /nilP ->.
- by move/IHu ->; rewrite orbT.
Qed.

Lemma append_nth_injl (d : unit) (T : inhOrderType d) u v (l : T) p :
  [::] \notin u -> [::] \notin v -> append_nth u l p = append_nth v l p -> u = v.
Proof.
move=> Hu Hv Heq; have:= congr1 shape Heq.
rewrite !shape_append_nth => /(incr_nth_injl (shape0 Hu) (shape0 Hv)) /eqP {Hu Hv}.
move: Heq; rewrite /append_nth.
elim: u v p => [/= | u0 u IHu] /=; case=> [| v0 v] //=.
case=> [| p] /= []; first by move/rconsK => -> ->.
by move=> -> Heq /eqP [] /eqP /(IHu _ _ Heq) ->.
Qed.

Lemma stdtab_of_yam_nil y : is_yam y -> [::] \notin (stdtab_of_yam y).
Proof.
move/stdtab_of_yamP; rewrite /is_stdtab => /andP [] Htab _.
elim: (stdtab_of_yam) Htab => [//= | t0 t IHt] /= /and4P [] Hnnil _ _ /IHt H.
by rewrite inE negb_or eq_sym Hnnil H.
Qed.

Lemma stdtab_of_yam_inj x y :
  is_yam x -> is_yam y -> stdtab_of_yam x = stdtab_of_yam y -> x = y.
Proof.
move=> Hx Hy Heq; have:= congr1 size_tab Heq.
rewrite !size_stdtab_of_yam => Hsz.
elim: x y Hsz Heq Hx Hy => [| x0 x IHx]; case=> [//= | y0 y] //= /eqP.
rewrite eqSS => /eqP Heqsz; rewrite Heqsz => Heq.
have Hfind w := find_append_nth _ (size_notin_stdtab_of_yam w).
have:= Hfind x0 x; rewrite Heqsz Heq Hfind {Hfind} => H0.
move=> /andP [] _ Hx /andP [] _ Hy.
rewrite H0; congr (_ :: _); apply: (IHx _ Heqsz) => {IHx Heqsz} //=.
move: Heq; rewrite H0 {H0}.
by apply: append_nth_injl; apply: stdtab_of_yam_nil.
Qed.

Lemma shape_yam_of_stdtab t : is_stdtab t -> evalseq (yam_of_stdtab t) = shape t.
Proof.
by move=> /yam_of_stdtabK/(congr1 shape); rewrite shape_stdtab_of_yam.
Qed.

Lemma size_yam_of_stdtab t : is_stdtab t -> size (yam_of_stdtab t) = size_tab t.
Proof.
move=> Htab.
by rewrite /size_tab -(shape_yam_of_stdtab Htab) evalseq_eq_size.
Qed.

Lemma part_yam_of_stdtab t : is_stdtab t -> is_part (evalseq (yam_of_stdtab t)).
Proof.
move=> Htab; rewrite (shape_yam_of_stdtab Htab).
apply: is_part_sht.
by move: Htab; rewrite /is_stdtab => /andP [].
Qed.

Lemma yam_of_stdtabP t : is_stdtab t -> is_yam (yam_of_stdtab t).
Proof.
move=> Hstdtab; have:= part_yam_of_stdtab Hstdtab.
rewrite /yam_of_stdtab.
move H : (size_tab t) => n.
elim: n t H Hstdtab => [//= | n IHn] t Hsize Hstdtab.
move Hw : (to_word t) Hsize => w; case : w Hw => [//= | w0 w].
  by rewrite -size_to_word => -> /=.
rewrite /= => Ht Hsize -> /=.
have Hnnil : t != [::] by move: Hsize => /eqP; apply contraL => /eqP ->.
have:= size_tab_remn Hstdtab Hnnil; rewrite Hsize /= => Hsz.
apply (IHn _ Hsz); first exact: is_stdtab_remn.
rewrite -Hsz.
exact: part_yam_of_stdtab (is_stdtab_remn Hstdtab).
Qed.

Theorem stdtab_of_yamK y : is_yam y -> yam_of_stdtab (stdtab_of_yam y) = y.
Proof.
move=> Hyam.
have /yam_of_stdtabK := (stdtab_of_yamP Hyam).
apply: stdtab_of_yam_inj; last exact Hyam.
by apply: yam_of_stdtabP; apply: stdtab_of_yamP.
Qed.

End Bijection.


Lemma eq_inv_is_row (d1 d2 : unit) (T1 : inhOrderType d1) (T2 : inhOrderType d2)
      (u1 : seq T1) (u2 : seq T2) :
  eq_inv u1 u2 -> is_row u1 -> is_row u2.
Proof.
move/eq_invP => [Hsz Hinv] /(is_rowP inh) Hrow.
apply/(is_rowP inh) => i j; rewrite -Hsz => Hij.
rewrite -(Hinv i j Hij).
exact: Hrow.
Qed.

Lemma is_row_stdE (d : unit) (T : inhOrderType d) (w : seq T) :
  is_row (std w) = is_row w.
Proof.
by apply/idP/idP; apply eq_inv_is_row; first apply eq_inv_sym; apply: eq_inv_std.
Qed.

(** * Sigma type for standard tableaux *)
Section StdtabOfShape.

Definition is_stdtab_of_shape sh := [pred t | (is_stdtab t) && (shape t == sh) ].
Definition enum_stdtabsh sh : seq (seq (seq nat)) :=
  map stdtab_of_yam (enum_yameval sh).

Variable sh : intpart.

Structure stdtabsh : Set :=
  StdtabSh {stdtabshval :> seq (seq nat); _ : is_stdtab_of_shape sh stdtabshval}.

Canonical stdtabsh_subType := Eval hnf in [subType for stdtabshval].
Definition stdtabsh_eqMixin := Eval hnf in [eqMixin of stdtabsh by <:].
Canonical stdtabsh_eqType := Eval hnf in EqType stdtabsh stdtabsh_eqMixin.
Definition stdtabsh_choiceMixin := Eval hnf in [choiceMixin of stdtabsh by <:].
Canonical stdtabsh_choiceType := Eval hnf in ChoiceType stdtabsh stdtabsh_choiceMixin.
Definition stdtabsh_countMixin := Eval hnf in [countMixin of stdtabsh by <:].
Canonical stdtabsh_countType := Eval hnf in CountType stdtabsh stdtabsh_countMixin.
Canonical stdtabsh_subCountType := Eval hnf in [subCountType of stdtabsh].

Let stdtabsh_enum : seq stdtabsh := pmap insub (enum_stdtabsh sh).

Lemma finite_stdtabsh : Finite.axiom stdtabsh_enum.
Proof using.
case=> /= t Ht; rewrite -(count_map _ (pred1 t)) (pmap_filter (@insubK _ _ _)).
rewrite count_filter -(@eq_count _ (pred1 t)) => [|s /=]; last first.
  by rewrite isSome_insub; case: eqP=> // ->.
move: Ht => /andP [] Htab /eqP.
rewrite -(shape_yam_of_stdtab Htab) => Hsht.
rewrite /enum_stdtabsh count_map.
rewrite (eq_in_count (a2 := pred1 (yam_of_stdtab t))); first last.
  move=> y /(allP (enum_yamevalP (intpartP sh))).
  rewrite /is_yam_of_eval => /andP [] Hyam /eqP Hevy /=.
  apply/idP/idP => /eqP H; apply/eqP.
  + by rewrite -H stdtab_of_yamK.
  + by rewrite H yam_of_stdtabK.
apply: (enum_yameval_countE (intpartP sh)).
by rewrite /is_yam_of_eval yam_of_stdtabP //= Hsht.
Qed.

Definition stdtabsh_finMixin := Eval hnf in FinMixin finite_stdtabsh.
Canonical stdtabsh_finType := Eval hnf in FinType stdtabsh stdtabsh_finMixin.
(* Redundant with tabsh_subFinType
Canonical stdtabsh_subFinType := Eval hnf in [subFinType of stdtabsh_countType]. *)

Lemma stdtabshP (t : stdtabsh) : is_stdtab t.
Proof using. by case: t => /= t /andP []. Qed.

Lemma shape_stdtabsh (t : stdtabsh) : shape t = sh.
Proof using. by case: t => /= t /andP [] _ /eqP. Qed.

Lemma enum_stdtabshE : map val (enum {:stdtabsh}) = enum_stdtabsh sh.
Proof.
rewrite enumT unlock /= /stdtabsh_enum /enum_stdtabsh.
elim: (enum_yameval sh) (enum_yamevalP (intpartP sh)) => //= y ly IHly.
move=> /andP [/andP [Hyam Heval] /IHly{IHly}Hrec].
by rewrite insubT /= stdtab_of_yamP //= ?shape_stdtab_of_yam // Hrec.
Qed.

Lemma hyper_stdtabsh_subproof :
  is_stdtab_of_shape sh (stdtab_of_yam (locked (hyper_yameval sh))).
Proof.
by rewrite /= stdtab_of_yamP //= shape_stdtab_of_yam // eval_yameval.
Qed.
Definition hyper_stdtabsh := StdtabSh hyper_stdtabsh_subproof.

End StdtabOfShape.
#[export] Hint Resolve stdtabshP : core.


Section StdtabCombClass.

Variable n : nat.

Definition is_stdtab_of_n := [pred t | (is_stdtab t) && (size_tab t == n) ].

Structure stdtabn : Set :=
  StdtabN {stdtabnval :> seq (seq nat); _ : is_stdtab_of_n stdtabnval}.
Canonical stdtabn_subType := Eval hnf in [subType for stdtabnval].
Definition stdtabn_eqMixin := Eval hnf in [eqMixin of stdtabn by <:].
Canonical stdtabn_eqType := Eval hnf in EqType stdtabn stdtabn_eqMixin.
Definition stdtabn_choiceMixin := Eval hnf in [choiceMixin of stdtabn by <:].
Canonical stdtabn_choiceType := Eval hnf in ChoiceType stdtabn stdtabn_choiceMixin.

Definition stdtabn_countMixin := Eval hnf in [countMixin of stdtabn by <:].
Canonical stdtabn_countType := Eval hnf in CountType stdtabn stdtabn_countMixin.
Canonical stdtabnn_subCountType := Eval hnf in [subCountType of stdtabn].


Definition enum_stdtabn : seq (seq (seq nat)) :=
  map (stdtab_of_yam \o val) (enum ({:yamn n})).
Let stdtabn_enum : seq stdtabn := pmap insub enum_stdtabn.

Lemma finite_stdtabn : Finite.axiom stdtabn_enum.
Proof using.
case=> /= t Ht; rewrite -(count_map _ (pred1 t)) (pmap_filter (@insubK _ _ _)).
rewrite count_filter -(@eq_count _ (pred1 t)) => [|s /=]; last first.
  by rewrite isSome_insub; case: eqP=> // ->.
move: Ht => /andP [] Htab /eqP.
rewrite -(size_yam_of_stdtab Htab) => Hszt.
rewrite /enum_stdtabn map_comp.
rewrite !enumT unlock subType_seqP.
rewrite count_map.
rewrite (eq_in_count (a2 := pred1 (yam_of_stdtab t))); first last.
  move=> y /(allP (all_unionP _ yamn_PredEq)) /=.
  rewrite /is_yam_of_size => /andP [] Hyam /eqP Hszy /=.
  apply/idP/idP => /eqP H; apply/eqP.
  + by rewrite -H stdtab_of_yamK.
  + by rewrite H yam_of_stdtabK.
apply: (count_unionP _ yamn_PredEq).
- exact: yamn_partition_evalseq.
- by rewrite /is_yam_of_size yam_of_stdtabP //= Hszt.
Qed.

Definition stdtabn_finMixin := Eval hnf in FinMixin finite_stdtabn.
Canonical stdtabn_finType := Eval hnf in FinType stdtabn stdtabn_finMixin.
(* Redundant with tabsh_subFinType
Canonical stdtabn_subFinType := Eval hnf in [subFinType of stdtabn_countType]. *)

Lemma stdtabnP (s : stdtabn) : is_stdtab s.
Proof using. by case: s => s /= /andP []. Qed.

Lemma size_tab_stdtabn (s : stdtabn) : size_tab s = n.
Proof using. by case: s => s /= /andP [] _ /eqP. Qed.

Lemma sumn_shape_stdtabnE (Q : stdtabn) : (sumn (shape Q)) = n.
Proof using.
by case: Q => q; rewrite /is_stdtab_of_n /= => /andP [] H /= /eqP.
Qed.

Lemma is_part_shape_deg (Q : stdtabn) : is_part_of_n n (shape Q).
Proof using.
rewrite /=; apply/andP; split.
- by rewrite -/(size_tab _) size_tab_stdtabn.
- apply: is_part_sht; apply stdtabP; apply: stdtabnP.
Qed.
Definition shape_deg (Q : stdtabn) := IntPartN (is_part_shape_deg Q).

End StdtabCombClass.

Section StdtabnOfStdtabsh.

Variables (n : nat) (sh : intpartn n).

Fact stdtabn_of_sh_subproof (t : stdtabsh sh) : is_stdtab_of_n n t.
Proof.
move: t => [t /= /andP[->/= /eqP eqsh]].
by rewrite /size_tab eqsh sumn_intpartn.
Qed.
Definition stdtabn_of_sh t := StdtabN (stdtabn_of_sh_subproof t).

Lemma shape_deg_stdtabn_of_sh t :
  shape_deg (stdtabn_of_sh t) = sh.
Proof. by apply val_inj; rewrite /= shape_stdtabsh. Qed.

End StdtabnOfStdtabsh.

(** * Conjugate of a standard tableau *)
Section ConjTab.

Variables (disp: unit) (T : inhOrderType disp).

Definition conj_tab (t : seq (seq T)) : seq (seq T) :=
  let c := conj_part (shape t) in
  mkseq (fun i => mkseq (fun j => get_tab t (j, i)) (nth 0 c i)) (size c).

Lemma size_conj_tab t : size (conj_tab t) = size (conj_part (shape t)).
Proof using. by rewrite /conj_tab size_mkseq. Qed.

Lemma shape_conj_tab t : shape (conj_tab t) = conj_part (shape t).
Proof using.
rewrite /conj_tab /shape -map_comp.
rewrite (eq_map (f2 := fun i =>
                         (nth 0 (conj_part [seq size i | i <- t]) i))); first last.
  by move => i /=; rewrite size_mkseq.
by rewrite -/(shape _) -/(mkseq _ _); apply: mkseq_nth.
Qed.

Lemma get_conj_tab t :
  is_part (shape t) -> forall i j, get_tab (conj_tab t) (i, j) = get_tab t (j, i).
Proof using.
move=> Ht i j.
case: (boolP (in_shape (shape t) (j, i))) => Hin;
  have:= Hin; rewrite (in_conj_part Ht) => Hconj.
- rewrite {1}/get_tab /conj_tab nth_mkseq; last exact: (in_shape_size Hconj).
  rewrite -shape_conj_tab.
  by rewrite nth_mkseq; last by rewrite shape_conj_tab; apply: Hconj.
- rewrite /get_tab.
  rewrite [RHS]nth_default; last by rewrite leqNgt -nth_shape.
  apply nth_default.
  by rewrite leqNgt -nth_shape shape_conj_tab.
Qed.

Lemma eq_from_shape_get_tab (t u : seq (seq T)) :
  shape t = shape u -> get_tab t =1 get_tab u -> t = u.
Proof using.
move=> Hsh Hget; apply (eq_from_nth (x0 := [::])).
  by rewrite -!(size_map size) -!/(shape _) Hsh.
move=> r _; apply (eq_from_nth (x0 := inh)).
  by rewrite -!nth_shape Hsh.
by move=> c _; rewrite -!/(get_tab _ (_, _)) Hget.
Qed.

Lemma conj_tab_shapeK t : is_part (shape t) -> conj_tab (conj_tab t) = t.
Proof using.
move=> Hpart; apply eq_from_shape_get_tab.
- by rewrite !shape_conj_tab conj_partK.
- move=> [r c]; rewrite ?get_conj_tab //.
  by rewrite shape_conj_tab; apply: is_part_conj.
Qed.

Lemma conj_tabK t : is_tableau t -> conj_tab (conj_tab t) = t.
Proof using. move=> /is_part_sht; apply :conj_tab_shapeK. Qed.

Lemma append_nth_conj_tab (t : seq (seq T)) l i :
  is_part (shape t) ->
  is_add_corner (shape t) i ->
  conj_tab (append_nth t l i) = append_nth (conj_tab t) l (nth 0 (shape t) i).
Proof using.
move=> Hsh Hcorn; apply eq_from_shape_get_tab.
- rewrite shape_conj_tab !shape_append_nth shape_conj_tab.
  exact: conj_part_incr_nth.
- move=> [r c]; rewrite get_conj_tab; first last.
    by rewrite shape_append_nth; apply: is_part_incr_nth.
  rewrite !get_tab_append_nth.
  case: (altP (r =P nth 0 (shape t) i));
    rewrite /= ?andbF ?andbT get_conj_tab // shape_conj_tab.
  move: Hcorn; rewrite /is_add_corner /= => /orP [/eqP Hi| H] Hr.
  + by rewrite Hi nth0 nth_default // size_conj_part.
  + have : nth 0 (shape t) i <= nth 0 (shape t) i < nth 0 (shape t) i.-1.
      by rewrite leqnn H.
    rewrite -nth_conjE //; last by case: i H {Hr}; rewrite // ltnn.
    by move=> /eqP ->.
Qed.

End ConjTab.


Example conj_tab_expl1 :
  conj_tab [:: [:: 0; 1; 4]; [:: 2; 3]] ==
           [:: [:: 0; 2]; [:: 1; 3]; [:: 4]].
Proof. by compute. Qed.
Example conj_tab_expl2 :
  conj_tab [:: [:: 0; 1; 3; 4]; [:: 2; 5]; [:: 6]] ==
           [:: [:: 0; 2; 6]; [:: 1; 5]; [:: 3]; [:: 4]].
Proof. by compute. Qed.


Lemma stdtab_get_tabNE t :
  is_stdtab t ->
  forall rc1 rc2,
    in_shape (shape t) rc1 ->
    in_shape (shape t) rc2 ->
    rc1 != rc2 -> get_tab t rc1 != get_tab t rc2.
Proof.
move=> /andP [] _ /std_uniq.
elim: t => [_ | t0 t /= IHt Huniq] [r1 c1] [r2 c2].
  by rewrite /in_shape /= nth_default //.
move: Huniq; rewrite to_word_cons cat_uniq => /and3P [] Ht /hasPn Htt0 Ht0.
rewrite /in_shape /get_tab; case: r1 r2 => [| r1] [| r2]/= Hc1 Hc2.
- by apply /contra; rewrite [(0, _) == _]/eq_op/= (nth_uniq _ Hc1 Hc2 Ht0).
- move=> _; have:= mem_nth inh Hc1 => /Htt0; apply contra => /eqP ->.
  move: Hc2; rewrite -/(get_tab _ (_, _)) -/(in_shape _ (_, _)).
  exact: mem_to_word.
- move=> _; have:= mem_nth inh Hc2 => /Htt0; apply contra => /eqP <-.
  move: Hc1; rewrite -/(get_tab _ (_, _)) -/(in_shape _ (_, _)).
  exact: mem_to_word .
- rewrite {1}/eq_op/= eqSS -[~~ ((r1 == r2) && (c1 == c2))]/((_, _) != (_, _)).
  exact: IHt.
Qed.

Lemma is_stdtab_conj t : is_stdtab t -> is_stdtab (conj_tab t).
Proof.
move=> Hstdtab.
have:= Hstdtab; rewrite /is_stdtab => /andP [] Htab Hstd.
have Hp := is_part_sht Htab; have Hc := is_part_conj Hp.
apply/andP; split.
- apply/is_tableauP; split.
  rewrite size_conj_tab => i Hi.
  have:= nth_part_non0 Hc Hi.
  apply contra => /eqP.
  by rewrite -shape_conj_tab nth_shape => ->.
- move=> i; apply/(is_rowP inh) => j1 j2 /andP [] Hj.
  rewrite -nth_shape shape_conj_tab -(conj_ltnE Hp) nth_shape => Hjsz.
  rewrite -!/(get_tab _ (_, _)) !(get_conj_tab Hp).
  have:= Htab => /is_tableauP [] _ _ Hdom.
  move: Hj; rewrite leq_eqVlt => /orP [/eqP -> //|] /Hdom/dominateP [] _ {}Hdom.
  by have /= := ltW (Hdom _ Hjsz); apply.
- move=> j1 j2 Hj.
  apply/dominateP; split.
  + rewrite -!nth_shape shape_conj_tab.
    by move: Hc => /is_part_ijP [] _; apply; apply: ltnW.
  + move=> i; rewrite -!nth_shape shape_conj_tab -(conj_ltnE Hp) => Hj2.
    rewrite -!/(get_tab _ (_, _)) !(get_conj_tab Hp) /get_tab.
    have:= Htab => /is_tableauP [] _ Hrow _.
    rewrite lt_def (is_rowP inh _ (Hrow i)); first last.
      by rewrite (ltnW Hj) -nth_shape Hj2.
    rewrite  -/(in_shape _ _) in Hj2.
    rewrite andbT -!/(get_tab _ (_, _)); apply (stdtab_get_tabNE Hstdtab).
    * exact: Hj2.
    * exact: (in_part_le (is_part_sht Htab) Hj2 (leqnn _) (ltnW Hj)).
    * by rewrite xpair_eqE eq_refl /= (gtn_eqF Hj).
- apply/is_stdP => n.
  rewrite size_to_word /size_tab shape_conj_tab sumn_conj_part
          -/(size_tab _) -size_to_word => /is_stdP/=/(_ Hstd) Hn.
  have:= Hn; rewrite -index_mem; have := nth_index inh Hn.
  move: (index _ _) => pos <- {Hn} Hpos.
  move: Hpos; rewrite size_to_word /size_tab -sumn_rev /shape -map_rev -/(shape _).
  move=> Htmp; have:= reshape_offsetP Htmp; move/reshape_indexP : Htmp.
  rewrite (nth_flatten inh (rev t) pos) shape_rev size_rev size_map => Hpos.
  do !rewrite nth_rev ?size_map //.
  rewrite -/(get_tab _ (_, _)) -/(in_shape _ (_, _)) -(get_conj_tab Hp).
  rewrite (in_conj_part Hp) -shape_conj_tab {Hpos}.
  exact: mem_to_word.
Qed.

Lemma conj_stdtabnP n (t : stdtabn n):
  is_stdtab_of_n n (conj_tab t).
Proof.
case: t => t /= /andP [] Ht /eqP Hsh.
rewrite (is_stdtab_conj Ht) /=.
by rewrite /size_tab shape_conj_tab sumn_conj_part -/(size_tab _) Hsh.
Qed.
Canonical conj_stdtabn n (t : stdtabn n) := StdtabN (conj_stdtabnP t).

Lemma conj_stdtabshP (sh : intpart) (t : stdtabsh sh) :
  is_stdtab_of_shape (conj_part sh) (conj_tab t).
Proof.
case: t => t /= /andP [] Ht /eqP Hsh.
rewrite (is_stdtab_conj Ht) /=.
by rewrite shape_conj_tab Hsh.
Qed.
Canonical conj_stdtabsh {sh : intpart} (t : stdtabsh sh) :=
  StdtabSh (conj_stdtabshP t).


Definition stdtabshcast m n (eq_mn : m = n) t :=
  let: erefl in _ = n := eq_mn return stdtabsh n in t.

Lemma val_stdtabshcast  m n (eq_mn : m = n) t : val (stdtabshcast eq_mn t) = val t.
Proof. by subst m; case: t. Qed.

Lemma conj_stdtabsh_bij sh : bijective (@conj_stdtabsh sh).
Proof.
by exists (stdtabshcast (conj_intpartK sh) \o conj_stdtabsh) => t;
   apply val_inj; rewrite /= val_stdtabshcast /= conj_tabK //;
     have:= stdtabshP t => /andP [].
Qed.

(** The canonical conj_intpart work for conj_stdtabsh and not here...  TODO:
rewrite the interface of stdtabsh to triger a unification (see eg what is done
for tuple). *)
Lemma card_stdtabsh_conj_part (sh : intpart) :
  #|{:stdtabsh [the intpart of conj_part sh]}| = #|{:stdtabsh sh}|.
Proof. by symmetry; apply: (bij_card (conj_stdtabsh_bij sh)). Qed.

#[export] Hint Resolve stdtabnP stdtabshP : core.
