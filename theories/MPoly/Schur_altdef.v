(** * Combi.MPoly.Schur_altdef : Alternants definition of Schur polynomials *)
(******************************************************************************)
(*      Copyright (C) 2016-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * Definition of Schur polynomials as quotient of alternant and Kostka numbers

In the combinatorial definitions below, we use the following notations:
- [n] : an integer denoting the number of variable.
- [la] [mu] : partitions of an integer [d]
- [m] : a monomial for the ring of polynomials [{mpoly R[n]}]
- [w] : a sequence of ['I_n]
- [t] : a tableau

We define the following notions:

- [add_mesym la S] == for a set [S] of ['I_n] the partition obtained by
           incrementing the parts in [S] if its a partition. If not
           the value is unspecified.
- [setdiff la mu] == the set of elements [i] of ['I_n] for which the
           [i]-th part of [la] is smaller than the one of [mu].

Kostka numbers:

- [eval w]        == the evaluation of [w] as a [n.-tuple nat].
- [KostkaTab la m] == the set of tableaux of shape [la] and evaluation [m].
- [KostkaMon la m] == the number of Kostka tableau : [#|KostkaTab la m|].
- [Kostka la mu]    ==
- ['K(la, mu)]      == the Kostka number associated to [la] and [mu]
           as a [nat] in [nat_scope] and as an element of [R] (inferred from
           the context) in [ring_scope].
- [Kostak_rec la mu] == a Coq implementation of the computation of the Kostka
      number. It suppose that [sumn la = sumn mu].
- ['K^-1(la, mu)] == the inverse Kostka number, that is the coefficient of the
           inverse Kostka matrix computed using matrix inversion.
- [eqeval t la] == the evaluation of [t] is [la]. More precisely, the evaluation
           of the row reading of the tableau [t] is equal to the monomial
           associated to [la]

Kostka numbers and standard tableaux:

In this section, we fix two nat [n] and [d] with hypothesis [Hd : d <= n.+1].

- [tabnat_of_ord Hd t] == the standard tableau of shape [la] corresponding to
                          the tableau [t : tabsh n la]
- [tabord_of_nat Hd t] == the tableau over ['I_n.+1] of shape [la]
                          corresponding to [t : stdtabsh la]

Extension of tableaux:

In this section, we fix
- a non empty sequence of integer [rcons s m] whose size is less than [n].
- [la] : a partition of [sumn s] whose size is less than [n].
- [mu] : a partition of [(sumn s) + m] whose size is less than [n].
We are given some proofs [Hs] [Hla] [Hmu] that all these partition are of size
less than [n]. We suppose moreover that [mu/la] is an horizontal border
strip. The proof is denoted [Hstrip].

We denote by
- [T] : any tableau of shape [la] and evaluation [s].
- [Tm] : any tableau of shape [mu] and evaluation [rcons s m].
Then we define:

- [shape_res_tab Hsz Tm] == the shape obtained by removing from [Tm] the boxes
      containing [size s]
- [res_tab Hsz Hmu Hstrip Tm] == the tableau obtained by removing from [Tm]
      the boxes containing [size s] if its of shape [la]. Otherwise the result
      is unspecified.
- [ext_tab Hsz Hmu Hstrip T] == the tableau obtained by filling the boxes of [mu/la]
      with [size s].

Then [ext_tab] and [res_tab] are two inverse bijections.
******)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype finfun tuple bigop ssralg ssrint.
From mathcomp Require Import order finset fingroup perm.
From SsrMultinomials Require Import ssrcomplements freeg mpoly.

Require Import tools combclass ordtype sorted partition tableau.
Require Import skewpart skewtab antisym Schur_mpoly freeSchur therule.
Require Import std stdtab unitriginv presentSn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.
Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope Combi_scope.


Local Reserved Notation "''a_' k"
      (at level 8, k at level 2, format "''a_' k").
Local Reserved Notation "''e_' k"
      (at level 8, k at level 2, format "''e_' k").
Local Reserved Notation "m # s"
      (at level 40, left associativity, format "m # s").

(** Alternating and symmetric polynomial *)
Section Alternant.

Variables (n : nat) (R : comRingType).

Local Notation RR := (GRing.ComRing.ringType R).
Local Notation rho := (rho n).
Local Notation "''e_' k" := (mesym n RR k).
Local Notation "''a_' k" := (@alternpol n RR 'X_[k]).

Lemma alt_syme (m : 'X_{1..n}) k :
  'a_(m + rho) * 'e_k =
  \sum_(h : {set 'I_n} | #|h| == k) 'a_(m + mesym1 h + rho).
Proof using .
rewrite /alternpol exchange_big /=.
rewrite mulr_suml; apply eq_bigr => s _.
rewrite -(issymP _ (mesym_sym n R k) s) mesymE.
rewrite (raddf_sum (msym_additive _ _)) /=.
rewrite mulr_sumr; apply eq_bigr => h _.
rewrite -scalerAl -msymM -mpolyXD.
by rewrite -!addmA [(mesym1 h + rho)%MM]addmC.
Qed.

Local Open Scope nat_scope.

Section HasIncr.

Variables (d k : nat) (la : 'P_d) (h : {set 'I_n}).

Local Definition hasincr :=
  has (fun i => (nth 0 (mpart la + mesym1 h)%MM i).+1 ==
                 nth 0 (mpart la + mesym1 h)%MM i.+1) (iota 0 n.-1).

Lemma hasincr0 : hasincr -> 'a_(mpart la + mesym1 h + rho) = 0%R :> {mpoly R[n]}.
Proof using . move=> /hasP [] i _ /eqP; exact: alt_add1_0. Qed.

Lemma not_hasincr_part :
  size la <= n -> ~~ hasincr ->
  is_part_of_n (d + #|h|) (rem_trail0 (mpart la + mesym1 h)%MM).
Proof using .
move=> Hsz /hasPn H.
rewrite /mpart Hsz.
apply/andP; split.
- rewrite sumn_rem_trail0.
  rewrite (@sumn_nth_le _ n); last by rewrite size_map size_enum_ord.
  rewrite big_mkord.
  under eq_bigr do rewrite -tnth_nth -mnm_tnth 2!mnmE.
  rewrite big_split /=; apply/eqP; congr (_ + _)%N.
  + by rewrite -{2}(sumn_intpartn la) (sumn_nth_le Hsz) big_mkord.
  + rewrite -mdeg_mesym1 /mdeg.
    rewrite -map_tnth_enum big_map big_enum; apply eq_bigr => i _.
    by rewrite mnm_tnth.
- apply/is_part_rem_trail0/(sorted1P 0) => i.
  rewrite size_map size_enum_ord => Hi1.
  have Hi : i < n by apply: (ltn_trans _ Hi1).
  have {}/H : i \in iota 0 n.-1.
    rewrite mem_iota add0n.
    by case: n Hi1 {Hsz H Hi} => [//= | n'] /=; rewrite ltnS.
  have H0 : 0 < n by apply: (leq_ltn_trans _ Hi1).
  rewrite /mpart Hsz !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
  rewrite !nth_enum_ord //.
  have [_ /(_ i) H1] := is_partP _ (intpartnP la).
  case: (_ i \in h) (_ i.+1 \in h) => [] [] /=; rewrite ?addn1 ?addn0 => H2.
  + by rewrite ltnS.
  + exact: (leq_trans H1).
  + by rewrite ltn_neqAle -eqSS eq_sym H2 H1.
  + exact: H1.
Qed.

Let add_mpart_mesym :=
  if [&& size la <= n, #|h| == k & ~~ hasincr]
  then (rem_trail0 (mpart la + mesym1 h)%MM)
  else rowpartn (d + k) (* unused *).
Lemma add_mpart_mesymP : is_part_of_n (d + k) add_mpart_mesym.
Proof using la h.
rewrite /add_mpart_mesym.
case: (boolP [&& _, _ & _]) => [/and3P [] Hsz /eqP <- Hincr | _].
- exact: not_hasincr_part.
- by rewrite rowpartnE; apply: rowpartn_subproof.
Qed.
Definition add_mesym : 'P_(d + k) := IntPartN add_mpart_mesymP.

Lemma add_mesymE :
  size la <= n -> #|h| == k -> ~~ hasincr ->
  mpart add_mesym = (mpart la + mesym1 h)%MM.
Proof using .
rewrite /add_mesym /add_mpart_mesym => Hsz /= /eqP <- Hincr.
rewrite /mpart Hincr Hsz eq_refl /=.
set S := (map _ _).
rewrite mnmP => i.
rewrite (leq_trans (size_rem_trail0 S)); last by rewrite size_map size_enum_ord.
rewrite mnmE nth_rem_trail0.
have H0 : 0 < n by apply: (leq_ltn_trans _ (ltn_ord i)).
rewrite !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
by rewrite !nth_ord_enum.
Qed.

End HasIncr.

Definition setdiff (la mu : seq nat) : {set 'I_n} :=
  [set i : 'I_n | nth 0 la i < nth 0 mu i].

Lemma card_setdiff d k (la : 'P_d) (mu : 'P_(d + k)) :
  size mu <= n -> size la <= n -> vb_strip la mu -> #|setdiff la mu| = k.
Proof using .
move=> Hszmu Hszla /(vb_stripP (intpartnP _) (intpartnP _)) Hstrip.
have Hstrip1 j : nth 0 mu j <= (nth 0 la j).+1 by have /andP[] := Hstrip j.
have {}Hstrip j : nth 0 la j <= nth 0 mu j by have /andP[] := Hstrip j.
apply esym; rewrite /setdiff -sum1dep_card -[LHS](addKn d k).
rewrite -{2}(sumn_intpartn la) -{1}(sumn_intpartn mu).
rewrite (sumn_nth_le Hszmu) (sumn_nth_le Hszla).
transitivity (\sum_(0 <= i < n) (nth 0 mu i - nth 0 la i)).
  rewrite /index_iota subn0.
  elim: n {Hszmu Hszla} => [//= | j IHj]; first by rewrite !big_nil.
  rewrite -addn1 iota_add /= add0n !big_cat !big_cons !big_nil /= !addn0.
  rewrite subnDA subnAC -addnBA // addnC [RHS]addnC -{}IHj.
  by rewrite addnBA // leq_sum.
rewrite !big_mkord [LHS](bigID (fun i : 'I_n => nth 0 la i < nth 0 mu i)) /=.
rewrite [X in (_ + X = _)]big1 ?addn0; first last.
  by move=> i; rewrite -leqNgt -subn_eq0 => /eqP ->.
apply eq_bigr => i H.
suff -> : nth 0 mu i = (nth 0 la i).+1 by rewrite subSn // subnn.
by apply anti_leq; rewrite Hstrip1 H.
Qed.

Lemma nth_add_setdiff d k (la : 'P_d) (mu : 'P_(d + k)) :
  size mu <= n -> size la <= n -> vb_strip la mu ->
  forall i,
  nth 0 [seq (mpart la) i0 + (mesym1 (setdiff la mu)) i0 | i0 : 'I_n] i =
  nth 0 mu i.
Proof using .
move=> Hszmu Hszla /(vb_stripP (intpartnP _) (intpartnP _)) Hstrip i.
have Hstrip1 j : nth 0 mu j <= (nth 0 la j).+1 by have /andP[] := Hstrip j.
have {}Hstrip j : nth 0 la j <= nth 0 mu j by have /andP[] := Hstrip j.
case: (ssrnat.ltnP i n) => Hi; first last.
  rewrite !nth_default //.
  - exact: leq_trans Hszmu Hi.
  - by rewrite size_map size_enum_ord.
have H0 : 0 < n by apply: (leq_ltn_trans _ Hi).
rewrite /mpart Hszla.
rewrite !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
rewrite inE /= (nth_enum_ord (Ordinal H0) Hi).
case: ssrnat.ltnP => H /=; rewrite ?addn0 ?addn1.
- by apply anti_leq; rewrite H Hstrip1.
- by apply anti_leq; rewrite H Hstrip.
Qed.

Lemma nohasincr_setdiff d k (la : 'P_d) (mu : 'P_(d + k)) :
  size mu <= n -> size la <= n ->
  vb_strip la mu -> ~~ hasincr la (setdiff la mu).
Proof using .
move=> Hszmu Hszla Hstrip.
apply/hasPn => i; rewrite mem_iota add0n => /andP[_ Hi].
rewrite /mnm_add [val _]/= !nth_add_setdiff //.
rewrite eq_sym ltn_eqF // ltnS.
by have [_]:= (is_partP _ (intpartnP mu)); apply.
Qed.

Lemma add_mesymK d k (la : 'P_d) :
  size la <= n ->
  {in [pred mu : 'P_(d + k) | vb_strip la mu && (size mu <= n)],
  cancel (fun mu : 'P_(d + k) => setdiff la (val mu)) (add_mesym k la)}.
Proof using .
move=> Hszla mu /=; rewrite inE => /andP [] Hstrip Hsz.
have:= vb_stripP (intpartnP _) (intpartnP _) Hstrip => Hstr.
apply/eqP/(part_eqP (intpartnP _) (intpartnP _)) => i.
rewrite /add_mesym /=.
rewrite Hszla card_setdiff // eq_refl /= nohasincr_setdiff //.
by rewrite nth_rem_trail0 nth_add_setdiff.
Qed.


(** * Piery's rule for alternating polynomials *)
Theorem alt_mpart_syme d (la : 'P_d) k :
  size la <= n ->
  ('a_(mpart la + rho) * 'e_k =
  \sum_(mu : 'P_(d + k) | vb_strip la mu && (size mu <= n))
     'a_(mpart mu + rho))%R.
Proof using .
rewrite alt_syme => Hszla.
rewrite (bigID (hasincr la)) /=.
rewrite big1 ?add0r; last by move=> i /andP [] _ /hasincr0.
under eq_bigr => i /andP[/add_mesymE H{}/H <- //].
rewrite (reindex_onto _ _ (add_mesymK Hszla)).
apply eq_bigl => S; rewrite inE -andbA.
apply/idP/and3P => [H | [Hstrip Hszle /eqP HS]].
- split.
  + apply/(vb_stripP (intpartnP _) (intpartnP _)) => i /=.
    rewrite Hszla H /= nth_rem_trail0.
    case: (ssrnat.ltnP i n) => Hi; first last.
      rewrite !nth_default //; first last.
      - exact: leq_trans Hszla Hi.
      - by rewrite size_map size_enum_ord.
    have H0 : 0 < n by apply: (leq_ltn_trans _ Hi).
    rewrite /mpart Hszla /= (nth_map (Ordinal H0)) ?size_enum_ord // !mnmE.
    rewrite (nth_enum_ord (Ordinal H0) Hi).
    by case: (_ \in _); rewrite ?addn0 ?addn1 leqnn ltnW.
  + rewrite /add_mesym /= Hszla H /=.
    apply (leq_trans (size_rem_trail0 _)).
    by rewrite size_map size_enum_ord.
  + rewrite /setdiff; apply/eqP/setP => i.
    rewrite inE /= Hszla H /= nth_rem_trail0.
    have H0 : 0 < n by apply: (leq_ltn_trans _ (ltn_ord i)).
    rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
    rewrite /mpart Hszla nth_ord_enum /= (mnm_nth 0) /= mnmE.
    rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
    rewrite nth_ord_enum.
    by case: (i \in S); rewrite ?addn0 ?addn1 ?ltnSn ?ltnn.
- rewrite -HS card_setdiff // eq_refl andTb.
  exact: nohasincr_setdiff.
Qed.

Lemma vb_strip_rem_col0 d (la : 'P_d) :
  vb_strip (conj_part (behead (conj_part la))) la.
Proof using .
rewrite -{2}(conj_intpartnK la) /=.
have Hc : is_part (conj_part la) by apply is_part_conj.
apply hb_strip_conj => //; first by apply is_part_behead.
elim: {d la} (conj_part la) Hc => [| s0 s IHs] //= /andP[H0 {}/IHs].
case: s H0 => [| s1 s]//= -> ->.
by rewrite leqnn.
Qed.

Lemma vb_strip_lexi (d1 k : nat) (la : 'P_(d1 + k)) (mu : seq nat) :
  vb_strip mu la ->
  sumn mu = d1 ->
  is_part mu -> (val la <= incr_first_n mu k :> seqlexi nat)%O.
Proof using .
rewrite /=.
elim: mu d1 k la => /= [| m0 mu IHmu] d1 k la Hstr.
  have {}Hstr := vb_stripP (is_true_true : is_part [::]) (intpartnP _) Hstr.
  move=> Hd1 _; subst d1.
  suff /= -> : val la = nseq k 1%N by [].
  case: la Hstr => la /=; rewrite add0n => /andP [] /eqP.
  elim: la k => [//= | l0 la IHla] /= k Hk; first by rewrite -Hk.
  rewrite -/(is_part (l0 :: la)) => Hpart Hstr.
  have Hl0 : l0 = 1.
    have := Hstr 0 => /=.
    have /= := part_head_non0 Hpart.
    by case l0 => [| [| l0']].
  subst l0; rewrite -Hk add1n /= {1}(IHla (sumn la)) //.
  - exact: (is_part_consK Hpart).
  - move=> i; have /= := Hstr i.+1.
    by rewrite !nth_nil.
case: la Hstr => la Hla /= Hstr.
case: k Hla => [| k] Hla Hd1; subst d1;
               rewrite -/(is_part (m0 :: mu)) /= => /andP[_ Hp].
  have Hincl := vb_strip_included Hstr.
  move: Hla; rewrite addn0 /= -/(sumn (m0 :: mu)) => /andP[/eqP/esym Heq Hla].
  by rewrite (included_sumnE Hla Hincl Heq).
case: la Hstr Hla => [//= |s0 la] /= /andP[/andP[ms0 sm0] Hstrip].
move=> /andP[/eqP Heq /andP[_ Hs]].
rewrite leEseqlexi leEnat sm0 /=.
case: (leqP s0 m0) => //= Hm0.
have Hs0 : s0 = m0.+1 by apply anti_leq; rewrite Hm0 sm0.
subst s0 => /= {Hm0}.
move: Heq; rewrite addSn addnS => /eqP; rewrite eqSS -addnA => /eqP /addnI Heq.
have Hla : is_part_of_n (sumn mu + k)%N la.
  by rewrite /= Heq eq_refl Hs.
exact: (IHmu _ _ (IntPartN Hla)).
Qed.

End Alternant.


(** * Jacobi's definition of schur function *)
Section SchurAlternantDef.

Variable (n0 : nat) (R : comRingType).
Local Notation n := (n0.+1).
Local Notation rho := (rho n).
Local Notation "''s_[' k ']'" := (Schur n0 R k).
Local Notation "''a_' k" := (@alternpol n R 'X_[k]).

Lemma Schur_cast d d' (la : 'P_d) (Heq : d = d') :
  Schur n0 R (cast_intpartn Heq la) = 's_[la].
Proof using . by subst d'; congr Schur. Qed.

Theorem alt_SchurE d (la : 'P_d) :
  size la <= n -> 'a_rho * 's_[la] = 'a_(mpart la + rho).
Proof using .
suff {d la} H : forall b d, d <= b -> forall (la : 'P_d),
  size la <= n -> 'a_rho * 's_[la] = 'a_(mpart la + rho) by apply: H.
elim=> [|b IHb] d Hd la.
  move: Hd; rewrite leqn0 => /eqP Hd; subst d.
  rewrite Schur0 mulr1 -{1}(add0m rho)=> _; congr 'a_(_ + rho).
  by rewrite val_intpartn0 /mpart /= mnmP => i; rewrite !mnmE /=.
case: (leqP d b) => Hdb; first exact: (IHb _ Hdb).
have {Hdb}Hd : d = b.+1 by apply anti_leq; rewrite Hd Hdb.
elim/(finord_wf (T := [finPOrderType of 'PLexi_d])) : la => la IHla Hszla.
pose k := head 1%N (conj_intpartn la).
pose p1 := behead (conj_intpartn la); pose d1 := sumn p1.
have Hk : (d = d1 + k)%N.
  have:= sumn_intpartn (conj_intpartn la).
  rewrite /d1 /k /p1 /=.
  by case: (conj_part la) => [| [//= | c0] c] /=; rewrite Hd // addnC.
have Hd1 : d1 <= b.
  rewrite -ltnS -Hd Hk.
  have:= part_head_non0 (intpartnP (conj_intpartn la)).
  rewrite -/k; case k => //= k' _.
  by rewrite addnS ltnS; exact: leq_addr.
have p1P : is_part_of_n d1 p1 by rewrite /= /d1 eq_refl is_part_behead.
pose mu := IntPartN p1P.
have Hszmu : size (conj_intpartn mu) <= n.
  rewrite size_conj_part //.
  apply: (leq_trans _ Hszla); rewrite /= /p1.
  have := size_conj_part (intpartnP (conj_intpartn la)).
  rewrite conj_partK // => ->.
  have:= (intpartnP (conj_intpartn la)) => /=.
  by case: (conj_part la) => [| c0 [| c1 c]] //= /andP [].
have := alt_mpart_syme R k Hszmu.
have {IHb Hszmu Hd1} <- := IHb _ Hd1 (conj_intpartn mu) Hszmu.
rewrite -mulrA mesym_SchurE Pieri_colpartn.
rewrite (bigID (fun P0 : 'P_(d1 + k) => (size P0 <= n))) /= addrC.
rewrite big1 ?add0r; first last.
  by move=> i /andP [] _; rewrite -ltnNge; exact: Schur_oversize.
rewrite mulr_sumr.
pose la' := cast_intpartn Hk la.
rewrite (bigID (pred1 la')) [X in _ = X](bigID (pred1 la')) /=.
set prd := BIG_P.
have Hprd : prd =1 pred1 la'.
  rewrite {}/prd => nu /=.
  case: eqP => [-> | _]; rewrite ?andbT ?andbF // {nu}.
  rewrite cast_intpartnE {la' mu d1 Hk p1P} Hszla andbT /p1 /=.
  exact: vb_strip_rem_col0.
rewrite !(eq_bigl _ _ Hprd) {Hprd prd} /= !big_pred1_eq cast_intpartnE.
set A := (X in _ + X); set B := (X in _ = _ + X).
suff -> : A = B by move=> /addIr <- {A B}; rewrite Schur_cast.
apply eq_bigr => {A B} nu /andP[/andP[Hstrip Hsznu] Hnu].
pose nu' := cast_intpartn (esym Hk) nu.
have Hlexi : (val nu' < la :> seqlexi _)%O.
  rewrite cast_intpartnE /= {nu'}.
  rewrite lt_neqAle; apply/andP; split.
    move: Hnu; apply contra => /eqP H.
    by apply/eqP; apply val_inj; rewrite cast_intpartnE.
  rewrite {Hnu Hsznu la'}.
  have /= -> : val la = incr_first_n (conj_part p1) k.
    move: Hk; rewrite /d1 /p1 /= -{2}(conj_intpartnK la) /=.
    rewrite -{1}(sumn_intpartn (conj_intpartn la)) /=.
    case: (conj_part la) => [//= | p0 p] /=; first by rewrite add0n => <-.
    rewrite addnC -{2}(addKn (sumn p) k) => <-.
    by rewrite addKn.
  have:= intpartnP (conj_intpartn mu).
  have /= {Hk p1P mu} := sumn_intpartn (conj_intpartn mu).
  exact: vb_strip_lexi.
have Hsznu' : size nu' <= n by rewrite cast_intpartnE.
have := IHla nu' Hlexi Hsznu'.
rewrite Schur_cast => ->.
by rewrite cast_intpartnE.
Qed.

Import LeqGeqOrder.

Lemma mcoeff_alt_SchurE d (la mu : 'P_d) :
  size la <= n -> size mu <= n ->
  ('a_rho * Schur n0 R la)@_(mpart mu + rho) = (la == mu)%:R.
Proof.
move=> Hszla Hszmu; rewrite (alt_SchurE Hszla).
have sorted_mpart_rho (nu : 'P_d) : sorted gtn ((mpart nu) + rho)%MM.
  apply/(sorted_strictP 0%N) => // i j.
  rewrite size_tuple => /andP [Hij Hj]; have Hi := ltn_trans Hij Hj.
  rewrite -[i]/((Ordinal Hi) : nat) -mnm_nth.
  rewrite -[j]/((Ordinal Hj) : nat) -mnm_nth /=.
  rewrite !mnmE /= /mpart.
  have :  n - 1 - j < n - 1 - i.
    apply ltn_sub2l => //; apply (leq_trans Hij).
    by move: Hj; case n => // m; rewrite ltnS subn1 /=.
  case: (leqP (size nu) n) => _; rewrite !mnmE ?add0n //=.
  rewrite -addnS; apply leq_add.
  have [_] := is_part_ijP _ (intpartnP nu); apply.
  exact: ltnW.
have : perm_eq (mpart la + rho)%MM (mpart mu + rho)%MM = (la == mu).
  apply/idP/eqP => [Hperm | -> //].
  suff : (mpart la + rho)%MM = (mpart mu + rho)%MM.
    move/eqP; rewrite eqm_add2r => /eqP/(congr1 (@partm n))/(congr1 pval).
    by rewrite !mpartK //; apply: val_inj.
  apply val_inj; apply val_inj => /=.
  exact: (irr_sorted_eq _ _ (sorted_mpart_rho la) (sorted_mpart_rho mu)
                        (perm_mem Hperm)).
case: eqP => [-> |] _.
- apply mcoeff_alt.
  exact: (sorted_uniq _ _ (sorted_mpart_rho mu)).
- rewrite /alternpol linear_sum => Hperm /=.
  rewrite big1 // => s _.
  rewrite linearZ /= msymX mcoeffX.
  case: eqP => [Habs |]; last by rewrite mulr0.
  exfalso.
  move: Hperm => /tuple_permP; apply.
  rewrite -{1}Habs; exists s; congr tval; apply eq_from_tnth => i.
  by rewrite -mnm_tnth !tnth_mktuple permK.
Qed.

End SchurAlternantDef.


(** ** Schur polynomials are symmetric at last *)
Section IdomainSchurSym.

Variable (n0 : nat) (R : idomainType).
Local Notation RR := (GRing.IntegralDomain.ringType R).
Local Notation n := (n0.+1).
Local Notation rho := (rho n).
Local Notation "''s_' k" := (Schur n0 R k).
Local Notation "''a_' k" := (@alternpol n R 'X_[k]).

Theorem alt_uniq d (la : 'P_d) (s : {mpoly R[n]}) :
  size la <= n -> 'a_rho * s = 'a_(mpart la + rho) -> s = 's_la.
Proof using . by move=> /(alt_SchurE R) <- /(mulfI (alt_rho_non0 n R)). Qed.

Theorem Schur_sym_idomain d (la : 'P_d) : 's_la \is symmetric.
Proof using .
case: (leqP (size la) n) => [Hla|].
- have := alt_anti R (mpart la + rho).
  rewrite -(alt_SchurE _ Hla) -sym_antiE //; last exact: alt_anti.
  exact: alt_rho_non0.
- move/Schur_oversize ->; exact: rpred0.
Qed.

End IdomainSchurSym.


Section RingSchurSym.

Variable (n0 : nat) (R : ringType).
Local Notation n := (n0.+1).
Local Notation "''s_' k" := (Schur n0 R k).

Theorem Schur_sym d (la : 'P_d) : 's_la \is symmetric.
Proof using .
have -> : 's_la = map_mpoly intr (Schur _ [ringType of int] la).
  rewrite /Schur /polylang /commword raddf_sum /=; apply eq_bigr => i _ /=.
  by rewrite rmorph_prod /=; apply eq_bigr => {}i _ ; rewrite map_mpolyX.
apply/issymP => s.
have:= Schur_sym_idomain n0 [idomainType of int] la => /issymP/(_ s) {2}<-.
by rewrite msym_map_mpoly.
Qed.

Lemma Schur_homog (d : nat) (la : 'P_d) : 's_la \is d.-homog.
Proof using .
rewrite Schur_tabsh_readingE /polylang /commword.
apply rpred_sum => [[t Ht]] _ /=.
move: Ht => /eqP <-; elim: t => [| s0 s IHs]/=.
  rewrite big_nil; exact: dhomog1.
rewrite big_cons -(add1n (size s)); apply dhomogM; last exact: IHs.
by rewrite dhomogX /= mdeg1.
Qed.

End RingSchurSym.


(** * Kostka numbers *)
Local Open Scope nat_scope.

Section DefsKostkaMon.

Variables (d : nat) (la : 'P_d) (n : nat).
Implicit Type m : 'X_{1..n.+1}.
Definition eval (w : seq 'I_n.+1) := [tuple count_mem i w | i < n.+1].
Definition KostkaTab m := [set t : tabsh la | eval (to_word t) == m].
Definition KostkaMon m := #|KostkaTab m|.

Lemma sumn_eval w : sumn (eval w) = size w.
Proof.
rewrite sumnE /eval big_tuple.
under eq_bigr do rewrite tnth_mktuple.
by rewrite sum_count_mem count_predT.
Qed.

Lemma KostkaMon_sumeval m :
  mdeg m != sumn la -> KostkaMon m = 0.
Proof.
move=> H; apply/eqP; move: H.
apply contraR; rewrite cards_eq0 => /set0Pn /= [t].
rewrite /mdeg -sumnE inE => /eqP <-{m}.
by rewrite sumn_eval size_to_word /size_tab shape_tabsh.
Qed.

Lemma evalE (R : ringType) m w :
  (\prod_(v <- w) 'X_v)@_m = (eval w == m)%:R :> R.
Proof.
rewrite -[X in X@_m](big_map (fun i : 'I_n.+1 => (U_(i))%MM) xpredT).
rewrite /eval mpolyX_prod mcoeffX; congr (nat_of_bool _)%:R.
apply/eqP/eqP => [/(congr1 val) /= <- {m}| H].
- elim: w => [| w0 w IHw] /=; first by rewrite big_nil.
  rewrite big_cons; apply eq_from_tnth => i.
  move/(congr1 (fun t => tnth t i)) : IHw; rewrite !tnth_mktuple => ->.
  by rewrite mnmE -mnm_tnth.
- apply val_inj => /=; rewrite -H {m H}.
  elim: w => [| w0 w IHw] /=; first by rewrite big_nil.
  rewrite big_cons; apply eq_from_tnth => i.
  move/(congr1 (fun t => tnth t i)) : IHw.
  by rewrite !tnth_mktuple mnmE -mnm_tnth => ->.
Qed.

Lemma Kostka_Coeff (R : ringType) m : (Schur n R la)@_m = (KostkaMon m)%:R.
Proof.
rewrite /Schur linear_sum /= /KostkaMon.
rewrite (bigID (fun t : tabsh la => t \in KostkaTab m)) /=.
rewrite addrC big1 ?add0r; first last => [i|].
  by rewrite /KostkaTab inE evalE => /negbTE ->.
under eq_bigr => i do rewrite /KostkaTab inE evalE => /eqP ->; rewrite eqxx.
by rewrite sumr_const; congr _%:R; apply eq_card.
Qed.

Lemma perm_KostkaMon m1 m2 :
  perm_eq m1 m2 -> KostkaMon m1 = KostkaMon m2.
Proof.
move=> /tuple_permP [s /val_inj Hs].
suff: Posz (KostkaMon m1) = Posz (KostkaMon m2) by move => [].
rewrite -!natz -!(Kostka_Coeff _ (Multinom _)).
set mu1 := Multinom m1.
set mu2 := Multinom m2.
have {Hs} -> : mu1 = [multinom mu2 (s i) | i < n.+1].
  apply val_inj => /=; rewrite Hs.
  by apply eq_from_tnth => i; rewrite tnth_mktuple.
by rewrite -mcoeff_sym (issymP _ (Schur_sym _ _ _)).
Qed.

Lemma tab_eval_partdom (t : tabsh la) : partdom (eval (to_word t)) la.
Proof.
apply/partdomP => i; rewrite -(shape_tabsh t).
case: (ssrnat.leqP i n.+1) => [Hi| /ltnW Hi]; first last.
  rewrite !take_oversize ?size_tuple //; first last.
    by rewrite size_map (leq_trans (size_tabsh _)).
  by rewrite sumn_eval size_to_word.
rewrite sumn_take big_mkord (big_ord_widen _ _ Hi).
under eq_bigr do rewrite (nth_map ord0) ?size_enum_ord // nth_ord_enum.
rewrite sum_count_mem /= /to_word seq.count_flatten map_rev sumn_rev.
rewrite -{1}(cat_take_drop i t) map_cat sumn_cat addnC.
rewrite sumnE big_map big_seq big1 ?add0n; first last.
  move=> /= s Hs; rewrite -(nth_index [::] Hs).
  rewrite nth_drop; apply/eqP; rewrite -leqn0 leqNgt -has_count -all_predC.
  under eq_all => j /= do rewrite -leqNgt.
  have:= all_ltn_nth_tabsh t (i + index s (drop i t)); apply sub_all.
  by move=> j; apply (leq_trans (leq_addr _ _)).
rewrite /shape -map_take !sumnE !big_map.
by apply leq_sum => /= j _; apply: count_size.
Qed.

Lemma KostkaMon_partdom m : KostkaMon m != 0 -> partdom m la.
Proof.
rewrite cards_eq0 => /set0Pn [/= t]; rewrite inE => /eqP <-.
exact: tab_eval_partdom.
Qed.

End DefsKostkaMon.


Section KostkaEq.

Variables (d : nat) (la : 'P_d).

Lemma Kostka_mnmwiden n (m : 'X_{1..n.+1}) :
  KostkaMon la m = KostkaMon la (mnmwiden m).
Proof.
rewrite /KostkaMon /KostkaTab.
pose ext_fun := fun (t : tabsh la) =>
              [seq [seq (widen_ord (leqnSn n.+1) i) | i <- r] | r <- t].
have extP t : is_tab_of_shape la (ext_fun t).
  rewrite /is_tab_of_shape /=; apply/andP; split.
  - by rewrite -incr_tab ?tabshP.
  - rewrite -(shape_tabsh t) /shape /ext_fun -map_comp.
    by apply/eqP/eq_map => s; rewrite /= size_map.
have ext_inj : injective (fun t => TabSh (extP t)).
  move=> u v [] /= H; apply val_inj => /=.
  have:= H => /(congr1 size); rewrite !size_map => Hsz.
  apply (eq_from_nth (x0 := [::])) => // r Hr.
  move: H => /(congr1 (fun t => nth [::] t r)).
  rewrite !(nth_map [::]) -?Hsz // => H.
  have:= H => /(congr1 size); rewrite !size_map => Hsz1.
  apply (eq_from_nth (x0 := ord0)) => // c Hc.
  move: H => /(congr1 (fun t => nth ord0 t c)).
  rewrite !(nth_map ord0) -?Hsz1 //= => /(congr1 val) /= Heq.
  by apply val_inj.
rewrite -(card_imset _ ext_inj); congr #|pred_of_set _|.
apply/setP => /= t2; rewrite inE /=.
apply/imsetP/eqP => /= [[t ] | Hm].
- rewrite inE /= => /eqP Hm /(congr1 val)/= Heq.
  rewrite /eval; apply eq_from_tnth => i; rewrite tnth_mktuple.
  case: (ssrnat.ltnP i n.+1) => Hi.
  + rewrite [RHS](tnth_nth 0) /= nth_rcons size_tuple Hi -{}Hm {}Heq /eval.
    rewrite (nth_map ord0) ?size_enum_ord //.
    have -> : to_word (ext_fun t) =
              [seq widen_ord (leqnSn n.+1) i | i <- to_word t].
      by rewrite /ext_fun /to_word -map_rev map_flatten.
    case: i Hi => [i Hin] /= Hi.
    rewrite count_map; apply eq_count => /= [] [j Hj] /=.
    by apply/eqP/eqP => /(congr1 val) /= Heq;
                       apply val_inj; rewrite /= Heq nth_enum_ord.
  + rewrite [RHS](tnth_nth 0) /= nth_rcons size_tuple.
    have:= Hi; rewrite ltnNge -ltnS => /negbTE ->; rewrite if_same.
    apply/count_memPn; rewrite {}Heq.
    apply/negP => /flattenP /= [rt2].
    rewrite mem_rev /ext_fun => /mapP [/= rt _ ->{rt2}] /mapP [/= j _].
    move=> /(congr1 val) /= Heq.
    move: Hi; rewrite Heq => /leq_ltn_trans/(_ (ltn_ord j)).
    by rewrite ltnn.
- have mt2 i : i \in to_word t2 -> i < n.+1.
    apply contraLR; rewrite -leqNgt => Hi; apply/count_memPn.
    move: Hm; rewrite /eval => /(congr1 (fun t => tnth t i)).
    rewrite tnth_mktuple => ->.
    by rewrite [LHS](tnth_nth 0) /= nth_rcons size_tuple ltnNge Hi /= if_same.
  pose t : seq (seq 'I_n.+1) := [seq [seq inord (val i) | i <- r] | r <- t2].
  have Ht : is_tab_of_shape la t.
    rewrite /is_tab_of_shape /=; apply/andP; split.
    + rewrite -incr_tab ?tabshP // => [] [i Hio] [j Hjo] /mt2 /= Hi /mt2 /= Hj.
      by rewrite !ltEsub /= !inordK.
    + rewrite /t {t} -(shape_tabsh t2) /shape /ext_fun -map_comp.
      by apply/eqP/eq_map => s; rewrite /= size_map.
  exists (TabSh Ht).
  + rewrite inE /= /t {t Ht}.
    rewrite /eval; apply/eqP/eq_from_tnth => i; rewrite tnth_mktuple.
    rewrite /to_word -map_rev -map_flatten -/(to_word t2) count_map.
    have -> : tnth m i = tnth (rcons_tuple m 0) (widen_ord (leqnSn n.+1) i).
      by rewrite !(tnth_nth 0) nth_rcons /= size_tuple ltn_ord.
    move: Hm; rewrite /eval =>
       /(congr1 (fun t => tnth t (widen_ord (leqnSn n.+1) i))) <-.
    rewrite tnth_mktuple; apply eq_in_count => j /= /mt2 Hj.
    apply/eqP/eqP => /(congr1 val) /=.
    * by rewrite inordK // => Heq; apply val_inj.
    * by move=> ->; apply val_inj; rewrite /= inordK.
  + apply val_inj => /=.
    apply (eq_from_nth (x0 := [::])); first by rewrite !size_map.
    move=> r Hr; rewrite (nth_map [::]); last by rewrite !size_map.
    apply (eq_from_nth (x0 := inh)).
    * by rewrite size_map -!nth_shape !shape_tabsh.
    * move=> c Hc.
      rewrite (nth_map inh); last by move: Hc; rewrite -!nth_shape !shape_tabsh.
      apply val_inj => /=.
      rewrite /t /= (nth_map [::]) // (nth_map inh) //.
      rewrite inordK //; apply: mt2.
      rewrite -/(get_tab _ (_, _)); apply: mem_to_word.
      by rewrite /in_shape nth_shape.
Qed.

End KostkaEq.


Section Kostka.

Variable d : nat.
Implicit Type la : 'P_d.

(* We prepend a 0 to take care of the empty partition *)
Definition Kostka la mu :=
  KostkaMon la (mpart (n := (size mu).-1.+1) mu).
Local Notation "''K' ( la , mu )" := (Kostka la mu)
  (at level 8, format "''K' ( la ,  mu )") : nat_scope.
Local Notation "''K' ( la , mu )" := ((Kostka la mu)%:R : int)
  (at level 8, format "''K' ( la ,  mu )") : ring_scope.

Local Arguments mpart n s : clear implicits.

Lemma mpartS n mu :
  size mu <= n -> mnmwiden (mpart n mu) = mpart n.+1 mu.
Proof.
case: n => [|n].
  rewrite leqn0 => /eqP; case: mu => //= _.
  rewrite /mpart /=.
  suff Hm0 (n) : [multinom nth 0 [::] i | i < n] = 0%MM.
    by rewrite !Hm0 mnmwiden0.
  by apply/mnmP => i; rewrite !mnmE nth_default.
move => H.
rewrite /mpart H.
have:= H; rewrite -ltnS => /ltnW ->.
apply mnmP => i; rewrite /mnmwiden.
rewrite (mnm_nth 0) /= nth_rcons size_map size_enum_ord if_same mnmE.
case: ssrnat.ltnP => Hi.
- by rewrite (nth_map ord0) ?nth_enum_ord ?size_enum_ord.
- by rewrite nth_default //; apply: (leq_trans H Hi).
Qed.

Lemma Kostka_any la mu n :
  size mu <= n.+1 -> 'K(la, mu) = KostkaMon la (mpart n.+1 mu).
Proof.
rewrite /Kostka => Hsz.
case: (altP (size mu =P n.+1)) => [-> //=| H].
have {H}Hsz : size mu <= n.
  by move: Hsz; rewrite leq_eqVlt (negbTE H) /= ltnS.
rewrite -(subnKC Hsz).
elim: (n - size mu) => {n Hsz}[|n ->] /=.
  rewrite addn0; have := mpartS (leqnn (size mu)).
  by case: (size mu) => //= n; rewrite Kostka_mnmwiden => ->.
rewrite Kostka_mnmwiden addnS; congr KostkaMon.
rewrite /mpart -addnS; symmetry; rewrite -{2}addnS !leq_addr !addnS.
apply mnmP => i; rewrite /mnmwiden !mnmE.
rewrite (mnm_nth 0) /= nth_rcons size_map size_enum_ord if_same.
case: ssrnat.ltnP => Hi.
- by rewrite (nth_map ord0) ?nth_enum_ord // size_enum_ord.
- by apply nth_default; apply: (leq_trans _ (ltnW Hi)); apply leq_addr.
Qed.

Lemma Kostka_sumnE la mu : d != sumn mu -> Kostka la mu = 0.
Proof.
rewrite /Kostka => Hd; apply KostkaMon_sumeval.
by rewrite eq_sym sumn_intpartn mdeg_mpart ?leqSpred.
Qed.

Lemma Kostka_size0 la mu :
  size la > size mu -> 'K(la, mu) = 0.
Proof.
move=> H; apply/eqP; move: H.
case Hsz : (size mu) => [|sz] /=.
  move=> Hla; rewrite cards_eq0 Hsz /=.
  move: Hsz => /eqP/nilP ->.
  rewrite -subset0; apply/subsetP => t; rewrite !inE.
  move=> /eqP/(congr1 (fun t : _.-tuple nat => sumn t)).
  rewrite sumn_eval size_to_word sumn_mpart //= => /(tab0 (tabshP _)) Ht.
  by move: Hla; rewrite -(shape_tabsh t) size_map Ht.
apply contraLR; rewrite cards_eq0 -leqNgt => /set0Pn /= [t _].
have := size_tabsh t.
by rewrite -(shape_tabsh t) size_map [X in _ <= X.-1.+1]Hsz /=.
Qed.

Lemma Kostka_partdom (la mu : 'PDom_d) : 'K(la, mu) != 0 -> (mu <= la)%O.
Proof.
rewrite /Kostka => /KostkaMon_partdom.
rewrite /mpart leqSpred => /partdomP Hdom.
apply/partdomP => i; move/(_ i): Hdom; congr (_ <= _).
rewrite !sumn_take; apply eq_bigr => {}i _.
case: (ssrnat.ltnP i (size mu)) => Hi.
- have -> : (size mu).-1.+1 = (size mu) by case: (size mu) Hi.
  by rewrite -{1}[i]/((Ordinal Hi) : nat) -mnm_nth mnmE.
- rewrite [RHS]nth_default //.
  case: mu Hi => [[|m mu] Hmu] Hi.
  + case: i Hi => [|i].
    * by rewrite -[X in nth _ _ X]/((@ord0 0) : nat) -mnm_nth mnmE.
    * by rewrite nth_default //= size_tuple card_ord.
  + move: Hmu Hi; rewrite /= => _ => Hi.
    by rewrite nth_default // size_tuple card_ord.
Qed.

Lemma Kostka0 (la mu : 'PDom_d) : ~~ (mu <= la)%O -> 'K(la, mu) = 0.
Proof.
by move=> H; apply/eqP; move: H; apply contraR; apply Kostka_partdom.
Qed.

Lemma Kostka_diag la : 'K(la, la) = 1.
Proof.
case Hla : (size la) => [|szla].
  rewrite /Kostka /KostkaMon Hla.
  move: Hla => /eqP/nilP Hla.
  have {Hla} Hd : d = 0 by rewrite -(sumn_intpartn la) Hla.
  subst d.
  have Ht : is_tab_of_shape la ([::] : seq (seq 'I_1)) by rewrite val_intpartn0.
  rewrite [KostkaTab _ _](_ : _ = [set TabSh Ht]) ?cards1 //.
  apply/setP => t; rewrite !inE; apply/eqP/eqP => [|->]/=.
  - rewrite /mpart val_intpartn0 /= => /(congr1 (fun t : 1.-tuple nat => sumn t)).
    rewrite sumn_eval size_to_word /=.
    rewrite (map_comp _ nat_of_ord) val_enum_ord /= addn0.
    by move=> /(tab0 (tabshP _)) => Ht0; apply val_inj.
  - rewrite /to_word /=; apply eq_from_tnth => i.
    by rewrite /mpart val_intpartn0 /= !tnth_mktuple /=.
rewrite (Kostka_any la (n := szla)) /KostkaMon ?Hla //.
have Hntht j :
  nth [::] [seq nseq (nth 0 la (i : nat)) i | i : 'I_szla.+1] j =
    nseq (nth 0 la j) (inord j).
  case: (ssrnat.ltnP j szla.+1) => Hj.
  - rewrite (nth_map ord0) ?size_enum_ord // nth_enum_ord //.
    by congr nseq; apply val_inj; rewrite /= inordK // nth_enum_ord.
  - by rewrite !nth_default ?Hla // size_map size_enum_ord.
have Hleqla : size la <= szla.+1 by rewrite Hla.
rewrite [KostkaTab _ _](_ : _ = [set tabrowconst Hleqla]) ?cards1 //.
apply/setP => /= t; rewrite !inE; apply/eqP/eqP => [|->]/=.
- rewrite /mpart Hla ltnSn => H; apply/eqP/tab_eqP => // /= i.
  rewrite take_oversize; last by rewrite size_map size_enum_ord -Hla.
  rewrite {}Hntht.
  have Hsht := shape_tabsh t.
  elim: i.+1 {-2}i (ltnSn i) => {i} [//| i IHi] j.
  rewrite ltnS leq_eqVlt => /orP [/eqP ->{j}|]; last exact: IHi.
  have Hszt : size t = szla.+1.
    by rewrite -(size_map size) -/(shape t) Hsht Hla.
  case: (ssrnat.ltnP i (size la)) => Hi; first last.
    by rewrite !nth_default // Hszt -Hla.
  rewrite Hla in Hi.
  rewrite -Hsht nth_shape; apply/all_pred1P; rewrite all_count -nth_shape Hsht.
  have:= congr1 (fun t => tnth t (inord i)) H.
  rewrite /eval !tnth_mktuple inordK // => <-.
  rewrite /to_word seq.count_flatten map_rev sumn_rev sumnE big_map.
  rewrite (big_nth [::]) Hszt big_mkord.
  rewrite (bigD1 (inord i)) //= inordK // big1 ?addn0 //.
  move=> j Hj.
  case: (ssrnat.ltnP j i) => [/IHi -> | Hij].
  - rewrite count_nseq /= inord_val.
    by move: Hj => /negbTE ->; rewrite mul0n.
  - have {Hi}Hij : i < j.
      rewrite ltn_neqAle Hij andbT.
      by move: Hj; apply contra => /eqP ->; rewrite inord_val.
    rewrite (eq_in_count (a2 := pred0)) ?count_pred0 // => /= x.
    rewrite eq_sym /eq_op /= (inordK (ltn_trans Hij _)) //.
    by move=> /(allP (all_ltn_nth_tabsh _ _)) /(leq_trans Hij) /ltn_eqF ->.
- apply eq_from_tnth => i.
  rewrite take_oversize; last by rewrite size_map size_enum_ord -Hla.
  rewrite /eval /mpart Hla ltnSn !tnth_mktuple.
  rewrite /to_word seq.count_flatten map_rev sumn_rev -map_comp.
  rewrite sumnE big_map enumT -/(index_enum _) (bigD1 i) //=.
  rewrite big1 ?addn0 ?count_nseq /= ?eq_refl ?mul1n //.
  move=> j Hj; apply/count_memPn/nseqP => [] [Heq _].
  by rewrite Heq eq_refl in Hj.
Qed.

End Kostka.


(** ** Converting between standard tableau and tableau over ['I_n].

The type [stdtabsh sh] is a subtype of [seq nat] whereas [tabsh sh] is a subtype
of [seq 'I_n.+1]. We provide two conversion functions [tabnat_of_ord] and
[tabord_of_nat] *)
Section StdKostka.

Variables (d : nat) (la : 'P_d).

Section Nvar.

Variable n : nat.
Hypothesis Hd : d <= n.+1.

Let td := [tuple ((i < d) : nat) | i < n.+1].

Lemma stdtabsh_eval_to_word (t : stdtabsh la) :
  eval [seq inord i | i <- to_word t] = td.
Proof.
apply/eq_from_tnth => i.
case: t => /= t /andP [/andP [Ht Hstd] /eqP Hsh].
rewrite /eval !tnth_mktuple.
move: Hstd; rewrite /is_std.
rewrite size_to_word /size_tab Hsh sumn_intpartn => Hstd.
rewrite count_map (eq_in_count (a2 := pred1 (i : nat))); first last.
  move=> /= j; rewrite (perm_mem Hstd) mem_iota /= add0n.
  move => /leq_trans /(_ Hd) Hj.
  by rewrite {1}/eq_op /= inordK.
by rewrite (seq.permP Hstd) count_uniq_mem ?iota_uniq // mem_iota /= add0n.
Qed.

Lemma tabsh_is_std (t : tabsh la) :
  eval (to_word t) = td -> is_std [seq (i : nat) | i : 'I_n.+1 <- to_word t].
Proof.
rewrite /is_std => Hev; apply/seq.permP => P.
rewrite count_map -sum_count_mem.
under eq_bigr => i _.
  move/(congr1 (fun t => tnth t i)) : Hev; rewrite !tnth_mktuple => ->.
  by rewrite over.
rewrite size_map size_to_word /size_tab shape_tabsh sumn_intpartn.
rewrite -sum1_count /= -(big_mkord _ (fun i => i < d : nat)).
rewrite -{2}(subn0 d) -/(index_iota 0 d) (big_nat_widen _ _ _ _ _ Hd).
rewrite (bigID (gtn d)) /= addnC big1 ?add0n; first last.
  by move=> i /andP[_ /negbTE ->].
by apply eq_bigr => i /andP[_ ->].
Qed.

Definition tabnat_of_ord_fun (t : tabsh la) :=
  if (eval (to_word t) == td)
  then [seq [seq (i : nat) | i : 'I_n.+1 <- r] | r <- t]
  else hyper_stdtabsh la.

Definition tabord_of_nat_fun (t : stdtabsh la) : seq (seq 'I_n.+1) :=
  [seq map inord r | r <- t].

Lemma tabnat_of_ord_subproof (t : tabsh la) :
  is_stdtab_of_shape la (tabnat_of_ord_fun t).
Proof.
rewrite /tabnat_of_ord_fun.
case: eqP => [Hev | _]; last by case: (hyper_stdtabsh la).
rewrite /= /is_stdtab -incr_tab // tabshP /= /eval.
rewrite shape_map_tab shape_tabsh eq_refl andbT.
by rewrite to_word_map_tab tabsh_is_std.
Qed.
Definition tabnat_of_ord (t : tabsh la) :=
  StdtabSh (sh := la) (tabnat_of_ord_subproof t).

Lemma tabord_of_nat_subproof (t : stdtabsh la) :
  is_tab_of_shape la (tabord_of_nat_fun t).
Proof.
have /andP [Ht Hstd] := stdtabshP t.
rewrite /tabord_of_nat_fun /=.
rewrite shape_map_tab shape_stdtabsh eq_refl andbT.
move: Hstd; rewrite /is_std size_to_word.
rewrite /size_tab shape_stdtabsh sumn_intpartn => /perm_mem Hperm.
rewrite -incr_tab // => /= i j.
rewrite !Hperm !mem_iota /= !add0n => /leq_trans/(_ Hd) Hi /leq_trans/(_ Hd) Hj.
by rewrite ltEsub !ltEnat /= !inordK.
Qed.
Definition tabord_of_nat (t : stdtabsh la) :=
  TabSh (sh := la) (tabord_of_nat_subproof t).

Lemma tabord_of_natK : cancel tabord_of_nat tabnat_of_ord.
Proof.
move=> t.
apply val_inj; rewrite /= /tabnat_of_ord_fun /= /tabord_of_nat_fun /=.
rewrite to_word_map_tab stdtabsh_eval_to_word eq_refl.
rewrite -map_comp map_id_in // => /= r Hr.
rewrite -map_comp map_id_in // => /= i Hi.
rewrite inordK //; apply: (leq_trans _ Hd).
have : i \in to_word t.
  by rewrite /to_word; apply/flattenP; exists r; first rewrite mem_rev.
have /andP [_] := stdtabshP t.
rewrite /is_std => /perm_mem ->.
rewrite mem_iota /= add0n.
by rewrite size_to_word /size_tab shape_stdtabsh sumn_intpartn.
Qed.

Lemma tabnat_of_ordK :
  {in [pred t : tabsh la | eval (to_word t) == td],
   cancel tabnat_of_ord tabord_of_nat }.
Proof.
move=> /= t; rewrite inE => /eqP Ht.
apply val_inj; rewrite /= /tabord_of_nat_fun /= /tabnat_of_ord_fun /=.
rewrite -Ht eq_refl.
rewrite -map_comp map_id_in // => /= r Hr.
rewrite -map_comp map_id_in // => /= i Hi.
by apply val_inj; rewrite /= inordK.
Qed.

End Nvar.

Lemma KostkaStd : Kostka la (colpartn d) = #|{: stdtabsh la}|.
Proof.
rewrite /Kostka.
have -> : (mpart (colpartn d)) =
          [multinom (i < d)%N : nat | i < (size (colpartn d)).-1.+1].
  apply/mnmP => /= i; rewrite /mpart.
  rewrite {2 3}size_colpartn leqSpred !mnmE.
  by rewrite {1}colpartnE nth_nseq; case: (ltnP i d).
rewrite /KostkaMon /KostkaTab colpartnE size_nseq.
rewrite -(card_imset _ (can_inj (tabord_of_natK (leqSpred _)))).
apply eq_card => /= t; rewrite !inE.
apply/eqP/imsetP => [Ht | [/= st _ ->{t}]].
- exists (tabnat_of_ord (leqSpred _) t); first by rewrite inE.
  by rewrite tabnat_of_ordK //= inE -Ht.
- rewrite /= /tabord_of_nat_fun /= /tabnat_of_ord_fun /= to_word_map_tab.
  by rewrite stdtabsh_eval_to_word // leqSpred.
Qed.

End StdKostka.


Definition eqeval n (t : (seq (seq 'I_n.+1))) (la : seq nat) :=
  eval (to_word t) == mpart la.

Lemma eqevalP n (t : (seq (seq 'I_n.+1))) (la : seq nat) :
  size la <= n.+1 ->
  reflect (forall i : 'I_n.+1, count_mem i (to_word t) = nth 0 la i)
          (eqeval t la).
Proof.
rewrite /eqeval /eval /mpart => ->.
apply (iffP eqP) => [Heq i| Hcount].
- by move: Heq => /(congr1 (fun t => tnth t i)); rewrite !tnth_mktuple.
- by apply eq_from_tnth => i; rewrite !tnth_mktuple.
Qed.



(** * Restricting and extending tableaux *)
Section BijectionExtTab.

Variable n : nat.

Local Open Scope nat_scope.

Variables (s : seq nat) (m : nat).
Hypothesis (Hsz : size s < n.+1).
Local Notation sz := (Ordinal Hsz).
Local Lemma Hszrcons : size (rcons s m) <= n.+1.
Proof. by rewrite size_rcons. Qed.

Local Notation P := ('P_(sumn s)).
Local Notation Pm := ('P_((sumn s) + m)).
Variable (mu : Pm).
Local Notation Tm := (tabsh mu).
Hypothesis Hmu : size mu <= n.+1.

Lemma shape_res_tab_subproof (t : Tm) :
  is_part_of_n (sumn s) (
                 if eqeval t (rcons s m) then shape (filter_gt_tab sz t)
                 else locked rowpartn (sumn s)).
Proof.
case: (boolP (eqeval t (rcons s m))) => Hev /= ; last by case: (locked _).
apply/andP; split.
- apply/eqP.
  rewrite -/(size_tab _) -size_to_word -filter_gt_to_word size_filter.
  rewrite -sum_count_mem /=.
  transitivity (\sum_(i < n.+1 | i < sz) nth 0 s i).
    apply eq_big => i; rewrite ltEsub ltEnat //= => Hi.
    by rewrite (eqevalP _ Hszrcons Hev) nth_rcons Hi.
  rewrite sumnE (big_nth 0) big_mkord /=.
  by apply esym; apply big_ord_widen; apply ltnW.
- by apply: is_part_sht; apply: is_tableau_filter_gt; apply: tabshP.
Qed.
Definition shape_res_tab (t : Tm) := IntPartN (shape_res_tab_subproof t).

Lemma hb_strip_shape_res_tab (t : Tm) :
  eqeval t (rcons s m) -> hb_strip (shape_res_tab t) mu.
Proof.
rewrite /shape_res_tab => Hev.
apply/hb_stripP => // i.
rewrite [nth 0 (IntPartN _) _]/= Hev.
have := shape_inner_filter_le sz (tabshP t) => /(congr1 (fun s => nth 0 s i)).
rewrite nth_pad => <-.
case: (ssrnat.ltnP i.+1 (size t)) => Hi.
- rewrite /shape !(nth_map [::]) ?size_map //; try by apply ltnW.
  apply/andP; split; first last.
    move/ltnW in Hi.
    by rewrite -(shape_tabsh t) nth_shape size_filter; apply: count_size.
  have:= tabshP t => /is_tableauP [_ /(_ i) Hrow].
  move=> /(_ _ _ (ltnSn i))/dominateP [].
  rewrite -(shape_tabsh t) nth_shape.
  move Hr : (nth [::] t i) Hrow => r.
  move Hr1 : (nth [::] t i.+1) => r1 Hrow Hszle Hdom.
  rewrite size_filter.
  case: leqP => // Hleq; move/(_ _ Hleq): Hdom.
  move: Hi => /(mem_nth [::]); rewrite Hr1 => Hi.
  set xabs := nth inh r1 (count (>%O sz) r).
  have /count_memPn/eqP : xabs \in to_word t.
    rewrite /to_word; apply/flattenP; exists r1; first by rewrite mem_rev.
    by apply: mem_nth.
  rewrite (eqevalP _ Hszrcons Hev) nth_rcons.
  case: (ssrnat.leqP xabs (size s)) => [Hxabs _ | Hxabs]; first last.
    by rewrite (gtn_eqF Hxabs) ltnNge (ltnW Hxabs).
  rewrite ltEsub ltEnat /= => /leq_trans/(_ Hxabs) {xabs Hxabs}.
  have size_take_leq l sq : size (take l sq) <= size sq.
    by rewrite size_take; case ssrnat.ltnP => [/ltnW|].
  move/(_ _ (count (<%O sz) r) r): size_take_leq => HHH.
  have := leq_trans Hleq Hszle.
  rewrite -{2 3}(cat_take_drop (count (>%O sz) r) r) nth_cat.
  rewrite size_take (leq_trans Hleq Hszle) ltnn subnn.
  rewrite size_cat size_take (leq_trans Hleq Hszle).
  rewrite -addn1 leq_add2l -(filter_le_row sz Hrow) => /(mem_nth inh).
  move: (nth _ _ _) => xabs.
  rewrite mem_filter /= leEsub leEnat andbC => /andP [_] /=.
  move=>/leq_ltn_trans H1/H1.
  by rewrite ltnn.
- rewrite nth_default -(shape_tabsh t) ?size_map //=.
  case: (ssrnat.ltnP i (size t)) => {}Hi.
  + rewrite !(nth_map [::]) ?size_map //.
    by rewrite size_filter; apply: (leq_trans (count_size _ _)).
  + by rewrite !nth_default ?size_map.
Qed.

Variable (la : P).
Hypothesis Hstrip : hb_strip la mu.
Local Notation T := (tabsh la).

Local Definition Hlamu := size_included (hb_strip_included Hstrip).
Local Definition Hla : size la <= n.+1 := leq_trans Hlamu Hmu.

Definition res_tab (t : Tm) : T :=
  if insub (filter_gt_tab sz t) is Some tr then tr
  else locked (tabrowconst Hla).
Local Definition ext_tab_fun (t : T) :=
  if eqeval t s then join_tab t (skew_reshape la mu (nseq m sz))
  else locked (tabrowconst Hmu).

Local Lemma sumndiff : sumn (mu / la) = m.
Proof.
by rewrite sumn_diff_shape ?hb_strip_included // !sumn_intpartn addKn.
Qed.

Lemma ext_tab_subproof t : is_tab_of_shape mu (ext_tab_fun t).
Proof.
rewrite /ext_tab_fun.
case: (boolP (eqeval t s)) => [/= Hev |_]; last by case: (locked _).
have Hincl:= hb_strip_included Hstrip.
apply/andP; split.
- apply join_tab_skew => //.
  + rewrite to_word_skew_reshape // ?size_nseq ?sumndiff //.
    apply/allP => /= i /nseqP [->{i} Hsm].
    apply/allP => /= i /count_memPn/eqP Hi.
    rewrite ltEsub ltEnat /=.
    move: Hi; apply contraR; rewrite -leqNgt => Hi.
    by rewrite (eqevalP _ (ltnW Hsz) Hev) nth_default.
  + have:= Hstrip; rewrite -(hb_strip_rowE (u := nseq m sz)) => //.
    * by rewrite Hincl /= shape_tabsh.
    * apply/(is_rowP ord0) => i j; rewrite size_nseq => /andP [Hij Hj].
      by rewrite !nth_nseq Hj (leq_ltn_trans Hij Hj).
    * by rewrite size_nseq sumndiff.
- rewrite -(shape_tabsh t) shape_join_tab_skew_reshape ?shape_tabsh //.
  by rewrite size_nseq sumndiff.
Qed.
Definition ext_tab t := TabSh (ext_tab_subproof t).

Lemma res_tabP (t : Tm) :
  shape (filter_gt_tab sz t) == la ->
  is_tab_of_shape la (filter_gt_tab sz t).
Proof.
rewrite /= andbC => -> /=.
by apply: is_tableau_filter_gt; apply tabshP.
Qed.

Lemma eval_res_tab (t : Tm) :
  shape (filter_gt_tab sz t) == la ->
  eqeval t (rcons s m) -> eqeval (res_tab t) s.
Proof.
move=> Hsh Hev ; rewrite /res_tab (insubT _ (res_tabP Hsh)) /=.
apply/eqevalP; first exact: ltnW.
move=> i /=; rewrite -filter_gt_to_word.
case: (ssrnat.ltnP i sz) => Hisz.
- move: Hev => /(eqevalP _ Hszrcons)/(_ i).
  rewrite nth_rcons Hisz => <-.
  elim: (to_word t) => //= w0 w IHw.
  case: ltP; rewrite /= IHw //= /eq_op /=.
  rewrite leEsub leEnat /= => /(leq_trans Hisz)/gtn_eqF => ->.
  by rewrite add0n.
- rewrite nth_default //.
  apply/count_memPn; rewrite mem_filter /=.
  by rewrite ltEsub ltEnat /= ltnNge Hisz.
Qed.

Lemma eval_ext_tab (t : T) :
  eqeval t s -> eqeval (ext_tab t) (rcons s m).
Proof.
move=> Hev; apply/eqevalP; first by rewrite size_rcons.
move=> i; rewrite /= /ext_tab_fun Hev /=.
have Hszle : size t <= size (skew_reshape la mu (nseq m sz)).
  rewrite size_skew_reshape.
  by apply: (leq_trans _ Hlamu); rewrite -(shape_tabsh t) size_map.
move: Hszle => /perm_join_tab/seq.permP ->.
rewrite count_cat (eqevalP _ (ltnW Hsz) Hev).
rewrite to_word_skew_reshape ?size_nseq ?sumndiff ?hb_strip_included //.
rewrite count_nseq /= nth_rcons /= {1}/eq_op /=.
case: (ssrnat.ltnP i (size s)) => [/gtn_eqF ->| H].
  by rewrite mul0n addn0.
rewrite (nth_default _ H) add0n eq_sym.
by case: eqP => _; rewrite ?mul0n ?mul1n.
Qed.

Lemma res_tabK (t : Tm) :
  shape (filter_gt_tab sz t) == la ->
  eqeval t (rcons s m) -> ext_tab (res_tab t) = t.
Proof.
rewrite /ext_tab => Hsh Hev; apply val_inj => /=.
rewrite /ext_tab_fun eval_res_tab //.
rewrite /res_tab (insubT _ (res_tabP Hsh)) /=.
rewrite -[RHS](join_tab_filter sz (tabshP t)); congr join_tab.
rewrite -[RHS](skew_reshapeK (inner := shape (filter_gt_tab sz t))); first last.
  rewrite /shape size_map /filter_gt_tab /filter_le_tab.
  rewrite size_map /= size_filter; apply: (leq_trans (count_size _ _)).
  by rewrite size_map.
move: Hsh => /eqP Hsh.
congr skew_reshape.
- by rewrite Hsh.
- suff -> : shape (filter_le_tab sz t) = mu / (shape (filter_gt_tab sz t)).
    rewrite diff_shapeK // -(shape_tabsh t); apply included_shape_filter_gt.
    exact: tabshP.
  apply (eq_from_nth (x0 := 0)).
  - by rewrite size_diff_shape /filter_le_tab -(shape_tabsh t) !size_map.
  - move=> i; rewrite /shape !size_map => Hi.
    rewrite -diff_shape_pad0 nth_diff_shape !nth_shape -/(shape _).
    rewrite -(shape_tabsh t) size_map.
    rewrite -shape_inner_filter_le //= nth_shape !(nth_map [::]) ?size_map //.
    rewrite !size_filter -(count_predC (>%O sz) (nth [::] t i)).
    rewrite addKn; apply eq_count => x /=.
    by rewrite -leNgt.
- have Hw : size (to_word (filter_le_tab sz t)) = m.
    rewrite -filter_le_to_word size_filter -sum_count_mem /=.
    rewrite (bigD1 sz) /= // (eqevalP _ Hszrcons Hev).
    rewrite nth_rcons ltnn eq_refl big1 ?addn0 // => i.
    rewrite andbC -lt_def ltEsub ltEnat /= => Hi.
    rewrite (eqevalP _ Hszrcons Hev) nth_rcons.
    by rewrite ltnNge (ltnW Hi) (gtn_eqF Hi).
  rewrite -{1}Hw; symmetry; apply/all_pred1P/allP => /= i.
  rewrite /to_word => /flattenP [/= rtmp].
  rewrite mem_rev => /mapP [/= r Hr ->{rtmp}].
  rewrite mem_filter leEsub leEnat => /andP [/= Hi Hir].
  apply/eqP/val_inj => /=; apply anti_leq; rewrite {}Hi andbT.
  have /count_memPn/eqP : i \in to_word t.
    by rewrite /to_word; apply/flattenP; exists r; first rewrite mem_rev.
  rewrite (eqevalP _ Hszrcons Hev); apply contraR; rewrite -ltnNge => Hi.
  by rewrite nth_default // size_rcons.
Qed.

Corollary res_tab_inj :
  {in [set x : Tm | eqeval x (rcons s m) & shape_res_tab x == la] &,
      injective res_tab}.
Proof.
move=> t1 t2; rewrite !inE.
move=> /andP [Hev1 /eqP/(congr1 val) /=]; rewrite Hev1 => /eqP Hsh1.
move=> /andP [Hev2 /eqP/(congr1 val) /=]; rewrite Hev2 => /eqP Hsh2.
by rewrite -{2}(res_tabK Hsh1 Hev1) -{2}(res_tabK Hsh2 Hev2) => ->.
Qed.

Lemma filter_ext_tab (t : T) :
  eqeval t s -> filter_gt_tab sz (ext_tab t) = t.
Proof.
move=> Hev.
rewrite /ext_tab /ext_tab_fun /= Hev.
rewrite [map _ (join_tab _ _)](_ : _ = pad [::] (size mu) t).
- rewrite /pad filter_cat {Hev}.
  rewrite [X in _ ++ X](eq_in_filter (a2 := pred0)); first last.
    by move=> x /nseqP [->].
  rewrite filter_pred0 cats0.
  case: t => t /= /andP [Ht _].
  by elim: t Ht => //= t0 t IHt /and4P [-> _ _ /IHt] /= ->.
- have Hszle : size t <= size mu.
    by apply: (leq_trans _ Hlamu); rewrite -(shape_tabsh t) size_map.
  apply (eq_from_nth (x0 := [::])).
    rewrite /join_tab !size_map size_zip !size_cat !size_nseq.
    by rewrite size_skew_reshape subnKC // minnn.
  move=> i; rewrite size_map => Hi.
  rewrite (nth_map [::]) // nth_cat nth_nseq if_same.
  move: Hi; rewrite /join_tab size_map => Hi.
  rewrite /join_tab (nth_map ([::], [::])) // nth_zip /=; first last.
    by rewrite size_skew_reshape size_cat size_nseq subnKC.
  rewrite filter_cat nth_cat.
  have Hfil :
      [seq x <- nth [::] (skew_reshape la mu (nseq m sz)) i | (x < sz)%O] = [::].
    apply/nilP; rewrite /nilp size_filter.
    rewrite (eq_in_count (a2 := pred0)) ?count_pred0 // => x /=.
    case: (ssrnat.ltnP i (size (skew_reshape la mu (nseq m sz))))
         => [|Hi1]; last by rewrite nth_default.
    rewrite /skew_reshape size_rev => Hi1; rewrite nth_rev //.
    rewrite nth_reshape => /mem_take/mem_drop/nseqP [-> _].
    by rewrite ltxx.
  case: (ssrnat.ltnP i (size t)) => {}Hi; first last.
    by rewrite Hfil nth_nseq if_same.
  rewrite Hfil cats0 (eq_in_filter (a2 := predT)) ?filter_predT //.
  move=> x /count_memPn/eqP Hcount.
  rewrite ltEsub ltEnat /=.
  suff : nth 0 s x != 0.
    by case: ssrnat.ltnP => // H; rewrite nth_default.
  rewrite -(eqevalP t (ltnW Hsz) Hev x).
  rewrite /to_word seq.count_flatten map_rev sumn_rev sumnE.
  rewrite (big_nth 0) size_map big_mkord /= (bigD1 (Ordinal Hi)) //=.
  rewrite (nth_map [::]) //.
  by move: Hcount; apply contra; rewrite addn_eq0 => /andP [].
Qed.

Lemma ext_tabK (t : T) : eqeval t s -> res_tab (ext_tab t) = t.
Proof.
move=> Hev.
apply val_inj => /=; rewrite -[RHS]to_wordK -[LHS]to_wordK /res_tab.
by rewrite filter_ext_tab //= insubT; first case t.
Qed.

Corollary ext_tab_inj : {in [pred t : T | eqeval t s] &, injective ext_tab }.
Proof. by move=> /= p1 p2 H1 H2 /(congr1 res_tab); rewrite !ext_tabK. Qed.

Lemma card_eq_eval :
  #|[set t : tabsh['I_n.+1] mu |
     (eqeval t (rcons s m)) && (shape (filter_gt_tab sz t) == la)]|
  = #|[set t : tabsh['I_n.+1] la | eqeval t s]|.
Proof.
rewrite -(card_in_imset (f := ext_tab)); first last.
  by move=> /= p1 p2; rewrite /= !inE; apply ext_tab_inj.
congr #|pred_of_set _|; apply/setP => t; rewrite !inE.
apply/andP/imsetP => [[Hev Hsh] | [tt]].
- exists (res_tab t); rewrite ?inE; first exact: eval_res_tab.
  by rewrite res_tabK.
- rewrite inE => Hev ->{t}; split; first exact: eval_ext_tab.
  by rewrite filter_ext_tab // shape_tabsh.
Qed.

End BijectionExtTab.


(** * Recursive computation of Kostka numbers *)
Section KostkaRec.

Local Open Scope nat_scope.


Lemma Kostka_ind d (la : 'P_d) m mu :
  d = m + sumn mu ->
  Kostka la (m :: mu) =
  \sum_(nu : 'P_(sumn mu) | hb_strip nu la) Kostka nu mu.
Proof.
case: (leqP (size la) (size mu).+1) => Hszla; first last.
  move=> _; rewrite Kostka_size0 //.
  apply esym; apply big1 => nu Hnu; apply Kostka_size0.
  by have := hb_strip_size Hnu => /andP [_ /(leq_trans Hszla)].
rewrite {1}/Kostka addnC => Hd; subst d.
have /permPl/(perm_mpart _)/perm_KostkaMon <- := perm_rcons m mu.
rewrite /KostkaMon /KostkaTab.
transitivity #|[set t : tabsh['I_(size mu).+1] la | eqeval t (rcons mu m)]|.
  by apply eq_card.
rewrite -sum1dep_card.
have Hszmu := ltnSn (size mu).
pose sht := @shape_res_tab (size mu) mu m Hszmu la.
rewrite (partition_big sht
           (fun nu : 'P_(sumn mu) => hb_strip nu la)) /=; first last.
  by move=> t Ht; apply hb_strip_shape_res_tab.
apply eq_bigr => /= nu Hstrip; rewrite sum1dep_card.
rewrite (Kostka_any _ (ltnW Hszmu)) /KostkaMon /KostkaTab.
rewrite -(card_eq_eval _ Hszla Hstrip).
apply eq_card => /= t; rewrite !inE.
by rewrite -val_eqE /=; case : (eqeval t (rcons mu m)).
Qed.

Fixpoint Kostka_rec (la mu : seq nat) : nat :=
  if mu is m :: mu then
    sumn [seq Kostka_rec nu mu | nu <- enum_partn (sumn mu) & hb_strip nu la]
  else la == [::].

Example Kostka_expl1 :
  Kostka_rec [:: 4; 3] [:: 3; 2; 2] == 2.
Proof. by []. Qed.
Example Kostka_expl2 :
  Kostka_rec [:: 4; 3; 1] [:: 3; 2; 2; 1] == 5.
Proof. by []. Qed.
Example Kostka_expl3 :
  Kostka_rec [:: 4; 4; 3; 1] [:: 3; 3; 2; 2; 1; 1] == 25.
Proof. by []. Qed.

Lemma Kostka_rec_size0 la mu :
  size la > size mu -> Kostka_rec la mu = 0.
Proof.
elim: mu la => [|m mu IHmu] la /= H; first by case: la H.
rewrite sumn_map_condE; apply big1 => nu Hnu.
by apply IHmu; have := hb_strip_size Hnu => /andP [_ /(leq_trans H)].
Qed.

Lemma Kostka_recE d (la : 'P_d) mu :
  sumn mu = d -> Kostka_rec la mu = Kostka la mu.
Proof.
elim: mu d la => [| m0 mu IHmu] d la /= Hd.
  subst d; have -> : la = rowpartn 0 by rewrite !intpartn0.
  by rewrite -rowpartn0E Kostka_diag eqxx.
rewrite sumn_map_condE -enum_intpartnE big_map enumT.
by rewrite Kostka_ind //; apply eq_big => //= nu Hstrip; apply IHmu.
Qed.

End KostkaRec.


Notation "''K' ( la , mu )" := (Kostka la mu)
  (at level 8, format "''K' ( la ,  mu )") : nat_scope.
Notation "''K' ( la , mu )" := (Kostka la mu)%:R
  (at level 8, format "''K' ( la ,  mu )") : ring_scope.

Lemma Kostka_unitrig (R : comUnitRingType) d :
  unitrig (fun la mu : 'PDom_d => 'K(la, mu)%:R : R).
Proof.
apply/unitrigP; split => [la | la mu].
- by rewrite Kostka_diag.
- by apply contraR => /Kostka0 ->.
Qed.

(** ** Inverse Kostka numbers *)
Definition KostkaInv d : 'P_d -> 'P_d -> int :=
  Minv (fun la mu : 'PDom_d => 'K(la, mu)%:R : int).

Lemma KostkaInv_unitrig d :
  unitrig (fun la mu : 'PDom_d => KostkaInv la mu).
Proof. exact: (Minv_unitrig (Kostka_unitrig _ d)). Qed.

Notation "''K^-1' ( la , mu )" := ((KostkaInv la mu)%:~R)
  (at level 8, format "''K^-1' ( la ,  mu )") : ring_scope.



(** * Straightening of alternant polynomials *)
Section AlternStraighten.

Variable n0 : nat.
Variable R : comRingType.

Local Notation n := n0.+1.
Local Notation rho := (rho n).
Local Notation "''a_' k" := (@alternpol n R 'X_[k]).
Local Notation "m # s" := [multinom m (s i) | i < n].

Lemma alt_straight_step (m : 'X_{1..n}) (i : nat) :
  i < n0 -> m (inord i.+1) != 0%N ->
  'a_(m + rho) = - 'a_(m # 's_i - U_(inord i) + U_(inord i.+1) + rho).
Proof.
rewrite /alternpol => ltin0 mi1.
have ltin : i < n by apply: ltnW.
rewrite -sumrN [RHS](reindex_inj (mulgI 's_i)); apply eq_bigr => /= s _.
rewrite odd_mul_tperm inordi_neq_i1 //= signrN scaleNr opprK.
rewrite msymMm; congr (_ *: msym _ _); rewrite msymX; congr ('X_[_]).
apply/mnmP => j; rewrite !mnmE permKV eltrV.
case: (altP (inord i =P j)) => [<-{j} /= | neqij].
  rewrite eltrL eqxx (negbTE (inordi_neq_i1 _)) //= subn0.
  by rewrite !inordK // -addnA subn1 add1n subnSK.
case: (altP (inord i.+1 =P j)) => [<-{j neqij} /= | neqi1j].
  rewrite tpermR eqxx eq_sym (negbTE (inordi_neq_i1 _)) // !inordK //=.
  rewrite addn0; case: (m (inord i.+1)) mi1 => // mi1 _.
  by rewrite addSnnS [(mi1.+1 - 1)%N]subSS subn0 subnSK // subn1.
by rewrite tpermD // (negbTE neqij) (negbTE neqi1j) subn0 addn0.
Qed.

Lemma alt_straight_add_ribbon0 (p : seq nat) (i : 'I_n) (d : nat) :
  is_part p -> size p <= n ->
  add_ribbon p d i == None -> 'a_(mpart p + rho + U_(i) *+ d.+1) = 0%R.
Proof.
rewrite /add_ribbon => Hpart Hsz.
case: startrem (startremE p d.+1 i) (startrem_leq_pos p d.+1 i) => a [|b]//= .
rewrite addn0 => Heq leai _.
move: leai; rewrite leq_eqVlt => /orP [/eqP Hai | ltai].
  by exfalso; move: Heq => /eqP; rewrite Hai -[X in X == _]addn0 !eqn_add2l.
have ltan := ltn_trans ltai (ltn_ord i).
set mon := (M in 'a_(M)).
suff /alt_alternate -> : mon i = mon (Ordinal ltan) => //.
  by rewrite -val_eqE /= (gtn_eqF ltai).
apply/eqP; rewrite {}/mon !mnmE !mpartE //=.
rewrite !mulmnE !mnm1E eqxx -val_eqE muln1 /= (gtn_eqF ltai) muln0 addn0.
rewrite addnAC -(eqn_add2r (a + i)) {1}(addnC a i) -!addnA.
rewrite subn1 /= ![(n0 - _) + _]addnA !subnK -?[i <= n0]ltnS //.
rewrite ![(n0 - _) + _]addnA !subnK -?[i <= n0]ltnS //.
by rewrite ![n0 + _]addnC !addnA [_ + _ + a]addnAC Heq.
Qed.

Lemma alt_straight_add_ribbon (p : seq nat) (i : 'I_n) (d : nat) :
  is_part p -> size p <= n ->
  forall res h, add_ribbon p d i = Some (res, h) ->
    'a_(mpart p + rho + U_(i) *+ d.+1) = (-1) ^+ h.-1 *: 'a_(mpart res + rho).
Proof.
rewrite /alternpol => Hpart ltsn res h Hrib.
have := size_add_ribbon Hrib; move: Hrib; rewrite /add_ribbon.
case startremeq : startrem (startrem_leq_pos p d.+1 i) => [start rem]// lesti.
case: ltnP => // lt0rem [<- <-] /= Hsz.
have starto := leq_ltn_trans lesti (ltn_ord i).
have : start = val (Ordinal starto) by [].
move: (Ordinal starto) => st Hstart; subst start.
rewrite (reindex_inj (mulgI 's_[iota st (i - st)]^-1)%g) /= scaler_sumr.
apply: eq_bigr => s _; rewrite scalerA; congr (_ *: _).
  rewrite odd_permM odd_permV -odd_size_permE; first last.
    apply/allP => j; rewrite mem_iota /= subnKC // => /andP[_].
    by move/leq_ltn_trans/(_ (ltn_ord i)).
  by rewrite size_iota signr_addb signr_odd.
rewrite msymMm msymX invgK; congr (msym s 'X_[_]).
apply mnmP => j; rewrite !mnmE !mpartE //; first last.
  by rewrite Hsz geq_max ltsn ltn_ord.
rewrite !mulmnE !mnm1E -val_eqE /=.
have := startrem_leq p d.+1 i; rewrite startremeq => /(_ lt0rem) /= lesmin.
case: (altP (j =P st)) => [/= eqjst |].
  subst j; apply/eqP.
  rewrite (nth_add_ribbon_start _ lesmin) cycleij_j // eqxx muln1.
  rewrite addnAC -(eqn_add2r (st + i)) {1}(addnC st i) -!addnA.
  rewrite subn1 /= ![(n0 - _) + _]addnA !subnK -?[i <= n0]ltnS //.
  rewrite ![(n0 - _) + _]addnA !subnK -?[i <= n0]ltnS //.
  rewrite ![n0 + _]addnC !addnA [_ + _ + i]addnAC [_ + _ + st]addnAC.
  by have:= startremE p d.+1 i; rewrite startremeq => ->.
rewrite neq_ltn => /orP [ltjst | ltstj].
  rewrite cycleij_lt // nth_add_ribbon_lt_start //.
  by rewrite (gtn_eqF (leq_trans ltjst lesti)) muln0 addn0.
case: (ltnP i j) => [/= ltij | leji].
  rewrite nth_add_ribbon_stop_lt // cycleij_gt //.
  by rewrite (ltn_eqF ltij) muln0 addn0.
rewrite -(ltn_predK ltstj) nth_add_ribbon_in //; first last.
  by rewrite (ltn_predK ltstj) ltstj leji.
rewrite cycleij_in ?ltstj ?leji // inordK; first last.
  by rewrite (ltn_predK ltstj) ltnW.
case: j ltstj leji => [[|j]//= Hj] _ /gtn_eqF ->.
by rewrite muln0 addn0 addSnnS subnSK // subn1.
Qed.

End AlternStraighten.
