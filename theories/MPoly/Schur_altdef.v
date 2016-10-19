(** * Combi.MPoly.Schur_basis : The Basis of Schur polynomials *)
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
(** Schur polynomials and Kostka numbers

In the combinatorial definitions below, we use the following notations:
- [n] : an integer denoting the number of variable.
- [la] [mu] : partitions of an integer [d]
- [m] : a monomial for the ring of polynomials {mpoly R[n]}
- [w] : a sequence of ['I_n]
- [t] : a tableau

We define the following notions:

- [add_mesym la S] == for a set [S] of ['I_n] the partition obtained by
           incrementing the parts in [S] if its a partition. If not
           the value is unspecified.
- [setdiff la mu] == the set of elements [i] of ['I_n] for which the
           [i]-th part of [la] is smaller than the one of [mu].
- ['s[la]]       == the Schur symmetric polynomials in [{sympoly R[n]}]

***** Kostka numbers:

- [eval w]        == the evaluation of [w] as a [n.-tuple nat].
- [KostkaTab la m] == the set of tableaux of shape [la] and evaluation [m].
- [KostkaMon la m] == the number of Kostka tableau : [#|KostkaTab la m|].
- [Kostka la mu]    ==
- ['K(la, mu)]      == the Kostka number associated to [la] and [mu] as an
      integer in [nat_scope] and as an element of [R] in [ring_scope].
- [Kostak_rec la mu] == a Coq implementation of the computation of the Kostka
      number. It suppose that [sumn la = sumn mu].
- [MatInv M la mu]  == the inverse of the uni-triangular matrix [M_(la, mu)].
      [la] and [mu] are supposed to belong to a finite partialy ordered
           type [T]. Both [M] and [MatInv] ar given as a function [la mu -> R]
           and are uni-triangular ro the order of [T] that is [M la la = 1] and
           [M la mu] is zero unless [mu <= la].
- ['K^-1(la, mu)] == the inverse Kostka number, that is the coefficient of the
           inverse Kostka matrix computed using [MatInv].
- [eqeval t la] == the evaluation of [t] is [la]. More precisely, the evaluation
           of the row reading of the tableau [t] is equal to the monomial
           associated to [la]

***** Extension of tableaux:

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
From mathcomp Require Import finset fingroup perm.
From SsrMultinomials Require Import ssrcomplements poset freeg bigenough mpoly.

Require Import tools combclass ordtype sorted partition tableau skewtab.
Require Import presentSn antisym Schur_mpoly freeSchur therule.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

(** Alternating and symmetric polynomial *)
Section Alternant.

Variable n : nat.
Variable R : comRingType.

Local Notation rho := (rho n).
Local Notation "''e_' k" := (@mesym n R k)
                              (at level 8, k at level 2, format "''e_' k").
Local Notation "''a_' k" := (@alternpol n R 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").

Lemma rho_uniq : uniq rho.
Proof using .
suff : perm_eq rho (iota 0 n) by move/perm_eq_uniq ->; exact: iota_uniq.
rewrite rho_iota perm_eq_sym; exact: perm_eq_rev.
Qed.

Lemma alt_uniq_non0 (m : 'X_{1..n}) : uniq m -> 'a_m != 0.
Proof using .
move=> Huniq.
suff : mcoeff m 'a_m == 1.
  apply contraL => /eqP ->; rewrite mcoeff0 eq_sym.
  exact: oner_neq0.
rewrite /alternpol (reindex_inj invg_inj) /=.
rewrite raddf_sum /= (bigID (pred1 1%g)) /=.
rewrite big_pred1_eq odd_permV odd_perm1 expr0 scale1r invg1 msym1m.
rewrite mcoeffX eq_refl /=.
rewrite (eq_bigr (fun => 0)); first by rewrite big1_eq addr0.
move=> s Hs; rewrite mcoeffZ msymX mcoeffX invgK.
suff : [multinom m (s i) | i < n] != m by move=> /negbTE ->; rewrite mulr0.
move: Hs; apply contra => /eqP; rewrite mnmP => Heq.
apply/eqP; rewrite -permP => i; rewrite perm1; apply val_inj => /=.
have /eqP := Heq i; rewrite !mnmE !(mnm_nth 0).
rewrite nth_uniq; last exact: Huniq.
- by move=> /eqP ->.
- rewrite size_tuple; exact: ltn_ord.
- rewrite size_tuple; exact: ltn_ord.
Qed.

Lemma alt_rho_non0 : 'a_rho != 0.
Proof using . exact: alt_uniq_non0 (rho_uniq). Qed.

Lemma alt_alternate (m : 'X_{1..n}) (i j : 'I_n) :
  i != j -> m i = m j -> 'a_m = 0.
Proof using .
move=> H Heq.
pose t := tperm i j.
have oddMt s: (t * s)%g = ~~ s :> bool by rewrite odd_permM odd_tperm H.
rewrite [alternpol _](bigID (@odd_perm _)) /=.
apply: canLR (subrK _) _; rewrite add0r -sumrN.
rewrite (reindex_inj (mulgI t)); apply: eq_big => //= s.
rewrite oddMt => /negPf ->; rewrite scaleN1r scale1r; congr (- _).
rewrite msymMm.
suff -> : msym t 'X_[m] = ('X_[m] : {mpoly R[n]}) by [].
rewrite msymX; congr mpolyX.
rewrite mnmP => k /=.
rewrite !mnmE /= tpermV.
by case: (tpermP i j k) => Hk //; rewrite Hk Heq.
Qed.

Lemma alt_add1_0 (m : 'X_{1..n}) i :
  (nth 0%N m i).+1 = nth 0%N m i.+1 -> 'a_(m + rho) = 0.
Proof using .
move=> Heq.
have Hi1n : i.+1 < n.
  rewrite ltnNge; apply (introN idP) => Hi.
  by move: Heq; rewrite [RHS]nth_default // size_tuple.
have Hi : i < n by rewrite ltnW.
pose i0 := Ordinal Hi; pose i1 := Ordinal Hi1n.
have /alt_alternate : i0 != i1.
  apply (introN idP) => /eqP/(congr1 val)/=/eqP.
  by rewrite ieqi1F.
apply.
rewrite !mnmDE !mnmE !(mnm_nth 0%N) -Heq -(mnm_nth 0%N m i0).
rewrite addSn -addnS subn1 /= subnS prednK //.
have -> : (n.-1 - i = n - i.+1)%N.
  case: n Hi1n Hi {i0 i1} => [//= | n' _] /=.
  by rewrite subSS.
by rewrite subn_gt0.
Qed.


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

Variables (d k : nat) (la : intpartn d) (h : {set 'I_n}).

Local Definition hasincr :=
  has (fun i => (nth 0 (mpart la + mesym1 h)%MM i).+1 ==
                 nth 0 (mpart la + mesym1 h)%MM i.+1) (iota 0 n.-1).

Lemma hasincr0 : hasincr -> 'a_(mpart la + mesym1 h + rho) = 0%R.
Proof using . move=> /hasP [] i _ /eqP; exact: alt_add1_0. Qed.

Lemma not_hasincr_part :
  size la <= n -> ~~ hasincr ->
  is_part_of_n (d + #|h|) (rem_trail0 (mpart la + mesym1 h)%MM).
Proof using .
move=> Hsz /hasPn H.
rewrite /mpart Hsz.
apply/andP; split.
- rewrite sumn_rem_trail0.
  rewrite -(@sum_iota_sumnE _ n); last by rewrite size_map size_enum_ord.
  rewrite big_mkord.
  rewrite (eq_bigr (fun i : 'I_n => nth 0 la i + mesym1 h i)%N); first last.
    move=> i _.
    have H0 : 0 < n by apply: (leq_ltn_trans _ (ltn_ord i)).
    rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
    rewrite nth_ord_enum /= (mnm_nth 0) /=.
    rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
    by rewrite nth_ord_enum.
  rewrite big_split /=; apply/eqP; congr (_ + _)%N.
  + rewrite -{2}(intpartn_sumn la).
    by rewrite -(sum_iota_sumnE Hsz) big_mkord.
  + rewrite -mdeg_mesym1 /mdeg.
    rewrite -map_tnth_enum big_map /index_enum enumT.
    apply eq_bigr => i _.
    by rewrite mnm_tnth.
- apply is_part_rem_trail0.
  apply/(sorted1P 0) => i.
  rewrite size_map size_enum_ord => Hi1.
  have Hi : i < n by exact: (ltn_trans _ Hi1).
  have {H} /H : i \in iota 0 n.-1.
    rewrite mem_iota add0n.
    by case: n Hi1 {Hsz H Hi} => [//= | n'] /=; rewrite ltnS.
  have H0 : 0 < n by apply: (leq_ltn_trans _ Hi1).
  rewrite /mpart Hsz !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
  rewrite !nth_enum_ord //.
  set bi := (_ \in h); set bi1 := (_ \in h).
  have:= is_partP _ (intpartnP la) => [] [] _ H.
  have {H} := H i; move: (i.+1) => j /= H1.
  case: bi bi1 => [] [] /=; rewrite ?addn1 ?addn0 => H2.
  + by rewrite ltnS.
  + exact: (leq_trans H1).
  + by rewrite ltn_neqAle -eqSS eq_sym H2 H1.
  + exact: H1.
Qed.

Let add_mpart_mesym :=
  if [&& size la <= n, #|h| == k & ~~ hasincr]
  then (rem_trail0 (mpart la + mesym1 h)%MM)
  else rowpart (d + k) (* unused *).
Lemma add_mpart_mesymP : is_part_of_n (d + k) add_mpart_mesym.
Proof using la h.
rewrite /add_mpart_mesym.
case: (boolP [&& _, _ & _]) => [/and3P [] Hsz /eqP <- Hincr | _].
- exact: not_hasincr_part.
- exact: rowpartnP.
Qed.
Definition add_mesym : intpartn (d + k) := IntPartN add_mpart_mesymP.

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

Lemma card_setdiff d k (la : intpartn d) (mu : intpartn (d + k)) :
  size mu <= n -> size la <= n -> vb_strip la mu -> #|setdiff la mu| = k.
Proof using .
move=> Hszmu Hszla /(vb_stripP (intpartnP _) (intpartnP _)) Hstrip.
rewrite /setdiff -sum1dep_card.
rewrite -{2}(addKn d k).
rewrite -{4}(intpartn_sumn la) -{2}(intpartn_sumn mu).
rewrite -(sum_iota_sumnE Hszmu) -(sum_iota_sumnE Hszla).
set rhs := RHS.
have {rhs} -> : rhs = (\sum_(0 <= i < n) (nth 0 mu i - nth 0 la i)).
  rewrite /rhs {rhs} /index_iota subn0.
  elim: n {Hszmu Hszla} => [//= | i IHi]; first by rewrite !big_nil.
  rewrite -addn1 iota_add /= add0n !big_cat !big_cons !big_nil /= !addn0.
  rewrite subnDA subnAC -addnBA; last by have := Hstrip i => /andP [].
  rewrite addnC [RHS]addnC -IHi {IHi}.
  rewrite addnBA //.
  elim: i => [//= | i IHi]; first by rewrite !big_nil.
  rewrite -addn1 iota_add /= add0n !big_cat !big_cons !big_nil /= !addn0.
  apply leq_add; first exact: IHi.
  by have := Hstrip i => /andP [].
rewrite big_mkord.
rewrite [RHS](bigID (fun i : 'I_n => nth 0 la i < nth 0 mu i)) /=.
rewrite [X in (_ = _ + X)]big1 ?addn0; first last.
  by move=> i; rewrite -leqNgt /leq => /eqP.
apply eq_bigr => i H.
have:= Hstrip i => /andP [] H1 H2.
suff -> : nth 0 mu i = (nth 0 la i).+1 by rewrite subSn // subnn.
by apply anti_leq; rewrite H2 H.
Qed.

Lemma nth_add_setdiff d k (la : intpartn d) (mu : intpartn (d + k)) :
  size mu <= n -> size la <= n -> vb_strip la mu ->
  forall i,
  nth 0 [seq (mpart la) i0 + (mesym1 (setdiff la mu)) i0 | i0 <- enum 'I_n] i =
  nth 0 mu i.
Proof using .
move=> Hszmu Hszla /(vb_stripP (intpartnP _) (intpartnP _)) Hstrip i.
case: (ssrnat.ltnP i n) => Hi; first last.
  rewrite !nth_default //.
  - exact: leq_trans Hszmu Hi.
  - by rewrite size_map size_enum_ord.
have H0 : 0 < n by apply: (leq_ltn_trans _ Hi).
rewrite /mpart Hszla.
rewrite !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
rewrite inE /= (nth_enum_ord (Ordinal H0) Hi).
case: ssrnat.ltnP => H /=; rewrite ?addn0 ?addn1.
- apply anti_leq; rewrite H /=.
  by have := Hstrip i => /andP [].
- apply anti_leq; rewrite H /= andbT.
  by have := Hstrip i => /andP [].
Qed.

Lemma nohasincr_setdiff d k (la : intpartn d) (mu : intpartn (d + k)) :
  size mu <= n -> size la <= n ->
  vb_strip la mu -> ~~ hasincr la (setdiff la mu).
Proof using .
move=> Hszmu Hszla Hstrip.
apply/hasPn => i; rewrite mem_iota add0n => /andP [] _ Hi.
rewrite /mnm_add [val _]/= !nth_add_setdiff //.
rewrite eq_sym ltn_eqF // ltnS.
have := (is_partP _ (intpartnP mu)) => [] [] _.
by apply.
Qed.

Lemma add_mesymK d k (la : intpartn d) :
  size la <= n ->
  {in [pred mu : intpartn (d + k) | vb_strip la mu && (size mu <= n)],
  cancel (fun mu : intpartn (d + k) => setdiff la (val mu)) (add_mesym k la)}.
Proof using .
move=> Hszla mu /=; rewrite inE => /andP [] Hstrip Hsz.
have:= vb_stripP (intpartnP _) (intpartnP _) Hstrip => Hstr.
apply/eqP/(part_eqP (intpartnP _) (intpartnP _)) => i.
rewrite /add_mesym /=.
rewrite Hszla card_setdiff // eq_refl /= nohasincr_setdiff //.
by rewrite nth_rem_trail0 nth_add_setdiff.
Qed.


(** * Piery's rule for alternating polynomials *)
Theorem alt_mpart_syme d (la : intpartn d) k :
  size la <= n ->
  ('a_(mpart la + rho) * 'e_k =
  \sum_(mu : intpartn (d + k) | vb_strip la mu && (size mu <= n))
     'a_(mpart mu + rho))%R.
Proof using .
rewrite alt_syme => Hszla.
rewrite (bigID (hasincr la)) /=.
rewrite (eq_bigr (fun x => 0%R)); last by move=> i /andP [] _ /hasincr0.
rewrite sumr_const mul0rn add0r.
rewrite (eq_bigr (fun h => 'a_(mpart (add_mesym k la h) + rho))); first last.
  by move=> i /andP [] Hk Hincr; rewrite add_mesymE.
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

Lemma vb_strip_rem_col0 d (la : intpartn d) :
  vb_strip (conj_part (behead (conj_part la))) la.
Proof using .
rewrite -{2}(conj_intpartnK la) /=.
have Hc : is_part (conj_part la) by apply is_part_conj.
apply hb_strip_conj => //; first by apply is_part_behead.
elim: {d la} (conj_part la) Hc => [//=| s0 s IHs] /= /andP [] H0 /IHs {IHs}.
case: s H0 => [//=| s1 s] /= -> ->.
by rewrite leqnn.
Qed.


Lemma vb_strip_lex (d1 k : nat) (la : intpartn (d1 + k)) mu :
  vb_strip mu la ->
  sumn mu = d1 ->
  is_part mu -> (val la <= incr_first_n mu k)%Ord.
Proof using .
rewrite /=.
elim: mu d1 k la => /= [| m0 mu IHmu] d1 k la Hstr.
  have {Hstr} Hstr := vb_stripP (is_true_true : is_part [::]) (intpartnP _) Hstr.
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
               rewrite -/(is_part (m0 :: mu)) /= => /andP [] _ Hp.
  have Hincl := vb_strip_included Hstr.
  move: Hla; rewrite addn0 /= -/(sumn (m0 :: mu)) => /andP [] /eqP /esym Heq Hla.
  by rewrite (included_sumnE Hla Hincl Heq).
case: la Hstr Hla => [//= |s0 la] /= /andP [] H0 Hstrip.
move=> /andP [] /eqP Heq /andP [] _ Hs.
rewrite leqXE /= ltnXnatE ltnS.
case: (leqP s0 m0) => //= Hm0.
have Hs0 : s0 = m0.+1.
  apply anti_leq; rewrite Hm0.
  by move: H0 => /andP [] _ ->.
subst s0; rewrite eq_refl /= {Hm0}.
move: Heq; rewrite addSn addnS => /eqP; rewrite eqSS -addnA => /eqP /addnI Heq.
have Hla : is_part_of_n (sumn mu + k)%N la.
  by rewrite /= Heq eq_refl Hs.
have /= := IHmu _ _ (IntPartN Hla).
by rewrite leqXE /=; apply.
Qed.

End Alternant.


(** * Jacobi's definition of schur function *)
Section SchurAlternantDef.

Variable (n0 : nat) (R : comRingType).
Local Notation n := (n0.+1).
Local Notation "''s_' k" := (Schur n0 R k)
                              (at level 8, k at level 2, format "''s_' k").
Local Notation rho := (rho n).
Local Notation "''a_' k" := (@alternpol n R 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").

Lemma Schur_cast d d' (la : intpartn d) (Heq : d = d') :
  Schur n0 R (cast_intpartn Heq la) = 's_la.
Proof using . by subst d'; congr Schur. Qed.

Theorem alt_SchurE d (la : intpartn d) :
  size la <= n -> 'a_rho * 's_la = 'a_(mpart la + rho).
Proof using .
suff {d la} H : forall b d, d <= b -> forall (la : intpartn d),
  size la <= n -> 'a_rho * 's_la = 'a_(mpart la + rho) by apply: H.
elim=> [|b IHb] d Hd la.
  move: Hd; rewrite leqn0 => /eqP Hd; subst d.
  rewrite Schur0 mulr1 -{1}(add0m rho)=> _; congr 'a_(_ + rho).
  by rewrite intpartn0 /mpart /= mnmP => i; rewrite !mnmE /=.
case: (leqP d b) => Hdb; first exact: (IHb _ Hdb).
have {Hd Hdb} Hd : d = b.+1 by apply anti_leq; rewrite Hd Hdb.
elim/(finord_wf (T := IntPartNLex.intpartnlex_finPOrdType d)) : la =>
    la IHla Hszla.
pose k := head 1%N (conj_intpartn la).
pose p1 := behead (conj_intpartn la); pose d1 := sumn p1.
have Hk : (d = d1 + k)%N.
  have:= intpartn_sumn (conj_intpartn la).
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
rewrite (bigID (fun P0 : intpartn (d1 + k) => (size P0 <= n))) /= addrC.
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
apply eq_bigr => {A B} nu /andP [] /andP [] Hstrip Hsznu Hnu.
pose nu' := cast_intpartn (esym Hk) nu.
have Hlex : (val nu' < la)%Ord.
  rewrite cast_intpartnE /= {nu'}.
  rewrite ltnX_neqAleqX; apply/andP; split.
    move: Hnu; apply contra => /eqP H.
    by apply/eqP; apply val_inj; rewrite cast_intpartnE.
  rewrite {Hnu Hsznu la'}.
  have /= -> : val la = incr_first_n (conj_part p1) k.
    move: Hk; rewrite /d1 /p1 /= -{2}(conj_intpartnK la) /=.
    rewrite -{1}(intpartn_sumn (conj_intpartn la)) /=.
    case: (conj_part la) => [//= | p0 p] /=; first by rewrite add0n => <-.
    rewrite addnC -{2}(addKn (sumn p) k) => <-.
    by rewrite addKn.
  have:= intpartnP (conj_intpartn mu).
  have /= {Hk p1P mu} := intpartn_sumn (conj_intpartn mu).
  exact: vb_strip_lex.
have Hsznu' : size nu' <= n by rewrite cast_intpartnE.
have := IHla nu' Hlex Hsznu'.
rewrite Schur_cast => ->.
by rewrite cast_intpartnE.
Qed.

End SchurAlternantDef.




(** ** Schur polynomials are symmetric *)
Section IdomainSchurSym.

Variable (n0 : nat) (R : idomainType).
Local Notation n := (n0.+1).
Local Notation "''s_' k" := (Schur n0 R k)
                             (at level 8, k at level 2, format "''s_' k").
Local Notation rho := (rho n).
Local Notation "''a_' k" := (@alternpol n R 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").

Theorem alt_uniq d (la : intpartn d) (s : {mpoly R[n]}) :
  size la <= n -> 'a_rho * s = 'a_(mpart la + rho) -> s = 's_la.
Proof using . by move=> /(alt_SchurE R) <- /(mulfI (alt_rho_non0 n R)). Qed.

Theorem Schur_sym_idomain d (la : intpartn d) : 's_la \is symmetric.
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
Local Notation "''s_' k" := (Schur n0 R k)
                              (at level 8, k at level 2, format "''s_' k").

Theorem Schur_sym d (la : intpartn d) : 's_la \is symmetric.
Proof using .
have -> : 's_la = map_mpoly intr (Schur _ [ringType of int] la).
  rewrite /Schur /polylang /commword raddf_sum /=; apply eq_bigr => i _ /=.
  by rewrite rmorph_prod /=; apply eq_bigr => {i} i _ ; rewrite map_mpolyX.
apply/issymP => s.
have:= Schur_sym_idomain n0 int_iDomain la => /issymP/(_ s) {2}<-.
by rewrite msym_map_mpoly.
Qed.

End RingSchurSym.

Section MPoESymHomog.

Variable (n0 : nat) (R : ringType).
Local Notation n := (n0.+1).

Implicit Types p q r : {mpoly R[n]}.
Implicit Type m : 'X_{1..n}.

Lemma Schur_homog (d : nat) (la : intpartn d) : Schur n0 R la \is d.-homog.
Proof using .
rewrite Schur_tabsh_readingE /polylang /commword.
apply rpred_sum => [[t Ht]] _ /=.
move: Ht => /eqP <-; elim: t => [| s0 s IHs]/=.
  rewrite big_nil; exact: dhomog1.
rewrite big_cons -(add1n (size s)); apply dhomogM; last exact: IHs.
by rewrite dhomogX /= mdeg1.
Qed.

End MPoESymHomog.


(** * Kostka numbers *)
Local Open Scope nat_scope.

Import IntPartNDom.
Import OrdNotations.
Close Scope ord_scope.

Section DefsKostkaMon.

Variables (d : nat) (la : intpartn d) (n : nat).
Implicit Type m : 'X_{1..n.+1}.
Definition eval (w : seq 'I_n.+1) := [tuple count_mem i w | i < n.+1].
Definition KostkaTab m := [set t : tabsh n la | eval (to_word t) == m].
Definition KostkaMon m := #|KostkaTab m|.

Lemma sumn_eval w : sumn (eval w) = size w.
Proof.
rewrite -sumnE /eval big_tuple.
rewrite (eq_bigr (fun i => count_mem i w)) ?sum_count_mem ?count_predT //.
by move=> i _; rewrite !tnth_mktuple.
Qed.

Lemma KostkaMon_sumeval m :
  mdeg m != sumn la -> KostkaMon m = 0.
Proof.
move=> H; apply/eqP; move: H.
apply contraR; rewrite cards_eq0 => /set0Pn /= [t].
rewrite /mdeg sumnE inE => /eqP <-{m}.
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
  have:= congr1 (fun t => tnth t i) IHw.
  rewrite !tnth_mktuple => ->.
  by rewrite mnmE -mnm_tnth.
- apply val_inj => /=; rewrite -H {m H}.
  elim: w => [| w0 w IHw] /=; first by rewrite big_nil.
  rewrite big_cons; apply eq_from_tnth => i.
  have:= (congr1 (fun t => tnth t i) IHw).
  by rewrite !tnth_mktuple mnmE -mnm_tnth => ->.
Qed.

Lemma Kostka_Coeff (R : ringType) m : (Schur n R la)@_m = (KostkaMon m)%:R.
Proof.
rewrite /Schur linear_sum /= /KostkaMon.
rewrite (bigID (fun t : tabsh n la => t \in KostkaTab m)) /=.
rewrite addrC big1 ?add0r; first last.
  by move=> i; rewrite /KostkaTab inE evalE => /negbTE ->.
rewrite (eq_bigr (fun => 1%R)); first last.
  by move=> i; rewrite /KostkaTab inE evalE => /eqP ->; rewrite eq_refl.
by rewrite sumr_const; congr _%:R; apply eq_card => i.
Qed.

Lemma perm_KostkaMon m1 m2 :
  perm_eq m1 m2 -> KostkaMon m1 = KostkaMon m2.
Proof.
move=> /tuple_perm_eqP [s /val_inj Hs].
suff: Posz (KostkaMon m1) = Posz (KostkaMon m2) by move => [].
rewrite -!natz -!(Kostka_Coeff _ (Multinom _)).
set mu1 := Multinom m1.
set mu2 := Multinom m2.
have {Hs} -> : mu1 = [multinom mu2 (s i) | i < n.+1].
  apply val_inj => /=; rewrite Hs.
  by apply eq_from_tnth => i; rewrite tnth_mktuple.
by rewrite -mcoeff_sym (issymP _ (Schur_sym _ _ _)).
Qed.

Lemma tab_eval_partdom (t : tabsh n la) : partdom (eval (to_word t)) la.
Proof.
apply/partdomP => i; rewrite -(shape_tabsh t).
case: (ssrnat.leqP i n.+1) => [Hi| /ltnW Hi]; first last.
  rewrite !take_oversize ?size_tuple //; first last.
    by rewrite size_map (leq_trans (size_tabsh _)).
  by rewrite sumn_eval size_to_word.
rewrite sumn_take big_mkord (big_ord_widen _ _ Hi).
rewrite (eq_bigr (fun j => count_mem j (to_word t))); first last.
  by move=> /= j _; rewrite (nth_map ord0) ?size_enum_ord // nth_ord_enum.
rewrite sum_count_mem /= /to_word count_flatten map_rev sumn_rev.
rewrite -{1}(cat_take_drop i t) map_cat sumn_cat addnC.
rewrite -sumnE big_map big_seq big1 ?add0n; first last.
  move=> /= s Hs; rewrite -(nth_index [::] Hs).
  rewrite nth_drop; apply/eqP; rewrite -leqn0 leqNgt -has_count -all_predC.
  rewrite (eq_all (a2 := fun i0 : 'I_n.+1 => i <= i0)); first last.
    by move=> j /=; rewrite -leqNgt.
  have:= all_ltn_nth_tabsh t (i + index s (drop i t)); apply sub_all.
  by move=> j; apply (leq_trans (leq_addr _ _)).
rewrite /shape -map_take -!sumnE !big_map.
by apply leq_sum => /= j _; apply: count_size.
Qed.

Lemma KostkaMon_partdom m : KostkaMon m != 0 -> partdom m la.
Proof.
rewrite cards_eq0 => /set0Pn [/= t]; rewrite inE => /eqP <-.
exact: tab_eval_partdom.
Qed.

End DefsKostkaMon.



Section KostkaEq.

Variables (d : nat) (la : intpartn d).

Lemma Kostka_mnmwiden n (m : 'X_{1..n.+1}) :
  KostkaMon la m = KostkaMon la (mnmwiden m).
Proof.
rewrite /KostkaMon /KostkaTab.
pose ext_fun := fun (t : tabsh n la) =>
              [seq [seq (widen_ord (leqnSn n.+1) i) | i <- r] | r <- t].
have extP t : is_tab_of_shape n.+1 la (ext_fun t).
  rewrite /is_tab_of_shape /=; apply/andP; split.
  - by rewrite -incr_tab.
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
  have Ht : is_tab_of_shape n la t.
    rewrite /is_tab_of_shape /=; apply/andP; split.
    + rewrite -incr_tab // => [] [i Hio] [j Hjo] /mt2 /= Hi /mt2 /= Hj.
      by rewrite !sub_pord_ltnXE /= !inordK.
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
    apply (eq_from_nth (x0 := ord0)).
    * by rewrite size_map -!nth_shape !shape_tabsh.
    * move=> c Hc.
      rewrite (nth_map ord0); last by move: Hc; rewrite -!nth_shape !shape_tabsh.
      apply val_inj => /=.
      rewrite /t /= (nth_map [::]) // (nth_map ord0) //.
      rewrite inordK //; apply mt2; apply mem_to_word.
      by rewrite /is_in_shape nth_shape.
Qed.

End KostkaEq.


Section Kostka.

Variable d : nat.
Implicit Type la : intpartn d.
Local Notation P := (intpartndom d).

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
have {Hsz H} Hsz : size mu <= n.
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
by rewrite eq_sym intpartn_sumn /mdeg /= sumnE sumn_mpart ?leqSpred.
Qed.

Lemma Kostka_size0 la mu :
  size la > size mu -> Kostka la mu = 0.
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
by rewrite -(shape_tabsh t) size_map {3}Hsz /=.
Qed.

Lemma Kostka_partdom (la mu : P) : 'K(la, mu) != 0 -> mu <=A la.
Proof.
rewrite /Kostka => /KostkaMon_partdom.
rewrite /mpart leqSpred => /partdomP Hdom.
apply/partdomP => i; move/(_ i): Hdom; congr (_ <= _).
rewrite !sumn_take; apply eq_bigr => {i} i _.
case: (ssrnat.ltnP i (size mu)) => Hi.
- have -> : (size mu).-1.+1 = (size mu) by case: (size mu) Hi.
  by rewrite -{1}[i]/(nat_of_ord (Ordinal Hi)) -mnm_nth mnmE.
- rewrite [RHS]nth_default //.
  case: mu Hi => [[|m mu] Hmu] Hi.
  + case: i Hi => [|i].
    * by rewrite -[X in nth _ _ X]/(nat_of_ord (n := 1) ord0) -mnm_nth mnmE.
    * by rewrite nth_default //= size_tuple card_ord.
  + move: Hmu Hi; rewrite /= => _ => Hi.
    by rewrite nth_default // size_tuple card_ord.
Qed.

Lemma Kostka0 (la mu : P) : ~~ (mu <=A la) -> 'K(la, mu) = 0.
Proof.
by move=> H; apply/eqP; move: H; apply contraR; apply Kostka_partdom.
Qed.

Lemma count_nseq (T : eqType) (P : pred T) n x :
  count P (nseq n x) = (P x) * n.
Proof.
rewrite (eq_in_count (a2 := fun => P x)); last by move=> i /nseqP [->].
case: (boolP (P x)) => HPx; rewrite /= ?mul0n ?count_pred0 //.
by rewrite ?mul1n ?0count_predT size_nseq.
Qed.

Lemma Kostka_diag la : 'K(la, la) = 1.
Proof.
case Hla : (size la) => [|szla].
  rewrite /Kostka /KostkaMon Hla.
  move: Hla => /eqP/nilP Hla.
  have {Hla} Hd : d = 0 by rewrite -(intpartn_sumn la) Hla.
  subst d.
  have Ht : is_tab_of_shape 0 la [::] by rewrite intpartn0.
  rewrite [KostkaTab _ _](_ : _ = [set TabSh Ht]) ?cards1 //.
  apply/setP => t; rewrite !inE; apply/eqP/eqP => [|->]/=.
  - rewrite /mpart intpartn0 /= => /(congr1 (fun t : 1.-tuple nat => sumn t)).
    rewrite sumn_eval size_to_word /=.
    rewrite (map_comp _ nat_of_ord) val_enum_ord /= addn0.
    by move=> /(tab0 (tabshP _)) => Ht0; apply val_inj.
  - rewrite /to_word /=; apply eq_from_tnth => i.
    by rewrite /mpart intpartn0 /= !tnth_mktuple /=.
rewrite (Kostka_any la (n := szla)) /KostkaMon ?Hla //.
have Hntht j :
  nth [::] [seq nseq (nth 0 la (nat_of_ord i)) i | i <- enum 'I_szla.+1] j =
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
  rewrite /to_word count_flatten map_rev sumn_rev -sumnE big_map.
  rewrite (big_nth [::]) Hszt big_mkord.
  rewrite (bigD1 (inord i)) //= inordK // big1 ?addn0 //.
  move=> j Hj.
  case: (ssrnat.ltnP j i) => [/IHi -> | Hij].
  - rewrite count_nseq /= inord_val.
    by move: Hj => /negbTE ->; rewrite mul0n.
  - have {Hi Hij} Hij : i < j.
      rewrite ltn_neqAle Hij andbT.
      by move: Hj; apply contra => /eqP ->; rewrite inord_val.
    rewrite (eq_in_count (a2 := pred0)) ?count_pred0 // => /= x.
    rewrite eq_sym /eq_op /= (inordK (ltn_trans Hij _)) //.
    by move=> /(allP (all_ltn_nth_tabsh _ _)) /(leq_trans Hij) /ltn_eqF ->.
- apply eq_from_tnth => i.
  rewrite take_oversize; last by rewrite size_map size_enum_ord -Hla.
  rewrite /eval /mpart Hla ltnSn !tnth_mktuple.
  rewrite /to_word count_flatten map_rev sumn_rev -map_comp.
  rewrite -sumnE big_map enumT -/(index_enum _) (bigD1 i) //=.
  rewrite big1 ?addn0 ?count_nseq /= ?eq_refl ?mul1n //.
  move=> j Hj; apply/count_memPn/nseqP => [] [Heq _].
  by rewrite Heq eq_refl in Hj.
Qed.

End Kostka.


Lemma sumn_rcons s sm : (sumn s + sm)%N = sumn (rcons s sm).
Proof. by rewrite -[RHS]sumn_rev rev_rcons /= sumn_rev addnC. Qed.

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

Section BijectionExtTab.

Variable n : nat.

Local Open Scope nat_scope.

Variables (s : seq nat) (m : nat).
Hypothesis (Hsz : size s < n.+1).
Local Notation sz := (Ordinal Hsz).
Local Lemma Hszrcons : size (rcons s m) <= n.+1.
Proof. by rewrite size_rcons. Qed.

Local Notation P := (intpartn (sumn s)).
Local Notation Pm := (intpartn ((sumn s) + m)).
Variable (mu : Pm).
Local Notation Tm := (tabsh n mu).
Hypothesis Hmu : size mu <= n.+1.

Lemma shape_res_tab_subproof (t : Tm) :
  is_part_of_n (sumn s) (
                 if eqeval t (rcons s m) then shape (filter_gtnX_tab sz t)
                 else locked rowpartn (sumn s)).
Proof.
case: (boolP (eqeval t (rcons s m))) => Hev /= ; last by case: (locked _).
apply/andP; split.
- apply/eqP.
  rewrite -/(size_tab _) -size_to_word -filter_gtnX_to_word size_filter.
  rewrite -sum_count_mem /=.
  transitivity (\sum_(i < n.+1 | i < sz) nth 0 s i).
    apply eq_big => i; rewrite sub_pord_ltnXE ltnXnatE //= => Hi.
    by rewrite (eqevalP _ Hszrcons Hev) nth_rcons Hi.
  rewrite -sumnE (big_nth 0) big_mkord /=.
  by apply esym; apply big_ord_widen; apply ltnW.
- by apply is_part_sht; apply is_tableau_filter_gtnX.
Qed.
Definition shape_res_tab (t : Tm) := IntPartN (shape_res_tab_subproof t).

Lemma hb_strip_shape_res_tab (t : Tm) :
  eqeval t (rcons s m) -> hb_strip (shape_res_tab t) mu.
Proof.
rewrite /shape_res_tab => Hev.
apply/hb_stripP => // i.
rewrite [nth 0 (IntPartN _) _]/= Hev.
have := shape_inner_filter_leqX sz (tabshP t) => /(congr1 (fun s => nth 0 s i)).
rewrite nth_pad => <-.
case: (ssrnat.ltnP i.+1 (size t)) => Hi.
- rewrite /shape !(nth_map [::]) ?size_map //; try by apply ltnW.
  apply/andP; split; first last.
    move/ltnW in Hi.
    by rewrite -(shape_tabsh t) nth_shape size_filter; apply: count_size.
  have:= tabshP t => /is_tableauP [_ /(_ i) Hrow].
  move=> /(_ _ _ (ltnSn i))/dominateP [].
  move: (inhabitant _) => Z.
  rewrite -(shape_tabsh t) nth_shape.
  move Hr : (nth [::] t i) Hrow => r.
  move Hr1 : (nth [::] t i.+1) => r1 Hrow Hszle Hdom.
  rewrite size_filter.
  case: leqP => // Hleq; move/(_ _ Hleq): Hdom.
  move: Hi => /(mem_nth [::]); rewrite Hr1 => Hi.
  set xabs := nth Z r1 (count (ltnX_op^~ sz) r).
  have /count_memPn/eqP : xabs \in to_word t.
    rewrite /to_word; apply/flattenP; exists r1; first by rewrite mem_rev.
    by apply: mem_nth.
  rewrite (eqevalP _ Hszrcons Hev) nth_rcons.
  case: (ssrnat.leqP xabs (size s)) => [Hxabs _ | Hxabs]; first last.
    by rewrite (gtn_eqF Hxabs) ltnNge (ltnW Hxabs).
  rewrite sub_pord_ltnXE ltnXnatE /= => /leq_trans/(_ Hxabs) {xabs Hxabs}.
  have size_take_leq l sq : size (take l sq) <= size sq.
    by rewrite size_take; case ssrnat.ltnP => [/ltnW|].
  move/(_ _ (count (ltnX_op^~ sz) r) r): size_take_leq => HHH.
  have := leq_trans Hleq Hszle.
  rewrite -{2 3}(cat_take_drop (count (ltnX_op^~ sz) r) r) nth_cat.
  rewrite size_take (leq_trans Hleq Hszle) ltnn subnn.
  rewrite size_cat size_take (leq_trans Hleq Hszle).
  rewrite -addn1 leq_add2l -(filter_leqX_row sz Hrow) => /(mem_nth Z).
  move: (nth _ _ _) => xabs.
  rewrite mem_filter /= sub_pord_leqXE leqXnatE andbC => /andP [_] /=.
  move=>/leq_ltn_trans H1/H1.
  by rewrite ltnn.
- rewrite nth_default -(shape_tabsh t) ?size_map //=.
  case: (ssrnat.ltnP i (size t)) => {Hi} Hi.
  + rewrite !(nth_map [::]) ?size_map //.
    by rewrite size_filter; apply: (leq_trans (count_size _ _)).
  + by rewrite !nth_default ?size_map.
Qed.

Variable (la : P).
Hypothesis Hstrip : hb_strip la mu.
Local Notation T := (tabsh n la).

Local Definition Hlamu := size_included (hb_strip_included Hstrip).
Local Definition Hla : size la <= n.+1 := leq_trans Hlamu Hmu.

Definition res_tab (t : Tm) : T :=
  if insub (filter_gtnX_tab sz t) is Some tr then tr
  else locked (tabrowconst Hla).
Local Definition ext_tab_fun (t : T) :=
  if eqeval t s then join_tab t (skew_reshape la mu (nseq m sz))
  else locked (tabrowconst Hmu).

Local Lemma sumndiff : sumn (diff_shape la mu) = m.
Proof.
by rewrite sumn_diff_shape ?hb_strip_included // !intpartn_sumn addKn.
Qed.

Lemma ext_tab_subproof t : is_tab_of_shape n mu (ext_tab_fun t).
Proof.
rewrite /ext_tab_fun.
case: (boolP (eqeval t s)) => [/= Hev |_]; last by case: (locked _).
have Hincl:= hb_strip_included Hstrip.
apply/andP; split.
- apply join_tab_skew => //.
  + rewrite to_word_skew_reshape // ?size_nseq ?sumndiff //.
    apply/allP => /= i /nseqP [->{i} Hsm].
    apply/allP => /= i /count_memPn/eqP Hi.
    rewrite sub_pord_ltnXE ltnXnatE /=.
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
  shape (filter_gtnX_tab sz t) == la ->
  is_tab_of_shape n la (filter_gtnX_tab sz t).
Proof.
rewrite /= andbC => -> /=.
by apply: is_tableau_filter_gtnX; apply tabshP.
Qed.

Lemma eval_res_tab (t : Tm) :
  shape (filter_gtnX_tab sz t) == la ->
  eqeval t (rcons s m) -> eqeval (res_tab t) s.
Proof.
move=> Hsh Hev ; rewrite /res_tab (insubT _ (res_tabP Hsh)) /=.
apply/eqevalP; first exact: ltnW.
move=> i /=; rewrite -filter_gtnX_to_word.
case: (ssrnat.ltnP i sz) => Hisz.
- move: Hev => /(eqevalP _ Hszrcons)/(_ i).
  rewrite nth_rcons Hisz => <-.
  elim: (to_word t) => //= w0 w IHw.
  case: ltnXP; rewrite /= IHw //= /eq_op /=.
  rewrite sub_pord_leqXE leqXnatE /= => /(leq_trans Hisz)/gtn_eqF => ->.
  by rewrite add0n.
- rewrite nth_default //.
  apply/count_memPn; rewrite mem_filter /=.
  by rewrite sub_pord_ltnXE ltnXnatE /= ltnNge Hisz.
Qed.

Lemma eval_ext_tab (t : T) :
  eqeval t s -> eqeval (ext_tab t) (rcons s m).
Proof.
move=> Hev; apply/eqevalP; first by rewrite size_rcons.
move=> i; rewrite /= /ext_tab_fun Hev /=.
have Hszle : size t <= size (skew_reshape la mu (nseq m sz)).
  rewrite size_skew_reshape.
  by apply: (leq_trans _ Hlamu); rewrite -(shape_tabsh t) size_map.
move: Hszle => /perm_eq_join_tab/perm_eqP ->.
rewrite count_cat (eqevalP _ (ltnW Hsz) Hev).
rewrite to_word_skew_reshape ?size_nseq ?sumndiff ?hb_strip_included //.
rewrite count_nseq /= nth_rcons /= {1}/eq_op /=.
case: (ssrnat.ltnP i (size s)) => [/gtn_eqF ->| H].
  by rewrite mul0n addn0.
rewrite (nth_default _ H) add0n eq_sym.
by case: eqP => _; rewrite ?mul0n ?mul1n.
Qed.

Lemma res_tabK (t : Tm) :
  shape (filter_gtnX_tab sz t) == la ->
  eqeval t (rcons s m) -> ext_tab (res_tab t) = t.
Proof.
rewrite /ext_tab => Hsh Hev; apply val_inj => /=.
rewrite /ext_tab_fun eval_res_tab //.
rewrite /res_tab (insubT _ (res_tabP Hsh)) /=.
rewrite -[RHS](join_tab_filter sz (tabshP t)); congr join_tab.
rewrite -[RHS](skew_reshapeK (inner := shape (filter_gtnX_tab sz t))); first last.
  rewrite /shape size_map /filter_gtnX_tab /filter_leqX_tab.
  rewrite size_map /= size_filter; apply: (leq_trans (count_size _ _)).
  by rewrite size_map.
move: Hsh => /eqP Hsh.
congr skew_reshape.
- by rewrite Hsh.
- suff -> : shape (filter_leqX_tab sz t) =
           diff_shape (shape (filter_gtnX_tab sz t)) mu.
    by rewrite diff_shapeK // -(shape_tabsh t); apply included_shape_filter_gtnX.
  apply (eq_from_nth (x0 := 0)).
  - by rewrite size_diff_shape /filter_leqX_tab -(shape_tabsh t) !size_map.
  - move=> i; rewrite /shape !size_map => Hi.
    rewrite -diff_shape_pad0 nth_diff_shape !nth_shape -/(shape _).
    rewrite -(shape_tabsh t) size_map.
    rewrite -shape_inner_filter_leqX //= nth_shape !(nth_map [::]) ?size_map //.
    rewrite !size_filter -(count_predC (ltnX_op^~ sz) (nth [::] t i)).
    rewrite addKn; apply eq_count => x /=.
    by rewrite -leqXNgtnX.
- have Hw : size (to_word (filter_leqX_tab sz t)) = m.
    rewrite -filter_leqX_to_word size_filter -sum_count_mem /=.
    rewrite (bigD1 sz) /= // (eqevalP _ Hszrcons Hev).
    rewrite nth_rcons ltnn eq_refl big1 ?addn0 // => i.
    rewrite eq_sym andbC -/(ltnX_op _ _) sub_pord_ltnXE ltnXnatE /= => Hi.
    rewrite (eqevalP _ Hszrcons Hev) nth_rcons.
    by rewrite ltnNge (ltnW Hi) (gtn_eqF Hi).
  rewrite -{1}Hw; symmetry; apply/all_pred1P/allP => /= i.
  rewrite /to_word => /flattenP [/= rtmp].
  rewrite mem_rev => /mapP [/= r Hr ->{rtmp}].
  rewrite mem_filter sub_pord_leqXE leqXnatE => /andP [/= Hi Hir].
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
  eqeval t s -> filter_gtnX_tab sz (ext_tab t) = t.
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
      [seq x <- nth [::] (skew_reshape la mu (nseq m sz)) i | x <A sz] = [::].
    apply/nilP; rewrite /nilp size_filter.
    rewrite (eq_in_count (a2 := pred0)) ?count_pred0 // => x /=.
    case: (ssrnat.ltnP i (size (skew_reshape la mu (nseq m sz))))
         => [|Hi1]; last by rewrite nth_default.
    rewrite /skew_reshape size_rev => Hi1; rewrite nth_rev //.
    rewrite nth_reshape => /mem_take/mem_drop/nseqP [-> _].
    by rewrite ltnXnn.
  case: (ssrnat.ltnP i (size t)) => {Hi} Hi; first last.
    by rewrite Hfil nth_nseq if_same.
  rewrite Hfil cats0 (eq_in_filter (a2 := predT)) ?filter_predT //.
  move=> x /count_memPn/eqP Hcount.
  rewrite sub_pord_ltnXE ltnXnatE /=.
  suff : nth 0 s x != 0.
    by case: ssrnat.ltnP => // H; rewrite nth_default.
  rewrite -(eqevalP t (ltnW Hsz) Hev x).
  rewrite /to_word count_flatten map_rev sumn_rev -sumnE.
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
  #|[set t : tabsh n mu |
     (eqeval t (rcons s m)) && (shape (filter_gtnX_tab sz t) == la)]|
  = #|[set t : tabsh n la | eqeval t s]|.
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


Section KostkaRec.

Local Open Scope nat_scope.


Lemma Kostka_ind d (la : intpartn d) m mu :
  d = m + sumn mu ->
  Kostka la (m :: mu) =
  \sum_(nu : intpartn (sumn mu) | hb_strip nu la) Kostka nu mu.
Proof.
case: (ssrnat.leqP (size la) (size mu).+1) => Hszla; first last.
  move=> _; rewrite Kostka_size0 //.
  apply esym; apply big1 => nu Hnu; apply Kostka_size0.
  by have := hb_strip_size Hnu => /andP [_ /(leq_trans Hszla)].
rewrite {1}/Kostka addnC => Hd; subst d.
have /perm_eqlP/(perm_eq_mpart _)/perm_KostkaMon <- := perm_rcons m mu.
rewrite /KostkaMon /KostkaTab.
transitivity #|[set t : tabsh (size mu) la | eqeval t (rcons mu m)]|.
  by apply eq_card.
rewrite -sum1dep_card.
have Hszmu := ltnSn (size mu).
pose sht := @shape_res_tab (size mu) mu m Hszmu la.
rewrite (partition_big sht
                       (fun nu : intpartn (sumn mu) => hb_strip nu la)); first last.
  by move=> t Ht; apply hb_strip_shape_res_tab.
apply eq_bigr => /= nu Hstrip; rewrite sum1dep_card.
pose res := res_tab Hszmu Hszla Hstrip.
pose ext := ext_tab Hszmu Hszla Hstrip.
rewrite -(card_in_imset (f := res)); last exact: res_tab_inj.
rewrite (Kostka_any _ (ltnW Hszmu)) /KostkaMon /KostkaTab.
apply eq_card => /= t; rewrite !inE.
apply/imsetP/idP => [[/= T] | Hev].
- rewrite inE => /andP [Hev].
  rewrite /sht /shape_res_tab => /eqP/(congr1 val)/=/eqP.
  by rewrite Hev => Hsh ->{t}; apply : eval_res_tab.
- exists (ext t); last by rewrite /res/ext ext_tabK.
  rewrite inE eval_ext_tab //=.
  apply/eqP/val_inj; rewrite /= -(shape_tabsh t).
  rewrite (eval_ext_tab _ _ Hstrip Hev).
  by have /= -> := (filter_ext_tab Hszmu Hszla Hstrip Hev).
Qed.

Fixpoint Kostka_rec la mu : nat :=
  if mu is m :: mu then
    sumn [seq Kostka_rec nu mu | nu <- enum_partn (sumn mu) & hb_strip nu la]
  else la == [::].

(* Eval compute in Kostka_rec [:: 4; 4; 3; 1] [:: 3; 3; 2; 2; 1; 1]. *)

Lemma Kostka_rec_size0 la mu :
  size la > size mu -> Kostka_rec la mu = 0.
Proof.
elim: mu la => [|m mu IHmu] la /= H; first by case: la H.
rewrite -sumn_map_condE; apply big1 => nu Hnu.
by apply IHmu; have := hb_strip_size Hnu => /andP [_ /(leq_trans H)].
Qed.

Lemma Kostka_recE d (la : intpartn d) mu :
  sumn mu = d -> Kostka_rec la mu = Kostka la mu.
Proof.
elim: mu d la => [| m0 mu IHmu] d la /= Hd.
  subst d; have -> : la = rowpartn 0 by apply val_inj; rewrite /= !intpartn0.
  by rewrite -[[::]]/(pnval (rowpartn 0)) Kostka_diag.
rewrite -sumn_map_condE -enum_intpartnE big_map enumT.
by rewrite Kostka_ind //; apply eq_big => //= nu Hstrip; apply IHmu.
Qed.

(* Eval compute in Kostka_rec [:: 4; 4; 3; 1] [:: 3; 3; 2; 2; 1; 1]. *)

End KostkaRec.


Notation "''K' ( la , mu )" := (Kostka la mu)
  (at level 8, format "''K' ( la ,  mu )") : nat_scope.
Notation "''K' ( la , mu )" := (Kostka la mu)%:R
  (at level 8, format "''K' ( la ,  mu )") : ring_scope.

Require Import unitriginv.

Lemma Kostka_unitrig d :
  unitrig (fun (la mu : intpartndom d) => 'K(la, mu)%:R : int).
Proof.
apply/unitrigP; split => [la | la mu].
- by rewrite Kostka_diag.
- by apply contraR => /Kostka0 ->.
Qed.

(** ** Inverse Kostka numbers *)
Definition KostkaInv d : intpartndom d -> intpartndom d -> int :=
  Minv (fun la mu : intpartndom d => 'K(la, mu)%:R : int).

Lemma KostkaInv_unitrig d : unitrig (@KostkaInv d).
Proof. exact: (Minv_unitrig (@Kostka_unitrig d)). Qed.

Notation "''K^-1' ( la , mu )" := ((KostkaInv la mu)%:~R)
  (at level 8, format "''K^-1' ( la ,  mu )") : ring_scope.

