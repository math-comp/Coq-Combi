(** * Combi.MPoly.antisym : Antisymmetric polynomials and Vandermonde product *)
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
(** * Antisymmetric polynomials

We start by general Polynomials stuff:

- tensR == the scalar extension morphism from [{mpoly Z[n]}] to [{mpoly R[n]}]
           obtained by tensoring the coefficients rings. This is a ring
           morphism.

Antisymmetric polynomials:

- p \is antisym == p is an antisymmetric polynomial. This is a keyed predicate
                   closed by submodule operations [submodPred].

Vandermonde products and determinants:

- alternpol f == the alternating sunm of the permuted of f.
- rho         == the multi-monomial [[n-1, n-2, ..., 1, 0]]
- mpart       == the multi-monomial associated to a partition
- vdmprod n R == the vandermonde product in [{mpoly R[n]}], that is the product
                 << \prod_(i < j) ('X_i - 'X_j) >>.

- antim s     == the n x n - matrix whose (i, j) coefficient is
                 << 'X_i^(s_j - rho_j) >>
- Vandmx      == the Vandermonde matrix << 'X_i^(n - 1 - j) = 'X_i^(rho_j) >>.
- Vandet      == the vandermonde determinant

The main results are the Vandermonde determinant expansion:

- [ vdmprod_alt     : vdmprod = alternpol 'X_[(rho n)] ]
- [ Vandet_vdmprodE : Vandet = vdmprod ]

*******************************************************************************)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice.
Require Import finset fintype finfun tuple bigop ssralg ssrint.
Require Import fingroup perm zmodp binomial.
Require Import ssrcomplements poset freeg mpoly.

Require Import tools symgroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma binomial_sumn_iota n : 'C(n, 2) = sumn (iota 0 n).
Proof. by rewrite -triangular_sum sumnE /index_iota subn0. Qed.

Local Notation "''II_' n" := ('I_n * 'I_n)%type (at level 8, n at level 2).

Lemma card_triangle n : #|[set i : 'II_n | i.1 < i.2]| = 'C(n, 2).
Proof.
  rewrite -card_ltn_sorted_tuples.
  pose f := (fun i : 'II_n => [tuple i.1; i.2]).
  have /card_imset <- : injective f by rewrite /f => [] [i1 i2] [j1 j2] /= [] -> ->.
  congr (card (mem (pred_of_set _))).
  rewrite -setP => [] [[| s0 [| s1 [|s]]]] // Hs.
  rewrite !inE; apply/idP/idP.
  - rewrite /f {f} => /imsetP [[i j]].
    by rewrite inE /= andbT => Hij /(congr1 val) /= [] -> ->.
  - move=> /= /andP [] Hsort _.
    apply/imsetP; exists (s0, s1); first by rewrite inE.
    by apply val_inj.
Qed.

Require Import sorted.
Open Scope nat_scope.

(* TODO : Move in Sorted *)
Lemma sorted_ltn_ind s :
  sorted ltn s -> sumn (iota 0 (size s)) <= sumn s /\ last 0 s >= (size s).-1.
Proof.
  elim/last_ind: s => [//=| s sn IHs] /= Hsort.
  move/(_ (sorted_rconsK Hsort)): IHs => [] Hsum Hlast; split.
  - rewrite -{2}(revK (rcons s sn)) rev_rcons sumn_rev /= [sn + _]addnC sumn_rev.
    rewrite size_rcons -addn1 iota_add /= sumn_cat /= add0n addn0.
    apply (leq_add Hsum).
    case/lastP: s Hsort Hlast {Hsum} => [//= | s sn1] /=.
    rewrite !size_rcons !last_rcons /= -!cats1 -catA cat1s => /sorted_catR /=.
    by rewrite andbT => /(leq_ltn_trans _); apply.
  - case/lastP: s Hsort Hlast {Hsum} => [//= | s sn1] /=.
    rewrite !size_rcons !last_rcons /= -!cats1 -catA cat1s => /sorted_catR /=.
    by rewrite andbT => /(leq_ltn_trans _); apply.
Qed.

(* TODO : Move in Sorted *)
Lemma sorted_sumn_iotaE s :
  sorted ltn s -> sumn s = sumn (iota 0 (size s)) -> s = iota 0 (size s).
Proof.
  elim/last_ind: s => [//= | s sn IHs] /= Hsort.
  have:= sorted_ltn_ind Hsort.
  rewrite -{2 5}(revK (rcons s sn)) rev_rcons sumn_rev /= [sn + _]addnC sumn_rev.
  rewrite size_rcons -{1 3 4}addn1 iota_add /= sumn_cat /= add0n addn0 cats1.
  rewrite last_rcons => [] [] _ Hsn.
  have:= sorted_ltn_ind (sorted_rconsK Hsort) => [] [] Hsum _ /esym.
  by move=> /(leq_addE Hsum Hsn) [] /esym/(IHs (sorted_rconsK Hsort)) <- <-.
Qed.

Import GRing.Theory.

Local Open Scope ring_scope.

(** ** Change of scalar in multivariate polynomials *)
Section ScalarChange.

Variable n : nat.
Variable R : ringType.


Definition tensR := [rmorphism of @map_mpoly n int_Ring R intr].

Lemma tensRX m : tensR 'X_[m] = 'X_[m].
Proof.
  rewrite -mpolyP => mm; rewrite mcoeff_map_mpoly /= !mcoeffX; by case: eqP.
Qed.

Lemma msym_tensR s p : msym s (tensR p) = tensR (msym s p).
Proof.
  rewrite (mpolyE p).
  rewrite [tensR _]raddf_sum [msym s _]raddf_sum.
  rewrite [msym s _]raddf_sum [tensR _]raddf_sum.
  apply eq_bigr => i _ /=.
  rewrite -(intz (p@_i)) scaler_int.
  by rewrite !raddfMz /= tensRX !msymX tensRX.
Qed.

End ScalarChange.

Arguments tensR {n} R.


(** ** Characteristic of multivariate polynomials *)
Section CharMPoly.

Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.

Lemma char_mpoly : [char R] =i [char {mpoly R[n]}].
Proof.
  move=> p; rewrite !unfold_in /= -mpolyC_nat.
  case: (prime.prime p) => //=.
  apply (sameP idP); apply (iffP idP) => [/eqP | /eqP -> //=].
  rewrite -(mpolyP) => /(_ 0%MM).
  by rewrite mcoeff0 raddfMn /= mcoeffMn mcoeff1 eq_refl /= => ->.
Qed.

End CharMPoly.


(** * Symmetric and Antisymmetric multivariate polynomials *)
Section MPolySym.

Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.

Lemma issym_tpermP p :
  reflect (forall i j, msym (tperm i j) p = p)
          (p \is symmetric).
Proof.
  apply (iffP idP).
  - move=> /forallP Hsym i j.
    by rewrite (eqP (Hsym (tperm _ _))).
  - move=> Htperm; apply/forallP => s.
    case: (prod_tpermP s) => ts -> {s} Hall.
    elim: ts Hall => [_ | t0 ts IHts] /=.
      by rewrite !big_nil /= msym1m.
    move=> /andP [] _ /IHts{IHts}/eqP Hrec.
    by rewrite !big_cons msymMm Htperm Hrec.
Qed.

Definition antisym : qualifier 0 {mpoly R[n]} :=
  [qualify p | [forall s, msym s p == (-1) ^+ s *: p]].

Fact antisym_key : pred_key antisym. Proof. by []. Qed.
Canonical antisym_keyed := KeyedQualifier antisym_key.

Lemma isantisymP p :
  reflect (forall s, msym s p = (-1) ^+ s *: p) (p \is antisym).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti s.
    by rewrite (eqP (Hanti s )).
  - move=> H; apply/forallP => s.
    by rewrite H.
Qed.

Definition simplexp := (expr0, expr1, scale1r, scaleN1r, mulrN, mulNr, mulrNN, opprK).

Lemma isantisym_tpermP p :
  reflect (forall i j, msym (tperm i j) p = if (i != j) then - p else p)
          (p \is antisym).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti i j.
    rewrite (eqP (Hanti (tperm _ _))) odd_tperm.
    case: (i != j); by rewrite !simplexp.
  - move=> Htperm; apply/forallP => s.
    case: (prod_tpermP s) => ts -> {s} Hall.
    elim: ts Hall => [_ | t0 ts IHts] /=.
      by rewrite !big_nil odd_perm1 /= msym1m expr0 scale1r.
    move=> /andP [] H0 /IHts{IHts}/eqP Hrec.
    rewrite !big_cons msymMm Htperm H0 msymN Hrec.
    rewrite odd_mul_tperm H0 /=.
    by case: (odd_perm _); rewrite !simplexp.
Qed.

Lemma antisym_char2 : (2 \in [char R]) -> symmetric =i antisym.
Proof.
  move=> Hchar p /=.
  apply (sameP idP); apply (iffP idP).
  - move=> /isantisymP H; apply/issymP => s.
    by rewrite H oppr_char2; first by rewrite expr1n scale1r.
  - move => /issymP H; apply/isantisymP => s.
    by rewrite H oppr_char2; first by rewrite expr1n scale1r.
Qed.

Lemma perm_smalln : n <= 1 -> forall s : 'S_n, s = 1%g.
Proof.
  move=> Hn s; rewrite -permP => i.
  rewrite perm1.
  case: n Hn s i => [| [| n']] //= Hn s; first by case.
  move=> i; case: (s i) => a Ha; case: i => b Hb.
  apply val_inj => /=.
  by case: a b Ha Hb => [|a][|b].
Qed.

Lemma sym_smalln : n <= 1 -> (@symmetric n R) =i predT.
Proof.
  move=> Hn p /=; rewrite [RHS]unfold_in /=.
  apply/issymP => s.
  by rewrite (perm_smalln Hn s) msym1m.
Qed.

Lemma antisym_smalln : n <= 1 -> antisym =i predT.
Proof.
  move=> Hn p /=; rewrite [RHS]unfold_in /=.
  apply/isantisymP => s.
  by rewrite (perm_smalln Hn s) odd_perm1 msym1m expr0 scale1r.
Qed.

Lemma antisym_zmod : zmod_closed antisym.
Proof.
split=> [|p q /isantisymP sp /isantisymP sq]; apply/isantisymP=> s.
  by rewrite msym0 scaler0.
by rewrite msymB sp sq scalerBr.
Qed.

Canonical antisym_opprPred := OpprPred antisym_zmod.
Canonical antisym_addrPred := AddrPred antisym_zmod.
Canonical antisym_zmodPred := ZmodPred antisym_zmod.


Lemma antisym_submod_closed : submod_closed antisym.
Proof.
split=> [|c p q /isantisymP sp /isantisymP sq]; apply/isantisymP=> s.
  by rewrite msym0 scaler0.
rewrite msymD msymZ sp sq.
by rewrite scalerA commr_sign -scalerA scalerDr.
Qed.

Canonical antisym_submodPred := SubmodPred antisym_submod_closed.

Lemma sym_anti p q :
  p \is antisym -> q \is symmetric -> p * q \is antisym.
Proof.
  move=> /isantisymP Hsym /issymP Hanti.
  apply/isantisymP => s.
  rewrite msymM Hsym Hanti.
  by case: (odd_perm _); rewrite !simplexp.
Qed.

Lemma anti_anti p q :
  p \is antisym -> q \is antisym -> p * q \is symmetric.
Proof.
  move=> /isantisymP Hp /isantisymP Hq.
  apply/issymP => s.
  rewrite msymM Hp Hq.
  by case: (odd_perm _); rewrite !simplexp.
Qed.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Lemma isantisym_msupp p (s : 'S_n) (m : 'X_{1..n}) : p \is antisym ->
  (m#s \in msupp p) = (m \in msupp p).
Proof.
  rewrite !mcoeff_msupp -mcoeff_sym => /isantisymP ->.
  case: (odd_perm s); last by rewrite expr0 scale1r.
  rewrite expr1 scaleN1r !mcoeff_eq0.
  by rewrite (perm_eq_mem (msuppN _)).
Qed.


Lemma mlead_antisym_sorted (p : {mpoly R[n]}) : p \is antisym ->
  forall (i j : 'I_n), i <= j -> (mlead p) j <= (mlead p) i.
Proof.
move=> sym_p i j le_ij; have [->|nz_p] := eqVneq p 0.
  by rewrite mlead0 !mnm0E.
set m := mlead p; case: leqP=> // h.
pose s := tperm i j; pose ms := m#s; have: (m < ms)%O.
  apply/lemP; first by rewrite mdeg_mperm.
  exists i=> [k lt_ki|]; last by rewrite mnmE tpermL.
  rewrite mnmE tpermD // neq_ltn orbC ?lt_ki //.
  by move/leq_trans: lt_ki => /(_ _ le_ij) ->.
have: ms \in msupp p by rewrite isantisym_msupp // mlead_supp.
by move/msupp_le_mlead/leoNgt/negbTE=> ->.
Qed.

End MPolySym.

Implicit Arguments antisym [n R].



Lemma issym_eltrP n (R : ringType) (p : {mpoly R[n.+1]}) :
  reflect (forall i, i < n -> msym (eltr n i) p = p) (p \is symmetric).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti i Hi.
    by have /eqP -> := Hanti (eltr n i).
  - move=> Heltr; apply/forallP; elim/eltr_ind => [| S i Hi /eqP IH].
    + by rewrite msym1m.
    + by rewrite msymMm (Heltr i Hi) IH.
Qed.

Lemma isantisym_eltrP n (R : ringType) (p : {mpoly R[n.+1]}) :
  reflect (forall i, i < n -> msym (eltr n i) p = - p) (p \is antisym).
Proof.
  apply (iffP idP).
  - move=> /forallP Hanti i Hi.
    have /eqP -> := Hanti (eltr n i).
    by rewrite /eltr odd_tperm (inordi1 Hi) !simplexp.
  - move=> Heltr; apply/forallP; elim/eltr_ind => [| S i Hi /eqP IH].
    + by rewrite odd_perm1 /= msym1m !simplexp.
    + rewrite msymMm (Heltr i Hi).
      rewrite msymN IH odd_mul_tperm (inordi1 Hi) addTb.
      by case: (odd_perm _); rewrite !simplexp.
Qed.




(** * Alternating polynomials *)
Definition alternpol n (R : ringType) (f : {mpoly R[n]}) :=
  \sum_(s : 'S_n) (-1) ^+ s *: msym s f.

Section AlternIDomain.

Variable n : nat.
Variable R : idomainType.
Hypothesis Hchar : ~~ (2 \in [char R]).


Lemma sym_antisym_char2 :
  n >= 2 -> forall p : {mpoly R[n]}, p \is symmetric -> p \is antisym -> p = 0.
Proof.
  move: Hchar; rewrite (char_mpoly n R) => Hchp Hn p /= /issymP Hsym /isantisymP Hanti.
  have H0 : 0 < n by apply: (ltn_trans _ Hn).
  pose s := (tperm (Ordinal H0) (Ordinal Hn)).
  have := Hanti s; rewrite Hsym.
  rewrite odd_tperm /= => /eqP; rewrite !simplexp -addr_eq0.
  rewrite -mulr2n -mulr_natr mulf_eq0 => /orP [/eqP -> //|] /= /eqP /= H2.
  exfalso; rewrite {Hsym Hanti H0 s}.
  by move: Hchp; rewrite negb_and H2 eq_refl.
Qed.

Section Lead.

Variable p : {mpoly R[n]}.

Implicit Types q r : {mpoly R[n]}.

Hypothesis Hpn0 : p != 0.
Hypothesis Hpanti : p \is antisym.

Lemma sym_antiE q :(q \is symmetric) = (p * q \is antisym).
Proof.
  case: (leqP n 1) => Hn.
    by rewrite !(sym_smalln Hn) !(antisym_smalln Hn) !unfold_in /=.
  apply (sameP idP); apply (iffP idP); last exact: (sym_anti Hpanti).
  move: Hpanti => /isantisymP Hsym /isantisymP Hpq.
  apply/issymP => s.
  have:= Hpq s; rewrite msymM Hsym => H; apply (mulfI Hpn0).
  move: H; case: (odd_perm s); rewrite !simplexp; last by [].
  by move=> /oppr_inj.
Qed.


Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Lemma isantisym_msupp_uniq (m : 'X_{1..n}) : m \in msupp p -> uniq m.
Proof.
  rewrite mcoeff_msupp => Hsupp.
  case: (boolP (uniq m)) => // /(notuniq_witnessP 0%N).
  move=> [] i [] j []; rewrite size_tuple => /andP [] Hi Hj Hnth.
  move/isantisymP/(_ (tperm (Ordinal (ltn_trans Hi Hj)) (Ordinal Hj))) : Hpanti.
  rewrite odd_tperm /eq_op /=.
  rewrite (ltn_eqF Hi) expr1 scaleN1r.
  move/(congr1 (mcoeff m)); rewrite mcoeffN mcoeff_sym.
  have -> : m#tperm (Ordinal (ltn_trans Hi Hj)) (Ordinal Hj) = m.
    rewrite mnmP => k; rewrite mnmE.
    case: (tpermP _ _ k) => [-> | -> |] //;
    by rewrite !(mnm_nth 0) /= Hnth.
  move/eqP; rewrite -addr_eq0.
  rewrite -mulr2n -mulr_natr mulf_eq0.
  move: Hchar; rewrite negb_and => /negbTE ->.
  by move: Hsupp => /negbTE ->.
Qed.

Hypothesis Hphomog : p \is 'C(n , 2).-homog.

Lemma isantisym_mlead_iota : mlead p = rev (iota 0 n) :> seq nat.
Proof.
  move: Hphomog; rewrite binomial_sumn_iota => /dhomogP Hhomog.
  have Huniq := isantisym_msupp_uniq (mlead_supp Hpn0).
  rewrite -(revK (mlead p)) -{4}(size_tuple (mlead p)) -size_rev; congr rev.
  apply sorted_sumn_iotaE; first last.
    rewrite size_rev size_tuple sumn_rev -sumnE -/(mdeg _).
    by rewrite (Hhomog _ (mlead_supp Hpn0)).
  rewrite ltn_sorted_uniq_leq rev_uniq Huniq /=.
  rewrite {Huniq Hhomog} rev_sorted.
  apply/sortedP.
    - by move=> i j k /= /(leq_trans _); apply.
    - by move=> i /=.
  move=> i j; rewrite size_tuple=> /andP [] Hij Hj.
  have H := mlead_antisym_sorted Hpanti.
  have /= := H (Ordinal (leq_ltn_trans Hij Hj)) (Ordinal Hj) Hij.
  by rewrite !(mnm_nth 0) /=; apply.
Qed.

Definition rho := [multinom (n - 1 - i)%N | i < n].
Definition mpart (s : seq nat) := [multinom (nth 0 s i)%N | i < n].

Local Notation "''e_' k" := (@mesym n R k) (at level 8, k at level 2, format "''e_' k").
Local Notation "''a_' k" := (@alternpol n R 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").

Lemma rho_iota : rho = rev (iota 0 n) :> seq nat.
Proof.
  apply (eq_from_nth (x0 := 0%N)).
    by rewrite size_rev size_iota size_map size_enum_ord.
  move=> i; rewrite size_map size_enum_ord => Hi.
  rewrite nth_rev size_iota // (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
  rewrite nth_enum_ord // nth_iota; first last.
    case: n Hi => [// | m] _; by rewrite ltnS subSS; exact: leq_subr.
  rewrite add0n; case: n Hi => [// | m] _; by rewrite !subSS subn0.
Qed.

Lemma alt_homog : 'a_rho \is 'C(n, 2).-homog.
Proof.
  apply rpred_sum => s _; rewrite rpredZsign msymX dhomogX /=.
  have -> : mdeg (rho#(s^-1)%g) = mdeg rho.
    rewrite /mdeg; apply eq_big_perm; apply/tuple_perm_eqP; by exists (s^-1)%g.
  rewrite /mdeg binomial_sumn_iota -sumnE; apply/eqP.
  apply eq_big_perm; rewrite rho_iota perm_eq_sym; exact: perm_eq_rev.
Qed.

Lemma alt_anti m : 'a_m \is antisym.
Proof.
  apply/isantisymP => S.
  rewrite /alternpol.
  rewrite (big_morph (msym S) (@msymD _ _ _) (@msym0 _ _ _)).
  rewrite scaler_sumr.
  rewrite [RHS](reindex_inj (mulIg S)); apply: eq_big => //= s _.
  rewrite msymZ -msymMm scalerA; congr (_ *: _).
  by rewrite odd_permM signr_addb [X in (_  = _ * X)]mulrC signrMK.
Qed.

Lemma isantisym_mlead_rho : mlead p = rho.
Proof.
  apply val_inj => /=; apply val_inj => /=; by rewrite isantisym_mlead_iota rho_iota.
Qed.

End Lead.

Local Notation "''e_' k" := (@mesym _ _ k) (at level 8, k at level 2, format "''e_' k").
Local Notation "''a_' k" := (alternpol 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").


Lemma isantisym_alt (p : {mpoly R[n]}) :
  p != 0 -> p \is antisym -> p \is ('C(n, 2)).-homog -> p = p@_rho *: 'a_rho.
Proof.
  move=> Hpn0 Hanti Hhom.
  apply/eqP; rewrite -subr_eq0; apply contraT => Habs.
  have /(isantisym_mlead_rho Habs) H : p - p@_rho *: 'a_rho \is antisym.
    apply (rpredD Hanti); apply rpredNr; apply rpredZ; exact: alt_anti.
  move: Habs => /mlead_supp.
  have /H{H} ->: p - p@_rho *: 'a_rho \is ('C(n, 2)).-homog.
    apply (rpredD Hhom); apply rpredNr; apply rpredZ; exact: alt_homog.
  rewrite mcoeff_msupp linearB /= linearZ linear_sum /=.
  rewrite (bigID (xpred1 1%g)) /= big_pred1_eq.
  rewrite odd_perm1 /= expr0 scale1r msym1m mcoeffX eq_refl /=.
  rewrite big1; first by rewrite addr0 mulr1 subrr eq_refl.
  move=> s Hs; apply /eqP; move: Hs; apply contraR.
  rewrite linearZ /= msymX mcoeffX.
  case: (altP ( _ =P rho)); last by rewrite mulr0 eq_refl.
  rewrite mnmP => H _; rewrite -eq_invg1; apply/eqP.
  rewrite -permP => i; rewrite perm1.
  move /(_ i) : H => /=.
  rewrite /rho !mnm_tnth !tnth_mktuple !mnm_tnth !tnth_mktuple !subn1 => H.
  rewrite -[LHS]rev_ordK -[RHS]rev_ordK; congr rev_ord.
  apply val_inj => /=; rewrite !subnS.
  have:= ltn_ord i => /ltn_predK {1 5}<-; by rewrite !subSKn.
Qed.

End AlternIDomain.


(** ** Vandermonde product *)
Definition vdmprod n (R : ringType) : {mpoly R[n]} :=
  \prod_(p : 'II_n | p.1 < p.2) ('X_p.1 - 'X_p.2).

Implicit Arguments vdmprod [n R].

Section EltrP.

Variable n i : nat.
Implicit Type (p : 'II_n.+1).

(* TODO : This should only be locaa *)
Definition eltrp p := (eltr n i p.1, eltr n i p.2).
Definition predi p := (p.1 < p.2) && (p != (inord i, inord i.+1)).

Lemma predi_eltrp p : i < n -> predi p -> predi (eltrp p).
Proof.
  move=> Hi.
  have Hii1 : val (@inord n i.+1) = (@inord n i).+1.
    rewrite /= inordK; last by apply (leq_trans Hi).
    by rewrite /= inordK; last by apply (leq_trans Hi).
  move: p => [u v] /=; rewrite /predi /= /eltrp /eltr => /andP [] Hlt Hneq.
  case: (altP (inord i =P u)) => Hu.
    subst u; rewrite tpermL.
    case: (altP (v =P inord i.+1)) Hneq Hlt => Hu; first by subst v => /=; rewrite eq_refl.
    move=> _ Hlt.
    rewrite tpermD; first last.
      by rewrite eq_sym.
      by rewrite neq_ltn Hlt.
    apply/andP; split.
    - rewrite ltn_neqAle eq_sym Hu /=.
      by rewrite Hii1.
    - rewrite /eq_op /= eq_sym.
      apply/nandP; left.
      rewrite /eq_op /= Hii1.
      by rewrite ieqi1F.
  case: (altP (inord i.+1 =P u)) => Hu1.
    subst u; rewrite tpermR /=.
    rewrite tpermD; first last.
    - move: Hlt; by rewrite ltn_neqAle => /andP [].
    - move: Hlt; rewrite Hii1 => /ltnW.
      by rewrite ltn_neqAle => /andP [].
    apply/andP; split.
    - apply: (ltn_trans _ Hlt).
      by rewrite Hii1.
    - rewrite /eq_op /= eq_refl /= eq_sym.
      move: Hlt; by rewrite ltn_neqAle => /andP [].
  rewrite (tpermD Hu Hu1); apply/andP; split; first last.
    apply/nandP => /=; left; by rewrite eq_sym.
  case: (altP (inord i =P v)) => Hv.
    subst v; rewrite tpermL Hii1.
    by apply (leq_trans Hlt).
  case: (altP (inord i.+1 =P v)) => Hv1.
    subst v; rewrite tpermR.
    move: Hlt; by rewrite Hii1 ltnS ltn_neqAle eq_sym Hu /=.
  by rewrite tpermD.
Qed.

Lemma predi_eltrpE p : i < n -> predi p = predi (eltr n i p.1, eltr n i p.2).
Proof.
  move=> Hi; apply/(sameP idP); apply(iffP idP); last by apply predi_eltrp.
  set p1 := ( _, _).
  suff -> : p = ((eltr n i) p1.1, (eltr n i) p1.2) by apply predi_eltrp.
  rewrite /p1 /= !tpermK {p1}.
  by case: p.
Qed.

End EltrP.

Lemma vdmprod_anti n (R : comRingType) : @vdmprod n R \is antisym.
Proof.
  case: n => [| n].
    apply/isantisymP => s.
    have -> : s = 1%g by rewrite -permP => i; have := ltn_ord i.
    by rewrite msym1m odd_perm1 simplexp.
  apply/isantisym_eltrP => i Hi.
  rewrite /vdmprod.
  rewrite (bigD1 (inord i, inord i.+1)) /=; last by rewrite !inordK //=; apply (leq_trans Hi).
  rewrite msymM -mulNr; congr (_ * _).
    rewrite msymB opprB; congr (_ - _); rewrite /msym mmapX mmap1U /eltr.
    - by rewrite tpermL.
    - by rewrite tpermR.
  rewrite (big_morph _ (msymM (eltr n i)) (msym1 _ (eltr n i))) /=.
  rewrite (eq_bigl (fun p : 'II_n.+1 => predi i (eltrp i p))); first last.
    move=> [u v] /=; by rewrite -/(predi i (u,v)) (predi_eltrpE (u, v) Hi) /=.
  rewrite (eq_bigr (fun p => 'X_(eltrp i p).1 - 'X_(eltrp i p).2)); first last.
    move => [u v] /= _; by rewrite msymB /msym !mmapX !mmap1U.
  rewrite -(big_map (@eltrp n i) (predi i) (fun p => ('X_p.1 - 'X_p.2))) /=.
  rewrite /index_enum -enumT /=.
  set en := enum _.
  rewrite (eq_big_perm en) //=.
  have Hin : map (eltrp i) en =i en.
    move=> [u v].
    rewrite mem_enum inE.
    have -> : (u, v) = eltrp i (eltrp i (u, v)) by rewrite /eltrp /= !tpermK.
    apply map_f.
    by rewrite mem_enum inE.
  apply: (uniq_perm_eq _ _ Hin).
  - rewrite (perm_uniq Hin); first by apply enum_uniq.
    by rewrite size_map.
  - by apply enum_uniq.
Qed.

Lemma sym_vdmprodM n (R : comRingType) (p : {mpoly R[n]}) :
  p \is symmetric -> vdmprod * p \is antisym.
Proof. apply sym_anti; by apply vdmprod_anti. Qed.


Section VdMProdIDomain.

Variable n : nat.
Variable R : idomainType.

Local Notation D := (@vdmprod n R).
Local Notation "'X_ i" := (@mpolyX n R U_(i)).


Lemma vdmprod_homog : D \is homog [measure of mdeg].
Proof.
  rewrite /vdmprod -big_filter.
  set F := BIG_F; rewrite (eq_bigl (fun x => xpredT (F x))) //.
  rewrite -(big_map F xpredT id) /F {F}.
  apply prod_homog; apply/allP => X /mapP [[i j]] /= _ -> {X}.
  apply/homogP; exists 1%N; apply rpredB; by rewrite dhomogX /= mdeg1.
Qed.

Lemma polyX_inj (i j : 'I_n) : 'X_i = 'X_j -> i = j.
Proof.
  move/(congr1 (mcoeff U_(j))); rewrite !mcoeffX eq_refl /=.
  case: (altP (U_(i)%MM =P U_(j)%MM)) => [H _ | _ /esym /= /eqP] /=; first last.
    by have:= oner_neq0 R => /negbTE ->.
  have:= congr1 (fun x : 'X_{1..n} => x j) H.
  rewrite !mnm1E eq_refl eq_sym; by case: eqP.
Qed.

Lemma diffX_neq0 (i j : 'I_n) : i != j -> 'X_i - 'X_j != 0.
Proof. by apply contra; rewrite subr_eq0 => /eqP /polyX_inj ->. Qed.

Lemma msuppX1 i : msupp 'X_i = [:: U_(i)%MM].
Proof. rewrite msuppE /= unlock /= domU //; exact: oner_neq0. Qed.

Lemma vdmprod_neq0 : D != 0.
Proof.
  rewrite /vdmprod -big_filter prodf_seq_neq0.
  apply/allP => [[i j]]; rewrite mem_filter /= => /andP [].
  rewrite ltn_neqAle => /andP [] Hij _ _; exact: diffX_neq0.
Qed.

Lemma vdmprod_dhomog : D \is 'C(n, 2).-homog.
Proof.
  have:= vdmprod_homog; rewrite homog_msize.
  suff -> : (msize D).-1 = 'C(n, 2) by [].
  rewrite /vdmprod -big_filter; set s := filter _ _.
  have <-: size s = 'C(n, 2).
    rewrite /s{s} /index_enum.
    rewrite (eq_filter (a2 := mem [set i : 'II_n | i.1 < i.2])); first last.
      by move => i /=; rewrite inE.
    by rewrite -cardE card_triangle.
 have : all (fun i => i.1 != i.2) s.
    rewrite {}/s; apply/allP => [[i j]] /=.
    rewrite mem_filter /= => /andP [].
    by rewrite ltn_neqAle => /andP [] ->.
  elim: s => [| [i j] s IHs] /=; first by rewrite big_nil msize1.
  move=> /andP [] Hs Hall; move /(_ Hall) : IHs => Hrec.
  have Hprodn0: \prod_(j0 <- s) ('X_j0.1 - 'X_j0.2) != 0.
    rewrite {i j Hs} prodf_seq_neq0; apply/allP => [[i j]] /= /(allP Hall) /=.
    exact: diffX_neq0.
  rewrite big_cons (msizeM (diffX_neq0 Hs) Hprodn0).
  have -> : msize ('X_i - 'X_j : {mpoly R[n]}) = 2.
    rewrite msizeE.
    have : perm_eq (msupp ('X_i - 'X_j : {mpoly R[n]})) [:: U_(i); U_(j)]%MM.
      apply: (perm_eq_trans (msuppD _)).
        move=> m /=; rewrite (perm_eq_mem (msuppN _)) !mcoeff_msupp !mcoeffX.
        case: (altP (U_(j)%MM =P m)) => /= [<- {m} |]; last by rewrite eq_refl andbF.
        suff -> : U_(i)%MM == U_(j)%MM = false by rewrite eq_refl.
        apply negbTE; move: Hs; apply contra => /eqP/(congr1 (fun x : 'X_{1..n} => x j)).
        rewrite !mnm1E eq_refl eq_sym; by case: eqP.
      by rewrite !msuppX1 cat1s perm_cons -msuppX1 msuppN.
    move=> /(eq_big_perm _) -> /=; by rewrite !big_cons big_nil !mdeg1.
  rewrite addSn add1n /= -Hrec.
  move: Hprodn0; rewrite -msize_poly_eq0.
  by case: (msize _).
Qed.

Local Notation "''a_' k" := (alternpol 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").
Local Notation rho := (rho n).
Let abound b  : {mpoly R[n]} :=
  \prod_(p : 'II_n | p.1 < p.2 <= b) ('X_p.1 - 'X_p.2).
Let rbound b := [multinom (b - i)%N | i < n].

Lemma mesymlm_rbound b : (mesymlm n b <= rbound b)%MM.
Proof.
  apply/mnm_lepP => i.
  rewrite !mnmE inE.
  case (ssrnat.ltnP i b) => [/= Hb| //].
  by rewrite subn_gt0.
Qed.

Hypothesis Hchar : ~~ (2 \in [char R]).

Lemma coeffXdiff (b : 'I_n) (k : 'X_{1..n}) (i : 'I_n) :
  (k <= rbound b)%MM -> ('X_i - 'X_b)@_k = (k == U_(i)%MM)%:R.
Proof.
  rewrite mcoeffB !mcoeffX => Hk.
  suff -> : (U_(b)%MM == k) = false by rewrite subr0 eq_sym.
  apply/(introF idP) => /eqP; rewrite mnmP => /(_ b).
  rewrite mnm1E eq_refl => /esym /= => Hkb.
  have {Hkb} : k b != 0%N by rewrite Hkb.
  by rewrite -lep1mP => /lepm_trans/(_ Hk); rewrite lep1mP mnmE /= subnn eq_refl.
Qed.

Lemma coeff_prodXdiff (b : 'I_n) (k : 'X_{1..n}) :
  (k <= rbound b)%MM ->
  (\prod_(i < n | i < b) ('X_i - 'X_b))@_k = (k == mesymlm n b)%:R.
Proof.
  case: b => b /=.
  elim: {1 5 7}b (leqnn b) k => [| c IHc] Hc k Hb Hk.
    rewrite big1 //.
    suff -> : mesymlm n 0 = 0%MM by rewrite mcoeff1.
    rewrite mnmP => i; by rewrite !mnmE /mesymlmnm inE ltn0.
  set ordb := Ordinal Hb.
  move/(_ (ltnW Hc)) : IHc => Hrec.
  have Hcn := ltn_trans Hc Hb.
  pose ordc := Ordinal Hcn.
  rewrite (bigID (xpred1 ordc)) /=.
    rewrite (eq_bigl (xpred1 ordc)); first last.
      move=> i /=; case: eqP => [->|]; last by rewrite andbF.
      by rewrite /= ltnSn.
    rewrite (eq_bigl (fun i : 'I_n => i < c)); first last.
      move=> i /=; by rewrite ltnS ltn_neqAle [RHS]andbC.
  rewrite big_pred1_eq.
  rewrite (mcoeff_poly_mul_lin _ _ (k := (mdeg k).+2)) //.
  case: (boolP (U_(ordc) <= k)%MM) => Hck.
  - have ordc_bound : mdeg (U_(ordc))%MM < (mdeg k).+2 by rewrite mdeg1.
    pose mc := BMultinom ordc_bound; rewrite (bigID (xpred1 mc)) /=.
    rewrite (eq_bigl (xpred1 mc)); first last.
      move=> m /=; case eqP => [->|]; last by rewrite andbF.
      by rewrite /= Hck.
    rewrite big_pred1_eq /= coeffXdiff; last exact: (lepm_trans Hck Hk).
    rewrite eq_refl mul1r {}Hrec; first last.
      apply: (lepm_trans _ Hk); apply/mnm_lepP => i.
      rewrite mnmBE; exact: leq_subr.
    rewrite big1 ?addr0; first last.
      move=> m /andP [] Hmk Hmc1; rewrite coeffXdiff; last exact: (lepm_trans Hmk Hk).
      move: Hmc1; rewrite {1}/eq_op /= => /= /negbTE /= ->; by rewrite mul0r.
      rewrite -{2}(submK Hck).
      have -> : mesymlm n c.+1 = (mesymlm n c + U_(ordc))%MM.
        rewrite mnmP => i; rewrite !mnmE !inE ltnS leq_eqVlt orbC eq_sym {2}/eq_op/=.
        case: eqP => [->|_]; first by rewrite ltnn.
        by rewrite orbF addn0.
        congr (nat_of_bool _)%:R; apply/idP/idP => [/eqP <- //| /eqP Heq]; apply/eqP.
        by rewrite -[RHS](addmK (U_(ordc))%MM) -[LHS](addmK (U_(ordc))%MM) Heq.
  - rewrite big1; first last.
      move=> m /= Hm; rewrite coeffXdiff; last exact: (lepm_trans Hm Hk).
      suff -> : m == U_(ordc)%MM :> 'X_{1..n} = false by rewrite mul0r.
      apply/(introF idP) => /eqP; rewrite mnmP => /(_ ordc).
      rewrite mnm1E eq_refl /= => Habs; move: Hck.
      have : (U_(ordc) <= m)%MM by rewrite lep1mP {}Habs.
      by move/lepm_trans/(_ Hm) => ->.
    suff -> : (k == mesymlm n c.+1) = false by [].
    apply/(introF idP) => /eqP; rewrite mnmP => /(_ ordc).
    move: Hck; rewrite lep1mP negbK => /eqP ->.
    by rewrite /mesymlm /mesymlmnm /mesym1 /= mnmE inE /= ltnSn.
Qed.

Lemma mcoeff_arbound b : b < n -> (abound b)@_(rbound b) = 1.
Proof.
  elim: b => [Hb | b IHb Hb1].
    rewrite /abound {Hb} big1; first last.
      by move=> [i j] /= /andP [] /leq_trans H/H{H}.
    rewrite mcoeff1 /=.
    suff -> : rbound 0 = 0%MM by rewrite eq_refl.
    rewrite mnmP => i; by rewrite mnmE.
  move/(_ (ltnW Hb1)): IHb => Hrec.
  rewrite /abound (bigID (fun p : 'II_n => p.2 <= b)) /=.
  rewrite (eq_bigl (fun p : 'II_n => p.1 < p.2 <= b)); first last.
    move=> [i j]/=; case: (leqP j b); last by rewrite !andbF.
    rewrite -ltnS => /ltnW ->; by rewrite !andbT.
  rewrite mulrC -/(abound _).
  pose ordb1 := Ordinal Hb1.

  rewrite [X in X * _](_ : _ =
             \prod_(i : 'I_n | i <= b)  ('X_i - 'X_ordb1)); first last.
    rewrite (eq_bigl (fun p : 'II_n => (p.1 <= b) && (p.2 == ordb1))); first last.
      move=> [i j]/=. rewrite -ltnNge -andbA -eqn_leq.
      case: eqP => Hj.
      - have -> : j = ordb1 by apply val_inj.
        by rewrite eq_refl /= ltnS.
      - suff -> : (j == ordb1) = false by rewrite !andbF.
        by apply negbTE; move: Hj => /eqP; apply contra => /eqP ->.
    rewrite (reindex (fun i : 'I_n => (i, ordb1))) /=.
    - by apply eq_bigl => i; rewrite eq_refl andbT.
    exists (fun p : 'II_n => p.1) => //.
    by move=> [i j] /=; rewrite inE /= => /andP [] _ /eqP <-.
  rewrite (mcoeff_poly_mul_lin _ _
                  (k := (mdeg (rbound b.+1)).+1)) //.
  have /= := @coeff_prodXdiff ordb1.
  rewrite (eq_bigl (fun i : 'I_(_) => i <= b)); last by move=> i /=; rewrite ltnS.
  move=> Hprod.
  have Hmesymlm : mdeg (mesymlm n b.+1) < (mdeg (rbound b.+1)).+1.
    rewrite ltnS /mdeg !big_tuple; apply leq_sum => i _.
    rewrite -!mnm_tnth; by move: (mesymlm_rbound b.+1) => /mnm_lepP; apply.
  pose msmb := BMultinom Hmesymlm.
  rewrite (bigID (xpred1 msmb)) /=.
  rewrite (eq_bigl (xpred1 msmb)); first last.
    move=> m /=; case: eqP => [->|]; last by rewrite andbF.
    by rewrite /= mesymlm_rbound.
  rewrite big_pred1_eq /= {}Hprod ?mesymlm_rbound // eq_refl mul1r.
  rewrite big1 ?addr0; first last.
    move=> m /andP [] Hm Hneq.
    rewrite (eq_bigl (fun i : 'I_(_) => i < b.+1)); last by move=> i /=; rewrite ltnS.
    rewrite (@coeff_prodXdiff ordb1) //.
    move: Hneq; rewrite {1}/eq_op/= => /negbTE -> /=; by rewrite mul0r.
  rewrite -Hrec; congr mcoeff.
  rewrite mnmP => i; rewrite !mnmE inE ltnS.
  case: leqP => /= Hi.
  - by rewrite subnAC subSS subn0.
  - rewrite subn0.
    have := Hi; rewrite /leq => /eqP ->.
    have := ltnW Hi; by rewrite /leq => /eqP ->.
Qed.

Lemma vdmprod_coeff_rho : D@_rho = 1.
Proof.
  rewrite /vdmprod.
  case: (altP (n =P 0%N)) => [Hn |].
  - rewrite big1; last by move=> [[i Hi]]; exfalso; rewrite Hn in Hi.
    suff -> : rho = 0%MM by rewrite mcoeff1 eq_refl.
    by rewrite mnmP => [[i Hi]]; exfalso; rewrite Hn in Hi.
  - rewrite -lt0n => /prednK/eqP; rewrite eqn_leq => /andP [].
    move=> /mcoeff_arbound <- _.
    congr mcoeff; first by rewrite /rho subn1.
    apply eq_bigl => [[i j]] /=.
    case: n i j => [//=| n'] i j /=; first by have:= ltn_ord i.
    by rewrite -(ltnS j) ltn_ord andbT.
Qed.

Lemma vdmprod_alt_idomain : D = 'a_rho.
Proof.
  rewrite (isantisym_alt Hchar
            vdmprod_neq0 (vdmprod_anti _ _) vdmprod_dhomog).
  by rewrite vdmprod_coeff_rho scale1r.
Qed.

End VdMProdIDomain.

Lemma vdmprod_alt n (R : ringType) :
  vdmprod = alternpol 'X_[(rho n)] :> {mpoly R[n]}.
Proof.
  have /(vdmprod_alt_idomain n)/(congr1 (tensR R)) : 2 \notin [char int] by [].
  rewrite /vdmprod raddf_sum rmorph_prod.
  rewrite (eq_bigr (fun i => 'X_i.1 - 'X_i.2)); first last.
    move=> [i j] _ /=; by rewrite raddfB /= !tensRX.
  move ->; apply eq_bigr => s _; by rewrite raddfZsign !msymX /= tensRX.
Qed.

Require Import matrix.


(** ** Vandermonde matrix and determinant *)
Section VandermondeDet.

Variable n : nat.
Variable R : comRingType.

Local Notation "''a_' k" := (alternpol 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").
Local Notation rho := (rho n).

Definition antim (s : seq nat) : 'M[ {mpoly R[n]} ]_n :=
  \matrix_(i, j < n) 'X_i ^+ (nth 0 s j + (n - 1) - j)%N.
Definition Vandmx : 'M[ {mpoly R[n]} ]_n := \matrix_(i, j < n) 'X_i ^+ (n - 1 - j).
Definition Vandet := \det Vandmx.

Local Open Scope ring_scope.

Lemma Vandmx_antimE : Vandmx = antim [::].
Proof. rewrite /Vandmx /antim -matrixP => i j /=; by rewrite !mxE nth_default. Qed.

Lemma alt_detE s : 'a_(s + rho) = \det (antim s).
Proof.
  rewrite /alternpol (reindex_inj (inv_inj invgK)) /=; apply eq_bigr => p _.
  rewrite odd_permV scaler_sign -mulr_sign; congr (_ * _).
  rewrite (eq_bigr (fun j => 'X_j ^+ (nth 0%N s (p j) + (n - 1) - (p j)))); first last.
    by move => i _; rewrite mxE.
  rewrite msymX mpolyXE_id; apply eq_bigr => i _; congr (_ ^+ _).
  rewrite mnmE /= mnmDE invgK mnmE (mnm_nth 0%N) subn1 addnBA //.
  by rewrite -ltnS (ltn_predK (ltn_ord i)).
Qed.

Corollary Vandet_vdmprodE : Vandet = vdmprod.
Proof.
  rewrite /Vandet Vandmx_antimE.
  suff -> : antim [::] = antim (0%MM : 'X_{1..n}).
    by rewrite -alt_detE add0m vdmprod_alt.
  rewrite /antim -matrixP => i j; by rewrite !mxE nth_nil -mnm_nth mnm0E.
Qed.

End VandermondeDet.
