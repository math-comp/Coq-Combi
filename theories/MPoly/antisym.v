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

Monomials and partitions:

- mpart s == the multi-monomial whose exponent are [s] if [size s] is smaller
           than the number of variables.
- partm m == the partition obtained by sorting the exponent of [m].
- m \is dominant == the exponent of [m] are sorted in reverse order.

Antisymmetric polynomials:

- p \is antisym == p is an antisymmetric polynomial. This is a keyed predicate
           closed by submodule operations [submodPred].

Vandermonde products and determinants:

- alternpol f == the alternating sunm of the permuted of f.
- rho            == the multi-monomial [[n-1, n-2, ..., 1, 0]]
- Vanprod n R == the Vandermonde product in [{mpoly R[n]}], that is the product
                 << \prod_(i < j) ('X_i - 'X_j) >>.

- antim s     == the n x n - matrix whose (i, j) coefficient is
                 << 'X_i^(s j - rho j) >>
- Vanmx       == the Vandermonde matrix << 'X_i^(n - 1 - j) = 'X_i^(rho j) >>.
- Vandet      == the Vandermonde determinant

The main results are the Vandermonde determinant expansion:

- [ Vanprod_alt     : Vanprod = alternpol 'X_[(rho n)] ]
- [ Vandet_VanprodE : Vandet = Vanprod ]

*******************************************************************************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq path choice.
From mathcomp Require Import finset fintype finfun tuple bigop ssralg ssrint.
From mathcomp Require Import fingroup perm zmodp binomial.
From SsrMultinomials Require Import ssrcomplements poset freeg mpoly.

Require Import tools permcomp presentSn sorted partition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import LeqGeqOrder.


Lemma binomial_sumn_iota n : 'C(n, 2) = sumn (iota 0 n).
Proof. by rewrite -triangular_sum sumnE /index_iota subn0. Qed.

Local Notation "''II_' n" := ('I_n * 'I_n)%type (at level 8, n at level 2).

Lemma card_triangle n : #|[set i : 'II_n | i.1 < i.2]| = 'C(n, 2).
Proof.
rewrite -card_ltn_sorted_tuples.
have /card_imset <- : injective (fun i : 'II_n => [tuple i.1; i.2]).
  by move => [i1 i2] [j1 j2] /= [-> ->].
congr (card (mem (pred_of_set _))).
apply/setP => [[[| s0 [| s1 [|s]]]]] // Hs.
rewrite !inE; apply/idP/idP => [/imsetP [[i j]] | /= /andP [Hsort _]].
- by rewrite inE /= andbT => Hij /(congr1 val) /= [-> ->].
- apply/imsetP; exists (s0, s1); first by rewrite inE.
  exact: val_inj.
Qed.

Open Scope nat_scope.

(** ** monomials and partitions *)
Section MonomPart.

Variable n : nat.
Implicit Type m : 'X_{1.. n}.

Definition mpart (s : seq nat) :=
  if size s <= n then [multinom (nth 0 s i)%N | i < n] else mnm0.
Definition dominant : qualifier 0 'X_{1.. n} :=
  [qualify m : 'X_{1.. n} | sorted geq m].

Fact partmP m : is_part (sort geq [seq d <- m | d != 0]).
Proof.
rewrite is_part_sortedE; apply/andP; split.
- exact: sort_sorted.
- by rewrite mem_sort mem_filter eq_refl.
Qed.
Definition partm m := locked (IntPart (partmP m)).
Lemma partmE m : partm m = sort geq [seq d <- m | d != 0] :> seq nat.
Proof. by rewrite /partm; unlock. Qed.

Lemma size_partm m : size (partm m) <= n.
Proof.
rewrite partmE size_sort size_filter -[X in _ <= X](size_tuple m).
exact: count_size.
Qed.

Lemma mpart_is_dominant sh : is_part sh -> mpart sh \is dominant.
Proof.
rewrite /mpart /dominant; case: leqP => [Hsz|_ _].
- rewrite is_part_sortedE => /andP [Hpart _].
  + apply/(sortedP 0) => // i j; rewrite size_tuple => /andP [Hij Hj].
    have Hi := leq_ltn_trans Hij Hj.
    rewrite -[i]/(val (Ordinal Hi)) -[j]/(val (Ordinal Hj)) -!mnm_nth !mnmE /=.
    case: (ssrnat.ltnP j (size sh)) => [Hjsz | /(nth_default _) -> //].
    by apply: (sortedP _ _ _ _ Hpart) => //; rewrite Hij Hjsz.
- apply/(sortedP 0) => // i j; rewrite size_tuple => /andP [Hij Hj] /=.
  by rewrite (nth_map (Ordinal Hj)) // -cardE card_ord.
Qed.

Lemma is_dominant_partm m :
  m \is dominant -> partm m = [seq d <- m | d != 0] :> seq nat.
Proof.
rewrite unfold_in partmE => Hsort.
apply: (eq_sorted (leT := geq)) => //.
- exact: sort_sorted.
- exact: sorted_filter.
- by rewrite perm_sort.
Qed.

Lemma is_dominant_nth_partm m (i : 'I_n) :
  m \is dominant -> nth 0 (partm m) i = m i.
Proof.
move=> Hdom; rewrite (is_dominant_partm Hdom).
case: m Hdom => [[s Hs /=]].
rewrite unfold_in (mnm_nth 0) /=.
case: i => [i /= _] {Hs}; elim: s i => [| s0 s IHs] i // Hsort /=.
case: (altP (s0 =P 0)) Hsort => [->{s0} /= {IHs} Hpath|_].
- have -> : s = nseq (size s) 0.
    elim: s Hpath => [//= | s0 s IHs] /= /andP [].
    by rewrite leqn0 => /eqP -> /IHs {1}->.
  rewrite (eq_in_filter (a2 := pred0)) ?filter_pred0; first last.
    by move=> x /nseqP [-> _].
  by case: i => //= i; rewrite nth_nseq if_same.
- move=> /sorted_consK/IHs {IHs} /= Hrec.
  by case: i.
Qed.

Lemma partmK m : m \is dominant -> mpart (partm m) = m.
Proof.
move=> Hdom; rewrite /mpart size_partm.
by apply/mnmP => i; rewrite mnmE is_dominant_nth_partm.
Qed.

Lemma mpartK sh :
  is_part sh -> size sh <= n -> partm (mpart sh) = sh :> seq nat.
Proof.
move=> Hpart Hsize; apply/eqP/part_eqP => // i.
case: (ssrnat.ltnP i n) => Hi.
- have /is_dominant_nth_partm Hdom := mpart_is_dominant Hpart.
  have:= Hdom (Ordinal Hi) => /= ->.
  by rewrite /mpart Hsize mnmE /=.
- rewrite !nth_default //; apply: leq_trans _ Hi => //.
  exact: size_partm.
Qed.

Lemma perm_eq_partm m1 m2 : perm_eq m1 m2 -> partm m1 = partm m2.
Proof.
move=> Hperm; apply val_inj; rewrite /= !partmE; apply/perm_sortP => //.
exact: perm_eq_filter.
Qed.

Lemma partm_perm_eqK m : perm_eq m (mpart (partm m)).
Proof.
have Hsm : size (sort geq m) == n by rewrite size_sort size_tuple.
pose sm := [multinom Tuple Hsm].
have Hperm : perm_eq sm m by rewrite /= perm_sort.
rewrite -(perm_eq_partm Hperm) partmK; first last.
  by rewrite unfold_in; apply: sort_sorted.
by rewrite perm_eq_sym.
Qed.

Lemma sumn_partm m : sumn (partm m) = mdeg m.
Proof.
rewrite -sumnE.
wlog: m / m \is dominant.
  move=> Hdom; have Hperm := partm_perm_eqK m.
  rewrite /mdeg (eq_big_perm _ Hperm) /= -/(mdeg _).
  have /Hdom <- := mpart_is_dominant (intpartP (partm m)).
  by rewrite mpartK // size_partm.
move/is_dominant_partm ->.
symmetry; rewrite big_filter /mdeg.
by rewrite (bigID (fun i => i == 0)) /= big1 ?add0n // => i /eqP.
Qed.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").


Lemma mnm_perm_eq m1 m2 : perm_eq m1 m2 -> {s : 'S_n | m1 == m2 # s}.
Proof.
move=> Hperm; apply sigW; move: Hperm => /tuple_perm_eqP [s /val_inj Hs] /=.
by exists s; apply/eqP; apply val_inj => /=.
Qed.

Lemma perm_mpart_partm m : {s : 'S_n | (mpart (partm m)) # s == m}.
Proof.
apply sigW; have [/= s /eqP {2}->] := mnm_perm_eq (partm_perm_eqK m).
by exists s.
Qed.

Lemma mpart_partm_perm m : {s : 'S_n | (mpart (partm m)) == m # s}.
Proof.
have [/= s /eqP {2}<-]:= perm_mpart_partm m.
exists (s^-1)%g; apply/eqP/mnmP => i.
by rewrite 2!mnmE permKV.
Qed.

End MonomPart.

Arguments mpart [n] s.
Arguments dominant [n].


Import GRing.Theory.
Local Open Scope ring_scope.
Local Definition simplexp := (expr0, expr1, scale1r, scaleN1r,
                              mulrN, mulNr, mulrNN, opprK).

(** ** Change of scalar in multivariate polynomials *)
Section ScalarChange.

Variables R S : ringType.
Variable mor : {rmorphism R -> S}.
Variable n : nat.

Lemma map_mpolyX (m : 'X_{1..n}) : map_mpoly mor 'X_[m] = 'X_[m].
Proof using.
by rewrite /= /map_mpoly mmapX /= /mmap1 mprodXnE -multinomUE_id.
Qed.

Lemma msym_map_mpoly s (p : {mpoly R[n]}) :
  msym s (map_mpoly mor p) = map_mpoly mor (msym s p).
Proof using.
rewrite (mpolyE p).
rewrite [map_mpoly _ _]raddf_sum [msym s _]raddf_sum.
rewrite [msym s _]raddf_sum [map_mpoly _ _]raddf_sum.
apply eq_bigr => i _ /=; apply/mpolyP => m.
by rewrite mcoeff_map_mpoly /= !mcoeff_sym mcoeff_map_mpoly.
Qed.

End ScalarChange.


(** ** Characteristic of multivariate polynomials *)

Lemma char_mpoly n (R : ringType) : [char R] =i [char {mpoly R[n]}].
Proof using.
move=> p; rewrite !unfold_in /= -mpolyC_nat.
case: (prime.prime p) => //=.
apply/eqP/eqP => [-> //|].
rewrite -(mpolyP) => /(_ 0%MM).
by rewrite mcoeff0 raddfMn /= mcoeffMn mcoeff1 eq_refl /= => ->.
Qed.


(** * Symmetric and Antisymmetric multivariate polynomials *)
Section MPolySym.

Variable n : nat.
Variable R : ringType.

Implicit Types p q r : {mpoly R[n]}.

Lemma issym_tpermP p :
  reflect (forall i j, msym (tperm i j) p = p) (p \is symmetric).
Proof using.
apply/(iffP forallP) => /= [Hsym i j | Htperm s].
- by rewrite (eqP (Hsym (tperm _ _))).
- case: (prod_tpermP s) => ts -> {s} Hall.
  elim: ts Hall => [_ | t0 ts IHts] /=.
    by rewrite !big_nil /= msym1m.
  move=> /andP [_ /IHts{IHts}/eqP Hrec].
  by rewrite !big_cons msymMm Htperm Hrec.
Qed.

Definition antisym : qualifier 0 {mpoly R[n]} :=
  [qualify p | [forall s, msym s p == (-1) ^+ s *: p]].

Fact antisym_key : pred_key antisym. Proof using. by []. Qed.
Canonical antisym_keyed := KeyedQualifier antisym_key.

Lemma isantisymP p :
  reflect (forall s, msym s p = (-1) ^+ s *: p) (p \is antisym).
Proof using. by apply/(iffP forallP) => /= H s; apply/eqP/H. Qed.

Lemma isantisym_tpermP p :
  reflect (forall i j, msym (tperm i j) p = if (i != j) then - p else p)
          (p \is antisym).
Proof using.
apply/(iffP forallP) => /= [Hanti i j | Htperm s].
- rewrite (eqP (Hanti (tperm _ _))) odd_tperm.
  by case: (i != j); rewrite !simplexp.
- case: (prod_tpermP s) => ts -> {s} Hall.
  elim: ts Hall => [_ | t0 ts IHts] /=.
    by rewrite !big_nil odd_perm1 /= msym1m expr0 scale1r.
  move=> /andP [H0 /IHts{IHts}/eqP Hrec].
  rewrite !big_cons msymMm Htperm H0 msymN Hrec.
  rewrite odd_mul_tperm H0 /=.
  by case: (odd_perm _); rewrite !simplexp.
Qed.

Lemma antisym_char2 : (2 \in [char R]) -> symmetric =i antisym.
Proof using.
move=> Hchar p /=; apply/issymP/isantisymP => H s;
  by rewrite H oppr_char2; first rewrite expr1n scale1r.
Qed.

Lemma perm_smalln : n <= 1 -> forall s : 'S_n, s = 1%g.
Proof using.
by case: n => [|[|//]] _ s; [rewrite (permS0 s) | rewrite (permS1 s)].
Qed.

Lemma sym_smalln : n <= 1 -> (@symmetric n R) =i predT.
Proof using.
move=> Hn p /=; rewrite [RHS]unfold_in /=.
apply/issymP => s.
by rewrite (perm_smalln Hn s) msym1m.
Qed.

Lemma antisym_smalln : n <= 1 -> antisym =i predT.
Proof using.
move=> Hn p /=; rewrite [RHS]unfold_in /=.
apply/isantisymP => s.
by rewrite (perm_smalln Hn s) odd_perm1 msym1m expr0 scale1r.
Qed.

Lemma antisym_zmod : zmod_closed antisym.
Proof using.
split=> [|p q /isantisymP sp /isantisymP sq]; apply/isantisymP=> s.
  by rewrite msym0 scaler0.
by rewrite msymB sp sq scalerBr.
Qed.

Canonical antisym_opprPred := OpprPred antisym_zmod.
Canonical antisym_addrPred := AddrPred antisym_zmod.
Canonical antisym_zmodPred := ZmodPred antisym_zmod.


Lemma antisym_submod_closed : submod_closed antisym.
Proof using.
split=> [|c p q /isantisymP sp /isantisymP sq]; apply/isantisymP=> s.
  by rewrite msym0 scaler0.
rewrite msymD msymZ sp sq.
by rewrite scalerA commr_sign -scalerA scalerDr.
Qed.

Canonical antisym_submodPred := SubmodPred antisym_submod_closed.

Lemma sym_anti p q :
  p \is antisym -> q \is symmetric -> p * q \is antisym.
Proof using.
move=> /isantisymP Hsym /issymP Hanti.
apply/isantisymP => s.
rewrite msymM Hsym Hanti.
by case: (odd_perm _); rewrite !simplexp.
Qed.

Lemma anti_anti p q :
  p \is antisym -> q \is antisym -> p * q \is symmetric.
Proof using.
move=> /isantisymP Hp /isantisymP Hq.
apply/issymP => s; rewrite msymM Hp Hq.
by case: (odd_perm _); rewrite !simplexp.
Qed.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Lemma isantisym_msupp p (s : 'S_n) (m : 'X_{1..n}) : p \is antisym ->
  (m#s \in msupp p) = (m \in msupp p).
Proof using.
rewrite !mcoeff_msupp -mcoeff_sym => /isantisymP ->.
case: (odd_perm s); last by rewrite expr0 scale1r.
rewrite expr1 scaleN1r !mcoeff_eq0.
by rewrite (perm_eq_mem (msuppN _)).
Qed.


Lemma mlead_antisym_sorted (p : {mpoly R[n]}) : p \is antisym ->
  forall (i j : 'I_n), i <= j -> (mlead p) j <= (mlead p) i.
Proof using.
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
apply/(iffP forallP) => [Hanti i Hi | Heltr].
- by have /eqP -> := Hanti (eltr n i).
- elim/eltr_ind => [| S i Hi /eqP IH].
  + by rewrite msym1m.
  + by rewrite msymMm (Heltr i Hi) IH.
Qed.

Lemma isantisym_eltrP n (R : ringType) (p : {mpoly R[n.+1]}) :
  reflect (forall i, i < n -> msym (eltr n i) p = - p) (p \is antisym).
Proof.
apply/(iffP forallP) => [Hanti i Hi | Heltr].
- have /eqP -> := Hanti (eltr n i).
  by rewrite /eltr odd_tperm (inordi1 Hi) !simplexp.
- elim/eltr_ind => [| S i Hi /eqP IH].
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


Lemma sym_antisym_char_not2 :
  n >= 2 -> forall p : {mpoly R[n]}, p \is symmetric -> p \is antisym -> p = 0.
Proof using Hchar.
move=>  Hn p /= /issymP Hsym /isantisymP Hanti.
move: Hchar; rewrite (char_mpoly n R) => Hchp.
pose s := tperm (Ordinal (ltnW Hn)) (Ordinal Hn).
have:= Hanti s; rewrite Hsym.
rewrite odd_tperm /= => /eqP; rewrite !simplexp -addr_eq0.
rewrite -mulr2n -mulr_natr mulf_eq0 => /orP [/eqP -> //|] /= /eqP /= H2.
by exfalso; move: Hchp; rewrite negb_and H2 eq_refl.
Qed.


Section Lead.

Variable p : {mpoly R[n]}.

Implicit Types q r : {mpoly R[n]}.

Hypothesis Hpn0 : p != 0.
Hypothesis Hpanti : p \is antisym.

Lemma sym_antiE q : (q \is symmetric) = (p * q \is antisym).
Proof using Hpanti Hpn0.
case: (leqP n 1) => Hn; first by rewrite !(sym_smalln Hn) !(antisym_smalln Hn).
apply/idP/idP; first exact: sym_anti Hpanti.
move: Hpanti => /isantisymP Hsym /isantisymP Hpq.
apply/issymP => s.
have:= Hpq s; rewrite msymM Hsym => H; apply (mulfI Hpn0).
move: H; case: (odd_perm s); rewrite !simplexp //.
by move/oppr_inj.
Qed.


Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

Lemma isantisym_msupp_uniq (m : 'X_{1..n}) : m \in msupp p -> uniq m.
Proof using Hchar Hpanti.
rewrite mcoeff_msupp => Hsupp.
case: (boolP (uniq m)) => // /(notuniq_witnessP 0%N).
move=> [i] [j] []; rewrite size_tuple => /andP [Hi Hj] Hnth.
move/isantisymP/(_ (tperm (Ordinal (ltn_trans Hi Hj)) (Ordinal Hj))) : Hpanti.
rewrite odd_tperm /eq_op /=.
rewrite (ltn_eqF Hi) expr1 scaleN1r.
move/(congr1 (mcoeff m)); rewrite mcoeffN mcoeff_sym.
have -> : m#tperm (Ordinal (ltn_trans Hi Hj)) (Ordinal Hj) = m.
  rewrite mnmP => k; rewrite mnmE.
  by case: (tpermP _ _ k) => [-> | -> |] //; rewrite !(mnm_nth 0) /= Hnth.
move/eqP; rewrite -addr_eq0.
rewrite -mulr2n -mulr_natr mulf_eq0.
move: Hchar; rewrite negb_and => /negbTE ->.
by move: Hsupp => /negbTE ->.
Qed.

Hypothesis Hphomog : p \is 'C(n , 2).-homog.

Lemma isantisym_mlead_iota : mlead p = rev (iota 0 n) :> seq nat.
Proof using Hchar Hpanti Hphomog Hpn0.
move: Hphomog; rewrite binomial_sumn_iota => /dhomogP Hhomog.
have Huniq := isantisym_msupp_uniq (mlead_supp Hpn0).
rewrite -(revK (mlead p)) -{4}(size_tuple (mlead p)) -size_rev; congr rev.
apply sorted_sumn_iotaE; first last.
  rewrite size_rev size_tuple sumn_rev -sumnE -/(mdeg _).
  by rewrite (Hhomog _ (mlead_supp Hpn0)).
rewrite ltn_sorted_uniq_leq rev_uniq Huniq /=.
rewrite {Huniq Hhomog} rev_sorted.
apply/(sortedP 0%N) => // i j; rewrite size_tuple=> /andP [Hij Hj].
have H := mlead_antisym_sorted Hpanti.
have /= := H (Ordinal (leq_ltn_trans Hij Hj)) (Ordinal Hj) Hij.
by rewrite !(mnm_nth 0) /=; apply.
Qed.

Definition rho := [multinom (n - 1 - i)%N | i < n].

Local Notation "''a_' k" := (@alternpol n R 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").

Lemma rho_iota : rho = rev (iota 0 n) :> seq nat.
Proof using.
apply (eq_from_nth (x0 := 0%N)).
  by rewrite size_rev size_iota size_map size_enum_ord.
move=> i; rewrite size_map size_enum_ord => Hi.
rewrite nth_rev size_iota // (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
rewrite nth_enum_ord // nth_iota; first last.
  by case: n Hi => [// | m] _; rewrite ltnS subSS; apply: leq_subr.
by rewrite add0n; case: n Hi => [// | m] _; rewrite !subSS subn0.
Qed.

Lemma mdeg_rho : mdeg rho = 'C(n, 2).
Proof.
rewrite /mdeg binomial_sumn_iota -sumnE.
by apply eq_big_perm; rewrite rho_iota perm_eq_sym; apply: perm_eq_rev.
Qed.

Lemma alt_homog : 'a_(rho) \is 'C(n, 2).-homog.
Proof using.
apply rpred_sum => s _; rewrite rpredZsign msymX dhomogX /=.
have -> : mdeg (rho#(s^-1)%g) = mdeg rho.
  by rewrite /mdeg; apply/eq_big_perm/tuple_perm_eqP; exists (s^-1)%g.
by rewrite mdeg_rho.
Qed.

Lemma alt_anti m : 'a_m \is antisym.
Proof using.
apply/isantisymP => S.
rewrite /alternpol (big_morph (msym S) (@msymD _ _ _) (@msym0 _ _ _)).
rewrite scaler_sumr.
rewrite [RHS](reindex_inj (mulIg S)); apply: eq_big => //= s _.
rewrite msymZ -msymMm scalerA; congr (_ *: _).
by rewrite odd_permM signr_addb [X in (_  = _ * X)]mulrC signrMK.
Qed.

Lemma isantisym_mlead_rho : mlead p = rho.
Proof using Hchar Hpanti Hphomog Hpn0.
by apply/val_inj/val_inj; rewrite /= isantisym_mlead_iota rho_iota.
Qed.

End Lead.

Local Notation "''a_' k" := (alternpol 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").


Lemma isantisym_alt (p : {mpoly R[n]}) :
  p != 0 -> p \is antisym -> p \is ('C(n, 2)).-homog -> p = p@_(rho) *: 'a_rho.
Proof using Hchar.
move=> Hpn0 Hanti Hhom.
apply/eqP; rewrite -subr_eq0; apply contraT => Habs.
have /(isantisym_mlead_rho Habs) H : p - p@_(rho) *: 'a_(rho) \is antisym.
  by apply/(rpredD Hanti)/rpredNr/rpredZ/alt_anti.
move: Habs => /mlead_supp.
have /H{H} ->: p - p@_(rho) *: 'a_(rho) \is ('C(n, 2)).-homog.
  by apply/(rpredD Hhom)/rpredNr/rpredZ/alt_homog.
rewrite mcoeff_msupp linearB /= linearZ linear_sum /=.
rewrite (bigID (xpred1 1%g)) /= big_pred1_eq.
rewrite odd_perm1 /= expr0 scale1r msym1m mcoeffX eq_refl /=.
rewrite big1; first by rewrite addr0 mulr1 subrr eq_refl.
move=> s Hs; apply /eqP; move: Hs; apply contraR.
rewrite linearZ /= msymX mcoeffX.
case: (altP ( _ =P rho)); last by rewrite mulr0 eq_refl.
rewrite mnmP => H _; rewrite -eq_invg1; apply/eqP.
rewrite -permP => i; rewrite perm1.
move/(_ i) : H => /=.
rewrite /rho !mnm_tnth !tnth_mktuple !mnm_tnth !tnth_mktuple !subn1 => H.
rewrite -[LHS]rev_ordK -[RHS]rev_ordK; congr rev_ord.
apply val_inj => /=; rewrite !subnS.
by have:= ltn_ord i => /ltn_predK {1 5}<-; rewrite !subSKn.
Qed.

End AlternIDomain.

(** ** Vandermonde product *)
Definition Vanprod {n} {R : ringType} : {mpoly R[n]} :=
  \prod_(p : 'II_n | p.1 < p.2) ('X_p.1 - 'X_p.2).


Section EltrP.

Variable n i : nat.
Implicit Type (p : 'II_n.+1).

Local Definition eltrp p := (eltr n i p.1, eltr n i p.2).
Local Definition predi p := (p.1 < p.2) && (p != (inord i, inord i.+1)).

Lemma predi_eltrp p : i < n -> predi p -> predi (eltrp p).
Proof using.
move=> Hi.
have Hii1 : val (@inord n i.+1) = (@inord n i).+1.
  by do 2 (rewrite /= inordK; last by apply (leq_trans Hi)).
move: p => [u v] /=; rewrite /predi /= /eltrp /eltr => /andP [Hlt Hneq] /=.
case: (altP (inord i =P u)) => Hu.
  subst u; rewrite tpermL.
  case: (altP (v =P inord i.+1)) Hneq Hlt => [Hu | Hu _ Hlt].
    by subst v; rewrite /= eq_refl.
  rewrite tpermD; [| by rewrite neq_ltn Hlt | by rewrite eq_sym].
  apply/andP; split.
  - by rewrite ltn_neqAle eq_sym Hu /= Hii1.
  - rewrite /eq_op /= eq_sym; apply/nandP; left.
    by rewrite /eq_op /= Hii1 ieqi1F.
case: (altP (inord i.+1 =P u)) => Hu1.
  subst u; rewrite tpermR /=.
  rewrite tpermD; first last.
  - move: Hlt; by rewrite ltn_neqAle => /andP [].
  - move: Hlt; rewrite Hii1 => /ltnW.
    by rewrite ltn_neqAle => /andP [].
  apply/andP; split.
  - by apply: (ltn_trans _ Hlt); rewrite Hii1.
  - rewrite /eq_op /= eq_refl /= eq_sym.
    by move: Hlt; rewrite ltn_neqAle => /andP [].
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
Proof using.
move=> Hi; apply/idP/idP; first exact: predi_eltrp.
set p1 := ( _, _).
suff -> : p = ((eltr n i) p1.1, (eltr n i) p1.2) by apply predi_eltrp.
rewrite /p1 /= !tpermK {p1}.
by case: p.
Qed.

End EltrP.

Lemma Vanprod_anti n (R : comRingType) : @Vanprod n R \is antisym.
Proof.
case: n => [| n].
  by apply/isantisymP => s; rewrite (permS0 s) msym1m odd_perm1 simplexp.
apply/isantisym_eltrP => i Hi.
rewrite /Vanprod.
rewrite (bigD1 (inord i, inord i.+1)) /=; first last.
  by rewrite !inordK //=; apply (leq_trans Hi).
rewrite msymM -mulNr; congr (_ * _).
  rewrite msymB opprB; congr (_ - _);
  by rewrite /msym mmapX mmap1U /eltr ?tpermL ?tpermR.
rewrite (big_morph _ (msymM (eltr n i)) (msym1 _ (eltr n i))) /=.
rewrite (eq_bigl (fun p : 'II_n.+1 => predi i (eltrp i p))); first last.
  by move=> [u v]; rewrite -/(predi i (u,v)) (predi_eltrpE (u, v) Hi) /=.
rewrite (eq_bigr (fun p => 'X_(eltrp i p).1 - 'X_(eltrp i p).2)); first last.
  by move => [u v] _; rewrite msymB /msym !mmapX !mmap1U.
rewrite -(big_map _ _ (fun p => ('X_p.1 - 'X_p.2))) /=.
rewrite /index_enum -enumT /=.
apply eq_big_perm.
have Hin : map (eltrp i) (enum {: 'II_ n.+1}) =i enum {: 'II_ n.+1}.
  move=> [u v].
  rewrite mem_enum inE.
  have -> : (u, v) = eltrp i (eltrp i (u, v)) by rewrite /eltrp /= !tpermK.
  by apply map_f; rewrite mem_enum inE.
apply: (uniq_perm_eq _ _ Hin).
- by rewrite (perm_uniq Hin) ?size_map // enum_uniq.
- exact: enum_uniq.
Qed.

Lemma sym_VanprodM n (R : comRingType) (p : {mpoly R[n]}) :
  p \is symmetric -> Vanprod * p \is antisym.
Proof. by apply sym_anti; apply Vanprod_anti. Qed.


Section Vanprod.

Variable n : nat.
Variable R : comRingType.

Local Notation Delta := (@Vanprod n R).
Local Notation "'X_ i" := (@mpolyX n R U_(i)). (* Enforce the base ring *)

Lemma polyX_inj (i j : 'I_n) : 'X_i = 'X_j -> i = j.
Proof using.
move/(congr1 (mcoeff U_(j))); rewrite !mcoeffX eq_refl /=.
case: (altP (_ =P _)) => [H _ | _ /esym /= /eqP] /=.
- have:= congr1 (fun x : 'X_{1..n} => x j) H.
  by rewrite !mnm1E eq_refl eq_sym; case: eqP.
- by have:= oner_neq0 R => /negbTE ->.
Qed.

Lemma diffX_neq0 (i j : 'I_n) : i != j -> 'X_i - 'X_j != 0.
Proof using. by apply contra; rewrite subr_eq0 => /eqP /polyX_inj ->. Qed.

Lemma msuppX1 i : msupp 'X_i = [:: U_(i)%MM].
Proof using. rewrite msuppE /= unlock /= domU //; exact: oner_neq0. Qed.

Local Notation "''a_' k" := (alternpol 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").
Local Notation rho := (rho n).
Let abound b  : {mpoly R[n]} :=
  \prod_(p : 'II_n | p.1 < p.2 <= b) ('X_p.1 - 'X_p.2).
Let rbound b := [multinom (b - i)%N | i < n].

Lemma mesymlm_rbound b : (mesymlm n b <= rbound b)%MM.
Proof using.
apply/mnm_lepP => i; rewrite !mnmE inE.
case (ssrnat.ltnP i b) => [/= Hb| //].
by rewrite subn_gt0.
Qed.

Lemma coeffXdiff (b : 'I_n) (k : 'X_{1..n}) (i : 'I_n) :
  (k <= rbound b)%MM -> ('X_i - 'X_b)@_k = (k == U_(i)%MM)%:R.
Proof using.
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
Proof using.
case: b => b /=.
elim: {1 5 7}b (leqnn b) k => [| c IHc] Hc k Hb Hk.
  rewrite big1 //.
  suff -> : mesymlm n 0 = 0%MM by rewrite mcoeff1.
  by rewrite mnmP => i; rewrite !mnmE /mesymlmnm inE ltn0.
set ordb := Ordinal Hb.
move/(_ (ltnW Hc)) : IHc => Hrec.
have Hcn := ltn_trans Hc Hb.
pose ordc := Ordinal Hcn.
rewrite (bigID (xpred1 ordc)) /=.
rewrite (eq_bigl (xpred1 ordc)); first last.
  move=> i /=; case: eqP => [->|]; last by rewrite andbF.
  by rewrite /= ltnSn.
rewrite (eq_bigl (fun i : 'I_n => i < c)); first last.
  by move=> i /=; rewrite ltnS ltn_neqAle [RHS]andbC.
rewrite big_pred1_eq.
rewrite (mcoeff_poly_mul_lin _ _ (k := (mdeg k).+2)) //.
case: (boolP (U_(ordc) <= k)%MM) => Hck.
- have ordc_bound : mdeg (U_(ordc))%MM < (mdeg k).+2 by rewrite mdeg1.
  pose mc := BMultinom ordc_bound; rewrite (bigID (xpred1 mc)) /=.
  rewrite (eq_bigl (xpred1 mc)); first last.
    move=> m /=; case eqP => [->|]; last by rewrite andbF.
    by rewrite /= Hck.
  rewrite big_pred1_eq /= coeffXdiff; last exact: lepm_trans Hck Hk.
  rewrite eq_refl mul1r {}Hrec; first last.
    apply: (lepm_trans _ Hk); apply/mnm_lepP => i.
    rewrite mnmBE; exact: leq_subr.
  rewrite big1 ?addr0; first last.
    move=> m /andP [Hmk Hmc1].
    rewrite coeffXdiff; last exact: lepm_trans Hmk Hk.
    move: Hmc1; rewrite {1}/eq_op /= => /= /negbTE /= ->; by rewrite mul0r.
    rewrite -{2}(submK Hck).
    have -> : mesymlm n c.+1 = (mesymlm n c + U_(ordc))%MM.
      rewrite mnmP => i; rewrite !mnmE !inE ltnS leq_eqVlt.
      rewrite orbC eq_sym {2}/eq_op/=.
      case: eqP => [->|_]; first by rewrite ltnn.
      by rewrite orbF addn0.
    congr (nat_of_bool _)%:R; apply/eqP/eqP => [ <- // | Heq].
    by rewrite -[RHS](addmK (U_(ordc))%MM) -[LHS](addmK (U_(ordc))%MM) Heq.
- rewrite big1; first last.
    move=> m /= Hm; rewrite coeffXdiff; last exact: lepm_trans Hm Hk.
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
Proof using.
elim: b => [Hb | b IHb Hb1].
  rewrite /abound {Hb} big1; first last.
    by move=> [i j] /= /andP [/leq_trans H/H{H}].
  rewrite mcoeff1 /=.
  suff -> : rbound 0 = 0%MM by rewrite eq_refl.
  by rewrite mnmP => i; rewrite mnmE.
move/(_ (ltnW Hb1)): IHb => Hrec.
rewrite /abound (bigID (fun p : 'II_n => p.2 <= b)) /=.
rewrite (eq_bigl (fun p : 'II_n => p.1 < p.2 <= b)); first last.
  move=> [i j]/=; case: (leqP j b); last by rewrite !andbF.
  by rewrite -ltnS => /ltnW ->; rewrite !andbT.
rewrite mulrC -/(abound _).
pose ordb1 := Ordinal Hb1.
rewrite [X in X * _](_ : _ =
           \prod_(i : 'I_n | i <= b)  ('X_i - 'X_ordb1)); first last.
  rewrite (eq_bigl (fun p : 'II_n => (p.1 <= b) && (p.2 == ordb1))); first last.
    move=> [i j]/=; rewrite -ltnNge -andbA -eqn_leq.
    case: eqP => Hj.
    - have -> : j = ordb1 by apply val_inj.
      by rewrite eq_refl /= ltnS.
    - suff -> : (j == ordb1) = false by rewrite !andbF.
      by apply negbTE; move: Hj => /eqP; apply contra => /eqP ->.
  rewrite (reindex (fun i : 'I_n => (i, ordb1))) /=; first last.
    exists (fun p : 'II_n => p.1) => //.
    by move=> [i j] /=; rewrite inE /= => /andP [_ /eqP <-].
  by apply eq_bigl => i; rewrite eq_refl andbT.
rewrite (mcoeff_poly_mul_lin _ _ (k := (mdeg (rbound b.+1)).+1)) //.
have /= := @coeff_prodXdiff ordb1.
rewrite (eq_bigl (fun i : 'I_(_) => i <= b)); last by move=> i; rewrite ltnS.
move=> Hprod.
have Hmesymlm : mdeg (mesymlm n b.+1) < (mdeg (rbound b.+1)).+1.
  rewrite ltnS /mdeg !big_tuple; apply leq_sum => i _.
  by rewrite -!mnm_tnth; move: (mesymlm_rbound b.+1) => /mnm_lepP; apply.
pose msmb := BMultinom Hmesymlm.
rewrite (bigID (xpred1 msmb)) /=.
rewrite (eq_bigl (xpred1 msmb)); first last.
  move=> m /=; case: eqP => [->|]; last by rewrite andbF.
  by rewrite /= mesymlm_rbound.
rewrite big_pred1_eq /= {}Hprod ?mesymlm_rbound // eq_refl mul1r.
rewrite big1 ?addr0; first last.
  move=> m /andP [Hm Hneq].
  rewrite (eq_bigl (fun i : 'I_(_) => i < b.+1)); first last.
    by move=> i; rewrite ltnS.
  rewrite (@coeff_prodXdiff ordb1) //.
  by move: Hneq; rewrite {1}/eq_op/= => /negbTE -> /=; rewrite mul0r.
rewrite -Hrec; congr mcoeff.
rewrite mnmP => i; rewrite !mnmE inE ltnS.
case: leqP => /= Hi.
- by rewrite subnAC subSS subn0.
- by rewrite subn0; move: Hi (ltnW Hi); rewrite /leq => /eqP -> /eqP ->.
Qed.

Lemma Vanprod_coeff_rho : Delta @_ rho = 1.
Proof using.
rewrite /Vanprod.
case: (altP (n =P 0%N)) => [Hn |].
- rewrite big1; last by move=> [[i Hi]]; exfalso; rewrite Hn in Hi.
  suff -> : rho = 0%MM by rewrite mcoeff1 eq_refl.
  by rewrite mnmP => [[i Hi]]; exfalso; rewrite Hn in Hi.
- rewrite -lt0n => /prednK/eqP; rewrite eqn_leq => /andP [].
  move=> /mcoeff_arbound <- _.
  rewrite /rho subn1; congr mcoeff.
  apply eq_bigl => [[i j]] /=.
  case: n i j => [//=| n'] i j /=; first by exfalso; have:= ltn_ord i.
  by rewrite -(ltnS j) ltn_ord andbT.
Qed.

Corollary Vanprod_neq0 : Delta != 0.
Proof using.
apply/negP => /eqP H.
have:= Vanprod_coeff_rho; rewrite {}H mcoeff0 => /esym/eqP.
by rewrite oner_eq0.
Qed.

Lemma Vanprod_dhomog : Delta \is 'C(n, 2).-homog.
Proof using.
have /homogP [d Hd] : Delta \is homog [measure of mdeg].
  rewrite /Vanprod -big_filter -(big_map _ xpredT id).
  apply homog_prod; apply/allP => X /mapP [[i j]] /= _ -> {X}.
  by apply/homogP; exists 1%N; apply rpredB; rewrite dhomogX /= mdeg1.
suff <- : d = 'C(n, 2) by [].
have Hr : rho \in msupp Delta.
  by rewrite mcoeff_msupp Vanprod_coeff_rho oner_neq0.
move: Hd => /dhomogP/(_ _ Hr) /= <-.
exact: mdeg_rho.
Qed.

End Vanprod.

Theorem Vanprod_alt_int n :
  Vanprod = alternpol 'X_[(rho n)] :> {mpoly int[n]}.
Proof.
rewrite (isantisym_alt _
          (Vanprod_neq0 n _) (Vanprod_anti _ _) (Vanprod_dhomog n _)).
- by rewrite Vanprod_coeff_rho scale1r.
- by apply/negP => /=; rewrite inE /= eqz_nat.
Qed.

Corollary Vanprod_alt n (R : ringType) :
  Vanprod = alternpol 'X_[(rho n)] :> {mpoly R[n]}.
Proof.
have := Vanprod_alt_int n => /(congr1 (map_mpoly (S := R) intr)).
rewrite /Vanprod raddf_sum rmorph_prod.
rewrite (eq_bigr (fun i => 'X_i.1 - 'X_i.2)); first last.
  by move=> [i j] _ /=; rewrite raddfB /= !map_mpolyX.
by move ->; apply eq_bigr => s _; rewrite raddfZsign !msymX /= map_mpolyX.
Qed.

From mathcomp Require Import matrix.


(** ** Vandermonde matrix and determinant *)
Section VandermondeDet.

Variable n : nat.
Variable R : comRingType.

Local Notation "''a_' k" := (alternpol 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").
Local Notation rho := (rho n).

Definition antim (s : seq nat) : 'M[ {mpoly R[n]} ]_n :=
  \matrix_(i, j < n) 'X_i ^+ (nth 0 s j + (n - 1) - j)%N.
Definition Vanmx : 'M[ {mpoly R[n]} ]_n :=
  \matrix_(i, j < n) 'X_i ^+ (n - 1 - j).
Definition Vandet := \det Vanmx.

Local Open Scope ring_scope.

Lemma Vanmx_antimE : Vanmx = antim [::].
Proof using. by apply/matrixP => i j /=; rewrite !mxE nth_default. Qed.

Lemma alt_detE s : 'a_(s + rho) = \det (antim s).
Proof using.
rewrite /alternpol (reindex_inj (inv_inj invgK)) /=; apply eq_bigr => p _.
rewrite odd_permV scaler_sign -mulr_sign; congr (_ * _).
transitivity
  (\prod_(i < n)
    'X_i ^+ (nth 0%N s (p i) + (n - 1) - p i) : {mpoly R[n]}); first last.
  by apply eq_bigr => i _; rewrite mxE.
rewrite msymX mpolyXE_id; apply eq_bigr => i _; congr (_ ^+ _).
rewrite mnmE /= mnmDE invgK mnmE (mnm_nth 0%N) subn1 addnBA //.
by rewrite -ltnS (ltn_predK (ltn_ord i)).
Qed.

Corollary Vandet_VanprodE : Vandet = Vanprod.
Proof using.
rewrite /Vandet Vanmx_antimE.
suff -> : antim [::] = antim (0%MM : 'X_{1..n}).
  by rewrite -alt_detE add0m Vanprod_alt.
by apply/matrixP => i j; rewrite !mxE nth_nil -mnm_nth mnm0E.
Qed.

End VandermondeDet.
