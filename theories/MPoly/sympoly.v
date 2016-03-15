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
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple finfun finset bigop ssralg path perm fingroup.
From SsrMultinomials Require Import ssrcomplements poset freeg bigenough mpoly.

From Combi Require Import tools ordtype partition Yamanouchi std tableau stdtab.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.


Section Bases.

Variable n0 : nat.
Local Notation n := (n0.+1).
Variable R : comRingType.

Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s").

(* From  mpoly.v : \sum_(h : {set 'I_n} | #|h| == k) \prod_(i in h) 'X_i. *)
Definition monomial d (sh : intpartn d) : {mpoly R[n]} :=
  \sum_(m : 'X_{1..n < d.+1} | sort leq m == sh :> seq nat) 'X_[m].
Definition elementary (k : nat) : {mpoly R[n]} := mesym n R k.
Definition complete (d : nat) : {mpoly R[n]} :=
  \sum_(m : 'X_{1..n < d.+1} | mdeg m == d) 'X_[m].
Definition power_sum (d : nat) : {mpoly R[n]} :=
  \sum_(i < n) 'X_i^+d.
Definition Schur d (sh : intpartn d) : {mpoly R[n]} :=
  \sum_(t : tabsh n0 sh) \prod_(v <- to_word t) 'X_v.

Lemma elementary_mesymE d : elementary d = mesym n R d.
Proof. by []. Qed.

Lemma mesym_homog d : mesym n R d \is d.-homog.
Proof.
  apply/dhomogP => m.
  rewrite msupp_mesymP => /existsP [] s /andP [] /eqP <- {d} /eqP -> {m}.
  exact: mdeg_mesym1.
Qed.


Lemma elementary_homog d : elementary d \is d.-homog.
Proof. by rewrite elementary_mesymE mesym_homog. Qed.

Lemma complete_homog d : complete d \is d.-homog.
Proof.
  rewrite /complete; apply rpred_sum => m /eqP H.
  by rewrite dhomogX /= H.
Qed.

Lemma power_sum_homog d : power_sum d \is d.-homog.
Proof.
  rewrite /power_sum; apply rpred_sum => m _.
  have /(dhomogMn d) : ('X_m : {mpoly R[n]}) \is 1.-homog.
    by rewrite dhomogX /= mdeg1.
  by rewrite mul1n.
Qed.

Lemma monomial_homog d (sh : intpartn d) : monomial sh \is d.-homog.
Proof.
  rewrite /monomial; apply rpred_sum => m /eqP Hm.
  rewrite dhomogX /= -{2}(intpartn_sumn sh) /mdeg.
  have Hperm : perm_eq m sh.
    by rewrite -(perm_sort leq) Hm perm_eq_refl.
  by rewrite (eq_big_perm _ Hperm) /= sumnE.
Qed.

Lemma elementary_sym d : elementary d \is symmetric.
Proof. rewrite elementary_mesymE; exact: mesym_sym. Qed.

Lemma complete_sym d : complete d \is symmetric.
Proof.
  apply/issymP => s; rewrite -mpolyP => m.
  rewrite /complete mcoeff_sym !raddf_sum /=.
  case: (altP (mdeg m =P d%N)) => [<- | Hd].
  - have Hsm : mdeg (m#s) < (mdeg m).+1.
      by rewrite mdeg_mperm.
    rewrite (bigD1 (BMultinom Hsm)) /=; last by rewrite mdeg_mperm.
    rewrite mcoeffX eq_refl big1 ?addr0 /=; first last.
      move=> n /= /andP [] _ /negbTE.
      by rewrite {1}/eq_op /= mcoeffX => ->.
    have Hm : mdeg m < (mdeg m).+1 by [].
    rewrite (bigD1 (BMultinom Hm)) //=.
    rewrite mcoeffX eq_refl big1 ?addr0 //=.
    move=> n /= /andP [] _ /negbTE.
    by rewrite {1}/eq_op /= mcoeffX => ->.
  - rewrite big1; first last.
      move=> n /eqP Hd1; rewrite mcoeffX.
      suff /= : val n != m#s by move/negbTE ->.
      move: Hd; rewrite -{1}Hd1; apply contra=> /eqP ->.
      by rewrite mdeg_mperm.
    rewrite big1 //.
    move=> n /eqP Hd1; rewrite mcoeffX.
    suff /= : val n != m by move/negbTE ->.
    by move: Hd; rewrite -{1}Hd1; apply contra=> /eqP ->.
Qed.

Lemma power_sum_sym d : power_sum d \is symmetric.
Proof.
  rewrite /power_sum; apply/issymP => s.
  rewrite raddf_sum /= (reindex_inj (h := s^-1))%g /=; last by apply/perm_inj.
  apply eq_bigr => i _; rewrite rmorphX /=; congr (_ ^+ _).
  rewrite msymX /=; congr mpolyX.
  rewrite mnmP => j; rewrite !mnmE /=; congr nat_of_bool.
  apply/eqP/eqP => [|->//].
  exact: perm_inj.
Qed.

Lemma monomial_sym d (sh : intpartn d) : monomial sh \is symmetric.
Proof.
  apply/issymP => s; rewrite /monomial raddf_sum /=.
  pose fm := fun m : 'X_{1..n < d.+1} => m#s.
  have Hfm m : mdeg (fm m) < d.+1 by rewrite /fm mdeg_mperm bmdeg.
  rewrite (reindex_inj (h := fun m => BMultinom (Hfm m))) /=; first last.
    rewrite /fm => m n /= /(congr1 val) /=.
    rewrite mnmP => Heq; apply val_inj; rewrite mnmP /= => i.
    have:= Heq ((s^-1)%g i).
    by rewrite !mnmE permKV.
  apply congr_big => //.
  - move=> m /=; rewrite [sort _ _](_ : _ = sort leq m) //.
    apply (eq_sorted leq_trans anti_leq); try exact: (sort_sorted leq_total).
    do 2 rewrite perm_eq_sym (perm_sort leq _).
    apply/tuple_perm_eqP; exists s.
    by apply (eq_from_nth (x0 := 0%N)); rewrite size_map.
  - move=> m _.
    rewrite msymX /fm /=; congr mpolyX.
    rewrite mnmP => j; rewrite !mnmE /=.
    by rewrite permKV.
Qed.




(** All basis agrees at degree 0 *)
Lemma elementary0 : elementary 0 = 1.
Proof. by rewrite elementary_mesymE mesym0E. Qed.

Lemma powersum0 : power_sum 0 = n%:R.
Proof.
  rewrite /power_sum (eq_bigr (fun _ => 1)); last by move=> i _; rewrite expr0.
  by rewrite sumr_const card_ord.
Qed.

Lemma complete0 : complete 0 = 1.
Proof.
  have Hd0 : (mdeg (0%MM : 'X_{1..n})) < 1 by rewrite mdeg0.
  rewrite /complete (big_pred1 (BMultinom Hd0)); first last.
    move=> m /=; by rewrite mdeg_eq0 {2}/eq_op /=.
  by rewrite /= mpolyX0.
Qed.

Lemma Schur_tabsh_readingE  d (sh : intpartn d) :
  Schur sh =  \sum_(t : d.-tuple 'I_n | tabsh_reading sh t)
               \prod_(v <- t) 'X_v.
Proof.
  rewrite /Schur /index_enum -!enumT.
  rewrite -[LHS](big_map (fun t => to_word (val t)) xpredT
                         (fun w => \prod_(v <- w) 'X_v)).
  rewrite -[RHS](big_map val (tabsh_reading sh)
                         (fun w => \prod_(v <- w) 'X_v)).
  rewrite -[RHS]big_filter.
  by rewrite (eq_big_perm _ (to_word_enum_tabsh _ sh)) /=.
Qed.

Lemma Schur0 (sh : intpartn 0) : Schur sh = 1.
Proof.
  rewrite Schur_tabsh_readingE (eq_bigl (xpred1 [tuple])); first last.
    move=> i /=; by rewrite tuple0 [RHS]eq_refl intpartn0.
  by rewrite big_pred1_eq big_nil.
Qed.

(** All basis agrees at degree 1 *)
Lemma elementary1 : elementary 1 = \sum_(i < n) 'X_i.
Proof. by rewrite elementary_mesymE mesym1E. Qed.

Lemma power_sum1 : power_sum 1 = \sum_(i < n) 'X_i.
Proof. by apply eq_bigr => i _; rewrite expr1. Qed.

Lemma complete1 : complete 1 = \sum_(i < n) 'X_i.
Proof.
  rewrite /complete -mpolyP => m.
  rewrite !raddf_sum /=.
  case: (boolP (mdeg m == 1%N)) => [/mdeg1P [] i /eqP -> | Hm].
  - have Hdm : (mdeg U_(i))%MM < 2 by rewrite mdeg1.
    rewrite (bigD1 (BMultinom Hdm)) /=; last by rewrite mdeg1.
    rewrite mcoeffX eq_refl big1; first last.
      move=> mm /andP [] _ /negbTE.
      by rewrite mcoeffX {1}/eq_op /= => ->.
    rewrite /= (bigD1 i) // mcoeffX eq_refl /= big1 // => j /negbTE H.
    rewrite mcoeffX.
    case eqP => //; rewrite mnmP => /(_ i).
    by rewrite !mnm1E H eq_refl.
  - rewrite big1; first last.
      move=> p /eqP Hp; rewrite mcoeffX.
      case eqP => // Hpm; subst m.
      by move: Hm; rewrite Hp.
    rewrite big1 // => p _.
    rewrite mcoeffX; case eqP => // Hmm; subst m.
    by rewrite mdeg1 in Hm.
Qed.


Lemma Schur_oversize d (sh : intpartn d) : size sh > n -> Schur sh = 0.
Proof.
  rewrite Schur_tabsh_readingE=> Hn; rewrite big_pred0 // => w.
  apply (introF idP) => /tabsh_readingP [] tab [] Htab Hsh _ {w}.
  suff F0 i : i < size sh -> nth (inhabitant _) (nth [::] tab i) 0 >= i.
    have H := ltn_ord (nth (inhabitant _) (nth [::] tab n) 0).
    have:= leq_trans H (F0 _ Hn); by rewrite ltnn.
  rewrite -Hsh size_map; elim: i => [//= | i IHi] Hi.
  have := IHi (ltn_trans (ltnSn i) Hi); move/leq_ltn_trans; apply.
  rewrite -ltnXnatE.
  move: Htab => /is_tableauP [] Hnnil _ Hdom.
  have {Hdom} := Hdom _ _ (ltnSn i) => /dominateP [] _; apply.
  rewrite lt0n; apply/nilP/eqP; exact: Hnnil.
Qed.

Definition rowpart d := if d is _.+1 then [:: d] else [::].
Fact rowpartnP d : is_part_of_n d (rowpart d).
Proof. case: d => [//= | d]; by rewrite /is_part_of_n /= addn0 eq_refl. Qed.
Definition rowpartn d : intpartn d := IntPartN (rowpartnP d).
(* Definition complete d : {mpoly R[n]} := Schur (rowpartn d). *)

Definition colpart d := nseq d 1%N.
Fact colpartnP d : is_part_of_n d (colpart d).
Proof.
  elim: d => [| d ] //= /andP [] /eqP -> ->.
  rewrite add1n eq_refl andbT /=.
  by case: d.
Qed.
Definition colpartn d : intpartn d := IntPartN (colpartnP d).
(* Definition elementary d : {mpoly R[n]} := Schur (colpartn d). *)

Lemma conj_rowpartn d : conj_intpartn (rowpartn d) = colpartn d.
Proof. apply val_inj => /=; rewrite /rowpart /colpart; by case: d. Qed.
Lemma conj_colpartn d : conj_intpartn (colpartn d) = rowpartn d.
Proof. rewrite -[RHS]conj_intpartnK; by rewrite conj_rowpartn. Qed.


Lemma tabwordshape_row d (w : d.-tuple 'I_n) :
  tabsh_reading (rowpartn d) w = sorted leq [seq val i | i <- w].
Proof.
  rewrite /tabsh_reading /= /rowpart ; case: w => w /=/eqP Hw.
  case: d Hw => [//= | d] Hw; rewrite Hw /=; first by case: w Hw.
  rewrite addn0 eq_refl andbT //=.
  case: w Hw => [//= | w0 w] /= /eqP; rewrite eqSS => /eqP <-.
  rewrite take_size; apply esym; apply (map_path (b := pred0)) => /=.
  - move=> i j /= _ ; exact: leqXnatE.
  - by apply/hasPn => x /=.
Qed.


Lemma perm_eq_enum_basis d :
  perm_eq [seq s2m (val s) | s <- enum (basis n d)]
          [seq val m | m <- enum [set m : 'X_{1..n < d.+1} | mdeg m == d]].
Proof.
  apply uniq_perm_eq.
  - rewrite map_inj_in_uniq; first exact: enum_uniq.
    move=> i j; rewrite !mem_enum => Hi Hj; exact: inj_s2m.
  - rewrite map_inj_uniq; first exact: enum_uniq.
    exact: val_inj.
  move=> m; apply (sameP idP); apply (iffP idP).
  - move=> /mapP [] mb; rewrite mem_enum inE => /eqP Hmb ->.
    have Ht : size (m2s mb) == d by rewrite -{2}Hmb size_m2s.
    apply/mapP; exists (Tuple Ht) => /=; last by rewrite s2mK.
    rewrite mem_enum inE /=; exact: srt_m2s.
  - move=> /mapP [] s; rewrite mem_enum inE /= => Hsort ->.
    have mdegs : mdeg (s2m s) = d.
      rewrite /s2m /mdeg mnm_valK /= big_map enumT -/(index_enum _).
      by rewrite combclass.sum_count_mem count_predT size_tuple.
    have mdegsP : mdeg (s2m s) < d.+1 by rewrite mdegs.
    apply/mapP; exists (BMultinom mdegsP) => //.
    by rewrite mem_enum inE /= mdegs.
Qed.

(** Equivalent definition of complete symmetric function *)
Lemma complete_basisE d : \sum_(s in (basis n d)) 'X_[s2m s] = Schur (rowpartn d).
Proof.
  rewrite Schur_tabsh_readingE (eq_bigl _ _ (@tabwordshape_row d)).
  rewrite [RHS](eq_bigr (fun s : d.-tuple 'I_n => 'X_[s2m s])); first last.
    move=> [s _] /= _; rewrite /s2m; elim: s => [| s0 s IHs]/=.
      by rewrite big_nil -/mnm0 mpolyX0.
    rewrite big_cons {}IHs -mpolyXD; congr ('X_[_]).
    rewrite mnmP => i; by rewrite mnmDE !mnmE.
  apply eq_bigl => m;  by rewrite inE /=.
Qed.

Lemma completeE d : complete d = Schur (rowpartn d).
Proof.
  rewrite /complete -complete_basisE.
  rewrite -(big_map (@bmnm n d.+1) (fun m => mdeg m == d) (fun m => 'X_[m])).
  rewrite /index_enum -enumT -big_filter.
  set tmp := filter _ _.
  have {tmp} -> : tmp = [seq val m | m <- enum [set m :  'X_{1..n < d.+1} | mdeg m == d]].
    rewrite {}/tmp /enum_mem filter_map -filter_predI; congr map.
    apply eq_filter => s /=; by rewrite !inE andbT.
  rewrite -(eq_big_perm _ (perm_eq_enum_basis d)) /=.
  by rewrite big_map -[RHS]big_filter.
Qed.

Lemma tabwordshape_col d (w : d.-tuple 'I_n) :
    tabsh_reading (colpartn d) w = sorted (@gtnX _) w.
Proof.
  rewrite /tabsh_reading /= /colpart ; case: w => w /=/eqP Hw.
  have -> : sumn (nseq d 1%N) = d.
    elim: d {Hw} => //= d /= ->; by rewrite add1n.
  rewrite Hw eq_refl /= rev_nseq.
  have -> : rev (reshape (nseq d 1%N) w) = [seq [:: i] | i <- rev w].
    rewrite map_rev; congr rev.
    elim: d w Hw => [| d IHd] //=; first by case.
    case => [| w0 w] //= /eqP; rewrite eqSS => /eqP /IHd <-.
    by rewrite take0 drop0.
  rewrite -rev_sorted.
  case: {w} (rev w) {d Hw} => [|w0 w] //=.
  elim: w w0 => [//= | w1 w /= <-] w0 /=.
  congr andb; rewrite /dominate /= andbT {w}.
  by rewrite /ltnX_op leqXE /= /leqOrd -ltn_neqAle.
Qed.

(** The definition of elementary symmetric polynomials as column Schur
    function agrees with the one from mpoly *)
Lemma elementaryE d : elementary d = Schur (colpartn d).
Proof.
  rewrite elementary_mesymE mesym_tupleE /tmono /elementary Schur_tabsh_readingE.
  rewrite (eq_bigl _ _ (@tabwordshape_col d)).
  set f := BIG_F.
  rewrite (eq_bigr (fun x => f(rev_tuple x))); first last.
    rewrite /f => i _ /=; apply: eq_big_perm; exact: perm_eq_rev.
  rewrite (eq_bigl (fun i => sorted gtnX (rev_tuple i))); first last.
    move=> [t /= _]; rewrite rev_sorted.
    case: t => [//= | t0 t] /=.
    apply: (map_path (b := pred0)).
    + move=> x y /= _; by rewrite -ltnXnatE.
    + by apply/hasPn => x /=.
  rewrite /f {f}.
  rewrite [RHS](eq_big_perm
                  (map (@rev_tuple _ _)
                       (enum (tuple_finType d (ordinal_finType n))))) /=.
  rewrite big_map /=; first by rewrite /index_enum /= enumT.
  apply uniq_perm_eq.
  - rewrite /index_enum -enumT; exact: enum_uniq.
  - rewrite map_inj_uniq; first exact: enum_uniq.
    apply (can_inj (g := (@rev_tuple _ _))).
    move=> t; apply val_inj => /=; by rewrite revK.
  - rewrite /index_enum -enumT /= => t.
    rewrite mem_enum /= inE; apply esym; apply/mapP.
    exists (rev_tuple t) => /=.
    + by rewrite mem_enum.
    + apply val_inj; by rewrite /= revK.
Qed.


Lemma Schur1 (sh : intpartn 1) : Schur sh = \sum_(i<n) 'X_i.
Proof.
  suff -> : sh = rowpartn 1 by rewrite -completeE complete1.
  apply val_inj => /=; exact: intpartn1.
Qed.

End Bases.
