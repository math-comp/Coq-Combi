Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun bigop finset binomial fingroup perm.
From mathcomp Require Import fintype tuple finfun bigop prime ssralg poly finset.
From mathcomp Require Import fingroup morphism perm automorphism quotient finalg action.
From mathcomp Require Import zmodp. (* Defines the coercion nat -> 'I_n.+1 *)
From mathcomp Require Import matrix vector mxalgebra falgebra ssrnum algC algnum ssralg pgroup.
From mathcomp Require Import presentation all_character.

Require Import tools permuted symgroup partition Greene sorted.
Require Import permcomp cycles cycletype reprdim1 reprS2.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section StdRepr.
(*This section can be moved into the reprS1 file, and generalised for all n easily*)
(*To show: \rank trivline = 1*)
(*The standard representation is irreducible*)

Notation natS3 := (nat_repr 3).

Definition trivline : 'M[algC]_(1, 3) := \matrix_(i < 1, j < 3) 1.

Lemma trivlineE : mxmodule natS3 trivline.
Proof.
rewrite /mxmodule.
apply /subsetP => /= s _.
rewrite !inE andTb.
have -> // : trivline *m natS3 s = trivline.
apply /matrixP => i j.
rewrite /mulmx !mxE.
rewrite (eq_bigr (fun i0 => (s i0 == j)%:R));
  last by move => j0 _; rewrite !mxE mul1r.
rewrite (bigD1 (s^-1 j)%g) //=.
rewrite permKV eqxx /=.
rewrite big1 ?addr0 //= => i0 i0jneq.
rewrite (_: (_==_) = false) //=.
apply /negP => /eqP i0jeq.
by move: i0jneq; rewrite -i0jeq permK eqxx.
Qed.

Definition trivline_sq : 'M_3 := (trivline + (0 : 'M[algC]_(2,3)))%MS.

Definition trivline_sqE : mxmodule natS3 trivline_sq.
Proof.
apply: addsmx_module; [exact: trivlineE | exact: mxmodule0].
Qed.

Lemma stdP : mxsplits natS3 1%:M trivline_sq.
Proof.
apply mx_Maschke => /=; [exact: algC'G | exact: trivline_sqE | exact: submx1].
Qed.

Definition std_mod : 'M[algC]_(3,3) := let: MxSplits W _ _ _ := stdP in W.

Lemma std_modP : mxmodule natS3 std_mod.
Proof. by rewrite /std_mod; case stdP => W. Qed.

Lemma std_mod_sum : (trivline_sq + std_mod :=: 1%:M)%MS.
Proof. by rewrite /std_mod; case stdP => W. Qed.

Lemma std_mod_direct : mxdirect (trivline_sq + std_mod).
Proof.
rewrite /std_mod /=.
case stdP => W _ _ /=.
rewrite /trivline_sq => /mxdirectP /= H.
apply/mxdirectP => /=.
rewrite H mxrank0 addn0.
congr (_ + _)%N.
apply eqmx_rank.
apply/eqmxP.
exact: addsmx0.
Qed.

Lemma degree_std : \rank std_mod = 2.
Proof.
have:= std_mod_direct => /mxdirectP /=.
rewrite (_ : \rank trivline = 1%N); first last.
  apply anti_leq; rewrite rank_leq_row /=.
  rewrite lt0n mxrank_eq0.
  apply/negP => /eqP/matrixP/(_ ord0 ord0).
  rewrite /trivline !mxE => H.
  by have := oner_neq0 [ringType of algC]; rewrite H eq_refl.
rewrite (_ : \rank 0 = 0%N); last by apply/eqP; rewrite mxrank_eq0.
rewrite addn0 add1n.
by rewrite std_mod_sum mxrank1 => [] [] <-.
Qed.

Definition std_repr := submod_repr std_modP.

Definition std_rep := Representation std_repr.
Definition trivline_rep := Representation (submod_repr (trivline_sqE)).

Lemma std_rep_sum : mx_rsim natS3 (dadd_grepr trivline_rep std_rep).
Proof.
apply (mx_rsim_trans (rG2 := submod_repr (mxmodule1 natS3))).
- by apply mx_rsim_sym; apply rsim_submod1.
- apply: (mx_rsim_dadd (mxmodule1 natS3) std_mod_sum).
  + exact: trivline_sqE.
  + exact: std_modP.
  + (*This line should be cleaned using the correct version of std_mod_direct*)
      by rewrite /std_mod; case stdP => W.
  + by move => H0; apply mx_rsim_iso; apply: mx_iso_refl.
  + by move => H0; apply mx_rsim_iso; apply: mx_iso_refl.
Qed.


Lemma norm_natchar : '[cfRepr (Representation natS3)] = 2%:R.
Proof.
rewrite cfdotE cardsT /= card_Sn factE /= mulnE /=.
Admitted.

Lemma chartrivline : cfRepr trivline_rep = 'chi_0.
Proof.
rewrite -cfunP irr0 => s.
rewrite cfunE cfun1E !inE mulr1n /=.
rewrite /mxtrace.

Admitted.

Lemma cfdot_triv : '['chi_0, cfRepr std_rep] = 0.
Proof.
Admitted.

Lemma std_irr : cfRepr (std_repr) \in irr [set: 'S_3].
Proof.
rewrite irrEchar cfRepr_char andTb.
move: norm_natchar; rewrite (cfRepr_sim std_rep_sum) cfRepr_dadd cfdotDl.
rewrite !cfdotDr addrA chartrivline /= cfnorm_irr.
rewrite ['[_,'chi_0]]cfdotC cfdot_triv conjC0 !addr0.
by rewrite (_: 2%:R = 1+1); first by move => /addrI /eqP -> //.
Qed.

Lemma std_irreducible : mx_irreducible std_repr.
Proof.
move /irr_reprP : std_irr =>
  [rG rGirr /eqP /cfRepr_rsimP /mx_rsim_sym /mx_rsim_irr].
by move=> /(_ rGirr).
Qed.

End StdRepr.

Local Open Scope ring_scope.

Lemma NirrS3 : Nirr [set: 'S_3] = 3.
Proof. by rewrite NirrSn card_intpartn. Qed.

Lemma IirrS3_non0 (i : Iirr [set: 'S_3]%G) :
  i != 0 ->
  (i == cast_ord (esym NirrS3) 1) ||
  (i == cast_ord (esym NirrS3) (@Ordinal 3 2 isT)).
Proof.
move=> in0; case: (boolP (_ == _)) => /= [|in1]; first by [].
apply /eqP; apply val_inj => /=.
case: i in0 in1 => [[|[|i]]] //=; rewrite NirrS3.
by rewrite !ltnS leqn0 => /eqP ->.
Qed.

Lemma std_sign_nrsim : ~ mx_rsim sign_repr std_repr.
Proof.
by move=> /mxrank_rsim; rewrite degree_std.
Qed.

Lemma char_std_sign_neq : cfRepr sign_repr != cfRepr std_repr.
Proof.
by apply /cfRepr_rsimP; apply: std_sign_nrsim.
Qed.

Lemma std_triv_nrsim : ~ mx_rsim triv_repr std_repr.
Proof.
by move=> /mxrank_rsim; rewrite degree_std.
Qed.


Lemma char_triv_std_neq : cfRepr triv_repr != cfRepr std_repr.
Proof.
by apply /cfRepr_rsimP; apply: std_triv_nrsim.
Qed.

Lemma perm_eq_char_S3 :
  perm_eq [:: cfRepr triv_repr;
              cfRepr sign_repr;
              cfRepr std_repr] (irr [set: 'S_3]).
Proof.
have Huniq : uniq [:: cfRepr triv_repr;
                      cfRepr sign_repr;
                      cfRepr std_repr].
  rewrite /= andbT !inE char_std_sign_neq andbT; apply /norP; split.
  - by apply/cfRepr_rsimP; apply: triv_sign_not_sim.
  - exact: char_triv_std_neq.
apply uniq_perm_eq => //; first by apply free_uniq; apply: irr_free.
apply leq_size_perm => //.
move=> i; rewrite !inE=> /orP [/eqP -> | /orP [] /eqP ->]; apply/irr_reprP.
- by exists (Representation triv_repr); first exact: triv_irr.
- by exists (Representation sign_repr); first exact: sign_irr.
- by exists (Representation std_repr); first exact: std_irreducible.
- have:= NirrSn 3; rewrite card_intpartn /=.
  have -> : intpartn_nb 3 = 3 by [].
  by rewrite size_tuple /= => ->.
Qed.


Lemma repr_S3 (rho : representation [fieldType of algC] [set: 'S_3]) :
  mx_irreducible rho ->
    mx_rsim rho triv_repr \/
    mx_rsim rho sign_repr \/
    mx_rsim rho std_repr.
Proof.
move=> Hirr.
have : cfRepr rho \in (irr [set: 'S_3]).
  apply/irr_reprP; by exists rho.
by rewrite -(perm_eq_mem perm_eq_char_S3) !inE =>
  /orP [/cfRepr_rsimP|/orP []/cfRepr_rsimP]; [left | right;left | right;right].
Qed.


