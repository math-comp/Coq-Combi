Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun bigop finset binomial fingroup perm.
From mathcomp Require Import fintype tuple finfun bigop prime ssralg poly finset.
From mathcomp Require Import fingroup morphism perm automorphism quotient finalg action.
From mathcomp Require Import zmodp. (* Defines the coercion nat -> 'I_n.+1 *)
From mathcomp Require Import matrix vector mxalgebra falgebra ssrnum algC algnum ssralg pgroup.
From mathcomp Require Import presentation all_character.

From Combi Require Import tools permuted symgroup partition Greene sorted rep1.

Require Import ssrcomp bij cycles cycletype reprS2.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section StdRepr.

Notation natS3 := (nat_repr 3).
  
Definition trivline : 'M[algC]_(3,3) :=
 \matrix_(i < 3,j < 3) (if i == ord0 then 1 else 0).

Lemma trivlineE : mxmodule natS3 trivline. 
Proof.
  rewrite /mxmodule.
  apply /subsetP => /= s _.
  rewrite !inE andTb.
  have -> // : trivline *m natS3 s = trivline. 
  apply /matrixP => i j.
  rewrite /mulmx !mxE.
  rewrite /natS3 /= /nat_mx /perm_mx /row_perm /scalar_mx.
  rewrite (eq_bigr (fun j0 => (if i == ord0 then 1 else 0) * ((s j0)==j)%:R));
    last by move => j0 _; rewrite !mxE.
  case (boolP (i == ord0)) => [|/negbTE] ->.
  - rewrite (eq_bigr (fun i0 => (s i0 == j)%:R)); last by move => i0 _; rewrite mul1r.
    rewrite (bigD1 (s^-1 j)%g) //=.
    rewrite permKV eqxx /=.
    rewrite big1 ?addr0 //= => i0 i0jneq.    
    rewrite (_: (_==_) = false) //=.
    apply /negP => /eqP i0jeq.
    by move: i0jneq; rewrite -i0jeq permK eqxx.
  - by rewrite big1 // => i0 _; rewrite mul0r.
Qed.

Lemma stdP : mxsplits natS3 1%:M trivline.
Proof.
  apply mx_Maschke => /=.
  - rewrite /= /pgroup cardsT /= -natf_neq0 card_Sn.
    by have /charf0P := Cchar => ->; rewrite -lt0n fact_gt0.
  - by exact: trivlineE.
  - by exact: submx1.
Qed.

Definition std_mod : 'M[algC]_(3,3).
  case stdP => W _ _ _.
  exact: W.
Defined.

Lemma std_modP : mxmodule natS3 std_mod.
Proof.
  rewrite /std_mod.
  by case stdP => W.
Qed.

Lemma std_mod_sum : (trivline + std_mod :=: 1%:M)%MS.
Proof.
  rewrite /std_mod.
  by case stdP => W.
Qed.

  
Lemma std_mod_direct : mxdirect (trivline + std_mod).
Proof.
  rewrite /std_mod.
  by case stdP => W.
Qed.

(*Lemma std_simple : mxsimple natS3 std_mod.*)

Definition std_repr := submod_repr std_modP.

Lemma std_irr : cfRepr (std_repr) \in irr [set: 'S_3].
Proof.
  rewrite irrEchar cfRepr_char andTb.
  admit.
Admitted.

Lemma std_irreducible : mx_irreducible std_repr.
Proof.
  move /irr_reprP : std_irr => [rG rGirr /eqP /cfRepr_rsimP /mx_rsim_sym /mx_rsim_irr].  
  by move=> /(_ rGirr).
Qed.

End StdRepr.

Local Open Scope ring_scope.

Lemma NirrS3 : Nirr [set: 'S_3] = 3.
Proof. by rewrite NirrSn card_intpartn. Qed.

Lemma IirrS3_non0 (i : Iirr [set: 'S_3]%G) :
  i != 0 -> (i == cast_ord (esym NirrS3) 1)||(i == cast_ord (esym NirrS3) (@Ordinal 3 2 isT)).
Proof.
  move=> in0; case: (boolP (_ == _)) => /= [|in1]; first by [].
  apply /eqP; apply val_inj => /=.
  case: i in0 in1 => [[|[|i]]] //=; rewrite NirrS3.
  by rewrite !ltnS leqn0 => /eqP ->.
Qed.

Lemma std_sign_nrsim : ~ mx_rsim sign_repr std_repr.
Proof.
  admit.
Admitted.

Lemma char_sign_std_neq : cfRepr sign_repr != cfRepr std_repr.
Proof.
  admit.
Admitted.

Lemma char_triv_std_neq : cfRepr triv_repr != cfRepr std_repr.
Proof.
  admit.
Admitted.


Lemma perm_eq_char_S3 :
  perm_eq [:: cfRepr triv_repr; cfRepr sign_repr; cfRepr std_repr] (irr [set: 'S_3]).
Proof.
  have Huniq : uniq [:: cfRepr (triv_repr (n := 3)); cfRepr sign_repr; cfRepr std_repr].
    rewrite /= andbT !inE char_sign_std_neq andbT; apply /norP; split.
    - by apply/cfRepr_rsimP; exact: triv_sign_not_sim.
    - by exact: char_triv_std_neq.
  apply uniq_perm_eq => //; first by apply free_uniq; exact: irr_free.
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
  mx_irreducible rho -> mx_rsim rho triv_repr \/ mx_rsim rho sign_repr \/ mx_rsim rho std_repr.
Proof.
  move=> Hirr.
  have : cfRepr rho \in (irr [set: 'S_3]).
    apply/irr_reprP; by exists rho.
  by rewrite -(perm_eq_mem perm_eq_char_S3) !inE =>
    /orP [/cfRepr_rsimP|/orP []/cfRepr_rsimP]; [left | right;left | right;right].
Qed.


