Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype path.
From mathcomp Require Import tuple finfun bigop finset binomial fingroup perm.
From mathcomp Require Import fintype prime ssralg poly finset gproduct.
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

Variables (n m : nat).

Local Notation ct := cycle_type.
Local Notation npart := (intpartn_cast (card_ord n)).
Local Notation mpart := (intpartn_cast (card_ord m)).
Local Notation partmn := (intpartn_cast (esym (card_ord (m+n)))).

Definition pval (s : 'S_m * 'S_n) :=
  fun (x : 'I_(m+n)) => let y := split x in
  match y with
  |inl a => unsplit (inl (s.1 a))
  |inr a => unsplit (inr (s.2 a))                  
  end.

Lemma pval_inj s: injective (pval s).
Proof.
  move=> x y.
  rewrite /pval.
  case: {2 3}(split x) (erefl (split x));
    case: {2 3} (split y) (erefl (split y)). 
Admitted.    

Definition p s :'S_(m+n) := perm (@pval_inj s).

Lemma pM (s1 s2 : 'S_m*'S_n) : (p (s1*s2)%g) = (p s1)*(p s2)%g. 
Proof.
  admit.
Admitted.

Lemma pmorph: {in [set: 'S_m*'S_n] &, {morph p : x y / x *y >-> x * y}}. 
Proof.
  admit.
Admitted.
  
Canonical morph_of_p := Morphism pmorph.

(*the image of 'S_m*'S_n via p endowed with a group structure of type 'S_(m+n)*)
Definition split := p @* ('dom p).

Definition unionpartval (l1 : intpartn m) (l2 : intpartn n) := sort geq l1++l2.

Lemma unionpartvalE l1 l2 : is_part_of_n (m+n) (unionpartval l1 l2).
Proof.
  apply /andP; split.
  - rewrite /unionpartval.
    admit. (*use sort_perm_eq and big_cat*)
  - admit.
Admitted.

Definition unionpart l1 l2 := IntPartN (unionpartvalE l1 l2).

Lemma cycle_typep s l1 l2:
  ct s.1 = l1 ->
  ct s.2 = l2 ->
  (cycle_type (p s)) = partmn (unionpart (mpart l1) (npart l2)).  
Proof.
  admit.
Admitted.

Lemma classfunp s l:
  classfun_part l (p s) = ((l == partmn (unionpart (mpart (ct s.1)) (npart (ct s.2))))%:R)%R.
Proof.
  admit.
Admitted.

Lemma classfun_Res (l: intpartn #|'I_(m+n)|):
  ('Res[split] (classfun_part l))%R = \sum_(x | (l == partmn (unionpart (mpart (x.1)) (npart (x.2)))))  (classfun_part x.1 * classfun_part x.2)%R. (*replace this using prod of repr*)

