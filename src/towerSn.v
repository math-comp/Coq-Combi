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

Local Notation algCF := [fieldType of algC].

Section cfExtProd.
(*
Variables (gT aT : baseFinGroupType).        
Variables (G : {set gT}) (H : {set aT}).

Definition cfExtProd (f1 : 'CF(G)) (f2 : 'CF(H)):=
  [ffun x : (gT*aT) => ((f1 x.1) * (f2 x.2))%R].

Lemma cfExtProd_subproof f1 f2 : is_class_fun (G*H) (cfExtProd f1 f2).
 *)

Variables (m n : nat).

Local Notation i1 := (@pairg1 [finGroupType of 'S_m] [finGroupType of 'S_n]).
Local Notation i2 := (@pair1g [finGroupType of 'S_m] [finGroupType of 'S_n]).

Definition cfExtProd (f1 : 'CF([set: 'S_m])) (f2 : 'CF([set: 'S_n])):=
  [ffun x : ('S_m*'S_n) => ((f1 x.1) * (f2 x.2))%R].

Lemma cfExtProd_subproof f1 f2 : is_class_fun <<[set: 'S_m*'S_n]>> (cfExtProd f1 f2).
Proof.
  admit.
Admitted.

Canonical cf_of_cfExtProd f1 f2:= Classfun (cfExtProd_subproof f1 f2).

Lemma cfExtProdl f1 f2: (cfExtProd f1 f2) \o i1 = f1.
Proof.
  admit.
Admitted.

Lemma cfExtProdr f1 f2 : (cfExtProd f1 f2) \o i2 = f2.
Proof.
  admit.
Admitted.

End cfExtProd.

Section ProdRepr.
(*
Variables (gT rT : finGroupType).
Variables (G : {group gT}) (H : {group rT}).
Variables (n1 n2 : nat) (rG : mx_representation algCF G n1) (rH : mx_representation algCF H n2).
Lemma extprod_mx_repr : mx_repr (G*H) (fun g => tprod (rG g.1) (rH g.2)).
*)

Variables (m n : nat).
Variables (n1 n2 : nat). 
Variables (rSm : mx_representation algCF [set: 'S_m] n1)
          (rSn : mx_representation algCF [set: 'S_n] n2).

  
Lemma extprod_mx_repr : mx_repr [set: 'S_m*'S_n] (fun g => tprod (rSm g.1) (rSn g.2)).
Proof.
  admit.
Admitted.

Definition extprod_repr := MxRepresentation extprod_mx_repr.

End ProdRepr.

Variables (m n: nat).


Lemma cfRepr_prod  n1 n2 (rSm : mx_representation algCF [set: 'S_m] n1) (rSn : mx_representation algCF [set: 'S_n] n2):
  cf_of_cfExtProd (cfRepr rSm) (cfRepr rSn) = cfRepr (extprod_repr rSm rSn).
Proof.
  admit.
Admitted.

Local Notation ct := cycle_typeSN.
(* Local Notation npart := (intpartn_cast (card_ord n)).
Local Notation mpart := (intpartn_cast (card_ord m)).
Local Notation partmn := (intpartn_cast (esym (card_ord (m+n)))).
*)

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

Lemma pmorphM: {in [set: 'S_m*'S_n] &, {morph p : x y / x *y >-> x * y}}. 
Proof.
  admit.
Admitted.
  
Canonical morph_of_p := Morphism pmorphM.

(*the image of 'S_m*'S_n via p endowed with a group structure of type 'S_(m+n)*)
Definition prodIm := p @* ('dom p).

(*i1 and i2 are canonical injection from S_m and S_n to S_m*S_n*)

Local Notation i1 := (@pairg1 [finGroupType of 'S_m] [finGroupType of 'S_n]).
Local Notation i2 := (@pair1g [finGroupType of 'S_m] [finGroupType of 'S_n]).

Definition p1 := p \o i1.

Lemma p1morphM : {in [set: 'S_m] &, {morph p1 : x y / x *y >-> x * y}}.
Proof.
  admit.
Admitted.

Canonical morh_of_p1 := Morphism p1morphM.

Definition p2 := p \o i2.

Lemma p2morphM : {in [set: 'S_n] &, {morph p2 : x y / x *y >-> x * y}}.
Proof.
  admit.
Admitted.

Canonical morh_of_p2 := Morphism p2morphM.

(*injm and injn are the images of 'S_m and 'S_n in S_(m+n) via p \o i1 and p \o i2*)
Definition injm := p1@*('dom p1).
Definition injn := p2@*('dom p2).

Lemma isomp : isom [set: 'S_m*'S_n] prodIm p.
Proof.
  admit.
Admitted.

Definition unionpartval (lpair : intpartn m * intpartn n) :=
  sort geq (lpair.1 ++ lpair.2).

Lemma unionpartvalE lpair : is_part_of_n (m+n) (unionpartval lpair).
Proof.
  apply /andP; split.
  - rewrite /unionpartval.
    admit. (*use sort_perm_eq and big_cat*)
  - admit.
Admitted.

Definition unionpart lpair := IntPartN (unionpartvalE lpair).

Lemma cycle_typep s lpair :
  (ct s.1, ct s.2) = lpair ->
  (cycle_type (p s)) = (unionpart lpair).
Proof.
  admit.
Admitted.

Lemma classfunp s l :
  classfun_part l (p s) = ((l == unionpart (ct s.1, ct s.2))%:R)%R.
Proof.
  admit.
Admitted.

Lemma classfun_Res (l: intpartn (m+n)):
  ('Res[prodIm] (classfun_part l) =
    cfIsom isomp (\sum_(x | (l == unionpart x))
    cf_of_cfExtProd (classfun_part x.1) (classfun_part x.2)))%R. 
Proof.
  admit.
Admitted.


