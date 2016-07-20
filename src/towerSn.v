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

Variables (gT aT : finGroupType).
Variables (G : {group gT}) (H : {group aT}).


Lemma cfExtProd_subproof (f1 : 'CF(G)) (f2 : 'CF(H)) :
  is_class_fun <<setX G H>>
               [ffun x : (gT * aT) => ((f1 x.1) * (f2 x.2))%R].
Proof.
  rewrite genGid.
  apply intro_class_fun => [x y|].
  - rewrite !inE => /andP [x1 x2] /andP [y1 y2].
  by rewrite !cfunJgen ?genGid.
  - move => x; rewrite inE => /nandP [x1|x2].
    + by rewrite cfun0gen ?mul0r ?genGid.
    + by rewrite [f2 _]cfun0gen ?mulr0 ?genGid.
Qed.


Definition cfExtProd f1 f2 := Cfun 0 (cfExtProd_subproof f1 f2).

(*
Local Notation i1 := (@pairg1 gT aT).
Local Notation i2 := (@pair1g gT aT).

Lemma cfExtProdl f1 f2 : (cfExtProd f1 f2) \o i1 =1 f1.
Proof.
  move=> s /=; rewrite /cfExtProd /= cfunE /=.
  admit.
Admitted.

Lemma cfExtProdr f1 f2 : (cfExtProd f1 f2) \o i2 =1 f2.
Proof.
  admit.
Admitted.
*)

End cfExtProd.


Section ProdRepr.

Variables (gT aT : finGroupType).
Variables (G : {group gT}) (H : {group aT}).
Variables (n1 n2 : nat).
Variables (rG : mx_representation algCF G n1)
          (rH : mx_representation algCF H n2).

Lemma extprod_mx_repr : mx_repr (setX G H) (fun g => tprod (rG g.1) (rH g.2)).
Proof.
  split=>[|i j]; first by rewrite !repr_mx1 tprod1.
  rewrite !inE => /andP [i1 i2] /andP [j1 j2].
  by rewrite !repr_mxM // tprodE.
Qed.

Definition extprod_repr := MxRepresentation extprod_mx_repr.
End ProdRepr.

Section cfRepr_ExtProd.
Variables (gT aT : finGroupType).
Variables (G : {group gT}) (H : {group aT}).


Lemma cfRepr_extprod n1 n2
      (rG : mx_representation algCF G n1)
      (rH : mx_representation algCF H n2):
  cfExtProd (cfRepr rG) (cfRepr rH) = cfRepr (extprod_repr rG rH).
Proof.
  apply/cfun_inP=> x GXHx.
  have := GXHx; rewrite !inE => /andP [Gx Hx].
  by rewrite !cfunE /= Gx Hx GXHx mxtrace_prod.
Qed.

End cfRepr_ExtProd.

Variables (m n: nat).

Local Notation ct := cycle_typeSN.

Definition tinjval (s : 'S_m * 'S_n) :=
  fun (x : 'I_(m+n)) => let y := split x in
  match y with
  |inl a => unsplit (inl (s.1 a))
  |inr a => unsplit (inr (s.2 a))
  end.

Lemma tinjval_inj s: injective (tinjval s).
Proof.
  move=> x y.
  rewrite /tinjval.
  case: {2 3}(split x) (erefl (split x)) => [] a Ha;
    case: {2 3} (split y) (erefl (split y)) => [] b Hb;
      move=> /(congr1 (@split _ _)); rewrite !unsplitK => [] // [];
      move=> /perm_inj Hab; subst a;
      by rewrite -(splitK x) Ha -Hb splitK.
Qed.

Definition tinj s :'S_(m + n) := perm (@tinjval_inj s).

Lemma tinjM (s1 s2 : 'S_m * 'S_n) : (tinj (s1 * s2)%g) = (tinj s1) * (tinj s2)%g.
Proof.
  admit.
Admitted.

Lemma pmorphM:
  {in (setX [set: 'S_m] [set: 'S_n]) &, {morph tinj : x y / x *y >-> x * y}}.
Proof.
  move=> /= s1 s2 _ _.
  rewrite /tinj; apply /permP => /= x.
  rewrite permM -(splitK x) !permE.
  case: splitP => [] j _;
  by rewrite /tinjval !unsplitK /= permM.
Qed.

Canonical morph_of_tinj := Morphism pmorphM.

(*the image of 'S_m*'S_n via tinj endowed with a group structure of type 'S_(m+n)*)
Definition prodIm := tinj @* ('dom tinj).

(*i1 and i2 are canonical injection from S_m and S_n to S_m*S_n*)
Local Notation i1 := (@pairg1 [finGroupType of 'S_m] [finGroupType of 'S_n]).
Local Notation i2 := (@pair1g [finGroupType of 'S_m] [finGroupType of 'S_n]).


(*
Definition p1 := tinj \o i1.

Lemma p1morphM : {in [set: 'S_m] &, {morph p1 : x y / x *y >-> x * y}}.
Proof.
  admit.
Admitted.

Canonical morh_of_p1 := Morphism p1morphM.

Definition p2 := tinj \o i2.

Lemma p2morphM : {in [set: 'S_n] &, {morph p2 : x y / x *y >-> x * y}}.
Proof.
  admit.
Admitted.

Canonical morh_of_p2 := Morphism p2morphM.
 *)



(*injm and injn are the images of 'S_m and 'S_n in S_(m+n) via tinj \o i1 and tinj \o i2*)
(*Definition injm := p1@*('dom p1).
Definition injn := p2@*('dom p2).
*)
Lemma isomtinj : isom (setX [set: 'S_m] [set: 'S_n]) prodIm tinj.
Proof.
  apply/isomP; split; last by [].
  apply/subsetP => [] /= [s1 s2]; rewrite inE => /andP [_].
  rewrite !inE /= => /eqP/permP H.
  rewrite -[1]/(1,1) /xpair_eqE /=.
  apply/andP; split; apply/eqP/permP => x; rewrite !perm1.
  - have := H (unsplit (inl x)).
    rewrite /tinj permE /tinjval unsplitK perm1 /=.
    exact: linjP.
  - have := H (unsplit (inr x)).
    rewrite /tinj permE /tinjval unsplitK perm1 /=.
    exact: rinjP.
Qed.

Definition unionpartval (lpair : intpartn m * intpartn n) :=
  sort geq (lpair.1 ++ lpair.2).

Lemma unionpartvalE lpair : is_part_of_n (m+n) (unionpartval lpair).
Proof.
  apply /andP; split.
  - rewrite /unionpartval.
    have /perm_eqlP/perm_sumn -> := perm_sort geq (lpair.1 ++ lpair.2).
    by rewrite sumn_cat !intpartn_sumn.
  - rewrite is_part_sortedE; apply/andP; split.
    + rewrite /unionpartval; apply sort_sorted.
      by move=> x y; exact: leq_total.
    + rewrite /unionpartval.
      have /perm_eqlP/perm_eq_mem -> := perm_sort geq (lpair.1 ++ lpair.2).
      rewrite mem_cat negb_or.
      have := intpartnP lpair.1; have := intpartnP lpair.2.
      by rewrite !is_part_sortedE => /andP [_ ->] /andP [_ ->].
Qed.
Definition unionpart lpair := IntPartN (unionpartvalE lpair).

Lemma cycle_type_tinj s :
  ct (tinj s) = unionpart (ct s.1, ct s.2).
Proof.
  admit.
Admitted.

(* Ancien enoncé :
Lemma cycle_typetinj s lpair :
  (ct s.1, ct s.2) = lpair ->
  cycle_type (tinj s) = unionpart lpair.
Proof.
  admit.
Admitted.
*)

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma classfun_tinj s (l : intpartn (m + n)) :
  classfun_part l (tinj s) = (l == unionpart (ct s.1, ct s.2))%:R.
Proof. by rewrite classfun_partnE cycle_type_tinj eq_sym. Qed.

Theorem classfun_Res (l : intpartn (m+n)):
  'Res[prodIm] (classfun_part l) =
  cfIsom isomtinj
         (\sum_(x | l == unionpart x)
           cfExtProd (classfun_part x.1) (classfun_part x.2)).
Proof.
  apply/cfunP => /= s.
  case: (boolP (s \in prodIm)) => Hs; last by rewrite !cfun0gen // genGid.
  rewrite (cfResE _ _ Hs); last exact: subsetT.
  move: Hs => /imsetP/= [[s1 s2]].
  rewrite inE => /andP [H1 _] -> {s}.
  rewrite classfun_tinj /= (cfIsomE _ _ H1).
  rewrite /cfExtProd /= sum_cfunE.
  rewrite (eq_bigr (fun x : intpartn m * intpartn n =>
                      ((classfun_part x.1 s1) * (classfun_part x.2 s2))));
    last by move=> i _; rewrite cfunE.
  case: (altP (l =P unionpart (ct s1, ct s2))) => [->| Hl] /=.
  - rewrite (bigD1 (ct s1, ct s2)) //=.
    rewrite !classfun_partnE !eqxx /= mulr1.
    rewrite big1 ?addr0 // => [[t1 t2]] /andP [_].
    rewrite !classfun_partnE eq_sym xpair_eqE.
    by move=> /nandP [] /negbTE -> /=; rewrite ?mulr0 ?mul0r.
  - rewrite big1 // => [[t1 t2]] /= /eqP Hll; subst l.
    have {Hl} : (t1, t2) != (ct s1, ct s2).
      by move: Hl; apply contra => /eqP ->.
    rewrite !classfun_partnE eq_sym xpair_eqE.
    by move=> /nandP [] /negbTE -> /=; rewrite ?mulr0 ?mul0r.
Qed.
