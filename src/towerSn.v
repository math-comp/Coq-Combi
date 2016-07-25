Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype path.
From mathcomp Require Import tuple finfun bigop finset binomial fingroup perm.
From mathcomp Require Import fintype prime ssralg poly finset gproduct.
From mathcomp Require Import fingroup morphism perm automorphism quotient finalg action.
From mathcomp Require Import zmodp. (* Defines the coercion nat -> 'I_n.+1 *)
From mathcomp Require Import matrix vector mxalgebra falgebra ssrnum algC algnum ssralg pgroup.
From mathcomp Require Import presentation all_character.

From Combi Require Import tools ordcast permuted symgroup partition Greene sorted rep1.

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



Section Restriction.

Variables (m n : nat).

Local Notation ct := cycle_typeSN.

Definition tinjval (s : 'S_m * 'S_n) :=
  fun (x : 'I_(m+n)) => let y := split x in
  match y with
  |inl a => unsplit (inl (s.1 a))
  |inr a => unsplit (inr (s.2 a))
  end.

Lemma tinjval_inj s : injective (tinjval s).
Proof.
  move=> x y.
  rewrite /tinjval.
  case: {2 3}(split x) (erefl (split x)) => [] a Ha;
    case: {2 3} (split y) (erefl (split y)) => [] b Hb;
      move=> /(congr1 (@split _ _)); rewrite !unsplitK => [] // [];
      move=> /perm_inj Hab; subst a;
      by rewrite -(splitK x) Ha -Hb splitK.
Qed.

Definition tinj s : 'S_(m + n) := perm (@tinjval_inj s).

Lemma pmorphM:
  {in (setX [set: 'S_m] [set: 'S_n]) &, {morph tinj : x y / x * y >-> x * y}}.
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

Lemma unionpart_subproof (lpair : intpartn m * intpartn n) :
  is_part_of_n (m + n) (sort geq (lpair.1 ++ lpair.2)).
Proof.
  apply /andP; split.
  - have /perm_eqlP/perm_sumn -> := perm_sort geq (lpair.1 ++ lpair.2).
    by rewrite sumn_cat !intpartn_sumn.
  - rewrite is_part_sortedE; apply/andP; split.
    + by apply sort_sorted => x y; exact: leq_total.
    + have /perm_eqlP/perm_eq_mem -> := perm_sort geq (lpair.1 ++ lpair.2).
      rewrite mem_cat negb_or.
      have := intpartnP lpair.1; have := intpartnP lpair.2.
      by rewrite !is_part_sortedE => /andP [_ ->] /andP [_ ->].
Qed.
Definition unionpart lpair := IntPartN (unionpart_subproof lpair).

Lemma expg_tinj_lshift s a i :
 (tinj s ^+ i) (lshift n a) = lshift n ((s.1 ^+ i) a).
Proof.
  elim: i => [|i IHi].
  - by rewrite !expg0 !perm1.
  - rewrite !expgSr !permM IHi permE /tinjval /=.
    pose y := inl ((s.1 ^+ i) a) => /=.
    rewrite (_: lshift _ _ = unsplit (y _)) //.
    by rewrite unsplitK.
Qed.

Lemma expg_tinj_rshift s a i :
  (tinj s ^+ i) (rshift m a) = rshift m ((s.2 ^+ i) a).
Proof.
  elim: i => [|i IHi].
  - by rewrite !expg0 !perm1.
  - rewrite !expgSr !permM IHi permE /tinjval /=.
    pose y := inr ((s.2 ^+ i) a) => /=.
    rewrite (_: rshift _ _ = unsplit (y _)) //.
    by rewrite unsplitK.
Qed.

Lemma pcycle_tinj_lshift s a :
  pcycle (tinj s) (lshift n a) = imset (lshift n) (mem (pcycle s.1 a)).
Proof.
  apply/setP => /= Y.
  apply/pcycleP/imsetP => /= [[i ->]|[y]].
  - exists ((s.1 ^+ i) a); first by apply /pcycleP; exists i.
    exact: expg_tinj_lshift.
  - move /pcycleP => [i ->] ->.
    by exists i; rewrite expg_tinj_lshift.
Qed.

Lemma pcycle_tinj_rshift s a :
  pcycle (tinj s) (rshift m a) = imset (@rshift m n) (mem (pcycle s.2 a)).
Proof.
  apply/setP => /= Y.
  apply/pcycleP/imsetP => /= [[i ->]|[y]].
  - exists ((s.2 ^+ i) a); first by apply /pcycleP; exists i.
    exact: expg_tinj_rshift.
  - move /pcycleP => [i ->] ->.
    by exists i; rewrite expg_tinj_rshift.
Qed.

Lemma pcycles_tinj s :
  pcycles (tinj s) =
  [set (@lshift m n) @: (x : {set 'I_m}) | x in pcycles s.1]
    :|:
    [set (@rshift m n) @: (x : {set 'I_n}) | x in pcycles s.2 ].
Proof.
  apply/setP/subset_eqP/andP; split; apply /subsetP => /= X.
  - move/imsetP => /= [x _ ->].
    rewrite inE; apply /orP.
    rewrite -(splitK x).
    case: (splitP x) => a /= Hx; [left|right]; apply/imsetP.
    + exists (pcycle s.1 a); first by apply/imsetP; exists a.
      by rewrite pcycle_tinj_lshift.
    + exists (pcycle s.2 a); first by apply/imsetP; exists a.
      by rewrite pcycle_tinj_rshift.
  - rewrite inE; move/orP => [|] /imsetP /= [Y /imsetP /= [y _ ->]] ->.
    + apply/imsetP; exists (lshift n y) => //.
      by rewrite pcycle_tinj_lshift.
    + apply/imsetP; exists (rshift m (n:=n) y) => //.
      by rewrite pcycle_tinj_rshift.
Qed.

Lemma count_set_of_card (T : finType) (p : pred nat) (s : {set {set T}}) :
  count p [seq #|(x : {set T})| | x <- enum s] =
  #|s :&: [set x : {set T} | p #|x|]|.
Proof.
  rewrite cardE -size_filter /enum_mem -enumT /=.
  rewrite filter_map size_map; congr size.
  rewrite -filter_predI; apply eq_filter.
  by move=> S; rewrite !inE andbC.
Qed.

Lemma parts_shape_union (T : finType) (A: {set {set T}}) (B: {set {set T}}) :
  [disjoint A & B] ->
  parts_shape (A :|: B) = sort geq (parts_shape A ++ parts_shape B).
Proof.
  rewrite /parts_shape -setI_eq0 => /eqP disj.
  apply /perm_sortP.
  - by move=> x y; exact: leq_total.
  - by move=> x y z yx xz; exact: (leq_trans xz yx).
  - by move=> x y; rewrite andbC; exact: anti_leq.
  apply/perm_eqP => P.
  have count_sort l : count ^~ (sort geq l) =1 count ^~ l.
    by apply/perm_eqP; rewrite perm_sort perm_eq_refl.
  rewrite count_cat !count_sort !count_set_of_card.
  rewrite setIUl cardsU -[RHS]subn0; congr(_ - _).
  apply/eqP; rewrite cards_eq0 -subset0 -disj.
  by apply/subsetP => x; rewrite !inE => /andP [/andP [-> _] /andP [-> _]].
Qed.

Lemma parts_shape_inj
      (T1 T2 : finType) (f : T1 -> T2) (A : {set {set T1}}) :
  injective f -> parts_shape [set f @: (x : {set T1}) | x in A] = parts_shape A.
Proof.
  rewrite /parts_shape /= => Hinj.
  apply/ssrcomp.perm_sort_geq/perm_eqP => P.
  rewrite !count_set_of_card.
  rewrite -(card_imset _ (imset_inj Hinj)).
  rewrite imsetI; first last.
    move=> B C _ _; exact: imset_inj.
  congr #|pred_of_set _|; apply/setP => S; rewrite !inE.
  case: (boolP (S \in (imset _ _))) => //= /imsetP [U _ -> {S}].
  rewrite (card_imset _ Hinj).
  apply/idP/imsetP => [| [] V].
  - by exists U; rewrite // inE.
  - by rewrite inE => HP /(imset_inj Hinj) ->.
Qed.

Lemma cycle_type_tinj s :
  ct (tinj s) = unionpart (ct s.1, ct s.2).
Proof.
  apply val_inj => /=.
  rewrite intpartn_castE /= /cycle_type_seq /=.
  rewrite pcycles_tinj parts_shape_union; first last.
    rewrite -setI_eq0; apply/eqP/setP => S.
    rewrite !inE; apply/(introF idP) => /andP [].
    move=> /imsetP [X /imsetP [x _ ->]] -> {X}.
    move=> /imsetP [X /imsetP [y _ ->]].
    move/setP => /(_ (lshift n x)).
    rewrite mem_imset; last exact: pcycle_id.
    move=> /esym/imsetP => [] [z _] /eqP.
    by rewrite lrinjF.
  congr sort.
  rewrite /ct !intpartn_castE /= /cycle_type_seq.
  congr (_++_).
  - apply parts_shape_inj; exact: linjP.
  - apply parts_shape_inj; exact: rinjP.
Qed.

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
