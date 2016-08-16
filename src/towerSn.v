Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import finfun fintype tuple finset bigop.
From mathcomp Require Import ssralg fingroup morphism perm gproduct.
From mathcomp Require Import zmodp. (* Defines the coercion nat -> 'I_n.+1 *)
From mathcomp Require Import ssralg matrix vector mxalgebra falgebra ssrnum algC.
From mathcomp Require Import presentation classfun character mxrepresentation.

From Combi Require Import tools ordcast permuted symgroup partition Greene sorted rep1.

Require Import ssrcomp slicedbij cycles cycletype reprS2.

Import LeqGeqOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.

Local Notation algCF := [fieldType of algC].


Section classGroup.

Variables gT aT: finGroupType.
Variable G H : {group gT}.

Lemma class_disj x y :
  y \notin x ^: G -> x ^: G :&: y ^: G = set0.
Proof using.
move/class_eqP=> xy.
apply /setP=> a; rewrite !inE.
apply /andP => [][/class_eqP ax /class_eqP ay].
by apply xy; rewrite -ax -ay.
Qed.

Lemma prod_conjg (x y : gT * aT) :
  x ^ y = (x.1 ^ y.1, x.2 ^ y.2).
Proof using. by []. Qed.

End classGroup.



Section CFExtProdDefs.

Variables (gT aT : finGroupType).
Variables (G : {group gT}) (H : {group aT}).

Local Open Scope ring_scope.

Lemma cfextprod_subproof (g : 'CF(G)) (h : 'CF(H)) :
  is_class_fun <<setX G H>> [ffun x => (g x.1) * (h x.2)].
Proof using.
rewrite genGid; apply intro_class_fun => [x y|].
- rewrite !inE => /andP [x1 x2] /andP [y1 y2].
  by rewrite !cfunJgen ?genGid.
- move=> x; rewrite inE => /nandP [x1|x2].
  + by rewrite cfun0gen ?mul0r ?genGid.
  + by rewrite [h _]cfun0gen ?mulr0 ?genGid.
Qed.
Definition cfextprod g h := Cfun 0 (cfextprod_subproof g h).
Definition cfextprodr_head k g h := let: tt := k in cfextprod h g.

End CFExtProdDefs.

Notation "f \ox g" := (cfextprod f g) (at level 40, left associativity).
Notation cfextprodr := (cfextprodr_head tt).

Section CFExtProdTheory.

Variables (gT aT : finGroupType).
Variables (G : {group gT}) (H : {group aT}).
Implicit Type (g : 'CF(G)) (h : 'CF(H)).

Local Open Scope ring_scope.

Lemma cfextprodrE h g : cfextprodr h g = g \ox h.
Proof using. by []. Qed.

Lemma cfextprod_is_linear g : linear (cfextprod g : 'CF(H) -> 'CF(setX G H)).
Proof using.
move=> /= a h1 h2.
apply/cfunP=> /= x.
by rewrite !cfunE !mulrDr mulrA [g _ * _]mulrC mulrA.
Qed.
Canonical cfextprod_additive g := Additive (cfextprod_is_linear g).
Canonical cfextprod_linear g := Linear (cfextprod_is_linear g).

Lemma cfextprod0r g : g \ox (0 : 'CF(H)) = 0.
Proof using. by rewrite linear0. Qed.
Lemma cfextprodNr g h : g \ox - h = - (g \ox h).
Proof using. by rewrite linearN. Qed.
Lemma cfextprodDr g h1 h2 : g \ox (h1 + h2) = g \ox h1 + g \ox h2.
Proof using. by rewrite linearD. Qed.
Lemma cfextprodBr g h1 h2 : g \ox (h1 - h2) = g \ox h1 - g \ox h2.
Proof using. by rewrite linearB. Qed.
Lemma cfextprodMnr h g n : g \ox (h *+ n) = (g \ox h) *+ n.
Proof using. by rewrite linearMn. Qed.
Lemma cfextprod_sumr g I r (P : pred I) (phi : I -> 'CF(H)) :
  g \ox (\sum_(i <- r | P i) phi i) = \sum_(i <- r | P i) g \ox phi i.
Proof using. by rewrite linear_sum. Qed.
Lemma cfextprodZr g a h : g \ox (a *: h) = a *: (g \ox h).
Proof using. by rewrite linearZ. Qed.

Lemma cfextprodr_is_linear h : linear (cfextprodr h : 'CF(G) -> 'CF(setX G H)).
Proof using.
move=> /= a g1 g2; rewrite !cfextprodrE.
apply/cfunP=> /= x.
by rewrite !cfunE !mulrDl -mulrA.
Qed.
Canonical cfextprodr_additive h := Additive (cfextprodr_is_linear h).
Canonical cfextprodr_linear h := Linear (cfextprodr_is_linear h).

Lemma cfextprod0l h : (0 : 'CF(G)) \ox h = 0.
Proof using. by rewrite -cfextprodrE linear0. Qed.
Lemma cfextprodNl h g : - g \ox h = - g \ox h.
Proof using. by rewrite -!cfextprodrE linearN. Qed.
Lemma cfextprodDl h g1 g2 : (g1 + g2) \ox h = g1 \ox h + g2 \ox h.
Proof using. by rewrite -!cfextprodrE linearD. Qed.
Lemma cfextprodBl h g1 g2 : (g1 - g2) \ox h = g1 \ox h - g2 \ox h.
Proof using. by rewrite -!cfextprodrE linearB. Qed.
Lemma cfextprodMnl h g n : g *+ n \ox h = g \ox h *+ n.
Proof using. by rewrite -!cfextprodrE linearMn. Qed.
Lemma cfextprod_suml h I r (P : pred I) (phi : I -> 'CF(G)) :
  (\sum_(i <- r | P i) phi i) \ox h = \sum_(i <- r | P i) phi i \ox h.
Proof using. by rewrite -!cfextprodrE linear_sum. Qed.
Lemma cfextprodZl h a g : (a *: g) \ox h = a *: (g \ox h).
Proof using. by rewrite -!cfextprodrE linearZ. Qed.

Variables (n1 n2 : nat).
Variables (rG : mx_representation algCF G n1)
          (rH : mx_representation algCF H n2).

Lemma extprod_mx_repr : mx_repr (setX G H) (fun x => tprod (rG x.1) (rH x.2)).
Proof using.
split=>[|i j]; first by rewrite !repr_mx1 tprod1.
rewrite !inE => /andP [i1 i2] /andP [j1 j2].
by rewrite !repr_mxM // tprodE.
Qed.
Definition extprod_repr := MxRepresentation extprod_mx_repr.

Lemma cfRepr_extprod : cfRepr extprod_repr = cfRepr rG \ox cfRepr rH.
Proof using.
apply/cfun_inP=> x GXHx.
by have:= GXHx; rewrite !inE !cfunE GXHx mxtrace_prod => /andP [-> ->] /=.
Qed.

End CFExtProdTheory.


Section TowerMorphism.

Variables m n : nat.

Implicit Types (p : intpartn m) (q : intpartn n).

Local Notation ct := cycle_typeSN.
Local Notation Smn := (setX [set: 'S_m] [set: 'S_n]).

Definition tinjval (s : ('S_m * 'S_n)) :=
  fun (x : 'I_(m + n)) => let y := split x in
  match y with
  | inl a => unsplit (inl (s.1 a))
  | inr a => unsplit (inr (s.2 a))
  end.

Fact tinjval_inj s : injective (tinjval s).
Proof using.
rewrite /tinjval => x y.
case: {2 3}(split x) (erefl (split x)) => [] a Ha;
  case: {2 3} (split y) (erefl (split y)) => [] b Hb;
    move=> /(congr1 (@split _ _)); rewrite !unsplitK => [] // [];
    move=> /perm_inj Hab; subst a;
    by rewrite -(splitK x) Ha -Hb splitK.
Qed.
Definition tinj s : 'S_(m + n) := perm (@tinjval_inj s).

Fact tinj_morphM : {morph tinj : x y / x * y >-> x * y}.
Proof using.
rewrite /tinj => /= s1 s2; apply /permP => /= x.
rewrite permM -(splitK x) !permE.
by case: splitP => [] j _; rewrite /tinjval !unsplitK /= permM.
Qed.
Canonical morph_of_tinj := Morphism (D := Smn) (in2W tinj_morphM).

(* The image of 'S_m * 'S_n via tinj with a 'S_(m + n) group structure *)
Definition tinj_im := tinj @* ('dom tinj).

Lemma isom_tinj : isom Smn tinj_im tinj.
Proof using.
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

Lemma expg_tinj_lshift s a i :
 (tinj s ^+ i) (lshift n a) = lshift n ((s.1 ^+ i) a).
Proof using.
elim: i => [|i IHi].
  by rewrite !expg0 !perm1.
rewrite !expgSr !permM IHi permE /tinjval /=.
pose y := inl ((s.1 ^+ i) a) => /=.
rewrite (_: lshift _ _ = unsplit (y _)) //.
by rewrite unsplitK.
Qed.

Lemma expg_tinj_rshift s a i :
  (tinj s ^+ i) (rshift m a) = rshift m ((s.2 ^+ i) a).
Proof using.
elim: i => [|i IHi].
  by rewrite !expg0 !perm1.
rewrite !expgSr !permM IHi permE /tinjval /=.
pose y := inr ((s.2 ^+ i) a) => /=.
rewrite (_: rshift _ _ = unsplit (y _)) //.
by rewrite unsplitK.
Qed.

Lemma pcycle_tinj_lshift s a :
  pcycle (tinj s) (lshift n a) = imset (lshift n) (mem (pcycle s.1 a)).
Proof using.
apply/setP => /= Y.
apply/pcycleP/imsetP => /= [[i ->]|[y]].
- exists ((s.1 ^+ i) a); first by apply /pcycleP; exists i.
  exact: expg_tinj_lshift.
- move /pcycleP => [i ->] ->.
  by exists i; rewrite expg_tinj_lshift.
Qed.

Lemma pcycle_tinj_rshift s a :
  pcycle (tinj s) (rshift m a) = imset (@rshift m n) (mem (pcycle s.2 a)).
Proof using.
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
Proof using.
apply/setP => S; rewrite /pcycles inE.
apply/imsetP/orP => [[x _ ->{S}] | [] /imsetP [T /imsetP [x _] ->{T}] ->{S}].
- rewrite -(splitK x); case: splitP => j _ {x}.
  + left; apply/imsetP; exists (pcycle s.1 j) => /=; first exact: mem_imset.
    exact: pcycle_tinj_lshift.
  + right; apply/imsetP; exists (pcycle s.2 j) => /=; first exact: mem_imset.
    exact: pcycle_tinj_rshift.
  - by exists (lshift n x); rewrite // pcycle_tinj_lshift.
  - by exists (rshift m x); rewrite // pcycle_tinj_rshift.
Qed.

Lemma cycle_type_tinj s : ct (tinj s) = union_intpartn (ct s.1) (ct s.2).
Proof using.
apply val_inj; rewrite union_intpartnE intpartn_castE /=.
rewrite pcycles_tinj parts_shape_union; first last.
  rewrite -setI_eq0; apply/eqP/setP => S.
  rewrite !inE; apply/negP => /andP [].
  move=> /imsetP [X /imsetP [x _ ->]] -> {X}.
  move=> /imsetP [X /imsetP [y _ ->]].
  move/setP => /(_ (lshift n x)).
  rewrite mem_imset; last exact: pcycle_id.
  move=> /esym/imsetP => [] [z _] /eqP.
  by rewrite lrinjF.
congr sort; rewrite /ct !intpartn_castE /=.
by congr (_ ++ _); apply parts_shape_inj; [exact: linjP | exact: rinjP].
Qed.

End TowerMorphism.

Arguments tinj {m n} s.
Arguments tinj_im {m n}.

Notation "f \o^ g" := (cfIsom (isom_tinj _ _) (cfextprod f g)) (at level 40).

Section Assoc.

Variables (m n p : nat).

Lemma tinjA (s : 'S_m) (t : 'S_n) (u : 'S_p) :
  tinj (tinj(s, t), u) = cast_perm (addnA m n p) (tinj (s, tinj (t, u))).
Proof using.
apply/permP => /= itmp.
rewrite -(splitK itmp) !permE.
case: splitP => i _ {itmp}; rewrite /tinjval !unsplitK /= /cast_perm_val.
- rewrite -(splitK i) !permE.
  case: splitP => j _ {i}; rewrite /tinjval !unsplitK /=.
  + rewrite [cast_ord (esym _) _](_ : _ = unsplit (inl j));
      last exact: val_inj.
    by rewrite !unsplitK /=; apply val_inj.
  + rewrite [cast_ord (esym _) _](_ : _ = unsplit (inr (lshift _ j)));
      last exact: val_inj.
    rewrite !unsplitK /=; apply val_inj => /=.
    rewrite (_: lshift _ _ = unsplit (inl j)) //.
    by rewrite !permE /tinjval !unsplitK /=.
- rewrite [cast_ord (esym _) _](_ : _ = unsplit (inr (rshift _ i)));
    last by apply: val_inj => /=; rewrite addnA.
  rewrite !permE /tinjval !unsplitK /=.
  rewrite (_: rshift n _ = unsplit (inr i)) //.
  rewrite !permE /tinjval !unsplitK /=.
  by apply val_inj; rewrite /= addnA.
Qed.

End Assoc.

Local Open Scope ring_scope.

Section Restriction.

Variables m n : nat.

Implicit Types (p : intpartn m) (q : intpartn n).

Local Notation ct := cycle_typeSN.
Local Notation Smn := (setX [set: 'S_m] [set: 'S_n]).

Lemma cfuni_tinj s (l : intpartn (m + n)) :
  '1_[l] (tinj s) = (l == union_intpartn (ct s.1) (ct s.2))%:R.
Proof using. by rewrite cfuni_partnE cycle_type_tinj eq_sym. Qed.

Theorem cfuni_Res (l : intpartn (m + n)):
  'Res[tinj_im] ('1_[l]) =
  \sum_(x | l == union_intpartn x.1 x.2) ('1_[x.1] \o^ '1_[x.2]).
Proof using.
apply/cfunP => /= s.
case: (boolP (s \in tinj_im)) => Hs; last by rewrite !cfun0gen // genGid.
rewrite (cfResE _ _ Hs); last exact: subsetT.
move: Hs => /imsetP/= [[s1 s2]].
rewrite inE => /andP [H1 _] -> {s}.
rewrite cfuni_tinj /= -linear_sum (cfIsomE _ _ H1).
rewrite /cfextprod /= sum_cfunE.
rewrite (eq_bigr
           (fun x : intpartn m * intpartn n => ('1_[x.1] s1) * ('1_[x.2] s2)));
  last by move=> i _; rewrite cfunE.
case: (altP (l =P _ )) => [->| Hl] /=.
- rewrite (bigD1 (ct s1, ct s2)) //=.
  rewrite !cfuni_partnE !eqxx /= mulr1.
  rewrite big1 ?addr0 // => [[t1 t2]] /andP [_].
  rewrite !cfuni_partnE eq_sym xpair_eqE.
  by move=> /nandP [] /negbTE -> /=; rewrite ?mulr0 ?mul0r.
- rewrite big1 // => [[t1 t2]] /= /eqP Hll; subst l.
  have {Hl} : (t1, t2) != (ct s1, ct s2).
    by move: Hl; apply contra => /eqP [-> ->].
  rewrite !cfuni_partnE eq_sym xpair_eqE.
  by move=> /nandP [] /negbTE -> /=; rewrite ?mulr0 ?mul0r.
Qed.

End Restriction.


Section Induction.

Variables m n : nat.

Implicit Types (p : intpartn m) (q : intpartn n).

Local Notation ct := cycle_typeSN.
Local Notation S := [set: 'S_(m + n)].
Local Notation Smn := (setX [set: 'S_m] [set: 'S_n]).
Local Notation classX p q := ((perm_of_partCT p, perm_of_partCT q) ^: Smn).
Local Notation class p := (class_of_partCT p).

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma classXE p q : classX p q = setX (class p) (class q).
Proof using.
apply /setP => /= x; rewrite inE.
apply /imsetP/andP => /= [[i _ ]|[/imsetP [i1 _ xi1] /imsetP[i2 _ xi2]]].
- rewrite prod_conjg /= => -> /=.
  by split; apply memJ_class; rewrite inE.
- exists (i1, i2); first by rewrite inE; apply /andP; split; rewrite inE.
  by rewrite prod_conjg -xi1{xi1} -xi2{xi2}; case: x => /=.
Qed.

Lemma cfextprod_cfuni p q :
  '1_[p] \ox '1_[q] = '1_(classX p q).
Proof using.
apply/cfunP => /= x.
rewrite cfunE !cfuni_partnE /= cfunElock genGid !inE /= -natrM mulnb.
congr ((nat_of_bool _)%:R).
rewrite classXE.
apply /andP/subsetP => [[ct1 ct2]|].
- move=> /= y /imsetP [/= x0 _ ] -> {y}.
  rewrite inE; apply/andP; split.
  + apply/classes_of_permP; rewrite perm_of_partCTP prod_conjg /=.
    rewrite cycle_type_conjg.
    by rewrite partn_of_partCTE partCT_of_partnK eq_sym ct1.
  + apply/classes_of_permP; rewrite perm_of_partCTP prod_conjg /=.
    rewrite cycle_type_conjg.
    by rewrite partn_of_partCTE partCT_of_partnK eq_sym ct2.
- move=> /(_ x); rewrite class_refl=> /(_ isT).
  rewrite inE=> /andP [/imsetP[y1 _ ->] /imsetP [y2 _ ->]].
  by rewrite /ct !cycle_type_conjg !perm_of_partCTP !partCT_of_partnK !eqxx.
Qed.

(*
Lemma cfdot_classfun_part p1 p2 :
  '[classfun_part p1, classfun_part p2] =
    (p1 == p2)%:R * (#|class_of_partCT p1|)%:R/(#|'S_n|)%:R.
Proof using.
  admit.
Admitted.
 *)

(*This lemma is of no use and a much more general case is stated below*)
Lemma decomp_cf_triv : \sum_(p : intpartn n) '1_[p] = 1.
Proof using.
apply/cfunP => /= x.
rewrite cfun1Egen genGid inE /=.
rewrite sum_cfunE (bigD1 (ct x)) //=.
rewrite big1 ?addr0 ?cfuni_partnE ?eqxx //=.
by move=> p /negbTE pct; rewrite cfuni_partnE eq_sym pct.
Qed.

Lemma classXI p1 p2 q1 q2 :
  (p2, q2) != (p1, q1) -> (classX p1 q1) :&: (classX p2 q2) = set0.
Proof using.
move=> /eqP qp; apply class_disj.
apply/imsetP => []/= [x _].
rewrite prod_conjg /= => [] [] qp1 qp2.
apply qp; congr (_, _);
  rewrite -[LHS]partCT_of_partnK -[RHS]partCT_of_partnK; congr partn_of_partCT;
  rewrite -[LHS]perm_of_partCTP -[RHS]perm_of_partCTP.
- by rewrite qp1 cycle_type_conjg.
- by rewrite qp2 cycle_type_conjg.
Qed.

(* Application of Frobenius duality : cfdot_Res_r *)
Lemma cfdot_Ind_cfuni_part p q (l : intpartn (m + n)):
  '['Ind[S] ('1_[p] \o^ '1_[q]), '1_[l]] =
  (union_intpartn p q == l)%:R * #|class p|%:R * #|class q|%:R / #|Smn|%:R.
Proof using.
rewrite -cfdot_Res_r cfuni_Res -linear_sum cfIsom_iso cfdot_sumr.
rewrite (eq_bigr
  (fun i : intpartn m * intpartn n =>
     #|(classX p q) :&: (classX i.1 i.2)|%:R / #|Smn|%:R)); first last.
- move => i _; rewrite !cfextprod_cfuni.
  by rewrite cfdot_cfuni //=; apply: class_normal; rewrite !inE.
- case: (boolP (_ == _)) => [|] /= unionp; [rewrite mul1r|rewrite !mul0r].
  + rewrite (bigD1 (p, q)) /=; last by rewrite eq_sym.
    rewrite setIid big1; first by rewrite addr0 classXE cardsX natrM //=.
    by move=> i /andP [] _ ip; rewrite classXI ?cards0 ?mul0r.
  + rewrite big1 //= => i /eqP unioni.
    have ip: i != (p, q).
      move: unionp; apply contraR; rewrite negbK {}unioni => /eqP.
      by case: i => [i1 i2] [-> ->].
    by rewrite classXI ?cards0 ?mul0r.
Qed.

Definition zcoeff (k : nat) (p : intpartn k) : algC :=
  #|'S_k|%:R / #|class_of_partCT p|%:R.

Local Notation "'z_ p " := (zcoeff p) (at level 2).

Lemma neq0zcoeff (k : nat) (p : intpartn k) : 'z_p != 0.
Proof using.
have := Cchar; rewrite charf0P => neq0.
rewrite /zcoeff /= card_Sn.
apply mulf_neq0.
- rewrite neq0 -lt0n; exact: fact_gt0.
- rewrite invr_eq0 neq0; exact: card_class_of_partCT_neq0.
Qed.

Definition pbasis (k : nat) (p : intpartn k) := 'z_p *: '1_[p].

Local Notation "''P_[' p ]" := (pbasis p).

Lemma cfdot_Ind_pbasis p q (l : intpartn (m + n)):
  '['Ind[S] ('P_[p] \o^ 'P_[q]), 'P_[l]] = (union_intpartn p q == l)%:R * 'z_l.
Proof using.
rewrite cfextprodZl cfextprodZr.
rewrite !linearZ /= !cfdotZl cfdotZr cfdot_Ind_cfuni_part /= cardsX.
(* TODO: This computation could be done certainly in an easier way *)
rewrite !mulrA [_ * (_ == _)%:R]mulrC -!mulrA; congr (_ * _).
rewrite [(_)^* * _]mulrC !mulrA -[RHS]mul1r; congr (_ * _); first last.
  by rewrite fmorph_div !conjC_nat.
rewrite -3!mulrA [(#|class p|%:R * _)]mulrC.
rewrite -[((#|class q|%:R * _) * _)]mulrA mulKf; first last.
  by rewrite pnatr_eq0 card_class_of_partCT_neq0.
rewrite mulnC natrM invfM !mulrA -!cardsT mulfK //; last apply neq0CG.
rewrite -mulrA [X in _ * X]mulrC -!mulrA mulKf; first last.
  by rewrite pnatr_eq0 card_class_of_partCT_neq0.
by apply divff; apply neq0CG.
Qed.

Lemma pbasis_gen k (f : 'CF([set: 'S_k])) :
  f = \sum_(p : intpartn k) f (perm_of_partCT p) / 'z_p *: 'P_[p].
Proof using.
apply/cfunP => /= x.
rewrite (bigD1 (ct x)) //= cfunE sum_cfunE big1.
- rewrite addr0 !cfunE cfuni_partnE eqxx /= mulr1.
  rewrite -mulrA [_^-1 *_]mulrC mulrA mulfK; last exact: neq0zcoeff.
  have: (perm_of_partCT (ct x)) \in x ^: [set: 'S_k].
    apply /classes_of_permP; rewrite perm_of_partCTP.
    by rewrite (partn_of_partCTK (cycle_type x)).
  by move/imsetP => [y _ ->]; rewrite cfunJgen ?genGid ?inE.
- by move=> p /negbTE pct; rewrite !cfunE cfuni_partnE eq_sym pct /= !mulr0.
Qed.

Lemma cfdotr_pbasis k (f : 'CF([set: 'S_k])) x : (f x) = '[f, 'P_[ct x]].
Proof using.
rewrite {2}(pbasis_gen f) cfdot_suml.
rewrite (bigD1 (ct x)) //= !cfdotZl cfdotZr.
rewrite cfdot_cfuni; try (by apply: class_normal; rewrite inE).
rewrite setIid big1 ?addr0.
- have: (perm_of_partCT (ct x)) \in x ^: [set: 'S_k].
    apply /classes_of_permP; rewrite perm_of_partCTP.
    by rewrite (partn_of_partCTK (cycle_type x)).
  move/imsetP => [y _ ->]; rewrite cfunJgen ?genGid ?inE //.
  rewrite /zcoeff invf_div -[LHS]mulr1 -!mulrA; congr (_ * _).
  rewrite -cardsT mulKf; last exact: neq0CG.
  rewrite [_^-1 * _]mulrC mulrA mulrC mulKf;
    last by rewrite pnatr_eq0 card_class_of_partCT_neq0.
  rewrite mulrC fmorph_div !conjC_nat -mulrA mulKf; last exact: neq0CG.
  by rewrite divff ?pnatr_eq0 ?card_class_of_partCT_neq0.
- move=> p /negbTE pct.
  rewrite !cfdotZl cfdotZr.
  rewrite cfdot_cfuni; try (by apply: class_normal; rewrite inE).
  rewrite class_disj; first by rewrite cards0 mul0r !mulr0.
  apply/negP=> /classes_of_permP; rewrite !perm_of_partCTP.
  by rewrite partn_of_partCTE !partCT_of_partnK pct.
Qed.

Theorem Ind_pbasis p q :
  'Ind[S] ('P_[p] \o^ 'P_[q]) = 'P_[union_intpartn p q].
Proof using.
apply/cfunP => /= x; rewrite cfunE.
rewrite cfdotr_pbasis cfdot_Ind_pbasis.
rewrite cfuni_partnE eq_sym mulrC.
by case: (boolP (_ == _)) => [/eqP ->|] //=; rewrite !mulr0.
Qed.

End Induction.
