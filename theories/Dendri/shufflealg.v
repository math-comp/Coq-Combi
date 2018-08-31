Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq path choice.
From mathcomp Require Import finset fintype finfun tuple bigop ssralg ssrint.
From mathcomp Require Import fingroup perm zmodp binomial order.
From Devel Require Export finmap xfinmap.
From Devel Require Import ssrcomplements monalg.

Import BigEnoughFSet.
Local Open Scope fset.
Local Open Scope fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "f ::| g" (at level 20).
Reserved Notation "f ⧢ g" (at level 40, left associativity).
Reserved Notation "{ 'shalg' G [ K ] }"
  (at level 0, K, G at level 2, format "{ 'shalg'  G [ K ] }").

Import GRing.Theory.
Local Open Scope ring_scope.

(* Missing lemma in malg *)
Lemma scale_malgC (R : ringType) (A : choiceType) r a :
  r *: << a >> = << r *g a >> :> {malg R[A]}.
Proof. by apply/eqP/malgP => k; rewrite !mcoeffsE mulr_natr. Qed.

Section MakeLinear.

Context {R : ringType} {A : choiceType} {M : lmodType R}.
Implicit Type f g : A -> M.
Implicit Type (r : R).
Implicit Type (a : A).
Implicit Type (x : {malg R[A]}) (y : M).

Definition linmalg f x : M :=
  \sum_(u <- msupp x)  x@_u *: f u.

(* The following proof require to go through enum      *)
(* This is not practical in complicated cases as below *)
Lemma linmalgB f a : linmalg f << a >> = f a.
Proof.
rewrite /linmalg msuppU oner_eq0 big_seq_fset1.
by rewrite mcoeffU eq_refl scale1r.
Qed.

Lemma linmalgEw f x (S : {fset A}) :
  msupp x `<=` S -> linmalg f x = \sum_(u <- S)  x@_u *: f u.
Proof.
rewrite /linmalg => /fsubsetP Hsubset.
rewrite [RHS](bigID (fun a => a \in msupp x)) /=.
rewrite [X in _ = X + _]big_fset_condE /=.
have -> : [fset i | i in S & i \in msupp x] = msupp x.
  apply/fsetP=> i; rewrite !inE /= andbC.
  by case: (boolP (i \in msupp x)) => //= /Hsubset ->.
rewrite [X in _ = _ + X]big1 ?addr0 // => a.
rewrite -mcoeff_eq0 => /eqP ->.
by rewrite scale0r.
Qed.

Lemma linmalg_is_linear f : linear (linmalg f).
Proof.
move => r /= a1 a2.
pose_big_fset A E.
  rewrite 3?(@linmalgEw _ _ E) // scaler_sumr -big_split /=.
  apply eq_bigr => i _.
  by rewrite linearD /= scalerDl linearZ /= scalerA.
by close.
Qed.


Lemma linmalgE f g : f =1 g -> linmalg f =1 linmalg g.
Proof.
rewrite /linmalg => H x.
apply: eq_bigr => /= a _ /=.
by rewrite H.
Qed.

Canonical linmalg_additive f := Additive  (linmalg_is_linear f).
Canonical linmalg_linear f   := AddLinear (linmalg_is_linear f).

End MakeLinear.

Lemma linmalg_id (R : ringType) (A : choiceType) (f : A -> {malg R[A]}) :
  (f =1 fun a => << a >>) -> linmalg f =1 id.
Proof.
rewrite /linmalg=> H x.
rewrite [RHS]monalgE; apply eq_bigr => a _.
by rewrite H scale_malgC.
Qed.

Section MakeBilinearDef.

Context {R : ringType} {A B : choiceType} {M : lmodType R}.
Implicit Type (r : R).
Implicit Type (a : A) (b : B).
Implicit Type (x : {malg R[A]}) (y : {malg R[B]}).

Variable f g : A -> B -> M.

Definition bilinmalg f x y : M :=
  linmalg (fun v => (linmalg (f v)) y) x.
Definition bilinmalgr_head k f p q := let: tt := k in bilinmalg f q p.

Notation bilinmalgr := (bilinmalgr_head tt).

Local Notation "a ⧢ b" := (bilinmalg f a b).

Lemma bilinmalgP x y :
  x ⧢ y = \sum_(u <- msupp x) \sum_(v <- msupp y) x@_u * y@_v *: f u v.
Proof.
rewrite /bilinmalg/linmalg; apply eq_bigr => a _.
rewrite scaler_sumr; apply eq_bigr => b _.
by rewrite scalerA.
Qed.

Lemma bilinmalgrP x y : bilinmalgr f y x = x ⧢ y.
Proof. by []. Qed.

Lemma bilinmalgE : f =2 g -> bilinmalg f =2 bilinmalg g.
Proof.
rewrite /bilinmalg => H x y /=.
apply: linmalgE => a.
exact: linmalgE => b.
Qed.

Lemma bilinmalgr_is_linear y : linear (bilinmalgr f y).
Proof. by move=> r x1 x2; rewrite !bilinmalgrP /bilinmalg linearP. Qed.

Canonical bilinmalgr_additive p := Additive (bilinmalgr_is_linear p).
Canonical bilinmalgr_linear p := Linear (bilinmalgr_is_linear p).

Lemma bilinmalgBB a b : << a >> ⧢ << b >> = f a b.
Proof. by rewrite /bilinmalg !linmalgB. Qed.

Lemma bilinmalgBA a y : << a >> ⧢ y = linmalg (f a) y.
Proof. by rewrite /bilinmalg linmalgB. Qed.

End MakeBilinearDef.

Notation bilinmalgr := (bilinmalgr_head tt).

(* possibility: not require a commutative ring but use the opposite ring *)
Lemma bilinmalgC (A B : choiceType) (R : comRingType) (M : lmodType R)
      (f : A -> B -> M) x y :
  bilinmalgr (fun a b => f b a) x y = (bilinmalg f) x y.
Proof.
rewrite bilinmalgrP !bilinmalgP exchange_big /=.
apply: eq_bigr => a _; apply: eq_bigr => b _.
by rewrite mulrC.
Qed.

Section MakeBilinear.

Context {R : comRingType} {A B : choiceType} (M : lmodType R).
Implicit Type (r : R).
Implicit Type (a : A) (b : B).
Implicit Type (x : {malg R[A]}) (y : {malg R[B]}).

Variable f : A -> B -> M.

Lemma bilinmalg_is_linear x : linear (bilinmalg f x).
Proof. by move=> r x1 x2; rewrite -!bilinmalgC linearP. Qed.

Canonical bilinmalg_additive p := Additive (bilinmalg_is_linear p).
Canonical bilinmalg_linear p := Linear (bilinmalg_is_linear p).

End MakeBilinear.


Section ShuffleAlgebraDef.

Variable (A : choiceType) (R : comRingType).

Definition shalg := {malg R[seq A]}.
Definition shalg_of (_ : phant A) (_ : phant R) := shalg.

End ShuffleAlgebraDef.

Bind Scope ring_scope with shalg.
Bind Scope ring_scope with shalg_of.

Notation "{ 'shalg' R [ A ] }" :=
  (@shalg_of _ _ (Phant A) (Phant R)) : type_scope.

Section ShuffleAlgebra.

Variable (A : choiceType) (R : comRingType).

Implicit Type a b : A.
Implicit Type u v : seq A.
Implicit Type f g : {shalg R[A]}.

Notation "<< z *g k >>" := (mkmalgU k z).
Notation "<< k >>" := << 1 *g k >> : ring_scope.

Definition consl (a : A) := locked linmalg (fun u => (<< a :: u >> : {shalg R[A]})).

Notation "a ::| f" := (consl a f).

Lemma conslE a v : a ::| << v >> = << a :: v >>.
Proof. rewrite /consl; unlock; exact: linmalgB. Qed.

Lemma consl_is_linear a : linear (consl a).
Proof. rewrite /consl; unlock; exact: linmalg_is_linear. Qed.

Canonical consl_additive a := Additive  (consl_is_linear a).
Canonical consl_linear a   := AddLinear (consl_is_linear a).

Lemma consl0 a : a ::| 0 = 0. Proof. exact: raddf0. Qed.
Lemma conslD a q1 q2 : a ::| (q1 + q2) = a ::| q1 + a ::| q2.
Proof. exact: raddfD. Qed.
Lemma consl_sum a I r (P : pred I) (q : I -> {shalg R[A]}) :
  a ::| (\sum_(i <- r | P i) q i) = \sum_(i <- r | P i) a ::| (q i).
Proof. exact: raddf_sum. Qed.
Lemma conslZ a r q : a ::| (r *: q) = r *: (a ::| q).
Proof. by rewrite linearZ. Qed.


Fixpoint shufflew_aux a u shu v :=
  if v is b :: v' then (a ::| (shu v )) + (b ::| (shufflew_aux a u shu v'))
  else a ::| << u >>.

Fixpoint shufflew u v :=
  if u is a :: u' then shufflew_aux a u' (shufflew u') v
  else << v >>.

Lemma shuffleNilw v : shufflew [::] v = << v >>.
Proof. by []. Qed.

Lemma  shufflewNil v : shufflew v [::] = << v >>.
Proof. by case: v => [| i v] //=; rewrite conslE. Qed.

Lemma shufflewCons a u b v :
  shufflew (a :: u) (b :: v) =
  (a ::| (shufflew u (b :: v))) + (b ::| (shufflew (a :: u) v)).
Proof. by []. Qed.

Lemma shufflewC u v : shufflew u v = shufflew v u.
Proof.
elim: u v => [| a u IHu] v /=; first by rewrite shufflewNil.
elim: v => [| b v IHv] /=; first exact: conslE.
by rewrite addrC IHv IHu.
Qed.


Definition shuffle : {shalg R[A]} -> {shalg R[A]} -> {shalg R[A]} :=
  locked (bilinmalg shufflew).

Notation "a ::| f" := (consl a f).
Notation "f ⧢ g" := (shuffle f g).

Lemma shuffleC : commutative shuffle.
Proof.
rewrite /shuffle; unlock => f g.
rewrite -bilinmalgC /= -/shufflew.
rewrite (bilinmalgE (g := shufflew)) // => u v.
exact: shufflewC.
Qed.

Lemma shuffleE u v : << u >> ⧢ << v >> = shufflew u v.
Proof. by rewrite /shuffle; unlock; rewrite bilinmalgBB. Qed.

Lemma shufflenill : left_id << [::] >> shuffle.
Proof.
by rewrite /shuffle=> f; unlock; rewrite /bilinmalg linmalgB linmalg_id.
Qed.
Lemma shufflenilr : right_id << [::] >> shuffle.
Proof. by move=> f; rewrite shuffleC shufflenill. Qed.

Lemma shuffle_is_linear f : linear (shuffle f).
Proof. rewrite /shuffle; unlock; exact: linearP. Qed.
Canonical shuffle_additive p := Additive (shuffle_is_linear p).
Canonical shuffle_linear p := Linear (shuffle_is_linear p).

Lemma shuffle0r p : p ⧢ 0 = 0. Proof. exact: raddf0. Qed.
Lemma shuffleNr p q : p ⧢ (- q) = - (p ⧢ q).
Proof. exact: raddfN. Qed.
Lemma shuffleDr p q1 q2 : p ⧢ (q1 + q2) = p ⧢ (q1) + p ⧢ (q2).
Proof. exact: raddfD. Qed.
Lemma shuffleMnr p q n : p ⧢ (q *+ n) = p ⧢ q *+ n.
Proof. exact: raddfMn. Qed.
Lemma shuffle_sumr p I r (P : pred I) (q : I -> {shalg R[A]}) :
  p ⧢ (\sum_(i <- r | P i) q i) = \sum_(i <- r | P i) p ⧢ (q i).
Proof. exact: raddf_sum. Qed.
Lemma shuffleZr r p q : p ⧢ (r *: q) = r *: (p ⧢ q).
Proof. by rewrite linearZ. Qed.

Lemma shuffle0l p : 0 ⧢ p = 0.
Proof. by rewrite shuffleC linear0. Qed.
Lemma shuffleNl p q : (- q) ⧢ p = - (q ⧢ p).
Proof. by rewrite ![_ ⧢ p]shuffleC linearN. Qed.
Lemma shuffleDl p q1 q2 : (q1 + q2) ⧢ p = q1 ⧢ p + q2 ⧢ p.
Proof. by rewrite ![_ ⧢ p]shuffleC linearD. Qed.
Lemma shuffleBl p q1 q2 : (q1 - q2) ⧢ p = q1 ⧢ p - q2 ⧢ p.
Proof. by rewrite ![_ ⧢ p]shuffleC linearB. Qed.
Lemma shuffleMnl p q n : (q *+ n) ⧢ p = q ⧢ p *+ n.
Proof. by rewrite ![_ ⧢ p]shuffleC linearMn. Qed.
Lemma shuffle_suml p I r (P : pred I) (q : I -> {shalg R[A]}) :
  (\sum_(i <- r | P i) q i) ⧢ p = \sum_(i <- r | P i) (q i) ⧢ p.
Proof.
rewrite ![_ ⧢ p]shuffleC linear_sum /=.
apply eq_bigr => i _; exact: shuffleC.
Qed.
Lemma shuffleZl p r q : (r *: q) ⧢ p = r *: (q ⧢ p).
Proof. by rewrite ![_ ⧢ p]shuffleC linearZ. Qed.


Lemma shuffleCons a u b v :
  << a :: u >> ⧢ << b :: v >> =
    (a ::| (<< u >> ⧢ << b :: v >>)) + (b ::| (<< a :: u >> ⧢ << v >>)).
Proof. rewrite !shuffleE; exact: shufflewCons. Qed.

Lemma shuffleconsl a b f g :
  a ::| f ⧢ b ::| g = a ::| (f ⧢ b ::| g) + b ::| (a ::| f ⧢ g).
Proof.
(* raddf_sum expands g along (monalgE g) in \sum_(i : msupp g) _ *)
rewrite (monalgE g) !(shuffle_sumr, consl_sum) -big_split /=.
apply eq_bigr => v _; rewrite -[<< g@_v *g _ >>]scale_malgC.
rewrite !(shuffleZr, conslZ) -scalerDr; congr ( _ *: _) => {g}.

rewrite (monalgE f) !(shuffle_suml, consl_sum) -big_split /=.
apply eq_bigr => u _; rewrite -[<< f@_u *g _ >>]scale_malgC.
rewrite !(shuffleZl, conslZ) -scalerDr; congr ( _ *: _) => {f}.
by rewrite !conslE shuffleCons.
Qed.

Lemma shuffle_auxA u v w :
  << u >> ⧢ (<< v >> ⧢ << w >>) = (<< u >> ⧢ << v >>) ⧢ << w >>.
Proof.
elim: u v w => /= [| a u IHu] v w; first by rewrite ?(shufflenill, shufflenilr).
elim: v w => /= [| b v IHv] w; first by rewrite ?(shufflenill, shufflenilr).
elim: w => /= [| c w IHw]; first by rewrite ?(shufflenill, shufflenilr).
rewrite -!conslE.
do 2 rewrite !shuffleconsl ?shuffleDr ?shuffleDl.
rewrite [X in X + _ = _]addrC [RHS]addrC -!addrA.
congr (_ + _); rewrite !conslE.
- by rewrite IHv.
- rewrite [LHS]addrA [RHS]addrC -[RHS]addrA.
  congr (_ + _).
- by rewrite -conslD -shuffleDr -shuffleCons IHu.
- by rewrite -conslD IHw -shuffleDl shuffleCons.
Qed.

Lemma shuffleA : associative shuffle.
Proof.
move=> a b c.
rewrite (monalgE c) ?(shuffle_sumr, shuffle_suml); apply eq_bigr => w _.
rewrite -[<< c@_w *g _ >>]scale_malgC ?(shuffleZr, shuffleZl).
congr ( _ *: _) => {c}.
rewrite (monalgE b) ?(shuffle_sumr, shuffle_suml); apply eq_bigr => v _.
rewrite -[<< b@_v *g _ >>]scale_malgC ?(shuffleZr, shuffleZl).
congr ( _ *: _) => {b}.
rewrite (monalgE a) ?(shuffle_sumr, shuffle_suml); apply eq_bigr => u _.
rewrite -[<< a@_u *g _ >>]scale_malgC ?(shuffleZr, shuffleZl).
by rewrite shuffle_auxA.
Qed.

Lemma shuffle_distr : left_distributive shuffle +%R.
Proof. move=> a b c; exact: shuffleDl. Qed.

Lemma malgnil_eq0 : << [::] >> != 0 :> {shalg R[A]}.
Proof. by apply/malgP => /(_ [::]) /eqP; rewrite !mcoeffsE oner_eq0. Qed.

Lemma shuffle_scalAl r f g : r *: (f ⧢ g) = (r *: f) ⧢ g.
Proof. by rewrite shuffleZl. Qed.
Lemma shuffle_scalAr r f g : r *: (f ⧢ g) = f ⧢ (r *: g).
Proof. by rewrite shuffleZr. Qed.

Canonical shalg_eqType := [eqType of {shalg R[A]}].
Canonical shalg_choiceType := [choiceType of {shalg R[A]}].
Canonical shalg_zmodType := [zmodType of {shalg R[A]}].
Canonical shalg_lmodType := [lmodType R of {shalg R[A]}].

Definition shalg_ringRingMixin :=
  ComRingMixin (R := [zmodType of {shalg R[A]}])
               shuffleA shuffleC shufflenill shuffle_distr malgnil_eq0.
Canonical shalg_ringType :=
  Eval hnf in RingType {shalg R[A]} shalg_ringRingMixin.
Canonical shalg_comRingType := ComRingType {shalg R[A]} shuffleC.
Canonical shalg_LalgType := LalgType R {shalg R[A]} shuffle_scalAl.
Canonical shalg_algType := CommAlgType R {shalg R[A]}.

Lemma shalg_mulE f g : f * g = f ⧢ g.
Proof. by []. Qed.

End ShuffleAlgebra.


Section Tests.

Lemma bla1 : (<<[:: 2]>> : {shalg int[nat]}) * <<[:: 2]>> = 2%:R *: <<[:: 2; 2]>>.
Proof.
rewrite shalg_mulE shuffleCons shufflenill shufflenilr conslE.
by rewrite -[in 2%:R]addn1 natrD scalerDl scale1r.
Qed.

Lemma bla2 : (<<[:: 2; 2]>> : {shalg int[nat]}) * <<[:: 2; 2]>>
             = 6%:R *: <<[:: 2; 2; 2; 2]>>.
Proof.
rewrite !(shalg_mulE, shuffleCons, shufflenill, shufflenilr, conslE, conslD).
by rewrite -[<<_>> in LHS]scale1r -!scalerDl !addrA.
Qed.

Lemma bla3 : (<<[:: 2; 2]>> : {shalg int[nat]}) * <<[:: 2; 2; 2]>>
             = 10%:R *: <<[:: 2; 2; 2; 2; 2]>>.
Proof.
rewrite !shalg_mulE !(shuffleCons, shufflenill, shufflenilr, conslE, conslD).
by rewrite -[<<_>> in LHS]scale1r -!scalerDl !addrA.
Qed.

Lemma bla4 : (<<[:: 2; 3%N]>> : {shalg int[nat]}) * <<[:: 2; 2; 2]>>
             =         <<[:: 2; 3; 2; 2; 2%N]>>
             + 2%:R *: <<[:: 2; 2; 3; 2; 2%N]>>
             + 3%:R *: <<[:: 2; 2; 2; 3; 2%N]>>
             + 4%:R *: <<[:: 2; 2; 2; 2; 3%N]>>.
Proof.
rewrite !shalg_mulE !(shuffleCons, shufflenill, shufflenilr, conslE, conslD).
(* ring tactic could be helpful here *)
rewrite -!addrA; congr (_ + _).
do 2 rewrite ![_ + (<<[:: 2; 2; 3; 2; 2]>> + _)]addrC -!addrA.
rewrite -[<<[:: 2; 2; 3; 2; 2]>> in LHS]scale1r.
rewrite !addrA -!scalerDl; congr (_ + _).
rewrite [_ + <<[:: 2; 2; 2; 3; 2]>>]addrC.
rewrite ![_ + (<<[:: 2; 2; 2; 3; 2]>> + _)]addrC -!addrA.
rewrite ![_ + (<<[:: 2; 2; 2; 3; 2]>> + _) in X in _ + (_ + X)]addrC !addrA.
rewrite -[<<[:: 2; 2; 2; 3; 2]>> in LHS]scale1r -!scalerDl.
rewrite -!addrA; congr (_ + _).
by rewrite !addrA -[<<2 :: 2 :: _>> in LHS]scale1r -!scalerDl .
Qed.

Lemma bla5 : (<<[:: 2; 3%N]>> : {shalg int[nat]}) * <<[:: 2; 3; 2]>>
             = 2%:R *: <<[:: 2; 3; 2; 3; 2]>> +
               2%:R *: <<[:: 2; 3; 2; 2; 3]>> +
               2%:R *: <<[:: 2; 2; 3; 2; 3]>> +
               4%:R *: <<[:: 2; 2; 3; 3; 2]>>.
Proof.
rewrite !shalg_mulE !(shuffleCons, shufflenill, shufflenilr, conslE, conslD).
rewrite -!addrA.
do 6 rewrite ![_ + (<<[:: 2; 3; 2; 3; 2]>> + _)]addrC -!addrA.
rewrite addrA -[<<[:: 2; 3; 2; 3; 2]>> in LHS]scale1r -!scalerDl; congr (_ + _).
rewrite addrA -[<<[:: 2; 3; 2; 2; 3]>> in LHS]scale1r -!scalerDl; congr (_ + _).
do 2 rewrite ![_ + (<<[:: 2; 2; 3; 2; 3]>> + _)]addrC -!addrA.
rewrite addrA -[<<[:: 2; 2; 3; 2; 3]>> in LHS]scale1r -!scalerDl; congr (_ + _).
by rewrite !addrA -[<<2 :: 2 :: _>> in LHS]scale1r -!scalerDl .
Qed.

End Tests.
