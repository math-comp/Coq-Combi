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

Reserved Notation "a ::| f" (at level 20).
Reserved Notation "f |:: a" (at level 20).
Reserved Notation "f ⧢ g" (at level 40, left associativity).
Reserved Notation "f ⧺ g" (at level 40, left associativity).
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
Implicit Types (f g : A -> M) (r : R) (a : A) (x : {malg R[A]}) (y : M).

Definition alg_lift f x : M := \sum_(u <- msupp x)  x@_u *: f u.

Lemma alg_liftB f a : alg_lift f << a >> = f a.
Proof.
by rewrite /alg_lift msuppU oner_eq0 big_seq_fset1 mcoeffU eq_refl scale1r.
Qed.

Lemma alg_liftEw (S : {fset A}) f x :
  msupp x `<=` S -> alg_lift f x = \sum_(u <- S) x@_u *: f u.
Proof.
rewrite /alg_lift => /fsubsetP Hsubset.
rewrite [RHS](bigID (mem (msupp x))) /=.
rewrite [X in _ = X + _]big_fset_condE /=.
have -> : [fset i | i in S & i \in msupp x] = msupp x.
  apply/fsetP=> i; rewrite !inE /= andbC.
  by case: (boolP (i \in msupp x)) => //= /Hsubset ->.
rewrite [X in _ = _ + X]big1 ?addr0 // => a.
rewrite -mcoeff_eq0 => /eqP ->.
by rewrite scale0r.
Qed.

Lemma alg_lift_is_linear f : linear (alg_lift f).
Proof.
move => r /= a1 a2.
pose_big_fset A E.
  rewrite 3?(@alg_liftEw E) // scaler_sumr -big_split /=.
  apply eq_bigr => i _.
  by rewrite linearD /= scalerDl linearZ /= scalerA.
by close.
Qed.

Lemma alg_liftE f g : f =1 g -> alg_lift f =1 alg_lift g.
Proof.
rewrite /alg_lift => H x.
by apply: eq_bigr => /= a _; rewrite H.
Qed.

Canonical alg_lift_additive f := Additive  (alg_lift_is_linear f).
Canonical alg_lift_linear f   := AddLinear (alg_lift_is_linear f).

Lemma alg_lift_unique f (lft : {linear {malg R[A]} -> M}) :
  (forall a, lft << a >> = f a) -> lft =1 alg_lift f.
Proof.
move=> H x.
rewrite (monalgE x) !linear_sum /=; apply eq_bigr => a _.
by rewrite -scale_malgC !linearZ /= H alg_liftB.
Qed.

End MakeLinear.

Lemma alg_lift_id (R : ringType) (A : choiceType) (f : A -> {malg R[A]}) :
  (f =1 fun a => << a >>) -> alg_lift f =1 id.
Proof.
rewrite /alg_lift=> H x.
rewrite [RHS]monalgE; apply eq_bigr => a _.
by rewrite H scale_malgC.
Qed.

Section MakeBilinearDef.

Context {R : ringType} {A B : choiceType} {M : lmodType R}.
Implicit Type (r : R).
Implicit Type (a : A) (b : B).
Implicit Type (x : {malg R[A]}) (y : {malg R[B]}).

Variable f g : A -> B -> M.

Definition alg_lift2 f x y : M := alg_lift (fun v => (alg_lift (f v)) y) x.
Definition alg_lift2r_head k f p q := let: tt := k in alg_lift2 f q p.

Notation alg_lift2r := (alg_lift2r_head tt).

Local Notation "a *|* b" := (alg_lift2 f a b) (at level 40).

Lemma alg_lift2P x y :
  x *|* y = \sum_(u <- msupp x) \sum_(v <- msupp y) x@_u * y@_v *: f u v.
Proof.
rewrite /alg_lift2/alg_lift; apply eq_bigr => a _.
rewrite scaler_sumr; apply eq_bigr => b _.
by rewrite scalerA.
Qed.

Lemma alg_lift2rP x y : alg_lift2r f y x = x *|* y.
Proof. by []. Qed.

Lemma alg_lift2E : f =2 g -> alg_lift2 f =2 alg_lift2 g.
Proof.
rewrite /alg_lift2 => H x y /=.
apply: alg_liftE => a.
exact: alg_liftE => b.
Qed.

Lemma alg_lift2r_is_linear y : linear (alg_lift2r f y).
Proof. by move=> r x1 x2; rewrite !alg_lift2rP /alg_lift2 linearP. Qed.

Canonical alg_lift2r_additive p := Additive (alg_lift2r_is_linear p).
Canonical alg_lift2r_linear p := Linear (alg_lift2r_is_linear p).

Lemma alg_lift2BB a b : << a >> *|* << b >> = f a b.
Proof. by rewrite /alg_lift2 !alg_liftB. Qed.

Lemma alg_lift2BA a y : << a >> *|* y = alg_lift (f a) y.
Proof. by rewrite /alg_lift2 alg_liftB. Qed.

End MakeBilinearDef.

Notation alg_lift2r := (alg_lift2r_head tt).

(* possibility: not require a commutative ring but use the opposite ring *)
(* However this require M to be a bimodule that is                       *)
(* both a lmodType R and a lmodType R^c                                  *)

Lemma alg_lift2C (A B : choiceType) (R : comRingType) (M : lmodType R)
      (f : A -> B -> M) x y :
  alg_lift2r (fun a b => f b a) x y = (alg_lift2 f) x y.
Proof.
rewrite alg_lift2rP !alg_lift2P exchange_big /=.
apply: eq_bigr => a _; apply: eq_bigr => b _.
by rewrite mulrC.
Qed.

Section MakeBilinear.

Context {R : comRingType} {A B : choiceType} (M : lmodType R).
Implicit Type (x : {malg R[A]}) .

Variable f : A -> B -> M.

Lemma alg_lift2_is_linear x : linear (alg_lift2 f x).
Proof. by move=> r x1 x2; rewrite -!alg_lift2C linearP. Qed.

Canonical alg_lift2_additive p := Additive (alg_lift2_is_linear p).
Canonical alg_lift2_linear p := Linear (alg_lift2_is_linear p).

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

Definition consl (a : A) := locked alg_lift
                                   (fun u => (<< a :: u >> : {shalg R[A]})).
Definition rconsl (a : A) := locked alg_lift
                                   (fun u => (<< rcons u a >> : {shalg R[A]})).

Notation "a ::| f" := (consl a f).
Notation "f |:: a" := (rconsl a f).

Lemma conslE a v : a ::| << v >> = << a :: v >>.
Proof. rewrite /consl; unlock; exact: alg_liftB. Qed.
Lemma rconslE v a : << v >> |:: a = << rcons v a >>.
Proof. rewrite /rconsl; unlock; exact: alg_liftB. Qed.

Lemma consl_is_linear a : linear (consl a).
Proof. rewrite /consl; unlock; exact: alg_lift_is_linear. Qed.
Lemma rconsl_is_linear a : linear (rconsl a).
Proof. rewrite /rconsl; unlock; exact: alg_lift_is_linear. Qed.

Canonical consl_additive a := Additive  (consl_is_linear a).
Canonical consl_linear a   := AddLinear (consl_is_linear a).
Canonical rconsl_additive a := Additive  (rconsl_is_linear a).
Canonical rconsl_linear a   := AddLinear (rconsl_is_linear a).

Lemma consl0 a : a ::| 0 = 0. Proof. exact: raddf0. Qed.
Lemma rconsl0 a : 0 |:: a = 0. Proof. exact: raddf0. Qed.
Lemma conslD a q1 q2 : a ::| (q1 + q2) = a ::| q1 + a ::| q2.
Proof. exact: raddfD. Qed.
Lemma rconslD a q1 q2 : (q1 + q2) |:: a = q1 |:: a + q2 |:: a.
Proof. exact: raddfD. Qed.
Lemma consl_sum a I r (P : pred I) (q : I -> {shalg R[A]}) :
  a ::| (\sum_(i <- r | P i) q i) = \sum_(i <- r | P i) a ::| q i.
Proof. exact: raddf_sum. Qed.
Lemma rconsl_sum a I r (P : pred I) (q : I -> {shalg R[A]}) :
  (\sum_(i <- r | P i) q i) |:: a = \sum_(i <- r | P i) q i |:: a.
Proof. exact: raddf_sum. Qed.
Lemma conslZ a r q : a ::| (r *: q) = r *: (a ::| q).
Proof. by rewrite linearZ. Qed.
Lemma rconslZ a r q : (r *: q) |:: a = r *: (q |:: a).
Proof. by rewrite linearZ. Qed.
Lemma rconsl_consl a q b : (a ::| q) |:: b = a ::| (q |:: b).
Proof.
rewrite (monalgE q) !linear_sum /=; apply eq_bigr => u _.
by rewrite -scale_malgC !linearZ /= !(conslE, rconslE) rcons_cons.
Qed.

Fixpoint shufflew_aux a u shu v :=
  if v is b :: v' then a ::| shu v + b ::| shufflew_aux a u shu v'
  else a ::| << u >>.

Fixpoint shufflew u v :=
  if u is a :: u' then shufflew_aux a u' (shufflew u') v
  else << v >>.

Lemma shuffleNilw v : shufflew [::] v = << v >>.
Proof. by []. Qed.

Lemma shufflewNil v : shufflew v [::] = << v >>.
Proof. by case: v => [| i v] //=; rewrite conslE. Qed.

Lemma shufflew_cons a u b v :
  shufflew (a :: u) (b :: v) =
  a ::| shufflew u (b :: v) + b ::| shufflew (a :: u) v.
Proof. by []. Qed.

Lemma shufflew_rcons a u b v :
  shufflew (rcons u a) (rcons v b) =
  shufflew u (rcons v b) |:: a + shufflew (rcons u a) v |:: b.
Proof.
elim: u a v b => [|c u IHu] a v b /=; elim: v a b => [| d v IHv] a b //=.
- by rewrite !conslE !rconslE /= addrC.
- rewrite {}IHv !linearD /= -!(conslE, rconslE) !addrA.
  by rewrite !rconsl_consl [_ + a ::| _]addrC.
- rewrite -{1}[[:: b]]/(rcons [::] b) {}IHu.
  rewrite shufflewNil !linearD /= !rconsl_consl.
  by rewrite -!addrA [X in _ + X = _]addrC !rconslE.
- rewrite -rcons_cons {}IHu {}IHv !linearD /= !rconsl_consl -!addrA.
  by rewrite [X in _ = _ + X]addrCA.
Qed.

Lemma shufflewC u v : shufflew u v = shufflew v u.
Proof.
elim: u v => [| a u IHu] v /=; first by rewrite shufflewNil.
elim: v => [| b v IHv] /=; first exact: conslE.
by rewrite addrC IHv IHu.
Qed.


Definition shuffle : {shalg R[A]} -> {shalg R[A]} -> {shalg R[A]} :=
  locked (alg_lift2 shufflew).

Notation "f ⧢ g" := (shuffle f g).

Lemma shuffleC : commutative shuffle.
Proof.
rewrite /shuffle; unlock => f g.
rewrite -alg_lift2C /= -/shufflew.
rewrite (alg_lift2E (g := shufflew)) // => u v.
exact: shufflewC.
Qed.

Lemma shuffleE u v : << u >> ⧢ << v >> = shufflew u v.
Proof. by rewrite /shuffle; unlock; rewrite alg_lift2BB. Qed.

Lemma shufflenill : left_id << [::] >> shuffle.
Proof.
by rewrite /shuffle=> f; unlock; rewrite /alg_lift2 alg_liftB alg_lift_id.
Qed.
Lemma shufflenilr : right_id << [::] >> shuffle.
Proof. by move=> f; rewrite shuffleC shufflenill. Qed.

Lemma shuffle_is_linear f : linear (shuffle f).
Proof. rewrite /shuffle; unlock; exact: linearP. Qed.
Canonical shuffle_additive p := Additive (shuffle_is_linear p).
Canonical shuffle_linear p := Linear (shuffle_is_linear p).

Lemma shuffle0r p : p ⧢ 0 = 0. Proof. exact: raddf0. Qed.
Lemma shuffleNr p q : p ⧢ - q = - (p ⧢ q).
Proof. exact: raddfN. Qed.
Lemma shuffleDr p q1 q2 : p ⧢ (q1 + q2) = p ⧢ q1 + p ⧢ q2.
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
Lemma shuffleNl p q : - q ⧢ p = - (q ⧢ p).
Proof. by rewrite ![_ ⧢ p]shuffleC linearN. Qed.
Lemma shuffleDl p q1 q2 : (q1 + q2) ⧢ p = q1 ⧢ p + q2 ⧢ p.
Proof. by rewrite ![_ ⧢ p]shuffleC linearD. Qed.
Lemma shuffleBl p q1 q2 : (q1 - q2) ⧢ p = q1 ⧢ p - q2 ⧢ p.
Proof. by rewrite ![_ ⧢ p]shuffleC linearB. Qed.
Lemma shuffleMnl p q n : (q *+ n) ⧢ p = q ⧢ p *+ n.
Proof. by rewrite ![_ ⧢ p]shuffleC linearMn. Qed.
Lemma shuffle_suml p I r (P : pred I) (q : I -> {shalg R[A]}) :
  (\sum_(i <- r | P i) q i) ⧢ p = \sum_(i <- r | P i) q i ⧢ p.
Proof.
rewrite ![_ ⧢ p]shuffleC linear_sum /=.
apply eq_bigr => i _; exact: shuffleC.
Qed.
Lemma shuffleZl p r q : (r *: q) ⧢ p = r *: (q ⧢ p).
Proof. by rewrite ![_ ⧢ p]shuffleC linearZ. Qed.


Lemma shuffle_cons a u b v :
  << a :: u >> ⧢ << b :: v >> =
    a ::| (<< u >> ⧢ << b :: v >>) + b ::| (<< a :: u >> ⧢ << v >>).
Proof. rewrite !shuffleE; exact: shufflew_cons. Qed.
Lemma shuffle_rcons a u b v :
  << rcons u a >> ⧢ << rcons v b >> =
    (<< u >> ⧢ << rcons v b >>) |:: a + (<< rcons u a >> ⧢ << v >>) |:: b.
Proof. rewrite !shuffleE; exact: shufflew_rcons. Qed.

Lemma shuffle_consl a b f g :
  a ::| f ⧢ b ::| g = a ::| (f ⧢ b ::| g) + b ::| (a ::| f ⧢ g).
Proof.
(* raddf_sum expands g along (monalgE g) in \sum_(i : msupp g) _ *)
rewrite (monalgE g) !(shuffle_sumr, consl_sum) -big_split /=.
apply eq_bigr => v _; rewrite -[<< g@_v *g _ >>]scale_malgC.
rewrite !(shuffleZr, conslZ) -scalerDr; congr ( _ *: _) => {g}.

rewrite (monalgE f) !(shuffle_suml, consl_sum) -big_split /=.
apply eq_bigr => u _; rewrite -[<< f@_u *g _ >>]scale_malgC.
rewrite !(shuffleZl, conslZ) -scalerDr; congr ( _ *: _) => {f}.
by rewrite !conslE shuffle_cons.
Qed.

Lemma shuffle_rconsl a b f g :
  f |:: a ⧢ g |:: b = (f ⧢ g |:: b) |:: a + (f |:: a ⧢ g) |:: b.
Proof.
rewrite (monalgE g) !(shuffle_sumr, rconsl_sum) -big_split /=.
apply eq_bigr => v _; rewrite -[<< g@_v *g _ >>]scale_malgC.
rewrite !(shuffleZr, rconslZ) -scalerDr; congr ( _ *: _) => {g}.

rewrite (monalgE f) !(shuffle_suml, rconsl_sum) -big_split /=.
apply eq_bigr => u _; rewrite -[<< f@_u *g _ >>]scale_malgC.
rewrite !(shuffleZl, rconslZ) -scalerDr; congr ( _ *: _) => {f}.
by rewrite !rconslE shuffle_rcons.
Qed.

Lemma shuffle_auxA u v w :
  << u >> ⧢ (<< v >> ⧢ << w >>) = (<< u >> ⧢ << v >>) ⧢ << w >>.
Proof.
elim: u v w => /= [| a u IHu] v w; first by rewrite ?(shufflenill, shufflenilr).
elim: v w => /= [| b v IHv] w; first by rewrite ?(shufflenill, shufflenilr).
elim: w => /= [| c w IHw]; first by rewrite ?(shufflenill, shufflenilr).
rewrite -!conslE.
do 2 rewrite !shuffle_consl ?shuffleDr ?shuffleDl.
rewrite [X in X + _ = _]addrC [RHS]addrC -!addrA.
congr (_ + _); rewrite !conslE.
- by rewrite IHv.
- rewrite [LHS]addrA [RHS]addrC -[RHS]addrA.
  congr (_ + _).
- by rewrite -conslD -shuffleDr -shuffle_cons IHu.
- by rewrite -conslD IHw -shuffleDl shuffle_cons.
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

(*
Section Tests.

Lemma bla1 : (<<[:: 2]>> : {shalg int[nat]}) * <<[:: 2]>> = 2%:R *: <<[:: 2; 2]>>.
Proof.
rewrite !shalg_mulE !(shuffle_cons, shufflenill, shufflenilr, conslE, conslD).
by rewrite -[<<_>> in LHS]scale1r -!scalerDl ?addrA.
Qed.

Lemma bla2 : (<<[:: 2; 2]>> : {shalg int[nat]}) * <<[:: 2; 2]>>
             = 6%:R *: <<[:: 2; 2; 2; 2]>>.
Proof.
rewrite !shalg_mulE !(shuffle_cons, shufflenill, shufflenilr, conslE, conslD).
by rewrite -[<<_>> in LHS]scale1r -!scalerDl ?addrA.
Qed.

Lemma bla3 : (<<[:: 2; 2]>> : {shalg int[nat]}) * <<[:: 2; 2; 2]>>
             = 10%:R *: <<[:: 2; 2; 2; 2; 2]>>.
Proof.
rewrite !shalg_mulE !(shuffle_cons, shufflenill, shufflenilr, conslE, conslD).
by rewrite -[<<_>> in LHS]scale1r -!scalerDl ?addrA.
Qed.

Lemma bla4 : (<<[:: 2; 3]>> : {shalg int[nat]}) * <<[:: 2; 2; 2]>>
             =         <<[:: 2; 3; 2; 2; 2]>>
             + 2%:R *: <<[:: 2; 2; 3; 2; 2]>>
             + 3%:R *: <<[:: 2; 2; 2; 3; 2]>>
             + 4%:R *: <<[:: 2; 2; 2; 2; 3]>>.
Proof.
rewrite !shalg_mulE !(shuffle_cons, shufflenill, shufflenilr, conslE, conslD).

move: <<[:: 2; 3; 2; 2; 2]>> => A.
move: <<[:: 2; 2; 3; 2; 2]>> => B.
move: <<[:: 2; 2; 2; 3; 2]>> => C.
move: <<[:: 2; 2; 2; 2; 3]>> => D.
(* Activating those instead of the previous 4 lines makes the scripts
 * extremely slow.
set A := <<[:: 2; 3; 2; 2; 2]>>.
set B := <<[:: 2; 2; 3; 2; 2]>>.
set C := <<[:: 2; 2; 2; 3; 2]>>.
set D := <<[:: 2; 2; 2; 2; 3]>>.
*)
rewrite -!addrA /=; congr (_ + _) => {A}.
repeat rewrite ?[C + (B + _)]addrCA ?[D + (B + _)]addrCA.
rewrite !addrA -[B in LHS]scale1r -!scalerDl -!addrA; congr (_ + _) => {B}.
rewrite ![D + (C + _)]addrCA.
rewrite !addrA -[C in LHS]scale1r -!scalerDl -!addrA; congr (_ + _) => {C}.
by rewrite !addrA -[D in LHS]scale1r -!scalerDl.
Qed.

Lemma bla5 : (<<[:: 2; 3%N]>> : {shalg int[nat]}) * <<[:: 2; 3; 2]>>
             = 2%:R *: <<[:: 2; 3; 2; 3; 2]>> +
               2%:R *: <<[:: 2; 3; 2; 2; 3]>> +
               2%:R *: <<[:: 2; 2; 3; 2; 3]>> +
               4%:R *: <<[:: 2; 2; 3; 3; 2]>>.
Proof.
rewrite !shalg_mulE !(shuffle_cons, shufflenill, shufflenilr, conslE, conslD).
move: <<[:: 2; 3; 2; 3; 2]>> => A.
move: <<[:: 2; 3; 2; 2; 3]>> => B.
move: <<[:: 2; 2; 3; 2; 3]>> => C.
move: <<[:: 2; 2; 3; 3; 2]>> => D.
rewrite -!addrA.
repeat rewrite ?[C + (A + _)]addrCA ?[D + (A + _)]addrCA.
rewrite !addrA -[A in LHS]scale1r -!scalerDl -!addrA; congr (_ + _) => {A}.
rewrite [C + (B + B)]addrC -addrA.
repeat rewrite ?[C + (B + _)]addrCA ?[D + (B + _)]addrCA.
rewrite !addrA -[B in LHS]scale1r -!scalerDl -!addrA; congr (_ + _) => {B}.
rewrite [D + C]addrC.
repeat rewrite ?[D + (C + _)]addrCA.
rewrite !addrA -[C in LHS]scale1r -!scalerDl -!addrA; congr (_ + _) => {C}.
by rewrite !addrA -[D in LHS]scale1r -!scalerDl.
Qed.

End Tests.
 *)

Section QSymDef.

Variable (R : comRingType).

Implicit Type a b c : nat.
Implicit Type u v w : seq nat.
Implicit Type f g : {shalg R[nat]}.

Notation "<< z *g k >>" := (mkmalgU k z).
Notation "<< k >>" := << 1 *g k >> : ring_scope.

Notation "a ::| f" := (consl a f).

Fixpoint stufflew_aux a u shu v : {shalg R[nat]} :=
  if v is b :: v' then
    (a ::| (shu v)) +
    (b ::| (stufflew_aux a u shu v')) +
    (a + b)%N ::| (shu v')
  else a ::| << u >>.

Fixpoint stufflew u v :=
  if u is a :: u' then stufflew_aux a u' (stufflew u') v
  else << v >>.

Lemma stuffleNilw v : stufflew [::] v = << v >>.
Proof. by []. Qed.

Lemma  stufflewNil v : stufflew v [::] = << v >>.
Proof. by case: v => [| i v] //=; rewrite conslE. Qed.

Lemma stufflew_cons a u b v :
  stufflew (a :: u) (b :: v) =
  (a ::| (stufflew u (b :: v))) +
  (b ::| (stufflew (a :: u) v)) +
  ((a + b) %N ::| (stufflew u v)).
Proof. by []. Qed.

Lemma stufflewC u v : stufflew u v = stufflew v u.
Proof.
elim: u v => [| a u IHu] v /=; first by rewrite stufflewNil.
elim: v => [| b v IHv] /=; first exact: conslE.
by rewrite [_ + consl a _]addrC IHv !IHu -[(b + a)%N]addnC.
Qed.

Definition stuffle : {shalg R[nat]} -> {shalg R[nat]} -> {shalg R[nat]} :=
  locked (alg_lift2 stufflew).

Notation "f ⧺ g" := (stuffle f g).

Lemma stuffleC : commutative stuffle.
Proof.
rewrite /stuffle; unlock => f g.
rewrite -alg_lift2C /= -/stufflew.
rewrite (alg_lift2E (g := stufflew)) // => u v.
exact: stufflewC.
Qed.

Lemma stuffleE u v : << u >> ⧺ << v >> = stufflew u v.
Proof. by rewrite /stuffle; unlock; rewrite alg_lift2BB. Qed.

Lemma stufflenill : left_id << [::] >> stuffle.
Proof.
by rewrite /stuffle=> f; unlock; rewrite /alg_lift2 alg_liftB alg_lift_id.
Qed.
Lemma stufflenilr : right_id << [::] >> stuffle.
Proof. by move=> f; rewrite stuffleC stufflenill. Qed.

Lemma stuffle_is_linear f : linear (stuffle f).
Proof. rewrite /stuffle; unlock; exact: linearP. Qed.
Canonical stuffle_additive p := Additive (stuffle_is_linear p).
Canonical stuffle_linear p := Linear (stuffle_is_linear p).

Lemma stuffle0r p : p ⧺ 0 = 0. Proof. exact: raddf0. Qed.
Lemma stuffleNr p q : p ⧺ - q = - (p ⧺ q).
Proof. exact: raddfN. Qed.
Lemma stuffleDr p q1 q2 : p ⧺ (q1 + q2) = p ⧺ q1 + p ⧺ q2.
Proof. exact: raddfD. Qed.
Lemma stuffleMnr p q n : p ⧺ (q *+ n) = p ⧺ q *+ n.
Proof. exact: raddfMn. Qed.
Lemma stuffle_sumr p I r (P : pred I) (q : I -> {shalg R[nat]}) :
  p ⧺ (\sum_(i <- r | P i) q i) = \sum_(i <- r | P i) p ⧺ (q i).
Proof. exact: raddf_sum. Qed.
Lemma stuffleZr r p q : p ⧺ (r *: q) = r *: (p ⧺ q).
Proof. by rewrite linearZ. Qed.

Lemma stuffle0l p : 0 ⧺ p = 0.
Proof. by rewrite stuffleC linear0. Qed.
Lemma stuffleNl p q : - q ⧺ p = - (q ⧺ p).
Proof. by rewrite ![_ ⧺ p]stuffleC linearN. Qed.
Lemma stuffleDl p q1 q2 : (q1 + q2) ⧺ p = q1 ⧺ p + q2 ⧺ p.
Proof. by rewrite ![_ ⧺ p]stuffleC linearD. Qed.
Lemma stuffleBl p q1 q2 : (q1 - q2) ⧺ p = q1 ⧺ p - q2 ⧺ p.
Proof. by rewrite ![_ ⧺ p]stuffleC linearB. Qed.
Lemma stuffleMnl p q n : (q *+ n) ⧺ p = q ⧺ p *+ n.
Proof. by rewrite ![_ ⧺ p]stuffleC linearMn. Qed.
Lemma stuffle_suml p I r (P : pred I) (q : I -> {shalg R[nat]}) :
  (\sum_(i <- r | P i) q i) ⧺ p = \sum_(i <- r | P i) q i ⧺ p.
Proof.
rewrite ![_ ⧺ p]stuffleC linear_sum /=.
apply eq_bigr => i _; exact: stuffleC.
Qed.
Lemma stuffleZl p r q : (r *: q) ⧺ p = r *: (q ⧺ p).
Proof. by rewrite ![_ ⧺ p]stuffleC linearZ. Qed.

Lemma stuffle_cons a u b v :
  << a :: u >> ⧺ << b :: v >> =
  a ::| (<< u >> ⧺ << b :: v >>) +
  b ::| (<< a :: u >> ⧺ << v >>) +
  (a + b)%N ::| (<< u >> ⧺ << v >>).
Proof. rewrite !stuffleE; exact: stufflew_cons. Qed.

Lemma stuffle_consl a b f g :
  a ::| f ⧺ b ::| g =
  a ::| (f ⧺ b ::| g) + b ::| (a ::| f ⧺ g) + (a + b)%N ::| (f ⧺ g).
Proof.
(* raddf_sum expands g along (monalgE g) in \sum_(i : msupp g) _ *)
rewrite (monalgE g) !(stuffle_sumr, consl_sum) -!big_split /=.
apply eq_bigr => v _; rewrite -[<< g@_v *g _ >>]scale_malgC.
rewrite !(stuffleZr, conslZ) -!scalerDr; congr ( _ *: _) => {g}.

rewrite (monalgE f) !(stuffle_suml, consl_sum) -!big_split /=.
apply eq_bigr => u _; rewrite -[<< f@_u *g _ >>]scale_malgC.
rewrite !(stuffleZl, conslZ) -!scalerDr; congr ( _ *: _) => {f}.
by rewrite !conslE stuffle_cons.
Qed.


(*

Definition addfl (a : nat) :=
  locked alg_lift
         (fun u => <<((a + head 0 u) :: behead u)%N>> : {shalg R[nat]}).

Notation "a ::+ f" := (addfl a f) (at level 40).

Lemma addflE a b v : a ::+ << b :: v >> = << (a + b)%N :: v >>.
Proof. rewrite /addfl; unlock; exact: alg_liftB. Qed.

Lemma addfl_is_linear a : linear (addfl a).
Proof. rewrite /addfl; unlock; exact: alg_lift_is_linear. Qed.

Canonical addfl_additive a := Additive  (addfl_is_linear a).
Canonical addfl_linear a   := AddLinear (addfl_is_linear a).

Lemma addfl0 a : a ::+ 0 = 0. Proof. exact: raddf0. Qed.
Lemma addflD a q1 q2 : a ::+ (q1 + q2) = a ::+ q1 + a ::+ q2.
Proof. exact: raddfD. Qed.
Lemma addfl_sum a I r (P : pred I) (q : I -> {shalg R[nat]}) :
  a ::+ (\sum_(i <- r | P i) q i) = \sum_(i <- r | P i) a ::+ (q i).
Proof. exact: raddf_sum. Qed.
Lemma addflZ a r q : a ::+ (r *: q) = r *: (a ::+ q).
Proof. by rewrite linearZ. Qed.

 *)
