(** * Combi.Basic.ordtype : Ordered Types *)
(******************************************************************************)
(*      Copyright (C) 2014-2021 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * Ordered type

Inhabited Types:

- [inhType] == interface for inhabited types
- [inhPordType] == interface for partially ordered inhabited types
- [inhOrdType] == interface for totally ordered inhabited types
- [inhOrdFinType] == interface for totally ordered finite types

Sequence on a totally ordered type:

- [maxL a L] == the maximum of [a] and the element of the sequence [L]
- [allLeq v a] == a is smaller or equal than all the element of [v]
- [allLnt v a] == a is strictly smaller than all the element of [v]

- [rembig w] == [w] minus last occurence of its largest letter
- [posbig w] == the position of the last occurence of the largest letter of [w]

- [shift_pos pos i] == if [i < pos] then [i] else [i.+1]
- [shiftinv_pos pos i] == if [i < pos] then [i] else [i.-1]

Cover relation:

- [covers x y] == [y] covers [x] where [x] and [y] belongs to a common
                  [finPOrderType].
 ********)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import order.
Require Import tools.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Open Scope order_scope.
Import Order.Theory.

(******************************************************************************)
(** * Induction on partially ordered types                                    *)
(******************************************************************************)

Lemma finord_wf (disp : unit) (T : finPOrderType disp) (P : T -> Type) :
  (forall x, (forall y, y < x -> P y) -> P x) -> forall x, P x.
Proof.
move=> IH x.
have [n] := ubnP #|[set y : T | y < x]|; elim: n => // n IHn in x *.
rewrite ltnS leq_eqVlt; case: eqP => [eqcn _ | _ ]; last exact: IHn.
apply: IH => y ltxy; apply: IHn.
rewrite -{}eqcn; apply proper_card; apply/andP; split; apply/subsetP.
- by move=> z; rewrite !inE => /lt_trans; apply.
- by move/(_ y); rewrite !inE => /(_ ltxy); rewrite ltxx.
Qed.

Lemma finord_wf_down (disp : unit) (T : finPOrderType disp) (P : T -> Type) :
  (forall x, (forall y, y > x -> P y) -> P x) -> forall x, P x.
Proof. exact: (finord_wf (T := T^d : finPOrderType _)). Qed.


(******************************************************************************)
(** * Covering relation                                                       *)
(******************************************************************************)

(** We only define covering relation for finite type, since it cannot be      *)
(** decided and it is not very useful for infinite orders.                    *)
Definition covers {disp : unit} {T : finPOrderType disp} :=
  [rel x y : T | (x < y) && [forall z, ~~(x < z < y)]].

Section CoversFinPOrder.

Variable (disp : unit) (T : finPOrderType disp).
Implicit Type (x y : T).

Lemma coversP x y : reflect (x < y /\ (forall z, ~(x < z < y))) (covers x y).
Proof.
apply (iffP andP) => /= [[ltxy /forallP Hcovers] | [ltxy Hcovers]].
- by split => // z; apply/negP.
- by split => //; apply/forallP => z; apply/negP.
Qed.

Lemma ltcovers x y : covers x y -> x < y.
Proof. by move/coversP => []. Qed.

Lemma coversEV x y : covers x y -> forall z, x <= z <= y -> z = x \/ z = y.
Proof.
move=> /coversP[ltxy Hcovers] z /andP[].
rewrite le_eqVlt => /orP[/eqP -> | ltxz]; first by left.
rewrite le_eqVlt => /orP[/eqP -> | ltzy]; first by right.
by exfalso; apply: (Hcovers z); rewrite ltxz ltzy.
Qed.

Lemma covers_dual x y :
  covers (T := T^d) y x = covers x y.
Proof.
rewrite /= ltEdual; congr (_ && _); apply: eq_forallb => z.
by rewrite !ltEdual andbC.
Qed.

Lemma covers_ind (P : T -> Type) :
  (forall x y, covers x y -> P x -> P y) ->
  forall x, P x -> forall y, x <= y -> P y.
Proof.
move=> IH x Px; elim/finord_wf => y IHy.
rewrite le_eqVlt; case: eqP => [<-|] //= _ ltxy.
case: (boolP (covers x y)) => [/IH|]; first exact.
rewrite /covers /= ltxy /= -negb_exists negbK => /existsP/sigW [z0].
move/(arg_minP (P := [pred z | x < z < y]) (fun z => #|[pred t | z < t < y]|))
    => {z0} [zmin /andP[ltxz ltzy] Hzmin].
suff /IH : covers zmin y by apply; apply: (IHy _ ltzy (ltW ltxz)).
rewrite /= ltzy /=; apply/forallP => u; apply/negP => /andP[ltzu ltuy].
have /Hzmin : x < u < y by rewrite ltuy (lt_trans ltxz ltzu).
rewrite leNgt => /negP; apply.
apply proper_card; rewrite /= properE; apply/andP; split.
  by apply/subsetP => v; rewrite !unfold_in => /andP[/(lt_trans ltzu)->->].
apply/negP => /subsetP/(_ u); rewrite !unfold_in ltxx /= => Habs.
by have /Habs : zmin < u < y by rewrite ltzu ltuy.
Qed.

Lemma covers_connect x y : (connect covers x y) = (x <= y).
Proof.
apply/connectP/idP => [[s]|].
  elim: s x => [x /= _ -> // |s0 s IHs] x /= /andP[/andP[/ltW ltxs0 _]].
  by move => {}/IHs /[apply] /(le_trans ltxs0).
move: y; apply covers_ind; last by exists [::].
move=> z y Hcovers [pth Hpath Hlast].
exists (rcons pth y); last by rewrite last_rcons.
by rewrite rcons_path Hpath -Hlast andTb.
Qed.

Lemma covers_path x y :
  reflect (exists2 s, path covers x s & y = last x s) (x <= y).
Proof. by rewrite -covers_connect; apply: (iffP connectP). Qed.

End CoversFinPOrder.

Lemma covers_rind (disp : unit) (T : finPOrderType disp) (P : T -> Type) :
  (forall x y, covers y x -> P x -> P y) ->
  forall x, P x -> forall y, x >= y -> P y.
Proof.
move=> IH x Px y.
rewrite -leEdual; apply: covers_ind => // {Px y}x y.
by rewrite covers_dual => /IH.
Qed.


(******************************************************************************)
(** * Inhabited types                                                         *)
(******************************************************************************)

HB.mixin Record isInhabited T := { inh_ex : exists x : T, true }.
#[short(type=inhType)]
HB.structure Definition Inhabited := {T of isInhabited T & Choice T}.

HB.factory Record isInhabitedType T := { x : T }.
HB.builders Context T of isInhabitedType T.
HB.instance Definition _ :=  isInhabited.Build T (ex_intro _ x is_true_true).
HB.end.

HB.instance Definition _ := isInhabitedType.Build unit tt.
HB.instance Definition _ := isInhabitedType.Build bool false.
HB.instance Definition _ := isInhabitedType.Build Prop False.
HB.instance Definition _ := isInhabitedType.Build nat 0.
HB.instance Definition _ (n : nat) := isInhabitedType.Build 'I_n.+1 ord0.

HB.instance Definition _ (T : choiceType) :=
  isInhabitedType.Build (option T) None.
HB.instance Definition _ (T : finType) :=
  isInhabitedType.Build {set T} set0.
HB.instance Definition _ (T T' : inhType) :=
  isInhabited.Build (T * T')%type
    (let: ex_intro t _  := @inh_ex T in
     let: ex_intro t' _ := @inh_ex T' in
     ex_intro _ (t, t') is_true_true).

Definition inh {T : inhType} := xchoose (@inh_ex T).

Lemma inh_xchooseE (T : inhType) (exP : exists x0 : T, true) :
  xchoose exP = @inh T.
Proof. exact: eq_xchoose. Qed.

Lemma inh_chooseE (T : inhType) (x0 : T) :
  choose xpredT x0 = @inh T.
Proof.
rewrite /choose; case: insubP => //= [[x Px]] _ /= ->.
by rewrite inh_xchooseE.
Qed.

#[short(type=inhFinType)]
HB.structure Definition InhFinite := { T of isInhabited T & Finite T }.

(******************************************************************************)
(** ** Inhabited ordered types                                                *)
(******************************************************************************)
#[short(type=inhPOrderType)]
HB.structure Definition InhPOrder (d : unit) :=
  {T of isInhabited T & Order.POrder d T}.

#[short(type=inhLatticeType)]
HB.structure Definition InhLattice (d : unit) :=
  {T of isInhabited T & Order.Lattice d T}.

#[short(type=inhTBLatticeType)]
HB.structure Definition InhTBLattice (d : unit) :=
  {T of isInhabited T & Order.TBLattice d T}.

#[short(type=inhOrderType)]
HB.structure Definition InhOrder (d : unit) :=
  {T of isInhabited T & Order.Total d T}.


(******************************************************************************)
(** ** Inhabited finite partially ordered types                               *)
(******************************************************************************)
#[short(type=inhFinPOrderType)]
HB.structure Definition InhFinPOrder (d : unit) :=
  {T of isInhabited T & Order.POrder d T & Finite T}.

#[short(type=inhFinLatticeType)]
HB.structure Definition InhFinLattice (d : unit) :=
  {T of isInhabited T & Order.FinLattice d T}.

#[short(type=inhFinOrderType)]
HB.structure Definition InhFinOrder (d : unit) :=
  {T of isInhabited T & Order.FinTotal d T}.

HB.instance Definition _ := Inhabited.on bool.
HB.instance Definition _ := Inhabited.on nat.
HB.instance Definition _ n := Inhabited.on 'I_n.+1.

Section Dual.
HB.instance Definition _ (T : inhType) :=
  isInhabitedType.Build (Order.dual T) (@inh T).

Variable d : unit.
HB.instance Definition _ (T : inhPOrderType d) := InhPOrder.on (T^d).
HB.instance Definition _ (T : inhLatticeType d) := InhLattice.on (T^d).
HB.instance Definition _ (T : inhTBLatticeType d) := InhTBLattice.on (T^d).
HB.instance Definition _ (T : inhOrderType d) := InhOrder.on (T^d).

HB.instance Definition _ (T : inhFinPOrderType d) := InhFinPOrder.on (T^d).
HB.instance Definition _ (T : inhFinLatticeType d) := InhFinLattice.on (T^d).
HB.instance Definition _ (T : inhFinOrderType d) := InhFinOrder.on (T^d).

End Dual.

(******************************************************************************)
(** * sequences over an ordered types                                        *)
(******************************************************************************)
(** *** Maximum of a sequence *)
Section MaxSeq.

Variables (disp : unit) (T : orderType disp).
Implicit Type a b c : T.
Implicit Type u v : seq T.

Definition maxL a := foldl Order.max a.

Lemma maxLb a u : a <= maxL a u.
Proof using.
elim: u a => //= u0 u IHu a.
apply: (@le_trans _ _ (Order.max a u0)); last exact: IHu.
by rewrite le_max lexx.
Qed.

Lemma in_maxL a u : (maxL a u) \in a :: u.
Proof using.
elim: u a => [| u0 u IHu]//= a; first by rewrite mem_seq1.
case (leP a u0) => H.
+ by have:= H => /max_idPr ->; rewrite in_cons IHu orbT.
+ have:= ltW H => /max_idPl ->; rewrite !in_cons.
  by rewrite orbA [(_ == _) || (_ == _) ]orbC -orbA -in_cons IHu orbT.
Qed.

Lemma maxXL a b u : Order.max a (maxL b u) = maxL (Order.max a b) u.
Proof using. by elim: u b => //= u0 u IHu b; rewrite -maxA; apply: IHu. Qed.

Lemma maxL_cat a u b v : maxL a (u ++ b :: v) = Order.max (maxL a u) (maxL b v).
Proof using.
elim: u a => [| u0 u IHu]/= a; first by rewrite maxXL.
exact: IHu.
Qed.

End MaxSeq.

(** *** Comparison of the elements of a sequence to an element *)
Section AllLeqLtn.

Variables (disp : unit) (T : orderType disp).
Implicit Type a b c : T.
Implicit Type u v : seq T.

Definition allLeq v a := all (<= a) v.
Definition allLtn v a := all (< a) v.

Lemma allLtn_notin s b : allLeq s b -> b \notin s -> allLtn s b.
Proof using.
elim: s => //= s0 s IHs /andP[].
rewrite lt_neqAle => -> {}/IHs Hrec.
by rewrite inE negb_or eq_sym => /andP[->].
Qed.

Lemma maxLPt a u : allLeq u (maxL a u).
Proof using.
rewrite/allLeq; apply/allP => x Hx.
elim: u Hx a => //= u0 u IHu; rewrite inE => /orP[/eqP-> | /IHu Hx] a.
- by rewrite maxC -maxXL le_max lexx.
- exact: Hx.
Qed.
Lemma maxLP a u : allLeq (a :: u) (maxL a u).
Proof using. by rewrite /= (maxLPt a u) (maxLb a u). Qed.

Lemma allLtnW v a : allLtn v a -> allLeq v a.
Proof using. by move/allP=> Hall; apply/allP=> x Hx; apply: ltW; apply: Hall. Qed.

Lemma allLeqE u a : allLeq u a -> maxL a u = a.
Proof using. by elim: u => //= u0 u IHu /andP[/max_idPl-> /IHu]. Qed.
Lemma allLeqP u a : reflect (maxL a u = a) (allLeq u a).
Proof using.
apply: (iffP idP); first exact: allLeqE.
rewrite/allLeq; elim: u a => //= u0 u IHu a.
rewrite maxC -maxXL => Hmax.
have Hu : maxL a u = a.
  by apply le_anti; rewrite maxLb andbT -{2}Hmax le_max lexx orbT.
by rewrite -{1}Hmax le_max lexx /= IHu.
Qed.

Lemma allLeqCons b u a : b <= a -> allLeq u a -> allLeq (b :: u) a.
Proof using.
move=> Hb /allP Hall; apply/allP => x.
by rewrite inE => /orP[/eqP-> //|] /Hall.
Qed.
Lemma allLtnCons b u a : b < a -> allLtn u a -> allLtn (b :: u) a.
Proof using.
move=> Hb /allP Hall; apply/allP => x.
by rewrite inE => /orP[/eqP-> //|] /Hall.
Qed.

Lemma allLeqConsE u a b : allLeq (b :: u) a = (maxL b u <= a).
Proof using.
elim: u b => [| u0 u IHu]/= b; first by rewrite andbT.
by rewrite maxC -maxXL ge_max -IHu /= !andbA [(u0 <= a) && (b <= a)]andbC.
Qed.

Lemma allLtnConsE u a b : allLtn (b :: u) a = (maxL b u < a).
Proof using.
elim: u b => [| u0 u IHu]/= b; first by rewrite andbT.
by rewrite maxC -maxXL gt_max -IHu /= !andbA [(u0 < a) && (b < a)]andbC.
Qed.

Lemma allLeq_consK b u a : allLeq (b :: u) a -> allLeq u a.
Proof using.
move/allP => Hall; apply/allP => x Hx; apply: Hall.
by rewrite inE Hx orbT.
Qed.
Lemma allLtn_consK b u a : allLtn (b :: u) a -> allLtn u a.
Proof using.
move/allP => Hall; apply/allP => x Hx; apply: Hall.
by rewrite inE Hx orbT.
Qed.

Lemma allLeq_catE u v a : allLeq (u ++ v) a = allLeq u a && allLeq v a.
Proof using. by rewrite /allLeq all_cat. Qed.
Lemma allLtn_catE u v a : allLtn (u ++ v) a = allLtn u a && allLtn v a.
Proof using. by rewrite /allLtn all_cat. Qed.

Lemma maxL_perm a u b v : perm_eq (a :: u) (b :: v) -> maxL a u = maxL b v.
Proof using.
move/permP => Hperm.
have {}Hperm : forall x, (x \in (a :: u)) = (x \in (b :: v)).
  move=> x; move/(_ (xpred1 x)) : Hperm => Hperm.
  by apply/idP/idP => /count_memPn H; apply/count_memPn;
    rewrite ?Hperm // -?Hperm.
apply/eqP; rewrite eq_le; apply/andP; split.
- move/(_ (maxL a u)) : Hperm; rewrite (in_maxL a u) => /esym Hin.
  exact: (allP (maxLP b v)).
- move/(_ (maxL b v)) : Hperm; rewrite (in_maxL b v) => /esym Hin.
  exact: (allP (maxLP a u)).
Qed.

Lemma perm_allLeq u v a : perm_eq u v -> allLeq u a -> allLeq v a.
Proof using.
move=> Hperm /allLeqP; rewrite (maxL_perm (b := a) (v := v)).
- by move=> Hall; apply/allLeqP.
- by rewrite perm_cons.
Qed.
Lemma perm_allLeqE u v a : perm_eq u v -> allLeq u a = allLeq v a.
Proof using.
move=> H; apply/idP/idP; apply: perm_allLeq; first by [].
by rewrite perm_sym.
Qed.
Lemma perm_allLtn u v a : perm_eq u v -> allLtn u a -> allLtn v a.
Proof using.
move=> Hperm /allP Hall; apply/allP => X Hx.
by apply: Hall; rewrite (perm_mem Hperm).
Qed.
Lemma perm_allLtnE u v a : perm_eq u v -> allLtn u a = allLtn v a.
Proof using.
move=> H; apply/idP/idP; apply: perm_allLtn; first by [].
by rewrite perm_sym.
Qed.

Lemma allLeq_rev u a : allLeq (rev u) a = allLeq u a.
Proof using. by apply: perm_allLeqE; rewrite perm_rev. Qed.
Lemma allLtn_rev u a : allLtn (rev u) a = allLtn u a.
Proof using. by apply: perm_allLtnE; rewrite perm_rev. Qed.

Lemma allLeq_rconsK b u a : allLeq (rcons u b) a -> allLeq u a.
Proof using.
rewrite -allLeq_rev rev_rcons => /allLeq_consK.
by rewrite allLeq_rev.
Qed.
Lemma allLtn_rconsK b u a : allLtn (rcons u b) a -> allLtn u a.
Proof using.
rewrite -allLtn_rev rev_rcons => /allLtn_consK.
by rewrite allLtn_rev.
Qed.

Lemma allLeq_last b u a : allLeq (rcons u b) a -> b <= a.
Proof using. by rewrite -allLeq_rev rev_rcons /= => /andP[]. Qed.
Lemma allLtn_last b u a : allLtn (rcons u b) a -> b < a.
Proof using. by rewrite -allLtn_rev rev_rcons /= => /andP[]. Qed.


Lemma maxL_LbR a v L b R :
  a :: v = L ++ b :: R -> allLeq L b -> allLeq R b -> maxL a v = b.
Proof using.
rewrite /allLeq /maxL => Heq HL Hr.
apply/eqP; rewrite eq_le; apply/andP; split.
- have: all (<= b) (a :: v) by rewrite Heq all_cat HL /= lexx Hr.
  by move/allP => Hallv; apply: Hallv; exact: in_maxL.
- have:= maxLP a v => /allP; rewrite Heq; apply.
  by rewrite mem_cat inE eq_refl /= orbT.
Qed.

End AllLeqLtn.


(** *** Removing the largest letter of a sequence *)
Section RemoveBig.

Variables (disp : unit) (T : orderType disp).
Variable Z : T.
Implicit Type a b c : T.
Implicit Type u v w r : seq T.

(** Remove the last occurence of the largest letter from w *)
Fixpoint rembig w :=
  if w is a :: v then
    if allLtn v a then v else a :: rembig v
  else [::].

(** Position of the last occurence of the largest letter of w *)
Fixpoint posbig w :=
  if w is a :: v then
    if allLtn v a then 0 else (posbig v).+1
  else 0.

Lemma size_rembig w : size (rembig w) = (size w).-1.
Proof using.
elim: w => //= a w IHw.
case: w IHw => [//= | b w'] IHw.
by case (allLtn (b :: w') a); rewrite //= IHw.
Qed.

Lemma rembig_catR a u b v :
  maxL a u <= maxL b v -> rembig (a :: u ++ b :: v) = a :: u ++ rembig (b :: v).
Proof using.
rewrite /=; elim: u a => [| u0 u IHu] a.
  by rewrite allLtnConsE /= leNgt /= => /negbTE ->.
rewrite allLtnConsE maxL_cat /= -maxXL ge_max => /andP[Ha Hmax].
by rewrite ltNge le_max Ha orbT /= -(IHu _ Hmax).
Qed.

Lemma rembig_catL a u b v :
  maxL a u > maxL b v -> rembig (a :: u ++ b :: v) = rembig (a :: u) ++ b :: v.
Proof using.
rewrite /=; elim: u a => [| u0 u IHu] a.
  by rewrite allLtnConsE /= ltNge /= => /negbTE ->.
rewrite allLtn_catE !allLtnConsE /= -maxXL maxC /Order.max.
case: (ltP (maxL u0 u) a) => [H -> //= | H Hmax /=].
by rewrite IHu.
Qed.

Lemma rembig_cat u v :
  rembig (u ++ v) = (rembig u) ++ v \/ rembig (u ++ v) = u ++ (rembig v).
Proof using.
case: u => [/= | a u]; first by right.
case: v => [/= | b v]; first by rewrite !cats0; left.
case (leP (maxL a u) (maxL b v)) => Hcase.
- by rewrite (rembig_catR Hcase); right.
- by rewrite (rembig_catL Hcase); left.
Qed.

Lemma rembig_eq_permL u1 u2 v :
  perm_eq u1 u2 ->
  (rembig (u1 ++ v) = (rembig u1) ++ v /\
   rembig (u2 ++ v) = (rembig u2) ++ v)
  \/
  (rembig (u1 ++ v) = u1 ++ (rembig v) /\
   rembig (u2 ++ v) = u2 ++ (rembig v)).
Proof using.
case: u2 => [| a2 u2]; first by move/perm_size => /eqP /= /nilP ->; right.
case: u1 => [| a1 u1]; first by move/perm_size.
case: v => [/= | b v]; first by rewrite /= !cats0; left.
move/maxL_perm => Heq.
case (leP (maxL a1 u1) (maxL b v)) => H1; have := H1; rewrite Heq => H2.
- by right; rewrite (rembig_catR H1) (rembig_catR H2).
- by left;  rewrite (rembig_catL H1) (rembig_catL H2).
Qed.

Lemma rembig_eq_permR u v1 v2 :
  perm_eq v1 v2 ->
  (rembig (u ++ v1) = (rembig u) ++ v1 /\
   rembig (u ++ v2) = (rembig u) ++ v2)
  \/
  (rembig (u ++ v1) = u ++ (rembig v1) /\
   rembig (u ++ v2) = u ++ (rembig v2)).
Proof using.
case: v2 => [| b2 v2].
  by move/perm_size => /eqP /= /nilP ->; left; rewrite !cats0.
case: v1 => [//= | b1 v1]; first by move/perm_size.
case: u => [//= | a u]; first by right.
move/maxL_perm => Heq.
case (leP (maxL a u) (maxL b1 v1)) => H1; have := H1; rewrite Heq => H2.
- by right; rewrite (rembig_catR H1) (rembig_catR H2).
- by left;  rewrite (rembig_catL H1) (rembig_catL H2).
Qed.

Lemma rembigP w wb : wb != [::] ->
  reflect
    (exists u b v, [/\ w = u ++ v, wb = u ++ b :: v, allLeq u b & allLtn v b])
    (w == rembig wb).
Proof using.
move=> Hwb; apply: (iffP idP).
- elim: wb Hwb w => [| w0 wb IHwb _] //= w.
  case H : (allLtn wb w0) => /eqP->{w}.
  + by exists [::], w0, wb; rewrite H !cat0s; split.
  + have Hwb : wb != [::] by move: H; case wb.
    move Hw : (rembig wb) => w.
    move: Hw => /esym/eqP/(IHwb Hwb w) [u] [b] [v] [Hcatw Hcatwb Hub Hvb].
    exists (w0 :: u), b, v; split.
    * by rewrite Hcatw.
    * by rewrite Hcatwb.
    * move: H; rewrite Hcatwb /= Hub andbT => /negbT.
      apply: contraR; rewrite -ltNge => Hb.
      rewrite allLtn_catE /= Hb /=; apply/andP; split.
      + move: Hub => /allP /= Hub; apply/allP => x Hx /=.
        exact: (le_lt_trans (Hub x Hx)).
      + move: Hvb => /allP /= Hvb; apply/allP => x Hx /=.
        exact: (lt_trans (Hvb x Hx)).
    * exact: Hvb.
- move=> [u] [b] [v] [] {Hwb}.
  elim: u w wb => [w wb -> -> _ /= -> // | u0 u IHu].
  move=> w wb ->{w} ->{wb} Hleqb Hltnb /=.
  move Hw : (u ++ v) => w; move: Hw => /esym Hw.
  move Hwb : (u ++ b :: v) => wb; move: Hwb => /esym => Hwb.
  have:= IHu _ _ Hw Hwb (allLeq_consK Hleqb) Hltnb => /eqP ->.
  rewrite allLeqConsE in Hleqb.
  have:= le_trans (maxLb u0 u) Hleqb; rewrite {2}Hwb.
  case H : (allLtn (u ++ b :: v) u0) => //=.
  move: H; rewrite allLtn_catE allLtnConsE => /andP[_].
  move/(le_lt_trans (maxLb _ _)) => H1 H2.
  by have:= lt_le_trans H1 H2; rewrite ltxx.
Qed.

Lemma perm_rembig u v :
  perm_eq u v -> perm_eq (rembig u) (rembig v).
Proof using.
case Hu: u => [/= | u0 u']; case Hv: v => [//= | v0 v'].
- by move=> /perm_size /=.
- by move=> /perm_size /=.
move=> Hperm; have Hmax:= maxL_perm Hperm; move: Hmax Hperm.

have/(congr1 rembig):= Hu => /eqP/rembigP Htmp.
have {}/Htmp : u0 :: u != [::] by [].
move=> [u1] [bu] [u2] []; rewrite {1}Hu => -> Hub Hlequ Hltnu.
rewrite (maxL_LbR Hub Hlequ (allLtnW Hltnu)) {Hlequ Hltnu}.
rewrite Hub {u Hu Hub u0 u'}.

have/(congr1 rembig):= Hv => /eqP/rembigP Htmp.
have {}/Htmp : v0 :: v != [::] by [].
move=> [v1] [bv] [v2] []; rewrite {1}Hv => -> Hvb Hleqv Hltnv.
rewrite (maxL_LbR Hvb Hleqv (allLtnW Hltnv)) {Hleqv Hltnv}.
rewrite Hvb {v Hv Hvb v0 v'}.

rename bv into mx; move ->.
rewrite -[mx :: u2]cat1s -[mx :: v2]cat1s.
rewrite -[perm_eq (u1 ++ u2) _](perm_cons mx).
have Hlemma u v : perm_eq (u ++ [:: mx] ++ v) (mx :: u ++ v).
  rewrite catA -[mx :: u ++ v]/((mx :: u) ++ v) perm_cat2r -[mx :: u]cat1s.
  apply: permEl; exact: perm_catC.
move=> H; have:= Hlemma u1 u2; rewrite perm_sym.
move/perm_trans; apply.
by apply: (perm_trans H); apply: Hlemma.
Qed.

Lemma rembig_rev_uniq s : uniq s -> rev (rembig s) = rembig (rev s).
Proof using.
case: (s =P [::]) => [-> //= |].
move=> /eqP/rembigP/(_ (eq_refl (rembig s))) [u] [b] [v] [] -> -> Hu Hb.
rewrite -rev_uniq !rev_cat rev_cons -cats1 -catA cat1s.
rewrite cat_uniq => /and3P[_ _ /= /andP[]].
rewrite mem_rev => Hbu _.
apply/eqP/rembigP; first by case: (rev v).
exists (rev v), b, (rev u); split => //.
- by rewrite allLeq_rev; apply: allLtnW.
- by rewrite allLtn_rev; apply: allLtn_notin.
Qed.

Lemma rembig_subseq s : subseq (rembig s) s.
Proof using.
elim: s => //= s0 s IHs.
case: allLtn; last by rewrite eq_refl.
case: s {IHs} => [//| s1 s].
by case: eqP => _; [apply: subseq_cons | apply: subseq_refl].
Qed.

Lemma rembig_uniq s : uniq s -> uniq (rembig s).
Proof using. by apply: subseq_uniq; apply: rembig_subseq. Qed.

Open Scope nat_scope.

Lemma posbig_size_cons l s : posbig (l :: s) < size (l :: s).
Proof using.
elim H : s l => [//= | s0 s' IHs] l; rewrite -H /=.
by case (allLtn s l); rewrite // H ltnS; apply: IHs.
Qed.

Lemma posbig_size s : s != [::] -> posbig s < size s.
Proof using. by case: s => //= s l _; apply: posbig_size_cons. Qed.

Lemma posbigE u b v :
  (allLeq u b && allLtn v b) = (posbig (u ++ b :: v) == size u).
Proof using.
apply/andP/idP => [[Hu Hv]|].
- elim: u Hu => [| u0 u IHu] /=; first by rewrite Hv.
  move=> /andP[Hub Hall]; rewrite allLtn_catE /= ltNge Hub andbF eqSS.
  exact: IHu.
- elim: u => [/= | u0 u /= IHu]; first by case (allLtn v b).
  case/boolP: (allLtn (u ++ b :: v) u0) => [| Hall] //=.
  rewrite eqSS => {}/IHu [Hub Hvb].
  split; last exact: Hvb.
  rewrite Hub andbT.
  move: Hall; apply: contraR; rewrite -ltNge => H.
  rewrite allLtn_catE /= H /=.
  apply/andP; split; apply/allP => x.
  + by move: Hub => /allP/[apply] /= H1; apply: (le_lt_trans H1 H).
  + by move: Hvb => /allP/[apply] /= H1; apply: (lt_trans H1 H).
Qed.

Lemma posbig_take_dropE l s :
  take (posbig (l :: s)) (rembig (l :: s)) ++
     maxL l s
     :: drop (posbig (l :: s)) (rembig (l :: s)) = l :: s.
Proof using.
elim Hs : s l => [// | s0 s' IHs] l; rewrite -Hs /=.
case/boolP: (allLtn s l) => Hl /=.
- by rewrite take0 drop0 /=; have:= (allLtnW Hl) => /allLeqE ->.
- move: Hl; rewrite Hs allLtnConsE -leNgt /= -maxXL => /max_idPr ->.
  by rewrite (IHs s0).
Qed.

Lemma nth_posbig l s : nth Z (l :: s) (posbig (l :: s)) = maxL l s.
Proof using.
rewrite /=; case: (boolP (allLtn s l)).
- by move/allLtnW/allLeqP => ->.
- elim Hs : s l => [| s0 s' IHs] //= l.
  rewrite maxC /Order.max.
  case: (ltP s0 l) => Hl /= H.
  + rewrite -(IHs l H).
    suff -> : allLtn s' s0 = false by [].
    apply: negbTE; move: H; apply: contra; apply: sub_all => i /= Hi.
    exact: (lt_trans Hi).
  + case/boolP: (allLtn s' s0) => /= [|Hs0].
    * by move /allLtnW/allLeqP ->.
    * exact: (IHs s0 Hs0).
Qed.

Lemma allLeq_posbig l s :
  allLeq (take (posbig (l :: s)) (l :: s)) (maxL l s).
Proof using.
have:= maxLP l s; rewrite -{1}[l :: s](cat_take_drop (posbig (l :: s))).
by rewrite allLeq_catE => /andP[].
Qed.

Lemma allLtn_posbig l s :
  allLtn (drop (posbig (l :: s)).+1 (l :: s)) (maxL l s).
Proof using.
elim Hs : s l => [// | s0 s'] IHs l; rewrite -Hs /=.
move/(_ (Order.max l s0)) : IHs; rewrite /= maxC /Order.max.
case: (ltP s0 l) => Hs0; rewrite Hs /=.
- rewrite Hs0 /=; have:= ltW Hs0 => /max_idPl ->.
  case (boolP (allLtn s' l)) => Hall.
  + rewrite drop0 /= => ->.
    have /allLeqE -> := allLtnW Hall.
    by rewrite Hs0.
  + suff -> : allLtn s' s0 = false by [].
    apply: negbTE; move: Hall; apply: contra; apply: sub_all => i /= Hi.
    exact: (lt_trans Hi).
- rewrite ltNge Hs0 /=.
  by move: Hs0 => /max_idPr ->.
Qed.

Lemma rembigE l s :
  take (posbig (l :: s)) (l :: s) ++
       drop (posbig (l :: s)).+1 (l :: s) = rembig (l :: s).
Proof using Z.
apply/eqP/rembigP; first by [].
set ss := l :: s; set pos := posbig (l :: s).
exists (take pos ss), (nth Z ss pos), (drop pos.+1 ss); split.
- by [].
- rewrite [X in _ ++ X](_ : _ = drop pos ss) ?cat_take_drop //.
  rewrite /ss /pos /= {ss pos}.
  elim H : s => [//= | s0 s']; rewrite -H.
  case (boolP (allLtn s l)) => Hmax /=; first by rewrite drop0.
  move: Hmax; rewrite H => Hmax /=.
  case (boolP (allLtn s' s0)) => Hmax0 /=; first by rewrite drop0.
  suff -> : allLtn s' l = false by [].
  apply: negbTE; move: Hmax; apply: contra => /= Hmax.
  apply: allLtnCons; last exact Hmax.
  case: s' Hmax0 Hmax {H} => [//= | s1 s']; rewrite !allLtnConsE.
  by rewrite -leNgt; apply: le_lt_trans.
- by rewrite /ss /pos {ss pos} nth_posbig; apply: allLeq_posbig.
- by rewrite /ss /pos {ss pos} nth_posbig; apply: allLtn_posbig.
Qed.

Lemma nth_lt_posbig i s : i < posbig s -> nth Z (rembig s) i = nth Z s i.
Proof using.
  case H : s => [//= | s0 s'] => Hi.
  rewrite -rembigE -H -{5}[s](cat_take_drop (posbig s)) !nth_cat.
  by rewrite size_take posbig_size H //= Hi.
Qed.

Definition shift_pos    pos i := if i < pos then i else i.+1.
Definition shiftinv_pos pos i := if i < pos then i else i.-1.

Lemma shift_posK pos i : shiftinv_pos pos (shift_pos pos i) = i.
Proof using.
rewrite /shift_pos /shiftinv_pos.
case (ltnP i pos) => [-> // | Hi].
by rewrite ltnNge (leq_trans Hi (leqnSn _)).
Qed.

Lemma shiftinv_posK pos i : i != pos -> shift_pos pos (shiftinv_pos pos i) = i.
Proof using.
rewrite /shift_pos /shiftinv_pos => Hipos.
case (ltnP i pos) => [-> // | Hi].
case: i Hipos Hi => [| i] /=.
- move=> H1 H2; exfalso.
  move: H2; rewrite leqn0 => /eqP H.
  by rewrite H in H1.
- rewrite ltnNge => H1 H2.
  rewrite eq_sym in H1.
  by rewrite -ltnS ltn_neqAle H1 H2 /=.
Qed.

Lemma nth_rembig s i :
  nth Z s (shift_pos (posbig s) i) = nth Z (rembig s) i.
Proof using.
case Hs : s => [//= | s0 s'].
rewrite /shift_pos -rembigE nth_cat -Hs.
rewrite size_take posbig_size; last by rewrite Hs.
case (ltnP i (posbig s)) => Hipos.
- by rewrite nth_take.
- by rewrite nth_drop addSn subnKC.
Qed.

Lemma nth_inspos s pos i n :
  pos <= size s ->
  nth Z ((take pos s) ++ n :: (drop pos s)) i =
  if i == pos then n else nth Z s (shiftinv_pos pos i).
Proof using.
move=> Hpos.
case: (i =P pos) => [->{i} | /eqP Hipos].
  by rewrite nth_cat size_takel // ltnn subnn.
rewrite /shiftinv_pos nth_cat size_take.
case (ltnP pos (size s)) => [{}Hpos | Hpos2].
- case: (ltnP i pos) => Hi; first by rewrite (nth_take _ Hi).
  have {Hipos}Hi : pos < i by rewrite ltn_neqAle eq_sym Hipos Hi.
  case: i Hi => //= i; rewrite ltnS => Hi.
  by rewrite (subSn Hi) /= nth_drop (subnKC Hi).
- have {Hpos2}Hpos : pos = size s by apply anti_leq; rewrite Hpos Hpos2.
  subst pos.
  case: (ltnP i (size s)) => Hisz; first by rewrite (nth_take _ Hisz).
  have {Hipos Hisz} : size s < i by rewrite ltn_neqAle eq_sym Hisz Hipos.
  case: i => //= i; rewrite ltnS => Hi.
  by rewrite (subSn Hi) /= nth_drop (subnKC Hi).
Qed.

Lemma shift_pos_mono pos : {mono shift_pos pos : i j / i <= j}.
Proof using.
rewrite /shift_pos => i j; case (ltnP j pos) => Hj.
- case (leqP i j) => Hij; first by rewrite (leq_ltn_trans Hij Hj) Hij.
  rewrite leqNgt (leq_trans Hij) //.
  by case: ltnP.
- case (leqP i j) => Hij.
    by rewrite (leq_trans (n := i.+1)) //; case ltnP.
  rewrite ltnNge (ltnW (leq_ltn_trans Hj Hij)) /=.
  by rewrite ltnNge Hij.
Qed.

Lemma shiftinv_pos_homo pos : {homo shiftinv_pos pos : i j / i <= j}.
Proof using.
move=> i j Hij; rewrite /shiftinv_pos; case (ltnP j pos) => Hj.
- by rewrite (leq_ltn_trans Hij Hj).
- case (ltnP i pos) => Hi.
  + by have:= leq_trans Hi Hj; case j.
  + by case: i Hij {Hj Hi} => //= i; case: j.
Qed.

End RemoveBig.

Prenex Implicits rembig posbig.

Lemma maxL_iota n i : maxL i (iota i.+1 n) = i + n.
Proof.
elim: n i => [|n IHn] i /=; first by rewrite addn0.
by rewrite /Order.max ltEnat /= ltnSn IHn addSnnS.
Qed.

Lemma maxL_iota_n n : maxL 0%N (iota 1 n) = n.
Proof. by rewrite -{2}[n]add0n maxL_iota. Qed.

Lemma rembig_iota n i : rembig (iota i n.+1) = iota i n.
Proof.
elim: n i => //= n IHn i.
move/(_  i.+1) : IHn => /= ->.
by rewrite ltEnat /= ltnNge leqnSn.
Qed.
