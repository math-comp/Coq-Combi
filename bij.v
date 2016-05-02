Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial.

Set Implicit Arguments.
Unset Strict Implicit.

Section BijSlicedSet.

Variable I : eqType.

Record sliced_set := SlicedSet { carrier :> finType;
                                 elt : carrier;
                                 slset : {set carrier};
                                 stat : carrier -> I }.

Definition slice S v := [set x | x in slset S & stat x == v].

Lemma mem_slice S x : x \in slset S -> x \in slice S (stat x).
Proof.
  move=> Hx; apply/imsetP; exists x => //.
  by rewrite inE Hx /=.
Qed.

Definition bij (U V : sliced_set) (x : U) : V :=
  nth (elt V) (enum (slice V (stat x))) (index x (enum (slice U (stat x)))).

Section Defs.

Variable U V : sliced_set.
Hypothesis HcardEq : forall i, #|slice U i| = #|slice V i|.

Lemma bij_in_slice x : x \in (slset U) -> bij V x \in slice V (stat x).
Proof.
  move=> Hx; rewrite -mem_enum; apply mem_nth.
  rewrite -cardE -HcardEq cardE index_mem mem_enum; exact: mem_slice.
Qed.

Lemma slset_bij x : x \in (slset U) -> bij V x \in slset V.
Proof.
  by move=> /bij_in_slice /imsetP [x0]; rewrite inE => /andP [] Hx0 _ ->.
Qed.

Lemma equi_bij x : x \in (slset U) -> stat (s := V) (bij V x) = stat (s := U) x.
Proof.
  move=> /bij_in_slice.
  by move=> /imsetP [im0]; rewrite inE => /andP [_ /eqP <- ->].
Qed.

Lemma bijK : {in slset U, cancel (bij V) (bij U)}.
Proof.
  move=> x Hx.
  have : index (bij V x) (enum (slice V (stat x))) =
         index x         (enum (slice U (stat x))).
    rewrite index_uniq //; last exact: enum_uniq.
    rewrite -cardE -HcardEq cardE index_mem mem_enum; exact: mem_slice.
  rewrite /bij (equi_bij Hx) => ->.
  apply nth_index.
  rewrite mem_enum; exact: mem_slice.
Qed.

Lemma inj_bij : {in slset U &, injective (bij V)}.
Proof. exact: can_in_inj bijK. Qed.

End Defs.

Lemma surj_bij (U V : sliced_set) :
  (forall i, #|slice U i| = #|slice V i|) ->
  [set bij V x | x in slset U] = slset V.
Proof.
  rewrite -setP => HcardEq y.
  apply/imsetP/idP => [[x Hx] -> {y} | Hy].
  - exact: slset_bij.
  - exists (bij U y); first exact: slset_bij.
    by rewrite bijK //.
Qed.

Lemma bijP (U V : sliced_set) :
  (forall i, #|slice U i| = #|slice V i|) ->
  [/\ {in slset U &, injective (bij V)},
   [set bij V x | x in slset U] = slset V &
   {in slset U, forall x, stat (bij V x) = stat x} ].
Proof. split; [exact: inj_bij | exact: surj_bij | exact: equi_bij]. Qed.

End BijSlicedSet.
