Add Rec LoadPath "../Combi/LRrule".

Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop ssrint rat ssralg ssrnum.
Require Import tools combclass partition yama stdtab.

Set Implicit Arguments.
Unset Strict Implicit.

Section RecYama.

  Definition decr_nth_part_def (p : seq nat) i : (seq nat) :=
    if is_out_corner p i then decr_nth p i
    else p.

  Lemma is_part_decr_nth_part (p : intpart) i :
    is_part (decr_nth_part_def p i).
  Proof.
    rewrite /decr_nth_part_def.
    case: (boolP (is_out_corner p i)).
    - apply is_part_decr_nth; exact: intpartP.
    - move=> _; exact: intpartP.
  Qed.

  Definition decr_nth_part (p : intpart) i  : intpart :=
    IntPart (is_part_decr_nth_part p i).

  Lemma decr_nth_partE (p : intpart) i :
    is_out_corner p i -> decr_nth_part p i = decr_nth p i :> seq nat.
  Proof.
    rewrite /decr_nth_part /decr_nth_part_def /=.
    by case: (is_out_corner p i).
  Qed.

  Lemma card_yama_rec (p : intpart) :
    (p != [::] :> seq nat) ->
    #|yameval_finType p| =
    \sum_(i <- out_corners p)
      #|yameval_finType (decr_nth_part p i)|.
  Proof.
    move=> H.
    rewrite cardE enumT unlock /= -(size_map val) subType_seqP.
    rewrite /enum_yameval.
    move Hn : (sumn p) => n.
    case: n Hn => [| n'] Hn' /=.
      exfalso; move: H.
      by rewrite (part0 (intpartP p) Hn').
    rewrite size_flatten /shape sumn_map_condE.
    rewrite /out_corners -!map_comp.
    congr sumn; apply eq_in_map => i /=.
    rewrite mem_filter => /andP [] Hcorn _.
    rewrite size_map.
    rewrite cardE enumT unlock /= -(size_map val) subType_seqP /=.
    rewrite /enum_yameval /= /decr_nth_part_def /= Hcorn.
    by rewrite (sumn_decr_nth (intpartP p) Hcorn) Hn' /=.
  Qed.

  Definition empty_part := IntPart (pval := [::]) is_true_true.

  Lemma card_yama0 :
    #|yameval_finType empty_part| = 1.
  Proof.
    by rewrite cardE enumT unlock -(size_map val) subType_seqP.
  Qed.

  Lemma card_yam_stdtabE (p : intpart) :
    #|yameval_finType p| = #|stdtabsh_finType p|.
  Proof.
    rewrite /stdtabsh_finType /= !cardE !enumT /= unlock /= -(size_map val) subType_seqP.
    rewrite size_pmap_sub.
    suff : all (is_stdtab_of_shape p) (enum_stdtabsh p).
      by rewrite all_count => /eqP ->; rewrite size_map.
    rewrite /enum_stdtabsh; apply/allP => t /mapP [] y Hy -> {t}.
    have /allP Hall := enum_yamevalP (intpartP p).
    have {Hy Hall} := Hall _ Hy.
-    rewrite /is_yam_of_eval /is_stdtab_of_shape /= => /andP [] /stdtab_of_yamP -> /=.
    move=> /eqP <-.
    by rewrite shape_stdtab_of_yam.
  Qed.

  Lemma intpart_out_corner_ind (f : intpart -> Type) :
    f empty_part ->
    ( forall p : intpart,
        (p != [::] :> seq nat) ->
        (forall i, is_out_corner p i -> f (decr_nth_part p i) ) -> f p ) ->
    ( forall p : intpart, f p).
  Proof.
    move=> H0 Hrec p.
    move Hp : (sumn p) => n.
    elim: n p Hp => [| n IHn] p Hp.
      suff -> : p = empty_part by exact H0.
      apply val_inj => /=; exact: (part0 (intpartP p) Hp).
    have Hnnil : p != [::] :> seq nat.
      move: Hp => /eqP; by apply contraL => /eqP ->.
    apply (Hrec p Hnnil) => i Hi.
    apply IHn.
    rewrite /decr_nth_part /decr_nth_part_def /= Hi.
    by rewrite (sumn_decr_nth (intpartP p) Hi) Hp.
  Qed.

  Lemma part_out_corner_ind (f : seq nat -> Type) :
    f [::] ->
    ( forall p, is_part p ->
        (p != [::]) ->
        (forall i, is_out_corner p i -> f (decr_nth p i) ) -> f p ) ->
    ( forall p, is_part p -> f p).
  Proof.
    move=> H0 Hrec p Hp.
    move Htmp : (IntPart Hp) => pdep.
    have -> : p = pdep by rewrite -Htmp.
    elim/intpart_out_corner_ind: pdep {p Hp Htmp} => [| p Hp IHp] //=.
    apply (Hrec p (intpartP p) Hp) => i Hi.
    have /= := (IHp i Hi).
    by rewrite /decr_nth_part_def Hi.
  Qed.

  Lemma card_stdtabsh_rec (f : intpart -> nat) :
    f empty_part = 1 ->
    ( forall p : intpart,
        (p != [::] :> seq nat) ->
        f p = \sum_(i <- out_corners p) f (decr_nth_part p i) ) ->
    ( forall p : intpart, f p = #|stdtabsh_finType p| ).
  Proof.
    move=> H0 Hrec.
    elim/intpart_out_corner_ind => [//= | p Hnnil IHp] /=.
      by rewrite H0 -card_yam_stdtabE card_yama0.
    rewrite (Hrec _ Hnnil) -card_yam_stdtabE (card_yama_rec Hnnil).
    rewrite /out_corners !big_filter; apply eq_bigr => i Hi.
    by rewrite card_yam_stdtabE IHp //=.
  Qed.

  Require Import rat_coerce.
  Import GRing.Theory.
  Import Num.Theory.

  Open Scope ring_scope.

  Lemma card_stdtabsh_rat_rec (f : intpart -> rat) :
    f empty_part = 1 ->
    ( forall p : intpart,
        (p != [::] :> seq nat) ->
        f p = \sum_(i <- out_corners p) f (decr_nth_part p i) ) ->
    ( forall p : intpart, f p = #|stdtabsh_finType p| ).
  Proof.
    move=> H0 Hrec.
    elim/intpart_out_corner_ind => [//= | p Hnnil IHp] /=.
      by rewrite H0 -card_yam_stdtabE card_yama0.
    rewrite (Hrec _ Hnnil) -card_yam_stdtabE (card_yama_rec Hnnil).
    rewrite (big_morph Posz PoszD (id1 := Posz O%N)) //.
    rewrite (big_morph int_to_rat int_to_ratD (id1 := 0)) //.
    rewrite /out_corners !big_filter; apply eq_bigr => i Hi.
    by rewrite card_yam_stdtabE IHp //=.
Qed.

End RecYama.
