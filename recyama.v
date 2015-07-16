Add Rec LoadPath "Coq-Combi/LRrule".

Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop.
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
    rewrite /is_yam_of_eval /is_stdtab_of_shape /= => /andP [] /stdtab_of_yamP -> /=.
    move=> /eqP <-.
    by rewrite shape_stdtab_of_yam.
  Qed.

  Lemma part_out_corner_ind (f : intpart -> nat) :
    f empty_part = 1 ->
    ( forall p : intpart,
        (p != [::] :> seq nat) ->
        f p = \sum_(i <- out_corners p) f (decr_nth_part p i) ) ->
    ( forall p : intpart, f p = #|stdtabsh_finType p| ).
  Proof.
    move=> H0 Hrec p.
    move Hp : (sumn p) => n.
    elim: n p Hp => [| n IHn] p Hp.
      suff -> : p = empty_part by rewrite H0 -card_yam_stdtabE card_yama0.
      apply val_inj => /=; exact: (part0 (intpartP p) Hp).
    have Hnnil : p != [::] :> seq nat.
      move: Hp => /eqP; by apply contraL => /eqP ->.
    rewrite (Hrec _ Hnnil) -card_yam_stdtabE (card_yama_rec Hnnil).
    rewrite /out_corners !big_filter; apply eq_bigr => i Hi.
    rewrite card_yam_stdtabE IHn //=.
    rewrite /decr_nth_part_def Hi (sumn_decr_nth (intpartP p) Hi).
    by rewrite Hp.
  Qed.

End RecYama.
