Add Rec LoadPath "Coq-Combi/LRrule".

Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop.
Require Import tools combclass partition yama.

Set Implicit Arguments.
Unset Strict Implicit.

Section BLa.

  Definition decr_nth_part (p : intpart) i : intpart :=
    if Sumbool.sumbool_of_bool (is_out_corner p i) is left pf then
      IntPart (is_part_decr_nth (intpartP p) pf)
    else p.

  Definition decr_nth_part (p : intpart) i : intpart :=
    if (boolP (is_out_corner p i)) is AltTrue pf then
      IntPart (is_part_decr_nth (intpartP p) pf)
    else p.

  Lemma bla (A B : Type) (f : A -> B) (C : Prop) b1 b2 (X : alt_spec C b1 b2) ptrue pfalse:
    f (match X with
         | AltTrue pf => ptrue pf
         | AltFalse pf => pfalse pf
       end) =
    match X with
      | AltTrue pf => f (ptrue pf)
      | AltFalse pf => f (pfalse pf)
    end.
  Proof. by case: X. Qed.

  Lemma decr_nth_partE (p : intpart) i :
    is_out_corner p i -> decr_nth_part p i = decr_nth p i :> seq nat.
  Proof.
    rewrite /decr_nth_part bla /=.
    case: (is_out_corner p i) => //= _.
    

  Qed.

  Lemma card_yama_rec (p : intpart) :
    (p != [::] :> seq nat) ->
    #|yameval_finType p| =
    sumn [seq #|yameval_finType (decr_nth_part p i)|  | i <- out_corners p ].
  Proof.
    move=> H.
    rewrite cardE enumT unlock /= -(size_map val) subType_seqP.
    rewrite /enum_yameval.
    move Hn : (sumn p) => n.
    case: n Hn => [| n'] Hn' /=.
      exfalso; move: H.
      by rewrite (part0 (intpartP p) Hn').
    rewrite size_flatten /shape.
    rewrite /out_corners -map_comp.
    congr sumn; apply eq_in_map => i /=.
    rewrite mem_filter => /andP [] Hcorn _.
    rewrite size_map.
    rewrite cardE enumT unlock /= -(size_map val) subType_seqP /=.
    rewrite /enum_yameval (decr_nth_partE Hcorn) sumn_decr_nth.
    
