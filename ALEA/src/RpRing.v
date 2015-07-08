(** * RpRing.v: Ring and Field tactics for [Rplus] *)
(** Contributed by David Baelde, 2011 *)

Add Rec LoadPath "." as ALEA.

Require Import Uprop.
Require Import Rplus.
Open Scope Rp_scope.

Require Export Ring.

Lemma RplusSRth : semi_ring_theory R0 R1 Rpplus Rpmult (Oeq (A:=Rp)).
  constructor; intros; auto.
Save.

(** ** Power theory and how to recognize constant in powers *)

Require Import NArith.

Lemma RplusSRpowertheory :
  power_theory R1 Rpmult (@Oeq Rp Rpord)
               nat_of_N Rpexp.
constructor; intros.
pattern n; apply Nrect.
reflexivity.
clear n; intros n IH.
rewrite Nnat.nat_of_Nsucc.
change (r ^ S (nat_of_N n))
  with (r * (r ^ nat_of_N n)).
rewrite IH.
destruct n.
simpl pow_N; auto.
unfold Nsucc; simpl pow_N.
rewrite pow_pos_succ; auto with typeclass_instances.
Save.

(** ** Morphism for coefficients in [nat] *)

Lemma RplusSRmorph :
  semi_morph R0 R1 Rpplus Rpmult (@Oeq Rp Rpord)
             0%nat 1%nat plus mult beq_nat
             N2Rp.
constructor; auto.
intros.
rewrite <- N2Rp_eq_rewrite.
apply beq_nat_eq; auto.
Qed.

(* Recognize minus over constants as a constant
   because it is otherwise not handled by semi-ring tactics. *)
Ltac is_nat_cst n :=
 match n with
   | minus ?x ?y =>
       match (is_nat_cst x) with
         | true =>
             match (is_nat_cst y) with
               | true => constr:true
               | false => constr:false
             end
         | false => constr:false
       end
   | S ?p => is_nat_cst p
   | O => constr:true
   | _ => constr:false
 end.

Ltac nat_cst t :=
 match is_nat_cst t with
 | true => constr:(N_of_nat t)
 | false => constr:NotConstant
 end.

Ltac coeff_nat t :=
  match t with
   | N2Rp ?n =>
       match is_nat_cst n with
         | true => n | _ => constr:NotConstant
       end
   | _ => constr:NotConstant
  end.

Add Ring Rp_ring : RplusSRth (morphism RplusSRmorph,
                              constants [coeff_nat],
                              power_tac RplusSRpowertheory [nat_cst]).

(** ** Tests *)
Goal forall x y, x * 2 * x + y * x == x * y + 2 * x * x.
intros; ring.
Qed.

Goal forall x y, x * y * x == y * x^2.
intros; ring.
Qed.

(** ** Field *)

Require Export Field.

Lemma RplusSFth :
  semi_field_theory R0 R1 Rpplus Rpmult Rpdiv Rp1div (Oeq (A:=Rp)).
Proof.
  constructor; auto.
  exact RplusSRth.
  intros.
  apply Rp1div_right; auto.
Qed.

Ltac remove_Sx x := match goal with
  | |- context[(S x)] => change (S x) with (1+x)%nat
end.

Ltac remove_S := match goal with
  | x:nat |- _ => remove_Sx x
end.

Ltac field_pre :=
  try apply Ole_refl_eq;
  repeat remove_S;
  repeat first [
      rewrite U2Rp_Unth
    (* TODO non-uniform convention: N2Rp_mult in reverse direction *)
    | rewrite <- plus_Sn_m
    | rewrite <- N2Rp_plus
    | rewrite N2Rp_mult ].

Add Field Rp_field : RplusSFth (morphism RplusSRmorph,
                                constants [coeff_nat],
                                power_tac RplusSRpowertheory [nat_cst],
                                preprocess [field_pre],
                                postprocess [auto]). (* TODO overkill *)

(** Trick to kill subgoals of fields *)
Lemma post_field_notz : forall x, notz (N2Rp x) -> ~ (mkRp x 0 == R0).
Proof.
  intuition.
Qed.
Hint Resolve post_field_notz.

Section Test.

  Variable x y z : Rp.
  Variable n : nat.

  Goal (1 / 2 * x + 1 / 2 * x == x).
  field.
  Qed.

  Goal (x / 2 + x) * x == x^2 * 3 / 2.
  field.
  Qed.

  Goal 3 * x == 6 * x * [1/2].
  field.
  Qed.

  Goal ([1/2] * x + x) * x <= x^2 * 3 / 2.
  field.
  Qed.

  Goal N2Rp (2-1)%nat == R1.
  field.
  Qed.

  Goal x^(2-1) == x^1.
  field.
  Qed.

  Goal (S (S n)) * x == (S n) * x + x.
  field.
  Qed.

End Test.
