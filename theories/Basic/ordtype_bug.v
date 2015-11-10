Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import ordtype.

Section RowsAndCols.

Variable T : inhOrdType.

Lemma Bug (m n : T) : (@leqX_op (dual_ordType T) m n) = (@leqX_op T n m).
Proof.
  (* by rewrite dual_leqX. ne marche pas. *)
  (* Explication:
  have:= @dual_leqX T m n.
  rewrite /leqX_op.
     Donne:

   PartOrder.r (PartOrder.mixin (PartOrder.class (dual_pordType T))) m n =
   PartOrder.r (PartOrder.mixin (PartOrder.class T)) n m ->
   PartOrder.r (PartOrder.mixin (PartOrder.class (dual_ordType T))) m n =
   PartOrder.r (PartOrder.mixin (PartOrder.class T)) n m

  Du coup le match rate. *)
  (* Pourtant, les deux solution ci-dessous fonctionnent *)
  by rewrite -dual_leqX.
  (* Ou *)
  exact: dual_leqX.
Qed.
