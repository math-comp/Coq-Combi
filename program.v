(** * program.v : the probabilistic program finding a corner *)

Add Rec LoadPath "ALEA/src" as ALEA.
Add Rec LoadPath "../Combi/LRrule".

Require Import Misc Ccpo Qmeasure.
Set Implicit Arguments.
Local Open Scope O_scope.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype rat 
               finfun ssrnum ssralg ssrint bigop.
Local Open Scope ring_scope.
Require Import partition.
Require Import equerre.
Local Open Scope rat_scope.

(* Require Import equerre. *)

Section FindCorner.

Variable p : intpart.

Definition last i := nth O p i.-1.

Definition is_in_hook (i j:nat) (k l : nat) := 
     ((i == k) && (j < l < nth 0 p i))%N || ((j == l) && (i < k < size p))%N.

Lemma in_hook_part (i j:nat) (k l : nat) :
   is_in_part p i j -> is_in_hook i j k l -> is_in_part p k l.
admit.
Save.

Definition hook_next_seq i j : seq (nat+nat) := 
    [seq (inl k) | k <- iota (i.+1) ((haut p j).-1 - i)]++
    [seq (inr k) | k <- iota (j.+1) ((nth O p i).-1 - j)].

(* Lemma size_hook : forall i j, size (hook_seq i j) == hook' i j. *)

Definition hook_next i j n : nat * nat := 
    match n with inl k => (k,j) | inr k => (i,k) end.

Definition hook_seq i j := [seq (hook_next i j n) | n <- hook_next_seq i j].

Lemma in_hook_seq (i j:nat) (k l : nat) :
   (k,l) \in (hook_seq i j) -> is_in_hook i j k l.
admit.
Save.

Lemma hook_seq_empty (i j:nat) : 
      is_in_part p i j -> (hook_seq i j == [::])%B -> (j == last i)%B && is_out_corner p i.
admit.
Save.

Lemma in_hook_seq_decr (i j:nat) (k l : nat) :
   (k,l) \in (hook_seq i j) -> (size (hook_seq k l) < size (hook_seq i j))%N.
admit.
Save.

Fixpoint choose_corner (m:nat) (i j : nat) : distr ((seq nat) * (seq nat)) := 
   if m is m'.+1 then
     let s := hook_next_seq i j in
     (if size s is p.+1 
     then Mlet (Uniform (unif_def (inl 0%N) s))
          (fun n => match n with inl k => 
               Mlet (choose_corner m' k j) (fun X => Munit (i::X.1,X.2))
                               | inr k => 
               Mlet (choose_corner m' i k) (fun X => Munit (X.1,j::X.2))
                    end)
     else Munit ([::i],[::j]))
   else Munit ([::i],[::j]).

Lemma choose_corner0_simpl i j : choose_corner 0 i j = Munit ([::i],[::j]).
trivial.
Save.

Lemma choose_corner_end_simpl m i j 
      : (size (hook_next_seq i j) == 0)%N -> choose_corner m i j = Munit ([::i],[::j]).
case m; rewrite //=.
move => N /eqP H.
rewrite H; trivial.
Save.

Lemma choose_corner_rec_simpl m i j : 
      forall (Hs : (size (hook_next_seq i j) != 0)%N), 
      choose_corner (m.+1) i j = Mlet (Uniform (mkunif (hook_next_seq i j) Hs))
          (fun n => match n with inl k => 
               Mlet (choose_corner m k j) (fun X => Munit (i::X.1,X.2))
                               | inr k => 
               Mlet (choose_corner m i k) (fun X => Munit (X.1,j::X.2))
                    end).
rewrite /=.
case (hook_next_seq i j) => //=.
Save.

Lemma choose_corner_inv m  : 
      forall i j, mu (choose_corner m i j) 
         (fun R => ((size R.1!=0)&&(size R.2!=0)&&(head 0 R.1==i)&&(head 0 R.2==j))%N%:Q)
      = 1.
elim m.
move => i j //=; rewrite 2!eq_refl //=.
move => n Hin i j.
case (boolP (size (hook_next_seq i j)== O)) => [H0|Hs].
rewrite choose_corner_end_simpl => //=.
by rewrite 2!eq_refl.
rewrite (choose_corner_rec_simpl n i j Hs).
rewrite Mlet_simpl.
rewrite mu_one_eq => //=.
move => [k|k] /=.
apply mu_bool_impl1 with (2:=Hin k j).
move => [A B] /=.
apply /implyP => /andP [H1 H2].
move:H1 => /andP [H3 _].
move:H3 => /andP [_ H3].
by rewrite H3 H2 eq_refl.
apply mu_bool_impl1 with (2:=Hin i k).
move => [A B] /=.
apply /implyP => /andP [H1 H2].
move:H1 => /andP [H3 H4].
move:H3 => /andP [H3 _].
by rewrite H3 H4 eq_refl.
Save.

Require Import path.

Lemma choose_corner_decomp m a b (A B : seq nat) : 
      (size (hook_next_seq a b) != 0)%N -> 
      (* path ltn a A -> path ltn b B -> *)
      mu (choose_corner m.+1 a b) (fun R => (R==(a::A,b::B))%:Q)
      = mu (choose_corner m  a (head O B)) (fun R => (R==(a::A,B))%:Q) + 
        mu (choose_corner m  (head O A) b) (fun R => (R==(A,b::B))%:Q).
move => Hs.
rewrite (choose_corner_rec_simpl _ _ _ Hs) Mlet_simpl.
rewrite mu_uniform_sum /=. 
rewrite /hook_next_seq.
rewrite big_cat /=.
rewrite !big_map /=.
rewrite (bigD1_seq (head O A) _ (iota_uniq _ _)) /=.
(*
rewrite {1}/eq_op /=.
rewrite {1 2}/eq_op /=.
rewrite !eq_refl /= -/eq_op.
*)


End FindCorner.