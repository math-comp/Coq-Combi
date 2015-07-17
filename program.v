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

Definition lend i := (nth O p i).-1.

Definition is_in_hook (i j:nat) (k l : nat) := 
     ((i == k) && (j < l < nth 0 p i))%N || ((j == l) && (i < k < haut p j))%N.

Lemma in_hook_part (i j:nat) (k l : nat) :
   is_in_part p i j -> is_in_hook i j k l -> is_in_part p k l.
Proof.
  rewrite /is_in_part /is_in_hook => Hj /orP [] /and3P [] /eqP <- // H1 H2.
  by rewrite ltnNge (haut_nth _ (intpartP p)) -ltnNge.
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
Proof.
  rewrite /hook_seq /is_in_hook => /mapP [] x.
  rewrite mem_cat => /orP [] /mapP [] u; rewrite mem_iota => Hu -> /= [] -> -> {x k l}.
  - rewrite eq_refl /=; apply/orP; right.
    move: Hu; case: (haut p j) => [|n] /=.
    + rewrite sub0n addn0 ltnS => /andP [] /leq_trans => H/H{H}.
      by rewrite ltnn.
    + rewrite addSn !ltnS.
      case: (leqP i n) => [Hi | /ltnW Hi].
      * by rewrite (subnKC Hi).
      * move: Hi; rewrite {1}/leq => /eqP ->.
        rewrite addn0 => /andP [] /leq_trans => H/H{H}.
      by rewrite ltnn.
  - rewrite eq_refl /=; apply/orP; left.
    move: Hu; case: (nth O p i) => [|n] /=.
    + rewrite sub0n addn0 ltnS => /andP [] /leq_trans => H/H{H}.
      by rewrite ltnn.
    + rewrite addSn !ltnS.
      case: (leqP j n) => [Hj | /ltnW Hj].
      * by rewrite (subnKC Hj).
      * move: Hj; rewrite {1}/leq => /eqP ->.
        rewrite addn0 => /andP [] /leq_trans => H/H{H}.
      by rewrite ltnn.
Save.

Lemma hook_seq_empty (i j:nat) : 
      is_in_part p i j -> (hook_seq i j == [::])%B -> (j == lend i)%B && is_out_corner p i.
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

Definition is_trace (A B : seq nat) := 
      [&& (A != [::]), (B != [::]), is_out_corner p (last O A), 
          lend (last O A) == last O B, sorted ltn A & sorted ltn B].

Lemma is_trace_in_part (A B : seq nat) : is_trace A B ->
      forall a b, a \in A -> b \in B -> is_in_part p a b.
admit.
Save.

Lemma is_trace_tll (a:nat) (A B : seq nat) : A != [::] -> is_trace (a::A) B -> is_trace A B.
admit.
Save.

Lemma is_trace_tlr (b:nat) (A B : seq nat) : B != [::] -> is_trace A (b::B) -> is_trace A B.
admit.
Save.


Lemma fun_cons_simpll a A B : 
    (fun x : seq nat * seq nat => ((a :: x.1, x.2) == (a :: A, B))%:~R) ==
    (fun x : seq nat * seq nat => (x == (A, B))%:~R).
move => [X Y] /=.
rewrite /eq_op /=.
rewrite {1}/eq_op /=.
by rewrite eq_refl.
Save.

Lemma fun_cons_simplr a A B : 
    (fun x : seq nat * seq nat => ((x.1, a :: x.2) == (A, a :: B))%:~R) ==
    (fun x : seq nat * seq nat => (x == (A, B))%:~R).
move => [X Y] /=.
rewrite /eq_op /=.
rewrite {2}/eq_op /=.
by rewrite eq_refl.
Save.

Lemma choose_corner_decomp m a b (A B : seq nat) : 
      (size (hook_next_seq a b) != 0)%N -> is_trace (a::A) (b::B) ->
      (* path ltn a A -> path ltn b B -> *)
      mu (choose_corner m.+1 a b) (fun R => (R==(a::A,b::B))%:Q)
      = (mu (choose_corner m  a (head O B)) (fun R => (R==(a::A,B))%:Q) + 
        mu (choose_corner m  (head O A) b) (fun R => (R==(A,b::B))%:Q))
        / (size (hook_next_seq a b))%:Q.
move => Hs Ht.
rewrite (choose_corner_rec_simpl _ _ _ Hs) Mlet_simpl.
rewrite mu_uniform_sum /=.
congr (_ / _). 
rewrite /hook_next_seq.
rewrite big_cat /=.
rewrite !big_map /=.
rewrite GRing.addrC.
congr (_+_)%R.
+ case (boolP (size B == O)) => HB.
 - rewrite big1.
   apply esym.
   apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m a (head O B))).
   move => [X Y] /=.
   apply /implyP => /andP [] /andP [] /andP [] _ SY _ _.
   move: SY; apply contra.
   by move => /eqP [] _ ->. 
   move => i _; rewrite fun_cons_simplr.
   apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m a i)).
   move => [X Y] /=.
   apply /implyP => /andP [] /andP [] /andP [] _ SY _ _.
   move: SY; apply contra.
   by move => /eqP [] _ ->. 
  - rewrite (bigD1_seq (head O B) _ (iota_uniq _ _)) /=.
  rewrite -{1}(fun_cons_simplr b).
  rewrite -[RHS]GRing.addr0.
  congr (_+_)%R.
  apply: big1.
  move => i Hi.
  rewrite fun_cons_simplr.
  apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m a i)).
  move => [X Y] /=.
  apply /implyP => /andP [] /andP [] /andP [] _ _ _ SH.
  move: Hi; apply contra.
  move => /eqP [_ H].
  rewrite -H.
  by rewrite eq_sym. 
  rewrite mem_iota.
  have:= Ht => /and5P [_ _ _ _] /andP [_ H4].
  apply /andP; split. 
  move: HB H4; rewrite /sorted.
  case B => [//|b0 B' /=].
  by move => _ /andP [].
  have Hh : (head O B \in b :: B).
  move: HB; case B => //=.
  move => n l _; by rewrite !inE eq_refl orbT.
  have := (is_trace_in_part _ _ Ht a (head O B) (mem_head _ _) Hh).
  rewrite /is_in_part addSn.
  move => Hlt.
  apply (leq_trans Hlt).
  apply leq_trans with ((nth O p a).-1).+1.
  by apply leqSpred => /=.
  rewrite ltnS.
  by rewrite -leq_subLR.
+ case (boolP (size A == O)) => HA.
  - rewrite big1.
   apply esym.
   apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m (head O A) b)).
   move => [X Y] /=.
   apply /implyP => /andP [] /andP [] /andP [] SX _ _ _.
   move: SX; apply contra.
   move => /eqP [H1 _]; by rewrite H1. 
   move => i _; rewrite fun_cons_simpll.
   apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m i b)).
   move => [X Y] /=.
   apply /implyP => /andP [] /andP [] /andP [] SX _ _ _.
   move: SX; apply contra.
   by move => /eqP [He _]; rewrite He. 
   - rewrite (bigD1_seq (head O A) _ (iota_uniq _ _)) /=.

rewrite -{1}(fun_cons_simpll a).
rewrite -[RHS]GRing.addr0.
congr (_+_)%R.
apply: big1.
move => i Hi.
rewrite fun_cons_simpll.
   apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m i b)).
   move => [X Y] /=.
   apply /implyP => /andP [] /andP [] /andP [] _ _ Ha _.
   move: Hi; apply contra.
   move => /eqP [He _]; rewrite -He. 
by rewrite eq_sym. 
  rewrite mem_iota.
  have:= Ht => /and5P [H1 H2 H3 H4] /andP [H5 H6].
  apply /andP; split. 
  move: HA H5; rewrite /sorted.
  case A => [//|a0 A' /=].
  by move => _ /andP [].
  have Hh : (head O A \in a :: A).
  move: HA; case A => //=.
  move => n l _; by rewrite !inE eq_refl orbT.
  have := (is_trace_in_part _ _ Ht (head O A) b Hh (mem_head _ _)).
  rewrite /is_in_part addSn.
  move => Hlt.
(*
  apply (leq_trans Hlt).
  apply leq_trans with ((nth O p a).-1).+1.
  by apply leqSpred => /=.
  rewrite ltnS.
  by rewrite -leq_subLR.*)
admit.

Save.




End FindCorner.
