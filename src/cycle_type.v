Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial.
From mathcomp Require Import fingroup perm automorphism action.

From Combi Require Import symgroup partition Greene sorted.

Require Import cycles.

Set Implicit Arguments.
Unset Strict Implicit.

Section cycle_type.
Variable T : finType.
Implicit Types (s t : {perm T}) (n : nat).

Definition cycle_type_seq (s : {perm T}) :=
  sort geq [seq #|(x: {set T})| |x <- enum (pcycles s)].

Definition card_support_cycles (s : {perm T}) :=
  [seq #|(C : {set T})| | C in (support_cycles s)].

Lemma cycle_type_dec (s : {perm T}) :
  let l := sort geq (card_support_cycles s) in
  cycle_type_seq (s : {perm T}) = l ++ (nseq (#|T| - sumn l) 1).
Proof.
  move => l. 
  admit.
Admitted.

Lemma support_cycle_type_seq s t :
  card_support_cycles s =i card_support_cycles t -> cycle_type_seq s = cycle_type_seq t.
Proof. by move => /(sort_eqP geq) /eqP; rewrite !cycle_type_dec => ->. Qed.

Lemma is_part_sortedP l:
  reflect (sorted (geq) l /\ {in l, forall x, x >= 1}) (is_part l).
Proof.
  admit.
Admitted.

Lemma geq_total : total geq.
Proof.
  admit.
Admitted.

  
Lemma cycle_type_part s:
  is_part (cycle_type_seq s).
Proof.
  apply /is_part_sortedP.
  split; first exact: (sort_sorted geq_total).
  move => n; rewrite mem_sort => /mapP [X].
  rewrite mem_enum => /imsetP [x] _ => -> -> {X}.
  case: posnP => // => /eqP; rewrite cards_eq0 => /eqP/setP /(_ x).
  by rewrite pcycle_id inE.
Qed.

Lemma big_sum_sumn (l: seq nat):
  \sum_(k <- l) k = sumn l.
Proof.
  rewrite /sumn.
  admit.
Admitted.

Lemma cycle_type_partn s:
  is_part_of_n #|T| (cycle_type_seq s).
Proof.
  apply /andP; split; last exact: cycle_type_part.
  rewrite cycle_type_dec sumn_cat sumn_nseq mul1n subnKC //.
  rewrite -big_sum_sumn.
  have /perm_eqlE Heq:= perm_sort geq (card_support_cycles s).
  rewrite (eq_big_perm _ Heq) /=.  
  rewrite big_map -big_enum.
  rewrite (support_cycle_dec s) -(card_partition (partition_support s)). 
  by apply: subset_leq_card; apply /subsetP => x.
Qed.

Definition cycle_type (s : {perm T}) := IntPartN (cycle_type_partn s).

Lemma congr_intpart (n : nat )(l1 l2 : seq nat) (H1 : is_part_of_n n l1) (H2 : is_part_of_n n l2):
  l1 = l2 -> IntPartN H1 = IntPartN H2.
Proof.
  admit.
Admitted.

  
Lemma support_cycle_type s t :
  perm_eq (card_support_cycles s) (card_support_cycles t) ->
    cycle_type s = cycle_type t.
Proof.
  move => Heq.
  apply cycle_type_dec.

  admit.
Admitted.

Lemma conjug_of_cycle s a:
  is_cycle s -> is_cycle (s ^ a)%g.
Proof.
  admit.
Admitted.

Lemma support_conjg s a:
  #|support s| = #|support (s ^ a)%g|.
Proof.
  admit.
Admitted.
  
(*
Utile pour construire explicitement la conjugaison également, donc à faire.

Lemma cycle_dec_of_conjugate s a :
  cycle_dec (s ^ a)%g =...*)

Lemma cycle_type_of_conjg s t a:
  (s ^ a)%g = t -> cycle_type s = cycle_type t.
Proof.
  rewrite /conjg => <-; apply: support_cycle_type => n.
  apply /mapP/mapP.
 -  move => [X]; rewrite mem_enum => /imsetP [x]  Hx ->.
    rewrite support_restr_perm // => ->.  
Admitted.

(* Ici il faut ayant supposé cycle_type s = cycle_type t, construire un
bijection entre pcycles s et pcycle t *)


Lemma bla s t :
  cycle_type s = cycle_type t ->
  exists f : {set T} -> {set T},
    {in pcycles s, injective f} /\ [set f x | x in pcycles s] = (pcycles t).
Proof.
Admitted.

Lemma classes_of_permP s t:
  reflect (t \in (s ^: [set: {perm T}])%g) (cycle_type s == cycle_type t).
Proof.
  admit.
Admitted.


(* Lemma cycle_type réalise une bijection de classes [set: {perm T}] sur enum_partn (#|T|) *)

(*
The action of the permutation (n, n+1, ... ,n+l-1) on (enum T)
*)

Definition cyclefun_of (n l : nat) : T -> T :=
  fun x =>
    let i := index x (enum T) in
    if n <= i < n+l-1 then (nth x (enum T) (i+1))
    else if i == n+l-1 then (nth x (enum T) n)
         else x.

Lemma injective_cyclefun_of n l:
  injective (cyclefun_of n l).
Proof.
  move => x1 x2.
  rewrite /cyclefun_of.
  case: (boolP (n <= index x1 (enum T) < n+l-1));
      case: (boolP (n <= index x2 (enum T) < n+l-1)).
  - move => _ _.
    


  admit.
Admitted.

Definition cycle_of n l : {perm T} :=
  perm (@injective_cyclefun_of n l).

Lemma cycle_ofP n l : n + l <= #|T| -> is_cycle (cycle_of n l).
Proof.
  admit.
Admitted.

Fixpoint perm_of_part_rec (part : seq nat) (n : nat) : seq {perm T} :=
  match part with
  | [::] => [::]
  | a :: l1 =>
    if a == 1 then (perm_of_part_rec l1 n.+1)
    else (cycle_of n a) :: (perm_of_part_rec l1 (a + n))
  end.

Definition perm_of_part l : {perm T} :=
  \prod_(c <- perm_of_part_rec l 0) c.

Lemma blabla l : cycle_dec (perm_of_part l) = [set i in perm_of_part_rec l 0].
Proof.
  admit.
Admitted.

Lemma perm_of_partE (l : intpartn #|T|) : cycle_type (perm_of_part l) = l.
Proof.
  admit.
Admitted.

End cycle_type.
