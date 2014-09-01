Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype seq tuple.
Require Import finset perm.

Set Implicit Arguments.
Unset Strict Implicit.

Section Permuted.

Variable T : eqType.

Section SizeN.

Variable n : nat.

Lemma card_Sn : #|'S_(n)| = n`!.
Proof.
  rewrite -[n in n`!]card_ord -!cardsT -(card_perm setT) cardsE; apply eq_card => p.
  rewrite /in_mem /perm_on /=.
  apply /eqP; rewrite eq_sym eqb_id.
  apply /subsetP => i _; by rewrite in_set.
Qed.

Definition permuted_tuple (t : n.-tuple T) :=
  [seq [tuple tnth t (aperm i p) | i < n] | p <- enum 'S_n ].

Lemma size_permuted_tuple (t : n.-tuple T) : size (permuted_tuple t) = n`!.
Proof. rewrite /permuted_tuple size_map -cardE; exact card_Sn. Qed.

Lemma perm_eq_permuted_tuple (s : list T) (H : size s == n) :
  forall s1, perm_eq s s1 -> s1 \in [seq tval t | t <- permuted_tuple (Tuple H)].
Proof.
  set t := Tuple H; have Ht : perm_eq s t by [].
  move=> s1 Hss1; rewrite perm_eq_sym in Hss1.
  have:= perm_eq_trans Hss1 Ht => /tuple_perm_eqP [] p Hs1.
  apply/mapP; set t1 := (X in _ = tval X) in Hs1; exists t1; last exact Hs1.
  rewrite /permuted_tuple; apply/mapP.
  by exists p; first by rewrite mem_enum.
Qed.

(*
Lemma permuted_tuple_eq_perm (s : list T) (H : size s == n) :
  forall s1, s1 \in [seq tval t | t <- permuted_tuple (Tuple H)] -> perm_eq s s1.
Proof.
  move=> s1; set t := Tuple H; have Ht : perm_eq s t by [].
  move/mapP => [] t1 /mapP [] p Hp -> -> {s1 t1}.
-  apply/tuple_perm_eqP.
  exists (perm_inv p).
   ......
Qed.
*)

End SizeN.

Definition permuted s :=
  [seq tval t | t <- permuted_tuple (Tuple (eq_refl (size s)))].

Lemma size_permuted s : size (permuted s) = (size s)`!.
Proof. by rewrite /permuted size_map size_permuted_tuple. Qed.

Lemma eq_seqE s s1 : perm_eq s s1 -> s1 \in permuted s.
Proof. by apply perm_eq_permuted_tuple. Qed.

End Permuted.

