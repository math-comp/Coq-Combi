Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm tuple path bigop.
Require Import subseq partition ordtype schensted congr plactic green.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bool.

Section GreenInvariants.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Definition cast_set n m (H : n = m) : {set 'I_n} -> {set 'I_m} :=
  [fun s : {set 'I_n} => (cast_ord H) @: s].

Lemma cover_cast m n (P : {set {set 'I_n}}) (H : n = m) :
  cover (imset (cast_set H) (mem P)) = (cast_set H) (cover P).
Proof.
  rewrite /= cover_imset /cover; apply esym; apply big_morph.
  + move=> i j /=; by apply imsetU.
  + by apply imset0.
Qed.

Notation "a =Pl b" := (plactcongr a b) (at level 70).

Definition kseq_inj k u1 u2 :=
  forall s1, ksupp (in_tuple (u1)) k s1 ->
             exists s2, (scover s1 == scover s2) && ksupp (in_tuple (u2)) k s2.

Lemma leq_green k u1 u2 : kseq_inj k u1 u2 -> green u1 k <= green u2 k.
Proof.
  move=> Hinj; rewrite /= /greent.
  set P1 := ksupp (in_tuple u1) k.
  have : #|P1| > 0.
    rewrite -cardsE card_gt0; apply/set0Pn.
    exists set0; rewrite in_set; by apply ksupp0.
  move/(eq_bigmax_cond scover) => [] ks1 Hks1 ->.
  have := Hinj _ Hks1 => [] [] ks2 /andP [] /eqP -> Hks2.
  by apply leq_bigmax_cond.
Qed.

Lemma kseq_inj_plact1 u v1 w v2 k :
  v2 \in plact1 v1 -> kseq_inj k (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof.
  move/plact1P => [] a [] b [] c [] Hord -> -> {v1 v2}.
  rewrite /kseq_inj /ksupp => s1 /and3P [] Hsz Htriv /forallP Hall.
  set t1 := (u ++ [:: a; c; b] ++ w); set t2 := (u ++ [:: c; a; b] ++ w).
  have Hszu1 : (size u).+1 < size (in_tuple t1).
    by rewrite /= size_cat /= addnS ltnS -{1}[size u]addn0 ltn_add2l.
  have Hszu2 : (size u).+2 < size (in_tuple t1).
    by rewrite /= size_cat /= 2!addnS 2!ltnS -{1}[size u]addn0 ltn_add2l.
  case (boolP ((Ordinal Hszu1) \in cover s1)) => Hu1.
  + admit.
  + case (boolP ((Ordinal Hszu2) \in cover s1)) => Hu2.
    * admit.
    * have Hcast : size t1 = size t2 by rewrite !size_cat.
      exists (imset (cast_set Hcast) (mem s1)).
      apply/and4P; split.
      - by rewrite /scover /= cover_cast card_imset; last by apply cast_ord_inj.
      - by rewrite card_imset; last by apply imset_inj; apply cast_ord_inj.
      - by apply imset_trivIset; first by apply cast_ord_inj.
      - apply/forallP => S2; apply/implyP => /imsetP [] S1 Hs1 -> {S2}.
      - admit.
Qed.
Lemma kseq_inj_plact1i u v1 w v2 k :
  v2 \in plact1i v1 -> kseq_inj k (in_tuple (u ++ v1 ++ w)) (in_tuple (u ++ v2 ++ w)).
Proof.
  admit.
Qed.

Lemma kseq_inj_plact2 u v1 w v2 k :
  v2 \in plact2 v1 -> kseq_inj k (in_tuple (u ++ v1 ++ w)) (in_tuple (u ++ v2 ++ w)).
Proof.
  admit.
Qed.
Lemma kseq_inj_plact2i u v1 w v2 k :
  v2 \in plact2i v1 -> kseq_inj k (in_tuple (u ++ v1 ++ w)) (in_tuple (u ++ v2 ++ w)).
Proof.
  admit.
Qed.

Lemma invar_plact1 u v1 w v2 k :
  v2 \in plact1 v1 -> (green (u ++ v1 ++ w)) k = (green (u ++ v2 ++ w)) k.
Proof.
  move=> Hpl; apply/eqP; rewrite eqn_leq; apply/andP; split; apply leq_green.
  + by apply kseq_inj_plact1.
  + apply kseq_inj_plact1i; by rewrite -plact1I.
Qed.

Lemma invar_plact1i u v1 w v2 k :
  v2 \in plact1i v1 -> (green (u ++ v1 ++ w)) k = (green (u ++ v2 ++ w)) k.
Proof. by rewrite -plact1I => H; apply esym; apply invar_plact1. Qed.

Lemma invar_plact2 u v1 w v2 k :
  v2 \in plact2 v1 -> (green (u ++ v1 ++ w)) k = (green (u ++ v2 ++ w)) k.
Proof.
  move=> Hpl; apply/eqP; rewrite eqn_leq; apply/andP; split; apply leq_green.
  + by apply kseq_inj_plact2.
  + apply kseq_inj_plact2i; by rewrite -plact2I.
Qed.

Lemma invar_plact2i u v1 w v2 k :
  v2 \in plact2i v1 -> (green (u ++ v1 ++ w)) k = (green (u ++ v2 ++ w)) k.
Proof. by rewrite -plact2I => H; apply esym; apply invar_plact2. Qed.

Theorem plactic_green_inv u v : u =Pl v -> forall k, green u k = green v k.
Proof.
  move=> Hpl k.
  move: v Hpl; apply gencongr_ind; first by apply erefl.
  move=> a b1 c b2 -> {u} /plactruleP [].
  + apply invar_plact1.
  + apply invar_plact1i.
  + apply invar_plact2.
  + apply invar_plact2i.
Qed.

Corollary plactic_shapeRS u v : u =Pl v -> shape (RS u) = shape (RS v).
Proof.
  move=> Hpl.
  suff HeqRS k : green (to_word (RS u)) k = green (to_word (RS v)) k
    by apply (green_tab_eq_shape (is_tableau_RS u) (is_tableau_RS v) HeqRS).
  have <- := plactic_green_inv (congr_Sch u) k.
  have <- := plactic_green_inv (congr_Sch v) k.
  by apply plactic_green_inv.
Qed.

Theorem plact_Sch u v : plactcongr u v <-> RS u == RS v.
Proof.
  split; last by apply Sch_plact.
  move Hu : (size u) => n Hpl.
  have:= perm_eq_size (gencongr_homog Hpl) => /esym; rewrite Hu.
  elim: n u v Hpl Hu => [| n IHn] u v;
    first by move=> _ /eqP/nilP -> /eqP/nilP ->; rewrite /RS.
  move=> Hpl Hu Hv.
  have:= size_rembig u; rewrite Hu /= => Hszu.
  have:= size_rembig v; rewrite Hv /= => Hszv.
  have {IHn} := IHn _ _ (rembig_plactcongr Hpl) Hszu Hszv => /eqP {Hszu Hszv}.
  case: u Hu Hpl => [//= | u0 u'] _.
  case: v Hv     => [//= | v0 v'] _ => Hpl Hplrem.
  have:= rembig_RS u0 u' => [] [] iu Hiu.
  have:= rembig_RS v0 v' => [] [] iv; rewrite -Hplrem {Hplrem} => Hiv.
  rewrite -(maxL_perm_eq (gencongr_homog Hpl)) in Hiv.
  have:= plactic_shapeRS Hpl.
  rewrite Hiu Hiv {Hiu Hiv} !shape_append_nth => H.
  by rewrite -(incr_nth_inj H).
Qed.

End GreenInvariants.
