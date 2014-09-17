Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm tuple path bigop.
Require Import subseq partition ordtype schensted congr plactic ordcast green.

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

Definition ksupp_inj R k u1 u2 :=
  forall s1, ksupp R (in_tuple (u1)) k s1 ->
             exists s2, (scover s1 == scover s2) && ksupp R (in_tuple (u2)) k s2.

Lemma leq_green R k u1 u2 : ksupp_inj R k u1 u2 -> green_rel R u1 k <= green_rel R u2 k.
Proof.
  move=> Hinj; rewrite /= /green_rel /green_rel_t.
  set P1 := ksupp R (in_tuple u1) k.
  have : #|P1| > 0.
    rewrite -cardsE card_gt0; apply/set0Pn.
    exists set0; rewrite in_set; by apply ksupp0.
  move/(eq_bigmax_cond scover) => [] ks1 Hks1 ->.
  have := Hinj _ Hks1 => [] [] ks2 /andP [] /eqP -> Hks2.
  by apply leq_bigmax_cond.
Qed.

Section NoMove.

Variable R : rel Alph.

Variable u v : word.
Variable a b : Alph.
Variable k : nat.
Let x := u ++ [:: a; b] ++ v.
Let y := u ++ [:: b; a] ++ v.

Variable P : {set {set 'I_(size x)}}.
Hypothesis Px : ksupp R (in_tuple x) k P.

Let ult : size u < size x.
Proof. by rewrite /= size_cat /= addnS ltnS -{1}[size u]addn0 leq_add2l. Qed.
Let posu := Ordinal ult.
Let u1lt : (size u).+1 < size x.
Proof. by rewrite /= size_cat /= addnS ltnS -{1}[size u]addn0 ltn_add2l. Qed.
Let posu1 := Ordinal u1lt.

Hypothesis Hu : posu \notin cover P.
Hypothesis Hu1 : posu1 \notin cover P.

Let Hcast : size x = size y. Proof. by rewrite !size_cat. Qed.

Definition Qnomove := imset (cast_set Hcast) (mem P).

Lemma extract_nomove S :
  S \in P -> (extract (in_tuple y)) (cast_set Hcast S) = (extract (in_tuple x)) S.
Proof.
  move=> HS; rewrite /extract /= /extractpred.
  rewrite (cast_map_cond _ _ Hcast).
  set f := (X in (filter X _)).
  have {f} /eq_filter -> : f =1 (mem S) by move=> i; rewrite /f /cast_set /= mem_cast.
  rewrite -eq_in_map => i; rewrite mem_filter => /andP [] Hi _.
  rewrite !(tnth_nth (inhabitant Alph)) /= /x /y.
  rewrite !nth_cat.
  case: (ltnP i (size u)) => //= Hiu.
  case: (ltnP (i - size u) 2) => //= Hiu2.
  exfalso; move: Hu Hu1.
  have: i \in cover P by rewrite /cover; apply/bigcupP; exists S.
  move: Hiu2; move HH : (i - size u) => d.
  case: d HH => [/eqP HH _| d1 HH].
  + rewrite subn_eq0 in HH.
    have -> : i = posu by apply/eqP; rewrite /eq_op /= eqn_leq Hiu HH.
    by move ->.
  + case: d1 HH => [/eqP HH _| //=].
    move: HH; rewrite -(eqn_add2r (size u)) (subnK Hiu) add1n=> /eqP Hiu1.
    have -> : i = posu1 by apply/eqP; rewrite /eq_op /= Hiu1.
    by move ->.
Qed.

Lemma ksupp_nomove : ksupp R (in_tuple y) k Qnomove.
Proof.
  move: Px => /and3P [] HszP HtrivP /forallP HallP.
  apply/and3P; split.
  - by rewrite card_imset; last by apply imset_inj; apply cast_ord_inj.
  - by apply imset_trivIset; first by apply cast_ord_inj.
  - apply/forallP => S2; apply/implyP => /imsetP [] S HS -> {S2}.
    suff -> : extract (in_tuple y) (cast_set Hcast S) = extract (in_tuple x) S.
      have:= (HallP S); by rewrite HS.
    by apply extract_nomove.
Qed.

Lemma scover_nomove : scover P == scover Qnomove.
Proof. by rewrite /scover /= cover_cast card_imset; last by apply cast_ord_inj. Qed.

End NoMove.


Lemma ksupp_inj_plact1 u v1 w v2 k :
  v2 \in plact1 v1 -> ksupp_inj (gtnX Alph) k (u ++ v1 ++ w) (u ++ v2 ++ w).
Proof.
  move/plact1P => [] a [] b [] c [] Hord -> -> {v1 v2}.
  rewrite /ksupp_inj  => s1 Hsupp.
  set t1 := (u ++ [:: a; c; b] ++ w); set t2 := (u ++ [:: c; a; b] ++ w).
  have Hszu : (size u) < size (in_tuple t1).
    by rewrite /= size_cat /= -{1}[size u]addn0 ltn_add2l.
  have Hszu1 : (size u).+1 < size (in_tuple t1).
    by rewrite /= size_cat /= addnS ltnS -{1}[size u]addn0 ltn_add2l.
  case (boolP ((Ordinal Hszu) \in cover s1)) => Hu.
  + admit.
  + case (boolP ((Ordinal Hszu1) \in cover s1)) => Hu1.
    * admit.
    * exists (Qnomove s1).
      rewrite scover_nomove ksupp_nomove //=.
      - set bigord := (Ordinal _).
        by have -> : bigord = (Ordinal Hszu) by apply /eqP; rewrite /eq_op /=.
      - set bigord := (Ordinal _).
        by have -> : bigord = (Ordinal Hszu1) by apply /eqP; rewrite /eq_op /=.
Qed.
Lemma ksupp_inj_plact1i u v1 w v2 k :
  v2 \in plact1i v1 -> ksupp_inj (gtnX Alph) k (in_tuple (u ++ v1 ++ w)) (in_tuple (u ++ v2 ++ w)).
Proof.
  admit.
Qed.

Lemma ksupp_inj_plact2 u v1 w v2 k :
  v2 \in plact2 v1 -> ksupp_inj (gtnX Alph) k (in_tuple (u ++ v1 ++ w)) (in_tuple (u ++ v2 ++ w)).
Proof.
  admit.
Qed.
Lemma ksupp_inj_plact2i u v1 w v2 k :
  v2 \in plact2i v1 -> ksupp_inj (gtnX Alph) k (in_tuple (u ++ v1 ++ w)) (in_tuple (u ++ v2 ++ w)).
Proof.
  admit.
Qed.

Lemma invar_plact1 u v1 w v2 k :
  v2 \in plact1 v1 -> (greenCol (u ++ v1 ++ w)) k = (greenCol (u ++ v2 ++ w)) k.
Proof.
  move=> Hpl; apply/eqP; rewrite eqn_leq; apply/andP; split; apply leq_green.
  + by apply ksupp_inj_plact1.
  + apply ksupp_inj_plact1i; by rewrite -plact1I.
Qed.

Lemma invar_plact1i u v1 w v2 k :
  v2 \in plact1i v1 -> (greenCol (u ++ v1 ++ w)) k = (greenCol (u ++ v2 ++ w)) k.
Proof. by rewrite -plact1I => H; apply esym; apply invar_plact1. Qed.

Lemma invar_plact2 u v1 w v2 k :
  v2 \in plact2 v1 -> (greenCol (u ++ v1 ++ w)) k = (greenCol (u ++ v2 ++ w)) k.
Proof.
  move=> Hpl; apply/eqP; rewrite eqn_leq; apply/andP; split; apply leq_green.
  + by apply ksupp_inj_plact2.
  + apply ksupp_inj_plact2i; by rewrite -plact2I.
Qed.

Lemma invar_plact2i u v1 w v2 k :
  v2 \in plact2i v1 -> (greenCol (u ++ v1 ++ w)) k = (greenCol (u ++ v2 ++ w)) k.
Proof. by rewrite -plact2I => H; apply esym; apply invar_plact2. Qed.

Theorem plactic_greenCol_inv u v : u =Pl v -> forall k, greenCol u k = greenCol v k.
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
  suff HeqRS k : greenCol (to_word (RS u)) k = greenCol (to_word (RS v)) k
    by apply (greenCol_tab_eq_shape (is_tableau_RS u) (is_tableau_RS v) HeqRS).
  have <- := plactic_greenCol_inv (congr_Sch u) k.
  have <- := plactic_greenCol_inv (congr_Sch v) k.
  by apply plactic_greenCol_inv.
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
