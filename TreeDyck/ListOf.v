Require Export Relations.
Require Export Arith.
Require Export Peano_dec.
Require Export List.
Require Export Coq.Sorting.PermutSetoid.
Require Export Multiset.


Section ListOf.

Variable A : Set.
Variable P : A -> Prop.

Variable eqA : relation A.
Variable eqA_dec : forall x y : A, {eqA x y} + {~ eqA x y}.
Hypothesis eqA_equiv : equivalence A eqA.

Lemma eq_dec_1 :
  forall (a b : A),
    eqA a b -> (if eqA_dec a b then 1 else 0) = 1.
Proof.
intros; elim (eqA_dec a b); intros; [auto | contradiction].
Qed.


Lemma eq_dec_l :
  forall (a0 a b : A),
    eqA a b ->
      (if eqA_dec a0 a then 1 else 0) = (if eqA_dec a0 b then 1 else 0).
Proof.
intros.
elim eqA_equiv; intros.
elim eqA_dec with a0 a; elim eqA_dec with a0 b; intros; auto.
 elim b0; apply equiv_trans with a; auto.
 elim b0; apply equiv_trans with b; auto.
Qed.

Lemma eq_dec_r :
  forall (a0 a b : A),
    eqA a b ->
      (if eqA_dec a a0 then 1 else 0) = (if eqA_dec b a0 then 1 else 0).
Proof.
intros.
elim eqA_equiv; intros.
elim eqA_dec with a a0; elim eqA_dec with b a0; intros; auto.
 elim b0; apply equiv_trans with a; auto.
 elim b0; apply equiv_trans with b; auto.
Qed.


Let mult_list (l : list A) (a : A) :=
  multiplicity (list_contents eqA eqA_dec l) a.

Lemma eqA_mult_comp :
  forall (a b : A) (l : list A),
    eqA a b -> mult_list l a = mult_list l b.
Proof.
intros; unfold mult_list.
induction l; intros; auto.
 unfold munion; simpl.
   rewrite IHl; auto.
   rewrite (eq_dec_l a0 a b); auto.
Qed.


(* List of elements of A, each element appears once and only once *)
Definition list_of_set : Set :=
  { l : list A |
    forall a : A, (  P a /\ mult_list l a = 1) \/
      	       	  (~ P a /\ mult_list l a = 0) }.


Lemma empty_set_list :
  (forall a : A, False) -> list_of_set.
Proof.
intros; unfold list_of_set.
apply exist with (nil (A:=A)); tauto.
Defined.

End ListOf.

Set Implicit Arguments.
Unset Strict Implicit.


Section ListOfOperations.
Variable A B : Set.

Variable eqA : relation A.
Hypothesis eqA_equiv : equivalence A eqA.
Variable eqA_dec : forall x y : A, {eqA x y} + {~ eqA x y}.

Variable eqB : relation B.
Hypothesis eqB_equiv : equivalence B eqB.
Variable eqB_dec : forall x y : B, {eqB x y} + {~ eqB x y}.


Section ListOfUnion.

Let sumAB := (A + B)%type.

Definition eqsumAB : relation sumAB :=
  fun P1 P2 : sumAB =>
    match P1 with
      | inl a1 =>
        match P2 with
          | inl a2 => eqA a1 a2
          | inr _  => False
        end
      | inr b1 =>
        match P2 with
          | inl _  => False
          | inr b2 => eqB b1 b2
        end
    end.

Theorem eqsumAB_dec :
  forall x y : sumAB, {eqsumAB x y} + {~ eqsumAB x y}.
Proof.
  destruct x; destruct y.
  destruct (eqA_dec a a0); [left | right]; simpl; assumption.
  right; simpl; auto.
  right; simpl; auto.
  destruct (eqB_dec b b0); [left | right]; simpl; assumption.
Qed.

Theorem eqsumAB_equiv : equivalence sumAB eqsumAB.
Proof.
  elim eqA_equiv; intros.
  elim eqB_equiv; intros.
  split.
    unfold reflexive.
      destruct x; simpl; auto.
    unfold transitive in *.
      destruct x as [xa | xb]; destruct y as [ya | yb].
      destruct z as [za | zb].
        simpl; apply equiv_trans.
        simpl; auto.
      simpl; intros z H; contradiction.
      simpl; intros z H; contradiction.
      destruct z as [za | zb].
      simpl; auto.
      simpl; apply equiv_trans0.
    unfold symmetric in *.
      destruct x as [xa | xb]; destruct y as [ya | yb].
      simpl; apply equiv_sym.
      simpl; auto.
      simpl; auto.
      simpl; apply equiv_sym0.
Qed.

Variable PA : A -> Prop.
Variable PB : B -> Prop.

Definition PsumAB (ab : sumAB) : Prop :=
  match ab with
    | inl a => PA a
    | inr b => PB b
  end.

Lemma eqA_eqsumAB_compat :
  forall (a0 a1 : A),
    (if eqsumAB_dec (inl a0) (inl a1) then 1 else 0) =
    (if eqA_dec a0 a1 then 1 else 0).
Proof.
  intros a0 a1.
  destruct (eqsumAB_dec (inl a0) (inl a1)); destruct (eqA_dec a0 a1); tauto.
Qed.

Lemma eqB_eqsumAB_compat :
  forall (b0 b1 : B),
    (if eqsumAB_dec (inr b0) (inr b1) then 1 else 0) =
    (if eqB_dec b0 b1 then 1 else 0).
Proof.
  intros b0 b1.
  destruct (eqsumAB_dec (inr b0) (inr b1)); destruct (eqB_dec b0 b1); tauto.
Qed.

Lemma mult_a_lA :
  forall (a : A) (lA : list A),
    multiplicity (list_contents _ eqsumAB_dec (map (fun a : A => inl a) lA)) (inl a) =
    multiplicity (list_contents _ eqA_dec lA) a.
Proof.
  intro a.
  induction lA as [| a0 lA].
  simpl; auto.
  simpl.
  rewrite IHlA.
  rewrite <- eqA_eqsumAB_compat with a0 a; reflexivity.
Qed.

Lemma mult_b_lB :
  forall (b : B) (lB : list B),
    multiplicity (list_contents _ eqsumAB_dec (map (fun b : B => inr b) lB)) (inr b) =
    multiplicity (list_contents _ eqB_dec lB) b.
Proof.
  intro b.
  induction lB as [| b0 lB].
  simpl; auto.
  simpl; rewrite IHlB.
  rewrite <- eqB_eqsumAB_compat with b0 b; reflexivity.
Qed.

Lemma mult_a_lB :
  forall (a : A) (lB : list B),
    multiplicity (list_contents _ eqsumAB_dec (map (fun b : B => inr b) lB))
      (inl a) = 0.
Proof.
  intro a.
  induction lB as [| b lB].
  simpl; auto.
  simpl; rewrite IHlB.
  destruct (eqsumAB_dec (inr b) (inl a)).
  contradiction.
  auto with arith.
Qed.

Lemma mult_b_lA :
  forall (b : B) (lA : list A),
    multiplicity (list_contents _ eqsumAB_dec (map (fun a : A => inl a) lA))
      (inr b) = 0.
Proof.
  intro b.
  induction lA as [| a lA].
  simpl; auto.
  simpl; rewrite IHlA.
  destruct (eqsumAB_dec (inl a) (inr b)).
  contradiction.
  auto with arith.
Qed.


Lemma mult_a :
  forall (a : A) (lA : list A) (lB : list B),
    multiplicity
      (list_contents eqsumAB eqsumAB_dec
         (map (fun a0 : A => inl a0) lA ++ map (fun b : B => inr b) lB))
      (inl a) =
    multiplicity (list_contents eqA eqA_dec lA) a.
Proof.
  intros a lA lB.
  induction lA.
  simpl.
  apply mult_a_lB.
  simpl.
  rewrite IHlA, <- eqA_eqsumAB_compat; reflexivity.
Qed.

Lemma mult_b :
  forall (b : B) (lA : list A) (lB : list B),
    multiplicity
      (list_contents eqsumAB eqsumAB_dec
         (map (fun a0 : A => inl a0) lA ++ map (fun b : B => inr b) lB))
      (inr b) =
    multiplicity (list_contents eqB eqB_dec lB) b.
Proof.
  intros b lA lB.
  induction lB as [ | b0 LB].
  simpl.
  rewrite app_nil_r.
  apply mult_b_lA.
  rewrite list_contents_app in *.
  simpl in *.
  rewrite <- eqB_eqsumAB_compat.
  rewrite plus_comm at 1.
  rewrite <- plus_assoc.
  rewrite plus_comm in IHLB.
  rewrite IHLB; reflexivity.
Qed.


Theorem list_of_union :
  list_of_set A PA eqA eqA_dec ->
  list_of_set B PB eqB eqB_dec ->
    list_of_set sumAB PsumAB eqsumAB eqsumAB_dec.
Proof.
  intros LA LB.
  destruct LA as (lA, HA).
  destruct LB as (lB, HB).
  exists ( (map (fun a : A => inl a) lA) ++ (map (fun b : B => inr b) lB) ).
  destruct a.
    clear HB.
    destruct HA with a; decompose [and] H; clear H;
      [left | right]; split; simpl; auto; rewrite mult_a; assumption. 
    clear HA.
    destruct HB with b; decompose [and] H; clear H;
      [left | right]; split; simpl; auto; rewrite mult_b; assumption. 
Defined.
  
End ListOfUnion.

Section ListOfPairs.

Let AB := (A * B)%type.

Definition eqAB : relation AB :=
  fun P1 P2 : AB =>
    let (a1, b1) := P1 in
    let (a2, b2) := P2 in (eqA a1 a2) /\ (eqB b1 b2).

Theorem eqAB_dec :
  forall x y : AB, {eqAB x y} + {~ eqAB x y}.
Proof.
intro x; elim x; intros a b.
intro y; elim y; intros a0 b0.
elim (eqA_dec a a0); intros.
 elim (eqB_dec b b0); intros.
  left; unfold eqAB; simpl; auto.
  right; unfold eqAB; simpl; tauto.
 right; unfold eqAB; simpl; tauto.
Defined.

Theorem eqAB_equiv : equivalence AB eqAB.
Proof.
elim eqA_equiv; intros.
elim eqB_equiv; intros.
split.
 unfold reflexive; intros x; elim x; intros a b.
   simpl; auto.
 unfold transitive.
   intros x; elim x; intros xa xb.
   intros y; elim y; intros ya yb.
   intros z; elim z; intros za zb.
   simpl; intros.
   decompose [and] H.
   decompose [and] H0.
   split.
  apply equiv_trans with ya; auto.
  apply equiv_trans0 with yb; auto.
 unfold symmetric.
   intros x; elim x; intros xa xb.
   intros y; elim y; intros ya yb.
   simpl; intro; decompose [and] H; auto.
Qed.

Lemma eqAB_mult :
  forall (a a' : A) (b b': B),
    (if eqAB_dec (a, b) (a', b') then 1 else 0) =
     (if eqA_dec a a' then 1 else 0) *
     (if eqB_dec b b' then 1 else 0).
Proof.
intros.
elim eqAB_dec; intros.
 elim a0; intros.
   rewrite <- (eq_dec_l A eqA eqA_dec eqA_equiv) with a a a'; auto.
   rewrite <- (eq_dec_l B eqB eqB_dec eqB_equiv) with b b b'; auto.
   rewrite (eq_dec_1 A eqA eqA_dec); auto.
  rewrite (eq_dec_1 B eqB eqB_dec); auto.
    elim eqB_equiv; intros; auto.
  elim eqA_equiv; intros; auto.
 unfold eqAB in b0; simpl in b0.
   elim (eqA_dec a a'); intros; auto.
   elim (eqB_dec b b'); intros; auto.
   elim b0; split; auto.
Qed.



Lemma prod_nil :
  forall (E F: Set) (x : list E),
    list_prod x (nil (A := F)) = nil.
Proof.
intros; unfold list_prod. induction x.
 auto.
 fold list_prod; fold list_prod in IHx.
   rewrite IHx; auto.
Qed.


Lemma map_prod_mult :
  forall (xa : A) (xb : B) (lb : list B),
    multiplicity
     (list_contents eqAB eqAB_dec
        (map (fun y : B => (xa, y)) lb)) (xa, xb) =
    multiplicity (list_contents eqB eqB_dec lb) xb.
Proof.
intros.
elim eqA_equiv; intros.
elim eqB_equiv; intros.
induction lb; intros; simpl; auto.
   rewrite IHlb; clear IHlb.
   assert
    ((if eqAB_dec (xa, a) (xa, xb) then 1 else 0) =
     (if eqB_dec a xb then 1 else 0)).
  rewrite eqAB_mult; rewrite (eq_dec_1 A eqA).
   auto with arith.
   apply equiv_refl.
  rewrite <- H; auto.
Qed.


Lemma mult_list_rec :
  forall (xa : A) (la : list A) (lb : list B) (a : A) (b : B),
    multiplicity
      (list_contents eqAB eqAB_dec (list_prod (xa::la) lb)) (a, b)
    = ( (if eqA_dec xa a then 1 else 0)
      	* multiplicity (list_contents eqB eqB_dec lb) b )
      + multiplicity
      	 (list_contents eqAB eqAB_dec (list_prod (la) lb)) (a, b).
Proof.
Opaque eqAB_dec.
intros; unfold list_prod at 1; fold list_prod.
  rewrite list_contents_app.
   simpl; elim (eqA_dec xa a); intros.
  rewrite mult_1_l.
    rewrite (eqA_mult_comp AB eqAB eqAB_dec eqAB_equiv (a, b) (xa, b)).
   rewrite map_prod_mult; auto.
   unfold eqAB; simpl.
     split.
    elim eqA_equiv; auto.
    elim eqB_equiv; auto.
  rewrite mult_0_l; rewrite plus_0_l.
    assert
     (multiplicity
        (list_contents eqAB eqAB_dec (map (fun y : B => (xa, y)) lb))
        (a, b) = 0).
     induction lb; auto.
     simpl; rewrite IHlb; clear IHlb.
     rewrite plus_0_r.
     elim (eqAB_dec (xa, a0) (a, b)); auto.
     intros.
     elim a1; intros.
     contradiction.
   unfold AB in H; rewrite H; auto.
Qed.


Theorem mult_list_of_pairs :
  forall (la : list A) (lb : list B) (a : A) (b : B),
    multiplicity
      (list_contents eqAB eqAB_dec (list_prod la lb)) (a,b)
    =   (multiplicity (list_contents eqA eqA_dec la) a)
      * (multiplicity (list_contents eqB eqB_dec lb) b).
Proof.
induction la.
 simpl; auto.
 intros lb xa xb.
   rewrite mult_list_rec.
   rewrite IHla; clear IHla.
   simpl; rewrite <- mult_plus_distr_r; auto.
Qed.


Variable PA : A -> Prop.
Variable PB : B -> Prop.

Definition PAB : AB -> Prop :=
  fun xx => match xx with (x1,x2) => (PA x1) /\ (PB x2) end.


Theorem list_of_pairs :
  list_of_set A PA eqA eqA_dec ->
  list_of_set B PB eqB eqB_dec ->
    list_of_set AB PAB eqAB eqAB_dec.
Proof.
intros.
elim H; clear H; intros lA plA.
elim H0; clear H0; intros lB plB.
unfold list_of_set; apply exist with (list_prod lA lB).
intro ab.
elim ab; clear ab; intros a b.
elim (plA a); clear plA; intros.
 decompose [and] H; clear H.
   elim (plB b); clear plB; intros.
  decompose [and] H; clear H.
    left; split.
   unfold PAB; simpl; tauto.
   rewrite mult_list_of_pairs; rewrite H1; rewrite H3; auto.
  decompose [and] H; clear H.
    right; split.
   unfold PAB; simpl; tauto.
   rewrite mult_list_of_pairs; rewrite H1; rewrite H3; auto.
 decompose [and] H; clear H.
   right; split.
  unfold PAB; simpl; tauto.
  rewrite mult_list_of_pairs; rewrite H1; auto.
Defined.

End ListOfPairs.


Section ListOfImage.

Variable PA : A -> Prop.
Variable PB : B -> Prop.
Hypothesis PB_eqB_comp : forall x y : B, PB x -> eqB x y -> PB y.
Variable f : A -> B.
Hypothesis f_P_comp : forall a : A, PA a -> PB (f a).
Hypothesis f_P_comp_rev : forall a : A, PB (f a) -> PA a.
Hypothesis f_eq_comp : forall x y : A, eqA x y -> eqB (f x) (f y).
Hypothesis f_eq_inj  : forall x y : A, eqB (f x) (f y) -> eqA x y.
Hypothesis f_surj : forall (b : B), PB b -> {a : A | eqB (f a) b}.
Hypothesis PB_dec : forall (b : B), { PB b } + {~ PB b}.

Theorem mult_image :
  forall (la : list A) (a : A),
    multiplicity
      (list_contents eqB eqB_dec (map f la)) (f a)
    = multiplicity
      	(list_contents eqA eqA_dec la) a.
Proof.
intros.
induction la; intros; simpl; auto.
  rewrite IHla; clear IHla.
   assert
    ((if eqB_dec (f a0) (f a) then 1 else 0) =
     (if eqA_dec a0 a then 1 else 0)); auto.
   elim (eqA_dec a0 a); elim (eqB_dec (f a0) (f a)); intros; auto.
  elim b; auto.
  elim b; auto.
Qed.

Lemma list_image_pos :
  forall (la : list A) (b : B),
    1 <= multiplicity (list_contents eqB eqB_dec (map f la)) b ->
      exists a : A, eqB (f a) b.
Proof.
induction la.
 intros; simpl in H.
   elim (le_Sn_O 0); auto.
 simpl in |- *.
   intro b; elim (eqB_dec (f a) b); intros.
  exists a; auto.
  simpl in H.
    elim (IHla b); auto.
Qed.

Theorem list_of_image :
    list_of_set A PA eqA eqA_dec ->
      list_of_set B PB eqB eqB_dec.
Proof.
intros.
elim H; clear H; intros lA plA.
unfold list_of_set; apply exist with (map f lA).
intro b.
elim (PB_dec b); intros PBb; [ left | right ].
 split; auto.
   elim (f_surj PBb); intros a fab.
   elim (plA a); clear plA; intros H; decompose [and] H; clear H.
  rewrite (eqA_mult_comp B eqB eqB_dec eqB_equiv b (f a)).
   rewrite mult_image; auto.
   elim eqB_equiv; intros; auto.
  absurd (PA a); auto.
    apply f_P_comp_rev; apply PB_eqB_comp with b; auto.
    elim eqB_equiv; auto.
 split; auto.
   elim (zerop (multiplicity (list_contents eqB eqB_dec (map f lA)) b)); auto.
   intros.
   red in b0.
   elim PBb.
   elim (list_image_pos b0).
   intros.
   rewrite <- (eqA_mult_comp B eqB eqB_dec eqB_equiv (f x) b) in b0; auto.
   rewrite mult_image in b0.
   elim (plA x); intros.
  decompose [and] H0; apply PB_eqB_comp with (f x); auto.
  decompose [and] H0.
    rewrite H2 in b0.
    elim (le_Sn_O 0); auto.
Defined.

End ListOfImage.

End ListOfOperations.




Section ListOfNat.

Lemma list_of_nat_lt_n :
  forall n : nat,
    list_of_set nat (fun i : nat => i < n) (eq (A := nat)) eq_nat_dec.
Proof.
unfold list_of_set; induction n; intros.
 apply exist with (nil (A:=nat)).
   intro a; right.
   split; auto with arith.
 elim IHn; clear IHn; intros.
   apply exist with (n :: x); intros.
   elim le_or_lt with (S n) a; intros; [ right | left ]; intros.
  split; auto with arith.
   elim (p a); clear p; intros.
    decompose [and] H0; clear H0.
      absurd (S n <= a); auto with arith.
    decompose [and] H0; clear H0.
      unfold multiplicity; simpl; rewrite H2.
      elim (eq_nat_dec n a); intros.
     rewrite a0 in H.
       elim le_Sn_n with a; auto.
       auto with arith.
  split; auto.
    elim (p a); clear p; intros.
   decompose [and] H0; clear H0.
     unfold multiplicity; simpl; rewrite H2.
     elim (eq_nat_dec n a); intros.
    rewrite a0 in H1.
      elim lt_irrefl with a; auto.
      auto with arith.
   decompose [and] H0; clear H0.
     assert (a = n).
    elim le_lt_or_eq with a n; intros; auto with arith.
      elim H1; auto.
    unfold multiplicity; simpl; rewrite H2.
      rewrite H0; elim (eq_nat_dec n n); auto with arith.
      intro; elim b; auto.
Defined.

End ListOfNat.
