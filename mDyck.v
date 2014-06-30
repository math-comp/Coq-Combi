Require Import Arith.
Require Import List.
Require Import Omega.
Require Import Dyck.
Require Import Bool.

Set Implicit Arguments.
Unset Strict Implicit.

Hint Unfold Is_true.

Lemma andb_prop_iff x y: Is_true (x && y) <-> Is_true x /\ Is_true y.
Proof.
  split; [apply andb_prop_elim | apply andb_prop_intro].
Qed.

Section mDyck.
  Variable m : nat.

  Fixpoint m_dyck_height (h : nat) (w : list Brace) : bool :=
  match w with
    | nil => beq_nat h 0
    | Open::tlb => m_dyck_height (m + h) tlb
    | Close::tlb =>
      match h with
        | 0    => false
        | S hh => m_dyck_height hh tlb
      end
  end.

  Definition is_m_dyck (w : list Brace) : Prop := Is_true (m_dyck_height 0 w).
  Hint Unfold is_m_dyck.

  Lemma m_dyck_height_unique:
    forall (w : list Brace) (h1 h2 : nat),
      Is_true (m_dyck_height h1 w) -> Is_true (m_dyck_height h2 w) -> h1 = h2.
  Proof.
    induction w.
    intros h1 h2 H1 H2.
    simpl in H1, H2.
    destruct h1, h2; auto; simpl in *; tauto.
    destruct h1, h2, a; auto with arith; intros H1 H2; simpl in H1, H2.
    apply plus_reg_l with m.
    apply IHw; assumption.
    apply plus_reg_l with m.
    apply IHw; assumption.
    specialize IHw with (m + S h1) (m + S h2); auto.
    apply plus_reg_l with m; auto.
  Qed.

  Lemma conc_is_dyck_height:
    forall (w1 w2: list Brace) (h1 h2 : nat),
      Is_true (m_dyck_height h1 w1) -> Is_true (m_dyck_height h2 w2) ->
      Is_true (m_dyck_height (h1 + h2) (w1 ++ w2)).
  Proof.
    induction w1; intros w2 h1 h2 H1 H2.
    destruct h1; simpl in H1.
    simpl; assumption.
    inversion H1.
    destruct a.
    simpl.
    simpl in H1.
    rewrite plus_assoc.
    apply IHw1; auto.
    destruct h1; simpl in H1|-*.
    inversion H1.
    apply IHw1; auto.
  Qed.

  Fixpoint m_dyck_height_factor (h : nat) (w : list Brace) : list Brace * list Brace :=
  match w with
    | nil => (nil, nil)
    | Open::tlb => let (w1, w2) := m_dyck_height_factor (m + h) tlb in
                   (Open :: w1, w2)
    | Close::tlb =>
      match h with
        | 0    => (nil, tlb)
        | S hh => let (w1, w2) := m_dyck_height_factor (hh) tlb in
                  (Close :: w1, w2)
      end
  end.

  Lemma factor_0_close :
    forall (w : list Brace), m_dyck_height_factor 0 (Close :: w) = (nil, w).
  Proof.
    intro w; simpl; auto.
  Qed.

  Lemma factor_conc:
    forall (w : list Brace) (hw h : nat),
      Is_true (m_dyck_height hw w) -> hw > h ->
      let (w1, w2) := m_dyck_height_factor h w in w = w1 ++ Close :: w2.
  Proof.
    induction w; intros hw h H Hp.
    destruct hw.
    inversion Hp.
    inversion H.
    destruct a; simpl in *.
    specialize IHw with (m + hw) (m + h).
    destruct (m_dyck_height_factor (m + h) w) as (w1, w2).
    rewrite IHw; auto.
    omega.
    destruct hw.
    inversion Hp.
    destruct h.
    auto with datatypes.
    specialize (IHw hw h H).
    destruct (m_dyck_height_factor h w) as (w1, w2).
    rewrite IHw; auto with datatypes.
    omega.
  Qed.

  Lemma factor_m_dyck:
    forall (w : list Brace) (hw h : nat),
      Is_true (m_dyck_height hw w) -> hw > h ->
      let (w1, w2) := m_dyck_height_factor h w in
      Is_true (m_dyck_height h w1) /\ Is_true (m_dyck_height (hw - S h) w2).
  Proof.
    induction w.
    destruct h; intros H Hc; simpl; auto.
    destruct hw.
    inversion Hc.
    inversion H.
    destruct hw.
    inversion Hc.
    inversion H.

    intros hw h Hc H.
    destruct a; simpl in *.
    specialize (IHw (m + hw) (m + h) Hc).
    destruct (m_dyck_height_factor (m + h) w) as (w1, w2).
    simpl.
    replace (hw - S h) with (m + hw - S (m + h)).
    apply IHw.
    omega.
    omega.

    destruct hw, h.
    inversion H.
    inversion H.
    simpl; split; auto.
    replace (hw - 0) with hw by auto with arith; auto.
    specialize IHw with hw h.
    destruct (m_dyck_height_factor h w) as (w1, w2).
    simpl.
    apply IHw; auto.
    omega.
  Qed.


  Ltac autolist H b := inversion H; clear H; subst b.


  Lemma m_dyck_factor_height_unique :
    forall (w : list Brace) (hw h : nat) (wa1 wa2 : list Brace),
      Is_true (m_dyck_height hw w) -> hw > h ->
      Is_true (m_dyck_height h wa1) -> w = wa1 ++ Close :: wa2 ->
      let (wb1, wb2) := m_dyck_height_factor h w
      in wa1 = wb1 /\ wa2 = wb2.
  Proof.
    induction w; intros hw h wa1 wa2 Hd Hp Hpa Hca.
    contradict Hca.
    auto with datatypes.

    destruct a.
    destruct wa1.
    inversion Hca.
    autolist Hca b.
    subst w.
    simpl.
    specialize (IHw (m + hw) (m + h) wa1 wa2 Hd).
    destruct (m_dyck_height_factor (m + h) (wa1 ++ Close :: wa2)) as (w1, w2).
    elim IHw; auto.
    intros Heq1 Heq2; rewrite Heq1, Heq2; auto.
    omega.

    destruct wa1, h.
    rewrite factor_0_close.
    inversion Hca; auto.

    inversion Hpa.

    autolist Hca b.
    inversion Hpa.

    autolist Hca b.
    simpl in *.
    destruct hw.
    inversion Hp.
    specialize (IHw hw h wa1 wa2 Hd).
    subst w.
    destruct (m_dyck_height_factor h (wa1 ++ Close :: wa2)) as (w1, w2).
    elim IHw; auto.
    intros H1 H2; rewrite H1; auto.
    omega.
  Qed.


  Definition list_m_dyck_to_m_dyck init l:=
    fold_right (fun (w1 w2 : list Brace) => (w1 ++ Close :: w2)) init l.

  Hint Unfold list_m_dyck_to_m_dyck.

  Definition is_list_m_dyck l := Is_true ( forallb (m_dyck_height 0) l ).

  Hint Unfold is_list_m_dyck.

  Lemma list_m_is_dyck_height :
    forall (l : list (list Brace)) (w : list Brace) (hw : nat),
      is_list_m_dyck l -> Is_true (m_dyck_height hw w) ->
      Is_true (m_dyck_height ((length l) + hw) (list_m_dyck_to_m_dyck w l)).
  Proof.
    unfold list_m_dyck_to_m_dyck, is_list_m_dyck.
    induction l as [ | w l0 ].
    simpl; trivial.
    intros w0 hw0 H H0; simpl.
    simpl in H.
    rewrite andb_prop_iff in H; decompose [and] H; clear H.
    replace (S (length l0 + hw0)) with (0 + S (length l0 + hw0)) by auto with arith.
    apply conc_is_dyck_height; auto.
    simpl; apply IHl0; auto.
  Qed.

  Fixpoint height_list_factor (h : nat) (w : list Brace) :=
    match h with
      | 0   => (nil, w)
      | S n => let (w1, w2) := m_dyck_height_factor 0 w
               in let (l, wr) := height_list_factor n w2
               in (w1 :: l, wr)
    end.

  Lemma list_factor_length :
    forall (h : nat) (w : list Brace), length (fst (height_list_factor h w)) = h.
  Proof.
    induction h; intro w; simpl; auto.
    destruct (m_dyck_height_factor 0 w) as (w1, w2).
    specialize IHh with w2.
    destruct (height_list_factor h w2) as (l, wr).
    simpl in *; rewrite IHh; auto.
  Qed.

  Theorem m_dyck_factorize_h :
    forall (h : nat) (w: list Brace),
      Is_true (m_dyck_height h w) ->
      let (l, wr) := (height_list_factor h w)
      in is_list_m_dyck l /\ is_m_dyck wr /\ (list_m_dyck_to_m_dyck wr l) = w.
  Proof.
    unfold is_dyck, is_list_m_dyck.
    induction h; intros w H; simpl.
    split; auto.
    assert (S h > 0) as Hpos by auto with arith.
    specialize (factor_conc H Hpos); intro H0.
    specialize (factor_m_dyck H Hpos); intro HH.
    destruct (m_dyck_height_factor 0 w) as (w1, w2).
    decompose [and] HH; clear HH.
    replace (S h - 1) with h in H2 by auto with arith.
    specialize (IHh w2 H2).
    subst w.
    destruct (height_list_factor h w2) as (l, wr).
    simpl; rewrite andb_prop_iff.
    decompose [and] IHh; clear IHh.
    rewrite H5.
    repeat split; auto.
  Qed.

  Definition m_factor (w : list Brace) := height_list_factor m w.

  Theorem m_dyck_factorize :
    forall (w : list Brace), w <> nil -> is_m_dyck w ->
      let (l, wr) := m_factor (tl w)
      in length l = m /\
         is_list_m_dyck l /\
         is_m_dyck wr /\
         Open :: (list_m_dyck_to_m_dyck wr l) = w.
  Proof.
    intros w Hwnil; destruct w; [contradiction Hwnil; auto | clear Hwnil ].
    unfold m_factor, tl.
    intros Hm; destruct b; [ | inversion Hm].
    unfold is_m_dyck in Hm; simpl in Hm.
    replace (m + 0) with m in Hm by auto with arith.
    specialize (m_dyck_factorize_h Hm); intro H.
    specialize (list_factor_length m w); intro Hl.
    destruct (height_list_factor m w) as (l, wr).
    decompose [and] H.
    rewrite H3; repeat split; auto.
  Qed.


  Lemma m_dyck_factorize_unique_h :
    forall (hr : nat) (wr : list Brace), Is_true (m_dyck_height hr wr) ->
      forall (h : nat) (w : list Brace), Is_true (m_dyck_height (h + hr) w) ->
        forall (l : list (list Brace)),  is_list_m_dyck l ->
          (list_m_dyck_to_m_dyck wr l) = w -> (l, wr) = height_list_factor h w.
  Proof.
    intros hr wr Hdr.
    induction h; intros w Hd l Hld Hconc.
    simpl in Hd|-*.
    specialize (list_m_is_dyck_height Hld Hdr); intro Hmd.
    rewrite Hconc in Hmd.
    specialize (m_dyck_height_unique Hd Hmd).
    intro Hl.
    destruct l as [ | w0 l].
    simpl in Hconc; rewrite Hconc; auto.
    simpl in Hl.
    omega.

    specialize (list_m_is_dyck_height Hld Hdr); intro Hmd.
    rewrite Hconc in Hmd.
    specialize (m_dyck_height_unique Hd Hmd); clear Hmd.
    intro Hll.
    assert (length l = S h) as Hl.
    omega.
    clear Hll.
    destruct l as [ | w0 l0]; inversion Hl as [Hl0]; clear Hl.
    unfold is_list_m_dyck in *.
    simpl in *.
    rewrite andb_prop_iff in Hld; decompose [and] Hld; clear Hld.
    rewrite Hl0 in *.
    assert (S (h + hr) > 0) as Hpos by auto with arith.
    symmetry in Hconc.
    specialize (m_dyck_factor_height_unique Hd Hpos H Hconc); clear Hpos.
    destruct (m_dyck_height_factor 0 w) as (w1, w2).
    intro HH; decompose [and] HH; clear HH.
    rewrite <- IHh with w2 l0; auto; clear IHh.
    rewrite H1; auto.

    subst w2; clear H1 w1.
    subst w; simpl in Hd.
    specialize (list_m_is_dyck_height H0 Hdr).
    rewrite <- Hl0; trivial.
  Qed.

  Theorem m_dyck_factorize_unique :
    forall (w : list Brace),
      w <> nil -> is_m_dyck w ->
      forall (l : list (list Brace)) (wr : list Brace),
         is_list_m_dyck l ->
         is_m_dyck wr ->
         Open :: (list_m_dyck_to_m_dyck wr l) = w ->
         (l, wr) = m_factor (tl w).
    Proof.
      intros w Hnil Hdw.
      destruct w; [ elim Hnil; auto | ].
      clear Hnil.
      destruct b; [ | inversion Hdw].
      intros l wr Hl Hdwr Hconc.
      inversion Hconc as [Hw]; clear Hconc.
      simpl; unfold m_factor.
      apply m_dyck_factorize_unique_h with 0; auto.
      rewrite Hw; trivial.
   Qed.

End mDyck.


