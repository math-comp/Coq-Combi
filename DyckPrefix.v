(*

Lemma eqBrace_dec :
  forall b1 b2 : Brace, {b1 = b2} + {b1 <> b2}.
Proof.
induction b1; induction b2.
 left; auto.
 right; unfold not; intro; inversion H.
 right; unfold not; intro; inversion H.
 left; auto.
Qed.

Lemma if_close_close :
   (if eqBrace_dec Close Close then 1 else 0) = 1.
Proof.
destruct (eqBrace_dec Close Close); intros.
ring.
induction n.
auto.
Qed.

Lemma if_close_open :
   (if eqBrace_dec Close Open then 1 else 0) = 0.
Proof.
destruct (eqBrace_dec Close Open); intros.
inversion e.
auto.
Qed.

Lemma if_open_close :
   (if eqBrace_dec Open Close then 1 else 0) = 0.
Proof.
destruct (eqBrace_dec Open Close); intros.
inversion e.
auto.
Qed.

Lemma if_open_open :
   (if eqBrace_dec Open Open then 1 else 0) = 1.
Proof.
destruct (eqBrace_dec Open Open); intros.
ring.
induction n.
auto.
Qed.


Fixpoint cut_loop
  (height : nat) (start : list Brace) (w : list Brace) :=
     match w with
       | nil       => (rev start, nil)
       | Open::tlb  => cut_loop (height+1) (Open::start) tlb
       | Close::tlb =>
           match height with
             | 0   =>  (rev start, tlb)
             | S n => cut_loop n (Close::start) tlb
           end
     end.

Fixpoint cut (w : list Brace) :=
  match w with
    | Open::l => cut_loop 0 nil l
    | _ => (nil, nil)   (* we don't care *)
  end.

Theorem dyck_cut_is_dyck:
  forall (w : list Brace) (n : nat), n > 0 -> dyck_height n w ->
     dyck_height n (fst (cut_loop n nil w)).
Proof.
intros.
induction n.
omega.


intros.
compute.
omega.
intros.
Admitted.

Let mult_list (l : list Brace) (a : Brace) :=
  multiplicity (list_contents (eq (A := Brace)) eqBrace_dec l) a.


Definition isDyck (w : list Brace) : Prop :=
  mult_list w Open = mult_list w Close /\
    forall (n : nat),
      mult_list (sublist Brace n w) Open
      	>= mult_list (sublist Brace n w) Close.


Lemma nil_is_Dyck : isDyck nil.
Proof.
unfold isDyck, mult_list; split; intros.
 simpl; auto.
 rewrite sublist_nil; simpl; auto.
Qed.

Lemma is_dyck_start_open :
  forall (a : Brace) (w : list Brace), isDyck (a::w) -> a = Open.
Proof.
intros.
elim H; intros; clear H H0.
assert (mult_list (sublist Brace 1 (a :: w)) Open >= mult_list (sublist Brace 1 (a :: w)) Close).
apply H1.
clear H1.
destruct a; auto.
simpl in H.
unfold mult_list in H; simpl in H.
rewrite if_close_close, if_close_open, sublist_0 in H.
compute in H.
omega.
Qed.

Lemma isDyck_dec :
  forall (l : list Brace), {isDyck l} + {~isDyck l}.
Proof.
intro l.
unfold isDyck.

Admitted. (* +++++++++++++++++++++++++ *)

Lemma hat_isDyck : isDyck (Open::Close::nil).
Proof.
unfold isDyck, mult_list; split; intros.
simpl.
rewrite if_open_open, if_open_close, if_close_open, if_close_close.
ring.
induction n.
auto.
simpl.
induction n.
simpl.
rewrite if_open_open, if_open_close.
auto.
simpl.
rewrite if_open_open, if_open_close, if_close_open, if_close_close.
simpl.
induction n; simpl; auto.
Qed.

Definition is_break (w : list Brace) (n : nat) : Prop :=
  mult_list (sublist Brace n w) Open
    = mult_list (sublist Brace n w) Close.

Lemma is_break_zero :
  forall (w : list Brace), isDyck w -> is_break w 0.
Proof.
intros.
unfold is_break.
rewrite sublist_0.
unfold mult_list.
simpl.
auto.
Qed.

Lemma is_break_lenght :
  forall (w : list Brace), isDyck w -> is_break w (length w).
Proof.
unfold isDyck, is_break; intros.
decompose [and] H; clear H; auto.
rewrite sublist_full; auto.
Qed.


Lemma break_is_Dyck :
  forall (w : list Brace) (n : nat),
    isDyck w -> is_break w n -> isDyck (sublist Brace n w).
Proof.
unfold isDyck, is_break; intros.
decompose [and] H; clear H; intros.
split; auto.
intros n0; elim le_gt_dec with n0 n; intros.
 rewrite subsublist_le; auto.
 rewrite subsublist_gt; auto.
Qed.


Lemma is_break_dec :
  forall (w : list Brace) (n : nat),
    {is_break w n} + {~is_break w n}.
Proof.
intros; unfold is_break; apply eq_nat_dec.
Qed.


Inductive first_break (w : list Brace) : Set :=
  fbreak : forall (n : nat), n > 0 -> is_break w n ->
    (forall (n0:nat), 0 < n0 <= n -> ~ is_break w n0)
      -> first_break w.

Theorem Dyck_first_break :
  forall (w : list Brace) (n : nat), isDyck w -> first_break w + { w = nil }.
Proof.
intros w n H.
elim w; intros.
right; auto.
left.
Admitted. (* +++++++++++++++++++++++++ *)

Inductive decomposition (w w1 w2 : list Brace) : Prop :=
  decomp : isDyck w1 -> isDyck w2 ->
      w = (Open::w1) ++ (Close::w2) -> decomposition w w1 w2.


Theorem Dyck_decompose :
  forall (w : list Brace), isDyck w ->
    { exists w1 w2 : list Brace, decomposition w w1 w2 } + { w = nil }.
Proof.
intros.
induction w.
right; auto.
elim H.
intros.
clear IHw.
left.

Admitted. (* +++++++++++++++++++++++++ *)

Theorem Dyck_decompose_unique :
  forall w wa1 wa2 wb1 wb2 : list Brace, decomposition w wa1 wa2 -> decomposition w wb1 wb2 ->
      wa1 = wb1 /\ wa2 = wb2.
Proof.

Admitted. (* +++++++++++++++++++++++++ *)

*)
