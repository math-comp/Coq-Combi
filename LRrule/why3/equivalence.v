(*
   here we prove the equivalence between definitions from
   - the Coq proof (in directory ..), and
   - the Why3 proof (in file lrrule.mlw)
*)

Add LoadPath "..".
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop.
(* Require Import tuple finfun finset path. *)
Require Import tuple finfun finset ssralg ssrnum ssrint bigop.
Require Import tools partition yama ordtype tableau std stdtab skewtab therule implem combclass.
(* import definitions from Why3 *)
Require Import ssrwhy3.
Require spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Local Open Scope ring_scope. *)


Import GRing.Theory Num.Theory.

Lemma cond_ltz_nat (P : int -> Prop) (l : nat) :
  (forall i : int, (0 <= i)%R /\ (i < l)%R -> P i) <->
  (forall i : nat,                i < l    -> P i).
Proof.
  split.
  + move=> H i Hi; apply H; by rewrite !lez_nat ltz_nat.
  + move=> H i [].
    case: i => i // _.
    rewrite ltz_nat; by apply H.
Qed.

Lemma cond_ltz_int (P : int -> int -> Prop) :
  (forall i j : int, (0 <= i)%R /\ (i < j)%R -> P i j) <->
  (forall i j : nat,                i < j    -> P i j).
Proof.
  split.
  - move=> H i j Hij; apply H;  by rewrite !lez_nat ltz_nat.
  - move=> H i [].
    + case: i => i j [] // _.
      rewrite ltz_nat; exact: H.
    + move=> j [] Hi Hij; exfalso.
      by have:= (ler_lt_trans Hi Hij).
Qed.

Lemma cond_lez_nat (P : int -> Prop) (l : nat) :
  (forall i : int, (0 <= i)%R /\ (i <= l)%R -> P i) <->
  (forall i : nat,                i <= l    -> P i).
Proof.
  split.
  + move=> H i Hi; apply H; by rewrite !lez_nat.
  + move=> H i [].
    case: i => i // _.
    rewrite lez_nat; by apply H.
Qed.

Lemma cond_lez_int (P : int -> int -> Prop) :
  (forall i j : int, (0 <= i)%R /\ (i <= j)%R -> P i j) <->
  (forall i j : nat,                i <= j    -> P i j).
Proof.
  split.
  - move=> H i j Hij; apply H; by rewrite !lez_nat.
  - move=> H i [].
    + case: i => i j [] // _.
      rewrite lez_nat; exact: H.
    + move=> j [] Hi Hij; exfalso.
      by have:= (ler_trans Hi Hij).
Qed.

Lemma cond_lez_ltz_nat (P : int -> int -> Prop) (l : nat) :
  (forall i j : int, (0 <= i)%R /\ (i <= j)%R /\ (j < l)%R -> P i j) <->
  (forall i j : nat,                i <= j /\     j < l    -> P i j).
Proof.
  split.
  + move=> H i j [] Hij Hj.
    apply H; by rewrite !lez_nat ltz_nat.
  + move=> H i j [].
    case: i => i // _ [].
    case: j => [j| [] //=].
    rewrite lez_nat ltz_nat => Hij Hj.
    by apply H.
Qed.

Lemma cond_ltz_ltz_nat (P : int -> int -> Prop) (l : nat) :
  (forall i j : int, (0 <= i)%R /\ (i < j)%R /\ (j < l)%R -> P i j) <->
  (forall i j : nat,                i < j /\     j < l    -> P i j).
Proof.
  split.
  + move=> H i j [] Hij Hj.
    apply H; by rewrite !lez_nat ltz_nat.
  + move=> H i j [].
    case: i => i // _ [].
    case: j => [j| [] //=].
    rewrite ltz_nat => Hij Hj.
    by apply H.
Qed.

Lemma spec_sum_nat (i j : nat) (f : int -> int) :
  spec.sum i j f = (\sum_( i <= k < j ) (f k))%R.
Proof.
  case: (leqP j i) => Hi.
  - have:= Hi; rewrite -lez_nat => /spec.sum_def1 ->.
    move: Hi; rewrite /index_iota /leq => /eqP -> /=.
    by rewrite big_nil.
  - rewrite /index_iota -{1}(subnKC (ltnW Hi)).
    move: (j-i) {Hi} => n.
    elim: n i => [|n IHn]/= i.
      by rewrite addn0 spec.sum_def1 // big_nil.
    rewrite spec.sum_left; first last.
      rewrite addnS ltz_nat ltnS; by apply leq_addr.
    by rewrite big_cons -PoszD addn1 -addSnnS IHn.
Qed.

Lemma spec_reindex s0 s (n : nat) (i : int):
  spec.numof (spec.fc s i) 0 n =
  spec.numof (spec.fc (s0 :: s) i) 1 (Posz n + 1).
Proof.
  elim: n => [//= | n IHn].
    by rewrite add0r !spec.Numof_empty.
  rewrite -addn1 PoszD.
  case: (boolP (spec.fc s i n)) => H.
  - rewrite spec.Numof_right_add; first last.
    + by rewrite addrK.
    + by rewrite ltz_nat !addn1.
    rewrite [RHS]spec.Numof_right_add; first last.
    + rewrite addrK.
      have : spec.fc s i n = true by [].
      by rewrite !spec.fc_def /= addn1.
    + by rewrite ltz_nat !addn1.
    by rewrite !addrK IHn.
  - rewrite spec.Numof_right_no_add; first last.
    + rewrite addrK.
      apply/eqP.
      move: H => /eqP.
      by apply contraL => /eqP ->.
    + by rewrite ltz_nat !addn1.
    rewrite [RHS]spec.Numof_right_no_add; first last.
    + rewrite addrK.
      apply/eqP.
      move: H => /eqP.
      apply contraL => /eqP H.
      suff -> : spec.fc s i n = true by [].
      move: H; rewrite !spec.fc_def.
      by rewrite -PoszD addn1.
    + by rewrite ltz_nat !addn1.
    by rewrite !addrK IHn.
Qed.

Lemma spec_numeqE s v (l : nat) :
  l <= size s -> spec.numof (spec.fc s v) 0 l = count_mem v (take l s).
Proof.
  rewrite /spec.numeq.
  elim: l s => [|l IHl] s.
    by rewrite spec.Numof_empty // take0.
  case: s => [| s0 s] //=.
  rewrite ltnS PoszD => /IHl <-.
  case: eqP => [-> {s0} | Hs0] /=.
  - rewrite spec.Numof_left_add //.
    + congr ( 1 + _)%R.
      rewrite -(addn1 l) PoszD add0r.
      by rewrite -spec_reindex.
    + by rewrite spec.fc_def.
  - rewrite spec.Numof_left_no_add //.
    + rewrite -(addn1 l) PoszD !add0r.
      by rewrite -spec_reindex.
    + by rewrite spec.fc_def /=.
Qed.

Fixpoint convert_part (a : array int) : (seq nat) :=
  if a is i :: tl then
    match i with
      | Posz 0 => [::]
      | Posz n => n :: (convert_part tl)
      | _      => [::]
    end
  else [::].

Definition convert_part_inv (len : nat) (p : seq nat) : array int :=
  mkseq (fun i => (nth 0 p i):int) len. (* why3 partition are non-empty *)

Lemma size_convert_part (a : array int) :
  size (convert_part a) <= size a.
Proof.
  elim: a => [//= | a0 a IHa] /=.
  case: a0 => [] //= [] //= n.
Qed.

Lemma nth_getE (a : array int) x i :
  i < size (convert_part a) -> get a i = nth x (convert_part a) i.
Proof.
  elim: a i x => [//= | a0 a IHa] i /=.
  case: a0 => [] //= [] //= a0 x.
  case: i => [| i] //=.
  rewrite ltnS => /IHa; by apply.
Qed.

Lemma get_convert_part_inv len p (i : nat) :
  size p <= len -> get (convert_part_inv len p) i = nth 0 p i.
Proof.
  rewrite /get /convert_part_inv /length => Hlen.
  case: (ltnP i len) => Hi.
  - by rewrite nth_mkseq.
  - rewrite !nth_default => //.
    * exact (leq_trans Hlen Hi).
    * by rewrite size_mkseq.
Qed.

Lemma part_nth_getE (a : array int) (i : nat) :
  spec.is_part a -> get a i = nth 0 (convert_part a) i.
Proof.
  rewrite /spec.is_part /length /= lez_nat => [] [] Hsz [].
  rewrite cond_lez_ltz_nat /length => Hpart /= Hlast.
  case (ltnP i (size (convert_part a))) => Hi; first by rewrite -nth_getE.
  rewrite (nth_default _ Hi).
  case (ltnP i (size a)) => Hi1; last by rewrite (nth_default _ Hi1).
  elim: a i Hi1 Hpart Hlast Hi {Hsz} => [//=|a0 a IHa] /= i.
  rewrite subn1 /=.
  case: i => [/= _ | i Hi] Hpart Hlast.
  - case: a0 Hpart Hlast => [[|]|i] //= Hpart Hlast _.
    exfalso.
    have /Hpart /= H1 : 0 <= (size a) /\ (size a) < (size a).+1 by [].
    by have := (ler_trans Hlast H1).
  - rewrite ltnS in Hi.
    case: a0 Hpart Hlast => [[|a0]|a0] //=.
    + move=> {IHa} Hpart Hlast _.
      apply ler_anti.
      have /Hpart /= -> /= : 0 <= i.+1 /\ i.+1 < (size a).+1 by [].
      have /Hpart /= H1 : i.+1 <= (size a) /\ (size a) < (size a).+1 by [].
      exact: (ler_trans Hlast).
    + rewrite ltnS => Hpart Hlast H.
      apply (IHa i Hi); last exact H.
      * move=> j k [] Hjk Hk /=.
        by apply (Hpart j.+1 k.+1).
      * case: a {IHa Hpart H} Hi Hlast => [//|a1 a] /= _.
        by rewrite subn1.
    + move => {IHa} Hpart Hlast _.
      exfalso.
      have /Hpart /= H1 : 0 <= (size a) /\ (size a) < (size a).+1 by [].
      by have := (ler_trans Hlast H1).
Qed.

(* Conversion preserve is_part *)
Lemma convert_part_impl (a : array int) :
  spec.is_part a -> is_part (convert_part a).
Proof.
  move=> H; apply/is_partP; split => [{H} |].
  - move: (X in last X.+1 _) => m.
    elim: a m => [| a0 a IHa] m //.
    by case: a0 => [] // [] // n.
  - move: H => [] Hlen [] Hdec Hlast i.
    case: (ltnP i.+1 (size (convert_part a))) => Hi.
    + rewrite -lez_nat -(nth_getE _ Hi) -nth_getE; last by apply: (leq_trans _ Hi).
      apply Hdec; repeat split => //.
      * by rewrite lez_nat.
      * rewrite ltz_nat; apply: (leq_trans Hi).
      by apply size_convert_part.
  - by rewrite nth_default.
Qed.

Lemma convert_part_inv_impl (p : seq nat) len :
  size p <= len -> 0 < len -> is_part p -> spec.is_part (convert_part_inv len p).
Proof.
  rewrite /spec.is_part /length cond_lez_ltz_nat lez_nat size_mkseq.
  move=> Hsz Hlen /is_part_ijP [] Hlast H.
  repeat split; first by [].
  + move=> i j [] Hij Hj.
    do 2 (rewrite get_convert_part_inv; last by []).
    rewrite lez_nat; exact: H.
  + case: len Hlen Hsz => [//= | len] _ Hsize.
    by rewrite /= subn1 /= -/(get _ len) get_convert_part_inv.
Qed.

(* On partition, conversion are invert one of each other *)
Lemma convert_partK (p : seq nat) len :
  size p <= len -> is_part p -> convert_part (convert_part_inv len p) = p.
Proof.
  rewrite /convert_part_inv.
  elim: p len => [| p0 p IHp] /= len Hsz.
    by case: len {Hsz} => [//| len].
  case: len Hsz => [//= | len].
  rewrite ltnS => /IHp {IHp}; rewrite /mkseq => Hrec /andP [] Hhead Hpart.
  rewrite /= -add1n iota_addl -map_comp.
  case: p0 Hhead.
    rewrite leqn0 => /part_head0F Habs; by rewrite Habs in Hpart.
  move=> n _; by rewrite -{2}(Hrec Hpart).
Qed.

Lemma convert_part_invK (a : array int) :
  spec.is_part a -> convert_part_inv (size a) (convert_part a) = a.
Proof.
  rewrite /convert_part_inv => Hpart.
  apply (eq_from_nth (x0 := 0 : int)); rewrite size_mkseq; first by [].
  move=> i Hi.
  by rewrite (nth_mkseq _ _ Hi) -part_nth_getE.
Qed.


(* Equivalence of inclusion of partition *)
Lemma convert_included_impl (a b : array int) :
  spec.included a b -> included (convert_part a) (convert_part b).
Proof.
  rewrite /spec.included /length => [] [] Hlen Hincl.
  have Hsize : size (convert_part a) <= size (convert_part b).
    elim: a b Hlen Hincl => [| a0 a IHa] [|b0 b] //= /eqP.
    rewrite eqz_nat eqSS => /eqP Hsize.
    case: a0 => [] //= [] //= a0.
    case: b0 => [[|b0]|b0] H /=.
    - exfalso; by have /H : (0 <= 0%:Z)%R /\ (0%:Z < (size b).+1)%R by [].
    - rewrite ltnS; apply IHa; first by rewrite Hsize.
      case=> i [] //= _; rewrite ltz_nat => Hi.
      suff /H /= : (0 <= i.+1%:Z)%R /\ (i.+1%:Z < (size b).+1)%R by [].
      split; first by rewrite lez_nat.
      by rewrite ltz_nat ltnS.
    - exfalso; by have /H : (0 <= 0%:Z)%R /\ (0%:Z < (size b).+1)%R by [].
  apply/includedP; split; first exact Hsize.
  move=> i.
  case: (ltnP i (size (convert_part a))) => Hi.
  + rewrite -lez_nat -(nth_getE _ Hi) -nth_getE; last by apply (leq_trans Hi).
    apply Hincl; split; first by [].
    rewrite ltz_nat; apply (leq_trans Hi).
    apply (leq_trans (size_convert_part a)).
    by rewrite -lez_nat Hlen.
  + by rewrite nth_default.
Qed.

Lemma convert_included_inv_impl (a b : seq nat) len :
  size b <= len -> included a b ->
  spec.included (convert_part_inv len a) (convert_part_inv len b).
Proof.
  rewrite /spec.included /length cond_ltz_nat => Hsize Hincl.
  rewrite !size_mkseq; split; first by [].
  elim: a b len Hincl Hsize => [|a0 a IHa] b len.
    move=> _ Hsize i Hi.
    by rewrite !get_convert_part_inv // nth_nil.
  case: b => [| b0 b] //.
  rewrite [included _ _]/= [size _]/= => /andP [] H0 Hincl.
  case: len => [// | len]; rewrite ltnS => Hsize.
  case=> [//= | i]; rewrite ltnS => /(IHa b len Hincl Hsize).
  move: Hincl => /includedP [] Hszab _.
  have Hsza := leq_trans Hszab Hsize.
  by rewrite !get_convert_part_inv.
Qed.

Lemma part_sumn_sum_arrayE sh :
  spec.is_part sh -> spec.sum_array sh = sumn (convert_part sh).
Proof.
  rewrite /spec.sum_array /spec.sum_sub_array=> Hpart.
  have:= Hpart => [] [].
  rewrite /length => Hlen _.
  case: sh Hlen Hpart => [//= | s0 sh] _ Hpart.
  rewrite [size _]/= -addn1 PoszD spec_sum_nat.
  rewrite (eq_bigr (fun n => Posz (nth 0 (convert_part (s0 :: sh)) n))); first last.
    move=> i _; exact: part_nth_getE.
  rewrite {Hpart} -(big_morph (id2 := 0) _ PoszD) //.
  apply/eqP; rewrite eqz_nat; apply/eqP.
  by rewrite addn1 sum_iota_sumnE; last exact: size_convert_part.
Qed.




(*
Lemma spec_eq_solE inner outer a b : spec.eq_sol inner outer a b <-> a = b.
Proof.
  rewrite /spec.eq_sol /spec.eq_rows.
  split => [|->]// [] /eqP; rewrite eqz_nat => /eqP.
  rewrite /spec.eq_prefix cond_ltz_nat /=.
  exact: eq_from_nth.
Qed.
*)

Section SpecFromWhy3.

Variable (outerw innerw evalw : array int).
Hypothesis Hinput : spec.valid_input outerw innerw.
Hypothesis Hvalideval :  spec.valid_eval evalw.
Hypothesis Hsum : spec.sum_array evalw =
  ((spec.sum_array outerw) - (spec.sum_array innerw))%R.

Lemma part_outerw : spec.is_part outerw.
Proof. by move: Hinput => [] _ []. Qed.

Lemma part_innerw : spec.is_part innerw.
Proof. by move: Hinput => [] _ []. Qed.

Lemma includedw : spec.included innerw outerw.
Proof. by move: Hinput => [] . Qed.

Lemma inputSpec_from_Why3 :
  inputSpec
    (convert_part innerw)
    (convert_part evalw)
    (convert_part outerw).
Proof.
  move: Hvalideval => [] _ [] Hparteval _.
  constructor.
  - exact: (convert_part_impl part_innerw).
  - exact: (convert_part_impl part_outerw).
  - exact: (convert_included_impl includedw).
  - exact: convert_part_impl.
  - apply/eqP; rewrite -eqz_nat -(part_sumn_sum_arrayE Hparteval) Hsum.
    rewrite (part_sumn_sum_arrayE part_innerw) (part_sumn_sum_arrayE part_outerw).
    rewrite sumn_diff_shape; last exact: (convert_included_impl includedw).
    rewrite subzn //.
    apply sumn_included.
    exact: (convert_included_impl includedw).
Qed.

Notation inner := (convert_part innerw).
Notation outer := (convert_part outerw).
Notation eval  := (convert_part evalw).
Notation width := (diff_shape inner outer).

Section SolCorrect.

Variable solw : matrix int.
Hypothesis Hsol : spec.is_solution outerw innerw evalw solw.

Lemma Hwork : spec.valid_work outerw innerw solw.
Proof. by move: Hsol => []. Qed.

Definition sol : seq (seq nat) :=
  mkseq (fun i =>
           [seq `|n| | n <- take (nth 0 width i) (nth [::] solw i)])
        (size outer).

Lemma size_sol : size sol = size outer.
Proof. by rewrite size_mkseq. Qed.

Lemma widthE (i : nat) : (spec.width outerw innerw) i = nth 0 width i.
Proof.
  rewrite /spec.width nth_diff_shape.
  rewrite (part_nth_getE _ part_innerw) (part_nth_getE _ part_outerw).
  move: inputSpec_from_Why3.(incl) => /includedP [] _ H.
  by rewrite (subzn (H i)).
Qed.

Lemma size_nth_solE i : i < size outer ->  size (nth [::] sol i) = nth 0 width i.
Proof.
  move=> Hi.
  rewrite (nth_mkseq _ _ Hi) size_map size_take.
  rewrite bad_if_leq // -lez_nat -{1}widthE.
  move: Hwork => [].
  case: solw => /= mat [nrows|//] [ncols|//] /= _ _ /= /eqP Hszmat /allP Hall [] Hsize.
  subst nrows; rewrite cond_ltz_nat => H.
  have -> : size (nth [::] mat i) = ncols.
    have := leq_trans Hi (size_convert_part outerw).
    by rewrite -Hsize => /(mem_nth [::])/Hall/eqP.
  apply H; apply (leq_trans Hi); exact: size_convert_part.
Qed.

Lemma shape_sol : shape sol = width.
Proof.
  apply (eq_from_nth (x0 := 0)); rewrite size_map size_mkseq.
  - by rewrite size_diff_shape.
  - move=> i Hi.
    rewrite (nth_map [::]); last by rewrite size_sol.
    exact: size_nth_solE.
Qed.

Lemma spec_sum_widthE (a b : nat) :
  spec.sum a b (spec.width outerw innerw) = \sum_(a <= i0 < b) nth 0 width i0.
Proof.
  rewrite spec_sum_nat.
  rewrite (eq_bigr (fun i => Posz (nth 0 width i))); last by move=> j _; exact: widthE.
  by rewrite -(big_morph (id2 := 0) _ PoszD).
Qed.

Lemma spec_sum_szouterw_widthE (a : nat) : a <= size outer ->
  spec.sum a (size outerw) (spec.width outerw innerw) =
  \sum_(a <= i0 < size outer) nth 0 width i0.
Proof.
  move=> Ha.
  rewrite spec_sum_widthE; apply/eqP; rewrite eqz_nat; apply/eqP.
  rewrite (big_cat_nat _ _ _ Ha (size_convert_part outerw)) /=.
  set B := (X in (_ + X)).
  suff -> : B = 0 by rewrite addn0.
  rewrite /B {B} big_seq_cond (eq_bigr (fun _ => 0)).
  + by rewrite -big_seq_cond sum_nat_const_nat muln0.
  + move=> j; rewrite /index_iota mem_iota => /andP [] /andP [] Hj _ _.
    apply nth_default; by rewrite size_diff_shape.
Qed.

Lemma size_to_wordE : size (to_word sol) = size (spec.to_word outerw innerw solw).
Proof.
  rewrite -size_to_word /size_tab shape_sol.
  have := spec.to_word_size includedw Hwork.
  rewrite spec_sum_widthE => /eqP; rewrite eqz_nat => /eqP ->.
  apply esym; apply sum_iota_sumnE.
  rewrite size_diff_shape; exact: size_convert_part.
Qed.

Lemma sols_pos r i :
  r < size outer -> i < nth 0 width r -> (matrix_get solw (Posz r, Posz i) >= 0)%R.
Proof.
  move => Hr Hi.
  rewrite -(@spec.to_word_contents outerw innerw); first last.
    - by rewrite widthE ?lez_nat ?ltz_nat.
    - rewrite ?lez_nat ?ltz_nat.
      by split; last exact: (leq_trans Hr (size_convert_part outerw)).
    - exact: Hwork.
    - exact: includedw.
  set k := (X in get _ X).
  move: Hsol => [] _ [] Heval _.
  move: Heval => [] _ [] Hval _.
  have {Hval} := Hval k; set Hyp := (X in ((X -> _) -> _)) => Hval.
  suff {Hval} /Hval [] : Hyp by [].
  rewrite /Hyp {Hyp} /k {k}; split; first by rewrite subrr spec_sum_widthE.
  rewrite -size_to_wordE -size_to_word /size_tab.
  rewrite -(sum_iota_sumnE (n := size outer)); last by rewrite shape_sol size_diff_shape.
  rewrite spec_sum_szouterw_widthE; last by rewrite addn1.
  rewrite ltz_nat.
  apply (leq_trans (n := \sum_(r <= i0 < size outer) nth 0 width i0)).
  - by rewrite (big_ltn Hr) addn1 ltn_add2r.
  - rewrite [X in (_ <= X)](eq_bigr (nth 0 width)); last by move=> k; rewrite shape_sol.
    have H : 0 <= r by [].
    rewrite (big_cat_nat _ _ _ H (ltnW Hr)) /=.
    exact: leq_addl.
Qed.

Lemma sol_contentsE r i :
  r < size outer -> i < nth 0 width r ->
  Posz (nth 0 (nth [::] sol r) i) = matrix_get solw (Posz r, Posz i).
Proof.
  rewrite /sol => Hr Hi.
  rewrite (nth_mkseq _ _ Hr) (nth_map (Posz 0)); first last.
    have := size_nth_solE Hr; rewrite /sol.
    by rewrite (nth_mkseq _ _ Hr) size_map => ->.
  rewrite /matrix_get witness_int_why3Type (nth_take _ Hi).
  apply gez0_abs; exact: sols_pos.
Qed.

Fixpoint slice_seq sh i :=
  if sh is s0 :: s then
    if i < s0 then (0, i)
    else let (r, c) := slice_seq s (i - s0) in (r.+1, c)
  else (0, i).

Lemma slice_seqE sh i :
  let (r, c) := (slice_seq sh i) in (\sum_(0 <= j < r) nth 0 sh j) + c = i.
Proof.
  elim: sh i => [| s0 s IHs] i //=; first by rewrite /index_iota /= big_nil.
  case: (ltnP i s0) => His0 //=; first by rewrite /index_iota /= big_nil.
  have {IHs} := IHs (i - s0); case: (slice_seq s (i - s0)) => r c.
  rewrite big_nat_recl //= -addnA => ->.
  exact: subnKC.
Qed.

Lemma slice_seqP sh i :
  i < sumn sh -> let (r, c) := (slice_seq sh i) in r < size sh /\ c < nth 0 sh r.
Proof.
  elim: sh i => [| s0 s IHs] i //= Hi.
  case: (ltnP i s0) => His0 //=.
  have {IHs} := IHs (i - s0); case: (slice_seq s (i - s0)) => r c /=.
  rewrite ltnS; apply.
  by rewrite -(subSn His0) leq_subLR.
Qed.

Lemma iota_gtn a b : [seq i <- iota 0 a | b <= i] = iota b (a - b).
Proof.
  elim: a => [//=| n IHn].
  rewrite -addn1 iota_add add0n /= filter_cat IHn {IHn} /=.
  case: leqP => Hb.
  - by rewrite addn1 (subSn Hb) -addn1 iota_add /= subnKC.
  - rewrite addn1 cats0.
    have := Hb; rewrite /leq => /eqP ->.
    by have := ltnW Hb; rewrite /leq => /eqP ->.
Qed.

Lemma sum_rev s r : r < size s ->
   \sum_(size s - r <= i0 < size s) nth 0 s i0 = \sum_(0 <= j < r) nth 0 (rev s) j.
Proof.
  move=> Hr.
  rewrite [RHS](big_nat_widen _ _ _ _ _ (ltnW Hr)) [RHS]big_nat_rev /= add0n.
  rewrite [RHS]big_seq_cond /= [RHS](eq_bigr (fun i => nth 0 s i)); first last.
    move=> i /andP []; rewrite mem_iota !add0n subn0 => /andP [] _ His Hi.
    rewrite nth_rev; last by apply (ltn_trans Hi).
    congr nth; by rewrite -(subSn His) subSS (subKn (ltnW His)).
  rewrite -big_seq_cond /=.
  rewrite -[RHS]big_filter /index_iota subn0.
  congr bigop.
  rewrite (eq_in_filter (a2 := fun i => size s - r <= i)); first by rewrite iota_gtn.
  move => i; rewrite mem_iota add0n => /andP [] _ Hi.
  by rewrite -(subSn Hi) subSS !leq_subLR addnC.
Qed.

Lemma index_slice i :
  i < size (to_word sol) ->
  let (r, c) := (slice_seq (rev width) i) in
  let rr := size width - r.+1 in
  [/\ r < size outer,
      rr < size outer,
      c < nth 0 width rr &
      c + \sum_(rr + 1 <= i0 < size outer) nth 0 width i0 = i ].
Proof.
  move=> Hi; have := (slice_seqE (rev width) i).
  have Hszout : size outer > 0.
    move: Hi; apply contraLR; rewrite -!leqNgt.
    rewrite -size_to_word /size_tab shape_sol leqn0 => /eqP Hszout.
    have:= eq_refl (size width); by rewrite {2}size_diff_shape Hszout => /nilP ->.
  move: Hi; rewrite -size_to_word /size_tab -sumn_rev => /slice_seqP.
  rewrite shape_sol.
  case: (slice_seq (rev width) i) => r c [].
  rewrite size_rev => Hr.
  rewrite (nth_rev _ Hr) => Hc Heq.
  split => //=.
  - move: Hr; by rewrite size_diff_shape.
  - rewrite size_diff_shape -subSn; last by rewrite -(size_diff_shape inner).
    rewrite subSS; exact: leq_subr.
  - rewrite -Heq addnC; congr (_ + _).
    rewrite -(size_diff_shape inner outer) addn1 (subnSK Hr).
    exact: sum_rev.
Qed.

Lemma nth_flatten T (x : T) tab i :
  nth x (flatten tab) i = let (r, c) := (slice_seq (shape tab) i) in
                          nth x (nth [::] tab r) c.
Proof.
  elim: tab i => [| t0 t IHt] //= i.
  rewrite nth_cat; case: ltnP => //= Hi.
  rewrite IHt {IHt}; by case: (slice_seq (shape t) (i - size t0)) => r c.
Qed.

Lemma to_wordE : to_word sol = [seq `|i| | i <- spec.to_word outerw innerw solw].
Proof.
  apply (eq_from_nth (x0 := 0)).
  - by rewrite size_map size_to_wordE.
  - move=> i Hi.
    rewrite /to_word nth_flatten shape_rev shape_sol.
    rewrite (nth_map (Posz 0)); last by rewrite -size_to_wordE.
    have := index_slice Hi.
    case: (slice_seq (rev width) i) => r c [] Hr Hr1 Hl <-.
    have:= (@spec.to_word_contents outerw innerw _ includedw Hwork).
    rewrite cond_ltz_nat => Hspec.
    have {Hspec} /Hspec := leq_trans Hr1 (size_convert_part outerw).
    rewrite widthE cond_ltz_nat => Hspec.
    have {Hspec} := Hspec _ Hl.
    rewrite spec_sum_szouterw_widthE /=; last by rewrite addn1.
    move => ->.
    move: Hr1 Hl; rewrite size_diff_shape => Hr1 Hl.
    rewrite nth_rev; last by rewrite size_sol.
    rewrite /sol size_mkseq (nth_mkseq _ _ Hr1).
    rewrite (nth_map (Posz 0)); first last.
      rewrite size_take bad_if_leq // -lez_nat -widthE.
      move: Hsol; rewrite /spec.is_solution => [] [] [] Hnrows.
      rewrite cond_ltz_nat => H _.
      have {H} := H _ (leq_trans Hr1 (size_convert_part outerw)).
      rewrite /spec.width.
      suff -> : ncols solw = size (nth [::] solw (size outer - r.+1)) by [].
      case: solw Hnrows => mat [nrows | //=] [ncols | //=] /= _ _ /eqP <- {nrows}.
      move=> /allP Hall /eqP; rewrite eqz_nat => /eqP Hsz.
      have := leq_trans Hr1 (size_convert_part outerw).
      by rewrite -Hsz => /(mem_nth [::])/Hall/=/eqP ->.
    by rewrite nth_take.
Qed.

(* Ok upto there ************)

Lemma count_mem_numeqE n i :
  Posz (count_mem i (drop n (to_word sol_from_Why3))) =
  spec.numeq sol i 0 (size sol - n)%N.
Proof.
  rewrite /spec.numeq to_word_sol_from_Why3 spec_numeqE; last exact: leq_subr.
  rewrite drop_rev count_rev size_map.
  apply /eqP; rewrite eqz_nat; apply/eqP.
  rewrite -map_take.
  move: (size sol - n) => {n} n.
  move: Hsol => [] [] _ []; rewrite cond_ltz_nat => Hpos _ _.
  have {Hpos} Hpos i0 : i0 < size sol -> (0 <= get sol i0)%R by move/Hpos => [].
  elim : sol n Hpos => [// | s0 s IHs] n Hpos /=.
  case: n => [//= | n] /=.
  rewrite -eqz_nat.
  have /Hpos /= /gez0_abs -> : 0 < size (s0 :: s) by [].
  congr (_ + _); apply IHs => j Hj.
  by have /Hpos : j.+1 < size (s0 :: s) by [].
Qed.

Lemma is_yam_sol : is_yam (to_word sol_from_Why3).
Proof.
  have Hlensol := spec.solution_length Hvalidsh Hsol.
  rewrite /sol_from_Why3; move: Hsol => [] [] Hyam _ _.
  apply/is_yamP => i n.
  move: Hyam => [] _ [].
  rewrite cond_ltz_nat => Hpos Hyam.
  rewrite -lez_nat !count_mem_numeqE.
  apply Hyam; split => //.
  - rewrite /length lez_nat.
    exact: leq_subr.
  - by rewrite lez_nat.
Qed.

Lemma numeq_false (s : array int) (i : int) :
  (forall j : int,
     (0 <= j)%R /\ (j < length s)%R -> ~ (get s j = i)%R) ->
  spec.numeq s i 0 (length s) = 0.
Proof.
  rewrite cond_ltz_nat /length /spec.numeq.
  elim: s => [_ | s0 s IHs]; first by rewrite spec.Numof_empty.
  move=> H; rewrite spec.Numof_left_no_add //.
  + rewrite /= -addn1 PoszD add0r.
    rewrite -spec_reindex IHs // => j Hj.
    by have /H /= : j.+1 < size (s0 :: s) by [].
  + rewrite spec.fc_def; by apply H.
Qed.

Lemma eval_sol : evalseq (to_word sol_from_Why3) = convert_part eval.
Proof.
  move: Hsol => [] [] _ [] Hval Hnumeq _.
  apply/eqP/part_eqP.
  - exact: (is_part_eval_yam is_yam_sol).
  - apply convert_part_impl.
    by move: Hvalideval => [] _ [].
  - move=> i; rewrite nth_evalseq.
    apply /eqP; rewrite -eqz_nat; apply/eqP.
    rewrite -[to_word _]drop0 count_mem_numeqE subn0.
    case: (ltnP i (size eval)) => Hi.
    - rewrite -/(length sol) Hnumeq; last by rewrite lez_nat ltz_nat.
      rewrite part_nth_getE //.
      by move: Hvalideval => [] _ [].
    - rewrite nth_default; last exact: (leq_trans (size_convert_part _) _).
      apply numeq_false => j /Hval [] _ Hget.
      apply/eqP; suff : (get sol j < i)%R by rewrite ltr_def eq_sym => /andP [].
      apply (ltr_le_trans Hget).
      by rewrite /length lez_nat.
Qed.

Lemma end_of_rowE (i : nat) :
  i < size outer ->
  get (spec.end_of_row sh) i.+1 = \sum_(0 <= k < i.+1) nth 0 (diff_shape inner outer) k.
Proof.
  have := Hvalidsh => [] [] _ [] [] /eqP; rewrite eqz_nat => /eqP Hsizeeor [] _ Heor _ Hi.
  have Hszout : size outer < size (spec.outer sh).
    rewrite /outer.
    move Hconv : (convert_part (spec.outer sh)) => cv.
    case: cv Hconv => [//= | cv0 cv] Hconv.
      have := Hvalidsh => [] [] [] []; rewrite lez_nat => Hsz _ _ _.
      exact: (leq_trans _ Hsz).
    rewrite  -/(size (cv0 :: cv)) -Hconv.
    exact: size_convert_part.
  have {Heor} /Heor -> : (1 <= Posz i.+1)%R /\ (Posz i.+1 < size (spec.end_of_row sh))%R.
    rewrite lez_nat ltz_nat Hsizeeor; split => //.
    by apply (leq_ltn_trans Hi).
  rewrite spec_sum_nat /index_iota subn0 subn1 -add1n iota_addl big_map.
  rewrite (big_morph (id1 := Posz 0) _ PoszD) //.
  apply eq_bigr => j _.
  rewrite add1n nth_diff_shape nth_inner nth_outer.
  apply subzn.
  have:= (inputSpec_from_Why3.(incl)) => /includedP [] _.
  by apply.
Qed.

Lemma get_sol_from_Why3 r i :
  r < size sol_from_Why3 -> i < size (nth [::] sol_from_Why3 r) ->
  nth 0 (nth [::] sol_from_Why3 r) i =
  `|get sol ((get (spec.end_of_row sh) r.+1) - (Posz i.+1))|.
Proof.
  move=> Hr.
  have := Hr; rewrite {1}/sol_from_Why3 size_skew_reshape => Hrouter.
  have <- : nth 0 (shape sol_from_Why3) r = size (nth [::] sol_from_Why3 r).
    rewrite /shape; by apply nth_map.
  rewrite shape_sol_from_Why3 => Hi.
  rewrite /sol_from_Why3 /skew_reshape.
  rewrite -rev_reshape; last by rewrite size_rev size_map sumn_rev size_sol.
  rewrite !revK (nth_map [::]); last by rewrite size_reshape size_diff_shape.
  have := Hvalidsh => [] [] _ [] [] /eqP; rewrite eqz_nat => /eqP Hsizeeor _ _.
  rewrite (end_of_rowE Hrouter).
  set tab := reshape _ _.
  have Hszrow : size (nth [::] tab r) = nth 0 (diff_shape inner outer) r.
    rewrite /tab -(nth_map _ 0 size); last by rewrite size_reshape size_diff_shape.
    by rewrite -/(shape _) reshapeKl; last by rewrite size_map size_sol.
  rewrite nth_rev; last by rewrite Hszrow.
  rewrite Hszrow {Hszrow} /tab nth_reshape.
  have Htmp : nth 0 (diff_shape inner outer) r - i.+1 < nth 0 (diff_shape inner outer) r.
    move: Hi; case: (nth _ _ _) => [//=| n] _.
    rewrite ltnS subSS; exact: leq_subr.
  rewrite -map_drop -map_take /= (nth_map (Posz 0)); first last.
    rewrite size_take size_drop size_sol bad_if_leq; first exact Htmp.
    elim: r (diff_shape _ _) {Hr Hrouter Hi Htmp} => [| r IHr] [|s0 s] //=.
      rewrite subn0; exact: leq_addr.
    rewrite subnDl; exact: IHr.
  congr `|_|.
  rewrite (nth_take _ Htmp) {Htmp} nth_drop.
  set A := (X in nth _ sol X); set B := (_ - _)%R.
  suff -> : B = A by [].
  rewrite /A /B {A B} sumn_take /index_iota !subn0 -addn1 iota_add /=.
  rewrite big_cat big_cons big_nil /= add0n addn0.
  move: Hi; move: (\sum_(i <- _) _) (nth _ _ _) => A B Hi.
  rewrite (addnBA _ Hi) subzn //.
  apply (leq_trans Hi).
  exact: leq_addl.
Qed.

Lemma skew_tab_sol : is_skew_tableau inner sol_from_Why3.
Proof.
  move: Hsol => [] _ [] Hrow Hdom.
  apply/is_skew_tableauP; split.
  - rewrite /sol_from_Why3 size_skew_reshape.
    exact: (size_included inputSpec_from_Why3.(incl)).
  - rewrite size_skew_reshape => i Hi.
    have -> : size (nth [::] sol_from_Why3 i) = nth 0 (shape sol_from_Why3) i.
      rewrite /shape; apply esym; apply nth_map.
      by rewrite size_skew_reshape.
    rewrite shape_sol_from_Why3 nth_diff_shape subnKC.
    apply: (nth_part_non0 inputSpec_from_Why3.(outer_part) Hi).
  - have /includedP := inputSpec_from_Why3.(incl) => [] [] _.
    by apply.
  - move=> r; case: (ltnP r (size sol_from_Why3)) => Hr; last by rewrite nth_default.
    apply /(is_rowP 0) => i j /andP [] Hij Hj.
    rewrite (get_sol_from_Why3 Hr (leq_ltn_trans Hij Hj)).
    rewrite (get_sol_from_Why3 Hr Hj) leqXnatE.
    admit.
  - admit.
Qed.

Lemma shape_sol :
   shape sol_from_Why3 = diff_shape inner outer.
Proof.
  rewrite /sol_from_Why3 shape_skew_reshape //.
  - apply inputSpec_from_Why3.(incl).
  - by rewrite size_rev size_map size_sol.
Qed.

Lemma is_solution_correct :
  outputSpec inner (convert_part eval) outer sol_from_Why3.
Proof.
  constructor.
  - exact: skew_tab_sol.
  - exact: shape_sol.
  - exact: is_yam_sol.
  - exact: eval_sol.
Qed.

End SolCorrect.

Section SolCompl.

Variable tab : seq (seq nat).
Hypothesis Hout : outputSpec inner (convert_part eval) outer tab.

Definition sol_from_tab : array int := [seq Posz i | i <- rev (to_word tab)].

Lemma is_yam_ev_sol : spec.is_yam_of_eval eval sol_from_tab.
Proof.
  rewrite /sol_from_tab.
  move: Hout => [] _ Heval /is_yam_ijP Hyam Hev.
  repeat split.
  - by [].
  - rewrite cond_ltz_nat size_map => i /= Hi.
    by rewrite (nth_map 0 _ _ Hi) lez_nat.
  - rewrite cond_lez_nat => l Hl.
    have:= Hl; rewrite size_map size_rev -evalseq_eq_size Hev cond_lez_int => Hl1 i j Hij.
    rewrite /spec.numeq !spec_numeqE // lez_nat.
    rewrite map_rev take_rev !count_rev -map_drop !count_map.
    rewrite [X in (X <= _)](eq_count (a2 := (pred1 j))); last by [].
    rewrite [X in (_ <= X)](eq_count (a2 := (pred1 i))); last by [].
    by apply Hyam.
  - move: i H; rewrite cond_ltz_nat size_map => i /= Hi.
    by rewrite (nth_map 0 _ _ Hi) lez_nat.
  - move: i H; rewrite cond_ltz_nat size_map => i /= Hi.
    rewrite (nth_map 0 _ _ Hi) ltz_nat.
    apply: (leq_trans _ (size_convert_part _)).
    have {Hi} := mem_nth 0 Hi => /count_memPn.
    move: (nth _ _ _) => {i} i.
    rewrite count_rev -nth_evalseq Hev => /eqP.
    apply contraR; rewrite -ltnNge ltnS // => Hi.
    by rewrite nth_default.
  - rewrite cond_ltz_nat => i Hi.
    rewrite /spec.numeq spec_numeqE // take_size.
    rewrite map_rev count_rev count_map.
    rewrite (eq_count (a2 := (pred1 i))); last by [].
    rewrite -nth_evalseq Hev part_nth_getE //.
    by move: Hvalideval => [] _ [].
Qed.

Lemma is_tab_sol : spec.is_tableau_reading sh sol_from_tab.
Proof.
  admit.
Qed.

Lemma is_solution_compl : spec.is_solution sh eval sol_from_tab.
Proof.
  split.
  - exact is_yam_ev_sol.
  - exact: is_tab_sol.
Qed.

End SolCompl.

Lemma sol_from_Why3K a : spec.is_solution sh eval a -> sol_from_tab (sol_from_Why3 a) = a.
Proof.
  move=> H; have Hsz:= size_sol H.
  move: H => [] [] _ []; rewrite cond_ltz_nat => Hsol _.
  have {Hsol} Hsol i : i < size a -> (0 <= get a i)%R by move=> /Hsol [].
  rewrite /sol_from_tab /sol_from_Why3 => _.
  rewrite (to_word_skew_reshape inputSpec_from_Why3.(incl));
    last by rewrite size_rev size_map.
  rewrite revK -map_comp.
  apply (eq_from_nth (x0 := Posz 0)); rewrite size_map => // i Hi /=.
  rewrite (nth_map (Posz 0) _ _ Hi) /=.
  exact (gez0_abs (Hsol _ Hi)).
Qed.

Lemma sol_from_tabK tab :
  shape tab = diff_shape inner outer -> tab = sol_from_Why3 (sol_from_tab tab).
Proof.
  have:= inputSpec_from_Why3 => [] [] Hpartinner Hpartouter Hincl Hparteval Hs.
  rewrite /sol_from_Why3 /sol_from_tab !map_rev revK -map_comp => Hshape.
  rewrite map_id_in; last by [].
  rewrite -(diff_shapeK Hincl) -Hshape skew_reshapeK //.
  rewrite -(size_map size tab) -/(shape tab) Hshape size_diff_shape.
  by apply size_included.
Qed.


Section Correction.

Variable s : spec.solutions.
Hypothesis Hcorr : spec.good_solutions sh eval s.

Notation d1 := (sumn inner).
Lemma Hinn_dep : is_part_of_n d1 inner.
Proof.
  have:= inputSpec_from_Why3 => [] [] Hpartinner _ _ _ _.
  by rewrite /= /d1 eq_refl.
Qed.
Notation P1 := (IntPartN Hinn_dep).

Notation d2 := (sumn (convert_part eval)).
Lemma Heval_dep : is_part_of_n d2 (convert_part eval).
Proof.
  have:= inputSpec_from_Why3 => [] [] Hpartinner Hpartouter Hincl Hparteval Hs.
  by rewrite /= /d2 eq_refl.
Qed.
Notation P2 := (IntPartN Heval_dep).

Lemma Hout_dep : is_part_of_n (d1 + d2) outer.
Proof.
  have:= inputSpec_from_Why3 => [] [] Hpartinner Hpartouter Hincl Hparteval Hs.
  by rewrite /= Hs (sumn_diff_shape Hincl) (subnKC (sumn_included Hincl)) eq_refl.
Qed.
Notation P := (IntPartN Hout_dep).

Lemma Hincl_dep : included P1 P.
Proof.
   have:= inputSpec_from_Why3 => [] [] Hpartinner Hpartouter Hincl Hparteval Hs.
   by [].
Qed.

Definition N := `|spec.next s|.
Lemma spec_nextE : spec.next s = N.
Proof. rewrite /N; move: Hcorr => []; by case: (spec.next s). Qed.

Definition sols := [seq sol_from_Why3 (spec.s2a (spec.sols s (Posz i))) | i <- iota 0 N ].

Lemma all_yamev_sols : all (is_yam_of_eval P2) (map (@to_word _) sols).
Proof.
  move: Hcorr => []; rewrite spec_nextE => _ [] Hsort [].
  rewrite cond_ltz_nat => Hsol Hcompl.
  rewrite /sols; apply/allP => x /mapP [] y /mapP [] i.
  rewrite mem_iota add0n => /andP [] _ /Hsol Hi -> -> {x y} /=.
  by rewrite /is_yam_of_eval (eval_sol Hi) (is_yam_sol Hi) /=.
Qed.

Lemma uniq_sols : uniq sols.
Proof.
  rewrite /sols.
  move: Hcorr => []; rewrite spec_nextE => _ [].
  rewrite /spec.sorted cond_ltz_ltz_nat => Hsort [].
  rewrite cond_ltz_nat => Hsol _.
  rewrite map_comp map_inj_in_uniq.
  - rewrite map_inj_in_uniq; first exact: iota_uniq.
    move=> i j; rewrite !mem_iota !add0n => /andP [] _ Hi /andP [] _ Hj Heq.
    case: (ltngtP i j) => // Hij; exfalso.
    - have /Hsort/spec.lt_not_eq : i < j /\ j < N by [].
      apply; by rewrite Heq.
    - have /Hsort/spec.lt_not_eq : j < i /\ i < N by [].
      apply; by rewrite Heq.
  - move=> a b /mapP [] ia; rewrite mem_iota add0n => /andP [] _ /Hsol Ha Hia.
    move=>     /mapP [] ib; rewrite mem_iota add0n => /andP [] _ /Hsol Hb Hib.
    rewrite -Hia in Ha; rewrite -Hib in Hb => {Hia Hib ia ib Hsol Hsort} H.
    by rewrite -(sol_from_Why3K Ha) -(sol_from_Why3K Hb) H.
Qed.

Lemma to_word_sol_inj : {in sols &, injective (@to_word nat_ordType)}.
Proof.
  move: Hcorr => []; rewrite spec_nextE => _ [] _ [].
  rewrite cond_ltz_nat => Hsol _.
  move=> a b. rewrite /sols map_comp => /mapP [] y /mapP [] i.
  rewrite mem_iota add0n => /andP [] _ /Hsol Hi -> -> {y} /=.
  move => /mapP [] y /mapP [] j.
  rewrite mem_iota add0n => /andP [] _ /Hsol Hj -> -> /= H.
  suff -> : (spec.s2a (spec.sols s i)) = (spec.s2a (spec.sols s j)) by [].
  by rewrite -(sol_from_Why3K Hi) -(sol_from_Why3K Hj) /sol_from_tab H.
Qed.

Definition sols_dep := subType_seq [subCountType of yameval P2] all_yamev_sols.
Lemma size_sols_dep : N = size sols_dep.
Proof. by rewrite /sols_dep -(size_map val) subType_seqP /sols !size_map size_iota. Qed.

Local Notation Spec := inputSpec_from_Why3.

Theorem Why3Correct : spec.next s = LRcoeff inner (convert_part eval) outer.
Proof.
  move: Hcorr => []; rewrite spec_nextE => _ [] Hsort [].
  rewrite cond_ltz_nat => Hsol Hcompl.
  apply/eqP; rewrite eqz_nat; apply/eqP.
  have /= <- := @LR_yamtabE d1 d2 P1 P2 P Hincl_dep.
  rewrite /LRyam_coeff -sum1dep_card.
  rewrite (eq_bigr (fun y => count_mem y sols_dep)); first last.
    move=> [] yam Hyamev /=.
    have := Hyamev; rewrite /is_yam_of_eval => /andP [] Hyam /eqP Hev.
    have Hszwdep : size yam = sumn (diff_shape P1 P).
      by rewrite /= -Spec.(sumn_eq) -evalseq_eq_size Hev /=.
    move=> /(is_skew_reshape_tableauP Hincl_dep Hszwdep) [] tab [] Htab Hshape Hyamtab.
    rewrite (eq_count (a2 := preim val (pred1 yam))); first last.
      move=> w /=; apply/(sameP idP); apply(iffP idP).
      - by move=> /eqP H; apply/eqP; apply val_inj => /=.
      - by move/eqP => -> /=.
    rewrite -count_map subType_seqP -Hyamtab.
    have Huniq : uniq [seq to_word i | i <- sols].
      rewrite map_inj_in_uniq; first exact uniq_sols.
      exact: to_word_sol_inj.
    rewrite (count_uniq_mem _ Huniq).
    suff : tab \in sols by move=> /map_f ->.
    have /is_solution_compl/Hcompl : outputSpec inner (convert_part eval) outer tab.
      by constructor => //; rewrite Hyamtab.
    move=> [] i [] Hi; move: i Hi; rewrite cond_ltz_nat => i Hi.
    rewrite spec_eq_solE => Htabsol.
    rewrite /sols; apply /mapP; exists i; first by rewrite mem_iota add0n Hi.
    rewrite -Htabsol.
    exact: sol_from_tabK.
  rewrite {Hcompl} sum_count_mem size_sols_dep.
  rewrite (eq_in_count (a2 := predT));
    first by rewrite count_predT -(size_map val) subType_seqP.
  move=> yam /=.
  rewrite -(mem_map val_inj) subType_seqP /= => /mapP [] tab.
  move=> /mapP [] i.
  rewrite mem_iota add0n => /andP [] _ /Hsol Hi -> -> {tab yam}.
  move: (spec.s2a (spec.sols s i)) Hi => sol {i} => Hsolok.
  have Hskew := skew_tab_sol Hsolok.
  have Hshape := shape_sol Hsolok.
  rewrite /is_skew_reshape_tableau.
  have <- /= : (outer_shape P1 (shape (sol_from_Why3 sol))) = P.
    rewrite Hshape diff_shapeK //.
    exact: Spec.(incl).
  rewrite skew_reshapeK; first by rewrite Hskew.
  rewrite /sol_from_Why3 size_skew_reshape.
  exact: (size_included (Spec.(incl))).
Qed.

End Correction.

End SpecFromWhy3.

