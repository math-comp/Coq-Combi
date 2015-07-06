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

Definition cond_nat := (cond_lez_nat, cond_ltz_nat,
                        cond_lez_int, cond_ltz_int,
                        cond_lez_ltz_nat, cond_ltz_ltz_nat).

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

Lemma spec_numeq_shift w0 w a (i j : nat) :
   spec.numeq w a i j = spec.numeq (w0 :: w) a i.+1 j.+1.
Proof.
  rewrite (spec.numeq_shift (a2 := w0 :: w)) /=; first by rewrite -!PoszD !addn1.
  repeat split => //=.
  case => n [] //= _ _.
  by rewrite addn1.
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
  rewrite !cond_nat /length => Hpart /= Hlast.
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
  rewrite /spec.is_part /length !cond_nat lez_nat size_mkseq.
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
  rewrite /spec.included /length cond_nat => Hsize Hincl.
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

Lemma part_evalw : spec.is_part evalw.
Proof. by move: Hvalideval => [] _ []. Qed.

Lemma inputSpec_from_Why3 :
  inputSpec
    (convert_part innerw)
    (convert_part evalw)
    (convert_part outerw).
Proof.
  constructor.
  - exact: (convert_part_impl part_innerw).
  - exact: (convert_part_impl part_outerw).
  - exact: (convert_included_impl includedw).
  - exact: (convert_part_impl part_evalw).
  - apply/eqP; rewrite -eqz_nat -(part_sumn_sum_arrayE part_evalw) Hsum.
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

Lemma inner_decr r : nth 0 inner r.+1 <= nth 0 inner r.
Proof. have := is_partP _ inputSpec_from_Why3.(inner_part) => [] [] _; by apply. Qed.
Lemma outer_decr r : nth 0 outer r.+1 <= nth 0 outer r.
Proof. have := is_partP _ inputSpec_from_Why3.(outer_part) => [] [] _; by apply. Qed.
Lemma le_inner_outer r : nth 0 inner r <= nth 0 outer r.
Proof. have := (includedP _ _ inputSpec_from_Why3.(incl)) => [] [] _; by apply. Qed.

Lemma widthE (i : nat) : (spec.width outerw innerw) i = nth 0 width i.
Proof.
  rewrite /spec.width nth_diff_shape.
  rewrite (part_nth_getE _ part_innerw) (part_nth_getE _ part_outerw).
  by rewrite (subzn (le_inner_outer i)).
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

Lemma index_slice i :
  i < sumn width ->
  let (r, c) := (shape_nth (rev width) i) in
  let rr := size width - r.+1 in
  [/\ r < size outer,
      rr < size outer,
      c < nth 0 width rr &
      c + \sum_(rr + 1 <= i0 < size outer) nth 0 width i0 = i ].
Proof.
  move=> Hi; have := (shape_nthE (rev width) i).
  have Hszout : size outer > 0.
    move: Hi; apply contraLR; rewrite -!leqNgt.
    rewrite leqn0 => /eqP Hszout.
    have:= eq_refl (size width); by rewrite {2}size_diff_shape Hszout => /nilP ->.
  move: Hi; rewrite -sumn_rev => /shape_nthP.
  case: (shape_nth (rev width) i) => r c [].
  rewrite size_rev => Hr.
  rewrite (nth_rev _ Hr) => Hc Heq.
  split => //=.
  - move: Hr; by rewrite size_diff_shape.
  - rewrite size_diff_shape -subSn; last by rewrite -(size_diff_shape inner).
    rewrite subSS; exact: leq_subr.
  - rewrite -Heq addnC; congr (_ + _).
    rewrite -(size_diff_shape inner outer) addn1 (subnSK Hr).
    by rewrite sum_nth_rev subn0.
Qed.


Section ToWord.

Variable solw : matrix int.
Hypothesis Hwork : spec.valid_work outerw innerw solw.

Lemma size_nth_solw i :
  nth 0 width i <= size (nth [::] solw i).
Proof.
  rewrite -lez_nat -{1}widthE.
  move: Hwork => [].
  case: solw => /= mat [nrows|//] [ncols|//] /= _ _ /= /eqP Hszmat /allP Hall [] Hsize.
  subst nrows; rewrite cond_nat => H.
  case: (ltnP i (size mat)) => Hi.
  - have -> : size (nth [::] mat i) = ncols.
      by move: Hi => /(mem_nth [::])/Hall/eqP.
    apply H; by rewrite -Hsize.
  - rewrite /spec.width /= (nth_default _ Hi).
    have:= Hi; rewrite Hsize => /(nth_default _) ->.
    move: Hinput Hi => [] [] /eqP; rewrite eqz_nat => /eqP.
    by rewrite Hsize => <- _ _ /(nth_default _) ->.
Qed.


Hypothesis Hsol_pos : forall r i : nat,
  r < size outer -> i < nth 0 width r -> (matrix_get solw (Posz r, Posz i) >= 0)%R.

Definition sol : seq (seq nat) :=
  mkseq (fun i =>
           [seq `|n| | n <- take (nth 0 width i) (nth [::] solw i)])
        (size outer).

Lemma size_sol : size sol = size outer.
Proof. by rewrite size_mkseq. Qed.

Lemma size_nth_solE i : i < size outer -> size (nth [::] sol i) = nth 0 width i.
Proof.
  move=> Hi.
  rewrite (nth_mkseq _ _ Hi) size_map size_take.
  by rewrite (bad_if_leq (size_nth_solw _)).
Qed.

Lemma shape_sol : shape sol = width.
Proof.
  apply (eq_from_nth (x0 := 0)); rewrite size_map size_mkseq.
  - by rewrite size_diff_shape.
  - move=> i Hi.
    rewrite (nth_map [::]); last by rewrite size_sol.
    exact: size_nth_solE.
Qed.

Lemma size_to_wordE : size (to_word sol) = size (spec.to_word outerw innerw solw).
Proof.
  rewrite -size_to_word /size_tab shape_sol.
  have := spec.to_word_size includedw Hwork.
  rewrite spec_sum_widthE => /eqP; rewrite eqz_nat => /eqP ->.
  apply esym; apply sum_iota_sumnE.
  rewrite size_diff_shape; exact: size_convert_part.
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
  apply gez0_abs; exact: Hsol_pos.
Qed.

Lemma Hnrows : nrows solw = size outerw.
Proof. by move: Hwork => []. Qed.

Lemma Hncols_solw :
  forall r : nat, r < size outerw -> (get outerw r - get innerw r <= ncols solw)%R.
Proof. move: Hwork => [] _; by rewrite cond_nat. Qed.

Notation wordw := (spec.to_word outerw innerw solw).

Lemma to_wordE : [seq Posz i | i <- to_word sol] =  wordw.
Proof.
  apply (eq_from_nth (x0 := Posz 0)); rewrite size_map.
  - by rewrite size_to_wordE.
  - move=> i Hi.
    rewrite /to_word (nth_map 0 _ _ Hi) nth_flatten shape_rev shape_sol.
    have:= Hi; rewrite -size_to_word /size_tab shape_sol => Hiw.
    have := index_slice Hiw.
    case: (shape_nth (rev width) i) => r c [] Hr Hr1 Hl <-.
    have:= (@spec.to_word_contents outerw innerw _ includedw Hwork).
    rewrite !cond_nat => Hspec.
    have {Hspec} /Hspec := leq_trans Hr1 (size_convert_part outerw).
    rewrite widthE !cond_nat => Hspec.
    have {Hspec} := Hspec _ Hl.
    rewrite spec_sum_szouterw_widthE /=; last by rewrite addn1.
    move => ->.
    move: Hr1 Hl; rewrite size_diff_shape => Hr1 Hl.
    rewrite nth_rev; last by rewrite size_sol.
    rewrite /sol size_mkseq (nth_mkseq _ _ Hr1).
    rewrite (nth_map (Posz 0)); first last.
      rewrite size_take bad_if_leq // -lez_nat -widthE.
      have := Hncols_solw (leq_trans Hr1 (size_convert_part outerw)).
      rewrite /spec.width.
      suff -> : ncols solw = size (nth [::] solw (size outer - r.+1)) by [].
      case: solw Hnrows => mat [nrows | //=] [ncols | //=] /= _ _ /eqP <- {nrows}.
      move=> /allP Hall /eqP; rewrite eqz_nat => /eqP Hsz.
      have := leq_trans Hr1 (size_convert_part outerw).
      by rewrite -Hsz => /(mem_nth [::])/Hall/=/eqP ->.
    rewrite (nth_take _ Hl).
    by have:= Hsol_pos Hr1 Hl => /gez0_abs.
Qed.

Lemma count_mem_numeqE (n i : nat) :
  Posz (count_mem i (drop n (to_word sol))) = spec.numeq wordw i n (size wordw).
Proof.
  rewrite -to_wordE.
  elim: (to_word sol) n => [| w0 w /= IHw] n /=.
    by rewrite /spec.numeq spec.Numof_empty.
  case: n => [| n] /=.
    have:= IHw 0; rewrite PoszD drop0 => ->.
    case: eqP => /= H0.
    + rewrite [RHS]spec.Numof_left_add //; first last.
        by rewrite spec.fc_def /= H0.
      by rewrite -PoszD addn1 (spec_numeq_shift w0).
    + rewrite [RHS]spec.Numof_left_no_add //; first last.
        rewrite spec.fc_def /=.
        by apply/eqP; rewrite eqz_nat; apply/eqP.
      by rewrite add0r -PoszD addn1 (spec_numeq_shift w0).
  - by rewrite IHw (spec_numeq_shift w0).
Qed.

Lemma is_yam_solE : spec.is_yam wordw <-> is_yam (to_word sol).
Proof.
  rewrite /spec.is_yam /spec.is_yam_suffix subrr !cond_nat; split.
  - move=> [] [] _ _ [] Hpos Hyamw.
    apply/is_yam_ijP => d i j Hij.
    case: (leqP d (size (to_word sol))) => [| /ltnW Hd].
    + rewrite size_to_wordE => Hd.
      rewrite -lez_nat !count_mem_numeqE.
      rewrite -(subKn Hd) -subzn; last by apply leq_subr.
      apply Hyamw; first by apply leq_subr.
      by rewrite !lez_nat Hij.
    + by rewrite drop_oversize.
  - move=> /is_yam_ijP Hyam; repeat split => //.
    + move=> i; rewrite -to_wordE size_map => /= Hi.
      by rewrite (nth_map 0 _ _ Hi).
    + move=> i Hi; rewrite cond_nat => u v Huv.
      rewrite (subzn Hi) -!count_mem_numeqE lez_nat.
      exact: Hyam.
Qed.

Lemma eval_solE :
  spec.is_yam wordw ->
  (spec.is_of_eval evalw wordw <-> evalseq (to_word sol) = eval).
Proof.
  move=> Hyamw.
  rewrite /spec.is_of_eval /spec.is_of_eval_suffix subrr !cond_nat; split.
  - move=> [] Hsz Heval; apply/eqP/part_eqP.
      + apply is_part_eval_yam; by rewrite -is_yam_solE.
      + exact: inputSpec_from_Why3.(eval_part).
    move=> i; rewrite nth_evalseq. rewrite -[to_word _]drop0.
    apply/eqP; rewrite -eqz_nat; apply/eqP.
    rewrite count_mem_numeqE.
    case: (ltnP i (size evalw)) => Hi.
    + by rewrite (Heval _ Hi) (part_nth_getE _ part_evalw).
    + rewrite spec.numeq0.
        rewrite nth_default //; first exact: (leq_trans (size_convert_part _) Hi).
      rewrite cond_nat => j /Hsz [] _ Hj.
      exact: (ltr_le_trans Hj).
  - move=> Heq; split => i Hi.
    + rewrite -to_wordE /= (nth_map 0); last by rewrite size_to_wordE.
      split; first by [].
      move: Hi; rewrite -to_wordE size_map => Hi.
      rewrite ltz_nat; apply: (leq_trans _ (size_convert_part _)).
      rewrite -Heq {Heq}.
      elim: (to_word sol) i Hi => [// | w0 w IHw] /= i.
      rewrite size_incr_nth.
      case: i => [_ | i] /=; first by case: (ltnP w0 (size _)).
      rewrite ltnS => /IHw H.
      case: (ltnP w0 (size _)) => //= Hw0.
      rewrite ltnS; apply ltnW; exact: (leq_trans H).
    + rewrite -count_mem_numeqE drop0 -nth_evalseq Heq.
      by rewrite (part_nth_getE _ part_evalw).
Qed.

End ToWord.

Lemma spec_eq_sol a b :
  spec.valid_work outerw innerw a ->
  spec.valid_work outerw innerw b ->
  spec.eq_sol outerw innerw a b -> sol a = sol b.
Proof.
  rewrite /spec.eq_sol /spec.eq_rows /sol !cond_nat => Ha Hb Heq.
  apply eq_mkseq => r.
  case: (ltnP r (size outerw)) => Hr.
  - have {Heq} := Heq _ Hr; rewrite widthE cond_ltz_nat => Heq.
    congr map; apply (eq_from_nth (x0 := Posz 0)).
    + rewrite !size_take !bad_if_leq //; exact: size_nth_solw.
    + move=> c; rewrite size_take bad_if_leq; last exact: size_nth_solw.
      move=> Hc; rewrite !(nth_take _ Hc).
      have:= Heq _ Hc; by rewrite /matrix_get witness_int_why3Type.
  - rewrite nth_default; first last.
      rewrite size_diff_shape; exact: (leq_trans (size_convert_part _) Hr).
    by rewrite !take0.
Qed.

Section SolCorrect.

Variable solw : matrix int.
Notation sol := (sol solw).
Hypothesis Hsol : spec.is_solution outerw innerw evalw solw.

Lemma Hwork : spec.valid_work outerw innerw solw.
Proof. by move: Hsol => []. Qed.

Notation wordw := (spec.to_word outerw innerw solw).

Lemma wordw_pos (i : nat) : (0 <= get wordw i)%R.
Proof.
  move: Hsol => [] _ [] [] _ []; rewrite subrr cond_ltz_nat => Hpos _ _.
  case: (ltnP i (size wordw)) => [/Hpos [] //= | H] /=.
  by rewrite (nth_default _ H).
Qed.

Lemma sols_pos r i :
  r < size outer -> i < nth 0 width r -> (matrix_get solw (Posz r, Posz i) >= 0)%R.
Proof.
  move=> Hr Hi.
  apply: (spec.sols_pos includedw Hsol); split => //=.
  - rewrite ltz_nat; apply: (leq_trans Hr); exact: size_convert_part.
  - by rewrite widthE ltz_nat.
Qed.

Lemma size_drop_nth_sol r :
  size (drop (nth 0 inner r - nth 0 (behead inner) r) (nth [::] sol r.+1))
  = nth 0 outer r.+1 - nth 0 inner r.
Proof.
  case (ltnP r.+1 (size outer)) => Hi.
  - rewrite size_drop (size_nth_solE Hwork Hi).
    rewrite !nth_diff_shape.
    have -> : nth 0 (behead inner) r = nth 0 inner r.+1 by case inner.
    rewrite subnBA; last exact: inner_decr.
    rewrite subnK //; last exact: le_inner_outer.
  - rewrite [nth _ sol _]nth_default; last by rewrite size_sol.
    by rewrite (nth_default _ Hi) /= sub0n.
Qed.

Lemma skew_dominate_nth_sol r :
  skew_dominate (nth 0 inner r - nth 0 (behead inner) r)
                (nth [::] sol r.+1) (nth [::] sol r).
Proof.
  rewrite /skew_dominate; apply/dominateP; split.
    rewrite size_drop_nth_sol.
    case (ltnP r (size outer)) => Hi.
    + rewrite (size_nth_solE Hwork Hi) // !nth_diff_shape.
      apply leq_sub2r; last exact: outer_decr.
    + rewrite [nth _ sol _]nth_default; last by rewrite size_sol.
      by rewrite (nth_default _ (leq_trans Hi _)).
  move=> c; rewrite size_drop_nth_sol.
  have -> : nth 0 (behead inner) r = nth 0 inner r.+1 by case inner.
  rewrite ltnXnatE inhabitant_nat_ordType => Hc.
  move: Hsol => [] _ [] _ [] _ [] _ [] Hcol _.
  rewrite nth_drop.
  case (ltnP r.+1 (size outer)) => Hr.
  - have {Hcol} /Hcol : (Posz 1 <= r.+1)%R /\ (Posz r.+1 < size outerw)%R.
      split; first by [].
      rewrite ltz_nat; apply (leq_trans Hr).
      by apply size_convert_part.
    rewrite -/(spec.width outerw innerw r.+1) widthE cond_ltz_nat.
    rewrite /spec.increasing_column => Hcol.
    pose i := (c + (nth 0 inner r - nth 0 inner r.+1)).
    have Hi : i < nth 0 width r.+1.
      rewrite /i nth_diff_shape.
      have:= Hc; rewrite -(ltn_add2r (nth 0 inner r - nth 0 inner r.+1)).
      do 2 (rewrite addnBA; last exact: inner_decr).
      rewrite subnK //.
      apply ltnW; rewrite -subn_gt0.
      exact: (leq_ltn_trans _ Hc).
    have {Hcol} := Hcol _ Hi.
    rewrite !(part_nth_getE _ part_innerw) !subn1 [r.+1.-1]/=.
    have -> : (Posz r.+1 - 1)%R = r by rewrite -addn1 PoszD addrK.
    set Hyp := (X in (X -> _) -> _) => H.
    have {H Hyp} /H : Hyp.
      rewrite /Hyp /i {Hyp H}; split => //.
      rewrite subzn; last exact: inner_decr.
      rewrite lez_nat; exact: leq_addl.
    rewrite -(sol_contentsE Hwork sols_pos Hr Hi).
    set tmp := (X in matrix_get _ (_, X)).
    have {tmp} -> : tmp = c by rewrite /tmp /i PoszD (subzn (inner_decr r)) addrK.
    rewrite -(sol_contentsE Hwork sols_pos); first last.
      - rewrite nth_diff_shape; apply (leq_trans Hc).
        exact: leq_sub2r (outer_decr _).
      - exact: ltn_trans _ Hr.
    by rewrite addnC.
  - exfalso; move: Hc; by rewrite (nth_default _ Hr) sub0n.
Qed.

Lemma skew_tab_sol : is_skew_tableau inner sol.
Proof.
  apply/is_skew_tableauP; split.
  - rewrite size_sol.
    exact: (size_included inputSpec_from_Why3.(incl)).
  - move=> i Hi.
    rewrite (size_nth_solE Hwork); last by apply (leq_trans Hi); rewrite size_sol.
    rewrite nth_diff_shape subnKC.
      apply (nth_part_non0 inputSpec_from_Why3.(outer_part)).
      move: Hi; by rewrite size_sol.
    have := (includedP _ _ inputSpec_from_Why3.(incl)) => [] [] _; by apply.
  - move=> r; case: (ltnP r (size sol)) => Hr; last by rewrite nth_default.
    apply/(is_rowP 0) => u v /andP [] Huv Hv; rewrite leqXnatE.
    move: Hsol => [] _ [] _ []; rewrite cond_ltz_nat => Hrow _.
    have {Hrow} /Hrow : r < size outerw.
      apply (leq_trans Hr); rewrite size_sol; exact: size_convert_part.
    rewrite /spec.non_decreasing_row_suffix -/(spec.width outerw innerw r) widthE.
    rewrite cond_lez_ltz_nat => Hrow.
    have Huvw : u <= v /\ v < nth 0 width r.
      split => //; by rewrite -(shape_sol Hwork) (nth_map [::]).
    have := Hrow u v Huvw.
    move: Hr; rewrite size_sol => Hr.
    rewrite -!(sol_contentsE Hwork sols_pos Hr).
    + by [].
    + by move: Huvw => [].
    + apply (leq_ltn_trans Huv); by move: Huvw => [].
  - exact skew_dominate_nth_sol.
Qed.

Lemma is_solution_correct :
  outputSpec inner eval outer sol.
Proof.
  have Hyam : is_yam (to_word sol).
    rewrite -(is_yam_solE Hwork sols_pos).
    by move: Hsol => [] _ [] [].
  constructor.
  - exact: skew_tab_sol.
  - by rewrite (shape_sol Hwork).
  - exact: Hyam.
  - rewrite -(eval_solE Hwork sols_pos); by move: Hsol => [] _ [] [].
Qed.

End SolCorrect.

Section SolCompl.

Variable tab : seq (seq nat).
Hypothesis Hout : outputSpec inner eval outer tab.

Lemma size_tab : size tab = size outer.
Proof.
  move: Hout => [] _ Hshape _ _.
  by rewrite -(size_map size) -/(shape tab) Hshape size_diff_shape.
Qed.

Lemma size_nth_tab r : size (nth [::] tab r) = nth 0 width r.
Proof.
  move: Hout => [] _ <- _ _.
  case: (ltnP r (size tab)) => Hr.
  - by rewrite (nth_map [::]).
  - by rewrite (nth_default _ Hr) nth_default // size_map.
Qed.

Notation nrows := (size outerw).
Definition ncols := `|get outerw 0|.

Definition solwmat : seq (seq int) :=
  mkseq (fun i => map Posz (nth [::] tab i) ++
                      nseq (ncols - size (nth [::] tab i)) (Posz 0)) nrows.

Lemma solwmatE r i :
  r < size outerw -> i < nth 0 width r ->
  nth (Posz 0) (nth [::] solwmat r) i = nth 0 (nth [::] tab r) i.
Proof.
  move=> Hr Hi.
  rewrite (nth_mkseq _ _ Hr) nth_cat size_map size_nth_tab Hi.
  by rewrite (nth_map 0) // size_nth_tab.
Qed.

Lemma solwmat_pos r i :
  r < size outer -> i < nth 0 width r ->
  (0 <= nth (Posz 0) (nth [::] solwmat r) i)%R.
Proof. move=> Hr Hi; by rewrite (solwmatE (leq_trans Hr (size_convert_part _)) Hi). Qed.

Lemma width_ncolsE r : nth 0 width r <= ncols.
Proof.
  rewrite nth_diff_shape; apply (@leq_trans (nth 0 outer r)); first exact: leq_subr.
  rewrite /ncols (part_nth_getE _ part_outerw) /=.
  have/is_part_ijP := (inputSpec_from_Why3.(outer_part)) => [] [] _ Hpart.
  by have /Hpart /= : 0 <= r by [].
Qed.

Lemma spec_width_ncolsE (r : nat) : (spec.width outerw innerw r <= ncols)%R.
Proof. rewrite widthE; exact: width_ncolsE. Qed.

Definition matw : matrix int.
Proof.
  apply (@Matrix int solwmat nrows ncols) => //; first by rewrite size_mkseq.
  apply/allP => row /mapP [] r.
  rewrite mem_iota add0n => /andP [] _ Hr -> {row}.
  rewrite /= size_cat size_map size_nseq subnKC //.
  case: (ltnP r (size tab)) => Hrs; last by rewrite nth_default.
  move: Hout => [] _ Hshape _ _.
  have:= erefl (nth 0 width r); rewrite -{1}Hshape (nth_map [::] _ _ Hrs) => ->.
  exact: width_ncolsE.
Defined.

Lemma matE : solwmat = matw. Proof. by []. Qed.

Lemma mat_work : spec.valid_work outerw innerw matw.
Proof.
  split => //=; rewrite cond_ltz_nat => i Hi.
  rewrite -/(spec.width _ _ _).
  exact: spec_width_ncolsE.
Qed.

Lemma sol_matE : sol matw = tab.
Proof.
  rewrite /sol -matE.
  apply (@eq_from_nth _ [::]); rewrite size_mkseq; first by rewrite size_tab.
  move => i Hi.
  rewrite /solwmat (nth_mkseq _ _ Hi) nth_mkseq; first last.
    apply (leq_trans Hi); exact: size_convert_part.
  rewrite take_cat size_map size_nth_tab ltnn subnn take0 cats0 -map_comp.
  by apply map_id_in.
Qed.

Notation wordw := (spec.to_word outerw innerw matw).


Lemma is_yam_wordw : spec.is_yam wordw.
Proof.
  rewrite (is_yam_solE mat_work solwmat_pos).
  rewrite sol_matE.
  exact: Hout.(yam_to_word).
Qed.

Lemma is_ev_wordw : spec.is_of_eval evalw wordw.
Proof.
  rewrite (eval_solE mat_work solwmat_pos is_yam_wordw).
  rewrite sol_matE.
  exact: Hout.(eval_eq).
Qed.

Lemma is_tab_matw : spec.is_tableau_reading outerw innerw matw.
Proof.
  rewrite /spec.is_tableau_reading /spec.is_tableau_reading_suffix !cond_nat .
  repeat split; try by rewrite ltrr.
  - move=> r Hr; rewrite /spec.non_decreasing_row_suffix.
    rewrite -/(spec.width outerw innerw _) widthE cond_nat => i j [] Hij Hj /=.
    have Hi := leq_ltn_trans Hij Hj.
    rewrite (solwmatE Hr Hj) (solwmatE Hr Hi).
    rewrite lez_nat -leqXnatE.
    move: Hout => [] /is_skew_tableauP [] _ _ Hrow _ _ _ _.
    apply: (is_rowP 0 _ (Hrow r)).
    by rewrite Hij /= size_nth_tab.
  - case=> [[[] //= | r ] | r [] //=] [] _.
    rewrite ltz_nat => Hr.
    rewrite -/(spec.width outerw innerw _) widthE cond_nat => i Hi.
    rewrite /spec.increasing_column => [] [] _.
    have -> : (Posz r.+1 - 1)%R = r by apply/eqP; rewrite eqz_nat /= subn1.
    rewrite !(part_nth_getE _ part_innerw).
    have/is_partP := (inputSpec_from_Why3.(inner_part)) => [] [] _ Hpart.
    have {Hpart} Hinn := Hpart r.
    rewrite (subzn Hinn) lez_nat => Hinni.
    rewrite (subzn Hinni).
    rewrite /matrix_get (solwmatE Hr Hi) (solwmatE (ltnW Hr)); first last.
      rewrite -ltz_nat -(subzn Hinni) -(subzn Hinn) nth_diff_shape.
      have /includedP := inputSpec_from_Why3.(incl) => [] [] _ Hincl.
      rewrite -(subzn (Hincl r)).
      rewrite ltr_subr_addr opprB addrA addrNK.
      move: Hi; rewrite !nth_diff_shape ltn_subRL addnC -ltz_nat PoszD => Hi.
      apply (ltr_le_trans Hi); rewrite lez_nat.
      by have/is_partP := (inputSpec_from_Why3.(outer_part)) => [] [] _ Hpart.
    rewrite ltz_nat.
    move: Hout => [] /is_skew_tableauP [] _ _ _ Hdom Hshape _ _.
    have {Hdom} := Hdom r => /dominateP.
    rewrite inhabitant_nat_ordType size_drop !size_nth_tab => [] [] _.
    have -> : nth 0 (behead inner) r = nth 0 inner r.+1 by case inner.
    move=> Hdom.
    have := Hdom (i - (nth 0 inner r - nth 0 inner r.+1)).
    set Hyp := (X in (is_true X -> _) -> _) => {Hdom} Hdom.
    have {Hyp Hdom} /Hdom : Hyp.
      by rewrite /Hyp {Hyp Hdom} ltn_subRL (subnKC Hinni).
    by rewrite ltnXnatE nth_drop (subnKC Hinni).
Qed.

Lemma is_solution_compl : spec.is_solution outerw innerw evalw matw.
Proof.
  split; last split.
  - exact: mat_work.
  - split.
    + exact: is_yam_wordw.
    + exact: is_ev_wordw.
  - exact: is_tab_matw.
Qed.

End SolCompl.

(*
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
*)

Section Correction.

Variable s : spec.solutions.
Hypothesis Hcorr : spec.good_solutions outerw innerw evalw s.

Notation d1 := (sumn inner).
Lemma Hinn_dep : is_part_of_n d1 inner.
Proof.
  have:= inputSpec_from_Why3 => [] [] Hpartinner _ _ _ _.
  by rewrite /= /d1 eq_refl.
Qed.
Notation P1 := (IntPartN Hinn_dep).

Notation d2 := (sumn eval).
Lemma Heval_dep : is_part_of_n d2 eval.
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

Definition sols := [seq sol (spec.s2m (spec.sols s (Posz i))) | i <- iota 0 N ].

Lemma all_yamev_sols : all (is_yam_of_eval P2) (map (@to_word _) sols).
Proof.
  move: Hcorr => []; rewrite spec_nextE => _ [] Hsort [].
  rewrite cond_ltz_nat => Hsol Hcompl.
  rewrite /sols; apply/allP => x /mapP [] y /mapP [] i.
  rewrite mem_iota add0n => /andP [] _ /Hsol Hi -> -> {x y} /=.
  rewrite /is_yam_of_eval.
  by have := is_solution_correct Hi => [] [] _ _ -> -> /=.
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

