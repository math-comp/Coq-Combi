Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import Coq.Arith.Wf_nat.
Require Import brace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Notation "#Open" := (count_mem Open).
Notation "#Close" := (count_mem Close).

Module Type M_PARAM.
  Parameter m : nat.
End M_PARAM.

Module MDyck (Param : M_PARAM).

  Import Param.

  Implicit Type h n : nat.
  Implicit Type w : seq Brace.
  Implicit Type l : seq (seq Brace).

  Definition brace_bal h w :=  m * (#Open w) + h == #Close w.
  Definition brace_pos h w :=  m * (#Open w) + h >= #Close w.

  Definition is_dyck_height h w := (brace_bal h w) /\ forall n, brace_pos h (take n w).
  Definition is_dyck w := is_dyck_height 0 w.

  Definition prefixes w := [seq take n w | n <- iota 0 ((size w).+1)].
  Definition dyck_prefix_height h w := brace_bal h w && all (brace_pos h) (prefixes w).
  Definition dyck_prefix := (dyck_prefix_height 0).

  Fixpoint dyck_height_rec h w : bool :=
  match w with
    (* I'd rather not use h == 0 here because of extraction *)
    | [::] => if h is 0 then true else false
    | Open::tlb => dyck_height_rec (m + h) tlb
    | Close::tlb => if h is h'.+1 then dyck_height_rec h' tlb else false
  end.

  Definition dyck_rec := (dyck_height_rec 0).

  Notation "dyck_rec( h )" := (dyck_height_rec h) (at level 2).

  (* The following allows to use w \in dyck_rec which prevent simplifitation of *)
  (* expression such as `Open :: w \in dyck_rec(h)` to `w \in dyck_rec(m + 3)`. *)
  (* One switch back to simplification by rewriting inE (see lemma belows).     *)
  Canonical dyck_height_rec_app_pred h := ApplicativePred (dyck_height_rec h).
  Canonical dyck_app_pred h := ApplicativePred dyck_rec.

Section Trivia.

  Variable w : seq Brace.
  Variable h : nat.

  Lemma open_dyck_height : (Open :: w) \in dyck_rec(h) <-> w \in dyck_rec(m + h).
  Proof. by rewrite inE. Qed.

  Lemma open_dyck : (Open :: w) \in dyck_rec <-> w \in dyck_rec(m).
  Proof. by rewrite /dyck_rec inE /= addn0. Qed.

  Lemma close_dyck_height : (Close :: w) \in dyck_rec(h.+1) <-> w \in dyck_rec(h).
  Proof. by rewrite inE. Qed.

End Trivia.


(* We prove the equivalence beteew the definition is_dyck and *)
(* the two predicate dyck_prefix and dyck_rec.                *)
Section DefRec.

  Lemma positive_equiv h w:
    (forall n, brace_pos h (take n w)) <-> all (brace_pos h) (prefixes w).
  Proof.
    rewrite all_map /preim; split => [H | b n]; first by apply /allP => HH _ //=.
    case: (ltnP n (size w).+1) => Hn.
    - have:= allP b n => Hb {b}; apply Hb; by rewrite mem_iota.
    - rewrite take_oversize; last by apply ltnW.
      have H : size w \in iota 0 (size w).+1 by rewrite mem_iota => //=.
      have:= allP b (size w) H => /=; by rewrite take_size.
  Qed.

  Lemma positiveP h w:
    reflect (forall n, brace_pos h (take n w)) (all (brace_pos h) (prefixes w)).
  Proof. apply: (iffP idP); apply positive_equiv. Qed.

  Lemma dyck_height_rec_unique h1 h2 w :
    w \in dyck_rec(h1) -> w \in dyck_rec(h2) -> h1 == h2.
  Proof.
    elim: w h1 h2 => [|[] w' IHw] h1 h2 /=.
     case h1; case h2; by [].
     rewrite -(eqn_add2l m); by apply IHw.
     case: h1 => h1; case: h2 => h2 //=; rewrite eqSS; by apply IHw.
  Qed.

  Lemma cat_dyck_height w1 w2 h1 h2 :
    w1 \in dyck_rec(h1) -> w2 \in dyck_rec(h2) -> (w1 ++ w2) \in dyck_rec(h1 + h2).
  Proof.
    elim: w1 w2 h1 h2 => [|[] w1 IHw1] w2 h1 h2 //=; first by case h1.
     rewrite !open_dyck_height addnA; by apply IHw1.
     case: h1 => h1 //=; by apply IHw1.
  Qed.

  Lemma dyck_height_eq : dyck_prefix_height =2 dyck_height_rec.
  Proof.
    rewrite /dyck_prefix_height /eqrel /prefixes /brace_pos /brace_bal => h w.
    elim: w h; first by case => //=; rewrite muln0.
    case => w IHw h.
    - rewrite [dyck_rec(_) _]/= -IHw {IHw} [size _]/=; move: (size w).+1 => len /=.
      rewrite add0n mulnDr muln1 [m + _] addnC -addnA; bool_congr.
      rewrite !all_map -[1]addn0 iota_addl all_map; apply eq_all => n /=.
      by rewrite add0n mulnDr muln1 [m + _] addnC -addnA.
    - case: h => [/= | h]; first by rewrite all_map /= take0 /= addn0 muln0 /= andbF.
      rewrite [dyck_rec(_) _]/= -IHw {IHw} [size _]/=; move: (size w).+1 => len /=.
      rewrite add0n add1n addnS eqSS; bool_congr.
      rewrite !all_map -[1]addn0 iota_addl all_map; apply eq_all => n /=.
      by rewrite add0n add1n addnS.
  Qed.

  Theorem dyck_eq : dyck_prefix =1 dyck_rec.
  Proof.
    rewrite /dyck_prefix /dyck_rec /eqfun.
    by apply dyck_height_eq.
  Qed.

  Lemma dyck_prefix_heightP h w :
    reflect (is_dyck_height h w) (dyck_prefix_height h w).
  Proof.
    apply: (iffP idP); rewrite /is_dyck_height /dyck_prefix_height positive_equiv.
    move=> H; by split; apply (andP H).
    move=> [] H1 H2; by rewrite H1.
  Qed.

  Theorem dyck_prefixP w : reflect (is_dyck w) (w \in dyck_prefix).
  Proof.
    by rewrite /is_dyck /dyck_prefix; apply dyck_prefix_heightP.
  Qed.

  Theorem dyckP w : reflect (is_dyck w) (w \in dyck_rec).
  Proof.
    by rewrite -topredE /= -dyck_eq; apply dyck_prefixP.
  Qed.

End DefRec.

Section Factor.

  Fixpoint cut_to_height h w : seq Brace * seq Brace :=
  match w with
    | nil => (nil, nil)
    | Open :: tlw => let (w1, w2) := cut_to_height (m + h) tlw in
                     (Open :: w1, w2)
    | Close::tlw =>
      if h is h'.+1
      then let (w1, w2) := cut_to_height h' tlw in (Close :: w1, w2)
      else (nil, tlw)
  end.

  Remark cut_equiv_dyck_height w h :
    w \in dyck_rec(h) <->
    ( (cut_to_height h w).1 == w /\ (cut_to_height h (w ++ [:: Close ])).1 == w ).
  Proof.
    elim: w h => [|[] w IHw] /=.
    - case=> [| h]; split; by move=> // [].
    - move=> h; move: IHw => /(_ (m + h)).
      elim (cut_to_height (m + h) w) => w1 w2 ->.
      by elim (cut_to_height (m + h) (w ++ [:: Close])).
    - case=> [| h] //; first by split; move=> // [].
      move: IHw => /(_ h).
      elim (cut_to_height h w) => w1 w2 ->.
      by elim (cut_to_height h (w ++ [:: Close])).
  Qed.

  Lemma cut_to_height_factor w hw h :
    w \in dyck_rec(hw) -> hw > h ->
      let (w1, w2) := cut_to_height h w in w == w1 ++ Close :: w2.
  Proof.
    elim: w hw h => [|[] w IHw hw h] //= ; first by case.
    - move: IHw => /(_ (m + hw) (m + h)).
      elim (cut_to_height (m + h) w) => w1 w2 IHw.
      by rewrite (ltn_add2l m) in IHw.
    - case: hw => hw; case: h => h //=.
      move: IHw => /(_ hw h); by elim (cut_to_height h w).
  Qed.

  Lemma cut_dyck_height w hw h :
    w \in dyck_rec(hw) -> hw > h ->
      let (w1, w2) := cut_to_height h w in w1 \in dyck_rec(h) /\ w2 \in dyck_rec(hw - S h).
  Proof.
    elim: w hw h => [|[] w IHw [] hw h Hd] //=; first by case.
    - move: IHw => /(_ (m + hw.+1) (m + h)).
      elim (cut_to_height (m + h) w) => w1 w2 IHw Hlt /=.
      rewrite -addnS (subnDl m) in IHw; apply IHw; first by apply Hd.
      by rewrite leq_add2l.
    - case: h => h; first by rewrite subn1 //=.
      move: IHw => /(_ hw h Hd).
      elim (cut_to_height h w) => w1 w2 IHw /=; by apply IHw.
  Qed.

  Lemma dyck_factor_eq_cut w hw h w1 w2 :
    w \in dyck_rec(hw) -> hw > h ->
    w1 \in dyck_rec(h) -> w == w1 ++ Close :: w2 ->
    (w1, w2) == cut_to_height h w.
  Proof.
    elim: w hw h w1 w2 => [|x w IHw] hw h w1 w2; first by case w1.
    case: x => Hd Hp; case: w1 => [|[] w1 Hdw1 /= Heq] //=.
    - move: IHw => /(_ (m + hw) (m + h) w1 w2 Hd _ Hdw1) {Hd Hdw1}.
      elim (cut_to_height (m + h) w) => wa1 wa2.
      rewrite (ltn_add2l m) => IHw; by apply (IHw Hp).

    - move: h Hp => [] Hp Hdw /= Happ //=; by rewrite eq_sym.

    - move: hw h Hp Hd Hdw1 => [] //= hw [] //= hw1 Hlt Hdw Hdw1.
      move: IHw => /(_ hw hw1 w1 w2 Hdw _ Hdw1) {Hdw Hdw1}.
      elim (cut_to_height hw1 w) => wa1 wa2; by apply.
  Qed.

  (* TODO: move to a Dyck2 module. *)
  Lemma cut_unique w1 w2 : w1 \in dyck_rec -> w2 \in dyck_rec ->
         (w1, w2) == cut_to_height 0 (behead (Open :: w1 ++ (Close :: w2))).
  Proof.
    move => Hd1; rewrite -close_dyck_height; move => Hd2.
    have:= (cat_dyck_height Hd1 Hd2); rewrite add0n => Hwd.
    by apply (dyck_factor_eq_cut (hw:=1)).
  Qed.

  Definition join (T : Set) (b : T) := foldr (fun s1 s2 => s1 ++ b :: s2).

  Lemma join_dyck_height l w hw :
    all (mem dyck_rec) l -> w \in dyck_rec(hw) -> join Close w l \in dyck_rec((size l) + hw).
  Proof.
    elim: l w hw => //= w l IHl w0 hw0 //= /andP [] Hdw Hld Hdw0.
    rewrite -(add0n (_ + hw0)); apply cat_dyck_height; first by [].
    by apply IHl.
  Qed.

  Fixpoint mult_cut n w :=
    if n is n'.+1
    then let (w1, w2) := cut_to_height 0 w in
         let (l, wr) := mult_cut n' w2 in (w1 :: l, wr)
    else (nil, w).

  CoInductive mult_cut_spec n w l wr : Type :=
    MMultCutSpec of
        size l == n & all (mem dyck_rec) l & wr \in dyck_rec & w == (join Close wr l)
        : mult_cut_spec n w l wr.

  Lemma mult_cutP n w :
    w \in dyck_rec(n) -> let (l, wr) := (mult_cut n w) in mult_cut_spec n w l wr.
  Proof.
    elim: n w => [| n IHn w H] /=; first by rewrite -/dyck_rec.
    have Hpos := ltn0Sn n.
    move: (cut_dyck_height H Hpos) (cut_to_height_factor H Hpos) => {H Hpos}.
    elim (cut_to_height 0 w) => w1 w2 [] Hdw1 Hdw2 Hcat.
    rewrite subn1 succnK in Hdw2; rewrite -/dyck_rec in Hdw1.
    move/IHn: Hdw2. move: (mult_cut n w2) => [l wr] [] => Hlen Hld Hwr Hjoinl.
    constructor => //=; first by rewrite Hld Hdw1.
    by rewrite (eqP Hcat) (eqP Hjoinl).
  Qed.

  Lemma mult_cut_spec_unique n w l wr:
    mult_cut_spec n w l wr -> (l, wr) == mult_cut n w.
  Proof.
    case; elim: n w l wr => [| n IHn ] w l wr Hlen //.
    by have -> := size0nil (eqP Hlen) => _ _ /= /eqP ->.
    case: l Hlen => //= w0 l Hlen /andP [] Hw0d Halld Hwrd Hjoinl.
    rewrite eqSS in Hlen; have:= join_dyck_height Halld Hwrd.
    rewrite addn0 (eqP Hlen) -close_dyck_height => Wdn.
    have{Wdn} Wdn := cat_dyck_height Hw0d Wdn.
    rewrite -(eqP Hjoinl) in Wdn.
    rewrite -(eqP (dyck_factor_eq_cut Wdn (ltn0Sn _) Hw0d Hjoinl)) => {Wdn Hw0d Hjoinl}.
    by rewrite -(eqP (IHn (join _ _ _) l wr Hlen Halld Hwrd (eq_refl _))).
  Qed.

  Definition factor w := mult_cut m (behead w).

  CoInductive factorization w : Set :=
    Factorization { l; wr;
                    _ : (size l == m);
                    _ : (all (mem dyck_rec) l);
                    _ : wr \in dyck_rec;
                    _ : w == Open :: (join Close wr l)
                  }.

  Lemma factorizeP w : w \in dyck_rec -> (w != [::]) -> factorization w.
  Proof.
    rewrite /factor /dyck_rec; case: w => [| [] w] //=.
    rewrite inE /dyck_height_rec addn0 -/dyck_height_rec.
    move/mult_cutP; case: (mult_cut m w) => l wr [] Hszl Halld Hwrd Heq _.
    by apply (Factorization (l:=l) (wr:=wr)).
  Qed.

  Lemma factored_is_dyck_non_nil w : factorization w -> w \in dyck_rec /\ (w != [::]).
  Proof.
    case => l wr Hszl Halld Hwrd /eqP {w} -> /=; split; last by [].
    by rewrite open_dyck_height -(eqP Hszl); apply join_dyck_height.
  Qed.

  Lemma factored_is_dyck w : factorization w -> w \in dyck_rec.
  Proof.
    case => l wr Hszl Halld Hwrd /eqP {w} -> /=.
    by rewrite open_dyck_height -(eqP Hszl); apply join_dyck_height.
  Qed.

  Theorem factor_eq w (fct : factorization w) : (l fct, wr fct) == factor w.
  Proof.
    case fct => {fct} l wr Hszl Halld Hwrd Heq /=.
    rewrite /factor.
    apply mult_cut_spec_unique.
    by rewrite (eqP Heq) in Hwrd *.
  Qed.

End Factor.

Section DyckSet.

  Record Dyck := DyckWord {dyckword :> seq Brace; is_dyckword :> dyck_rec dyckword}.

  Canonical Dyck_subType := Eval hnf in [subType for dyckword].
  Definition Dyck_eqMixin := Eval hnf in [eqMixin of Dyck by <:].
  Canonical Dyck_eqType := Eval hnf in EqType Dyck Dyck_eqMixin.
  Definition Dyck_choiceMixin := [choiceMixin of Dyck by <:].
  Canonical Dyck_choiceType :=
    Eval hnf in ChoiceType Dyck Dyck_choiceMixin.

  Lemma dyck_inj : injective dyckword. Proof. exact: val_inj. Qed.

  Implicit Type d : Dyck.

  Definition emptyDyck := (@DyckWord [::] is_true_true).

  Lemma nil_nil : forall d, d != emptyDyck -> (dyckword d) != [::]. Proof. by []. Qed.

  Lemma is_dyck_Dyck d : (dyckword d) \in dyck_rec.
  Proof. by case d => [w H] /=. Qed.

  Definition cat_Dyck d1 d2 := DyckWord (cat_dyck_height d1 d2).

  Definition seq_Dyck (l : seq (seq Brace)) (H : all (mem dyck_rec) l) : seq Dyck.
    elim: l H => [_| w0 l IHl /andP [] H Hl]; first by apply [::].
    move: (IHl Hl) => Hdl; by apply ((DyckWord H) :: Hdl).
  Defined.

  Lemma seq_Dyck_val (l : seq (seq Brace)) (H : all (mem dyck_rec) l) :
    [seq dyckword i | i <- seq_Dyck H] == l.
  Proof.
    elim: l H => [|w0 l IHl] H /=; first by rewrite /seq_Dyck.
    set MatchH := elimTF andP H; case: MatchH => Hw0 Hl /=.
    by rewrite (eqP (IHl Hl)).
  Qed.

  Lemma seq_Dyck_size (lD : seq Dyck) : size lD == size (map dyckword lD).
  Proof. by elim: lD => [//=|D0 lD] /= /eqP <-. Qed.

  Lemma seq_Dyck_all_dyck (lD : seq Dyck) : all (mem dyck_rec) (map dyckword lD).
  Proof.
    elim: lD => [//=| D0 ld IHlD].
    rewrite all_map; simpl; rewrite -all_map IHlD /= andbT; by apply is_dyck_Dyck.
  Qed.

  Notation m_seq := {lD : seq Dyck | size lD == m}.

  Definition joinDyck (lD : m_seq) (Dr : Dyck) :=
    Open :: join Close Dr [seq dyckword i | i <- val lD].

  CoInductive Dyck_factorization D : Set :=
    DyckFactorization { lD :> m_seq;  Dr :> Dyck;  _ : dyckword D == joinDyck lD Dr }.

  Definition eq_DyckFact D (fct1 fct2 : Dyck_factorization D) :=
    (lD fct1 == lD fct2) && (Dr fct1 == Dr fct2).

  Lemma eq_DyckFactP D : Equality.axiom (eq_DyckFact (D := D)).
  Proof.
    move=> f1 f2; apply: (iffP idP) => [|<-].
    case f1 => lD1 Dr1 H1; case f2 => lD2 Dr2 H2.
    rewrite /eq_DyckFact => /= /andP [] /eqP Heql /eqP Heqwr.
    move: Heql Heqwr H1 H2 => -> -> H1 H2 {lD1 Dr1}.
    suff: (H1 = H2) by move => -> .
    by apply eq_irrelevance.
    rewrite /eq_DyckFact. set HlD := (_ == _).
    have: (HlD = true) by apply eq_refl.
    move => -> /=; by apply eq_refl.
  Qed.

  Canonical DyckFact_eqMixin D := EqMixin (eq_DyckFactP (D := D)).
  Canonical DyckFact_eqType D :=
    Eval hnf in EqType (Dyck_factorization D) (DyckFact_eqMixin D).

  Lemma factor_to_Dyck w (fct : factorization w) :
    Dyck_factorization (DyckWord (factored_is_dyck fct)).
  Proof.
    case fct => /= l wr Hszl Halld Hwrd Heq.
    have Hwd := (factored_is_dyck fct).
    have:= (seq_Dyck_size (seq_Dyck Halld)).
    set lD := seq_Dyck Halld.
    rewrite (eqP (seq_Dyck_val Halld)) (eqP Hszl) => HszD.
    have: val ((exist _ lD HszD) : m_seq) = lD by [] => HlD.
    set lDm := (exist _ _ _) in HlD.
    exists lDm (DyckWord Hwrd) => //=.
    by rewrite /joinDyck /lD (eqP (seq_Dyck_val Halld)).
  Qed.

  Theorem factor_Dyck D (H : D != emptyDyck) : Dyck_factorization D.
  Proof.
    case: D H => [w Hw] H /=.
    have fct := (factorizeP Hw H).
    have:= factor_to_Dyck fct.
    have: ((factored_is_dyck fct) = Hw) by apply bool_irrelevance.
    by move=> ->.
  Qed.

  Lemma factor_Dyck_non_nil D (Fct : Dyck_factorization D) : D != emptyDyck.
  Proof.
    case Fct => lD Dr {Fct}.
    case D => /= w Hdw Heq.
    suff: (w != [::]) by [].
    by rewrite (eqP Heq).
  Qed.

  Lemma join_Dyck_eq_factor (lD : m_seq) (Dr : Dyck) :
    ([seq dyckword i | i <- sval lD], dyckword Dr) == factor (joinDyck lD Dr).
  Proof.
    case: lD => lD Hsz.
    move Heqw : (joinDyck _ _) => w.
    case: Dr Heqw => wr Hdwr /eqP /= Heqw.
    rewrite eq_sym in Heqw.
    have:= (seq_Dyck_size lD).
    have:= (seq_Dyck_all_dyck lD).
    rewrite (eqP Hsz) eq_sym => Halld Hszl.
    move Hfct : (Factorization (w := w) Hszl Halld Hdwr Heqw) => fct.
    have:= (factor_eq fct).
    by rewrite -Hfct /= => {Hfct fct Hsz Halld Heqw}.
  Qed.

  Lemma join_Dyck_eq (lD1 lD2 : m_seq) (Dr1 Dr2 : Dyck) :
    joinDyck lD1 Dr1 == joinDyck lD2 Dr2 -> lD1 == lD2 /\ Dr1 == Dr2.
  Proof.
    move=> Heq.
    have:= join_Dyck_eq_factor lD1 Dr1.
    have:= join_Dyck_eq_factor lD2 Dr2.
    move: Heq => /eqP -> /eqP <- /eqP [] /eqP Hl /eqP Hr; split; last by [].
    case: {Hr} lD1 Hl => lD1 Hsz1; case: lD2 => lD2 Hsz2 /= /eqP H.
    have:= (inj_map dyck_inj).
    rewrite /injective => Hinj.
    have:= (Hinj _ _ H) => {H Hinj} Hinj.
    move: Hinj Hsz1 -> => Hsz1.
    have: Hsz1 = Hsz2 by apply bool_irrelevance.
    by move ->.
  Qed.


  (* For some reason, I'm not able to use eq_DyckFactP. I'm reproving it *)
  Theorem factor_Dyck_eq D (fct1 fct2 : Dyck_factorization D) : fct1 == fct2.
  Proof.
    case: fct1 => l1 wr1 H1; case: fct2 => l2 wr2 H2.
    have:= H2; rewrite (eqP H1); move/join_Dyck_eq => [] /eqP Heql /eqP Heqwr /=.
    move: Heql Heqwr H1 H2 => -> -> H1 H2 {l1 wr1}.
    suff: (H1 = H2) by move => -> .
    move: H1 H2.
    set b2 := (dyckword D == joinDyck l2 wr2).
    move=> H1 H2.
    apply eq_irrelevance.
  Qed.

End DyckSet.


Section DyckSetInd.

  Implicit Type D : Dyck.
  Implicit Type lD : {lD : seq Dyck | size lD == m}.

  Lemma in_size_lt_joinDyck lD D Dr : D \in sval lD -> size D < size (joinDyck lD Dr).
  Proof.
    rewrite /joinDyck; case: lD => lD /= _.
    elim: lD => //= D0 lD IHlD; rewrite size_cat in_cons.
    case/orP => [{IHlD} /eqP <- |].
    - by rewrite ltnS; apply leq_addr.
    - move/IHlD => {IHlD} H; apply (ltn_trans H) => {H} /=.
      by rewrite addnS ?ltnS; apply leq_addl.
  Qed.

  Lemma init_size_lt_joinDyck lD (Dr : Dyck) : size Dr < size (joinDyck lD Dr).
  Proof.
    rewrite /joinDyck /join /=; case: lD => lD /= _.
    elim: lD => //= D0 lD IHlD.
    apply (ltn_trans IHlD) => {IHlD}.
    rewrite size_cat /= addnS ?ltnS; apply leq_addl.
  Qed.

  Variable P : Dyck -> Type.
  Hypothesis (Pnil : P emptyDyck)
             (Pcons : forall D (fct : Dyck_factorization D),
                                (forall ww, ww \in val (lD fct) -> P ww) -> P (Dr fct) ->
                                P D).

  Definition Dyck_lt_size D' D := size D' < size D.

  Lemma Dyck_ind_rec D : (forall D', size D' < size D -> P D') -> P D.
  Proof.
    case: (altP (D =P emptyDyck)); first by move=> -> _; exact Pnil.
    move=> Hnnil HltP; have fct := (factor_Dyck Hnnil).
    apply (Pcons (fct := fct)); case fct => /= l Dr Hcat.
    - move=> DD HDDinl; apply HltP.
      by rewrite (eqP Hcat); apply in_size_lt_joinDyck.
    - apply HltP.
      by rewrite (eqP Hcat); apply init_size_lt_joinDyck.
  Qed.

  Lemma RwfDyck : well_founded Dyck_lt_size.
  Proof.
    apply (well_founded_lt_compat Dyck size).
    rewrite /Dyck_lt_size => x y. by apply /ltP.
  Qed.

  Definition Dyck_gram_ind : forall D, P D := Fix RwfDyck (fun D =>  P D) Dyck_ind_rec.

End DyckSetInd.

End MDyck.



Module m0. Definition m := 0. End m0.
Module MDyck0 := MDyck m0.

Module m1. Definition m := 1. End m1.
Module MDyck1 := MDyck m1.

Section Tests0.

Import MDyck0.

Lemma dyck_zero_unique :
  forall d : Dyck, dyckword d == nseq (size d) Open.
Proof.
  elim/Dyck_gram_ind => //= D [[]] //= lD /=.
  by rewrite /joinDyck /= => /nilP -> Dr /eqP -> _ /= /eqP {1}->.
Qed.

End Tests0.

(*

 Eval compute in ((nseq 13 Open) \in dyck_rec 0).

Let hat := [:: Open; Close].
Let d := Open :: hat ++ Close :: hat.
Eval compute in dyck 1 hat.
Eval compute in dyck 1 d.

Eval compute in tval (tuple_factor 1 d).
Eval compute in (factor 1 d).
*)
