Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import subseq partition.

Set Implicit Arguments.
Unset Strict Implicit.



Section Rows.

  Implicit Type l : nat.
  Implicit Type r : seq nat.

  Fixpoint is_row r : bool :=
    match r with
      | [::] => true
      | l :: r => (l <= head l r) && is_row r
    end.

  Lemma is_row1P r :
    reflect
      (forall (i : nat), i.+1 < (size r) -> nth 0 r i <= nth 0 r i.+1)
      (is_row r).
  Proof.
    apply/(iffP idP).
    - elim: r => [_ i H //=| l0 [/= _ _ [|i] //=|l1 r /= IHr]] /andP [] Hleq Hrow.
      have {IHr Hrow} IHr := IHr Hrow.
      case => [_ //=| i /= H]; by apply IHr.
    - elim: r => [_ //=|] l0 [/=| l1 t] IHr Ht /=; first by rewrite leqnn.
      apply/andP; split; first by apply (Ht 0).
      apply IHr => i; by apply (Ht i.+1).
  Qed.

  Lemma non_decr_equiv r :
    (forall (i j : nat), i <= j -> j < (size r) -> nth 0 r i <= nth 0 r j)
    <->
    (forall (i : nat), i.+1 < (size r) -> nth 0 r i <= nth 0 r i.+1).
  Proof.
    split => H; first by move=> i; apply (H i i.+1).
    move=> i j; move Hdiff : (j - i) => diff.
    elim: diff i j Hdiff => [i j /eqP Hdiff Hleq _ | diff IHdiff i j Hdiff Hleq Hsize].
    - have HH : i <= j <= i by apply/andP.
      by rewrite (anti_leq HH).
    - have Hiltj : i < j by rewrite -subn_gt0 Hdiff.
      apply (leq_trans (n := nth 0 r i.+1)).
      apply H; by apply (leq_ltn_trans (n := j)).
      apply IHdiff => //=; first by rewrite subnS Hdiff.
  Qed.

  Lemma is_rowP r :
    reflect
      (forall (i j : nat), i <= j -> j < (size r) -> nth 0 r i <= nth 0 r j)
      (is_row r).
  Proof. apply/(iffP idP); by rewrite non_decr_equiv => /is_row1P. Qed.

  Lemma is_row_consK l r : is_row (cons l r) -> is_row r.
  Proof. by move=> /= /andP [] _. Qed.

  Lemma is_row_rconsK l r : is_row (rcons r l) -> is_row r.
  Proof.
    elim:  r => [//= | l0 [_ //=|l1 r] IHr]; first by rewrite leqnn.
    by move=> /= /andP [] ->.
  Qed.

  Lemma is_row_last l r : is_row (rcons r l) -> last 0 r <= l.
  Proof.
    elim: r => [//=|t0 r IHr] /= /andP [] Ht0.
    move/IHr {IHr}; by case: r Ht0 => [//=| l0 r] /=.
  Qed.

  Lemma head_leq_last_row l r : is_row (l :: r) -> l <= last l r.
  Proof.
    elim: r l => [//=| t0 r IHr] l /= /andP [] Hl.
    move/IHr {IHr}; by apply (leq_trans Hl).
  Qed.

  Lemma is_row_rcons l r : is_row r -> last 0 r <= l -> is_row (rcons r l).
  Proof.
    move/is_row1P => Hrow Hl; apply/is_row1P => i; rewrite size_rcons !nth_rcons => HH.
    have {HH} HH := HH : (i < size r); rewrite HH.
    case (ltngtP i.+1 (size r)) => Hisz.
    - by apply Hrow.
    - by rewrite ltnNge HH in Hisz.
    - move: Hrow HH Hl => _ _; by rewrite (last_nth 0) -Hisz.
  Qed.

  Lemma row_lt_by_pos r p q :
    is_row r -> p < size r -> q < size r -> nth 0 r p < nth 0 r q -> p < q.
  Proof.
    move/is_rowP => Hrow Hp Hq Hlt.
    have H : q <= p -> nth 0 r q <= nth 0 r p by move=> H; apply Hrow.
    by have:= contra H; rewrite -!ltnNge; apply.
  Qed.

  Lemma is_row_set_nth l r pos :
    is_row r -> l < nth 0 r pos ->
    (forall n : nat, l < nth 0 r n -> pos <= n) -> is_row (set_nth 0 r pos l).
  Proof.
    move=> /is_row1P Hrow Hl Hmin; apply/is_row1P => i.
    rewrite (lock (i.+1)) !nth_set_nth /=; unlock.
    case: (ltnP pos (size r)) Hl => [Hpos Hl |HH]; last by rewrite (nth_default 0 HH) ltn0.
    rewrite size_set_nth maxnC /maxn; have:= Hpos; rewrite leqNgt; move/negbTE => -> Hi1lt.
    case (altP (i =P pos)) => Hipos; case (altP (i.+1 =P pos)) => Hi1pos.
    - apply leqnn.
    - apply ltnW; apply (leq_trans Hl); rewrite -Hipos; by apply Hrow.
    - move: {Hmin} (contra (Hmin i)); rewrite -leqNgt -ltnNge; apply.
      by rewrite Hi1pos leqnn.
    - by apply Hrow.
  Qed.

End Rows.



Section Insert.

  Variable Row : seq nat.
  Hypothesis HRow : is_row Row.
  Variable l : nat.

  Definition inspred i := l < nth 0 Row i.
  Definition bump := l < (last 0 Row).

  Lemma notbump : ~~bump = (l >= (last 0 Row)).
  Proof. by rewrite /bump /= -leqNgt. Qed.

  Lemma transf : bump -> l < (nth 0 Row (size Row).-1).
  Proof. by rewrite nth_last. Qed.

  Lemma inspred_any_bump i : inspred i -> bump.
  Proof.
    rewrite /inspred /= /bump; have := HRow.
    elim: Row i => [/= | l0 r IHr] i; first by case: i.
    case: i => [|i] /= /andP [] Hhead Hrow.
    - case: r {IHr} Hhead Hrow => [//=|l1 r] /= Hl0l1.
      move/head_leq_last_row => Hlast Hll0.
      by apply (leq_trans Hll0 (leq_trans Hl0l1 Hlast)).
    - move=> H; have:= IHr _ Hrow H; by case r.
  Qed.

  Definition mininspred : nat :=
    if ltnP l (last 0 Row) is LtnNotGeq Hlast
    then ex_minn (ex_intro inspred (size Row).-1 (transf Hlast))
    else size Row.
  Definition insmin := set_nth 0 Row mininspred l.

  Lemma bump_mininspredE (Hbump : bump) :
    mininspred = ex_minn (ex_intro inspred (size Row).-1 (transf Hbump)).
  Proof.
    rewrite /mininspred /inspred; apply /eqP.
    case (ltnP l (last 0 Row)) => Hlast.
    - set exP := ex_intro _ _ _; case (ex_minnP exP) => pos1 {exP} Hl1 Hpos1.
      set exP := ex_intro _ _ _; case (ex_minnP exP) => pos2 {exP} Hl2 Hpos2.
      by rewrite eqn_leq (Hpos1 _ Hl2) (Hpos2 _ Hl1).
    - by exfalso; move: Hbump; rewrite /bump /= ltnNge Hlast.
  Qed.

  Lemma nbump_mininspredE : ~~bump -> mininspred = size Row.
  Proof.
    rewrite notbump /mininspred /inspred; by case (ltnP l (last 0 Row)) => [Hlt |//=].
  Qed.

  Fixpoint insrow r l : seq nat :=
    if r is l0 :: r then
      if l < l0 then l :: r
      else l0 :: (insrow r l)
    else [:: l].

  Fixpoint inspos r l : nat :=
    if r is l0 :: r then
      if l < l0 then 0
      else (inspos r l).+1
    else 0.

  Notation pos := (inspos Row l).
  Definition ins := set_nth 0 Row pos l.

  Lemma pos_lt_size_ins : pos < size ins.
  Proof.
    rewrite /ins size_set_nth /maxn; by case (ltnP pos.+1 (size Row)); first by apply ltnW.
  Qed.

  Lemma nth_pos_ins : nth 0 ins pos = l.
  Proof. by rewrite /ins nth_set_nth /= eq_refl. Qed.

  Lemma nbump_insposE : ~~bump -> mininspred = pos.
  Proof.
    move=> Hbump; rewrite (nbump_mininspredE Hbump).
    move: Hbump; rewrite notbump.
    elim: Row HRow => [//=|l0 r IHr] Hrow /= Hlast.
    case: (ltnP l l0) => [Hll0|_].
    * exfalso => {IHr}.
      have:= leq_ltn_trans (leq_trans (head_leq_last_row Hrow) Hlast) Hll0.
      by rewrite ltnn.
    * move: {IHr Hrow} (IHr (is_row_consK Hrow)).
      case: r Hlast => [//=| l1 r] /= Hlast.
      by case (ltnP l l1) => _ IHr; rewrite (IHr Hlast).
  Qed.

  Lemma inspred_inspos : bump -> inspred pos.
  Proof.
    rewrite /inspred /bump; elim: Row => [//=| l0 [_ /= H| l1 r /= IHr]].
    - by rewrite H /= H.
    - move/IHr; by case (ltnP l l0) => //=.
  Qed.

  Lemma inspred_mininspred : bump -> inspred mininspred.
  Proof.
    move=> Hbump; rewrite (bump_mininspredE Hbump).
    set exP := ex_intro _ _ _; by case (ex_minnP exP).
  Qed.

  Lemma nth_lt_inspos i : i < pos -> nth 0 Row i <= l.
  Proof.
    elim: Row i => [//=|t0 r IHr] /=; case (ltnP l t0) => //= Ht.
    case=> [//=|i] /=; by apply IHr.
  Qed.

  Lemma inspredN_lt_inspos i : i < pos -> ~~ (inspred i).
  Proof. rewrite /inspred -leqNgt; apply nth_lt_inspos. Qed.

  Lemma bump_insposE : bump -> mininspred = pos.
  Proof.
    move=> Hbump; rewrite (bump_mininspredE Hbump).
    set exP := ex_intro _ _ _; case (ex_minnP exP) => pos {exP} Hl Hpos.
    have Hleq := Hpos _ (inspred_inspos Hbump).
    case (ltnP pos (inspos Row l)) => H2.
    - exfalso; move: Hl; by rewrite (negbTE (inspredN_lt_inspos H2)).
    - apply /eqP; by rewrite eqn_leq Hleq H2.
  Qed.

  Lemma insposE : mininspred = pos.
  Proof. case (boolP bump); first by apply bump_insposE. by apply nbump_insposE. Qed.

  Lemma inspos_leq_exP i : inspred i -> pos <= i.
  Proof.
    move=> HlPred.
    rewrite -insposE (bump_mininspredE (inspred_any_bump HlPred)).
    set exP := ex_intro _ _ _; case (ex_minnP exP) => pos {exP} _ Hpos.
    by apply Hpos.
  Qed.

  Lemma insE : insmin = ins.
  Proof. by rewrite /insmin /ins insposE. Qed.

  Lemma insrowE : insmin = insrow Row l.
  Proof.
    rewrite /insmin insposE.
    elim: Row HRow => [//=| l0 r IHr] Hrow /=.
    case (ltnP l l0) => _ //=; by rewrite (IHr (is_row_consK Hrow)).
  Qed.

  Lemma bump_inspos_lt_size : bump -> pos < size Row.
  Proof.
    rewrite -insposE /bump; move=> Hbump; rewrite (bump_mininspredE Hbump).
    set exP := ex_intro _ _ _; case (ex_minnP exP) => pos {exP} Hl Hpos.
    have:= Hpos _ (transf Hbump); case: Row Hbump {Hl Hpos}; first by rewrite /= ltn0.
    move=> l0 r _ /=; by rewrite ltnS.
  Qed.

  Lemma nbump_inspos_eq_size : ~~bump -> pos = size Row.
  Proof. move=> Hnbump; by rewrite -insposE nbump_mininspredE. Qed.

  Lemma pos_leq_size : pos <= size Row.
  Proof.
    case (boolP bump) => Hlast.
    - apply ltnW; apply (bump_inspos_lt_size Hlast).
    - by rewrite nbump_inspos_eq_size.
  Qed.

  Lemma lt_inspos_nth i : i < size Row -> nth 0 Row i <= l -> i < pos.
  Proof.
    move: HRow; move=> /is_rowP Hrow Hi Hnthi; rewrite -insposE /mininspred /inspred.
    case (ltnP l (last 0 Row)) => [Hlt |//=].
    set exP := ex_intro _ _ _; case (ex_minnP exP) => pos {exP} Hl Hpos.
    have H1 := leq_ltn_trans Hnthi Hl; have H2 := Hrow pos i => {Hrow} {Hpos}.
    have {H2} H2: pos <= i -> nth 0 Row pos <= nth 0 Row i by move=> H; by apply H2.
    have := contra H2; rewrite -!ltnNge; by apply.
  Qed.

  Lemma insrow_head_lt : head 0 (insrow Row l) <= l.
  Proof. case: Row => [//=|l0 r] /=; by case (ltnP l l0). Qed.

  Lemma ins_head_lt : head 0 ins <= l.
  Proof. rewrite -insE insrowE; by apply insrow_head_lt. Qed.

  Lemma is_row_ins : is_row ins.
  Proof.
    move: HRow; rewrite -insE /insmin /mininspred => Hrow.
    case (ltnP l (last 0 Row)) => Hlast.
    - set exP := ex_intro _ _ _; case (ex_minnP exP) => pos {exP}.
      rewrite /inspred; by apply is_row_set_nth.
    - rewrite rcons_set_nth; by apply is_row_rcons.
  Qed.

  Lemma bump_size_ins : bump -> size ins = size Row.
  Proof.
    move/bump_inspos_lt_size; rewrite /insE /insmin size_set_nth maxnC /maxn leqNgt.
    by move/negbTE => ->.
  Qed.

  Lemma nbump_size_ins : ~~bump -> size ins = (size Row).+1.
  Proof.
    move/nbump_mininspredE => H.
    by rewrite -insE /insmin size_set_nth maxnC /maxn H ltnSn.
  Qed.

  Lemma nbump_ins_rconsE : ~~bump -> ins = rcons Row l.
  Proof. move/nbump_mininspredE => H; by rewrite -insE /insmin H rcons_set_nth. Qed.

  Lemma size_ins_inf : (size Row) <= size ins.
  Proof.
    rewrite -insE /insmin size_set_nth /maxn.
    by case (ltnP mininspred.+1 (size Row)).
  Qed.

  Lemma size_ins_sup : size ins <= (size Row).+1.
  Proof.
    rewrite /ins size_set_nth /maxn.
    case (ltnP pos.+1 (size Row)) => _.
    - by apply leqnSn.
    - by apply pos_leq_size.
  Qed.

  Lemma ins_leq i : i < size Row -> nth 0 ins i <= nth 0 Row i.
  Proof.
    rewrite -insE /insmin nth_set_nth /=.
    case (altP (i =P mininspred)) => [->|_ _]; last by apply leqnn.
    rewrite /mininspred /inspred; case (ltnP l (last 0 Row)) => [Hcase | Hcase].
    - set exP := ex_intro _ _ _; case (ex_minnP exP) => pos Hl _ _; by apply ltnW.
    - by rewrite ltnn.
  Qed.

  Lemma ins_non_nil : ins != [::].
  Proof. rewrite /ins; by apply set_nth_non_nil. Qed.

  Lemma size_ins_non_0 : 0 < size ins.
  Proof. move: ins_non_nil; by case ins. Qed.

End Insert.

Lemma bump_tail l0 r l : bump (l0 :: r) l -> l0 <= l -> bump r l.
Proof.
  rewrite /bump /= => Hbump Hll0.
  case: r Hbump => [/= H1 | //=].
  exfalso; have:= leq_trans H1 Hll0; by rewrite ltnn.
Qed.



Section Schensted.

  Implicit Type l : nat.
  Implicit Type r w s : seq nat.

  Fixpoint Sch_rev w := if w is l0 :: w' then ins (Sch_rev w') l0 else [::].
  Definition Sch w := Sch_rev (rev w).

  Lemma Sch_rcons l w : Sch (rcons w l) = ins (Sch w) l.
  Proof. by rewrite /Sch rev_rcons. Qed.

  Lemma is_row_Sch w : is_row (Sch w).
  Proof.
    elim/last_ind: w => [//= | w wn IHw]; by rewrite Sch_rcons is_row_ins.
  Qed.

  Lemma Sch_size w : size (Sch w) <= size w.
  Proof.
    elim/last_ind: w => [//= | w wn IHw]; rewrite Sch_rcons size_rcons.
    by apply (leq_trans (size_ins_sup (is_row_Sch w) wn)).
  Qed.

  Definition subseqrow s w := subseq s w && is_row s.
  Definition subseqrow_n s w n := [&& subseq s w , (size s == n) & is_row s].

  Theorem Sch_exists w i :
    i < size (Sch w) ->
    exists s : seq nat, (last 0 s == nth 0 (Sch w) i) && subseqrow_n s w i.+1.
  Proof.
    rewrite /subseqrow_n.
    elim/last_ind: w i => [//=| w wn IHw] i.
    rewrite Sch_rcons {2}/ins. (* -(insE (is_row_Sch w)) {2}/insmin. *)
    case (altP (i =P (inspos (Sch w) wn))) =>[|Hineq Hileq].
    - case: i => [<-|i Hieq ] _.
      * exists [:: wn] => /=; case (Sch w) => [|_ _];
            rewrite -cats1 suffix_subseq; apply/and4P; by repeat split.
      * have:= pos_leq_size (is_row_Sch w) wn; rewrite -Hieq.
        case/IHw => {IHw} s => /and4P [] /eqP Hlast Hsubs /eqP Hsz Hrow.
        exists (rcons s wn); apply/and4P; repeat split.
        + by rewrite last_rcons nth_set_nth /= eq_refl.
        + by apply subseq_rcons_eq.
        + by rewrite size_rcons Hsz.
        + apply (is_row_rcons Hrow); rewrite Hlast.
          by apply nth_lt_inspos; rewrite -Hieq ltnSn.
    - have: (i < size (Sch w)); have HrowSch := is_row_Sch w.
        move: Hineq Hileq; case (boolP (bump (Sch w) wn )) => Hcase.
        + by rewrite (bump_size_ins HrowSch Hcase).
        + rewrite (nbump_inspos_eq_size HrowSch Hcase) (nbump_size_ins HrowSch Hcase).
          by rewrite ltnS ltn_neqAle => -> ->.
      case/IHw => {IHw} s => /and4P [] /eqP Hlast Hsubs /eqP Hsz Hrow.
      exists s; apply/and4P; repeat split.
        + by rewrite Hlast nth_set_nth /= (negbTE Hineq).
        + by apply (subseq_trans Hsubs); apply subseq_rcons.
        + by rewrite Hsz.
        + exact Hrow.
  Qed.

  Theorem Sch_leq_last w s si:
    subseqrow (rcons s si) w -> size s < size (Sch w) /\ nth 0 (Sch w) (size s) <= si.
  Proof.
    rewrite /subseqrow => /andP [].
    elim/last_ind: w s si => [| w wn IHw] s si; first by rewrite subseq0 rcons_nilF.
    rewrite Sch_rcons  /=; have HSch := is_row_Sch w.
    case (altP (si =P wn)) => [-> {si} | Hsiwn Hsubs Hrow].

    (* The subseqence s ends by wn *)
    - rewrite -subseq_rcons_eq.
      case/lastP: s => [ _ _ {IHw} | s si Hsubs Hrow].
      (* s = wn *)
      * split; first by rewrite size_ins_non_0.
        rewrite -[size [::]]/(0) nth0; apply ins_head_lt; by apply is_row_Sch.
      (* s = [s] si wn *)
      have:= IHw _ _ Hsubs (is_row_rconsK Hrow) => [] [] Hszlt Hlt {IHw}.
      have:= is_row_last Hrow; rewrite last_rcons => Hsiwn.

      case (boolP (bump (Sch w) wn )) => [Hbump | Hnbump].
      (* Wn bump a letter *)
      * have Hszpos: (size s < inspos (Sch w) wn).
          apply (lt_inspos_nth (is_row_Sch w) Hszlt).
          by apply (leq_trans Hlt Hsiwn).
        rewrite size_rcons (bump_size_ins HSch Hbump); split.
        + by apply (leq_ltn_trans Hszpos (bump_inspos_lt_size HSch Hbump)).
        + rewrite {2}(_: wn = nth 0 (ins (Sch w) wn) (inspos (Sch w) wn));
            last by rewrite /ins nth_set_nth /= eq_refl.
          have: (is_row (ins (Sch w) wn)) by apply is_row_ins.
          move /is_rowP; apply; first by [].
          by rewrite size_set_nth leq_max ltnSn.

      (* Insertion add a new [wn] box *)
      * rewrite (nbump_ins_rconsE HSch Hnbump) !size_rcons nth_rcons; split; first by [].
        case (leqP (size s).+2 (size (Sch w))) => Hsz.
        + apply (@leq_trans (last 0 (Sch w)) _ wn); last by rewrite -notbump.
          rewrite -(nth_last 0).
          apply (is_rowP _ HSch); first by have:= Hsz; rewrite -{1}(ltn_predK Hsz).
          rewrite -{2}(ltn_predK Hsz); by apply ltnSn.
        + case (altP ((size s).+1 =P size (Sch w))) => _; first by apply leqnn.
          by apply leq0n.

    (* The subsequence doesn't end by wn *)
    - have {Hsiwn Hsubs} Hsubs := subseq_rcons_neq Hsiwn Hsubs.
      have:= IHw _ _ Hsubs Hrow => [] {IHw Hrow Hsubs} [] Hsize Hleq; split.
      * by apply (leq_trans Hsize); apply size_ins_inf.
      * by apply (leq_trans (ins_leq HSch wn Hsize) Hleq).
  Qed.

  Theorem size_ndec_Sch w s : subseqrow s w -> (size s) <= size (Sch w).
  Proof.
    case/lastP: s => [//=| s si].
    move/Sch_leq_last => [] H _.
    by rewrite size_rcons.
  Qed.

  Theorem exist_size_Sch w : exists s : seq nat, subseqrow_n s w (size (Sch w)).
  Proof.
    case/lastP: w => [| w wn]; first by exists [::].
    have:= size_ins_non_0 (Sch w) wn; rewrite -Sch_rcons.
    case Hn : (size _) => [_ //=| n] _.
    have:= ltnSn n; rewrite -{2}Hn => H.
    elim (Sch_exists H) => s /andP [] _ Hrsq.
    by exists s.
  Qed.

End Schensted.

Section SubSeq.

  Variable w : seq nat.

  Definition PRowSeq :=
    [pred i : nat | [exists s : SubSeq w, (size s == i) && (is_row s)]].

  Lemma exrow0 : PRowSeq 0.
  Proof. apply /existsP. by exists (sub_nil w). Qed.

  Lemma max_row_len : forall i : nat, PRowSeq i -> i <= size w.
  Proof. rewrite /PRowSeq=> i /= /existsP [[s Hs]] /andP [] /eqP <- _; by apply size_le. Qed.

  Definition max_subseqrow_size := ex_maxn (ex_intro _ 0 exrow0) max_row_len.

  Theorem size_max_subseqrow : max_subseqrow_size == size (Sch w).
  Proof.
    rewrite /max_subseqrow_size.
    case (ex_maxnP (ex_intro _ 0 exrow0) max_row_len) => i.
    rewrite /PRowSeq /= => /existsP [] [s Hs] /andP [] /= /eqP Hsz Hrow Hmax.
    rewrite -Hsz.
    apply/eqP/anti_leq/andP; split.
    - apply size_ndec_Sch; rewrite /subseqrow; apply/andP; split; last exact Hrow.
      rewrite subseqs_all; by apply Hs.
    - rewrite Hsz; case (exist_size_Sch w) => smax {Hrow Hsz}.
      rewrite /subseqrow_n => /and3P [] /subseqs_all Hsubs /eqP <- Hrow.
      apply Hmax; apply /existsP; exists (SeqSub Hsubs).
      by rewrite /= Hrow eq_refl.
  Qed.

End SubSeq.

Section Bump.

  Variable Row : seq nat.
  Hypothesis HRow : is_row Row.
  Variable l : nat.

  Definition bumped := nth 0 Row (inspos Row l).
  Notation ins := (ins Row l).
  Notation inspos := (inspos Row l).
  Notation insRow := (insrow Row l).
  Notation bump := (bump Row l).

  Lemma lt_bumped : bump -> l < bumped.
  Proof. by move/inspred_inspos. Qed.

  Fixpoint bumprow r l : (option nat) * (seq nat) :=
    if r is l0 :: r then
      if l < l0 then (Some l0, l :: r)
      else let: (lr, rr) := bumprow r l in (lr, l0 :: rr)
    else (None, [:: l]).

  Notation bumpRow := (bumprow Row l).

  Lemma ins_bumprowE : insRow = bumpRow.2.
  Proof.
    elim: Row => [//= | t0 r IHr /=].
    case (ltnP l t0) => _ //=.
    by move: IHr; case (bumprow r l) => [lr tr] /= ->.
  Qed.

  Lemma bump_bumprowE : bump -> bumpRow = (Some bumped, ins).
  Proof.
    rewrite /bumped -(insE HRow) (insrowE HRow).
    elim: Row HRow => [//= | t0 r IHr] Hrow /= Hlast.
    case (ltnP l t0) => //=.
    move: Hlast => /bump_tail H/H {H} Hlast.
    by rewrite (IHr (is_row_consK Hrow) Hlast).
  Qed.

  Lemma nbump_bumprowE : ~~bump -> bumpRow = (None, ins).
  Proof.
    rewrite notbump -(insE HRow) (insrowE HRow).
    elim: Row HRow => [//= | t0 r IHr] Hrow Hlast /=.
    case (ltnP l t0) => //= Ht0.
    - exfalso.
      have:= leq_ltn_trans (leq_trans (head_leq_last_row Hrow) Hlast) Ht0.
      by rewrite ltnn.
    - have {Hlast} Hlast : (last 0 r <= l) by case: r {IHr Hrow} Hlast.
      by rewrite (IHr (is_row_consK Hrow) Hlast).
  Qed.

  Lemma head_ins_lt_bumped i : bump -> head i ins < bumped.
  Proof.
    move=> Hbump; have:= is_row_ins HRow l => /is_rowP Hrowins.
    rewrite -nth0 (nth_any i 0 (size_ins_non_0 _ _)).
    apply (@leq_ltn_trans (nth 0 ins inspos)).
    + apply (Hrowins _ _ (leq0n _)).
      rewrite (bump_size_ins HRow Hbump).
      by apply bump_inspos_lt_size.
    + rewrite /ins nth_set_nth /= eq_refl.
      by apply lt_bumped.
  Qed.

  Lemma bumprow_size :
    let: (lr, tr) := bumpRow in
    (size Row).+1 == (size tr) + if lr is Some _ then 1 else 0.
  Proof.
    elim: Row => [//= | t0 r IHr /=].
    case (ltnP l t0) => _ /=; first by rewrite -addn1.
    by move: IHr; case (bumprow r l) => [lr tr] /= /eqP ->.
  Qed.

  Lemma bumprow_mult i :
    let: (lr, tr) := bumpRow in
    count_mem i Row + (l == i) == count_mem i tr + if lr is Some ll then (ll == i) else 0.
  Proof.
    elim: Row => [| t0 r IHr] /=; first by rewrite !addn0.
    case (ltnP l t0) => _ /=.
    - by rewrite addnC -addnA eqn_add2l addnC eqn_add2l [t0 == i]eq_sym.
    - move: IHr; case (bumprow r l) => [tr lr] /= IHr.
      by rewrite -!addnA eqn_add2l.
  Qed.

End Bump.


Lemma bumprow_rcons r l : is_row (rcons r l) -> bumprow r l = (None, rcons r l).
Proof.
  move=> Hrow; have:=(is_row_last Hrow); rewrite leqNgt => Hnbump.
  have Hr := is_row_rconsK Hrow.
  by rewrite (nbump_bumprowE Hr Hnbump) (nbump_ins_rconsE Hr Hnbump).
Qed.


Section Dominate.

  Implicit Type l : nat.
  Implicit Type r u v : seq nat.

  Definition dominate u v :=
    ((size u) <= (size v)) && (all (fun i => nth 0 u i > nth 0 v i) (iota 0 (size u))).

  Lemma dominateP u v :
    reflect ((size u) <= (size v) /\ forall i, i < size u -> nth 0 u i > nth 0 v i)
            (dominate u v).
  Proof.
    rewrite /dominate /mkseq ; apply/(iffP idP).
    - move=> /andP [] Hsz /allP Hall; split; first by exact Hsz.
      move=> i Hi; apply Hall; by rewrite mem_iota add0n.
    - move=> [] -> /= H; apply /allP => i; rewrite mem_iota add0n; by apply H.
  Qed.

  Lemma dominate_nil u : dominate [::] u.
  Proof. apply /dominateP => /=; by split. Qed.

  Lemma dominate_rcons v u l : dominate u v -> dominate u (rcons v l).
  Proof.
    move /dominateP => [] Hsz Hlt.
    apply /dominateP; split => [|i Hi]; first by rewrite size_rcons; apply leqW.
    have H := Hlt _ Hi; rewrite nth_rcons.
    case (ltnP i (size v)) => Hcomp //= {H}.
    move: {Hsz Hlt Hcomp} (leq_trans Hsz Hcomp) => Hs.
    have:= leq_ltn_trans Hs Hi; by rewrite ltnn.
  Qed.

  Lemma dominate_rconsK u v l :
    size u <= size v -> dominate u (rcons v l) -> dominate u v.
  Proof.
    move=> Hsz /dominateP [] _ Hlt.
    apply /dominateP; split => [|i Hi]; first exact Hsz.
    have Hiv := leq_trans Hi Hsz.
    by have:= Hlt _ Hi; rewrite nth_rcons Hiv.
  Qed.

  Lemma dominate_head u v : u != [::] -> dominate u v -> head 0 v < head 0 u.
  Proof.
    move=> Hu /dominateP []; case: u Hu => [//=|u0 u _]; case: v => [|v0 v _] /=.
    - by rewrite ltn0.
    - move=> Hdom; by apply (Hdom 0 (ltn0Sn _)).
  Qed.

  Lemma dominate_inspos r1 r0 l :
    is_row r0 -> is_row r1 -> dominate r1 r0 ->
    bump r0 l -> inspos r0 l >= inspos r1 (bumped r0 l).
  Proof.
    move=> Hrow0 Hrow1 /dominateP [] _ Hdom /= Hbump.
    case (ltnP (inspos r0 l) (size r1)) => [|Hpossz].
    - move/Hdom => {Hdom}; rewrite -/(bumped r0 l).
      move: (bumped r0 l) (inspos r0 l) => l1 pos {r0 Hrow0 Hbump l} Hl1.
      by apply inspos_leq_exP.
    - by apply (@leq_trans (size r1)); first by apply pos_leq_size.
  Qed.

  Lemma bump_dominate r1 r0 l :
    is_row r0 -> is_row r1 -> bump r0 l ->
    dominate r1 r0 -> dominate (ins r1 (bumped r0 l)) (ins r0 l).
  Proof.
    move=> Hrow0 Hrow1 Hbump Hdom; have:= Hdom => /dominateP [] Hsize Hlt.
    apply /dominateP; split.
    - rewrite (bump_size_ins Hrow0 Hbump) {1}/ins size_set_nth /maxn.
      case: (ltnP (inspos r1 (bumped r0 l)).+1 (size r1)) => [//=|_].
      apply (@leq_ltn_trans (inspos r0 l)); first by apply dominate_inspos.
      by apply bump_inspos_lt_size.
    - move=> i Hi; rewrite /ins; have:= dominate_inspos Hrow0 Hrow1 Hdom Hbump.
      set pos0 := inspos r0 _; set pos1 := inspos r1 _.
      move=> Hpos; rewrite !nth_set_nth /=.
      case (altP (i =P pos0)) => Hipos0;
         case (altP (i =P pos1)) => Hipos1.
      * by apply lt_bumped.
      * apply (leq_trans (lt_bumped Hbump)); move Hl0 : (bumped r0 l) => l0.
        rewrite -Hipos0 in Hpos => {Hrow0 Hlt Hdom Hsize Hbump Hipos0}.
        rewrite /pos1 in Hipos1 Hpos; rewrite Hl0 in Hipos1 Hi Hpos => {pos1 pos0 Hl0}.
        have:= is_row_ins Hrow1 l0 => /is_rowP Hrowins.
        rewrite (_ : l0 = nth 0 (ins r1 l0) (inspos r1 l0));
          last by rewrite nth_set_nth /= eq_refl.
        rewrite (_ : nth 0 r1 i = nth 0 (ins r1 l0) i);
          last by rewrite nth_set_nth /= (negbTE Hipos1).
        by apply Hrowins.
      * apply (@leq_ltn_trans l); last by apply lt_bumped.
        subst pos0; apply nth_lt_inspos; by rewrite ltn_neqAle Hipos0 /= Hipos1.
      * case (ltnP i (size r1)) => [|Hsz]; first by apply Hlt.
        exfalso; case (boolP (bump r1 (bumped r0 l))) => [|Hnbump].
        + move/bump_size_ins => H; rewrite (H Hrow1) in Hi.
          have:= leq_ltn_trans Hsz Hi; by rewrite ltnn.
        + have:= Hnbump; move/nbump_ins_rconsE => Heq.
          rewrite (Heq Hrow1) size_rcons ltnS in Hi.
          have {Hi Hsz} Hi: (i == size r1) by rewrite eqn_leq Hi Hsz.
          rewrite /pos1 (nbump_inspos_eq_size Hrow1 Hnbump) in Hipos1.
          by rewrite Hi in Hipos1.
  Qed.

  Lemma dominateK_inspos r1 r0 l0 :
    is_row r0 -> is_row r1 -> dominate (ins r1 (bumped r0 l0)) (ins r0 l0) ->
    bump r0 l0 -> inspos r0 l0 >= inspos r1 (bumped r0 l0).
  Proof.
    move Hl1 : (bumped r0 l0) => l1; rewrite /bumped in Hl1.
    move=> Hrow0 Hrow1 /dominateP [] Hsz Hdom /= Hbump.
    case (leqP (inspos r1 l1) (inspos r0 l0)) => [//= | Habs].
    have Hpos1 := (pos_lt_size_ins r1 l1).
    have := (leq_trans Hpos1 Hsz); rewrite (bump_size_ins Hrow0 Hbump) => Hpos0.
    move: Hrow0 => /is_rowP Hrow0.
    have {Hrow0} := Hrow0 _ _ (ltnW Habs) Hpos0; rewrite Hl1 => H1.
    have:= (Hdom _ Hpos1); rewrite /ins !nth_set_nth /= (gtn_eqF Habs) eq_refl.
    move/(leq_ltn_trans H1); by rewrite ltnn.
  Qed.

  Lemma bump_dominateK r1 r0 l0 :
    is_row r0 -> is_row r1 -> bump r0 l0 ->
    dominate (ins r1 (bumped r0 l0)) (ins r0 l0) -> dominate r1 r0.
  Proof.
    move=> Hrow0 Hrow1 Hbump0 Hdom; have:= Hdom => /dominateP [] Hsize Hlt.
    have:= dominateK_inspos Hrow0 Hrow1 Hdom Hbump0 => Hpos.
    move Hl1 : (bumped r0 l0) => l1; rewrite Hl1 in Hdom Hsize Hlt Hpos.
    rewrite /bumped in Hl1.
    apply /dominateP; split.
    - move: Hsize; rewrite (bump_size_ins Hrow0 Hbump0).
      apply/leq_trans; by apply size_ins_inf.
    - move=> i Hi; have Hi' := leq_trans Hi (size_ins_inf Hrow1 l1).
      case (altP (i =P inspos r1 l1)) => Hipos1.
      * have:= nth_pos_ins r1 l1; rewrite -Hipos1.
        have:= Hlt i Hi'; rewrite {1}Hipos1 {1}/ins nth_set_nth {1}Hipos1 /=.
        case (altP (i =P inspos r0 l0)) => [Hipos0 _| Hipos0].
        + rewrite {2}Hipos0 Hl1 => <-; rewrite Hipos1 nth_pos_ins.
          case (boolP (bump r1 l1)) => Hbump;
            last by move: Hi; rewrite Hipos1 (nbump_inspos_eq_size Hrow1 Hbump) ltnn.
          have:= (inspred_mininspred Hbump); by rewrite insposE /inspred.
        + rewrite -{1 2}Hipos1 (negbTE Hipos0) nth_pos_ins => Hlt1 Heqins.
          apply (leq_trans Hlt1); rewrite -Heqins.
          by apply ins_leq.
      * case (altP (i =P inspos r0 l0)) => [Hipos0 | Hipos0].
        + rewrite Hipos0 Hl1.
          have:= (contra (@lt_inspos_nth r1 Hrow1 l1 _ Hi)).
          rewrite -leqNgt -ltnNge Hipos0; by apply.
        + have:= Hlt _ Hi'; by rewrite !/ins !nth_set_nth /= (negbTE Hipos0) (negbTE Hipos1).
  Qed.

End Dominate.

Section Tableaux.

  Implicit Type l : nat.
  Implicit Type r w : seq nat.
  Implicit Type t : seq (seq nat).

  Fixpoint is_tableau t :=
    if t is t0 :: t'
    then [&& (t0 != [::]), is_row t0, dominate (head [::] t') t0 & is_tableau t']
    else true.

  Lemma tableau_is_row r t : is_tableau (r :: t) -> is_row r.
  Proof. by move=> /= /and4P []. Qed.

  Lemma is_part_sht t : is_tableau t -> is_part (shape t).
  Proof.
    elim: t => [//= | t0 t IHt] /= /and4P [] Ht0 _ /dominateP [] Hdom _ Htab.
    rewrite (IHt Htab) andbT {IHt Htab} /shape.
    case: t Hdom => //=; by case: t0 Ht0.
  Qed.

  Fixpoint instab t l : seq (seq nat) :=
    if t is t0 :: t' then
      let: (lr, rr) := bumprow t0 l in
      if lr is Some ll then rr :: (instab t' ll) else rr :: t'
    else [:: [:: l]].

  Lemma head_instab (t0 : seq nat) t l :
    is_row t0 -> head [::] (instab (t0 :: t) l) = ins t0 l.
  Proof.
    move=> Hrow; rewrite -(insE Hrow) (insrowE Hrow).
    rewrite ins_bumprowE /=; by case (bumprow t0 l) => [[l'|]] b.
  Qed.

  Theorem is_tableau_instab t l : is_tableau t -> is_tableau (instab t l).
  Proof.
    elim: t l => [l _ /=| t0 t IHt l Htab]; first by rewrite leqnn /=.
    move: Htab => /and4P [] Ht0 Hrow0 Hdom; rewrite -/is_tableau =>  Htab.
    case (boolP (bump t0 l)) => [Hbump0 | Hnbump0].
    - rewrite /= (bump_bumprowE Hrow0 Hbump0).
      case: t IHt Hdom Htab => [_ _ _ | t1 t IHt Hdom Htab] /=.
      * rewrite ins_non_nil (is_row_ins Hrow0) leqnn /= andbT.
        rewrite -[[:: bumped t0 l]]/(ins [::] ( bumped t0 l)).
        by apply bump_dominate.
      * have Hrow1 := tableau_is_row Htab.
        rewrite (head_instab _ _ Hrow1).
        move: {IHt} (IHt (bumped t0 l) Htab) => /= ->.
        rewrite ins_non_nil (is_row_ins Hrow0) /= andbT.
        by apply bump_dominate.
    - rewrite /= (nbump_bumprowE Hrow0 Hnbump0) /= Htab.
      rewrite ins_non_nil (is_row_ins Hrow0) /= andbT.
      rewrite (nbump_ins_rconsE Hrow0 Hnbump0); by apply dominate_rcons.
  Qed.

  Lemma instab_non_nil t l : instab t l != [::].
  Proof. case: t => [//=| t0 t /=]. by case (bumprow t0 l) => [[ll|]] l0. Qed.

  Definition to_word t := flatten (rev t).

  Fixpoint RS_rev w : seq (seq nat) :=
    if w is w0 :: wr then instab (RS_rev wr) w0 else [::].
  Definition RS w := RS_rev (rev w).

  Theorem is_tableau_RS w : is_tableau (RS w).
  Proof.
    elim/last_ind: w => [//= | w l0 /=].
    rewrite /RS rev_rcons /=.
    by apply is_tableau_instab.
  Qed.

End Tableaux.



Section InverseBump.

  Implicit Type a b l : nat.
  Implicit Type r s w : seq nat.
  Implicit Type t : seq (seq nat).

  Definition invbump b s := (head 0 s) < b.

  Fixpoint invbumprow b s : (seq nat) * nat :=
    if s is l0 :: s then
      if b <= head b s
      then (b :: s, l0)
      else let: (rr, lr) := invbumprow b s in (l0 :: rr, lr)
    else (* unused case *) ([::], b).

  Definition invins b s := (invbumprow b s).1.
  Definition invbumped b s := (invbumprow b s).2.

  Lemma head_lt_invins b s i : s != [::] -> invbump b s -> head i s <= head i (invins b s).
  Proof.
    rewrite /invins /invbump; case: s => [//=| l0 s /= _].
    case: (invbumprow b s) => r a.
    case (leqP b (head b s)) => _ //=.
    by apply ltnW.
  Qed.

  Lemma is_row_invins b s : is_row s -> is_row (invins b s).
  Proof.
    rewrite /invins.
    elim: s => [_ //=|l0 s IHs] /= /andP [] Hhead Hrow.
    case (leqP b (head b s)) => [/= -> //=| Hb /=].
    have:= IHs Hrow.
    case H : (invbumprow b s) => [r a] /= ->; rewrite andbT.
    apply (leq_trans Hhead).
    rewrite (_ : r = invins b s); last by rewrite /invins H.
    case (altP (s =P [::])) => [|Hnnil]; first by move ->.
    apply (head_lt_invins _ Hnnil).
    by rewrite /invbump (head_any _ b Hnnil).
  Qed.

  Lemma head_leq_invbumped b s :
    s != [::] -> is_row s -> head 0 s <= (invbumped b s).
  Proof.
    rewrite /invbumped.
    elim: s => [_ //=|l0 s IHs] /= _ /andP [] Hhead Hrow.
    case (altP (s =P [::])) => [-> /=| Hnnil]; first by rewrite leqnn.
    rewrite (head_any _ 0 Hnnil).
    case (leqP b (head (0:nat_eqType) s)) => [/= |_]; first by rewrite leqnn.
    move: {IHs} (IHs Hnnil Hrow).
    case H : (invbumprow b s) => [r a] /= Hb.
    apply (leq_trans Hhead).
    by rewrite (head_any _ 0 Hnnil).
  Qed.

  Lemma invbumprowK r a :
    is_row r -> bump r a ->
    (invbumprow (bumped r a) (ins r a)) == (r, a).
  Proof.
    rewrite /bump; move=> Hrow Hbump; have:= bump_bumprowE Hrow Hbump.
    elim: r Hrow Hbump => [_ /= |l0 r IHr /= /andP [] Hl0 Hrow Hbump]; first by rewrite ltn0.
    case: (ltnP a l0) => Hal0.
    - move=> [] <- <- /=; by rewrite Hl0.
    - have {Hbump} Hbump: (a < last 0 r) by
        case: r {IHr Hl0 Hrow} Hbump Hal0 => [/= /leq_trans H/H|//=]; by rewrite ltnn.
      have H := bump_bumprowE Hrow Hbump.
      rewrite H => [] [] <- <- /=.
      have:= head_ins_lt_bumped Hrow (bumped r a) Hbump; rewrite ltnNge => /negbTE ->.
      - by rewrite (eqP (IHr Hrow Hbump H)).
  Qed.

  Lemma bumprowinvK b s :
    s != [::] -> is_row s -> invbump b s ->
    (bumprow (invins b s) (invbumped b s)) == (Some b, s).
  Proof.
    rewrite /invbump /invins /invbumped.
    elim: s => [//= | s0 s IHs] /= _ /andP [] Hhead Hrows Hs0.
    case (altP (s =P [::])) => [-> /=| Hnnil]; first by rewrite leqnn /= Hs0.
    rewrite (head_any _ 0 Hnnil).
    case (leqP b (head (0:nat_eqType) s)) => [/= |]; first by rewrite Hs0.
    move/(IHs Hnnil Hrows) {IHs}.
    case H : (invbumprow b s) => [r a] /= /eqP Hb; rewrite Hb.
    suff: (s0 <= a); first by rewrite leqNgt => /negbTE ->.
    apply (leq_trans Hhead); rewrite (head_any _ 0 Hnnil).
    by have:= head_leq_invbumped b Hnnil Hrows; rewrite /invbumped H /=.
  Qed.

  Fixpoint instabn t l : seq (seq nat) * nat :=
    if t is t0 :: t then
      let: (lr, rr) := bumprow t0 l
      in if lr is Some ll then
           let: (tres, nres) := instabn t ll
           in (rr :: tres, nres.+1)
         else (rr :: t, 0)
    else ([:: [:: l]], 0).

  Lemma instabnE t l : (instabn t l).1 = instab t l.
  Proof.
    elim: t l => [//=| t0 t IHt] l /=.
    case: (bumprow t0 l) => [[ll|//=] rr].
    have:= IHt ll; by case: (instabn t ll) => [tres nres] /= ->.
  Qed.


  Lemma shape_instabn t l :
    is_tableau t ->
    let: (tr, row) := instabn t l in shape tr == incr_nth (shape t) row.
  Proof.
    case H : (instabn t l) => [tr row] Htab.
    elim: t Htab l tr row H => [/= _| t0 t IHt /= /and4P [] _ Hrow _ Htab] l tr row /=;
        first by move=> [] <- <-.
    case: (boolP (bump t0 l)) => [Hbump | Hnbump].
    - rewrite (bump_bumprowE Hrow Hbump).
      case: row => [|row]; first by case (instabn t (bumped t0 l)).
      case Hins: (instabn t (bumped t0 l)) => [tres nres] [] <- <- /=.
      have:= IHt Htab (bumped t0 l) tres nres Hins => /eqP ->.
      by rewrite (bump_size_ins Hrow Hbump).
    - have:= nbump_bumprowE Hrow Hnbump => -> [] <- <- /=.
      by rewrite (nbump_size_ins Hrow Hnbump).
  Qed.

End InverseBump.



Section Inverse.

  Implicit Type a b l : nat.
  Implicit Type r s w : seq nat.
  Implicit Type t u : seq (seq nat).

  Lemma is_out_corner_nrow t l : is_tableau t ->
      let: (res, nrow) := instabn t l in is_out_corner (shape res) nrow.
  Proof.
    rewrite /is_out_corner.
    elim: t l => [l _ //=|t0 t IHt l /= /and4P [] Hnnil Hrow /dominateP [] Hdom _ Htab].
    case: (boolP (bump t0 l)) => [Hbump | Hnbump].
    - rewrite (bump_bumprowE Hrow Hbump) /=.
      have:= IHt (bumped t0 l) Htab.
      by case (instabn t (bumped t0 l)) => [res nrow].
    - rewrite (nbump_bumprowE Hrow Hnbump) (nbump_ins_rconsE Hrow Hnbump) /= size_rcons.
      move: Hdom; rewrite -nth0 /=; by case t => //=.
  Qed.

  Fixpoint invinstabn t nrow : seq (seq nat) * nat :=
    if t is t0 :: t
    then if nrow is nrow.+1
         then let: (tr, lr) := invinstabn t nrow in
              let: (t0r, l0r) := invbumprow lr t0 in
              (t0r :: tr, l0r)
         else if t0 is l0 :: t0
              then if t0 == [::]
                   then (t, l0)
                   else ((belast l0 t0) :: t, last l0 t0)
              else (* unused case *) ([::], 0)
    else (* unused case *) ([::], 0).

  Theorem invinstabnK t l :
    is_tableau t -> invinstabn (instab t l) (instabn t l).2 == (t, l).
  Proof.
    elim: t l => [l //=| t0 t IHt] l /= /and4P [] Hnnil Hrow0 Hdom Htab.
    case: (boolP (bump t0 l)) => [Hbump | Hnbump].
    - rewrite (bump_bumprowE Hrow0 Hbump) /=.
      have:= IHt (bumped t0 l) Htab.
      case Hres : (instabn t (bumped t0 l)) => [tres nres] /= /eqP ->.
      by rewrite (eqP (invbumprowK Hrow0 Hbump)).
    - rewrite (nbump_bumprowE Hrow0 Hnbump) (nbump_ins_rconsE Hrow0 Hnbump) /=.
      case Hres : (rcons t0 l) => [| ares tres]; first by move: Hres; case t0.
      case: (altP (tres =P [::])) => Htres.
      * exfalso; move: Hnnil; have:= eq_refl (size (rcons t0 l)).
        by rewrite {2}Hres Htres size_rcons /= => /nilP ->.
      * rewrite (_ : (belast ares tres) = t0);
          last by have:= eq_refl (belast 0 (rcons t0 l));
                  rewrite {2}belast_rcons Hres /= => /eqP [].
        by rewrite (_ : (last ares tres) = l);
          last by have:= eq_refl (last 0 (rcons t0 l));
                  rewrite {2}last_rcons Hres /= => /eqP.
  Qed.

  Lemma invbump_geq_head t tin l nrow :
    t != [::] -> is_tableau t -> invinstabn t nrow = (tin, l) -> l >= head 0 (head [::] t).
  Proof.
    case: t => [//= | r0 t] /= _ /and4P [] Hnnil0 Hrow0 _ _.
    case: nrow => [| nrow].
    - case: r0 Hnnil0 Hrow0 => [//= | l0 [| l1 tl0]] _ H /= [] _ <- //=.
      exact (head_leq_last_row H).
    - case: (invinstabn t nrow) => [tr lr].
      have:= head_leq_invbumped lr Hnnil0 Hrow0.
      rewrite /invbumped.
      by case: (invbumprow lr r0) => [t0r l0r] /= H [] _ <-.
  Qed.

  Lemma invbump_dom r0 t tin l nrow :
    t != [::] -> is_tableau t -> invinstabn t nrow = (tin, l) ->
    r0 != [::] -> dominate (head [::] t) r0 -> invbump l r0.
  Proof.
    rewrite /invbump => Htnnil Ht Hinv.
    have {Hinv} := invbump_geq_head Htnnil Ht Hinv.
    case: t Htnnil Ht => [//= | r1 t] /= _ /and4P [] Hnnil1 _ _ _.
    case: r1 Hnnil1 => [//= | l1 r1 ] /= _ Hl1.
    case: r0 => [//= | l0 r0 ] /= _ /dominateP [ ] _ Hdom.
    have {Hdom} :=(Hdom 0 (ltn0Sn _)) => /= Hl0.
    exact (leq_trans Hl0 Hl1).
  Qed.

  Theorem instabninvK t nrow :
    is_tableau t -> t != [::] -> is_out_corner (shape t) nrow ->
    let: (tin, l) := invinstabn t nrow in (instabn tin l) == (t, nrow).
  Proof.
    elim: t nrow => [//= | t0 t IHt] nrow /= /and4P [] Hnnil0 Hrow0 Hdom Htab _.
    rewrite /is_out_corner.
    case: nrow => [{IHt} /= Hcorn | nrow Hcorn].
    + case: t0 Hnnil0 Hrow0 Hdom Hcorn => [//= | l0 t0 _].
      case: (altP (t0 =P [::])) => [/= -> _ _ | Hnnil0 Hrow0 _ _].
      * case: t Htab => [//= |t1 t] /= /and4P [] Ht _ _ _ Hsz.
        exfalso; move: Ht Hsz; by case t1.
      * elim/last_ind: t0 Hnnil0 Hrow0 => [//= | tt0 ln IHtt0] _ Hrow0.
        (* t0 = l0 :: [tt0] :: ln *)
        have:= head_leq_last_row Hrow0.
        rewrite belast_rcons last_rcons /= leqNgt => /negbTE ->.
        move: Hrow0 => /= /andP [] _ Hrow0.
        by rewrite (bumprow_rcons Hrow0).
    + have Hnnil : (t != [::]) by move: Hcorn; case t => //=; rewrite nth_nil.
      have {IHt Hcorn} := IHt nrow Htab Hnnil Hcorn => /=.
      case H: (invinstabn t nrow) => [tin l].
      have Hinvbump: (invbump l t0) by apply (@invbump_dom t0 t tin l nrow).
      have:= bumprowinvK Hnnil0 Hrow0 Hinvbump.
      rewrite /invins /invbumped.
      by case: (invbumprow l t0) => [t0r l0r] /= /eqP -> /eqP ->.
  Qed.

  Fixpoint RSmap_rev w : (seq (seq nat)) * (seq nat) :=
    if w is w0 :: wtl
    then let: (t, rows) := RSmap_rev wtl in
         let: (tr, nrow) := instabn t w0 in
         (tr, nrow :: rows)
    else ([::], [::]).
  Definition RSmap w := RSmap_rev (rev w).

  Lemma RSmapE w : (RSmap w).1 = RS w.
  Proof.
    elim/last_ind: w => [//= | w wn /=]; rewrite /RSmap /RS rev_rcons /= -instabnE.
    case: (RSmap_rev (rev w)) => [t rows] /= ->.
    by case: (instabn (RS_rev (rev w)) wn).
  Qed.

  Lemma is_tableau_RSmap1 w : is_tableau (RSmap w).1.
  Proof. rewrite /RSmap RSmapE; apply is_tableau_RS. Qed.

  Lemma shape_RSmap_eq w : shape (RSmap w).1 = shape_rowseq (RSmap w).2.
  Proof.
    elim/last_ind: w => [//=| w l0]; rewrite /RSmap rev_rcons /=.
    have:= is_tableau_RSmap1 w; rewrite /RSmap.
    case: (RSmap_rev (rev w)) => [t rows] /= Htab.
    have:= shape_instabn l0 Htab.
    case: (instabn t l0) => [tr row].
    by rewrite /= => /eqP -> ->.
  Qed.

  Lemma is_yam_RSmap2 w : is_yam (RSmap w).2.
  Proof.
    elim/last_ind: w => [//=| w l0].
    have:= is_part_sht (is_tableau_RSmap1 (rcons w l0)).
    rewrite shape_RSmap_eq /RSmap rev_rcons /=.
    case Hbij : (RSmap_rev (rev w)) => [t rows] /=.
    by case Hins: (instabn t l0) => [tr row] /= -> ->.
  Qed.

  Definition is_RSpair pair :=
    let: (P, Q) := pair in [&& is_tableau P, is_yam Q & (shape P == shape_rowseq Q)].

  Theorem RSmap_spec w : is_RSpair (RSmap w).
  Proof.
    rewrite /is_RSpair.
    case H : (RSmap w) => [P Q]; apply /and3P; repeat split.
    - have:= is_tableau_RSmap1 w; by rewrite H.
    - have:= is_yam_RSmap2 w; by rewrite H.
    - have:= shape_RSmap_eq w; by rewrite H => ->.
  Qed.

  Fixpoint RSmapinv tab srow :=
    if srow is row :: srow'
    then let: (tr, lr) := invinstabn tab row in
         rcons (RSmapinv tr srow') lr
    else [::].
  Definition RSmapinv2 pair := RSmapinv (pair.1) (pair.2).

  Theorem RS_bij_1 w : RSmapinv2 (RSmap w) == w.
  Proof.
    rewrite /RSmapinv2.
    elim/last_ind: w => [//=| w wn]; rewrite /RSmap /RS rev_rcons /=.
    have:= is_tableau_RSmap1 w; rewrite /RSmap.
    case Hbij : (RSmap_rev (rev w)) => [t rows] /= Htab /eqP IHw.
    have:= invinstabnK wn Htab; rewrite -(instabnE t wn).
    case (instabn t wn) => [tr row] /= /eqP ->.
    by rewrite IHw.
  Qed.

  Lemma behead_incr_nth s nrow : behead (incr_nth s nrow.+1) = incr_nth (behead s) nrow.
  Proof. elim: s => //=; by case nrow. Qed.

  Lemma size_invins b s : size (invins b s) = (size s).
  Proof.
    rewrite /invins; elim: s => [//= | s0 s] /=.
    case H : (invbumprow b s) => [r a] /=.
    by case (leqP b (head b s)) => _ //= ->.
  Qed.

  Lemma yam_tail_non_nil l s : is_yam (l.+1 :: s) -> s != [::].
  Proof. case: s => [|//=] Hyam. have:= is_part_shyam Hyam. by rewrite part_head0F. Qed.

  Lemma shape_instabninv1 t row srow :
    is_yam (row :: srow) -> shape t == shape_rowseq (row :: srow) ->
    shape (invinstabn t row).1 == shape_rowseq srow.
  Proof.
    elim: row srow t => [|row IHrow] srow t Hyam.
    - case: t => [//= | r0 t]; first by case (shape_rowseq srow).
      rewrite shape_rowshape_cons => Hshape.
      have {Hyam} Hpart := is_part_shyam (is_yam_tl Hyam).
      case: r0 Hpart Hshape => [/= | l0 [| l1 r0'] ] Hpart Hshape /=.
      * by case: (shape_rowseq srow) Hshape.
      * case: (shape_rowseq srow) Hpart Hshape => //=.
        case => [|//=] l /andP []; rewrite leqn0.
        by move/part_head0F => ->.
      * move: Hshape; rewrite size_belast /=.
        by case: (shape_rowseq srow).
    - case: t => [//= | r0 t]; first by case (shape_rowseq srow).
      rewrite shape_rowshape_cons => /eqP Hshape.
      have Hsz0 : (size r0) = head 0 (shape_rowseq srow) by
        move: Hshape => /=; case (shape_rowseq srow) => [|s0 s] [] ->.
      have {Hshape} Hshape : shape t == shape_rowseq (row :: (shift_yam srow)).
        have:= eq_refl (behead (shape (r0 :: t))).
        by rewrite {2}Hshape behead_incr_nth -shape_shift.
      have Hnnilsrow := yam_tail_non_nil Hyam.
      have {Hyam} Hyam : (is_yam (row :: shift_yam srow)) by apply (is_yam_shift Hyam).
      have {IHrow Hshape Hyam} := IHrow _ _ Hyam Hshape => /=.
      case Hinv: (invinstabn t row) => [tin l] /=.
      have:= size_invins l r0; rewrite /invins.
      case Hbump: (invbumprow l r0) => [t0r l0r] /= -> {Hbump t0r l0r} /eqP -> {Hinv tin l}.
      rewrite shape_shift Hsz0 {Hsz0 r0}.
      case: srow Hnnilsrow => [//= | a b _].
      have: shape_rowseq (a :: b) != [::] by case: a => [/= | a /=]; case (shape_rowseq b).
      by case (shape_rowseq (a :: b)).
  Qed.

  Lemma head_tableau_non_nil h t : is_tableau (h :: t) -> h != [::].
  Proof. by move/and4P => [] ->. Qed.

  Lemma is_tableau_instabninv1 (s : seq (seq nat)) row :
    is_tableau s -> is_out_corner (shape s) row -> is_tableau (invinstabn s row).1.
  Proof.
    rewrite /is_out_corner.
    elim: s row => [/= |s0 s IHs] row; first by case row.
    case: row => [/= | row].
    - move=> {IHs} /and4P []; case: s0 => [//= | s0h s0t] _.
      case (altP (s0t =P [::])) => [-> /= _ _ | Hnnil]; first by case s.
      rewrite (negbTE Hnnil).
      case/lastP: s0t Hnnil => [//= | s0t s0l] _; rewrite -!rcons_cons => Hrow.
      rewrite belast_rcons.
      case Ht : s => [/= | s1 s']; first by have:= is_row_rconsK Hrow => /= ->.
      rewrite -Ht /= => Hdom -> Hshape.
      have:= is_row_rconsK Hrow => /= -> /=; rewrite andbT.
      apply (@dominate_rconsK _ _ s0l); last by [].
      move: Hshape; by rewrite Ht /= size_rcons ltnS.
    - case Hs : s => [//= | s1 s']; first by rewrite nth_nil.
      rewrite -Hs => /= /and4P [] Hnnil0 Hrows0 Hdom Htabs Hcorn.
      have:= Htabs; rewrite {1}Hs; move/head_tableau_non_nil => Hnnil1.
      move: {IHs} (IHs _ Htabs Hcorn).
      have Hnnils : (s != [::]) by rewrite Hs.
      move: {Hcorn} (instabninvK Htabs Hnnils Hcorn).
      case Hinv1 : (invinstabn s row) => [t l0] /= Hins1 Htabt.
      move: {Hnnils Htabs Hinv1} (invbump_geq_head Hnnils Htabs Hinv1).
      have:= instabnE t l0; rewrite (eqP Hins1) /= Hs => {Hins1} Hins1.
      move: Hdom; rewrite Hs /= => Hdom {s Hs}.
      move/(leq_trans (dominate_head Hnnil1 Hdom)) => Hbump0.
      have:= bumprowinvK Hnnil0 Hrows0 Hbump0.
      have:= is_row_invins l0 Hrows0; have:= size_invins l0 s0;
      rewrite /invins /invbumped.
      case Hinv0: (invbumprow l0 s0) => [t0 l] /= Hsize Hrowt0 Hins0.
      have Hnnilt0: (t0 != [::]) by move: Hnnil0 Hsize; case t0 => [//=|]; case s0.
      rewrite Hnnilt0 Hrowt0 Htabt andbT /=.
      case Ht : t Htabt => [//=| t1 t'] /tableau_is_row Hrowt1 /=.
      have:= @head_instab t1 t' l0 Hrowt1; rewrite -Ht -Hins1 /= => Hins {t t' Ht s' Hins1}.
      have Hbump : (bump t0 l).
        case: (boolP (bump t0 l)) => [//= | Hnbump].
        have:= nbump_bumprowE Hrowt0 Hnbump; by rewrite (eqP Hins0).
      apply (bump_dominateK Hrowt0 Hrowt1 Hbump).
      have:= bump_bumprowE Hrowt0 Hbump.
      rewrite /bumped (eqP Hins0) => [] [] <- <-; by rewrite -Hins.
  Qed.

  Theorem RS_bij_2 pair : is_RSpair pair -> RSmap (RSmapinv2 pair) == pair.
  Proof.
    rewrite /is_RSpair /RSmap /RSmapinv2; case: pair => [tab srow] /and3P [].
    elim: srow tab => [[] //= _ _ | row srow IHsrow] tab Htab Hyam Hshape /=.
    have:= is_out_corner_yam Hyam; rewrite -(eqP Hshape) => Hcorn.
    have Hnnil : (tab != [::]).
      move: Hshape; case tab => //= /eqP Habs.
      have:= eq_refl (size ([::]: seq nat)); rewrite {2}Habs /= size_incr_nth.
      move: (size (shape_rowseq srow)) => n.
      by case (ltnP row n) => //= /ltn_predK <-.
    have:= instabninvK Htab Hnnil Hcorn.
    have:= is_tableau_instabninv1 Htab Hcorn.
    have:= shape_instabninv1 Hyam Hshape.
    case Hinvins: (invinstabn tab row) => [tin l] /= Hshapetin Htabtin.
    rewrite rev_rcons /=.
    move: Hyam => /= /andP [] Hincr Hyam.
    by have:= IHsrow tin Htabtin Hyam Hshapetin => /= /eqP -> /eqP ->.
  Qed.

End Inverse.



Section Bijection.

  Notation Pair := (seq (seq nat) * seq nat : Type).

  Record rspair := RSpair { pqpair :> Pair; _ : is_RSpair pqpair }.

  Canonical rspair_subType := Eval hnf in [subType for pqpair].
  Definition rspair_eqMixin := Eval hnf in [eqMixin of rspair by <:].
  Canonical rspair_eqType := Eval hnf in EqType rspair rspair_eqMixin.
  Definition rspair_choiceMixin := [choiceMixin of rspair by <:].
  Canonical rspair_choiceType :=
    Eval hnf in ChoiceType rspair rspair_choiceMixin.

  Lemma pqpair_inj : injective pqpair. Proof. exact: val_inj. Qed.

  Definition RSbij w := RSpair (RSmap_spec w).
  Definition RSbijinv (ps : rspair) := RSmapinv2 ps.

  Lemma bijRS : bijective RSbij.
  Proof.
    split with (g := RSbijinv); rewrite /RSbij /RSbijinv.
    - move=> w /=; by rewrite (eqP (RS_bij_1 w)).
    - move=> [pq H]; apply pqpair_inj => /=; exact (eqP (RS_bij_2 H)).
  Qed.

End Bijection.



Section Tests.

  Goal (insrow [:: 1; 1; 2; 3; 5] 2) = [:: 1; 1; 2; 2; 5].
  Proof. compute; by apply erefl. Qed.

  Goal (insrow [:: 1; 1; 2; 3; 5] 2) = [:: 1; 1; 2; 2; 5].
  Proof. compute; by apply erefl. Qed.

  Goal (ins [:: 1; 1; 2; 3; 5] 2) = [:: 1; 1; 2; 2; 5].
  Proof. compute; by apply erefl. Qed.

  Goal (Sch [:: 2; 5; 1; 6; 4; 3]) = [:: 1; 3; 6].
  Proof. compute; by apply erefl. Qed.

  Goal (RS [:: 2; 5; 1; 6; 4; 3]) = [:: [:: 1; 3; 6]; [:: 2; 4]; [:: 5]].
  Proof. compute; by apply erefl. Qed.

  Goal (to_word (RS [:: 2; 5; 1; 6; 4; 3])) = [:: 5; 2; 4; 1; 3; 6].
  Proof. compute; by apply erefl. Qed.

  Goal is_tableau (RS [:: 2; 5; 1; 6; 4; 3]).
  Proof. compute; by apply erefl. Qed.

  Goal (invbumprow 3 [:: 1; 1; 2; 2; 5]) = ([:: 1; 1; 2; 3; 5], 2).
  Proof. compute; by apply erefl. Qed.

  Goal (invbumprow 3 [:: 1; 1; 2; 2; 3]) = ([:: 1; 1; 2; 3; 3], 2).
  Proof. compute; by apply erefl. Qed.

  Goal instabn [:: [:: 1; 3; 6]; [:: 2; 4];    [:: 5]] 3 =
              ([:: [:: 1; 3; 3]; [:: 2; 4; 6]; [:: 5]], 1).
  Proof. compute; by apply erefl. Qed.

  Goal invinstabn [:: [:: 1; 3; 3]; [:: 2; 4; 6]; [:: 5]] 1  =
                 ([:: [:: 1; 3; 6]; [:: 2; 4];    [:: 5]], 3).
  Proof. compute; by apply erefl. Qed.

  Goal is_part [:: 0] = false.
  Proof. compute; by apply erefl. Qed.

  Goal shape_rowseq [::] = [::].
  Proof. compute; by apply erefl. Qed.

  Goal shape_rowseq [:: 0; 1; 2; 0; 1; 3] = [:: 2; 2; 1; 1].
  Proof. compute; by apply erefl. Qed.

  Goal (RSmapinv2 (RSmap [:: 4; 1; 2; 1; 3; 2])) = [:: 4; 1; 2; 1; 3; 2].
  Proof. compute; by apply erefl. Qed.

End Tests.


