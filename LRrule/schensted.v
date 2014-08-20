Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import subseq.

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
      move: (IHr Hrow) => {IHr Hrow} IHr.
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
    - have HH: (i <= j <= i) by apply/andP.
      by rewrite (anti_leq HH).
    - have Hiltj: (i < j) by rewrite -subn_gt0 Hdiff.
      apply (leq_trans (n := (nth 0 r i.+1))).
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
    have:= (HH : (i < size r)) => {HH} HH; rewrite HH.
    case (ltngtP i.+1 (size r)) => Hisz.
    - by apply Hrow.
    - by rewrite ltnNge HH in Hisz.
    - move: Hrow HH Hl => _ _; by rewrite (last_nth 0) -Hisz.
  Qed.

  Lemma row_lt_by_pos r p q :
    is_row r -> p < size r -> q < size r -> nth 0 r p < nth 0 r q -> p < q.
  Proof.
    move/is_rowP => Hrow Hp Hq Hlt.
    have H : (q <= p -> nth 0 r q <= nth 0 r p) by move=> H; apply Hrow.
    by move: (contra H); rewrite -!ltnNge; apply.
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

  Implicit Type l : nat.
  Implicit Type r w s : seq nat.

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
    - move=> H; move: (IHr _ Hrow H); by case r.
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
    - set exP := (ex_intro _ _ _); case (ex_minnP exP) => pos1 {exP} Hl1 Hpos1.
      set exP := (ex_intro _ _ _); case (ex_minnP exP) => pos2 {exP} Hl2 Hpos2.
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

  Lemma nbump_insposE : ~~bump -> mininspred = pos.
  Proof.
    move=> Hbump; rewrite (nbump_mininspredE Hbump).
    move: Hbump; rewrite notbump.
    elim: Row HRow => [//=|l0 r IHr] Hrow /= Hlast.
    case: (ltnP l l0) => [Hll0|_].
    * exfalso => {IHr}.
      move: (leq_ltn_trans (leq_trans (head_leq_last_row Hrow) Hlast) Hll0).
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
    set exP := (ex_intro _ _ _); by case (ex_minnP exP).
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
    set exP := (ex_intro _ _ _); case (ex_minnP exP) => pos {exP} Hl Hpos.
    move: (Hpos _ (inspred_inspos Hbump)) => Hleq.
    case (ltnP pos (inspos Row l)) => H2.
    - exfalso; move: (inspredN_lt_inspos H2) Hl => H; by rewrite (negbTE H).
    - apply /eqP; by rewrite eqn_leq Hleq H2.
  Qed.

  Lemma insposE : mininspred = pos.
  Proof. case (boolP bump); first by apply bump_insposE. by apply nbump_insposE. Qed.

  Lemma inspos_leq_exP i : inspred i -> pos <= i.
  Proof.
    move=> HlPred.
    rewrite -insposE (bump_mininspredE (inspred_any_bump HlPred)).
    set exP := (ex_intro _ _ _); case (ex_minnP exP) => pos {exP} _ Hpos.
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
    set exP := (ex_intro _ _ _); case (ex_minnP exP) => pos {exP} Hl Hpos.
    have:= (Hpos _ (transf Hbump)); case: Row Hbump {Hl Hpos}; first by rewrite /= ltn0.
    move=> l0 r _ /=; by rewrite ltnS.
  Qed.

  Lemma nbump_inspos_eq_size : ~~bump -> pos = size Row.
  Proof. move=> Hnbump; by rewrite -insposE nbump_mininspredE. Qed.

  Lemma pos_leq_size : pos <= size Row.
  Proof.
    case (boolP bump) => Hlast.
    - move: (bump_inspos_lt_size Hlast) => H; by apply ltnW.
    - by rewrite nbump_inspos_eq_size.
  Qed.

  Lemma lt_inspos_nth i : i < size Row -> nth 0 Row i <= l -> i < pos.
  Proof.
    move: HRow; move=> /is_rowP Hrow Hi Hnthi; rewrite -insposE /mininspred /inspred.
    case (ltnP l (last 0 Row)) => [Hlt |//=].
    set exP := (ex_intro _ _ _); case (ex_minnP exP) => pos {exP} Hl Hpos.
    move: (leq_ltn_trans Hnthi Hl) (Hrow pos i) => {Hrow} {Hpos} H1 H2.
    have {H2} H2: (pos <= i -> nth 0 Row pos <= nth 0 Row i) by move=> H; by apply H2.
    move: (contra H2); rewrite -!ltnNge; by apply.
  Qed.

  Lemma insrow_head_lt : head 0 (insrow Row l) <= l.
  Proof. case: Row => [//=|l0 r] /=; by case (ltnP l l0). Qed.

  Lemma ins_head_lt : head 0 ins <= l.
  Proof. rewrite -insE insrowE; by apply insrow_head_lt. Qed.

  Lemma is_row_ins : is_row ins.
  Proof.
    move: HRow; rewrite -insE /insmin /mininspred => Hrow.
    case (ltnP l (last 0 Row)) => Hlast.
    - set exP := (ex_intro _ _ _); case (ex_minnP exP) => pos {exP}.
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
    - set exP := (ex_intro _ _ _); case (ex_minnP exP) => pos Hl _ _; by apply ltnW.
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
  move: (leq_trans H1 Hll0); by rewrite ltnn.
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
      * move: (pos_leq_size (is_row_Sch w) wn); rewrite -Hieq.
        case/IHw => {IHw} s => /and4P [] /eqP Hlast Hsubs /eqP Hsz Hrow.
        exists (rcons s wn); apply/and4P; repeat split.
        + by rewrite last_rcons nth_set_nth /= eq_refl.
        + by apply subseq_rcons_eq.
        + by rewrite size_rcons Hsz.
        + apply (is_row_rcons Hrow); rewrite Hlast.
          by apply nth_lt_inspos; rewrite -Hieq ltnSn.
    - have: (i < size (Sch w)); have HrowSch := (is_row_Sch w).
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
    rewrite Sch_rcons  /=; have:= (is_row_Sch w)=> HSch.
    case (altP (si =P wn)) => [-> {si} | Hsiwn Hsubs Hrow].

    (* The subseqence s ends by wn *)
    - rewrite -subseq_rcons_eq.
      case/lastP: s => [ _ _ {IHw} | s si Hsubs Hrow].
      (* s = wn *)
      * split; first by rewrite size_ins_non_0.
        rewrite -[size [::]]/(0) nth0; apply ins_head_lt; by apply is_row_Sch.
      (* s = [s] si wn *)
      move: (IHw _ _ Hsubs (is_row_rconsK Hrow)) => [] Hszlt Hlt {IHw}.
      move: (is_row_last Hrow); rewrite last_rcons => Hsiwn.

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
    - move: (subseq_rcons_neq Hsiwn Hsubs) => {Hsiwn Hsubs} Hsubs.
      move: (IHw _ _ Hsubs Hrow) => {IHw Hrow Hsubs} [] Hsize Hleq; split.
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
    move: (size_ins_non_0 (Sch w) wn); rewrite -Sch_rcons.
    move Hn : (size _) => [_ //=| n] _.
    move: (ltnSn n); rewrite -{2}Hn => H.
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

  Implicit Type l : nat.
  Implicit Type r w : seq nat.
  Implicit Type t : seq (seq nat).

  Definition bumped r l := nth 0 r (inspos r l).

  Lemma lt_bumped r l : bump r l -> l < bumped r l.
  Proof. by move/inspred_inspos. Qed.

  Fixpoint bumprow r l : (option nat) * (seq nat) :=
    if r is l0 :: r then
      if l < l0 then (Some l0, l :: r)
      else let: (lr, rr) := bumprow r l in (lr, l0 :: rr)
    else (None, [:: l]).

  Lemma ins_bumprowE r l : insrow r l = (bumprow r l).2.
  Proof.
    elim: r => [//= | t0 r IHr /=].
    case (ltnP l t0) => _ //=.
    by move: IHr; case (bumprow r l) => [lr tr] /= ->.
  Qed.

  Lemma bump_bumprowE r l :
    is_row r -> bump r l -> bumprow r l = (Some (bumped r l), ins r l).
  Proof.
    move=> Hrow; rewrite /bumped -(insE Hrow) (insrowE Hrow).
    elim: r Hrow => [//= | t0 r IHr] Hrow /= Hlast.
    case (ltnP l t0) => //=.
    move: Hlast => /bump_tail H/H {H} Hlast.
    by rewrite (IHr (is_row_consK Hrow) Hlast).
  Qed.

  Lemma nbump_bumprowE r l :
    is_row r -> ~~(bump r l) -> bumprow r l = (None, ins r l).
  Proof.
    rewrite notbump; move=> Hrow; rewrite -(insE Hrow) (insrowE Hrow).
    elim: r Hrow => [//= | t0 r IHr] Hrow Hlast /=.
    case (ltnP l t0) => //= Ht0.
    - exfalso.
      move: (leq_ltn_trans (leq_trans (head_leq_last_row Hrow) Hlast) Ht0).
      by rewrite ltnn.
    - have {Hlast} Hlast : (last 0 r <= l) by case: r {IHr Hrow} Hlast.
      by rewrite (IHr (is_row_consK Hrow) Hlast).
  Qed.

  Lemma head_ins_lt_bumped r l i : is_row r -> bump r l -> head i (ins r l) < bumped r l.
  Proof.
    move=> Hrow Hbump; move: (is_row_ins Hrow l) => /is_rowP Hrowins.
    rewrite -nth0 (nth_any i 0 (size_ins_non_0 _ _)).
    apply (@leq_ltn_trans (nth 0 (ins r l) (inspos r l))).
    + apply (Hrowins _ _ (leq0n _)).
      rewrite (bump_size_ins Hrow Hbump).
      by apply bump_inspos_lt_size.
    + rewrite /ins nth_set_nth /= eq_refl.
      by apply lt_bumped.
  Qed.

  Lemma bumprow_size r l:
    let: (lr, tr) := bumprow r l in
    (size r).+1 == (size tr) + if lr is Some _ then 1 else 0.
  Proof.
    elim: r => [//= | t0 r IHr /=].
    case (ltnP l t0) => _ /=; first by rewrite -addn1.
    by move: IHr; case (bumprow r l) => [lr tr] /= /eqP ->.
  Qed.

  Lemma bumprow_mult r l i :
    let: (lr, tr) := bumprow r l in
    count_mem i r + (l == i) == count_mem i tr + if lr is Some ll then (ll == i) else 0.
  Proof.
    elim: r => [| t0 r IHr] /=; first by rewrite !addn0.
    case (ltnP l t0) => _ /=.
    - by rewrite addnC -addnA eqn_add2l addnC eqn_add2l [t0 == i]eq_sym.
    - move: IHr; case (bumprow r l) => [tr lr] /= IHr.
      by rewrite -!addnA eqn_add2l.
  Qed.

End Bump.

Definition In := [fun n => nosimpl (iota 0 n)].

Section Dominate.

  Implicit Type l : nat.
  Implicit Type r u v : seq nat.

  Definition dominate u v :=
    ((size u) <= (size v)) && (all (fun i => nth 0 u i > nth 0 v i) (In (size u))).

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
    move: (Hlt _ Hi) => H; rewrite nth_rcons.
    case (ltnP i (size v)) => Hcomp //= {H}.
    move: {Hsz Hlt Hcomp} (leq_trans Hsz Hcomp) => Hs.
    move: (leq_ltn_trans Hs Hi); by rewrite ltnn.
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
    is_row r0 -> is_row r1 -> dominate r1 r0 ->
    bump r0 l -> dominate (ins r1 (bumped r0 l)) (ins r0 l).
  Proof.
    move=> Hrow0 Hrow1 Hdom. have:= Hdom => /dominateP [] Hsize Hlt Hbump.
    apply /dominateP; split.
    - rewrite (bump_size_ins Hrow0 Hbump) {1}/ins size_set_nth /maxn.
      case: (ltnP (inspos r1 (bumped r0 l)).+1 (size r1)) => [//=|_].
      apply (@leq_ltn_trans (inspos r0 l)); first by apply dominate_inspos.
      by apply bump_inspos_lt_size.
    - move=> i Hi; rewrite /ins; move: (dominate_inspos Hrow0 Hrow1 Hdom Hbump).
      set pos0 := inspos r0 _; set pos1 := inspos r1 _.
      move=> Hpos; rewrite !nth_set_nth /=.
      case (altP (i =P pos0)) => Hipos0;
         case (altP (i =P pos1)) => Hipos1.
      * by apply lt_bumped.
      * apply (leq_trans (lt_bumped Hbump)); move Hl0 : (bumped r0 l) => l0.
        rewrite -Hipos0 in Hpos => {Hrow0 Hlt Hdom Hsize Hbump Hipos0}.
        rewrite /pos1 in Hipos1 Hpos; rewrite Hl0 in Hipos1 Hi Hpos => {pos1 pos0 Hl0}.
        move: (is_row_ins Hrow1 l0) => /is_rowP Hrowins.
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
          move: (leq_ltn_trans Hsz Hi); by rewrite ltnn.
        + have:= Hnbump; move/nbump_ins_rconsE => Heq.
          rewrite (Heq Hrow1) size_rcons ltnS in Hi.
          have {Hi Hsz} Hi: (i == size r1) by rewrite eqn_leq Hi Hsz.
          rewrite /pos1 (nbump_inspos_eq_size Hrow1 Hnbump) in Hipos1.
          by rewrite Hi in Hipos1.
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
      * move: (tableau_is_row Htab) => Hrow1.
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

  Lemma is_row_invbumprow b s : is_row s -> is_row (invins b s).
  Proof.
    rewrite /invins.
    elim: s => [_ //=|l0 s IHs] /= /andP [] Hhead Hrow.
    case (leqP b (head b s)) => [/= -> //=| Hb /=].
    move: (IHs Hrow).
    move H : (invbumprow b s) => [r a] /= ->; rewrite andbT. 
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
    move H : (invbumprow b s) => [r a] /= Hb.
    apply (leq_trans Hhead).
    by rewrite (head_any _ 0 Hnnil).
  Qed.

  Lemma invbumprowK r a :
    is_row r -> bump r a ->
    (invbumprow (bumped r a) (ins r a)) == (r, a).
  Proof.
    rewrite /bump; move=> Hrow Hbump; move: (bump_bumprowE Hrow Hbump).
    elim: r Hrow Hbump => [_ /= |l0 r IHr /= /andP [] Hl0 Hrow Hbump]; first by rewrite ltn0.
    case: (ltnP a l0) => Hal0.
    - move=> [] <- <- /=; by rewrite Hl0.
    - have {Hbump} Hbump: (a < last 0 r) by
        case: r {IHr Hl0 Hrow} Hbump Hal0 => [/= /leq_trans H/H|//=]; by rewrite ltnn.
      move: (bump_bumprowE Hrow Hbump) => H.
      rewrite H => [] [] <- <- /=.
      move: (head_ins_lt_bumped (bumped r a) Hrow Hbump); rewrite ltnNge => /negbTE ->.
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
    move H : (invbumprow b s) => [r a] /= /eqP Hb; rewrite Hb.
    suff: (s0 <= a); first by rewrite leqNgt => /negbTE ->.
    apply (leq_trans Hhead); rewrite (head_any _ 0 Hnnil).
    by move: (head_leq_invbumped b Hnnil Hrows); rewrite /invbumped H /=.
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
    move: (IHt ll); by case: (instabn t ll) => [tres nres] /= ->.
  Qed.

End InverseBump.

Section Shape.

  Implicit Type s : seq nat.
  Implicit Type t : seq (seq nat).

  Definition shape t := map size t.
  Definition is_part sh :=
    (last 1 sh != 0) &&
    all (fun i => (nth 0 sh i) >= nth 0 sh i.+1) (In (size sh)).
  Definition is_out_corner sh i := nth 0 sh i > nth 0 sh i.+1.

  Lemma is_partP sh :
    reflect (last 1 sh != 0 /\ forall i, (nth 0 sh i) >= nth 0 sh i.+1) (is_part sh).
  Proof.
    rewrite /is_part; apply (iffP idP).
    - move=> /andP [] Hn0 /allP => Hall; split; first exact Hn0.
      move {Hn0} => i; case (ltnP i (size sh)) => Hi.
      * apply Hall; by rewrite mem_iota add0n.
      * rewrite (nth_default _ Hi) nth_default; first by [].
        by apply (leq_trans Hi).
    - move=> [] -> Hi; apply /allP => i _; by apply Hi.
  Qed.

  Lemma stupid i : (i == i.+1) = false.
  Proof. by elim: i => [//=| I IHi]; rewrite eqSS. Qed.

  Lemma del_cornerE sh i :
    last 1 sh != 0 -> is_part (incr_nth sh i) ->
    is_out_corner (incr_nth sh i) i = is_part sh.
  Proof.
    move=> Hn0 /is_partP [] _ Hpart1.
    apply (sameP (@idP (is_out_corner _ i))); apply (equivP (@idP (is_part _))).
    rewrite /is_out_corner; split.
    - move=> /is_partP => [] [] _ Hpart; move: (Hpart i) => {Hpart}.
      by rewrite !nth_incr_nth stupid eq_refl add0n add1n ltnS.
    - move=> Hcorn; apply /is_partP; split; first exact Hn0.
      move=> j; move: Hcorn (Hpart1 j).
      rewrite !nth_incr_nth stupid eq_refl add0n add1n ltnS => Hcorn.
      case (altP (i =P j)) => [<- //=|_].
      case (altP (i =P j.+1)) => [Hi |_].
      * rewrite add0n add1n; apply ltnW.
      * by rewrite !add0n.
  Qed.

  Lemma is_part_sht t : is_tableau t -> is_part (shape t).
  Proof.
    rewrite /shape => Ht; apply /is_partP.
    split.
    - elim: t Ht => [//= | t0 t IHt] /= /and4P [] Ht0 _ _ Htab.
      move: (map size _) (IHt Htab) => s.
      case: s => //= _; by case: t0 Ht0.
    - elim: t Ht => [_ i |t0 t IHt /= /and4P [] Hnnil Hrow /dominateP [] Hdom _ Htab i];
        first by rewrite nth_nil.
      case: i => [|i] /=; first by move: Hdom; case t.
      by apply IHt.
  Qed.

  Fixpoint shape_rowseq s :=
    if s is s0 :: s'
    then incr_nth (shape_rowseq s') s0
    else [::].

  (* Unused old definition *)
  Definition shape_rowseq_count :=
    [fun s => [seq (count_mem i) s | i <- iota 0 (foldr maxn 0 (map S s))]].

  Lemma shape_rowseq_countE : shape_rowseq_count =1 shape_rowseq.
  Proof.
    elim=>[//= | l0 s /= <-]; apply (@eq_from_nth _ 0).
    - rewrite size_incr_nth !size_map !size_iota /= {1}maxnC {1}/maxn.
      set m := (foldr _ _ _); case (ltngtP l0.+1 m) => [H||->].
      * by rewrite (leq_ltn_trans (leqnSn l0) H).
      * by rewrite ltnNge => /negbTE ->.
      * by rewrite leqnn.
    - move=> i; rewrite nth_incr_nth size_map => Hsz.
      rewrite (nth_map 0 _ _ Hsz); rewrite size_iota in Hsz; rewrite (nth_iota _ Hsz).
      rewrite add0n.
      case (ltnP i (foldr maxn 0 [seq i.+1 | i <- s])) => Hi.
      * rewrite (nth_map 0 _ _); last by rewrite size_iota.
        by rewrite (nth_iota _ Hi) /= add0n.
      * rewrite (nth_default 0) /=; last by rewrite size_map size_iota.
        congr ((l0 == i) + _).
        elim: s Hi {Hsz} => [//=| s0 s /=].
        set m := (foldr _ _ _) => IHs; rewrite /maxn.
        case (ltnP s0.+1 m) => Hs Hi.
        - by rewrite (IHs Hi) (ltn_eqF (leq_ltn_trans (leqnSn s0) (leq_trans Hs Hi))).
        - by rewrite (IHs (leq_trans Hs Hi)) (ltn_eqF Hi).
  Qed.

  Fixpoint is_yam s :=
    if s is s0 :: s'
    then is_part (shape_rowseq s) && is_yam s'
    else true.

  Lemma is_part_shyam s : is_yam s -> is_part (shape_rowseq s).
  Proof. by case: s => [//= | s0 s] /= /andP []. Qed.

  Lemma is_yam_tl l0 s : is_yam (l0 :: s) -> is_yam s.
  Proof. by move=> /= /andP []. Qed.

  Lemma is_out_corner_yam l0 s :
    is_yam (l0 :: s) -> is_out_corner (shape_rowseq (l0 :: s)) l0.
  Proof.
    move=> Hyam; move: (is_part_shyam (is_yam_tl Hyam)) => /is_partP [] _ Hpart.
    rewrite /is_out_corner !nth_incr_nth stupid eq_refl add0n add1n ltnS.
    by apply Hpart.
  Qed.

  Lemma shape_instabn t l :
    is_tableau t ->
    let: (tr, row) := instabn t l in shape tr == incr_nth (shape t) row.
  Proof.
    move H : (instabn t l) => [tr row] Htab.
    elim: t Htab l tr row H => [/= _| t0 t IHt /= /and4P [] _ Hrow _ Htab] l tr row /=;
        first by move=> [] <- <- => /=.
    case: (boolP (bump t0 l)) => [Hbump | Hnbump].
    - move: (bump_bumprowE Hrow Hbump) ->.
      case: row => [|row]; first by case (instabn t (bumped t0 l)).
      move Hins: (instabn t (bumped t0 l)) => [tres nres] [] <- <- /=.
      move: (IHt Htab (bumped t0 l) tres nres Hins) => /eqP ->.
      by rewrite (bump_size_ins Hrow Hbump).
    - move: (nbump_bumprowE Hrow Hnbump) => -> [] <- <- /=.
      by rewrite (nbump_size_ins Hrow Hnbump).
  Qed.

End Shape.

Section Inverse.

  Implicit Type a b l : nat.
  Implicit Type r s w : seq nat.
  Implicit Type t : seq (seq nat).

  Lemma is_out_corner_nrow t l : is_tableau t ->
      let: (res, nrow) := instabn t l in is_out_corner (shape res) nrow.
  Proof.
    rewrite /is_out_corner.
    elim: t l => [l _ //=|t0 t IHt l /= /and4P [] Hnnil Hrow /dominateP [] Hdom _ Htab].
    case: (boolP (bump t0 l)) => [Hbump | Hnbump].
    - rewrite (bump_bumprowE Hrow Hbump) /=.
      move: (IHt (bumped t0 l) Htab).
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
      move: (IHt (bumped t0 l) Htab).
      move Hres : (instabn t (bumped t0 l)) => [tres nres] /= /eqP ->.
      by rewrite (eqP (invbumprowK Hrow0 Hbump)).
    - rewrite (nbump_bumprowE Hrow0 Hnbump) (nbump_ins_rconsE Hrow0 Hnbump) /=.
      move Hres : (rcons t0 l) => [| ares tres]; first by move: Hres; case t0.
      case: (altP (tres =P [::])) => Htres.
      * exfalso; move: (eq_refl (size (rcons t0 l))) Hnnil.
        by rewrite {2}Hres Htres size_rcons /= => /nilP ->.
      * rewrite (_ : (belast ares tres) = t0);
          last by move: (eq_refl (belast 0 (rcons t0 l)));
                  rewrite {2}belast_rcons Hres /= => /eqP [].
        by rewrite (_ : (last ares tres) = l);
          last by move: (eq_refl (last 0 (rcons t0 l)));
                  rewrite {2}last_rcons Hres /= => /eqP.
  Qed.

  Lemma bumprow_rcons r l : is_row (rcons r l) -> bumprow r l = (None, rcons r l).
  Proof.
    move=> Hrow; move: (is_row_last Hrow) (is_row_rconsK Hrow); rewrite leqNgt => Hnbump Hr.
    by rewrite (nbump_bumprowE Hr Hnbump) (nbump_ins_rconsE Hr Hnbump).
  Qed.

  Lemma invbump_geq_head t tin l nrow :
    t != [::] -> is_tableau t -> invinstabn t nrow = (tin, l) -> l >= head 0 (head [::] t).
  Proof.
    case: t => [//= | r0 t] /= _ /and4P [] Hnnil0 Hrow0 _ _.
    case: nrow => [| nrow].
    - case: r0 Hnnil0 Hrow0 => [//= | l0 [| l1 tl0]] _ H /= [] _ <- //=.
      exact (head_leq_last_row H).
    - case: (invinstabn t nrow) => [tr lr].
      move: (head_leq_invbumped lr Hnnil0 Hrow0).
      rewrite /invbumped.
      by case: (invbumprow lr r0) => [t0r l0r] /= H [] _ <-.
  Qed.

  Lemma invbump_dom r0 t tin l nrow :
    t != [::] -> is_tableau t -> invinstabn t nrow = (tin, l) ->
    r0 != [::] -> dominate (head [::] t) r0 -> invbump l r0.
  Proof.
    rewrite /invbump => Htnnil Ht Hinv.
    move: (invbump_geq_head Htnnil Ht Hinv) => {Hinv}.
    case: t Htnnil Ht => [//= | r1 t] /= _ /and4P [] Hnnil1 _ _ _.
    case: r1 Hnnil1 => [//= | l1 r1 ] /= _ Hl1.
    case: r0 => [//= | l0 r0 ] /= _ /dominateP [ ] _ Hdom.
    move: (Hdom 0 (ltn0Sn _)) => {Hdom} /= Hl0.
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
        move : (head_leq_last_row Hrow0).
        rewrite belast_rcons last_rcons /= leqNgt => /negbTE ->.
        move: Hrow0 => /= /andP [] _ Hrow0.
        by rewrite (bumprow_rcons Hrow0).
    + have Hnnil : (t != [::]) by move: Hcorn; case t => //=; rewrite nth_nil.
      move: (IHt nrow Htab Hnnil Hcorn) => {IHt Hcorn} /=.
      move H: (invinstabn t nrow) => [tin l].
      have Hinvbump: (invbump l t0) by apply (@invbump_dom t0 t tin l nrow).
      move: (bumprowinvK Hnnil0 Hrow0 Hinvbump).
      rewrite /invins /invbumped.
      by case: (invbumprow l t0) => [t0r l0r] /= /eqP -> /eqP ->.
  Qed.

  Fixpoint RSbij_rev w : (seq (seq nat)) * (seq nat) :=
    if w is w0 :: wtl
    then let: (t, rows) := RSbij_rev wtl in
         let: (tr, nrow) := instabn t w0 in
         (tr, nrow :: rows)
    else ([::], [::]).
  Definition RSbij w := RSbij_rev (rev w).

  Lemma RSbijE w : (RSbij w).1 = RS w.
  Proof.
    elim/last_ind: w => [//= | w wn /=]; rewrite /RSbij /RS rev_rcons /= -instabnE.
    case: (RSbij_rev (rev w)) => [t rows] /= ->.
    by case: (instabn (RS_rev (rev w)) wn).
  Qed.

  Lemma is_tableau_RSbij1 w : is_tableau (RSbij w).1.
  Proof. rewrite /RSbij RSbijE; apply is_tableau_RS. Qed.

  Lemma shape_RSbij_eq w : shape (RSbij w).1 = shape_rowseq (RSbij w).2.
  Proof.
    elim/last_ind: w => [//=| w l0]; rewrite /RSbij rev_rcons /=.
    move: (is_tableau_RSbij1 w); rewrite /RSbij.
    case: (RSbij_rev (rev w)) => [t rows] /= Htab.
    move: (shape_instabn l0 Htab).
    case: (instabn t l0) => [tr row].
    by rewrite /= => /eqP -> ->.
  Qed.

  Lemma is_yam_RSbij2 w : is_yam (RSbij w).2.
  Proof.
    elim/last_ind: w => [//=| w l0].
    move: (is_part_sht (is_tableau_RSbij1 (rcons w l0))).
    rewrite shape_RSbij_eq /RSbij rev_rcons /=.
    move Hbij : (RSbij_rev (rev w)) => [t rows] /=.
    by move Hins: (instabn t l0) => [tr row] /= -> ->.
  Qed.

  Definition RSpair pair :=
    let: (P, Q) := pair in [&& is_tableau P, is_yam Q & (shape P == shape_rowseq Q)].

  Theorem RSbij_spec w : RSpair (RSbij w).
  Proof.
    rewrite /RSpair.
    move H : (RSbij w) => [P Q]; apply /and3P; repeat split.
    - move: (is_tableau_RSbij1 w); by rewrite H.
    - move: (is_yam_RSbij2 w); by rewrite H.
    - move: (shape_RSbij_eq w); by rewrite H => ->.
  Qed.

  Fixpoint RSbijinv tab srow :=
    if srow is row :: srow'
    then let: (tr, lr) := invinstabn tab row in
         rcons (RSbijinv tr srow') lr
    else [::].
  Definition RSbijinv2 pair := RSbijinv (pair.1) (pair.2).

  Theorem RS_bij_1 w : RSbijinv2 (RSbij w) == w.
  Proof.
    rewrite /RSbijinv2.
    elim/last_ind: w => [//=| w wn]; rewrite /RSbij /RS rev_rcons /=.
    move: (is_tableau_RSbij1 w); rewrite /RSbij.
    move Hbij : (RSbij_rev (rev w)) => [t rows] /= Htab /eqP IHw.
    move: (invinstabnK wn Htab); rewrite -(instabnE t wn).
    move Hins: (instabn t wn) => [tr row] /= /eqP ->.
    by rewrite IHw.
  Qed.

  Lemma is_tableau_instabninv1 t nrow :
    is_tableau t -> is_out_corner (shape t) nrow ->
    is_tableau (invinstabn t nrow).1.
  Proof.
    admit.
  Qed.

  Lemma shape_instabninv1 t row srow :
    is_tableau t -> shape t == shape_rowseq (row :: srow) ->
    shape (invinstabn t row).1 == shape_rowseq srow.
  Proof.
    admit.
  Qed.

  Theorem RS_bij_2 pair : RSpair pair -> RSbij (RSbijinv2 pair) == pair.
  Proof.
    rewrite /RSpair /RSbij /RSbijinv2; case: pair => [tab srow] /and3P [].
    elim: srow tab => [[] //= _ _ | row srow IHsrow] tab Htab Hyam Hshape /=.
    move: (is_out_corner_yam Hyam); rewrite -(eqP Hshape) => Hcorn.
    have Hnnil : (tab != [::]).
      move: Hshape; case tab => //= /eqP Habs.
      move: (eq_refl (size ([::]: seq nat))); rewrite {2}Habs /= size_incr_nth.
      move: (size (shape_rowseq srow)) => n.
      by case (ltnP row n) => //= /ltn_predK <-.
    move: (instabninvK Htab Hnnil Hcorn).
    move: (is_tableau_instabninv1 Htab Hcorn).
    move: (shape_instabninv1 Htab Hshape).
    move Hinvins: (invinstabn tab row) => [tin l] /= Hshapetin Htabtin.
    rewrite rev_rcons /=.
    move: Hyam => /= /andP [] Hincr Hyam.
    by move: (IHsrow tin Htabtin Hyam Hshapetin) => /= /eqP -> /eqP ->.
  Qed.

End Inverse.


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

  Goal (RSbijinv2 (RSbij [:: 4; 1; 2; 1; 3; 2])) = [:: 4; 1; 2; 1; 3; 2].
  Proof. compute; by apply erefl. Qed.

End Tests.


