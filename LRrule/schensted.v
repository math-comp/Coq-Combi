Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.

Require Import subseq.

Section Rows.

  Fixpoint is_row (t : seq nat) : bool :=
    match t with
      | [::] => true
      | [:: a] => true
      | a :: (b :: _) as tl => (a <= b) && is_row tl
    end.

  Lemma is_row1P (t : seq nat) :
    reflect
      (forall (i : nat), i.+1 < (size t) -> nth 0 t i <= nth 0 t i.+1)
      (is_row t).
  Proof.
    apply: (iffP idP).
    - elim: t => [_ i H //=| t0 [/= _ _ [|i] //=|t1 t /= IHt]] /andP [] Hleq Hrow.
      move: (IHt Hrow) => {IHt Hrow} IHt.
      case => [_ //=| i /= H]; by apply IHt.
    - elim: t => [_ //=|] t0 [//=| t1 t] IHt Ht /=.
      apply/andP; split; first by apply (Ht 0).
      apply IHt => i; by apply (Ht i.+1).
  Qed.

  Lemma non_decr_equiv (t : seq nat) :
    (forall (i j : nat), i <= j -> j < (size t) -> nth 0 t i <= nth 0 t j)
    <->
    (forall (i : nat), i.+1 < (size t) -> nth 0 t i <= nth 0 t i.+1).
  Proof.
    split => H; first by move=> i; apply (H i i.+1).
    move=> i j; move Hdiff : (j - i) => diff.
    elim: diff i j Hdiff => [i j /eqP Hdiff Hleq _ | diff IHdiff i j Hdiff Hleq Hsize].
    - have HH: (i <= j <= i) by apply/andP.
      by rewrite (anti_leq HH).
    - have Hiltj: (i < j) by rewrite -subn_gt0 Hdiff.
      apply (leq_trans (n := (nth 0 t i.+1))).
      apply H; by apply (leq_ltn_trans (n := j)).
      apply IHdiff => //=; first by rewrite subnS Hdiff.
  Qed.

  Lemma is_rowP (t : seq nat) :
    reflect
      (forall (i j : nat), i <= j -> j < (size t) -> nth 0 t i <= nth 0 t j)
      (is_row t).
  Proof. apply: (iffP idP); by rewrite non_decr_equiv => /is_row1P. Qed.

  Lemma is_row_rconsK l (t : seq nat) : is_row (rcons t l) -> is_row t.
  Proof.
    elim: t => [//=|t0 [//=|t1 t] IHt] /= /andP [] -> /= H; by apply (IHt H).
  Qed.

  Lemma is_row_last l (t : seq nat) : is_row (rcons t l) -> last 0 t <= l.
  Proof.
    elim: t => [//=|t0 t IHt /=]; move H: (rcons t l) => rtl.
    case: rtl H => [/eqP H _| a l0 H /andP []]; first by rewrite rcons_non_nil in H.
    case: t IHt H => [_ /= [] -> //= | t1 t IH Heq Ht0].
    move: Heq IH; rewrite !rcons_cons; move=> [] Ht1 Hl0.
    subst t1; subst l0. by apply.
  Qed.

  Lemma is_row_rcons l (t : seq nat) : is_row t -> last 0 t <= l -> is_row (rcons t l).
  Proof.
    move/is_row1P => Hrow Hl; apply/is_row1P => i; rewrite size_rcons !nth_rcons => HH.
    have := (HH : (i < size t)) => {HH} HH; rewrite HH.
    case: (ltngtP i.+1 (size t)) => Hisz.
    - by apply Hrow.
    - by rewrite ltnNge HH in Hisz.
    - move: Hrow HH Hl => _ _; by  rewrite (last_nth 0) -Hisz /=.
  Qed.

  Lemma row_lt_by_pos (t : seq nat) p q :
    is_row t -> p < size t -> q < size t -> nth 0 t p < nth 0 t q -> p < q.
  Proof.
    move/is_rowP => Hrow Hp Hq Hlt.
    have H : (q <= p -> nth 0 t q <= nth 0 t p) by move=> H; apply Hrow.
    by move: (contra H); rewrite -!ltnNge; apply.
  Qed.

End Rows.


Section Schensted.

  Implicit Type l : nat.
  Implicit Type t w : seq nat.

  Fixpoint insert (l : nat) (t : seq nat) : seq nat :=
    if t is l0 :: t then
      if l < l0 then l :: t
      else l0 :: (insert l t)
    else [:: l].

  Fixpoint insert_pos (l : nat) (t : seq nat) : nat :=
    if t is l0 :: t then
      if l < l0 then 0
      else (insert_pos l t).+1
    else 0.


  Lemma insert_head_lt l t : head 0 (insert l t) <= l.
  Proof. case: t => [//=|t0 t] /=; by case (ltnP l t0). Qed.

  Lemma insert_pos_size (l : nat) (t : seq nat) : insert_pos l t <= size t.
  Proof. elim: t => //= t0 t; by case (ltnP l t0). Qed.

  Lemma insert_lt_pos (l : nat) (t : seq nat) i :
    i < (insert_pos l t) -> nth 0 (insert l t) i = nth 0 t i.
  Proof.
    elim: t i => //= t0 t; case (ltnP l t0) => //= _ IH.
    case => [_  //=| i Hi] /=; by apply IH.
  Qed.

  Lemma insert_gt_pos (l : nat) (t : seq nat) i :
    (insert_pos l t) < i -> nth 0 (insert l t) i = nth 0 t i.
  Proof.
    elim: t i => [[|n _] //=| t0 t] /=; first by rewrite nth_nil.
    case (ltnP l t0) => Ht H [|i Hi] //=; by apply H.
  Qed.

  Lemma insert_eq_pos (l : nat) (t : seq nat) :
    nth 0 (insert l t) (insert_pos l t) = l.
  Proof.
    elim: t => [//=| t0 t /=]; by case (ltnP l t0).
  Qed.

  Lemma insert_set (l : nat) (t : seq nat) : insert l t = set_nth 0 t (insert_pos l t) l.
  Proof.
    elim: t => [//=|t0 t IHt] /=; case (ltnP l t0) => H //=.
    by rewrite IHt.
  Qed.

  Lemma insert_size_non_0 l t : 0 < size (insert l t).
  Proof.
    rewrite insert_set size_set_nth.
    apply (leq_trans (n := (insert_pos l t).+1)) => //=; by apply leq_maxl.
  Qed.

  Lemma insert_pos_lt (l : nat) (t : seq nat) i : i < insert_pos l t -> nth 0 t i <= l.
  Proof.
    elim: t i => [//=|t0 t IHt] /=; case (ltnP l t0) => //= Ht.
    case=> [//=|i] /=; by apply IHt.
  Qed.

  Lemma insert_pos_gt (l : nat) (t : seq nat) : l < nth l.+1 t (insert_pos l t).
  Proof.
    elim: t => [//=|t0 t IHt] /=; by case (ltnP l t0).
  Qed.

  Lemma insert_size_inf l t : (size t) <= size (insert l t).
  Proof.
    elim: t => //= t0 t; by case (ltnP l t0) => //=.
  Qed.

  Lemma insert_size_sup l t : size (insert l t) <= (size t).+1.
  Proof.
    elim: t => //= t0 t; by case (ltnP l t0) => //=.
  Qed.

  Lemma insert_leq l (t : seq nat) : forall (i : nat), nth 0 (insert l t) i <= nth l t i.
  Proof.
    elim: t => [| t0 t IHt] i /=.
    rewrite nth_nil; case i => [| n]; first by rewrite nth0 /=.
    by rewrite -nth_behead /= nth_nil.
    case (ltnP l t0) => Hcomp //=.
    - case i => /=; first by apply ltnW.
      elim t => [| s0 s IHs] n; first by rewrite !nth_nil.
      by case n => //=.
    - by case i => //=.
  Qed.

  Lemma insert_is_row l t : (is_row t) -> is_row (insert l t).
  Proof.
    elim: t => //= l0 [_ _| l1 t IHt /andP [] Hl0l1 Hrow] /=.
    case (ltnP l l0) => //= -> //=.
    case (ltnP l l0) => Hlt /=.
    - have Hll1: (l < l1) by apply (leq_trans Hlt Hl0l1).
      move: {Hl0l1 Hlt} Hrow => /= ->; by rewrite (ltnW Hll1).
    - have:= (IHt Hrow) => {IHt Hrow} /=.
      case (ltnP l l1) => /= _; first by rewrite Hlt.
      case: (insert l t); by rewrite Hl0l1.
  Qed.

  Fixpoint Sch_rev (w : seq nat) :=
    if w is l0 :: w' then insert l0 (Sch_rev w')
    else [::].
  Definition Sch w := Sch_rev (rev w).

  Lemma Sch_rcons l (w : seq nat) : Sch (rcons w l) = insert l (Sch w).
  Proof. by rewrite /Sch rev_rcons /=. Qed.

  Lemma Sch_size w : size (Sch w) <= size w.
  Proof.
    elim/last_ind: w => [| w l0 IHw] //=.
    rewrite Sch_rcons; move : (insert_size_sup l0 (Sch w)) => Hins.
    rewrite size_rcons; by apply (leq_trans Hins).
  Qed.

  Lemma Sch_is_row w : is_row (Sch w).
  Proof.
    elim/last_ind: w => [//= | w wn IHw]; rewrite Sch_rcons; by apply insert_is_row.
  Qed.

  Theorem Sch_exists (w : seq nat) i :
    i < size (Sch w) ->
    exists s : seq nat, let s' := rcons s (nth 0 (Sch w) i) in
      subseq s' w /\ is_row s' /\ size s == i.
  Proof.
    elim/last_ind: w i => [| w l0 IHw] //= i.
    rewrite Sch_rcons insert_set size_set_nth nth_set_nth /=.
    case: (altP (i =P (insert_pos l0 (Sch w)))).
    - case: i => [_ _|i]; first by exists [::]; split => //=; rewrite -cats1 suffix_subseq.
      move=> Hieq _; have := (insert_pos_size l0 (Sch w)); rewrite -Hieq => Hisz.
      case: (IHw i Hisz) => {Hisz IHw} s [] Hsubs [] Hrow Hsz.
      exists (rcons s (nth 0 (Sch w) i)); split; last split.
      * rewrite -!cats1; apply cat_subseq => //=; first by rewrite cats1.
        by rewrite (eq_refl l0).
      * have HH : (i < insert_pos l0 (Sch w)) by rewrite Hieq.
        have Hlt := (insert_pos_lt _ _ _ HH) => {HH}.
        apply is_row_rcons => //=; by rewrite last_rcons.
      * by rewrite size_rcons.
    - case: (altP (insert_pos l0 (Sch w) =P (size (Sch w)))) => [->|].
      rewrite /maxn (_ : _.+1 < _ = false) => [Hneq Hlt1|]; last by elim: (size _).
      have Hlt : (i < size (Sch w)) by rewrite ltn_neqAle Hneq.
      case: (IHw i Hlt) => {Hneq Hlt1 Hlt IHw} s /= [] Hsubs [] Hrow Hsz.
      by exists s; split => //=; apply (subseq_trans Hsubs); apply subseq_rcons.
    - rewrite /maxn => Hneq Hneqi Hmax.
      have Hlt : (i < size (Sch w)).
      case (ltngtP (insert_pos l0 (Sch w)).+1 (size (Sch w))) => //= HH.
      * by rewrite HH in Hmax.
      * suff Heq: insert_pos l0 (Sch w) == size (Sch w) by rewrite Heq in Hneq.
        apply/eqP/anti_leq/andP; split => //=; by apply insert_pos_size.
      * by rewrite HH if_same in Hmax.
      case (IHw i Hlt) => {Hneq Hneqi Hlt IHw Hmax} s /= [] Hsubs [] Hrow Hsz.
      by exists s; split => //=; apply (subseq_trans Hsubs); apply subseq_rcons.
  Qed.

  Theorem Sch_leq_last w s si:
    (is_row (rcons s si)) -> subseq (rcons s si) w ->
    (size s) < size (Sch w) /\ nth 0 (Sch w) (size s) <= si.
  Proof.
    elim/last_ind: w s si=> [| w wn IHw] s si; first by rewrite subseq0 rcons_non_nil.
    case: (altP (si =P wn)) => [-> {si} Hrow | Hsiwn Hrow Hsubs]; rewrite Sch_rcons.
    (* The subseqence s ends by wn *)
    - rewrite -subseq_rcons_eq; case/lastP: s Hrow => [/= _ _ | s si Hrow Hsubs].
      (* s = wn *)
      split; first by apply insert_size_non_0. by apply insert_head_lt.
      (* s = [s] si wn *)
    - move: (IHw _ _ (is_row_rconsK _ _ Hrow) Hsubs) => [] Hszlt Hlt {IHw}.
      move: (is_row_last _ _ Hrow); rewrite last_rcons => Hsiwn.
      rewrite insert_set size_set_nth nth_set_nth maxnC /maxn /=.
      have Hrowinswn : is_row (insert wn (Sch w))
        by apply insert_is_row; apply Sch_is_row; apply ltnW.

      case (ltnP (size (Sch w)) (insert_pos wn (Sch w)).+1).

      (* Insertion add a new [wn] box *)
      * rewrite size_rcons !ltnS => Hsize_ins.
        have Heqsize: (insert_pos wn (Sch w) = size (Sch w)) by
          apply anti_leq; apply/andP; split; first by apply insert_pos_size.
        rewrite Heqsize {Hsize_ins}; split; first by [].
        case: (altP ((size s).+1 =P size (Sch w))) => H; first by [].
        rewrite -[wn](insert_eq_pos _ (Sch w)).
        have Hlts: ((size s).+1 < size (Sch w)) by rewrite ltn_neqAle; apply/andP.
        rewrite -Heqsize in Hlts {H Hszlt}.
        rewrite -(insert_lt_pos wn _ _ Hlts).
        apply/is_rowP => //=; first by apply ltnW.
        by rewrite insert_set size_set_nth maxnC /maxn Heqsize ltnSn ltnSn.

      (* Wn bump a letter *)
      * case: (altP (size (rcons s si) =P insert_pos wn (Sch w))) => [|Hneq Hlts];
                                                                    first by move ->.
        rewrite -[wn](insert_eq_pos _ (Sch w)).
        move: (insert_pos_gt wn (Sch w)); rewrite (nth_any _ (Sch w) _ 0); last by [].
        move: (leq_trans Hlt Hsiwn) => Hltwn Hwnpos.
        move: (leq_ltn_trans Hltwn Hwnpos) => {Hltwn Hwnpos} Hltnth.
        move: (row_lt_by_pos _ _ _ (Sch_is_row w) Hszlt Hlts Hltnth) => {Hltnth} Hltswn.
        rewrite size_rcons; rewrite size_rcons in Hneq.
        have Hltsi: (size s).+1 < insert_pos wn (Sch w) by rewrite ltn_neqAle Hneq Hltswn.
        split; first by apply (ltn_trans Hltsi).
        rewrite -(insert_lt_pos _ _ _ Hltsi).
        apply/is_rowP => //=; apply (leq_trans Hlts); by apply insert_size_inf.

    (* The subsequence doesn't end by wn *)
    - move: (subseq_rcons_neq _ _ _ _ _ Hsiwn Hsubs) => {Hsiwn Hsubs} Hsubs.
      move: (IHw _ _ Hrow Hsubs) => {IHw Hrow Hsubs} [] Hsize Hleq; split.
      by apply (leq_trans Hsize); apply (insert_size_inf).
      have:= (insert_leq wn (Sch w) (size s)) => H1.
      apply (leq_trans H1); by rewrite (nth_any _ _ _ 0).
  Qed.

  Definition rowsubseq s w := is_row s /\ subseq s w.
  Definition rowsubseq_n s w n := is_row s /\ subseq s w /\ size s == n.

  Theorem size_ndec_Sch w s : rowsubseq s w -> (size s) <= size (Sch w).
  Proof.
    rewrite /rowsubseq; move=> [].
    case/lastP: s => [//=| s si] =>  Hrow Hsubs.
    move: (Sch_leq_last _ _ _ Hrow Hsubs) => [] H _.
    by rewrite size_rcons.
  Qed.

  Theorem exist_size_Sch w : exists s : seq nat, rowsubseq_n s w (size (Sch w)).
  Proof.
    rewrite /rowsubseq; case/lastP: w => [| w wn]; first by exists [::].
    move: (insert_size_non_0 wn (Sch w)); rewrite -Sch_rcons.
    move H : (size _) => ssch; case: ssch H => [_ //=| n] Hn _.
    move: (ltnSn n); rewrite -{2}Hn => H.
    elim (Sch_exists _ _ H) => s [] Hsubs [] Hrow Hsize.
    set ss := (rcons _ _) in Hrow; exists ss; split; first by []; split => //=.
    by rewrite /ss size_rcons.
  Qed.

  Fixpoint insert_bump (l : nat) (t : seq nat) : (seq nat)*(option nat) :=
    if t is l0 :: t then
      if l < l0 then (l :: t, Some l0)
      else let: (tr, lr) := insert_bump l t in (l0::tr, lr)
    else ([:: l], None).

End Schensted.

Section SubSeq.

  Variable w : seq nat.

  Definition PRowSeq :=
    [fun i : nat => [exists s : SubSeq nat_countType w, (is_row s) && (size s == i)]].

  Lemma exrow0 : PRowSeq 0.
  Proof. apply /existsP. by exists (sub_nil _ w). Qed.

  Lemma max_row_len : forall i : nat, PRowSeq i -> i <= size w.
  Proof. rewrite /PRowSeq=> i /= /existsP [[s Hs]] /andP [] _ /eqP <-; by apply size_le. Qed.

  Definition max_rowsubseq_size := ex_maxn (P := PRowSeq) (ex_intro _ 0 exrow0) max_row_len.

  Theorem size_max_rowsubseq : max_rowsubseq_size == size (Sch w).
  Proof.
    rewrite /max_rowsubseq_size.
    case (ex_maxnP (ex_intro _ 0 exrow0) max_row_len) => i.
    rewrite /PRowSeq /= => /existsP [] [s Hs] /andP [] /= Hrow Hsz Hmax.
    rewrite -(eqP Hsz).
    apply/eqP/anti_leq/andP; split.
    - apply size_ndec_Sch; rewrite /rowsubseq; split; first exact Hrow.
      by apply Hs.
    - rewrite (eqP Hsz); case (exist_size_Sch w) => smax {Hrow Hsz}.
      rewrite /rowsubseq /rowsubseq_n => [] [] Hrow [] Hsubs /eqP <-.
      apply Hmax; apply /existsP.
      exists (exist (is_subseq _ w) smax Hsubs).
      by rewrite Hrow /=.
  Qed.

End SubSeq.

