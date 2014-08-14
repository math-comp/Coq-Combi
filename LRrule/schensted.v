Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import subseq.

Set Implicit Arguments.
Unset Strict Implicit.

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
    apply/(iffP idP).
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
  Proof. apply/(iffP idP); by rewrite non_decr_equiv => /is_row1P. Qed.

  Lemma is_row_rconsK l (t : seq nat) : is_row (rcons t l) -> is_row t.
  Proof.
    elim: t => [//=|t0 [//=|t1 t] IHt] /= /andP [] -> /= H; by apply (IHt H).
  Qed.

  Lemma is_row_last l (t : seq nat) : is_row (rcons t l) -> last 0 t <= l.
  Proof.
    elim: t => [//=|t0 t IHt /=]; move H: (rcons t l) => rtl.
    case: rtl H => [/eqP H _| a l0 H /andP []]; first by rewrite rcons_nilF in H.
    case: t IHt H => [_ /= [] -> //= | t1 t IH Heq Ht0].
    move: Heq IH; rewrite !rcons_cons; move=> [] Ht1 Hl0.
    subst t1; subst l0. by apply.
  Qed.

  Lemma is_row_rcons l (t : seq nat) : is_row t -> last 0 t <= l -> is_row (rcons t l).
  Proof.
    move/is_row1P => Hrow Hl; apply/is_row1P => i; rewrite size_rcons !nth_rcons => HH.
    have := (HH : (i < size t)) => {HH} HH; rewrite HH.
    case (ltngtP i.+1 (size t)) => Hisz.
    - by apply Hrow.
    - by rewrite ltnNge HH in Hisz.
    - move: Hrow HH Hl => _ _; by rewrite (last_nth 0) -Hisz.
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
  Implicit Type r w : seq nat.

  Fixpoint insrow r l : seq nat :=
    if r is l0 :: r then
      if l < l0 then l :: r
      else l0 :: (insrow r l)
    else [:: l].

  Fixpoint insrow_pos r l : nat :=
    if r is l0 :: r then
      if l < l0 then 0
      else (insrow_pos r l).+1
    else 0.


  Lemma insrow_head_lt r l : head 0 (insrow r l) <= l.
  Proof. case: r => [//=|t0 t] /=; by case (ltnP l t0). Qed.

  Lemma insrow_pos_size r l : insrow_pos r l <= size r.
  Proof. elim: r => //= t0 t; by case (ltnP l t0). Qed.

  Lemma insrow_lt_pos r l i :
    i < (insrow_pos r l) -> nth 0 (insrow r l) i = nth 0 r i.
  Proof.
    elim: r i => //= t0 t; case (ltnP l t0) => //= _ IH.
    case => [_  //=| i Hi] /=; by apply IH.
  Qed.

  Lemma insrow_gt_pos r l i :
    (insrow_pos r l) < i -> nth 0 (insrow r l) i = nth 0 r i.
  Proof.
    elim: r i => [[|n _] //=| t0 t] /=; first by rewrite nth_nil.
    case (ltnP l t0) => Ht H [|i Hi] //=; by apply H.
  Qed.

  Lemma insrow_eq_pos r l :
    nth 0 (insrow r l) (insrow_pos r l) = l.
  Proof.
    elim: r => [//=| t0 r /=]; by case (ltnP l t0).
  Qed.

  Lemma insrow_set r l : insrow r l = set_nth 0 r (insrow_pos r l) l.
  Proof.
    elim: r => [//=|t0 r IHt] /=; case (ltnP l t0) => H //=.
    by rewrite IHt.
  Qed.

  Lemma insrow_non_nil r l : insrow r l != [::].
  Proof. case: r => [//=|t0 t] /=; by case (ltnP l t0) => H. Qed.

  Lemma insrow_size_non_0 r l : 0 < size (insrow r l).
  Proof.
    rewrite insrow_set size_set_nth.
    apply (leq_trans (n := (insrow_pos r l).+1)) => //=; by apply leq_maxl.
  Qed.

  Lemma insrow_pos_lt r l i : i < insrow_pos r l -> nth 0 r i <= l.
  Proof.
    elim: r i => [//=|t0 r IHt] /=; case (ltnP l t0) => //= Ht.
    case=> [//=|i] /=; by apply IHt.
  Qed.

  Lemma insrow_pos_gt r l : l < nth l.+1 r (insrow_pos r l).
  Proof. elim: r => //= t0 t; by case (ltnP l t0). Qed.

  Lemma insrow_size_inf r l : (size r) <= size (insrow r l).
  Proof. elim: r => //= t0 t; by case (ltnP l t0). Qed.

  Lemma insrow_size_sup r l : size (insrow r l) <= (size r).+1.
  Proof. elim: r => //= t0 t; by case (ltnP l t0). Qed.

  Lemma insrow_leq r l : forall (i : nat), nth 0 (insrow r l) i <= nth l r i.
  Proof.
    elim: r => [| t0 r IHt] i /=.
    rewrite nth_nil; case i => [| n]; first by rewrite nth0 /=.
    by rewrite -nth_behead /= nth_nil.
    case (ltnP l t0) => Hcomp; last by case i.
    case i => /=; first by apply ltnW.
    elim r => [| s0 s IHs] n; first by rewrite !nth_nil.
    by case n.
  Qed.

  Lemma insrow_is_row r l : (is_row r) -> is_row (insrow r l).
  Proof.
    elim: r => //= l0 [_ _| l1 r IHt /andP [] Hl0l1 Hrow] /=;
       first by case (ltnP l l0) => //= ->.
    case (ltnP l l0) => Hlt /=.
    - have Hll1: (l < l1) by apply (leq_trans Hlt Hl0l1).
      move: {Hl0l1 Hlt} Hrow => /= ->; by rewrite (ltnW Hll1).
    - have:= (IHt Hrow) => {IHt Hrow} /=.
      case (ltnP l l1) => /= _; first by rewrite Hlt.
      case (insrow r l); by rewrite Hl0l1.
  Qed.

  Fixpoint Sch_rev (w : seq nat) :=
    if w is l0 :: w' then insrow (Sch_rev w') l0
    else [::].
  Definition Sch w := Sch_rev (rev w).

  Lemma Sch_rcons l (w : seq nat) : Sch (rcons w l) = insrow (Sch w) l.
  Proof. by rewrite /Sch rev_rcons. Qed.

  Lemma Sch_size w : size (Sch w) <= size w.
  Proof.
    elim/last_ind: w => [//= | w wn IHw]; rewrite Sch_rcons size_rcons.
    by apply (leq_trans (insrow_size_sup (Sch w) wn)).
  Qed.

  Lemma Sch_is_row w : is_row (Sch w).
  Proof. elim/last_ind: w => [//= | w wn IHw]; by rewrite Sch_rcons insrow_is_row. Qed.

  Theorem Sch_exists (w : seq nat) i :
    i < size (Sch w) ->
    exists s : seq nat, let s' := rcons s (nth 0 (Sch w) i) in
      subseq s' w /\ is_row s' /\ size s == i.
  Proof.
    elim/last_ind: w i => [//=| w l0 IHw] i.
    rewrite Sch_rcons insrow_set size_set_nth nth_set_nth /=.
    case (altP (i =P (insrow_pos (Sch w) l0))).
    - case: i => [_ _|i]; first by exists [::]; split => //=; rewrite -cats1 suffix_subseq.
      move=> Hieq _; have := (insrow_pos_size (Sch w) l0); rewrite -Hieq => Hisz.
      case (IHw i Hisz) => {Hisz IHw} s [] Hsubs [] Hrow Hsz.
      exists (rcons s (nth 0 (Sch w) i)); split; last split.
      * rewrite -!cats1; apply cat_subseq => //=; first by rewrite cats1.
        by rewrite (eq_refl l0).
      * have HH : (i < insrow_pos (Sch w) l0) by rewrite Hieq.
        have Hlt := (insrow_pos_lt HH) => {HH}.
        apply is_row_rcons => //=; by rewrite last_rcons.
      * by rewrite size_rcons.
    - case (altP (insrow_pos (Sch w) l0 =P (size (Sch w)))) => [->|].
      - rewrite /maxn (_ : _.+1 < _ = false) => [Hneq Hlt1|]; last by elim: (size _).
        have Hlt : (i < size (Sch w)) by rewrite ltn_neqAle Hneq.
        case (IHw i Hlt) => {Hneq Hlt1 Hlt IHw} s /= [] Hsubs [] Hrow Hsz.
        by exists s; split => //=; apply (subseq_trans Hsubs); apply subseq_rcons.
      - rewrite /maxn => Hneq Hneqi Hmax.
        have Hlt : (i < size (Sch w)).
        case (ltngtP (insrow_pos (Sch w) l0).+1 (size (Sch w))) => //= HH.
        * by rewrite HH in Hmax.
        * suff Heq: insrow_pos (Sch w) l0 == size (Sch w) by rewrite Heq in Hneq.
          apply/eqP/anti_leq/andP; split => //=; by apply insrow_pos_size.
        * by rewrite HH if_same in Hmax.
        case (IHw i Hlt) => {Hneq Hneqi Hlt IHw Hmax} s /= [] Hsubs [] Hrow Hsz.
        by exists s; split => //=; apply (subseq_trans Hsubs); apply subseq_rcons.
  Qed.

  Theorem Sch_leq_last w s si:
    (is_row (rcons s si)) -> subseq (rcons s si) w ->
    (size s) < size (Sch w) /\ nth 0 (Sch w) (size s) <= si.
  Proof.
    elim/last_ind: w s si=> [| w wn IHw] s si; first by rewrite subseq0 rcons_nilF.
    rewrite Sch_rcons.
    case (altP (si =P wn)) => [-> {si} Hrow | Hsiwn Hrow Hsubs].
    (* The subseqence s ends by wn *)
    - rewrite -subseq_rcons_eq.
      case/lastP: s Hrow => [/= _ _ | s si Hrow Hsubs];
      (* s = wn *)
         first by rewrite insrow_size_non_0 insrow_head_lt.
      (* s = [s] si wn *)
      move: (IHw _ _ (is_row_rconsK Hrow) Hsubs) => [] Hszlt Hlt {IHw}.
      move: (is_row_last Hrow); rewrite last_rcons => Hsiwn.
      rewrite insrow_set size_set_nth nth_set_nth maxnC /maxn /=.
      have Hrowinswn : is_row (insrow (Sch w) wn)
        by apply insrow_is_row; apply Sch_is_row; apply ltnW.

      case (ltnP (size (Sch w)) (insrow_pos (Sch w) wn).+1).

      (* Insrowion add a new [wn] box *)
      * rewrite size_rcons !ltnS => Hsize_ins.
        have Heqsize: (insrow_pos (Sch w) wn = size (Sch w)) by
          apply anti_leq; apply/andP; split; first by apply insrow_pos_size.
        rewrite Heqsize {Hsize_ins}; split; first exact Hszlt.
        case (altP ((size s).+1 =P size (Sch w))) => [//=|] H.
        rewrite -[wn](insrow_eq_pos (Sch w) _).
        have Hlts: ((size s).+1 < size (Sch w)) by rewrite ltn_neqAle; apply/andP.
        rewrite -Heqsize in Hlts {H Hszlt}.
        rewrite -(insrow_lt_pos Hlts).
        apply/is_rowP => //=; first by apply ltnW.
        by rewrite insrow_set size_set_nth maxnC /maxn Heqsize ltnSn ltnSn.

      (* Wn bump a letter *)
      * case (altP (size (rcons s si) =P insrow_pos (Sch w) wn)) => [-> //= |Hneq Hlts].
        rewrite -[wn](insrow_eq_pos (Sch w) _).
        move: (insrow_pos_gt (Sch w) wn); rewrite (@nth_any _ (Sch w) _ 0); last by [].
        move: (leq_trans Hlt Hsiwn) => Hltwn Hwnpos.
        move: (leq_ltn_trans Hltwn Hwnpos) => {Hltwn Hwnpos} Hltnth.
        move: (row_lt_by_pos (Sch_is_row w) Hszlt Hlts Hltnth) => {Hltnth} Hltswn.
        rewrite size_rcons; rewrite size_rcons in Hneq.
        have Hltsi: (size s).+1 < insrow_pos (Sch w) wn by rewrite ltn_neqAle Hneq Hltswn.
        split; first by apply (ltn_trans Hltsi).
        rewrite -(insrow_lt_pos Hltsi).
        apply/is_rowP => //=; apply (leq_trans Hlts); by apply insrow_size_inf.

    (* The subsequence doesn't end by wn *)
    - move: (subseq_rcons_neq Hsiwn Hsubs) => {Hsiwn Hsubs} Hsubs.
      move: (IHw _ _ Hrow Hsubs) => {IHw Hrow Hsubs} [] Hsize Hleq; split.
      by apply (leq_trans Hsize); apply (insrow_size_inf).
      have:= (insrow_leq (Sch w) wn (size s)) => H1.
      apply (leq_trans H1); by rewrite (@nth_any _ _ _ 0).
  Qed.

  Definition rowsubseq s w := is_row s /\ subseq s w.
  Definition rowsubseq_n s w n := is_row s /\ subseq s w /\ size s == n.

  Theorem size_ndec_Sch w s : rowsubseq s w -> (size s) <= size (Sch w).
  Proof.
    rewrite /rowsubseq; move=> [].
    case/lastP: s => [//=| s si] =>  Hrow Hsubs.
    move: (Sch_leq_last Hrow Hsubs) => [] H _.
    by rewrite size_rcons.
  Qed.

  Theorem exist_size_Sch w : exists s : seq nat, rowsubseq_n s w (size (Sch w)).
  Proof.
    rewrite /rowsubseq; case/lastP: w => [| w wn]; first by exists [::].
    move: (insrow_size_non_0 (Sch w) wn); rewrite -Sch_rcons.
    move H : (size _) => ssch; case: ssch H => [_ //=| n] Hn _.
    move: (ltnSn n); rewrite -{2}Hn => H.
    elim (Sch_exists H) => s [] Hsubs [] Hrow Hsize.
    set ss := (rcons _ _) in Hrow; exists ss; split; first by []; split => //=.
    by rewrite /ss size_rcons.
  Qed.

End Schensted.

Section SubSeq.

  Variable w : seq nat.

  Definition PRowSeq :=
    [fun i : nat => [exists s : SubSeq w, (is_row s) && (size s == i)]].

  Lemma exrow0 : PRowSeq 0.
  Proof. apply /existsP. by exists (sub_nil w). Qed.

  Lemma max_row_len : forall i : nat, PRowSeq i -> i <= size w.
  Proof. rewrite /PRowSeq=> i /= /existsP [[s Hs]] /andP [] _ /eqP <-; by apply size_le. Qed.

  Definition max_rowsubseq_size := ex_maxn (ex_intro _ 0 exrow0) max_row_len.

  Theorem size_max_rowsubseq : max_rowsubseq_size == size (Sch w).
  Proof.
    rewrite /max_rowsubseq_size.
    case (ex_maxnP (ex_intro _ 0 exrow0) max_row_len) => i.
    rewrite /PRowSeq /= => /existsP [] [s Hs] /andP [] /= Hrow Hsz Hmax.
    rewrite -(eqP Hsz).
    apply/eqP/anti_leq/andP; split.
    - apply size_ndec_Sch; rewrite /rowsubseq; split; first exact Hrow.
      rewrite subseqs_all; by apply Hs.
    - rewrite (eqP Hsz); case (exist_size_Sch w) => smax {Hrow Hsz}.
      rewrite /rowsubseq /rowsubseq_n => [] [] Hrow [] /subseqs_all Hsubs /eqP <-.
      apply Hmax; apply /existsP; exists (SeqSub Hsubs).
      by rewrite Hrow /=.
  Qed.

End SubSeq.

Section Bump.

  Implicit Type l : nat.
  Implicit Type r w : seq nat.
  Implicit Type t : seq (seq nat).

  Fixpoint bumprow r l : (option nat) * (seq nat):=
    if r is l0 :: r then
      if l < l0 then (Some l0, l :: r)
      else let: (lr, rr) := bumprow r l in (lr, l0 :: rr)
    else (None, [:: l]).

  Lemma insbumprowE r l: (bumprow r l).2 = insrow r l.
  Proof.
    elim: r => [//= | t0 r IHt /=].
    case (ltnP l t0) => _ //=.
    by move: IHt; case (bumprow r l) => [lr tr] /= ->.
  Qed.

  Lemma bumprow_append r l tr:
    bumprow r l = (None, tr) -> tr = rcons r l.
  Proof.
    elim: r tr => [[/eqP | a l0 [] <- <-] //=| t0 r IHt ] //=.
    case (ltnP l t0) => _ //=.
    move: IHt; case (bumprow r l) => [[ll //=|]] l0 H tr [] <-.
    by rewrite (H l0 _).
  Qed.

  Lemma insrow_append_pos r l tr:
    bumprow r l = (None, tr) -> (insrow_pos r l) = size r.
  Proof.
    elim: r tr => [//= | t0 r IHt /=].
    case (ltnP l t0) => _ //=.
    move: IHt; case (bumprow r l) => [[ll //=|] l0 IHt _ _ ].
    by rewrite (IHt l0).
  Qed.

  Lemma bumprow_lt r l ll tr:
    bumprow r l = (Some ll, tr) -> l < ll.
  Proof.
    elim: r ll tr => [//= | t0 r IHt /=].
    case (ltnP l t0) => Hcomp /=; first by move => ll tr [] <- _.
    move: IHt; case (bumprow r l) => [[lc //=|_ ll tr //=] trr] /= IHt ll tr [] Hlc Htr.
    subst lc; subst tr; by apply (IHt _ trr).
  Qed.

  Lemma bumprow_bump r l ll tr:
    bumprow r l = (Some ll, tr) -> ll = (nth 0 r (insrow_pos r l)).
  Proof.
    elim: r ll tr => [//= | t0 r IHt /=].
    case (ltnP l t0) => _ /=; first by move => ll tr [] -> _.
    move: IHt; case (bumprow r l) => [[lc //=|_ ll tr //=] trr] /= IHt ll tr [] Hlc Htr.
    subst lc; subst tr; by apply (IHt _ trr).
  Qed.

  Lemma bumprow_pos r l ll tr:
    bumprow r l = (Some ll, tr) -> (insrow_pos r l) < size r.
  Proof.
    elim: r ll tr => [//= | t0 r IHt /=].
    case (ltnP l t0) => _ /=; first by move => ll tr [] _ _.
    move: IHt; case (bumprow r l) => [[lc //=|_ _ _ //=] tr] /= IHt _ _ _.
    by apply (IHt lc tr).
  Qed.

  Lemma bumprow_size r l:
    let: (lr, tr) := bumprow r l in
    (size r).+1 == (size tr) + if lr is Some _ then 1 else 0.
  Proof.
    elim: r => [//= | t0 r IHt /=].
    case (ltnP l t0) => _ /=; first by rewrite -addn1.
    by move: IHt; case (bumprow r l) => [lr tr] /= /eqP ->.
  Qed.

  Lemma bumprow_mult r l i :
    let: (lr, tr) := bumprow r l in
    count_mem i r + (l == i) == count_mem i tr + if lr is Some ll then (ll == i) else 0.
  Proof.
    elim: r => [| t0 r IHt] /=; first by rewrite !addn0.
    case (ltnP l t0) => _ /=.
    - by rewrite addnC -addnA eqn_add2l addnC eqn_add2l [t0 == i]eq_sym.
    - move: IHt; case (bumprow r l) => [tr lr] /= IHt.
      by rewrite -!addnA eqn_add2l.
  Qed.

  Fixpoint instab t l : seq (seq nat) :=
    if t is t0 :: t then
      let: (lr, tr) := bumprow t0 l in
      if lr is Some ll then tr :: (instab t ll) else tr :: t
    else [:: [:: l]].

  Lemma bump0 (t0 : seq nat) t l b0 b : instab (t0 :: t) l = b0 :: b -> b0 = insrow t0 l.
  Proof.
    rewrite -insbumprowE /=.
    by case (bumprow t0 l) => [[l'|]] b' /= [] -> _.
  Qed.

End Bump.

Section Tableaux.

  Implicit Type l : nat.
  Implicit Type r u v w : seq nat.
  Implicit Type t : seq (seq nat).

  Definition dominate u v :=
    ((size u) <= (size v)) &&
    [forall i : ordinal (size u), nth 0 u i > nth 0 v i].

  Lemma dominateP u v :
    reflect ((size u) <= (size v) /\ forall i, i < size u -> nth 0 u i > nth 0 v i)
            (dominate u v).
  Proof.
    rewrite /dominate; apply/(iffP idP).
    - move=> /andP [] Hsz /forallP Hall; split => [//=| i Hi].
      by apply (Hall (Ordinal Hi)).
    - move=> [] -> /= H; apply /forallP => [[i Hi]] /=; by apply H.
  Qed.

  Lemma dominate_rcons v u l : dominate u v -> dominate u (rcons v l).
  Proof.
    move /dominateP => [] Hsz Hlt.
    apply /dominateP; split => [|i Hi]; first by rewrite size_rcons; apply leqW.
    move: (Hlt _ Hi) => H.
    rewrite nth_rcons; case (ltnP i (size v)) => Hcomp //= {H}.
    move: {Hsz Hlt Hcomp} (leq_trans Hsz Hcomp) => Hs.
    move: (leq_ltn_trans Hs Hi); by rewrite ltnn.
  Qed.

  Lemma dominate_insrow_non_pos r1 r0 l i :
    is_row r0 -> is_row r1 -> dominate r1 r0 ->
    i < size (insrow r1 l) -> i != insrow_pos r1 l -> nth 0 r0 i < nth 0 r1 i.
  Proof.
    move=> Hrow0 Hrow1 /dominateP [] Hsz Hdom Hi Hipos1.
    apply Hdom; have:= (bumprow_size r1 l).
    move Hins1 : (bumprow r1 l) => res1.
    case: res1 Hins1 Hi => [[l1 |] tr1 Hins1] /=;
        first by rewrite -insbumprowE addn1 Hins1 /= => Hi /eqP [] ->.
    case (ltnP i (size r1)) => //= Hi1 Hi2 _.
    (* absurd case *)
    have HH : (i == size r1); move: (leq_trans Hi2 (insrow_size_sup r1 l));
        first by rewrite ltnS eqn_leq Hi1 => ->.
    move=> _ {Hi1 Hi2}.
    move: (insrow_append_pos Hins1) HH Hipos1 => <- /eqP ->.
    by rewrite eq_refl.
  Qed.

  Lemma dominate_eqsize_bump_appendF r1 r0 l l0 tr0 tr1 :
    is_row r0 -> is_row r1 -> dominate r1 r0 -> size r1 = size r0 ->
    bumprow r0 l = (Some l0, tr0) ->
    bumprow r1 l0 = (None, tr1) -> False.
  Proof.
    move=> Hrow0 Hrow1 Hdomin Heqsz Hins0 Hins1.
    have:= Hdomin => /dominateP [] _ Hdom.
    move: (bumprow_append Hins1) => Htr1; subst tr1.
    have {Hins1} Hins1: (rcons r1 l0) = (insrow r1 l0) by rewrite -insbumprowE Hins1.
    have {Hins1} : (is_row (rcons r1 l0)) by rewrite Hins1 insrow_is_row.

    move Hsz: (size r0) => n. (* n := size r0 <> 0 *)
    case: n Hsz => [/eqP /nilP Hnil _| n Hn]; first by move: Hins0; rewrite Hnil.

    move/is_row_last; rewrite -nth_last Heqsz Hn /= => H1.
    have Hnlt : (n < size r1) by rewrite -Hn Heqsz.
    move: (Hdom _ Hnlt) => /= H2.
    move: (bumprow_bump Hins0) => Hl0.
    move: (bumprow_pos Hins0); rewrite Hn ltnS => Hpos.
    move: Hnlt; rewrite Heqsz => Hnlt.
    move: (is_rowP _ Hrow0 _ _ Hpos Hnlt); rewrite -Hl0 => H3.
    move: (leq_ltn_trans H1 (leq_ltn_trans H3 H2)); by rewrite ltnn.
  Qed.

  Fixpoint is_tableau t :=
    match t with
      | [::] => true
      | [:: t0] => (t0 != [::]) && is_row t0
      | t0 :: ((t1 :: _) as ttl) => is_row t0 && dominate t1 t0 && is_tableau ttl
    end.

  Lemma tableau_is_row r t : is_tableau (r :: t) -> is_row r.
  Proof. by case t => [| l0 l1 /andP []] /andP [] //=. Qed.

  Lemma tableau_tail r t : is_tableau (r :: t) -> is_tableau t.
  Proof. by case t => [| l0 l1 /andP []] /andP [] //=. Qed.

  Lemma bump_dominate r1 r0 l tr0 l0:
    is_row r0 -> is_row r1 -> dominate r1 r0 ->
    bumprow r0 l = (Some l0, tr0) -> dominate (insrow r1 l0) tr0.
  Proof.
    move=> Hrow0 Hrow1 Hdomin; have:= Hdomin => /dominateP [] Hsz Hdom Hins0.
    apply /dominateP; split => [|i Hi].

    - have := (bumprow_size r0 l); rewrite Hins0 addn1 => /eqP [] <-.
      case (ltnP (size r1) (size r0)) => Hcomp;
          first by apply (leq_trans (insrow_size_sup r1 l0)).
      have: ((size r1) == (size r0)) by rewrite eqn_leq; apply /andP.
      move=> /eqP Heqsz {Hsz Hcomp}; rewrite -Heqsz.
      have:= (bumprow_size r1 l0).
      move Hins1 : (bumprow r1 l0) => res1.
      case: res1 Hins1 => [[l1 tr1 Hins1 | tr1 Hins1 _]] /=;
        first by rewrite -insbumprowE Hins1 addn1 => /eqP [] ->.
      exfalso. (* absurd : l0 <= last r0 < last r1  and last r1 <= l0 *)
      by apply (@dominate_eqsize_bump_appendF r1 r0 l l0 tr0 tr1).

    - have Hins0': tr0 = (insrow r0 l) by rewrite -insbumprowE Hins0.
      rewrite Hins0' !insrow_set !nth_set_nth /= => {Hins0'}.
      case (altP (i =P (insrow_pos r0 l))) => Hipos0;
         case (altP (i =P (insrow_pos r1 l0))) => Hipos1.
      * by apply (bumprow_lt Hins0).
      * have Hl: (l <= nth 0 r0 i).
          rewrite -(insrow_eq_pos r0 l) -Hipos0 -[nth _ r0 _](nth_any l 0);
              first by apply insrow_leq.
          by rewrite Hipos0 (bumprow_pos Hins0).
        have H01 := dominate_insrow_non_pos Hrow0 Hrow1 Hdomin Hi Hipos1.
        by apply (leq_ltn_trans Hl H01).
      * apply (leq_ltn_trans (n := l)); last by apply (bumprow_lt Hins0).
        apply insrow_pos_lt.
        rewrite neq_ltn in Hipos0.
        move: Hipos0 => /orP; case => [//=| Habs].
        (* absurd case *)
        set j := (insrow_pos r0 l).
        move: (insrow_pos_size r1 l0); rewrite -Hipos1 => H1.
        move: (leq_trans Habs H1) => H2; move: (Hdom _ H2) => {Hdom H2}.
        rewrite {1}/j -(bumprow_bump Hins0) => H2.
        move: Habs; rewrite Hipos1 => Habs.
        move: (leq_trans H2 (insrow_pos_lt Habs)).
        by rewrite ltnn.
      * by apply (dominate_insrow_non_pos Hrow0 Hrow1 Hdomin Hi Hipos1). 
  Qed.

  Theorem instab_is_tableau t l : is_tableau t -> is_tableau (instab t l).
  Proof.
    elim: t l => [l _ //=| t0 t IHt] l Htab /=.
    move H : (bumprow t0 l) => x; case: x H => [[ll|] tr] Hbump.
    - move: {IHt} (IHt ll (tableau_tail Htab)).
      move Hbp : (instab t ll) => bp.
      have Htr : (tr = insrow t0 l) by rewrite -insbumprowE Hbump.
      have Hrow := (insrow_is_row l (tableau_is_row Htab)).
      case: bp Hbp => [_| b0 btl Hbp /= ->].
      * by rewrite /= Htr Hrow insrow_non_nil.
      * rewrite {1}Htr Hrow /= andbT => {Hrow}.
        case: t Htab Hbp => [Htab /= [] <- _| t1 t Htabt01 Hbump1].
        + have H : ([:: ll] = insrow [::] ll) by [].
          have Hdom : (dominate [::] t0) by
             rewrite /dominate /=; apply /forallP => [[m /=]]; rewrite ltn0.
          rewrite H; apply (bump_dominate (r0 := t0) (l := l)) => //=.
          by move: Htab => /= /andP [] _.
        + have Htabt1 := (tableau_is_row (tableau_tail Htabt01)).
          move: Htabt01 => /= /andP [] /andP [] Htabt0 Hdom _.
          rewrite (bump0 Hbump1).
          by apply (bump_dominate Htabt0 Htabt1 Hdom Hbump).
    - move: (bumprow_append Hbump) => Htr {IHt}; subst tr.
      have Htr : (rcons t0 l = insrow t0 l) by rewrite -insbumprowE Hbump.
      case: t Htab (tableau_tail Htab) => [/= /andP [] Htab Hnnil _| t1 t].
      * rewrite rcons_nilF /= Htr; by apply insrow_is_row.
      * move=> /= /andP [] /andP [] Hrowt0 Hdom -> _.
        apply /andP; split; last by []; apply /andP; split;
            first by rewrite Htr; by apply insrow_is_row.
        by apply dominate_rcons.
  Qed.

  Definition to_word t := flatten (rev t).

  Fixpoint RS_rev w : seq (seq nat) :=
    if w is w0 :: wr then instab (RS_rev wr) w0 else [::].
  Definition RS w := RS_rev (rev w).

  Theorem RS_tableau w : is_tableau (RS w).
  Proof.
    elim/last_ind: w => [//=| w l0]; rewrite /RS rev_rcons /=.
    by apply instab_is_tableau.
  Qed.

End Tableaux.

(*
Eval compute in (RS [:: 2; 5; 1; 6; 4; 3]).
Eval compute in (to_word (RS [:: 2; 5; 1; 6; 4; 3])).
*)
