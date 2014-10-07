(******************************************************************************)
(*       Copyright (C) 2014 Florent Hivert <florent.hivert@lri.fr>            *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm fingroup.

Require Import subseq partition permuted ordtype schensted congr plactic greeninv std.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Standardisation.

Variable Alph : ordType.
Let Z := (inhabitant Alph).
Implicit Type s u v w : seq Alph.
Implicit Type p : seq nat.


Fixpoint posbig s := (* Position of the last occurence of the largest letter of w *)
  if s is a :: v then
    if maxLtn v a then 0 else (posbig v).+1
  else 0.

Lemma posbig_size_cons l s : posbig (l :: s) < size (l :: s).
Proof.
  elim: s l => [//= | s0 s /= IHs] l.
  case (foldl (maxX (T:=Alph)) s0 s <A l) => //=.
  rewrite ltnS; by apply IHs.
Qed.

Lemma posbig_size s : s != [::] -> posbig s < size s.
Proof. case: s => [//= | s l _]. by apply posbig_size_cons. Qed.

Fixpoint std_rec n s :=
  if n is n'.+1 then
    let rec := std_rec n' (rembig s) in
    let pos := posbig s in
    take pos rec ++ n' :: drop pos rec
  else [::].
Definition std s := std_rec (size s) s.

Lemma size_std_rec n s : size (std_rec n s) = n.
Proof.
  elim: n s => [//= | n IHn] s /=.
  by rewrite size_cat /= addnS -size_cat cat_take_drop IHn.
Qed.

Lemma std_is_std s : is_std (std s).
Proof.
  rewrite /is_std /std size_std_rec perm_eq_sym.
  move Hn : (size s) => n; elim: n s Hn => [//= | n IHn] s Hn.
  apply (@perm_eq_trans _ (n :: (iota 0 n))).
    rewrite -addn1 iota_add /= add0n -cat1s; apply/perm_eqlP; by apply perm_catC.
  apply (@perm_eq_trans _ (n :: std_rec n (rembig s))).
    rewrite perm_cons; apply IHn; by rewrite size_rembig Hn.
  rewrite {IHn Hn} /= -[n :: drop _ _]cat1s catA.
  move: (std_rec n (rembig s)) => l.
  rewrite -{1}[l](cat_take_drop (posbig s)) -cat1s -catA.
  by apply/perm_eqlP; apply perm_catCA.
Qed.

Lemma in_std_ltn_size s i : i \in std s = (i < size s).
Proof. by rewrite (mem_std _ (std_is_std s)) size_std_rec. Qed.

Lemma std_all_gtnX_size s : all (gtnX nat_ordType (size s)) (std s).
Proof. apply/allP=> i /=; by rewrite ltnXnatE in_std_ltn_size. Qed.

Lemma maxLtn_std_rec s : maxLtn (std s) (size s).
Proof. rewrite maxLtnAllP; by apply std_all_gtnX_size. Qed.

Lemma rembig_ins_std s pos :
  rembig (take pos (std s) ++ size s :: drop pos (std s)) = std s.
Proof.
  apply esym; apply/eqP; apply/rembigP; first by case: (take _ _).
  set ll := take _ _; set lr := drop _ _.
  exists ll; exists (size s); exists lr; split.
  + by rewrite cat_take_drop.
  + by [].
  + apply (@maxLeq_catl _ _ lr); rewrite cat_take_drop; apply maxLtnW.
    by apply maxLtn_std_rec.
  + apply (@maxLtn_catr _ ll); rewrite cat_take_drop; by apply maxLtn_std_rec.
Qed.

Lemma std_rembig s : std (rembig s) = rembig (std s).
Proof.
  rewrite /std.
  elim: s => [//= | s0 s IHs] /=.
  case (boolP (maxLtn s s0)) => [_ | Hmax].
  + case H : (std_rec (size s) s) => [//= | t0 t].
    by rewrite -H rembig_ins_std.
  + case H : s IHs Hmax => [//= |s1 s']; rewrite -H => IHs Hmax.
    have <- : size (s0 :: rembig s) = size s by rewrite /= size_rembig H.
    have:= rembig_ins_std; by rewrite /std => ->.
Qed.

Lemma posbigE l s :
  take (posbig (l :: s)) (rembig (l :: s)) ++
       foldl (@maxX _) l s
       :: drop (posbig (l :: s)) (rembig (l :: s)) = l :: s.
Proof.
  elim: s l => [//= | s0 s IHs] l /=.
  rewrite -maxXL.
  case (ltnXP (foldl (@maxX _) s0 s) l) => Hl /=.
  + by move: Hl => /ltnXW/maxX_idPl ->.
  + move: Hl => /maxX_idPr ->.
    by rewrite (IHs s0).
Qed.

Lemma nth_posbig l s : nth Z (l :: s) (posbig (l :: s)) = foldl (@maxX _) l s.
Proof.
  rewrite /=; case: (boolP (maxLtn s l)) => /=; rewrite /maxLtn.
  + case: s => [//= | s0 s] /=.
    move/ltnXW/maxX_idPl; by rewrite maxXL => ->.
  + elim Hs : s => [//= | s0 s' IHs] /=.
    rewrite /maxLtn -leqXNgtnX => Hmax.
    move: IHs; case Hs': s' {Hs} Hmax => [/= | s2 tls].
      by move=> /maxX_idPr ->.
    rewrite -Hs' -leqXNgtnX -maxXL.
    case (ltnXP (foldl (maxX (T:=Alph)) s2 tls) s0) => /=.
    * rewrite Hs' /= -!maxXL; set m := foldl _ _ _.
      by move=> /ltnXW/maxX_idPl -> /maxX_idPr ->.
    * rewrite {1 4 7}Hs' /= -!maxXL; set m := foldl _ _ _.
      move=> /maxX_idPr -> H1 H2.
      by rewrite (H2 H1).
Qed.

Lemma maxLeq_posbig l s :
  maxLeq (take (posbig (l :: s)) (l :: s)) (nth Z (l :: s) (posbig (l :: s))).
Proof.
  have : maxLeq (l :: s) (foldl (@maxX _) l s) by rewrite /maxLeq.
  rewrite -{1}[l :: s](cat_take_drop (posbig (l :: s))) nth_posbig.
  apply maxLeq_catl.
Qed.


Lemma maxLtn_posbig l s :
  maxLtn (drop (posbig (l :: s)).+1 (l :: s)) (nth Z (l :: s) (posbig (l :: s))).
Proof.
  rewrite nth_posbig.
  elim: s l => [//= | s0 s] /= IHs l.
  have {IHs} := IHs (maxX l s0); rewrite -!maxXL.
  set m := foldl (maxX (T:=Alph)) s0 s.
  rewrite [maxX l m]maxXC [maxX m l]/maxX.
  case: (ltnXP m l) => //=; rewrite /m {m} => Hm.
  suff -> : maxLtn s (maxX l s0) = maxLtn s s0 by [].
  rewrite maxXC /maxX; case (ltnXP s0 l) => //=.
  case: s Hm => [//= | s1 s] /=.
  rewrite -!maxXL; set m := foldl (maxX (T:=Alph)) s1 s.
  rewrite /maxX; case (ltnXP m s0) => Hm.
  - have := (ltnXW Hm); rewrite leqXNgtnX => /negbTE -> H1.
    move/(leqX_ltnX_trans H1); by rewrite ltnXnn.
  - rewrite {1}/ltnX_op Hm andbT.
    case: (s0 == m) => /=.
    + move=> H1; move/(leqX_ltnX_trans H1); by rewrite ltnXnn.
    + by rewrite leqXNgtnX => /negbTE ->.
Qed.

Lemma rembigE l s :
  take (posbig (l :: s)) (l :: s) ++
       drop (posbig (l :: s)).+1 (l :: s) = rembig (l :: s).
Proof.
  apply/eqP; apply/rembigP; first by [].
  set ss := l :: s; set pos := posbig (l :: s).
  exists (take pos ss).
  exists (nth Z ss pos).
  exists (drop pos.+1 ss).
  split; first by [].
  + set sr := (X in _ ++ X); suff -> : sr = drop pos ss by rewrite cat_take_drop.
    rewrite /sr /ss /pos /= {ss pos sr}.
    elim H : s => [//= | s0 s']; rewrite -H.
    case (boolP (maxLtn s l)) => Hmax /=; first by rewrite drop0.
    move: Hmax; rewrite H => Hmax /=.
    case (boolP (maxLtn s' s0)) => Hmax0 /=; first by rewrite drop0.
    suff -> : maxLtn s' l = false by [].
    apply negbTE; move: Hmax; apply contra => /= Hmax.
    apply maxLtnCons; last exact Hmax.
    case: s' Hmax0 Hmax {H} => [//= | s1 s' /=]; rewrite /maxLtn.
    rewrite -leqXNgtnX; by apply leqX_ltnX_trans.
  + rewrite /ss /pos {ss pos}; by apply maxLeq_posbig.
  + rewrite /ss /pos {ss pos}; by apply maxLtn_posbig.
Qed.

Lemma nth_lt_posbig i s : i < posbig s -> nth Z (rembig s) i = nth Z s i.
Proof.
  case H : s => [//= | s0 s'] => Hi.
  rewrite -rembigE -H -{5}[s](cat_take_drop (posbig s)) !nth_cat.
  by rewrite size_take posbig_size H //= Hi.
Qed.

Definition shift_pos pos i := if i < pos then i else i.-1.

Lemma nth_rembig s i :
  i != (posbig s) -> nth Z s i = nth Z (rembig s) (shift_pos (posbig s) i).
Proof.
  case Hs : s => [/= | s0 s']; first by rewrite !nth_nil.
  rewrite /shift_pos -rembigE nth_cat [i < _]ltn_neqAle -Hs.
  move=> Hi; rewrite Hi andTb.
  rewrite size_take posbig_size; last by rewrite Hs.
  case (leqP i (posbig s)) => Hipos.
  + have {Hipos Hi} Hipos : i < posbig s by rewrite ltn_neqAle Hi Hipos.
    by rewrite nth_take Hipos.
  + rewrite ltnNge -ltnS (ltn_predK Hipos) Hipos /=.
    rewrite nth_drop addSn subnKC; first by rewrite (ltn_predK Hipos).
    by rewrite -ltnS (ltn_predK Hipos).
Qed.

Lemma shift_pos_incr pos i j : i <= j -> shift_pos pos i <= shift_pos pos j.
Proof.
  move=> Hij; rewrite /shift_pos; case (ltnP j pos) => Hj.
  - by rewrite (leq_ltn_trans Hij Hj).
  - case (ltnP i pos) => Hi.
    + have {Hij Hi Hj} Hij := leq_trans Hi Hj.
      by rewrite -ltnS (ltn_predK Hij).
    + case: i Hij {Hi Hj} => [//= | i] /= Hij.
      by rewrite -ltnS (ltn_predK Hij).
Qed.

Lemma max_iota_i_n i n : foldl (@maxX _) i (iota i.+1 n) = i + n.
Proof.
  elim: n i => [//= | n IHn] /= i.
  rewrite -maxXL IHn addSnnS; apply/maxX_idPr.
  by rewrite leqXnatE -{1}[i]addn0 leq_add2l.
Qed.

Lemma max_iota_n n : foldl (@maxX _) 0 (iota 1 n) = n.
Proof. by rewrite -{2}[n]add0n max_iota_i_n. Qed.

End Standardisation.

Lemma std_std s : is_std s -> std s = s.
Proof.
  rewrite /std /is_std.
  move Hn : (size s) => n; elim: n s Hn => [/= | n IHn] s Hsz.
  + by move: Hsz=> /eqP/nilP ->.
  + case Hs : s Hsz => [//= | s0 s'].
    rewrite -{2 3 4}Hs => Hsz Hperm /=.
    have Hszrem : size (rembig s) = n by rewrite size_rembig Hs Hsz.
    have Hprem : perm_eq (rembig s) (iota 0 n).
      rewrite -rembig_iota; by apply perm_eq_rembig.
    rewrite (IHn _ Hszrem Hprem) Hs {IHn}.
    have:= Hperm; rewrite {1}Hs => /maxL_perm_eq.
    rewrite max_iota_n => <-.
    by rewrite posbigE.
Qed.

Lemma std_stdE (T : ordType) (s : seq T) : std (std s) = std s.
Proof. apply std_std; by apply std_is_std. Qed.

Section Spec.

Variable Alph : ordType.
Let Z := (inhabitant Alph).
Implicit Type s u v w : seq Alph.
Implicit Type p : seq nat.

CoInductive std_spec s : seq nat -> Type :=
  | StdSpec :
      forall p, (size p = size s) ->
                (forall i j, i <= j < size p ->
                             (nth Z s i <=A nth Z s j) = (nth 0 p i <= nth 0 p j))
                -> std_spec s p.

Local Notation N0 := (inhabitant nat_ordType).

Lemma stdP s : std_spec s (std s).
Proof.
  constructor; first by apply size_std_rec.
  (*   rewrite /std size_std_rec. *)
  move=> i j => /andP [] Hij Hj; have Hi := leq_ltn_trans Hij Hj.
  rewrite (nth_any _ N0 Hi) (nth_any _ N0 Hj).
  move: Hi Hj; rewrite size_std_rec; move Hn : (size s) => n.
  elim: n s Hn  => [/= | n IHn] s; first by move/eqP/nilP => ->; rewrite /std /= !nth_nil.
  case Hs : s => [//= | s0 s'] Hsz Hi Hj; rewrite -Hs.
  case (altP (i =P posbig (std s))) => [-> | Hipos].
  + rewrite nth_posbig.
  rewrite (@nth_rembig _ (std s)).
  
  move=> Hsize i j Hij /=.
  have:= Hij => /andP [] Hi Hj.
  have Hnnil : s != [::] by move: Hsize; case s.
  rewrite !nth_cat size_take size_std_rec.
  have -> : (if posbig s < n then posbig s else n) = posbig s.
    case (ltnP (posbig s) n) => //= Hn.
    apply /eqP; rewrite eqn_leq Hn /=.
    have:= (posbig_size Hnnil); by rewrite Hsize ltnS.
  have Hszrem : size (rembig s) = n by rewrite size_rembig Hsize.
  case (ltnP j (posbig s)) => Hjpos.
  + have Hipos := leq_ltn_trans Hi Hjpos.
    rewrite Hipos (nth_take _ Hipos) (nth_take _ Hjpos).
    have : i <= j < n.
      rewrite Hi /=; apply (leq_trans Hjpos); rewrite -ltnS -Hsize.
      by apply posbig_size.
    move/(IHn _ Hszrem) <- => {IHn}.
    by rewrite (nth_lt_posbig Hipos) (nth_lt_posbig Hjpos).
  admit.
Qed.

End Spec.

Lemma std_rconsK (S T : ordType) (u : seq S) (v : seq T) a b :
  std (rcons u a) = std (rcons v b) -> std u = std v. 
Proof.
  admit.
Qed.

Section StdRS.

Variable Alph : ordType.
Let Z := (inhabitant Alph).
Implicit Type s u v w : seq Alph.
Implicit Type p : seq nat.

Theorem std_plact u v : plactcongr u v -> plactcongr (std u) (std v).
Proof.
  have:= @plactcongr_equiv nat_ordType => /equivalence_relP [] Hrefl Htrans.
  move: v; apply gencongr_ind; first by apply Hrefl.
  move=> a b1 c b2 H Hplact.
  rewrite -(@Htrans (std (a ++ b1 ++ c))); last by rewrite -(Htrans _ _ H); apply Hrefl.
  move: Hplact {H} => /plactruleP.
  admit. (* TODO standardize the rules *)
Qed.

Theorem shape_RS_std u : shape (RS (std u)) = shape (RS u).
Proof.
  admit. (* TODO green invariants using specification of std by inversions *)
Qed.

Lemma shape_Qsymb (u : seq Alph) l i :
  shape_rowseq (RSmap (rcons u l)).2 = incr_nth (shape_rowseq (RSmap u).2) i ->
  (RSmap (rcons u l)).2 = i :: (RSmap u).2.
Proof.
  rewrite /RSmap rev_rcons /= -[RSmap_rev (rev u)]/(RSmap u).
  case HRS : (RSmap u) => [t0 rows].
  case Hins : (instabnrow t0 l) => [tr irow] /=.
  by move/incr_nth_inj ->.
Qed.

Lemma size_RSmap2 u : size ((RSmap u).2) = size u.
Proof.
  elim/last_ind: u => [//= | u un].
  rewrite /RSmap rev_rcons /=.
  case: (RSmap_rev (rev u)) => [t rows] /=.
  case: (instabnrow t un) => [tr nrow] /= ->.
  by rewrite size_rcons.
Qed.

End StdRS.

Theorem RSmap_std (T : ordType) (w : seq T) : (RSmap (std w)).2 = (RSmap w).2.
Proof.
  move Hn : (size w) => n.
  elim: n T w Hn => [/= | n IHn] T w; first by move/eqP/nilP => ->.
  case/lastP Hw : w => [//= | w' wn] Hn.
  have:= shape_RS_std (rcons w' wn).
  rewrite -!RSmapE !shape_RSmap_eq.
  case/lastP H : (std (rcons w' wn)) => [/= | st stn].
    exfalso; have:= eq_refl (@size nat [::]).
    by rewrite -{1}H size_std_rec size_rcons.
  case HRS : ((RSmap (rcons w' wn)).2) => [/= | iw yamw].
    exfalso; have:= eq_refl (@size nat [::]).
    by rewrite -{1}HRS size_RSmap2 size_rcons.
  have Hyamw : yamw = (RSmap w').2.
    move: HRS; rewrite /RSmap rev_rcons /=.
    case: (RSmap_rev (rev w')) => [t rows] /=.
    by case: (instabnrow t wn) => [tr nrow] /= [] _ ->.
  have Hsize : size w' = n by move: Hn => /eqP; rewrite size_rcons eqSS => /eqP.
  have /std_rconsK Hst : std (rcons w' wn) = std (rcons st stn) by rewrite -H std_stdE.
  rewrite Hyamw /= -(IHn _ _ Hsize).
  have Hsizest : size st = n.
    have := Hst; rewrite /std -{2}(size_std_rec (size st) st) => <-.
    by rewrite size_std_rec.
  rewrite Hst (IHn _ _ Hsizest).
  by apply shape_Qsymb.
Qed.



Lemma is_tableau_reshape_std t :
 is_tableau t -> is_tableau (reshape (rev (shape t)) (std (to_word t))).
Proof.
  admit.
Qed.

Lemma is_tableau_std t : is_tableau t -> std (to_word t) = to_word (RS (std (to_word t))).
Proof.
  admit.
Qed.

Theorem std_RS w : to_word (RS (std w)) = std (to_word (RS w)).
Proof.
  rewrite (is_tableau_std (is_tableau_RS w)); congr (to_word _).
  apply /eqP; rewrite -plactic_RS.
  apply std_plact; by apply congr_RS.
Qed.

(*
Definition inc_val v := [fun i => if i < v then i else i.+1].
Definition ins_val v p := v :: [seq inc_val v i | i <- p].

Lemma ins_val_uniq v p : uniq p -> uniq (ins_val v p).
Proof.
  rewrite /ins_val /= => Huniq; apply/andP; split.
  - apply (introN idP) => /mapP [] x _.
    case (ltnP x v) => Hx Hv; move: Hx; by rewrite Hv ltnn.
  - rewrite map_inj_in_uniq; first exact Huniq.
    move=> i j _ _ /=.
    case (ltnP i v) => Hi; case (ltnP j v) => Hj //= Heq.
    + rewrite Heq in Hi; have:= leq_trans Hi Hj.
      by rewrite ltnNge leqnSn.
    + rewrite -Heq in Hj; have:= leq_trans Hj Hi.
      by rewrite ltnNge leqnSn.
    + apply /eqP; move: Heq => /eqP; by rewrite eqSS.
Qed.

Lemma std_ins_val v p : is_std p -> v <= size p -> is_std (ins_val v p).
Proof.
  move=> Hstd Hsize.
  rewrite /is_std {2}/ins_val [size(_ :: _)]/= size_map.
  apply uniq_perm_eq.
  - apply ins_val_uniq; by apply std_uniq.
  - apply iota_uniq.
  - move=> i; rewrite mem_iota /= add0n /ins_val.
    apply/(sameP idP); apply(iffP idP); rewrite inE.
    + move=> Hp.
      case (altP (i =P v)) => //= Hiv; apply/mapP.
      case (ltnP i v) => Hi.
      * exists i; last by rewrite Hi.
        rewrite (mem_std _ Hstd); by apply (leq_trans Hi).
      * have {Hi Hiv} Hi : v < i by rewrite ltn_neqAle Hi eq_sym Hiv.
        case: i Hp Hi => //= i'. rewrite !ltnS [v <= i']leqNgt => Hp /negbTE Hi.
        exists i'; last by rewrite Hi.
        by rewrite (mem_std _ Hstd).
    + case (altP (i =P v)) => [/= -> _| /= Hi]; first by rewrite ltnS.
      move/mapP => [] j; rewrite (mem_std _ Hstd) => Hj H; subst i.
      move: Hi; case (ltnP j v) => Hv Heq.
      * rewrite ltnS; apply ltnW; by apply (leq_trans Hv).
      * by rewrite ltnS.
Qed.

Fixpoint std_old s : seq nat :=
  if s is s0 :: s' then
    let c := count (gtnX _ s0) s' in ins_val c (std_old s')
  else [::].

Lemma size_std_old s : size (std_old s) = size s.
Proof. elim: s => [//= |s0 s IHs] /=. by rewrite /ins_val size_map IHs. Qed.

Lemma std_old_is_std s : is_std (std_old s).
Proof.
  elim: s => [//= |s0 s IHs] /=.
  apply (std_ins_val IHs).
  rewrite size_std_old; by apply count_size.
Qed.

Lemma in_std_old_ltn_size s i : i \in std_old s = (i < size s).
Proof. by rewrite (mem_std _ (std_old_is_std s)) size_std_old. Qed.

Lemma std_old_all_gtnX_size s : all (gtnX nat_ordType (size s)) (std_old s).
Proof. apply/allP=> i /=; by rewrite ltnXnatE in_std_old_ltn_size. Qed.

Lemma count_rembig x s :
  ~~ maxLtn s x -> count (gtnX _ x) (rembig s) = count (gtnX _ x) s.
Proof.
  elim: s => [//= | s0 s IHs] /= H.
  case: (boolP (maxLtn s s0)) => Hmax.
  - case (ltnXP s0 x) => Hx; last by [].
    exfalso; case: s {IHs} H Hmax => [| s1 s] /=; first by rewrite Hx.
    rewrite -maxXL gtnX_maxX Hx /= => Hn H.
    by rewrite (ltnX_trans H Hx) in Hn.
  - move=> /=; congr (_ + _); apply IHs => {IHs}.
    case: s Hmax H => [| s1 s] //=.
    by rewrite -maxXL -!leqXNgtnX => /maxX_idPr ->.
Qed.

Section IncrMap.

Variable T1 T2 : ordType.
Variable f : T1 -> T2.
Hypothesis Hinc : forall i j, i <A j -> f i <A f j.

Lemma maxLtn_inc_map (s : seq T1) c :
  maxLtn [seq f i | i <- s] (f c) = maxLtn s c.
Proof.
  rewrite !maxLtnAllP.
  elim: s => [//= | s0 s IHs] /=.
  rewrite IHs; congr (_ && _).
  apply/(sameP idP); apply(iffP idP); first by apply Hinc.
  apply contraLR; rewrite -!leqXNgtnX.
  case: (ltnXP c s0); first by move/Hinc/ltnXW ->.
  move=> H1 H2; have /eqP -> //= : c == s0.
  by rewrite eqn_leqX H1 H2.
Qed.

Lemma inc_rembig (s : seq T1) : rembig [seq f i | i <- s] = [seq f i | i <- rembig s].
Proof.
  elim: s => [//= | s0 s IHs] /=.
  rewrite maxLtn_inc_map.
  case: (maxLtn s s0) => //=.
  by rewrite IHs.
Qed.

End IncrMap.

Lemma std_old_rembig s : std_old (rembig s) = rembig (std_old s).
Proof.
  elim: s => [//= | s0 s IHs] /=.
  case: (boolP (maxLtn s s0)) => /=.
  + rewrite maxLtnAllP all_count => /eqP ->.
    rewrite map_id_in; last by move=> i; rewrite in_std_old_ltn_size => ->.
    by rewrite maxLtnAllP std_old_all_gtnX_size.
  + move=> Hmax.
    have := Hmax; rewrite maxLtnAllP all_count (count_rembig Hmax) IHs {IHs}.
    move Hc : (count ((gtnX _) s0) s) => c Hcs.
    set l := map _ _.
    have {Hcs} Hcs : c < size s by rewrite ltn_neqAle Hcs /= -Hc count_size.
    have Hl : (size s) \in l.
      rewrite /l; apply/mapP; move: Hcs; case s => [//= |s1 s' Hcs].
      exists (size s'); first by rewrite in_std_old_ltn_size.
      move: Hcs => /=; by rewrite ltnNge => /negbTE ->.
    have -> : maxLtn l c = false.
      rewrite maxLtnAllP; apply (introF idP) => /allP H.
      have /= := H (size s) Hl; rewrite ltnXnatE ltnNge.
      by rewrite (ltnW Hcs).
    rewrite /l inc_rembig //=.
    move=> i j; rewrite !ltnXnatE => Hij.
    case: (ltnP j c).
    + by move/(ltn_trans Hij) ->.
    + move=> _; case (i < c) => //=.
      by apply (ltn_trans Hij).
Qed.

Lemma count_gtn_std_old c s : c <= (size s) -> count (gtn c) (std_old s) = c.
Proof.
  admit.
Qed.

Lemma std_old_big_ind s :
  (forall i j, i < j < size (std_old s) ->
               (nth Z s i <=A nth Z s j) = (nth 0 (std_old s) i <= nth 0 (std_old s) j)) /\
  (forall l v, count (gtnX _ l) s = count (gtn v) (std_old s) ->
               forall i, i < size (std_old s) -> l <=A (nth Z s i) = (v <= (nth 0 (std_old s) i))).
Proof.
  elim: s => [| s0 s [] IHs2 IHs1] /=.
  + split.
    - move=> i j /=; first by rewrite ltn0 andbF.
    - move=> l v _ i; by rewrite ltn0.
  + split.
    - move=>  i j /=; rewrite size_map /ins_val.
      set c := count ((gtnX Alph) s0) s.
      case: j => [//= | j] /=; rewrite !ltnS.
      case: i => [ | i]/= Hj.
      * rewrite (IHs1 _ c); last exact Hj.
        + rewrite (nth_map 0); last exact Hj.
          rewrite leqNgt; case: (ltnP (nth 0 (std_old s) j) c).
          - by rewrite [c <= _]leqNgt => ->.
          - move/leq_trans => -> //=; by apply leqnSn.
        + rewrite count_gtn_std_old //=.
          apply count_size.
    - rewrite (IHs2 _ _ Hj).
CoInductive std_spec s : seq nat -> Type :=
  | StdSpec : forall p, (size p = size s) ->
                        (forall i j, i < j < size p ->
                                     (nth Z s i <=A nth Z s j) = (nth 0 p i <= nth 0 p j))
                        -> std_spec s p.

Lemma stdP s : std_spec s (std s).
Proof.
  constructor; first by apply size_std.
  elim: s => [| s0 s IHs] i j /=; first by rewrite ltn0 andbF.
  rewrite size_map /ins_val.
  set c := count ((gtnX Alph) s0) s.
  case: j => [//= | j] /=; rewrite !ltnS.
  case: i => [ | i]/= Hj.
  - rewrite (nth_map 0 _ _ Hj); set lj := (nth _ _ j).
    case: (boolP (c == (size s))) => Hc.
    + have:= Hc; rewrite {1}/c -all_count => /allP Hall.
      have /Hall /= : lj \in s by apply mem_nth; rewrite -size_std.
      rewrite leqXNgtnX => -> /=.
      move: Hc => /eqP -> {IHs s0 c Hall}.
      have H : nth 0 (std s) j < size s.
        move: Hj => /(mem_nth 0).
        have:= (std_is_std s); rewrite /is_std => /perm_eq_mem ->.
        by rewrite mem_iota /= add0n size_std.
      by rewrite H leqNgt H.
    + have {Hc} Hc : c \in std s.
        have:= (std_is_std s); rewrite /is_std => /perm_eq_mem ->.
        rewrite mem_iota /= add0n size_std ltn_neqAle Hc /=; by apply count_size.
      rewrite -(nth_index 0 Hc).
      set i := index c (std s).
      
      admit.
  - rewrite (IHs _ _ Hj) {IHs}; move: Hj => /andP [] Hi Hj.
    rewrite (nth_map 0 _ _ Hj) (nth_map 0 _ _ (ltn_trans Hi Hj)) {Hi Hj}.
    set li := (nth _ _ i); set lj := (nth _ _ j).
    case: (ltnP lj c) => Hj; case: (leqP li lj) => Hij.
    + by rewrite (leq_ltn_trans Hij Hj) Hij.
    + case (ltnP li c) => Hi; rewrite leqNgt; first by rewrite Hij.
      by rewrite (ltn_trans Hij (ltnSn _)).
    + case (ltnP li c) => Hi. by rewrite (leq_trans Hij (leqnSn _)).
      by rewrite (leq_ltn_trans Hij (ltnSn _)).
    + rewrite ltnNge; rewrite (ltnW (leq_ltn_trans Hj Hij)) /=.
      by rewrite ltnNge Hij.
Qed.
*)

End StdRS.
