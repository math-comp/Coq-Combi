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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice.
Require Import finset fintype finfun tuple bigop ssralg ssrint.
Require Import fingroup perm zmodp binomial poly matrix.
Require Import partition skewtab.
Require Import ssrcomplements poset freeg mpoly.

Require Import sym_group antisym.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.


Section VandermondeDet.

Variable n : nat.
Variable R : comRingType.

Definition alternpol (f : {mpoly R[n]}) : {mpoly R[n]} :=
  \sum_(s : 'S_n) (-1) ^+ s *: msym s f.
Definition rho := [multinom (n - 1 - i)%N | i < n].
Definition altSchur (m : 'X_{1..n}) := alternpol 'X_[m + rho].
Definition mpart (s : seq nat) :=
  if (size s) > n then 0%MM else [multinom (nth 0 s i)%N | i < n].

Lemma altSchur_anti m : altSchur m \is antisym.
Proof.
  apply/isantisymP => S.
  rewrite /altSchur/alternpol.
  rewrite (big_morph (msym S) (@msymD _ _ _) (@msym0 _ _ _)).
  rewrite scaler_sumr.
  rewrite [RHS](reindex_inj (mulIg S)); apply: eq_big => //= s _.
  rewrite msymZ -msymMm scalerA; congr (_ *: _).
  by rewrite odd_permM signr_addb [X in (_  = _ * X)]mulrC signrMK.
Qed.

Lemma alterpol_alternate (m : 'X_{1..n}) (i j : 'I_n) :
  i != j -> m i = m j -> alternpol 'X_[m] = 0.
Proof.
  move=> H Heq.
  pose t := tperm i j.
  have oddMt s: (t * s)%g = ~~ s :> bool by rewrite odd_permM odd_tperm H.
  rewrite [alternpol _](bigID (@odd_perm _)) /=.
  apply: canLR (subrK _) _; rewrite add0r -sumrN.
  rewrite (reindex_inj (mulgI t)); apply: eq_big => //= s.
  rewrite oddMt => /negPf ->; rewrite scaleN1r scale1r; congr (- _).
  rewrite msymMm.
  suff -> : msym t 'X_[m] = ('X_[m] : {mpoly R[n]}) by [].
  rewrite msymX; congr mpolyX.
  rewrite mnmP => k /=.
  rewrite !mnmE /= tpermV.
  case: (tpermP i j k) => Hk //; by rewrite Hk Heq.
Qed.

Lemma altSchur_add1_0 (m : 'X_{1..n}) i :
  (nth 0%N m i).+1 = nth 0%N m i.+1 -> altSchur m = 0.
Proof.
  move=> Heq.
  have Hi1n : i.+1 < n.
    rewrite ltnNge; apply (introN idP) => Hi.
    move: Heq; by rewrite [RHS]nth_default // size_tuple.
  have Hi : i < n by rewrite ltnW.
  pose i0 := Ordinal Hi; pose i1 := Ordinal Hi1n.
  have /alterpol_alternate : i0 != i1.
    apply (introN idP) => /eqP H.
    have := erefl (val i0); rewrite {2}H /= => /eqP.
    by rewrite ieqi1F.
  apply.
  rewrite !mnmDE !mnmE !(mnm_nth 0%N) -Heq -(mnm_nth 0%N m i0).
  rewrite addSn -addnS subn1 /= subnS prednK //.
  have -> : (n.-1 - i = n - i.+1)%N.
    case: n Hi1n Hi {i0 i1} => [//= | n' _] /=.
    by rewrite subSS.
  by rewrite subn_gt0.
Qed.

Local Notation "''e_' k" := (@mesym _ _ k) (at level 8, k at level 2, format "''e_' k").
(* Local Notation "m # s" := [multinom m (s i) | i < n]
  (at level 40, left associativity, format "m # s"). *)

Lemma altSchur_elementary (m : 'X_{1..n}) k :
  (altSchur m) * 'e_k =
  \sum_(h : {set 'I_n} | #|h| == k) altSchur (m + mesym1 h).
Proof.
  rewrite /altSchur/alternpol exchange_big /=.
  rewrite mulr_suml; apply eq_bigr => s _.
  rewrite -(issymP _ (mesym_sym n R k) s) mesymE.
  rewrite (raddf_sum (msym_additive _ _)) /=.
  rewrite mulr_sumr; apply eq_bigr => h _.
  rewrite -scalerAl -msymM -mpolyXD.
  by rewrite -!addmA [(mesym1 h + rho)%MM]addmC.
Qed.

Section HasIncr.

Require Import tools sorted Schur.
Local Open Scope nat_scope.

Variables (d k : nat) (P1 : intpartn d) (h : {set 'I_n}).

Definition hasincr :=
  has (fun i => (nth 0 (mpart P1 + mesym1 h)%MM i).+1 ==
                 nth 0 (mpart P1 + mesym1 h)%MM i.+1) (iota 0 n.-1).

Lemma hasincr0 : hasincr -> altSchur ((mpart P1) + mesym1 h) = 0%R.
Proof. move=> /hasP [] i _ /eqP; exact: altSchur_add1_0. Qed.

Fixpoint rem_trail0 s :=
  if s is s0 :: s' then
    if (rem_trail0 s') is t1 :: t' then s0 :: t1 :: t'
    else if s0 == 0 then [::] else [:: s0]
  else [::].

Lemma size_rem_trail0 s : size (rem_trail0 s) <= size s.
Proof.
  elim: s => [//= | s0 s]/=.
  case: (rem_trail0 s) => [/= _ | //=].
  by case: eqP.
Qed.

Lemma nth_rem_trail0 s i : nth 0 (rem_trail0 s) i = nth 0 s i.
Proof.
  elim: s i => [//= | s0 s]/=.
  case: (rem_trail0 s) => [/= | t1 t'] IHs i.
  - case (altP (s0 =P 0)) => [-> |_].
    * by case: i => [//= | i]; first by rewrite /= -IHs.
    * case: i => [//= | i] /=; exact: IHs.
  - case: i => [//= | i] /=; exact: IHs.
Qed.

Lemma sumn_rem_trail0 s : sumn (rem_trail0 s) = sumn s.
Proof.
  elim: s => [//= | s0 s] /=.
  case: (rem_trail0 s) => [/= <- | t1 t' <- //=].
  case: (altP (s0 =P 0%N)) => [-> | _] /=; by rewrite ?addn0.
Qed.

Lemma is_part_rem_trail0 s : sorted geq s -> is_part (rem_trail0 s).
Proof.
  case: s => [//= | s0 s]; rewrite [sorted _ _]/=.
  elim: s s0 => [| s1 s IHs] s0 /=; first by case: s0.
  move=> /andP [] H01 /IHs /=.
  case: (rem_trail0 s) => [_ | t0 t] /=; last by rewrite H01.
  case: (altP (s1 =P 0)) => [_ | Hs1].
  - case (altP (s0 =P 0)) => [// | Hs0] /=.
    by rewrite lt0n Hs0.
  - by rewrite /= H01 lt0n Hs1.
Qed.

Lemma not_hasincr_part :
  size P1 <= n -> ~~ hasincr ->
  is_part_of_n (d + #|h|) (rem_trail0 ((mpart P1) + mesym1 h)%MM).
Proof.
  move=> Hsz /hasPn H.
  rewrite /mpart ltnNge Hsz /=.
  apply/andP; split.
  - rewrite sumn_rem_trail0.
    rewrite -(@sum_iota_sumnE _ n); last by rewrite size_map size_enum_ord.
    rewrite big_mkord.
    rewrite (eq_bigr (fun i : 'I_n => nth 0 P1 i + (mesym1 h) i)%N); first last.
      move=> i _.
      have H0 : 0 < n by apply: (leq_ltn_trans _ (ltn_ord i)).
      rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
      rewrite nth_ord_enum /= (mnm_nth 0) /=.
      rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
      by rewrite nth_ord_enum.
    rewrite big_split /=; apply/eqP; congr (_ + _)%N.
    + rewrite -{2}(intpartn_sumn P1).
      by rewrite -(sum_iota_sumnE Hsz) big_mkord.
    + rewrite -mdeg_mesym1 /mdeg.
      rewrite -map_tnth_enum big_map /index_enum enumT.
      apply eq_bigr => i _.
      by rewrite mnm_tnth.
  - apply is_part_rem_trail0.
    apply/(sorted1P 0) => i.
    rewrite size_map size_enum_ord => Hi1.
    have Hi : i < n by exact: (ltn_trans _ Hi1).
    have {H} /H : i \in iota 0 n.-1.
      rewrite mem_iota add0n.
      by case: n Hi1 {Hsz H Hi} => [//= | n'] /=; rewrite ltnS.
    rewrite /mpart ltnNge Hsz.
    have H0 : 0 < n by apply: (leq_ltn_trans _ Hi1).
    rewrite !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
    rewrite !nth_enum_ord //.
    set bi := (_ \in h); set bi1 := (_ \in h).
    have:= is_partP _ (intpartnP P1) => [] [] _ H.
    have {H} := H i; move: (i.+1) => j /= H1.
    case: bi bi1 => [] [] /=; rewrite ?addn1 ?addn0 => H2.
    - by rewrite ltnS.
    - exact: (leq_trans H1).
    - by rewrite ltn_neqAle -eqSS eq_sym H2 H1.
    - exact: H1.
Qed.

Let add_mpart_mesym :=
  if [&& size P1 <= n, #|h| == k & ~~ hasincr] then (rem_trail0 ((mpart P1) + mesym1 h)%MM)
  else rowpart (d + k) (* unused *).
Lemma add_mpart_mesymP : is_part_of_n (d + k) add_mpart_mesym.
Proof.
  rewrite /add_mpart_mesym.
  case: (boolP [&& _, _ & _]) => [/and3P [] H1 /eqP <- H3| _].
  + exact: not_hasincr_part.
  + exact: rowpartnP.
Qed.
Definition add_mesym : intpartn (d + k) := IntPartN add_mpart_mesymP.

Lemma add_mesymE :
  size P1 <= n -> #|h| == k -> ~~ hasincr ->
  mpart add_mesym = (mpart P1 + mesym1 h)%MM.
Proof.
  rewrite /add_mesym /add_mpart_mesym => Hsz /= /eqP <- Hincr.
  rewrite /mpart /= Hsz Hincr /= (ltnNge n (size P1)) Hsz eq_refl /=.
  set S := (map _ _).
  have := size_rem_trail0 S.
  rewrite size_map size_enum_ord (ltnNge n) /S {S} => -> /=.
  rewrite mnmP => i.
  rewrite mnmE nth_rem_trail0.
  have H0 : 0 < n by apply: (leq_ltn_trans _ (ltn_ord i)).
  rewrite !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
  by rewrite !nth_ord_enum.
Qed.

End HasIncr.

Definition setdiff (P1 P : seq nat) : {set 'I_n} :=
  [set i : 'I_n | nth 0%N P1 i < nth 0%N P i].

Lemma card_setdiff d k (P1 : intpartn d) (P : intpartn (d + k)) :
  size P <= n -> size P1 <= n -> vb_strip P1 P -> #|setdiff P1 P| = k.
Proof.
  move=> Hsz Hsz1 /(vb_stripP (intpartnP _) (intpartnP _)) Hstrip.
  rewrite /setdiff -sum1dep_card.
  rewrite -{2}(addKn d k).
  rewrite -{4}(intpartn_sumn P1) -{2}(intpartn_sumn P).
  rewrite -(sum_iota_sumnE Hsz) -(sum_iota_sumnE Hsz1).
  set rhs := RHS.
  have {rhs} -> : rhs = (\sum_(0 <= i < n) (nth 0 P i - nth 0 P1 i)).
    rewrite /rhs {rhs} /index_iota subn0.
    elim: n {Hsz Hsz1} => [//= | i IHi]; first by rewrite !big_nil.
    rewrite -addn1 iota_add /= add0n !big_cat !big_cons !big_nil /= !addn0.
    rewrite subnDA subnAC -addnBA; last by have := Hstrip i => /andP [].
    rewrite addnC [RHS]addnC -IHi {IHi}.
    rewrite addnBA //.
    elim: i => [//= | i IHi]; first by rewrite !big_nil.
    rewrite -addn1 iota_add /= add0n !big_cat !big_cons !big_nil /= !addn0.
    apply leq_add; first exact: IHi.
    by have := Hstrip i => /andP [].
  rewrite big_mkord.
  rewrite [RHS](bigID (fun i : 'I_n => nth 0 P1 i < nth 0 P i)) /=.
  rewrite [X in (_ = _ + X)]big1 ?addn0; first last.
    move=> i; by rewrite -leqNgt /leq => /eqP.
  apply eq_bigr => i H.
  have:= Hstrip i => /andP [] H1 H2.
  suff -> : nth 0 P i = (nth 0 P1 i).+1 by rewrite subSn // subnn.
  apply anti_leq; by rewrite H2 H.
Qed.

Lemma nth_add_setdiff d k (P1 : intpartn d) (P : intpartn (d + k)) :
  size P <= n -> size P1 <= n -> vb_strip P1 P ->
  forall i,
  nth 0 [seq (mpart P1) i0 + (mesym1 (setdiff P1 P)) i0 | i0 <- enum 'I_n] i =
  nth 0 P i.
Proof.
  move=> Hsz Hsz1 /(vb_stripP (intpartnP _) (intpartnP _)) Hstr i.
  case: (ssrnat.ltnP i n) => Hi; first last.
    rewrite !nth_default //.
    - exact: leq_trans Hsz Hi.
    - by rewrite size_map size_enum_ord.
  have H0 : 0 < n by apply: (leq_ltn_trans _ Hi).
  rewrite !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
  rewrite inE /mpart ltnNge Hsz1 /= mnmE (nth_enum_ord (Ordinal H0) Hi).
  case: ssrnat.ltnP => H /=; rewrite ?addn0 ?addn1.
  - apply anti_leq; rewrite H /=.
    by have := Hstr i => /andP [].
  - apply anti_leq; rewrite H /= andbT.
    by have := Hstr i => /andP [].
Qed.

Lemma nohasincr_setdiff d k (P1 : intpartn d) (P : intpartn (d + k)) :
  size P <= n -> size P1 <= n -> vb_strip P1 P -> ~~ hasincr P1 (setdiff P1 P).
Proof.
  move=> Hsz Hsz1 Hstrip.
  apply/hasPn => i; rewrite mem_iota add0n => /andP [] _ Hi.
  rewrite /mnm_add [val _]/= !nth_add_setdiff //.
  rewrite eq_sym ltn_eqF // ltnS.
  have := (is_partP _ (intpartnP P)) => [] [] _.
  by apply.
Qed.

Lemma add_mesymK d k (P1 : intpartn d) :
  size P1 <= n ->
  {in [pred P : intpartn (d + k) | vb_strip P1 P && (size P <= n)],
  cancel (fun P : intpartn (d + k) => setdiff P1 (val P)) (add_mesym k P1)}.
Proof.
  move=> Hsz1 P /=; rewrite inE => /andP [] Hstrip Hsz.
  have:= (vb_stripP (intpartnP _) (intpartnP _) Hstrip) => Hstr.
  apply/eqP/(part_eqP (intpartnP _) (intpartnP _)) => i.
  rewrite /add_mesym /=.
  rewrite Hsz1 card_setdiff // eq_refl /= nohasincr_setdiff //.
  by rewrite nth_rem_trail0 nth_add_setdiff.
Qed.

(* TODO : Fixme *)
Local Open Scope ring_scope.

Theorem altSchur_mpart_elementary d (P1 : intpartn d) k :
  size P1 <= n ->
  (altSchur (mpart P1)) * 'e_k =
  \sum_(P : intpartn (d + k) | vb_strip P1 P && (size P <= n)) altSchur (mpart P).
Proof.
  rewrite altSchur_elementary => Hsz.
  rewrite (bigID (hasincr P1)) /=.
  rewrite (eq_bigr (fun x => 0)); last by move=> i /andP [] _ /hasincr0.
  rewrite sumr_const mul0rn add0r.
  rewrite (eq_bigr (fun h => altSchur (mpart (add_mesym k P1 h)))); first last.
    move=> i /andP [] Hk Hincr; by rewrite add_mesymE.
  rewrite (reindex_onto _ _ (add_mesymK Hsz)).
  apply eq_bigl => S; rewrite inE.
  apply (sameP idP); apply (iffP idP).
  - move=> /andP [] /andP [] Hstrip Hszle /eqP HS.
    rewrite -HS card_setdiff // eq_refl andTb.
    exact: nohasincr_setdiff.
  - move=> H; apply/andP; split; first (apply/andP; split).
    + apply/(vb_stripP (intpartnP _) (intpartnP _)) => i /=.
      rewrite Hsz H /= nth_rem_trail0.
      case: (ssrnat.ltnP i n) => Hi; first last.
        rewrite !nth_default //; first last.
        - exact: leq_trans Hsz Hi.
        - by rewrite size_map size_enum_ord.
      have H0 : 0 < n by apply: (leq_ltn_trans _ Hi).
      rewrite (nth_map (Ordinal H0)) ?size_enum_ord // !mnmE.
      rewrite /mpart ltnNge Hsz /= mnmE (nth_enum_ord (Ordinal H0) Hi).
      by case: (_ \in _); rewrite ?addn0 ?addn1 leqnn ltnW.
    + rewrite /add_mesym /= Hsz H /=.
      apply (leq_trans (size_rem_trail0 _)).
      by rewrite size_map size_enum_ord.
    + rewrite /setdiff; apply/eqP; rewrite -setP => i.
      rewrite inE /= Hsz H /= nth_rem_trail0.
      have H0 : 0 < n by apply: (leq_ltn_trans _ (ltn_ord i)).
      rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
      rewrite nth_ord_enum /= (mnm_nth 0) /= mnmE.
      rewrite /mpart (ltnNge n _) Hsz /=.
      rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
      rewrite nth_ord_enum.
      by case: (i \in S); rewrite ?addn0 ?addn1 ?ltnSn ?ltnn.
Qed.

Hypothesis Hn : n != 0%N.

(* pose part0 := @IntPartN 0 [::] is_true_true. *)

Theorem altSchurE d (P : intpartn d) :
  size P <= n -> altSchur (mpart P) = altSchur 0 * Schur Hn R P.
Proof.
  suff {d P} H : forall b d, d <= b -> forall (P : intpartn d),
    size P <= n -> altSchur (mpart P) = altSchur 0 * Schur Hn R P by apply: (H d).
  elim=> [ |b IHb] d Hd P.
    move: Hd; rewrite leqn0 => /eqP Hd; subst d.
    rewrite Schur0 mulr1 => _; congr altSchur.
    rewrite intpartn0 /mpart /= mnmP => i; by rewrite !mnmE /=.
  case: (leqP d b) => Hdb; first exact: (IHb _ Hdb).
  have {Hd Hdb} Hd : d = b.+1 by apply anti_leq; rewrite Hd Hdb.
  subst d => HszP.
  pose k := head 1%N (conj_intpartn P).
  pose p1 := behead (conj_intpartn P); pose d1 := sumn p1.
  have Hk : (d1 + k = b.+1)%N.
    have:= intpartn_sumn (conj_intpartn P).
    rewrite /d1 /k /p1 /=.
    case: (conj_part P) => [//= | [//= | c0] c] /=; by rewrite addnC.
  have Hd1 : d1 <= b.
    rewrite -ltnS -Hk.
    have:= part_head_non0 (intpartnP (conj_intpartn P)).
    rewrite -/k; case k => //= k' _.
    rewrite addnS ltnS; exact: leq_addr.
  have Hp1 : is_part_of_n d1 p1 by rewrite /= /d1 eq_refl is_part_behead.
  pose P1 := IntPartN Hp1.
  have HszP1 : size (conj_intpartn P1) <= n.
    rewrite size_conj_part //.
    apply: (leq_trans _ HszP); rewrite /= /p1.
    have := size_conj_part (intpartnP (conj_intpartn P)).
    rewrite conj_partK // => ->.
    have:= (intpartnP (conj_intpartn P)) => /=.
    by case: (conj_part P) => [| c0 [| c1 c]] //= /andP [].
  have {IHb} Hrec := IHb _ Hd1 (conj_intpartn P1) HszP1.
  have := altSchur_mpart_elementary k HszP1.
  rewrite Hrec.
  
Definition antim (s : seq nat) : 'M[ {mpoly R[n]} ]_n :=
  \matrix_(i, j < n) 'X_i ^+ (nth 0 s j + (n - 1) - j)%N.
Definition Vandmx : 'M[ {mpoly R[n]} ]_n := \matrix_(i, j < n) 'X_i ^+ (n - 1 - j).
Definition Vandet := \det Vandmx.

Lemma Vandmx_antimE : Vandmx = antim [::].
Proof. rewrite /Vandmx /antim -matrixP => i j /=; by rewrite !mxE nth_default. Qed.

Lemma altSchur_detE s : altSchur s = \det (antim s).
Proof.
  rewrite /altSchur /alternpol.
  have H : injective (fun (f : 'S_n) => (f ^-1)%g) by apply inv_inj; exact: invgK.
  rewrite (reindex_inj H) /=.
  apply eq_bigr => p _; rewrite odd_permV.
  rewrite scaler_sign -mulr_sign.
  congr (_ * _).
  rewrite (eq_bigr (fun j => 'X_j ^+ (nth 0%N s (p j) + (n - 1) - (p j)))); first last.
    by move => i _; rewrite mxE.
  rewrite msymX mpolyXE_id.
  apply eq_bigr => i _; congr (_ ^+ _).
  rewrite mnmE /= mnmDE invgK.
  rewrite mnmE (mnm_nth 0%N).
  rewrite subn1 addnBA //.
  have Hi := ltn_ord (p i); by rewrite -ltnS (ltn_predK Hi).
Qed.

Lemma tperm_antim_xrow s i j :
 msym (tperm i j) (\det (antim s)) = \det (xrow i j (antim s)).
Proof.
  rewrite /antim -det_map_mx /=; congr (\det _).
  rewrite /map_mx -matrixP => r c /=.
  rewrite !mxE rmorphX /= msymX /=.
  congr (mpolyX _ _ ^+ _) => {c}.
  rewrite mnmP => u /=; rewrite !mnm_tnth /=.
  rewrite !tnth_map /= tnth_ord_tuple /= mnm1E tpermV.
  congr (nat_of_bool _); apply (sameP idP); apply (iffP idP).
  - by move/eqP <-; rewrite tpermK.
  - by move/eqP ->; rewrite tpermK.
Qed.

Lemma antimP s : \det (antim s) \is antisym.
Proof.
  apply/isantisym_tpermP => i j.
  case: (altP (i =P j)) => [-> | Hij] /=; first by rewrite tperm1 msym1m.
  rewrite tperm_antim_xrow xrowE det_mulmx det_perm.
  by rewrite odd_tperm Hij /= expr1 mulN1r.
Qed.

Corollary Vandet_anti : Vandet \is antisym.
Proof. rewrite /Vandet Vandmx_antimE. exact: antimP. Qed.

Lemma antim_add1_0 (s : seq nat) i :
  i.+1 < n -> (nth 0%N s i).+1 = nth 0%N s i.+1 -> \det (antim s) = 0.
Proof.
  move=> Hi1n; have Hi : i < n by rewrite ltnW.
  pose i0 := Ordinal Hi; pose i1 := Ordinal Hi1n.
  have : i0 != i1.
    apply (introN idP) => /eqP H.
    have := erefl (val i0); rewrite {2}H /= => /eqP.
    by rewrite ieqi1F.
  move => H Heq; rewrite -det_tr.
  apply: (determinant_alternate H) => j.
  by rewrite /antim !mxE -Heq /= addSn subSS.
Qed.

End VandermondeDet.
