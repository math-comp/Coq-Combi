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
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype finfun tuple bigop ssralg ssrint.
From mathcomp Require Import finset fingroup perm.
From SsrMultinomials Require Import ssrcomplements poset freeg bigenough mpoly.

Require Import tools combclass ordtype sorted partition tableau skewtab.
Require Import presentSn antisym sympoly freeSchur therule.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Section Alternant.

Variable n : nat.
Variable R : comRingType.

Local Notation rho := (rho n).
Local Notation "''e_' k" := (@mesym n R k)
                              (at level 8, k at level 2, format "''e_' k").
Local Notation "''a_' k" := (@alternpol n R 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").

Lemma rho_uniq : uniq rho.
Proof using .
suff : perm_eq rho (iota 0 n) by move/perm_eq_uniq ->; exact: iota_uniq.
rewrite rho_iota perm_eq_sym; exact: perm_eq_rev.
Qed.

Lemma alt_uniq_non0 (m : 'X_{1..n}) : uniq m -> 'a_m != 0.
Proof using .
move=> Huniq.
suff : mcoeff m 'a_m == 1.
  apply contraL => /eqP ->; rewrite mcoeff0 eq_sym.
  exact: oner_neq0.
rewrite /alternpol (reindex_inj invg_inj) /=.
rewrite raddf_sum /= (bigID (pred1 1%g)) /=.
rewrite big_pred1_eq odd_permV odd_perm1 expr0 scale1r invg1 msym1m.
rewrite mcoeffX eq_refl /=.
rewrite (eq_bigr (fun _ => 0)); first by rewrite big1_eq addr0.
move=> s Hs; rewrite mcoeffZ msymX mcoeffX invgK.
suff : [multinom m (s i) | i < n] != m.
  move=> /negbTE -> /=; by rewrite mulr0.
move: Hs; apply contra => /eqP; rewrite mnmP => Heq.
apply/eqP; rewrite -permP => i; rewrite perm1; apply val_inj => /=.
have /eqP := Heq i; rewrite !mnmE !(mnm_nth 0).
rewrite nth_uniq; last exact: Huniq.
- by move=> /eqP ->.
- rewrite size_tuple; exact: ltn_ord.
- rewrite size_tuple; exact: ltn_ord.
Qed.

Lemma alt_rho_non0 : 'a_rho != 0.
Proof using . exact: alt_uniq_non0 (rho_uniq). Qed.

Lemma alt_alternate (m : 'X_{1..n}) (i j : 'I_n) :
  i != j -> m i = m j -> 'a_m = 0.
Proof using .
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

Lemma alt_add1_0 (m : 'X_{1..n}) i :
  (nth 0%N m i).+1 = nth 0%N m i.+1 -> 'a_(m + rho) = 0.
Proof using .
move=> Heq.
have Hi1n : i.+1 < n.
  rewrite ltnNge; apply (introN idP) => Hi.
  move: Heq; by rewrite [RHS]nth_default // size_tuple.
have Hi : i < n by rewrite ltnW.
pose i0 := Ordinal Hi; pose i1 := Ordinal Hi1n.
have /alt_alternate : i0 != i1.
  apply (introN idP) => /eqP/(congr1 val)/=/eqP.
  by rewrite ieqi1F.
apply.
rewrite !mnmDE !mnmE !(mnm_nth 0%N) -Heq -(mnm_nth 0%N m i0).
rewrite addSn -addnS subn1 /= subnS prednK //.
have -> : (n.-1 - i = n - i.+1)%N.
  case: n Hi1n Hi {i0 i1} => [//= | n' _] /=.
  by rewrite subSS.
by rewrite subn_gt0.
Qed.


Lemma alt_syme (m : 'X_{1..n}) k :
  'a_(m + rho) * 'e_k =
  \sum_(h : {set 'I_n} | #|h| == k) 'a_(m + mesym1 h + rho).
Proof using .
rewrite /alternpol exchange_big /=.
rewrite mulr_suml; apply eq_bigr => s _.
rewrite -(issymP _ (mesym_sym n R k) s) mesymE.
rewrite (raddf_sum (msym_additive _ _)) /=.
rewrite mulr_sumr; apply eq_bigr => h _.
rewrite -scalerAl -msymM -mpolyXD.
by rewrite -!addmA [(mesym1 h + rho)%MM]addmC.
Qed.

Local Open Scope nat_scope.

Section HasIncr.

Variables (d k : nat) (la : intpartn d) (h : {set 'I_n}).

Definition hasincr :=
  has (fun i => (nth 0 (mpart la + mesym1 h)%MM i).+1 ==
                 nth 0 (mpart la + mesym1 h)%MM i.+1) (iota 0 n.-1).

Lemma hasincr0 : hasincr -> 'a_(mpart la + mesym1 h + rho) = 0%R.
Proof using . move=> /hasP [] i _ /eqP; exact: alt_add1_0. Qed.

Lemma not_hasincr_part :
  size la <= n -> ~~ hasincr ->
  is_part_of_n (d + #|h|) (rem_trail0 (mpart la + mesym1 h)%MM).
Proof using .
move=> Hsz /hasPn H.
rewrite /mpart Hsz.
apply/andP; split.
- rewrite sumn_rem_trail0.
  rewrite -(@sum_iota_sumnE _ n); last by rewrite size_map size_enum_ord.
  rewrite big_mkord.
  rewrite (eq_bigr (fun i : 'I_n => nth 0 la i + mesym1 h i)%N); first last.
    move=> i _.
    have H0 : 0 < n by apply: (leq_ltn_trans _ (ltn_ord i)).
    rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
    rewrite nth_ord_enum /= (mnm_nth 0) /=.
    rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
    by rewrite nth_ord_enum.
  rewrite big_split /=; apply/eqP; congr (_ + _)%N.
  + rewrite -{2}(intpartn_sumn la).
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
  have H0 : 0 < n by apply: (leq_ltn_trans _ Hi1).
  rewrite /mpart Hsz !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
  rewrite !nth_enum_ord //.
  set bi := (_ \in h); set bi1 := (_ \in h).
  have:= is_partP _ (intpartnP la) => [] [] _ H.
  have {H} := H i; move: (i.+1) => j /= H1.
  case: bi bi1 => [] [] /=; rewrite ?addn1 ?addn0 => H2.
  + by rewrite ltnS.
  + exact: (leq_trans H1).
  + by rewrite ltn_neqAle -eqSS eq_sym H2 H1.
  + exact: H1.
Qed.

Let add_mpart_mesym :=
  if [&& size la <= n, #|h| == k & ~~ hasincr]
  then (rem_trail0 (mpart la + mesym1 h)%MM)
  else rowpart (d + k) (* unused *).
Lemma add_mpart_mesymP : is_part_of_n (d + k) add_mpart_mesym.
Proof using la h.
rewrite /add_mpart_mesym.
case: (boolP [&& _, _ & _]) => [/and3P [] Hsz /eqP <- Hincr | _].
- exact: not_hasincr_part.
- exact: rowpartnP.
Qed.
Definition add_mesym : intpartn (d + k) := IntPartN add_mpart_mesymP.

Lemma add_mesymE :
  size la <= n -> #|h| == k -> ~~ hasincr ->
  mpart add_mesym = (mpart la + mesym1 h)%MM.
Proof using .
rewrite /add_mesym /add_mpart_mesym => Hsz /= /eqP <- Hincr.
rewrite /mpart Hincr Hsz eq_refl /=.
set S := (map _ _).
rewrite mnmP => i.
rewrite (leq_trans (size_rem_trail0 S)); last by rewrite size_map size_enum_ord.
rewrite mnmE nth_rem_trail0.
have H0 : 0 < n by apply: (leq_ltn_trans _ (ltn_ord i)).
rewrite !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
by rewrite !nth_ord_enum.
Qed.

End HasIncr.

Definition setdiff (la mu : seq nat) : {set 'I_n} :=
  [set i : 'I_n | nth 0 la i < nth 0 mu i].

Lemma card_setdiff d k (la : intpartn d) (mu : intpartn (d + k)) :
  size mu <= n -> size la <= n -> vb_strip la mu -> #|setdiff la mu| = k.
Proof using .
move=> Hszmu Hszla /(vb_stripP (intpartnP _) (intpartnP _)) Hstrip.
rewrite /setdiff -sum1dep_card.
rewrite -{2}(addKn d k).
rewrite -{4}(intpartn_sumn la) -{2}(intpartn_sumn mu).
rewrite -(sum_iota_sumnE Hszmu) -(sum_iota_sumnE Hszla).
set rhs := RHS.
have {rhs} -> : rhs = (\sum_(0 <= i < n) (nth 0 mu i - nth 0 la i)).
  rewrite /rhs {rhs} /index_iota subn0.
  elim: n {Hszmu Hszla} => [//= | i IHi]; first by rewrite !big_nil.
  rewrite -addn1 iota_add /= add0n !big_cat !big_cons !big_nil /= !addn0.
  rewrite subnDA subnAC -addnBA; last by have := Hstrip i => /andP [].
  rewrite addnC [RHS]addnC -IHi {IHi}.
  rewrite addnBA //.
  elim: i => [//= | i IHi]; first by rewrite !big_nil.
  rewrite -addn1 iota_add /= add0n !big_cat !big_cons !big_nil /= !addn0.
  apply leq_add; first exact: IHi.
  by have := Hstrip i => /andP [].
rewrite big_mkord.
rewrite [RHS](bigID (fun i : 'I_n => nth 0 la i < nth 0 mu i)) /=.
rewrite [X in (_ = _ + X)]big1 ?addn0; first last.
  move=> i; by rewrite -leqNgt /leq => /eqP.
apply eq_bigr => i H.
have:= Hstrip i => /andP [] H1 H2.
suff -> : nth 0 mu i = (nth 0 la i).+1 by rewrite subSn // subnn.
apply anti_leq; by rewrite H2 H.
Qed.

Lemma nth_add_setdiff d k (la : intpartn d) (mu : intpartn (d + k)) :
  size mu <= n -> size la <= n -> vb_strip la mu ->
  forall i,
  nth 0 [seq (mpart la) i0 + (mesym1 (setdiff la mu)) i0 | i0 <- enum 'I_n] i =
  nth 0 mu i.
Proof using .
move=> Hszmu Hszla /(vb_stripP (intpartnP _) (intpartnP _)) Hstrip i.
case: (ssrnat.ltnP i n) => Hi; first last.
  rewrite !nth_default //.
  - exact: leq_trans Hszmu Hi.
  - by rewrite size_map size_enum_ord.
have H0 : 0 < n by apply: (leq_ltn_trans _ Hi).
rewrite /mpart Hszla.
rewrite !(nth_map (Ordinal H0) 0) ?size_enum_ord // !mnmE.
rewrite inE /= (nth_enum_ord (Ordinal H0) Hi).
case: ssrnat.ltnP => H /=; rewrite ?addn0 ?addn1.
- apply anti_leq; rewrite H /=.
  by have := Hstrip i => /andP [].
- apply anti_leq; rewrite H /= andbT.
  by have := Hstrip i => /andP [].
Qed.

Lemma nohasincr_setdiff d k (la : intpartn d) (mu : intpartn (d + k)) :
  size mu <= n -> size la <= n ->
  vb_strip la mu -> ~~ hasincr la (setdiff la mu).
Proof using .
move=> Hszmu Hszla Hstrip.
apply/hasPn => i; rewrite mem_iota add0n => /andP [] _ Hi.
rewrite /mnm_add [val _]/= !nth_add_setdiff //.
rewrite eq_sym ltn_eqF // ltnS.
have := (is_partP _ (intpartnP mu)) => [] [] _.
by apply.
Qed.

Lemma add_mesymK d k (la : intpartn d) :
  size la <= n ->
  {in [pred mu : intpartn (d + k) | vb_strip la mu && (size mu <= n)],
  cancel (fun mu : intpartn (d + k) => setdiff la (val mu)) (add_mesym k la)}.
Proof using .
move=> Hszla mu /=; rewrite inE => /andP [] Hstrip Hsz.
have:= vb_stripP (intpartnP _) (intpartnP _) Hstrip => Hstr.
apply/eqP/(part_eqP (intpartnP _) (intpartnP _)) => i.
rewrite /add_mesym /=.
rewrite Hszla card_setdiff // eq_refl /= nohasincr_setdiff //.
by rewrite nth_rem_trail0 nth_add_setdiff.
Qed.


Theorem alt_mpart_syme d (la : intpartn d) k :
  size la <= n ->
  ('a_(mpart la + rho) * 'e_k =
  \sum_(mu : intpartn (d + k) | vb_strip la mu && (size mu <= n))
     'a_(mpart mu + rho))%R.
Proof using .
rewrite alt_syme => Hszla.
rewrite (bigID (hasincr la)) /=.
rewrite (eq_bigr (fun x => 0%R)); last by move=> i /andP [] _ /hasincr0.
rewrite sumr_const mul0rn add0r.
rewrite (eq_bigr (fun h => 'a_(mpart (add_mesym k la h) + rho))); first last.
  by move=> i /andP [] Hk Hincr; rewrite add_mesymE.
rewrite (reindex_onto _ _ (add_mesymK Hszla)).
apply eq_bigl => S; rewrite inE -andbA.
apply/idP/and3P => [H | [Hstrip Hszle /eqP HS]].
- split.
  + apply/(vb_stripP (intpartnP _) (intpartnP _)) => i /=.
    rewrite Hszla H /= nth_rem_trail0.
    case: (ssrnat.ltnP i n) => Hi; first last.
      rewrite !nth_default //; first last.
      - exact: leq_trans Hszla Hi.
      - by rewrite size_map size_enum_ord.
    have H0 : 0 < n by apply: (leq_ltn_trans _ Hi).
    rewrite /mpart Hszla /= (nth_map (Ordinal H0)) ?size_enum_ord // !mnmE.
    rewrite (nth_enum_ord (Ordinal H0) Hi).
    by case: (_ \in _); rewrite ?addn0 ?addn1 leqnn ltnW.
  + rewrite /add_mesym /= Hszla H /=.
    apply (leq_trans (size_rem_trail0 _)).
    by rewrite size_map size_enum_ord.
  + rewrite /setdiff; apply/eqP/setP => i.
    rewrite inE /= Hszla H /= nth_rem_trail0.
    have H0 : 0 < n by apply: (leq_ltn_trans _ (ltn_ord i)).
    rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
    rewrite /mpart Hszla nth_ord_enum /= (mnm_nth 0) /= mnmE.
    rewrite (nth_map (Ordinal H0)); last by rewrite size_enum_ord.
    rewrite nth_ord_enum.
    by case: (i \in S); rewrite ?addn0 ?addn1 ?ltnSn ?ltnn.
- rewrite -HS card_setdiff // eq_refl andTb.
  exact: nohasincr_setdiff.
Qed.

Lemma vb_strip_rem_col0 d (la : intpartn d) :
  vb_strip (conj_part (behead (conj_part la))) la.
Proof using .
rewrite -{2}(conj_intpartnK la) /=.
have Hc : is_part (conj_part la) by apply is_part_conj.
apply hb_strip_conj => //; first by apply is_part_behead.
elim: {d la} (conj_part la) Hc => [//=| s0 s IHs] /= /andP [] H0 /IHs {IHs}.
case: s H0 => [//=| s1 s] /= -> ->.
by rewrite leqnn.
Qed.


Lemma vb_strip_lex (d1 k : nat) (la : intpartn (d1 + k)) p :
  vb_strip p la ->
  sumn p = d1 ->
  is_part p -> (val la <= incr_first_n p k)%Ord.
Proof using .
rewrite /=.
elim: p d1 k la => [| p0 p IHla] d1 k la Hstr.
  have {Hstr} Hstr := vb_stripP (is_true_true : is_part [::]) (intpartnP _) Hstr.
  move=> Hd1 _; subst d1.
  suff /= -> : val la = nseq k 1%N by [].
  case: la Hstr => la /=; rewrite add0n => /andP [] /eqP.
  elim: la k => [//= | s0 s IHs] /= k Hk; first by rewrite -Hk.
  rewrite -/(is_part (s0 :: s)) => Hpart Hstr.
  have Hs0 : s0 = 1.
    have := Hstr 0 => /=.
    have /= := part_head_non0 Hpart.
    by case s0 => [| [| s0']].
  subst s0; rewrite -Hk add1n /= {1}(IHs (sumn s)) //.
  - exact: (is_part_consK Hpart).
  - move=> i; have /= := Hstr i.+1.
    by rewrite !nth_nil.
case: la Hstr => la Hla /= Hstr.
case: k Hla => [| k] Hla Hd1; subst d1;
               rewrite -/(is_part (p0 :: p)) /= => /andP [] _ Hp.
  have Hincl := vb_strip_included Hstr.
  move: Hla; rewrite addn0 /= -/(sumn (p0 :: p)) => /andP [] /eqP /esym Heq Hla.
  by rewrite (included_sumnE Hla Hincl Heq).
case: la Hstr Hla => [//= |s0 la] /= /andP [] H0 Hstrip.
move=> /andP [] /eqP Heq /andP [] _ Hs.
rewrite leqXE /= ltnXnatE ltnS.
case: (leqP s0 p0) => //= Hp0.
have Hs0 : s0 = p0.+1.
  apply anti_leq; rewrite Hp0.
  by move: H0 => /andP [] _ ->.
subst s0; rewrite eq_refl /= {Hp0}.
move: Heq; rewrite addSn addnS => /eqP; rewrite eqSS -addnA => /eqP /addnI Heq.
have Hla : is_part_of_n (sumn p + k)%N la.
  by rewrite /= Heq eq_refl Hs.
have /= := IHla _ _ (IntPartN Hla).
by rewrite leqXE /=; apply.
Qed.

End Alternant.


Section SchurAlternantDef.

Variable (n0 : nat) (R : comRingType).
Local Notation n := (n0.+1).
Local Notation "''s_' k" := (Schur n0 R k)
                              (at level 8, k at level 2, format "''s_' k").
Local Notation rho := (rho n).
Local Notation "''a_' k" := (@alternpol n R 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").

Lemma Schur_cast d d' (la : intpartn d) (Heq : d = d') :
  's_la = Schur n0 R (cast_intpartn Heq la).
Proof using . subst d'; by congr Schur. Qed.

Theorem alt_SchurE d (la : intpartn d) :
  size la <= n -> 'a_rho * 's_la = 'a_(mpart la + rho).
Proof using .
suff {d la} H : forall b d, d <= b -> forall (la : intpartn d),
  size la <= n -> 'a_rho * 's_la = 'a_(mpart la + rho) by apply: H.
elim=> [|b IHb] d Hd la.
  move: Hd; rewrite leqn0 => /eqP Hd; subst d.
  rewrite Schur0 mulr1 -{1}(add0m rho)=> _; congr 'a_(_ + rho).
  by rewrite intpartn0 /mpart /= mnmP => i; rewrite !mnmE /=.
case: (leqP d b) => Hdb; first exact: (IHb _ Hdb).
have {Hd Hdb} Hd : d = b.+1 by apply anti_leq; rewrite Hd Hdb.
elim/(finord_wf (T := IntPartNLex.intpartnlex_finPOrdType d)) : la =>
    la IHla Hszla.
pose k := head 1%N (conj_intpartn la).
pose p1 := behead (conj_intpartn la); pose d1 := sumn p1.
have Hk : (d = d1 + k)%N.
  have:= intpartn_sumn (conj_intpartn la).
  rewrite /d1 /k /p1 /=.
  by case: (conj_part la) => [| [//= | c0] c] /=; rewrite Hd // addnC.
have Hd1 : d1 <= b.
  rewrite -ltnS -Hd Hk.
  have:= part_head_non0 (intpartnP (conj_intpartn la)).
  rewrite -/k; case k => //= k' _.
  by rewrite addnS ltnS; exact: leq_addr.
have p1P : is_part_of_n d1 p1 by rewrite /= /d1 eq_refl is_part_behead.
pose mu := IntPartN p1P.
have Hszmu : size (conj_intpartn mu) <= n.
  rewrite size_conj_part //.
  apply: (leq_trans _ Hszla); rewrite /= /p1.
  have := size_conj_part (intpartnP (conj_intpartn la)).
  rewrite conj_partK // => ->.
  have:= (intpartnP (conj_intpartn la)) => /=.
  by case: (conj_part la) => [| c0 [| c1 c]] //= /andP [].
have := alt_mpart_syme R k Hszmu.
have {IHb Hszmu Hd1} <- := IHb _ Hd1 (conj_intpartn mu) Hszmu.
rewrite -mulrA Pieri_syme.
rewrite (bigID (fun P0 : intpartn (d1 + k) => (size P0 <= n))) /= addrC.
rewrite big1 ?add0r; first last.
  by move=> i /andP [] _; rewrite -ltnNge; exact: Schur_oversize.
rewrite mulr_sumr.
pose la' := cast_intpartn Hk la.
rewrite (bigID (pred1 la')) [X in _ = X](bigID (pred1 la')) /=.
set prd := BIG_P.
have Hprd : prd =1 pred1 la'.
  rewrite {}/prd => nu /=.
  case: eqP => [-> | _]; rewrite ?andbT ?andbF // {nu}.
  rewrite cast_intpartnE {la' mu d1 Hk p1P} Hszla andbT /p1 /=.
  exact: vb_strip_rem_col0.
rewrite !(eq_bigl _ _ Hprd) {Hprd prd} /= !big_pred1_eq cast_intpartnE.
set A := (X in _ + X); set B := (X in _ = _ + X).
suff -> : A = B by move=> /addIr <- {A B}; rewrite -Schur_cast.
apply eq_bigr => {A B} nu /andP [] /andP [] Hstrip Hsznu Hnu.
pose nu' := cast_intpartn (esym Hk) nu.
have Hlex : (val nu' < la)%Ord.
  rewrite cast_intpartnE /= {nu'}.
  rewrite ltnX_neqAleqX; apply/andP; split.
    move: Hnu; apply contra => /eqP H.
    by apply/eqP; apply val_inj; rewrite cast_intpartnE.
  rewrite {Hnu Hsznu la'}.
  have /= -> : val la = incr_first_n (conj_part p1) k.
    move: Hk; rewrite /d1 /p1 /= -{2}(conj_intpartnK la) /=.
    rewrite -{1}(intpartn_sumn (conj_intpartn la)) /=.
    case: (conj_part la) => [//= | p0 p] /=; first by rewrite add0n => <-.
    rewrite addnC -{2}(addKn (sumn p) k) => <-.
    by rewrite addKn.
  have:= intpartnP (conj_intpartn mu).
  have /= {Hk p1P mu} := intpartn_sumn (conj_intpartn mu).
  exact: vb_strip_lex.
have Hsznu' : size nu' <= n by rewrite cast_intpartnE.
have := IHla nu' Hlex Hsznu'.
rewrite -Schur_cast => ->.
by rewrite cast_intpartnE.
Qed.

End SchurAlternantDef.



Section IdomainSchurSym.

Variable (n0 : nat) (R : idomainType).
Local Notation n := (n0.+1).
Local Notation "''s_' k" := (Schur n0 R k)
                             (at level 8, k at level 2, format "''s_' k").
Local Notation rho := (rho n).
Local Notation "''a_' k" := (@alternpol n R 'X_[k])
                              (at level 8, k at level 2, format "''a_' k").

Theorem alt_uniq d (la : intpartn d) (s : {mpoly R[n]}) :
  size la <= n -> 'a_rho * s = 'a_(mpart la + rho) -> s = 's_la.
Proof using . by move=> /(alt_SchurE R) <- /(mulfI (alt_rho_non0 n R)). Qed.

Theorem Schur_sym_idomain d (la : intpartn d) : 's_la \is symmetric.
Proof using .
case: (leqP (size la) n) => [Hla|].
- have := alt_anti R (mpart la + rho).
  rewrite -(alt_SchurE _ Hla) -sym_antiE //; last exact: alt_anti.
  exact: alt_rho_non0.
- move/Schur_oversize ->; exact: rpred0.
Qed.

End IdomainSchurSym.


Section RingSchurSym.

Variable (n0 : nat) (R : ringType).
Local Notation n := (n0.+1).
Local Notation "''s_' k" := (Schur n0 R k)
                              (at level 8, k at level 2, format "''s_' k").

Theorem Schur_sym d (la : intpartn d) : 's_la \is symmetric.
Proof using .
have -> : 's_la = map_mpoly intr (Schur _ [ringType of int] la).
  rewrite /Schur /polylang /commword raddf_sum /=; apply eq_bigr => i _ /=.
  rewrite rmorph_prod /=; apply eq_bigr => {i} i _ ; by rewrite map_mpolyX.
apply/issymP => s.
have:= Schur_sym_idomain n0 int_iDomain la => /issymP/(_ s) {2}<-.
by rewrite msym_map_mpoly.
Qed.

Definition syms d (la : intpartn d) : {sympoly R[n]} := SymPoly (Schur_sym la).

End RingSchurSym.

Notation "''s[' la ]" := (syms _ _ la)
                         (at level 8, la at level 2, format "''s[' la ]").


Section ChangeRing.

Variables R S : comRingType.
Variable mor : {rmorphism R -> S}.

Variable n : nat.

Lemma map_syms d (la : intpartn d) :
  map_sympoly (n := n.+1) mor 's[la] = 's[la].
Proof.
apply val_inj; rewrite /= rmorph_sum /=.
apply eq_bigr => X _; rewrite rmorph_prod; apply eq_bigr => /= i _.
by rewrite map_mpolyX.
Qed.

End ChangeRing.

(* TODO : contribute to Pierre-Yves Repo *)
Section MPoESymHomog.

Variable (n0 : nat) (R : comRingType).
Local Notation n := (n0.+1).

Implicit Types p q r : {mpoly R[n]}.
Implicit Type m : 'X_{1..n}.

Lemma prod_homog l (dt : l.-tuple nat) (mt : l.-tuple {mpoly R[n]}) :
  (forall i : 'I_l, tnth mt i \is (tnth dt i).-homog) ->
  \prod_(i <- mt) i \is (\sum_(i <- dt) i).-homog.
Proof using .
elim: l dt mt => [| l IHl] dt mt H.
  rewrite tuple0 big_nil tuple0 big_nil; exact: dhomog1.
case/tupleP: dt H => d dt.
case/tupleP: mt => p mt H /=.
rewrite !big_cons; apply dhomogM.
  have := H ord0 => /=; by rewrite (tnth_nth 0) (tnth_nth 0%N).
apply IHl => i.
have := H (inord i.+1).
rewrite !(tnth_nth 0) !(tnth_nth 0%N) /=.
by rewrite !inordK; last exact: (ltn_ord i).
Qed.

Local Notation E := [tuple mesym n R i.+1  | i < n].

Lemma homog_X_mPo_elem (m : 'X_{1..n}) :
  'X_[m] \mPo E \is (mnmwgt m).-homog.
Proof using .
rewrite comp_mpolyX.
pose dt := [tuple (i.+1 * (m i))%N | i < n].
pose mt := [tuple (mesym n R i.+1) ^+ m i | i < n] : n.-tuple {mpoly R[n]}.
rewrite (eq_bigr (fun i : 'I_n => tnth mt i)); first last.
  by move=> i _ /=; rewrite !tnth_mktuple.
rewrite -(big_tuple _ _ mt xpredT id).
rewrite /mnmwgt (eq_bigr (fun i : 'I_n => tnth dt i)); first last.
  by move=> i _ /=; rewrite !tnth_mktuple mulnC.
rewrite -(big_tuple _ _ dt xpredT id).
apply prod_homog => i.
rewrite !tnth_mktuple {mt dt}; apply: dhomogMn.
exact: mesym_homog.
Qed.

Lemma pihomog_mPo p d :
  pihomog [measure of mdeg] d (p \mPo E) =
  (pihomog [measure of mnmwgt] d p) \mPo E.
Proof using .
elim/mpolyind: p => [| c m p Hm Hc IHp] /=; first by rewrite !linear0.
rewrite !linearP /= {}IHp; congr (c *: _ + _).
case: (altP (mnmwgt m =P d)) => H.
- have/eqP := H; rewrite -(dhomogX R) => /pihomog_dE ->.
  have:= homog_X_mPo_elem m; by rewrite H => /pihomog_dE ->.
- rewrite (pihomog_ne0 H (homog_X_mPo_elem m)).
  rewrite (pihomog_ne0 H); first by rewrite linear0.
  by rewrite dhomogX.
Qed.

Lemma mwmwgt_homogE (p : {mpoly R[n]}) d :
  p \is d.-homog for [measure of mnmwgt] = ((p \mPo E) \is d.-homog).
Proof using .
rewrite !homog_piE; rewrite pihomog_mPo.
by apply/idP/idP => [/eqP |  /eqP/msym_fundamental_un ] ->.
Qed.

Lemma sym_fundamental_homog (p : {mpoly R[n]}) (d : nat) :
  p \is symmetric -> p \is d.-homog ->
  { t | t \mPo E = p /\ t \is d.-homog for [measure of mnmwgt] }.
Proof.
move=> /sym_fundamental [t [Ht _]] Hhom.
exists (pihomog [measure of mnmwgt] d t); split.
- by rewrite -pihomog_mPo Ht pihomog_dE.
- exact: pihomogP.
Qed.

Lemma Schur_homog (d : nat) (la : intpartn d) : Schur n0 R la \is d.-homog.
Proof using .
rewrite /syms /= Schur_tabsh_readingE /polylang /commword.
apply rpred_sum => [[t Ht]] _ /=.
move: Ht => /eqP <-; elim: t => [| s0 s IHs]/=.
  rewrite big_nil; exact: dhomog1.
rewrite big_cons -(add1n (size s)); apply dhomogM; last exact: IHs.
by rewrite dhomogX /= mdeg1.
Qed.

Lemma syms_homog (d : nat) (la : intpartn d) : sympol (syms n0 R la) \is d.-homog.
Proof. exact: Schur_homog. Qed.

End MPoESymHomog.


Local Open Scope nat_scope.

Import IntPartNDom.
Import OrdNotations.

Section DefsKostkaMon.


Variables (d : nat) (la : intpartn d) (n : nat).
Implicit Type mu : 'X_{1..n.+1}.
Definition eval (w : seq 'I_n.+1) := [tuple count_mem i w | i < n.+1].
Definition KostkaTab mu := [set t : tabsh n la | eval (to_word t) == mu].
Definition KostkaMon mu := #|KostkaTab mu|.

Lemma sumn_eval w : sumn (eval w) = size w.
Proof.
rewrite -sumnE /eval big_tuple.
rewrite (eq_bigr (fun i => count_mem i w)) ?sum_count_mem ?count_predT //.
by move=> i _; rewrite !tnth_mktuple.
Qed.

Lemma KostkaMon_sumeval mu :
  mdeg mu != sumn la -> KostkaMon mu = 0.
Proof.
move=> H; apply/eqP; move: H.
apply contraR; rewrite cards_eq0 => /set0Pn /= [t].
rewrite /mdeg sumnE inE => /eqP <-{mu}.
by rewrite sumn_eval size_to_word /size_tab shape_tabsh.
Qed.

Lemma evalE (R : ringType) mu w :
  (\prod_(v <- w) 'X_v)@_mu = (eval w == mu)%:R :> R.
Proof.
rewrite -[X in X@_mu](big_map (fun i : 'I_n.+1 => (U_(i))%MM) xpredT).
rewrite /eval mpolyX_prod mcoeffX; congr (nat_of_bool _)%:R.
apply/eqP/eqP => [/(congr1 val) /= <- {mu}| H].
- elim: w => [| w0 w IHw] /=; first by rewrite big_nil.
  rewrite big_cons; apply eq_from_tnth => i.
  have:= (congr1 (fun t => tnth t i) IHw).
  rewrite !tnth_mktuple => ->.
  by rewrite mnmE -mnm_tnth.
- apply val_inj => /=; rewrite -H {mu H}.
  elim: w => [| w0 w IHw] /=; first by rewrite big_nil.
  rewrite big_cons; apply eq_from_tnth => i.
  have:= (congr1 (fun t => tnth t i) IHw).
  by rewrite !tnth_mktuple mnmE -mnm_tnth => ->.
Qed.

Lemma Kostka_Coeff (R : ringType) mu : (Schur n R la)@_mu = (KostkaMon mu)%:R.
Proof.
rewrite /Schur linear_sum /= /KostkaMon.
rewrite (bigID (fun t : tabsh n la => t \in KostkaTab mu)) /=.
rewrite addrC big1 ?add0r; first last.
  by move=> i; rewrite /KostkaTab inE evalE => /negbTE ->.
rewrite (eq_bigr (fun _ => 1%R)); first last.
  by move=> i; rewrite /KostkaTab inE evalE => /eqP ->; rewrite eq_refl.
by rewrite sumr_const; congr _%:R; apply eq_card => i.
Qed.

Lemma perm_KostkaMon mu1 mu2 :
  perm_eq mu1 mu2 -> KostkaMon mu1 = KostkaMon mu2.
Proof.
move=> /tuple_perm_eqP [s /val_inj Hs].
suff: Posz (KostkaMon mu1) = Posz (KostkaMon mu2) by move => [].
rewrite -!natz -!(Kostka_Coeff _ (Multinom _)).
set m1 := Multinom mu1.
set m2 := Multinom mu2.
have {Hs} -> : m1 = [multinom m2 (s i) | i < n.+1].
  apply val_inj => /=; rewrite Hs.
  by apply eq_from_tnth => i; rewrite tnth_mktuple.
by rewrite -mcoeff_sym (issymP _ (Schur_sym _ _ _)).
Qed.

Lemma tab_eval_partdom (t : tabsh n la) : partdom (eval (to_word t)) la.
Proof.
apply/partdomP => i; rewrite -(shape_tabsh t).
case: (ssrnat.leqP i n.+1) => [Hi| /ltnW Hi]; first last.
  rewrite !take_oversize ?size_tuple //; first last.
    by rewrite size_map (leq_trans (size_tabsh _)).
  by rewrite sumn_eval size_to_word.
rewrite sumn_take big_mkord (big_ord_widen _ _ Hi).
rewrite (eq_bigr (fun j => count_mem j (to_word t))); first last.
  by move=> /= j _; rewrite (nth_map ord0) ?size_enum_ord // nth_ord_enum.
rewrite sum_count_mem /= /to_word count_flatten map_rev sumn_rev.
rewrite -{1}(cat_take_drop i t) map_cat sumn_cat addnC.
rewrite -sumnE big_map big_seq big1 ?add0n; first last.
  move=> /= s Hs; rewrite -(nth_index [::] Hs).
  rewrite nth_drop; apply/eqP; rewrite -leqn0 leqNgt -has_count -all_predC.
  rewrite (eq_all (a2 := fun i0 : 'I_n.+1 => i <= i0)); first last.
    by move=> j /=; rewrite -leqNgt.
  have:= all_ltn_nth_tabsh t (i + index s (drop i t)); apply sub_all.
  by move=> j; apply (leq_trans (leq_addr _ _)).
rewrite /shape -map_take -!sumnE !big_map.
by apply leq_sum => /= j _; apply: count_size.
Qed.

Lemma KostkaMon_partdom mu : KostkaMon mu != 0 -> partdom mu la.
Proof.
rewrite cards_eq0 => /set0Pn [/= t]; rewrite inE => /eqP <-.
exact: tab_eval_partdom.
Qed.

End DefsKostkaMon.



Section KostkaEq.

Variables (d : nat) (la : intpartn d).

Lemma Kostka_rcons n (mu : 'X_{1..n.+1}) :
  KostkaMon la mu = KostkaMon la (mnmwiden mu).
Proof.
rewrite /KostkaMon /KostkaTab.
pose ext_fun := fun (t : tabsh n la) =>
              [seq [seq (widen_ord (leqnSn n.+1) i) | i <- r] | r <- t].
have extP t : is_tab_of_shape n.+1 la (ext_fun t).
  rewrite /is_tab_of_shape /=; apply/andP; split.
  - by rewrite -incr_tab.
  - rewrite -(shape_tabsh t) /shape /ext_fun -map_comp.
    by apply/eqP/eq_map => s; rewrite /= size_map.
have ext_inj : injective (fun t => TabSh (extP t)).
  move=> u v [] /= H; apply val_inj => /=.
  have:= H => /(congr1 size); rewrite !size_map => Hsz.
  apply (eq_from_nth (x0 := [::])) => // r Hr.
  move: H => /(congr1 (fun t => nth [::] t r)).
  rewrite !(nth_map [::]) -?Hsz // => H.
  have:= H => /(congr1 size); rewrite !size_map => Hsz1.
  apply (eq_from_nth (x0 := ord0)) => // c Hc.
  move: H => /(congr1 (fun t => nth ord0 t c)).
  rewrite !(nth_map ord0) -?Hsz1 //= => /(congr1 val) /= Heq.
  by apply val_inj.
rewrite -(card_imset _ ext_inj); congr #|pred_of_set _|.
apply/setP => /= t2; rewrite inE /=.
apply/imsetP/eqP => /= [[t ] | Hmu].
- rewrite inE /= => /eqP Hmu /(congr1 val)/= Heq.
  rewrite /eval; apply eq_from_tnth => i; rewrite tnth_mktuple.
  case: (ssrnat.ltnP i n.+1) => Hi.
  + rewrite [RHS](tnth_nth 0) /= nth_rcons size_tuple Hi -{}Hmu {}Heq /eval.
    rewrite (nth_map ord0) ?size_enum_ord //.
    have -> : to_word (ext_fun t) =
              [seq widen_ord (leqnSn n.+1) i | i <- to_word t].
      by rewrite /ext_fun /to_word -map_rev map_flatten.
    case: i Hi => [i Hin] /= Hi.
    rewrite count_map; apply eq_count => /= [] [j Hj] /=.
    by apply/eqP/eqP => /(congr1 val) /= Heq;
                       apply val_inj; rewrite /= Heq nth_enum_ord.
  + rewrite [RHS](tnth_nth 0) /= nth_rcons size_tuple.
    have:= Hi; rewrite ltnNge -ltnS => /negbTE ->; rewrite if_same.
    apply/count_memPn; rewrite {}Heq.
    apply/negP => /flattenP /= [rt2].
    rewrite mem_rev /ext_fun => /mapP [/= rt _ ->{rt2}] /mapP [/= j _].
    move=> /(congr1 val) /= Heq.
    move: Hi; rewrite Heq => /leq_ltn_trans/(_ (ltn_ord j)).
    by rewrite ltnn.
- have mt2 i : i \in to_word t2 -> i < n.+1.
    apply contraLR; rewrite -leqNgt => Hi; apply/count_memPn.
    move: Hmu; rewrite /eval => /(congr1 (fun t => tnth t i)).
    rewrite tnth_mktuple => ->.
    by rewrite [LHS](tnth_nth 0) /= nth_rcons size_tuple ltnNge Hi /= if_same.
  pose t : seq (seq 'I_n.+1) := [seq [seq inord (val i) | i <- r] | r <- t2].
  have Ht : is_tab_of_shape n la t.
    rewrite /is_tab_of_shape /=; apply/andP; split.
    + rewrite -incr_tab // => [] [i Hio] [j Hjo] /mt2 /= Hi /mt2 /= Hj.
      by rewrite !sub_pord_ltnXE /= !inordK.
    + rewrite /t {t} -(shape_tabsh t2) /shape /ext_fun -map_comp.
      by apply/eqP/eq_map => s; rewrite /= size_map.
  exists (TabSh Ht).
  + rewrite inE /= /t {t Ht}.
    rewrite /eval; apply/eqP/eq_from_tnth => i; rewrite tnth_mktuple.
    rewrite /to_word -map_rev -map_flatten -/(to_word t2) count_map.
    have -> : tnth mu i = tnth (rcons_tuple mu 0) (widen_ord (leqnSn n.+1) i).
      by rewrite !(tnth_nth 0) nth_rcons /= size_tuple ltn_ord.
    move: Hmu; rewrite /eval =>
       /(congr1 (fun t => tnth t (widen_ord (leqnSn n.+1) i))) <-.
    rewrite tnth_mktuple; apply eq_in_count => j /= /mt2 Hj.
    apply/eqP/eqP => /(congr1 val) /=.
    * by rewrite inordK // => Heq; apply val_inj.
    * by move=> ->; apply val_inj; rewrite /= inordK.
  + apply val_inj => /=.
    apply (eq_from_nth (x0 := [::])); first by rewrite !size_map.
    move=> r Hr; rewrite (nth_map [::]); last by rewrite !size_map.
    apply (eq_from_nth (x0 := ord0)).
    * by rewrite size_map -!nth_shape !shape_tabsh.
    * move=> c Hc.
      rewrite (nth_map ord0); last by move: Hc; rewrite -!nth_shape !shape_tabsh.
      apply val_inj => /=.
      rewrite /t /= (nth_map [::]) // (nth_map ord0) //.
      rewrite inordK //; apply mt2; apply mem_to_word.
      by rewrite /is_in_shape nth_shape.
Qed.

End KostkaEq.


Section Kostka.

Variable d : nat.
Implicit Type la : intpartn d.
Local Notation P := (intpartndom d).

(* We prepend a 0 to take care of the empty partition *)
Definition Kostka la mu :=
  KostkaMon la (mpart (n := (size mu).+1) mu).
Local Notation "''K' ( la , mu )" := (Kostka la mu)
  (at level 8, format "''K' ( la ,  mu )") : nat_scope.
Local Notation "''K' ( la , mu )" := ((Kostka la mu)%:R : int)
  (at level 8, format "''K' ( la ,  mu )") : ring_scope.

Local Arguments mpart n s : clear implicits.

Lemma mpartS n mu :
  size mu <= n.+1 -> mnmwiden (mpart n.+1 mu) = mpart n.+2 mu.
Proof.
move => H.
rewrite /mpart H.
have:= H; rewrite -ltnS => /ltnW ->.
apply mnmP => i; rewrite /mnmwiden.
rewrite (mnm_nth 0) /= nth_rcons size_map size_enum_ord if_same mnmE.
case: ssrnat.ltnP => Hi.
- by rewrite (nth_map ord0) ?nth_enum_ord ?size_enum_ord.
- by rewrite nth_default //; apply: (leq_trans H Hi).
Qed.

Lemma Kostka_any la mu n :
  size mu <= n.+1 -> 'K(la, mu) = KostkaMon la (mpart n.+1 mu).
Proof.
rewrite /Kostka => Hsz.
case: (altP (size mu =P n.+1)) => [->| H].
  by rewrite [RHS]Kostka_rcons mpartS //.
have {Hsz H} Hsz : size mu <= n.
  by move: Hsz; rewrite leq_eqVlt (negbTE H) /= ltnS.
rewrite -(subnKC Hsz).
elim: (n - size mu) => {n Hsz}[|n ->] /=; first by rewrite addn0.
rewrite Kostka_rcons addnS; congr KostkaMon.
rewrite /mpart -addnS; symmetry; rewrite -{2}addnS !leq_addr !addnS.
apply mnmP => i; rewrite /mnmwiden !mnmE.
rewrite (mnm_nth 0) /= nth_rcons size_map size_enum_ord if_same.
case: ssrnat.ltnP => Hi.
- by rewrite (nth_map ord0) ?nth_enum_ord // size_enum_ord.
- by apply nth_default; apply: (leq_trans _ (ltnW Hi)); apply leq_addr.
Qed.

Lemma Kostka_partdom (la mu : P) : 'K(la, mu) != 0 -> mu <=A la.
Proof.
rewrite /Kostka => /KostkaMon_partdom.
rewrite /mpart leqnSn => /partdomP Hdom.
apply/partdomP => i; move/(_ i): Hdom; congr (_ <= _).
rewrite !sumn_take; apply eq_bigr => {i} i _.
case: (ssrnat.ltnP i (size mu).+1) => Hi.
- by rewrite -{1}[i]/(nat_of_ord (Ordinal Hi)) -mnm_nth mnmE.
- by rewrite !nth_default ?size_tuple //; apply ltnW.
Qed.

Lemma Kostka0 (la mu : P) : ~~ (mu <=A la) -> 'K(la, mu) = 0.
Proof.
by move=> H; apply/eqP; move: H; apply contraR; apply Kostka_partdom.
Qed.

Lemma count_nseq (T : eqType) (P : pred T) n x :
  count P (nseq n x) = (P x) * n.
Proof.
rewrite (eq_in_count (a2 := fun _ => P x)); last by move=> i /nseqP [->].
case: (boolP (P x)) => HPx; rewrite /= ?mul0n ?count_pred0 //.
by rewrite ?mul1n ?0count_predT size_nseq.
Qed.

Lemma Kostka_diag la : 'K(la, la) = 1.
Proof.
case Hla : (size la) => [|szla].
  rewrite /Kostka /KostkaMon Hla.
  move: Hla => /eqP/nilP Hla.
  have {Hla} Hd : d = 0 by rewrite -(intpartn_sumn la) Hla.
  subst d.
  have Ht : is_tab_of_shape 0 la [::] by rewrite intpartn0.
  rewrite [KostkaTab _ _](_ : _ = [set TabSh Ht]) ?cards1 //.
  apply/setP => t; rewrite !inE; apply/eqP/eqP => [|->]/=.
  - rewrite /mpart intpartn0 /= => /(congr1 (fun t : 1.-tuple nat => sumn t)).
    rewrite sumn_eval size_to_word /=.
    rewrite (map_comp _ nat_of_ord) val_enum_ord /= addn0.
    by move=> /(tab0 (tabshP _)) => Ht0; apply val_inj.
  - rewrite /to_word /=; apply eq_from_tnth => i.
    by rewrite /mpart intpartn0 /= !tnth_mktuple /=.
rewrite (Kostka_any la (n := szla)) /KostkaMon ?Hla //.
have Hntht j :
  nth [::] [seq nseq (nth 0 la (nat_of_ord i)) i | i <- enum 'I_szla.+1] j =
    nseq (nth 0 la j) (inord j).
  case: (ssrnat.ltnP j szla.+1) => Hj.
  - rewrite (nth_map ord0) ?size_enum_ord // nth_enum_ord //.
    by congr nseq; apply val_inj; rewrite /= inordK // nth_enum_ord.
  - by rewrite !nth_default ?Hla // size_map size_enum_ord.
have HT : is_tab_of_shape szla la [tuple nseq (nth 0 la i) i | i < szla.+1].
  rewrite /= /shape andbC; apply/andP; split.
  - rewrite -map_comp (eq_map (f2 := fun i : 'I__=> nth 0 la i)); first last.
      by move=> i /=; rewrite size_nseq.
    apply/eqP/(eq_from_nth (x0 := 0)); rewrite size_map size_enum_ord ?Hla //.
    by move=> i Hi; rewrite (nth_map ord0) ?size_enum_ord // nth_enum_ord.
  - apply/is_tableauP; rewrite size_map size_enum_ord.
    split => [i Hi | i | i j Hij]; rewrite !{}Hntht.
    + have : nth 0 la i != 0 by apply nth_part_non0; rewrite // Hla.
      by apply contra => /eqP/nilP; rewrite /nilp size_nseq.
    + case: (nth 0 la i) => [|l] //=.
      elim: l => [//= | l] /= ->; by rewrite andbT.
    + have:= intpartnP la => /is_part_ijP [_ /(_ _ _ (ltnW Hij)) Hnthij].
      apply /dominateP; split; first by rewrite !size_nseq.
      rewrite size_nseq /= => c Hc.
      rewrite !nth_nseq Hc (leq_trans Hc Hnthij).
      rewrite sub_pord_ltnXE ltnXnatE /=.
      case: (ssrnat.ltnP j szla.+1) => Hj.
      * by rewrite !inordK // (leq_trans Hij (ltnW _)).
      * by exfalso; move: Hc; rewrite nth_default // Hla.
rewrite [KostkaTab _ _](_ : _ = [set TabSh HT]) ?cards1 //.
apply/setP => /= t; rewrite !inE; apply/eqP/eqP => [|->]/=.
- rewrite /mpart Hla ltnSn => H.
  apply/eqP/tab_eqP => // /= i; rewrite {}Hntht.
  have Hsht := shape_tabsh t.
  elim: i.+1 {-2}i (ltnSn i) => {i} [//| i IHi] j.
  rewrite ltnS leq_eqVlt => /orP [/eqP ->{j}|]; last exact: IHi.
  have Hszt : size t = szla.+1.
    by rewrite -(size_map size) -/(shape t) Hsht Hla.
  case: (ssrnat.ltnP i (size la)) => Hi; first last.
    by rewrite !nth_default // Hszt -Hla.
  rewrite Hla in Hi.
  rewrite -Hsht nth_shape; apply/all_pred1P; rewrite all_count -nth_shape Hsht.
  have:= congr1 (fun t => tnth t (inord i)) H.
  rewrite /eval !tnth_mktuple inordK // => <-.
  rewrite /to_word count_flatten map_rev sumn_rev -sumnE big_map.
  rewrite (big_nth [::]) Hszt big_mkord.
  rewrite (bigD1 (inord i)) //= inordK // big1 ?addn0 //.
  move=> j Hj.
  case: (ssrnat.ltnP j i) => [/IHi -> | Hij].
  - rewrite count_nseq /= inord_val.
    by move: Hj => /negbTE ->; rewrite mul0n.
  - have {Hi Hij} Hij : i < j.
      rewrite ltn_neqAle Hij andbT.
      by move: Hj; apply contra => /eqP ->; rewrite inord_val.
    rewrite (eq_in_count (a2 := pred0)) ?count_pred0 // => /= x.
    rewrite eq_sym /eq_op /= (inordK (ltn_trans Hij _)) //.
    by move=> /(allP (all_ltn_nth_tabsh _ _)) /(leq_trans Hij) /ltn_eqF ->.
- apply eq_from_tnth => i.
  rewrite /eval /mpart Hla ltnSn !tnth_mktuple.
  rewrite /to_word count_flatten map_rev sumn_rev -map_comp.
  rewrite -sumnE big_map enumT -/(index_enum _) (bigD1 i) //=.
  rewrite big1 ?addn0 ?count_nseq /= ?eq_refl ?mul1n //.
  move=> j Hj; apply/count_memPn/nseqP => [] [Heq _].
  by rewrite Heq eq_refl in Hj.
Qed.

End Kostka.

Local Close Scope nat_scope.

Notation "''K' ( la , mu )" := (Kostka la mu)
  (at level 8, format "''K' ( la ,  mu )") : nat_scope.
Notation "''K' ( la , mu )" := (Kostka la mu)%:R
  (at level 8, format "''K' ( la ,  mu )") : ring_scope.

Section SymsSymm.

Variable (n : nat) (R : comRingType) (d : nat).
Local Notation SF := {sympoly R[n.+1]}.
Implicit Type (la mu : intpartn d).

Lemma syms_to_symm la :
  's[la] = \sum_(mu : intpartn d) 'K(la, mu)%:R *: 'm[mu] :> SF.
Proof.
rewrite /Kostka; apply val_inj => /=.
rewrite [RHS](linear_sum (@sympol_lrmorphism _ _)) /=.
apply mpolyP => m; rewrite Kostka_Coeff linear_sum /=.
case: (altP (mdeg m =P sumn la)) => Heq; first last.
- rewrite (KostkaMon_sumeval Heq); symmetry; apply big1 => i _.
  rewrite mcoeffZ.
  case: (leqP (size i) n.+1) => [Hszl | /symm_oversize ->]; first last.
    by rewrite mcoeff0 mulr0.
  rewrite mcoeff_symm //=.
  rewrite [perm_eq _ _](_ : _ = false) /= ?mulr0 //.
  apply (introF idP) => /perm_sumn.
  rewrite -!sumnE -!/(mdeg _) -sumn_partm mpartK // intpartn_sumn => Habs.
  by move: Heq; rewrite intpartn_sumn Habs eq_refl.
- have Hpm : is_part_of_n d (partm m).
   by rewrite /= sumn_partm Heq intpartn_sumn eq_refl /=.
  rewrite (bigD1 (IntPartN Hpm)) //= big1 ?addr0.
  + rewrite mcoeffZ (mcoeff_symm _ _ (size_partm _)).
    rewrite perm_eq_sym partm_perm_eqK /= mulr1.
    congr _%:R.
    rewrite -Kostka_any // [RHS](Kostka_any _ (size_partm m)).
    by apply perm_KostkaMon; apply: partm_perm_eqK.
  + move=> mu Hmu; rewrite mcoeffZ.
    case: (leqP (size mu) n.+1) => [Hszl | /symm_oversize ->]; first last.
      by rewrite mcoeff0 mulr0.
    rewrite mcoeff_symm //=.
    suff /negbTE -> : ~~ (perm_eq (mpart (n := n.+1) mu) m) by rewrite mulr0.
    move: Hmu; apply contra => /perm_eq_partm H.
    apply/eqP/val_inj => /=; rewrite -H.
    by rewrite mpartK.
Qed.

Local Notation P := (intpartndom d).

Lemma syms_to_symm_partdom la :
  's[la] = 'm[la] + \sum_(mu : P | mu <A la) 'K(la, mu) *: 'm[mu] :> SF.
Proof.
rewrite syms_to_symm (bigD1 la) //= Kostka_diag scale1r; congr (_ + _).
rewrite (bigID (fun mu : P => mu <=A la)) /= addrC big1 ?add0r //.
by move=> i /andP [_ /Kostka0 ->]; rewrite scale0r.
Qed.

End SymsSymm.


Section KostkaInv.

Variable (d : nat).
Implicit Type (la mu : intpartn d).
Local Notation P := (intpartndom d).

Local Definition decms la (coe : P -> int) :=
  forall (n : nat),
    ('m[la] = 's[la] + \sum_(mu : P | mu <A la) coe mu *: 's[mu]
                      :> {sympoly int[n.+1]}).


(* Inversing a triangular matrix with 1 on the diagonal *)
Lemma symm_to_syms_ex :
  { coe : P -> P -> int | forall la, decms la (coe la) }.
Proof.
suff rec (la : P) : { coela : P -> int | decms la coela }.
  by exists (fun la => sval (rec la)) => la; case: rec.
elim/(finord_wf (T := intpartndom_finPOrdType d)) : la => /= la IHla.
have {IHla} (y : P) : { coela : P -> int | y <A la -> decms y coela }.
  case: (boolP (y <A la)) => Hy; last by exists (fun _ => 0).
  by have [coela Hcoela] := IHla y Hy; exists coela.
rewrite /decms => rec.
exists (fun mu : P =>
          - ('K(la, mu) +
             \sum_(p | (mu < p < la)%Ord) sval (rec p) mu * 'K(la, p))) => n.
rewrite (eq_bigr (fun mu : P =>
    - ('K(la, mu) *: 's[mu] +
       (\sum_(p | (mu < p < la)%Ord)
         sval (rec p) mu * 'K(la, p) *: 's[mu])))); first last.
  by move=> i Hi; rewrite scaleNr scalerDl -scaler_suml.
rewrite sumrN big_split /=.
rewrite (exchange_big_dep (fun j : P => j <A la)) /=; first last.
  by move=> i j _ /andP [].
rewrite -big_split /=.
apply/eqP; rewrite eq_sym syms_to_symm_partdom subr_eq; apply/eqP; congr (_ + _).
apply eq_bigr => mu Hmu.
rewrite (eq_bigl (fun j : P => j <A mu)) /=; first last.
  move=> i; case: (boolP (i <A mu)); rewrite /= ?Hmu ?andbT ?andbF //.
  by move=> /ltnX_trans/(_ Hmu) ->.
case: (rec mu) => coela /= /(_ Hmu) ->.
rewrite scalerDr scaler_sumr; congr (_ + _).
by apply eq_bigr => i _; rewrite scalerA mulrC.
Qed.

End KostkaInv.

Definition KostkaInv d (la mu : intpartn d) : int :=
  if mu == la then 1 else
    if (mu : intpartndom d) <A la then sval (symm_to_syms_ex d) la mu else 0.

Notation "''K^-1' ( la , mu )" := ((KostkaInv la mu)%:~R)
  (at level 8, format "''K^-1' ( la ,  mu )") : ring_scope.

Section SymmSyms.

Variables (R : comRingType) (n : nat).
Local Notation SF := {sympoly R[n.+1]}.
Local Notation intR := (map_sympoly [rmorphism of intr]).

Variable (d : nat).
Local Notation P := (intpartndom d).

Implicit Type la : intpartn d.

Lemma symm_to_syms la :
  'm[la] = \sum_(mu : P) 'K^-1(la, mu) *: 's[mu] :> SF.
Proof.
rewrite /KostkaInv -(map_symm [rmorphism of intr]).
case: symm_to_syms_ex => Kinv /= /(_ la) ->.
rewrite rmorphD /= rmorph_sum /=.
apply esym; rewrite (bigD1 la) //= eq_refl scale1r map_syms; congr (_ + _).
rewrite (bigID (fun mu : P => mu <=A la)) /= addrC big1 ?add0r; first last.
  move=> i /andP [Hd /negbTE Hdiff].
  by rewrite ltnX_neqAleqX (negbTE Hd) Hdiff /= scale0r.
by apply eq_bigr => i Hi; rewrite Hi (ltnX_eqF Hi) scale_map_sympoly map_syms.
Qed.

Lemma symm_to_syms_partdom la :
  'm[la] = 's[la] + \sum_(mu : P | mu <A la) 'K^-1(la, mu) *:'s[mu] :> SF.
Proof.
rewrite symm_to_syms /KostkaInv (bigD1 la) //= eq_refl scale1r; congr (_ + _).
rewrite (bigID (fun mu : P => mu <=A la)) /= addrC big1 ?add0r; first last.
  move=> i /andP [Hd /negbTE Hdiff].
  by rewrite ltnX_neqAleqX (negbTE Hd) Hdiff /= scale0r.
by apply eq_bigr => i Hi; rewrite Hi (ltnX_eqF Hi).
Qed.

End SymmSyms.
