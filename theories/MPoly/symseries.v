From mathcomp Require Import all_boot ssralg ssrint poly.
From mathcomp Require Import ssrcomplements freeg mpoly.

Require Import tfps auxresults.
Require Import tools sorted partition sympoly.

Set SsrOldRewriteGoalsOrder.  (* change to Unset and remove the line when requiring MathComp >= 2.6 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope tfps_scope.


Section BigSumSet.

Variables (n : nat).
Implicit Type (A : {set 'I_n}).

Section BigSet.

Import Monoid.Theory.

Variable R : Type.
Variable idx : R.
Local Notation "0" := idx.
Variable op : Monoid.com_law 0.

Local Notation "'+%M'" := op.
Local Notation "x + y" := (op x y).


Local Definition Ilt k : {set 'I_n} := [set i : 'I_n | i < k].

Lemma big_set_ind (F : {set 'I_n} -> R) (k : 'I_n) :
  \big[+%M/0]_(A : {set 'I_n} | A \subset Ilt k.+1) F A
  = \big[+%M/0]_(A : {set 'I_n} | A \subset Ilt k) F A
  + \big[+%M/0]_(A : {set 'I_n} | A \subset Ilt k) F (k |: A).
Proof.
rewrite [LHS](bigID (fun A : {set 'I_n} => k \in A)) /= mulmC; congr (_ + _).
  apply eq_bigl => A; first last.
  apply/andP/subsetP => [[/subsetP Asubk1 kninA] i iinA | Asubk].
    move/(_ _ iinA): Asubk1.
    rewrite !inE ltnS leq_eqVlt => /orP[/eqP/val_inj eqik| //].
    by move: kninA; rewrite -eqik iinA.
  split; first by apply/subsetP => j /Asubk; rewrite !inE => /ltnW.
  by apply/negP => /Asubk; rewrite inE /= ltnn.
set P := BIG_P; have /(reindex_onto _) -> /= :
    {in P, cancel (fun A => A :\ k) (fun A => k |: A)}.
  by move=> A; rewrite /P unfold_in /= => /andP[_ /setD1K].
apply: eq_bigl => A; rewrite unfold_in setU11 andbT andbC {P}.
have -> : ((k |: A) :\ k == A) = (k \notin A).
  by apply/eqP/idP => [<- | /setU1K ->]; first by rewrite setD11.
case: (boolP (k \in A)) => [kinA | kninA] /=.
  apply/esym; move: kinA; apply: contraPF => /subsetP/[apply].
  by rewrite inE ltnn.
apply/subsetP/subsetP => Hsubs j; rewrite !inE; first last.
  by rewrite ltnS => /orP[/eqP-> // | /Hsubs/[!inE]/ltnW].
move=> jinA; have {}/Hsubs : j \in k |: A by rewrite inE jinA orbT.
rewrite inE ltnS leq_eqVlt => /orP[/eqP/val_inj eqjk | //].
by rewrite -eqjk jinA in kninA.
Qed.

End BigSet.


Section BigSumProdSet.

Variables (R : comPzSemiRingType).  (* TODO generalize to non commutative *)

Lemma sum_prod_allset (F : 'I_n -> R) :
  \sum_(A : {set 'I_n}) \prod_(i in A) F i = \prod_(i < n) (1 + F i).
Proof.
pose sumlt k := \sum_(A : {set 'I_n} | A \subset Ilt k) \prod_(i in A) F i.
suff bound k : k <= n -> sumlt k = \prod_(i < n | i < k) (1 + F i).
  transitivity (sumlt n).
    by apply: eq_bigl => /= h; apply/esym/subsetP => i _; rewrite inE ltn_ord.
  by rewrite {}bound //; apply: eq_bigl => i; rewrite ltn_ord.
elim: k => [_ | k /[swap]ltkn].
  rewrite {}/sumlt (big_pred1 set0) => [| h /=].
    by rewrite !big_pred0 => // h; rewrite inE.
  apply /idP/eqP => [/subsetP sub0 | ->]; last exact: sub0set.
  by apply/eqP; rewrite -subset0; apply/subsetP => i /sub0 /[!inE].
rewrite -[k]/(\val (Ordinal ltkn)); move: (Ordinal ltkn) => {ltkn}k /=.
move=> /(_ (ltnW (ltn_ord k))) IHk.
rewrite [LHS]big_set_ind /= -/(sumlt k).
rewrite [X in _ + X](_ : _ = (sumlt k) * (F k)) /=.
  rewrite -[X in X + _]mulr1 -mulrDr {}IHk mulrC.
  rewrite [RHS](bigD1 k) //=; congr (_ * _).
  by apply: eq_bigl => j; rewrite ltn_neqAle andbC -val_eqE.
rewrite {IHk} mulr_suml; apply eq_bigr => A /subsetP Asubk.
rewrite (bigD1 k) /= ?inE ?eqxx // mulrC; congr (_ * _).
apply eq_bigl => j; rewrite !inE andbC; case: eqP => /=[->| //].
by apply/esym/(introF idP) => /Asubk; rewrite inE ltnn.
Qed.

End BigSumProdSet.

End BigSumSet.


Section Series.

Variables (n : nat) (R : idomainType).

Local Notation "''e_' k" := (mesym n R k).
Local Notation "''h_' k" := (symh_pol n R k).
Local Notation "''p_' k" := (symp_pol n R k).

Section ElemCompl.

Context {d : nat}.

Notation Gf := {tfps {mpoly R[n]} d}.
Notation Pol := {poly {mpoly R[n]}}.

Definition gfunE : Gf  := \prod_(i < n) (1 + 'X_i *: \X).
Definition gpolE : Pol := \prod_(i < n) (1 + 'X_i *: 'X).

(* Notation Gfsym := {poly {sympoly R[n]}}. *)
(* Definition gpolEsym : Gfsym := \poly_(i < n.+1) 'e_i. *)


Local Lemma coef1XiX i : (1 + 'X_i *: \X : Gf)`_0 = 1.
Proof. by apply/eqP; exact: (coeft1cX d 'X_i). Qed.
Local Lemma coefN1XiX i : (1 - 'X_i *: \X : Gf)`_0 = 1.
Proof. by apply/eqP; rewrite -scaleNr; exact: (coeft1cX d (- 'X_i)). Qed.

Lemma gfun_trXnE : gfunE = trXn d gpolE.
Proof.
rewrite /gfunE rmorph_prod /=; apply: eq_bigr => i _.
by rewrite raddfD /= linearZ /= trXn1.
Qed.
Lemma size_gpolE : size gpolE = n.+1.
Proof.
rewrite size_prod => [|/= i _]; first last.
  apply/negP => /eqP/(congr1 (coefp 0%N))/eqP /=.
  by rewrite coef0 coefD coefZ coef1 eqxx coefX /= mulr0 addr0 oner_eq0.
suff -> : \sum_i size (1 + 'X_i *: 'X : Pol)%R = n.*2.
  by rewrite card_ord -addnn -addSn addnK.
rewrite (eq_bigr (fun _ => 2%N)) => [| /= i _].
  by rewrite sum_nat_const card_ord muln2.
suff szXX : size ('X_i *: 'X : Pol) = 2.
  by rewrite addrC size_polyDl szXX // size_poly1.
rewrite size_scale ?size_polyX //.
apply/negP => /eqP/(congr1 (fun p => p@_(mnm1 i)))/eqP.
by rewrite mcoeffXU eqxx mcoeff0 oner_eq0.
Qed.

Lemma gpolE_mesymE : gpolE = \sum_(i < n.+1) 'e_i *: 'X ^ i.
Proof.
rewrite /gpolE /mesym; apply esym.
transitivity (\sum_(h : {set 'I_n}) \prod_(i in h) 'X_i *: 'X ^ #|h| : Pol).
  have cardle (h : {set 'I_n}) : #|h| < n.+1.
    by rewrite ltnS -[X in _ <= X](card_ord n) max_card.
  pose card_ord h := Ordinal (cardle h).
  rewrite [RHS](partition_big card_ord xpredT) //=.
  apply: eq_bigr => /= i _; rewrite scaler_suml /=.
  by apply: eq_big => [H | D /eqP ->]; first by rewrite -val_eqE.
transitivity (\sum_(h : {set 'I_n}) \prod_(i in h) ('X_i *: 'X) : Pol).
  by apply: eq_bigr => /= h _; rewrite -['X ^ _]prodr_const -scaler_prod.
exact: sum_prod_allset.
Qed.



Lemma coef_gpolE_mesym i : gpolE`_i = 'e_i.
Proof.
rewrite gpolE_mesymE coef_sum /=.
case: (ltnP i n.+1) => [ltin1 | gein]; first last.
  rewrite (mesym_geqnE _ gein).
  rewrite big1 // => j _; rewrite coefZ coefXn.
  by rewrite (gtn_eqF (leq_trans _ gein)) // mulr0.
rewrite (bigD1 (Ordinal ltin1)) //=.
rewrite coefZ coefXn eqxx mulr1 big1 ?addr0 // => j.
rewrite coefZ coefXn eq_sym -val_eqE /= => /negbTE ->.
by rewrite mulr0.
Qed.

Lemma gfunE_mesymE i : i <= d -> gfunE`_i = 'e_i.
Proof.
rewrite gfun_trXnE coef_trXn => ->.
exact: coef_gpolE_mesym.
Qed.
Lemma gfunE_coeft0_eq1 : gfunE \in coeft0_eq1.
Proof.
apply/eqP; rewrite /gfunE coeft0_prod; apply: big1 => i _.
by rewrite coef1XiX.
Qed.
Lemma gfunE_unit : gfunE \is a GRing.unit.
Proof. by rewrite unit_tfpsE (eqP gfunE_coeft0_eq1) unitr1. Qed.

Lemma mesym0 : 'e_0 = 1.
Proof. by rewrite -gfunE_mesymE // (eqP gfunE_coeft0_eq1). Qed.

Lemma mesym_over m : m > n -> 'e_m = 0.
Proof.
move=> lt_n_m; rewrite -coef_gpolE_mesym.
apply/leq_sizeP; last exact: lt_n_m.
by rewrite size_gpolE.
Qed.


Definition gfunH : Gf := \prod_(i < n) (1 - 'X_i *: \X) ^-1.

Lemma gfunH_coeft0_eq1 : gfunH \in coeft0_eq1.
Proof.
apply: rpred_prod => i _ /=.
by rewrite rpredV /=; apply/eqP; rewrite coefN1XiX.
Qed.


Lemma gfunHE : gfunH = \sum_(m : 'X_{1..n < d.+1}) 'X_[m] *: \X ^+ (mdeg m).
Proof.
rewrite /= /gfunH.
pose bnd k (m : 'X_{1..n < d.+1}) := [forall i : 'I_n, (i >= k) ==> (m i == 0)].
have bndP k (m : 'X_{1..n < d.+1}) :
    reflect (forall i : 'I_n, i >= k -> m i = 0) (bnd k m).
  apply (iffP forallP) => /= H i.
    by move/(_ i): H => /implyP/[apply]/eqP.
  by apply/implyP => /H ->.
pose prodlt k : Gf :=  \prod_(i < n | i < k) (1 - 'X_i *: \X)^-1.
suff rec k : k <= n ->
             prodlt k = \sum_(m | bnd k m) 'X_[m] *: \X ^+ mdeg m :> Gf.
  transitivity (prodlt n).
    by apply: eq_bigl => /= i; rewrite ltn_ord.
  rewrite rec //; apply eq_bigl => m; apply/bndP => /= i.
  by rewrite leqNgt ltn_ord.
elim: k => [_ | k /[swap]/[dup] ltkn /ltnW/[swap]/[apply]].
  rewrite {}/prodlt big1 // (big_pred1 bm0) /=.
    by rewrite mdeg0 expr0 mpolyX0 scale1r.
  rewrite /bnd /= => m /=.
  apply/forallP/eqP => [/= H0 | -> /= i]; last by rewrite mnm0E.
  by apply/val_inj/mnmP => /= i; rewrite mnm0E; apply/eqP.
rewrite -[k]/(\val (Ordinal ltkn)); move: (Ordinal ltkn) => {ltkn}k /= rec.
have -> : prodlt k.+1 = prodlt k * (1 - 'X_k *: \X)^-1.
  rewrite {1}/prodlt (bigD1 k) //= mulrC; congr (_ / _).
  by apply: eq_bigl => i; rewrite ltnS ltn_neqAle andbC.
rewrite {prodlt}rec mulr_suml.
pose restr_fun (m : 'X_{1.. n < d.+1}) :=
  [multinom if i < k then m i else 0 | i < n].
have rest_subproof m : mdeg (restr_fun m) < d.+1.
  apply: (leq_trans _ (bmdeg m)); rewrite ltnS !mdegE.
  by apply: leq_sum => /= i _; rewrite {}/restr_fun /= mnmE; case: ltnP.
pose restr m := BMultinom (rest_subproof m).
rewrite [RHS](partition_big restr (bnd k)) /= => [| m]; first last.
  move/bndP => H; apply/bndP => i.
  rewrite leq_eqVlt => /orP[/eqP/val_inj <-|]; rewrite mnmE ?ltnn //.
  by move=> /H ->; rewrite if_same.
apply: eq_bigr => m /bndP Hbnd /=.
have geti_subproof (h : 'X_{1.. n < d.+1}) : h k < d.+1.
  by apply: (leq_trans _ (bmdeg h)); rewrite ltnS mdegE (bigD1 k) //= leq_addr.
pose geti h := Ordinal (geti_subproof h).
pose join_fun (h : 'X_{1.. n < d.+1}) (c : 'I_d.+1) :=
  [multinom if i != k then h i else c | i < n].
have join_subproof h c :
  mdeg (if mdeg (join_fun h c) < d.+1 then join_fun h c else 0%MM) < d.+1.
  by case: (ltnP (mdeg (join_fun h c)) _) => // _; rewrite mdeg0.
pose join h c := BMultinom (join_subproof h c).
have mdeg_join i : mdeg (join_fun m i) = mdeg m + i.
  rewrite !mdegE /= (bigD1 k) //= mnmE eqxx /= addnC; congr (_ + _)%N.
  rewrite [RHS](bigD1 k) //= Hbnd // add0n.
  by apply: eq_bigr => j nejk; rewrite mnmE nejk.
rewrite (reindex_onto (join m) geti) /= => [|h]; first last.
  case/andP => /bndP hbnd /eqP <-.
  apply/val_inj/mnmP => /= i; rewrite /join_fun.
  set mh := [multinom _ | i < n]; suff -> : mh = h by rewrite bmdeg.
  apply/mnmP => {}i; rewrite !mnmE -!val_eqE /=.
  by case: (ltngtP i k) => [| /= /hbnd ->| /val_inj ->].
rewrite geometrict_1cNV mulr_sumr /=; apply esym.
rewrite (eq_bigl (fun j => mdeg (join_fun m j) < d.+1)) => [| i]; first last.
  have -> /= : bnd k.+1 (join m i).
    apply/bndP => j ltkj; rewrite /join /= /join_fun.
    case: ltnP => _; rewrite mnmE //.
    by rewrite -!val_eqE /= (gtn_eqF ltkj) /= Hbnd // ltnW.
  case: ltnP => [mdeglt | mdeggt]; first last.
    have -> : join m i = bm0 by apply: val_inj; rewrite /= ltnNge mdeggt.
    apply/negP => /andP[/eqP/esym eqm /eqP/esym/(congr1 val)/=].
    rewrite mnmE => eqi; move: mdeggt.
    suff -> : join_fun m i = 0%MM by rewrite mdeg0.
    by apply/mnmP => j; rewrite !mnmE eqi eqm !mnmE !if_same.
  apply/andP; split; apply/eqP/val_inj => /=.
    apply/mnmP => j; rewrite !mnmE /= mdeglt mnmE -val_eqE /= neq_ltn.
    by case: ltnP => // /Hbnd ->.
  by rewrite mdeglt mnmE eqxx /=.
rewrite [RHS](bigID (fun j => mdeg (join_fun m j) < d.+1)) /=.
rewrite [X in _ = _ + X]big1 ?addr0 => [|i]; first last.
  rewrite mdeg_join -leqNgt => Hmdeg.
  rewrite -scalerAr -scalerAl scalerA -exprD; apply/tfpsP => c lecd.
  by rewrite !coeft_simpl lecd /= (ltn_eqF (leq_ltn_trans lecd Hmdeg)) mulr0.
apply: eq_bigr => i /[dup] Hmdeg -> /=.
rewrite mdeg_join -scalerAr -scalerAl scalerA -exprD /=; congr (_ *: _).
rewrite mpolyXn -mpolyXD; congr ('X_[_]).
apply/mnmP => j; rewrite !mnmE mulmnE /= mnmE eq_sym.
case: eqP => [<-|] /=; last by rewrite mul0n add0n.
by rewrite mul1n Hbnd.
Qed.

Lemma gfunH_symhE i : i <= d -> gfunH`_i = 'h_i.
Proof.
rewrite gfunHE => leid.
rewrite coeft_sum (bigID (fun m : 'X_{1..n < d.+1} => mdeg m == i)) /=.
rewrite [X in _ + X = _]big1 ?addr0 => [| m /negbTE neqm]; first last.
  by rewrite !coeft_simpl eq_sym leid neqm /= mulr0.
rewrite (symh_pol_any _ _ (leid : i < d.+1)).
rewrite /symh_pol_bound /=; apply: eq_bigr => m /eqP eqmdeg.
by rewrite !coeft_simpl eq_sym leid eqmdeg eqxx mulr1.
Qed.

Lemma gfunEgfunH : (gfunE \oT -\X) * gfunH = 1.
Proof.
rewrite /gfunE /gfunH rmorph_prod /= -big_split /=; apply: big1 => i _.
rewrite raddfD /= comp_tfps1 linearZ /= comp_tfpsX; first last.
  exact/coeft0_eq0N/tfpsX_in_coeft0_eq0.
by rewrite scalerN divrr // unit_tfpsE coefN1XiX unitr1.
Qed.

Lemma sum_syme_symh k :
  0 < k <= d -> \sum_(0 <= i < k.+1) (-1) ^+ i *: ('e_i * 'h_(k - i)) = 0.
Proof.
case/andP=> lt0k lekd.
have := (congr1 (fun f : Gf => f`_k) gfunEgfunH).
rewrite coeft_simpl (gtn_eqF lt0k) /= => Heq; rewrite -{}[RHS]Heq.
rewrite coeftM lekd big_mkord; apply eq_bigr => i _.
rewrite scalerAl -(gfunH_symhE (leq_trans (leq_subr _ _) lekd)).
rewrite -scaleN1r coef_comp_tfps_cX /= gfunE_mesymE.
rewrite -mulr_algl -in_algE rmorphXn rmorphN rmorph1 //.
by rewrite (leq_trans _ lekd) // -ltnS ltn_ord.
Qed.

Lemma gfunHgfunE : (gfunH \oT -\X) * gfunE = 1.
Proof.
rewrite /gfunE /gfunH rmorph_prod /= -big_split /=; apply: big1 => i _.
rewrite rmorphV /=; first last.
  by apply: coeft0_eq1_unit; apply/eqP; rewrite coefN1XiX.
rewrite raddfB /= comp_tfps1 linearZ /= comp_tfpsX; first last.
  by rewrite -scaleN1r tfpscX_in_coeft0_eq0.
by rewrite scalerN opprK mulVr // unit_tfpsE coef1XiX unitr1.
Qed.

End ElemCompl.


Section PowerSums.

Import TFPSUnitRing.

Variable (d : nat).
Notation Gf := {tfps {mpoly R[n]} d}.
Notation Pol := {mpoly R[n]}.

Hypothesis nat_unit : forall i : nat, i.+1%:R \is a @GRing.unit R.
Lemma poly_nat_unit i : i.+1%:R \is a @GRing.unit {mpoly R[n]}.
Proof. by rewrite -mpolyC_nat; apply: rmorph_unit. Qed.

Definition gfunP : Gf := \sum_(i < d.+1) 'p_i.+1 *: \X ^+ i.

Lemma gfunP_sympE i : i < d.+1 -> gfunP`_i = 'p_i.+1.
Proof.
move=> /[dup] ltid1 /[!ltnS] ltid.
rewrite coeft_sum /= (bigD1 (Ordinal ltid1)) //=.
rewrite coeftZ coef_tfpsXn eqxx ltid /= mulr1.
rewrite big1 ?addr0 // => j.
rewrite -val_eqE /= coeftZ coef_tfpsXn eq_sym => /negbTE-> /=.
by rewrite andbF mulr0.
Qed.

Lemma gfunP_dlog_gfunH : gfunP = (log (gfunH (d := d.+1)))^`().
Proof.
have pln := poly_nat_unit.
have N1x d' i : (1 - 'X_i *: \X) \in @coeft0_eq1 {mpoly R[n]} d'.
  exact/eqP/coefN1XiX.
have N1xV d' i : (1 - 'X_i *: \X)^-1 \in @coeft0_eq1 {mpoly R[n]} d'.
  exact/coeft0_eq1V/N1x.
rewrite /gfunH log_prod => [|i|/= i _] //; last exact: N1xV.
rewrite /gfunP /= big_mknat.
under eq_bigr do rewrite scaler_suml.
rewrite exchange_big /= raddf_sum /=; apply eq_bigr => i _.
rewrite logV ?(N1x _ _) //.
rewrite log_coeft0_eq1 ?(N1x _ _) // opprK raddf_sum /=.
rewrite big_add1 /= !big_nat; apply: eq_bigr => k /= /[!ltnS] ltkd.
rewrite inordK ?ltnS //.
rewrite opprD opprK addrA subrr add0r linearZ /= derivX_tfps /=.
rewrite !linearZ /= trXnt_tfpsX deriv_tfpsX -[X in _ = _ *: X]scaler_nat.
rewrite scalerA mulVr // exprZn scale1r.
by rewrite mulr_algr scalerA -exprS.
Qed.
Lemma gfunP_gfunH : gfunP = (gfunH (d := d.+1))^`()%tfps / (gfunH (d := d)).
Proof.
rewrite gfunP_dlog_gfunH.
rewrite (deriv_log poly_nat_unit gfunH_coeft0_eq1).
congr (_ / _); apply/tfpsP => i leid; rewrite coef_trXnt leid.
by rewrite !gfunH_symhE // (leq_trans leid).
Qed.
Lemma gfunH_gfunP : (gfunH (d := d.+1))^`()%tfps = gfunP * (gfunH (d := d)).
Proof.
have -> := congr1 (fun f => f * (gfunH (d := d))) gfunP_gfunH.
by rewrite divrK // coeft0_eq1_unit // gfunH_coeft0_eq1.
Qed.

Lemma Newton_symh (k : nat) :
  k <= d -> k%:R *: 'h_k = \sum_(0 <= i < k) 'h_i * 'p_(k - i).
Proof.
case: k => [_ | k ltkd]; first by rewrite scale0r big_nat big1.
have := congr1 (fun f : Gf => f`_k) gfunH_gfunP.
rewrite coef_deriv_tfps gfunH_symhE ?ltnS ?(ltnW ltkd) // scaler_nat => ->.
rewrite mulrC coeftM (ltnW ltkd).
rewrite big_mknat !big_nat; apply eq_bigr => i /= ltik1.
rewrite inordK // gfunH_symhE; last exact/ltnW/(leq_trans ltik1).
rewrite subSn ?ltnS // gfunP_sympE //.
exact: (leq_trans (leq_subr _ _) (ltnW ltkd)).
Qed.
Lemma Newton_symh1 (k : nat) :
  k <= d -> k%:R *: 'h_k = \sum_(1 <= i < k.+1) 'p_i * 'h_(k - i).
Proof.
move/Newton_symh=> ->.
rewrite [RHS]big_nat_rev /= big_add1 /= !big_nat.
apply: eq_bigr => i /= ltik.
by rewrite add1n !subSS mulrC subKn // ltnW.
Qed.

Local Lemma gfunENX_unit dg : gfunE (d := dg) \oT - \X \is a GRing.unit.
Proof. by rewrite comp_tfps_unitE gfunE_unit. Qed.
Local Lemma gfunENX0_eq1 dg : gfunE (d := dg) \oT - \X \in coeft0_eq1.
Proof. by rewrite coeft0_eq1_comp gfunE_coeft0_eq1. Qed.
Local Lemma gfunH_gfunEV dg : gfunH (d := dg) = (gfunE \oT -\X)^-1.
Proof.
by apply (mulrI (gfunENX_unit _)); rewrite gfunEgfunH divrr ?gfunENX_unit.
Qed.
Local Lemma trXnt_gfunE dg :
  trXnt dg (gfunE (d := dg.+1) \oT - \X) = gfunE (d := dg) \oT - \X.
Proof.
rewrite (trXnt_comp _ _ (leqnSn _)) raddfN /= trXnt_tfpsX.
by rewrite !gfun_trXnE trXntE /= trXn_trXn.
Qed.

Lemma gfunP_dlog_gfunE : gfunP = (-log (gfunE (d := d.+1) \oT - \X))^`().
Proof.
rewrite gfunP_dlog_gfunH /=.
suff -> : log (gfunH (d := d.+1)) = - log (gfunE \oT - \X) by [].
by rewrite -[RHS](logV poly_nat_unit (gfunENX0_eq1 _)) gfunH_gfunEV.
Qed.
Lemma gfunP_gfunE :
  gfunP \oT -\X = (gfunE (d := d.+1))^`()%tfps / (gfunE (d := d)).
Proof.
have ENXud := gfunENX_unit d.
have ENXud1 := gfunENX_unit d.+1.
rewrite gfunP_dlog_gfunH !gfunH_gfunEV.
rewrite (deriv_log poly_nat_unit) /= ?rpredV /= ?gfunENX0_eq1 //.
rewrite derivV_tfps ?(coeft0_eq1_unit (gfunENX0_eq1 _)) //=.
rewrite -mulrA !rmorphXn /= -invrM; first last.
- by apply: unitrX; rewrite trXnt_gfunE.
- by rewrite trXnt_unitE -unit_tfpsE unitrV.
rewrite (rmorphV _ (gfunENX_unit _)) /= trXnt_gfunE.
rewrite deriv_tfps_comp ?rpredN ?tfpsX_in_coeft0_eq0 //= !raddfN /=.
rewrite [LHS]rmorphM /=; congr (_ * _).
  rewrite deriv_tfpsX mulrN1 opprK trXnt_tfpsX -comp_tfpsA raddfN /=.
  by rewrite comp_tfpsX ?rpredN ?tfpsX_in_coeft0_eq0 //= opprK comp_tfpsXr.
rewrite mulrC -[X in _ * X]exprN1 -exprB //=.
rewrite subSS subn0 expr1 rmorphV //=.
rewrite  -comp_tfpsA raddfN /=.
by rewrite comp_tfpsX ?rpredN ?tfpsX_in_coeft0_eq0 //= opprK comp_tfpsXr.
Qed.
Lemma gfunE_gfunP :
  (gfunE (d := d.+1))^`()%tfps = (gfunP \oT - \X) * (gfunE (d := d)).
Proof.
have := congr1 (fun f => f * gfunE) gfunP_gfunE.
by rewrite divrK ?gfunE_unit.
Qed.

Lemma Newton_syme (k : nat) :
  k <= d ->
  k%:R *: 'e_k =
  \sum_(0 <= i < k) (-1) ^+ (k - i).+1 *: 'e_i * 'p_(k - i).
Proof.
case: k => [_ | k ltkd]; first by rewrite scale0r big_nat big1.
have := congr1 (fun f : Gf => f`_k) gfunE_gfunP.
rewrite coef_deriv_tfps gfunE_mesymE ?ltnS ?(ltnW ltkd) // scaler_nat => ->.
rewrite mulrC coeftM (ltnW ltkd).
rewrite big_mknat !big_nat; apply eq_bigr => i /= ltik1.
rewrite inordK // gfunE_mesymE; last exact/ltnW/(leq_trans ltik1).
rewrite subSn ?ltnS // -scalerAl scalerAr; congr (_ * _).
rewrite expri2 /gfunP [in LHS]raddf_sum /= coeft_sum.
have ltki : k - i < d.+1 by apply: (leq_trans (leq_subr _ _) (ltnW ltkd)).
rewrite (bigD1 (Ordinal ltki)) //= big1 ?addr0 => [|j]; first last.
  rewrite -val_eqE /= => /negbTE neq.
  rewrite linearZ coeftZ /= comp_tfpsXn ?rpredN ?tfpsX_in_coeft0_eq0 //.
  by rewrite -scaleN1r exprZn coeftZ coef_tfpsXn eq_sym neq andbF !mulr0.
rewrite linearZ coeftZ /= comp_tfpsXn ?rpredN ?tfpsX_in_coeft0_eq0 //.
rewrite -scaleN1r exprZn coeftZ coef_tfpsXn eqxx -ltnS ltki /= mulr1 mulrC.
by rewrite -mulr_algl -in_algE rmorphXn rmorphN rmorph1.
Qed.

Lemma Newton_syme1 (k : nat) :
  k <= d ->
  k%:R *: 'e_k =
  \sum_(1 <= i < k.+1) (-1) ^+ i.+1 *: 'p_i * 'e_(k - i).
Proof.
move/Newton_syme ->.
rewrite [RHS]big_nat_rev /= big_add1 /= !big_nat.
apply: eq_bigr => i /= ltik.
by rewrite add1n !subSS -!scalerAl mulrC subKn ?(ltnW ltik).
Qed.

End PowerSums.

End Series.

