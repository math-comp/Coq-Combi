Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun finset binomial order.
From mathcomp Require Import bigop ssralg ssrint path perm fingroup.
From SsrMultinomials Require Import ssrcomplements freeg mpoly.
From SsrMultinomials Require monalg.

Require Import sorted tools ordtype permuted partition skewpart.
Require Import antisym Schur_mpoly Schur_altdef sympoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.


Local Reserved Notation "''a_' k"
      (at level 8, k at level 2, format "''a_' k").
Local Reserved Notation "m # s"
      (at level 40, left associativity, format "m # s").


Section BigPMap.
Variables (R : Type) (idx : R).
Local Notation "1" := idx.
Variable (op : Monoid.law idx).
Local Notation "*%M" := op (at level 0).
Local Notation "x * y" := (op x y).
Variable I : Type.

Lemma big_pmap J (h : J -> option I) r F :
  \big[*%M/1]_(i <- pmap h r) F i = \big[*%M/1]_(j <- r) oapp F idx (h j).
Proof.
elim: r => [| r0 r IHr]/=; first by rewrite !big_nil.
rewrite /= big_cons; case: (h r0) => [i|] /=; last by rewrite Monoid.mul1m.
by rewrite big_cons IHr.
Qed.

End BigPMap.


Section MultAlternSymp.

Variable n0 : nat.
Variable R : comRingType.

Local Notation n := n0.+1.
Local Notation rho := (rho n).
Local Notation "''a_' k" := (@alternpol n R 'X_[k]).


Lemma mult_altern_symp_pol p d :
  'a_(mpart p + rho) * (symp_pol n R d.+1) =
   \sum_(i < n) 'a_(mpart p + rho + U_(i) *+ d.+1).
Proof.
rewrite /alternpol mulr_suml [RHS]exchange_big /=; apply eq_bigr => s _.
rewrite -scaler_sumr -scalerAl; congr (_ *: _).
rewrite -(issymP _ (symp_sym n R d.+1) s) -msymM -linear_sum /=; congr msym.
rewrite /symp_pol mulr_sumr; apply eq_bigr => i _.
by rewrite !mpolyXD mpolyXn.
Qed.

Lemma mult_altern_oapp p d :
  is_part p -> size p <= n ->
  'a_(mpart p + rho) * (symp_pol n R d.+1) =
  \sum_(i < n) oapp (fun ph => (-1) ^+ ph.2.-1 *: 'a_(mpart ph.1 + rho)) 0
   (add_ribbon p d.+1 i).
Proof.
move=> partp szp; rewrite mult_altern_symp_pol.
apply eq_bigr => i _ /=.
case Hrib : add_ribbon => [[sh h]|] /=.
  by rewrite (alt_straight_add_ribbon _ partp szp Hrib).
by rewrite (alt_straight_add_ribbon0 _ partp szp) // Hrib.
Qed.

Lemma mult_altern_pmap p d :
  is_part p -> size p <= n ->
  'a_(mpart p + rho) * (symp_pol n R d.+1) =
  \sum_(psh <- pmap (add_ribbon p d.+1) (iota 0 n))
   (-1) ^+ (psh.2).-1 *: 'a_(mpart psh.1 + rho).
Proof.
move=> partp szp; rewrite mult_altern_oapp //.
rewrite -(big_mkord xpredT (fun i => oapp _ 0 (add_ribbon p d.+1 i))).
by rewrite big_pmap /index_iota subn0.
Qed.


Section Bijection.

Variable (m : nat) (la : intpartn m).
Hypothesis (szla : size la <= n).
Variable nbox : nat.
Local Notation PP := (intpartn (m + nbox.+1)).

Fact add_ribbon_intpartn_subproof pos :
  is_part_of_n (m + nbox.+1)%N
               (oapp (fun p => p.1) [:: (m + nbox).+1]
                     (add_ribbon la nbox.+1 pos)).
Proof.
case Hrib : add_ribbon => [[res h]|] /=; last by rewrite addn0 addnS eqxx.
have:= is_part_of_add_ribbon (intpartnP la) Hrib => /andP[/eqP -> ->].
by rewrite addnC sumn_intpartn eqxx.
Qed.
Definition add_ribbon_intpartn pos :=
  match add_ribbon la nbox.+1 pos with
  | Some (_, h) => Some (IntPartN (add_ribbon_intpartn_subproof pos))
  | None => None
  end.

Fact ribbon_stop_subproof (mu : PP) :
  (if size mu <= n then (mindropeq la mu).-1 else 0%N) < n.
Proof.
case: (leqP (size mu) n) => // szmu.
case: mindropeq (mindropeq_leq la mu) => // md /= /leq_trans; apply.
by rewrite geq_max szla szmu.
Qed.
Definition ribbon_stop mu := Ordinal (ribbon_stop_subproof mu).


Lemma mult_altern_sympol :
  'a_(mpart la + rho) * (symp_pol n R nbox.+1) =
  \sum_(sh : PP | (size sh <= n) && (ribbon la sh))
   (-1) ^+ (ribbon_height la sh).-1 *: 'a_(mpart sh + rho).
Proof.
rewrite mult_altern_oapp //.
rewrite (bigID (fun i : 'I_n => add_ribbon la nbox.+1 i)) /=.
rewrite [X in _ + X = _]big1 ?addr0; last by move=> i; case: add_ribbon.
rewrite (reindex_omap ribbon_stop add_ribbon_intpartn) /=; first last.
  move=> i; rewrite /add_ribbon_intpartn.
  case Haddrib : {1 2}(add_ribbon la nbox.+1 i) => [[res h]|]//= _.
  congr Some; apply val_inj; rewrite /= Haddrib /=.
  rewrite (size_add_ribbon Haddrib) geq_max szla ltn_ord /=.
  rewrite (ribbon_on_mindropeq (intpartnP la) _ (add_ribbon_onP Haddrib)) //.
  exact: (is_part_add_ribbon _ Haddrib).
apply esym; apply: eq_big => mu.
  case leqP => Hszmu /=; first last.
  + rewrite /add_ribbon_intpartn.
    case Haddrib : {1 2}(add_ribbon la nbox.+1 0) => [[res h]|//=].
    rewrite andTb /=; case (altP (_ =P Some mu)) => // [[/(congr1 val) /=]].
    rewrite Haddrib /= => Heq.
    have := size_add_ribbon Haddrib; rewrite Heq => {}Heq.
    by move: Hszmu; rewrite Heq leq_max 2!ltnNge szla.
  + apply esym; case: (boolP (ribbon la mu)) => [Hrib | Hnrib].
    * have := ribbon_addE (intpartnP la) (intpartnP mu) Hrib.
      rewrite sumn_diff_shape ?ribbon_included // !sumn_intpartn addKn => Heq.
      rewrite Heq andTb /=; apply/eqP; rewrite /add_ribbon_intpartn.
      rewrite {1}Heq; congr Some; apply val_inj => /=.
      by rewrite Heq /=.
    * case Haddrib : (add_ribbon la nbox.+1 _) => [[res h]|//=].
      rewrite andTb /=; apply/negP => /eqP.
      rewrite /add_ribbon_intpartn {1}Haddrib => [[/(congr1 val) /=]].
      rewrite Haddrib /= => Heq.
      by move: Hnrib; rewrite -{}Heq (add_ribbonP _ Haddrib).
move=> /andP[-> Hrib].
have:= ribbon_addE (intpartnP la) (intpartnP mu) Hrib.
by rewrite sumn_diff_shape ?ribbon_included // !sumn_intpartn addKn => ->.
Qed.

End Bijection.

End MultAlternSymp.


Section MultSymsSympIDomain.

Variable n0 : nat.
Variable R : idomainType.

Local Notation n := n0.+1.
Local Notation rho := (rho n).
Local Notation "''a_' k" := (@alternpol n R 'X_[k]).

Lemma syms_sympM_idomain m (la : intpartn m) nbox :
  's[la] * 'p_(nbox.+1) =
  \sum_(sh : intpartn (m + nbox.+1) | (size sh <= n) && (ribbon la sh))
   (-1) ^+ (ribbon_height la sh).-1 *: 's[sh] :> {sympoly R[n]}.
Proof.
apply val_inj; case: (leqP (size la) n) => szla /=; first last.
  rewrite Schur_oversize // mul0r raddf_sum /=.
  apply/esym/big1 => mu /andP[szmu Hrib]; exfalso.
  move: Hrib => /ribbon_included/includedP[].
  by move/leq_trans/(_ szmu)/(leq_trans szla); rewrite ltnn.
apply: (mulfI (alt_rho_non0 n R)).
rewrite mulrA alt_SchurE // mult_altern_sympol //.
rewrite raddf_sum mulr_sumr; apply eq_bigr => mu /andP[szmu Hrib] /=.
by rewrite -scalerAr alt_SchurE.
Qed.

End MultSymsSympIDomain.


Section MultSymsSymp.

Variable n0 : nat.
Variable R : comRingType.

Local Notation n := n0.+1.
Local Notation rho := (rho n).
Local Notation "''a_' k" := (@alternpol n R 'X_[k]).

Lemma syms_sympM m (la : intpartn m) nbox :
  's[la] * 'p_(nbox.+1) =
  \sum_(sh : intpartn (m + nbox.+1) | (size sh <= n) && (ribbon la sh))
   (-1) ^+ (ribbon_height la sh).-1 *: 's[sh] :> {sympoly R[n]}.
Proof.
rewrite -(map_syms [rmorphism of intr]) -(map_symp [rmorphism of intr]).
rewrite -rmorphM syms_sympM_idomain rmorph_sum /=.
by under [LHS]eq_bigr do rewrite scale_map_sympoly rmorphX rmorphN1 map_syms.
Qed.

End MultSymsSymp.

