Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm.
Require Import subseq partition ordtype schensted congr.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bool.

Notation "x <=A y" := (x <= y)%Ord (at level 70, y at next level).
Notation "x >=A y" := (x >= y)%Ord (at level 70, y at next level, only parsing).
Notation "x <A y"  := (x < y)%Ord (at level 70, y at next level).
Notation "x >A y"  := (x > y)%Ord (at level 70, y at next level, only parsing).

Section Defs.

(*
Notation "[A m <= n < p ]" := ((m <=A n) && (n <A p)) (at level 71).
Notation "[A m <= n <= p ]" := ((m <=A n) && (n <=A p)) (at level 71).
Notation "[A m < n <= p ]" := ((m <A n) && (n <=A p)) (at level 71).
Notation "[A m < n < p ]" := ((m <A n) && (n <A p)) (at level 71).
*)

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w : word.

Definition plact1 :=
  fun s => match s return seq word with
             | [:: a; c; b] => if (a <= b < c)%Ord then [:: [:: c; a; b]] else [::]
             | _ => [::]
           end.

Definition plact1i :=
  fun s => match s return seq word with
             | [:: c; a; b] => if (a <= b < c)%Ord then [:: [:: a; c; b]] else [::]
             | _ => [::]
           end.

Definition plact2 :=
  fun s => match s return seq word with
             | [:: b; a; c] => if (a < b <= c)%Ord then [:: [:: b; c; a]] else [::]
             | _ => [::]
           end.

Definition plact2i :=
  fun s => match s return seq word with
             | [:: b; c; a] => if (a < b <= c)%Ord then [:: [:: b; a; c]] else [::]
             | _ => [::]
           end.

Lemma plact1P u v :
  reflect (exists a b c,
             [/\ (a <= b < c)%Ord, u = [:: a; c; b] & v = [:: c; a; b] ] )
          (v \in plact1 u).
Proof.
  apply (iffP idP).
  + case: u => [//=|u0[//=|u1[//=|u2[]//=]]]; case H : ((u0 <= u2 < u1)%Ord).
    - rewrite mem_seq1 => /eqP ->; by exists u0; exists u2; exists u1.
    - by rewrite in_nil.
  + move=> [] a [] b [] c [] H -> ->; by rewrite /= H mem_seq1 eq_refl.
Qed.

Lemma plact1iP u v :
  reflect (exists a b c,
             [/\ (a <= b < c)%Ord, v = [:: a; c; b] & u = [:: c; a; b] ] )
          (v \in plact1i u).
Proof.
  apply (iffP idP).
  + case: u => [//=|u0[//=|u1[//=|u2[]//=]]]; case H : ((u1 <= u2 < u0)%Ord).
    - rewrite mem_seq1 => /eqP ->; by exists u1; exists u2; exists u0.
    - by rewrite in_nil.
  + move=> [] a [] b [] c [] H -> ->; by rewrite /= H mem_seq1 eq_refl.
Qed.


Lemma plact2P u v :
  reflect (exists a b c,
             [/\ (a < b <= c)%Ord, u = [:: b; a; c] & v = [:: b; c; a] ] )
          (v \in plact2 u).
Proof.
  apply (iffP idP).
  + case: u => [//=|u0[//=|u1[//=|u2[]//=]]]; case H : ((u1 < u0 <= u2)%Ord).
    - rewrite mem_seq1 => /eqP ->; by exists u1; exists u0; exists u2.
    - by rewrite in_nil.
  + move=> [] a [] b [] c [] H -> ->; by rewrite /= H mem_seq1 eq_refl.
Qed.

Lemma plact2iP u v :
  reflect (exists a b c,
             [/\ (a < b <= c)%Ord, v = [:: b; a; c] & u = [:: b; c; a] ] )
          (v \in plact2i u).
Proof.
  apply (iffP idP).
  + case: u => [//=|u0[//=|u1[//=|u2[]//=]]]; case H : ((u2 < u0 <= u1)%Ord).
    - rewrite mem_seq1 => /eqP ->; by exists u2; exists u0; exists u1.
    - by rewrite in_nil.
  + move=> [] a [] b [] c [] H -> ->; by rewrite /= H mem_seq1 eq_refl.
Qed.

Lemma plact1I u v : u \in plact1 v <-> v \in plact1i u.
Proof.
  split => [/plact1P | /plact1iP] [] a [] b [] c [] H -> -> => /=;
    by rewrite H mem_seq1 eq_refl.
Qed.

Lemma plact2I u v : u \in plact2 v <-> v \in plact2i u.
Proof.
  split => [/plact2P | /plact2iP] [] a [] b [] c [] H -> -> => /=;
    by rewrite H mem_seq1 eq_refl.
Qed.

Definition plactrule := [fun s => plact1 s ++ plact1i s ++ plact2 s ++ plact2i s].

Lemma plactruleP u v :
  reflect ([\/ v \in plact1 u, v \in plact1i u, v \in plact2 u | v \in plact2i u ])
          (v \in plactrule u).
Proof.
  apply (iffP idP).
  + by rewrite /plactrule /= !mem_cat => /or4P.
  + by rewrite /plactrule /= !mem_cat => H; apply /or4P.
Qed.

Lemma plactrule_sym u v : v \in (plactrule u) -> u \in (plactrule v).
Proof.
  move/plactruleP => [] /=; rewrite !mem_cat.
  by rewrite plact1I => ->; rewrite !orbT.
  by rewrite -plact1I => ->.
  by rewrite plact2I => ->; rewrite !orbT.
  by rewrite -plact2I => ->; rewrite !orbT.
Qed.

Lemma plact1_homog : forall u : word, all (perm_eq u) (plact1 u).
Proof.
  move=> u; apply /allP => v /plact1P.
  move=> [] a [] b [] c [] /andP [] H1 H2 -> -> /=; rewrite /perm_eq /=.
  rewrite !eq_refl ![c == a]eq_sym ![c == b]eq_sym ![b == a]eq_sym /=.
  case Hab : (a == b);
      by rewrite (ltnX_eqF H2) (ltnX_eqF (leqX_ltnX_trans H1 H2)) !eq_refl /=.
Qed.

Lemma plact1i_homog : forall u : word, all (perm_eq u) (plact1i u).
Proof.
  move=> u; apply /allP => v /plact1iP.
  move=> [] a [] b [] c [] /andP [] H1 H2 -> -> /=; rewrite /perm_eq /=.
  rewrite !eq_refl ![c == a]eq_sym ![c == b]eq_sym ![b == a]eq_sym /=.
  case Hab : (a == b);
      by rewrite (ltnX_eqF H2) (ltnX_eqF (leqX_ltnX_trans H1 H2)) !eq_refl /=.
Qed.

Lemma plact2_homog : forall u : word, all (perm_eq u) (plact2 u).
Proof.
  move=> u; apply /allP => v /plact2P.
  move=> [] a [] b [] c [] /andP [] H1 H2 -> -> /=; rewrite /perm_eq /=.
  rewrite !eq_refl ![c == a]eq_sym ![c == b]eq_sym ![b == a]eq_sym /=.
  case Hab : (b == c);
      by rewrite (ltnX_eqF H1) (ltnX_eqF (ltnX_leqX_trans H1 H2)) !eq_refl /=.
Qed.

Lemma plact2i_homog : forall u : word, all (perm_eq u) (plact2i u).
Proof.
  move=> u; apply /allP => v /plact2iP.
  move=> [] a [] b [] c [] /andP [] H1 H2 -> -> /=; rewrite /perm_eq /=.
  rewrite !eq_refl ![c == a]eq_sym ![c == b]eq_sym ![b == a]eq_sym /=.
  case Hab : (b == c);
      by rewrite (ltnX_eqF H1) (ltnX_eqF (ltnX_leqX_trans H1 H2)) !eq_refl /=.
Qed.

Lemma plact_homog : forall u : word, all (perm_eq u) (plactrule u).
Proof.
  move=> u; by rewrite !all_cat plact1_homog plact1i_homog plact2_homog plact2i_homog.
Qed.

Definition plactcongr := (gencongr plact_homog).

Lemma plactcongr_equiv : equivalence_rel plactcongr.
Proof. apply gencongr_equiv; by apply plactrule_sym. Qed.

Lemma plactcongr_is_congr : congruence_rel plactcongr.
Proof. apply gencongr_is_congr; by apply plactrule_sym. Qed.

Lemma plactcongr_homog u v : v \in plactcongr u -> perm_eq u v.
Proof. by apply gencongr_homog. Qed.

Lemma size_plactcongr u v : v \in plactcongr u -> size u = size v.
Proof. by move/plactcongr_homog/perm_eq_size. Qed.

End Defs.

Section RSToPlactic.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Notation "a =Pl b" := (plactcongr a b) (at level 70).

Lemma rcons_rcons w a b : rcons (rcons w a) b = w ++ [:: a; b].
Proof. by rewrite -!cats1 -catA cat1s. Qed.

Lemma congr_row_1 r b l :
  is_row (rcons r l) -> l <A b -> rcons (rcons r b) l =Pl b :: rcons r l.
Proof.
  have:= (@plactcongr_equiv Alph) => /equivalence_relP [] Hrefl Htrans.
  have:= (@plactcongr_is_congr Alph) => Hcongr.
  elim/last_ind: r l => [_ _ //= | r rn IHr] l Hrow Hl.
  have := (is_row_last Hrow); rewrite last_rcons => Hrnl.
  rewrite (@Htrans _ (rcons (rcons (rcons r b) rn) l)).
  - rewrite -rcons_cons; apply (congr_rcons Hcongr).
    apply (IHr _ (is_row_rconsK Hrow)).
    exact (leqX_ltnX_trans Hrnl Hl).
  - rewrite !rcons_rcons -!cats1 -!catA !cat1s.
    apply (congr_catr Hcongr); apply rule_gencongr => /=.
    by rewrite Hl Hrnl !mem_cat !mem_seq1 eq_refl.
 Qed.

Lemma congr_row_2 a r l :
  is_row (a :: r) -> l <A a -> a :: rcons r l =Pl a :: l :: r.
Proof.
  have:= (@plactcongr_equiv Alph) => /equivalence_relP [] Hrefl Htrans.
  have:= (@plactcongr_is_congr Alph) => Hcongr.
  elim/last_ind: r => [_ _ //= | r rn].
  case/lastP: r => [_ /=| r rn1].
  - move=> /and3P [] Harn _ _ Hla; apply rule_gencongr => //=.
    by rewrite Harn Hla !mem_cat !mem_seq1 eq_refl /= !orbT.
  - move=> IH; rewrite -rcons_cons => Hrow Hla.
    have {IH} IH := (IH (is_row_rconsK Hrow) Hla).
    rewrite (@Htrans _ (a :: rcons (rcons (rcons r rn1) l) rn)).
    * move: IH; rewrite -!rcons_cons; by apply (congr_rcons Hcongr).
    * apply (congr_cons Hcongr); rewrite !rcons_rcons -!cats1 -!catA.
      apply (congr_catr Hcongr) => /=; apply rule_gencongr.
      have := head_leq_last_row (is_row_rconsK Hrow); rewrite last_rcons => Harn1.
      have := is_row_last Hrow. rewrite -rcons_cons last_rcons => Hrn1rn.
      by rewrite /= Hrn1rn (ltnX_leqX_trans Hla Harn1) !mem_cat !mem_seq1 eq_refl /= !orbT.
Qed.

Lemma set_nth_LxR L c R l pos :
  (size L) = pos -> set_nth l (L ++ c :: R) pos l = L ++ l :: R.
Proof.
  move Hr : (L ++ c :: R) => r Hsize.
  have Hpos : pos < size r
    by rewrite -Hsize -Hr size_cat /= -addSnnS -{1}[(size L).+1]addn0 leq_add2l.
  have Hsizeset : size (set_nth l r pos l) = size r.
    rewrite size_set_nth maxnC /maxn ltnS.
    by move: Hpos; rewrite ltnNge => /negbTE => ->.
  apply (eq_from_nth (x0 := l)) => [| i].
  - rewrite (_ : size (_ ++ _ :: _) = size r); last by rewrite -Hr !size_cat.
    by rewrite Hsizeset.
  - rewrite Hsizeset nth_set_nth -/pos nth_cat Hsize /= => Hi.
    case (ltngtP i pos) => Hipos.
    + by rewrite -Hr nth_cat Hsize Hipos.
    + rewrite -Hr nth_cat Hsize.
      have:= ltnW Hipos; rewrite leqNgt => /negbTE ->.
      case H : (i - pos) => [|//=].
      exfalso; have H1 : i <= pos by rewrite /leq H.
      by have:= (leq_trans Hipos H1); rewrite ltnn.
    + by rewrite Hipos subnn.
Qed.

Lemma congr_bump r l :
  r != [::] -> is_row r -> bump r l -> r ++ [:: l] =Pl [:: bumped r l] ++ ins r l.
Proof.
  have:= (@plactcongr_equiv Alph) => /equivalence_relP [] Hrefl Htrans.
  have:= (@plactcongr_is_congr Alph) => Hcongr.
  move=> Hnnil Hrow Hbump.
  have := (bump_inspos_lt_size Hrow Hbump); set pos := (inspos r l) => Hpos.
  move: (cat_take_drop pos r) (is_row_take pos Hrow) (is_row_drop pos Hrow).
  move HL : (take pos r) => L; move HR : (drop pos r) => R.
  case: R HR => [_ H| rpos R' HR Hr HrowL HrowR]. (* R is not empty *)
    exfalso; move: H; rewrite -HL cats0 => H.
    have:= (eq_refl (size r)); by rewrite -{1}H size_take Hpos (ltn_eqF Hpos).
  have Hrpos : (rpos = bumped r l)
    by rewrite /bumped -{1}Hr nth_cat -HL size_take Hpos /pos ltnn subnn.
  rewrite (@Htrans _ (L ++ [:: rpos, l & R'])).
  + rewrite (_ : ins r l = L ++ l :: R').
    * rewrite -[[:: rpos, l & R']]cat1s -![l :: R']cat1s !catA.
      apply (@congr_catl _ _ Hcongr _ _ R').
      rewrite -Hrpos !cats1 cat1s rcons_cons.
      apply congr_row_1; last by rewrite Hrpos; apply lt_bumped.
      apply (is_row_rcons HrowL).
      case/lastP: L HL {Hr HrowL} => [//= | L ll Hll]; rewrite last_rcons.
      have H : (size L) < pos by have:= size_take pos r; rewrite Hpos Hll size_rcons => <-.
      have:= (nth_lt_inspos H).
      by rewrite -(nth_take (n0 := pos) _ H) Hll nth_rcons ltnn eq_refl.
    * rewrite /ins -/pos -Hr; apply set_nth_LxR.
      by rewrite -HL size_take Hpos.
  + rewrite -Hr -catA; apply (congr_catr Hcongr).
    rewrite cats1 rcons_cons; apply (congr_row_2 HrowR).
    rewrite Hrpos; by apply lt_bumped.
Qed.

Theorem congr_Sch w : w =Pl (to_word (RS w)).
Proof.
  have:= (@plactcongr_equiv Alph) => /equivalence_relP [] Hrefl Htrans.
  have:= (@plactcongr_is_congr Alph) => Hcongr.
  elim/last_ind: w => [//= | w l0]; rewrite /RS rev_rcons /= -[RS_rev (rev w)]/(RS w) => H.
  rewrite (@Htrans _ (rcons (to_word (RS w)) l0)); last by apply congr_rcons.
  have:= (is_tableau_RS w).
  elim: (RS w) l0 {H} => [//= | r0 t IHt] l0 /= /and4P [] Ht0 Hrow0 _ Htab.
  case (boolP (bump r0 l0)) => [Hbump | Hnbump].
  - rewrite (bump_bumprowE Hrow0 Hbump); have {IHt} := (IHt (bumped r0 l0) Htab).
    rewrite /to_word !rev_cons -!cats1 !flatten_cat /= !cats0 -catA => IHt.
    rewrite (Htrans _ (flatten (rev t) ++ [:: bumped r0 l0] ++ (ins r0 l0))).
    * rewrite catA; by apply congr_catl.
    * apply (congr_catr Hcongr); by apply congr_bump.
  - rewrite (nbump_bumprowE Hrow0 Hnbump) {IHt}.
    rewrite /to_word !rev_cons -!cats1 !flatten_cat /= !cats0 -catA cats1.
    apply (congr_catr Hcongr); by rewrite nbump_ins_rconsE.
Qed.

Theorem Sch_plact u v : RS u == RS v -> plactcongr u v .
Proof.
  have:= (@plactcongr_equiv Alph) => /equivalence_relP [] Hrefl Htrans /eqP Heq.
  rewrite (@Htrans _ (to_word (RS u))); last by apply congr_Sch.
  rewrite Heq; rewrite -(Htrans _ _ (congr_Sch v)); by apply Hrefl.
Qed.

End RSToPlactic.

Section RemoveBig.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Lemma rembig_plact1 u v : u \in (plact1 v) -> rembig u = rembig v.
Proof.
  move/plact1P => [] a [] b [] c [] /andP [] Hab Hbc -> -> /=.
  have:= Hab => /maxX_idPr ->; rewrite Hbc.
  have:= ltnXW Hbc => /maxX_idPl ->.
  have:= ltnXW (leqX_ltnX_trans Hab Hbc); by rewrite leqXNgtnX => /negbTE ->.
Qed.

Lemma rembig_plact1i u v : u \in (plact1i v) -> rembig u = rembig v.
Proof. by rewrite -plact1I => /rembig_plact1 ->. Qed.

Lemma rembig_plact2 u v : u \in (plact2 v) -> rembig u = rembig v.
Proof.
  move/plact2P => [] a [] b [] c [] /andP [] Hab Hbc -> -> /=.
  have:= ltnX_leqX_trans Hab Hbc => Hac; rewrite Hac maxXC.
  have {Hac} Hac := ltnXW Hac; have:= Hac => /maxX_idPr ->.
  move: Hac; rewrite leqXNgtnX => /negbTE ->.
  move: Hbc; by rewrite leqXNgtnX => /negbTE ->.
Qed.

Lemma rembig_plact2i u v : u \in (plact2i v) -> rembig u = rembig v.
Proof. by rewrite -plact2I => /rembig_plact2 ->. Qed.

Lemma rembig_plact u v : u \in (plactrule _ v) -> rembig u = rembig v.
Proof.
  move/plactruleP => [].
  by apply rembig_plact1. by apply rembig_plact1i.
  by apply rembig_plact2. by apply rembig_plact2i.
Qed.

Notation "a =Pl b" := (plactcongr a b) (at level 70).

Theorem rembig_congr u v : u =Pl v -> (rembig u) =Pl (rembig v).
Proof.
  have:= (@plactcongr_equiv Alph) => /equivalence_relP [] Hrefl Htrans.
  have:= (@plactcongr_is_congr Alph) => Hcongr.
  move: v; apply gencongr_ind; first by apply Hrefl.
  move=> a b1 c b2 => H Hplact.
  rewrite -(@Htrans (rembig (a ++ b1 ++ c))); last by rewrite -(Htrans _ _ H); apply Hrefl.
  have:= (plact_homog b1) => {u H} /allP Heq; have {Heq} Heq := (Heq _ Hplact).
  have:= Heq; rewrite -(perm_cat2r c) => Heqc.
  have:= (rembig_eq_permR _ Heqc) => Htmp; have {Htmp} := (Htmp a) => [] [] [] -> ->.
  - apply Hcongr; by apply rule_gencongr.
  - apply (congr_catr Hcongr).
    have:= (rembig_eq_permL _ Heq) => Htmp; have {Htmp} := (Htmp c) => [] [] [] -> ->.
    * apply (congr_catl Hcongr); rewrite (rembig_plact Hplact); by apply Hrefl.
    * apply (congr_catl Hcongr); by apply rule_gencongr.
Qed.

Notation maxL := (foldl (@maxX Alph)).

Notation appi T b i := (set_nth [::] T i (rcons (nth [::] T i) b)).

Lemma shape_appi T b i : shape (appi T b i) = incr_nth (shape T) i.
Proof.
  rewrite /shape /=; apply (@eq_from_nth _ 0).
  + rewrite size_map size_set_nth size_incr_nth size_map /maxn.
    case (ltngtP i.+1 (size T)).
    - by move/ltnW ->.
    - by rewrite ltnNge => /negbTE ->.
    - by move => ->; rewrite leqnn.
  + move=> j Hi.
    rewrite nth_incr_nth (nth_map [::]) /=; last by move: Hi; rewrite size_map.
    rewrite nth_set_nth /= eq_sym.
    have -> : nth 0 [seq size i | i <- T] j = size (nth [::] T j).
      case (ltnP j (size T)) => Hcase.
      * by rewrite (nth_map [::] _ _ Hcase).
      * by rewrite (nth_default _ Hcase) nth_default; last by rewrite size_map.
    case (altP (i =P j)) => [->| Hij].
    - by rewrite size_rcons add1n.
    - by rewrite add0n.
Qed.

Lemma instab_appi b l n w :
  l <A b -> maxLeq w b -> is_tableau (appi (RS w) b n) ->
  exists i : nat,
    instab (appi (RS w) b n) l = appi (instab (RS w) l) b i.
Proof.
  admit.
  (*
  elim: n w l => [| n IHn] w l.
  case H : (instabnrow (RS w) l) => [t nrow].
  case (altP (i =P nrow)) => [-> | Hnrow] Htab.
  * exists nrow.+1 => {i}.
  * exists i.
  *)
Qed.

Theorem rembig_RS a v :
  exists i, RS (a :: v) = appi (RS (rembig (a :: v))) (maxL a v) i.
Proof.
  have Htmp : a::v != [::] by [].
  have:= eq_refl (rembig (a :: v)) => /(rembigP _ Htmp) [] L [] b [] R [] -> Hav HL HR {Htmp}.
  rewrite (maxL_LbR Hav HL (maxLtnW HR)) Hav {v Hav}.
  elim/last_ind: R HR => [_ | R Rn IHR HR].
  + exists 0; rewrite !cats0 cats1 {1}/RS rev_rcons [LHS]/= -[RS_rev (rev L)]/(RS L).
    have:= is_tableau_RS L; case H : (RS L) => [//= | t0 t] /= /and4P [].
    case/lastP: t0 H => [//= | t0' t0n] H _ Hrow _ _.
    suff Hnbump : (~~ bump (rcons t0' t0n) b)
      by rewrite (nbump_bumprowE Hrow Hnbump) (nbump_ins_rconsE Hrow Hnbump).
    have := (perm_eq_maxLeq (gencongr_homog (congr_Sch L)) HL).
    rewrite H {H} /bump /= last_rcons -leqXNgtnX.
    have := (maxLP b (to_word (rcons t0' t0n :: t))) => /allP Htmp.
    have : t0n \in b :: to_word (rcons t0' t0n :: t).
      rewrite inE /to_word; apply /orP; right.
      apply /flattenP; exists (rcons t0' t0n); first by rewrite mem_rev /= inE eq_refl.
      by rewrite mem_rcons inE eq_refl.
    move/Htmp => {Htmp} /=.
    case: (to_word _) => [//= | x0 x /=].
    rewrite -maxXL => H1 H2; by move: H2 H1 => /maxX_idPl ->.
  + have {IHR} := IHR (maxLtn_rconsK HR) => [] [] i IHR.
    have := is_tableau_RS (L ++ b :: R).
    rewrite -rcons_cons -!rcons_cat /RS !rev_rcons /= -[RS_rev (rev (L ++ R))]/(RS (L ++ R)).
    rewrite -[RS_rev (rev (L ++ b :: R))]/(RS (L ++ b :: R)) IHR {IHR}.
    have:= (maxLeq_cat HL (maxLtnW (maxLtn_rconsK HR))).
    move: (L ++ R) => W; have := (maxLtn_last HR) => {HR HL R L}.
    by apply instab_appi.
Qed.

End RemoveBig.



Section GreenInvariants.

Variable Alph : ordType.
Let word := seq Alph.

Implicit Type a b c : Alph.
Implicit Type u v w r : word.

Notation "a =Pl b" := (plactcongr a b) (at level 70).

Theorem plactic_shapeRS u v : u =Pl v -> shape (RS u) = shape (RS v).
Proof.
  admit. (* Needs Green's invariant *)
Qed.

Theorem plact_Sch u v : plactcongr u v <-> RS u == RS v.
Proof.
  split; last by apply Sch_plact.
  move Hu : (size u) => n Hpl.
  have:= (perm_eq_size (gencongr_homog Hpl)) => /esym; rewrite Hu.
  elim: n u v Hpl Hu => [| n IHn] u v;
    first by move=> _ /eqP/nilP -> /eqP/nilP ->; rewrite /RS.
  move=> Hpl Hu Hv.
  have:= (size_rembig u); rewrite Hu /= => Hszu.
  have:= (size_rembig v); rewrite Hv /= => Hszv.
  have {IHn} := IHn _ _ (rembig_congr Hpl) Hszu Hszv => /eqP Hplrem {Hszu Hszv}.
  move: Hu; case Hu : u => [//= | u0 u'] _.
  move: Hv; case Hv : v => [//= | v0 v'] _.
  have:= rembig_RS u0 u' => [] [] iu; rewrite -Hu => Hiu.
  have:= rembig_RS v0 v' => [] [] iv; rewrite -Hv -Hplrem {Hplrem} => Hiv.
  rewrite Hu Hv in Hpl; rewrite -(maxL_perm_eq (gencongr_homog Hpl)) in Hiv.
  suff H : iu = iv by rewrite Hiu Hiv -H.
  apply /eqP; rewrite -Hu -Hv in Hpl; have:= (plactic_shapeRS Hpl) => /eqP.
  rewrite Hiu Hiv {Hu Hv Hiu Hiv} !shape_appi; move: (shape _) => sh /eqP Hsh.
  case (altP (iu =P iv)) => [//= | /negbTE Hdiff].
  have:= eq_refl (nth 0 (incr_nth sh iu) iu).
  by rewrite {2}Hsh !nth_incr_nth eq_refl [iv == iu]eq_sym Hdiff eqn_add2r.
Qed.

End GreenInvariants.


