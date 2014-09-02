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
  have:= @plactcongr_equiv Alph => /equivalence_relP [] Hrefl Htrans.
  have:= @plactcongr_is_congr Alph => Hcongr.
  elim/last_ind: r l => [_ _ //= | r rn IHr] l Hrow Hl.
  have:= is_row_last Hrow; rewrite last_rcons => Hrnl.
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
  have:= @plactcongr_equiv Alph => /equivalence_relP [] Hrefl Htrans.
  have:= @plactcongr_is_congr Alph => Hcongr.
  elim/last_ind: r => [_ _ //= | r rn].
  case/lastP: r => [_ /=| r rn1].
  - move/and3P => [] Harn _ _ Hla; apply rule_gencongr => //=.
    by rewrite Harn Hla !mem_cat !mem_seq1 eq_refl /= !orbT.
  - move=> IH; rewrite -rcons_cons => Hrow Hla.
    have {IH} IH := (IH (is_row_rconsK Hrow) Hla).
    rewrite (@Htrans _ (a :: rcons (rcons (rcons r rn1) l) rn)).
    * move: IH; rewrite -!rcons_cons; by apply (congr_rcons Hcongr).
    * apply (congr_cons Hcongr); rewrite !rcons_rcons -!cats1 -!catA.
      apply (congr_catr Hcongr) => /=; apply rule_gencongr.
      have:= head_leq_last_row (is_row_rconsK Hrow); rewrite last_rcons => Harn1.
      have:= is_row_last Hrow. rewrite -rcons_cons last_rcons => Hrn1rn.
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
      by have:= leq_trans Hipos H1; rewrite ltnn.
    + by rewrite Hipos subnn.
Qed.

Lemma congr_bump r l :
  r != [::] -> is_row r -> bump r l -> r ++ [:: l] =Pl [:: bumped r l] ++ ins r l.
Proof.
  have:= @plactcongr_equiv Alph => /equivalence_relP [] Hrefl Htrans.
  have:= @plactcongr_is_congr Alph => Hcongr.
  move=> Hnnil Hrow Hbump.
  have:= bump_inspos_lt_size Hrow Hbump; set pos := (inspos r l) => Hpos.
  move: (cat_take_drop pos r) (is_row_take pos Hrow) (is_row_drop pos Hrow).
  move HL : (take pos r) => L; move HR : (drop pos r) => R.
  case: R HR => [_ H| rpos R' HR Hr HrowL HrowR]. (* R is not empty *)
    exfalso; move: H; rewrite -HL cats0 => H.
    have:= eq_refl (size r); by rewrite -{1}H size_take Hpos (ltn_eqF Hpos).
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
      have:= nth_lt_inspos H.
      by rewrite -(nth_take (n0 := pos) _ H) Hll nth_rcons ltnn eq_refl.
    * rewrite /ins -/pos -Hr; apply set_nth_LxR.
      by rewrite -HL size_take Hpos.
  + rewrite -Hr -catA; apply (congr_catr Hcongr).
    rewrite cats1 rcons_cons; apply (congr_row_2 HrowR).
    rewrite Hrpos; by apply lt_bumped.
Qed.

Theorem congr_Sch w : w =Pl (to_word (RS w)).
Proof.
  have:= @plactcongr_equiv Alph => /equivalence_relP [] Hrefl Htrans.
  have:= @plactcongr_is_congr Alph => Hcongr.
  elim/last_ind: w => [//= | w l0]; rewrite /RS rev_rcons /= -[RS_rev (rev w)]/(RS w) => H.
  rewrite (@Htrans _ (rcons (to_word (RS w)) l0)); last by apply congr_rcons.
  have:= is_tableau_RS w.
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
  have:= @plactcongr_equiv Alph => /equivalence_relP [] Hrefl Htrans /eqP Heq.
  rewrite (@Htrans _ (to_word (RS u))); last by apply congr_Sch.
  rewrite Heq; rewrite -(Htrans _ _ (congr_Sch v)); by apply Hrefl.
Qed.

Lemma perm_eq_RS w : perm_eq w (to_word (RS w)).
Proof. apply plactcongr_homog. by apply congr_Sch. Qed.

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

Theorem rembig_plactcongr u v : u =Pl v -> (rembig u) =Pl (rembig v).
Proof.
  have:= @plactcongr_equiv Alph => /equivalence_relP [] Hrefl Htrans.
  have:= @plactcongr_is_congr Alph => Hcongr.
  move: v; apply gencongr_ind; first by apply Hrefl.
  move=> a b1 c b2 => H Hplact.
  rewrite -(@Htrans (rembig (a ++ b1 ++ c))); last by rewrite -(Htrans _ _ H); apply Hrefl.
  have:= plact_homog b1 => {u H} /allP Heq; have {Heq} Heq := (Heq _ Hplact).
  have:= Heq; rewrite -(perm_cat2r c) => Heqc.
  have:= rembig_eq_permR _ Heqc => Htmp; have {Htmp} := (Htmp a) => [] [] [] -> ->.
  - apply Hcongr; by apply rule_gencongr.
  - apply (congr_catr Hcongr).
    have:= rembig_eq_permL _ Heq => Htmp; have {Htmp} := (Htmp c) => [] [] [] -> ->.
    * apply (congr_catl Hcongr); rewrite (rembig_plact Hplact); by apply Hrefl.
    * apply (congr_catl Hcongr); by apply rule_gencongr.
Qed.

Notation maxL := (foldl (@maxX Alph)).

Notation append_nth T b i := (set_nth [::] T i (rcons (nth [::] T i) b)).

Lemma shape_append_nth T b i : shape (append_nth T b i) = incr_nth (shape T) i.
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

Lemma inspos_rcons l r b : l <A b -> inspos r l = inspos (rcons r b) l.
Proof. elim: r => [/= -> //= | r0 r IHr]; by rewrite rcons_cons /= => /IHr ->. Qed.

Lemma bump_bumprow_rconsE l r b :
  is_row (rcons r b) -> l <A b -> bump r l ->
  let: (lres, rres) := bumprow r l in bumprow (rcons r b) l = (lres, rcons rres b).
Proof.
  move=> Hrowb Hl; have:= Hl => /inspos_rcons Hpos Hbump.
  have Hrow := is_row_rconsK Hrowb.
  have Hbumpb : bump (rcons r b) l by rewrite /bump last_rcons.
  rewrite (bump_bumprowE Hrow Hbump) (bump_bumprowE Hrowb Hbumpb).
  rewrite /bumped /ins -(inspos_rcons r Hl).
  have:= bump_inspos_lt_size Hrow Hbump => Hsize.
  by rewrite nth_rcons set_nth_rcons Hsize.
Qed.

Lemma nbump_bumprow_rconsE l r b :
  is_row (rcons r b) -> l <A b -> ~~bump r l ->
  let: (lres, rres) := bumprow r l in bumprow (rcons r b) l = (Some b, rres).
Proof.
  move=> Hrowb Hl; have:= Hl => /inspos_rcons Hpos Hnbump.
  have Hrow := is_row_rconsK Hrowb.
  have Hbumpb : bump (rcons r b) l by rewrite /bump last_rcons.
  rewrite (nbump_bumprowE Hrow Hnbump) (bump_bumprowE Hrowb Hbumpb).
  rewrite /bumped /ins -(inspos_rcons r Hl).
  have:= nbump_inspos_eq_size Hrow Hnbump => Hsize.
  by rewrite nth_rcons set_nth_rcons Hsize eq_refl ltnn rcons_set_nth.
Qed.

Fixpoint last_big t b :=
  if t is t0 :: t' then
    if last b t0 == b then 0
    else (last_big t' b).+1
  else 0.

Lemma maxLeq_to_word_hd t0 t b : maxLeq (to_word (t0 :: t)) b -> maxLeq t0 b.
Proof. rewrite /to_word rev_cons flatten_rcons; by apply maxLeq_catr. Qed.

Lemma maxLeq_to_word_tl t0 t b : maxLeq (to_word (t0 :: t)) b -> maxLeq (to_word t) b.
Proof. rewrite /to_word rev_cons flatten_rcons; by apply maxLeq_catl. Qed.

Lemma last_bigP t b i :
  is_tableau t -> maxLeq (to_word t) b ->
  reflect (last b (nth [::] t i) = b /\ forall j, j < i -> last b (nth [::] t j) <A b)
          (i == last_big t b).
Proof.
  move=> Htab Hmax; apply (iffP idP).
  + move/eqP ->; split.
    * elim: t Htab {Hmax} => [//= | t0 t IHt] /= /and4P [] _ _ _ Htab.
      case (altP (last b t0 =P b)) => [//= | _]; by apply IHt.
    * elim: t Htab Hmax => [//= | t0 t IHt] /= /and4P [] Hnnil _ _ Htab Hmax.
      case (altP (last b t0 =P b)) => [//= | H].
      case=> [/= _ | j].
      + have:= (maxLeq_to_word_hd Hmax); move: Hnnil H.
        case/lastP: t0 {Hmax} => [//= | t0 tn] _; rewrite last_rcons => H1 /maxLeq_last.
        by rewrite ltnX_neqAleqX H1.
      + rewrite /=; by apply IHt; last by apply (maxLeq_to_word_tl Hmax).
  + move=> []; elim: t i Htab Hmax => [/= i _ _| t0 t IHt].
    * case: i => [//= | i] /= _ H.
      exfalso; have:= H 0 (ltn0Sn _); by rewrite ltnXnn.
    * case=> [/= _ _ -> _| i]; first by rewrite eq_refl.
      move=> /= /and4P [] _ _ _ Htab Hmax Hlast Hj.
      have:= Hj 0 (ltn0Sn _) => /= /ltnX_eqF ->.
      apply (IHt _ Htab (maxLeq_to_word_tl Hmax) Hlast).
      move=> j; by apply (Hj j.+1).
Qed.

Lemma maxL_LbR a v L b R : a :: v = L ++ b :: R -> maxLeq L b -> maxLeq R b -> maxL a v = b.
Proof.
  move=> Hav HL HR; apply/eqP; rewrite eqn_leqX; apply /andP; split.
  - have:= in_maxL a v; rewrite Hav mem_cat inE => /orP []; last move/orP => [].
    * move: HL; by rewrite maxLeqAllP => /allP H/H{H}.
    * by move/eqP ->.
    * move: HR; by rewrite maxLeqAllP => /allP H/H{H}.
  - have:= maxLP a v => /allP; apply.
    by rewrite Hav mem_cat inE eq_refl orbT.
Qed.

Lemma maxLeq_is_row_rcons w b :
  maxLeq w b -> forall row, row \in RS w -> is_row (rcons row b).
Proof.
  move=> H row Hin; apply is_row_rcons.
  + move: Hin; have:= (is_tableau_RS w).
    elim: (RS w) => [//= | t0 t IHt] /= /and4P [] _ Hrow _ Htab.
    rewrite inE => /orP [].
    * by move/eqP => ->.
    * by apply IHt.
  + have: maxLeq (to_word (RS w)) b by rewrite (perm_eq_maxLeq (perm_eq_RS w)).
    rewrite /to_word; elim: (RS w) Hin => [//= | t0 t IHt] /=.
    rewrite inE rev_cons flatten_rcons => /orP [/eqP ->|].
    * move/maxLeq_catr; case/lastP: t0 => [//=| t0 tn].
      move/maxLeq_last; by rewrite last_rcons.
    * move=> Hrow /maxLeq_catl; by apply IHt.
Qed.

Lemma last_ins_lt r l b : l <A b -> last b r <A b -> last b (ins r l) <A b.
Proof.
  rewrite -!nth_last => Hl Hlast.
  rewrite (nth_any b l); first last.
    have : (ins r l) != [::] by apply set_nth_non_nil.
    by case : (ins r l).
  rewrite nth_set_nth size_set_nth /= maxnC /maxn ltnS.
  case (leqP (size r) (inspos r l)) => H /=; first by rewrite eq_refl.
  case (boolP ((size r).-1 == inspos r l)) => _; first exact Hl.
  by rewrite (nth_any l b); last by move: Hlast; case r => /=; first by rewrite ltnXnn.
Qed.

Lemma bumped_lt r b l : is_row r -> l <A b -> last b r <A b -> bumped r l <A b.
Proof.
  rewrite -!nth_last /bumped => /is_rowP Hrow Hl Hlast.
  case (ltnP (inspos r l) (size r)) => H.
  + rewrite (nth_any l b H).
    apply (@leqX_ltnX_trans _ (nth b r (size r).-1)); last exact Hlast.
    apply Hrow; move: H; by case: (size r).
  + by rewrite (nth_default _ H).
Qed.

Lemma last_big_append_nth t b lb :
  (forall j : nat, j < lb -> last b (nth [::] t j) <A b) ->
  last_big (append_nth t b lb) b = lb.
Proof.
  elim: t lb =>[/= | t0 t IHt /=].
  + case => [/= _| lb Hj /=]; first by rewrite eq_refl.
    exfalso; have:= Hj 0 (ltn0Sn _); by rewrite ltnXnn.
  + case => [/= _| lb Hj /=]; first by rewrite last_rcons eq_refl.
    rewrite (ltnX_eqF (Hj 0 (ltn0Sn _))).
    have {Hj} Hj j : j < lb -> last b (nth [::] t j) <A b by apply/(Hj j.+1).
    by rewrite (IHt _ Hj).
Qed.

Lemma bisimul_instab t l b lb :
  is_tableau t -> l <A b ->
  (forall row, row \in t -> is_row (rcons row b)) ->
  (forall j : nat, j < lb -> last b (nth [::] t j) <A b) ->
  let tres := (append_nth t b lb) in
  instab tres l = append_nth (instab t l) b (last_big (instab tres l) b).
Proof.
  elim: t l lb => [/= l lb _| t0 t IHt l lb Htab] Hl Hallrow.
  - case: lb => [_ /=| lb Hj]; first by rewrite Hl /= (ltnX_eqF Hl) eq_refl.
    exfalso; have:= (Hj 0 (ltn0Sn _)); by rewrite /= ltnXnn.
  - move: Htab => /= /and4P [] Hnnil Hrow0 _ Htab.
    case: lb => [/= _ {IHt Htab} | lb Hj /=].
    * have Hrow: is_row (rcons t0 b) by apply Hallrow; rewrite inE eq_refl.
      case: (boolP (bump t0 l)) => [Hbump | Hnbump].
      + have:= bump_bumprow_rconsE Hrow Hl Hbump.
        rewrite (bump_bumprowE Hrow0 Hbump) => ->.
        by rewrite /= last_rcons eq_refl.
      + have:= nbump_bumprow_rconsE Hrow Hl Hnbump.
        rewrite (nbump_bumprowE Hrow0 Hnbump) (nbump_ins_rconsE Hrow0 Hnbump) => ->.
        rewrite /= last_rcons (ltnX_eqF Hl) /= {Hrow0 Hrow Hnbump}.
        case: t Hallrow => [//= _ | t1 t Hallrow /=]; first by rewrite eq_refl.
        have : t1 \in [:: t0, t1 & t] by rewrite !inE eq_refl orbT.
        move/Hallrow/bumprow_rcons => -> /=.
        by rewrite last_rcons eq_refl /=.
    * have Hlast0:= Hj 0 (ltn0Sn _); rewrite /= in Hlast0.
      have {Hj} Hj j : j < lb -> last b (nth [::] t j) <A b by apply/(Hj j.+1).
      case: (boolP (bump t0 l)) => [Hbump | Hnbump].
      + rewrite (bump_bumprowE Hrow0 Hbump) /=.
        have Hbumped := bumped_lt Hrow0 Hl Hlast0.
        rewrite (ltnX_eqF (last_ins_lt Hl Hlast0)).
        have {Hallrow} Hallrow row : row \in t -> is_row (rcons row b).
          by move=> Hrow; apply Hallrow; rewrite inE Hrow orbT.
        by rewrite /= {1}(IHt _ _ Htab Hbumped Hallrow Hj).
      + rewrite (nbump_bumprowE Hrow0 Hnbump) /=.
        by rewrite (ltnX_eqF (last_ins_lt Hl Hlast0)) /= (last_big_append_nth Hj).
Qed.

Theorem rembig_RS_last_big a v :
  RS (a :: v) = append_nth (RS (rembig (a :: v)))
                           (maxL a v)
                           (last_big (RS (a :: v)) (maxL a v)).
Proof.
  have: a :: v != [::] by [].
  move Hrem : (rembig (a :: v)) => rem; move: Hrem => /eqP; rewrite eq_sym.
  move/rembigP => H/H{H} [] L [] b [] R [] -> Hav HL HR.
  rewrite (maxL_LbR Hav HL (maxLtnW HR)) Hav {a v Hav}.
  elim/last_ind: R HR => [/= _| R Rn IHR].
  + rewrite cats0 cats1.
    rewrite [RS (rcons L b)]/RS rev_rcons /= -[RS_rev (rev L)]/(RS L).
    case HRS : (instab (RS L)) => [| tr0 tr /=].
    * exfalso; move: HRS; case: (RS L) => [//= | t0 t /=].
      by case: (bumprow t0 b) => [[] u v].
    * move: HRS; case HRSL : (RS L) => [//= | t0 t /=].
      - move=> [] <- <- /=; by rewrite eq_refl.
      - have Hrow: is_row (rcons t0 b).
          have := maxLeq_is_row_rcons HL; rewrite HRSL; apply; by rewrite inE eq_refl orTb.
        rewrite (bumprow_rcons Hrow).
        move=> [] <- <-; by rewrite last_rcons eq_refl /=.
  + move=> Hmax; have HmaxR:= (maxLtn_rconsK Hmax); move: Hmax => /maxLtn_last => HRnb.
    rewrite -rcons_cons -!rcons_cat /RS !rev_rcons /=.
    rewrite -[RS_rev (rev (L ++ b :: R))]/(RS (L ++ b :: R))
            -[RS_rev (rev (L ++ R))]/(RS (L ++ R)).
    have {IHR} := IHR HmaxR => /=.
    move Hlb : (last_big (RS (L ++ b :: R)) b) => lb IHR.
    move: Hlb => /eqP; rewrite eq_sym => /last_bigP Htmp.
    have Htmp2 : maxLeq (to_word (RS (L ++ b :: R))) b.
      apply (perm_eq_maxLeq (perm_RS (L ++ b :: R))).
      move: HL; case L => [/= _ | L0 L' /=]; first by rewrite (maxLeqL (maxLtnW HmaxR)).
      by rewrite maxL_cat (maxLeqL (maxLtnW HmaxR)) => /maxX_idPr ->.
    have {Htmp Htmp2} := Htmp (is_tableau_RS (L ++ b :: R)) Htmp2 => [] [] _.
    rewrite IHR => {IHR} Hj.
    apply (bisimul_instab (is_tableau_RS (L ++ R)) HRnb).
    - apply maxLeq_is_row_rcons; apply (maxLeq_cat HL); by apply maxLtnW.
      move=> j Hjlb; have:= Hj j Hjlb; by rewrite nth_set_nth /= (ltn_eqF Hjlb).
Qed.

Theorem rembig_RS a v :
  exists i, RS (a :: v) = append_nth (RS (rembig (a :: v))) (maxL a v) i.
Proof. exists (last_big (RS (a :: v)) (maxL a v)); by apply rembig_RS_last_big. Qed.

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
  have:= perm_eq_size (gencongr_homog Hpl) => /esym; rewrite Hu.
  elim: n u v Hpl Hu => [| n IHn] u v;
    first by move=> _ /eqP/nilP -> /eqP/nilP ->; rewrite /RS.
  move=> Hpl Hu Hv.
  have:= size_rembig u; rewrite Hu /= => Hszu.
  have:= size_rembig v; rewrite Hv /= => Hszv.
  have {IHn} := IHn _ _ (rembig_plactcongr Hpl) Hszu Hszv => /eqP {Hszu Hszv}.
  case: u Hu Hpl => [//= | u0 u'] _.
  case: v Hv     => [//= | v0 v'] _ => Hpl Hplrem.
  have:= rembig_RS u0 u' => [] [] iu Hiu.
  have:= rembig_RS v0 v' => [] [] iv; rewrite -Hplrem {Hplrem} => Hiv.
  rewrite -(maxL_perm_eq (gencongr_homog Hpl)) in Hiv.
  have:= plactic_shapeRS Hpl.
  rewrite Hiu Hiv {Hiu Hiv} !shape_append_nth => H.
  by rewrite -(incr_nth_inj H).
Qed.

End GreenInvariants.


