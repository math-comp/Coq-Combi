(** * program.v : the probabilistic program finding a corner *)

Add Rec LoadPath "ALEA/src" as ALEA.
Add Rec LoadPath "../Combi/LRrule".

Require Import Misc Ccpo Qmeasure.
Set Implicit Arguments.
Local Open Scope O_scope.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype rat 
               finfun ssrnum ssralg ssrint bigop.
Local Open Scope ring_scope.
Require Import partition.
Require Import equerre.
Local Open Scope rat_scope.

(* Require Import equerre. *)

Section FindCorner.

Variable p : intpart.

Fact is_part_p : is_part p.
apply intpartP.
Save.
Hint Resolve is_part_p.

Definition is_in_hook (i j:nat) (k l : nat) := 
     ((i == k) && (j < l < nth 0 p i))%N || ((j == l) && (i < k < haut p j))%N.

Lemma in_hook_part (i j:nat) (k l : nat) :
   is_in_part p i j -> is_in_hook i j k l -> is_in_part p k l.
Proof.
  rewrite /is_in_part /is_in_hook => Hj /orP [] /and3P [] /eqP <- // H1 H2.
  by rewrite ltnNge (haut_nth _ (intpartP p)) -ltnNge.
Save.

Definition hook_next_seq i j : seq (nat+nat) := 
    [seq (inl k) | k <- iota (i.+1) ((haut p j).-1 - i)]++
    [seq (inr k) | k <- iota (j.+1) ((nth O p i).-1 - j)].

(* Lemma size_hook : forall i j, size (hook_seq i j) == hook' i j. *)

Definition hook_next i j n : nat * nat := 
    match n with inl k => (k,j) | inr k => (i,k) end.

Definition hook_seq i j := [seq (hook_next i j n) | n <- hook_next_seq i j].

Lemma size_hook_seq_next_eq i j : size (hook_seq i j)=size (hook_next_seq i j).
apply: size_map.
Save.

Lemma in_hook_seq (i j:nat) (k l : nat) :
   (k,l) \in (hook_seq i j) -> is_in_hook i j k l.
Proof.
  rewrite /hook_seq /is_in_hook => /mapP [] x.
  rewrite mem_cat => /orP [] /mapP [] u; rewrite mem_iota => Hu -> /= [] -> -> {x k l}.
  - rewrite eq_refl /=; apply/orP; right.
    move: Hu; case: (haut p j) => [|n] /=.
    + rewrite sub0n addn0 ltnS => /andP [] /leq_trans => H/H{H}.
      by rewrite ltnn.
    + rewrite addSn !ltnS.
      case: (leqP i n) => [Hi | /ltnW Hi].
      * by rewrite (subnKC Hi).
      * move: Hi; rewrite {1}/leq => /eqP ->.
        rewrite addn0 => /andP [] /leq_trans => H/H{H}.
      by rewrite ltnn.
  - rewrite eq_refl /=; apply/orP; left.
    move: Hu; case: (nth O p i) => [|n] /=.
    + rewrite sub0n addn0 ltnS => /andP [] /leq_trans => H/H{H}.
      by rewrite ltnn.
    + rewrite addSn !ltnS.
      case: (leqP j n) => [Hj | /ltnW Hj].
      * by rewrite (subnKC Hj).
      * move: Hj; rewrite {1}/leq => /eqP ->.
        rewrite addn0 => /andP [] /leq_trans => H/H{H}.
      by rewrite ltnn.
Save.

Lemma hook_seq_empty (i j:nat) : 
      is_in_part p i j -> (hook_seq i j == [::])%B 
      -> (j == lindex p i)%B && is_out_corner p i.
Proof.
  rewrite /is_in_part => Hpart.
  rewrite /hook_seq => /eqP/nilP; rewrite /nilp size_map.
  rewrite /hook_next_seq size_cat !size_map.
  rewrite addn_eq0 !size_iota /lindex => /andP [].
  rewrite /is_out_corner => Hhaut Hnth.
  apply/andP; split.
  - apply/eqP; apply anti_leq.
    rewrite {2}/leq Hnth andbT.
    by rewrite -ltnS (ltn_predK Hpart).
  - move: Hnth; rewrite subn_eq0 -ltnS (ltn_predK Hpart) => Hnth.
    have Hj : nth O p i = j.+1 by apply anti_leq; rewrite Hpart Hnth.
    move: Hhaut => {Hpart Hnth}; rewrite subn_eq0 Hj.
    case: p Hj => pp /=.
    elim: pp i j => [//= | p0 p' IHp'] /= i j /andP [] Hhead Hpart Hj.
    case: ltnP => //=.
    + rewrite -Hj => H1 H2.
      move: H2; rewrite -(haut_nth _ Hpart) Hj => /leq_trans; by apply.
    + case: i Hj => [| i]/= Hj Hp0 _.
      * case: p' Hhead Hpart {IHp'} => [| p1 p'] //=.
        subst p0; move: Hp0; by rewrite ltnn.
      * apply: (IHp' _ _ Hpart Hj) => {IHp'}.
        exfalso.
        move: Hpart => /is_part_ijP [] _ Hpart.
        have {Hpart} /Hpart : (0 <= i)%N by [].
        rewrite Hj => Habs.
        have:= leq_ltn_trans (leq_trans Hhead Hp0) Habs.
        case p' => //= p1 /= _.
        by rewrite ltnn.
Save.

Lemma size_hook_seq_hook' i j : size (hook_seq i j) = hook' p i j.
rewrite size_hook_seq_next_eq /hook' /hook_next_seq size_cat !size_map !size_iota.
rewrite addnC -!subn1.
congr addn; apply subnAC.
Save.


Lemma size_hook_next_seq_hook' i j : size (hook_next_seq i j) = hook' p i j.
rewrite -size_hook_seq_next_eq; apply size_hook_seq_hook'.
Save.

Lemma leq_subnKC : forall m n, (n <= m + (n - m))%N.
move => m n; rewrite -leq_subLR //.
Save.

Lemma leq_subnK : forall m n, (n <= (n - m) + m)%N.
move => m n; rewrite addnC; apply leq_subnKC.
Save.

Lemma leq_ltn_add : forall m1 m2 n1 n2, ((m1<=n1) -> (m2<n2) -> (m1+m2<n1+n2))%N.
move => m1 m2 n1 n2 H1 H2; rewrite -addnS; apply leq_add => //.
Save.

Lemma ltn_leq_add : forall m1 m2 n1 n2, ((m1<n1) -> (m2<=n2) -> (m1+m2<n1+n2))%N.
move => m1 m2 n1 n2 H1 H2; rewrite -addSn; apply leq_add => //.
Save.

Lemma in_hook_seq_decr (i j:nat) (k l : nat) :
   is_in_part p i j -> (k,l) \in (hook_seq i j) -> (size (hook_seq k l) < size (hook_seq i j))%N.
rewrite (is_in_part_simpl i j) // => /andP [] Hijl Hijc.
rewrite !size_hook_seq_hook' /hook_seq /hook_next_seq map_cat mem_cat -!map_comp /hook_next /funcomp /= 
  => /orP [].
+ rewrite -(rwP (mapP (y:=(k, l)))) => [[x Hx Hy]].
  move: Hx; rewrite mem_iota; move /andP => [[Hx1 Hx2]].
  injection Hy => Hy1 Hy2; subst.
  rewrite /hook' -!subn1.
  apply leq_ltn_add. 
  - apply leq_sub => //; apply leq_sub => //.
  have [_ Hm]:=(elimT (is_part_ijP p) is_part_p).
  apply Hm; apply ltnW => //.
  - rewrite -!subnDA.
  move: Hijc.
  rewrite (leq_eqVlt (i.+1) (haut p j)) => /orP [].
  move /eqP => Hh.
  exfalso; move: Hx2; rewrite -Hh => /=.
  rewrite subnn addn0 => Hxi.
  have abs := (leq_ltn_trans Hx1 Hxi).
  by move:abs; rewrite ltnn //.
  move => Hh.
  move: Hh Hx2.
  rewrite -(add1n i) => Hh; rewrite -subn1 -subnDA.
  rewrite subnKC //=.
  move => Hj; apply leq_trans with (haut p j - x)%N.
  apply ltn_sub2l => //.
  rewrite addn1 //.
  apply leq_sub => //.
  rewrite addn1 //.
  apply ltnW => //.
+ rewrite -(rwP (mapP (y:=(k, l)))) => [[x Hx Hy]].
  move: Hx; rewrite mem_iota; move /andP => [[Hx1 Hx2]].
  injection Hy => Hy1 Hy2; subst.
  rewrite /hook' -!subn1.
  apply ltn_leq_add.
  - rewrite -!subnDA.
  move: Hijl.
  rewrite (leq_eqVlt (j.+1) (nth O p i)) => /orP [].
  move /eqP => Hh.
  exfalso; move: Hx2; rewrite -Hh => /=.
  rewrite subnn addn0 => Hxi.
  have abs := (leq_ltn_trans Hx1 Hxi).
  by move:abs; rewrite ltnn //.
  move => Hh.
  move: Hh Hx2.
  rewrite -(add1n j) => Hh; rewrite -subn1 -subnDA.
  rewrite subnKC //=.
  move => Hj; apply leq_trans with (nth O p i - x)%N.
  apply ltn_sub2l => //.
  rewrite addn1 //.
  apply leq_sub => //.
  rewrite addn1 //.
  apply ltnW => //.
  - apply leq_sub => //; apply leq_sub => //.
  apply haut_decr => //.
  by apply ltnW => //.
Save.

Fixpoint choose_corner (m:nat) (i j : nat) : distr ((seq nat) * (seq nat)) := 
   if m is m'.+1 then
     let s := hook_next_seq i j in
     (if size s is p.+1 
     then Mlet (Uniform (unif_def (inl 0%N) s))
          (fun n => match n with inl k => 
               Mlet (choose_corner m' k j) (fun X => Munit (i::X.1,X.2))
                               | inr k => 
               Mlet (choose_corner m' i k) (fun X => Munit (X.1,j::X.2))
                    end)
     else Munit ([::i],[::j]))
   else Munit ([::i],[::j]).

Lemma choose_corner0_simpl i j : choose_corner 0 i j = Munit ([::i],[::j]).
trivial.
Save.

Lemma choose_corner_end_simpl m i j 
      : (size (hook_next_seq i j) == 0)%N -> choose_corner m i j = Munit ([::i],[::j]).
case m; rewrite //=.
move => N /eqP H.
rewrite H; trivial.
Save.

Lemma choose_corner_rec_simpl m i j : 
      forall (Hs : (size (hook_next_seq i j) != 0)%N), 
      choose_corner (m.+1) i j = Mlet (Uniform (mkunif (hook_next_seq i j) Hs))
          (fun n => match n with inl k => 
               Mlet (choose_corner m k j) (fun X => Munit (i::X.1,X.2))
                               | inr k => 
               Mlet (choose_corner m i k) (fun X => Munit (X.1,j::X.2))
                    end).
rewrite /=.
case (hook_next_seq i j) => //=.
Save.

Lemma choose_corner_inv m  : 
      forall i j, mu (choose_corner m i j) 
         (fun R => ((size R.1!=0)&&(size R.2!=0)&&(head 0 R.1==i)&&(head 0 R.2==j))%N%:Q)
      = 1.
elim m.
move => i j //=; rewrite 2!eq_refl //=.
move => n Hin i j.
case (boolP (size (hook_next_seq i j)== O)) => [H0|Hs].
rewrite choose_corner_end_simpl => //=.
by rewrite 2!eq_refl.
rewrite (choose_corner_rec_simpl n i j Hs).
rewrite Mlet_simpl.
rewrite mu_one_eq => //=.
move => [k|k] /=.
apply mu_bool_impl1 with (2:=Hin k j).
move => [A B] /=.
apply /implyP => /andP [H1 H2].
move:H1 => /andP [H3 _].
move:H3 => /andP [_ H3].
by rewrite H3 H2 eq_refl.
apply mu_bool_impl1 with (2:=Hin i k).
move => [A B] /=.
apply /implyP => /andP [H1 H2].
move:H1 => /andP [H3 H4].
move:H3 => /andP [H3 _].
by rewrite H3 H4 eq_refl.
Save.

Lemma choose_corner_emptyl m i j (A B : seq nat) : 
      (A == [::])%B -> mu (choose_corner m i j) (fun R => (R==(A,B))%:Q) = 0.
move => HA.
apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m i j)).
   move => [X Y] /=.
   apply /implyP => /andP [] /andP [] /andP [] SX SY _ _.
   move: SX; apply contra.
   by rewrite size_eq0 xpair_eqE (eqP HA); move => /andP [].
Save.

Lemma choose_corner_emptyr m i j (A B : seq nat) : 
      (B == [::])%B -> mu (choose_corner m i j) (fun R => (R==(A,B))%:Q) = 0.
move => HB.
apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m i j)).
   move => [X Y] /=.
   apply /implyP => /andP [] /andP [] /andP [] SX SY _ _.
   move: SY; apply contra.
   by rewrite size_eq0 xpair_eqE (eqP HB); move => /andP [].
Save.

Lemma choose_corner_headl m i j (A B : seq nat) : 
      (i != head O A)%B -> mu (choose_corner m i j) (fun R => (R==(A,B))%:Q) = 0.
move => Ha.
apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m i j)).
   move => [X Y] /=.
   apply /implyP => /andP [] /andP [] /andP [] _ _ hi hj.
   rewrite xpair_eqE.
   apply /negP; move => /andP [] /eqP Ha1 _.
   move:hi; rewrite Ha1 /=.
   move => Ha2; apply (elimN eqP Ha).
   by move: Ha2 => /eqP.
Save.

Lemma choose_corner_headr m i j (A B : seq nat) : 
      (j != head O B)%B -> mu (choose_corner m i j) (fun R => (R==(A,B))%:Q) = 0.
move => Hb.
apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m i j)).
   move => [X Y] /=.
   apply /implyP => /andP [] /andP [] /andP [] _ _ hi hj.
   rewrite xpair_eqE.
   apply /negP; move => /andP [] _ /eqP Hb1.
   move:hj; rewrite Hb1 /=.
   move => Hb2; apply (elimN eqP Hb).
   by move: Hb2 => /eqP.
Save.


Require Import path.

Definition is_trace (A B : seq nat) := 
      [&& (A != [::]), (B != [::]), is_out_corner p (last O A), 
          lindex p (last O A) == last O B, sorted ltn A & sorted ltn B].

Lemma is_trace_in_part (A B : seq nat) : is_trace A B ->
      forall a b, a \in A -> b \in B -> is_in_part p a b.
admit.
Save.

Lemma is_trace_tll (a:nat) (A B : seq nat) : A != [::] -> is_trace (a::A) B -> is_trace A B.
admit.
Save.

Lemma is_trace_tlr (b:nat) (A B : seq nat) : B != [::] -> is_trace A (b::B) -> is_trace A B.
admit.
Save.

Lemma is_trace_corner_nil (a b:nat) (A B : seq nat) : is_trace (a::A) (b::B) 
      -> (size (hook_next_seq a b) == 0)%N -> (A == [::]) && (B == [::]).
admit.
Save.

Lemma is_trace_corner_not_nil (a b:nat) (A B : seq nat) : is_trace (a::A) (b::B) 
      -> (size (hook_next_seq a b) != 0)%N -> (A != [::]) || (B != [::]).
admit.
Save.

Lemma fun_cons_simpll a A B : 
    (fun x : seq nat * seq nat => ((a :: x.1, x.2) == (a :: A, B))%:~R) ==
    (fun x : seq nat * seq nat => (x == (A, B))%:~R).
move => [X Y] /=.
rewrite /eq_op /=.
rewrite {1}/eq_op /=.
by rewrite eq_refl.
Save.

Lemma fun_cons_simplr a A B : 
    (fun x : seq nat * seq nat => ((x.1, a :: x.2) == (A, a :: B))%:~R) ==
    (fun x : seq nat * seq nat => (x == (A, B))%:~R).
move => [X Y] /=.
rewrite /eq_op /=.
rewrite {2}/eq_op /=.
by rewrite eq_refl.
Save.

Lemma choose_corner_decomp m a b (A B : seq nat) : 
      (size (hook_next_seq a b) != 0)%N -> is_trace (a::A) (b::B) ->
      mu (choose_corner m.+1 a b) (fun R => (R==(a::A,b::B))%:Q)
      = (mu (choose_corner m  a (head O B)) (fun R => (R==(a::A,B))%:Q) + 
        mu (choose_corner m  (head O A) b) (fun R => (R==(A,b::B))%:Q))
        / (size (hook_next_seq a b))%:Q.
move => Hs Ht.
rewrite (choose_corner_rec_simpl _ _ _ Hs) Mlet_simpl.
rewrite mu_uniform_sum /=.
congr (_ / _). 
rewrite /hook_next_seq.
rewrite big_cat /=.
rewrite !big_map /=.
rewrite GRing.addrC.
congr (_+_)%R.
+ case (boolP (B == [::])) => HB.
 - rewrite big1.
   * apply esym.
     by apply choose_corner_emptyr.
   * move => i _; rewrite fun_cons_simplr.
     by apply choose_corner_emptyr.
 - rewrite (bigD1_seq (head O B) _ (iota_uniq _ _)) /=.
   * rewrite -{1}(fun_cons_simplr b).
     rewrite -[RHS]GRing.addr0.
     congr (_+_)%R.
     apply: big1.
     move => i Hi.
     rewrite fun_cons_simplr.
     by apply choose_corner_headr.
   * rewrite mem_iota.
     have:= Ht => /and5P [_ _ _ _] /andP [_ H4].
     apply /andP; split. 
     move: HB H4; rewrite /sorted.
     case B => [//|b0 B' /=].
     by move => _ /andP [].
     have Hh : (head O B \in b :: B).
     move: HB; case B => //=.
     move => n l _; by rewrite !inE eq_refl orbT.
     have := (is_trace_in_part _ _ Ht a (head O B) (mem_head _ _) Hh).
     rewrite /is_in_part addSn.
     move => Hlt.
     apply (leq_trans Hlt).
     apply leq_trans with ((nth O p a).-1).+1.
     by apply leqSpred => /=.
     rewrite ltnS.
     by rewrite -leq_subLR.
+ case (boolP (A == [::])) => HA.
  - rewrite big1.
    * by apply esym; apply choose_corner_emptyl.
    * move => i _; rewrite fun_cons_simpll.
      by apply: choose_corner_emptyl.
  - rewrite (bigD1_seq (head O A) _ (iota_uniq _ _)) /=.
    * rewrite -{1}(fun_cons_simpll a).
      rewrite -[RHS]GRing.addr0.
      congr (_+_)%R.
      apply: big1.
      move => i Hi; rewrite fun_cons_simpll.
      by apply choose_corner_headl.
    * rewrite mem_iota.
      have:= Ht => /and5P [H1 H2 H3 H4] /andP [H5 H6].
  apply /andP; split. 
  move: HA H5; rewrite /sorted.
  case A => [//|a0 A' /=].
  by move => _ /andP [].
  have Hh : (head O A \in a :: A).
  move: HA; case A => //=.
  move => n l _; by rewrite !inE eq_refl orbT.
  have := (is_trace_in_part _ _ Ht (head O A) b Hh (mem_head _ _)) => Hp.
  apply (@leq_trans (haut p b)). 
  rewrite -(haut_in_le (L:=p) (head O A) b _) //=.
  rewrite addSn.
  apply leq_trans with ((haut p b).-1).+1.
  by apply leqSpred => /=.
  rewrite ltnS.
  by rewrite -leq_subLR.
Save.

Lemma belast_empty  (T:eqType) (x:T) (s : seq T) : (s==[::])%B -> belast x s = [::].
by move => /eqP Hs; subst.
Save.

Lemma cons_head_behead (T:eqType) x (s : seq T) : (s!=[::]) -> s = head x s :: behead s.
case s => //=.
Save.


Definition PI (a b:nat) (A B:seq nat) : rat := 
     \prod_(i <- belast a A) (1/(hook' p i (last b (b::B)))%:Q) 
   * \prod_(j <- belast b B) (1/(hook' p (last a (a::A)) j)%:Q).

Lemma PIprog m : forall a b (A B : seq nat), (size A + size B <= m)%N ->  is_trace (a::A) (b::B) ->
      mu (choose_corner m a b) (fun R => (R==(a::A,b::B))%:Q) = PI a b A B.
elim:m.
* move => a b A B.
rewrite leqn0 addn_eq0 size_eq0 size_eq0 => /andP [].
move => /eqP HA /eqP HB; subst.
by move => HT; rewrite choose_corner0_simpl Munit_simpl /PI eq_refl /belast big_nil big_nil //=.
* move => n IHn a b A B Hs Ht.
have [HO|Hn0]:= boolP (size (hook_next_seq a b) == O).
 + rewrite choose_corner_end_simpl //=.
have HAB := is_trace_corner_nil a b A B Ht HO.
move : HAB => /andP [].
move => /eqP HA /eqP HB; subst.
by rewrite xpair_eqE eqseq_cons eqseq_cons eq_refl eq_refl /PI big_nil big_nil.
 + rewrite choose_corner_decomp //=.
have HAB:= is_trace_corner_not_nil a b A B Ht Hn0.
move : HAB => /orP [].
move => HA.
have [HB|HnB]:= boolP (B == [::]).
rewrite /PI.
rewrite (choose_corner_emptyr n a (head O B)) //.
rewrite GRing.add0r.
have HAd := (cons_head_behead _ O A HA).
rewrite  {2} HAd.
rewrite (IHn (head O A) b (behead A)).
rewrite (belast_empty _ b B HB).
rat_to_ring; rewrite big_nil GRing.mulr1.
rewrite /PI (eqP HB) big_nil /=.
rewrite  {3} HAd (belast_cat a [::head O A] (behead A)) big_cat big_seq1 /=.
rewrite size_hook_next_seq_hook'.
rat_to_ring; rewrite GRing.mul1r GRing.mulr1.
rewrite GRing.mulrC //.
rewrite -ltnS size_behead -addSn.
apply: (leq_trans _ Hs).
apply leq_add; trivial.
rewrite prednK //.
by rewrite lt0n size_eq0.
rewrite -HAd.
apply (is_trace_tll _ _ _ HA Ht).
admit.
admit.
Save.
End FindCorner.
