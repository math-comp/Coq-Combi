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
Add Rec LoadPath "ALEA/src" as ALEA.
Add Rec LoadPath "../Combi/LRrule".

Require Import Misc Ccpo Qmeasure.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype rat
               finfun ssrnum ssralg ssrint bigop.
Require Import tools partition.
(* Require Import equerre.
Local Open Scope O_scope.
Local Open Scope rat_scope.
Local Open Scope ring_scope. *)
Local Open Scope nat_scope.

(*
Add Rec LoadPath "../Combi/LRrule".
Add Rec LoadPath "ALEA/src" as ALEA.

Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop fintype rat ssrint ssralg.
Require Import tools partition.
*)
Import GRing.Theory.
Notation arm_length sh r c := ((nth 0 sh r) - c).-1.
Notation leg_length sh r c := (arm_length (conj_part sh) c r).

Notation al_length sh r c := ((arm_length sh r c) + (leg_length sh r c)).
Definition hook_length (sh : seq nat) r c : nat := (al_length sh r c).+1.

Definition F_deno (sh : seq nat) :=
    \prod_(r < length sh) \prod_(c < nth 0 sh r) (hook_length sh r c).

Lemma al_length0_out_corner sh r c :
  is_part sh -> is_in_part sh r c -> al_length sh r c = 0 ->
  is_out_corner sh r && (c == (nth 0 sh r).-1).
Proof.
  move => Hpart.
  rewrite /is_in_part => Hin_part /eqP.
  rewrite addn_eq0 => /andP [Hnth Hhaut].
  apply /andP; split.
  - rewrite /is_out_corner.
    apply: (leq_trans _ Hin_part).
    rewrite ltnS (conj_leqE Hpart).
    by rewrite -subn_eq0 subnS.
  - rewrite eqn_leq; apply /andP; split.
    + rewrite -ltnS; apply (leq_trans Hin_part).
      exact: leqSpred.
    + by rewrite -subn_eq0 -subn1 -subnAC subn1.
Qed.

Coercion ratz : int >-> rat.
Definition F sh :=  (((sumn sh)`!) / (F_deno sh))%Q.


Section FindCorner.

Variable p : intpart.

Fact is_part_p : is_part p.
apply intpartP.
Save.
Hint Resolve is_part_p.

Local Notation conj := (conj_part p).

Definition is_in_hook (r c : nat) (k l : nat) :=
  ((r == k) && (c < l < nth 0 p r)) ||
  ((c == l) && (r < k < nth 0 conj c)).

Lemma in_hook_part (r c : nat) (k l : nat) :
   is_in_part p r c -> is_in_hook r c k l -> is_in_part p k l.
Proof.
  rewrite /is_in_part /is_in_hook => Hj /orP [] /and3P [] /eqP <- // H1 H2.
  by rewrite conj_ltnE.
Qed.

Definition hook_next_seq r c : seq (nat+nat) :=
  [seq inl k | k <- iota r.+1 ((nth O conj c).-1 - r)] ++
  [seq inr k | k <- iota c.+1 ((nth O p r).-1 - c)].
Definition hook_next r c n : nat * nat :=
    match n with inl k => (k,c) | inr k => (r,k) end.
Definition hook_seq r c := [seq hook_next r c n | n <- hook_next_seq r c].

Lemma size_hook_seq r c : size (hook_seq r c) = al_length p r c.
Proof.
  rewrite size_map size_cat !size_map !size_iota.
  by rewrite -!subn1 -!subnDA !add1n !addn1 addnC.
Qed.

Lemma ltnPred a b : a < b -> (a <= b.-1).
Proof. by case: b. Qed.

Lemma iota_hookE a b c : a < b -> b < a.+1 + (c.-1 - a) = (b < c).
Proof.
  move => Hab; rewrite addSn.
  case: (ltnP b c) => Hbc.
  - have:= ltn_trans Hab Hbc => /ltnPred/subnKC ->.
    exact: (leq_trans Hbc (leqSpred _)).
  - case: c Hbc => [_ | c Hbc] /=.
    + by rewrite sub0n addn0 ltnS leqNgt Hab.
    + rewrite ltnS.
       case: (leqP a c).
      * move/subnKC ->; by rewrite leqNgt Hbc.
      * move=> /ltnW; rewrite {1}/leq => /eqP ->.
        by rewrite addn0 leqNgt Hab.
Qed.

Lemma in_hook_seqP (r c : nat) (k l : nat) :
   (k,l) \in (hook_seq r c) = is_in_hook r c k l.
Proof.
  apply/(sameP idP); apply(iffP idP).
  - rewrite /is_in_hook => /orP [] /and3P [] /eqP <-.
    + move => {k} Hc Hr.
      apply/mapP; exists (inr l); last by [].
      rewrite mem_cat; apply/orP; right; rewrite mem_map; last by move=> u v [].
      by rewrite mem_iota Hc /= iota_hookE.
    + move => {l} Hr Hc.
      apply/mapP; exists (inl k); last by [].
      rewrite mem_cat; apply/orP; left; rewrite mem_map; last by move=> u v [].
      by rewrite mem_iota Hr /= iota_hookE.
  - move=> /mapP [] [] x; rewrite mem_cat => /orP [] /=.
    + rewrite mem_map; last by move=> u v [].
      rewrite mem_iota => /andP [] Hrx Hxr /= [] -> -> {k l}.
      rewrite /is_in_hook; apply/orP; right.
      by rewrite eq_refl Hrx /= -(iota_hookE _ Hrx).
    + move=> /mapP [] y _; discriminate.
    + move=> /mapP [] y _; discriminate.
    + rewrite mem_map; last by move=> u v [].
      rewrite mem_iota => /andP [] Hcx Hxc /= [] -> -> {k l}.
      rewrite /is_in_hook; apply/orP; left.
      by rewrite eq_refl Hcx /= -(iota_hookE _ Hcx).
Qed.

Definition is_corner_box sh r c := (is_out_corner sh r && (c == (nth 0 sh r).-1)).

Lemma is_corner_box_is_part sh r c :
  is_corner_box sh r c -> is_in_part sh r c.
Proof.
  rewrite /is_corner_box /is_in_part /is_out_corner => /andP [] Hr /eqP ->.
  move: Hr; by case (nth 0 sh r).
Qed.

Lemma hook_seq_empty (r c : nat) :
  is_in_part p r c -> hook_seq r c = [::] -> is_corner_box p r c.
Proof.
  move=> Hpart Hhl; by apply al_length0_out_corner; last by rewrite -size_hook_seq Hhl.
Qed.



Fixpoint choose_corner (m : nat) (i j : nat) : distr ((seq nat) * (seq nat)) :=
   if m is m'.+1 then
     let s := hook_next_seq i j in
     (if size s is p.+1
     then Mlet (Uniform (unif_def (inl (0 : nat)) s))
          (fun n => match n with inl k =>
               Mlet (choose_corner m' k j) (fun X => Munit (i::X.1,X.2))
                               | inr k =>
               Mlet (choose_corner m' i k) (fun X => Munit (X.1,j::X.2))
                    end)
     else Munit ([::i],[::j]))
   else Munit ([::i],[::j]).

Lemma choose_corner0_simpl r c : choose_corner 0 r c = Munit ([:: r],[:: c]).
Proof. by []. Qed.

Lemma choose_corner_end_simpl m r c :
  (size (hook_next_seq r c) = 0) -> choose_corner m r c = Munit ([:: r],[:: c]).
Proof. by case m => [| n] //= ->. Qed.

Lemma choose_corner_rec_simpl m r c :
  forall (Hs : (size (hook_next_seq r c) != 0)%N),
    choose_corner (m.+1) r c = Mlet (Uniform (mkunif (hook_next_seq r c) Hs))
      (fun n => match n with
                  | inl k => Mlet (choose_corner m k c) (fun X => Munit (r::X.1, X.2))
                  | inr k => Mlet (choose_corner m r k) (fun X => Munit (X.1, c::X.2))
                end).
Proof. rewrite /=; by case (hook_next_seq r c). Qed.

Lemma is_in_part_le (sh : seq nat) r c j k :
  is_part sh -> is_in_part sh r c -> j <= r -> k <= c -> is_in_part sh j k.
Proof.
  rewrite /is_in_part => /is_part_ijP [] _ Hpart Hcr /Hpart Hrj Hkc.
  exact: leq_ltn_trans Hkc (leq_trans Hcr Hrj).
Qed.

Lemma choose_corner_inv m r c :
  (mu (choose_corner m r c)
      (fun HS => [&& (size   HS.1 != 0), (size   HS.2   != 0),
                     (head 0 HS.1 == r)& (head 0 HS.2 == c)]%N%:Q)
      = 1)%R.
Proof.
  elim: m r c => [| n Hn] r c.
    by rewrite /= 2!eq_refl.
  case (altP (size (hook_next_seq r c) =P 0)) => [H0|Hs].
  - by rewrite choose_corner_end_simpl //= !eq_refl.
  - rewrite (choose_corner_rec_simpl _ Hs).
    rewrite Mlet_simpl mu_one_eq //.
    move => [] k /=.
    + apply: (mu_bool_impl1 _ _ _ _ (Hn k c)) => [] [A B] /=.
      apply /implyP => /and4P [H1 H2 H3 H4].
      by rewrite H2 H4 eq_refl.
    + apply: (mu_bool_impl1 _ _ _ _ (Hn r k)) => [] [A B] /=.
      apply /implyP => /and4P [H1 H2 H3 H4].
      by rewrite H1 H3 eq_refl.
Qed.

Lemma choose_corner_emptyl m r c (A B : seq nat) :
  (A == [::])%B -> mu (choose_corner m r c) (fun R => (R==(A,B))%:Q)%R = 0%:Q%R.
Proof.
  move => HA.
  apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv _ _ _)) => [] [X Y] /=.
  apply /implyP => /and4P [] SX SY _ _.
  move: SX; apply contra.
  by rewrite size_eq0 xpair_eqE (eqP HA); move => /andP [].
Qed.

Lemma choose_corner_emptyr m i j (A B : seq nat) :
  (B == [::])%B -> mu (choose_corner m i j) (fun R => (R==(A,B))%:Q)%R = 0%:Q%R.
Proof.
  move => HB.
  apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m i j)) => [] [X Y] /=.
  apply /implyP => /and4P [] SX SY _ _.
  move: SY; apply contra.
  by rewrite size_eq0 xpair_eqE (eqP HB); move => /andP [].
Qed.



Require Import path.

Definition is_trace (A B : seq nat) :=
      [&& (A != [::]), (B != [::]),
          sorted ltn A, sorted ltn B &
          is_corner_box p (last 0 A) (last 0 B) ].

Lemma is_trace_tll (a:nat) (A B : seq nat) : A != [::] -> is_trace (a::A) B -> is_trace A B.
Proof.
  rewrite /is_trace => HA /and5P [] _ -> /path_sorted -> ->.
  rewrite HA /=; by case: A HA.
Qed.

Lemma is_trace_tlr (b:nat) (A B : seq nat) : B != [::] -> is_trace A (b::B) -> is_trace A B.
Proof.
  rewrite /is_trace => HB /and5P [] -> _ -> /path_sorted ->.
  rewrite HB /=; by case: B HB.
Qed.

Lemma is_trace_lastr (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> is_trace (a :: A) [:: last b B].
Proof.
  elim: B b => [//= | B0 B IHB] b /= /is_trace_tlr H.
  have {H} /H : B0 :: B != [::] by [].
  exact: IHB.
Qed.

Lemma is_trace_lastl (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> is_trace [:: last a A] (b :: B).
Proof.
  elim: A a => [//= | A0 A IHA] a /= /is_trace_tll H.
  have {H} /H : A0 :: A != [::] by [].
  exact: IHA.
Qed.

Lemma sorted_leq_last A a : sorted ltn A -> a \in A -> a <= last 0 A.
Proof.
  elim: A a => [//= | A0 A IHA] a /= Hpart.
  rewrite inE => /orP [/eqP |] Ha.
  - subst a => {IHA}.
    elim: A A0 Hpart => [//= | A1 A IHA] A0 /= /andP [] /ltnW H01 /IHA{IHA}.
    exact: leq_trans H01.
  - have {IHA Hpart} := IHA _ (path_sorted Hpart) Ha.
    by case: A Ha.
Qed.

Lemma is_trace_in_part (A B : seq nat) : is_trace A B ->
  forall a b, a \in A -> b \in B -> is_in_part p a b.
Proof.
  rewrite /is_trace => /and5P [] _ _ HltnA HltnB /is_corner_box_is_part Hpart a b Ha Hb.
  apply: (@is_in_part_le p (last 0 A) (last 0 B) _ _ (intpartP p) Hpart);
    exact: sorted_leq_last.
Qed.

Lemma fun_cons_simpll a A B :
  (fun x : seq nat * seq nat => ((a :: x.1, x.2) == (a :: A, B))%:Q)%R ==
  (fun x : seq nat * seq nat => (x == (A, B))%:Q)%R.
Proof.
  move => [X Y] /=.
  by rewrite /eq_op /= {1}/eq_op /= eq_refl.
Qed.

Lemma fun_cons_simplr a A B :
    (fun x : seq nat * seq nat => ((x.1, a :: x.2) == (A, a :: B))%:Q)%R ==
    (fun x : seq nat * seq nat => (x == (A, B))%:Q)%R.
Proof.
  move => [X Y] /=.
  by rewrite /eq_op /= {2}/eq_op /= eq_refl.
Qed.


Lemma choose_corner_decomp m a b (A B : seq nat) :
  (size (hook_next_seq a b) != 0)%N -> is_trace (a::A) (b::B) ->
  mu (choose_corner m.+1 a b) (fun R => (R==(a::A,b::B))%:Q%R)
  = ((mu (choose_corner m  a (head O B)) (fun R => (R==(a::A,B))%:Q) +
      mu (choose_corner m  (head O A) b) (fun R => (R==(A,b::B))%:Q))
       / (size (hook_next_seq a b))%:Q)%R.
Proof.
  move => Hs Ht.
  rewrite (choose_corner_rec_simpl _ Hs) Mlet_simpl.
  rewrite mu_uniform_sum /=.
  congr (_ / _)%R.
  rewrite /hook_next_seq big_cat /= !big_map /= addrC.
  congr (_ + _)%R.
  - case (boolP (size B == 0)) => HB.
    + rewrite big1.
      * apply esym.
        apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m a (head O B))) => [] [X Y] /=.
        apply/implyP => /and4P [] _ SY _ _.
        move: SY; by apply contra => /eqP [] _ ->.
      * move => i _; rewrite fun_cons_simplr.
        apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m a i)) => [] [X Y] /=.
        apply/implyP => /and4P [] _ SY _ _.
        move: SY; by apply contra => /eqP [] _ ->.
    + rewrite (bigD1_seq (head O B) _ (iota_uniq _ _)) /=.
      * rewrite -{1}(fun_cons_simplr b) -[RHS]addr0.
        congr (_+_)%R.
        apply: big1 => i Hi.
        rewrite fun_cons_simplr.
        apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m a i)) => [] [X Y] /=.
        apply/implyP => /and4P [] _ _ _ SH.
        move: Hi; apply contra => /eqP [] _ <-.
        by rewrite eq_sym.
      * have:= Ht => /and5P [] _ _ _ HsortB _.
        have Hb : b < head 0 B by move: HsortB HB; case B => [//= | b0 B'] /= /andP [].
        rewrite mem_iota (iota_hookE _ Hb) Hb /=.
        have Hh : (head O B \in b :: B).
          move: HB; case B => [//= | n l] _; by rewrite !inE eq_refl orbT.
        exact: (is_trace_in_part Ht (mem_head _ _) Hh).
  - case (boolP (size A == O)) => HA.
    + rewrite big1.
      * apply esym.
        apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m (head O A) b)) => [] [X Y] /=.
        apply /implyP => /andP [] SX _.
        move: SX; by apply contra => /eqP [] ->.
      * move => i _; rewrite fun_cons_simpll.
        apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m i b)) => [] [X Y] /=.
        apply /implyP => /andP [] SX _.
        move: SX; by apply contra => /eqP [] ->.
    + rewrite (bigD1_seq (head O A) _ (iota_uniq _ _)) /=.
      * rewrite -{1}(fun_cons_simpll a) -[RHS]addr0.
        congr (_+_)%R.
        apply: big1 => i Hi.
        rewrite fun_cons_simpll.
        apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m i b)) => [] [X Y] /=.
        apply /implyP => /and4P [] _ _ HX _.
        move: Hi; apply contra => /eqP [] <- _.
        by rewrite eq_sym.
      * have:= Ht => /and5P [] _ _ HsortA _ _.
        have Ha : a < head 0 A by move: HsortA HA; case A => [//= | a0 A'] /= /andP [].
        rewrite mem_iota (iota_hookE _ Ha) Ha /=.
        have Hh : (head O A \in a :: A).
          move: HA; case A => [//= | n l] _; by rewrite !inE eq_refl orbT.
        have:= (is_trace_in_part Ht Hh (mem_head _ _)).
        case: p => /= part Hpart.
        by rewrite is_in_conj_part.
Qed.

Lemma is_trace_corner_nil (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) ->
  (size (hook_next_seq a b) == 0)%N = (A == [::]) && (B == [::]).
Proof.
  admit.
Qed.

Lemma is_trace_last_rectangle (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) ->
  al_length p a b = al_length p (last a A) b + al_length p a (last b B).
Proof.
  rewrite /is_trace => /and5P [] _ _ HA HB /=.
  
Qed.

Definition PI (a b : nat) (A B : seq nat) : rat :=
  (   \prod_(i <- belast a A) (1 / (al_length p i (last b (b::B)))%:Q)
    * \prod_(j <- belast b B) (1 / (al_length p (last a (a::A)) j)%:Q) )%R.

Lemma belast_empty (T : eqType) (x : T) (s : seq T) : (s==[::])%B -> belast x s = [::].
Proof. by move => /eqP Hs; subst. Qed.

Lemma cons_head_behead (T : eqType) x (s : seq T) : (s!=[::]) -> s = head x s :: behead s.
Proof. by case s. Qed.

Lemma PIprog m a b (A B : seq nat) :
  size A + size B <= m -> is_trace (a :: A) (b :: B) ->
  (mu (choose_corner m a b) (fun R => (R == (a :: A, b :: B))%:Q) = PI a b A B)%R.
Proof.
  elim: m a b A B => [/= | m IHm] /= a b A B.
    rewrite leqn0 addn_eq0 size_eq0 size_eq0 => /andP []/eqP HA /eqP HB; subst.
    move => HT; by rewrite eq_refl /= /PI /belast /= !big_nil.
  case: (boolP (size (hook_next_seq a b) == 0)) => [HO|Hn0].
    move=> _ Htrace; rewrite (eqP HO).
    move: HO; rewrite (is_trace_corner_nil Htrace) => /andP [] /eqP Ha /eqP Hb.
    subst A B; by rewrite /= eq_refl /= /PI /= !big_nil.
  move=> Hs Ht; rewrite choose_corner_decomp //.
  have:= Hn0; rewrite (is_trace_corner_nil Ht) negb_and.
  have -> (u v : bool) : ~~u || ~~v = [|| (~~u && ~~v), (u && ~~v) | (~~ u && v)].
    by case: u; case: v.
  move=> /or3P [] /andP [] HA HB.
  - case: A B HA HB Hs Ht => [//= | A0 A] [//= | B0 B] _ _ Hsize Htrace /=.
    rewrite (IHm a B0 (A0 :: A) B); first last.
      * exact: (is_trace_tlr _ Htrace).
      * move: Hsize => /=; by rewrite addnS ltnS.
    rewrite (IHm A0 b A (B0 :: B)); first last.
      * exact: (is_trace_tll _ Htrace).
      * move: Hsize => /=; by rewrite addSn ltnS.
    rewrite {IHm Hsize Hn0} -(size_map (hook_next a b)) size_hook_seq.
    rewrite /PI /= !big_cons.
    set lA := (last A0 A); set lB := (last B0 B).
    set A' := (belast A0 A); set B' := (belast B0 B).
    set PjlB := (\big[ *%R/1]_(j <- A') (1 / (al_length p j lB)%:~R))%R.
    set PlAj := (\big[ *%R/1]_(j <- B') (1 / (al_length p lA j)%:~R))%R.
    rewrite -![(_ * PjlB)%R]mulrC !mulrA -![(_ * PlAj)%R]mulrC.
    rewrite !mulrA -!mulrDr mulr1 -!mulrA.
    congr (_ * (_ * _))%R.
    rewrite !mulrA mulr1.
    have /= := is_trace_last_rectangle Htrace.
    rewrite -/lA -/lB => ->.
    rewrite (PoszD (al_length p lA b) (al_length p a lB)) mulrzDl.
    set Alen := (al_length p lA b); set Blen := (al_length p a lB).
    have Alen0 : Alen != 0.
      rewrite /Alen /lA -size_hook_seq size_map.
      by rewrite (is_trace_corner_nil (is_trace_lastl Htrace)).
    have Blen0 : Blen != 0.
      rewrite /Blen /lB -size_hook_seq size_map.
      by rewrite (is_trace_corner_nil (is_trace_lastr Htrace)).
    have := @addf_div rat_fieldType 1 Alen%:~R 1 Blen%:~R.
    rewrite addrC !div1r !mul1r => ->; rewrite ?intr_eq0 ?eqz_nat //.
    rewrite addrC [LHS]mulrC mulrA mulVf; first by rewrite mul1r invfM mulrC.
    rewrite -mulrzDl /= intr_eq0 eqz_nat.
    by rewrite addn_eq0 negb_and Alen0 Blen0.
  - move: HA => /eqP HA; subst A.
    rewrite [X in (_ + X)%R]choose_corner_emptyl // addr0.
    have HBd := (cons_head_behead 0 HB).
    rewrite {2}HBd.
    rewrite (IHm a (head O B) [::] (behead B)); first last.
      * rewrite -HBd; exact: (is_trace_tlr HB Ht).
      * rewrite size_behead; move: HB Hs.
        case B => [//= | B0 B'] _ /=.
        by rewrite !add0n.
    rewrite /PI !big_nil /=.
    rewrite {3}HBd (belast_cat b [:: head O B] (behead B)) big_cat big_seq1 /=.
    rewrite -(size_map (hook_next a b)) size_hook_seq.
    by rewrite !mul1r mulrC.
  - move: HB => /eqP HB; subst B.
    rewrite choose_corner_emptyr  // add0r.
    have HAd := (cons_head_behead 0 HA).
    rewrite {2}HAd.
    rewrite (IHm (head O A) b (behead A) [::]); first last.
      * rewrite -HAd; exact: (is_trace_tll HA Ht).
      * rewrite size_behead; move: HA Hs.
        case A => [//= | A0 A'] _ /=.
        by rewrite !addn0.
    rewrite /PI !big_nil /=.
    rewrite {3}HAd (belast_cat a [:: head O A] (behead A)) big_cat big_seq1 /=.
    rewrite -(size_map (hook_next a b)) size_hook_seq.
    by rewrite mul1r !mulr1 mulrC.
Qed.

End FindCorner.

