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
Import GRing.Theory.
*)
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

Local Notation conj := (conj_part p).

Definition is_in_hook (r c : nat) (k l : nat) :=
  ((r == k) && (c < l < nth 0 p r)) ||
  ((c == l) && (r < k < nth 0 conj c)).

Lemma in_hook_part (r c : nat) (k l : nat) :
   is_in_part p r c -> is_in_hook r c k l -> is_in_part p k l.
Proof.
  rewrite /is_in_part /is_in_hook => Hj /orP [] /and3P [] /eqP <- // H1 H2.
  by rewrite (conj_ltnE (intpartP p)).
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
      by rewrite eq_refl Hrx /= -(iota_hookE _ _ _ Hrx).
    + move=> /mapP [] y _; discriminate.
    + move=> /mapP [] y _; discriminate.
    + rewrite mem_map; last by move=> u v [].
      rewrite mem_iota => /andP [] Hcx Hxc /= [] -> -> {k l}.
      rewrite /is_in_hook; apply/orP; left.
      by rewrite eq_refl Hcx /= -(iota_hookE _ _ _ Hcx).
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
  move=> Hpart Hhl; apply (al_length0_out_corner _ _ _ (intpartP p) Hpart).
  by rewrite -size_hook_seq Hhl.
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
                     (head 0 HS.1 == r)& (head 0 HS.2 == c)]%N%:~R)
      = 1)%R.
Proof.
  elim: m r c => [| n Hn] r c.
    by rewrite /= 2!eq_refl.
  case (altP (size (hook_next_seq r c) =P 0)) => [H0|Hs].
  - by rewrite choose_corner_end_simpl //= !eq_refl.
  - rewrite (choose_corner_rec_simpl n r c Hs).
    rewrite Mlet_simpl mu_one_eq //.
    move => [] k /=.
    + apply: (mu_bool_impl1 _ _ _ _ (Hn k c)) => [] [A B] /=.
      apply /implyP => /and4P [H1 H2 H3 H4].
      by rewrite H2 H4 eq_refl.
    + apply: (mu_bool_impl1 _ _ _ _ (Hn r k)) => [] [A B] /=.
      apply /implyP => /and4P [H1 H2 H3 H4].
      by rewrite H1 H3 eq_refl.
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
  apply (@is_in_part_le p (last 0 A) (last 0 B) _ _ (intpartP p) Hpart);
    exact: sorted_leq_last.
Qed.

Lemma fun_cons_simpll a A B :
  (fun x : seq nat * seq nat => ((a :: x.1, x.2) == (a :: A, B))%:~R)%R ==
  (fun x : seq nat * seq nat => (x == (A, B))%:~R)%R.
Proof.
  move => [X Y] /=.
  by rewrite /eq_op /= {1}/eq_op /= eq_refl.
Qed.

Lemma fun_cons_simplr a A B :
    (fun x : seq nat * seq nat => ((x.1, a :: x.2) == (A, a :: B))%:~R)%R ==
    (fun x : seq nat * seq nat => (x == (A, B))%:~R)%R.
Proof.
  move => [X Y] /=.
  by rewrite /eq_op /= {2}/eq_op /= eq_refl.
Qed.


Lemma choose_corner_decomp m a b (A B : seq nat) :
  (size (hook_next_seq a b) != 0)%N -> is_trace (a::A) (b::B) ->
  mu (choose_corner m.+1 a b) (fun R => (R==(a::A,b::B))%:~R%R)
  = ((mu (choose_corner m  a (head O B)) (fun R => (R==(a::A,B))%:~R) +
      mu (choose_corner m  (head O A) b) (fun R => (R==(A,b::B))%:~R))
       / (size (hook_next_seq a b))%:~R)%R.
Proof.
  move => Hs Ht.
  rewrite (choose_corner_rec_simpl _ _ _ Hs) Mlet_simpl.
  rewrite mu_uniform_sum /=.
  congr (_ / _)%R.
  rewrite /hook_next_seq big_cat /= !big_map /= GRing.addrC.
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
      * rewrite -{1}(fun_cons_simplr b) -[RHS]GRing.addr0.
        congr (_+_)%R.
        apply: big1 => i Hi.
        rewrite fun_cons_simplr.
        apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m a i)) => [] [X Y] /=.
        apply/implyP => /and4P [] _ _ _ SH.
        move: Hi; apply contra => /eqP [] _ <-.
        by rewrite eq_sym.
      * have:= Ht => /and5P [] _ _ _ HsortB _.
        have Hb : b < head 0 B by move: HsortB HB; case B => [//= | b0 B'] /= /andP [].
        rewrite mem_iota (iota_hookE _ _ _ Hb) Hb /=.
        have Hh : (head O B \in b :: B).
          move: HB; case B => [//= | n l] _; by rewrite !inE eq_refl orbT.
        exact: (is_trace_in_part _ _ Ht a (head O B) (mem_head _ _) Hh).
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
      * rewrite -{1}(fun_cons_simpll a) -[RHS]GRing.addr0.
        congr (_+_)%R.
        apply: big1 => i Hi.
        rewrite fun_cons_simpll.
        apply: (mu_bool_negb0 _ _ _ _ (choose_corner_inv m i b)) => [] [X Y] /=.
        apply /implyP => /and4P [] _ _ HX _.
        move: Hi; apply contra => /eqP [] <- _.
        by rewrite eq_sym.
      * have:= Ht => /and5P [] _ _ HsortA _ _.
        have Ha : a < head 0 A by move: HsortA HA; case A => [//= | a0 A'] /= /andP [].
        rewrite mem_iota (iota_hookE _ _ _ Ha) Ha /=.
        have Hh : (head O A \in a :: A).
          move: HA; case A => [//= | n l] _; by rewrite !inE eq_refl orbT.
        have:= (is_trace_in_part _ _ Ht (head O A) b Hh (mem_head _ _)).
        case: p => /= part Hpart.
        by rewrite is_in_conj_part.
Qed.

End FindCorner.
