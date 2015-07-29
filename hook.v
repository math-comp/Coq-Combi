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
               finfun ssrnum ssralg ssrint bigop path.
Require Import tools subseq partition.
(* Require Import equerre.
Local Open Scope O_scope.
Local Open Scope rat_scope.
Local Open Scope ring_scope. *)
Import GRing.Theory.

Local Open Scope nat_scope.

(*
Add Rec LoadPath "../Combi/LRrule".
Add Rec LoadPath "ALEA/src" as ALEA.

Require Import ssreflect ssrbool ssrfun ssrnat eqtype fintype choice seq.
Require Import bigop fintype rat ssrint ssralg.
Require Import tools partition.
*)


Require Import recyama.

Lemma sorted_subseq_iota_rcons s n : subseq s (iota 0 n) = sorted ltn (rcons s n).
Proof.
  apply (sameP idP); apply (iffP idP).
  - elim: n s => [/= [//=| s0 s]| n IHn s].
      rewrite rcons_cons /= => /(order_path_min ltn_trans) /= /allP Hall.
      exfalso.
      suff /Hall : 0 \in rcons s 0 by [].
      by rewrite mem_rcons inE eq_refl.
    case/lastP: s => [_| s sn]; first exact: sub0seq.
    case: (ltnP sn n) => Hsn Hsort.
    + have {Hsort} Hsort : sorted ltn (rcons s sn).
        case: s Hsort => [//= | s0 s].
        by rewrite !rcons_cons /= rcons_path => /andP [].
      have /IHn : sorted ltn (rcons (rcons s sn) n).
        case: s Hsort => [_ /= | s0 s]; first by rewrite andbT.
        rewrite !rcons_cons /=.
        by rewrite (rcons_path ltn s0 (rcons s sn) n) /= last_rcons Hsn => ->.
      move/subseq_trans; apply.
      rewrite -addn1 iota_add add0n cats1.
      exact: subseq_rcons.
    + have H : sn = n.
        apply anti_leq; rewrite Hsn andbT.
        move: Hsort.
        case: s => [/= /andP []| s0 s]/=; first by rewrite ltnS.
        by rewrite rcons_path /= last_rcons ltnS => /andP [].
      subst sn.
      rewrite -addn1 iota_add add0n /= cats1.
      rewrite -subseq_rcons_eq; apply IHn.
      case: s Hsort => [//= | s0 s].
      by rewrite !rcons_cons /= rcons_path => /andP [].
  - move=> Hsubs.
    apply: (subseq_sorted ltn_trans (s2 := (iota 0 n.+1))).
    + by rewrite -addn1 iota_add add0n /= cats1 -subseq_rcons_eq.
    + exact: iota_ltn_sorted.
Qed.


Lemma is_in_part_le (sh : seq nat) r c j k :
  is_part sh -> is_in_part sh r c -> j <= r -> k <= c -> is_in_part sh j k.
Proof.
  rewrite /is_in_part => /is_part_ijP [] _ Hpart Hcr /Hpart Hrj Hkc.
  exact: leq_ltn_trans Hkc (leq_trans Hcr Hrj).
Qed.

Definition is_corner_box sh r c := (is_out_corner sh r && (c == (nth 0 sh r).-1)).

Lemma is_corner_box_in_part sh r c :
  is_corner_box sh r c -> is_in_part sh r c.
Proof.
  rewrite /is_corner_box /is_in_part /is_out_corner => /andP [] Hr /eqP ->.
  move: Hr; by case (nth 0 sh r).
Qed.

Lemma is_corner_box_conj_part sh u v :
  is_part sh -> is_corner_box sh u v -> is_corner_box (conj_part sh) v u.
Proof.
  rewrite /is_corner_box {1}/is_out_corner => Hpart /andP [] Hcorn /eqP Hv.
  subst.
  rewrite (out_corner_conj_part Hpart Hcorn) /= eq_sym.
  have : nth 0 sh u.+1 <= (nth 0 sh u).-1 < (nth 0 sh u).
    move: Hcorn; case: (nth 0 sh u) => [//= | shu].
    by rewrite ltnS [shu.+1.-1]/= => -> /=.
  by rewrite -nth_conjE // => /eqP -> /=.
Qed.


Definition arm_length sh r c := ((nth 0 sh r) - c).-1.
Definition leg_length sh r c := (arm_length (conj_part sh) c r).

Definition al_length sh r c := ((arm_length sh r c) + (leg_length sh r c)).
Definition hook_length (sh : seq nat) r c : nat := (al_length sh r c).+1.

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

Definition F_deno (sh : seq nat) :=
    \prod_(r < length sh) \prod_(c < nth 0 sh r) (hook_length sh r c).
Definition F sh :=  (((sumn sh)`!)%:Q / (F_deno sh)%:Q)%R.


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
  by rewrite /al_length /leg_length /arm_length -!subn1 -!subnDA !add1n !addn1 addnC.
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

Lemma hook_seq_empty (r c : nat) :
  is_in_part p r c -> hook_seq r c = [::] -> is_corner_box p r c.
Proof.
  move=> Hpart Hhl; by apply al_length0_out_corner; last by rewrite -size_hook_seq Hhl.
Qed.



Fixpoint walk_to_corner (m : nat) (i j : nat) : distr ((seq nat) * (seq nat)) :=
   if m is m'.+1 then
     let s := hook_next_seq i j in
     (if size s is p.+1
     then Mlet (Uniform (unif_def (inl (0 : nat)) s))
          (fun n => match n with inl k =>
               Mlet (walk_to_corner m' k j) (fun X => Munit (i::X.1,X.2))
                               | inr k =>
               Mlet (walk_to_corner m' i k) (fun X => Munit (X.1,j::X.2))
                    end)
     else Munit ([::i],[::j]))
   else Munit ([::i],[::j]).

Lemma walk_to_corner0_simpl r c : walk_to_corner 0 r c = Munit ([:: r],[:: c]).
Proof. by []. Qed.

Lemma walk_to_corner_end_simpl m r c :
  (size (hook_next_seq r c) = 0) -> walk_to_corner m r c = Munit ([:: r],[:: c]).
Proof. by case m => [| n] //= ->. Qed.

Lemma walk_to_corner_rec_simpl m r c :
  forall (Hs : (size (hook_next_seq r c) != 0)),
    walk_to_corner (m.+1) r c = Mlet (Uniform (mkunif (hook_next_seq r c) Hs))
      (fun n => match n with
                  | inl k => Mlet (walk_to_corner m k c) (fun X => Munit (r::X.1, X.2))
                  | inr k => Mlet (walk_to_corner m r k) (fun X => Munit (X.1, c::X.2))
                end).
Proof. rewrite /=; by case (hook_next_seq r c). Qed.

Open Scope ring_scope.

Lemma walk_to_corner_inv m r c :
  mu (walk_to_corner m r c)
     (fun HS => [&& (size   HS.1 != 0), (size   HS.2 != 0),
                    (head 0 HS.1 == r)& (head 0 HS.2 == c)]%N%:Q)
      = 1.
Proof.
  elim: m r c => [| n Hn] r c.
    by rewrite /= 2!eq_refl.
  case (altP (size (hook_next_seq r c) =P 0%N)) => [H0|Hs].
  - by rewrite walk_to_corner_end_simpl //= !eq_refl.
  - rewrite (walk_to_corner_rec_simpl _ Hs).
    rewrite Mlet_simpl mu_one_eq //.
    move => [] k /=.
    + apply: (mu_bool_impl1 _ _ _ _ (Hn k c)) => [] [A B] /=.
      apply /implyP => /and4P [H1 H2 H3 H4].
      by rewrite H2 H4 eq_refl.
    + apply: (mu_bool_impl1 _ _ _ _ (Hn r k)) => [] [A B] /=.
      apply /implyP => /and4P [H1 H2 H3 H4].
      by rewrite H1 H3 eq_refl.
Qed.

Close Scope ring_scope.


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

Lemma sorted_in_leq_last A a : sorted ltn A -> a \in A -> a <= last 0 A.
Proof.
  elim: A a => [//= | A0 A IHA] a /= Hpart.
  rewrite inE => /orP [/eqP |] Ha.
  - subst a => {IHA}.
    elim: A A0 Hpart => [//= | A1 A IHA] A0 /= /andP [] /ltnW H01 /IHA{IHA}.
    exact: leq_trans H01.
  - have {IHA Hpart} := IHA _ (path_sorted Hpart) Ha.
    by case: A Ha.
Qed.

Lemma sorted_leq_last A a : sorted ltn (a :: A) -> a <= last a A.
Proof.
  move=> /sorted_in_leq_last H.
  by have /H /= : a \in (a :: A) by rewrite inE eq_refl.
Qed.

Lemma is_trace_in_in_part (A B : seq nat) : is_trace A B ->
  forall a b, a \in A -> b \in B -> is_in_part p a b.
Proof.
  rewrite /is_trace => /and5P [] _ _ HltnA HltnB /is_corner_box_in_part Hpart a b Ha Hb.
  apply: (@is_in_part_le p (last 0 A) (last 0 B) _ _ (intpartP p) Hpart);
    exact: sorted_in_leq_last.
Qed.

Lemma is_trace_in_part (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> is_in_part p a b.
Proof. move/is_trace_in_in_part; apply; by rewrite inE eq_refl. Qed.

Open Scope ring_scope.

Definition charfun (A B : seq nat) := (fun x : seq nat * seq nat => (x == (A, B))%:Q).

Lemma walk_to_corner_emptyl m r c (A B : seq nat) :
  (A == [::])%B -> mu (walk_to_corner m r c) (charfun A B) = 0.
Proof.
  move => HA.
  apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv _ _ _)) => [] [X Y] /=.
  apply /implyP => /and4P [] SX SY _ _.
  move: SX; apply contra.
  by rewrite size_eq0 xpair_eqE (eqP HA); move => /andP [].
Qed.

Lemma walk_to_corner_emptyr m i j (A B : seq nat) :
  (B == [::])%B -> mu (walk_to_corner m i j) (charfun A B) = 0.
Proof.
  move => HB.
  apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m i j)) => [] [X Y] /=.
  apply /implyP => /and4P [] SX SY _ _.
  move: SY; apply contra.
  by rewrite size_eq0 xpair_eqE (eqP HB); move => /andP [].
Qed.

Lemma charfun_simpll a A B :
  (fun x => charfun (a :: A) B (a :: x.1, x.2)) == charfun A B.
Proof.
  move => [X Y] /=.
  by rewrite /charfun /eq_op /= {1}/eq_op /= eq_refl.
Qed.

Lemma charfun_simplr b A B :
  (fun x => charfun A (b :: B) (x.1, b :: x.2)) == charfun A B.
Proof.
  move => [X Y] /=.
  by rewrite /charfun /eq_op /= {2}/eq_op /= eq_refl.
Qed.


Lemma walk_to_corner_decomp m a b (A B : seq nat) :
  (size (hook_next_seq a b) != 0)%N -> is_trace (a::A) (b::B) ->
  mu (walk_to_corner m.+1 a b) (charfun (a :: A) (b :: B))
  = (mu (walk_to_corner m  a (head O B)) (charfun (a :: A) B) +
     mu (walk_to_corner m  (head O A) b) (charfun A (b :: B)) )
        / (size (hook_next_seq a b))%:Q.
Proof.
  move => Hs Ht.
  rewrite (walk_to_corner_rec_simpl _ Hs) Mlet_simpl.
  rewrite mu_uniform_sum /=.
  congr (_ / _)%R.
  rewrite /hook_next_seq big_cat /= !big_map /= addrC.
  congr (_ + _)%R.
  - case (boolP (size B == 0%N)) => HB.
    + rewrite big1.
      * apply esym.
        apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m a (head O B))) => [] [X Y] /=.
        apply/implyP => /and4P [] _ SY _ _.
        move: SY; by apply contra => /eqP [] _ ->.
      * move => i _; rewrite charfun_simplr.
        apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m a i)) => [] [X Y] /=.
        apply/implyP => /and4P [] _ SY _ _.
        move: SY; by apply contra => /eqP [] _ ->.
    + rewrite (bigD1_seq (head O B) _ (iota_uniq _ _)) /=.
      * rewrite -{1}(@charfun_simplr b (a :: A) B) -[RHS]addr0.
        congr (_+_)%R.
        apply: big1 => i Hi.
        rewrite charfun_simplr.
        apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m a i)) => [] [X Y] /=.
        apply/implyP => /and4P [] _ _ _ SH.
        move: Hi; apply contra => /eqP [] _ <-.
        by rewrite eq_sym.
      * have:= Ht => /and5P [] _ _ _ HsortB _.
        have Hb : (b < head 0 B)%N by move: HsortB HB; case B => [//= | b0 B'] /= /andP [].
        rewrite mem_iota (iota_hookE _ Hb) Hb /=.
        have Hh : (head O B \in b :: B).
          move: HB; case B => [//= | n l] _; by rewrite !inE eq_refl orbT.
        exact: (is_trace_in_in_part Ht (mem_head _ _) Hh).
  - case (boolP (size A == O)) => HA.
    + rewrite big1.
      * apply esym.
        apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m (head O A) b)) => [] [X Y] /=.
        apply /implyP => /andP [] SX _.
        move: SX; by apply contra => /eqP [] ->.
      * move => i _; rewrite charfun_simpll.
        apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m i b)) => [] [X Y] /=.
        apply /implyP => /andP [] SX _.
        move: SX; by apply contra => /eqP [] ->.
    + rewrite (bigD1_seq (head O A) _ (iota_uniq _ _)) /=.
      * rewrite -{1}(@charfun_simpll a A (b :: B)) -[RHS]addr0.
        congr (_+_)%R.
        apply: big1 => i Hi.
        rewrite charfun_simpll.
        apply: (mu_bool_negb0 _ _ _ _ (walk_to_corner_inv m i b)) => [] [X Y] /=.
        apply /implyP => /and4P [] _ _ HX _.
        move: Hi; apply contra => /eqP [] <- _.
        by rewrite eq_sym.
      * have:= Ht => /and5P [] _ _ HsortA _ _.
        have Ha : (a < head 0 A)%N by move: HsortA HA; case A => [//= | a0 A'] /= /andP [].
        rewrite mem_iota (iota_hookE _ Ha) Ha /=.
        have Hh : (head O A \in a :: A).
          move: HA; case A => [//= | n l] _; by rewrite !inE eq_refl orbT.
        have:= (is_trace_in_in_part Ht Hh (mem_head _ _)).
        case: p => /= part Hpart.
        by rewrite is_in_conj_part.
Qed.

Close Scope ring_scope.

Lemma trace_size_arm_length (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> size B <= arm_length p a b.
Proof.
  elim: B b => [//= | B0 B IHB] b /= Htrace.
  apply: (leq_ltn_trans (IHB _ (is_trace_tlr _ Htrace))); first by [].
  have:= Htrace => /and5P [] _ _ _ /= /andP [] Hb _ _.
  rewrite {IHB} /arm_length.
  suff HB0 : B0 < nth 0 p a.
    rewrite -ltnS prednK; last by rewrite subn_gt0.
    rewrite -ltnS prednK //; last by rewrite subn_gt0; exact: (ltn_trans Hb HB0).
    rewrite ltnS; apply ltn_sub2l; last exact Hb.
    exact: (ltn_trans Hb HB0).
  rewrite -/(is_in_part _ _ _).
  by apply (is_trace_in_in_part Htrace); rewrite !inE eq_refl /= ?orbT.
Qed.

Lemma trace_size_leg_length (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> size A <= leg_length p a b.
Proof.
  elim: A a => [//= | A0 A IHA] a /= Htrace.
  apply: (leq_ltn_trans (IHA _ (is_trace_tll _ Htrace))); first by [].
  have:= Htrace => /and5P [] _ _ /= /andP [] Ha _ _ _.
  rewrite {IHA} /leg_length.
  suff HA0 : A0 < nth 0 conj b.
    rewrite -ltnS prednK; last by rewrite subn_gt0.
    rewrite -ltnS prednK //; last by rewrite subn_gt0; exact: (ltn_trans Ha HA0).
    rewrite ltnS; apply ltn_sub2l; last exact Ha.
    exact: (ltn_trans Ha HA0).
  rewrite -/(is_in_part _ _ _).
  rewrite -is_in_conj_part //.
  by apply (is_trace_in_in_part Htrace); rewrite !inE eq_refl /= ?orbT.
Qed.

Lemma size_tracer (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> size B <= al_length p a b.
Proof.
  move=> /trace_size_arm_length/leq_trans; apply.
  by rewrite leq_addr.
Qed.

Lemma size_tracel (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) -> size A <= al_length p a b.
Proof.
  move=> /trace_size_leg_length/leq_trans; apply.
  by rewrite leq_addl.
Qed.

Lemma is_trace_corner_nil (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) ->
  (size (hook_next_seq a b) == 0) = (A == [::]) && (B == [::]).
Proof.
  rewrite -(size_map (hook_next a b)) size_hook_seq.
  move=> Htrace; apply (sameP idP); apply (iffP idP).
  - move=> /andP [] /eqP HA /eqP HB; subst.
    move: Htrace => /and5P [] _ _ _ _ /=.
    rewrite /is_corner_box /al_length /leg_length /arm_length /is_out_corner.
    move => /andP [] Ha /eqP Hb; subst.
    have -> : (nth 0 p a - (nth 0 p a).-1) = 1.
      move: Ha; case: (nth 0 p a) => [//= | pa] _.
      by rewrite /= subSn // subnn.
    rewrite /= add0n.
    suff -> : nth 0 conj (nth 0 p a).-1 = a.+1 by rewrite subSn // subnn.
    apply/eqP; rewrite nth_conjE //.
    move: Ha; case: (nth 0 p a) => [//= | pa].
    by rewrite !ltnS => -> /=.
  - move=> /eqP Hal.
    have := size_tracel Htrace; have := size_tracer Htrace.
    by rewrite Hal !leqn0 => /nilP -> /nilP ->.
Qed.

Lemma arm_length_corner_box sh (r c u v : nat) :
  is_part sh ->
  r <= u -> c <= v -> is_corner_box sh u v ->
  arm_length sh r c = arm_length sh u c + arm_length sh r v.
Proof.
  move=> /is_part_ijP [] _ Hpart.
  rewrite /is_corner_box /is_out_corner => Hr Hc /andP [] Hcorn /eqP Hv.
  subst v.
  rewrite /arm_length.
  have {Hpart Hr} := Hpart _ _ Hr.
  move: Hc Hcorn; case: (nth 0 sh u) => [//= | pu].
  rewrite [_.+1.-1]/= => Hcpu; rewrite (subSn Hcpu) => _ Hpu.
  have := leq_ltn_trans Hcpu Hpu.
  case: (nth 0 sh r) Hpu => [//= | pr].
  rewrite !ltnS => Hpu Hcpr.
  by rewrite !subSn //= addnC addnBA // subnK.
Qed.

Lemma leg_length_corner_box sh (r c u v : nat) :
  is_part sh ->
  r <= u -> c <= v -> is_corner_box sh u v ->
  leg_length sh r c = leg_length sh u c + leg_length sh r v.
Proof.
  rewrite /leg_length addnC => Hpart Hru Hcv Hcorn.
  apply: (arm_length_corner_box (is_part_conj Hpart) Hcv Hru).
  exact: is_corner_box_conj_part.
Qed.

Lemma al_length_corner_box sh (r c u v : nat) :
  is_part sh -> r <= u -> c <= v -> is_corner_box sh u v ->
  al_length sh r c = al_length sh u c + al_length sh r v.
Proof.
  move=> Hpart Hru Hcv Hcorn.
  rewrite /al_length (arm_length_corner_box Hpart Hru Hcv Hcorn).
  rewrite /al_length (leg_length_corner_box Hpart Hru Hcv Hcorn).
  rewrite !addnA; congr (_ + _); rewrite -!addnA; congr (_ + _); by rewrite addnC.
Qed.

Lemma al_length_last_rectangle (a b : nat) (A B : seq nat) :
  is_trace (a :: A) (b :: B) ->
  al_length p a b = al_length p (last a A) b + al_length p a (last b B).
Proof.
  rewrite /is_trace => /and5P [] _ _ HA HB /=.
  exact: al_length_corner_box (sorted_leq_last HA) (sorted_leq_last HB).
Qed.

Lemma belast_empty (T : eqType) (x : T) (s : seq T) : (s == [::])%B -> belast x s = [::].
Proof. by move => /eqP Hs; subst. Qed.

Lemma cons_head_behead (T : eqType) x (s : seq T) :
  (s != [::]) -> s = head x s :: behead s.
Proof. by case s. Qed.

Lemma belast_behead_rcons (T : eqType) x l (s : seq T) :
  belast (head x (rcons s l)) (behead (rcons s l)) = s.
Proof. case: s => [//= | s0 s]; by rewrite rcons_cons /= belast_rcons. Qed.

Lemma last_behead_rcons (T : eqType) x l (s : seq T) :
  last (head x (rcons s l)) (behead (rcons s l)) = l.
Proof. case: s => [//= | s0 s]; by rewrite rcons_cons /= last_rcons. Qed.

Open Scope ring_scope.

(* Formula of Lemma 3. *)
Definition PI (a b : nat) (A B : seq nat) : rat :=
  \prod_(i <- belast a A) (1 / (al_length p i (last b (b :: B)))%:Q) *
  \prod_(j <- belast b B) (1 / (al_length p (last a (a :: A)) j)%:Q).

(* Lemma 3. *)
Lemma PIprog m a b (A B : seq nat) :
  (size A + size B <= m)%N -> is_trace (a :: A) (b :: B) ->
  mu (walk_to_corner m a b) (charfun (a :: A) (b :: B)) = PI a b A B.
Proof.
  elim: m a b A B => [/= | m IHm] /= a b A B.
    rewrite leqn0 addn_eq0 size_eq0 size_eq0 => /andP []/eqP HA /eqP HB; subst.
    move => HT; by rewrite /charfun eq_refl /= /PI /belast /= !big_nil.
  case: (boolP (size (hook_next_seq a b) == O)) => [HO|Hn0].
    move=> _ Htrace; rewrite (eqP HO).
    move: HO; rewrite (is_trace_corner_nil Htrace) => /andP [] /eqP Ha /eqP Hb.
    subst A B; by rewrite /charfun /= eq_refl /= /PI /= !big_nil.
  move=> Hs Ht; rewrite walk_to_corner_decomp //.
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
    set PjlB := (\big[ *%R/1]_(j <- A') (1 / (al_length p j lB)%:Q))%R.
    set PlAj := (\big[ *%R/1]_(j <- B') (1 / (al_length p lA j)%:Q))%R.
    rewrite -![(_ * PjlB)%R]mulrC !mulrA -![(_ * PlAj)%R]mulrC.
    rewrite !mulrA -!mulrDr mulr1 -!mulrA.
    congr (_ * (_ * _))%R.
    rewrite !mulrA mulr1.
    have /= := al_length_last_rectangle Htrace.
    rewrite -/lA -/lB => ->.
    rewrite (PoszD (al_length p lA b) (al_length p a lB)) mulrzDl.
    set Alen := (al_length p lA b); set Blen := (al_length p a lB).
    have Alen0 : Alen != O.
      rewrite /Alen /lA -size_hook_seq size_map.
      by rewrite (is_trace_corner_nil (is_trace_lastl Htrace)).
    have Blen0 : Blen != O.
      rewrite /Blen /lB -size_hook_seq size_map.
      by rewrite (is_trace_corner_nil (is_trace_lastr Htrace)).
    have := @addf_div rat_fieldType 1 Alen%:Q 1 Blen%:~R.
    rewrite addrC !div1r !mul1r => ->; rewrite ?intr_eq0 ?eqz_nat //.
    rewrite addrC [LHS]mulrC mulrA mulVf; first by rewrite mul1r invfM mulrC.
    rewrite -mulrzDl /= intr_eq0 eqz_nat.
    by rewrite addn_eq0 negb_and Alen0 Blen0.
  - move: HA => /eqP HA; subst A.
    rewrite [X in (_ + X)%R]walk_to_corner_emptyl // addr0.
    have HBd := (cons_head_behead O HB).
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
    rewrite walk_to_corner_emptyr  // add0r.
    have HAd := (cons_head_behead O HA).
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

Close Scope ring_scope.

Definition trace_seq (last : nat) : seq (seq nat) :=
  [seq rcons tr last | tr <- enum_subseqs (iota 0 last)].

Definition enum_trace (Alpha Beta : nat) : seq ((seq nat) * (seq nat)) :=
  [seq (A, B) | A <- trace_seq Alpha, B <- trace_seq Beta].

Lemma trace_corner_box (Alpha Beta : nat) :
  is_corner_box p Alpha Beta ->
  forall A B, A \in trace_seq Alpha -> B \in trace_seq Beta -> is_trace A B.
Proof.
  move=> Hcorn A B.
  move=> /mapP [] A' /(allP (enum_subseqsP (iota 0 Alpha))) HsubA -> {A}.
  move=> /mapP [] B' /(allP (enum_subseqsP (iota 0 Beta)))  HsubB -> {B}.
  by rewrite /is_trace !rcons_nilF /= -!sorted_subseq_iota_rcons HsubA HsubB !last_rcons.
Qed.

Lemma trace_seqlP (A B : seq nat) :
  is_trace A B -> A \in trace_seq (last 0 A).
Proof.
  move=> /and5P [].
  case/lastP: A => [//= | A lA] _ _ Hsort _ /= _.
  rewrite last_rcons /trace_seq.
  apply/mapP; exists A; last by [].
  apply: mem_enum_subseqs.
  by rewrite sorted_subseq_iota_rcons.
Qed.

Lemma trace_seqrP (A B : seq nat) :
  is_trace A B -> B \in trace_seq (last 0 B).
Proof.
  move=> /and5P [].
  case/lastP: B => [//= | B lB] _ _ _ Hsort /= _.
  rewrite last_rcons /trace_seq.
  apply/mapP; exists B; last by [].
  apply: mem_enum_subseqs.
  by rewrite sorted_subseq_iota_rcons.
Qed.

Lemma enum_traceP (Alpha Beta : nat) :
  is_corner_box p Alpha Beta ->
  forall A B,
    (A, B) \in enum_trace Alpha Beta =
    [&& (is_trace A B), (last 0 A == Alpha) & (last 0 B == Beta)].
Proof.
  move=> Hcorn A B.
  apply (sameP idP); apply (iffP idP).
  - move=> /and3P [] Htrace /eqP HlA /eqP HlB.
    apply/allpairsP; exists (A, B) => /=; split.
    + rewrite -HlA; exact: (trace_seqlP Htrace).
    + rewrite -HlB; exact: (trace_seqrP Htrace).
    + by [].
  - move=> /allpairsP [] [eA eB] /= [] HA HB [] H1 H2; subst eA eB.
    apply/and3P; split.
    + exact: (trace_corner_box Hcorn).
    + move: HA => /mapP [] A' _ ->; by rewrite last_rcons.
    + move: HB => /mapP [] B' _ ->; by rewrite last_rcons.
Qed.

(* Choose BOX in part *)

Definition choose_corner : distr ((seq nat) * (seq nat)) :=
  Mlet (Random (sumn p).-1)
       (fun n => let (r, c) := reshape_coord p n in
                 walk_to_corner (al_length p r c) r c).

Section EndsAt.

Variable (Alpha Beta : nat).
Hypothesis Hcorn : is_corner_box p Alpha Beta.

Definition ends_at := (fun R => (last O R.1 == Alpha) && (last O R.2 == Beta)).
Definition PI_trace X := (PI (head O X.1) (head O X.2) (behead X.1) (behead X.2)).
Lemma bla (prd : nat -> bool) :
  forall i, prd i ->
  (mu (let (r, c) := reshape_coord p i in
       walk_to_corner (al_length p r c) r c)) ends_at =
  (\sum_(X <- enum_trace Alpha Beta |
         let (r, c) := reshape_coord p i in (head O X.1 == r) && (head O X.2 == c))
    PI_trace X)%R.
Proof.
  move=> i _ {prd}; case: (reshape_coord p i) => [r c].
  rewrite big_seq_cond.
  rewrite (eq_bigr
             (fun X => mu (walk_to_corner (al_length p r c) r c)
                          (charfun X.1 X.2))); first last.
    move=> [A B] /= /and3P [].
    rewrite (enum_traceP Hcorn) => /and3P [] Htrace HAlpha HBeta /eqP <- /eqP <- {r c}.
    rewrite /PI_trace -(PIprog (m := al_length p (head 0 A) (head 0 B))) /=; first last.
    - have:= Htrace => /and3P [] HA HB _; by rewrite -!cons_head_behead.
    - have:= Htrace => /and3P [] HA HB _.
      case: A B HA HB Htrace {HAlpha HBeta} => [//= | a A] [//= | b B] /= _ _ Htrace.
      rewrite addnC.
      exact: (leq_add (trace_size_arm_length Htrace) (trace_size_leg_length Htrace)).
    apply: Mstable_eq => [] [X1 X2].
    have:= Htrace => /and3P [] HA HB _; by rewrite -!cons_head_behead.
  rewrite -big_seq_cond.
  admit.
Qed.

Lemma sumnpSPE : (sumn p).-1.+1 = sumn p.
Proof.
  have Hszp : Alpha < size p.
    move: Hcorn; rewrite /is_corner_box /is_out_corner => /andP [] H _.
    move: H; apply contraLR; rewrite -!ltnNge ltnS => H.
    by rewrite (nth_default _ H).
  move: Hszp; case: p => /= [] [//= | p0 p'].
  move=> /part_head_non0 /= => Hp0 _.
  case: p0 Hp0 => [//= | p0] _.
  by rewrite !addSn.
Qed.

Open Scope ring_scope.

Lemma prob_cond :
  mu choose_corner ends_at =
  1 / (sumn p)%:Q * \sum_(X <- enum_trace Alpha Beta) PI_trace X.
Proof.
  rewrite /choose_corner MLet_simpl mu_random_sum sumnpSPE.
  rewrite mulrC mul1r; congr (_ / _)%R.
  rewrite (eq_bigr _ (@bla _)).
  rewrite (exchange_big_dep (@predT _)) //=.
  apply eq_big_seq => [[A B]]; rewrite (enum_traceP Hcorn) => /and3P [] Htrace HA HB.
  have Hin : (head O B < nth O p (head O A))%N.
    have:= Htrace => /and3P [] HA0 HB0 _.
    case: A B HA0 HB0 Htrace {HA HB} => [//= | a A] [//= | b B] /= _ _ Htrace.
    exact: (is_trace_in_part Htrace).
  rewrite -big_filter (bigD1_seq (flatten_coord p (head O A) (head O B))) /=; first last.
  - apply filter_uniq; exact: iota_uniq.
  - rewrite mem_filter (flatten_coordK Hin) !eq_refl /=.
    rewrite mem_iota add0n subn0 /=.
    exact: flatten_coordP.
  rewrite -[RHS]addr0; congr (_ + _)%R.
  rewrite big_filter_cond; apply big_pred0 => i.
  have:= (reshape_coordK p i); case: (reshape_coord p i) => [r c] <-.
  case: (boolP ((head 0 A) == r)%N) => //= /eqP <-.
  case: (boolP ((head 0 B) == c)%N) => //= /eqP <-.
  by rewrite eq_refl.
Qed.

Require Import gnw bigallpairs.

Lemma Formula1 :
  (F_deno p)%:Q / (F_deno (decr_nth p Alpha))%:Q =
  ( \prod_(0 <= i < Alpha) (1 + (al_length p i Beta)%:Q^-1)) *
  ( \prod_(0 <= j < Beta)  (1 + (al_length p Alpha j)%:Q^-1)).
Proof.
  admit.
Qed.

Lemma SimpleCalculation :
  \big[+%R/0%R]_(X <- enum_trace Alpha Beta) PI_trace X =
  (F_deno p)%:Q / (F_deno (decr_nth p Alpha))%:Q.
Proof.
  rewrite /enum_trace /trace_seq /PI_trace /PI.
  rewrite big_allpairs /=.
  rewrite Formula1 !expand_prod_add1_seq.
  rewrite /index_iota subn0 big_map big_distrl /=; apply eq_big_seq => A HA.
  rewrite /index_iota subn0 big_map big_distrr /=; apply eq_big_seq => B HB.
  rewrite !belast_behead_rcons !last_behead_rcons.
  congr (_ * _); apply eq_big_seq => L _; by rewrite mul1r.
Qed.

Theorem Theorem2 :
  mu choose_corner ends_at = ((F (decr_nth_part p Alpha)) / (F p))%R.
Proof.
  rewrite prob_cond /F.
  have:= Hcorn => /andP [] Hout _.
  rewrite -{1 2}(decr_nthK is_part_p Hout) /=.
  rewrite /decr_nth_part_def Hout.
  move Hdec : (decr_nth p Alpha) => dec.
  rewrite sumn_incr_nth.
  rewrite factS PoszM -!ratzE ratzM !ratzE.
  rat_to_ring.
  set Rhs := (RHS).
  have -> : Rhs = ((1 / (sumn dec).+1%:~R) * (F_deno p)%:Q / (F_deno dec)%:Q)%R.
    rewrite /Rhs -!mulrA [(((F_deno dec)%:Q)^-1 / _)%R]mulrC !invfM !mul1r.
    rewrite !mulrA [X in (X / _ / _ / _)%R]mulrC.
    congr (_ * _)%R; rewrite -!mulrA; congr (_ * _)%R.
    rewrite mulrA divff; first by rewrite invrK mul1r.
    rewrite intr_eq0 eqz_nat -lt0n.
    exact: fact_gt0.
  rewrite {Rhs} !mul1r -[RHS]mulrA; congr (_ * _)%R.
  rewrite -Hdec; exact: SimpleCalculation.
Qed.

End EndsAt.

Corollary Corollary4 :
  (\sum_(i <- out_corners p) (F (decr_nth_part p i)) / (F p) = 1)%R.
Proof.
  admit.
Qed.

End FindCorner.

