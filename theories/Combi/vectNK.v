(** * Combi.Combi.vectNK : Integer Vector of Given Sums and Sizes *)
(******************************************************************************)
(*      Copyright (C) 2014-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(******************************************************************************)
(** * Integer vectors of sum n and size k

- [vect_n_k n k] == the list of integer vectors of sum n and size k
- [cut_k k s] == the list of the cutting of s in k slices (the result is of
                 type [seq (seq T)])
- [cut3 s] == the list of the cutting of s in 3 slices (the result is of type
              [seq (seq T) * (seq T) * (seq T)])

*****)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype seq.
Require Import tools.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section VectNK.

Fixpoint vect_n_k n k :=
  if k is k'.+1
  then flatten (mkseq (fun i => map (cons i) (vect_n_k (n-i) k') ) n.+1)
  else if n is 0 then [:: [::]] else [::].

Lemma vect_n_k_in n k s : sumn s == n -> size s == k -> s \in vect_n_k n k.
Proof.
elim: k n s => [| k IHk n].
- by case => [s _ /nilP -> //= | n]; case.
- case => [//= | s0 s] /eqP Hsum Hsize.
  apply/flattenP; rewrite -/vect_n_k /mkseq.
  exists (map (cons s0) (vect_n_k (n - s0) k)).
  + apply/mapP; exists s0; last by [].
    by rewrite mem_iota leq0n add0n /= ltnS -Hsum /=; apply: leq_addr.
  + apply/mapP; exists s; last by [].
    apply: IHk; first by rewrite -Hsum /= -{2}[s0]addn0 subnDl subn0.
    by move: Hsize => /=.
Qed.

Lemma in_vect_n_k n k s : s \in vect_n_k n k -> (sumn s == n) && (size s == k).
Proof.
elim: k n s => [| k IHk n]; first case => [[| s0 s]|] //=.
case => [|s0 s] /flattenP /= [ll /mapP [i Hi ->] /mapP [s' //=]].
rewrite -/vect_n_k => /IHk /andP [/eqP Hsum /eqP Hsize] [-> ->].
rewrite Hsize /= eq_refl andbT Hsum.
move: Hi; rewrite mem_iota add0n ltnS => /andP [_ Hi].
by rewrite addnC subnK.
Qed.

Lemma vect_n_kP n k s : s \in vect_n_k n k = (sumn s == n) && (size s == k).
Proof.
apply/idP/idP; first exact: in_vect_n_k.
by move=> /andP []; apply: vect_n_k_in.
Qed.

Lemma vect_0_k k : vect_n_k 0 k = [:: nseq k 0].
Proof. by elim: k => [//= | k IHk] /=; rewrite subn0 cats0 IHk. Qed.

Lemma count_mem_vect_n_k_eq_1 n k s :
  s \in vect_n_k n k -> count_mem s (vect_n_k n k) = 1.
Proof.
elim: k n s=> [/=| k IHk n s]; first by case=> s //=; rewrite mem_seq1 => /eqP ->.
rewrite count_flatten -/vect_n_k -map_comp.
case: s => [|s0 s]; first by rewrite vect_n_kP /= => /andP [_].
move/flatten_mapP; rewrite -/vect_n_k => [] [i].
rewrite mem_iota [iota _ _]lock add0n => Hs0.
move/mapP => [t Ht [H1 H2]]; subst i; subst t.
rewrite (eq_map (f2 := (fun i : nat => i == s0 : nat))).
  by unlock; rewrite sumn_pred1_iota add0n Hs0.
move=> i; rewrite /= count_map /=.
rewrite (eq_count (a2 := fun t => (i == s0) && (s == t))); first last.
  rewrite /= /preim => t /=.
  by apply/eqP/andP => [[-> ->] | [/eqP -> /eqP ->]].
case H : (i == s0) => /=; last by rewrite count_pred0.
rewrite (eq_count (a2 := (xpred1 s))); last exact: eq_sym.
by apply: IHk; rewrite (eqP H).
Qed.

Lemma uniq_vect_n_k n k : uniq (vect_n_k n k).
Proof.
apply: count_mem_uniq => s.
case H : (s \in vect_n_k n k); first by rewrite (count_mem_vect_n_k_eq_1 H).
by move: H => /count_memPn ->.
Qed.

End VectNK.


(** Cutting a seq in k slices : the result is of type [seq (seq T)] *)

Section CutK.

Variable T : eqType.
Implicit Type (s : seq T) (ss : seq (seq T)).

Lemma mem_shape_vect_n_k ss : (shape ss) \in vect_n_k (size (flatten ss)) (size ss).
Proof using.
apply: vect_n_k_in; first by rewrite size_flatten.
by rewrite size_map.
Qed.

Definition cut_k k s := [seq reshape sh s | sh <- vect_n_k (size s) k].

Lemma cut_k_flatten ss : ss \in cut_k (size ss) (flatten ss).
Proof using.
rewrite /cut_k; apply/mapP.
exists (shape ss); first exact (mem_shape_vect_n_k ss).
by rewrite flattenK.
Qed.

Lemma flatten_equiv_cut_k s ss : s == flatten ss <-> ss \in cut_k (size ss) s.
Proof using.
split; first by move=> /eqP ->; apply (cut_k_flatten ss).
move => /mapP [sh]; rewrite vect_n_kP => /andP [/eqP Hsum _] H; subst ss.
by rewrite reshapeKr; last rewrite Hsum.
Qed.

Lemma size_cut_k k s ss : ss \in (cut_k k s) -> size ss = k.
Proof using.
rewrite /cut_k => /mapP [sh /in_vect_n_k/andP [/eqP Hsum /eqP Hsize] -> {ss}].
by rewrite -(size_map size _) -/(shape _) reshapeKl; last rewrite Hsum.
Qed.

End CutK.


(** Cutting a seq in 3 slices : the result is of type [seq (seq T) * (seq T) * (seq T)] *)

Section Cut3.

Variable T : eqType.
Implicit Type (s : seq T) (ss : seq (seq T)).

Let match3 :=
  fun ss => match ss return (seq T) * (seq T) * (seq T) with
              | [:: a; b; c] => (a, b, c) | _ => ([::], [::], [::]) end.

Definition cut3 s : seq ((seq T) * (seq T) * (seq T)) :=
  [seq match3 ss | ss <- cut_k 3 s].

Lemma cat3_equiv_cut3 s a b c : s == a ++ b ++ c <-> (a, b, c) \in cut3 s.
Proof using.
have -> : (a ++ b ++ c) = flatten [:: a; b; c] by rewrite /= cats0.
rewrite flatten_equiv_cut_k /cut3; split.
- by move=> H; apply/mapP; exists [:: a; b; c].
- move=> /mapP [t].
  case: t => [| t0 t]; first by rewrite /cut_k => /size_cut_k.
  case: t => [| t1 t]; first by rewrite /cut_k => /size_cut_k.
  case: t => [| t2 t]; first by rewrite /cut_k => /size_cut_k.
  case: t => [| t3 t]; last by rewrite /cut_k => /size_cut_k.
  by move=> Hcut [-> -> ->].
Qed.

End Cut3.
