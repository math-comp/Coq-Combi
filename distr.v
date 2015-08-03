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

Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat seq ssrint rat
               fintype bigop path ssralg ssrnum.
(* Import bigop before ssralg/ssrnum to get correct printing of \sum \prod*)

Require Import tools subseq partition.

Import GRing.Theory.
Import Num.Theory.

Definition int_to_rat : int -> rat := intmul (GRing.one rat_Ring).
Coercion int_to_rat : int >-> rat.


Lemma iter_plus1 n : (iter n (+%R (1 : rat)) 0 = int_to_rat n)%R.
Proof.
  elim: n => [//= | n IHn] /=.
  by rewrite -add1n PoszD IHn /int_to_rat mulrzDl.
Qed.

(* TODO : Move in Qmeasure *)
Section DistrSum.

Local Open Scope ring_scope.

Lemma mu_stable_sum (A : Type) (m : distr A) (I : Type) (s : seq I) (f : I -> A -> rat) :
  mu m (fun a => \sum_(i <- s) f i a) = \sum_(i <- s) (mu m (f i)).
Proof.
  elim: s => [| s0 s IHs] /=.
    rewrite big_nil; apply mu_zero_eq => x; by rewrite big_nil.
  rewrite big_cons -IHs -mu_stable_add.
  apply Mstable_eq => x /=; by rewrite big_cons.
Qed.

Lemma in_seq_sum (A : eqType) (s : seq A) x :
  uniq s -> (x \in s)%:Q = \sum_(i <- s) (x == i)%:Q.
Proof.
  elim: s => [| s0 s IHs] /=; first by rewrite big_nil.
  rewrite inE big_cons => /andP [] /negbTE Hs0 /IHs <- {IHs}.
  case: (boolP (x == s0)) => [/= /eqP -> | _ ]; last by rewrite /= add0r.
  by rewrite Hs0 addr0.
Qed.

Lemma mu_in_seq (A : eqType) (m : distr A) (s : seq A) :
  uniq s ->
  mu m (fun x => (x \in s)) = \sum_(a <- s) mu m (fun x => (x == a)).
Proof.
  rewrite -mu_stable_sum => Hs.
  apply Mstable_eq => x /=.
  exact: in_seq_sum.
Qed.

Lemma mu_bool_cond (A : Type) (m : distr A) (f g : A -> bool) :
  mu m (fun x => (f x)) = 1 ->
  mu m (fun x => (g x)) = mu m (fun x => (f x && g x)).
Proof.
  move=> H; apply ler_asym; apply/andP; split.
  - rewrite -[X in (_ <= X)]addr0.
    have <- : (mu m) (fun x : A => (~~ f x && g x)) = 0.
      move: H; apply mu_bool_negb0 => x; by case: (f x).
    rewrite -Mstable_add //.
    apply mu_monotonic => x /=.
    case: (f x); by rewrite ?addr0 ?add0r.
  - by apply mu_bool_impl => x; apply/implyP => /andP [].
Qed.

Section Bool_mult.

Variable (A:Type) (c : A -> bool) (m : distr A).

Hypothesis Hc : mu m (fun x => (c x)) = 1.

Instance bool_mon : monotonic (fun (g : MF A) => mu m (fun x => (c x)%:Q * (g x))).
Proof.
  red => f g Hfg; apply mu_monotonic => a.
  case: (c a) => /=.
  - rewrite !mul1r; exact: Hfg.
  - by rewrite !mul0r.
Qed.

Definition bool_mult : M A := mon (fun (g : MF A) => mu m (fun x => (c x)%:Q * (g x))).

Lemma bool_mult_prob : bool_mult (fun x => 1%:Q) = 1.
Proof.
  rewrite /bool_mult /=; rewrite -{3}Hc.
  apply Mstable_eq => x.
  by rewrite mulr1.
Qed.

Definition Bool_mult : distr A.
Proof.
  exists bool_mult; last exact: bool_mult_prob.
  move=> f g /=; rewrite -mu_stable_sub.
  apply Mstable_eq => x /=.
  by rewrite mulrDr mulrN.
Defined.

Lemma bool_mult_simpl f : mu Bool_mult f = mu m (fun x => (c x)%:Q * (f x)).
Proof. by []. Qed.

Lemma mu_pos_cond (g : A -> rat) : mu m g = mu Bool_mult g.
Proof.
  rewrite bool_mult_simpl; apply ler_asym; apply/andP; split.
  - admit.
  - apply mu_monotonic => x /=.
    case : (c x); rewrite ?mul1r ?mul0r //.
    
End Bool_mult.
  
Lemma mu_pos_cond (A : Type) (m : distr A) (f : A -> bool) (g : A -> rat) :
  (forall x, 0 <= g x) ->
  mu m (fun x => (f x)) = 1 ->
  mu m (fun x => (g x)) = mu m (fun x => ((f x)%:Q * g x)).
Proof.
  move=> Hg H; apply ler_asym; apply/andP; split.
  - rewrite -[X in (_ <= X)]addr0.
    have <- : (mu m) (fun x : A => ((~~ f x)%:Q * g x)) = 0.
      apply ler_asym; apply/andP; split.
      + rewrite -(subrr 1) -{3}H -mu_bool_negb.
        apply mu_monotonic => x /=.
        case: (f x) => //=.      have : 1 - 1 = 0 by rewrite .
      move: H; rewrite 
      move: H; apply mu_bool_negb0 => x; by case: (f x).
    rewrite -Mstable_add //.
    apply mu_monotonic => x /=.
    case: (f x); by rewrite ?addr0 ?add0r.
  - by apply mu_bool_impl => x; apply/implyP => /andP [].
Qed.

End DistrSum.
