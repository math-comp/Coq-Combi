Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple finfun bigop finset binomial fingroup perm automorphism action.

From Combi Require Import symgroup partition.
(*
Variable n : nat.
Check 'S_n.

Check classes.
(*Check classes 'S_n.*)
Check classes [set: 'S_n].

Check perm_finGroupType.
Check ordinal_finType.

Check conjg_action.


Check ordinal_finType n.
Check 'I_n.


Notation "''I_' n" := (ordinal_finType n) (at level 8, n at level 2, format "''I_' n").
Check 'I_n.

Check perm_finGroupType.

Notation "''S_' n" := (perm_finGroupType 'I_n) (at level 8, n at level 2, format "''S_' n").
Check 'S_n.


Check conjg_action 'S_n.
Check conjg_groupAction 'S_n.
Check conjsg_action 'S_n.
Check conjG_action 'S_n.


Search class.
Check classes.

From mathcomp Require Import fingroup.
Check classes.
Check classes [set: 'S_n].
(*Check classes 'S_n.*)
*)

Check pcycle.

Variable n:nat.

Record mixin_of (T:eqType) := Mixin {l:seq T; _:uniq l}.

Record class_of (T:eqType) := Class {base: Equality.class_of T; mixin: mixin_of T}.

Variable T:eqType.
(* seq peut être définie eqType -> eqType, ensuite, faire class_of (seq T) *)
(* Définir l'égalité des seq à rotation près *)


(*DEJA DANS MATHCOMP
(*elementary rotation*)
Definition elrot (s1: seq T) :=
  match s1 with
    |(h::t) => rcons t h
    |nil => nil
  end.

(*rotation == nth iteration of elementary rotation*)
Fixpoint rotate (n:nat) (s1: seq T) :=
  match n with
    |0=> s1
    |m.+1 => rotate m (elrot s1)
  end.

Lemma elrot_is_perm :
  forall s1, perm_eq s1 (elrot s1).
Proof.
  case; simpl => //.
  move => a l0.
  unfold perm_eq.
  .
  
  apply iffp.
Qed.



Lemma periodic :
  forall s1, exists n, rotate n s1 = s1. 
Proof.
  move => s1.
  exists (size s1).

  
  induction s1; simpl => //.
  
Qed.
 *)

(*Necessite de redefinir les rotations à cause de rot_oversize*)
(*Lemmes à montrer ensuite en utilisant ces notations*)
(*Remontrer ensuite tous les lemmes sur les rotations présents dans ssreflect.seq*)

Definition aa := {x:seq T|uniq x}.

Lemma fixpoint:
  forall (s1: seq T), exists (n: nat), rot n s1 = s1.
Proof.
  move => s1; exists (size s1).
  apply rot_size.
Qed.

(*Lemma rot_addn m n s : m + n ≤ size s → rot (m + n) s = rot m (rot n s).*)
(*Enlever la condition m + n <= size s*)

(*Lemma periodic:
  forall (s1: seq T) (n0 m a b:nat), a = m*n0+b -> rot n0 s1 = s1 -> rot a s1  = rot b s1.*)
(*Faux avec la définition de ssreflect*)

Definition rot_eq (s1:seq T) (s2: seq T) :=
  [exists n:'I_(size (s1)), rot n s1 == s2].

(*reflect -> apply iffP idP.*)


(*remplacer seq par cycleseq quand cycleseq sera défini*)
Fixpoint cycle_aux (l: seq T) (fst: T) (x: T) :=
  match l with
    |h1::l1 =>  if h1 == x then
                    if l1 is (h2::t) then h2 else fst
                  else cycle_aux l1 fst x                              
    |[::] => x
  end.


Definition cycle (l: seq T) :=
  match l with
    |h::t => (fun x => cycle_aux l h x)
    |[::] => (fun x => x)
  end.

  
Check cycle.

(*nth x l++l (index x l++l).+1 *)

(*Enlever l'hypothèse uniq l en changeant le type cycleSeq*)
(*Lemma cycle_bij:
  forall (l: seq T), uniq l -> bijective (cycle l).  
*)

(*Définie à rotation près*)
(*Lemma cycle_rot:
  forall (s1 s2: seq T), rot_eq s1 s2 -> cycle s1 = cycle s2. 
*)

(*Definition is_cycle
Définir la proposition p est un cycle, lorsque p est une permutation*)
(*Montrer l'équivalence avec la notion de cycle l précdemment définie si besoin*)

(*Décomposition d'une transposition en permutations ?*)
(*Décomposition d'une permutation en cycle*)


(*Cycle associé à une partition*)
Implicit Type s: seq nat.

Definition consec_list (k: nat): seq nat.
  induction k.
  exact [::0].
  exact (k::IHk).
Defined.



Definition sigma (sh: seq nat): nat -> nat.    
  induction sh.
  generalize nat.
  exact (fun (x:nat) => x).
  exact ((cycle (map (fun x => x + n) (consec_list a)))*IHsh).
Defined.






