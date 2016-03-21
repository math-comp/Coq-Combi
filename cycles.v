Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun bigop finset binomial fingroup perm automorphism action.

From Combi Require Import symgroup partition.

Set Implicit Arguments.
Unset Strict Implicit.


Section Definitions.
  Variable T : Type.
  Implicit Type s : seq T.

Definition rotate n s : seq T :=
  rot (n %% (size s)) s.


Definition rotater n s :=
  rotr (n%%(size s)) s.

End Definitions.
  

Section RotateLemmas.

  Variables (n0 : nat) (T : Type) (T' : eqType).
  Implicit Type s : seq T.


Lemma rotate0 s : rotate 0 s = s.
Proof. by rewrite /rotate; rewrite mod0n; apply (rot0 s). Qed.

Lemma size_rotate s : size (rotate n0 s) = size s.
Proof. by apply size_rot. Qed.

Lemma rotate_size s : rotate (size s) s = s.
Proof. by rewrite /rotate; rewrite modnn; apply rot0. Qed.

Lemma has_rotate s a : has a (rotate n0 s) = has a s.
Proof. by apply has_rot. Qed.

Lemma rotate_size_cat s1 s2 : rotate (size s1) (s1 ++ s2) = s2 ++ s1.
Proof.
  rewrite /rotate size_cat.
  case s2 => /=; first by rewrite addn0 modnn cats0; apply rot0.
  move => s l; rewrite modn_small.
  -  by apply rot_size_cat.
  -  by rewrite -addSnnS; apply ltn_addr; apply ltnSn.
Qed.

Lemma rotateK : cancel (@rotate T n0) (rotater n0).
Proof.
  rewrite /rotate /rotater => s.
  rewrite /rotr size_rot -size_drop {2}/rot.
  by rewrite rot_size_cat cat_take_drop.
Qed.

Lemma rotate_inj : injective (@rotate T n0). 
Proof. exact (can_inj rotateK). Qed.

Lemma rotate1_cons x s : rotate 1 (x :: s) = rcons s x.
Proof. by rewrite /rotate; case s; [rewrite modnn; apply rot0|move => s0 l; apply rot1_cons]. Qed.

Lemma rotate_uniq (s: seq T') : uniq (rotate n0 s) = uniq s.
Proof. by unfold rotate; apply rot_uniq. Qed.

Lemma mem_rotate (s: seq T') : rotate n0 s =i s.
Proof. by unfold rotate; apply mem_rot. Qed.

(*
Lemma eqseq_rotate (s1 s2: seq T') : (rotate n0 s1 == rotate n0 s2) = (s1 == s2).
Proof. by apply: inj_eq; apply: rotate_inj. Qed.  
*)

(*  
CoInductive rot_to_spec s x := RotToSpec i s' of rot i s = x :: s'.
Lemma rot_to s x : x \in s -> rot_to_spec s x.
*)

Lemma perm_rotate n (s: seq T') : perm_eql (rotate n s) s.
Proof. by apply perm_rot. Qed.

Lemma rotate_inv n m s : n=m%[mod (size s)] -> rotate n s  = rotate m s .
Proof. by move => H; rewrite /rotate H => //. Qed.

Lemma rotate_nil n : @rotate T n [::] = [::].
Proof. by rewrite /rotate /rot => //. Qed.

End RotateLemmas.

Lemma addn_subn:
  forall m n p, m + n = p -> m = p - n.
Proof.
  move => m n p H.
  have H0: m+n-n=p-n by rewrite H => //.  
  by rewrite -addnBA in H0; [rewrite subnn addn0 in H0 => //|apply leqnn].  
Qed.  
  
Lemma ltn_add m1 m2 n1 n2:
  m1 < n1 -> m2 < n2 -> m1+m2 < n1+n2.
Proof. by move => H1 H2; rewrite -addSn; apply leq_add => //; exact: ltnW. Qed.

(*
Section RotaterLemmas.

Variables (n0 : nat) (T : Type) (T' : eqType).
Implicit Type s : seq T.

Lemma size_rotr s : size (rotr n0 s) = size s.

Lemma mem_rotr (s : seq T') : rotr n0 s =i s.

Lemma rotr_size_cat s1 s2 : rotr (size s2) (s1 ++ s2) = s2 ++ s1.

Lemma rotr1_rcons x s : rotr 1 (rcons s x) = x :: s.

Lemma has_rotr a s : has a (rotr n0 s) = has a s.

Lemma rotr_uniq (s : seq T') : uniq (rotr n0 s) = uniq s.

Lemma rotrK : cancel (@rotr T n0) (rot n0).

Lemma rotr_inj : injective (@rotr T n0).

Lemma rev_rot s : rev (rot n0 s) = rotr n0 (rev s).

Lemma rev_rotr s : rev (rotr n0 s) = rot n0 (rev s).

Lemma perm_rotater n (s: seq T') : perm_eql (rotater n s) s.
Proof.
  by apply perm_rotr.
Qed.

  
End RotaterLemmas.
*)

Section RotateCompLemmas.

  Variable T : eqType.
  Implicit Type s : seq T.

  
Lemma rotate_addn m n s : rotate (m + n) s = rotate m (rotate n s).
Proof.
 (*The case of the empty list is trivial, but must be treated separately*)
  case: (posnP (size s)) => [/eqP /nilP -> | Hsize].
    by rewrite rotate_nil.                                     
  rewrite /rotate size_rot rot_add_mod; last 3 [idtac]||by apply ltnW; apply ltn_pmod.
  case: (ltngtP (m%%size s + n%% size s) (size s)) => H.
  - by rewrite (ltnW H) -modnDm modn_small.
  - rewrite leqNgt H /=; congr rot.
    have Hineg: m %% size s + n %% size s - size s < size s.
      rewrite -(ltn_add2r (size s)) (subnK (ltnW H)).
      by apply ltn_add; apply ltn_pmod.
    by rewrite -(modn_small Hineg) -modnDm -[RHS]modnDr (subnK (ltnW H)). 
  - rewrite H leqnn -modnDm H modnn.
    by rewrite rot_size rot0.                                              
Qed.

Lemma rotate_rotate m n s : rotate m (rotate n s) = rotate n (rotate m s).
Proof. by rewrite -!rotate_addn addnC. Qed.


(*
Lemma rotate_rotater m n s : rotate m (rotater n s) = rotater n (rotate m s).
Proof.
  rewrite /rotater /rotr !/size_rotate.
  
Lemma rotater_rotater m n s : rotater m (rotater n s) = rotater n (rotater m s).

 *)

End RotateCompLemmas.

Section Blabla.
  Variable T : eqType.
  Implicit Type s : seq T.

Definition rot_eq (s1: seq T) (s2: seq T) :=
  [exists n:'I_((size s1)).+1, rotate n s1 == s2].


Lemma rot_eqP (s1: seq T) (s2: seq T):
  reflect (exists (n:nat), rotate n s1 = s2)  (rot_eq s1 s2).
Proof.
  apply (iffP idP) => [/existsP [] n /eqP Hn |H]; first by exists n.
  apply /existsP; move: H.
  case: (posnP (size s1)) => [/eqP /nilP -> | Hsize H].
  - move => H /=; destruct H as (n0, H); rewrite rotate_nil in H.
    by rewrite -H; exists (Ordinal (ltnSn 0)); rewrite rotate_nil.
  - destruct H as (n0, H).
    exists  (widen_ord (leqnSn _) (Ordinal (ltn_pmod n0 Hsize))). 
    simpl; rewrite -H; apply /eqP; apply rotate_inv.
    exact: modn_mod.
Qed.

End Blabla.



Eval compute in (rot_eq [::1;2] [::2;1]).
Definition cycleSeq := {x:seq T|uniq x}.



