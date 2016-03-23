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
Proof. by rewrite /rotate; apply rot_uniq. Qed.

Lemma mem_rotate (s: seq T') : rotate n0 s =i s.
Proof. by rewrite /rotate; apply mem_rot. Qed.


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
Proof.
    move => H1 H2; rewrite -addSn; apply leq_add => //.
    exact: ltnW.
Qed.


Section RotaterLemmas.

Variables (n0 : nat) (T : Type) (T' : eqType).
Implicit Type s : seq T.

Lemma size_rotater s : size (rotater n0 s) = size s.
Proof. by apply: size_rotr. Qed.

Lemma mem_rotater (s : seq T') : rotater n0 s =i s.
Proof. by apply: mem_rotr. Qed.


Lemma rotater_size_cat s1 s2 : rotater (size s2) (s1 ++ s2) = s2 ++ s1.
Proof.
  rewrite /rotater size_cat.
  case s1; first by rewrite add0n modnn cats0 /rotr subn0; apply rot_size.
  move => s l; rewrite modn_small.
  -  by apply rotr_size_cat.
  -  by rewrite /= addSnnS; apply: ltn_addl; apply: ltnSn.
 Qed.


Lemma rotater1_rcons x s : rotater 1 (rcons s x) = x :: s.
Proof.
  rewrite /rotater size_rcons.
  case: (posnP (size s)) => [/eqP /nilP -> /=| ].
  - by rewrite modnn /rotr subn0 rot_size.
  - move => H; rewrite modn_small.
    + exact: rotr1_rcons.
    + by rewrite ltnS.
Qed.

Lemma has_rotater a s : has a (rotater n0 s) = has a s.
Proof. by apply: has_rotr. Qed.  

Lemma rotater_uniq (s : seq T') : uniq (rotater n0 s) = uniq s.
Proof. by apply rotr_uniq. Qed.

Lemma rotaterK : cancel (@rotater T n0) (rotate n0).
Proof.
  rewrite /rotate /rotater => s.
  rewrite size_rotr.
  by apply: rotrK.
Qed.  
  
Lemma rotater_inj : injective (@rotater T n0).
Proof. exact (can_inj rotaterK). Qed.
  

Lemma rev_rotate s : rev (rotate n0 s) = rotater n0 (rev s).
Proof. by rewrite rev_rot /rotater size_rev. Qed.
  
Lemma rev_rotr s : rev (rotr n0 s) = rot n0 (rev s).
Proof. by rewrite rev_rotr /rotate. Qed.
  
Lemma perm_rotater n (s: seq T') : perm_eql (rotater n s) s.
Proof. by apply perm_rotr. Qed.  
End RotaterLemmas.


Section RotateCompLemmas.
Variable (T: eqType) (n0: nat).
Implicit Type s : seq T.

Lemma eqseq_rotate (s1 s2: seq T):
  (rotate n0 s1 == rotate n0 s2) = (s1 == s2).
Proof. apply: inj_eq. apply: rotate_inj. Qed.  

CoInductive rot_to_spec s x := RotToSpec i s' of rot i s = x :: s'.

(*Lemma rot_to s x : x \in s -> rot_to_spec s x.*)


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


Lemma rotate_rotater m n s : rotate m (rotater n s) = rotater n (rotate m s).
Proof. by rewrite /rotater /rotr size_rotate /rotate rot_rot size_rot. Qed.
  
Lemma rotater_rotater m n s : rotater m (rotater n s) = rotater n (rotater m s).
Proof. by rewrite /rotater /rotr !size_rot rot_rot. Qed.

End RotateCompLemmas.



Section Rot_eq.
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

Lemma rot_eq_size (s: seq T) (t: seq T):
  rot_eq s t -> size s = size t.
Proof.
  move => /existsP [] /= n /eqP Hn; rewrite -Hn.
  by rewrite size_rot.
Qed.

Lemma rot_eq_nil s:
  rot_eq s [::] -> s = [::].
Proof. by move => H; apply /nilP; apply /eqP; apply: (rot_eq_size H). Qed.
  
Lemma rot_eq_refl s : rot_eq s s.
Proof. by apply /rot_eqP; exists 0; rewrite rotate0. Qed. 
  
Lemma rot_eq_sym s t : rot_eq s t -> rot_eq t s.
Proof.
  move => /rot_eqP [] n <-; apply /rot_eqP.
  exists (size s - (n%%size s)).
  rewrite -(rotate_inv (modn_mod n _)) -rotate_addn.
  case: (posnP (size s)) => [/eqP /nilP -> /= | Hsize].
    by rewrite rotate_nil.
  rewrite subnK ?rotate_size //.
  apply ltnW; exact: ltn_pmod.
Qed.


Lemma rot_eq_trans t s u: rot_eq s t -> rot_eq t u -> rot_eq s u.
Proof.
  move => /rot_eqP [] n <- /rot_eqP [] m <-.
  by apply /rot_eqP; exists (m+n); rewrite rotate_addn.
Qed.
End Rot_eq.



(*
Lemma mask_rot m s : size m = size s →
   mask (rot n0 m) (rot n0 s) = rot (count id (take n0 m)) (mask m s).

Lemma mem_mask_rot m s :
  size m = size s → mask (rot n0 m) (rot n0 s) =i mask m s.

Lemma map_rot s : map (rot n0 s) = rot n0 (map s).

Lemma map_rotr s : map (rotr n0 s) = rotr n0 (map s).
 *)

Section CycleLists.
Variable T: eqType.
  
Definition cycleSeq := {x:seq T|uniq x}.

End CycleLists.

Section Cylces.
From mathcomp Require Import finfun.
Variable T: eqType.

Implicit Type s: seq T.

(*
Definition cycle (s: seq T) := 
  [ffun x => nth x (rcons s x) (index x (rcons s x)).+1].
*)

Definition cycle (s: seq T) :=
  (fun (x: T) => if s is a::l then
                   nth x (rcons s a) ((index x (rcons s a)) + 1)
                 else x).

Lemma uniq_next_rotate1 s x:
  uniq s -> x \in s -> cycle s x = cycle (rotate 1 s) x. 
Proof.
  move => Huniq.
  case s => // s0 l Hx.
  rewrite rotate1_cons /=.
  

Qed.

Lemma eq_perm_cycle s t: uniq s -> rot_eq s t -> cycle s =1 cycle t.  
Proof.
  move => Huniq.
  case s.
    by move => /rot_eq_sym /rot_eq_nil -> //.
  move => a l /existsP [] n /eqP <- x.
  (*Trois cas à distinguer : x=a, x\in l et x\notin (a::l)*)
  case: (posnP (size l)) => [/eqP /nilP -> /=|].

  case: (altP (x =P a)) => [-> /=|Hx1].

    rewrite eq_refl /=.  
    case: (posnP (size l)) => [/eqP /nilP H|].
    rewrite H.
Qed.


Fixpoint cycle_aux (l: cycleSeq T) (fst: T) (x: T) :=
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

End Cycles.