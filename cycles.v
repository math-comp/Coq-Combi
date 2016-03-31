Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun bigop finset binomial fingroup perm.

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

Lemma rotater_isrotate s :
  (rotater n0 s) = rotate (size s - n0%%(size s)) s.
Proof.
  case: (posnP (size s)) => [/eqP /nilP -> /=| H0].
    by rewrite rotate_nil.
  rewrite /rotater /rotate /rotr.
  case: (posnP (n0%%size s)) => [->|H1].
    by rewrite subn0 rot_size modnn rot0 //.
  congr rot.
  rewrite [RHS]modn_small //.
  rewrite -subn_gt0 subnBA.
  by rewrite addnC addnK.
  by apply: ltnW; apply: ltn_pmod.
Qed.  

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

Lemma rotate_rotate m n s :
  rotate m (rotate n s) = rotate n (rotate m s).
Proof. by rewrite -!rotate_addn addnC. Qed.


Lemma rotate_rotater m n s :
  rotate m (rotater n s) = rotater n (rotate m s).
Proof. by rewrite /rotater /rotr size_rotate /rotate rot_rot size_rot. Qed.
  
Lemma rotater_rotater m n s : rotater m (rotater n s) = rotater n (rotater m s).
Proof. by rewrite /rotater /rotr !size_rot rot_rot. Qed.

Lemma nth_rotate x i n s :
  i<size s -> nth x (rotate n s) i = nth x s ((n+i)%%size s).
Proof.
  elim: n s => [|m IHm] s Hs /=.
    by rewrite rotate0 add0n modn_small.
  rewrite -{1}addn1 rotate_addn {}IHm size_rotate //.
  case: s Hs => [//|s0 s Hs].    
  rewrite rotate1_cons nth_rcons.
  case: (ltngtP ((m + i) %% size (s0 :: s)) (size s)) => Hineg.
  - rewrite addSn -addn1 (nth_ncons _ 1) -(modnDml (m+i) 1).
    rewrite [((m + i) %% size (s0 :: s) + 1)%%size(s0::s)] modn_small.  
    + by rewrite {1}addn1 ltnS ltn0 addnK.
    + by rewrite /= addn1 ltnS. 
  - exfalso; move: Hineg.    
    apply /negP; rewrite -leqNgt /= -ltnS.
    exact: ltn_pmod.
  - rewrite addSn -addn1 -(modnDml (m+i) 1) Hineg /= addn1 modnn.
    by rewrite (nth_ncons _ 1).
Qed.

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

Section CycleSeq.
Variable T: eqType.
  
Record cycleSeq := {x :> seq T; Huniq: uniq x}.

Canonical cycleSeq_subType := Eval hnf in [subType for x].
Definition cycleSeq_eqMixin := Eval hnf in [eqMixin of cycleSeq by <:].
Canonical cycleSeq_eqType := Eval hnf in EqType cycleSeq cycleSeq_eqMixin.
(*
Definition cycleSeq_choiceMixin := Eval hnf in [choiceMixin of cycleSeq by <:].
Canonical cycleSeq_choiceType := Eval hnf in ChoiceType cycleSeq cycleSeq_choiceMixin.
Definition cycleSeq_countMixin := Eval hnf in [countMixin of cycleSeq by <:].
Canonical cycleSeq_countType := Eval hnf in CountType cycleSeq cycleSeq_countMixin.
Canonical cycelSeq_subCountType := Eval hnf in [subCountType of cycleSeq].
*)

End CycleSeq.

Section Cycles.
From mathcomp Require Import finfun.

Variable T: eqType.

Implicit Type s: seq T.

Definition cycle_of_seq s x := nth x (rotate 1 s) (index x s).

Definition cycle_inv_of_seq s x := nth x (rotater 1 s) (index x s).


Lemma uniq_index_rotate s x n:
  uniq s -> x \in s -> (index x s) = ((index x (rotate n s)) + n)%%size s.
Proof.
  move => Huniq.
  rewrite -index_mem => Hindex.
  apply /eqP.
  rewrite -(nth_uniq x Hindex) ?nth_index //;
       move: Hindex; rewrite index_mem // => Hin.
  rewrite addnC -nth_rotate ?nth_index //.
  by rewrite mem_rotate.
  by move: Hin; rewrite -(mem_rotate n) -index_mem size_rotate.
  case: (posnP (size s)) Huniq Hin => [/eqP /nilP -> //|Hsize _ _].
  by apply: ltn_pmod.
Qed.

Lemma eq_perm_cycle s t:
  uniq s -> rot_eq s t -> cycle_of_seq s =1 cycle_of_seq t.  
Proof.
  move => Huniq /existsP [] n /eqP <- x.
  case: (boolP (x \in s)) => [Hin|].
  - rewrite /cycle_of_seq -rotate_addn (uniq_index_rotate n) //.
    rewrite !nth_rotate.
    by rewrite addnAC -modnDm modn_mod modnDm addnA //.
    by move: Hin; rewrite -(mem_rotate n) -index_mem size_rotate.
    case: (posnP (size s)) Hin => [/eqP /nilP {1}-> // |Hsize _].
    exact: ltn_pmod.
  - rewrite /cycle_of_seq => Hineg.
    rewrite !nth_default //; move: Hineg.
    by rewrite -(mem_rotate n) -index_mem -leqNgt -{1}(size_rotate 1).
    by rewrite -index_mem -leqNgt -{1}(size_rotate 1).      
Qed.

Lemma uniq_cycle_of_seq s:
  uniq s -> bijective(cycle_of_seq s).
Proof.
  move => Huniq.
  case: (posnP (size s)) => [/eqP /nilP ->|Hsize].
  - rewrite /cycle_of_seq /=.
    by exists id.  
  - exists (cycle_inv_of_seq (rotate 1 s)) => x;
     case (boolP (x \in s)) => Hin;
     rewrite /cycle_inv_of_seq /cycle_of_seq rotateK /=.
    + rewrite index_uniq;
         [|by move: Hin; rewrite -index_mem -(size_rotate 1)
          |by rewrite rotate_uniq].
       by rewrite nth_index.
    + rewrite !nth_default //.
      by move: Hin; rewrite -index_mem -leqNgt size_rotate.
      by move: Hin; rewrite -(mem_rotate 1) -index_mem -leqNgt size_rotate.  
      by move: Hin; rewrite -index_mem -leqNgt size_rotate.
    + rewrite index_uniq // ?nth_index //.   
        by rewrite mem_rotate.
        by move: Hin; rewrite -(mem_rotate 1) -index_mem size_rotate.
    + rewrite !nth_default //.
      by move: Hin; rewrite -(mem_rotate 1) -index_mem -leqNgt size_rotate.
      by move: Hin; rewrite -index_mem -leqNgt -(size_rotate 1).  
      by move: Hin; rewrite -(mem_rotate 1) -index_mem -leqNgt size_rotate.
Qed.

Lemma uniq_cycle_of_seq_inj s:
    uniq s -> injective(cycle_of_seq s).
Proof.
  move => Huniq.
  apply: bij_inj; exact: uniq_cycle_of_seq.
Qed.

End Cycles.

From mathcomp Require Import perm.

Section PermCycles.
Variable T: finType.

Definition permCycle (s: cycleSeq T) := perm (uniq_cycle_of_seq_inj (Huniq s)). 

Definition support (s: {perm T}) := [set x | s x != x].

Definition is_cycle (s : {perm T}) :=
  #|[set x in pcycles s | #|x| != 1 ]| == 1.

(*
Definition is_cycle s :=
 all (fun c : {set T} => (#|c| != 1) ==> all (fun d: {set T} => (d == c) || (#|d| == 1)) (enum (pcycles s))) (enum (pcycles s)).
*)

Definition cyclefun_of s x y : T :=
  if y \in pcycle s x then s y else y.

Lemma cyclefun_ofP s x : injective (cyclefun_of s x).
Proof.
  move => x1 x2.
  case (boolP (x1 \in pcycle s x)); case (boolP (x2 \in pcycle s x)).
  - rewrite /cyclefun_of => -> ->.
    by apply: perm_inj.
  - rewrite /cyclefun_of => /negbTE H1 H2; rewrite H1 H2; move => Heq; move: H2. 
    rewrite -eq_pcycle_mem => /eqP.
    rewrite -(pcycle_perm s 1 x1) expg1 Heq => /eqP.
    rewrite eq_pcycle_mem.
    by move: H1 => /negbT /negP.
  - rewrite /cyclefun_of => H1 /negbTE H2; rewrite H1 H2; move => Heq; move: H1. 
    rewrite -eq_pcycle_mem => /eqP.
    rewrite -(pcycle_perm s 1 x2) expg1 -Heq => /eqP.
    rewrite eq_pcycle_mem.
    by move: H2 => /negbT /negP.
  - by rewrite /cyclefun_of => /negbTE -> /negbTE ->.
Qed.

Definition cycle_of s x : {perm T} := perm (@cyclefun_ofP s x).

Lemma cycle_ofE s x : cycle_of s x =1 cyclefun_of s x.
Proof. by move => y; rewrite permE. Qed.

Lemma pcycleP (s: {perm T}) x y :
  reflect (exists n, y = (s ^+ n)%g x) (y \in pcycle s x).
Proof.
  apply (iffP idP).
  - rewrite /pcycle => /imsetP [] s0 /cycleP [] i Hs0 ->.  
    by exists i; rewrite /aperm Hs0.
  - move => [] n ->.
    apply /imsetP; exists (s ^+ n)%g; last by rewrite /aperm.
    by apply mem_cycle.
Qed.  

  
Lemma pcyclefixP (s: {perm T}) x :
  reflect (pcycle s x = [set x]) (s x == x). 
Proof.
  apply (iffP idP) => [/eqP Heq|/setP H].  
  - rewrite -setP => z.
    rewrite in_set1.
    apply /pcycleP /eqP => [ [] n -> |->].
    + by elim: n => [|n];[rewrite expg0 perm1 |rewrite expgS permM Heq].
    + by exists 0; rewrite expg0 perm1.
  - rewrite -in_set1 -H /pcycle.
    apply /imsetP => /=.  
    by exists s; [apply: cycle_id|rewrite /aperm].                           
Qed.

Lemma pcyclecardfix (s: {perm T}) x :
  (#|pcycle s x| != 1) = (x \in support s).
Proof.
  rewrite neq_ltn ltnS leqn0 cards_eq0.
  have /negbTE -> /= : pcycle s x != set0.
    apply /set0Pn; exists x; exact: pcycle_id.
  rewrite inE; apply /idP /idP.
  - apply contraL => /pcyclefixP ->.
    by rewrite cards1.
  - apply contraR; rewrite -leqNgt => H.
    apply /pcyclefixP /eqP; rewrite eq_sym eqEcard cards1 H andbT.
    apply /subsetP => y; rewrite inE => /eqP ->; exact: pcycle_id.
Qed.

Lemma pcyclecardfixP (s: {perm T}) x :
  reflect (#|pcycle s x| = 1) (s x == x).
Proof.
  apply (iffP idP) => [/pcyclefixP -> /=|].
    by rewrite cards1.
  move => /eqP /cards1P [] x0 => H; apply /pcyclefixP.
  rewrite H.
  have H0: x \in [set x0].
    by rewrite -H pcycle_id.
  move: H0.
  by rewrite in_set1 => /eqP ->.
Qed.

Lemma cycle_of_nsupp s x :
  x \notin (support s) -> cycle_of s x = (perm_one T).
Proof.
  rewrite in_set negbK => /pcyclefixP Heq.
  rewrite /cycle_of /perm_one; apply permP => y.
  rewrite !permE /cyclefun_of.
  case: (boolP (y \in pcycle s x)) => //.
  rewrite Heq in_set1 => /eqP ->.
  by move: Heq => /pcyclefixP /eqP.
Qed.

Lemma supp_of_cycle s x :
  x \in (support s) -> support (cycle_of s x) = pcycle s x.
Proof.
  rewrite inE => /pcyclefixP Hs.
  apply /setP => y.
  rewrite /support inE /cycle_of permE /cyclefun_of.
  case: (boolP (y \in pcycle s x)); last by move => _; apply /negbTE; rewrite negbK.
  rewrite -eq_pcycle_mem => /eqP Hpcycle; rewrite -Hpcycle in Hs.
  apply /negbT; apply /pcyclefixP.
  move => Habs; move: Hpcycle.
  rewrite Habs => Hpcycle.
  have Hyp: x \in [set y].
    by rewrite Hpcycle; apply: pcycle_id.
  move: Hyp; rewrite in_set => /eqP Heq.
  by rewrite Heq in Hs.
Qed.

(*
Lemma cycle_ofE s x y :
  is_cycle s -> x \in support s -> y \in support s ->
                                         cycle_of s x = cycle_of s y.
Proof.
  rewrite /is_cycle => H.
  rewrite /support !in_set => /pcyclecardfixP H1 /pcyclecardfixP H2.
 
  

Admitted.
*)


Lemma cycle_ofP s :
  reflect (exists x, x \in (support s) /\ cycle_of s x = s) (is_cycle s).
Proof.
  apply (iffP idP).
  - rewrite /is_cycle.
    move => /cards1P [] /= C /setP => Hcycle.
    have Hc := (Hcycle C).
    move: Hc; rewrite !inE eq_refl /pcycles => /andP [] /imsetP [] x _ ->.
    rewrite pcyclecardfix => Hin.
    exists x; split => //.
    rewrite cycle_ofE.
    
Admitted.

Lemma perm_cycle_ofK s x :
  support (s * (cycle_of s x)^-1) = support s :\: pcycle s x.
Proof.
Admitted.

End PermCycles.



(*
OK: cycle_of_seq: seqT -> T -> T
OK: uniq s -> bijective (cycle_of_seq s)
   cas où T:finType cycle_of_seq s : finfun (inutile)
OK:       T:finType s:cycleSeq cycle_of_seq s: perm

seq_of_cycle : fonction réciproque
is_cycle: 'S_T -> bool (utiliser la décomposition en support de cycles)

Lemma decomp sigma exists! D:{set 'S_T}, [&& all is_cycle D, trivIseq [:: support d| d \in enum D] & \prod _{c\inD}c = sigma


Définition du type et coercion naturelle : regarder dans le fichier std.v
*)