Add Rec LoadPath "../Combi/LRrule".

Require Import ssreflect ssrbool eqtype ssrnat seq .
Require Import bigop fintype Omega rat ssrint ssralg.
Require Import partition.
Import GRing.Theory.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Lemma ltppSS : forall m n , n<m-1 -> m = (m.-2).+2 .
case => [ltn0 //=|[ltn0 //=|m' //=]].
Save.

Lemma leq_succ : forall m n, (m.+1 <= n.+1) = (m <= n).
move => m n.
rewrite -addn1 -(addn1 n).
apply leq_add2r.
Save.



Fixpoint haut (L : seq nat) j {struct L} : nat :=
 match L with
  |[::] => 0
  |b :: reste => if j<b then (haut reste j).+1 else 0
end.


Lemma haut_nth : forall L j, is_part L -> forall i, (nth 0 L i <= j) = (haut L j <= i).
elim => [|a L IH] j Hpart i; [rewrite nth_default //= |].
case: (leqP a j) => [Haj|Hja].
+ move /is_part_ijP : Hpart.
  case => _ Hdecroissance.
  move : (Hdecroissance 0 i). 
  simpl.
  move => H1.
  have: (nth 0 (a :: L) i <= j).
    by rewrite (@leq_trans a (nth 0 (a :: L) i) j (H1 _) Haj).
  move => H2.
  rewrite H2. 
  move : Haj.
  rewrite leqNgt.
  case (j<a); by simpl.
+ rewrite /=.
  case: i => [|i'].
  rewrite /=.
  rewrite leqNgt.
  move : Hja.
  by case (j<a) => [_|].
  rewrite /=.
  move : Hja.
  case (j<a); [|rewrite //=].
  apply conj.
  exact (IH j (is_part_tl Hpart) i') .
Qed.

Lemma haut_decr (L : seq nat) j1 j2 : is_part L -> j1 <= j2 -> haut L j2 <= haut L j1.
move => Hp Hle.
rewrite -(haut_nth _ Hp).
apply: (leq_trans _ Hle).
by rewrite (haut_nth j1 Hp).
Save.

Definition hook' (L : seq nat) i j := ((nth 0 L i)-j).-1 + ((haut L j)-i).-1.
Definition hook (L : seq nat) i j := (hook' L i j ).+1.
Definition lindex L i := (nth 0 L i).-1.

Definition F_deno (L : seq nat) := 
    \prod_(i < (length L)) ( \prod_(j < (nth 0 L i)) (hook L i j)).

Definition is_in_part L i j := j < nth 0 L i.

Lemma is_in_part_col L i j : is_part L -> is_in_part L i j -> i < size L.
rewrite  /is_in_part.
move => Hpart Hin_part.
case : ltnP => [rewrite //= |  Hi].
have : (nth 0 L i = 0) .
  rewrite nth_default //=.
move  => H.
by rewrite H in Hin_part.
Save.

Lemma in_empty : forall i j, is_in_part [::] i j = false.
move => i j.
rewrite /is_in_part nth_default //=.
Qed.

Definition p0 := [:: 5; 3; 3; 1].

Lemma haut_lindex ( p : intpart) i : is_out_corner p i -> haut p (lindex p i) == 1+i .
rewrite /is_out_corner /lindex.
move => His_out_corner.
rewrite eqn_leq.
apply /andP; split.
rewrite -haut_nth; last by apply intpartP. 
rewrite -leq_succ.
rewrite prednK; last .
admit. admit.
Qed.


Lemma hook'0_out_corner L i j : is_part L -> is_in_part L i j -> hook' L i j == 0 
                                   -> is_out_corner L i && (j == (nth 0 L i).-1).
move => Hpart.
rewrite /is_in_part => Hin_part.
rewrite /hook' addn_eq0.
move /andP => [Hnth Hhaut].
apply /andP; split.
rewrite /is_out_corner. 
apply leq_trans with j.+1; last rewrite //=.
rewrite ltnS haut_nth //=.
by rewrite -subn_eq0 subnS.
rewrite eqn_leq.
apply /andP; split. 
rewrite -(leq_add2l 1).
apply leq_trans with (nth 0 L i).
trivial.
apply leqSpred.
rewrite -subn_eq0.
by rewrite -subn1 -subnAC subn1.
Qed.

Lemma negb_simpl : forall b1 b2, ~~ b1= ~~ b2 -> b1=b2.
move => b1 b2; by case b1; case b2.
Save.

Lemma iff_eqb : forall (b1 b2:bool), (b1<->b2) -> b1=b2.
move => b1 b2; case b1; case b2 => //=; intuition.
discriminate H0.
trivial.
Save.

Lemma haut_in_le L i j : is_part L -> ((is_in_part L i j) = (i < haut L j)). 
rewrite /is_in_part; move => Hp.
apply negb_simpl.
rewrite -!leqNgt.
apply iff_eqb.
by rewrite haut_nth.
Save.

Lemma out_corner_hook'0 L i : is_out_corner L i -> hook' L i (nth 0 L i).-1 = 0.
admit. 
Save.



Definition F L :=  ((((sumn L )`!)%:Q) / (F_deno L)%:Q)%Q. 

Definition F_decr L i := F (decr_nth L i).

Lemma F_decr_over_F L a : is_out_corner L a -> 
       (F_decr L a / F L =
        (sumn L)%:Q^-1 * (\prod_(0 <= i < a) (1 + (hook' L i (lindex L a))%:Q^-1))
             * (\prod_(0 <= j < lindex L a) (1 + (hook' L a j)%:Q^-1)))%Q.
admit. Save.
 
(* Lemma l4311 : F_deno [:: 4;2;1;1] = 448.
unfold F_deno.
rewrite !big_ord_recr !big_ord0.
simpl.
reflexivity.
Qed. *)

Fixpoint mange_nth  (L : seq nat) (n : nat) {struct L} : seq nat :=
  match L with
  | [::] => [::] 
  | x :: L' =>
     match n with
     | 0 => (x-1) :: L'
     | n'.+1 => x :: mange_nth L' n'
     end
  end.

Lemma hook_cons a L i j : is_part (a :: L) -> hook' ( a::L ) i.+1 j = hook' L i j.
Proof.
rewrite /hook' /= .
move =>  /andP  [] Hhead _.
case : (ltnP j a) => Hja.
- by rewrite subSS.
- case: L Hhead => [| b L'] //= Hhead.
  have := leq_trans Hhead Hja.
  rewrite leqNgt => /negbTE ->.
  by rewrite !sub0n .
Qed.


Lemma is_out_corner_cons a L i : is_out_corner L i <-> is_out_corner (a :: L) i.+1.
intuition. Qed.


Lemma hook_mange_ligne (L : seq nat) (i j :nat) : (is_part L) -> is_out_corner L i 
      -> (i < size L) -> (j < nth 0 L i -1) -> 
            hook' L i j = (hook' (decr_nth L i) i j).+1.
elim :  L i => [//= | a l IHl] [|i'] /= Hpart Hcorn Hl1 Hj.
- rewrite {2}(ltppSS Hj) /hook' /nth  /=.
  have -> : (j<a).
    exact: (leq_trans Hj (leq_subr _ _)). 
  rewrite prednK -!subn1. 
  rewrite Hj.
  succn_to_add.
  rewrite addnA.
  congr addn.
  rewrite addnC.
  rewrite subnK.
    rewrite -!subnDA addnC //=.
  * by rewrite ltn_subRL addn0.
  * rewrite (leq_trans (n := j.+1)) //=.
- rewrite !hook_cons.
  apply IHl.
  * move : Hpart.
    move => /andP [] _ Hpartr //=.
  * rewrite (is_out_corner_cons a l i') //=.
  * move : Hl1.
    by rewrite leq_succ.
  * trivial.
  * rewrite /is_part.
admit.
admit.
Qed.


Lemma hook'_decomp (L : intpart) (a b :nat) (o:nat) : 
     is_in_part L a b -> is_out_corner L o -> a <= o -> b <= lindex L o 
     -> hook' L a b = hook' L a  (lindex L o) + hook' L o b.
move => Hpart Hc Hl Hr; rewrite /hook'.
have Lpart : is_part L.
by apply intpartP.
have Hnao : (nth O L o <= nth O L a).
have :=(is_part_ijP L Lpart).
move => [_ H2].
by apply H2.
have Hnb : (haut L (lindex L o) <= haut L b).
by apply haut_decr.
have H : (haut L (lindex L o) = o).
rewrite /lindex.
set na:= nth 0 L a.
set hb:= haut L b.
set no:= nth 0 L o.
set ho:= haut L (no.-1).
admit.
admit.
Save.




