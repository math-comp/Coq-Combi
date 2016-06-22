Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple path.
From mathcomp Require Import finset perm fingroup matrix ssralg.
Require Import tools combclass subseq partition Yamanouchi permuted ordtype Schensted plactic Greene_inv std stdtab tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.
Open Local Scope ring_scope.

Section Hello.
Variable m n: nat.

Definition bimon_of_mat (M : 'M[nat]_(m, n)) : seq ('I_m * 'I_n) :=
  flatten [seq nseq (M a b) (a,b) | a <- enum 'I_m, b <- enum 'I_n].

Definition M := \matrix_(i<2,j<3) 1%N.

End Hello.

Check @bimon_of_mat 2 3.
Check M (Ordinal (lt0n 2)) (Ordinal (lt0n 3)).
Check bimon_of_mat (m:=2) (n:=3) M.
(*Eval compute in ((bimon_of_mat M == [:: (0,0); (0,1); (0,2); (1,0); (1,1); (1,2)])%N).*)


Section Lexico2.

Variable T R: eqType.
Variable r: rel T.
Variable r': rel R.
Variable order: [/\ reflexive r, antisymmetric r & transitive r].
Variable order': [/\ reflexive r', antisymmetric r' & transitive r'].


Definition lexico2 : rel (T*R) :=
  fun (p1: T*R) => fun(p2: T*R) =>
  match p1 with
  |pair i j => match p2 with
               |pair k l => (r i k && (i!=k))||((i==k) && r' j l)
               end
  end.

Lemma lexico2_refl: reflexive lexico2.
Proof.
  case => a b /=.
  apply /orP; right.
  rewrite eqxx andTb.
  by apply order'.
Qed.

Lemma lexico2_antisym: antisymmetric lexico2.
Proof.
  case => a b; case => c d => /= /andP [].
  have anti: antisymmetric r by apply order.
  have anti': antisymmetric r' by apply order'.
  move => /orP; case => /andP [H1 H2];
  move => /orP; case => /andP [].
  - move => H3.
    contradict H2; apply /negP; rewrite negbK; apply /eqP.
    by apply anti; apply /andP.
  - rewrite eq_sym => H3.
    by contradict H2; apply /negP; rewrite negbK.
  - rewrite eq_sym => _ H3.
    by contradict H3; apply /negP; rewrite negbK.
  - move => _ H3.
    move: H1 => /eqP ->. 
    rewrite (_: b=d) //.
    by apply anti'; apply /andP.
Qed.


Lemma lexico2_trans: transitive lexico2.
Proof.
  case => a b; case => c d; case => e f /=.
  have trans': transitive r' by apply order'.
  have trans: transitive r by apply order.
  have anti: antisymmetric r by apply order.
  move => /orP [] /andP [H1 H2]; 
  move => /orP [] /andP [H3 H4];
  apply /orP.                    
  - left.
    have Hr: r c e by apply (trans a c e).
    rewrite Hr andTb.
    apply /negP => /eqP Heq; subst c.
    move: H4; apply /negP; rewrite negbK; apply /eqP.
    by apply anti; apply /andP.
  - left.
    apply /andP.
    by move: H3 => /eqP H; subst a.
  - left.
    apply /andP.
    by move: H1 => /eqP H; subst c.
  - right.
    apply /andP; split.
    + by move: H1 => /eqP ->.
    + by apply (trans' b d f).
Qed.

Lemma order_lexico2: [/\ reflexive lexico2, antisymmetric lexico2 & transitive lexico2].
Proof.
  split.
  - exact: lexico2_refl.
  - exact: lexico2_antisym.
  - exact: lexico2_trans.
Qed.

End Lexico2.

Section Lexico.


Variable T: eqType.
Variable r: rel T.
Variable order: [/\ reflexive r, antisymmetric r & transitive r].

Definition lexico : rel (T*T) := lexico2 r r. 

Lemma lexico_refl: reflexive lexico.
Proof. by apply lexico2_refl. Qed.

Lemma lexico_antisym: antisymmetric lexico.
Proof. by apply lexico2_antisym. Qed.


Lemma lexico_trans: transitive lexico.
Proof. by apply lexico2_trans. Qed.

Lemma order_lexico: [/\ reflexive lexico, antisymmetric lexico & transitive lexico].
Proof.
  split.
  - exact: lexico_refl.
  - exact: lexico_antisym.
  - exact: lexico_trans.
Qed.
End Lexico.

Section add_mx.
(*Not in MathComp (as far as I know) but useful here : 
adding k in a cell of the matrix given by its coordinates
This cant be done with a map *)
Fact add_mx_key: unit. Proof. by []. Qed.  
Definition add_mx m n (A:'M_(m,n)) k i0 j0 : 'M_(m,n):=
  \matrix[add_mx_key]_(i,j) (if (i==i0)&&(j==j0) then ((A i0 j0) + k)%N else A i0 j0). 
  
End add_mx.


Section leq_m.
  
Definition leqm m: rel ('I_m) :=
  fun x => fun y => x <= y.
  
End leq_m.

Section bimon_mat.
Variables m n: nat.
Variable T: eqType.

Fixpoint mat_of_bimon (w:seq ('I_m*'I_n)) : 'M_(m,n):=
  match w with
  |[::] => \matrix_(i, j) (0%N)
  |(p::b) => match p with |pair i0 j0 =>
                           let M := mat_of_bimon b in add_mx M 1 i0 j0
                          
             end
  end.

  (*Par récurrence sur le nombre de lignes => utiliser row' ou [u|d]submx ?
    Dans tous les cas, il faut définir ce qu'est une matrice à laquelle on ajoute une ligne, col_mx doit pouvoir marcher la dessus
*)
(*
Definition col_mx_ind (A:'M[T]_(m.+1,n)) := let M':= row' (Ordinal (ltnSn m)) A in let r := row (Ordinal (ltnSn m)) A in A = col_mx M' r.
*)
Lemma bimon_lex (M:'M_(m,n)): sorted (lexico2 (@leqm m)  (@leqm n)) (bimon_of_mat M).
Proof.
  elim: m M => [|m0 IHm0 M0].
  - admit.
  - 
Admitted.

Lemma matK (M:'M_(m,n)): mat_of_bimon (bimon_of_mat M) = M.
Proof.
Admitted.
  
Lemma bimonK (w: seq ('I_m*'I_n)) : sorted (lexico2 (@leqm m)  (@leqm n)) w -> bimon_of_mat (mat_of_bimon w) = w.
Proof.
Admitted.

Definition bottomw_of_mat (M:'M_(m,n)): seq 'I_n :=
  [seq (snd p)| p <- (bimon_of_mat M)].

Definition upw_of_mat (M:'M_(m,n)): seq 'I_m :=
  [seq (fst p)| p <- (bimon_of_mat M)].

End bimon_mat.

Section Schensted.

Variables m n : nat.

Fixpoint tab_of_yam y (w: seq 'I_m.+1) :=
  if y is y0 :: y' then
    if w is w0 :: w' then 
    append_nth (tab_of_yam y' w') w0 y0
    else [::]
  else [::].


Definition RSKmap (M : 'M[nat]_(m.+1, n.+1)) :=
  let (P,Q) := RSmap (bottomw_of_mat M) in
  (P, tab_of_yam Q (upw_of_mat M)).


(*Definition istabpair (pair : seq(seq 'I_n) * seq (seq 'I_m)) :=
  let: (P,Q) := pair in
  is_tableau P && is_tableau Q.
 *)

Lemma RSKmap_spec M : let (P,Q) := RSKmap M in
                      is_tableau P && is_tableau Q.
Proof.
  admit.
Admitted.


(*Definition de RSKmap_inv :
-w=[::]
tant que Q est non nul: 
  -parcourir Q en sens croissant à la recherche du plus grand élément
  -enlever cet élément i et garder les ligne k_1...k_n dans l'ordre 
  -faire invinstab P [k] -> on obitent P' [j]
  -w= (i,j)::w
fin
retourner w.
*)                              

Variable T: eqType.

Fixpoint remove_in_tab k (Q:seq (seq nat)) compt:=
  match Q with
  |(h::t) => let i := index k h in
             let (Q',l) := remove_in_tab k t compt.+1 in
             ((take i h)::Q', cat l (nseq (size (drop i h)) compt))
  |[::] => ([::],[::])
  end.

Fixpoint invinstabseq (P:seq (seq nat)) lnrow: (seq(seq nat)*seq nat):=
  match lnrow with
  |(nrow::ln') => let (P',l) := invinstabnrow P nrow in
                  let (Q,l') := invinstabseq P' ln' in
                  (Q, l::l')
  |[::] => ([::],[::])
  end.


Fixpoint RSK_inv (pair: seq(seq nat) * seq(seq nat)) (a:nat) : seq (seq (nat*nat)):=
  let (P,Q) := pair in
  let (Q',nrow) := remove_in_tab a Q 0 in
  let (P',l) := invinstabseq P nrow in
  if a is a'.+1 then
    [seq (a,j)| j<-l]::RSK_inv (P',Q') a'
  else
    [seq (0%N,j)| j<-l] :: [::].

Definition RSKmap_inv pair:=
  mat_of_bimon (flatten (RSK_inv pair)).

End Schensted.
