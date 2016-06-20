Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple path.
From mathcomp Require Import finset perm fingroup matrix ssralg.
Require Import tools combclass subseq partition Yamanouchi permuted ordtype Schensted plactic Greene_inv std.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Section Hello.
Variable m n: nat.

Definition bimon_of_mat (M : 'M[nat]_(m, n)) : seq ('I_m * 'I_n) :=
  flatten [seq nseq (M a b) (a,b) | a <- enum 'I_m, b <- enum 'I_n].

Definition M := \matrix_(i<2,j<3) 1%N.

End Hello.

Check @bimon_of_mat 2 3.
Check M (Ordinal (lt0n 2)) (Ordinal (lt0n 3)).
Check bimon_of_mat (m:=2) (n:=3) M.
Eval compute in bimon_of_mat M.

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

Fixpoint mat_of_bimon (w:seq ('I_m*'I_n)) : 'M_(m,n):=
  match w with
  |[::] => \matrix_(i, j) (0%N)
  |(p::b) => match p with |pair i0 j0 =>
                           let M := mat_of_bimon b in add_mx M 1 i0 j0
                          
             end
  end.


Lemma bimon_lex (M:'M_(m,n)): sorted (lexico2 (@leqm m)  (@leqm n)) (bimon_of_mat M).
Proof.
Admitted.

Lemma matK (M:'M_(m,n)): mat_of_bimon (bimon_of_mat M) = M.
Proof.
Admitted.
  
Lemma bimonK (w: seq ('I_m*'I_n)) : sorted (lexico2 (@leqm m)  (@leqm n)) w -> bimon_of_mat (mat_of_bimon w) = w.
Proof.
Admitted.
  
End bimon_mat.
  

(* - mat_of_bimon et bimon_of_mat sont réciproques pour des w dans l'ordre lexico
   - utiliser la correspondance RSK (cf) Schensted.v en remplacant les 1,2,3... qui apparaissent dans Q, par 1,1,1,2,2,3,3,... et montrer que c'est un tableau*)
