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


Section add_mx.
(*Not in MathComp (as far as I know) but useful here : 
adding k in a cell of the matrix given by its coordinates
This cant be done with a map *)
Fact add_mx_key: unit. Proof. by []. Qed.  
Definition add_mx m n (A:'M_(m,n)) k i0 j0 : 'M_(m,n):=
  \matrix[add_mx_key]_(i,j) (if (i==i0)&&(j==j0) then ((A i0 j0) + k)%N else A i0 j0). 
  
End add_mx.


Section bimon_mat.

Variables m' n': nat.
Notation m := m'.+1.
Notation n := n'.+1.
Definition alph := ('I_m * 'I_n)%type.

Canonical alph_pordType := Eval hnf in POrdType alph (prodlex_pordMixin _ _).

Definition alph_ordMixin :=
  Order.Mixin (T := alph_pordType) (@prodlex_total _ _).
Canonical alph_ordType :=
  Eval hnf in OrdType alph alph_ordMixin.

Definition bimon_of_mat (M : 'M[nat]_(m, n)) : seq alph :=
  flatten [seq nseq (M a b) (a,b) | a <- enum 'I_m, b <- enum 'I_n].

Fixpoint mat_of_bimon (w : seq alph) : 'M_(m,n):=
  match w with
  | [::] => \matrix_(i, j) (0%N)
  | ((i0, j0) :: b) => let M := mat_of_bimon b in add_mx M 1 i0 j0
  end.

End bimon_mat.

  (*Par récurrence sur le nombre de lignes => utiliser row' ou [u|d]submx ?
    Dans tous les cas, il faut définir ce qu'est une matrice à laquelle on ajoute une ligne, col_mx doit pouvoir marcher la dessus
*)
(*
Definition col_mx_ind (A:'M[T]_(m.+1,n)) := let M':= row' (Ordinal (ltnSn m)) A in let r := row (Ordinal (ltnSn m)) A in A = col_mx M' r.
*)

Section Bla.

Variables m' n': nat.
Notation m := m'.+1.
Notation n := n'.+1.
Notation alph := (alph m' n').

Definition col_mx_ind (A:'M[nat]_(m'.+1, n'.+1)) :=
  let M':= row' (Ordinal (ltnSn m')) A in
  let r := row (Ordinal (ltnSn m')) A in A = col_mx M' r.


Lemma bimon_lex (M : 'M_(m,n)): is_row (bimon_of_mat M).
Proof.
  
  (*
  elim: m M => [|m0 IHm0 M0].
  - admit.
  - *)
Admitted.

Lemma matK (M:'M_(m,n)): mat_of_bimon (bimon_of_mat M) = M.
Proof.
Admitted.
  
Lemma bimonK (w: seq alph) : is_row w -> bimon_of_mat (mat_of_bimon w) = w.
Proof.
Admitted.

Definition bottomw_of_mat (M:'M_(m,n)): seq 'I_n :=
  [seq p.2 | p <- (bimon_of_mat M)].

Definition upw_of_mat (M:'M_(m,n)): seq 'I_m :=
  [seq p.1 | p <- (bimon_of_mat M)].

End Bla.

Section Schensted.

Variables m' n' : nat.
Notation m := m'.+1.
Notation n := n'.+1.
Notation alph := (alph m' n').

Fixpoint tab_of_yam_rev y (w: seq 'I_m) : seq (seq 'I_m) :=
  if y is y0 :: y' then
    if w is w0 :: w' then
    append_nth (tab_of_yam_rev y' w') w0 y0
    else [::]
  else [::].

Definition tab_of_yam y w := tab_of_yam_rev y (rev w).

Definition RSKmap (M : 'M[nat]_(m, n)) : seq (seq 'I_n) * seq (seq 'I_m):=
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
