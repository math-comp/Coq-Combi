Require Import Wf_nat.
Extraction Inline Wf_nat.lt_wf_rec1 Wf_nat.lt_wf_rec
  Wf_nat.lt_wf_ind Wf_nat.gt_wf_rec Wf_nat.gt_wf_ind.

Require Import Dyck.
Require Import DyckTree.
Require Import ListOfBinTrees.
Require Import ListOfDyck.


Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive prod => "(*)"  [ "(,)" ].

(*
Extract Inductive nat => "Big_int.big_int"
  [ "Big_int.zero_big_int" "Big_int.succ_big_int" ] "(fun fO fS n ->
    let one = Big_int.unit_big_int in
    if n = Big_int.zero_big_int then fO () else fS (Big_int.sub_big_int n one))".
*)

(*
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant minus => "( - )".
Extract Constant beq_nat => "( = )".
*)


Extraction "extract/dycktree.ml" dyck_to_tree tree_to_dyck.
Extraction "extract/dyck.ml" dyck_decompose_grammar.
Extraction "extract/listTree.ml" list_of_trees list_of_trees_slow.
Extraction "extract/listDyck.ml" list_of_dyck.
