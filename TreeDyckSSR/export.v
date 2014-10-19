Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
Require Import brace mDyck.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Constant eqb => "( = )".

Extract Inductive reflect => "bool" [ "true" "false" ].

Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inlined Constant size => "List.length".
Extract Inlined Constant behead => "List.tl".
Extract Inlined Constant cat => "List.append".

Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".

Extract Inlined Constant eq_brace => "( = )".

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".

Extract Inlined Constant plus => "( + )".
Extract Inlined Constant leq => "( <= )".
Extract Inlined Constant addn => "( + )".
Extract Inlined Constant muln => "( * )".
Extract Inlined Constant eqn => "( = )".

(*

Extract Constant seq_eqType => "( = )".
Extract Constant nat_eqType => "( = )".


val addn_rec : nat -> nat -> nat
val addn : nat -> nat -> nat
val leq : 'a -> 'a -> bool
val muln_rec : nat -> nat -> nat
val muln : nat -> nat -> nat

(* Extract Inductive alt_spec => "bool" [ "true" "false" ]. *)

(*
Extract Inductive nat => "Big_int.big_int"
  [ "Big_int.zero_big_int" "Big_int.succ_big_int" ] "(fun fO fS n ->
    let one = Big_int.unit_big_int in
    if n = Big_int.zero_big_int then fO () else fS (Big_int.sub_big_int n one))".
*)

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".

Extract Inlined Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqn => "( = )".
Extract Constant eqb => "( = )".
Extract Constant seq_eqType => "( = )".
Extract Constant nat_eqType => "( = )".
Extract Constant eq_op => "(fun eq -> eq)".

Extraction Inline addn addn_rec.
*)
(*
Extraction "mdycktuple.ml" tuple_factor.
Extraction "mdyck.ml" dyck factor.
*)

Extraction "mdyck.ml"  MDyck.
