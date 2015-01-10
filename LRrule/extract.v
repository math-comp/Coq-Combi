(******************************************************************************)
(*       Copyright (C) 2014 Florent Hivert <florent.hivert@lri.fr>            *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm.
Require Import subseq partition ordtype schensted congr plactic green greeninv
        std stdtab skewtab therule implem.

Require Import Wf_nat.
Extraction Inline Wf_nat.lt_wf_rec1 Wf_nat.lt_wf_rec
  Wf_nat.lt_wf_ind Wf_nat.gt_wf_rec Wf_nat.gt_wf_ind.

Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive prod => "(*)"  [ "(,)" ].

(*
Extract Inductive nat => "Big_int.big_int"
  [ "Big_int.zero_big_int" "Big_int.succ_big_int" ] "(fun fO fS n ->
    let one = Big_int.unit_big_int in
    if n = Big_int.zero_big_int then fO () else fS (Big_int.sub_big_int n one))".

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant beq_nat => "( = )".
*)

Let RSbijnat := (@RSbij nat_ordType).
Let RSbijinvnat := (@RSbijinv nat_ordType).
Let RStabnat := (@RStab nat_ordType).
Let RStabinvnat := (@RStabinv nat_ordType).

Extraction "extract/schensted.ml"
           RS RSbijnat RSbijinvnat
           plactcongr
           greenRow greenCol
           is_std std.std
           RStabnat RStabinvnat
           is_stdtab
           LRyam_coeff LRcoeff LRyamtab_list
.
