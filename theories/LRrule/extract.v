(** * Combi.LRrule.extract : Extracting the implementation to OCaml *)
(******************************************************************************)
(*      Copyright (C) 2014-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
(** * A certified OCaml implementation

We extract to OCaml the implementation of the Robinson-Schensted correspondance
and The Littlewood-Richardson Rule.
 **********)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg.
From mathcomp Require Import mpoly.
Require Import subseq partition ordtype Schensted congr plactic Greene Greene_inv
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
Extract Constant add => "( + )".
Extract Constant mult => "( * )".
Extract Constant minus => "(fun m n -> if n > m then 0 else m - n )".
Extract Constant eqn => "( = )".
Extract Constant leq => "( <= )".
*)

Definition disp := Order.NatOrder.nat_display.
Definition RS := (@RS disp nat).
Definition RSbijnat := (@RSbij disp nat).
Definition RSbijinvnat := (@RSbijinv disp nat).
Definition RStabnat := (@RStab disp nat).
Definition RStabinvnat := (@RStabinv disp nat).

Set Warnings "-extraction-reserved-identifier,-extraction-opaque-accessed".
(*
(** ** The Robinson-Schensted correspondance *)
Extraction "src/LRrule/schensted.ml"
           RS (*RSbijnat RSbijinvnat
           plactcongr
           Greene_row Greene_col
           is_std std.std
           RStabnat RStabinvnat
           is_stdtab
           LRyam_coeff LRcoeff LRyamtab_list *)
.
*)

(** ** The Littlewood-Richardson Rule *)
Extraction "src/LRrule/lrcoeff.ml"
           LRcoeff LRyamtab_list
.
