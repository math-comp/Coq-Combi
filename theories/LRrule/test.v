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
From mathcomp Require Import all_ssreflect.
Require Import ordtype tableau Yamanouchi stdtab shuffle freeSchur skewtab therule implem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint subs_eval eval i :=
  if eval is e0 :: ev then
        if i < e0 then 0
      else (subs_eval ev (i - e0)).+1
    else 0 (* Unused case *).

Definition yam_from_LRtab inner eval (tab : seq (seq nat)) :=
  let sinn := sumn inner in
    map (subs_eval eval) (sfilterleq sinn (to_word tab)).


Goal
  let inner := [:: 2; 1] in
  let eval  := [:: 2; 1] in
  let outer := [:: 3; 2; 1] in
  ( map (yam_from_LRtab inner eval)
        (filter
           (pred_LRtriple_fast (stdtab_of_yam (hyper_yam inner))
                               (stdtab_of_yam (hyper_yam eval)) )
           (enum_stdtabsh outer)),
    (LRyam_enum inner eval outer) )
  =
  ([:: [:: 0; 1; 0]; [:: 1; 0; 0]], [:: [:: 0; 1; 0]; [:: 1; 0; 0]]).
Proof. by vm_compute; exact erefl. Qed.

Goal
    let inner := [:: 2; 1] in
    let eval  := [:: 2; 1] in
    let outer := [:: 3; 2; 1] in
    perm_eq
      ( map (yam_from_LRtab inner eval)
            (filter
               (pred_LRtriple_fast (stdtab_of_yam (hyper_yam inner))
                                   (stdtab_of_yam (hyper_yam eval)) )
               (enum_stdtabsh outer)) )
      ( LRyam_enum inner eval outer ).
Proof. vm_compute; exact erefl. Qed.

Goal
  let inner := [:: 3; 2; 1] in
  let eval  := [:: 2; 2] in
  let outer := [:: 4; 3; 2; 1] in
  (LRyam_enum inner eval outer)
  = [:: [:: 1; 0; 1; 0]; [:: 1; 1; 0; 0]].
Proof. vm_compute; exact erefl. Qed.


Goal LRyamtab_list [:: 2] [:: 1; 1] [:: 3; 1]
     = [:: [:: [:: 0]; [:: 1]]].
Proof. vm_compute; exact erefl. Qed.

Goal LRyamtab_list [:: 2] [:: 1] [:: 3] = [:: [:: [:: 0]]].
Proof. vm_compute; exact erefl. Qed.

Goal LRyamtab_list [:: 2; 1] [:: 2; 1] [:: 3; 2; 1]
     = [:: [:: [:: 0]; [:: 0]; [:: 1]]; [:: [:: 0]; [:: 1]; [:: 0]]].
Proof. vm_compute; exact erefl. Qed.

Goal LRyamtab_list [:: 3; 3; 1] [:: 3; 2; 1; 1] [:: 5; 4; 3; 2]
     = [:: [:: [:: 0; 0]; [:: 1]; [:: 0; 2]; [:: 1; 3]];
           [:: [:: 0; 0]; [:: 1]; [:: 1; 2]; [:: 0; 3]]].
Proof. vm_compute; exact erefl. Qed.

Goal map to_word (LRyamtab_list [:: 3; 3; 1] [:: 3; 2; 1; 1] [:: 5; 4; 3; 2])
     = [:: [:: 1; 3; 0; 2; 1; 0; 0]; [:: 0; 3; 1; 2; 1; 0; 0]].
Proof. vm_compute; exact erefl. Qed.


Goal LRyam_enum [:: 3; 3; 1] [:: 3; 2; 1; 1] [:: 5; 4; 3; 2]
= [:: [:: 0; 3; 1; 2; 1; 0; 0]; [:: 1; 3; 0; 2; 1; 0; 0]].
Proof. vm_compute; exact erefl. Qed.
(**
...00 ...00
...1  ...1
.02   .12
13    03
*)

Goal map to_word (LRyamtab_list [:: 3; 3; 1] [:: 4; 2; 1] [:: 5; 4; 3; 2])
     = [:: [:: 1; 2; 0; 0; 1; 0; 0]; [:: 0; 2; 0; 1; 1; 0; 0];
           [:: 0; 1; 0; 2; 1; 0; 0]].
Proof. vm_compute; exact erefl. Qed.

Goal LRyam_enum [:: 3; 3; 1] [:: 4; 2; 1] [:: 5; 4; 3; 2]
     = [:: [:: 0; 1; 0; 2; 1; 0; 0]; [:: 0; 2; 0; 1; 1; 0; 0];
           [:: 1; 2; 0; 0; 1; 0; 0]].
Proof. vm_compute; exact erefl. Qed.
(**
...11 ...11 ...11
...2  ...2  ...2
.11   .12   .13
23    13    12
*)

(* According LRcalc = 18 *)
Goal size (LRyamtab_list
  [:: 4; 3; 2; 1] [:: 4; 3; 2; 1] [:: 6; 5; 4; 3; 1; 1]) = 18.
Proof. vm_compute; exact erefl. Qed.
(* According LRcalc = 9 *)
Goal size (LRyamtab_list
  [:: 4; 3; 2; 1] [:: 4; 3; 2; 1] [:: 5; 5; 3; 3; 2; 1; 1]) = 9.
Proof. vm_compute; exact erefl. Qed.
(* According to LRcalc and Wikipedia = 176 *)
Goal size (LRyamtab_list
  [:: 5; 4; 3; 2; 1] [:: 5; 4; 3; 2; 1] [:: 8; 6; 5; 4; 3; 2; 1; 1]) = 176.
Proof. vm_compute; exact erefl. Qed.
Goal LRcoeff
  [:: 5; 4; 3; 2; 1] [:: 5; 4; 3; 2; 1] [:: 8; 6; 5; 4; 3; 2; 1; 1] = 176.
Proof. vm_compute; exact erefl. Qed.
(* According to LRcalc and Wikipedia = 2064 *)
Goal size (LRyamtab_list
  [:: 6; 5; 4; 3; 2; 1] [:: 6; 5; 4; 3; 2; 1] [:: 9; 8; 7; 5; 4; 3; 3; 2; 1]) = 2064.
Proof. vm_compute; exact erefl. Qed.
Goal LRcoeff
  [:: 6; 5; 4; 3; 2; 1] [:: 6; 5; 4; 3; 2; 1] [:: 9; 8; 7; 5; 4; 3; 3; 2; 1] = 2064.
Proof. vm_compute; exact erefl. Qed.
