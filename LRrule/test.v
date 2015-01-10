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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import ordtype tableau yama stdtab shuffle multpoly skewtab therule implem.

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
    map (subs_eval eval) (sfilterleq sinn ((@to_word _) tab)).


Eval compute in
    let inner := [:: 2; 1] in
    let eval  := [:: 2; 1] in
    let outer := [:: 3; 2; 1] in
    ( map (yam_from_LRtab inner eval)
          (filter
             (predLRTripleFast (stdtab_of_yam (hyper_yam inner))
                               (stdtab_of_yam (hyper_yam eval)) )
             (list_stdtabsh outer)),
      (LRyam_enum inner eval outer) ).

Eval compute in
    let inner := [:: 2; 1] in
    let eval  := [:: 2; 1] in
    let outer := [:: 3; 2; 1] in
    perm_eq
      ( map (yam_from_LRtab inner eval)
            (filter
               (predLRTripleFast (stdtab_of_yam (hyper_yam inner))
                                 (stdtab_of_yam (hyper_yam eval)) )
               (list_stdtabsh outer)) )
      ( LRyam_enum inner eval outer ).

Eval compute in
    let inner := [:: 3; 2; 1] in
    let eval  := [:: 2; 2] in
    let outer := [:: 4; 3; 2; 1] in
      (LRyam_enum inner eval outer).


Eval compute in LRyamtab_list [:: 2] [:: 1; 1] [:: 3; 1].

Eval compute in LRyamtab_list [:: 2] [:: 1] [:: 3].

Eval compute in LRyamtab_list [:: 2; 1] [:: 2; 1] [:: 3; 2; 1].

Eval compute in LRyamtab_list [:: 3; 3; 1] [:: 3; 2; 1; 1] [:: 5; 4; 3; 2].

Eval compute in
    map (@to_word _) (LRyamtab_list [:: 3; 3; 1] [:: 3; 2; 1; 1] [:: 5; 4; 3; 2]).
(*
Eval compute in LRyam_enum [:: 3; 3; 1] [:: 3; 2; 1; 1] [:: 5; 4; 3; 2].
     = [:: [:: 0; 3; 1; 2; 1; 0; 0]; [:: 1; 3; 0; 2; 1; 0; 0]]
...00 ...00
...1  ...1
.02   .12
13    03
*)

Eval compute in
    map (@to_word _) (LRyamtab_list [:: 3; 3; 1] [:: 4; 2; 1] [:: 5; 4; 3; 2]).
(*
Eval compute in LRyam_enum [:: 3; 3; 1] [:: 4; 2; 1] [:: 5; 4; 3; 2].
     = [:: [:: 0; 1; 0; 2; 1; 0; 0]; [:: 0; 2; 0; 1; 1; 0; 0];
           [:: 1; 2; 0; 0; 1; 0; 0]]
...11 ...11 ...11
...2  ...2  ...2
.11   .12   .13
23    13    12
*)

(* According LRcalc = 18 *)
Eval compute in size (LRyamtab_list
  [:: 4; 3; 2; 1] [:: 4; 3; 2; 1] [:: 6; 5; 4; 3; 1; 1]).
(* According LRcalc = 9 *)
Eval compute in size (LRyamtab_list
  [:: 4; 3; 2; 1] [:: 4; 3; 2; 1] [:: 5; 5; 3; 3; 2; 1; 1]).
(* According to LRcalc and Wikipedia = 176 *)
Eval compute in size (LRyamtab_list
  [:: 5; 4; 3; 2; 1] [:: 5; 4; 3; 2; 1] [:: 8; 6; 5; 4; 3; 2; 1; 1]).
Eval compute in LRcoeff
  [:: 5; 4; 3; 2; 1] [:: 5; 4; 3; 2; 1] [:: 8; 6; 5; 4; 3; 2; 1; 1].
(* According to LRcalc and Wikipedia = 2064 *)
Eval compute in size (LRyamtab_list
  [:: 6; 5; 4; 3; 2; 1] [:: 6; 5; 4; 3; 2; 1] [:: 9; 8; 7; 5; 4; 3; 3; 2; 1]).
Eval compute in LRcoeff
  [:: 6; 5; 4; 3; 2; 1] [:: 6; 5; 4; 3; 2; 1] [:: 9; 8; 7; 5; 4; 3; 3; 2; 1].
