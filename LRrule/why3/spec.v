(* This file is generated by Why3's coq-ssreflect driver *)
(* Beware! Only edit allowed sections below    *)

Require Import ssreflect ssrbool ssrfun ssrnat seq eqtype ssrint.
Require Import ssrint ssrwhy3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import ssralg ssrnum.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.


(* Why3 assumption *)
Definition unit := unit.

Axiom qtmark : Type.

Parameter set: forall {a: why3Type} {b: why3Type}, (a -> b)%type -> a -> b ->
  (a -> b)%type.

Axiom Select_eq : forall {a: why3Type} {b: why3Type},
  forall (m:(a -> b)%type), forall (a1:a) (a2:a), forall (b1:b), (a1 = a2) ->
  (((set m a1 b1) a2) = b1).

Axiom Select_neq : forall {a: why3Type} {b: why3Type},
  forall (m:(a -> b)%type), forall (a1:a) (a2:a), forall (b1:b),
  (~ (a1 = a2)) -> (((set m a1 b1) a2) = (m a2)).

Parameter const: forall {a: why3Type} {b: why3Type}, b -> (a -> b)%type.

(* Why3 assumption *)
Definition index := (int* int)%type.

(* Why3 assumption *)
Definition valid_index {a: why3Type} (a1:(matrix a)) (i:(int*
  int)%type): Prop :=
  match i with
  | (r, c) => ((0%:Z <= r)%Z /\ (r < (nrows a1 : int))%Z) /\
      ((0%:Z <= c)%Z /\ (c < (ncols a1 : int))%Z)
  end.

Parameter sum: int -> int -> (int -> int) -> int.

Axiom sum_def1 : forall (f:(int -> int)) (a:int) (b:int), (b <= a)%Z ->
  ((sum a b f) = 0%:Z).

Axiom sum_def2 : forall (f:(int -> int)) (a:int) (b:int), (a < b)%Z ->
  ((sum a b f) = ((sum a (b - 1%:Z)%Z f) + (f (b - 1%:Z)%Z))%Z).

Axiom sum_left : forall (f:(int -> int)) (a:int) (b:int), (a < b)%Z ->
  ((sum a b f) = ((f a) + (sum (a + 1%:Z)%Z b f))%Z).

Axiom sum_ext : forall (f:(int -> int)) (g:(int -> int)) (a:int) (b:int),
  (forall (i:int), ((a <= i)%Z /\ (i < b)%Z) -> ((f i) = (g i))) -> ((sum a b
  f) = (sum a b g)).

Axiom sum_le : forall (f:(int -> int)) (g:(int -> int)) (a:int) (b:int),
  (forall (i:int), ((a <= i)%Z /\ (i < b)%Z) -> ((f i) <= (g i))%Z) ->
  ((sum a b f) <= (sum a b g))%Z.

Axiom sum_nonneg : forall (f:(int -> int)) (a:int) (b:int), (forall (i:int),
  ((a <= i)%Z /\ (i < b)%Z) -> (0%:Z <= (f i))%Z) -> (0%:Z <= (sum a b f))%Z.

Axiom sum_decomp : forall (f:(int -> int)) (a:int) (b:int) (c:int),
  ((a <= b)%Z /\ (b <= c)%Z) -> ((sum a c f) = ((sum a b f) + (sum b c
  f))%Z).

(* Why3 assumption *)
Definition sum_sub_array (a:(array int)) (lo:int) (hi:int): int := (sum lo hi
  (fun (i:int) => (get a i))).

(* Why3 assumption *)
Definition sum_array (a:(array int)): int := (sum_sub_array a 0%:Z
  (size a : int)).

Axiom sum_sub_array_shift : forall (a:(array int)) (b:(array int)) (lo:int)
  (hi:int), (((0%:Z <= (size a : int))%Z /\ (0%:Z <= (size b : int))%Z) /\
  ((((size a : int) + 1%:Z)%Z = (size b : int)) /\ forall (i:int),
  ((lo <= i)%Z /\ (i < hi)%Z) -> ((get a i) = (get b (i + 1%:Z)%Z)))) ->
  ((sum_sub_array a lo hi) = (sum_sub_array b (lo + 1%:Z)%Z (hi + 1%:Z)%Z)).

Axiom sum_array_sub : forall (a:(array int)) (b:(array int)) (lo:int)
  (hi:int), (((0%:Z <= (size a : int))%Z /\ (0%:Z <= (size b : int))%Z) /\
  ((size a : int) = (size b : int))) -> ((sum lo hi (fun (i:int) =>
  ((get b i) - (get a i))%Z)) = ((sum_sub_array b lo hi) - (sum_sub_array a
  lo hi))%Z).

Parameter numof: (int -> bool) -> int -> int -> int.

Axiom Numof_empty : forall (p:(int -> bool)) (a:int) (b:int), (b <= a)%Z ->
  ((numof p a b) = 0%:Z).

Axiom Numof_right_no_add : forall (p:(int -> bool)) (a:int) (b:int),
  (a < b)%Z -> ((~ ((p (b - 1%:Z)%Z) = true)) -> ((numof p a b) = (numof p a
  (b - 1%:Z)%Z))).

Axiom Numof_right_add : forall (p:(int -> bool)) (a:int) (b:int),
  (a < b)%Z -> (((p (b - 1%:Z)%Z) = true) -> ((numof p a
  b) = (1%:Z + (numof p a (b - 1%:Z)%Z))%Z)).

Axiom Numof_bounds : forall (p:(int -> bool)) (a:int) (b:int), (a < b)%Z ->
  ((0%:Z <= (numof p a b))%Z /\ ((numof p a b) <= (b - a)%Z)%Z).

Axiom Numof_append : forall (p:(int -> bool)) (a:int) (b:int) (c:int),
  ((a <= b)%Z /\ (b <= c)%Z) -> ((numof p a c) = ((numof p a b) + (numof p b
  c))%Z).

Axiom Numof_left_no_add : forall (p:(int -> bool)) (a:int) (b:int),
  (a < b)%Z -> ((~ ((p a) = true)) -> ((numof p a b) = (numof p (a + 1%:Z)%Z
  b))).

Axiom Numof_left_add : forall (p:(int -> bool)) (a:int) (b:int), (a < b)%Z ->
  (((p a) = true) -> ((numof p a b) = (1%:Z + (numof p (a + 1%:Z)%Z b))%Z)).

Axiom Empty : forall (p:(int -> bool)) (a:int) (b:int), (forall (n:int),
  ((a <= n)%Z /\ (n < b)%Z) -> ~ ((p n) = true)) -> ((numof p a b) = 0%:Z).

Axiom Full : forall (p:(int -> bool)) (a:int) (b:int), (a <= b)%Z ->
  ((forall (n:int), ((a <= n)%Z /\ (n < b)%Z) -> ((p n) = true)) -> ((numof p
  a b) = (b - a)%Z)).

Axiom numof_increasing : forall (p:(int -> bool)) (i:int) (j:int) (k:int),
  ((i <= j)%Z /\ (j <= k)%Z) -> ((numof p i j) <= (numof p i k))%Z.

Axiom numof_strictly_increasing : forall (p:(int -> bool)) (i:int) (j:int)
  (k:int) (l:int), ((i <= j)%Z /\ ((j <= k)%Z /\ (k < l)%Z)) -> (((p
  k) = true) -> ((numof p i j) < (numof p i l))%Z).

Axiom numof_change_any : forall (p1:(int -> bool)) (p2:(int -> bool)) (a:int)
  (b:int), (forall (j:int), ((a <= j)%Z /\ (j < b)%Z) -> (((p1 j) = true) ->
  ((p2 j) = true))) -> ((numof p1 a b) <= (numof p2 a b))%Z.

Axiom numof_change_some : forall (p1:(int -> bool)) (p2:(int -> bool))
  (a:int) (b:int) (i:int), ((a <= i)%Z /\ (i < b)%Z) -> ((forall (j:int),
  ((a <= j)%Z /\ (j < b)%Z) -> (((p1 j) = true) -> ((p2 j) = true))) ->
  ((~ ((p1 i) = true)) -> (((p2 i) = true) -> ((numof p1 a b) < (numof p2 a
  b))%Z))).

Axiom numof_change_equiv : forall (p1:(int -> bool)) (p2:(int -> bool))
  (a:int) (b:int), (forall (j:int), ((a <= j)%Z /\ (j < b)%Z) -> (((p1
  j) = true) <-> ((p2 j) = true))) -> ((numof p2 a b) = (numof p1 a b)).

(* Why3 assumption *)
Definition is_part (shape:(array int)): Prop :=
  (1%:Z <= (size shape : int))%Z /\ ((forall (i:int) (j:int),
  ((0%:Z <= i)%Z /\ ((i <= j)%Z /\ (j < (size shape : int))%Z)) ->
  ((get shape j) <= (get shape i))%Z) /\
  (0%:Z <= (get shape ((size shape : int) - 1%:Z)%Z))%Z).

Axiom is_part_nonneg : forall (sh:(array int)), (is_part sh) ->
  forall (i:int), ((0%:Z <= i)%Z /\ (i < (size sh : int))%Z) ->
  (0%:Z <= (get sh i))%Z.

(* Why3 assumption *)
Definition included (inner:(array int)) (outer:(array int)): Prop :=
  ((size inner : int) = (size outer : int)) /\ forall (i:int),
  ((0%:Z <= i)%Z /\ (i < (size outer : int))%Z) ->
  ((get inner i) <= (get outer i))%Z.

Axiom sum_le_eq : forall (f:(int -> int)) (g:(int -> int)) (a:int) (b:int),
  ((forall (i:int), ((a <= i)%Z /\ (i < b)%Z) -> ((f i) <= (g i))%Z) /\
  ((sum a b f) = (sum a b g))) -> forall (i:int), ((a <= i)%Z /\
  (i < b)%Z) -> ((f i) = (g i)).

Axiom included_parts_eq : forall (innev:(array int)) (eval:(array int)),
  (included innev eval) -> (((sum_array innev) = (sum_array eval)) ->
  forall (i:int), ((0%:Z <= i)%Z /\ (i < (size innev : int))%Z) ->
  ((get innev i) = (get eval i))).

Parameter fc: (array int) -> int -> (int -> bool).

Axiom fc_def : forall (a:(array int)) (v:int) (i:int), (((fc a v)
  i) = true) <-> ((get a i) = v).

(* Why3 assumption *)
Definition numeq (a:(array int)) (v:int) (lo:int) (hi:int): int :=
  (numof (fc a v) lo hi).

Axiom numeq_shift : forall (a1:(array int)) (a2:(array int)) (v:int) (lo:int)
  (hi:int), (((0%:Z <= (size a1 : int))%Z /\ (0%:Z <= (size a2 : int))%Z) /\
  forall (i:int), ((lo <= i)%Z /\ (i < hi)%Z) ->
  ((get a1 i) = (get a2 (i + 1%:Z)%Z))) -> ((numeq a1 v lo hi) = (numeq a2 v
  (lo + 1%:Z)%Z (hi + 1%:Z)%Z)).

(* Why3 assumption *)
Definition valid_input (outer:(array int)) (inner:(array int)): Prop :=
  (included inner outer) /\ ((is_part inner) /\ (is_part outer)).

(* Why3 assumption *)
Definition eq_prefix (s1:(array int)) (s2:(array int)) (i:int): Prop :=
  forall (k:int), ((0%:Z <= k)%Z /\ (k < i)%Z) -> ((get s1 k) = (get s2 k)).

(* Why3 assumption *)
Definition eq_array (s1:(array int)) (s2:(array int)): Prop :=
  ((size s1 : int) = (size s2 : int)) /\ (eq_prefix s1 s2 (size s1 : int)).

(* Why3 assumption *)
Definition valid_eval (eval:(array int)): Prop :=
  (1%:Z <= (size eval : int))%Z /\ ((is_part eval) /\
  ((get eval ((size eval : int) - 1%:Z)%Z) = 0%:Z)).

(* Why3 assumption *)
Definition valid_innev (outer:(array int)) (inner:(array int))
  (eval:(array int)) (innev:(array int)) (work:(matrix int)) (row:int)
  (idx:int) (lastinnev:int): Prop := ((0%:Z <= lastinnev)%Z /\
  (lastinnev < (size eval : int))%Z) /\ ((is_part innev) /\ ((included innev
  eval) /\ ((forall (r:int), ((0%:Z <= r)%Z /\ (r < row)%Z) ->
  forall (i:int), ((0%:Z <= i)%Z /\
  (i < ((get outer r) - (get inner r))%Z)%Z) -> ((0%:Z <= (matrix_get work (
  r, i)))%Z /\ ((matrix_get work (r, i)) < lastinnev)%Z)) /\
  (((row < (size outer : int))%Z -> forall (i:int), ((idx < i)%Z /\
  (i < ((get outer row) - (get inner row))%Z)%Z) ->
  ((0%:Z <= (matrix_get work (row, i)))%Z /\ ((matrix_get work (row,
  i)) < lastinnev)%Z)) /\ (((lastinnev = 0%:Z) \/
  (0%:Z < (get innev (lastinnev - 1%:Z)%Z))%Z) /\ forall (i:int),
  ((lastinnev <= i)%Z /\ (i < (size innev : int))%Z) ->
  ((get innev i) = 0%:Z)))))).

Axiom is_part_eq : forall (a1:(array int)) (a2:(array int)), (is_part a1) ->
  ((eq_array a1 a2) -> (is_part a2)).

(* Why3 assumption *)
Definition width (outer:(array int)) (inner:(array int)): (int -> int) :=
  fun (r:int) => ((get outer r) - (get inner r))%Z.

(* Why3 assumption *)
Definition frame (outer:(array int)) (inner:(array int)) (w1:(matrix int))
  (w2:(matrix int)) (row:int) (idx:int): Prop := (forall (r:int),
  ((0%:Z <= r)%Z /\ (r < row)%Z) -> forall (i:int), ((0%:Z <= i)%Z /\
  (i < ((width outer inner) r))%Z) -> ((matrix_get w2 (r,
  i)) = (matrix_get w1 (r, i)))) /\ forall (i:int), ((idx < i)%Z /\
  (i < ((get outer row) - (get inner row))%Z)%Z) -> ((matrix_get w2 (row,
  i)) = (matrix_get w1 (row, i))).

Axiom valid_innev_framed : forall (outer:(array int)) (inner:(array int))
  (eval:(array int)) (innev:(array int)) (work1:(matrix int))
  (work2:(matrix int)) (row:int) (idx:int) (lastinnev:int), (valid_innev
  outer inner eval innev work1 row idx lastinnev) -> ((frame outer inner
  work1 work2 row idx) -> (valid_innev outer inner eval innev work2 row idx
  lastinnev)).

Axiom frame_weakening : forall (outer:(array int)) (inner:(array int))
  (work1:(matrix int)) (work2:(matrix int)) (row:int) (idx:int), (frame outer
  inner work1 work2 row (idx - 1%:Z)%Z) -> (frame outer inner work1 work2 row
  idx).

Axiom frame_trans : forall (outer:(array int)) (inner:(array int))
  (work1:(matrix int)) (work2:(matrix int)) (work3:(matrix int)) (row:int)
  (idx:int), (frame outer inner work1 work2 row idx) -> ((frame outer inner
  work2 work3 row idx) -> (frame outer inner work1 work3 row idx)).

(* Why3 assumption *)
Definition non_decreasing_row_suffix (outer:(array int)) (inner:(array int))
  (work:(matrix int)) (r:int) (start:int): Prop := forall (i1:int) (i2:int),
  ((start <= i1)%Z /\ ((i1 <= i2)%Z /\
  (i2 < ((get outer r) - (get inner r))%Z)%Z)) -> ((matrix_get work (r,
  i1)) <= (matrix_get work (r, i2)))%Z.

(* Why3 assumption *)
Definition increasing_column (outer:(array int)) (inner:(array int))
  (work:(matrix int)) (r:int) (i:int): Prop := ((0%:Z < r)%Z /\
  (((get inner (r - 1%:Z)%Z) - (get inner r))%Z <= i)%Z) ->
  ((matrix_get work ((r - 1%:Z)%Z,
  (i - ((get inner (r - 1%:Z)%Z) - (get inner r))%Z)%Z)) < (matrix_get work (
  r, i)))%Z.

(* Why3 assumption *)
Definition is_tableau_reading_suffix (outer:(array int)) (inner:(array int))
  (work:(matrix int)) (row:int) (idx:int): Prop := (forall (r:int),
  ((0%:Z <= r)%Z /\ (r < row)%Z) -> (non_decreasing_row_suffix outer inner
  work r 0%:Z)) /\ (((row < (size outer : int))%Z ->
  (non_decreasing_row_suffix outer inner work row (idx + 1%:Z)%Z)) /\
  ((forall (r:int), ((1%:Z <= r)%Z /\ (r < row)%Z) -> forall (i:int),
  ((0%:Z <= i)%Z /\ (i < ((get outer r) - (get inner r))%Z)%Z) ->
  (increasing_column outer inner work r i)) /\
  ((row < (size outer : int))%Z -> forall (i:int), ((idx < i)%Z /\
  (i < ((get outer row) - (get inner row))%Z)%Z) -> (increasing_column outer
  inner work row i)))).

(* Why3 assumption *)
Definition is_tableau_reading (outer:(array int)) (inner:(array int))
  (work:(matrix int)): Prop := (is_tableau_reading_suffix outer inner work
  (size outer : int) 0%:Z).

(* Why3 assumption *)
Definition valid_work (outer:(array int)) (inner:(array int))
  (w:(matrix int)): Prop := ((nrows w : int) = (size outer : int)) /\
  forall (r:int), ((0%:Z <= r)%Z /\ (r < (size outer : int))%Z) ->
  (((get outer r) - (get inner r))%Z <= (ncols w : int))%Z.

Parameter to_word: (array int) -> (array int) -> (matrix int) -> (array int).

Axiom to_word_size : forall (outer:(array int)) (inner:(array int))
  (w:(matrix int)), (included inner outer) -> ((valid_work outer inner w) ->
  ((size (to_word outer inner w) : int) = (sum 0%:Z (size outer : int)
  (width outer inner)))).

Axiom to_word_contents : forall (outer:(array int)) (inner:(array int))
  (w:(matrix int)), (included inner outer) -> ((valid_work outer inner w) ->
  forall (r:int), ((0%:Z <= r)%Z /\ (r < (size outer : int))%Z) ->
  forall (i:int), ((0%:Z <= i)%Z /\ (i < ((width outer inner) r))%Z) ->
  ((get (to_word outer inner w) (i + (sum (r + 1%:Z)%Z (size outer : int)
  (width outer inner)))%Z) = (matrix_get w (r, i)))).

(* Why3 assumption *)
Definition is_yam_suffix (w:(array int)) (len:int): Prop := let n :=
  (size w : int) in (((0%:Z <= len)%Z /\ (len <= n)%Z) /\ ((forall (i:int),
  (((n - len)%Z <= i)%Z /\ (i < n)%Z) -> (0%:Z <= (get w i))%Z) /\
  forall (p:int), ((0%:Z <= p)%Z /\ (p <= len)%Z) -> forall (v1:int)
  (v2:int), ((0%:Z <= v1)%Z /\ (v1 <= v2)%Z) -> ((numeq w v2 (n - p)%Z
  n) <= (numeq w v1 (n - p)%Z n))%Z)).

(* Why3 assumption *)
Definition is_yam_of_eval_suffix (eval:(array int)) (w:(array int))
  (len:int): Prop := let n := (size w : int) in ((is_yam_suffix w len) /\
  ((forall (i:int), (((n - len)%Z <= i)%Z /\ (i < n)%Z) ->
  ((0%:Z <= (get w i))%Z /\ ((get w i) < (size eval : int))%Z)) /\
  forall (v:int), ((0%:Z <= v)%Z /\ (v < (size eval : int))%Z) -> ((numeq w v
  (n - len)%Z n) = (get eval v)))).

(* Why3 assumption *)
Definition is_yam_of_eval (eval:(array int)) (w:(array int)): Prop :=
  (is_yam_of_eval_suffix eval w (size w : int)).

Axiom is_yam_of_eval_length : forall (eval:(array int)) (w:(array int)),
  (is_yam_of_eval eval w) -> ((size w : int) = (sum_array eval)).

(* Why3 assumption *)
Definition is_solution_suffix (outer:(array int)) (inner:(array int))
  (eval:(array int)) (w:(matrix int)) (row:int) (idx:int): Prop :=
  (valid_work outer inner w) /\ ((is_yam_of_eval_suffix eval (to_word outer
  inner w) (((sum 0%:Z (row + 1%:Z)%Z (width outer
  inner)) - idx)%Z - 1%:Z)%Z) /\ (is_tableau_reading_suffix outer inner w row
  idx)).

(* Why3 assumption *)
Definition is_solution (outer:(array int)) (inner:(array int))
  (eval:(array int)) (w:(matrix int)): Prop := (valid_work outer inner w) /\
  ((is_yam_of_eval eval (to_word outer inner w)) /\ (is_tableau_reading outer
  inner w)).

Axiom solution_length : forall (outer:(array int)) (inner:(array int))
  (eval:(array int)) (w:(matrix int)), (is_solution outer inner eval w) ->
  ((size (to_word outer inner w) : int) = (sum_array eval)).

(* Why3 assumption *)
Definition eq_rows (outer:(array int)) (inner:(array int)) (w1:(matrix int))
  (w2:(matrix int)) (row:int): Prop := forall (r:int), ((0%:Z <= r)%Z /\
  (r < row)%Z) -> forall (i:int), ((0%:Z <= i)%Z /\ (i < ((width outer inner)
  r))%Z) -> ((matrix_get w1 (r, i)) = (matrix_get w2 (r, i))).

(* Why3 assumption *)
Definition lt_sol (outer:(array int)) (inner:(array int)) (w1:(matrix int))
  (w2:(matrix int)): Prop := exists row:int, ((0%:Z <= row)%Z /\
  (row < (size outer : int))%Z) /\ ((eq_rows outer inner w1 w2 row) /\
  exists col:int, ((0%:Z <= col)%Z /\ (col < ((width outer inner) row))%Z) /\
  ((forall (i:int), ((col < i)%Z /\ (i < ((width outer inner) row))%Z) ->
  ((matrix_get w1 (row, i)) = (matrix_get w2 (row, i)))) /\ ((matrix_get w1 (
  row, col)) < (matrix_get w2 (row, col)))%Z)).

Axiom frame_lt_sol : forall (outer:(array int)) (inner:(array int))
  (w1:(matrix int)) (w2:(matrix int)) (row:int) (idx:int), (frame outer inner
  w1 w2 row idx) -> (((0%:Z <= row)%Z /\ (row < (size outer : int))%Z) ->
  (((0%:Z <= idx)%Z /\ (idx < ((width outer inner) row))%Z) ->
  (((matrix_get w1 (row, idx)) < (matrix_get w2 (row, idx)))%Z -> (lt_sol
  outer inner w1 w2)))).

(* Why3 assumption *)
Definition eq_sol (outer:(array int)) (inner:(array int)) (w1:(matrix int))
  (w2:(matrix int)): Prop := (eq_rows outer inner w1 w2 (size outer : int)).

Axiom lt_not_eq : forall (outer:(array int)) (inner:(array int))
  (w1:(matrix int)) (w2:(matrix int)), (lt_sol outer inner w1 w2) ->
  ~ (eq_sol outer inner w1 w2).

Axiom solution : Type.

Parameter m2s: (matrix int) -> solution.

Parameter s2m: solution -> (matrix int).

Axiom m2s2m_def : forall (m:(matrix int)), ((s2m (m2s m)) = m).

(* Why3 assumption *)
Inductive solutions :=
  | mk_solutions : (int -> solution)%type -> int -> solutions.

(* Why3 assumption *)
Definition next (v:solutions): int :=
  match v with
  | (mk_solutions x x1) => x1
  end.

(* Why3 assumption *)
Definition sols (v:solutions): (int -> solution)%type :=
  match v with
  | (mk_solutions x x1) => x
  end.

(* Why3 assumption *)
Definition sorted (outer:(array int)) (inner:(array int)) (s:solutions)
  (lo:int) (hi:int): Prop := forall (i:int) (j:int), ((lo <= i)%Z /\
  ((i < j)%Z /\ (j < hi)%Z)) -> (lt_sol outer inner (s2m ((sols s) i))
  (s2m ((sols s) j))).

Axiom no_duplicate : forall (outer:(array int)) (inner:(array int))
  (s:solutions) (lo:int) (hi:int), (sorted outer inner s lo hi) ->
  forall (i:int) (j:int), ((lo <= i)%Z /\ ((i < j)%Z /\ (j < hi)%Z)) ->
  ~ (eq_sol outer inner (s2m ((sols s) i)) (s2m ((sols s) j))).

(* Why3 assumption *)
Definition good_solutions (outer:(array int)) (inner:(array int))
  (eval:(array int)) (s:solutions): Prop := (0%:Z <= (next s))%Z /\ (sorted
  outer inner s 0%:Z (next s)).

