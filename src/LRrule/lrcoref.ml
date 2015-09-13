let rec subn = (fun m n -> if n > m then 0 else m - n )
let minn m n = if m <= n then m else n

open List

let size = length

(** val head : 'a1 -> 'a1 list -> 'a1 **)

let head x0 = function
| [] -> x0
| x::l -> x

(** val behead : 'a1 list -> 'a1 list **)

let behead = function
| [] -> []
| t::s' -> s'

(** val ncons : int -> 'a1 -> 'a1 list -> 'a1 list **)

let rec ncons n x l = match n with | 0 -> l | n -> ncons (n-1) x (x::l)


(** val nth : 'a1 -> 'a1 list -> int -> 'a1 **)

let rec nth x0 s n =
  match s with
  | [] -> x0
  | x::s' ->
    ((fun zero succ n ->
      if n=0 then zero () else succ (n-1))
       (fun _ ->
       x)
       (fun n' ->
       nth x0 s' n')
       n)

(** val filter : 'a1 pred0 -> 'a1 list -> 'a1 list **)

let rec filter a = function
| [] -> []
| x::s' -> if a x then x::(filter a s') else filter a s'

(** val take : int -> 'a1 list -> 'a1 list **)

let rec take n = function
| [] -> []
| x::s' ->
    if n = 0 then []
    else x::(take (n - 1) s')

(** val incr_nth : int list -> int -> int list **)

let rec incr_nth v i =
  match v with
  | [] -> ncons i 0 (1::[])
  | n::v' ->
      if i = 0 then (n + 1)::v'
      else n::(incr_nth v' (i -1))

(** val iota : int -> int -> int list **)

let rec iota m =
  function | 0 -> [] | n -> m::(iota (m+1) (n-1))


(** val is_in_corner : int list -> Equality.sort simpl_pred **)

let is_in_corner sh i =
  if i = 0
  then true
  else (nth 0 sh i) + 1 <= (nth 0 sh (i - 1))


(** val choose_one_letter :
    int list -> int list -> int -> int -> Equality.sort list **)

let choose_one_letter outev innev mini maxi =
  filter (fun i ->
    if is_in_corner innev i
    then (nth 0 innev i) < (nth 0 outev i)
    else false)
    (iota mini (((minn (size innev) maxi) + 1) - mini))

(** val yamtab_row :
    int list -> int list -> int list -> (int list*int list) list **)

let rec yamtab_row outev innev = function
| [] -> ([],innev)::[]
| r0::tlr ->
  flatten
    (map (fun res ->
      map (fun i -> (i::(fst res)),(incr_nth (snd res) i))
        (choose_one_letter outev (snd res) (r0+1)
          (head (size innev) (fst res)))) (yamtab_row outev innev tlr))

(** val yamtab_shift :
    int list -> int list -> int -> int -> int list -> (int list*int list)
    list **)

let rec yamtab_shift outev innev maxi sh sol =
  if sh = 0 then [(sol,innev)]
  else
    flatten
      (map (fun res ->
        map (fun i ->
          (i::(fst res)),(incr_nth (snd res) i))
          (choose_one_letter outev (snd res) 0 (head maxi (fst res))))
        (yamtab_shift outev innev maxi (sh - 1) sol))


(** val lRyamtab_list_rec :
    int list -> int list -> int list -> int list -> int -> int list -> int
    list list list **)

let rec lRyamtab_list_rec outev innev inner outer sh0 row0 =
  match outer with
  | [] -> []::[]
  | out0::out ->
    let inn0 = head 0 inner in
    let inn = behead inner in
    let rowres = yamtab_row outev innev (take (subn out0 sh0) row0) in
    let rows =
      flatten
        (map (fun res ->
          yamtab_shift outev (snd res) (head (size innev) (fst res))
            (subn (minn sh0 out0) inn0) (fst res)) rowres)
    in
    flatten
      (map (fun row ->
        map (fun tab -> (fst row)::tab)
          (lRyamtab_list_rec outev (snd row) inn out inn0 (fst row))) rows)

(** val lRyamtab_count_rec :
    int list -> int list -> int list -> int list -> int -> int list -> int **)

let lRyamtab_count_rec =
  let tsumn = fold_left (+) 0 in
  (fun outev ->
  let rec lRyamtab_count_rec0 innev inner outer sh0 row0 =
    match outer with
    | [] -> 1
    | out0::out ->
      let inn0 = head 0 inner in
      let inn = behead inner in
      let rowres = yamtab_row outev innev (take (subn out0 sh0) row0) in
      tsumn
        (map (fun res ->
          tsumn
            (map (fun row ->
              lRyamtab_count_rec0 (snd row) inn out inn0 (fst row))
              (yamtab_shift outev (snd res) (head (size innev) (fst res))
                (subn (minn sh0 out0) inn0) (fst res)))) rowres)
  in lRyamtab_count_rec0)

(** val lRyamtab_list :
    int list -> int list -> int list -> int list list list **)

let lRyamtab_list inner eval outer =
  lRyamtab_list_rec eval [] inner outer (head 1 outer) []

(** val lRcoeff : int list -> int list -> int list -> int **)

let lRcoeff inner eval outer =
  lRyamtab_count_rec eval [] inner outer (head 1 outer) []

