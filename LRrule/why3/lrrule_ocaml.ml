
(* manually-written OCaml code *)

type skew_shape = {
  outer: int array;
  inner: int array;
  end_of_row: int array;
  end_of_overlap: int array;
  below: int array;
}

let compute_end_of_row outer inner =
  let n = Array.length outer in
  let sums = Array.make n 0 in
  for i = 1 to n-1 do
    sums.(i) <- sums.(i-1) + outer.(i) - inner.(i)
  done;
  sums

let lrrule (sh: skew_shape) (eval: int array) : int =
  let n = sh.end_of_row.(Array.length sh.end_of_row - 1) in
  let szshape = Array.length sh.outer in (* = Array.length inner *)
  let szeval = Array.length eval in
  let innev = Array.make szeval 0 in
  let lastinnev = ref 0 in (* only zeros from this index *)
  let work = Array.make n 0 in
  (* row = current row
     idx = current index in work, from the start *)
  let rec count_rec row idx =
    if row = szshape then
      1 (* found a solution *)
    else if idx = sh.end_of_row.(row) then
      (* move from row [row-1] to row [row] *)
      count_rec (row + 1) idx
    else begin
      let min =
        if idx < sh.end_of_overlap.(row) then work.(idx - sh.below.(row)) + 1
        else 0 in
      let max =
        if idx = sh.end_of_row.(row-1) then !lastinnev
        else Pervasives.min !lastinnev work.(idx - 1) in
      let sum = ref 0 in
      for v = min to max do
        if innev.(v) < eval.(v) && (v = 0 || innev.(v-1) > innev.(v)) then begin
          innev.(v) <- innev.(v) + 1;
          if v = !lastinnev then incr lastinnev;
          work.(idx) <- v;
          sum := !sum + count_rec row (idx+1);
          innev.(v) <- innev.(v) - 1;
          if !lastinnev = v+1 && innev.(v) = 0 then decr lastinnev
        end
      done;
      !sum
    end
  in
  count_rec 1 0

let add_empty_row
  (outer: int array) (inner: int array) : (int array * int array) =
  let sz = Array.length outer in
  let n = outer.(0) in
  let out = Array.make (sz + 1) n in
  let inn = Array.make (sz + 1) n in
  for k = 1 to sz do
    out.(k) <- outer.(k - 1); inn.(k) <- inner.(k - 1)
  done;
  (out, inn)

let compute_skew_shape outer inner : skew_shape =
  let (outer, inner) = add_empty_row outer inner in
  let end_of_row = compute_end_of_row outer inner in
  let n = Array.length outer in
  let eoo = Array.make n 0 in
  let below = Array.make n 0 in
  for r = 1 to n-1 do
    below.(r) <- outer.(r) - inner.(r-1);
    eoo.(r) <- end_of_row.(r-1) + below.(r)
  done;
  { outer = outer; inner = inner; end_of_row = end_of_row;
    end_of_overlap = eoo; below = below }

let lrrule2 outer inner eval =
  let sh = compute_skew_shape outer inner in
  lrrule sh eval

(* variant using a matrix insteaf of a flat array work

     row = current row, in [0 .. length outer[
     idx = current index in row (from right to left), in [0 .. outer[0][

   ^  +-------------------+
   |  |_______|___        |
  row |  |________|___    |
   |  |    |__________|___|
   0  |_______|___________|
          <--   idx <--  0

*)

let lrrule_matrix outer inner eval =
  let szshape = Array.length outer in (* = Array.length inner *)
  let width = outer.(0) in
  let szeval = Array.length eval in
  let innev = Array.make szeval 0 in
  let lastinnev = ref 0 in (* only zeros from this index *)
  let work = Array.make_matrix szshape width 0 in
  let rec count_rec row idx =
    if row = szshape then
      1 (* found a solution *)
    else if idx = width - inner.(row) then
      (* move from row [row-1] to row [row] *)
      count_rec (row + 1)
	(if row + 1 < szshape then width - outer.(row + 1) else 0)
    else begin
      let min =
        if row > 0 && idx < width - inner.(row - 1)
	then work.(row - 1).(idx) + 1
        else 0 in
      let max =
        if idx = width - outer.(row) then !lastinnev
        else Pervasives.min !lastinnev work.(row).(idx - 1) in
      let sum = ref 0 in
      for v = min to max do
        if innev.(v) < eval.(v) && (v = 0 || innev.(v-1) > innev.(v)) then begin
          innev.(v) <- innev.(v) + 1;
          if v = !lastinnev then incr lastinnev;
          work.(row).(idx) <- v;
          sum := !sum + count_rec row (idx + 1);
          innev.(v) <- innev.(v) - 1;
          if !lastinnev = v+1 && innev.(v) = 0 then decr lastinnev
        end
      done;
      !sum
    end
  in
  count_rec 0 0

(* variant using a matrix insteaf of a flat array work

     row = current row, in [0 .. length outer[
     idx = current index in row (from left to left),
           in [0 .. outer[row]-inner[row][

   ^  +-------------------+
   |  |_______|___        |
  row |  |________|___    |
   |  |    |__________|___|
   0  |_______|___________|
               0 -> idx -->

*)

let lrrule_matrix2 outer inner eval =
  let szshape = Array.length outer in (* = Array.length inner *)
  let width = Array.mapi (fun r out -> out - inner.(r)) outer in
  let max_width = Array.fold_left max 0 width in
  let shift =
    Array.mapi (fun r inn -> if r = 0 then 0 else inner.(r-1) - inn) inner in
  let szeval = Array.length eval in
  let innev = Array.make szeval 0 in
  let lastinnev = ref 0 in (* only zeros from this index *)
  let work = Array.make_matrix szshape max_width 0 in
  let rec count_rec row idx =
    if row = szshape then
      1 (* found a solution *)
    else if idx < 0 then
      (* move from row [row-1] to row [row] *)
      count_rec (row + 1) (if row + 1 < szshape then width.(row + 1) - 1 else 0)
    else begin
      let min =
	if row > 0 && idx >= shift.(row)
	then work.(row - 1).(idx - shift.(row)) + 1 else 0 in
      let max =
        if idx = width.(row) - 1 then !lastinnev
        else Pervasives.min !lastinnev work.(row).(idx + 1) in
      let sum = ref 0 in
      for v = min to max do
        if innev.(v) < eval.(v) && (v = 0 || innev.(v-1) > innev.(v)) then begin
          innev.(v) <- innev.(v) + 1;
          if v = !lastinnev then incr lastinnev;
          work.(row).(idx) <- v;
          sum := !sum + count_rec row (idx - 1);
          innev.(v) <- innev.(v) - 1;
          if !lastinnev = v+1 && innev.(v) = 0 then decr lastinnev
        end
      done;
      !sum
    end
  in
  count_rec 0 (width.(0) - 1)

(* tests *)

let test_lrrule lrrule =
  assert (lrrule [| 3; 2; 1 |] [| 2; 1; 0 |] [| 2; 1; 0 |] = 2);
  assert (lrrule [| 5; 4; 1 |] [| 3; 1; 0 |] [| 3; 2; 1; 0 |] = 1);
  assert (lrrule [| 5; 4; 3; 2 |] [| 3; 3; 1; 0 |] [| 4; 2; 1; 0 |] = 3);
  assert (lrrule
            [|11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1 |]
            [| 7;  6; 5; 5; 4; 3; 2; 1; 0; 0; 0 |]
            [| 7;  6; 5; 5; 4; 3; 2; 1; 0       |] = 268484)

let () = test_lrrule lrrule2
let () = test_lrrule lrrule_matrix
let () = test_lrrule lrrule_matrix2
let () = exit 0

open List

let cut_list cut l =
  let rec loop = function
    | [] -> [], []
    | l :: t ->
	let ct, res = loop t
	in if l = cut then ([], ct :: res)
	  else (l :: ct), res
  in let res0, res = loop l
  in res0 :: res

let [outer; inner; eval] =
  map
    (fun l -> Array.of_list (map int_of_string l))
    (cut_list "-" (tl (Array.to_list Sys.argv)))

let () =
  Format.printf "%d@." (lrrule_matrix2 outer inner eval)

(*
  Local Variables:
  compile-command: "make lrrule_ocaml.opt && time ./lrrule_ocaml.opt"
  End:
*)
