(* ocamlopt lrcoeff.cmx coeff.ml -o coeff *)

(*
Note : the result is computed with Unary integer !!!!

  
time ./lrcoef 11 10 9 8 7 6 5 4 3 2 1 - 7 6 5 5 4 3 2 1 - 7 6 5 5 4 3 2 1
268484
./lrcoef 11 10 9 8 7 6 5 4 3 2 1 - 7 6 5 5 4 3 2 1 - 7 6 5 5 4 3 2 1  0.14s user 0.00s system 99% cpu 0.143 total

time ./coeff
268484
./coeff  1.20s user 0.01s system 100% cpu 1.214 total
*)

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

let  [p; p1; p2] =
  map
    (map int_of_string)
    (cut_list "-" (tl (Array.to_list Sys.argv)))

open Lrcoeff

let natint n =
  let rec loop res =
    function | 0 -> res | n -> loop (S res) (n - 1)
  in loop O n;;

let intnat n =
  let rec loop res =
    function | O -> res | S n -> loop (res + 1) n
  in loop 0 n;;

print_int (
  intnat (lRcoeff (map natint p1) (map natint p2) (map natint p))
);;
print_newline ();;

