
open Why3extract
open Lrrule__LRruleMatrix

(*
time ./test_lrrule 11 10 9 8 7 6 5 4 3 2 1 - 7 6 5 5 4 3 2 1 - 7 6 5 5 4 3 2 1
268484
./test_lrrule 11 10 9 8 7 6 5 4 3 2 1 - 7 6 5 5 4 3 2 1 - 7 6 5 5 4 3 2 1  0.14s user 0.00s system 99% cpu 0.143 total

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

let [outer; inner; eval] =
  map
    (fun l -> Array.of_list (map Why3__BigInt.of_string l))
    (cut_list "-" (tl (Array.to_list Sys.argv)))

let () =
  Format.printf "%s@."
    (Why3__BigInt.to_string (lrrule outer inner eval))
