
open Format

let () = Random.self_init ()

let random_partition n =
  let rec build acc m n = (* partition of n in parts at most m *)
    if n = 0 then List.rev acc else
      let m = min m n in
      let p = 1 + Random.int m in
      build (p :: acc) p (n - p) in
  Array.of_list (build [] n n)

let rows = int_of_string Sys.argv.(1)

let inner = Array.init rows (fun _ -> Random.int 3)
let () = for i = rows - 2 downto 0 do inner.(i) <- inner.(i) + inner.(i+1) done

let outer = Array.make rows 0
let () = outer.(rows-1) <- inner.(rows-1) + Random.int 3
let () = for i = rows - 2 downto 0 do
    outer.(i) <- Random.int 3 + max inner.(i) outer.(i+1) done

let n = ref 0
let () = Array.iteri (fun i out -> n := !n + out - inner.(i)) outer
let eval = random_partition !n

let cmd exec =
  let b = Buffer.create 1024 in
  let fmt = formatter_of_buffer b in
  fprintf fmt "%s " exec;
  for i = 0 to rows-1 do fprintf fmt "%d " outer.(i) done;
  fprintf fmt "- ";
  for i = 0 to rows-1 do fprintf fmt "%d " inner.(i) done;
  fprintf fmt "- ";
  Array.iter (fun p -> fprintf fmt "%d " p) eval;
  fprintf fmt "0@?";
  let s = Buffer.contents b in
  s

let () =
  printf "%s@." (cmd "");
  ignore (Sys.command (cmd "time ./lrrule64.opt"));
  ignore (Sys.command (cmd "time lrcoef"));
  ()







