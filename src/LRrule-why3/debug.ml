
open Why3extract
open Format

let print fmt x = Format.fprintf fmt "%s" (Why3__BigInt.to_string x)

let print_array fmt a =
  fprintf fmt "@[[";
  Array.iter (fun x -> fprintf fmt "%a " print x) a;
  fprintf fmt "]@]"

