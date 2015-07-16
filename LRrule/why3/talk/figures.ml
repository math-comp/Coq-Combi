
open Format
open Mlpost
open Metapost
open Command
open Picture
open Path
open Num
open Num.Infix
open Helpers
open Box
open Color

let pen = Pen.transform [Transform.scaled (bp 3.)] Pen.default

let tabular l =
  "\\begin{tabular}{c}" ^
    String.concat "\\\\\n" l ^
    "\\end{tabular}"

let rec listn n x = if n = 0 then [] else x :: listn (n-1) x

let red = rgb8 204 0 0
let thered = red
let lightgray = rgb8 243 243 243
let gray = rgb8 217 217 217
let darkgray = gray

let tbox = round_rect ~stroke:None ~fill:gray ~dy:zero
let tboxr = round_rect ~stroke:None ~fill:lightred ~dy:zero

let head = Arrow.head_classic ~color:red ~pen
let kind =
  Arrow.add_line ~color:red  ~pen (Arrow.add_head ~head Arrow.empty)
let arrow b ?ind ?outd x y =
  Arrow.box_to_box ~kind ?ind ?outd (sub x b) (sub y b) ~sep:(bp 5.)

let proof equiv =
  let alg = tex (tabular ["algebra"; "$c_{\\lambda,\\mu}^\\nu$"]) in
  let pgm = tex (tabular ["combinatorics"; "\\texttt{LRcoeff}"]) in
  let coq =
    let b = hbox ~padding:(bp 10.) ~pos:`Center
      [alg; tex "$\\Leftrightarrow$"; pgm] in
    tbox (vbox ~pos:`Left ~padding:(bp 10.)
            [tex "\\textcolor{thered}{Coq}"; b]) in
  let lrrule = tex (tabular ["\\texttt{let lrrule =}"; "\\dots"]) in
  let why3 =
    tbox (vbox ~pos:`Left ~padding:(bp 10.)
            [tex "\\textcolor{thered}{Why3}"; lrrule])
  in
  let b = hbox ~padding:(bp 30.) [coq; why3] in
  let ocaml1 = Box.place ~padding:(bp 30.) `South (sub pgm b) (tex "OCaml") in
  let ocaml2 =
    Box.place ~padding:(bp 30.) `South (sub lrrule b) (tex "OCaml") in
  let b = group [b; ocaml1; ocaml2] in
  let arrow ?ind ?outd x y =
    Arrow.box_to_box ~kind ?ind ?outd (sub x b) (sub y b) ~sep:(bp 5.) in
  draw b ++ arrow pgm ocaml1 ++ arrow lrrule ocaml2 ++
    (if equiv then arrow why3 coq else nop)

let () = Metapost.emit "proof" (proof false)
let () = Metapost.emit "proof_equiv" (proof true)

(*
Local Variables:
compile-command: "export TEXINPUTS=`pwd`: && mlpost -latex dummy.tex -native -pdf figures.ml"
End:
*)
