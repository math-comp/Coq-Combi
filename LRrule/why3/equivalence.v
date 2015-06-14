
(*
   here we prove the equivalence between definitions from
   - the Coq proof (in directory ..), and
   - the Why3 proof (in file lrrule.mlw)
*)

Add LoadPath "..".
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
(* Require Import tuple finfun finset bigop path. *)
Require Import tools partition yama ordtype tableau std stdtab skewtab.

(* import definitions from Why3 *)
Require Import ssrint ssrwhy3.
Require spec.


Require Import ssralg ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
*)

Fixpoint convert_part (a : array int) : (seq nat) :=
  if a is i :: tl then
    match i with
      | Posz 0 => [::]
      | Posz n => n :: (convert_part tl)
      | _      => [::]
    end
  else [::].

Definition convert_part_inv (len : nat) (p : seq nat) : array int :=
  mkseq (fun i => (nth 0 p i):int) len. (* why3 partition are non-empty *)

Lemma size_convert_part (a : array int) :
  size (convert_part a) <= size a.
Proof.
  elim: a => [//= | a0 a IHa] /=.
  case: a0 => [] //= [] //= n.
Qed.

Lemma nth_getE (a : array int) x i :
  i < size (convert_part a) -> get a i = nth x (convert_part a) i.
Proof.
  elim: a i x => [//= | a0 a IHa] i /=.
  case: a0 => [] //= [] //= a0 x.
  case: i => [| i] //=.
  rewrite ltnS => /IHa; by apply.
Qed.

Lemma convert_part_impl (a : array int) :
  spec.is_part a -> is_part (convert_part a).
Proof.
  move=> H; apply/is_partP; split => [{H} |].
  - move: (X in last X.+1 _) => m.
    elim: a m => [| a0 a IHa] m //.
    by case: a0 => [] // [] // n.
  - move: H => [] Hlen [] Hdec Hlast i.
    case: (ltnP i.+1 (size (convert_part a))) => Hi.
    + rewrite -lez_nat -(nth_getE _ Hi) -nth_getE; last by apply: (leq_trans _ Hi).
      apply Hdec; repeat split => //.
      * by rewrite lez_nat.
      * rewrite ltz_nat; apply: (leq_trans Hi).
      by apply size_convert_part.
  - by rewrite nth_default.
Qed.

Lemma get_convert_part_inv len p (i : nat) :
  size p <= len -> get (convert_part_inv len p) i = nth 0 p i.
Proof.
  rewrite /get /convert_part_inv /length => Hlen.
  case: (ltnP i len) => Hi.
  - by rewrite nth_mkseq.
  - rewrite !nth_default => //.
    * exact (leq_trans Hlen Hi).
    * by rewrite size_mkseq.
Qed.

Lemma cond_ijl_int_nat (P : int -> int -> Prop) (l : nat) :
  (forall i j : int, (0 <= i)%R /\ (i <= j)%R /\ (j < l)%R -> P i j) <->
  (forall i j : nat,                i <= j /\     j < l    -> P (Posz i) (Posz j)).
Proof.
  split.
  + move=> H i j [] Hij Hj.
    apply H; by rewrite !lez_nat ltz_nat.
  + move=> H i j [].
    case: i => i // _ [].
    case: j => [j| [] //=].
    rewrite lez_nat ltz_nat => Hij Hj.
    by apply H.
Qed.

Lemma convert_part_inv_impl (p : seq nat) len :
  size p <= len -> 0 < len -> is_part p -> spec.is_part (convert_part_inv len p).
Proof.
  rewrite /spec.is_part /length cond_ijl_int_nat lez_nat size_mkseq.
  move=> Hsz Hlen /is_part_ijP [] Hlast H.
  repeat split; first by [].
  + move=> i j [] Hij Hj.
    do 2 (rewrite get_convert_part_inv; last by []).
    rewrite lez_nat; exact: H.
  + case: len Hlen Hsz => [//= | len] _ Hsize.
    by rewrite /= subn1 /= -/(get _ len) get_convert_part_inv.
Qed.

Lemma convert_partK (p : seq nat) len :
  size p <= len -> is_part p -> convert_part (convert_part_inv len p) = p.
Proof.
  rewrite /convert_part_inv.
  elim: p len => [| p0 p IHp] /= len Hsz.
    by case: len {Hsz} => [//| len].
  case: len Hsz => [//= | len].
  rewrite ltnS => /IHp {IHp}; rewrite /mkseq => Hrec /andP [] Hhead Hpart.
  rewrite /= -add1n iota_addl -map_comp.
  case: p0 Hhead.
    rewrite leqn0 => /part_head0F Habs; by rewrite Habs in Hpart.
  move=> n _; by rewrite -{2}(Hrec Hpart).
Qed.

Lemma convert_part_invK (a : array int) :
  spec.is_part a -> convert_part_inv (size a) (convert_part a) = a.
Proof.
  rewrite /spec.is_part /length cond_ijl_int_nat lez_nat /convert_part_inv.
  move=> [] _.
  elim: a => [//= | a0 a IHa] [] Hget Hlast.
  case: a0 Hget Hlast => [[|a0]| a0] H Hlast /=.
  - have {IHa Hlast H} H (j : nat) : j < size a -> get a j = 0.
      move=> Hj {IHa}.
      have /H /= Hlt : 0 <= j.+1 /\ j.+1 < size (Posz 0 :: a) by [].
      have /H /= : j.+1 <= size a /\ size a  < size (Posz 0 :: a) by [].
      move: Hlast; rewrite /= subn1 /= => /Num.Theory.ler_trans H1/H1{H1} Hgt.
      apply Num.Theory.ler_asym.
      by rewrite Hlt Hgt.
    rewrite /mkseq /= -add1n iota_addl -map_comp.
    congr (_ :: _).
    rewrite -{2}(mkseq_nth (0 : int) a).
    apply eq_map => i /=.
    case: (ltnP i (size a)) => [/H /= -> //= |] H1.
    by rewrite  nth_default.
  - rewrite /mkseq /= -[1]add1n iota_addl -map_comp -{3}IHa {IHa} //.
    split.
    + move=> i j {Hlast} Hij.
      have : i.+1 <= j.+1 /\ j.+1 < (size a).+1 by [].
      by apply H.
    + move: Hlast; rewrite /get /=.
      case: a {H} => [|a1 a] //=.
      by rewrite subn1.
  + exfalso.
    suff : 0 <= (size (Negz a0 :: a) - 1) /\
              (size (Negz a0 :: a) - 1) < size (Negz a0 :: a).
      by move=> /H /(Num.Theory.ler_trans Hlast).
    split; first by [].
    by rewrite /= subn1.
Qed.

Lemma convert_included_size (a b : array int) :
  spec.included a b -> size (convert_part a) <= size (convert_part b).
Proof.
  rewrite /spec.included /length.
  elim: a b => [| a0 a IHa] [|b0 b] [] //= /eqP.
  rewrite eqz_nat eqSS => /eqP Hsize.
  case: a0 => [] //= [] //= a0.
  case: b0 => [[|b0]|b0] H /=.
  - exfalso; by have /H : (0 <= 0%:Z)%R /\ (0%:Z < (size b).+1)%R by [].
  - rewrite ltnS; apply IHa.
    split; first by rewrite Hsize.
    case=> i [] //= _; rewrite ltz_nat => Hi.
    suff /H /= : (0 <= i.+1%:Z)%R /\ (i.+1%:Z < (size b).+1)%R by [].
    split; first by rewrite lez_nat.
    by rewrite ltz_nat ltnS.
  - exfalso; by have /H : (0 <= 0%:Z)%R /\ (0%:Z < (size b).+1)%R by [].
Qed.

Lemma convert_included_impl (a b : array int) :
  spec.included a b -> included (convert_part a) (convert_part b).
Proof.
  move=> H; have Hsize := (convert_included_size H).
  move: H; rewrite /spec.included /length => [] [] Hlen Hincl.
  apply/includedP; split; first exact Hsize.
  move=> i.
  case: (ltnP i (size (convert_part a))) => Hi.
  + rewrite -lez_nat -(nth_getE _ Hi) -nth_getE; last by apply (leq_trans Hi).
    apply Hincl; split; first by [].
    rewrite ltz_nat; apply (leq_trans Hi).
    apply (leq_trans (size_convert_part a)).
    by rewrite -lez_nat Hlen.
  + by rewrite nth_default.
Qed.
