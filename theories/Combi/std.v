(** * Combi.Combi.std : Standard Words, i.e. Permutation as Words *)
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
(** Standard words : words wich are permutations of [0, 1, ..., n-1]:

- [is_std s] == s is a standard word
- [is_std_of_n n s] == s is a standard word of size n
- [wordperm p] == the standard word associated with a permutation [p] of ['S_n]

Sigma types for standard word

- [stdwordn n] == a type for [seq nat] which standard words size n;
                  it is canonically a [finType]

Inversions and standardisation of a word over a totally ordered alphabet

- [std s] == given a word w over an [ordType] returns the standard word with
             the same set of inversion (lemmas [stdP] and [std_eq_invP])
- [versions w i j] == i j is an non-inversion of w that is
                        <<i <= j < size w and w_i <= w_j>>

- [eq_inv w1 w2] == w1 and w2 have the same versions which is equivalent
                    to the same set of inversions; in particular w1 and w2
                    have the same size.
The main result here is [std_eq_invP] which says that having the same inversions
is the same as having the same standardized.

- [linvseq s t] == t is the left inverse of s
- [invseq s t] == s and t are inverse on of each other
- [invstd w] == the inverse of the standardized of w that is the permutation
                which sorts w in a stable way.

*****)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
From mathcomp Require Import finset perm fingroup path.

From Combi Require Import tools combclass ordtype permuted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import OrdNotations.

Open Scope nat_scope.


(** * Standard words *)
Section StandardWords.

Implicit Type n : nat.
Definition is_std (s : seq nat) := perm_eq s (iota 0 (size s)).

Lemma perm_eq_std u v : is_std u -> perm_eq v u -> is_std v.
Proof.
  rewrite /is_std => Hperm Heq.
  rewrite (perm_eq_size Heq); exact: (perm_eq_trans Heq Hperm).
Qed.

Lemma std_perm_eq u v : is_std u -> is_std v -> size u = size v -> perm_eq v u.
Proof.
  rewrite /is_std => Hperm Heq Hsize.
  rewrite Hsize perm_eq_sym in Hperm.
  exact: (perm_eq_trans Heq Hperm).
Qed.

Lemma mem_std p i : is_std p -> (i \in p) = (i < size p).
Proof. rewrite /is_std => /perm_eq_mem ->; by rewrite mem_iota /= add0n. Qed.

Lemma std_uniq u : is_std u -> uniq u.
Proof. rewrite /is_std => /perm_eq_uniq ->. exact: iota_uniq. Qed.

Lemma std_max s0 s : is_std (s0 :: s) -> maxL s0 s = size s.
Proof. rewrite /is_std => /= /maxL_perm_eq /= ->. by rewrite maxL_iota_n. Qed.

Lemma is_stdP s : reflect (forall n, n < size s -> n \in s) (is_std s).
Proof.
  rewrite /is_std; apply (iffP idP).
  - move=> Hperm n Hn; by rewrite (perm_eq_mem Hperm) mem_iota add0n Hn.
  - move=> H.
    have Hsubs : {subset iota 0 (size s) <= s}.
      move=> n; rewrite mem_iota /= add0n; exact: H.
    have Hsz : size s <= size (iota 0 (size s)) by rewrite size_iota.
    have:= leq_size_perm (iota_uniq _ _) Hsubs Hsz => [] [] Hs _.
    have Huniq:= leq_size_uniq (iota_uniq _ _) Hsubs Hsz.
    apply (uniq_perm_eq Huniq (iota_uniq _ _)).
    move => i; by rewrite Hs.
Qed.

Definition wordperm n (p : 'S_n) := [seq val (p i) | i <- enum 'I_n].

Open Scope group_scope.

Lemma wordperm_iota n (p : 'S_n) : (wordperm p) =i iota 0 n.
Proof.
  move=> i; rewrite mem_iota add0n /=.
  apply/idP/idP.
  - move/mapP => [] j _ -> /=; exact: ltn_ord.
  - move=> Hi; apply/mapP; exists ((p^-1) (Ordinal Hi)).
    + by rewrite mem_enum.
    + by rewrite permKV.
Qed.

Lemma uniq_wordperm n (p : 'S_n) : uniq (wordperm p).
Proof.
  rewrite (perm_uniq (wordperm_iota _)); first exact: (iota_uniq 0 n).
  by rewrite size_map size_enum_ord size_iota.
Qed.

Lemma wordperm_std n (p : 'S_n) : is_std (wordperm p).
Proof.
  rewrite /is_std size_map size_enum_ord.
  apply: uniq_perm_eq.
  - exact: uniq_wordperm.
  - exact: iota_uniq.
  - exact: wordperm_iota.
Qed.

Lemma perm_of_std s : is_std s -> { p : 'S_(size s) | s = wordperm p }.
Proof.
  rewrite /is_std => H.
  pose fpn := fun i : 'I_(size s) => nth 0 s i.
  have Hfpi i : fpn i < size s.
    have:= mem_nth 0 (ltn_ord i).
    by rewrite (perm_eq_mem H) mem_iota /= add0n.
  pose fp := finfun (fun i : 'I_(size s) => Ordinal (Hfpi i)).
  have Hfp : injective fp.
    move=> i j; rewrite /fp /= !ffunE => Heq; apply/eqP.
    move: Heq => /(congr1 val)/eqP /=.
    rewrite /fpn (nth_uniq _ (ltn_ord _) (ltn_ord _)) //=.
    exact: std_uniq.
  exists (perm Hfp); rewrite /wordperm /=.
  apply: (@eq_from_nth _ 0); first by rewrite size_map size_enum_ord.
  move=> i Hi; rewrite (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
  rewrite -{3}[i]/(val (Ordinal Hi)).
  by rewrite nth_ord_enum /= permE /fp /= ffunE /= /fpn /=.
Qed.

Lemma is_std_wordpermP s :
  reflect (exists p : 'S_(size s), s = wordperm p) (is_std s).
Proof.
  apply: (iffP idP).
  + move/perm_of_std => [] p Hp; by exists p.
  + move=> [] p ->; exact: wordperm_std.
Qed.

Lemma wordperm_invP n (p : 'S_n) i (j : 'I_n) :
  nth n (wordperm p) i = j <-> i = (p^-1) j.
Proof.
  split; rewrite /wordperm.
  - case (ltnP i n) => Hi.
    + rewrite (nth_map j); last by rewrite size_enum_ord.
      rewrite /= => /val_inj <-.
      by rewrite permK nth_enum_ord.
    + rewrite nth_default; last by rewrite size_map size_enum_ord.
      move=> Hn; exfalso; have:= ltn_ord j; by rewrite -{1}Hn ltnn.
  - move ->; rewrite (nth_map j); last by rewrite size_enum_ord; apply: ltn_ord.
    by rewrite nth_ord_enum /= permKV.
Qed.

End StandardWords.


(** * Standard words as a [finType] *)
Section StdCombClass.

Variable n : nat.

Definition is_std_of_n := [pred w | (is_std w) && (size w == n) ].

Structure stdwordn : Set :=
  StdWordN {stdwordnval :> seq nat; _ : is_std_of_n stdwordnval}.
Canonical stdwordn_subType := Eval hnf in [subType for stdwordnval].
Definition stdwordn_eqMixin := Eval hnf in [eqMixin of stdwordn by <:].
Canonical stdwordn_eqType := Eval hnf in EqType stdwordn stdwordn_eqMixin.
Definition stdwordn_choiceMixin := Eval hnf in [choiceMixin of stdwordn by <:].
Canonical stdwordn_choiceType := Eval hnf in ChoiceType stdwordn stdwordn_choiceMixin.
Definition stdwordn_countMixin := Eval hnf in [countMixin of stdwordn by <:].
Canonical stdwordn_countType := Eval hnf in CountType stdwordn stdwordn_countMixin.
Canonical stdwordnn_subCountType := Eval hnf in [subCountType of stdwordn].

Lemma stdwordnP (s : stdwordn) : is_std (val s).
Proof. by case: s => s /= /andP []. Qed.

Lemma size_sdtn (s : stdwordn) : size (val s) = n.
Proof. by case: s => s /= /andP [] _ /eqP. Qed.

Definition enum_stdwordn := [seq wordperm p | p <- enum 'S_n].

Lemma enum_stdwordnE : enum_stdwordn =i is_std_of_n.
(* (is_std_of_n s) = (s \in enum_stdwordn). *)
Proof.
  move=> s; apply/idP/idP.
  + move/mapP => [] p _ -> /=.
    by rewrite unfold_in /= wordperm_std /= size_map size_enum_ord.
  + move=> /andP [] /is_std_wordpermP [] p Hstd /eqP Hsize.
    apply/mapP; rewrite -Hsize; exists p; last exact Hstd.
    by rewrite mem_enum.
Qed.

Lemma wordperm_inj : injective (@wordperm n).
Proof.
  move=> p q; rewrite /wordperm => Heq.
  rewrite -permP => i; have:= congr1 (fun s => nth 0 s i) Heq.
  have Hi : i < size (enum 'I_n) by rewrite size_enum_ord; apply: ltn_ord.
  rewrite /= !(nth_map i _ _ Hi).
  rewrite nth_ord_enum; exact: val_inj.
Qed.

Lemma enum_stdwordn_uniq : uniq enum_stdwordn.
Proof. rewrite/enum_stdwordn (map_inj_uniq wordperm_inj). exact: enum_uniq. Qed.

Canonical stdwordn_finMixin :=
  Eval hnf in sub_uniq_finMixin stdwordnn_subCountType enum_stdwordn_uniq enum_stdwordnE.
Canonical stdwordn_finType := Eval hnf in FinType stdwordn stdwordn_finMixin.

Lemma card_stdwordn : #|{:stdwordn}| = n`!.
Proof. by rewrite card_sub_uniqE size_map -card_Sn cardE. Qed.

End StdCombClass.


(** * Standardisation of a word over a totally ordered alphabet *)
Section Standardisation.

Variable Alph : ordType.
Implicit Type s u v w : seq Alph.

Fixpoint std_rec n s :=
  if n is n'.+1 then
    let rec := std_rec n' (rembig s) in
    let pos := posbig s in
    take pos rec ++ n' :: drop pos rec
  else [::].
Definition std s := std_rec (size s) s.

Lemma size_std_rec n s : size (std_rec n s) = n.
Proof.
  elim: n s => [//= | n IHn] s /=.
  by rewrite size_cat /= addnS -size_cat cat_take_drop IHn.
Qed.

Lemma size_std s : size (std s) = size s.
Proof. exact: size_std_rec. Qed.

Lemma std_is_std s : is_std (std s).
Proof.
  rewrite /is_std /std size_std_rec perm_eq_sym.
  move Hn : (size s) => n; elim: n s Hn => [//= | n IHn] s Hn.
  apply: (@perm_eq_trans _ (n :: (iota 0 n))).
    rewrite -addn1 iota_add /= add0n -cat1s; apply/perm_eqlP; exact: perm_catC.
  apply: (@perm_eq_trans _ (n :: std_rec n (rembig s))).
    rewrite perm_cons; apply: IHn; by rewrite size_rembig Hn.
  rewrite {IHn Hn} /= -[n :: drop _ _]cat1s catA.
  move: (std_rec n (rembig s)) => l.
  rewrite -{1}[l](cat_take_drop (posbig s)) -cat1s -catA.
  by apply/perm_eqlP; apply: perm_catCA.
Qed.

Lemma in_std_ltn_size s i : i \in std s = (i < size s).
Proof. by rewrite (mem_std _ (std_is_std s)) size_std_rec. Qed.

Lemma allLtn_std_rec s : allLtn (std s) (size s).
Proof. apply/allP=> i /=; by rewrite ltnXnatE in_std_ltn_size. Qed.

Lemma rembig_ins_std s pos :
  rembig (take pos (std s) ++ size s :: drop pos (std s)) = std s.
Proof.
  apply: esym; apply/eqP/rembigP; first by case: (take _ _).
  have:= allLtn_std_rec s.
  rewrite -{1}[std s](cat_take_drop pos) allLtn_catE => /andP [].
  set ll := take _ _; set lr := drop _ _ => /allLtnW Hll Hlr.
  exists ll, (size s), lr; by split; first by rewrite cat_take_drop.
Qed.

Lemma std_rembig s : std (rembig s) = rembig (std s).
Proof.
  rewrite /std.
  elim: s => [//= | s0 s IHs] /=.
  case (boolP (allLtn s s0)) => [_ | Hmax].
  + case H : (std_rec (size s) s) => [//= | t0 t].
    by rewrite -H rembig_ins_std.
  + case H : s IHs Hmax => [//= |s1 s']; rewrite -H => IHs Hmax.
    have <- : size (s0 :: rembig s) = size s by rewrite /= size_rembig H.
    have:= rembig_ins_std; by rewrite /std => ->.
Qed.

Lemma std_posbig s : posbig (std s) = posbig s.
Proof.
  rewrite /std.
  case: s => [//= | s0 s] /=.
  case (boolP (allLtn s s0)) => [/= | Hmax] /=;
    first by rewrite take0 drop0 cat0s /= allLtn_std_rec.
  set pos := (posbig s).+1; set LR := take _ _.
  have HposLR : pos = size LR.
    rewrite /LR size_take /pos size_std_rec.
    case: (ltnP (posbig s).+1 (size s)) => Hpos; first by [].
    apply/eqP; rewrite eqn_leq Hpos andbT.
    have: s != [::] by move: Hmax; case s.
    exact: posbig_size.
  rewrite HposLR; apply/eqP; rewrite -posbigE.
  have:= allLtn_std_rec (s0 :: rembig s).
  rewrite size_take size_std_rec HposLR.
  have Hif : (if size LR < size s then size LR else size s) = size LR.
    rewrite /LR /pos size_take size_std_rec.
    case: (ltnP (posbig s).+1 (size s)) => Hpos; first by rewrite Hpos.
    by rewrite ltnn.
  rewrite /LR size_take size_std_rec HposLR !Hif /std.
  have -> : size (s0 :: rembig s) = size s.
    rewrite /= size_rembig; move: Hmax; by case s.
  rewrite -{1}[std_rec _ _](cat_take_drop (size LR)) allLtn_catE => /andP [] H1 ->.
  rewrite andbT; exact: allLtnW.
Qed.

End Standardisation.

Lemma std_std s : is_std s -> std s = s.
Proof.
  rewrite /std /is_std.
  move Hn : (size s) => n; elim: n s Hn => [/= | n IHn] s Hsz.
  + by move: Hsz=> /eqP/nilP ->.
  + case Hs : s Hsz => [//= | s0 s'].
    rewrite -{2 3 4}Hs => Hsz Hperm /=.
    have Hszrem : size (rembig s) = n by rewrite size_rembig Hs Hsz.
    have Hprem : perm_eq (rembig s) (iota 0 n).
      rewrite -rembig_iota; exact: perm_eq_rembig.
    rewrite (IHn _ Hszrem Hprem) Hs {IHn}.
    have:= Hperm; rewrite {1}Hs => /maxL_perm_eq.
    rewrite maxL_iota_n => <-.
    exact: posbig_take_dropE.
Qed.

Lemma std_stdE (T : ordType) (s : seq T) : std (std s) = std s.
Proof. apply: std_std; exact: std_is_std. Qed.

(** ** Inversion sets and standardization *)
Section Spec.

Implicit Type S T : inhOrdType.

Definition versions T (w : seq T) : rel nat :=
  fun i j => (i <= j < size w) && (nth (inhabitant T) w i <=A nth (inhabitant T) w j).

Definition eq_inv T1 T2 (w1 : seq T1) (w2 : seq T2) :=
  ((versions w1) =2 (versions w2)).

Lemma eq_inv_refl T (w : seq T) : eq_inv w w.
Proof. by []. Qed.

Lemma eq_inv_nil T1 T2 : eq_inv (@nil T1) (@nil T2).
Proof.
  rewrite /eq_inv /versions => i j /=.
  by rewrite ltn0 andbF.
Qed.

Lemma eq_inv_sym T1 T2 (w1 : seq T1) (w2 : seq T2) :
  eq_inv w1 w2 -> eq_inv w2 w1.
Proof. rewrite /versions => Hinv i j; move/(_ i j) : Hinv; exact esym. Qed.

Lemma eq_inv_trans T1 T2 T3 (w1 : seq T1) (w2 : seq T2) (w3 : seq T3) :
  eq_inv w1 w2 -> eq_inv w2 w3 -> eq_inv w1 w3.
Proof.
  rewrite /versions => H12 H23 i j.
  exact (etrans (H12 i j) (H23 i j)).
Qed.

Lemma eq_inv_size T1 T2 (w1 : seq T1) (w2 : seq T2) :
  eq_inv w1 w2 -> size w1 = size w2.
Proof.
  move=> Hinv.
  wlog suff Hwlog : T1 T2 w1 w2 Hinv / size w1 <= size w2.
    by apply anti_leq; rewrite !Hwlog.
  rewrite /eq_inv /versions in Hinv.
  case H : (size w1) => [//= | n].
  move/(_ n n) : Hinv; rewrite H leqnn ltnSn leqXnn /=.
  by move/eqP/andP => [].
Qed.

Lemma eq_invP  T1 T2 (w1 : seq T1) (w2 : seq T2) :
  (size w1 = size w2 /\
   forall i j, i <= j < size w1 ->
               (nth (inhabitant T1) w1 i <=A nth (inhabitant T1) w1 j) =
               (nth (inhabitant T2) w2 i <=A nth (inhabitant T2) w2 j))
    <-> (eq_inv w1 w2).
Proof.
  split.
  - rewrite /eq_inv /versions; move=> [] Hsz H i j /=.
    apply/idP/idP => /andP [] Hij Hnth.
    + by rewrite -(H _ _ Hij) -Hsz Hij.
    + by rewrite H Hsz Hij.
  - move=> H; have Hsz:= eq_inv_size H; split; first exact Hsz.
    move=> i j Hij.
    move: H; rewrite /eq_inv /versions -Hsz => /(_ i j); by rewrite Hij.
Qed.

Lemma eq_inv_inversionP  T1 T2 (w1 : seq T1) (w2 : seq T2) :
  (size w1 = size w2 /\
   forall i j, i <= j < size w1 ->
               (nth (inhabitant T1) w1 i >A nth (inhabitant T1) w1 j) =
               (nth (inhabitant T2) w2 i >A nth (inhabitant T2) w2 j))
    <-> (eq_inv w1 w2).
Proof.
  rewrite -eq_invP; split => [] [] Hsz H; split; try exact Hsz.
  - move=> i j Hij; rewrite !leqXNgtnX; by rewrite H.
  - move=> i j Hij; rewrite !ltnXNgeqX; by rewrite H.
Qed.

Lemma eq_inv_consK T1 T2 (a : T1) u (b : T2) v :
  eq_inv (a :: u) (b :: v) -> eq_inv u v.
Proof.
  rewrite /eq_inv /versions => H i j.
  move/(_ i.+1 j.+1) : H; by rewrite !ltnS.
Qed.

Lemma eq_inv_rconsK T1 T2 (a : T1) u (b : T2) v :
  eq_inv (rcons u a) (rcons v b) -> eq_inv u v.
Proof.
  rewrite -!eq_invP !size_rcons => [] [] Hsz H.
  move: Hsz => /eqP; rewrite eqSS => /eqP Hsz; rewrite Hsz; rewrite Hsz in H.
  split; first by [].
  move=> i j Hij.
  move: Hij => /andP [] Hi Hj.
  have {H}/H : i <= j < (size v).+1.
    rewrite Hi /=; exact: (ltn_trans Hj).
  by rewrite !nth_rcons Hsz Hj (leq_ltn_trans Hi Hj).
Qed.

Lemma eq_inv_allgtnXimply S T (a : S) u (b : T) v :
  eq_inv (a :: u) (b :: v) -> (allLtn u a) -> (allLtn v b).
Proof.
  move=> H; have:= eq_inv_size H.
  move: H; rewrite /eq_inv /versions => H /= /eqP; rewrite eqSS => /eqP Hsz.
  move/(all_nthP (inhabitant S)) => Hall; apply/(all_nthP (inhabitant T)).
  rewrite -Hsz => i Hi; move/(_ i Hi) : Hall => Hleq.
  move/(_ 0 i.+1) : H => /=.
  move: Hi; rewrite -Hsz -ltnS => -> /=.
  rewrite ltnXNgeqX => <-; by rewrite -ltnXNgeqX.
Qed.

Lemma eq_inv_allgtnX S T (a : S) u (b : T) v :
  eq_inv (a :: u) (b :: v) -> (allLtn u a) = (allLtn v b).
Proof.
  move=> H1; have H2 := eq_inv_sym H1.
  apply/idP/idP; exact: eq_inv_allgtnXimply.
Qed.

Lemma eq_inv_posbig S T (u : seq S) (v : seq T) :
  eq_inv u v -> posbig u = posbig v.
Proof.
  move=> H; have /eqP := eq_inv_size H.
  elim: u v H => [| a u IHu] /= v.
    by move=> _; rewrite eq_sym => /nilP ->.
  case: v => [//= |b v] /= Heq.
  rewrite eqSS => Hsize; move/(_ v (eq_inv_consK Heq) Hsize) : IHu => Hpos.
  have:= Heq; rewrite /eq_inv /versions => Hinv.
  rewrite -(eq_inv_allgtnX Heq).
  by case: (allLtn u a); last by rewrite Hpos.
Qed.

Lemma eq_inv_rembig S T (u : seq S) (v : seq T) :
  eq_inv u v -> eq_inv (rembig u) (rembig v).
Proof.
  move => Hinv; have Heqpos:= eq_inv_posbig Hinv.
  have:= Hinv; rewrite -!eq_invP => [] [] Hsz Heq.
  rewrite !size_rembig -Hsz; split => //= i j /andP [] Hij Hj.
  rewrite -!nth_rembig /shift_pos -Heqpos.
  case (ltnP i (posbig u)) => Hipos;
    case (ltnP j (posbig u)) => Hjpos; apply: Heq.
  - rewrite Hij /=; apply: (ltn_trans Hj).
    move: Hj; by case: (size u).
  - rewrite (leq_trans Hij (leqnSn _)) /=.
    suff -> : (size u) = (size u).-1.+1 by rewrite ltnS.
    by move: Hj; rewrite -ltnS; case: (size u).
  - exfalso; have:= leq_trans (leq_trans Hjpos Hipos) Hij; by rewrite ltnn.
  - rewrite ltnS Hij /=.
    suff -> : (size u) = (size u).-1.+1 by rewrite ltnS.
    by move: Hj; rewrite -ltnS; case: (size u).
Qed.

Lemma std_eq_inv S T (u : seq S) (v : seq T) :
  eq_inv u v -> std u = std v.
Proof.
  move => Hinv; move Hn : (size u) => n.
  elim: n u v Hn Hinv => [//= | n IHn] u v Hn Hinv.
    have:= eq_inv_size Hinv.
    rewrite Hn => /esym/eqP/nilP ->.
    by move: Hn => /eqP/nilP ->.
  have Hsz := eq_inv_size Hinv.
  have Hszremu : size (rembig u) = n by rewrite size_rembig Hn.
  have Hszremv : size (rembig v) = n by rewrite size_rembig -Hsz Hn.
  move/(_ (rembig u) (rembig v) Hszremu (eq_inv_rembig Hinv)) : IHn.
  rewrite /std -Hsz Hn Hszremu Hszremv /= => <-.
  by rewrite -(eq_inv_posbig Hinv).
Qed.

Lemma eq_inv_std T (u : seq T) : eq_inv u (std u).
Proof.
  move Hn : (size u) => n.
  elim: n u Hn => [//= | n IHn] u Hn.
    move: Hn => /eqP/nilP ->.
    rewrite /std /=; exact: eq_inv_nil.
  case Hu : u Hn => [//= | u0 u']; rewrite -Hu => Hn.
  have Hszrem : size (rembig u) = n by rewrite size_rembig Hn.
  move/(_ (rembig u) Hszrem) : IHn.
  rewrite /std Hn /= Hszrem => /eq_invP [] _ Hinv.
  apply/eq_invP; split;
    first by rewrite size_cat /= addnS -size_cat cat_take_drop size_std_rec.
  move=> i j /andP [] Hij Hj.
  rewrite {1 2}[u]Hu -posbig_take_dropE -Hu.
  have Hpossz : posbig u <= size (rembig u).
    have /posbig_size : u != [::] by rewrite Hu.
    by rewrite Hszrem Hn.
  rewrite !(nth_inspos _ _ _ Hpossz).
  have Hposszstd : posbig u <= size (std_rec n (rembig u)).
    by rewrite size_std_rec -Hszrem.
  rewrite !(nth_inspos _ _ _ Hposszstd).
  case (altP (i =P posbig u)) => Hipos.
  - subst i.
    case (altP (j =P posbig u)) => Hjpos; first by rewrite !leqXnn.
    rewrite -nth_rembig (shiftinv_posK Hjpos).
    have {Hij Hjpos} Hjpos : posbig u < j by rewrite ltn_neqAle eq_sym Hij Hjpos.
    have /allP Hall := allLtn_std_rec (rembig u).
    set uj := (X in n <=A X).
    have /Hall /= : uj \in std (rembig u).
      rewrite /std Hszrem.
      apply: mem_nth; rewrite /shiftinv_pos size_std_rec [j < _]ltnNge (ltnW Hjpos) /=.
      move: Hjpos Hj; case j => [//= |j'] /= _.
      by rewrite Hn.
    rewrite Hszrem [n <=A uj]leqXNgtnX => -> /= {Hall uj}.
    rewrite -(subnKC Hjpos) -nth_drop.
    have:= allLtn_posbig u0 u'; rewrite -Hu => /allP /= Hall.
    set uj := (X in _ <=A X).
    have /Hall /= : uj \in drop (posbig u).+1 u.
      apply: mem_nth; rewrite size_drop ltn_sub2r //=.
      exact: (leq_ltn_trans Hjpos).
    by rewrite leqXNgtnX => ->.
  - case (altP (j =P posbig u)) => Hjpos.
    subst j.
    have {Hipos Hij} Hipos : i < posbig u by rewrite ltn_neqAle Hipos Hij.
    rewrite /shiftinv_pos Hipos -nth_rembig.
    have /allP Hall := maxLP u0 u'.
    set ui := (nth _ _ _).
    have {ui Hall} /Hall /= -> : ui \in (u0 :: u').
      rewrite /ui Hu; apply: mem_nth.
      rewrite /shift_pos -Hu Hipos.
      exact: (ltn_trans Hipos).
    have:= allLtn_std_rec (rembig u) => /allP Hall.
    set ui := (nth _ _ _).
    have /Hall /= : ui \in std (rembig u).
      rewrite /std Hszrem.
      apply: mem_nth; rewrite /shiftinv_pos size_std_rec -Hszrem.
      exact: (leq_trans Hipos).
    by rewrite Hszrem => /ltnXW ->.
  - apply: Hinv; rewrite (shiftinv_pos_incr _ Hij) /=.
    rewrite /shiftinv_pos.
    case (ltnP j (posbig u)) => Hjpos2; first exact: (leq_trans Hjpos2).
    have {Hjpos Hjpos2} : posbig u < j by rewrite ltn_neqAle eq_sym Hjpos2 Hjpos.
    case: j Hj {Hij} => [//= | j] /=.
    by rewrite Hn Hszrem ltnS.
Qed.

CoInductive std_spec T (s : seq T) (p : seq nat) : Prop :=
  | StdSpec : is_std p -> eq_inv s p -> std_spec s p.

Lemma std_spec_uniq T (u : seq T) p q :
  std_spec u p -> std_spec u q -> p = q.
Proof.
  case=> Heqp Hp; case=> Heqq /(eq_inv_trans (eq_inv_sym Hp)) {Hp u}.
  rewrite -{2}(std_std Heqp) -{2}(std_std Heqq).
  exact: std_eq_inv.
Qed.

Lemma std_specP T (s : seq T) : std_spec s (std s).
Proof. constructor; [exact: std_is_std | exact: eq_inv_std]. Qed.

Lemma stdP T (s : seq T) p :
  reflect (std_spec s p) (std s == p).
Proof.
  apply/(iffP idP).
  + move/eqP <-; exact: std_specP.
  + move=> Hspec; apply/eqP; exact: (std_spec_uniq (std_specP s)).
Qed.

Lemma std_eq_invP S T (u : seq S) (v : seq T) :
  reflect (eq_inv u v) (std u == std v).
Proof.
  apply: (iffP idP).
  + move=> /eqP Heq; apply: (eq_inv_trans (eq_inv_std u)).
    rewrite Heq; apply: eq_inv_sym; exact: eq_inv_std.
  + by move /std_eq_inv ->.
Qed.

Lemma std_rconsK S T (u : seq S) (v : seq T) a b :
  std (rcons u a) = std (rcons v b) -> std u = std v.
Proof.
  move/eqP/std_eq_invP/eq_invP => [] /eqP; rewrite !size_rcons eqSS => /eqP Hsz Hinv.
  apply/eqP/std_eq_invP/eq_invP; split; first exact Hsz.
  move=> i j /andP [] Hij Hj.
  have {Hinv} /Hinv : i <= j < (size u).+1 by rewrite Hij /=; exact: (leq_trans Hj).
  by rewrite !nth_rcons -Hsz (leq_ltn_trans Hij Hj) Hj.
Qed.

Lemma eq_inv_catl T1 T2 (u1 v1 : seq T1) (u2 v2 : seq T2) :
  eq_inv (u1 ++ v1) (u2 ++ v2) -> size u1 = size u2 -> eq_inv u1 u2.
Proof.
  move/eq_invP => []; rewrite !size_cat => Hsz Hinv Hszu.
  apply/eq_invP; split; first exact Hszu.
  move=> i j /andP [] Hij Hj.
  have /Hinv : i <= j < size u1 + size v1.
    rewrite Hij /=; apply (leq_trans Hj); exact: leq_addr.
  by rewrite !nth_cat -Hszu Hj (leq_ltn_trans Hij Hj).
Qed.

Lemma std_take_std T (u v : seq T) : std (take (size u) (std (u ++ v))) = std u.
Proof.
  apply/eqP/std_eq_invP.
  rewrite -{3}(take_size_cat v (erefl (size u))).
  apply (eq_inv_catl (v1 := drop (size u) (std (u ++ v)))
                     (v2 := drop (size u) (u ++ v)) ).
  - rewrite !cat_take_drop; apply eq_inv_sym; exact: eq_inv_std.
  - by rewrite !size_take size_std.
Qed.

Lemma eq_inv_catr T1 T2 (u1 v1 : seq T1) (u2 v2 : seq T2) :
  eq_inv (u1 ++ v1) (u2 ++ v2) -> size u1 = size u2 -> eq_inv v1 v2.
Proof.
  move/eq_invP => []; rewrite !size_cat => Hsz Hinv Hszu.
  apply/eq_invP; split; first by apply/eqP; rewrite -(eqn_add2l (size u1)) {2}Hszu Hsz.
  move=> i j /andP [] Hij Hj.
  have /Hinv : size u1 + i <= size u1 + j < size u1 + size v1.
    rewrite leq_add2l ltn_add2l Hij /=; exact: (leq_trans Hj).
  by rewrite !nth_cat -Hszu !ltnNge !leq_addr /= !addKn.
Qed.

Lemma std_drop_std T (u v : seq T) : std (drop (size u) (std (u ++ v))) = std v.
Proof.
  apply/eqP/std_eq_invP.
  rewrite -{2}(drop_size_cat v (erefl (size u))).
  apply (eq_inv_catr (u1 := take (size u) (std (u ++ v)))
                     (u2 := take (size u) (u ++ v)) ).
  - rewrite !cat_take_drop; apply eq_inv_sym; exact: eq_inv_std.
  - by rewrite !size_take size_std.
Qed.

End Spec.


Section PermEq.

Variable Alph : ordType.
Implicit Type u v : seq Alph.

Theorem perm_eq_stdE u v : perm_eq u v -> std u = std v -> u = v.
Proof.
  move=> Hperm.
  move Hn : (size v) => n; elim: n u v Hn Hperm => [| n IHn] u v Hn Hperm /=.
    move: Hperm => /perm_eq_size; rewrite Hn => /eqP/nilP -> _.
    by move: Hn => /eqP/nilP ->.
  move=> Hstd.
  have:= size_rembig v; rewrite Hn /= => Hszrem.
  have Hpermrem := perm_eq_rembig Hperm.
  have:= congr1 rembig Hstd; rewrite -!std_rembig => Hstdrem.
  move/(_ _ _ Hszrem Hpermrem Hstdrem) : IHn => Hrem {Hszrem Hpermrem Hstdrem}.
  have:= congr1 posbig Hstd; rewrite !std_posbig => Hstdpos.
  have:= Hn; case Hv : v => [//= | v0 v'] /= _.
  have:= Hperm => /perm_eq_size; rewrite Hn.
  case Hu : u => [//= | u0 u'] /= _.
  rewrite -[u0 :: u'](posbig_take_dropE) -[v0 :: v'](posbig_take_dropE).
  rewrite -Hu -Hv Hrem Hstdpos; congr (_ ++ _ :: _).
  by apply maxL_perm_eq; rewrite -Hu -Hv.
Qed.

End PermEq.


(** ** Standardization and elementary transpositions of a word *)
Section Transp.

Variable Alph : inhOrdType.
Let Z := (inhabitant Alph).
Implicit Type u v : seq Alph.

Lemma nth_transp u v a b i :
  i != size u -> i != (size u).+1 ->
  nth Z (u ++ [:: a; b] ++ v) i =  nth Z (u ++ [:: b; a] ++ v) i.
Proof.
  move=> Hi Hi1; rewrite !nth_cat.
  case: (ltnP i (size u)) => //= Hui.
  have {Hui Hi} Hi: (size u) < i by rewrite ltn_neqAle eq_sym Hui Hi.
  have {Hi1 Hi}   : (size u).+1 < i by rewrite ltn_neqAle eq_sym Hi1 Hi.
  rewrite -addn1 addSnnS => /(leq_sub2r (size u)); rewrite addnC addnK.
  by case: (i - (size u)) => [//= | [//= | j]] _.
Qed.

Lemma nth_sizeu u v a b :
  nth Z (u ++ [:: a; b] ++ v) (size u) = a.
Proof. by rewrite nth_cat ltnn subnn. Qed.

Lemma nth_sizeu1 u v a b :
  nth Z (u ++ [:: a; b] ++ v) (size u).+1 = b.
Proof. by rewrite nth_cat ltnNge leqnSn /= subSnn /=. Qed.

Lemma nth_sizeu2 u v a b c :
  nth Z (u ++ [:: a; b; c] ++ v) (size u).+2 = c.
Proof.
  rewrite nth_cat ltnNge (leq_trans (leqnSn _) (leqnSn _)) /=.
  by rewrite -add1n -[(size u).+1]add1n addnA addn1 (addnK (size u) 2).
Qed.

End Transp.

Lemma eq_inv_transp (s T : inhOrdType) (u v : seq s) a b
                                 (U V : seq T) A B :
  a <A b -> A <A B -> size u = size U ->
  eq_inv (u ++ [:: a; b] ++ v) (U ++ [:: A; B] ++ V) ->
  eq_inv (u ++ [:: b; a] ++ v) (U ++ [:: B; A] ++ V).
Proof.
  move=> Hab HAB HuU /eq_invP [] Hsz Hinv.
  apply/eq_invP; split; first by move: Hsz; rewrite !size_cat /=.
  have Hsztransp :
    (size (u ++ [:: a, b & v])) = (size (u ++ [:: b, a & v])) by rewrite !size_cat.
  move=> i j /andP [] Hij Hj.
  case: (altP (i =P (size u))) => Hiu.
  - subst i; rewrite {2}HuU !nth_sizeu.
    case: (altP (j =P (size u))) => Hju.
    + subst j; by rewrite {2}HuU !nth_sizeu !leqXnn.
    case: (altP (j =P (size u).+1)) => Hju1.
    + subst j; rewrite {2}HuU !nth_sizeu1.
      by rewrite !leqXNgtnX Hab HAB.
    + move/(_ (size u).+1 j) : Hinv.
      set Hyp := (X in (X -> _ ) -> _) => Hinv.
      have {Hyp Hinv} /Hinv : Hyp.
        by rewrite /Hyp ltn_neqAle eq_sym Hju Hij; move: Hj; rewrite !size_cat.
      rewrite (nth_transp _ _ _ Hju Hju1).
      rewrite HuU in Hju; rewrite HuU in Hju1.
      rewrite (nth_transp _ _ _ Hju Hju1).
      by rewrite {2}HuU !nth_sizeu1.
  case: (altP (i =P (size u).+1)) => Hiu1.
  - subst i; rewrite {2}HuU !nth_sizeu1.
    case: (altP (j =P (size u).+1)) => Hju1.
    + subst j; rewrite {2}HuU !nth_sizeu1.
      by rewrite !leqXnn.
    + move/(_ (size u) j) : Hinv.
      set Hyp := (X in (X -> _ ) -> _) => Hinv.
      have {Hyp Hinv} /Hinv : Hyp.
        by rewrite /Hyp (ltnW Hij) /=; move: Hj; rewrite !size_cat.
      have Hju : j != size u by rewrite eq_sym (ltn_eqF Hij).
      rewrite (nth_transp _ _ _ Hju Hju1).
      rewrite HuU in Hju; rewrite HuU in Hju1.
      rewrite (nth_transp _ _ _ Hju Hju1).
      by rewrite {2}HuU !nth_sizeu.
  - rewrite (nth_transp _ _ _ Hiu Hiu1).
    rewrite HuU in Hiu; rewrite HuU in Hiu1.
    rewrite (nth_transp _ _ _ Hiu Hiu1).
    rewrite -HuU in Hiu; rewrite -HuU in Hiu1.
    case: (altP (j =P (size u))) => Hju.
    + subst j; rewrite {2}HuU !nth_sizeu.
      move/(_ i (size u).+1) : Hinv.
      set Hyp := (X in (X -> _ ) -> _) => Hinv.
      have {Hyp Hinv} /Hinv : Hyp.
        rewrite /Hyp (leq_trans Hij (leqnSn _)) /=; rewrite !size_cat /=.
        rewrite !addnS !ltnS; exact: leq_addr.
      by rewrite {2}HuU !nth_sizeu1.
    case: (altP (j =P (size u).+1)) => Hju1.
    + subst j; rewrite {2}HuU !nth_sizeu1.
      move/(_ i (size u)) : Hinv.
      set Hyp := (X in (X -> _ ) -> _) => Hinv.
      have {Hyp Hinv} /Hinv : Hyp.
        rewrite /Hyp -ltnS ltn_neqAle Hiu1 Hij /=.
        by rewrite -[size u]addn0 size_cat ltn_add2l.
      by rewrite {2}HuU !nth_sizeu.
    + rewrite (nth_transp _ _ _ Hju Hju1).
      rewrite HuU in Hju; rewrite HuU in Hju1.
      rewrite (nth_transp _ _ _ Hju Hju1).
      move/(_ i j) : Hinv.
      set Hyp := (X in (X -> _ ) -> _) => Hinv.
      have {Hyp Hinv} /Hinv : Hyp.
        by rewrite /Hyp Hij /=; move: Hj; rewrite !size_cat.
      by apply.
Qed.

Lemma std_transp (T : inhOrdType) (u v : seq T) a b
                               (U V : seq nat) A B :
  a <A b -> size u = size U ->
  std (u ++ [:: a; b] ++ v) = (U ++ [:: A; B] ++ V) ->
  std (u ++ [:: b; a] ++ v) = (U ++ [:: B; A] ++ V).
Proof.
  move=> Hab Hsz /eqP/stdP [] Hstd Hinv.
  apply/eqP/stdP; constructor.
  + apply: (perm_eq_std Hstd).
    rewrite perm_cat2l perm_cat2r -[[:: B; A]]cat1s -[[:: A; B]]cat1s.
    apply/perm_eqlP; exact: perm_catC.
  + apply: eq_inv_transp => //=.
    move: Hinv => /eq_invP [] _ Hinv.
    move/(_ (size u) (size u).+1) : Hinv.
    set Hyp := (X in (X -> _ ) -> _) => Hinv.
    have {Hyp Hinv} /Hinv : Hyp.
      by rewrite /Hyp leqnSn /= size_cat /= -addn1 addSnnS leq_add2l.
    rewrite {3}Hsz !nth_sizeu !{2}Hsz !nth_sizeu1.
    rewrite (ltnXW Hab) /ltnX_op => <-; rewrite andbT.
    move: Hstd => /std_uniq; rewrite cat_uniq => /and3P [] _ _ /= /and3P [].
    by rewrite inE negb_or => /andP [].
Qed.

Lemma std_cutabc (T : ordType) (u v : seq T) a b c :
  exists U V A B C, size u = size U /\
  std (u ++ [:: a; b; c] ++ v) = (U ++ [:: A; B; C] ++ V).
Proof.
  set w1 := u ++ _.
  have Hsz : size u < size (w1).
    by rewrite /w1 size_cat /= -{1}[size u]addn0 ltn_add2l.
  exists (take (size u) (std w1)).
  exists (drop (size u).+3 (std w1)).
  exists (nth 0 (std w1) (size u)).
  exists (nth 0 (std w1) (size u).+1).
  exists (nth 0 (std w1) (size u).+2).
  split; first by rewrite size_take size_std Hsz.
  rewrite -{1 3 4 5 6}(cat_take_drop (size u) (std w1)); congr (_ ++ _).
  rewrite drop_cat !nth_cat !size_take size_std Hsz ltnn.
  rewrite !ltnNge leqnSn /= (leq_trans (leqnSn _) (leqnSn _)) /=.
  rewrite (leq_trans (leq_trans (leqnSn _) (leqnSn _)) (leqnSn _)) /=.
  set d := drop (size u) (std w1).
  have : size d >= 3 by rewrite /d /w1 size_drop size_std size_cat addnC addnK.
  case H : d => [//= | A [//= | B [//= | C d']]] _ /=.
  rewrite !subSn //=; last exact: (@leq_trans (size u).+1).
  by rewrite subnn drop0.
Qed.



(** * Inverse of a standard word *)
Lemma perm_eq_size_uniq (T : eqType) (s1 s2 : seq T) :
  uniq s1 -> {subset s1 <= s2} -> size s2 <= size s1 -> perm_eq s1 s2.
Proof.
  move=> Hus1 Hsubs /(leq_size_perm Hus1 Hsubs) => [] [] Heq Hsz.
  apply: (uniq_perm_eq Hus1); last exact Heq.
  by rewrite -(perm_uniq Heq Hsz).
Qed.

Section InvSeq.

Implicit Type n : nat.

Definition linvseq s :=
  [fun t => all (fun i => nth (size s) t (nth (size t) s i) == i) (iota 0 (size s))].
Definition invseq s t := linvseq s t && linvseq t s.

Lemma linvseqP s t :
  reflect (forall i, i < size s -> nth (size s) t (nth (size t) s i) = i) (linvseq s t).
Proof.
  rewrite /linvseq; apply: (iffP idP) => /=.
  - move=> /allP H i Hi.
    apply/eqP; apply: H; by rewrite mem_iota.
  - move=> H; apply/allP => /= i; rewrite mem_iota /= add0n => Hi.
    by rewrite (H i Hi).
Qed.

Lemma invseq_sym s t : invseq s t -> invseq t s.
Proof. by rewrite /invseq andbC. Qed.

Lemma size_all_leq n t : (forall i, i < n -> i \in t) -> n <= size t.
Proof.
  move=> H.
  pose s := undup (filter (gtn n) t).
  have Hperm : perm_eq s (iota 0 n).
    apply: (uniq_perm_eq (undup_uniq _) (iota_uniq _ _)).
    move=> i; rewrite /s mem_undup mem_iota /= add0n mem_filter /=.
    apply/idP/idP => [/andP [] -> //| Hi].
    by rewrite Hi (H i Hi).
  have <- := size_iota 0 n.
  rewrite -(perm_eq_size Hperm) /s.
  apply: (leq_trans (size_undup _)).
  rewrite size_filter; exact: count_size.
Qed.

Lemma linvseq_ltn_szt s t :
  linvseq s t -> forall i, i < size s -> nth (size t) s i < size t.
Proof.
  move/linvseqP => Hinv i Hi; move/(_ i Hi) : Hinv.
  case: (ltnP (nth (size t) s i) (size t)) => //= Habs.
  rewrite (nth_default _ Habs) => H.
  by move: Hi; rewrite H ltnn.
Qed.

Lemma size_leq_invseq s t : linvseq s t -> size s <= size t.
Proof.
  move=> Hinv; have:= Hinv => /linvseqP H.
  apply: size_all_leq => i Hi; move/(_ i Hi) : H => <-.
  apply: mem_nth; exact: linvseq_ltn_szt.
Qed.

Lemma size_invseq s t : invseq s t -> size s = size t.
Proof.
  rewrite /invseq => /andP [] Hst Hts.
  apply/eqP; by rewrite eqn_leq !size_leq_invseq.
Qed.

Lemma linvseq_subset_iota s t : linvseq s t -> {subset iota 0 (size s) <= t}.
Proof.
  move/linvseqP => Hinv i.
  rewrite mem_iota /= add0n => Hi.
  move/(_ i Hi) : Hinv => Heq; rewrite -Heq.
  apply: mem_nth; move: Hi; apply: contraLR; rewrite -!ltnNge !ltnS => H.
  have := nth_default (size s) H.
  by rewrite Heq => ->.
Qed.

Lemma invseq_is_std s t : invseq s t -> is_std s.
Proof.
  move=> /invseq_sym Hinv; rewrite /is_std perm_eq_sym.
  apply: perm_eq_size_uniq.
  - exact: iota_uniq.
  - rewrite -(size_invseq Hinv); apply: linvseq_subset_iota.
    move: Hinv; by rewrite /invseq => /andP [].
  - by rewrite size_iota.
Qed.

Lemma linvseq_sizeP s t :
  linvseq s t -> size s = size t -> invseq s t.
Proof.
  move=> Hinv Hsize; rewrite /invseq; apply/andP; split; first exact Hinv.
  have Hiota := linvseq_subset_iota Hinv.
  have Htmp : size t <= size (iota 0 (size s)) by rewrite size_iota Hsize.
  have Huniq := leq_size_uniq (iota_uniq 0 (size s)) Hiota Htmp.
  move/(perm_eq_size_uniq (iota_uniq 0 (size s)) Hiota) : Htmp => Hperm {Hiota}.
  apply/linvseqP => i Hi; move: Hinv => /linvseqP Hinv.
  have:= mem_nth (size s) Hi; rewrite -(perm_eq_mem Hperm) mem_iota /= add0n => Hnth.
  move/(_ _ Hnth) : Hinv => Heq.
  have/eqP := Heq; rewrite nth_uniq //=; first by move/eqP.
  case: (ltnP (nth (size t) s (nth (size s) t i)) (size t)) => //= H.
  move: Heq; rewrite (nth_default _ H) => /eqP.
  by rewrite (gtn_eqF Hnth).
Qed.

Lemma invseq_nthE s t :
  invseq s t ->
  forall i j, i < size s -> j < size t -> (i = nth (size s) t j <-> nth (size t) s i = j).
Proof.
  move=> Hinv i j Hi Hj.
  move: Hinv; rewrite /invseq => /andP [] /linvseqP Hst /linvseqP Hts.
  split => H.
  + move/(_ j Hj) : Hts; by rewrite H.
  + move/(_ i Hi) : Hst; by rewrite H.
Qed.

(** * inverse of the standardized of w *)

Definition invstd s := mkseq (fun i => index i s) (size s).

Lemma invseq_invstd s : is_std s -> invseq s (invstd s).
Proof.
  move=> Hstd; rewrite /invseq; apply/andP; split; apply/linvseqP; rewrite size_mkseq => i Hi.
  - rewrite nth_mkseq.
    + apply: (index_uniq _ Hi). exact: std_uniq.
    + by rewrite -(mem_std _ Hstd) mem_nth.
  - rewrite nth_mkseq //=; apply: nth_index; by rewrite (mem_std _ Hstd).
Qed.

Lemma size_invstd p : size (invstd p) = size p.
Proof. by rewrite /invstd size_mkseq. Qed.

Lemma invstd_is_std p : is_std p -> is_std (invstd p).
Proof.
  move=> H; apply: (invseq_is_std (t := p)).
  apply: invseq_sym; exact: invseq_invstd.
Qed.

Lemma invseqE s t1 t2 : invseq s t1 -> invseq s t2 -> t1 = t2.
Proof.
  move=> Hinv1 Hinv2.
  have Hsz: size t1 = size t2 by rewrite -(size_invseq Hinv1) -(size_invseq Hinv2).
  apply: (eq_from_nth (x0 := size s) Hsz) => i Hi1.
  have:= Hi1; rewrite Hsz => Hi2.
  have:= Hinv1; rewrite /invseq => /andP [] _ Ht1s.
  have Hnth1 := linvseq_ltn_szt Ht1s Hi1.
  rewrite (invseq_nthE Hinv2 Hnth1 Hi2) -Hsz.
  by move: Ht1s => /linvseqP ->.
Qed.

Lemma invstdK s : is_std s -> invstd (invstd s) = s.
Proof.
  move=> Hstd; apply: (invseqE (s := invstd s)).
  + apply: invseq_invstd; exact: invstd_is_std.
  + apply: invseq_sym; exact: invseq_invstd.
Qed.

Lemma invstd_inj s t : is_std s -> is_std t -> (invstd s) = (invstd t) -> s = t.
Proof. move=> Hs Ht /(congr1 invstd); by rewrite !invstdK. Qed.

End InvSeq.


Section Test.

  Let u := [:: 4;1;2;2;5;3].
  Let v := [:: 0;4;3;3].

  Goal std u = [:: 4; 0; 1; 2; 5; 3].
  Proof. compute; exact: erefl. Qed.

  Goal invstd (std u) = filter (gtn (size u)) (invstd (std (u ++ v))).
  Proof. compute; exact: erefl. Qed.

End Test.
