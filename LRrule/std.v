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
Require Import ssreflect ssrbool ssrfun ssrnat eqtype finfun fintype choice seq tuple.
Require Import finset perm fingroup.

Require Import subseq partition permuted ordtype schensted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import OrdNotations.

Section StandardWords.

Implicit Type n : nat.
Definition is_std (s : seq nat) := perm_eq s (iota 0 (size s)).

Lemma perm_eq_std u v : is_std u -> perm_eq v u -> is_std v.
Proof.
  rewrite /is_std => Hperm Heq.
  rewrite (perm_eq_size Heq); by apply (perm_eq_trans Heq Hperm).
Qed.

Lemma std_perm_eq u v : is_std u -> is_std v -> size u = size v -> perm_eq v u.
Proof.
  rewrite /is_std => Hperm Heq Hsize.
  rewrite Hsize perm_eq_sym in Hperm.
  by apply (perm_eq_trans Heq Hperm).
Qed.

Lemma mem_std p i : is_std p -> (i \in p) = (i < size p).
Proof. rewrite /is_std => /perm_eq_mem ->; by rewrite mem_iota /= add0n. Qed.

Lemma std_uniq u : is_std u -> uniq u.
Proof. rewrite /is_std => /perm_eq_uniq ->. by apply iota_uniq. Qed.

Definition wordperm n (p : 'S_n) := [seq val (p i) | i <- enum 'I_n].

Open Scope group_scope.

Lemma wordperm_iota n (p : 'S_n) : (wordperm p) =i iota 0 n.
Proof.
  move=> i; rewrite mem_iota add0n /=.
  apply/(sameP idP); apply(iffP idP).
  - move=> Hi; apply/mapP.
    exists ((p^-1) (Ordinal Hi)).
    + by rewrite mem_enum.
    + by rewrite permKV.
  - move/mapP => [] j _ -> /=.
    by apply ltn_ord.
Qed.

Lemma uniq_wordperm n (p : 'S_n) : uniq (wordperm p).
Proof.
  rewrite (perm_uniq (wordperm_iota _)); first by apply (iota_uniq 0 n).
  by rewrite size_map size_enum_ord size_iota.
Qed.

Lemma wordperm_std n (p : 'S_n) : is_std (wordperm p).
Proof.
  rewrite /is_std size_map size_enum_ord.
  apply uniq_perm_eq.
  - by apply uniq_wordperm.
  - by apply iota_uniq.
  - by apply wordperm_iota.
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
    have:= eq_refl (val (Ordinal (Hfpi i))); rewrite {2}Heq /=.
    rewrite /fpn (nth_uniq _ (ltn_ord _) (ltn_ord _)) //=.
    by apply std_uniq.
  exists (perm Hfp); rewrite /wordperm /=.
  apply (@eq_from_nth _ 0); first by rewrite size_map size_enum_ord.
  move => i Hi; rewrite (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
  have {3}-> : i = Ordinal Hi by [].
  by rewrite nth_ord_enum /= permE /fp /= ffunE /= /fpn /=.
Qed.

Lemma is_stdP s : reflect (exists p : 'S_(size s), s = wordperm p) (is_std s).
Proof.
  apply (iffP idP).
  + move/perm_of_std => [] p Hp; by exists p.
  + move=> [] p ->; by apply wordperm_std.
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
      move=> Hn; exfalso; have:= ltn_ord j.
      by rewrite -{1}Hn ltnn.
  - move ->; rewrite (nth_map j); last by rewrite size_enum_ord; apply ltn_ord.
    by rewrite nth_ord_enum /= permKV.
Qed.

End StandardWords.


Section Standardisation.

Variable Alph : ordType.
Let Z := (inhabitant Alph).
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

Lemma std_is_std s : is_std (std s).
Proof.
  rewrite /is_std /std size_std_rec perm_eq_sym.
  move Hn : (size s) => n; elim: n s Hn => [//= | n IHn] s Hn.
  apply (@perm_eq_trans _ (n :: (iota 0 n))).
    rewrite -addn1 iota_add /= add0n -cat1s; apply/perm_eqlP; by apply perm_catC.
  apply (@perm_eq_trans _ (n :: std_rec n (rembig s))).
    rewrite perm_cons; apply IHn; by rewrite size_rembig Hn.
  rewrite {IHn Hn} /= -[n :: drop _ _]cat1s catA.
  move: (std_rec n (rembig s)) => l.
  rewrite -{1}[l](cat_take_drop (posbig s)) -cat1s -catA.
  by apply/perm_eqlP; apply perm_catCA.
Qed.

Lemma in_std_ltn_size s i : i \in std s = (i < size s).
Proof. by rewrite (mem_std _ (std_is_std s)) size_std_rec. Qed.

Lemma std_all_gtnX_size s : all (gtnX nat_ordType (size s)) (std s).
Proof. apply/allP=> i /=; by rewrite ltnXnatE in_std_ltn_size. Qed.

Lemma allLtn_std_rec s : allLtn (std s) (size s).
Proof. by apply std_all_gtnX_size. Qed.

Lemma rembig_ins_std s pos :
  rembig (take pos (std s) ++ size s :: drop pos (std s)) = std s.
Proof.
  apply esym; apply/eqP/rembigP; first by case: (take _ _).
  have:= allLtn_std_rec s.
  rewrite -{1}[std s](cat_take_drop pos) allLtn_catE => /andP [].
  set ll := take _ _; set lr := drop _ _ => /allLtnW Hll Hlr.
  exists ll; exists (size s); exists lr; by split; first by rewrite cat_take_drop.
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
    case (ltnP (posbig s).+1 (size s)) => Hpos; first by [].
    apply/eqP; rewrite eqn_leq Hpos andbT.
    have: s != [::] by move: Hmax; case s.
    by apply posbig_size.
  rewrite HposLR; apply/eqP; rewrite -posbigE.
  have:= allLtn_std_rec (s0 :: rembig s).
  rewrite size_take size_std_rec HposLR.
  have Hif : (if size LR < size s then size LR else size s) = size LR.
    rewrite /LR /pos size_take size_std_rec.
    case (ltnP (posbig s).+1 (size s)) => Hpos; first by rewrite Hpos.
    by rewrite ltnn.
  rewrite /LR size_take size_std_rec HposLR !Hif /std.
  have -> : size (s0 :: rembig s) = size s.
    rewrite /= size_rembig; move: Hmax; by case s.
  rewrite -{1}[std_rec _ _](cat_take_drop (size LR)) allLtn_catE => /andP [] H1 ->.
  rewrite andbT; by apply allLtnW.
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
      rewrite -rembig_iota; by apply perm_eq_rembig.
    rewrite (IHn _ Hszrem Hprem) Hs {IHn}.
    have:= Hperm; rewrite {1}Hs => /maxL_perm_eq.
    rewrite maxL_iota_n => <-.
    by apply posbig_take_dropE. 
Qed.

Lemma std_stdE (T : ordType) (s : seq T) : std (std s) = std s.
Proof. apply std_std; by apply std_is_std. Qed.

Section Spec.

Definition inversions (T : ordType) (w : seq T) : rel nat :=
  fun i j => (i <= j < size w) && (nth (inhabitant T) w i <=A nth (inhabitant T) w j).

Definition eq_inv (T1 T2 : ordType) (w1 : seq T1) (w2 : seq T2) :=
  ((inversions w1) =2 (inversions w2)).

Lemma eq_inv_refl (T : ordType) (w : seq T) : eq_inv w w.
Proof. by []. Qed.

Lemma eq_inv_nil (T1 T2 : ordType) : eq_inv (@nil T1) (@nil T2).
Proof.
  rewrite /eq_inv /inversions => i j /=.
  by rewrite ltn0 andbF.
Qed.

Lemma eq_inv_sym (T1 T2 : ordType) (w1 : seq T1) (w2 : seq T2) :
  eq_inv w1 w2 -> eq_inv w2 w1.
Proof.
  rewrite /inversions => Hinv i j.
  have:= Hinv i j; exact esym.
Qed.

Lemma eq_inv_trans (T1 T2 T3 : ordType) (w1 : seq T1) (w2 : seq T2) (w3 : seq T3) :
  eq_inv w1 w2 -> eq_inv w2 w3 -> eq_inv w1 w3.
Proof.
  rewrite /inversions => H12 H23 i j.
  exact (etrans (H12 i j) (H23 i j)).
Qed.

Lemma eq_inv_size_leq (T1 T2 : ordType) (w1 : seq T1) (w2 : seq T2) :
  eq_inv w1 w2 -> size w1 <= size w2.
Proof.
  rewrite /eq_inv /inversions => Hinv.
  case H : (size w1) => [//= | n].
  have:= Hinv n n; rewrite H leqnn ltnSn leqXnn /=.
  by move/eqP/andP => [].
Qed.

Lemma eq_inv_size (T1 T2 : ordType) (w1 : seq T1) (w2 : seq T2) :
  eq_inv w1 w2 -> size w1 = size w2.
Proof.
  move=> H; apply /eqP; rewrite eqn_leq.
  by rewrite (eq_inv_size_leq H) (eq_inv_size_leq (eq_inv_sym H)).
Qed.

Lemma eq_invP  (T1 T2 : ordType) (w1 : seq T1) (w2 : seq T2) :
  (size w1 = size w2 /\
   forall i j, i <= j < size w1 ->
               nth (inhabitant T1) w1 i <=A nth (inhabitant T1) w1 j =
               (nth (inhabitant T2) w2 i <=A nth (inhabitant T2) w2 j))
    <-> (eq_inv w1 w2).
Proof.
  split.
  - rewrite /eq_inv /inversions; move=> [] Hsz H i j /=.
    apply/(sameP idP); apply(iffP idP) => /andP [] Hij Hnth.
    + by rewrite H Hsz Hij.
    + by rewrite -(H _ _ Hij) -Hsz Hij.
  - move=> H; have Hsz := eq_inv_size H; split; first exact Hsz.
    move=> i j Hij.
    move: H; rewrite /eq_inv /inversions -Hsz => H.
    have {H} := H i j; by rewrite Hij.
Qed.

Lemma eq_inv_consK (T1 T2 : ordType) (a : T1) u (b : T2) v :
  eq_inv (a :: u) (b :: v) -> eq_inv u v.
Proof.
  rewrite /eq_inv /inversions => H i j.
  have /= := H i.+1 j.+1; by rewrite !ltnS.
Qed.

Lemma eq_inv_rconsK (T1 T2 : ordType) (a : T1) u (b : T2) v :
  eq_inv (rcons u a) (rcons v b) -> eq_inv u v.
Proof.
  rewrite -!eq_invP !size_rcons => [] [] Hsz H.
  move: Hsz => /eqP; rewrite eqSS => /eqP Hsz; rewrite Hsz; rewrite Hsz in H.
  split; first by [].
  move=> i j Hij.
  move: Hij => /andP [] Hi Hj.
  have {H}/H : i <= j < (size v).+1.
    rewrite Hi /=; by apply (ltn_trans Hj).
  by rewrite !nth_rcons Hsz Hj (leq_ltn_trans Hi Hj).
Qed.

Lemma eq_inv_allgtnXimply (S T : ordType) (a : S) u (b : T) v :
  eq_inv (a :: u) (b :: v) -> (allLtn u a) -> (allLtn v b).
Proof.
  move=> H; have:= (eq_inv_size H).
  move: H; rewrite /eq_inv /inversions => H /= /eqP; rewrite eqSS => /eqP Hsz.
  move/(all_nthP (inhabitant S)) => Hall; apply/(all_nthP (inhabitant T)).
  rewrite -Hsz => i Hi; have /= Hleq := (Hall i Hi).
  have /= := H 0 i.+1.
  move: Hi; rewrite -Hsz -ltnS => -> /=.
  rewrite ltnXNgeqX => <-. by rewrite -ltnXNgeqX.
Qed.

Lemma eq_inv_allgtnX (S T : ordType) (a : S) u (b : T) v :
  eq_inv (a :: u) (b :: v) -> (allLtn u a) = (allLtn v b).
Proof.
  move=> H1; have H2 := eq_inv_sym H1.
  apply/(sameP idP); apply(iffP idP); by apply eq_inv_allgtnXimply.
Qed.

Lemma eq_inv_posbig (S T : ordType) (u : seq S) (v : seq T) :
  eq_inv u v -> posbig u = posbig v.
Proof.
  move=> H; have /eqP := eq_inv_size H.
  elim: u v H => [| a u IHu] /= v.
    by move=> _; rewrite eq_sym => /nilP ->.
  case: v => [//= |b v] /= Heq.
  rewrite eqSS => Hsize; have {IHu} Hpos := IHu v (eq_inv_consK Heq) Hsize.
  have:= Heq; rewrite /eq_inv /inversions => Hinv.
  rewrite -(eq_inv_allgtnX Heq).
  by case: (allLtn u a); last by rewrite Hpos.
Qed.

Lemma eq_inv_rembig (S T : ordType) (u : seq S) (v : seq T) :
  eq_inv u v -> eq_inv (rembig u) (rembig v).
Proof.
  move => Hinv; have Heqpos:= eq_inv_posbig Hinv.
  have:= Hinv; rewrite -!eq_invP => [] [] Hsz Heq.
  rewrite !size_rembig -Hsz; split => //= i j /andP [] Hij Hj.
  rewrite -!nth_rembig /shift_pos -Heqpos.
  case (ltnP i (posbig u)) => Hipos;
    case (ltnP j (posbig u)) => Hjpos; apply Heq.
  - rewrite Hij /=; apply (ltn_trans Hj).
    move: Hj; by case (size u).
  - rewrite (leq_trans Hij (leqnSn _)) /=.
    have -> : (size u) = (size u).-1.+1 by move: Hj; rewrite -ltnS; case (size u).
    by rewrite ltnS.
  - exfalso; have := leq_trans (leq_trans Hjpos Hipos) Hij; by rewrite ltnn.
  - rewrite ltnS Hij /=.
    have -> : (size u) = (size u).-1.+1 by move: Hj; rewrite -ltnS; case (size u).
    by rewrite ltnS.
Qed.

Lemma std_eq_inv (S T : ordType) (u : seq S) (v : seq T) :
  eq_inv u v -> std u = std v.
Proof.
  move => Hinv; move Hn : (size u) => n.
  elim: n u v Hn Hinv => [//= | n IHn] u v Hn Hinv.
    have := eq_inv_size Hinv.
    rewrite Hn => /esym/eqP/nilP ->.
    by move: Hn => /eqP/nilP ->.
  have Hsz := eq_inv_size Hinv.
  have Hszremu : size (rembig u) = n by rewrite size_rembig Hn.
  have Hszremv : size (rembig v) = n by rewrite size_rembig -Hsz Hn.
  have {IHn} := (IHn (rembig u) (rembig v) Hszremu (eq_inv_rembig Hinv)).
  rewrite /std -Hsz Hn Hszremu Hszremv /= => <-.
  by rewrite -(eq_inv_posbig Hinv).
Qed.

Lemma eq_inv_std (S : ordType) (u : seq S) : eq_inv u (std u).
Proof.
  move Hn : (size u) => n.
  elim: n u Hn => [//= | n IHn] u Hn.
    move: Hn => /eqP/nilP ->.
    rewrite /std /=; by apply eq_inv_nil.
  case Hu : u Hn => [//= | u0 u']; rewrite -Hu => Hn.
  have Hszrem : size (rembig u) = n by rewrite size_rembig Hn.
  have {IHn} := (IHn (rembig u) Hszrem).
  rewrite /std Hn /= Hszrem => /eq_invP [] _ Hinv.
  apply /eq_invP; split;
    first by rewrite size_cat /= addnS -size_cat cat_take_drop size_std_rec.
  move => i j /andP [] Hij Hj.
  rewrite {1 2}[u]Hu -posbig_take_dropE -Hu.
  have Hpossz : posbig u <= size (rembig u).
    have /posbig_size : u != [::] by rewrite Hu.
    by rewrite Hszrem Hn.
  rewrite !(nth_inspos _ _ Hpossz).
  have Hposszstd : posbig u <= size (std_rec n (rembig u)).
    by rewrite size_std_rec -Hszrem.
  rewrite !(nth_inspos _ _ Hposszstd).
  case (altP (i =P posbig u)) => Hipos.
  - subst i.
    case (altP (j =P posbig u)) => Hjpos; first by rewrite !leqXnn.
    rewrite -nth_rembig (shiftinv_posK Hjpos).
    have {Hij Hjpos} Hjpos : posbig u < j by rewrite ltn_neqAle eq_sym Hij Hjpos.
    have /allP Hall := allLtn_std_rec (rembig u).
    set uj := (X in n <=A X).
    have /Hall /= : uj \in std (rembig u).
      rewrite /std Hszrem.
      apply mem_nth; rewrite /shiftinv_pos size_std_rec [j < _]ltnNge (ltnW Hjpos) /=.
      move: Hjpos Hj; case j => [//= |j'] /= _.
      by rewrite Hn.
    rewrite Hszrem [n <=A uj]leqXNgtnX => -> /= {Hall uj}.
    rewrite -(subnKC Hjpos) -nth_drop.
    have := allLtn_posbig u0 u'; rewrite -Hu => /allP /= Hall.
    set uj := (X in _ <=A X).
    have /Hall /= : uj \in drop (posbig u).+1 u.
      apply mem_nth; rewrite size_drop ltn_sub2r //=.
      by apply (leq_ltn_trans Hjpos).
    by rewrite leqXNgtnX => ->.
  - case (altP (j =P posbig u)) => Hjpos.
    subst j.
    have {Hipos Hij} Hipos : i < posbig u by rewrite ltn_neqAle Hipos Hij.
    rewrite /shiftinv_pos Hipos -nth_rembig.
    have /allP Hall := maxLP u0 u'.
    set ui := (nth _ _ _).
    have {ui Hall} /Hall /= -> : ui \in (u0 :: u').
      rewrite /ui Hu; apply mem_nth.
      rewrite /shift_pos -Hu Hipos.
      by apply (ltn_trans Hipos).
    have:= allLtn_std_rec (rembig u) => /allP Hall.
    set ui := (nth _ _ _).
    have /Hall /= : ui \in std (rembig u).
      rewrite /std Hszrem.
      apply mem_nth; rewrite /shiftinv_pos size_std_rec -Hszrem.
      by apply (leq_trans Hipos).
    by rewrite Hszrem => /ltnXW ->.
  - apply Hinv; rewrite (shiftinv_pos_incr _ Hij) /=.
    rewrite /shiftinv_pos.
    case (ltnP j (posbig u)) => Hjpos2; first by apply (leq_trans Hjpos2).
    have {Hjpos Hjpos2} : posbig u < j by rewrite ltn_neqAle eq_sym Hjpos2 Hjpos.
    case: j Hj {Hij} => [//= | j] /=.
    by rewrite Hn Hszrem ltnS.
Qed.

CoInductive std_spec (T : ordType) (s : seq T) : seq nat -> Type :=
  | StdSpec : forall p, is_std p -> eq_inv s p -> std_spec s p.

Lemma std_spec_uniq (T : ordType) (u : seq T) p q :
  std_spec u p -> std_spec u q -> p = q.
Proof.
  case => {p} p Heqp Hp; case => {q} q Heqq Hq.
  have {Hp Hq u} Hinv := eq_inv_trans (eq_inv_sym Hp) Hq.
  rewrite -(std_std Heqp) -(std_std Heqq).
  by apply std_eq_inv.
Qed.

Lemma stdP (T : ordType) (s : seq T) : std_spec s (std s).
Proof.
  constructor; first by apply std_is_std.
  by apply eq_inv_std.
Qed.

Lemma std_eq_invP (S T : ordType) (u : seq S) (v : seq T) :
  reflect (eq_inv u v) (std u == std v).
Proof.
  apply (iffP idP).
  + move=> /eqP Heq; apply (eq_inv_trans (eq_inv_std u)).
    rewrite Heq; apply eq_inv_sym; by apply eq_inv_std.
  + by move /std_eq_inv ->.
Qed.

Lemma std_rconsK (S T : ordType) (u : seq S) (v : seq T) a b :
  std (rcons u a) = std (rcons v b) -> std u = std v.
Proof.
  move/eqP/std_eq_invP/eq_invP => [] /eqP; rewrite !size_rcons eqSS => /eqP Hsz Hinv.
  apply/eqP/std_eq_invP/eq_invP; split; first exact Hsz.
  move=> i j /andP [] Hij Hj.
  have {Hinv} /Hinv : i <= j < (size u).+1 by rewrite Hij /=; by apply (leq_trans Hj).
  by rewrite !nth_rcons -Hsz (leq_ltn_trans Hij Hj) Hj.
Qed.

End Spec.
