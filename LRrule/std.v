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

Require Import subseq partition permuted ordtype schensted congr plactic greeninv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
