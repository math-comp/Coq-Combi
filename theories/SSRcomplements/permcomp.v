(** * Combi.SScomplement.perrcomp : complement on permutations *)
(******************************************************************************)
(*      Copyright (C) 2016-2018 Florent Hivert <florent.hivert@lri.fr>        *)
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
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import finset fingroup perm morphism action.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Import GroupScope.

Lemma imset1 (T : finType) (S : {set T}) : [set fun_of_perm 1 x | x in S] = S.
Proof using.
by rewrite -[RHS]imset_id; apply eq_imset => x; rewrite perm1.
Qed.

Lemma permS0 (g : 'S_0) : g = 1%g.
Proof. by apply permP => x; case x. Qed.
Lemma permS1 (g : 'S_1) : g = 1%g.
Proof.
apply/permP => i; rewrite perm1.
case: (g i) => a Ha; case: i => b Hb.
by apply val_inj => /=; case: a b Ha Hb => [|a] [|b].
Qed.

Lemma card_Sn n : #|'S_(n)| = n`!.
Proof using .
rewrite (eq_card (B := perm_on [set : 'I_n])).
  by rewrite card_perm /= cardsE /= card_ord.
move=> p; rewrite inE unfold_in /perm_on /=.
by apply/esym/subsetP => i _; rewrite in_set.
Qed.


Section CastSn.

Definition cast_perm m n (eq_mn : m = n) (s : 'S_m) :=
  let: erefl in _ = n := eq_mn return 'S_n in s.

Lemma cast_perm_id n eq_n s : cast_perm eq_n s = s :> 'S_n.
Proof using. by apply/permP => i; rewrite /cast_perm /= eq_axiomK. Qed.

Lemma cast_ord_permE m n eq_m_n (s : 'S_m) i :
  @cast_ord m n eq_m_n (s i) = (cast_perm eq_m_n s) (cast_ord eq_m_n i).
Proof using. by subst m; rewrite cast_perm_id !cast_ord_id. Qed.

Lemma cast_permE m n (eq_m_n : m = n) (s : 'S_m) (i : 'I_n) :
  cast_ord eq_m_n (s (cast_ord (esym eq_m_n) i)) = cast_perm eq_m_n s i.
Proof. by rewrite cast_ord_permE cast_ordKV. Qed.

Lemma cast_permK m n eq_m_n :
  cancel (@cast_perm m n eq_m_n) (cast_perm (esym eq_m_n)).
Proof using. by subst m. Qed.

Lemma cast_permKV m n eq_m_n :
  cancel (cast_perm (esym eq_m_n)) (@cast_perm m n eq_m_n).
Proof using. by subst m. Qed.

Lemma cast_perm_inj m n eq_m_n : injective (@cast_perm m n eq_m_n).
Proof using. exact: can_inj (cast_permK eq_m_n). Qed.

Lemma cast_perm_morphM m n eq_m_n :
  {morph @cast_perm m n eq_m_n : x y / x * y >-> x * y}.
Proof using. by subst m. Qed.
Canonical morph_of_cast_perm m n eq_m_n :=
  Morphism (D := setT) (in2W (@cast_perm_morphM m n eq_m_n)).

Lemma isom_cast_perm m n eq_m_n : isom setT setT (@cast_perm m n eq_m_n).
Proof using.
subst m.
apply/isomP; split.
- apply/injmP=> i j _ _; exact: cast_perm_inj.
- apply/setP => /= s; rewrite !inE.
  by apply/imsetP; exists s; rewrite ?inE.
Qed.

End CastSn.

Section PermComp.

Variable T : finType.
Implicit Type (s : {perm T}) (X : {set T}) (P : {set {set T}}).

Lemma permX_fix s x n : s x = x -> (s ^+ n) x = x.
Proof using.
move=> Hs; elim: n => [|n IHn]; first by rewrite expg0 perm1.
by rewrite expgS permM Hs.
Qed.

Lemma setactC (aT : finGroupType) (D : {set aT})
      (rT : finType) (to : action D rT) S a :
  to^* (~: S) a = ~: to^* S a.
Proof using.
apply/eqP; rewrite eqEcard; apply/andP; split.
- apply/subsetP => x /imsetP [y]; rewrite !inE => Hy -> {x}.
  by move: Hy; apply contra => /imsetP [z Hz] /act_inj ->.
- rewrite card_setact [X in _ <= X]cardsCs setCK.
  by rewrite cardsCs setCK card_setact.
Qed.

Lemma card_pcycle_neq0 s x : #|pcycle s x| != 0.
Proof using.
by rewrite -lt0n card_gt0; apply/set0Pn; exists x; exact: pcycle_id.
Qed.

Lemma pcyclePmin s x y :
  y \in pcycle s x -> exists2 i, i < #[s] & y = (s ^+ i) x.
Proof using. by move=> /imsetP [z /cyclePmin[ i Hi ->{z}] ->{y}]; exists i. Qed.

Lemma pcycleP s x y :
  reflect (exists i, y = (s ^+ i) x) (y \in pcycle s x).
Proof using.
apply (iffP idP) => [/pcyclePmin [i _ ->]| [i ->]]; last exact: mem_pcycle.
by exists i.
Qed.

End PermComp.


Section PermOnG.

Variable T : finType.
Implicit Type (s t c : {perm T}).

Definition perm_ong S : {set {perm T}} := [set s | perm_on S s].
Lemma group_set_perm_ong S : group_set (perm_ong S).
Proof using.
apply/group_setP; split => [| s t]; rewrite !inE;
   [exact: perm_on1 | exact: perm_onM].
Qed.
Canonical perm_ong_group S : {group {perm T}} := Group (group_set_perm_ong S).
Lemma card_perm_ong S : #|perm_ong S| = #|S|`!.
Proof using. by rewrite cardsE /= card_perm. Qed.

Lemma perm_ongE S : perm_ong S = 'C(~:S | 'P).
Proof using.
apply/setP => s; rewrite inE; apply/idP/astabP => [Hperm x | Hstab].
- by rewrite inE /= apermE => /out_perm; apply.
- apply/subsetP => x; rewrite unfold_in; apply contraR => H.
  by move/(_ x): Hstab; rewrite inE /= apermE => ->.
Qed.

Lemma restr_perm_commute C s : commute (restr_perm C s) s.
Proof using.
case: (boolP (s \in 'N(C | 'P))) =>
    [HC | /triv_restr_perm ->]; last exact: (commute_sym (commute1 _)).
apply/permP => x; case: (boolP (x \in C)) => Hx; rewrite !permM.
- by rewrite !restr_permE //; move: HC => /astabsP/(_ x)/= ->.
- have:= restr_perm_on C s => /out_perm Hout.
  rewrite (Hout _ Hx) {}Hout //.
  by move: Hx; apply contra; move: HC => /astabsP/(_ x)/= ->.
Qed.

End PermOnG.
