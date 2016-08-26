Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun path bigop finset binomial.
From mathcomp Require Import fingroup perm morphism action ssralg.
From mathcomp Require finmodule.

Require Import symgroup partition Greene tools sorted.

Reserved Notation "#{ x }" (at level 0, x at level 10, format "#{ x }").

Set Implicit Arguments.
Unset Strict Implicit.

Import GroupScope.

Notation "#{ x }" :=  #|(x: {set _})|
                      (at level 0, x at level 10, format "#{ x }").

Lemma imset1 (T : finType) (S : {set T}) : [set fun_of_perm 1 x | x in S] = S.
Proof using.
by rewrite -[RHS]imset_id; apply eq_imset => x; rewrite perm1.
Qed.

Section CastSn.

Definition cast_perm_val m n (eq_m_n : m = n) (s : 'S_m) :=
  fun x : 'I_n => cast_ord eq_m_n (s (cast_ord (esym eq_m_n) x)).

Fact cast_perm_proof m n eq_m_n s : injective (@cast_perm_val m n eq_m_n s).
Proof using. by move=> x y /cast_ord_inj/perm_inj/cast_ord_inj. Qed.
Definition cast_perm m n eq_m_n s : 'S_n :=
  perm (@cast_perm_proof m n eq_m_n s).

Lemma cast_permE m n eq_m_n (s : 'S_m) i :
  @cast_ord m n eq_m_n (s i) = (cast_perm eq_m_n s) (cast_ord eq_m_n i).
Proof using. by rewrite permE /cast_perm_val cast_ordK. Qed.

Lemma cast_perm_id n eq_n s : cast_perm eq_n s = s :> 'S_n.
Proof using.
by apply/permP => i /=; rewrite permE /cast_perm_val !cast_ord_id.
Qed.

Lemma cast_permK m n eq_m_n :
  cancel (@cast_perm m n eq_m_n) (cast_perm (esym eq_m_n)).
Proof using.
move=> s /=; apply/permP => i /=; do 2 rewrite permE /cast_perm_val.
by rewrite esymK !cast_ordK.
Qed.

Lemma cast_permKV m n eq_m_n :
  cancel (cast_perm (esym eq_m_n)) (@cast_perm m n eq_m_n).
Proof using. move=> s /=; rewrite -{1}(esymK eq_m_n); exact: cast_permK. Qed.

Lemma cast_perm_inj m n eq_m_n : injective (@cast_perm m n eq_m_n).
Proof using. exact: can_inj (cast_permK eq_m_n). Qed.

Lemma cast_perm_morphM m n eq_m_n :
  {morph @cast_perm m n eq_m_n : x y / x * y >-> x * y}.
Proof using.
rewrite /cast_perm => /= s1 s2; apply /permP => /= i.
apply val_inj => /=.
by rewrite permM /= !permE /cast_perm_val cast_ordK permM.
Qed.
Canonical morph_of_cast_perm m n eq_m_n :=
  Morphism (D := setT) (in2W (@cast_perm_morphM m n eq_m_n)).

Lemma isom_cast_perm m n eq_m_n : isom setT setT (@cast_perm m n eq_m_n).
Proof using.
apply/isomP; split.
- apply/injmP=> i j _ _; exact: cast_perm_inj.
- apply/setP => /= s; rewrite inE.
  apply/imsetP; exists (cast_perm (esym eq_m_n) s); first by rewrite !inE.
  by rewrite /= cast_permKV.
Qed.

End CastSn.

Section PermComp.

Variable T : finType.
Variables (R : Type) (idx : R) (op : R -> R -> R) (F : T -> R).
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
  y \in pcycle s x -> exists2 i, i < (#[s])%g & y = (s ^+ i)%g x.
Proof using. by move=> /imsetP [z /cyclePmin[ i Hi ->{z}] ->{y}]; exists i. Qed.

Lemma pcycleP s x y :
  reflect (exists i, y = (s ^+ i)%g x) (y \in pcycle s x).
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