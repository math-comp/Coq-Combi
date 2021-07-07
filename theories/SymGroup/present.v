(** * Group Presentations *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finset finfun.
From mathcomp Require Import bigop fingroup perm morphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GroupScope.

Section Satisfy.

Variable (gT : finGroupType) (n : nat).
Implicit Type (gens : 'I_n -> gT) (rels : seq (seq 'I_n)).

Definition satisfy rels gens :=
  all (fun s : seq 'I_n => \prod_(i <- s) gens i == 1) rels.

Lemma satisfyP rels gens :
  reflect (forall s : seq 'I_n, s \in rels -> \prod_(i <- s) gens i = 1)
          (satisfy rels gens).
Proof. by apply: (iffP allP) => /= [H s /H /eqP| H s /H ->]. Qed.

Lemma satisfy_eq gens1 gens2 rels :
  gens1 =1 gens2 -> satisfy rels gens1 = satisfy rels gens2.
Proof.
by move=> Heq; apply/satisfyP/satisfyP => /= H s /H {2}<-; apply eq_bigr => i _.
Qed.

Lemma perm_satisfy rels1 rels2 gens :
  perm_eq rels1 rels2 -> satisfy rels1 gens = satisfy rels2 gens.
Proof. by rewrite/satisfy => /perm_all ->. Qed.

Lemma satisfy_perm_impl (p : 'S_n) rels gens :
  satisfy rels gens ->
  satisfy [seq [seq p^-1 i | i <- r] | r <- rels] (gens \o p).
Proof.
move/satisfyP => H; apply/satisfyP => s' /mapP [/= s {}/H {2}<- ->{s'}].
by rewrite big_map; apply: eq_bigr => i _; rewrite permKV.
Qed.

Lemma satisfy_perm (p : 'S_n) rels gens :
  satisfy rels gens = satisfy [seq [seq p^-1 i | i <- r] | r <- rels] (gens \o p).
Proof.
apply/idP/idP => /satisfy_perm_impl // /(_ p^-1).
have /satisfy_eq -> : ((gens \o p) \o p^-1) =1 gens.
  by move=> i /=; rewrite permKV.
congr satisfy.
rewrite -map_comp -[RHS]map_id; apply eq_map => s /=.
rewrite -map_comp -[RHS]map_id; apply eq_map => i /=.
by rewrite permK.
Qed.

End Satisfy.

Lemma satisfy_morph (gT : finGroupType) (G : {group gT})
                    (hT : finGroupType) (H : {group hT})
      (f : {morphism G >-> hT}) m (gens : 'I_m -> gT) rels :
  (forall i, gens i \in G) -> satisfy rels gens -> satisfy rels (f \o gens).
Proof.
move=> memgens /satisfyP /= sat; apply/satisfyP => s {}/sat /(congr1 f).
by rewrite morph1 => mor; rewrite -{}[RHS]mor morph_prod.
Qed.



Record presentation
       (gT : finGroupType)
       (n : nat) (gr : ('I_n -> gT) * (seq (seq 'I_n)))
       (G : {group gT}) : Prop := Presentation {
  gen_eq : <<[set gr.1 i | i : 'I_n]>> = G;
  satisfy_gens : satisfy gr.2 gr.1;
  presm_ex : forall (hT : finGroupType) (gensh : 'I_n -> hT),
      satisfy gr.2 gensh ->
      exists presm : {morphism G >-> hT}, forall i, presm (gr.1 i) = gensh i
}.

Notation "gr \present G" := (presentation gr G) (at level 10).

Section Presentation.

Variables (gT : finGroupType) (G : {group gT})
          (n : nat) (gens  : 'I_n -> gT) (rels  : seq (seq 'I_n)).
Hypothesis pres : (gens, rels) \present G.

Lemma pres_mem  i : gens i \in G.
Proof.
case: pres => [eqG /= _ _]; rewrite -{}eqG.
exact/mem_gen/imset_f.
Qed.
Hint Resolve pres_mem : core.

Lemma presP x :
  reflect (exists l, exists c : 'I_l -> 'I_n, x = \prod_i gens (c i))
          (x \in G).
Proof.
apply (iffP idP); first last.
  by move=> [l [dec ->{x}]]; apply group_prod.
rewrite -{1}(gen_eq pres) => /gen_prodgP [l [dec Hdec ->{x}]].
have {}Hdec i : {j : 'I_n | dec i == gens j}.
  by apply sigW => /=; move: Hdec => /(_ i) /imsetP [/= j _ ->]; exists j.
have dec_in i : dec i \in G by case: (Hdec i) => j /eqP ->.
pose get_gen (i : 'I_l) := let: exist j _ := Hdec i in j.
have decE i : dec i = gens (get_gen i).
  by rewrite /get_gen; case: (Hdec i) => j /eqP.
by exists l, get_gen; apply eq_bigr.
Qed.


Section PresMorphism.

Variable (hT : finGroupType) (gensH : 'I_n -> hT).
Hypothesis (sat : satisfy rels gensH).

Lemma presm_spec :
  {presm : {morphism G >-> hT} | forall i, presm (gens i) = gensH i}.
Proof.
suff : {m : {ffun gT -> hT} | morphic G m && [forall i, m (gens i) == gensH i]}.
  move=> [m /andP [morm /forallP /= Heq]].
  by exists (morphm_morphism morm) => /= i; rewrite morphmE; apply/eqP.
apply sigW; case: (presm_ex pres sat) => [m Heq] /=.
exists (finfun m); apply/andP; split.
  by apply/morphicP => x y xG yG /=; rewrite !ffunE morphM.
by apply/forallP => /= i; rewrite ffunE Heq.
Qed.
Definition presm := let: exist m _ := presm_spec in m.
Lemma presmP : forall i, presm (gens i) = gensH i.
Proof. by rewrite /presm; case: presm_spec. Qed.

Lemma presmE (phi : {morphism G >-> hT}) :
  (forall i, phi (gens i) = gensH i) -> {in G, phi =1 presm}.
Proof.
move=> Heq x /presP [l [decc ->{x}]].
rewrite !morph_prod //.
by apply: eq_bigr => /= i _; rewrite Heq presmP.
Qed.

Lemma morphim_presm : presm @* G = <<[set gensH i | i : 'I_n]>>.
Proof.
apply/setP => /= h; apply/imsetP/gen_prodgP; rewrite setIid.
- move=> [g /(presP) [l [dec ->{g} ->{h}]]]; exists l.
  exists (gensH \o dec); first by move=> i /=; apply: imset_f.
  rewrite morph_prod //.
  by apply: eq_bigr => /= i _; rewrite presmP.
- move=> [l [dec Hdec ->{h}]].
  have {}Hdec i : {j : 'I_n | dec i == gensH j}.
    by apply sigW => /=; move: Hdec => /(_ i) /imsetP [/= j _ ->]; exists j.
  pose get_gen (i : 'I_l) := let: exist j _ := Hdec i in gens j.
  have get_in i : get_gen i \in G by rewrite /get_gen; case: (Hdec i).
  have getE i : dec i = presm (get_gen i).
    by rewrite /get_gen; case: (Hdec i) => j /eqP ->; rewrite presmP.
  exists (\prod_(i < l) get_gen i); first by apply: group_prod => /= i _.
  by rewrite morph_prod //; apply eq_bigr => /= i _.
Qed.

End PresMorphism.

End Presentation.


Section Isomorphism.

Variable gT hT : finGroupType.
Variables (G : {group gT}) (H : {group hT}).
Variables (n : nat) (gens  : 'I_n -> gT) (rels  : seq (seq 'I_n)).
Hypothesis (prG : (gens, rels) \present G).

Lemma presm_id (sat : satisfy rels gens) :
  {in G, presm prG sat =1 id}.
Proof.
have : forall i, idm G (gens i) = (gens i) by [].
by move/(presmE prG sat) => Heq x /Heq.
Qed.

Lemma pres_isog (gh : 'I_n -> hT) : (gh, rels) \present H -> G \isog H.
Proof.
move=> prH; apply/isogP.
have satH := satisfy_gens prH.
have satG := satisfy_gens prG.
have:= morphim_presm prG satH; rewrite (gen_eq prH) => impH.
have phi_morph : morphic G (presm prH satG \o presm prG satH).
  apply/morphicP => x y xinG yinG.
  by rewrite /= !morphM // -impH mem_morphim.
have : forall i, morphm phi_morph (gens i) = gens i.
  by move=> i; rewrite morphmE /= !presmP.
move=> /(presmE prG (satisfy_gens prG)) presmP.
have {presmP} presmK : {in G, cancel (presm prG satH) (presm prH satG)}.
  by move => x Hx; move: presmP => /(_ x Hx) /=; rewrite presm_id.
exists (presm prG satH) => //.
exact/injmP/(can_in_inj presmK).
Qed.

Lemma isog_pres :
  G \isog H -> {gensh: 'I_n -> hT | (gensh, rels) \present H}.
Proof.
move=> /isog_isom [f /isomP [injf imf]].
have prmemG := pres_mem prG.
have subgen : [set gens i | i : 'I_n] \subset G.
  by apply/subsetP => x /imsetP [/= j _ ->].
exists (f \o gens); constructor.
- rewrite -{}imf -{4}(gen_eq prG) morphim_gen //.
  by congr << _ >>; rewrite morphimEsub // -imset_comp.
- apply/satisfyP => s Hs.
  have:= satisfy_gens prG => /satisfyP/(_ _ Hs)/(congr1 f).
  by rewrite morph1 morph_prod.
move=> aT gensA sat.
pose phi := presm prG sat \o invm injf.
have phi_morph : {in H & , {morph phi : x y / x * y}}.
  have inmG x : x \in H -> invm injf x \in G.
    move=> Hx; rewrite -(im_invm injf) {2}imf.
    by apply: mem_morphim; rewrite //= imf.
  move=> x y xinG yinG.
  by rewrite /phi /= !morphM ?imf //= inmG.
exists (Morphism phi_morph) => i /=.
by rewrite /= /phi /= invmE ?(pres_mem prG) // presmP.
Qed.

End Isomorphism.
