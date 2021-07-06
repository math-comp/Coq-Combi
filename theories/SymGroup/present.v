(** * The presentation of Groups *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finset.
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


Section Presentation.

Variables (gT : finGroupType) .

Record presentation (n : nat) (G : {group gT}) := Presentation {
  gens  : 'I_n -> gT;
  rels  : seq (seq 'I_n);
  _     : <<[set gens i | i : 'I_n]>> = G;
  _     : satisfy rels gens;
  presm : forall (hT : finGroupType) (gensh : 'I_n -> hT),
      satisfy rels gensh -> {morphism G >-> hT};
  _     : forall (hT : finGroupType) (gensh : 'I_n -> hT)
                (sat : satisfy rels gensh) i, presm sat (gens i) = gensh i;
}.

Variables (G : {group gT}) (n : nat) (pres : presentation n G).

Lemma pres_mem  i : gens pres i \in G.
Proof.
case: pres => [g r eqG /= _ _ _]; rewrite -{}eqG.
exact/mem_gen/imset_f.
Qed.
Hint Resolve pres_mem : core.

Lemma gen_eq : <<[set gens pres i | i : 'I_n]>> = G.
Proof. by case: pres. Qed.
Lemma satisfy_gens : satisfy (rels pres) (gens pres).
Proof. by case: pres. Qed.

Lemma presP x :
  reflect (exists l, exists c : 'I_l -> 'I_n, x = \prod_i gens pres (c i))
          (x \in G).
Proof.
apply (iffP idP); first last.
  by move=> [l [dec ->{x}]]; apply group_prod.
rewrite -{1}gen_eq => /gen_prodgP [l [dec Hdec ->{x}]].
have {}Hdec i : {j : 'I_n | dec i == gens pres j}.
  by apply sigW => /=; move: Hdec => /(_ i) /imsetP [/= j _ ->]; exists j.
have dec_in i : dec i \in G by case: (Hdec i) => j /eqP ->.
pose get_gen (i : 'I_l) := let: exist j _ := Hdec i in j.
have decE i : dec i = gens pres (get_gen i).
  by rewrite /get_gen; case: (Hdec i) => j /eqP.
by exists l, get_gen; apply eq_bigr.
Qed.

Variables (hT : finGroupType)
          (gensH : 'I_n -> hT)
          (sat : satisfy (rels pres) gensH).

Lemma presmP : forall i, presm sat (gens pres i) = gensH i.
Proof. by case: pres sat. Qed.

Lemma presmE (phi : {morphism G >-> hT}) :
  (forall i, phi (gens pres i) = gensH i) -> {in G, phi =1 presm sat}.
Proof.
move=> Heq x /presP [l [decc ->{x}]].
rewrite !morph_prod //.
by apply: eq_bigr => /= i _; rewrite Heq presmP.
Qed.

Lemma morphim_presm : presm sat @* G = << [set gensH i | i : 'I_n] >>.
Proof.
apply/setP => /= h; apply/imsetP/gen_prodgP; rewrite setIid.
- move=> [g /(presP) [l [dec ->{g} ->{h}]]]; exists l.
  exists (gensH \o dec); first by move=> i /=; apply: imset_f.
  rewrite morph_prod //.
  by apply: eq_bigr => /= i _; rewrite presmP.
- move=> [l [dec Hdec ->{h}]].
  have {}Hdec i : {j : 'I_n | dec i == gensH j}.
    by apply sigW => /=; move: Hdec => /(_ i) /imsetP [/= j _ ->]; exists j.
  pose get_gen (i : 'I_l) := let: exist j _ := Hdec i in gens pres j.
  have get_in i : get_gen i \in G by rewrite /get_gen; case: (Hdec i).
  have getE i : dec i = presm sat (get_gen i).
    by rewrite /get_gen; case: (Hdec i) => j /eqP ->; rewrite presmP.
  exists (\prod_(i < l) get_gen i); first by apply: group_prod => /= i _.
  by rewrite morph_prod //; apply eq_bigr => /= i _.
Qed.

End Presentation.


Section Morph.

Variable gT hT : finGroupType.
Variables (G : {group gT}) (H : {group hT}).
Variables (n : nat) (prG : presentation n G).

Lemma presm_id (sat : satisfy (rels prG) (gens prG)) :
  {in G, presm sat =1 id}.
Proof.
have : forall i, idm G (gens prG i) = (gens prG i) by [].
by move/(presmE sat) => Heq x /Heq.
Qed.

Lemma pres_isog (prH : presentation n H) : rels prG = rels prH -> G \isog H.
Proof.
move=> Hrel; apply/isogP.
have:= satisfy_gens prH; rewrite -Hrel => satH.
have:= satisfy_gens prG; rewrite  Hrel => satG.
have:= morphim_presm satH; rewrite gen_eq => impH.
have phi_morph : morphic G (presm satG \o presm satH).
  apply/morphicP => x y xinG yinG.
  by rewrite /= !morphM // -impH mem_morphim.
have : forall i, morphm phi_morph (gens prG i) = gens prG i.
  by move=> i; rewrite morphmE /= !presmP.
move=> /(presmE (satisfy_gens prG)) presmP.
have {presmP} presmK : {in G, cancel (presm satH) (presm satG)}.
  by move => x Hx; move: presmP => /(_ x Hx) /=; rewrite presm_id.
exists (presm satH) => //.
exact/injmP/(can_in_inj presmK).
Qed.

Section BuildPresM.

Variable (f : {morphism G >-> hT}).
Hypotheses (injf : 'injm f) (imf : f @* G = H).
Variables (aT : finGroupType)
          (gensh : 'I_n -> aT)
          (sat : satisfy (rels prG) gensh).

Local Definition phi := presm sat \o invm injf.
Local Fact phi_morph : {in H & , {morph phi : x y / x * y}}.
Proof.
have inmG x : x \in H -> invm injf x \in G.
  move=> Hx; rewrite -(im_invm injf) {2}imf.
  by apply: mem_morphim; rewrite //= imf.
move=> x y xinG yinG.
by rewrite /phi /= !morphM ?imf //= inmG.
Qed.
Local Canonical phi_morph_morphism := Morphism phi_morph.

Local Lemma phi_morphP i : phi_morph_morphism ((f \o (gens prG)) i) = gensh i.
Proof. by rewrite /= /phi /= invmE ?(pres_mem prG) // presmP. Qed.

End BuildPresM.

Lemma isog_pres :
  G \isog H -> exists (prH : presentation n H), rels prG = rels prH.
Proof.
move=> /isogP [f injf imf].
have prmemG := pres_mem prG.
have subgen : [set gens prG i | i : 'I_n] \subset G.
  by apply/subsetP => x /imsetP [/= j _ ->].
pose gh := f \o (gens prG).
have Hgen : <<[set gh i | i : 'I_n]>> = H.
  rewrite -{}imf -{3}(gen_eq prG) morphim_gen //.
  by congr << _ >>; rewrite morphimEsub // -imset_comp.
have Hsat : satisfy (rels prG) gh.
  apply/satisfyP => s Hs.
  have:= satisfy_gens prG => /satisfyP/(_ _ Hs)/(congr1 f).
  by rewrite morph1 morph_prod.
by exists (Presentation Hgen Hsat (phi_morphP injf imf)).
Qed.

End Morph.
