(** * WalkMaze.v: An example of probabilistic termination
      related to Vacid0 example of Maze construction
*)

(* begin hide *)
Add Rec LoadPath "../src" as ALEA.

Require Export AbstractWalk.
Set Implicit Arguments.
Open Local Scope U_scope.
Open Local Scope O_scope.
(* end hide *)

Definition point := (nat * nat)%type.
Inductive orient := Right | Up.

Record edge := mk_edge {src:point; dir:orient}.

Definition right (p:point) := let (x,y) := p in (S x,y).
Definition up (p:point) := let (x,y) := p in (x,S y).

Definition in_grid (n:nat) (p:point) :Prop := 
      (fst p <= n /\ snd p <=n)%nat.

Definition decomp (e:edge) : point * point 
     := let (p,d):= e in (p,match d with Right => right p | Up => up p end).

Definition dst (e:edge) : point 
   := match dir e with Right => right (src e) | Up => up (src e) end.

Definition pick_point (n:nat)  : distr point := 
    Mlet (Random n) (fun x => Mlet (Random n) (fun y => Munit (x,y))).

(*
Definition pick_next (p:point) : distr point 
   := Mif Flip (Munit (right p)) (Munit (up p)).

Definition pick_edge n : distr edge 
   := Mlet (pick_point n) (fun a => Mlet (pick_next a) (fun b => Munit (a,b))).
*)

Definition pick_edge (n:nat) : distr edge 
   := Mlet (pick_point n) 
           (fun p => Mif Flip (Munit (mk_edge p Right)) (Munit (mk_edge p Up))).

Definition Ueq_point (p q: point) : U :=
        carac_eq (fst p) (fst q) * carac_eq (snd p) (snd q).

Lemma cover_Ueq_point : forall (p:point),
     cover (fun q => p=q) (Ueq_point p).
intros (xp,yp); 
 apply cover_eqset_stable with (inter (fun q => xp = fst q) (fun q => yp = snd q)); simpl.
intros (xq,yq); unfold inter; simpl.
intuition.
injection H; auto.
injection H; auto.
apply cover_inter_mult; auto.
intro q; exact (is_eq xp (fst q)).
intro q; exact (is_eq yp (snd q)).
Save.
Hint Resolve cover_Ueq_point.

Definition Ueq_dir (d1 d2:orient) := 
  match d1,d2 with Right, Right => 1 | Up, Up =>1 | _,_ => 0 end.

Lemma cover_Ueq_dir : forall (d:orient),
     cover (fun d' => d=d') (Ueq_dir d).
unfold Ueq_dir; destruct d; intro d'; case d'; split; simpl; 
   intros; try discriminate; auto.
case H; auto.
case H; auto.
Save.


Definition Ueq_edge (a b:edge) : U :=
           Ueq_point (src a) (src b) * Ueq_dir (dir a) (dir b).

Lemma cover_Ueq_edge : forall (p:edge),
      cover (fun q => p=q) (Ueq_edge p).
unfold Ueq_edge; intros (p,d); 
 apply cover_eqset_stable with (inter (fun e => p = src e) (fun e => d = dir e)); 
        simpl.
intros (q,d'); unfold inter; simpl.
intuition.
subst; auto.
injection H; auto.
injection H; auto.
apply cover_inter_mult; auto.
intro e; exact (cover_Ueq_point p (src e)).
intro e; exact (cover_Ueq_dir d (dir e)).
Save.

Definition Uin_grid (n:nat) (p:point) : U := 
      carac_le n (fst p) * carac_le n (snd p).


Lemma cover_in_grid : forall (n:nat), cover (in_grid n) (Uin_grid n).
unfold Uin_grid,in_grid; intro n.
apply cover_inter_mult; auto.
intro p; exact (is_le n (fst p)).
intro p; exact (is_le n (snd p)).
Save.

Lemma pick_point_val : 
  forall n p, in_grid n p 
  -> mu (pick_point n) (Ueq_point p) == ([1/]1+n) * ([1/]1+n).
unfold pick_point,Ueq_point,in_grid; intros n (x,y).
simpl @fst; simpl @snd; intros (H1,H2).
rewrite Mlet_simpl.
transitivity 
(mu (Random n)
  (fun x0 : nat =>
    mu (Random n) (fun y0 : nat => 
        carac_eq x (fst (x0,y0)) * carac_eq y (snd (x0,y0))))).
apply mu_eq_compat; auto.
simpl @fst; simpl @snd.
rewrite <- fmult_def.
setoid_rewrite (mu_stable_mult (Random n)).
setoid_rewrite Umult_sym.
setoid_rewrite <- fmult_def.
setoid_rewrite (mu_stable_mult (Random n)).
repeat setoid_rewrite (@Random_eq n); auto.
Save.

Lemma in_grid_src : forall n e, in_grid n (dst e) -> in_grid n (src e).
unfold in_grid,dst; intros n ((x,y),[|]); simpl; intuition.
Save.

Lemma pick_edge_val : 
  forall n e, in_grid n (src e)
  -> mu (pick_edge n) (Ueq_edge e) == [1/2] * ([1/]1+n) * ([1/]1+n).
unfold Ueq_edge,pick_edge; intros n (p,[|]); simpl @src; simpl @dir.
intro H.
setoid_rewrite Mlet_simpl.
setoid_rewrite Mif_eq.
setoid_rewrite Flip_true.
setoid_rewrite Flip_false.
transitivity (mu (pick_point n)
  (fun x : point =>
   (Ueq_point p x * Ueq_dir Right Right) * 
   [1/2] +
   (Ueq_point p x * Ueq_dir Right Up) * 
   [1/2])); auto.
simpl Ueq_dir.
transitivity 
  (mu (pick_point n)
  (fun x : point => Ueq_point p x * [1/2])).
apply mu_eq_compat; trivial.
intro x; repeat Usimpl; auto.
rewrite mu_stable_mult_right.
rewrite pick_point_val; auto.
rewrite <- Umult_assoc.
rewrite (Umult_sym [1/2]); auto.

intro H.
setoid_rewrite Mlet_simpl.
setoid_rewrite Mif_eq.
setoid_rewrite Flip_true.
setoid_rewrite Flip_false.
transitivity (mu (pick_point n)
  (fun x : point =>
   (Ueq_point p x * Ueq_dir Up Right) * 
   [1/2] +
   (Ueq_point p x * Ueq_dir Up Up) * 
   [1/2])); auto.
simpl Ueq_dir.
transitivity 
  (mu (pick_point n)
  (fun x : point => Ueq_point p x * [1/2])).
apply mu_eq_compat; trivial.
intro x; repeat Usimpl; auto.
rewrite mu_stable_mult_right.
rewrite pick_point_val; auto.
rewrite <- Umult_assoc.
rewrite (Umult_sym [1/2]); auto.
Save.

Variable UF : Type.
Variable nbclass : UF -> nat.
Variable same : UF -> point -> point -> bool.
Variable merge : UF -> point -> point -> UF.
Variable n : nat.
Variable init_grid : UF.

Definition in_uf uf p := same uf p p = true.

Hypothesis nbclass_not_zero : 
   forall u, nbclass u <> O -> exists p : point, exists q:point,
             in_uf u p /\ in_uf u q /\ same u p q = false.

Hypothesis nbclass_merge : 
   forall u p q, in_uf u p -> in_uf u q -> same u p q = false 
   -> nbclass u = S (nbclass (merge u p q)).
Hint Resolve nbclass_merge.

Hypothesis same_init : 
   forall p q, same init_grid p q = true <-> p=q /\ in_grid n p.

Hypothesis same_sym : forall uf p q, same uf p q = same uf q p.

Hypothesis same_trans : forall uf p q r, 
   same uf p q = true -> same uf q r = true -> same uf p r = true.

Hypothesis same_merge : forall uf p q r s, 
   same (merge uf p q) r s = true <-> 
      same uf r s = true \/ (same uf r p = true /\ same uf s q = true)
    \/ (same uf r q = true /\ same uf s p = true).

Lemma nbclass_zero : 
   forall u, nbclass u = O -> forall p q,
             in_uf u p -> in_uf u q -> same u p q = true.
intros; case_eq (same u p q); auto; intro.
absurd (O=S(nbclass (merge u p q))); auto.
rewrite <- H; auto.
Save.

Inductive path (m:list edge) (o:point) : point -> Prop := 
    path_refl : path m o o
  | path_add_dir : forall e, List.In e m 
         -> path m o (src e) -> path m o (dst e)
  | path_add_rev : forall e, List.In e m 
         -> path m o (dst e) -> path m o (src e).
Hint Constructors path.

Lemma path_trans : forall m p q r,
   path m p q -> path m q r -> path m p r.
induction 2; intros; auto.
Save.

Lemma path_edge_dir : forall m e, List.In e m -> path m (src e) (dst e).
auto.
Save.

Lemma path_edge_rev : forall m e, List.In e m -> path m (dst e) (src e).
auto.
Save.
Hint Resolve path_edge_dir path_edge_rev.

Lemma path_sym : forall m p q, path m p q -> path m q p.
induction 1; auto.
apply path_trans with (src e); auto.
apply path_trans with (dst e); auto.
Save.
Hint Immediate path_sym.

Lemma path_incl : forall m1 m2 p q, (forall e, List.In e m1 -> List.In e m2) 
    -> path m1 p q -> path m2 p q.
induction 2; intros; auto.
Save.

Lemma path_cons : forall e m p q, path m p q -> path (e::m) p q.
intros; apply path_incl with m; simpl; auto.
Save.
Hint Immediate path_cons.

Lemma path_edge_cons_dir : forall e m, path (e::m) (src e) (dst e).
intros; apply path_edge_dir; simpl; auto.
Save.
Hint Resolve path_edge_cons_dir.

Lemma path_edge_cons_rev : forall e m, path (e::m) (dst e) (src e).
intros; apply path_edge_rev; simpl; auto.
Save.
Hint Resolve path_edge_cons_rev.

Definition inv (uf : UF) (maze : list edge) := forall p q, 
   same uf p q = true -> path maze p q.

Definition all (uf : UF) := forall p, in_grid n p <-> in_uf uf p.

Record Input := mki {uf : UF; maze : list edge; span : inv uf maze; coh : all uf}.

Definition input0 : Input.
exists init_grid nil.
intros p q Hs.
rewrite same_init in Hs.
destruct Hs as (Heq,(_,_)); subst; auto.
split; unfold in_uf; rewrite same_init; intuition.
Defined.

Definition step (i:Input) (e:edge) : Input.
exists (merge (uf i) (src e) (dst e)) (e::maze i).
intros p q Hs. 
rewrite same_merge in Hs.
destruct i as (uf,maze,span,coh); simpl in *.
destruct Hs as [H0|[(H1,H2)|(H1,H2)]]; auto.
apply path_incl with maze; simpl; auto.
apply path_trans with (src e); simpl.
apply path_incl with maze; simpl; auto.
apply path_trans with (dst e); simpl; auto.
apply path_incl with maze; simpl; auto.
apply path_sym; auto.
apply path_trans with (dst e); simpl.
apply path_incl with maze; simpl; auto.
apply path_trans with (src e); simpl; auto.
apply path_incl with maze; simpl; auto.
apply path_sym; auto.
destruct i as (uf,maze,span,coh); simpl in *.
split; unfold in_uf; rewrite same_merge; intros.
left; apply coh; trivial.
assert (same uf p p = true).
destruct H as [H0|[(H1,H2)|(H1,H2)]]; auto.
apply same_trans with (src e); auto.
rewrite same_sym; auto.
apply same_trans with (dst e); auto.
rewrite same_sym; auto.
apply coh; trivial.
Defined.

Lemma uf_step_eq (i:Input) (e:edge) : uf (step i e) = merge (uf i) (src e) (dst e).
trivial.
Save.

Definition Data := edge.
Definition Result := list edge.
Definition size : Input -> nat := fun i => nbclass (uf i).
Definition output : Input -> Result := fun i => maze i.

Definition finished (i:Input) := match (size i) with 0 => true | _ => false end.

(** Iteration with the same step when the edge is already covered with a path 
    or outside the grid *)

Definition cond (i:Input) (d:Data) := 
           if same (uf i) (src d) (dst d) then true else 
           if same (uf i) (dst d) (dst d) then false else true.

Lemma cond_false (i:Input) (d:Data) :
   cond i d = false -> same (uf i) (src d) (dst d) = false /\ same (uf i) (dst d) (dst d) = true.
unfold cond; destruct (same (uf i) (src d) (dst d)); try discriminate.
destruct (same (uf i) (dst d) (dst d)); try discriminate; auto.
Save.

Lemma finished_size : forall u, size u = O -> finished u = true.
intros u Heq; unfold finished; rewrite Heq; auto.
Save.

(** When not finished, there exists at least one edge between two components
    this edge will not satisfy the condition *)

Variable alledges : list edge.
Hypothesis inalledges : forall e, List.In e alledges <-> in_grid n (src e) /\ in_grid n (dst e).

Hypothesis connected : forall p q, in_grid n p -> in_grid n q -> path alledges p q.

Lemma one_ok (uf : UF) (coh : all uf): 
  nbclass uf <> O -> 
  (exists e : edge, List.In e alledges /\ same uf (src e) (dst e) = false).
intros Hnb.
destruct (nbclass_not_zero Hnb) as (p,(q,(H1,(H2,H3)))).
assert (Hip:in_grid n p).
rewrite (coh p); trivial.
assert (Hiq:in_grid n q).
rewrite (coh q); trivial.
(* when there is a path from p and q in different components, 
   then there is an edge across components, by induction on the path *)
generalize (connected Hip Hiq) H3.
clear H2 H3 Hiq. 
intro Hp; elim Hp.
(* empty path *)
red in H1; intros H2; rewrite H2 in H1; discriminate.
(* a path followed by an edge e in direct sense *)
intros e He Hpath IHpath H2.
case_eq (same uf p (src e)); intro.
exists e; repeat split; auto.
case_eq (same uf (src e) (dst e)); intros; auto.
assert (contr:same uf p (dst e) = true).
apply same_trans with (src e); auto.
rewrite H2 in contr; discriminate.
apply IHpath; auto.
(* a path followed by an edge e in reverse sense *)
intros e He Hpath IHpath H2.
case_eq (same uf p (dst e)); intro.
exists e; repeat split; auto.
case_eq (same uf (src e) (dst e)); intros; auto.
assert (contr:same uf p (src e) = true).
apply same_trans with (dst e); auto.
rewrite same_sym; auto.
rewrite H2 in contr; discriminate.
apply IHpath; auto.
Save.

Lemma edge_cond : forall e (i:Input), 
     List.In e alledges -> same (uf i) (src e) (dst e) = false
                        -> cond i e = false.
unfold cond; intros.
rewrite H0.
replace (same (uf i) (dst e) (dst e)) with true; auto.
symmetry.
rewrite <- (coh i (dst e)).
rewrite (inalledges e) in H.
intuition.
Save.


(** Proof that the size decreases, when a step is taken *)

Lemma size_step : forall (u:Input) (x:Data), 
   finished u = false -> cond u x = false -> (size (step u x) < size u)%nat.
intros; unfold size; rewrite uf_step_eq.
destruct (cond_false u x H0).
rewrite nbclass_merge with (uf u) (src x) (dst x); auto.
apply (coh u).
apply in_grid_src; auto.
apply (coh u); auto.
Save.

Section AbstractMaze.

(* ** Maze with an abstract distribution for choosing edges *)

Variable dedge : distr edge.
Hypothesis dedge_term : mu dedge (fun d => 1) == 1.
Variable p : U.
Hypothesis pnot0 : 0 < p.
Hypothesis pick_one_p :
  forall n e, in_grid n (src e) -> p <= mu dedge (Ueq_edge e).

(** Instantiating the abstract walk scheme *)

Definition dData : distr Data := dedge.

Definition maze_prog := AbstractWalk.iter dData finished output cond.

Definition k := [1-]p.
Lemma knot1 : k < 1.
unfold k; auto.
Save.

Lemma d_true_bounded 
    : forall i, finished i = false -> mu dData (fun d => B2U (cond i d)) <= k.
intros.
rewrite mu_stable_inv_inv.
unfold k; Usimpl.
destruct (@one_ok (uf i) (coh i)) as (e,(He1,He2)).
unfold finished, size in H.
destruct (nbclass (uf i)) ; try discriminate; omega.
transitivity (mu dData (Ueq_edge e)).
apply (@pick_one_p n e).
rewrite inalledges in He1; intuition.
apply mu_le_compat; trivial; intro d.
apply cover_incl_le with (fun p => e=p) (compl (fun p => cond i p = true)); auto.
apply cover_Ueq_edge.
apply cover_compl.
apply cover_bool.
intro f; unfold compl; intro; subst.
rewrite (edge_cond f i); auto.
Save.

End AbstractMaze.


