(** * Prog_Intervals.v: Rules for distributions and intervals *)

Add Rec LoadPath "." as ALEA.

Require Export Prog.
Require Export Intervals.

(* Module Rules (Univ:Universe). *)
(* Module PP := (Proba Univ). *)
(* Import Univ. *)
(* Import PP MP UP. *)

(* begin hide *)
Set Implicit Arguments.
Open Local Scope U_scope.
Open Local Scope O_scope.
(* end hide *)

(** Distributions operates on intervals *)

Definition Imu : forall A:Type, distr A ->  (A -> IU) -> IU.
intros A m F; exists (mu m (fun x => low (F x))) (mu m (fun x => up (F x))).
apply mu_monotonic; auto.
Defined.

Lemma low_Imu : forall (A:Type) (e:distr A) (F: A -> IU),
             low (Imu e F) = mu e (fun x => low (F x)).
trivial.
Save.

Lemma up_Imu : forall (A:Type) (e:distr A) (F: A -> IU),
             up (Imu e F) = mu e (fun x => up (F x)).
trivial.
Save.

Lemma Imu_monotonic : forall (A:Type) (e:distr A) (F G : A -> IU),
            (forall x, Iincl (F x) (G x)) -> Iincl (Imu e F) (Imu e G).
unfold Iincl,Imu; simpl; intuition.
apply (mu_monotonic e); intro x; case (H x); auto.
apply (mu_monotonic e); intro x; case (H x); auto.
Save.

Lemma Imu_stable_eq : forall (A:Type) (e:distr A) (F G : A -> IU),
            (forall x, Ieq (F x) (G x)) -> Ieq (Imu e F) (Imu e G).
unfold Ieq,Imu; simpl; intuition.
apply (mu_stable_eq e); intro x; case (H x); auto.
apply (mu_stable_eq e); intro x; case (H x); auto.
Save.
Hint Resolve Imu_monotonic Imu_stable_eq.

Lemma Imu_singl : forall (A:Type) (e:distr A) (f:A -> U),
           Ieq (Imu e (fun x => singl (f x))) (singl (mu e f)).
unfold Ieq,Imu,singl; simpl; intuition.
Save.

Lemma Imu_inf : forall (A:Type) (e:distr A) (f:A -> U),
           Ieq (Imu e (fun x => inf (f x))) (inf (mu e f)).
unfold Ieq,Imu,inf; simpl; intuition.
Save.

Lemma Imu_sup : forall (A:Type) (e:distr A) (f:A -> U),
           Iincl (Imu e (fun x => sup (f x))) (sup (mu e f)).
unfold Iincl,Imu,inf; simpl; intuition.
Save.

Lemma Iin_mu_Imu :
   forall (A:Type) (e:distr A) (F:A -> IU) (f:A -> U),
           (forall x, Iin (f x) (F x)) -> Iin (mu e f) (Imu e F).
unfold Iin,Imu; simpl; split.
apply (mu_monotonic e); intro x; case (H x); auto.
apply (mu_monotonic e); intro x; case (H x); auto.
Save.
Hint Resolve Iin_mu_Imu.

Definition Iok (A:Type) (I:IU) (e:distr A) (F:A -> IU) := Iincl (Imu e F) I.
Definition Iokfun (A B:Type)(I:A -> IU) (e:A -> distr B) (F:A -> B -> IU)
               := forall x, Iok (I x) (e x) (F x).

Lemma Iin_mu_Iok :
   forall (A:Type) (I:IU) (e:distr A) (F:A -> IU) (f:A -> U),
           (forall x, Iin (f x) (F x)) -> Iok I e F -> Iin (mu e f) I.
intros; apply Iincl_in with (Imu e F); auto.
Save.


(** *** Stability *)
Lemma Iok_le_compat : forall (A:Type) (I J:IU) (e:distr A) (F G:A -> IU),
   Iincl I J -> (forall x, Iincl (G x) (F x)) -> Iok I e F -> Iok J e G.
unfold Iok; intros; apply Iincl_trans with I; auto.
apply Iincl_trans with (Imu e F); auto.
Save.

Lemma Iokfun_le_compat : forall (A B:Type) (I J:A -> IU) (e:A -> distr B) (F G:A -> B -> IU),
   (forall x, Iincl (I x) (J x)) -> (forall x y, Iincl (G x y) (F x y)) -> Iokfun I e F -> Iokfun J e G.
unfold Iokfun; intros; apply Iok_le_compat with (I x) (F x); auto.
Save.

(** *** Rule for values *)

Lemma Iunit_eq : forall (A: Type) (a:A) (F:A -> IU), Ieq (Imu (Munit a) F) (F a).
intros; unfold Ieq,Imu,Munit; auto.
Save.


(** *** Rule for application *)

Lemma Ilet_eq : forall (A B : Type) (a:distr A) (f:A -> distr B)(I:IU)(G:B -> IU),
   Ieq (Imu (Mlet a f) G) (Imu a (fun x => Imu (f x) G)).
unfold Ieq,Imu,Mlet,Iincl; simpl; intuition.
Save.
Hint Resolve Ilet_eq.

Lemma Iapply_rule : forall (A B : Type) (a:distr A) (f:A -> distr B)(I:IU)(F:A -> IU)(G:B -> IU),
    Iok I a F -> Iokfun F f (fun x => G) -> Iok I (Mlet a f) G.
unfold Iokfun,Iok;intros.
apply Ieq_incl_trans with (Imu a (fun x => Imu (f x) G)); auto.
apply Iincl_trans with (Imu a F); auto.
Save.

(** *** Rule for abstraction *)
Lemma Ilambda_rule : forall (A B:Type)(f:A -> distr B)(F:A -> IU)(G:A -> B -> IU),
   (forall x:A, Iok (F x) (f x) (G x)) -> Iokfun F f G.
trivial.
Save.


(** *** Rule for conditional *)

Lemma Imu_Mif_eq : forall (A:Type)(b:distr bool)(f1 f2:distr A)(F:A -> IU),
 Ieq (Imu (Mif b f1 f2) F) (Iplus (Imultk (mu b B2U) (Imu f1 F)) (Imultk (mu b NB2U) (Imu f2 F))).
red; intros.
rewrite low_Imu; rewrite up_Imu.
repeat rewrite Mif_eq.
repeat rewrite low_Iplus; repeat rewrite low_Imultk.
repeat rewrite up_Iplus; repeat rewrite up_Imultk.
repeat rewrite low_Imu; repeat rewrite up_Imu; auto.
Save.

Lemma Iifrule :
  forall (A:Type)(b:(distr bool))(f1 f2:distr A)(I1 I2:IU)(F:A -> IU),
       Iok I1 f1 F -> Iok I2 f2 F
       -> Iok (Iplus (Imultk (mu b B2U) I1) (Imultk (mu b NB2U) I2)) (Mif b f1 f2) F.
unfold Iok; intros.
apply Ieq_incl_trans with (1:=Imu_Mif_eq b f1 f2 F).
split.
repeat rewrite low_Iplus; repeat rewrite low_Imultk.
apply Uplus_le_compat; auto.
repeat rewrite up_Iplus; repeat rewrite up_Imultk.
apply Uplus_le_compat; auto.
Save.

(** *** Rule for fixpoints
with [ phi x = F phi x ], [p] a decreasing sequence of intervals functions 
([ p (i+1) x ] is a bubset of [ (p i x) ] such that [ (p 0 x) ] contains [0] for all [x].

[ forall f i, (forall x, iok (p i x) f (q x)) => forall x, iok (p (i+1) x) (F f x) (q x) ]  implies [ forall x, iok (lub p x) (phi x) (q x) ] 
*)
Section IFixrule.
Variables A B : Type.

Variable F : (A -> distr B) -m> (A -> distr B).

Section IRuleseq.
Variable Q : A -> B -> IU.

Variable I : A -> nat -m> IU.

Lemma Ifixrule :
   (forall x:A, Iin 0 (I x O)) ->
   (forall (i:nat) (f:A -> distr B),
      (Iokfun (fun x => I x i) f Q) -> Iokfun (fun x => I x (S i))  (fun x => F f x) Q)
   -> Iokfun (fun x => Ilim (I x)) (Mfix F) Q.
red; intros p0 Hrec.
assert (forall n:nat,
        (Iokfun (fun x => (I x n)) (fun x => Miter F n x) Q)).
induction n; simpl; auto.
split.
rewrite low_lim; rewrite low_Imu.
apply lub_le; auto.
intro n; transitivity (low (Imu (Miter F n x) (Q x))).
case (H n x); auto.
rewrite low_Imu; apply Mfix_le_iter; auto.
rewrite up_lim; rewrite up_Imu.
unfold Mfix,mu_lub; simpl.
apply lub_glb_le; intros.
case (H n x); auto.
Save.
End IRuleseq.

Section ITransformFix.

Section IFix_muF.
Variable Q : A -> B -> IU.
Variable ImuF : (A -> IU) -m> (A -> IU).

Lemma ImuF_stable : forall I J, I==J -> ImuF I == ImuF J.
intros; apply fstable with (f:=ImuF); auto.
Save.

Section IF_muF_results.
Hypothesis Iincl_F_ImuF :
    forall f x, f <= Mfix F ->
                      Iincl (Imu (F f x) (Q x)) (ImuF (fun y => Imu (f y) (Q y)) x).

Lemma Iincl_fix_ifix : forall x, Iincl (Imu (Mfix F x) (Q x)) (fixp (D:=A -> IU) ImuF x).
assert (forall n x, Iincl (Imu (Miter F n x) (Q x)) (Ccpo.iter (D:=A -> IU) ImuF n x)).
induction n; simpl; intros; auto.
apply Iincl_trans with (ImuF (fun y => Imu (Miter F n y) (Q y)) x).
apply Iincl_F_ImuF.
intro y; unfold Mfix, fixp.
intro f; simpl.
apply (le_mlub (fun y0 : nat => mu (iter_ F y0 y) f) n).
apply (fmonotonic ImuF); auto.
intros; unfold Iincl, Imu,Mfix,fixp; simpl; split.
apply lub_le_compat; intro n; case (H n x); intros.
transitivity (low (Imu (Miter F n x) (Q x))); auto.
apply lub_glb_le; intros; auto.
case (H n x); intros.
transitivity (up (Imu (Miter F n x) (Q x))); auto.
Save.
Hint Resolve Iincl_fix_ifix.

(*
Hypothesis Iincl_ImuF_F :
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y)) ->
                      Iincl (ImuF (fun y => Imu (f y) (Q y)) x) (Imu (F f x) (Q x)).

Lemma Iincl_ifix_fix : forall x, Iincl (Ifix ImuF ImuF_mon x) (Imu (Mfix F F_mon x) (Q x)) .
assert (forall n x, Iincl (Iiter ImuF n x) (Imu (iter F n x) (Q x))).
induction n; simpl; intros; auto.
apply Iincl_trans with (ImuF (fun y => Imu (iter F n y) (Q y)) x).
apply IF_muF_incl.
repeat red; intros; unfold Mfix, mu_lub,mu_lub_;simpl.
apply le_lub with (f:=fun n => mu (iter F n y) f); auto.
apply ImuF_mon; auto.
intros; unfold Iincl, Ifix,Imu,Mfix,mu_lub; simpl.
unfold mu_lub_; split.
apply lub_le_compat; intros.
case (H n x); intros.
transitivity (low (Imu (iter F n x) (Q x))); auto.
apply lub_glb_le; intros; auto.
apply (@muf_mon_succ A B F F_mon n x).
case (Iiter_decr ImuF ImuF_mon x n); auto.
case (H n x); intros.
transitivity (up (Imu (iter F n x) (Q x))); auto.
Save.
Hint Resolve Iincl_fix_mu.

Lemma Iincl_ImuF : forall f, (forall x, Iincl (f x) (ImuF f x)) -> forall x, Iincl (Imu (Mfix F F_mon x) (Q x)) (f x).
intros; apply Iincl_trans with (Ifix ImuF ImuF_mon x); auto.
apply Iincl_inv; auto.
Save.

Hypothesis muF_F_le :
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y)) ->
                        muF (fun y => mu (f y) (q y)) x <= mu (F f x) (q x).

Lemma mufix_mu_le : forall x, mufix muF x <= mu (Mfix F F_mon x) (q x).
intros; unfold mufix,Mfix,mu_lub; simpl.
unfold mu_lub_.
apply lub_le_compat; intros.
generalize x; induction n; simpl; intros; auto.
transitivity (muF (fun y => mu (iter F n y) (q y)) x0).
apply muF_mon; auto.
apply muF_F_le.
repeat red; intros; unfold Mfix, mu_lub,mu_lub_;simpl.
apply le_lub with (f:=fun n => mu (iter F n y) f); auto.
Save.

End F_muF_results.
Hint Resolve mu_mufix_le mufix_mu_le.

Lemma mufix_mu :
   (forall f x, (forall y, le_distr (f y) (Mfix F F_mon y))
          -> mu (F f x) (q x) == muF (fun y => mu (f y) (q y)) x)
   -> forall x, mufix muF x == mu (Mfix F F_mon x) (q x).
intros; apply Ole_antisym; auto.
apply mufix_mu_le; intros; auto.
rewrite (H f x0); auto.
Save.
Hint Resolve mufix_mu.
End Fix_muF.

Section Fix_Term.

Definition pterm (x:A) := mu (Mfix F F_mon x) (f_one B).
Variable muF : (A -> U) -> A -> U.

Hypothesis muF_mon : Fmonotonic muF.

Hypothesis F_muF_eq_one :
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y))
    -> mu (F f x) (f_one B) == muF (fun y => mu (f y) (f_one B)) x.

Hypothesis muF_cont :  Fcontlub muF.

Lemma muF_pterm :  feq pterm (muF pterm).
red; intros; unfold pterm.
rewrite <- (mufix_mu (fun (x:A) => f_one B) muF_mon F_muF_eq_one x).
rewrite mufix_eq; auto.
apply muF_stable; auto.
red; intros; auto.
apply (mufix_mu (fun (x:A) => f_one B) muF_mon F_muF_eq_one x0).
Save.
Hint Resolve muF_pterm.
End Fix_Term.

Section Fix_muF_Term.

Variable muF : (A -> B -> U) -> (A -> U) -> A -> U.

Hypothesis muF_mon : forall q, Fmonotonic (muF q).

Variable q : A -> B -> U.
Definition qinv x y := [1-]q x y.

Hypothesis F_muF_le_inv :
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y))
    -> mu (F f x) (qinv x) <= muF qinv (fun y => mu (f y) (qinv y)) x.

Lemma muF_le_term : forall f,  (muF qinv (finv f) <= finv f) ->
    forall x, f x & pterm x <= mu (Mfix F F_mon x) (q x).
intros; transitivity (mu (Mfix F F_mon x) (fesp (q x) (f_one B))).
transitivity ([1-] mu (Mfix F F_mon x) (qinv x) & pterm x).
apply Uesp_le_compat; auto.
apply Uinv_le_perm_right.
apply muF_le with (muF:=muF qinv) (q:=qinv) (f:=finv f) (x:=x); auto.
unfold pterm; replace (qinv x) with (finv (q x)); auto.
apply mu_monotonic; intro; unfold fesp,f_one; repeat Usimpl; auto.
Save.

Hypothesis F_muF_le :
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y))
    -> mu (F f x) (q x) <= muF q (fun y => mu (f y) (q y)) x.

Lemma muF_eq : forall f, fle (muF q f) f -> fle (muF qinv (finv f)) (finv f)->
    forall x, pterm x == 1 -> mu (Mfix F F_mon x) (q x) == f x.
intros; apply Ole_antisym.
apply muF_le with (muF:=muF q); auto.
transitivity (f x & pterm x).
rewrite H1; auto.
apply muF_le_term; auto.
Save.

End Fix_muF_Term.

*)
End IF_muF_results.

End IFix_muF.
End ITransformFix.
End IFixrule.

Lemma IFlip_eq : forall Q : bool -> IU, Ieq (Imu Flip Q) (Iplus (Imultk [1/2] (Q true)) (Imultk [1/2] (Q false))).
red; unfold Flip, flip; intro x; auto.
Save.
Hint Resolve IFlip_eq.
