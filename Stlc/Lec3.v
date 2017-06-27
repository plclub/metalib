(*************************************************************************)
(*                                                                       *)
(* Lecture 3                                                             *)
(*                                                                       *)
(*************************************************************************)

Require Import Metalib.Metatheory.

(** Next, we import the definitions of the simply-typed lambda calculus. *)
Require Import Stlc.Definitions.

(** And some auxiliary lemmas about these definitions. *)
Require Import Stlc.Lemmas.

Require Import Stlc.Lec2.

(*************************************************************)

Inductive res (a : Set) : Set :=
  | val     : a -> res a
  | timeout : res a
  | stuck   : res a.

Fixpoint n_bigstep (n:nat) (e:exp) : res exp :=
  match n with
  | 0 => @timeout exp
  | S m =>
    match e with
    | var_b n => @stuck exp
    | var_f x => @stuck exp
    | app e1 e2 =>
      match n_bigstep m e1 with
      | val _ (abs T e1') =>
        match n_bigstep m e2 with
        | val _ v1 =>
          n_bigstep m (open e1' v1)
        | r => r
        end
      | r       => r
      end
    | abs T e   => val _ (abs T e)
    end
  end.

(* Type soundness for the definitional interpreter.
   If the interpreter doesn't timeout, then it doesn't get stuck. *)

Lemma n_bigstep_eval : forall n e T,
  typing nil e T ->
  @timeout exp <> n_bigstep n e ->
  exists v, val _ v = n_bigstep n e /\ typing nil v T /\ is_value_of_exp v.
Proof.
  induction n; intros e T TE EV; simpl in *.
  contradiction.
  destruct e; inversion TE; subst.
  - Case "var_f". inversion H2.
  - Case "abs".
    exists (abs T0 e). split; simpl; eauto.
  - Case "app".
    pose (Ih1 := IHn e1 (typ_arrow T1 T) H2). clearbody Ih1.
    pose (Ih2 := IHn e2 T1 H4). clearbody Ih2.

    destruct (n_bigstep n e1); try contradiction;
    destruct Ih1 as [v1 [EV1 [Tv1 vv1]]];
       try solve [intro h; inversion h]; inversion EV1.

    (* By canonical forms, know that v1 must be an abstraction. *)
    destruct v1; simpl in vv1; try contradiction; clear vv1. subst e.

    destruct (n_bigstep n e2); try contradiction;
    destruct Ih2 as [v2 [EV2 [Tv2 vv2]]];
        try solve [intro h; inversion h]; inversion EV2. subst.

    eapply IHn; eauto.

    (* result typechecks *)
    inversion Tv1. subst.
    pick fresh x.
    rewrite (subst_exp_intro x).
    eapply typing_subst_simple; eauto.
    fsetdec.
Qed.

(*************************************************************)

Inductive bigstep : exp -> exp -> Prop :=    (* defn bigstep *)
 | bs_app : forall (e1 v2:exp) (T1:typ) (e1' e2 v1:exp),
     is_value_of_exp v1 ->
     bigstep e1 (abs T1 e1') ->
     bigstep e2 v1 ->
     bigstep  (open_exp_wrt_exp  e1' v1 )  v2 ->
     bigstep (app e1 e2) v2
| bs_val : forall (v:exp),
     is_value_of_exp v ->
     lc_exp v ->
     bigstep v v.
Hint Constructors bigstep.


(*************************************************************)
(*   Connection to nominal representation of terms           *)
(*************************************************************)

Inductive n_exp : Set :=  (*r expressions *)
 | n_var (x:var)
 | n_abs (x:var) (T:typ) (e:n_exp)
 | n_app (e1:n_exp) (e2:n_exp).

Fixpoint nom_fv (e : n_exp) : vars :=
  match e with
  | n_var x => {{ x }}
  | n_abs x T e => AtomSetImpl.remove x (nom_fv e)
  | n_app e1 e2 => nom_fv e1 \u nom_fv e2
  end.

(* --- translate back to LN rep --- *)
Fixpoint nom_to_exp (ne : n_exp) : exp :=
  match ne with
  | n_var x => var_f x
  | n_app e1 e2 => app (nom_to_exp e1) (nom_to_exp e2)
  | n_abs x T e1 => abs T (close_exp_wrt_exp x (nom_to_exp e1))
end.

Lemma nom_to_exp_lc : forall ne, lc_exp (nom_to_exp ne).
Proof.
  induction ne; simpl; auto.
  eapply lc_abs_exists with (x := x).
  rewrite open_exp_wrt_exp_close_exp_wrt_exp.
  auto.
Qed.

Lemma nom_to_exp_fv : forall ne, nom_fv ne [=] fv_exp (nom_to_exp ne).
Proof.
  induction ne; simpl in *.
  - fsetdec.
  - rewrite IHne.
    autorewrite with lngen.
    fsetdec.
  - rewrite IHne1. rewrite IHne2.
    fsetdec.
Qed.

(* ----- result of interpretation -------------- *)
Inductive nom_val : Set :=
  | nom_closure : atom -> typ -> nom_env -> n_exp -> nom_val
with nom_env : Set :=
  | nom_nil : nom_env
  | nom_cons : atom -> nom_val -> nom_env -> nom_env.

Scheme nom_val_ind' := Induction for nom_val Sort Prop
 with  nom_env_ind' := Induction for nom_env Sort Prop.
Combined Scheme nom_mutual from nom_val_ind', nom_env_ind'.

Fixpoint nom_unload (cv:nom_val) : exp :=
  match cv with
  | nom_closure x T rho e =>
    nom_envsubst rho (nom_to_exp (n_abs x T e))
  end
with
nom_envsubst (ne:nom_env) : exp -> exp :=
  match ne with
  | nom_nil => fun e => e
  | nom_cons x v rho => fun e => nom_envsubst rho (subst_exp (nom_unload v) x e)
  end.

Fixpoint dom_rho (rho :nom_env) :=
  match rho with
  | nom_nil => {}
  | nom_cons x v rho => {{x}} \u dom_rho rho
  end.


Inductive closed_val : nom_val -> Prop :=
  | closed_closure : forall x T rho e,
      closed_env rho ->
      nom_fv e [<=] {{x}} \u dom_rho rho ->
      closed_val (nom_closure x T rho e)
with closed_env : nom_env -> Prop :=
     | closed_nil : closed_env nom_nil
     | closed_cons : forall x v rho,
         closed_val v -> closed_env rho -> closed_env (nom_cons x v rho).
Hint Constructors closed_env closed_val.

Scheme closed_val_ind' := Induction for closed_val Sort Prop
 with  closed_env_ind' := Induction for closed_env Sort Prop.
Combined Scheme closed_nom from closed_val_ind', closed_env_ind'.

Lemma fv_closed_mutual :
  (forall v, closed_val v -> fv_exp (nom_unload v) [=] {}) /\
  (forall rho, closed_env rho -> forall e, fv_exp e [<=] dom_rho rho ->
                                fv_exp (nom_envsubst rho e) [=] {}).
Proof.
  eapply closed_nom; intros.
  + simpl. rewrite H. fsetdec.
    simpl. autorewrite with lngen.
    rewrite nom_to_exp_fv in s.
    fsetdec.
  + simpl in *. fsetdec.
  + simpl in *.
    rewrite H0. fsetdec.
    rewrite fv_exp_subst_exp_upper.
    rewrite H.
    fsetdec.
Qed.

Lemma fv_closed :
  (forall v, closed_val v -> fv_exp (nom_unload v) [=] {}).
Proof.
  eapply fv_closed_mutual.
Qed.

Lemma fv_closed_env :
  (forall rho, closed_env rho -> forall e, fv_exp e [<=] dom_rho rho ->
                                fv_exp (nom_envsubst rho e) [=] {}).
Proof.
  eapply fv_closed_mutual.
Qed.

Lemma unload_fresh : forall rho v,
    closed_val v ->
    nom_envsubst rho (nom_unload v) = nom_unload v.
Proof.
  induction rho. simpl. auto.
  intros. simpl.
  rewrite subst_exp_fresh_eq; auto.
  rewrite fv_closed; auto.
Qed.

Fixpoint rho_lookup x rho :=
  match rho with
  | nom_nil => None
  | nom_cons y v rho' =>
    if (x == y) then
      Some v
    else
      rho_lookup x rho'
  end.

Lemma rho_lookup_closed_val : forall x rho v,
    closed_env rho ->
    Some v = rho_lookup x rho ->
    closed_val v.
Proof.
  induction rho; intros; simpl in *.
  - inversion H0.
  - inversion H. subst.
    destruct (x == a).
    default_simp.
    eapply IHrho; eauto.
Qed.

Lemma nom_envsubst_var : forall x rho v,
    closed_env rho ->
    Some v = rho_lookup x rho ->
    nom_envsubst rho (var_f x) = nom_unload v.
Proof.
  induction rho.
  - intros. simpl in *.
  inversion H0.
  -  intros. simpl in *.
     inversion H. subst.
     destruct (x == a).
     + inversion H0. subst. clear H0.
    simpl.
    rewrite unload_fresh; auto.
  + eapply IHrho; auto.
Qed.

Lemma nom_envsubst_abs : forall rho T e,
 nom_envsubst rho (abs T e) = abs T (nom_envsubst rho e).
Proof.
  induction rho; simpl.
  - auto.
  - intros.
    rewrite IHrho.
    auto.
Qed.

Lemma nom_envsubst_app : forall rho e1 e2,
 nom_envsubst rho (app e1 e2) = app (nom_envsubst rho e1) (nom_envsubst rho e2).
Proof.
  induction rho; simpl.
  - auto.
  - intros.
    rewrite IHrho.
    auto.
Qed.

Lemma nom_unload_is_value : forall v, is_value_of_exp (nom_unload v).
Proof.
  destruct v. simpl. rewrite nom_envsubst_abs.
  simpl. auto.
Qed.

Lemma nom_unload_lc_mutual :
  (forall v, lc_exp (nom_unload v)) /\
  (forall rho, forall e, lc_exp e -> lc_exp (nom_envsubst rho e)).
Proof.
  eapply nom_mutual.
  - intros. simpl.
    eapply H.
    eapply lc_abs_exists with (x:=a).
    autorewrite with lngen.
    eapply nom_to_exp_lc.
  - intros. simpl. auto.
  - intros; simpl in *.
    eapply H0; eauto.
    eapply subst_exp_lc_exp; eauto.
Qed.

Lemma nom_envsubst_lc : (forall rho, forall e, lc_exp e -> lc_exp (nom_envsubst rho e)).
  eapply nom_unload_lc_mutual.
Qed.

Fixpoint nom_bigstep (n:nat) (e:n_exp) (rho: nom_env) : res nom_val :=
  match n with
  | 0 => timeout _
  | S m =>
    match e with
    | n_var x =>  match (rho_lookup x rho) with
                | Some v => val _ v
                | None   => stuck _
                end
    | n_app e1 e2 =>
      match nom_bigstep m e1 rho with
      | val _ (nom_closure x T rho' e1') =>
         match AtomSetProperties.In_dec x (dom_rho rho') with
        | left _ => stuck _
        | right _ =>
            match nom_bigstep m e2 rho with
            | val _ v1 =>
              nom_bigstep m e1' (nom_cons x v1 rho')
            | r => r
            end
         end
      | r       => r
      end
    | n_abs x T e   => val _ (nom_closure x T rho e)
    end
  end.



Lemma nom_closed : forall n rho e v,
    val _ v = nom_bigstep n e rho ->
    closed_env rho ->
    nom_fv e [<=] dom_rho rho ->
    closed_val v.
Proof.
  induction n.
  intros; simpl in *. inversion H.
  intros.  destruct e; simpl in *.
  - Case "var".
    eapply rho_lookup_closed_val with (x:=x); eauto.
    destruct (rho_lookup x rho);
    inversion H;  auto.
  - Case "abs".
    inversion H.
    econstructor; eauto.
    rewrite <- H1.
    rewrite <-  AtomSetProperties.add_union_singleton.
    eapply FSetDecideTestCases.test_Subset_add_remove.
  - Case "app".
    remember (nom_bigstep n e1 rho) as r1.
    remember (nom_bigstep n e2 rho) as r2.
    destruct r1; try solve [inversion H].

    assert (C: closed_val n0). eapply IHn; eauto. fsetdec.
    destruct n0 as [x T rho' e1'].
    inversion C.
    destruct (AtomSetProperties.In_dec x (dom_rho rho')); try solve [inversion H].
    destruct r2; try solve [inversion H].
    assert (closed_val n1). eapply IHn; eauto. fsetdec.
    eauto.
Qed.

Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 68).


Lemma commute_subst_envsubst : forall rho x v e,
  closed_env rho ->
  closed_val v  ->
  x \notin dom_rho rho ->
  nom_envsubst rho ([x ~> nom_unload v] e) =
                    [x ~> nom_unload v] nom_envsubst rho e.
Proof.
  induction rho.
  - intros. simpl. auto.
  - intros.
    simpl in *.
    inversion H.
    rewrite subst_exp_subst_exp; auto.
    rewrite (subst_exp_fresh_eq (nom_unload v)); auto.
    rewrite fv_closed; auto.
    rewrite fv_closed; auto.
Qed.

Lemma open_nom_envsubst : forall rho e e',
 fv_exp e' [=] {} ->
 (open_exp_wrt_exp (nom_envsubst rho e) e') =
 nom_envsubst rho (open_exp_wrt_exp e e').
Proof.
  induction rho; intros; simpl. auto.
  rewrite subst_exp_open_exp_wrt_exp.
  rewrite (subst_exp_fresh_eq e'); auto.
  rewrite H.
  fsetdec.
  eapply nom_unload_lc_mutual.
Qed.

Lemma nom_soundness : forall n rho e v,
    val _ v = nom_bigstep n e rho  ->
    closed_env rho ->
    nom_fv e [<=] dom_rho rho ->
    bigstep (nom_envsubst rho (nom_to_exp e)) (nom_unload v).
Proof.
  induction n.
  intros; simpl in *. inversion H.
  intros.  destruct e; simpl in *.
  - Case "var".
    remember (rho_lookup x rho) as l.
    destruct l as [[w Pr]| Pr].
    inversion H. subst. clear H1.
    erewrite nom_envsubst_var; eauto.
    econstructor; eauto.
    eapply nom_unload_is_value.
    eapply nom_unload_lc_mutual.
    eapply nom_to_exp_lc.
    inversion H.
  - Case "abs".
    inversion H.
    subst.
    simpl.
    rewrite nom_envsubst_abs.
    econstructor; eauto.
    simpl. auto.
    rewrite <- nom_envsubst_abs.
    eapply nom_envsubst_lc.
    eapply lc_abs_exists with (x := x).
    autorewrite with lngen.
    eapply nom_to_exp_lc.
  - Case "app".
    remember (nom_bigstep n e1 rho) as r1.
    remember (nom_bigstep n e2 rho) as r2.
    destruct r1; try solve [inversion H].
    assert (closed_val n0). eapply nom_closed; eauto. fsetdec.
    destruct n0 as [x T rho' e1'].
    inversion H2.

    destruct (AtomSetProperties.In_dec x (dom_rho rho')); try solve [inversion H].


    destruct r2; try solve [inversion H].
    assert (closed_val n1).
    eapply nom_closed; eauto. fsetdec.

    apply IHn in Heqr1; auto; try fsetdec.
    apply IHn in Heqr2; auto; try fsetdec.
    simpl in Heqr1.
    rewrite nom_envsubst_abs in Heqr1.

    apply IHn in H; eauto.
    simpl in H.

    rewrite nom_envsubst_app.
    econstructor; eauto.
    apply nom_unload_is_value.
    rewrite open_nom_envsubst.
    rewrite <- subst_exp_spec.
    auto.
    rewrite fv_closed. fsetdec.
    auto.
Qed.
