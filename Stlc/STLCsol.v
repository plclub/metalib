


(*************************************************************)
(* Denotational-interpreter based type soundness proof
   (cf. Amin/Rompf, though with substitution semantics)
*)
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
(*   Connection to env-based semantics                       *)
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


Lemma bigstep_lc1 : forall x y, bigstep x y -> lc_exp x.
Proof. induction 1; auto. Qed.
Lemma bigstep_lc2 : forall x y, bigstep x y -> lc_exp y.
Proof. induction 1; auto. Qed.

Inductive multistep : exp -> exp -> Prop :=
| ms_refl : forall e, lc_exp e -> multistep e e
| ms_step : forall e1 e2 e3, eval e1 e2 -> multistep e2 e3 -> multistep e1 e3.
Hint Constructors multistep.
Lemma ms_trans : forall e2 e1 e3,
    multistep e1 e2 -> multistep e2 e3 -> multistep e1 e3.
Proof. induction 1; intros; eauto. Qed.

Lemma multistep_lc1 : forall x y, multistep x y -> lc_exp x.
Proof. intros. induction H; eauto using eval_lc_exp1. Qed.
Lemma multistep_lc2 : forall x y, multistep x y -> lc_exp y.
Proof. intros. induction H; eauto using eval_lc_exp2. Qed.

Lemma app_cong1 : forall e1 e1' e2,
    lc_exp e2 ->
    multistep e1 e1' -> multistep (app e1 e2) (app e1' e2).
Proof. induction 2.
  - eapply ms_refl. eauto.
  - eapply ms_step. eauto. eauto.
Qed.

Lemma app_cong2 : forall e1 e2 e2',
    lc_exp e1 ->
    is_value_of_exp e1 ->
    multistep e2 e2' -> multistep (app e1 e2) (app e1 e2').
Proof. induction 3.
  - eapply ms_refl; eauto.
  - eapply ms_step; eauto.
Qed.

Lemma bigstep_smallstep : forall e v, bigstep e v -> multistep e v.
Proof.
  induction 1.
  apply (@ms_trans (app (abs T1 e1') e2)).
  eapply app_cong1; eauto using bigstep_lc1, bigstep_lc2.
  apply (@ms_trans (app (abs T1 e1') v1)).
  eapply app_cong2; eauto using bigstep_lc1, bigstep_lc2. simpl; auto.
  apply (@ms_trans (open_exp_wrt_exp e1' v1)).
  eapply ms_step.
  apply eval_beta;
  eauto using bigstep_lc1, bigstep_lc2.
  eapply ms_refl; eauto using bigstep_lc1.
  auto.
  eapply ms_refl; auto.
Qed.

Lemma smallstep_bigstep1 : forall e e', eval e e' -> forall v, bigstep e v -> bigstep e' v.
Proof.
  induction 1; intros.
  - inversion H2; simpl in *; try contradiction. subst.
    inversion H6. subst.
    destruct v; simpl in *; try contradiction.
    inversion H7; simpl in *; try contradiction; subst.
    auto.
  - inversion H1; simpl in *; try contradiction; subst.
    eapply bs_app; eauto.
  - inversion H2; simpl in *; try contradiction; subst.
    eapply bs_app; eauto.
Qed.

Lemma smallstep_bigstep2 : forall e e', eval e e' -> forall v, bigstep e' v -> bigstep e v.
Proof.
  induction 1; intros.
  - eapply bs_app; eauto.
    eapply bs_val; simpl; eauto.
  - inversion H1; simpl in *; try contradiction; subst.
    eapply bs_app; simpl; eauto.
  - inversion H2; simpl in *; try contradiction; subst.
    eapply bs_app; eauto.
Qed.


Lemma smallstep_bigstep : forall e v, multistep e v -> is_value_of_exp v -> bigstep e v.
Proof.
  induction 1; intros.
  - destruct e; simpl in *; auto; try contradiction.
  - eapply smallstep_bigstep2; eauto.
Qed.


(****************************************************************)
(* Now, an environment-based bigstep semantics for the program. *)
(****************************************************************)

Inductive rt_val : Set :=
  | closure : typ -> list (atom * rt_val) -> exp -> rt_val.
Definition rt_env := list (atom * rt_val).

Inductive close (rho : rt_env) : exp -> rt_val -> Prop :=
  | close_abs : forall T e,
      close rho (abs T e) (closure T rho e).

Inductive env_bigstep : rt_env -> exp -> rt_val -> Prop :=
  | env_bs_val : forall rho v cv,
      close rho v cv ->
      env_bigstep rho v cv
  | env_bs_app : forall L rho e1 e2 T rho' e1' cv' cv,
      env_bigstep rho e1 (closure T rho' e1')     ->
      env_bigstep rho e2 cv'                      ->
      (forall x, x \notin L ->
          env_bigstep (x ~ cv' ++ rho') (e1' ^ x) cv)   ->
      env_bigstep rho (app e1 e2) cv.

(* Can we prove type soundness for this semantics? *)

Inductive typing_rt_val : rt_val -> typ -> Prop :=
 | typing_closure : forall T1 T2 G rho e1 L,
     typing_rt_env G rho ->
     (forall x, x \notin L ->
           typing ((x ~ T1) ++ G) (e1 ^ x) T2) ->
     typing_rt_val (closure T1 rho e1) (typ_arrow T1 T2)
with typing_rt_env : env -> rt_env -> Prop :=
 | typing_rt_nil  : typing_rt_env nil nil
 | typing_rt_cons : forall x v T G rho,
     typing_rt_val v T ->
     typing_rt_env G rho ->
     x \notin dom G ->
     typing_rt_env ((x ~ T) ++ G) ((x ~ v) ++ rho).

Hint Constructors typing_rt_val typing_rt_env.


Lemma typing_preservation : forall rho e cv,
    env_bigstep rho e cv ->
    forall G T,
      typing G e T ->
      typing_rt_env G rho ->
      typing_rt_val cv T.
Proof.
  induction 1; intros G U TE TR.
  - inversion H. subst.
    inversion TE. eauto.
  - inversion TE. subst.
    assert (HC : typing_rt_val (closure T rho' e1') (typ_arrow T1 U)).
    eapply IHenv_bigstep1; eauto.
    inversion HC. subst.
    pick fresh x.
    eapply H2 with (G := x ~ T1 ++ G0) ; eauto.
Qed.

(* Connection between environment & subst based values: unload and envsubst *)

Lemma same_dom : forall G rho,
  typing_rt_env G rho -> dom G = dom rho.
Proof.
  induction 1; auto. simpl; f_equal; auto.
Qed.

Fixpoint unload (cv:rt_val) : exp :=
  match cv with
  | closure T rho e =>
    (fold_left (fun e entry => match entry with
                           | (x,v) => subst_exp (unload v) x e
                           end)
                rho (abs T e))
  end.
Definition envsubst := (fold_left (fun e entry  => match entry with
                          | (x,v) => subst_exp (unload v) x e
                          end)).

Lemma envsubst_abs : forall rho T e,
 envsubst rho (abs T e) = abs T (envsubst rho e).
Proof.
  induction rho; simpl.
  - auto.
  - intros. destruct a as [x v].
    rewrite IHrho.
    auto.
Qed.

Lemma envsubst_app : forall rho e1 e2,
 envsubst rho (app e1 e2) = app (envsubst rho e1) (envsubst rho e2).
Proof.
  induction rho; simpl.
  - auto.
  - intros. destruct a as [x v].
    rewrite IHrho.
    auto.
Qed.

(* The next three theorems need to be proven together. To do that we
   will define a combined induction scheme for the mutual typing
   judgements typing_rt_val and typing_rt_env.
 *)
Scheme typing_val_ind' := Induction for typing_rt_val Sort Prop
 with  typing_rt_ind' := Induction for typing_rt_env Sort Prop.

Combined Scheme typing_rt from typing_val_ind', typing_rt_ind'.

Lemma typing_unload_mutual :
  (forall v T (H: typing_rt_val v T),

      typing nil (unload v) T)
 /\
  (forall G rho (H : typing_rt_env G rho),

      ((forall x e, x \notin dom rho ->
              envsubst rho (e ^ x) = (envsubst rho e) ^ x))
 /\
      (forall G1 e T, typing (G ++ G1) e T ->
         typing G1 (envsubst rho e) T)).
Proof.
  eapply typing_rt; intros.
  - simpl. fold envsubst.
    pick fresh x for (L \u dom G \u dom rho \u fv_exp e1).
    destruct H as [h0 h1].
    eapply h1; eauto.
    simpl_env.
    eapply typing_abs_exists with (x:=x). fsetdec.
    auto.
  - simpl. split; intros.
    auto.
    simpl_env in *. auto.
  - simpl.
    destruct H0 as [h0 h1].
    split; intros.
    + rewrite <- h0; eauto.
      rewrite subst_exp_open_exp_wrt_exp; eauto.
      rewrite subst_neq_var. auto.
      fsetdec.
      eapply typing_to_lc_exp; eauto.
    + simpl_env in *.
      eapply h1.
      eapply typing_subst_simple; eauto.
      rewrite_env ((G ++ G1) ++ nil).
      eapply typing_weakening. auto.
      simpl_env.
      apply typing_uniq in H0.
      eapply uniq_app_2.
      eauto.
Qed.

Lemma typing_unload :
  (forall v T (H: typing_rt_val v T),      typing nil (unload v) T).
Proof.
  eapply typing_unload_mutual.
Qed.
Lemma envsubst_open : forall G rho (H : typing_rt_env G rho),
      (forall x e, x \notin dom rho ->
              envsubst rho (e ^ x) = (envsubst rho e) ^ x).
Proof.
  eapply typing_unload_mutual.
Qed.
Lemma typing_envsubst : forall G rho (H : typing_rt_env G rho),
      (forall G1 e T, typing (G ++ G1) e T ->
         typing G1 (envsubst rho e) T).
Proof.
  eapply typing_unload_mutual.
Qed.


Lemma commute_subst_envsubst : forall G rho,
   typing_rt_env G rho ->
   forall x v e T,
     typing nil (unload v) T ->
     x \notin dom rho ->
     envsubst rho ([x ~> unload v] e)  = [x ~> unload v] envsubst rho e.
Proof.
  induction 1.
  - intros. simpl. auto.
  - intros.
    simpl in *.
    rewrite subst_exp_subst_exp; eauto.
    rewrite (subst_exp_fresh_eq x (unload v0)); eauto.
    assert (fv_exp (unload v0) [<=] (@dom typ nil)). eapply fv_in_dom.
    eauto using typing_unload.
    fsetdec.
    assert (typing nil (unload v) T). eauto using typing_unload.
    assert (fv_exp (unload v) [<=] (@dom typ nil)). eapply fv_in_dom. eauto.
    fsetdec.
Qed.


Lemma unload_is_value : forall v, is_value_of_exp (unload v).
Proof.
  destruct v. simpl. rewrite envsubst_abs. simpl.  auto.
Qed.

(* -------------------------------------------------- *)

Lemma tr_soundness : forall rho e v,
    env_bigstep rho e v ->
    forall G T, typing G e T -> typing_rt_env G rho ->
           bigstep (envsubst rho e) (unload v).
Proof.
  induction 1.
  - intros G T Tv Trho.
    inversion H. subst.
    simpl. fold envsubst.
    rewrite envsubst_abs.
    eapply bs_val; simpl; auto.
    eapply typing_to_lc_exp.
    rewrite <- envsubst_abs.
    eapply typing_envsubst with (G1 := nil); simpl_env; eauto.
  - intros. rewrite envsubst_app.
    inversion H3. subst.
    assert (TC: typing_rt_val (closure T rho' e1') (typ_arrow T1 T0)).
    { eapply typing_preservation; eauto. }
    inversion TC. subst.

    assert (TC': typing_rt_val cv' T1).
    { eapply typing_preservation; eauto. }


    pose (h0 := IHenv_bigstep1 _ _ H8 H4). clearbody h0.
    simpl in h0. fold envsubst in h0.
    rewrite envsubst_abs in h0.
    pose (h1 := IHenv_bigstep2 _ _ H10 H4). clearbody h1.

    pose (AVOID := fv_exp (envsubst rho' e1') \u dom rho').
    pick fresh x. subst AVOID.
    assert (typing_rt_env (x ~ T1 ++ G0) (x ~ cv' ++ rho')). eauto.

    assert (bigstep (envsubst ((x ~ cv') ++ rho') (e1' ^ x)) (unload cv)).
    eapply H2; eauto.

    eapply bs_app with (v1 := unload cv'); simpl; eauto.
    eapply unload_is_value.
    simpl in H6.
    rewrite (subst_exp_intro x); eauto.
    erewrite commute_subst_envsubst in H6; eauto.
    erewrite <- envsubst_open; eauto.
    eapply typing_unload; eauto.
Qed.

(* ------------------------------------------------------- *)

(* de Bruijn index version *)

Inductive db_val : Set :=
  | db_closure : typ -> list db_val -> exp -> db_val.
Definition db_env := list db_val.


Fixpoint db_bigstep (n:nat) (e:exp) (rho: db_env) : res db_val :=
  match n with
  | 0 => timeout _
  | S m =>
    match e with
    | var_b k => nth k (List.map (val _) rho) (stuck _)
    | var_f x => stuck _
    | app e1 e2 =>
      match db_bigstep m e1 rho with
      | val _ (db_closure T rho' e1') =>
        match db_bigstep m e2 rho with
        | val _ v1 =>
          db_bigstep m e1' (v1 :: rho')
        | r => r
        end
      | r       => r
      end
    | abs T e   => val _ (db_closure T rho e)
    end
  end.

Fixpoint close_ctx e (G : env) :=
  match G with
  | nil => e
  | (x,_)::G0 => close_ctx (close_exp_wrt_exp x e) G0
  end.


Fixpoint open_ctx e (G : env) :=
  match G with
  | nil => e
  | (x,_)::G0 => open_ctx (e ^ x) G0
  end.

Inductive typing_db_val : db_val -> typ -> Prop :=
 | typing_db_closure : forall T1 T2 G rho e1 L,
     typing_db_env G rho ->
     (forall x, x \notin L ->
           typing ((x ~ T1) ++ G) (open_ctx (e1 ^ x) G) T2) ->
     typing_db_val (db_closure T1 rho e1) (typ_arrow T1 T2)
with typing_db_env : env -> db_env -> Prop :=
 | typing_db_nil  : typing_db_env nil nil
 | typing_db_cons : forall x v T G rho,
     typing_db_val v T ->
     typing_db_env G rho ->
     x \notin dom G ->
     typing_db_env ((x ~ T) ++ G) (v :: rho).

Hint Constructors typing_db_val typing_db_env.

(* e has m=length rho dangling bound variables.
   Let's describe how scoping works in this interpreter.
 *)
Inductive scoped_val : db_val -> Prop :=
  | scoped_closure : forall T rho e,
      scoped_env rho ->
      degree_exp_wrt_exp (length rho) (abs T e) ->
      scoped_val (db_closure T rho e)
with scoped_env : db_env -> Prop :=
     | scoped_nil : scoped_env nil
     | scoped_cons : forall v rho,
         scoped_val v -> scoped_env rho -> scoped_env (v :: rho).
Hint Constructors scoped_env scoped_val.

Lemma db_bigstep_scoped : forall n e rho v,
    scoped_env rho ->
    degree_exp_wrt_exp (length rho) e ->
    val _ v = db_bigstep n e rho ->
    scoped_val v.
Proof.
  induction n; intros e rho v SR DE EV; simpl in *.
  inversion EV.
  destruct e; inversion DE; subst.
  - Case "var_b".
    revert SR EV H1.
    generalize rho.
    generalize n0.
    induction n1; intros; destruct rho0; simpl in *.
    + inversion EV.
    + inversion SR. inversion EV. subst. auto.
    + inversion EV.
    + inversion SR. subst.
      eapply IHn1; eauto.
      apply lt_S_n. auto.
  - Case "var_f".
    inversion EV.
  - Case "abs".
    inversion EV. eauto.
  - Case "app".
    remember (db_bigstep n e1 rho) as r1.
    remember (db_bigstep n e2 rho) as r2.
    destruct r1; try solve [inversion EV].
    destruct d as [T rho' e1'].
    destruct r2; try solve [inversion EV].
    assert (SV1: scoped_val (db_closure T rho' e1')) by
        (eapply (@IHn e1); eauto).
    assert (SV2: scoped_val d) by (eapply (@IHn e2); eauto).
    inversion SV1. subst.
    inversion H5.
    eapply (@IHn e1' (d :: rho')); eauto.
Qed.

(* --------------------- *)

Fixpoint db_unload (cv:db_val) : exp :=
  match cv with
  | db_closure T rho e =>
    (fold_left (fun e v => open e (db_unload v)) rho (abs T e))
  end.
Definition db_envsubst := fold_left (fun e v => open e (db_unload v)).

Lemma db_unload_is_value : forall v, is_value_of_exp (db_unload v).
Proof.
  destruct v. simpl.
Admitted.


(* The next three theorems need to be proven together. To do that we
   will define a combined induction scheme for the mutual typing
   judgements typing_rt_val and typing_rt_env.
 *)
Scheme scoped_val_ind' := Induction for scoped_val Sort Prop
 with  scoped_env_ind' := Induction for scoped_env Sort Prop.

Combined Scheme scoped_mutual from scoped_val_ind', scoped_env_ind'.

Lemma db_envsubst_lc_exp_closed : forall rho e,
    lc_exp e -> db_envsubst rho e = e.
Proof.
  induction rho; intros; simpl in *.
  auto.
  rewrite open_exp_wrt_exp_lc_exp; auto.
Qed.

Lemma db_subst_fresh : forall v rho,
    degree_exp_wrt_exp 0 v -> (db_envsubst rho v) = v.
Proof.
  induction rho.
  simpl. auto.
  intros. simpl.
  rewrite open_exp_wrt_exp_lc_exp. auto.
  apply lc_exp_of_degree. auto.
Qed.


Lemma weaken_degree : forall k n e, degree_exp_wrt_exp n e -> degree_exp_wrt_exp (k + n) e.
Proof.
  induction k.
  auto.
  intros.
  simpl.
Admitted.

Lemma open_first : forall e' e k m,
    m < k ->
    degree_exp_wrt_exp 0 e' ->
    degree_exp_wrt_exp (S k) e ->
    degree_exp_wrt_exp k (open_exp_wrt_exp_rec m e' e).
Proof.
  intros e' e.
  induction e; simpl.
  - intros k m LT D.
    simpl. destruct (lt_eq_lt_dec n m).
    destruct s; intro h.
    econstructor. admit.
    replace k with (k + 0). eapply weaken_degree. auto. admit.
    intro h.
    inversion h. subst.
    econstructor. admit.
  - intros k m LT D h.
    econstructor; eauto.
  - intros k m LT D h.
    econstructor; eauto.
    eapply IHe. admit.
    auto.
    inversion h.
    auto.
  - intros. inversion H1. eauto.
Admitted.

Lemma db_unload_mutual :
  (forall v, scoped_val v -> degree_exp_wrt_exp 0 (db_unload v)) /\
  (forall env, scoped_env env ->
        Forall (fun x => degree_exp_wrt_exp 0 (db_unload x)) env /\
        forall e n, degree_exp_wrt_exp (n + (length env)) e ->
               degree_exp_wrt_exp n (db_envsubst env e)).
Proof.
  eapply scoped_mutual; intros.
  simpl. destruct H. fold db_envsubst. eapply H0. simpl. auto.
  - split. auto.
    intros e n H. simpl in *. replace (n + 0) with n in *.  auto. admit.
  - destruct H0 as [h0 h1]; split; simpl in *.
    econstructor; eauto.
    intros e n D.
    replace (n + S (length rho)) with (S n + length rho) in D.
    eapply h1.
    eapply open_first.
    admit.
    auto.
    auto.
    admit.
Admitted.

Lemma scoped_val_lc_exp : forall v, scoped_val v -> lc_exp (db_unload v).
Proof.
  intros. apply lc_exp_of_degree. eapply db_unload_mutual. auto.
Qed.

Lemma scoped_env_lc_exp :
  forall rho, scoped_env rho ->
         Forall (fun x => lc_exp (db_unload x)) rho.
Admitted.


Lemma db_bigstep_sound : forall n e rho v,
    db_bigstep n e rho = val _ v ->
    scoped_env rho ->
    degree_exp_wrt_exp (length rho) e ->
    bigstep (db_envsubst rho e) (db_unload v).
Proof.
  induction n; intros e rho v EV TR TE; simpl in EV.
  inversion EV.
  destruct e.
  - Case "bvar".
    revert TR EV TE.
    generalize rho.
    generalize n0.
    induction n1; intros; destruct rho0; simpl in *.
    + inversion EV.
    + inversion TR. inversion EV. subst.
      unfold open. simpl.
      rewrite db_subst_fresh.
      econstructor. apply db_unload_is_value.
      apply scoped_val_lc_exp. auto.
      admit.
    + inversion EV.
    + admit.
  - Case "fvar". inversion EV.
  - Case "abs".  inversion EV.
    econstructor.
    apply db_unload_is_value.
    apply scoped_val_lc_exp.
    econstructor. auto. auto.
  - Case "app".
    remember (db_bigstep n e1 rho) as r1.
    remember (db_bigstep n e2 rho) as r2.
    destruct r1; try solve [inversion EV].
    destruct d as [T rho' e1'].
    destruct r2; try solve [inversion EV].
Admitted.

Lemma db_bigstep_eval : forall n G e T rho,
  typing nil (close_ctx e G) T ->
  typing_db_env G rho ->
  timeout _ <> db_bigstep n e rho ->
  exists v, val _ v = db_bigstep n e rho /\ typing_db_val v T.
Proof.
  induction n; intros G e T rho TE TR EV; simpl in *.
  contradiction.
  destruct e.
  - Case "var_b".
    admit.
  - Case "var_f".
    admit.
  - Case "abs".
    exists (db_closure T0 rho e). split; simpl; eauto.
    admit.
  - Case "app".
    admit.

(*    (* Consider whether e1 evaluates to a value. If it does, apply the IH. *)
    pose (Ih1 := IHn G e1 (typ_arrow T1 T) rho H2 TR). clearbody Ih1.
    destruct (db_bigstep n e1 rho); try contradiction;
    destruct Ih1 as [v1 [EV1 Tv1]]; try solve [intro h; inversion h]; inversion EV1.

    (* By canonical forms, know that v1 must be an abstraction. *)
    inversion Tv1.  subst.

    (* Consider whether e2 evaluates to a value (and apply the IH if so). *)
    pose (Ih2 := IHn G e2 T1 rho H4 TR). clearbody Ih2.
    destruct (db_bigstep n e2 rho); try contradiction;
    destruct Ih2 as [v2 [EV2 Tv2]]; try solve [intro h; inversion h]; inversion EV2. subst.

    pick fresh x.

    eapply IHn with (G := x ~ T1 ++ G0); eauto.

    pick fresh y. eapply (typing_rename y); eauto.
    eauto.
*)
(* ------------------------------------------------------- *)
(* Interpreter based big-step semantics *)

Fixpoint rt_bigstep (n:nat) (e:exp) (rho: rt_env) : res rt_val :=
  match n with
  | 0 => timeout _
  | S m =>
    match e with
    | var_b n => stuck _
    | var_f x => match (binds_lookup _ x rho) with
                | inl (exist _ y _) => val _ y
                | inr _             => stuck _
                end
    | app e1 e2 =>
      match rt_bigstep m e1 rho with
      | val _ (closure T rho' e1') =>
        match rt_bigstep m e2 rho with
        | val _ v1 =>
          let (x,_) := atom_fresh (dom rho') in
          rt_bigstep m (e1' ^ x) ((x ~ v1) ++ rho')
        | r => r
        end
      | r       => r
      end
    | abs T e   => val _ (closure T rho e)
    end
  end.

(* Soundness for definitional interpreter *)


Lemma rt_env_uniq1 : forall G rho,
    typing_rt_env G rho -> uniq G.
Proof.
  induction 1; auto.
Qed.
Lemma rt_env_uniq2 : forall G rho,
    typing_rt_env G rho -> uniq rho.
Proof.
  induction 1; auto. erewrite same_dom in H1; eauto.
Qed.

Lemma binds_typing_tr_val : forall G rho x T v,
 typing_rt_env G rho ->
 binds x T G ->
 binds x v rho ->
 typing_rt_val v T.
Proof.
  induction 1; intros BT BV.
  - inversion BT.
  - simpl in *.
    apply binds_cons_uniq_1 in BT; eauto using rt_env_uniq1.
    apply binds_cons_uniq_1 in BV; eauto using rt_env_uniq2.
    destruct BT as [[? [? NI1]]| [BT NE1]];
    destruct BV as [[? [? NI2]]| [BV NE2]]; try contradiction; subst; auto.
    rewrite same_dom with (rho:=rho) in H1; auto.
    eauto using rt_env_uniq2.
Qed.

Lemma notbinds_typing_tr_env : forall G rho x T,
  typing_rt_env G rho ->
  binds x T G ->
  exists v, binds x v rho /\ typing_rt_val v T.
Proof.
  induction 1; intros BT.
  - inversion BT.
  - simpl in *.
    apply binds_cons_uniq_1 in BT; eauto using rt_env_uniq1.
    destruct BT as [[? [? NI1]]| [BT NE1]]. subst.
    + exists v. split. auto. auto.
Admitted.


Lemma rt_bigstep_eval : forall n G e T rho,
  typing G e T ->
  typing_rt_env G rho ->
  timeout _ <> rt_bigstep n e rho ->
  exists v, val _ v = rt_bigstep n e rho /\ typing_rt_val v T.
Proof.
  induction n; intros G e T rho TE TR EV; simpl in *.
  contradiction.
  destruct e; inversion TE; subst.
  - Case "var_f".
    destruct (binds_lookup _ x rho) as [[v Pf]|Pf].
    + (* found *)
      exists v. split; auto. eapply binds_typing_tr_val; eauto.
    + (* not found *)
      admit.
  - Case "abs".
    exists (closure T0 rho e). split; simpl; eauto.
  - Case "app".


    (* Consider whether e1 evaluates to a value. If it does, apply the IH. *)
    pose (Ih1 := IHn G e1 (typ_arrow T1 T) rho H2 TR). clearbody Ih1.
    destruct (rt_bigstep n e1 rho); try contradiction;
    destruct Ih1 as [v1 [EV1 Tv1]]; try solve [intro h; inversion h]; inversion EV1.

    (* By canonical forms, know that v1 must be an abstraction. *)
    inversion Tv1.  subst.

    (* Consider whether e2 evaluates to a value (and apply the IH if so). *)
    pose (Ih2 := IHn G e2 T1 rho H4 TR). clearbody Ih2.
    destruct (rt_bigstep n e2 rho); try contradiction;
    destruct Ih2 as [v2 [EV2 Tv2]]; try solve [intro h; inversion h]; inversion EV2. subst.

    destruct (atom_fresh (dom rho0)) as [x Pf].
    assert (x `notin` dom G0)
      by (rewrite same_dom with (rho := rho0); auto).

    eapply IHn with (G := x ~ T1 ++ G0); eauto.

    pick fresh y. eapply (typing_rename y); eauto.
    eauto.
Admitted.

Lemma rt_type_soundness : forall n G e T rho v,
  typing G e T ->
  typing_rt_env G rho ->
  val _ v = rt_bigstep n e rho ->
  typing_rt_val v T.
Proof.
  induction n.
  intros. simpl in *. default_simp.
  intros G e T rho v TE TR EV.
  destruct e; default_simp.
  - destruct (binds_lookup _ x rho) as [[y Pr]| Pr];
    inversion EV.
    inversion TE.
    eapply binds_typing_tr_val; eauto.
  - eapply typing_closure with (L:=L); eauto.
  - inversion TE. subst.
    remember (rt_bigstep n e1 rho) as r1.
    destruct r1; try inversion EV.
    (* "e1 evaluates to a closure".  *)
    destruct r as [T1' rho' e1'].
    remember (rt_bigstep n e2 rho) as r2.
    destruct r2; try inversion EV.
    (* "e2 evals to a value" *)
    destruct (atom_fresh (dom rho')) as [x Pr].
    assert (TC : typing_rt_val (closure T1' rho' e1') (typ_arrow T1 T))
      by eauto.
    inversion TC; subst.
    assert (Frx : x \notin dom G0)
      by (rewrite same_dom with (rho := rho'); eauto).
    eapply IHn with (G := x ~ T1 ++ G0) (e := e1' ^ x); eauto.
    pick fresh y.
    eapply typing_rename with (x:=y); eauto.
    econstructor; eauto.
Qed.

(*
Lemma not_stuck : forall n e T G rho,
  typing G e T ->
  typing_rt_env G rho ->
  rt_bigstep n e rho <> stuck.
Proof.
  induction n.
  intros. simpl. default_simp.
  intros e T G rho TH TR.
  destruct e; default_simp.
  - Case "var_f".
    destruct (binds_lookup _ x rho) as [[y Pr]| Pr].
    default_simp.
    admit.
  - Case "app".
    remember (rt_bigstep n e1 rho) as r.
    destruct r; default_simp.
    assert (TC: typing_rt_val r (typ_arrow T1 T)) by
      (eapply rt_type_soundness; eauto).
    inversion TC; subst.
    destruct (rt_bigstep n e2 rho); default_simp.
    eapply IHn with (G := (x ~ T1) ++ G0); eauto.
    eapply typing_rename with (x := x); auto.
Admitted.
*)

Lemma ensubst_var :  forall x v rho,
  binds x v rho -> envsubst rho (var_f x) = unload v.
Proof.
  induction rho.
  simpl in *.
  intros.  inversion H.
  intros.
  destruct a as [x0 v0].
  simpl.
  destruct (x == x0). subst.
Admitted.


Lemma rt_bigstep_soundness : forall n rho e v,
    rt_bigstep n e rho = val _ v ->
    forall G T, typing G e T -> typing_rt_env G rho ->
           bigstep (envsubst rho e) (unload v).
Proof.
  induction n;
  intros rho e v EV G T TE TR.
  simpl in *; inversion EV.
  simpl in *. destruct e.
  - inversion EV.
  - destruct (binds_lookup _ x rho) as [[y Pr]|Pr];
    inversion EV. subst.
    inversion TE. subst.
    erewrite ensubst_var; eauto.
    econstructor; eauto.
    eapply unload_is_value.
    admit.
  - inversion EV. simpl. fold envsubst.
    rewrite envsubst_abs.
    eapply bs_val. simpl. auto.
    admit.
  - rewrite envsubst_app.
Admitted.


(************************************************)




(* Connection between environment & substitution based semantics *)

(* Now let's prove this stepper correct.  Start by showing that it preserves
   properties of bound and free variables.

   NOTE: This also follows from the type soundness result of this
   evaluator.

 *)
Definition wf_exp (rho: rt_env) (e : exp)  : Prop :=
  lc_exp e /\ fv_exp e [<=] dom rho.

Lemma wf_exp_rename : forall rho e x y v,
    y \notin dom rho ->
    wf_exp ((x ~ v) ++ rho) (e ^ x) ->
    wf_exp ((y ~ v) ++ rho) (e ^ y).
Proof.
  intros.
  inversion H0.
  split.
Admitted.

Inductive wf_val : rt_val -> Prop :=
| wf_closure : forall T rho e L,
    (forall x v, x \notin L -> wf_exp ((x,v)::rho) (e ^ x)) ->
    wf_rho rho -> wf_val (closure T rho e)
with wf_rho : rt_env -> Prop :=
| wf_nil  : wf_rho nil
| wf_cons : forall x v rho,
    x `notin` dom rho ->
    wf_val v -> wf_rho rho -> wf_rho ((x,v)::rho)
.

Hint Constructors wf_val wf_rho.

Lemma wf_lookup : forall rho x v, binds x v rho -> wf_rho rho -> wf_val v.
Proof.
  induction rho; intros. inversion H.
  default_simp.
  inversion H. inversion H2. subst. clear H2.
  econstructor; eauto.
  eauto.
Qed.

Lemma wf_rt_bigstep : forall n e rho v,
    wf_rho rho   ->
    wf_exp rho e ->
    val _ v = rt_bigstep n e rho ->
    wf_val v.
Proof.
  induction n; intros.
  simpl in H1. inversion H1.
  destruct e; simpl in H1.
  - inversion H1.
  - destruct (binds_lookup _ x rho) as [[v0 B]|Pf]; auto. inversion H1. subst.
    apply wf_lookup in B. auto. auto.
    inversion H0. simpl in H3.
    assert False. assert (IN: x `in` dom rho). fsetdec.
    destruct (binds_In_inv _ _ _ IN).
    unfold not in Pf. eauto. contradiction.
  - inversion H1. inversion H0.
    econstructor; eauto.
    intros.
    simpl in H4. inversion H2.
    econstructor; eauto.
    simpl.
    rewrite (fv_exp_open_exp_wrt_exp_upper e (var_f x)).
    simpl. fsetdec.
  - inversion H0. inversion H2. simpl in H3. subst.
    remember (rt_bigstep n e1 rho) as R1.
    destruct R1.
    + assert (W1 : wf_exp rho e1). econstructor; eauto. fsetdec.
      pose (IH1 := IHn e1 rho r H W1 HeqR1). clearbody IH1.
      inversion IH1. subst.
      remember (rt_bigstep n e2 rho) as R2.
      destruct R2.
      -- assert (W2 : wf_exp rho e2). econstructor; eauto. fsetdec.
         pose (IH2 := IHn e2 rho r H W2 HeqR2). clearbody IH2.
         destruct (atom_fresh (dom rho0)).
         apply (@IHn (e ^ x) ((x,r)::rho0) v); auto.
         admit.
      -- inversion H1.
      -- inversion H1.
    + inversion H1.
    + inversion H1.
Admitted.

(* Connection between environment & subst based values: unload and envsubst *)
(*
Section EnvSubst.

Variable unload    : rt_val -> exp.
Variable unload_lc : forall v, wf_val v -> lc_exp (unload v).

Definition envsubst' (rho:rt_env) e : exp :=
  (fold_right (fun entry => match entry with
                         | (x,v) => subst_exp (unload v) x
                         end)
              e rho).

Lemma envsubst'_open : forall rho e e',
 wf_rho rho ->
 (envsubst' rho (open e e')) = open (envsubst' rho e) (envsubst' rho e').
Proof.
  induction rho; intros e e' WF; simpl.
  - auto.
  - destruct a as [x v].
    inversion WF.
    rewrite IHrho.
    rewrite subst_exp_open_exp_wrt_exp. auto.
    apply unload_lc. auto. auto.
Qed.

End EnvSubst.


Fixpoint unload (v : rt_val) : exp :=
  match v with
  | closure T rho e =>
    abs T (envsubst' unload rho e)
  end.

Lemma unload_lc : forall v, wf_val v -> lc_exp (unload v).
Proof.
  intros v WFv.
  inversion WFv.
  simpl.
  econstructor.
  intro x.
  assert (WFe: wf_exp ((x,v)::rho) (e ^ x)). auto.
  inversion WFe.




Definition envsubst : rt_env -> exp -> exp :=
  envsubst' unload.




Lemma wf_envsubst : forall rho e,
    wf_exp rho e -> wf_rho rho -> wf_exp nil (envsubst rho e).
Proof.
  intros rho e.
  induction rho; intros; unfold wf_exp in *.
  - default_simp.
  - destruct H as [LCe FVe].
    destruct a as [x v].
    inversion H0. subst.
    simpl in *.
Admitted.




Lemma unload_lc : forall v, wf_val v -> lc_exp (unload v).
Proof.
  intros v WFv.
  inversion WFv.
  simpl.
  econstructor.
  intro x.
  assert (WFe: wf_exp ((x,v)::rho) (e ^ x)). auto.
  inversion WFe.

(* Now some properties of envsubst *)

(* Lemma envsubst_fresh_eq : forall rho e, fv_exp e = {} -> envsubst rho e = e.
Admitted. *)

Lemma envsubst_var_f : forall x y rho,
 binds x y rho -> envsubst rho (var_f x) = (unload y).
Admitted.

Lemma envsubst_var_f_not : forall x rho,
 x `notin` dom rho -> envsubst rho (var_f x) = var_f x.
Admitted.

Lemma envsubst_abs : forall rho T e,
 envsubst rho (abs T e) = abs T (envsubst rho e).
Admitted.


Lemma rt_complete : forall n e rho v,
    wf_rho rho   ->
    wf_exp rho e ->
    rt_bigstep n e rho = val v ->
    bigstep (envsubst rho e) (unload v).
Proof.
  induction n; intros e rho v WFrho WFe BS.
  - simpl in BS. inversion BS.
  - simpl in BS.
    destruct e; try inversion BS.
    + destruct (binds_lookup _ x rho) as [[v0 B]|Pf]; inversion BS; subst.
      rewrite (envsubst_var_f x v); auto.
      assert (WFv : wf_val v) by (eapply wf_lookup; eauto).
      apply bs_val.
      apply unload_is_value.
      apply wf_lookup in B. inversion B. simpl.
      admit. auto.
      simpl in H0.
      assert False.
      assert (IN: x `in` dom rho). fsetdec.
      destruct (binds_In_inv _ _ _ IN).
      unfold not in Pf. eauto. contradiction.
    + inversion H1. simpl. fold envsubst.
      rewrite envsubst_abs.
      eapply bs_val.
      admit.
    + simpl in *. inversion H. subst.
      remember (rt_bigstep n e1 rho) as R1.
      destruct R1.
      assert (FV1: fv_exp e1 [<=] dom rho). fsetdec.
      pose (IH1 := IHn e1 rho r H4 FV1 (eq_sym HeqR1)). clear IH1.
      remember (rt_bigstep n e2 rho) as R2.
      destruct R2.
      assert (FV2: fv_exp e2 [<=] dom rho). fsetdec.
      pose (IH2 := IHn e2 rho r0 H5 FV2 (eq_sym HeqR2)). clear IH2.
      destruct r.
      destruct (atom_fresh (dom l)).
      assert (FV3 : fv_exp (e ^ x) [<=] dom ((x,r0) :: l)).

Inductive rt_res : Set :=
  | val   : rt_val -> rt_res
  | res   : exp    -> rt_env -> rt_res
  | stuck : rt_res.
Inductive wf_res : rt_res -> Prop :=
| wf_res_val : forall v, wf_val v -> wf_res (val v)
| wf_res_res : forall e rho, wf_exp rho e -> wf_rho rho -> wf_res (res e rho)
| wf_stuck : wf_res stuck.

Fixpoint rt_step (e: exp) (rho : rt_env) : rt_res :=
  match e with
  | var_b n => stuck
  | var_f x => match (binds_lookup _ x rho) with
              | inl (exist _ y _) => val y
              | inr _             => stuck
              end
  | app e1 e2 =>
    match rt_step e1 rho with
    | val (closure T rho' body) =>
      match rt_step e2 rho with
      | val v =>
        let (x,_) := atom_fresh (dom rho') in
        res (body ^ x) ((x ~ v) ++ rho')
      | res e2' rho' => res (app e1 e2') rho'
      | stuck => stuck
      end
    | res e1' rho' => res (app e1' e2) rho'
    | stuck       => stuck
    end
  | abs T e   => val (closure T rho e)
  end.


Lemma wf_rt_step : forall e rho,
    wf_exp rho e -> wf_rho rho -> wf_res (rt_step e rho).
Proof.
  intros e. induction e; intros; unfold wf_exp in *; default_simp.
  - default_simp.
    destruct (binds_lookup _ x rho) as [[y Pr]| Pr]; auto.
    apply wf_lookup in Pr. auto.
    auto.
  - econstructor; eauto.
    econstructor; eauto.
    intros x v.
    econstructor; eauto.
    simpl.
    pose (K := fv_exp_open_exp_wrt_exp_upper e (var_f x)). clearbody K.
    simpl in K.
    fsetdec.
  - assert (h1 : lc_exp e1 /\ fv_exp e1 [<=] dom rho).
    split; auto; fsetdec.
    assert (h2 : lc_exp e2 /\ fv_exp e2 [<=] dom rho).
    split; auto; fsetdec.
    pose (Ih1 := IHe1 _ h1 H0).
    pose (Ih2 := IHe2 _ h2 H0).
    destruct h1. destruct h2.
    inversion Ih1; auto.
    destruct v.
    inversion H1. subst.
    inversion Ih2; auto.
    destruct (atom_fresh (dom l1)).
    eauto.
    inversion H6.
    repeat (econstructor; simpl; eauto).

    econstructor; eauto.






Lemma envsubst_var_b : forall x rho,
  envsubst rho (var_b x) = (var_b x).
Proof. induction rho;
       unfold envsubst in *; unfold envsubst' in *; simpl.
       auto.
       destruct a.
       rewrite IHrho. simpl. auto.
Qed.




Lemma envsubst_app : forall rho e1 e2,
 envsubst rho (app e1 e2) = app (envsubst rho e1) (envsubst rho e2).
Admitted.

Lemma envsubst_cons : forall rho x v e,
 (envsubst ((x, v) :: rho) e) = [x ~> (unload v)](envsubst rho e).
Admitted.


Lemma envsubst_fv : forall e rho,
  fv_exp e [<=] dom rho ->
  fv_exp (envsubst rho e) = {}.
Admitted.

Lemma lockstep : forall e rho,
    lc_exp e -> lc_rho rho ->
    fv_exp e [<=] dom rho ->
    match rt_step e rho with
    | res e' rho' => fv_exp e' [<=] dom rho' /\
                    lc_exp e' /\
                    lc_rho rho' /\
                    eval (envsubst rho e) (envsubst rho' e')
    | val v       => lc_val v /\
                    (envsubst rho e) = (unload v)
    | stuck       => not (exists e', eval (envsubst rho e) e')
    end.
Proof.
  induction e; simpl; intros.
  - intros h. destruct h as [e' EVAL].
    rewrite envsubst_var_b in EVAL. inversion EVAL.
  - Case "var_f".
    destruct (binds_lookup rt_val x rho) as [ [y Pf] | Pf ].
    + apply envsubst_var_f in Pf.
      rewrite Pf.
      auto.
    + intros h.
      assert (IN: x `in` dom rho). fsetdec.
      destruct (binds_In_inv _ _ _ IN).
      unfold not in Pf. eauto.
  - Case "abs". apply envsubst_abs.
  - Case "app".
    inversion H.
    assert (FV1 : fv_exp e1 [<=] dom rho). fsetdec.
    assert (FV2 : fv_exp e2 [<=] dom rho). fsetdec.
    pose (IH1 := IHe1 rho H3 FV1). clearbody IH1. clear IHe1.
    pose (IH2 := IHe2 rho H4 FV2). clearbody IH2. clear IHe2.
    destruct (rt_step e1 rho) as [ [T rho' body] | | ].
    + destruct (rt_step e2 rho) as [ v | | ].
      destruct (atom_fresh (dom rho')) as [x Fr].
      rewrite envsubst_app.
      rewrite IH1.
      rewrite IH2.
      rewrite envsubst_cons.
      rewrite envsubst_open.
      rewrite envsubst_var_f_not; auto.
      rewrite <- subst_exp_intro.
      apply eval_beta.
      admit.
      admit.
*)
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


(* Note: this definition does not produce a good induction prinicple.*)
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
    pose (K := fv_exp_subst_exp_upper (nom_envsubst rho e) (nom_unload v) x). clearbody K.
Admitted.

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

(* Note: maybe replace current metalib defn with this one? *)
(*
Program Fixpoint binds_lookup (A:Set) (x:atom) (E:list(atom*A)) :
  {a : A | binds x a E} + (forall a, ~ binds x a E) :=
  match E with
    | nil => inr _
    | (y,v)::E' => if (x == y) then
                    inl (exist _ v  _)
                  else
                    match binds_lookup _ x E' with
                      | inl (exist _ v _) => inl (exist _ v _)
                      | inr _     => inr _
                    end
  end.
Next Obligation.
intros h. inversion h. inversion H0. subst. contradiction.
apply n with (a:= a). auto.
Defined.
*)

Fixpoint rho_lookup x rho :=
  match rho with
  | nom_nil => None
  | nom_cons y v rho' =>
    if (x == y) then
      Some v
    else
      rho_lookup x rho'
  end.

(*
Lemma binds_lookup : forall A x E,
    {a : A | binds x a E} + (forall a, ~ binds x a E).
  Proof with intuition eauto.
    intros.
    induction E. right...
    destruct a as [y v].
    destruct (eq_dec x y).
    left. exists v. subst. auto.
    destruct IHE.
    destruct s. left...
    right...
    inversion H. inversion H0. subst. contradiction.
    apply n0 with (a:=a). unfold binds. auto.
  Defined.
*)

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

Inductive Forall_rho (f : nom_val -> Prop) : nom_env -> Prop :=
| Forall_nom_nil : Forall_rho f nom_nil
| Forall_nom_cons : forall x a rho, f a -> Forall_rho f rho -> Forall_rho f (nom_cons x a rho).

(*
Lemma nom_envsubst_lc : forall rho e, Forall_rho  (fun v => lc_exp (nom_unload v)) rho -> lc_exp e -> lc_exp (nom_envsubst rho e).
Proof.
  induction rho.
  intros; simpl; auto.
  intros; simpl in *.
  inversion H. subst.
  eapply IHrho; eauto.
  eapply subst_exp_lc_exp; eauto.
Qed.
*)

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
(*         match AtomSetProperties.In_dec x (dom rho') with
        | left _ => stuck _
        | right _ => *)
            match nom_bigstep m e2 rho with
            | val _ v1 =>
              nom_bigstep m e1' (nom_cons x v1 rho')
            | r => r
            end
(*         end *)
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
    destruct r2; try solve [inversion H].
    assert (closed_val n0). eapply IHn; eauto. fsetdec.
    eauto.
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
    destruct r2; try solve [inversion H].
    assert (closed_val n0). eapply nom_closed; eauto. fsetdec.

    apply IHn in Heqr1; auto; try fsetdec.
    apply IHn in Heqr2; auto; try fsetdec.
    simpl in Heqr1.
    rewrite nom_envsubst_abs in Heqr1.

    apply IHn in H; eauto.
    simpl in H.

    rewrite nom_envsubst_app.
    econstructor; eauto.
    apply nom_unload_is_value.

    rewrite (subst_exp_intro x).

    Focus 2.
    rewrite fv_closed_env; auto.
    autorewrite with lngen.
    admit.
Admitted.

    pose (IH3 := IHn (nom_cons a v

    fold nom_envsubst.
    assert (C: closed_val n0). eapply IHn; eauto. fsetdec.
    destruct n0 as [x T rho' e1'].
    inversion C.

    assert (closed_val n0). eapply IHn with (e := e2)(rho := rho); eauto. fsetdec.
    eapply IHn with (e:= e1')(rho:= nom_cons x n0 rho'); eauto.
Qed.



(* The next three theorems need to be proven together. To do that we
   will define a combined induction scheme for the mutual typing
   judgements typing_rt_val and typing_rt_env.
 *)
Scheme typing_val_ind' := Induction for typing_rt_val Sort Prop
 with  typing_rt_ind' := Induction for typing_rt_env Sort Prop.

Combined Scheme typing_rt from typing_val_ind', typing_rt_ind'.




Definition swap_var (x:var) (y:var) (z:var) : var :=
  if (z == x) then y else if (z == y) then x else z.
Fixpoint swap_n_exp (x:var) (y:var) (e:n_exp) : n_exp :=
  match e with
  | n_var z => n_var (swap_var x y z)
  | n_abs z T e => n_abs (swap_var x y z) T (swap_n_exp x y e)
  | n_app e1 e2 => n_app (swap_n_exp x y e1) (swap_n_exp x y e2)
  end.

Lemma swap_id_var : forall x z, swap_var x x z = z.
Proof.
  intros.
  unfold swap_var.
  destruct (z == x); subst; auto.
Qed.
Lemma swap_id : forall x e, swap_n_exp x x e = e.
Proof.
  intros. induction e.
  simpl. rewrite swap_id_var. auto.
  simpl. rewrite swap_id_var. rewrite IHe. auto.
  simpl. rewrite IHe1. rewrite IHe2. auto.
Qed.

Lemma swap_swap_var : forall x y z, swap_var x y (swap_var x y z) = z.
Proof. intros.
       unfold swap_var.
       destruct (z == x). destruct (y == x); subst; auto.
       destruct (y == y); subst; auto. contradiction.
       destruct (z == y); subst.
       destruct (x == x); auto; try contradiction.
       destruct (z == x); auto; try contradiction.
       destruct (z == y); auto; try contradiction.
Qed.

Lemma swap_swap : forall x y e, swap_n_exp x y (swap_n_exp x y e) = e.
Proof.
  induction e.
  - simpl. rewrite swap_swap_var. auto.
  - simpl. rewrite swap_swap_var. rewrite IHe. auto.
  - simpl. rewrite IHe1. rewrite IHe2. auto.
Qed.

(* alpha-equivalence relation between named-terms *)
Inductive aeq : n_exp -> n_exp -> Prop :=
  | aeq_var : forall x,
      aeq (n_var x) (n_var x)
  | aeq_app : forall e1 e1' e2 e2',
      aeq e1 e1' -> aeq e2 e2' -> aeq (n_app e1 e2) (n_app e1' e2')
  | aeq_abs_same : forall x T e1 e1',
      aeq e1 e1' -> aeq (n_abs x T e1) (n_abs x T e1')
  | aeq_abs_diff : forall x y T e1 e1',
      (forall z,
          z `notin` nom_fv e1' ->
          z `notin` nom_fv e1  ->  (* perhaps unnecessary *)
          aeq (swap_n_exp z x e1) (swap_n_exp y x e1')) ->
      aeq (n_abs x T e1) (n_abs y T e1').


Inductive named : exp -> n_exp -> Prop :=
 | named_var : forall x , named (var_f x) (n_var x)
 | named_abs : forall x T e1 e2,
     x `notin` fv_exp e1 ->
     named (e1 ^ x) e2 ->
     named (abs T e1) (n_abs x T e2)
 | named_app : forall e1 e2 e1' e2',
     named e1 e1' -> named e2 e2' ->
     named (app e1 e2) (n_app e1' e2').
Hint Constructors named.

(* Named terms have the same free variables as LN terms *)
Lemma named_fv : forall e en, named e en -> fv_exp e [=] nom_fv en.
Proof.
  induction 1; simpl; auto.
  - fsetdec.
  - rewrite <- IHnamed.
    rewrite <- fv_exp_close_exp_wrt_exp.
    rewrite close_exp_wrt_exp_open_exp_wrt_exp.
    fsetdec.
    auto.
  - rewrite IHnamed1.
    rewrite IHnamed2.
    fsetdec.
Qed.

Lemma notin_open : forall x y e1,
      x <> y ->
      y `notin` fv_exp (e1 ^ x) <->
      y `notin` fv_exp e1.
Proof.
  intros.
Admitted.

Lemma named_equivariance :
  forall e ne, named e ne ->
          forall x y, y `notin` fv_exp e ->
                 named ([x ~> y]e) (swap_n_exp x y ne).
Proof.
  induction 1; simpl; intros.
  - unfold swap_var. destruct (x == x0); auto.
    destruct (x == y). subst. fsetdec. auto.
  - unfold swap_var.
    destruct (x == x0); subst.
    destruct (x0 == y); subst.
    + apply (named_abs y).
      rewrite fv_exp_subst_exp_fresh; auto.
      rewrite swap_id. rewrite subst_same. auto.
    + apply (named_abs y).
      rewrite fv_exp_subst_exp_fresh; auto.
      pose (K := subst_exp_open_exp_wrt_exp e1 (var_f y) (var_f x0) x0). clearbody K.
      rewrite subst_eq_var in K.
      rewrite <- K; auto.
      eapply IHnamed.
      rewrite notin_open. auto. auto.
    + destruct (x == y). subst.
      apply (named_abs x0).
      admit.
      rewrite <- (subst_eq_var y (var_f x0)).
      rewrite <- subst_exp_open_exp_wrt_exp.

    rewrite subst_exp_open_exp_wrt_exp_var; auto.




Lemma named_aeq : forall e e1, named e e1 -> forall e2, aeq e1 e2 -> named e e2.
Proof.
  induction 1; intros ne2 AEQ; inversion AEQ; subst; auto.
  (* only real case is when the names don't match in abs. *)
  apply (named_abs x).
  apply (notin_open x); auto.
  rewrite named_fv with (en := e2); auto.

  apply named_fv in H0. rewrite <- H0 in H6.
  rewrite






(* Note: capture-avoiding substitution is difficult to define for
   named representations. *)


(* a variable permutation is a list of "swaps"
   where the domain and range are uniq *)
Definition perm := list (var * var).

Definition permute_var (P : perm) (z:var) : var :=
  match (binds_lookup _ z P) with
  | inl (exist _ y _) => y
  | inr _      => z
  end.
Fixpoint permute_n_exp (P : perm) (e:n_exp) : n_exp :=
  match e with
  | n_var z => n_var (permute_var P z)
  | n_abs z T e => n_abs (permute_var P z) T (permute_n_exp P e)
  | n_app e1 e2 => n_app (permute_n_exp P e1) (permute_n_exp P e2)
  end.


Fixpoint subst_n (u : n_exp) (x:var) (e:n_exp) (scope: atoms) (P : perm) : n_exp :=
  match e with
  | n_var y => if (x == y) then u else (permute_n_exp P e)
  | n_abs z T e =>
    (* capture avoiding substitution *)
    if (x == z) then e else
      let (w,_) := atom_fresh scope in
      n_abs w T (subst_n u x (swap_n_exp w z e) (scope \u {{ w }}))
  | n_app e1 e2 =>
    n_app (subst_n u x e1 scope) (subst_n u x e2 scope)
  end.

















(* Swapped terms are also named *)
Lemma swap_named : forall e ne, named e ne ->
                           forall x y, y `notin` fv_exp e ->
                                  named ([x ~> var_f y]e) (swap_n_exp x y ne).
Proof.
  induction 1; intros; simpl.
  - unfold swap_var. destruct (x == x0).
    auto.
    simpl in *. destruct (x == y). fsetdec. auto.
  - unfold swap_var.
    destruct (x == x0). subst.
    eapply (named_abs y).
    eapply fv_exp_subst_exp_notin. simpl in H1. auto.
