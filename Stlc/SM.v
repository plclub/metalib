Require Import Metalib.Metatheory.

Require Import Stlc.Stlc.
Require Import Stlc.Stlc_inf.

Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 68).

Require Import Stlc.Nominal.




(* ------------------------------------------- *)

(* Translation from machine configurations to LN terms.
   For flexibility in the proof, we decode the
   stack into a stack of LN frames, before applying the
   decoded stack to LN terms.

   In this way, we only need to use LN substitution.
   We do not need to define (capture-avoiding) substitution
   for nominal terms.
 *)

Fixpoint nom_to_exp (ne : n_exp) : exp :=
  match ne with
  | n_var x => var_f x
  | n_app e1 e2 => app (nom_to_exp e1) (nom_to_exp e2)
  | n_abs x e1 => abs (close_exp_wrt_exp x (nom_to_exp e1))
end.

Fixpoint apply_heap (h : heap) (e : exp) : exp  :=
  match h with
  | nil => e
  | (x , e') :: h' => apply_heap h' (subst_exp (nom_to_exp e') x e)
  end.

Fixpoint apply_stack h (s : list frame) (e :exp) : exp :=
  match s with
  | nil => e
  | n_app2 e' :: s' => apply_stack h s' (app e (apply_heap h (nom_to_exp e')))
  end.

Definition decode (c:conf) : exp  :=
  match c with
  | (h,e,s) => apply_stack h s (apply_heap h (nom_to_exp e))
  end.



(* -----------------------------------------  *)

(* Here's our first result about our decoding: that the two
   free variable functions agree. *)

Lemma fv_nom_fv_exp_eq : forall n,
    fv_nom n [=] fv_exp (nom_to_exp n).
Proof.
  induction n; intros; simpl; autorewrite with lngen; fsetdec.
Qed.

Hint Rewrite fv_nom_fv_exp_eq : lngen.
Hint Resolve fv_nom_fv_exp_eq : lngen.

(* -----------------------------------------  *)

(* It is straightforward to show our decoding of nominal terms and
   configurations produces locally closed LN terms. *)

Lemma nom_to_exp_lc : forall t, lc_exp (nom_to_exp t).
Proof.
  induction t; simpl in *; eauto with lngen.
Qed.
Hint Resolve nom_to_exp_lc : lngen.

Lemma apply_heap_lc : forall h e,
    lc_exp e -> lc_exp (apply_heap h e).
Proof.
  alist induction h; simpl in *; auto with lngen.
Qed.
Hint Resolve apply_heap_lc : lngen.

Lemma apply_stack_lc : forall s h e,
    lc_exp e -> lc_exp (apply_stack h s e).
Proof.
  induction s; try destruct a; simpl in *; auto with lngen.
Qed.
Hint Resolve apply_stack_lc : lngen.

Lemma decode_lc : forall c, lc_exp (decode c).
Proof.
  intro c; destruct c as [[h e] s]; simpl in *; auto with lngen.
Qed.

(* ------------------------------------------ *)

(* Since the heap is just an iterated substitution,
   it inherits properties from [subst_exp]. *)

Hint Rewrite subst_exp_open_exp_wrt_exp : lngen.

Lemma apply_heap_abs : forall h e,
  apply_heap h (abs e) = abs (apply_heap h e).
Proof.
  alist induction h; simpl in *; auto with lngen.
Qed.

Hint Rewrite apply_heap_abs : lngen.

Lemma apply_heap_app : forall h e1 e2,
  apply_heap h (app e1 e2) = app (apply_heap h e1) (apply_heap h e2).
Proof.
  alist induction h; simpl in *; auto with lngen.
Qed.

Hint Rewrite apply_heap_app : lngen.

Lemma apply_heap_open : forall h e e0,
    lc_exp e0 ->
    apply_heap h (open_exp_wrt_exp e e0)  =
       open_exp_wrt_exp (apply_heap h e) (apply_heap h e0).
Proof.
  alist induction h; intros; simpl in *; autorewrite with lngen; auto with lngen.
Qed.

Hint Rewrite apply_heap_open : lngen.

(* This last lemma "unsimpl"s the 'apply_heap' function. *)
Lemma combine : forall h x e e',
  apply_heap h ([x ~> nom_to_exp e] e') = (apply_heap ((x,e)::h) e').
Proof.
  simpl. auto.
Qed.

(* ----------------------------------------------------------------- *)

(* Next, we define when a heap is *well-scoped*.
   well-scoped heaps behave "telescopically".
   Each binding (x,e) added to the heap is
   for a unique name x and the free variables
   of e are bound in the remainder of the heap.
*)

Inductive scoped_heap (D : atoms) : heap -> Prop :=
  | scoped_nil  : scoped_heap D nil
  | scoped_cons : forall x e h,
      x `notin` dom h \u D ->
      fv_exp (nom_to_exp e) [<=] dom h \u D ->
      scoped_heap D h ->
      scoped_heap D ((x,e)::h).


Lemma scoped_get : forall h D1 D2 x e,
  scoped_heap D1 h ->
  get x h = Some e ->
  dom h \u D1 [<=] D2 ->
  fv_exp (nom_to_exp e) [<=] D2.
Proof.
  induction 1; intros; default_simp.
  fsetdec.
  eapply IHscoped_heap; auto; fsetdec.
Qed.

Lemma apply_heap_get :  forall h D x e,
    scoped_heap D h ->
    get x h = Some e ->
    apply_heap h (var_f x) = apply_heap h (nom_to_exp e).
Proof.
  induction 1; intros; default_simp.
  rewrite subst_exp_fresh_eq; auto.
  rewrite H0. auto.
  rewrite subst_exp_fresh_eq; auto.
  rewrite scoped_get with (D2:= dom h\u D );  eauto with lngen.
Qed.

(* ------------------------------------------ *)

(* We also care about the free variables that can appear
   in stacks. *)

Fixpoint fv_stack s :=
  match s with
    nil => {}
  | n_app2 e :: s => fv_exp (nom_to_exp e) \u fv_stack s
  end.

(* TODO: how do we get inductive proofs to automatically
   rewrite with the IH? *)
Lemma apply_stack_fresh_eq : forall s x e1 h ,
    x `notin` fv_stack s ->
    apply_stack ((x, e1) :: h) s = apply_stack h s.
Proof.
  induction s; intros; try destruct a; simpl in *; auto with lngen.
  rewrite subst_exp_fresh_eq; auto.
  rewrite IHs; auto.
Qed.

Lemma apply_stack_cong : forall s h e e',
    step e e' ->
    step (apply_stack h s e) (apply_stack h s e').
Proof.
  induction s; intros; try destruct a; simpl in *; auto with lngen.
Qed.


(* ------------------------------------------ *)

(* Next, we show that nominal terms are aeq iff they decode
   to the same LN terms.

   The tricky part of this reasoning below is a lemma that lets us
   convert swapping (with fresh variables) in the nominal calculus
   to substitution in the LN representation.

<<
Lemma swap_spec : forall  n w y,
    y `notin` fv_exp (nom_to_exp n) ->
    w <> y ->
    [w ~> var_f y] (nom_to_exp n) =
    nom_to_exp (swap w y n).
>>

 *)

(* SCW: Make LNgen generate this? *)
Lemma close_exp_wrt_exp_freshen : forall x y e,
    y `notin` fv_exp e ->
    close_exp_wrt_exp x e =
    close_exp_wrt_exp y ([x ~> var_f y] e).
Proof.
  intros x y e.
  unfold close_exp_wrt_exp.
  generalize 0 as k.
  generalize e. clear e.
  induction e; default_simp.
Qed.


Lemma swap_spec_aux : forall m t w y,
    size t <= m ->
    y `notin` fv_exp (nom_to_exp t) ->
    w <> y ->
    [w ~> var_f y] (nom_to_exp t) =
    nom_to_exp (swap w y t).
Proof.
  induction m; intros t w y SZ;
  destruct t; simpl in *; try omega;
  intros.
  + default_simp.
  + default_simp.
    { (* w is the binder *)
      autorewrite with lngen in *.
      rewrite subst_exp_fresh_eq;
        autorewrite with lngen in *; try fsetdec.
      rewrite <- IHm; auto; try omega.
      rewrite subst_exp_spec.
      rewrite close_exp_wrt_exp_open_exp_wrt_exp. auto.
      autorewrite with lngen. fsetdec. }
    { (* y is the binder *)
       autorewrite with lngen in *.
       (* don't know anything about w or y. Either one could
          appear in n. So our IH is useless now. *)
       (* Let's pick a fresh variable z and use it with that. *)
       pick fresh z for (
              fv_exp (nom_to_exp t) \u
              fv_exp (nom_to_exp (swap w y t)) \u {{w}} \u {{y}}).

       rewrite (close_exp_wrt_exp_freshen y z); auto.
       rewrite subst_exp_close_exp_wrt_exp; auto.

       rewrite IHm; auto; try omega.
       rewrite (close_exp_wrt_exp_freshen w z); auto.

       rewrite IHm; auto; try rewrite swap_size_constant; try omega.
       rewrite IHm; auto; try rewrite swap_size_constant; try omega.

       rewrite shuffle_swap; auto.
       rewrite <- fv_nom_fv_exp_eq.
       apply fv_nom_swap.
       rewrite fv_nom_fv_exp_eq.
       fsetdec.
    }
    { (* neither are binders *)
       rewrite <- IHm; auto; try omega.
       rewrite subst_exp_close_exp_wrt_exp; auto.
       autorewrite with lngen in *.
       fsetdec.
    }
  + rewrite IHm; auto; try omega; try fsetdec.
    rewrite IHm; auto; try omega; try fsetdec.
Qed.

Lemma swap_spec : forall t w y,
    y `notin` fv_exp (nom_to_exp t) ->
    w <> y ->
    [w ~> var_f y] (nom_to_exp t) =
    nom_to_exp (swap w y t).
Proof.
  intros.
  eapply swap_spec_aux with (t:=t)(m:=size t); auto.
Qed.

Lemma aeq_nom_to_exp : forall n1 n2, aeq n1 n2 -> nom_to_exp n1 = nom_to_exp n2.
Proof.
  induction 1; default_simp;
  autorewrite with lngen in *.
  - congruence.
  - rewrite (close_exp_wrt_exp_freshen y x); auto.
    rewrite swap_spec; auto.
    congruence.
Qed.

Lemma nom_to_exp_eq_aeq : forall n1 n2, nom_to_exp n1 = nom_to_exp n2 -> aeq n1 n2.
Proof.
  induction n1; intro n2; destruct n2; default_simp.
  destruct (x == x0).
  - subst. eauto with lngen.
  - assert (FX : x `notin` fv_exp (nom_to_exp n2)).
    { intro IN.
      assert (x `in` fv_exp (nom_to_exp (n_abs x0 n2))).
      { simpl. autorewrite with lngen. fsetdec. }
      simpl in *.
      rewrite <- H0 in H.
      autorewrite with lngen in *.
      fsetdec. }
    eapply aeq_abs_diff; auto.
    + autorewrite with lngen. auto.
    + eapply IHn1.
      rewrite <- swap_spec; eauto.
      rewrite subst_exp_spec.
      rewrite <- H0.
      autorewrite with lngen.
      auto.
Qed.

(* --------------------------------------------------------------- *)

Inductive scoped_conf : atoms -> conf -> Prop :=
  scoped_conf_witness : forall D h e s,
    scoped_heap D h ->
    fv_exp (nom_to_exp e) [<=] dom h \u D ->
    fv_stack s [<=] dom h \u D  ->
    scoped_conf D (h,e,s).


(* Could be zero or one steps! *)
Lemma simulate_step : forall D h e s h' e' s' ,
    machine_step (dom h \u D) (h,e,s) = TakeStep _ (h',e',s') ->
    scoped_conf D (h,e,s) ->
    decode (h,e,s) = decode (h',e',s') \/
    step (decode (h,e,s)) (decode (h',e',s')).
Proof.
  intros D h e s h' e' s' STEP SCOPE.
  inversion SCOPE; subst; clear SCOPE.
  simpl in *.
  destruct (isVal e) eqn:?.
  destruct s.
  - inversion STEP.
  - destruct f eqn:?.
    + destruct e eqn:?; try solve [inversion STEP].
       right.
       destruct AtomSetProperties.In_dec;
       try destruct atom_fresh;
       inversion STEP; subst; clear STEP;
       simpl in *;
       rewrite combine;
       rewrite apply_stack_fresh_eq; auto; try fsetdec;
       apply apply_stack_cong;
       autorewrite with lngen in *;
       simpl.

       -- assert (x <> x0) by fsetdec.
          rewrite <- swap_spec; auto; try fsetdec.
          rewrite (subst_exp_spec _ _ x).
          autorewrite with lngen; auto with lngen.
          default_simp.
          rewrite subst_exp_fresh_eq; autorewrite with lngen; auto.

          apply step_beta; auto with lngen.
          rewrite <- apply_heap_abs.
          eapply apply_heap_lc.
          auto with lngen.

          rewrite H4. fsetdec.
       -- rewrite subst_exp_spec.
          rewrite apply_heap_open; auto with lngen.

          apply step_beta; auto with lngen.
          rewrite <- apply_heap_abs.
          eapply apply_heap_lc.
          auto with lngen.

  - destruct e eqn:?; try solve [inversion STEP].
    + destruct (get x h) eqn:?; inversion STEP; subst; clear STEP.
      left.
      f_equal.
      apply apply_heap_get with (D:= D); auto.
    + inversion STEP; subst; clear STEP.
      left.
      simpl.
      rewrite apply_heap_app.
      auto.
Qed.

Lemma simulate_done : forall D h e s,
    machine_step (dom h \u D) (h,e,s) = Done _ ->
    scoped_heap D h ->
    fv_exp (nom_to_exp e) [<=] dom h \u D ->
    fv_stack s [<=] dom h \u D ->
    is_value (nom_to_exp e).
Proof.
  intros.
  simpl in *.
  destruct (isVal e) eqn:?.
  destruct s eqn:?.
  - destruct e; simpl in Heqb; inversion Heqb.
    econstructor; eauto.
  - destruct f eqn:?.
     + destruct e eqn:?; try solve [inversion H].
       econstructor; eauto.
  - destruct e; inversion H.
    simpl in Heqb. destruct (get x h); inversion H.
Qed.


(*
Lemma machine_is_scoped: forall D h e s h' e' s',
    machine_step D (h,e,s) = TakeStep _ (h',e',s') ->
    scoped_heap D h  /\ fv_exp (nom_to_exp e)  [<=] dom h \u D /\ fv_stack s [<=] dom h ->
    scoped_heap D h' /\ fv_exp (nom_to_exp e') [<=] dom h' \u D /\ fv_stack s' [<=] dom h'.
Proof.
  intros.
  simpl in H.
  destruct H0 as [SH [SE SS]].
  destruct (isVal e) eqn:?.
  destruct s eqn:?.
  - inversion H.
  - destruct f eqn:?.
     + destruct e eqn:?; try solve [inversion H].
       destruct (AtomSetProperties.In_dec x (dom h)).
       ++ destruct (atom_fresh (dom h)).
          inversion H; subst; clear H.
          simpl in *.
          split.
            econstructor; eauto. fsetdec.
          split.
            assert (x <> x0). fsetdec.
            autorewrite with lngen in SE.
            rewrite <- swap_spec; try fsetdec.
            rewrite fv_exp_subst_exp_upper.
            simpl.
            fsetdec.
          fsetdec.
       ++ inversion H; subst; clear H.
          simpl in *.
          autorewrite with lngen in *.
          repeat split; try fsetdec.
          econstructor; eauto. fsetdec.
          rewrite <- SE.
          eapply FSetDecideTestCases.test_Subset_add_remove.
  - destruct e eqn:?; try solve [inversion H].
    destruct (get x h) eqn:?;
    inversion H; subst; clear H.
    + split. auto.
      simpl in *.
      split. eapply scoped_get; eauto.
      fsetdec.
      auto.
    + simpl in *.
    inversion H; subst; clear H.
    split; auto.
    split; try fsetdec.
    simpl. fsetdec.
Qed.
*)

(* TODO: completeness *)
(*
Lemma completeness : forall e0 e0' h e s,
    step e0 e0' ->
    scoped_heap h ->
    fv_exp (nom_to_exp e) [<=] dom h ->
    fv_stack s [<=] dom h ->
    decode (h,e,s) = e0 ->
    exists h', exists e', exists s', machine_step (h,e,s) = TakeStep _ (h',e',s').
Proof.
  induction 1.
  - intros.
    destruct e; simpl in H4.
    simpl in H2.
    exists h , (app (abs e1) v).
*)