Require Import Metalib.Metatheory.

Require Import Stlc.Stlc.
Require Import Stlc.Stlc_inf.


Notation open e a := (open_exp_wrt_exp e a).



Definition Heap := list (atom * exp).

Inductive StackElem : Set :=
| ApplyTo : exp -> StackElem.

Definition Conf := (Heap * exp * list StackElem)%type.

Definition initConf (e : exp) : Conf := (nil,e,nil).

(* The semantics *)

Inductive Step a := Error   : Step a
                 | Done     : Step a
                 | TakeStep : a -> Step a.

Definition isVal (e : exp) :=
  match e with
  | abs _ => true
  | _     => false
  end.

Definition isTrivial (e: exp) :=
  match e with
  | var_f _ => true
  | _       => false
end.



Definition machine_step (c : Conf) : Step Conf := match c with (heap, e, stack) =>
  match isVal e with
  | true => match stack with
               | nil => Done _
       (*      | Update v :: stack' => TakeStep (updateOnHeap v e heap, e, stack') *)
               | ApplyTo a :: stack' =>
                 match e with
                 | abs e =>
                   match isTrivial a with
                   | true => TakeStep _ (heap, open e a, stack')
                   | false =>   let (fresh,_) := atom_fresh (dom heap) in
                              TakeStep _ ((fresh, a):: heap,
                                        open e (var_f fresh), stack')
                   end
                 | _ => Error _ (* non-function applied to argument *)
                 end
               end
  | false  =>  match e with
            | var_f v => match get v heap with
                      | Some e => TakeStep _ (heap, e, stack)
                      (*          if isVal e
                    then TakeStep (heap, e, stack)
                    else TakeStep (heap, e, Update v :: stack) *)
                      | Nothing => Error _ (* Unbound variable *)
                      end
            | app e1 e2 => TakeStep _ (heap, e1, ApplyTo e2 :: stack)
            | _ => Error _ (* should be unreachable (value in nonValueStep) *)
            end
  end
end.


(*
Example run (may take extra steps):

      {}, (\y. (\x. x) y) 0 , nil                     (\y. (\x. x) y) 0
  ==> {}, (\y. (\x. x) y), ApplyTo 0 :: nil           (\y. (\x. x) y) 0
  ==> {y -> 0}, (\x.x) y, nil                         (\x. x) 0
  ==> {y -> 0}, (\x.x), ApplyTo y :: nil              (\x. x) 0
  ==> {y -> 0}, y , nil                               0
  ==> {y -> 0}, 0 , nil                               0
  ==> Done

decode {y -> 0}, (\x.x), ApplyTo y :: nil
  == apply_heap { y -> 0 } (apply_stack (ApplyTo y :: nil) (\x.x)
  == (ApplyTo 0 :: nil) (\x.x)
  == (\x.x) 0

*)



Fixpoint apply_stack (s : list StackElem) e :=
  match s with
  | nil => e
  | ApplyTo e' :: s' => apply_stack s' (app e e')
  end.

Lemma app_cong : forall s e e',
    step e e' ->
    step (apply_stack s e) (apply_stack s e').
Proof.
  induction s.
  intros; simpl. auto.
  intros; simpl.
  destruct a.
  apply IHs.
  econstructor. admit.
  auto.
Admitted.

Fixpoint apply_heap (h : Heap) e  :=
  match h with
  | nil => e
  | (x , e') :: h' => apply_heap h' (subst_exp e' x e)
  end.

Lemma apply_heap_abs : forall h e,
  apply_heap h (abs e) = abs (apply_heap h e).
Proof.
  induction h; intros; simpl; auto.
  destruct a as [y e0]. eauto.
Qed.

Lemma apply_heap_app : forall h e1 e2,
  apply_heap h (app e1 e2) = app (apply_heap h e1) (apply_heap h e2).
Proof.
  induction h; intros; try destruct a; simpl; eauto.
Qed.

Lemma apply_heap_open : forall h e e0,
    apply_heap h (open e e0)  = open (apply_heap h e) (apply_heap h e0).
Proof.
  induction h; intros; simpl.
  auto.
  destruct a.
  rewrite subst_exp_open_exp_wrt_exp.
  rewrite IHh.
  eauto.
  admit. (* LC *)
Admitted.

Fixpoint apply_heap_stack h s :=
  match s with
  | nil => nil
  | ApplyTo a::s' => ApplyTo (apply_heap h a) :: apply_heap_stack h s'
  end.

Lemma apply_heap_apply_stack : forall h s e,
      apply_heap h (apply_stack s e) =
      apply_stack (apply_heap_stack h s) (apply_heap h e).
Proof.
  induction s; intros; try destruct a; simpl in *; eauto.
  rewrite IHs. rewrite apply_heap_app. auto.
Qed.


Lemma push :
  forall s e e',
    apply_stack s (app (abs e) e') =
    apply_stack (ApplyTo e' :: s) (abs e).
simpl. auto.
Qed.

Lemma combine : forall h x e e',
  apply_heap h ([x ~> e] e') = (apply_heap ((x,e)::h) e').
Proof.
  simpl. auto.
Qed.

Fixpoint fv_heap  (h : Heap) :=
  match h with nil => {} | (x,e) :: h => fv_exp e \u fv_heap h end.


Inductive scoped_heap : Heap -> Prop :=
  | scoped_nil  : scoped_heap nil
  | scoped_cons : forall x e h,
      x `notin` dom h ->
      fv_exp e [<=] dom h ->
      scoped_heap h ->
      scoped_heap ((x,e)::h).

Lemma scoped_heap_fv_heap_dom : forall h,
    scoped_heap h -> fv_heap h [<=] dom h.
Proof.
  induction h.
  simpl. fsetdec.
  simpl. destruct a as [x e0]; simpl.
  intro k. inversion k. subst.
  rewrite IHh; auto.
  fsetdec.
Qed.

Lemma fv_apply_heap : forall e h,
    scoped_heap h ->
    fv_exp e [<=] dom h ->
    fv_exp (apply_heap h e) [<=] dom h.
Proof.
  intros e h Sc.
  apply scoped_heap_fv_heap_dom in Sc.
  remember (dom h) as D.
  revert Sc.
  generalize e.
  generalize h.
  induction h0; intros; simpl in *. fsetdec.
  destruct a as [x e1]; simpl in *.
  rewrite IHh0; auto. fsetdec.
  fsetdec.
  rewrite fv_exp_subst_exp_upper.
  fsetdec.
Qed.

Fixpoint fv_stack s :=
  match s with nil => {} | ApplyTo e :: s => fv_exp e \u fv_stack s end.

Lemma scoped_get : forall h x e,
  scoped_heap h ->
  get x h = Some e ->
  fv_exp e [<=] dom h.
Proof.
  intros.
  apply scoped_heap_fv_heap_dom in H.
  remember (dom h) as D.
  revert H H0.
  generalize h.
  induction h0; intros; simpl in *;
  inversion H0.
  destruct a as [y e0].
  destruct (KeySetFacts.eq_dec x y).
  inversion H2.
  subst.
  fsetdec.
  eapply IHh0.
  fsetdec.
  auto.
Qed.

Lemma machine_is_scoped: forall h e s h' e' s',
    machine_step (h,e,s) = TakeStep _ (h',e',s') ->
    scoped_heap h /\ fv_exp e [<=] dom h /\ fv_stack s [<=] dom h ->
    scoped_heap h' /\ fv_exp e' [<=] dom h' /\ fv_stack s [<=] dom h.
Proof.
  intros.
  simpl in H.
  destruct H0 as [SH [SE SS]].
  destruct (isVal e) eqn:?.
  destruct s eqn:?.
  - inversion H.
  - destruct s0 eqn:?.
     + destruct e eqn:?; try solve [inversion H].
       destruct (isTrivial e0) eqn:?.
       ++ destruct e0; inversion Heqb0.
          inversion H; subst; clear H; split; auto.
          simpl in *.
          rewrite fv_exp_open_exp_wrt_exp_upper.
          simpl.
          split; fsetdec.
       ++ destruct (atom_fresh (dom h)).
          inversion H; subst; clear H.
          simpl in *.
          split. econstructor; eauto. fsetdec.
          split.
          rewrite fv_exp_open_exp_wrt_exp_upper.
          simpl.
          fsetdec.
          auto.
  - destruct e eqn:?; try solve [inversion H].
    destruct (get x h) eqn:?;
    inversion H; subst; clear H.
    + split. auto.
      simpl in *.
      split. eapply scoped_get; eauto.
      auto.
    + simpl in *.
    inversion H; subst; clear H.
    split; auto.
    split; fsetdec.
Qed.

Lemma apply_heap_fresh_eq : forall x e1 h e,
    x `notin` dom h ->
    fv_exp e [<=] dom h ->
    apply_heap ((x, e1) :: h) e = apply_heap h e.
Proof.
  induction h; intros; simpl; eauto.
  rewrite subst_exp_fresh_eq; auto.
  destruct a.
  simpl in *.
  rewrite (subst_exp_fresh_eq e); auto.
Qed.

Lemma apply_heap_stack_fresh_eq : forall s x e1 h ,
    scoped_heap h ->
    x `notin` dom h ->
    fv_stack s [<=] dom h ->
    apply_heap_stack ((x, e1) :: h) s = apply_heap_stack h s.
Proof.
  induction s; intros; simpl; eauto.
  simpl in H.
  destruct a.
  simpl in *.
  rewrite IHs; simpl; eauto.
  rewrite subst_exp_fresh_eq; auto.
  fsetdec.
Qed.

Lemma apply_heap_var : forall h x e1,
    x `notin` dom h ->
    x `notin` fv_heap h ->
    (apply_heap ((x, e1) :: h) (var_f x)) = apply_heap h e1.
Proof. induction h; intros; simpl.
       destruct (x==x). auto. contradiction.
       destruct a as [y e2].
       destruct (x ==x). auto.
       simpl. destruct (x==y). contradiction.
       contradiction.
Qed.


Lemma apply_heap_get :  forall h x e,
    scoped_heap h ->
    get x h = Some e ->
    apply_heap h (var_f x) = apply_heap h e.
Proof.
  induction 1.
  intros; simpl in *. inversion H.
  intros; simpl in *.
  destruct (KeySetFacts.eq_dec x x0); subst.
  destruct (x0 == x0); try contradiction.
  inversion H2; subst; clear H2.
  rewrite subst_exp_fresh_eq; auto.
  destruct (x == x0); try contradiction.
  rewrite subst_exp_fresh_eq; auto.
  apply scoped_get in H2.
  fsetdec.
  auto.
Qed.

Definition decode (c:Conf) : exp :=
  match c with
  | (h,e,s) => apply_heap h (apply_stack s e)
  end.

(* Could be zero steps! *)
Lemma simulate_step : forall h e s h' e' s' e0 e0',
    machine_step (h,e,s) = TakeStep _ (h',e',s') ->
    scoped_heap h ->
    fv_exp e [<=] dom h ->
    fv_stack s [<=] dom h ->
    e0 = decode (h,e,s) ->
    e0' = decode (h',e',s') ->
    e0 = e0' \/ step e0 e0'.
Proof.
  intros.
  simpl in *.
  destruct (isVal e) eqn:?.
  destruct s eqn:?.
  - inversion H.
  - destruct s0 eqn:?.
     + destruct e eqn:?; try solve [inversion H].
       destruct (isTrivial e1).
       ++ inversion H; subst; clear H.
          simpl in *.
          right.
          rewrite apply_heap_apply_stack.
          rewrite apply_heap_apply_stack.
          apply app_cong.
          rewrite apply_heap_app.
          rewrite apply_heap_abs.
          rewrite apply_heap_open.
          econstructor.
          admit. (* LC *)
          admit. (* LC *)
       ++ subst. destruct (atom_fresh).
          inversion H; subst; clear H.
          right.
          simpl in *.
          rewrite combine.
          rewrite apply_heap_apply_stack.
          rewrite apply_heap_apply_stack.

          rewrite apply_heap_app.
          rewrite apply_heap_abs.

          rewrite apply_heap_stack_fresh_eq; auto; try fsetdec.
          apply app_cong.

          rewrite apply_heap_open.
          rewrite apply_heap_var; eauto.

          rewrite apply_heap_fresh_eq.

          econstructor; eauto.
          admit. (* LC *)
          admit. (* LC *)
          auto.
          auto.
          apply scoped_heap_fv_heap_dom in H0.
          fsetdec.
  - destruct e eqn:?; try solve [inversion H].
    destruct (get x h) eqn:?; try solve [inversion H].
    + inversion H; subst; clear H.
      left.
      rewrite apply_heap_apply_stack.
      rewrite apply_heap_apply_stack.
      f_equal.
      apply apply_heap_get; auto.
    + inversion H; subst; clear H.
      left.
      simpl.
      auto.
Admitted.

Lemma simulate_done : forall h e s,
    machine_step (h,e,s) = Done _ ->
    scoped_heap h ->
    fv_exp e [<=] dom h ->
    fv_stack s [<=] dom h ->
    is_value e.
Proof.
  intros.
  simpl in *.
  destruct (isVal e) eqn:?.
  destruct s eqn:?.
  - destruct e; simpl in Heqb; inversion Heqb.
    econstructor; eauto.
  - destruct s0 eqn:?.
     + destruct e eqn:?; try solve [inversion H].
       destruct (isTrivial e0).
       econstructor; eauto.
       econstructor; eauto.
  - destruct e; inversion H.
    simpl in Heqb. destruct (get x h); inversion H.
Qed.