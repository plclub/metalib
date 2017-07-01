Require Import Metalib.Metatheory.

Require Import Stlc.Stlc.
Require Import Stlc.Stlc_inf.


Notation open e a := (open_exp_wrt_exp e a).


(*************************************************************)
(*   Connection to nominal representation of terms           *)
(*************************************************************)

(* A named representation of STLC terms.
   No debruijn indices, and binders include the names of free variables. *)

Inductive n_exp : Set :=
 | n_var (x:var)
 | n_abs (x:var) (e:n_exp)
 | n_app (e1:n_exp) (e2:n_exp).

(* We can rename variables *)
Definition swap_var (x:var) (y:var) (z:var) : var :=
  if (z == x) then y else if (z == y) then x else z.
Fixpoint swap (x:var) (y:var) (e:n_exp) : n_exp :=
  match e with
  | n_var z => n_var (swap_var x y z)
  | n_abs z e => n_abs (swap_var x y z) (swap x y e)
  | n_app e1 e2 => n_app (swap x y e1) (swap x y e2)
  end.


(* An abstract machine for named terms *)

Definition heap := list (atom * n_exp).

Inductive frame : Set :=
| n_app2 : n_exp -> frame.

Definition conf := (heap * n_exp * list frame)%type.

Definition initconf (e : n_exp) : conf := (nil,e,nil).

(* The semantics *)

Inductive Step a := Error   : Step a
                 | Done     : Step a
                 | TakeStep : a -> Step a.

Definition isVal (e : n_exp) :=
  match e with
  | n_abs _ _ => true
  | _         => false
  end.






Definition machine_step (c : conf) : Step conf :=
  match c with (heap, e, stack) =>
  match isVal e with
  | true => match stack with
               | nil => Done _
               | n_app2 a :: stack' =>
                 match e with
                 | n_abs x e =>
(*                   match a with
                   | n_var y => TakeStep _ (heap, swap x y e, stack')
                   | _     => *)
                     let (fresh,_) := atom_fresh (dom heap) in
                     TakeStep _ ((fresh, a):: heap, swap x fresh e, stack')
(*                    end *)
                 | _ => Error _ (* non-function applied to argument *)
                 end
               end
  | false  =>  match e with
            | n_var x => match get x heap with
                      | Some e => TakeStep _ (heap, e, stack)
                      | Nothing => Error _ (* Unbound variable *)
                      end
            | n_app e1 e2 => TakeStep _ (heap, e1, n_app2 e2 :: stack)
            | _ => Error _ (* should be unreachable (value in nonValueStep) *)
            end
  end
end.


(*
Example run (may take extra steps):

      {}, (\y. (\x. x) y) 0 , nil                  (\y. (\x. x) y) 0
  ==> {}, (\y. (\x. x) y), app2 0 :: nil           (\y. (\x. x) y) 0
  ==> {y -> 0}, (\x.x) y, nil                      (\x. x) 0
  ==> {y -> 0}, (\x.x), app2 y :: nil              (\x. x) 0
  ==> {y -> 0}, y , nil                            0
  ==> {y -> 0}, 0 , nil                            0
  ==> Done

decode {y -> 0}, (\x.x), app2 y :: nil
  == apply_heap { y -> 0 } (apply_stack (app2 y :: nil) (\x.x)
  == (app2 0 :: nil) (\x.x)
  == (\x.x) 0

*)

(* ------------------------------------------- *)

(* Translation from machine configurations to LN terms *)

Fixpoint nom_to_exp (ne : n_exp) : exp :=
  match ne with
  | n_var x => var_f x
  | n_app e1 e2 => app (nom_to_exp e1) (nom_to_exp e2)
  | n_abs x e1 => abs (close_exp_wrt_exp x (nom_to_exp e1))
end.

Inductive decoded_frame :=
  | app2 : exp -> decoded_frame.

Fixpoint  decode_stack (s : list frame) : list decoded_frame :=
  match s with
  | nil => nil
  | n_app2 e :: s' => app2 (nom_to_exp e) :: decode_stack s'
  end.

Fixpoint apply_stack (s : list decoded_frame) (e :exp) : exp :=
  match s with
  | nil => e
  | app2 e' :: s' => apply_stack s' (app e e')
  end.

(* Note: this is exp -> exp because that is where substitution
   is defined *)
Fixpoint apply_heap (h : heap) (e : exp) : exp  :=
  match h with
  | nil => e
  | (x , e') :: h' => apply_heap h' (subst_exp (nom_to_exp e') x e)
  end.


Definition decode (c:conf) : exp  :=
  match c with
  | (h,e,s) => apply_heap h (apply_stack (decode_stack s) (nom_to_exp e))
  end.

(* -----------------------------------------  *)

Lemma nom_to_exp_lc : forall ne, lc_exp (nom_to_exp ne).
Proof.
  induction ne; simpl; auto.
  eapply lc_abs_exists with (x1 := x).
  rewrite open_exp_wrt_exp_close_exp_wrt_exp.
  auto.
Qed.

Hint Resolve nom_to_exp_lc : lngen.

Lemma apply_heap_lc : forall h e,
    lc_exp e ->
    lc_exp (apply_heap h e).
Proof.
  induction h; simpl.
  auto.
  intros; destruct a as [y e0].
  eauto with lngen.
Qed.

Hint Resolve apply_heap_lc : lngen.



Lemma decode_lc : forall c, lc_exp (decode c).
Proof.
  intro c.
  destruct c as [[h e] s].
  simpl.
  eauto with lngen.
Admitted.

(* ------------------------------------------ *)

(* This is the hard part --- the definition of alpha equivalence
   and the proof that alpha-equivalent named terms
   map to the same LN term. *)

Lemma swap_swap: forall x y n,
  swap x y (swap x y n) = n.
Admitted.

Lemma swap_id : forall x n,
    swap x x n = n.
Admitted.


Fixpoint size (n : n_exp) : nat :=
  match n with
  | n_var x => 1
  | n_abs x e => 1 + size e
  | n_app e1 e2 => 1 + size e1 + size e2
  end.

Lemma swap_size_constant : forall x y n,
    size n = size (swap x y n).
Proof.
  induction n; simpl; auto.
Qed.

Fixpoint support (n : n_exp) : atoms :=
  match n with
  | n_var x => {{x}}
  | n_abs x n => AtomSetImpl.remove x (support n)
  | n_app n1 n2 => support n1 `union` support n2
  end.

Lemma support_fv_exp_eq : forall n,
    fv_exp (nom_to_exp n) [=] support n.
Proof.
  induction n; intros; simpl; autorewrite with lngen; try fsetdec.
Qed.

Inductive aeq : n_exp -> n_exp -> Prop :=
 | aeq_var : forall x, aeq (n_var x) (n_var x)
 | aeq_abs_same : forall x n1 n2, aeq n1 n2 -> aeq (n_abs x n1) (n_abs x n2)
 | aeq_abs_diff : forall x y n1 n2,
     x <> y ->
     x `notin` support n2 ->
     aeq n1 (swap y x n2) ->
     aeq (n_abs x n1) (n_abs y n2)
 | aeq_app : forall n1 n2 n1' n2',
     aeq n1 n1' -> aeq n2 n2' -> aeq (n_app n1 n2) (n_app n1' n2').

Hint Constructors aeq.

Lemma notin_other : forall x y S, x <> y -> x `notin` remove y S -> x `notin` S.
intros. fsetdec.
Qed.

(*
[x ~> y] (\y. x) = \. y
swap x y (\y. x) = \. y
*)

Lemma swap_spec : forall n w y,
    y `notin` fv_exp (nom_to_exp n) ->
    w <> y ->
    [w ~> var_f y] (nom_to_exp n) =
    nom_to_exp (swap w y n).
Proof.
  induction n; intros; simpl in *.
  + unfold swap_var.
    destruct (x == w); auto.
    destruct (x == y); auto.
    fsetdec.
  + unfold swap_var.
    destruct (x == w). subst.
    ++ (* w is the binder *)
       rewrite subst_exp_fresh_eq; auto.
       rewrite <- IHn.
       rewrite subst_exp_spec.
       autorewrite with lngen.
       auto.
       rewrite fv_exp_close_exp_wrt_exp in H.
       fsetdec. auto.
       autorewrite with lngen.
       fsetdec.
    ++ destruct (x == y). subst.
       (* y is the binder *)
       admit.
       (* neither are binders *)
       rewrite <- IHn; auto.
       rewrite subst_exp_close_exp_wrt_exp; auto.
       autorewrite with lngen in H.
       fsetdec.
  + rewrite IHn1; auto; try fsetdec.
    rewrite IHn2; auto; try fsetdec.
Admitted.

Lemma aeq_nom_to_exp : forall n1 n2, aeq n1 n2 -> nom_to_exp n1 = nom_to_exp n2.
Proof.
  induction 1; simpl; eauto.
  - rewrite IHaeq; auto.
  - rewrite IHaeq.
    f_equal.
    rewrite <- support_fv_exp_eq in H0.
    eapply open_exp_wrt_exp_inj with (x1 := x);
    try (autorewrite with lngen; fsetdec).
    rewrite open_exp_wrt_exp_close_exp_wrt_exp.
    rewrite <- subst_exp_spec.
    rewrite swap_spec; auto.
  - rewrite IHaeq1. rewrite IHaeq2. auto.
Qed.

Lemma nom_to_exp_eq_aeq : forall n1 n2, nom_to_exp n1 = nom_to_exp n2 -> aeq n1 n2.
Proof.
  induction n1; intro n2; destruct n2; intro H; inversion H; eauto.
  - destruct (x == x0).
    subst. apply close_exp_wrt_exp_inj in H1. eauto.
    assert (FX : x `notin` fv_exp (nom_to_exp n2)).
    { intro IN.
      assert (x `in` fv_exp (nom_to_exp (n_abs x0 n2))).
      { simpl. autorewrite with lngen. fsetdec. }
      rewrite <- H in H0.
      simpl in H0. autorewrite with lngen in H0.
      fsetdec. }
    eapply aeq_abs_diff; auto.
    + rewrite <- support_fv_exp_eq. auto.
    + eapply IHn1.
      rewrite <- swap_spec; eauto.
      rewrite subst_exp_spec.
      rewrite <- H1.
      autorewrite with lngen.
      auto.
Qed.


(*
Lemma close_swap : forall x x0 n0,
  x <> x0 ->
  x0 `notin` fv_exp (close_exp_wrt_exp x (nom_to_exp n0)) ->
  close_exp_wrt_exp x (nom_to_exp n0) =
  close_exp_wrt_exp x0 (nom_to_exp (swap x x0 n0)).
Proof.
  induction n0; intros; simpl in *.
  unfold swap_var.
  destruct (x1 == x). subst.
  simpl.
*)
Lemma subst_swap : forall x0 x (h : heap) e n0,
    x <> x0 ->
    x0 `notin` fv_exp (nom_to_exp n0) ->
(*    fv_exp (close_exp_wrt_exp x (nom_to_exp n0)) [<=] dom h ->
    fv_exp e [<=] dom h -> *)
    [x ~> e] nom_to_exp n0 = [x0 ~> e] nom_to_exp (swap x x0 n0).
Proof.
  induction n0; intros; simpl in *.
  - destruct (x1 == x). subst.
    unfold swap_var.
    destruct (x == x); try contradiction.
    destruct (x0 == x0); try contradiction.
    auto.
    unfold swap_var.
    destruct (x1 == x); try contradiction.
    destruct (x1 == x0); try contradiction.
    destruct (x == x0); try contradiction.
    subst. fsetdec.
    destruct (x1 == x0); try contradiction.
    auto.
  - f_equal.
    unfold swap_var.
    destruct (x1 == x); try contradiction.
    subst.
    rewrite subst_exp_fresh_eq.
    rewrite subst_exp_fresh_eq.

    rewrite subst_exp_spec.

    rewrite subst_exp_close_exp_wrt_exp with (x1 := x0).

    destruct (x1 == x0); try contradiction.


Definition swap_atoms x y S :=
  if AtomSetImpl.mem x S then
    if AtomSetImpl.mem y S then S
    else (add y (AtomSetImpl.remove x S))
  else
    if AtomSetImpl.mem y S then
      (add x (AtomSetImpl.remove y S))
    else
      S.

Lemma commute_remove : forall x y S, remove x (remove y S) [=] remove y (remove x S).
intros. fsetdec.
Qed.


Lemma fv_swap_fresh : forall x0 x (h : heap) n0
 (Fr1 : x0 `notin` dom h)
 (SE : remove x (fv_exp (nom_to_exp n0)) [<=] dom h),
  fv_exp (nom_to_exp (swap x x0 n0)) [<=] add x0 (dom h).
Proof.
  induction n0; intros; simpl in *.
  + unfold swap_var.
    destruct (x1== x). subst. fsetdec.
    destruct (x1 == x0). subst. fsetdec.
    fsetdec.
  + rewrite fv_exp_close_exp_wrt_exp in *.
    unfold swap_var.
    destruct (x1 == x). subst.
    rewrite IHn0; auto. fsetdec. fsetdec.
    destruct (x1 == x0). subst.
    rewrite IHn0; auto. fsetdec.
    rewrite commute_remove in SE.
    admit.
    rewrite IHn0; auto. fsetdec.
    admit.
Abort.

Lemma fv_swap_var : forall x y z,
    singleton (swap_var x y z) [=] swap_atoms x y (singleton z).
Proof.
  intros x y z.
  unfold swap_var, swap_atoms.
  destruct (z == x).
  subst.
Admitted.

Lemma fv_swap : forall x y e,
    fv_exp (nom_to_exp (swap x y e)) [<=] {{x}} \u {{y}} \u fv_exp (nom_to_exp e).
Proof.
  induction e.
  - simpl.
    unfold swap_var.
    destruct (x0 == x). subst. fsetdec.
    destruct (x0 == y). subst. fsetdec.
    fsetdec.
  - simpl.
    rewrite fv_exp_close_exp_wrt_exp.
    rewrite IHe.
    rewrite fv_exp_close_exp_wrt_exp.
    unfold swap_var.
    destruct (x0 == x). subst.
    admit.
    destruct (x0 == y). subst.
    admit.
    fsetdec.
  - simpl.
    rewrite IHe1.
    rewrite IHe2.
    fsetdec.
Admitted.

(* ------------------------------------------ *)

(* Since the heap is just an iterated substitution,
   it inherits properties from subst. *)

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
    lc_exp e0 ->
    apply_heap h (open e e0)  = open (apply_heap h e) (apply_heap h e0).
Proof.
  induction h; intros; simpl; eauto.
  destruct a; eauto.
  rewrite subst_exp_open_exp_wrt_exp; eauto with lngen.
Qed.


(* ------------------------------------------ *)


Lemma push :
  forall s e e',
    apply_stack s (app e e') =
    apply_stack (app2 e' :: s) e.
simpl. auto.
Qed.

Lemma combine : forall h x e e',
  apply_heap h ([x ~> nom_to_exp e] e') = (apply_heap ((x,e)::h) e').
Proof.
  simpl. auto.
Qed.

(* ------------------------------------------ *)


Fixpoint fv_stack s :=
  match s with
    nil => {}
  | n_app2 e :: s => fv_exp (nom_to_exp e) \u fv_stack s
  end.

Inductive scoped_heap : heap -> Prop :=
  | scoped_nil  : scoped_heap nil
  | scoped_cons : forall x e h,
      x `notin` dom h ->
      fv_exp (nom_to_exp e) [<=] dom h ->
      scoped_heap h ->
      scoped_heap ((x,e)::h).


Fixpoint fv_heap  (h : heap) :=
  match h with
  | nil => {}
  | (x,e) :: h => fv_exp (nom_to_exp e) \u fv_heap h
  end.

Lemma scoped_heap_fv_heap_dom : forall h,
    scoped_heap h ->
    fv_heap h [<=] dom h.
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


Lemma scoped_get : forall h x e,
  scoped_heap h ->
  get x h = Some e ->
  fv_exp (nom_to_exp e) [<=] dom h.
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
    scoped_heap h  /\ fv_exp (nom_to_exp e)  [<=] dom h  /\ fv_stack s [<=] dom h ->
    scoped_heap h' /\ fv_exp (nom_to_exp e') [<=] dom h' /\ fv_stack s' [<=] dom h'.
Proof.
  intros.
  simpl in H.
  destruct H0 as [SH [SE SS]].
  destruct (isVal e) eqn:?.
  destruct s eqn:?.
  - inversion H.
  - destruct f eqn:?.
     + destruct e eqn:?; try solve [inversion H].
(*     destruct n eqn:?.
       ++ inversion H; subst; clear H; split; auto.
          simpl in *.
          rewrite fv_exp_close_exp_wrt_exp in SE.
          split.
          admit.
          fsetdec.
       ++ *)
          destruct (atom_fresh (dom h)).
          inversion H; subst; clear H.
          simpl in *.
          split.
            econstructor; eauto. fsetdec.
          split.
            rewrite fv_exp_close_exp_wrt_exp in *.
            admit.
          fsetdec.
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
    split; try fsetdec.
    simpl. fsetdec.
Admitted.

(* --------------------------------------------------------------- *)

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



Fixpoint apply_heap_stack h s :=
  match s with
  | nil => nil
  | app2 a::s' => app2 (apply_heap h a) :: apply_heap_stack h s'
  end.

Lemma apply_heap_apply_stack : forall h s e,
      apply_heap h (apply_stack s e) =
      apply_stack (apply_heap_stack h s) (apply_heap h e).
Proof.
  induction s; intros; try destruct a; simpl in *; eauto.
  rewrite IHs. rewrite apply_heap_app. auto.
Qed.

Lemma apply_heap_stack_fresh_eq : forall s x e1 h ,
    scoped_heap h ->
    x `notin` dom h ->
    fv_stack s [<=] dom h ->
    apply_heap_stack ((x, e1) :: h) (decode_stack s) = apply_heap_stack h (decode_stack s).
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
    (apply_heap ((x, e1) :: h) (var_f x)) = apply_heap h (nom_to_exp e1).
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
    apply_heap h (var_f x) = apply_heap h (nom_to_exp e).
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


(* Could be zero steps! *)
Lemma simulate_step : forall h e s h' e' s' e0 e0',
    machine_step (h,e,s) = TakeStep _ (h',e',s') ->
    scoped_heap h ->
    fv_exp (nom_to_exp e) [<=] dom h ->
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
  - destruct f eqn:?.
     + destruct e eqn:?; try solve [inversion H].
(*       destruct (isTrivial e1).
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
       ++ *)
       subst. destruct (atom_fresh).
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

          simpl.

          assert (open (apply_heap h (close_exp_wrt_exp x (nom_to_exp n0)))
                        (apply_heap h (nom_to_exp n)) =
                  (apply_heap h ([x0 ~> nom_to_exp n]
                                   nom_to_exp (swap x x0 n0)))).
          {
            rewrite <- apply_heap_open.
            f_equal.
            rewrite <- subst_exp_spec.
          }
          admit.
          rewrite <- H.
          eapply step_beta; eauto with lngen.
          rewrite <- apply_heap_abs.
          apply apply_heap_lc.
          econstructor; eauto with lngen.
(*          rewrite apply_heap_open.
          rewrite apply_heap_var; eauto.

          rewrite apply_heap_fresh_eq.

          econstructor; eauto.
          admit. (* LC *)
          admit. (* LC *)
          auto.
          auto.
          apply scoped_heap_fv_heap_dom in H0.
          fsetdec. *)
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
    fv_exp (nom_to_exp e) [<=] dom h ->
    fv_stack s [<=] dom h ->
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