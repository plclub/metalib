(** A nominal representation of STLC terms.

    This version looks a lot like we expect a representation of
    the lambda calculus to look like. Unlike the LN version,
    the syntax does not distinguish between bound and free
    variables and abstractions include the name of binding
    variables.  *)

(*************************************************************)
(** * Imports                                                *)
(*************************************************************)

(** We will use the [atom] type from the metatheory library to
    represent variable names. *)
Require Export Metalib.Metatheory.

(** Although we are not using LNgen, some of the tactics from
    its library are useful for automating reasoning about
    names.  *)
Require Export Metalib.LibLNgen.

(** Some of our proofs are by induction on the *size* of
    terms. We'll use Coq's [omega] tactic to easily dispatch
    reasoning about natural numbers. *)
Require Export Omega.

(*************************************************************)
(** * A nominal representation of terms                      *)
(*************************************************************)

Inductive n_exp : Set :=
 | n_var (x:atom)
 | n_abs (x:atom) (t:n_exp)
 | n_app (t1:n_exp) (t2:n_exp).

(** What makes this a *nominal* representation is that our
    operations are based on the following swapping function for
    names.  Note that this operation is symmetric: [x] becomes
    [y] and [y] becomes [x]. *)

Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z == x) then y else if (z == y) then x else z.

Hint Unfold swap_var : nominal.

(** The main insight of nominal representations is that we can
    rename variables, without capture, using a simple
    structural induction. Note how in the [n_abs] case we swap
    all variables, both bound and free.

    For example:

      (swap x y) (\z. (x y)) = \x. (y x))

      (swap x y) (\x. x) = \y.y

      (swap x y) (\y. x) = \x.y

*)
Fixpoint swap (x:atom) (y:atom) (t:n_exp) : n_exp :=
  match t with
  | n_var z     => n_var (swap_var x y z)
  | n_abs z t1  => n_abs (swap_var x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  end.


(** The free variable function needs to remove the
    bound variable in the [n_abs] case. *)
Fixpoint fv_nom (n : n_exp) : atoms :=
  match n with
  | n_var x => {{x}}
  | n_abs x n => AtomSetImpl.remove x (fv_nom n)
  | n_app n1 n2 => fv_nom n1 `union` fv_nom n2
  end.

(** We can also define the "alpha-equivalence" relation that
    declares when two nominal terms are equivalent (up to
    renaming of bound variables).

    Note the two different rules for [n_abs]: either the
    binders are the same and we can directly compare the
    bodies, or the binders differ, but we can swap one side to
    make it look like the other.  *)

Inductive aeq : n_exp -> n_exp -> Prop :=
 | aeq_var : forall x,
     aeq (n_var x) (n_var x)
 | aeq_abs_same : forall x n1 n2,
     aeq n1 n2 -> aeq (n_abs x n1) (n_abs x n2)
 | aeq_abs_diff : forall x y n1 n2,
     x <> y ->
     x `notin` fv_nom n2 ->
     aeq n1 (swap y x n2) ->
     aeq (n_abs x n1) (n_abs y n2)
 | aeq_app : forall n1 n2 n1' n2',
     aeq n1 n1' -> aeq n2 n2' ->
     aeq (n_app n1 n2) (n_app n1' n2').

Hint Constructors aeq.

(*************************************************************)
(** * Properties about swapping                              *)
(*************************************************************)


(** Because swapping is a simpl, structurally recursive
    function, it is highly automatable using the [default_simp]
    tactic from LNgen library.

    This tactic "simplifies" goals using a combination of
    common proof steps, including case analysis of all disjoint
    sums in the goal. Because atom equality returns a sumbool,
    this makes this tactic useful for reasoning by cases about
    atoms.

    For more information about the [default_simp] tactic, see
    [metalib/LibDefaultSimp.v]. *)

Lemma swap_id : forall n x,
    swap x x n = n.
Proof.
  induction n; simpl; unfold swap_var;  default_simp.
Qed.

(** Demo: We will need the next two properties later in the tutorial,
    so we show that even though there are many cases to consider,
    [default_simp] can find these proofs. *)

Lemma fv_nom_swap : forall z y n,
  z `notin` fv_nom n ->
  y `notin` fv_nom (swap y z n).
Proof.
  (* WORKINCLASS *)
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed. (* /WORKINCLASS *)

Lemma shuffle_swap : forall w y n z,
    w <> z -> y <> z ->
    (swap w y (swap y z n)) = (swap w z (swap w y n)).
Proof.
  (* WORKINCLASS *)
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed. (* /WORKINCLASS *)

(*************************************************************)
(** * Exercises                                              *)
(*************************************************************)


(** Exercise: swap properties

    Prove the following properties about swapping, either
    explicitly (by destructing [x == y]) or automatically
    (using [default_simp]).  *)

Lemma swap_symmetric : forall n x y,
    swap x y n = swap y x n.
Proof.
  (* ADMITTED *)
  induction n;  simpl; unfold swap_var; default_simp.
Qed.   (* /ADMITTED *)

Lemma swap_involutive : forall n x y,
    swap x y (swap x y n) = n.
Proof.
  (* ADMITTED *)
  induction n;  simpl; unfold swap_var; default_simp.
Qed.   (* /ADMITTED *)

(** Challenge exercises: equivariance

    Equivariance is the property that all functions and relations
    are preserved under swapping.

*)
Lemma swap_var_equivariance : forall n x y z w,
    swap_var x y (swap_var z w n) =
    swap_var (swap_var x y z) (swap_var x y w) (swap_var x y n).
Proof.
  (* ADMITTED *)
  unfold swap_var; default_simp.
Qed.   (* /ADMITTED *)

Lemma swap_equivariance : forall n x y z w,
    swap x y (swap z w n) = swap (swap_var x y z) (swap_var x y w) (swap x y n).
Proof.
  (* ADMITTED *)
  induction n; intros; simpl.
  - rewrite swap_var_equivariance. auto.
  - rewrite swap_var_equivariance. rewrite IHn. auto.
  - rewrite IHn1. rewrite IHn2. auto.
Qed. (* /ADMITTED *)

Lemma fv_nom_equivariance : forall x0 x y n,
  x0 `notin` fv_nom n ->
  swap_var x y x0  `notin` fv_nom (swap x y n).
Proof.
  (* ADMITTED *)
  induction n; intros; simpl in *.
  - unfold swap_var; default_simp.
  - unfold swap_var in *. default_simp.
  - destruct_notin.
    eapply IHn1 in H.
    eapply IHn2 in NotInTac.
    fsetdec.
Qed. (* /ADMITTED *)

Lemma aeq_equivariance : forall x y n1 n2,
    aeq n1 n2 ->
    aeq (swap x y n1) (swap x y n2).
Proof.
  (* ADMITTED *)
  induction 1; intros; simpl in *; auto.
  destruct (swap_var x y x0 == swap_var x y y0).
  - rewrite e. eapply aeq_abs_same.
    rewrite swap_equivariance in IHaeq.
    rewrite e in IHaeq.
    rewrite swap_id in IHaeq.
    auto.
  - rewrite swap_equivariance in IHaeq.
    eapply aeq_abs_diff; auto.
    eapply fv_nom_equivariance; auto.
Qed. (* /ADMITTED *)

(*************************************************************)
(** * An abstract machine for cbn evaluation                 *)
(*************************************************************)


Fixpoint get {A :Type} (x:atom) (l : list (atom * A)) : option A :=
  match l with
  | nil => None
  | (y,a)::tl => if (x == y) then Some a else get x tl
  end.


(** The advantage of named terms is an efficient operational
    semantics! Compared to LN or debruijn representation, we
    don't need to modify terms (such as via open or shifting)
    as we traverse binders. Instead, as long as the binder is
    "sufficiently fresh" we can use the name as is, and only
    rename (via swapping) when absolutely necessary. *)

(** Below, we define an operational semantics based on an
    abstract machine.

    Our abstract machine configurations have three components:

    - the current expression being evaluated
    - the heap (aka environment):
        a mapping between variables and expressions
    - the stack:
        the evaluation context of the current expression

    Because we have a heap, we don't need to use substitution
    to define our semantics! To implement [e/x] we place e on
    the heap and then look it up when we get to x during
    evaluation.
*)


Definition heap := list (atom * n_exp).

Inductive frame : Set := | n_app2 : n_exp -> frame.
Notation  stack := (list frame).

Definition conf := (heap * n_exp * stack)%type.

(** The (small-step) semantics is a function from configurations to
    configurations, until completion or error. *)

Inductive Step a := Error    : Step a
                  | Done     : Step a
                  | TakeStep : a -> Step a.

Definition isVal (e : n_exp) :=
  match e with
  | n_abs _ _ => true
  | _         => false
  end.

Definition machine_step (avoid : atoms) (c : conf) : Step conf :=
  match c with
    (h, e, s) =>
    if isVal e then
      match s with
      | nil => Done _
      | n_app2 a :: s' =>
        match e with
        | n_abs x e =>
          (* if the bound name [x] is not fresh, we need to rename it *)
          if AtomSetProperties.In_dec x avoid  then
            let (y,_) := atom_fresh avoid in
             TakeStep _ ((y,a)::h, swap x y e, s')
          else
            TakeStep _ ((x,a)::h, e, s')
        | _ => Error _ (* non-function applied to argument *)
        end
      end
    else match e with
         | n_var x => match get x h with
                     | Some e  => TakeStep _ (h, e, s)
                     | None    => Error _ (* Unbound variable *)
                     end
         | n_app e1 e2 => TakeStep _ (h, e1, n_app2 e2 :: s)
         | _ => Error _ (* unreachable (value in nonValueStep) *)
         end
  end.

Definition initconf (e : n_exp) : conf := (nil,e,nil).


(** Example: evaluation of  "(\y. (\x. x) y) X"

<<
     machine                                       corresponding term

      {}, (\y. (\x. x) y) X , nil                  (\y. (\x. x) y) X
  ==> {}, (\y. (\x. x) y), n_app2 X :: nil         (\y. (\x. x) y) X
  ==> {y -> X}, (\x.x) y, nil                      (\x. x) X
  ==> {y -> X}, (\x.x), n_app2 y :: nil            (\x. x) X
  ==> {y -> X}, y , nil                            X
  ==> {y -> X}, X , nil                            X
  ==> Done
>>

(Note that the machine takes extra steps compared to the
substitution semantics.)

*)


(*************************************************************)
(** * Size, Nominal induction and recursion                  *)
(*************************************************************)


(** Some properties about nominal terms require calling the
    induction hypothesis not on a direct subterm, but on one
    that has first had a swapping applied to it.

    However, swapping names does not change the size of terms,
    so that means we can prove such properties by induction on
    that size.  *)

Fixpoint size (n : n_exp) : nat :=
  match n with
  | n_var x => 1
  | n_abs x e => 1 + size e
  | n_app e1 e2 => 1 + size e1 + size e2
  end.

Lemma swap_size_eq : forall x y n,
    size (swap x y n) = size n.
Proof.
  induction n; simpl; auto.
Qed.

Hint Rewrite swap_size_eq.


Lemma nominal_induction_size L :
     forall n, forall t, size t <= n ->
     forall P : n_exp -> Type,
    (forall x, P (n_var x)) ->
    (forall x t, (forall y, y `notin` L -> P (swap x y t)) -> P (n_abs x t)) ->
    (forall t1 t2, P t1 -> P t2 -> P (n_app t1 t2)) ->
    P t.
Proof.
  induction n.
  intros t SZ; destruct t; intros; simpl in SZ; omega.
  intros t SZ P VAR ABS APP; destruct t; simpl in *.
  - auto.
  - apply ABS.
    intros y Fr.
    apply IHn; eauto; rewrite swap_size_eq; try omega.
  - apply APP.
    apply IHn; eauto; omega.
    apply IHn; eauto; omega.
Defined.

Definition nominal_induction
  : forall (L : atoms) (P : n_exp -> Type),
    (forall x : atom, P (n_var x)) ->
    (forall (x : atom) (t : n_exp),
        (forall y : atom, y `notin` L -> P (swap x y t)) -> P (n_abs x t)) ->
    (forall t1 t2 : n_exp, P t1 -> P t2 -> P (n_app t1 t2)) ->
    forall t : n_exp, P t :=
  fun L P VAR APP ABS t =>
  nominal_induction_size L (size t) t ltac:(auto) P VAR APP ABS.

(* LATER *)

Definition extract {L} (m : {x : atom | x `notin` L}) : atom :=
  match m with
  | exist _ x _ => x
  end.

Inductive subst_rel (u : n_exp) (x: atom) : n_exp -> n_exp -> Prop :=
 | subst_var_same : subst_rel u x (n_var x) u
 | subst_var_diff : forall y, x <> y -> subst_rel u x (n_var y) (n_var y)
 | subst_abs      : forall y z t0 t0',
     z = extract (atom_fresh (fv_nom u \u fv_nom (n_abs y t0))) ->
     subst_rel u x (swap y z t0) t0' ->
     subst_rel u x (n_abs y t0) (n_abs z t0')
 | subst_app      : forall t0 t0' t1 t1',
     subst_rel u x t0 t0' ->
     subst_rel u x t1 t1' ->
     subst_rel u x (n_app t0 t1) (n_app t0' t1').
Hint Constructors subst_rel.


Lemma subst_rel_exists : forall u x t, sig (subst_rel u x t).
Proof.
  intros u x t.
  apply nominal_induction with (t := t)(L := fv_nom u).
  - intros y. destruct (x == y); subst. exists u. eauto.
    exists (n_var y). auto.
  - intros y t0 IH.
    remember (atom_fresh (fv_nom u \u fv_nom (n_abs y t0))) as sg.
    destruct (IH (extract sg)) as [t0' K]. subst. simpl.
    unfold extract. destruct atom_fresh.
    fsetdec.
    exists (n_abs (extract sg) t0'). subst; eauto.
  - intros t1 t2 [t1' IH1] [t2' IH2].
    exists (n_app t1' t2'). eauto.
Defined.

Definition subst (u : n_exp) (x:atom) (t:n_exp) : n_exp :=
  match (subst_rel_exists u x t) with
  | exist _ t' _ => t'
  end.

Lemma simpl_subst_app : forall u x t1 t2,
    subst u x (n_app t1 t2) = n_app (subst u x t1) (subst u x t2).
Proof.
  intros.
  unfold subst in *.
  destruct subst_rel_exists.
  inversion s.
Admitted.


Program Fixpoint subst_rec (n:nat) (t:n_exp) (pf : size t <= n)
        (u :n_exp) (x:atom)  : n_exp :=
  match n with
  | 0 => _
  | S m => match t with
          | n_var y => if (x == y) then u else t
          | n_abs y t1 => if (x == y) then t
                        else let (z,_) := atom_fresh (fv_nom u \u fv_nom t) in
                             n_abs z (subst_rec m (swap y z t1) _ u x)
          | n_app t1 t2 => n_app (subst_rec m t1 _ u x) (subst_rec m t2 _ u x)
          end
  end.
Next Obligation.
rewrite swap_size_eq. simpl in *. omega.
Defined.
Next Obligation.
simpl in *. omega.
Defined.
Next Obligation.
simpl in *. omega.
Defined.

Lemma subst_rec_proof_irrel :
  forall n t p1 p2 u x, subst_rec n t p1 u x = subst_rec n t p2 u x.
Proof.
  induction n.
  simpl. auto.
  simpl. destruct t; auto.
  - intros; destruct (x0 == x); auto.
    destruct atom_fresh; auto.
    erewrite IHn. eauto.
  - intros.
    erewrite IHn with (t := t1).
    erewrite IHn with (t := t2).
    eauto.
Qed.

(* /LATER *)

(* HIDE *)

(*
Lemma subst_rec_size_weaken :
  forall n1 t u x (p1 : size t <= n1) (p2: size t <= size t),
    subst_rec n1 t p1 u x = subst_rec (size t) t p2 u x.
Proof.
Admitted.


Definition subst (u : n_exp) (x:atom) (t:n_exp) :=
  subst_rec (size t) t ltac:(auto) u x.

Lemma subst_var_eq : forall u x,
    subst u x (n_var x) = u.
Proof.
  intros. unfold subst. default_simp.
Qed.
Lemma subst_var_neq : forall u x y,
    x <> y ->
    subst u x (n_var y) = n_var y.
Proof.
  intros. unfold subst. default_simp.
Qed.
Lemma subst_app : forall u x t1 t2,
    subst u x (n_app t1 t2) = n_app (subst u x t1) (subst u x t2).
Proof.
  intros. unfold subst.
  erewrite subst_rec_proof_irrel with (t := t1).
  erewrite subst_rec_proof_irrel with (t := t2).
  simpl; eauto.
  remember (le_n (size (n_app t1 t2))) as Pf1.
  remember (le_n (size t1)) as Pf2.
  remember (le_n (size t2)) as Pf3.
  simpl.

  repeat f_equal. f_equal.

Definition impossible {A:Type} (t:n_exp)(pf: size t <= 0) : A.
destruct t; simpl in pf; omega.
Defined.

Fixpoint nominal_recursion_size {A : Type} L
  (n : nat) (t : n_exp) (pf : size t <= n)
          (VAR : atom -> A)
          (ABS : forall x, x `notin` L -> A -> A)
          (APP : A -> A -> A)
           : A :=
  match n with
  | 0 => impossible t _
  | S m => match t with
          | n_var x => VAR x
          | n_abs y t0 =>
            let (z,Pf) := atom_fresh L in
            let ABS'   := fun x Fr => ABS x _ in
            ABS z Pf (nominal_recursion_size
                        (add z L) m (swap z y t0) _ VAR ABS' APP)
          | n_app t0 t1 =>
            APP (nominal_recursion_size L m t0 _ VAR ABS APP)
                (nominal_recursion_size L m t1 _ VAR ABS APP)
          end
  end.
*)


(*
Inductive typ := typ_base | typ_arrow : typ -> typ -> typ.

Definition ctx := list (atom * typ).

Inductive typing : ctx -> n_exp -> typ -> Prop :=
 | typing_var : forall (G:ctx) (x:var) (T:typ),
     uniq G ->
     binds x T G  ->
     typing G (n_var x) T
 | typing_abs : forall (G:ctx) x (T1:typ) (e:n_exp) (T2:typ),
     typing ([(x, T1)] ++ G) e T2  ->
     typing G (n_abs x e) (typ_arrow T1 T2)
 | typing_app : forall (G:ctx) (e1 e2:n_exp) (T2 T1:typ),
     typing G e1 (typ_arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (n_app e1 e2) T2 .

Inductive typing_stack (G : ctx) : stack -> typ -> typ -> Prop :=
| typing_stack_nil : forall T, typing_stack G nil T T
| typing_stack_app2 : forall s e T T1 T2,
    typing G e T1 ->
    typing_stack G s T T2 ->
    typing_stack G ((n_app2 e)::s) T (typ_arrow T1 T2).

Inductive typing_heap : ctx -> heap -> Prop :=
 | typing_heap_nil : typing_heap nil nil
 | typing_heap_cons : forall G h x e T,
     typing G e T ->
     typing_heap G h ->
     typing_heap ((x, T)::G) ((x,e)::h).

Inductive typing_conf : conf -> typ -> Prop :=
 | typing_conf_witness:
     forall h e s G T1 T2,
       typing_heap G h ->
       typing_stack G s T1 T2 ->
       typing G e T1 ->
       typing_conf (h,e,s) T2.

Lemma preservation : forall T h e s conf',
    machine_step (dom h) (h,e,s) = TakeStep _ conf' ->
    typing_conf (h,e,s)  T ->
    typing_conf conf' T.
Proof.
  intros.
  destruct conf' as [[h' e'] s']. inversion H0. subst.
  simpl in *.
  destruct (isVal e) eqn:?.
  - destruct s eqn:?. inversion H.
    destruct f.
    destruct e eqn:?. inversion H.
    destruct AtomSetProperties.In_dec.
    + destruct atom_fresh.
      inversion H. subst. clear H.
      simpl in *.
      inversion H7. subst. clear H7.
      inversion H6. subst. clear H6.
      econstructor; eauto.
      instantiate (1 :=  [(x0,T3)] ++ G).
      eapply typing_heap_cons; eauto.
*)



Lemma aeq_fv_nom : forall n1 n2,
    aeq n1 n2 ->
    fv_nom n1 [=] fv_nom n2.
Proof.
  induction 1; simpl in *; try fsetdec.
  rewrite IHaeq.
  apply fv_nom_equivariance with (x:=x)(y:=y) in H0.
  unfold swap_var in H0. default_simp.
Admitted.

Lemma aeq_refl : forall n, aeq n n.
Proof.
  induction n; auto.
Qed.

Lemma aeq_sym : forall n1 n2,
    aeq n1 n2 -> aeq n2 n1.
Proof.
  induction 1; auto.
  - eapply aeq_abs_diff; auto.
    admit.
    eapply aeq_equivariance in IHaeq.
    rewrite swap_involutive in IHaeq.
    rewrite swap_symmetric.
    auto.
Admitted.

Lemma aeq_trans : forall n2 n1 n3, aeq n1 n2 -> aeq n2 n3 -> aeq n1 n3.
Proof.
  induction n2; intros; simpl in *.
  - inversion H; inversion H0. subst. auto.
  - inversion H; inversion H0; subst; auto.
    eapply aeq_abs_diff; eauto.
    rewrite <- aeq_fv_nom; eauto.
    assert (aeq (swap x x0 n2) (swap x x0 n6)).
    eapply aeq_equivariance; auto.
    admit.
Admitted.

(* /HIDE *)
