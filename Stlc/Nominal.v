Require Import Metalib.Metatheory.
Require Import Metalib.LibLNgen.

(* Some of our proofs are by induction on the *size* of
   terms. We use the Omega tactic to easily dispatch reasoning
   about natural numbers. *)
Require Export Omega.


(*************************************************************)
(*   A nominal representation of terms                       *)
(*************************************************************)

(* A named representation of STLC terms.

   Binders include the names of free variables. *)

Inductive n_exp : Set :=
 | n_var (x:var)
 | n_abs (x:var) (t:n_exp)
 | n_app (t1:n_exp) (t2:n_exp).

(* We can swap variables: this operation is
   symmetric: x becomes y and y becomes x. *)
Notation swap_var := (fun (x:var) (y:var) (z:var) =>
  if (z == x) then y else if (z == y) then x else z).

(* The main insight of nominal representations:

   We can rename variables, without capture, using a simple
   structural induction. Note how the [n_abs} case
   we swap all variables, both bound and free.

   For example:

      (swap x y) (\z. (x y)) = \x. (y x))

      (swap x y) (\x. x) = \y.y

      (swap x y) (\y. x) = \x.y

*)
Fixpoint swap (x:var) (y:var) (t:n_exp) : n_exp :=
  match t with
  | n_var z     => n_var (swap_var x y z)
  | n_abs z t1  => n_abs (swap_var x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  end.

(* The free variable function needs to remove the
   bound variable in the [n_abs] case. *)
Fixpoint fv_nom (n : n_exp) : atoms :=
  match n with
  | n_var x => {{x}}
  | n_abs x n => AtomSetImpl.remove x (fv_nom n)
  | n_app n1 n2 => fv_nom n1 `union` fv_nom n2
  end.

(* We can also define the "alpha-equivalence" relation
   that declares when two nominal terms are equivalent
   (up to swapping).

   Note the two different rules for [n_abs]: either the
   binders are the same and we can directly compare the
   bodies, or the binders differ, but we can swap one
   side to make it look like the other.

 *)
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

(* -------------------------------------------------------- *)

(* Properties about nominal terms. *)

(* Some are straightforward to prove *)

Lemma swap_id : forall n x,
    swap x x n = n.
Proof.
  induction n; default_simp.
Qed.

Lemma swap_symmetric : forall n x y,
    swap x y n = swap y x n.
Proof.
  induction n; default_simp.
Qed.

Lemma swap_involutive : forall n x y,
    swap x y (swap x y n) = n.
Proof.
  induction n; default_simp.
Qed.

(* We will need these later! *)

Lemma fv_nom_swap : forall z y n,
  z `notin` fv_nom n ->
  y `notin` fv_nom (swap y z n).
Proof.
  induction n; default_simp.
Qed.

Lemma shuffle_swap : forall w y n z,
    w <> z -> y <> z ->
    (swap w y (swap y z n)) = (swap w z (swap w y n)).
Proof.
  induction n; default_simp.
Qed.

(* Other proofs about nominal terms involve swapping to make sure that
   variable names are "fresh enough". In this case, we need to strengthen our
   induction hypothesis.
 *)

Fixpoint size (n : n_exp) : nat :=
  match n with
  | n_var x => 1
  | n_abs x e => 1 + size e
  | n_app e1 e2 => 1 + size e1 + size e2
  end.

Lemma swap_size_constant : forall x y n,
    size (swap x y n) = size n.
Proof.
  induction n; simpl; auto.
Qed.

Hint Rewrite swap_size_constant.


Local Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let D := gather_atoms_with (fun x : n_exp => fv_nom x) in
  constr:(A `union` B `union` D).

Lemma nominal_induction_size L :
     forall n, forall t, size t <= n ->
     forall P : n_exp -> Prop,
    (forall x, P (n_var x)) ->
    (forall x t, (forall y, y `notin` L -> P (swap x y t)) -> P (n_abs x t)) ->
    (forall t1 t2, P t1 -> P t2 -> P (n_app t1 t2)) ->
    P t.
Proof.
  induction n.
  intros t SZ; destruct t; simpl in *; inversion SZ.
  intros t SZ P VAR ABS APP; destruct t; simpl in *.
  - auto.
  - apply ABS.
    intros y Fr.
    apply IHn; eauto; rewrite swap_size_constant; try omega.
  - apply APP.
    apply IHn; eauto; omega.
    apply IHn; eauto; omega.
Qed.

Definition nominal_induction
  : forall (L : atoms) (P : n_exp -> Prop),
    (forall x : atom, P (n_var x)) ->
    (forall (x : atom) (t : n_exp),
        (forall y : atom, y `notin` L -> P (swap x y t)) -> P (n_abs x t)) ->
    (forall t1 t2 : n_exp, P t1 -> P t2 -> P (n_app t1 t2)) ->
    forall t : n_exp, P t :=
  fun L P VAR APP ABS t =>
  nominal_induction_size L (size t) t ltac:(auto) P VAR APP ABS.

(* -------------------------------------------------------- *)
(* An abstract machine for cbn evaluation of named terms    *)

Fixpoint get {A :Type} (x:atom) (l : list (atom * A)) : option A :=
  match l with
  | nil => None
  | (y,a)::tl => if (x == y) then Some a else get x tl
  end.


(* The advantage of named terms is an efficient operational semantics! We
   don't need to recurse terms, opening and closing each binder. Instead, as
   long as the binder is "sufficiently fresh" we can use the name as is, and
   only rename (via swapping) when absolutely necessary. *)

(* We also don't even need to use substitution for our semantics.  Our
   abstract maching will work with configurations (see below) which consist of
   a head (i.e. delayed substitution) a term, and a stack. *)

Definition heap := list (atom * n_exp).

Inductive frame : Set := | n_app2 : n_exp -> frame.
Notation  stack := (list frame).

Definition conf := (heap * n_exp * stack)%type.


(* The (small-step) semantics is a function from configurations to
   configurations, until completion or error. *)

Inductive Step a := Error   : Step a
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


(*

Example: evaluation of  "(\y. (\x. x) y) 0"

     machine                                       corresponding term

      {}, (\y. (\x. x) y) 0 , nil                  (\y. (\x. x) y) 0
  ==> {}, (\y. (\x. x) y), n_app2 0 :: nil         (\y. (\x. x) y) 0
  ==> {y -> 0}, (\x.x) y, nil                      (\x. x) 0
  ==> {y -> 0}, (\x.x), n_app2 y :: nil            (\x. x) 0
  ==> {y -> 0}, y , nil                            0
  ==> {y -> 0}, 0 , nil                            0
  ==> Done

(Note that the machine takes extra steps compared to the
substitution semantics.)

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