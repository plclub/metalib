
(*************************************************************************)
(** * The simply-typed lambda calculus in Coq. *)
(*************************************************************************)


(** First, we import a number of definitions from the Metatheory library (see
    Metatheory.v).  The following command makes those definitions available in
    the rest of this file.

    This command will only succeed if you have already run "make" in the
    toplevel directory to compile the Metatheory library and the tutorial
    files.

*)
Require Import Metalib.Metatheory.

(** Next, we import the definitions of the simply-typed lambda calculus.
    If you haven't skimmed this file yet, you should do so now. You don't
    need to understand everything in the file at first, but you will need to
    refer back to it in the material below. *)
Require Import Stlc.Definitions.

(** And some notations (defined in `Stlc.Definitions`), but not automatically
    brought into scope. *)
Import StlcNotations.

(** For the examples below, we introduce some sample variable names to
    play with. *)
Parameter X : var.
Parameter Y : var.
Parameter Z : var.
Parameter FrXY : X <> Y.
Parameter FrXZ : X <> Z.
Parameter FrYZ : Y <> Z.

(*************************************************************************)
(** * Encoding terms in STLC *)
(*************************************************************************)

(* FULL *)
(** We start with examples of encodings in STLC.

    For example, we can encode the expression (\x. Y x) as below.  Because "Y"
  is free variable in this term, we need to assume an atom for this name.  *)
Definition demo_rep1 := abs (app (var_f Y) (var_b 0)).

(**  Here is another example: the encoding of (\x. \y. (y x)).
*)

Definition demo_rep2 := abs (abs (app (var_b 0) (var_b 1))).
(* /FULL *)

(** Exercise: Define the following lambda calculus terms using the locally
	 nameless representation.

       "two" : \s. \z. s (s z)

       "COMB_K" : \x. \y. x

       "COMB_S" : \x. \y. \z. x z (y z)

*)

(* SOLUTION *)
Definition two
  := abs (abs (app (var_b 1) (app (var_b 1) (var_b 0)))).

Definition COMB_K :=
	abs (abs (var_b 1)).

Definition COMB_S :=
   abs (abs (abs
        (app (app (var_b 2) (var_b 0)) (app (var_b 1) (var_b 0))))).

(* /SOLUTION *)

(* FULL *)
(** There are two important advantages of the locally nameless
    representation:
     - Alpha-equivalent terms have a unique representation.
       We're always working up to alpha-equivalence.
     - Operations such as free variable substitution and free
       variable calculation have simple recursive definitions
       (and therefore are simple to reason about).

    Weighed against these advantages are two drawbacks:
     - The [exp] datatype admits terms, such as [abs 3], where
       indices are unbound.
       A term is called "locally closed" when it contains
       no unbound indices.
     - We must define *both* bound variable & free variable
       substitution and reason about how these operations
       interact with each other.
*)
(* /FULL *)

(*************************************************************************)
(** * Substitution *)
(*************************************************************************)

(* FULL *)
(** The substitution function replaces a free variable with a term.  For
    simplicity, we define a notation for free variable substitution that
    mimics standard mathematical notation.  *)

Check [Y ~> var_f Z](abs (app (var_b 0)(var_f Y))).

(** To demonstrate how free variable substitution works, we need to
    reason about var equality.
*)
Check (Y == Z).

(** The decidable var equality function returns a sum. If the two
    vars are equal, the left branch of the sum is returned, carrying
    a proof of the proposition that the vars are equal.  If they are
    not equal, the right branch includes a proof of the disequality.

    The demo below uses three new tactics:
    - The tactic [simpl] reduces a Coq expression to its normal
      form.
    - The tactic [destruct (Y==Y)] considers the two possible
      results of the equality test.
    - The tactic [Case] marks cases in the proof script.
      It takes any string as its argument, and puts that string in
      the hypothesis list until the case is finished.
*)
(* /FULL *)

Lemma demo_subst1:
  [Y ~> var_f Z] (abs (app (var_b 0) (var_f Y))) = (abs (app (var_b 0) (var_f Z))).
Proof.
(* WORKINCLASS *)
  simpl.
  destruct (Y==Y).
  - Case "left".
    auto.
  - Case "right".
    destruct n. auto.
Qed. (* /WORKINCLASS *)


(** Exercise [subst_eq_var]

    We can use almost the same proof script as
    above to show how substitution works in the variable case. Try it
    on your own.  *)

Lemma subst_eq_var: forall (x : var) u,
  [x ~> u](var_f x) = u.
Proof.
  (* ADMITTED *)
  intros x u.
  simpl.
  destruct (x == x).
  - Case "left".
    auto.
  - Case "right".
    destruct n. auto.
Qed. (* /ADMITTED *)

(** Exercise [subst_neq_var] *)

Lemma subst_neq_var : forall (x y : var) u,
  y <> x -> [x ~> u](var_f y) = var_f y.
Proof.
  (* ADMITTED *)
  intros x y u.
  simpl.
  intro Neq.
  destruct (y == x).
  - Case "left".
    destruct Neq. auto.
  - Case "right".
    auto.
Qed. (* /ADMITTED *)

(** Exercise [subst_same] *)

Lemma subst_same : forall y e, [y ~> var_f y] e = e.
Proof.
  (* ADMITTED *)
  induction e; simpl; intros; eauto.
  destruct (x == y); subst; eauto.
  rewrite IHe. auto.
  rewrite IHe1. rewrite IHe2. auto.
Qed. (* /ADMITTED *)


(*************************************************************************)
(** * Free variables and variable sets *)
(*************************************************************************)

(** The function [fv] calculates the set of free variables in an expression.
    This function returns a value of type `atoms` --- a finite set of
    variable names.
 *)

(** Demo [fsetdec]

   The tactic [fsetdec] solves a certain class of propositions
   involving finite sets. See the documentation in [FSetWeakDecide]
   for a full specification.
*)

Lemma fsetdec_demo : forall (x : atom) (S : atoms),
  x `in` (singleton x `union` S).
Proof.
  fsetdec.
Qed.

(** Exercise [subst_exp_fresh_eq]

    To show the ease of reasoning with these definitions, we will prove a
    standard result from lambda calculus: if a variable does not appear free
    in a term, then substituting for it has no effect.

    HINTS: Prove this lemma by induction on [e].

    - You will need to use [simpl] in many cases.  You can [simpl] everything
      everywhere (including hypotheses) with the pattern [simpl in *].

    - Part of this proof includes a false assumption about free variables.
      Destructing this hypothesis produces a goal about finite set membership
      that is solvable by [fsetdec].

    - The [f_equal] tactic converts a goal of the form [f e1 = f e1'] in to
      one of the form [e1 = e1'], and similarly for [f e1 e2 = f e1' e2'],
      etc.  *)

Lemma subst_exp_fresh_eq : forall (x : var) e u,
  x `notin` fv_exp e -> [x ~> u] e = e.
Proof.
  (* ADMITTED *)
  intros x e u H.
  induction e.
  - Case "var_b".
    auto.
  - Case "var_f".
    simpl.
    destruct (x0 == x).
    + SCase "x0=x".
      subst. simpl fv_exp in H. fsetdec.
    + SCase "x0<>x".
      auto.
  - Case "abs".
    simpl.
    f_equal.
    auto.
  - Case "app".
    simpl in *.
    f_equal.
    auto.
    auto.
Qed. (* /ADMITTED *)

(*************************************************************************)
(** More Exercises                                                        *)
(*************************************************************************)

(**
   Step through the proof that free variables are not introduced by substitution.

   This proof actually is very automatable ([simpl in *; auto.] takes care of
   all but the var_f case), but the explicit proof below demonstrates two
   parts of the finite set library. These two parts are the tactic
   [destruct_notin] and the lemma [notin_union], both defined in the module
   [FSetWeakNotin].

   Before stepping through this proof, you should go to that module to read
   about those definitions and see what other finite set reasoning is
   available.

  *)
Lemma fv_exp_subst_exp_notin : forall x y u e,
   x `notin` fv_exp e ->
   x `notin` fv_exp u ->
   x `notin` fv_exp ([y ~> u]e).
Proof.
  intros x y u e Fr1 Fr2.
  induction e; simpl in *.
  - Case "var_b".
    assumption.
  - Case "var_f".
    destruct (x0 == y).
      assumption.
      simpl. assumption.
  - Case "abs".
    apply IHe. assumption.
  - Case "app".
    destruct_notin.
    apply notin_union.
    apply IHe1.
    assumption.
    apply IHe2.
    assumption.
Qed.

(** Now prove the following properties of substitution and fv *)

(** Exercise [subst_exp_fresh_same] *)

Lemma subst_exp_fresh_same :
forall u e x,
  x `notin` fv_exp e ->
  x `notin` fv_exp ([x ~> u] e).
Proof.
 (* ADMITTED *)
  intros.
  induction e; simpl in *; auto.
  - destruct (x0 == x).
    ++ subst. fsetdec.
    ++ simpl. auto.
Qed. (* /ADMITTED *)

(** Exercise [fv_exp_subst_exp_fresh] *)

Lemma fv_exp_subst_exp_fresh :
forall e u x,
  x `notin` fv_exp e ->
  fv_exp ([x ~> u] e) [=] fv_exp e.
Proof.
  (* ADMITTED *)
  intros.
  induction e; simpl in *; auto.
  - fsetdec.
  - destruct (x0 == x).
    ++ subst. fsetdec.
    ++ simpl. fsetdec.
  - rewrite IHe1.
    rewrite IHe2.
    fsetdec.
    fsetdec.
    fsetdec.
Qed. (* /ADMITTED *)

(** Exercise [fv_exp_subst_exp_upper] *)

Lemma fv_exp_subst_exp_upper :
forall e1 e2 x1,
  fv_exp (subst_exp e2 x1 e1) [<=] fv_exp e2 `union` remove x1 (fv_exp e1).
Proof.
  (* ADMITTED *)
  intros. induction e1; simpl in *.
  - fsetdec.
  - destruct (x == x1); simpl; fsetdec.
  - rewrite IHe1. fsetdec.
  - rewrite IHe1_1. rewrite IHe1_2.
    fsetdec.
Qed. (* /ADMITTED *)

(*************************************************************************)
(*************************************************************************)
(*************************************************************************)
(*************************************************************************)



(*************************************************************************)
(** * Opening *)
(*************************************************************************)

(** Opening replaces an index with a term, and is defined in the Definitions
    module.  (Also don't miss the notations at the end of the file.)
*)


(** This next demo shows the operation of [open].  For example, the
    locally nameless representation of the term (\y. (\x. (y x)) y) is
    [abs (app (abs (app 1 0)) 0)].  To look at the body without the
    outer abstraction, we need to replace the indices that refer to
    that abstraction with a name.  Therefore, we show that we can open
    the body of the abs above with Y to produce [app (abs (app Y 0))
    Y)].
*)

Lemma demo_open :
  (app (abs (app (var_b 1) (var_b 0))) (var_b 0)) ^ Y =
  (app (abs (app (var_f Y) (var_b 0))) (var_f Y)).
Proof.
  unfold open_exp_wrt_exp.
  unfold open_exp_wrt_exp_rec.
  simpl.
  auto.
Qed.

(* HINT for demo: To show the equality of the two sides below, use the
   tactics [unfold], which replaces a definition with its RHS and
   reduces it to head form, and [simpl], which reduces the term the
   rest of the way.  Then finish up with [auto].  *)

(* Now use this tactic to simplify the proof above. *)
Ltac simpl_open :=
  unfold open_exp_wrt_exp; unfold open_exp_wrt_exp_rec; simpl;
  fold open_exp_wrt_exp_rec; fold open_exp_wrt_exp.

Lemma demo_open_revised :
  (app (abs (app (var_b 1) (var_b 0))) (var_b 0)) ^ Y =
  (app (abs (app (var_f Y) (var_b 0))) (var_f Y)).
Proof.
  (* ADMITTED *)
  simpl_open.
  reflexivity.
Qed. (* /ADMITTED *)


(*************************************************************************)
(** * Local closure *)
(*************************************************************************)

(** The local closure judgement classifies terms that have *no* dangling
   indices.

   Step through this derivation to see why the term is locally closed.
*)

Lemma demo_lc :
  lc_exp (app (abs (app (var_f Y) (var_b 0))) (var_f Y)).
Proof.
  eapply lc_app.
    eapply lc_abs.
     intro x. simpl_open.
     auto.
    auto.
Qed.

(*************************************************************************)
(** More Properties about basic operations *)
(*************************************************************************)

(** The most important properties about open and lc_exp concern their relationship
    with the free variable and subst functions.

    For example, one important property is shown below: that we can
    commute free and bound variable substitution.

    We won't prove this lemma as part of the tutorial (it is proved
    in Lemmas.v), but it is an important building block for reasoning
    about LN terms.

 *)

Lemma subst_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  [x1 ~> e1] (open e3 e2) = open ([x1 ~> e1] e3) ([x1 ~> e1] e2).
Proof.
Admitted.

(** *** Exercise [subst_var] *)

(** The lemma above is most often used with [e2] as some fresh
    variable. Therefore, it simplifies matters to define the following useful
    corollary.

    HINT: Do not use induction.  Rewrite with [subst_exp_open_exp_wrt_exp] and
    [subst_neq_var].

*)

Lemma subst_var : forall (x y : var) u e,
  y <> x ->
  lc_exp u ->
  ([x ~> u] e) ^ y = [x ~> u] (e ^ y).
Proof.
  (* ADMITTED *)
  intros x y u e Neq H.
  rewrite subst_exp_open_exp_wrt_exp with (e2 := var_f y); auto.
  rewrite subst_neq_var; auto.
Qed.   (* /ADMITTED *)

(** *** Take-home Exercise [subst_exp_intro] *)

(** This next lemma states that opening can be replaced with variable
    opening and substitution.

    HINT: Prove by induction on [e], first generalizing the
    argument to [open] by using the [generalize] tactic, e.g.,
    [generalize 0].

*)

Lemma subst_exp_intro : forall (x : var) u e,
  x `notin` (fv_exp e) ->
  open e u = [x ~> u](e ^ x).
Proof.
  (* ADMITTED *)
  intros x u e FV_EXP.
  unfold open.
  unfold open_exp_wrt_exp.
  generalize 0.
  induction e; intro n0; simpl.
  - Case "var_b".
    destruct (lt_eq_lt_dec n n0).
    destruct s. simpl. auto.
    rewrite subst_eq_var. auto.
    simpl. auto.
  - Case "var_f".
    destruct (x0 == x). subst. simpl in FV_EXP. fsetdec. auto.
  - Case "abs".
    f_equal. simpl in FV_EXP. apply IHe. auto.
  - Case "app".
    simpl in FV_EXP.
    f_equal.
    apply IHe1. auto.
    apply IHe2. auto.
Qed. (* /ADMITTED *)


(*************************************************************************)
(** Forall quantification in [lc_exp].                                   *)
(*************************************************************************)

(** Let's look more closely at lc_abs and lc_exp_ind. *)

Check lc_exp_ind.

(** The induction principle for the lc_exp relation is particularly strong
   in the abs case.

<<
 forall P : exp -> Prop,
       ...
       (forall e : exp,
        (forall x : atom, lc_exp (e ^ x)) ->
        (forall x : atom, P (e ^ x)) -> P (abs e)) ->
       ...
       forall e : exp, lc_exp e -> P e
>>

  This principle says that to prove that a property holds for an abstraction,
  we can assume that the property holds for the body of the abstraction,
  opened with *any* variable that we like.

*)


Check lc_abs.

(** However, on the other hand, when we show that an abstraction is locally
   closed, we need to show that its body is locally closed, when
   opened by any variable.

   That can sometimes be a problem. *)

Lemma subst_lc0 : forall (x : var) u e,
  lc_exp e ->
  lc_exp u ->
  lc_exp ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  - Case "lc_var_f".
    simpl.
    destruct (x0 == x).
      auto.
      auto.
  - Case "lc_abs".
    simpl.
    eapply lc_abs.
    intros x0.
    rewrite subst_var.
    apply H0.
Admitted.

(** Here we are stuck. We don't know that [x0] is not equal to [x],
    which is a preconduction for [subst_var].

    The solution is to prove an alternative introduction rule for
    local closure for abstractions.  In the current rule, we need
    to show that the body of the abstraction is locally closed,
    no matter what variable we choose for the binder.


<<
  | lc_abs : forall e,
      (forall x:var, lc_exp (open e x)) ->
      lc_exp (abs e)
>>

    An easier to use lemma requires us to only show that the body
    of the abstraction is locally closed for a *single* variable.

    As before, we won't prove this lemma as part of the tutorial,
    (it too is proved in Lemmas.v) but we will use it as part of
    our reasoning.
*)
Lemma lc_abs_exists : forall (x : var) e,
      lc_exp (e ^ x) ->
      lc_exp (abs e).
Admitted.

(** For example, with this addition, we can complete the proof above. *)

Lemma subst_exp_lc_exp : forall (x : var) u e,
  lc_exp e ->
  lc_exp u ->
  lc_exp ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  - Case "lc_var_f".
    simpl.
    destruct (x0 == x); auto.
  - Case "lc_abs".
    simpl.
    pick fresh x0 for {{x}}.  (* make sure that x0 <> x *)
    apply (lc_abs_exists x0).
    rewrite subst_var; auto.
  - Case "lc_app".
    simpl. eauto.
Qed.
