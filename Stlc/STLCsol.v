
(*************************************************************************)
(** The simply-typed lambda calculus in Coq. *)
(*************************************************************************)

(** An interactive tutorial on developing programming language metatheory.
    This file uses the simply-typed lambda calculus (STLC) to demonstrate the
    locally nameless representation of lambda terms and cofinite
    quantification in judgments.

    This tutorial concentrates on "how" to formalize STLC; for more details
    about "why" we use this style of development see the associated lecture
    slides.

    Tutorial author: Stephanie Weirich, based on prior tutorials by Brian
    Aydemir and Stephanie Weirich, with help from Aaron Bohannon, Nate Foster,
    Benjamin Pierce, Jeffrey Vaughan, Dimitrios Vytiniotis, and Steve
    Zdancewic.  Adapted from code by Arthur Chargu'eraud.

*)


(*************************************************************************)
(** * Contents

    - Syntax of STLC
    - Substitution
    - Free variables
    - Properties about basic operations

    - Open
    - Local closure
    - Cofinite quantification
    - Tactic support
    - Typing environments
    - Typing relation
    - Weakening
    - Substitution
    - Values and evaluation
    - Preservation
    - Progress
    - Additional properties
    - Renaming
    - Decidability of typechecking
    - Equivalence of exist fresh and cofinite

  Solutions to exercises are in [STLCsol.v].
*)
(*************************************************************************)


(** First, we import a number of definitions from the Metatheory library (see
    Metatheory.v).  The following command makes those definitions available in
    the rest of this file.  This command will only succeed if you have already
    run "make" in the toplevel directory to compile the Metatheory library and
    the tutorial files.
*)

Require Import Metalib.Metatheory.

(** Next, we import the definitions of the simply-typed lambda calculus. *)
Require Import Definitions.

(** And some auxiliary lemmas about these definitions. *)
Require Import Lemmas.

(*************************************************************************)
(** * Encoding terms in STLC *)
(*************************************************************************)

(*
  We start with examples of encodings in STLC.

  For example, we can encode the expression (\x:b. Y x) as below.
  Because "Y" is free variable in this term, we need to assume an
  atom for this name.
*)

Parameter Y : var.
Definition demo_rep1 := abs typ_base (app (var_f Y) (var_b 0)).

(**
    Below is another example: the encoding of (\x:b. \y:b. (y x)).
*)

Definition demo_rep2 := abs typ_base (abs typ_base (app (var_b 0) (var_b 1))).


(** Exercise: Uncomment and then complete the definitions of the following
	 lambda calculus terms using the locally nameless representation.

       "two"     :    \s:b->b. \z:b. s (s z)

       "COMB_K"  :    \x:b. \y:b. x

       "COMB_S"  :    \x:b -> b -> b.\y:b -> b.\z:b. x z (y z)

*)


Definition two :=
  (* SOLUTION *)
  abs (typ_arrow typ_base typ_base)
                      (abs typ_base (app (var_b 1) (app (var_b 1) (var_b 0)))).

Definition COMB_K :=
  (* SOLUTION *)
	abs typ_base
    (abs typ_base (var_b 1)).

Definition COMB_S :=
   (* SOLUTION *)
   abs (typ_arrow typ_base (typ_arrow typ_base typ_base))
    (abs (typ_arrow typ_base typ_base)
      (abs (typ_base)
        (app (app (var_b 2) (var_b 0)) (app (var_b 1) (var_b 0))))).

(* SCW: move to talk slides *)
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


(*************************************************************************)
(** * Substitution *)
(*************************************************************************)

(** The substitution function replaces a free variable with a term.  For
    simplicity, we define a notation for free variable substitution that
    mimics standard mathematical notation.  *)

Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 68).


(** To demonstrate how free variable substitution works, we need to
    reason about var equality.
*)

Parameter Z : var.
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

Lemma demo_subst1:
  [Y ~> var_f Z] (abs typ_base (app (var_b 0) (var_f Y))) = (abs typ_base (app (var_b 0) (var_f Z))).
Proof.
  simpl.
  destruct (Y==Y).
  - Case "left".
    auto.
  - Case "right".
    destruct n. auto.
Qed.

(** Take-home Exercise: We can use almost the same proof script as
    above to state how substitution works in the variable case. Try it
    on your own.  *)

Lemma subst_eq_var: forall (x : var) u,
  [x ~> u](var_f x) = u.
Proof.
  (* SOLUTION *)
  intros x u.
  simpl.
  destruct (x == x).
  - Case "left".
    auto.
  - Case "right".
    destruct n. auto.
Qed.

Lemma subst_neq_var : forall (x y : var) u,
  y <> x -> [x ~> u](var_f y) = var_f y.
Proof.
  (* SOLUTION *)
  intros x y u.
  simpl.
  intro Neq.
  destruct (y == x).
  - Case "left".
    destruct Neq. auto.
  - Case "right".
    auto.
Qed.

Lemma subst_same : forall y e, [y ~> var_f y] e = e.
Proof.
  (* SOLUTION *)
  induction e; simpl; intros; default_simp.
Qed.

(*************************************************************************)
(** * Free variables and variable sets *)
(*************************************************************************)

(** The function [fv] calculates the set of free variables in an expression.
    *)

(* Demo [fsetdec]

   The tactic [fsetdec] solves a certain class of propositions
   involving finite sets. See the documentation in [FSetWeakDecide]
   for a full specification.
*)

Lemma fsetdec_demo : forall (x : atom) (S : atoms),
  x `in` (singleton x `union` S).
Proof.
  fsetdec.
Qed.

(** Exercise [subst_exp_fresh_eq] To show the ease of reasoning with these
    definitions, we will prove a standard result from lambda calculus: if a
    variable does not appear free in a term, then substituting for it has no
    effect.

    HINTS: Prove this lemma by induction on [e].

    - You will need to use [simpl] in many cases.  You can [simpl] everything
      everywhere (including hypotheses) with the pattern [simpl in *].

    - Part of this proof includes a false assumption about free variables.
      Destructing this hypothesis produces a goal about finite set membership
      that is solvable by [fsetdec].

    - The [f_equal] tactic converts a goal of the form [f e1 = f e1'] in to
      one of the form [e1 = e1'], and similarly for [f e1 e2 = f e1' e2'],
      etc.
*)

Lemma subst_exp_fresh_eq : forall (x : var) e u,
  x `notin` fv_exp e -> [x ~> u] e = e.
Proof.
  (* SOLUTION *)
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
Qed.

(*************************************************************************)
(* Exercises                                                             *)
(*************************************************************************)

(*
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

(* Now prove two other properties of substitution and fv *)
Lemma subst_exp_fresh_same :
forall u e x,
  x `notin` fv_exp e ->
  x `notin` fv_exp ([x ~> u] e).
Proof.
 (* SOLUTION *)
  intros.
  induction e; simpl in *; auto.
  - destruct (x0 == x).
    ++ subst. fsetdec.
    ++ simpl. auto.
Qed.

Lemma fv_exp_subst_exp_fresh :
forall e u x,
  x `notin` fv_exp e ->
  fv_exp ([x ~> u] e) [=] fv_exp e.
Proof.
  (* SOLUTION *)
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
Qed.

(*************************************************************************)
(*                                                                       *)
(* Lecture 2                                                             *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(** * Opening *)
(*************************************************************************)


(** Opening replaces an index with a term.  It corresponds to informal
    substitution for a bound variable, such as in the rule for beta
    reduction. Note that only "dangling" indices (those that do not
    refer to any abstraction) can be opened.
*)

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [(open e x)] can be read as "substitute the variable [x]
    for index [0] in [e]" and "open [e] with the variable [x]."
    Recall that the coercions above let us write [x] in place of
    [(var_f x)].
*)


Definition open e u := open_exp_wrt_exp_rec 0 u e.


Notation "e ^ x"    := (open_exp_wrt_exp e (var_f x)).

(** This next demo shows the operation of [open].  For example, the
    locally nameless representation of the term (\y. (\x. (y x)) y) is
    [abs (app (abs (app 1 0)) 0)].  To look at the body without the
    outer abstraction, we need to replace the indices that refer to
    that abstraction with a name.  Therefore, we show that we can open
    the body of the abs above with Y to produce [app (abs (app Y 0))
    Y)].
*)

Lemma demo_open :
  (app (abs typ_base (app (var_b 1) (var_b 0))) (var_b 0)) ^ Y =
  (app (abs typ_base (app (var_f Y) (var_b 0))) (var_f Y)).
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

Ltac simpl_open :=
  unfold open_exp_wrt_exp; unfold open_exp_wrt_exp_rec; simpl;
  fold open_exp_wrt_exp_rec; fold open_exp_wrt_exp.

(*************************************************************************)
(** * Local closure *)
(*************************************************************************)

(* The local closure judgement classifies terms that have no dangling
   indices.

   Step through this derivation to see why the term is locally closed.
*)

Lemma demo_lc :
  lc_exp (app (abs typ_base (app (var_f Y) (var_b 0))) (var_f Y)).
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
    with the free variable and subst functions. *)


Lemma subst_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  [x1 ~> e1] (open e3 e2) = open ([x1 ~> e1] e3) ([x1 ~> e1] e2).
Proof.
Admitted.

(** We also define a notation for [open_rec] to make stating some of
    the properties simpler. However, we don't need to use open_rec
    outside of this part of the tutorial so we make it a local
    notation, confined to this section. *)
(*
Section BasicOperations.
Local Notation "{ k ~> u } t" := (open_exp_wrt_exp_rec k u t) (at level 67).





Inductive degree : nat -> exp -> Prop :=
  | degree_var_f : forall n1 x1,
    degree n1 (var_f x1)
  | degree_var_b : forall n1 n2,
    lt n2 n1 ->
    degree n1 (var_b n2)
  | degree_abs : forall n1 T1 e1,
    degree (S n1) e1 ->
    degree n1 (abs T1 e1)
  | degree_app : forall n1 e1 e2,
    degree n1 e1 ->
    degree n1 e2 ->
    degree n1 (app e1 e2).

Hint Constructors degree.

(** These define only an upper bound, not a strict upper bound. *)

Lemma degree_S :
(forall n1 e1,
  degree n1 e1 ->
  degree (S n1) e1).
Proof.
induction 1; eauto.
Qed.

Lemma subst_exp_degree :
(forall e1 e2 x1 n1,
  degree n1 e1 ->
  degree n1 e2 ->
  degree n1 (subst_exp e2 x1 e1)).
Proof.
  induction 1; intros; simpl; auto.
  - destruct (x0 == x1); auto.
  - econstructor. apply IHdegree. apply degree_S. auto.
Qed.


(*
Lemma subst_exp_open_exp_wrt_exp :
forall n e3 e1 e2 x1,
  degree n e2 ->
  subst_exp e1 x1 (open_exp_wrt_exp_rec n e3 e2) = open_exp_wrt_exp_rec n (subst_exp e1 x1 e3) (subst_exp e1 x1 e2).
Proof.
  induction e2; intros.
  - simpl.
    destruct (lt_eq_lt_dec n0 n).
    destruct s. simpl. auto. auto. simpl. auto.
  - simpl.
    destruct (x == x1).
    subst.
Admitted.
*)

Lemma open_exp_wrt_exp_degree : (forall e2 e1, degree 0 e2 -> e2 ^ e1 = e2).
Proof.
  induction e2; intros.
  unfold open_exp_wrt_exp.
  simpl. inversion H; subst.
Admitted.


(** The first property we would like to show is the analogue to
    [subst_fresh]: index substitution has no effect for closed terms.

    Here is an initial attempt at the proof.
*)


Lemma open_rec_lc_0 : forall k u e,
  lc_exp e ->
  e = {k ~> u} e.
Proof.
  intros k u e LC.
  induction LC.
  Case "lc_var_f".
    simpl.
    auto.
  Case "lc_abs".
    simpl.
    f_equal.
Admitted.

(** At this point there are two problems.  Our goal is about
    substitution for index [S k] in term [e], while our induction
    hypothesis IHLC only tells use about index [k] in term [e ^ x].

    To solve the first problem, we generalize our IH over all [k].
    That way, when [k] is incremented in the [abs] case, it will still
    apply.  Below, we use the tactic [generalize dependent] to
    generalize over [k] before using induction.
*)

Lemma open_rec_lc_1 : forall k u e,
  lc_exp e ->
  e = {k ~> u} e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC.
  Case "lc_var_f".
    simpl. auto.
  Case "lc_abs".
    simpl.
    intro k.
    f_equal.
Admitted.

(** At this point we are still stuck because the IH concerns
    [e ^ x] instead of [e]. The result that we need is that if an
    index substitution has no effect for an opened term, then it has
    no effect for the raw term (as long as we are *not* substituting
    for [0], hence [S k] below).
<<
   open e x = {S k ~> u}(open e x)  -> e = {S k ~> u} e
>>
   In other words, expanding the definition of open:
<<
   {0 ~> x}e = {S k ~> u}({0 ~> x} e)  -> e = {S k ~> u} e
>>
   Of course, to prove this result, we must generalize
   [0] and [S k] to be any pair of inequal numbers to get a strong
   enough induction hypothesis for the [abs] case.
 *)

Lemma open_rec_lc_core : forall e j v i u,
  i <> j ->
  {j ~> v} e = {i ~> u} ({j ~> v} e) ->
  e = {i ~> u} e.
Proof.
Admitted.
(*
  induction e; intros j v i u Neq H; simpl in *.
  Case "var_b".
    destruct (j == n);  destruct (i == n).
      SCase "j = n = i".
        subst n. destruct Neq. auto.
      SCase "j = n, i <> n".
        admit.
      SCase "j <> n, i = n".
        subst n. simpl in H.
        destruct (i == i).
           SSCase "i=i".
             auto.
           SSCase "i<>i".
             destruct n. auto.
      SCase "j <> n, i <> n".
        auto.
  Case "var_f".
    auto.
  Case "abs".
    f_equal.
    inversion H.
    apply  IHe with (j := S j) (u := u) (i := S i) (v := v).
    auto.
    auto.
  Case "app".
    inversion H.
    f_equal.
    eapply IHe1; eauto.
    eapply IHe2; eauto.
Qed. *)

(* Take-home Exercise: We've proven the above lemma very explicitly,
   so that you can step through it slowly to see how it
   works. However, with automation, it is possible to give a *much*
   shorter proof. Reprove this lemma on your own to see how compact
   you can make it. *)

(* SOLUTION *)
Lemma open_rec_lc_core_automated : forall e j v i u,
  i <> j ->
  {j ~> v} e = {i ~> u} ({j ~> v} e) ->
  e = {i ~> u} e.
Proof with try solve [eauto | congruence].
  induction e; intros j v i u Neq H; simpl in *;
      try solve [inversion H; f_equal; eauto].
  Case "var_b".
    destruct (j == n)...
    destruct (i == n)...
Admitted.


(** With the help of this lemma, we can complete the proof. *)

Lemma open_rec_lc : forall k u e,
  lc_exp e -> e = {k ~> u} e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC.
  Case "lc_var_f".
    simpl.
    auto.
  Case "lc_abs".
    simpl.
    intro k.
    f_equal.
    unfold open_exp_wrt_exp in *.
    apply open_rec_lc_core with
      (i := S k) (j := 0) (u := u) (v := var_f Y).
    auto.
    auto.
  Case "lc_app".
    intro k.
    simpl.
    f_equal.
    auto.
    auto.
Qed.


(** Take-home Exercise [subst_open_rec] *)

(** The next lemma demonstrates that free variable substitution
    distributes over index substitution.

    The proof of this lemma is by straightforward induction over
    [e1]. When [e1] is a free variable, we need to appeal to
    [open_rec_lc], proved above.
*)

Lemma subst_open_rec : forall e1 e2 u (x : var) k,
  lc_exp u ->
  [x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
Proof.
Admitted.
(*  (* SOLUTION *)
  induction e1; intros e2 u x0 k H; simpl in *; f_equal; auto.
  Case "var_b".
    destruct (k == n); auto.
  Case "var_f".
    destruct (x == x0); subst; auto.
    apply open_rec_lc; auto.
Qed.
*)
*)


(** *** Exercise [subst_exp_open_exp_wrt_exp_var] *)

(** The lemma above is most often used with [e2] as some fresh
    variable. Therefore, it simplifies matters to define the following useful
    corollary.

    HINT: Do not use induction.  Rewrite with [subst_exp_open_exp_wrt_exp] and
    [subst_neq_var].

*)

Lemma subst_exp_open_exp_wrt_exp_var : forall (x y : var) u e,
  y <> x ->
  lc_exp u ->
  ([x ~> u] e) ^ y = [x ~> u] (e ^ y).
Proof.
  (* SOLUTION *)
  intros x y u e Neq H.
  rewrite subst_exp_open_exp_wrt_exp with (e2 := var_f y); auto.
  rewrite subst_neq_var; auto.
Qed.

(** *** Take-home Exercise [subst_intro] *)

(** This lemma states that opening can be replaced with variable
    opening and substitution.

    HINT: Prove by induction on [e], first generalizing the
    argument to [open] by using the [generalize] tactic, e.g.,
    [generalize 0].

*)

Lemma subst_exp_intro : forall (x : var) u e,
  x `notin` (fv_exp e) ->
  open e u = [x ~> u](e ^ x).
Proof.
  (* SOLUTION *)
  intros x u e FV_EXP.
  unfold open.
  unfold open_exp_wrt_exp.
  generalize 0.
  induction e; intro n0; simpl.
  Case "var_b".
    destruct (lt_eq_lt_dec n n0).
    destruct s. simpl. auto.
    rewrite subst_eq_var. auto.
    simpl. auto.
  Case "var_f".
    destruct (x0 == x). subst. simpl in FV_EXP. fsetdec. auto.
  Case "abs".
    f_equal. simpl in FV_EXP. apply IHe. auto.
  Case "app".
    simpl in FV_EXP.
    f_equal.
    apply IHe1. auto.
    apply IHe2. auto.
Qed.


(* End BasicOperations. *)


(*************************************************************************)
(** Quantification in inductive predicates. *)
(*************************************************************************)

(* In the next example, we will reexamine the definition of
   [lc_exp] in the [abs] case.

   The lemma [subst_lc] says that local closure is preserved by
   substitution.  Let's start working through this proof.
*)

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
    rewrite subst_exp_open_exp_wrt_exp_var.
    apply H0.
Admitted.

(** Here we are stuck. We don't know that [x0] is not equal to [x],
    which is a preconduction for [subst_exp_open_exp_wrt_exp_var].

    The solution is to prove an alternative introduction rule for
    local closure for abstractions.  In the current rule, we need
    to show that the body of the abstraction is locally closed,
    no matter what variable we choose for the binder.


<<
  | lc_abs : forall e,
      (forall x:var, lc_exp (open e x)) ->
      lc_exp (abs e)
>>

    An easier to use lemma, requires us to only show that the body
    of the abstraction is locally closed for a *single* variable.
    The Lemmas file walks through the proof of this result; for
    convenience we repeat it below.
*)
Lemma lc_abs_exists : forall (x : var) e T,
      lc_exp (e ^ x) ->
      lc_exp (abs T e).
Admitted.

(* With this addition, we can complete the proof of subst_lc. *)

Lemma subst_exp_lc_exp : forall (x : var) u e,
  lc_exp e ->
  lc_exp u ->
  lc_exp ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  - Case "lc_var_f".
    simpl. default_simp.
  - Case "lc_abs".
    simpl.
    pick fresh x0 for {{x}}.  (* make sure that x0 <> x *)
    eapply (lc_abs_exists x0).
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
  - Case "lc_app".
    default_simp.
Qed.



(*
    The solution is to change the *definition* of local closure so
    that we get a different induction principle.  Currently, in the
    [lc_abs] case, we show that an abstraction is locally closed by
    showing that the body is locally closed after it has been opened
    with one particular variable.

<<
  | lc_abs : forall (x : var) e,
      x `notin` fv_exp e ->
      lc_exp (open e x) ->
      lc_exp (abs e)
>>

    Therefore, our induction hypothesis in this case only applies to
    that variable. From the hypothesis list in the [lc_abs] case:

      x0 : var,
      IHHe : lc_exp ([x ~> u]open e x0)

    The problem is that we don't have any assumptions about [x0]. It
    could very well be equal to [x].

    A stronger induction principle provides an IH that applies to many
    variables. In that case, we could pick one that is "fresh enough".
    To do so, we need to revise the above definition of lc_exp and replace
    the type of lc_abs with this one:

<<
  | lc_abs_c : forall L e,
      (forall x:var, x `notin` L -> lc_exp (open e x)) ->
      lc_exp (abs e)
>>

   This rule says that to show that an abstraction is locally closed,
   we need to show that the body is closed, after it has been opened by
   any var [x], *except* those in some set [L]. With this rule, the IH
   in this proof is now:

     H0 : forall x0 : var, x0 `notin` L -> lc_exp ([x ~> u]open e x0)

   Below, lc_c is the local closure judgment revised to use this new
   rule in the abs case. We call this "cofinite quantification"
   because the IH applies to an infinite number of vars [x0], except
   those in some finite set [L].

   Changing the rule in this way does not change what terms are locally
   closed.  (For more details about cofinite-quantification see:
   "Engineering Formal Metatheory", Aydemir, Chargu'eraud, Pierce,
   Pollack, Weirich. POPL 2008.)

*)

(*
Inductive lc_c : exp -> Prop :=
  | lc_var_c : forall (x:var),
      lc_c x
  | lc_abs_c : forall (L : atoms) e T,
      (forall x : var, x `notin` L -> lc_c (open e x)) ->
      lc_c (abs T e)
  | lc_app_c : forall e1 e2,
      lc_c e1 ->
      lc_c e2 ->
      lc_c (app e1 e2).

Hint Constructors lc_c.

(* Reintroduce notation for [open_rec] so that we can reprove
   properties about it and the new version of lc_c. *)

Section CofiniteQuantification.
Local Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).

(* With this new definition, we can almost use the same proof for
   [open_rec_lc], we only need one change. We need to add the line
   [pick fresh x for L.]  immediately before the use of [apply
   open_rec_lc_core].  This tactic, defined in [Metatheory],
   introduces a new var [x] that is known not to be in the set [L].
*)

Lemma open_rec_lc_c : forall k u e,
  lc_c e ->
  e = {k ~> u} e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC.
  Case "lc_var_f".
    simpl.
    auto.
  Case "lc_abs".
    simpl.
    intro k.
    f_equal.
    unfold open in *.
    pick fresh x for L.  (* Note: NEW LINE added *)
    apply open_rec_lc_core with
      (i := S k) (j := 0) (u := u) (v := var_f x).
    auto.
    auto.
  Case "lc_app".
    intro k.
    simpl.
    f_equal.
    auto.
    auto.
Qed.

(* Take-home Exercise: The next two lemmas have exactly the same
   proofs as before. *)

Lemma subst_open_rec_c : forall e1 e2 u (x : var) k,
  lc_c u ->
  [x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
Proof.
(* SOLUTION *)
  induction e1; intros e2 u x0 k H; simpl in *; f_equal; auto.
  Case "var_b".
    destruct (k == n); auto.
  Case "var_f".
    destruct (x == x0); subst; auto.
    apply open_rec_lc_c; auto.
Qed.

Lemma subst_open_var_c : forall (x y : var) u e,
  y <> x ->
  lc_c u ->
  open ([x ~> u] e) y = [x ~> u] (open e y).
Proof.
  (* SOLUTION *)
  intros x y u e Neq H.
  unfold open.
  rewrite subst_open_rec_c with (e2 := var_f y); auto.
  rewrite subst_neq_var; auto.
Qed.

(* Exercise [subst_lc_c]:

   Once we have changed the definition of lc, we can complete the
   proof of subst_lc.

    HINT: apply lc_abs_c with cofinite set (L `union` singleton x).
    This gives us an var x0, and a hypothesis that
    x0 is fresh for both L and x.
*)

Lemma subst_lc_c : forall (x : var) u e,
  lc_c e ->
  lc_c u ->
  lc_c ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  Case "lc_var_c".
   simpl.
   destruct (x0 == x).
     auto.
     auto.
  Case "lc_abs_c".
    simpl.
    (* SOLUTION *)
    apply lc_abs_c with (L := L `union` singleton x).
    intros x0 Fr.
    rewrite subst_open_var_c. auto. auto. auto.
  Case "lc_app_c".
     simpl. auto.
Qed.

End CofiniteQuantification.
*)

(*************************************************************************)
(** * Tactic support *)
(*************************************************************************)

(** When picking a fresh var or applying a rule that uses cofinite
    quantification, choosing a set of vars to be fresh for can be
    tedious.  In practice, it is simpler to use a tactic to choose the
    set to be as large as possible.

    The tactic [gather_atoms] is used to collect together all the
    atoms in the context.  It relies on an auxiliary tactic,
    [gather_atoms_with] (from MetatheoryAtom), which maps a function
    that returns a finite set of atoms over all hypotheses with the
    appropriate type.
*)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  constr:(A `union` B `union` C `union` D).

(** A number of other, useful tactics are defined by the Metatheory
    library, and each depends on [gather_atoms].  By redefining
    [gather_atoms], denoted by the [::=] in its definition below, we
    automatically update these tactics so that they use the proper
    notion of "all atoms in the context."

    For example, the tactic [(pick fresh x)] chooses an atom fresh for
    "everything" in the context.  It is the same as [(pick fresh x for
    L)], except where [L] has been computed by [gather_atoms].

*)


(** *** Example

    The tactic [(pick fresh x and apply H)] applies a rule [H] that is
    defined using cofinite quantification.  It automatically
    instantiates the finite set of atoms to exclude using
    [gather_atoms].

    Below, we reprove [subst_lc_c] using [(pick fresh and apply)].
    Step through the proof below to see how [(pick fresh and apply)]
    works.
*)

(*
Lemma subst_lc_c_alternate_proof : forall (x : atom) u e,
  lc_c e ->
  lc_c u ->
  lc_c ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  Case "var_f".
   simpl.
   destruct (x0 == x).
     auto.
     auto.
  Case "abs".
    simpl.
    pick fresh y and apply lc_abs_c.
    (* Here, take note of the hypothesis [Fr]. *)
    rewrite subst_open_var_c. auto. auto. auto.
  Case "app".
     simpl. auto.
Qed.
*)

(*************************************************************************)
(*                                                                       *)
(*  Coffee break                                                         *)
(*                                                                       *)
(*************************************************************************)


(*************************************************************************)
(** * Typing environments *)
(*************************************************************************)

(** We represent environments as association lists (lists of pairs of
    keys and values) whose keys are [atom]s.
*)

(** For STLC, environments bind [atom]s to [typ]s.  We define an
    abbreviation [env] for the type of these environments.

    Lists are defined in Coq's standard library, with the constructors
    [nil] and [cons].  The list library includes the [::] notation
    for cons as well as standard list operations such as append, map,
    and fold. The infix operation "++" is list append.

    The Metatheory library extends this reasoning by instantiating the
    AssocList library to provide support for association lists whose
    keys are [atom]s.  Everything in this library is polymorphic over
    the type of objects bound in the environment.  Look in AssocList
    for additional details about the functions and predicates that we
    mention below.
*)

(** Environment equality *)

(** When reasoning about environments, we often need to talk about
    bindings in the "middle" of an environment. Therefore, it is common
    for lemmas and definitions to use list append in their statements.
    Unfortunately, list append is associative, so two Coq expressions may
    denote the same environment even though they are not equal.

    The tactic [simpl_env] reassociates all concatenations of
    environments to the right.
*)

Lemma append_assoc_demo : forall (E0 E1 E2 E3:env),
  E0 ++ (E1 ++ E2) ++ E3 = E0 ++ E1 ++ E2 ++ E3.
Proof.
  intros.
  auto. (* Does nothing. *)
  simpl_env.
  reflexivity.
Qed.

(** To make environments easy to read, instead of building them from
    [nil] and [cons], we prefer to build them from the following
    components:
      - [nil]: The empty list.
      - [one]: Lists consisting of exactly one item.
      - [++]:  List append.

   Furthermore, we introduce compact notation for one (singleton lists):
   [(x ~ T)] is the same as [one (x, T)].
*)

(** The simpl_env tactic actually puts lists built from only nil, one
    and [++] into a "normal form". This process reassociates all appends
    to the right, removes extraneous nils converts cons to singleton
    lists with an append.
*)

Lemma simpl_env_demo : forall (x y:atom) (T1 T2:typ) (E F:env),
   ((x ~ T1) ++ nil) ++ (y,T2) :: (nil ++ E) ++ F =
   (x ~ T1) ++ (y ~ T2) ++ E ++ F.
Proof.
   intros.
   (* simpl_env puts the left side into the normal form. *)
   simpl_env.
   reflexivity.
Qed.

(** Note that the [simpl] tactic doesn't produce the "normal form" for
    environments. It should always be followed up with [simpl_env].

    Furthermore, to convert an environment to any equivalent form
    other than the normal form (perhaps to apply a lemma) use the
    tactic [rewrite_env].
*)

Lemma rewrite_env_demo : forall (x y:atom) (T:typ) P,
  (forall E, P ((x,T):: E) -> True) ->
  P (x ~ T) ->
  True.
Proof.
  intros x y T P H.
  (* apply H. fails here. *)
  rewrite_env ((x,T) :: nil).
  apply H.
Qed.

(** Environment operations. *)

(** The ternary predicate [binds] holds when a given binding is
    present somewhere in an environment.
*)

Lemma binds_demo : forall (x:atom) (T:typ) (E F:env),
  binds x T (E ++ (x ~ T) ++ F).
Proof.
  auto.
Qed.

(** The function [dom] computes the domain of an environment,
    returning a finite set of [atom]s. Note that we cannot use Coq's
    equality for finite sets, we must instead use a defined relation
    [=] for atom set equality.
 *)

Lemma dom_demo : forall (x y : atom) (T : typ),
  dom (x ~ T) [=] singleton x.
Proof.
  auto.
Qed.

(** The unary predicate [uniq] holds when each atom is bound at most
    once in an environment.
*)

Lemma uniq_demo : forall (x y : atom) (T : typ),
  x <> y -> uniq ((x ~ T) ++ (y ~ T)).
Proof.
  auto.
Qed.


(*************************************************************************)
(** * Typing relation *)
(*************************************************************************)

(** The definition of the typing relation is straightforward.  In
    order to ensure that the relation holds for only well-formed
    environments, we check in the [typing_var] case that the
    environment is [uniq].  The structure of typing derivations
    implicitly ensures that the relation holds only for locally closed
    expressions.

    Finally, note the use of cofinite quantification in
    the [typing_abs] case.
*)

Inductive typing_e : env -> exp -> typ -> Prop :=
  | typing_e_var : forall E (x : atom) T,
      uniq E ->
      binds x T E ->
      typing_e E (var_f x) T
  | typing_e_abs : forall x E e T1 T2,
      x `notin` dom E ->
      typing_e ((x ~ T1) ++ E) (e ^ x) T2 ->
      typing_e E (abs T1 e) (typ_arrow T1 T2)
  | typing_e_app : forall E e1 e2 T1 T2,
      typing_e E e1 (typ_arrow T1 T2) ->
      typing_e E e2 T1 ->
      typing_e E (app e1 e2) T2.

(** We add the constructors of the typing relation as hints to be used
    by the [auto] and [eauto] tactics.
*)

Hint Constructors typing_e.


(*************************************************************************)
(** * Weakening and CoFinite quantification *)
(*************************************************************************)

(** Weakening states that if an expression is typeable in some
    environment, then it is typeable in any well-formed extension of
    that environment.  This property is needed to prove the
    substitution lemma.

    As stated below, this lemma is not directly proveable.  The
    natural way to try proving this lemma proceeds by induction on the
    typing derivation for [e].
*)


Lemma typing_weakening_0 : forall E F e T,
  typing_e E e T ->
  uniq (F ++ E) ->
  typing_e (F ++ E) e T.
Proof.
  intros E F e T H J.
  induction H; auto.
  Case "typing_abs".
    apply (typing_e_abs x).
    (* ... stuck here ... *)
Admitted.

(** We are stuck in the [typing_abs] case because the induction
    hypothesis [IHtyping_e] applies only when we weaken the environment at its
    head.  In this case, however, we need to weaken the environment in
    the middle; compare the conclusion at the point where we're stuck
    to the hypothesis [H], which comes from the given typing derivation.

    We can obtain a more useful induction hypothesis by changing the
    statement to insert new bindings into the middle of the
    environment, instead of at the head.  However, the proof still
    gets stuck, as can be seen by examining each of the cases in
    the proof below.

    Note: To view subgoal n in a proof, use the command "[Show n]".
    To work on subgoal n instead of the first one, use the command
    "[Focus n]".
*)

Lemma typing_weakening_strengthened_0 : forall (E F G : env) e T,
  typing_e (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing_e (G ++ F ++ E) e T.
Proof.
  intros E F G e T H J.
  induction H.
  Case "typing_var".
    (* The G0 looks strange in the [typing_var] case. *)
  Focus 2.
  Case "typing_abs".
    (* The [typing_abs] case still does not have a strong enough IH. *)
Admitted.

(** The hypotheses in the [typing_var] case include an environment
    [G0] that that has no relation to what we need to prove.  The
    missing fact we need is that [G0 = (G ++ E)].

    The problem here arises from the fact that Coq's [induction]
    tactic let's us only prove something about all typing derivations.
    While it's clear to us that weakening applies to all typing
    derivations, it's not clear to Coq, because the environment is
    written using concatenation.  The [induction] tactic expects that
    all arguments to a judgement are variables.  So we see [E0] in the
    proof instead of [(G ++ E)].

    The solution is to restate the lemma.  For example, we can prove

<<
  forall E F E' e T, typing E' e T ->
  forall G, E' = G ++ E -> uniq (G ++ F ++ E) -> typing (G ++ F ++ E) e T.
>>

    The equality gets around the problem with Coq's [induction]
    tactic.  The placement of the [(forall G)] quantifier gives us a
    sufficiently strong induction hypothesis in the [typing_abs] case.

    However, we prefer not to state the lemma in the way shown above,
    since it is not as readable as the original statement.  Instead,
    we use a tactic to introduce the equality within the proof itself.
    The tactic [(remember t as t')] replaces an object [t] with the
    identifier [t'] everywhere in the goal and introduces an equality
    [t' = t] into the context.  It is often combined with [generalize
    dependent], as illustrated below.
*)

Lemma typing_weakening_strengthened_1 :  forall (E F G : env) e T,
  typing_e (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing_e (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G0 Eq Uniq; subst.
  - Case "typing_var". auto.
  - Case "typing_abs".
    eapply (typing_e_abs x).
    (* STILL STUCK! *)
Admitted.

Print typing_abs.

(** At this point, we are very close. However, there is still one issue. We
    cannot show that [x] is fresh for the weakened environment [F].

    This is the difficulty with the definition of [typing_e]. As in the local
    closure judgement, the induction hypotheses is not strong enough in the
    [abs] case.

    However, this time, we take a slightly different solution. Instead of
    quantifying over all variables that are fresh for all but a known and
    fixed set of atoms, we quantify over all variabels that are fresh for all
    but some, unknown set of atoms.


<<
| typing_abs :
    forall (L : atoms) (G : env) (T1 : typ) (e : exp) (T2 : typ),
    (forall x, x `notin` L -> typing ([(x, T1)] ++ G) (e ^ x) T2) ->
    typing (abs T1 e) (typ_arrow T1 T2) >>
>>

   We call this "cofinite quantification". The advantage of this definition
   is that it is easier to derive the "exists-fresh" version of the rule
   [typing_e_abs] as a lemma, than the version we used in [lc_exp].
   (See below, we prove this lemma after we show substitution.) At the same
   time, this version of the rule is sufficiently expressive to complete
   the proof of weakening.

*)


(** *** Exercise

    Complete the proof below, using the [typing] relation from [Definitions.v].

    HINTS:

       - The [typing_var] case follows from [binds_weaken], the
         weakening lemma for the [binds] relation.

       - The [typing_abs] case follows from the induction
         hypothesis, but the [apply] tactic may be unable to unify
         things as you might expect.

           -- Recall the [pick fresh and apply] tactic.

           -- In order to apply the induction hypothesis, use
              [rewrite_env] to reassociate the list operations.

           -- After applying the induction hypothesis, use
              [simpl_env] to use [uniq_push].

           -- Here, use [auto] to solve facts about finite sets of
              atoms, since it will simplify the [dom] function behind
              the scenes.  [fsetdec] does not work with the [dom]
              function.

       - The [typing_app] case follows directly from the induction
         hypotheses.
  *)

Lemma typing_weakening_strengthened :  forall (E F G : env) e T,
  typing (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G0 Eq Uniq; subst.
 (* SOLUTION *)
  Case "typing_var".
    apply typing_var.
      apply Uniq.
      apply binds_weaken. auto.
  Case "typing_abs".
    pick fresh x and apply typing_abs.
    rewrite_env (((x ~ T1) ++ G0) ++ F ++ E).
    apply H0.
      auto.
      simpl_env. reflexivity.
      simpl_env. apply uniq_push.
        apply Uniq.
        auto.
  Case "typing_app".
    eapply typing_app.
      eapply IHtyping1. reflexivity. apply Uniq.
      eapply IHtyping2. reflexivity. apply Uniq.
Qed.


(** *** Example

    We can now prove our original statement of weakening.  The only
    interesting step is the use of the rewrite_env tactic.
*)

Lemma typing_weakening : forall (E F : env) e T,
    typing E e T ->
    uniq (F ++ E) ->
    typing (F ++ E) e T.
Proof.
  intros E F e T H J.
  rewrite_env (nil ++ F ++ E).
  apply typing_weakening_strengthened; auto.
Qed.


(*************************************************************************)
(** * Substitution *)
(*************************************************************************)

(** Having proved weakening, we can now prove the usual substitution
    lemma, which we state both in the form we need and in the
    strengthened form needed to make the proof go through.

<<
  typing_subst_simple : forall E e u S T z,
    typing ((z ~ S) ++ E) e T ->
    typing E u S ->
    typing E ([z ~> u] e) T

  typing_subst : forall E F e u S T z,
    typing (F ++ (z ~ S) ++ E) e T ->
    typing E u S ->
    typing (F ++ E) ([z ~> u] e) T
>>

    The proof of the strengthened statement proceeds by induction on
    the given typing derivation for [e].  The most involved case is
    the one for variables; the others follow from the induction
    hypotheses.
*)


(** *** Exercise

    Below, we state what needs to be proved in the [typing_var] case
    of the substitution lemma.  Fill in the proof.

    Proof sketch: The proof proceeds by a case analysis on [(x == z)],
    i.e., whether the two variables are the same or not.

      - If [(x = z)], then we need to show [(typing (F ++ E) u T)].
        This follows from the given typing derivation for [u] by
        weakening and the fact that [T] must equal [S].

      - If [(x <> z)], then we need to show [(typing (F ++ E) x T)].
        This follows by the typing rule for variables.

    HINTS: Lemmas [binds_mid_eq], [uniq_remove_mid],
    and [binds_remove_mid] are useful.

  *)

Lemma typing_subst_var_case : forall (E F : env) u S T (z x : atom),
  binds x T (F ++ (z ~ S) ++ E) ->
  uniq (F ++ (z ~ S) ++ E) ->
  typing E u S ->
  typing (F ++ E) ([z ~> u] (var_f x)) T.
Proof.
  intros E F u S T z x H J K.
  simpl.
 (* SOLUTION *)
  destruct (x == z).
  Case "x = z".
    subst.
    assert (T = S).
      eapply binds_mid_eq. apply H. apply J.
    subst.
    apply typing_weakening.
      apply K.
      eapply uniq_remove_mid. apply J.
  Case "x <> z".
    apply typing_var.
      eapply uniq_remove_mid. apply J.
      eapply binds_remove_mid. apply H. apply n.
Qed.

(** *** Note

    The other two cases of the proof of the substitution lemma are
    relatively straightforward.  However, the case for [typing_abs]
    needs the fact that the typing relation holds only for
    locally-closed expressions.
*)

Lemma typing_to_lc_exp : forall E e T,
  typing E e T -> lc_exp e.
Proof.
  intros E e T H. induction H; eauto.
Qed.


(** *** Exercise

    Complete the proof of the substitution lemma. The proof proceeds
    by induction on the typing derivation for [e].  The initial steps
    should use [remember as] and [generalize dependent] in a manner
    similar to the proof of weakening.

   HINTS:
      - Use the lemma proved above for the [typing_var] case.

      - The [typing_abs] case follows from the induction hypothesis.
         -- Use [simpl] to simplify the substitution.

          -- Recall the tactic [pick fresh and apply].

          -- In order to use the induction hypothesis, use
             [subst_open_var_c] to push the substitution under the
             opening operation.

          -- Recall the lemma [typing_to_lc_c] and the
             [rewrite_env] and [simpl_env] tactics.

      - The [typing_app] case follows from the induction hypotheses.
        Use [simpl] to simplify the substitution.
*)

Lemma typing_subst : forall (E F : env) e u S T (z : atom),
  typing (F ++ (z ~ S) ++ E) e T ->
  typing E u S ->
  typing (F ++ E) ([z ~> u] e) T.
Proof.
(* SOLUTION *)
  intros E F e u S T z He Hu.
  remember (F ++ (z ~ S) ++ E) as E'.
  generalize dependent F.
  induction He.
  Case "typing_var".
    intros F Eq.
    subst.
    eapply typing_subst_var_case. apply H0. apply H. apply Hu.
  Case "typing_abs".
    intros F Eq.
    subst.
    simpl.
    pick fresh y and apply typing_abs.
    rewrite subst_exp_open_exp_wrt_exp_var.
    rewrite_env (((y ~ T1) ++ F) ++ E).
    apply H0.
      auto.
      simpl_env. reflexivity.
    (* The following subgoals are from [rewrite subst_open_var]. *)
    auto.
    eapply typing_to_lc_exp. apply Hu.
  Case "typing_app".
    intros F Eq. subst. simpl. eapply typing_app.
      apply IHHe1. reflexivity.
      apply IHHe2. reflexivity.
Qed.

(** *** Exercise

    Complete the proof of the substitution lemma stated in the form we
    need it.  The proof is similar to that of [typing_weakening].

    HINT: You'll need to use [rewrite_env] to prepend [nil],
    and [simpl_env] to simplify nil away.
*)

Lemma typing_subst_simple : forall (E : env) e u S T (z : atom),
  typing ((z ~ S) ++ E) e T ->
  typing E u S ->
  typing E ([z ~> u] e) T.
Proof.
(* SOLUTION *)
  intros E e u S T z H J.
  rewrite_env (nil ++ E).
  eapply typing_subst.
    simpl_env. apply H.
    apply J.
Qed.

(*************************************************************************)
(** * Values and Evaluation *)
(*************************************************************************)

(** In order to state the preservation lemma, we first need to define
    values and the small-step evaluation relation.  These inductive
    relations are straightforward to define.

    Note the hypotheses which ensure that the relations hold only for
    locally closed terms.  Below, we prove that this is actually the
    case, since it is not completely obvious from the definitions
    alone.
*)

Lemma eval_lc_exp1 : forall e1 e2, eval e1 e2 -> lc_exp e1.
Proof. induction 1; auto. Qed.
Lemma eval_lc_exp2 : forall e1 e2, eval e1 e2 -> lc_exp e2.
Proof. induction 1; auto.
       - pick fresh x.
         rewrite (subst_exp_intro x).
         inversion H0.
         default_simp.
         apply subst_exp_lc_exp; auto.
         fsetdec.
Qed.

(*************************************************************************)
(** * Preservation *)
(*************************************************************************)

(** *** Take-home Exercise

    Complete the proof of preservation.  In this proof, we proceed by
    induction on the given typing derivation.  The induction
    hypothesis has already been appropriately generalized by the given
    proof fragment.

    Proof sketch: By induction on the typing derivation for [e].

      - [typing_var] case: Variables don't step.

      - [typing_abs] case: Abstractions don't step.

      - [typing_app] case: By case analysis on how [e] steps. The
        [eval_beta] case is interesting, since it follows by the
        substitution lemma.  The others follow directly from the
        induction hypotheses.
*)

  (* HINTS:

       - Use [auto] and [eauto], especially with [;], to solve
         "uninteresting" subgoals.

       - Use [inversion] to perform case analyses and to rule out
         impossible cases.

       - In the [eval_beta] subcase of the [typing_app] case:

          -- Use [inversion] on a typing judgement to obtain a
             hypothesis about when the body of the abstraction is
             well-typed.

          -- Use [subst_intro] to rewrite the [open] operation into an
             [open] followed by a [subst].  You'll need to pick a
             fresh variable first.

  *)

Lemma preservation : forall (E : env) e e' T,
  typing E e T ->
  eval e e' ->
  typing E e' T.
Proof.
  intros E e e' T H.
  generalize dependent e'.
  induction H; intros e' J.
(* SOLUTION *)
  Case "typing_var".
    inversion J.
  Case "typing_abs".
    inversion J.
  Case "typing_app".
    inversion J; subst; eauto.
    SCase "eval_beta".
      inversion H; subst.
      pick fresh y.
      rewrite (subst_exp_intro y); auto.
      eapply typing_subst_simple; auto.
Qed.

(*************************************************************************)
(** * Progress *)
(*************************************************************************)

(** *** Exercise

    Complete the proof of the progress lemma.  The induction
    hypothesis has already been appropriately generalized by the given
    proof fragment.

    Proof sketch: By induction on the typing derivation for [e].

      - [typing_var] case: Can't happen; the empty environment doesn't
        bind anything.

      - [typing_abs] case: Abstractions are values.

      - [typing_app] case: Applications reduce.  The result follows
        from an exhaustive case analysis on whether the two components
        of the application step or are values and the fact that a
        value must be an abstraction.
*)

  (* HINTS:

       - Use [auto] and [eauto], especially with [;], to solve
         "uninteresting" subgoals.

       - Use [inversion] to rule out impossible cases.

       - The lemma [typing_to_lc_c] will be useful for reasoning
         about local closure.

       - In the [typing_app] case:

          -- Use [destruct] to perform a case analysis on the
             conclusions of the induction hypotheses.

          -- Use [inversion] on a [value] judgement to determine that
             the value must be an abstraction.
  *)



Lemma progress : forall e T,
  typing nil e T ->
  is_value_of_exp e \/ exists e', eval e e'.
Proof.
  intros e T H.

  (* It will be useful to have a "non-destructed" form of the given
     typing derivation, since [induction] takes apart the derivation
     it is called on. *)
  assert (typing nil e T); auto.

  (* [remember nil as E] fails here because [nil] takes an implicit
     argument that Coq is unable to infer.  By prefixing [nil] with
     [@], we can supply the argument to nil explicitly. *)
  remember (@nil (atom * typ)) as E.

  induction H; subst.

(* SOLUTION *)
  - Case "typing_var".
    inversion H1.
  - Case "typing_abs".
    left.
    simpl. auto.
  - Case "typing_app".
    right.
    destruct IHtyping1 as [V1 | [e1' Eval1]]; auto.
      + SCase "e1 is a value".
      destruct IHtyping2 as [V2 | [e2' Eval2]]; auto.
        SSCase "e2 is a value".
        destruct e1; inversion V1; subst. exists (open_exp_wrt_exp e1 e2); eauto using typing_to_lc_exp.
        SSCase "e2 is not a value".
          exists (app e1 e2'). eauto using typing_to_lc_exp.
      + SCase "e1 is not a value".
        exists (app e1' e2).
        apply eval_app1.
          eapply typing_to_lc_exp; eauto.
          assumption.
Qed.


(*************************************************************************)
(** * Renaming *)
(*************************************************************************)

(* Substitution and weakening together give us a property we call
   renaming: (see [typing_rename below] that we can change the name
   of the variable used to open an expression in a typing
   derivation. In practice, this means that if a variable is not
   "fresh enough" during a proof, we can use this lemma to rename it
   to one with additional freshness constraints.

   Renaming is used below to show the correspondence between the
   exists-fresh version of the rules with the cofinite version, and
   also to show that typechecking is decidable.
*)

(*
   However, before we prove renaming, we need an auxiliary lemma about
   typing judgments which says that terms are well-typed only in
   unique environments.
*)

Lemma typing_uniq : forall E e T,
  typing E e T -> uniq E.
Proof.
  intros E e T H.
  induction H; auto.
  - Case "typing_abs".
    pick fresh x.
    assert (uniq ((x ~ T1) ++ G)); auto.
    inversion H1. auto.
Qed.


(*
   Demo: the proof of renaming.

   Note that this proof does not proceed by induction: even if we add
   new typing rules to the language, as long as the weakening and
   substution properties hold we can use this proof.
*)
Lemma typing_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv_exp e ->
  y `notin` dom E    ->
  typing ((x ~ T1) ++ E) (e ^ x) T2 ->
  typing ((y ~ T1) ++ E) (e ^ y) T2.
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
  destruct (x == y).
  - Case "x = y".
    subst; eauto.
  - Case "x <> y".
    assert (J : uniq ((x ~ T1) ++ E)).
      eapply typing_uniq; eauto.
    assert (J' : uniq E).
      inversion J; eauto.
    rewrite (@subst_exp_intro x); eauto.
    rewrite_env (nil ++ (y ~ T1) ++ E).
    apply typing_subst with (S := T1).
    simpl_env.
    + SCase "(open x s) is well-typed".
      apply typing_weakening_strengthened. eauto. auto.
    + SCase "y is well-typed".
      eapply typing_var; eauto.
Qed.


(*************************************************************************)
(** * Exists-Fresh Definitions *)
(*************************************************************************)

(* The use of cofinite quantification may make some people worry that we
   are not formalizing the "right" language. Below, we show that
   the "exists-fresh" version of the rules is the same as the cofinite
   version. *)

Lemma typing_abs_exists : forall E e T1 T2 (x : atom),
      x `notin` fv_exp e ->
      typing ((x ~ T1) ++ E) (e ^ x) T2 ->
      typing E (abs T1 e) (typ_arrow T1 T2).
Proof.
  intros.
  apply typing_abs with (L := dom E \u fv_exp e).
  intros y Fr.
  apply typing_rename with (x:=x); auto.
Qed.


(*************************************************************************)
(** * Decidability of Typechecking *)
(*************************************************************************)

(* Finally, we give another example of a proof that makes use of the
   renaming lemma. We show that determining whether a program type
   checks is decidable.
*)

(** Equality on types is decidable *)
Lemma eq_typ_dec : forall (T T' : typ),
  { T = T' } + { T <> T' }.
Proof.
  decide equality.
Qed.

(** Take-home exercise.

    To prove that ill-formed terms cannot be typechecked, we will need an
    auxiliary lemma that says that each term only has a single type.

    HINT: to prove this lemma you will need to generalize the induction
    hypothesis for T2 and use the lemma [binds_unique] from [AtomEnv.v].
*)
Lemma typing_unique : forall E e T1 T2,
  typing E e T1 ->
  typing E e T2 ->
  T1 = T2.
Proof.
(* SOLUTION *)
  intros E e T1 T2 Typ1 Typ2.
  generalize dependent T2.
  induction Typ1; intros T' Typ'; inversion Typ'; subst; eauto.
  Case "typing_var".
    eapply binds_unique; eauto.
  Case "typing_abs".
    f_equal; eauto.
    pick fresh x.
    apply (H0 x); eauto.
  Case "typing_app".
    assert (typ_arrow T1 T2 = typ_arrow T3 T') by auto.
    inversion H; eauto.
Qed.


(* A property P is decidable if we can show the proposition P \/ ~P. *)
Definition decidable (P : Prop) := (P \/ ~ P).

Lemma typing_decidable : forall E e,
  lc_exp e -> uniq E -> decidable (exists T, typing E e T).
Proof.
  intros E e LC Uniq.
  generalize dependent E.
  induction LC; intros E Uniq.
  - Case "typing_var".
    destruct (@binds_lookup_dec _ x E) as [[T H] | H].
      SCase "variable is in environment".
      left; eauto.
      SCase "variable not in environment".
      right.  intros [T J]. inversion J; subst; eauto.
  - Case "typing_abs".
    (* To know whether the body typechecks, we must first
       pick a fresh variable to use the IH (aka HO).
    *)
    pick fresh x.
    destruct (H0 x ((x ~ T) ++ E)) as [[S J] | J]; eauto.
    SCase "body typeable".
      left.
      exists (typ_arrow T S).
      (* Check (typing_abs L E (abs T e) T S). *)
      pick fresh z and apply typing_abs.
      apply typing_rename with (x := x); eauto.
    SCase "body not typeable".
      right.
      intros [S K].
      inversion K; subst.
      apply J.
      exists T2.
      pick fresh z.
      apply typing_rename with (x := z); eauto.
  - Case "typing_app".
    destruct (IHLC1 E) as [[T H] | H]; eauto.
    SCase "function typeable".
      destruct (IHLC2 E) as [[S J] | J]; eauto.
      SSCase "argument typeable".
        destruct T.
          SSSCase "function has typ_base".
            right.
            intros [S' J'].
            inversion J'; subst.
            assert (K : typ_base = typ_arrow T1 S'); eauto using typing_unique.
            inversion K.
          SSSCase "typ_arrow".
            destruct (eq_typ_dec T1 S).
              subst. left; eauto.
              right.
                intros [S' J'].
                inversion J'; subst.
                assert (T3 = S); eauto using typing_unique.
                assert (typ_arrow T1 T2 = typ_arrow T3 S'); eauto using typing_unique.
                inversion H1; subst; eauto using typing_unique.
      SSCase "argument not typeable".
        right. intros [S' J']. inversion J'; subst; eauto.
    SCase "function not typeable".
      right. intros [S' J']. inversion J'; subst; eauto.
Qed.

(*************************************************************)

(* We also want a property that states that the free variables of well-typed
   terms are contained within the domain of their typing environments. *)
Lemma fv_in_dom : forall G e T,
    typing G e T -> fv_exp e [<=] dom G.
Proof.
  intros G e T H.
  induction H; simpl.
  - Case "typing_var".
    apply binds_In in H0.
    unfold AtomSetImpl.Subset.
    intros y Iny.
    assert (y = x). fsetdec. subst.
    auto.
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ((x ~ T1) ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
  - fsetdec.
Qed.

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
    destruct Ih1 as [v1 [EV1 [Tv1 vv1]]]; try solve [intro h; inversion h]; inversion EV1.

    (* By canonical forms, know that v1 must be an abstraction. *)
    destruct v1; simpl in vv1; try contradiction; clear vv1. subst e.

    destruct (n_bigstep n e2); try contradiction;
    destruct Ih2 as [v2 [EV2 [Tv2 vv2]]]; try solve [intro h; inversion h]; inversion EV2. subst.

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
(* Interpreter based big-step semantics *)

Fixpoint rt_bigstep (n:nat) (e:exp) (rho: rt_env) : res rt_val :=
  match n with
  | 0 => @timeout rt_val
  | S m =>
    match e with
    | var_b n => @stuck rt_val
    | var_f x => match (binds_lookup _ x rho) with
                | inl (exist _ y _) => val _ y
                | inr _             => @stuck rt_val
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


Lemma rt_bigstep_eval : forall n e T,
  typing nil e T ->
  @timeout exp <> n_bigstep n e ->
  exists v, val _ v = n_bigstep n e /\ typing nil v T /\ is_value_of_exp v.

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

Lemma rt_type_soundness : forall n G e T rho v,
  typing G e T ->
  typing_rt_env G rho ->
  val v = rt_bigstep n e rho ->
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
    rt_bigstep n e rho = val v ->
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
  eapply lc_exp.

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
    val v = rt_bigstep n e rho ->
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
      -- inversion H1.
      -- inversion H1.
    + inversion H1.
    + inversion H1.
Qed.

(* Connection between environment & subst based values: unload and envsubst *)

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

Fixpoint fv_n (e : n_exp) : vars :=
  match e with
  | n_var x => {{ x }}
  | n_abs x T e => AtomSetImpl.remove x (fv_n e)
  | n_app e1 e2 => fv_n e1 \u fv_n e2
  end.


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
          z `notin` fv_n e1' ->
          z `notin` fv_n e1  ->  (* perhaps unnecessary *)
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
Lemma named_fv : forall e en, named e en -> fv_exp e [=] fv_n en.
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
