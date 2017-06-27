(*************************************************************************)
(*                                                                       *)
(* Lecture 2                                                             *)
(*                                                                       *)
(*************************************************************************)

Require Import Metalib.Metatheory.

(** Next, we import the definitions of the simply-typed lambda calculus. *)
Require Import Stlc.Definitions.

(** And some auxiliary lemmas about these definitions. *)
Require Import Stlc.Lemmas.

Require Import Stlc.Lec1.


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



(*************************************************************************)
(** Forall quantification in inductive predicates. *)
(*************************************************************************)

(* Note: Let's look more closely at lc_abs, lc_exp_ind and lc_abs_exists *)

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
