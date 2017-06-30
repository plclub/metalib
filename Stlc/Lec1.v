
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


(** First, we import a number of definitions from the Metatheory library (see
    Metatheory.v).  The following command makes those definitions available in
    the rest of this file.

    This command will only succeed if you have already run "make" in the
    toplevel directory to compile the Metatheory library and the tutorial
    files.

*)

Require Import Metalib.Metatheory.

(** Next, we import the definitions of the simply-typed lambda calculus. *)
Require Import Stlc.Definitions.


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
  induction e; simpl; intros; eauto.
  destruct (x == y); subst; eauto.
  rewrite IHe. auto.
  rewrite IHe1. rewrite IHe2. auto.
Qed.

(*************************************************************************)
(** * Free variables and variable sets *)
(*************************************************************************)

(** The function [fv] calculates the set of free variables in an expression.
    This function returns a value of type `atoms` --- a finite set of
    variable names.
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

(* Now prove the following properties of substitution and fv *)

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

Lemma fv_exp_subst_exp_upper :
forall e1 e2 x1,
  fv_exp (subst_exp e2 x1 e1) [<=] fv_exp e2 `union` remove x1 (fv_exp e1).
Proof.
  (* SOLUTION *)
  intros. induction e1; simpl in *.
  - fsetdec.
  - destruct (x == x1); simpl; fsetdec.
  - rewrite IHe1. fsetdec.
  - rewrite IHe1_1. rewrite IHe1_2.
    fsetdec.
Qed.

(*************************************************************************)
(** * Connection between small-step and bigstep semantics (Part I)       *)
(*************************************************************************)



(*
Lemma bigstep_lc1 : forall x y, bigstep x y -> lc_exp x.
Proof. induction 1; auto. Qed.
Lemma bigstep_lc2 : forall x y, bigstep x y -> lc_exp y.
Proof. induction 1; auto. Qed.
*)

Inductive multistep : exp -> exp -> Prop :=
| ms_refl : forall e, lc_exp e -> multistep e e
| ms_step : forall e1 e2 e3, step e1 e2 -> multistep e2 e3 -> multistep e1 e3.
Hint Constructors multistep.

(*
Lemma ms_trans : forall e2 e1 e3,
    multistep e1 e2 -> multistep e2 e3 -> multistep e1 e3.
Proof. induction 1; intros; eauto. Qed.

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
  apply step_beta;
  eauto using bigstep_lc1, bigstep_lc2.
  eapply ms_refl; eauto using bigstep_lc1.
  auto.
  eapply ms_refl; auto.
Qed.
*)
(*
Lemma smallstep_bigstep1 : forall e e', step e e' -> forall v, bigstep e v -> bigstep e' v.
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

Lemma smallstep_bigstep_aux : forall e e', step e e' -> forall v, bigstep e' v -> bigstep e v.
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
  - eapply smallstep_bigstep_aux; eauto.
Qed.
*)