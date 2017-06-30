Require Import Metalib.Metatheory.

(*************************************************************************)
(** * Syntax of STLC *)
(*************************************************************************)

(** We use a locally nameless representation for the simply-typed
    lambda calculus, where bound variables are represented as natural
    numbers (de Bruijn indices) and free variables are represented as
    [atom]s.

    The type [atom], defined in the MetatheoryAtom library, represents
    names.  Equality on names is decidable ([eq_atom_dec]), and it is
    possible to generate an atom fresh for any given finite set of
    atoms ([atom_fresh]).
*)

Inductive typ : Set :=  (*r types *)
 | typ_base : typ
 | typ_arrow (T1:typ) (T2:typ).

Inductive exp : Set :=  (*r expressions *)
 | var_b (_:nat)
 | var_f (x:var)
 | abs (T:typ) (e:exp)
 | app (e1:exp) (e2:exp).


(*************************************************************************)
(** * Substitution *)
(*************************************************************************)

(** Substitution replaces a free variable with a term.  The definition
    below is simple for two reasons:
      - Because bound variables are represented using indices, there
        is no need to worry about variable capture.
      - We assume that the term being substituted in is locally
        closed.  Thus, there is no need to shift indices when
        passing under a binder.
*)

(** The [Fixpoint] keyword defines a Coq function.  As all functions
    in Coq must be total.  The annotation [{struct e}] indicates the
    termination metric---all recursive calls in this definition are
    made to arguments that are structurally smaller than [e].

    Note also that subst uses the function [eq_var x z] for decidable var
    equality.  This operation is defined in the Metatheory library.
*)

(** substitutions *)
Fixpoint subst_exp (u:exp) (y:var) (e:exp) {struct e} : exp :=
  match e with
  | (var_b n) => var_b n
  | (var_f x) => (if eq_var x y then u else (var_f x))
  | (abs T e1) => abs T (subst_exp u y e1)
  | (app e1 e2) => app (subst_exp u y e1) (subst_exp u y e2)
end.

(*************************************************************************)
(** * Free variables *)
(*************************************************************************)

(** The function [fv], defined below, calculates the set of free
    variables in an expression.  Because we are using a locally
    nameless representation, where bound variables are represented as
    indices, any name we see is a free variable of a term.  In
    particular, this makes the [abs] case simple.
*)

(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (var_b nat) => {}
  | (var_f x) => {{x}}
  | (abs T e) => (fv_exp e)
  | (app e1 e2) => (fv_exp e1) \u (fv_exp e2)
end.

(** The type [atoms] represents a finite set of elements of type
    [atom].  The notation for infix union is defined in the Metatheory
    library.
*)



(*************************************************************************)
(** * Opening *)
(*************************************************************************)

(** Opening replaces an index with a term.  It corresponds to informal
    substitution for a bound variable, such as in the rule for beta reduction.
    Note that only "dangling" indices (those that do not refer to any
    abstraction) can be opened.  Opening has no effect for terms that are
    locally closed.

    Natural numbers are just an inductive datatype with two constructors: [O]
    (as in the letter 'oh', not 'zero') and [S], defined in
    Coq.Init.Datatypes.  Coq allows literal natural numbers to be written
    using standard decimal notation, e.g., 0, 1, 2, etc.
    The function [lt_eq_lt_dec] compares its two arguments for ordering.

    We do not assume that zero is the only unbound index in the term.
    Consequently, we must substract one when we encounter other unbound
    indices.

    However, we do assume that the argument [u] is locally closed.  This
    assumption simplifies the implementation since we do not need to shift
    indices in [u] when passing under a binder.

    There is no need to worry about variable capture because bound variables
    are indices.  *)

(** arities *)
(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (u:exp) (e:exp) {struct e}: exp :=
  match e with
  | (var_b n) =>
      match lt_eq_lt_dec n k with
        | inleft (left _) => var_b n
        | inleft (right _) => u
        | inright _ => var_b (n - 1)
      end
  | (var_f x) => var_f x
  | (abs T e) => abs T (open_exp_wrt_exp_rec (S k) u e)
  | (app e1 e2) => app (open_exp_wrt_exp_rec k u e1) (open_exp_wrt_exp_rec k u e2)
end.

Definition open_exp_wrt_exp e u := open_exp_wrt_exp_rec 0 u e.

(*************************************************************************)
(** * Local closure *)
(*************************************************************************)

(** Recall that [exp] admits terms that contain unbound indices.  We say that
    a term is locally closed when no indices appearing in it are unbound.  The
    proposition [lc_exp e] holds when an expression [e] is locally closed.

    The inductive definition below formalizes local closure such that the
    resulting induction principle serves as the structural induction principle
    over (locally closed) expressions.  In particular, unlike induction for
    type [exp], there are no cases for bound variables.  Thus, the induction
    principle corresponds more closely to informal practice than the one
    arising from the definition of pre-terms.  *)


Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_var_f : forall (x:var),
     (lc_exp (var_f x))
 | lc_abs : forall (T:typ) (e:exp),
      ( forall x , lc_exp  (open_exp_wrt_exp e (var_f x) )  )  ->
     (lc_exp (abs T e))
 | lc_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (app e1 e2)).


(*************************************************************************)
(** * Typing environments *)
(*************************************************************************)

(** We represent environments as association lists (lists of pairs of
    keys and values) whose keys are [atom]s.
*)

Definition ctx : Set := list ( atom * typ ).

(** For STLC, environments bind [atom]s to [typ]s.  We define an abbreviation
    [env] for the type of these environments.

    Lists are defined in Coq's standard library, with the constructors [nil]
    and [cons].  The list library includes the [::] notation for cons as well
    as standard list operations such as append, map, and fold. The infix
    operation "++" is list append.

    The Metatheory library extends this reasoning by instantiating the
    AssocList library to provide support for association lists whose keys are
    [atom]s.  Everything in this library is polymorphic over the type of
    objects bound in the environment.  Look in AssocList for additional
    details about the functions and predicates that we mention below.
 *)


(*************************************************************************)
(** * Typing relation *)
(*************************************************************************)

(** The definition of the typing relation is straightforward.  In
    order to ensure that the relation holds for only well-formed
    environments, we check in the [typing_var] case that the
    environment is [uniq].  The structure of typing derivations
    implicitly ensures that the relation holds only for locally closed
    expressions.  Finally, note the use of cofinite quantification in
    the [typing_abs] case.
*)


(** definitions *)

(* defns JTyping *)
Inductive typing : ctx -> exp -> typ -> Prop :=
 | typing_var : forall (G:ctx) (x:var) (T:typ),
     uniq G ->
     binds x T G  ->
     typing G (var_f x) T
 | typing_abs : forall (L:vars) (G:ctx) (T1:typ) (e:exp) (T2:typ),
     (forall x , x \notin L -> typing ((x ~ T1) ++ G) (open_exp_wrt_exp e (var_f x)) T2)  ->
     typing G (abs T1 e) (typ_arrow T1 T2)
 | typing_app : forall (G:ctx) (e1 e2:exp) (T2 T1:typ),
     typing G e1 (typ_arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (app e1 e2) T2 .


(*************************************************************************)
(** * Values and Small-step Evaluation *)
(*************************************************************************)

(** In order to state the preservation lemma, we need to define values and the
    small-step evaluation relation.  These relations are straightforward to
    define.

    Note the hypotheses which ensure that the relations hold only for locally
    closed terms.  *)

Definition is_value (e_5:exp) : Prop :=
  match e_5 with
  | (var_b n) => False
  | (var_f x) => True
  | (abs T e) => (True)
  | (app e1 e2) => False
end.


(* defns JStep *)
Inductive step : exp -> exp -> Prop :=    (* defn step *)
 | step_beta : forall (T1:typ) (e1 v:exp),
     is_value v ->
     lc_exp (abs T1 e1) ->
     lc_exp v ->
     step (app  ( (abs T1 e1) )  v)  (open_exp_wrt_exp  e1 v )
 | step_app1 : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (app e1 e2) (app e1' e2)
 | step_app2 : forall (e2 v e2':exp),
     is_value v ->
     lc_exp v ->
     step e2 e2' ->
     step (app v e2) (app v e2').

Hint Constructors typing step lc_exp.

(*************************************************************************)
(** * Big-step Evaluation *)
(*************************************************************************)

Inductive bigstep : exp -> exp -> Prop :=    (* defn bigstep *)
 | bs_app : forall (e1 v2:exp) (T1:typ) (e1' e2 v1:exp),
     is_value v1 ->
     bigstep e1 (abs T1 e1') ->
     bigstep e2 v1 ->
     bigstep  (open_exp_wrt_exp  e1' v1 )  v2 ->
     bigstep (app e1 e2) v2
| bs_val : forall (v:exp),
     is_value v ->
     lc_exp v ->
     bigstep v v.
Hint Constructors bigstep.

(*************************************************************)


Inductive eq : ctx -> exp -> exp -> typ -> Prop :=    (* defn eq *)
 | eq_refl : forall (G:ctx) (e:exp) (T:typ),
     typing G e T ->
     eq G e e T
 | eq_sym : forall (G:ctx) (e2 e1:exp) (T:typ),
     eq G e1 e2 T ->
     eq G e2 e1 T
 | eq_trans : forall (G:ctx) (e1 e3:exp) (T:typ) (e2:exp),
     eq G e1 e2 T ->
     eq G e2 e3 T ->
     eq G e1 e3 T
 | eq_beta : forall (G:ctx) (T1:typ) (e v:exp) (T2:typ),
     is_value v ->
     typing G (app  ( (abs T1 e) )  v) T2 ->
     eq G (app  ( (abs T1 e) )  v)  (open_exp_wrt_exp  e v )  T2
 | eq_abs_cong : forall (L:vars) (G:ctx) (T1:typ) (e1 e2:exp) (T2:typ),
      ( forall x , x \notin  L  -> eq  (( x ~ T1 )++ G )   ( open_exp_wrt_exp e1 (var_f x) )   ( open_exp_wrt_exp e2 (var_f x) )  T2 )  ->
     eq G (abs T1 e1) (abs T1 e2) (typ_arrow T1 T2)
 | eq_app_cong : forall (G:ctx) (e1 e1' e2 e2':exp) (T2 T1:typ),
     eq G e1 e1' (typ_arrow T1 T2) ->
     eq G e2 e2' T1 ->
     eq G (app e1 e1') (app e2 e2') T2.
Hint Constructors eq.

(*************************************************************)

Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 68).
Definition open e u := open_exp_wrt_exp_rec 0 u e.