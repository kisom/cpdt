(*begin hide*)
Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.
(*end hide*)

(** * Inductive Predicates

Curry-Howard correspondence states formal connection between
functional programs and mathematical proofs. The definitions of [True]
and [unit] help clarify:*)

Print unit.
(**
[[
Inductive unit : Set :=  tt : unit
]]
*)

Print True.
(**
[[
Inductive True : Prop :=  I : True
]]

Specifically, one is a type with a single value, and the other is a
proposition that always holds; the same induction principle can be
used for both. Substituting names gives the same definition, but the
type is the distinguisher: [T] of type [Set] is a type of programs,
while [T] of type [Prop] is a logical proposition. Understanding why
the distinction is made helps to avoid conflating programming and
proving.

Engineering-wise, not all functions of type [A->B] are equally
constructed, but all proofs of the proposition [P->Q] are (_proof
irrelevance_). We program by applying functional programming
techniques to dependent types, and prove by writing custom decision
procedures.

** Propositional Logic*)

Section Propositional.
  Variables P Q R : Prop.

(** The most basic propositional construct is [->], implies. It's built into
Coq as the function type constructor.

The trivial proof of [True]:*)

  Theorem obvious: True.
  Proof.
    apply I.
  Qed.

(** [apply] is a tactic allowing us to use a particular constructor of
the inductive predicate being established. A shortcut:*)

  Theorem obvious': True.
  Proof.
    constructor.
  Qed.

(** The predicate [False] is the Curry-Howard mirror of [Empty_set]: *)

  Print False.

(**
[[
Inductive False : Prop :=  
]]

Doing case analysis on a proof of [False] has no cases:*)

  Theorem False_imp: False -> 2 + 2 = 5.
  Proof. destruct 1. Qed.

(** No proof of [False] can be constructed in a consistent contex.*)

  Theorem arith_neq: 2 + 2 = 5 -> 9 + 9 = 835.
  Proof. intro. elimtype False. crush. Qed.

(** Related is logical negation:*)

  Print not.
(**
[[
not = fun A : Prop => A -> False
     : Prop -> Prop

Argument scope is [type_scope]
]]

The syntax [~P] expands to [not P].
*)

  Theorem arith_neq': ~(2 + 2 = 5).
  Proof. unfold not. crush. Qed.

(** Conjunction:*)

  Print and.
(**
[[
Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B

For conj: Arguments A, B are implicit
For and: Argument scopes are [type_scope type_scope]
For conj: Argument scopes are [type_scope type_scope _ _]
]]

[and] has a Curry-Howard equivalent [prod].

We can reason about conjunction with tactics; for example, through an
explicit proof of commutivity: *)

  Theorem and_comm: P /\ Q -> Q /\ P.
  Proof.
    destruct 1. split.
    assumption. assumption. (* for each case, conclusion is among hypotheses. *)
  Qed.

(** Disjunction occurs via [or]:*)

  Print or.

(**
[[
Inductive or (A B : Prop) : Prop :=
    or_introl : A -> A \/ B | or_intror : B -> A \/ B

For or_introl, when applied to less than 1 argument:
  Arguments A, B are implicit
For or_introl, when applied to 2 arguments:
  Argument A is implicit
For or_intror, when applied to less than 1 argument:
  Arguments A, B are implicit
For or_intror, when applied to 2 arguments:
  Argument B is implicit
For or: Argument scopes are [type_scope type_scope]
For or_introl: Argument scopes are [type_scope type_scope _]
For or_intror: Argument scopes are [type_scope type_scope _]
]]

There are two ways to prove a disunction: prove the first disjunct or prove the second. (The Curry-Howard analogue is the [sum] type.)
*)

  Theorem or_comm: P \/ Q -> Q \/ P.
  Proof.
    destruct 1.
    right; assumption. (*Prove disjunction by proving the right disjunct.*)
    left; assumption.
  Qed.

(** The [tauto] tactic is a complete decision procedure for
constructive propositional logic. [intuition] is a generalisation of
[tauto] proving everything it can through propositional
reasoning. Consider:*)

  Theorem arith_comm: forall ls1 ls2 : list nat,
          length ls1 = length ls2 \/ length ls1 + length ls2 = 6 ->
          length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
  Proof.
    intuition.
    rewrite app_length.
    tauto.
  Qed.

(** Each of these theorems becomes universally quantified over the
propositional variables.*)

End Propositional.