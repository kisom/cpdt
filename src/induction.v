(** * Introducing Inductive Types

We do not distinguish between programs and mathematical types: many
mathematical formulae are most easily encoded as programs.

Curry-Howard correspondence relates programs and proofs; for example,
function types may be though of as implications -- they're
equivalent. Consider*)

(*begin hide*)
Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.
(*end hide*)

Check (fun x : nat => x).
(** This will output [:nat -> nat]*)

(** An alternative: *)
Check (fun x : True => True).
(** This will output [:True -> True]*)

(** These two programs represent identity functions. The second is a proof that True implies itself. Another example ([I] is the single proof of [True]):*)
Check I. (** :True *)

(** Proving another simple propositional theorem:*)
Check (fun _ : False => I).

(** This implication-as-function analogy shows that false implies itself.*)

Check (fun x : False => x). (** This outputs: [:False -> False].*)

(** A program which looks like a logical formula is a proof term --
any Gallina term of a logical type.

Note that [bool] is a type (as are [True] and [False]), while [true]
and [false] are not. Any term of [bool] _evaluates_ to [true] or
[false], while most propositions do not evaluate to [True] or [False].
*)

(** ** Enumeration

Inductive types generalise GADTs (generalised algebraic types). [unit]
is a singleton type:*)

Inductive unit : Set :=
  | tt.

Theorem unit_singleton: forall x : unit, x = tt.
Proof. induction x. reflexivity. Qed.

(** So, what _is_ the induction principle for unit?*)

Check unit_ind.

(**
[unit_ind: forall P : unit -> Prop, P tt -> forall u : unit, P u]
*)

(**An [Inductive] defining some type [T] also defines an induction
principle [I_ind]. Determining what is a proof and what is a program
is the distinction between [Prop] and [Set]: [Prop] is the type of
logical propositions, and the values of these types are proofs, while
[Set] is the type of types used in programs. The induction principle
above quantifies over a predicate [P] over [unit] values: a proof that
[P] holds for [tt] implies a proof that [P] holds for any value [u] of
type [unit]. Consider*)

Inductive Bool : Set := True | False.
Check Bool_ind.

(*begin hide*)
Reset Bool.
(*end hide*)

(**
[Bool_ind: forall P:Bool -> Prop, P True -> P False -> forall b:Bool, P b]
*)

(** The simplest inductive, the empty set, has no elements and
therefore implies anything:*)

Inductive Empty_set : Set := .
Theorem the_sky_is_falling: forall x : Empty_set, 2 + 2 = 5.
Proof. destruct 1. Qed.
Check Empty_set_ind.
(** [Empty_set_ind: forall (P : Empty_set -> Prop) (e : Empty_set), P e]*)

(** A lazy way of converting from [Empty_set] to [unit]:*)
Definition e2u (e : Empty_set) : unit := match e with end.

(** [Empty_set] is the Curry-Howard equivalent of [False].

A simpler definition of [negb]:*)

Definition negb (b : bool) : bool := if b then false else true.
Theorem negb_inverse: forall b : bool, negb (negb b) = b.
Proof.
  destruct b; reflexivity.
Qed.

Theorem negb_ineq: forall b : bool, negb b <> b.
Proof. destruct b; discriminate. Qed.

(** [discriminate] is a tactic that proves two values of an inductive
type are not equal if their constructors are different.*)

(** ** Simple Recursive Types

Natural numbers are the simplest useful example:*)

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

(** [O] is zero, and [S] is the successor function: 0 is [O], 1 is [S
O], 2 is [S (S O)].*)

Definition isZero (n : nat) : bool :=
  match n with
    | O => true
    | S _ => false
  end.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Fixpoint plus (n m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** We can prove some theorems about [plus] without induction:*)

Theorem O_plus_n: forall n : nat, plus O n = n.
Proof. intros. reflexivity. Qed.

(** However, reversing the arguments causes our previous approach to fail:*)

Theorem n_plus_O: forall n : nat,
        plus n O = n.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Check nat_ind.
(** [[
nat_ind
     : forall P : nat -> Prop,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]

As [nat] has a constructor with an argument, it is injective:
*)
Theorem S_inj: forall n m : nat, S n = S m -> n = m.
Proof. injection 1. trivial. Qed.

(** [injection], which refers to a premise by numbers, injects new
equalities between arguments of corresponding terms, reducing it (in
this case) to [n = m -> n = m]. The [congruence] tactic can prove this immediately: it generalises properties on numbers -- it is a _complete decision procedure for the theory of equality and uninterpreted programs_.

A list of natural numbers:
*)

Inductive nat_list : Set :=
  | NNil : nat_list
  | NCons : nat -> nat_list -> nat_list.

(** In general, any tree type may be implemented as an inductive:*)

Inductive nat_btree : Set :=
  | NLeaf : nat_btree
  | NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Fixpoint nsize (tr : nat_btree): nat :=
  match tr with
    | NLeaf => S O
    | NNode tr1 _ tr2 => plus (nsize tr1) (nsize tr2)
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
    | NLeaf => NNode tr2 O NLeaf
    | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc: forall n1 n2 n3 : nat,
        plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
Proof.
 induction n1; crush. 
Qed.

Theorem nsize_nsplice: forall tr1 tr2 : nat_btree,
        nsize (nsplice tr1 tr2) = plus (nsize tr2) (nsize tr1).
Proof.
 Hint Rewrite n_plus_O plus_assoc.
 intros.
 induction tr1; crush.
Qed.

(** ** Parameterised Types

Defining polymorphic inductive types.*)

Inductive list (T:Set) : Set :=
  | nil : list T
  | cons : T -> list T -> list T.

Fixpoint length T (ls : list T)  : nat :=
  match ls with
    | nil => O
    | cons _ ls' => S (length ls')
  end.

Fixpoint app T (ls1 ls2 : list T) : list T :=
  match ls1 with
    | nil => ls2
    | cons x ls1' => cons x (app ls1' ls2)
  end.

Theorem length_app: forall T (ls1 ls2 : list T),
        length (app ls1 ls2) =
        plus (length ls1) (length ls2).
Proof. induction ls1; crush. Qed.

(** An alternative notation for parameterised types:*)

(* begin hide *)
Reset list.
(* end hide *)

Section list.
  Variable T : Set.

  Inductive list : Set :=
    | nil : list
    | cons : T -> list -> list.

  Fixpoint length (ls : list) : nat :=
    match ls with
      | nil => O
      | cons _ ls' => S (length ls')
    end.

  Fixpoint app (ls1 ls2 : list) : list :=
    match ls1 with
      | nil => ls2
      | cons x ls1' => cons x (app ls1' ls2)
    end.

  Theorem length_app: forall ls1 ls2 : list,
          length (app ls1 ls2) =
          plus (length ls1) (length ls2).
  Proof. induction ls1; crush. Qed.
End list.

Implicit Arguments nil [T].

(** ** Mutually Inductive Types

Mutually inductive types are types that refer to each other.*)

Inductive even_list : Set :=
  | ENil : even_list
  | ECons : nat -> odd_list -> even_list
with odd_list : Set :=
  | OCons : nat -> even_list -> odd_list.

Fixpoint elength (el : even_list) : nat :=
  match el with
    | ENil => O
    | ECons _ ol => S (olength ol)
  end
  with olength (ol : odd_list) : nat :=
    match ol with
      | OCons _ el => S (elength el)
    end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
    | ENil => el2
    | ECons n ol => ECons n (oapp ol el2)
  end
  with oapp (ol : odd_list) (el : even_list) : odd_list :=
    match ol with
      | OCons n el' => OCons n (eapp el' el)
    end.

(** However, proving a theorem as before fails; with our current
techniques, it will degenerate into an infinite chain of
inductions. This can be understood by looking at [even_list_ind]:*)

Check even_list_ind.

(**
[[
even_list_ind
     : forall P : even_list -> Prop,
       P ENil ->
       (forall (n : nat) (o : odd_list), P (ECons n o)) ->
       forall e : even_list, P e
]]

No inductive hypothesis are included; we must ask for a mutual
principle via [Scheme]:*)

Scheme even_list_mut := Induction for even_list Sort Prop
with odd_list_mut := Induction for odd_list Sort Prop.

(** [Induction] implies standard induction, and [Sort Prop] that we really want induction schemes (not recursion schemes; these are the same according to Curry-Howard, apart from the [Prop/Set] distinction).*)

Check even_list_mut.
(**
[[
even_list_mut
     : forall (P : even_list -> Prop) (P0 : odd_list -> Prop),
       P ENil ->
       (forall (n : nat) (o : odd_list), P0 o -> P (ECons n o)) ->
       (forall (n : nat) (e : even_list), P e -> P0 (OCons n e)) ->
       forall e : even_list, P e
]]

The [induction] tactic will not apply it automatically; consider how
to solve one of our previous theorems without induction:*)

Theorem n_plus_O': forall n : nat, plus n O = n.
Proof.

  (** Replace the current goal with one new goal for each premise of
  the applies theorem.*)

  apply nat_ind.

  (** More verbosely: *)

  Undo.
  apply (nat_ind (fun n => plus n O = n)); crush.
Qed.

(** [induction] apparently only does some bookkeeping to ease
application of a theorem. genealising to the mutual example:*)

Theorem elength_app: forall el1 el2: even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).
Proof.
  apply (even_list_mut
         (fun el1:even_list => forall el2:even_list,
              elength (eapp el1 el2) = plus (elength el1) (elength el2))
         (fun ol:odd_list => forall el:even_list,
              olength (oapp ol el) = plus (olength ol) (elength el)));
  crush.
Qed.

(** We had to specify two predicates, one for each of the mutually
inductive types.*)

(** ** Reflexive Types

Inductive types that include a constructor with a function returning
the same type being defined as an argument, i.e. for variable
binders. We'll start with a simpler inductive:*)

Inductive pformula : Set :=
  | Truth : pformula
  | Falsehood : pformula
  | Conjunction : pformula -> pformula -> pformula.

(** Distinction should be made between the syntax [Truth] and its
semantics [true]. The semantics may be made explicit (through a
recursive function) using the infix operator [/\] (which desugars to
[and]); the family [and] implements conjunction, the [Prop]
Curry-Howard analgoue of the usual pair type from FP (the Coq type
[prod]).*)

Fixpoint pformulaDenote (f : pformula) : Prop :=
  match f with
    | Truth => True
    | Falsehood => False
    | Conjunction f1 f2 => pformulaDenote f1 /\ pformulaDenote f2
  end.

(** However, it would be easier to give constructors recursive
function as arguments, e.g. for first-order logic.*)

Inductive formula : Set :=
  | Eq : nat -> nat -> formula
  | And : formula -> formula -> formula
  | Forall : (nat -> formula) -> formula.

(** Formulas are equalities between naturals, conjunction, and
universal quantification over natural numbers. For example, the
encoding of [forall x: nat, x = x]:*)

Example forall_refl: formula := Forall (fun x => Eq x x).

(** It's easy to write recursive functions over reflexive types.*)

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
    | Eq n1 n2 => n1 = n2
    | And f1 f2 => formulaDenote f1 /\ formulaDenote f2
    | Forall f' => forall n : nat, formulaDenote (f' n)
  end.

Fixpoint swapper (f:formula) : formula :=
  match f with
    | Eq n1 n2 => Eq n2 n1
    | And f1 f2 => And (swapper f2) (swapper f1)
    | Forall f' => Forall (fun n => swapper (f' n))
  end.

(** Proving the previous transformation does not make true false:*)

Theorem swapper_preserves_truth: forall f,
        formulaDenote f -> formulaDenote (swapper f).
Proof. induction f; crush. Qed.

(** The proof's induction principle:*)

Check formula_ind.
(**
[[
formula_ind
     : forall P : formula -> Prop,
       (forall n n0 : nat, P (Eq n n0)) ->
       (forall f0 : formula,
        P f0 -> forall f1 : formula, P f1 -> P (And f0 f1)) ->
       (forall f1 : nat -> formula,
        (forall n : nat, P (f1 n)) -> P (Forall f1)) ->
       forall f2 : formula, P f2
]]

Note that we are allowed to assume the theorem holds for any
application of [f1], the argument function. [formula] is an example of
higher-order abstract syntax (HOAS). This function-based
representation technique is used for lambda calculii in Twelf and many
ML/Haskell applications.

We might try to represent this as:
[[
Inductive term : Set :=
  | App : term -> term -> term
  | Abs : (term -> term) -> term.
]]

However, the _strict positivity requirement_ for inductive definitions
demands the type being defined not appear on the left of an arrow in a
constructor argument. Consider the previous definition would allow the
following function:
[[
Definition uhoh (t:term) : term :=
  match t with
    | Abs f => f t
    | _ => t
  end.
]]

Simple analysis shows that this would be permitted to run forever,
which would destroy any confidence in the meaning of a proof: every
theorem could be proven with an infinite loop.*)


