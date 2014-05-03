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

(** ** An Interlude on Induction Principles

Coq proofs are actually programs. Let's study some induction principle
definitions to gain additional insight:*)

Print nat_ind.

(**
[[
nat_ind = 
fun P : nat -> Prop => nat_rect P
     : forall P : nat -> Prop,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]
*)

(**
[P] has a type of [Type] (which is another universe, like [Prop] or
[Set]); it's actually a common supertype of both. Further exploring
this symmetry:
*)

Print nat_rec.

(**
[[
nat_rec = 
fun P : nat -> Set => nat_rect P
     : forall P : nat -> Set,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]

It's identical to [nat_ind], except instead of [Prop], it is based on
[Set]. We see that for most types [T], we get both the induction
principle [T_ind] and the recursion principle [T_rec]. [T_rec] can be
used to write recursive definitions without explicit [Fixpoint]
recursion. This means*)

Fixpoint plus_recursive (n : nat) : nat -> nat :=
  match n with
    | O => fun m => m
    | S n' => fun m => S (plus_recursive n' m)
  end.

(** is identical to*)

Definition plus_rec : nat -> nat -> nat :=
  nat_rec (fun _ : nat => nat->nat) (fun m => m)
          (fun _ r m => S (r m)).

(** Proof: *)

Theorem plus_equivalent: plus_recursive = plus_rec.
Proof. reflexivity. Qed.

(** This implies that [nat_rect] is not a primitive but a function
that may be manually written:*)

Print nat_rect.

(**
[[
nat_rect = 
fun (P : nat -> Type) (f : P O) (f0 : forall n : nat, P n -> P (S n)) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | O => f
  | S n0 => f0 n0 (F n0)
  end
     : forall P : nat -> Type,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]

[fix] is a Gallina keyword defining an anonymous recursive function,
and match uses a dependently-typed pattern match.

Type inference for dependent matching is undecideable (proven via
reduction from higher-order unification). Programs often need
dependence annotation to guide the type-checker. [as] binds a name for
the discriminee, while [return] defines a means to compute the match
result type as a function of the discriminee.

The definition of [nat_ind] might be better suited for helping us to
understand through the use of [Section].*)

Section nat_ind'.
  Variable P : nat -> Prop. (** The property we wish to prove.*)
  Hypothesis O_case : P O. (** A proof of the O case. [Hypothesis] is a synonym of [Variable] conventionally used for variables whose type is a [Prop].*)
  Hypothesis S_case: forall n : nat, P n -> P (S n).
  
  (** Tying the pieces together:*)

  Fixpoint nat_ind' (n : nat) : P n :=
    match n with
      | O => O_case
      | S n' => S_case (nat_ind' n')
    end.
End nat_ind'.

(** Observing the mutuall recursive definitions of even_list_mut,
etc... drives home the point that induction principle implementations,
while tedious, do not require much creativity.*)

(** ** Nested Inductive Types

Let's extend binary trees to arbitrarily-branching trees:*)

Inductive nat_tree : Set :=
  | NNode' : nat -> list nat_tree -> nat_tree.

(** This is a nested inductive type (the type being defined is used as
the argument to a parameterised type family). In this case, Coq
assumes [nat_tree] is being defined mutually with a specialised list
variant. This way, strict positivity is observed. However, the default
induction principle [nat_ind] is too weak:*)

Check nat_tree_ind.
(**
[[
nat_tree_ind
     : forall P : nat_tree -> Prop,
       (forall (n : nat) (l : list nat_tree), P (NNode' n l)) ->
       forall n : nat_tree, P n
]]

Scheme won't help us here in improving the principle; we'll need to
apply some creativity in implementing a suitable principle.

We start with a general predicate for capturing the notion that
property holds for all elements in a list; this is present in the
standard library as [Forall], but for the purpose of education, an
alternate version is implemented here as [All].*)

Section All.
  Variable T : Set.
  Variable P : T -> Prop.
  
  Fixpoint All (ls : list T) : Prop :=
    match ls with
      | nil => True
      | cons h t => P h /\ All t
    end.
End All.

(** Let's review [True] and [/\]:*)

Print True.
(**
[[
Inductive True : Prop :=  I : True
]]

[True] is a proposition with one prof, [I].

We'll have to use Locate to find [/\], which is defined as an
arbitrary parsing rule.*)

Locate "/\".
(**
[[
Notation            Scope     
"A /\ B" := and A B  : type_scope
                      (default interpretation)
]]
*)

Print and.

(**
[[
Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B

For conj: Arguments A, B are implicit
For and: Argument scopes are [type_scope type_scope]
For conj: Argument scopes are [type_scope type_scope _ _]
]]

We build a proof of a conjunction by calling conj on proofs o its
arguments (without the need to supply types explicitly.)*)

Section nat_tree_ind'.
  Variable P : nat_tree -> Prop.
  Hypothesis NNode'_case: forall (n : nat) (ls : list nat_tree),
                            All P ls -> P (NNode' n ls).

(** A first pass at defining the recursive principle will fail:

[[
  Fixpoint nat_tree_ind' (tr : nat_tree): P tr :=
    match tr with
      | NNode' n ls => NNode'_case n ls (list_nat_tree_ind ls)
    end
    with list_nat_tree_ind (ls : list nat_tree) : All P ls :=
           match ls with
             | nil => I
             | cons tr rest => conj (nat_tree_ind' tr) (list_nat_tree_ind rest)
           end.
]]

This gives us the error

[[
Error:
Recursive definition of list_nat_tree_ind is ill-formed.
In environment
P : nat_tree -> Prop
NNode'_case : forall (n : nat) (ls : list nat_tree),
              All P ls -> P (NNode' n ls)
nat_tree_ind' : forall tr : nat_tree, P tr
list_nat_tree_ind : forall ls : list nat_tree, All P ls
ls : list nat_tree
tr : nat_tree
rest : list nat_tree
Recursive call to nat_tree_ind' has principal argument equal to 
"tr" instead of "rest".
Recursive definition is:
"fun ls : list nat_tree =>
 match ls as ls0 return (All P ls0) with
 | nil => I
 | cons tr rest => conj (nat_tree_ind' tr) (list_nat_tree_ind rest)
 end".
]]

It turns out that Coq applies incomplete termination checking
heuristics. Some rules are in order: first, just as mutually inductive
types require mutually recursive induction principles, nested types
require nested recursion:*)

  Fixpoint nat_tree_ind' (tr : nat_tree) : P tr :=
    match tr with
      | NNode' n ls => NNode'_case n ls
        ((fix list_nat_tree_ind (ls : list nat_tree) : All P ls :=
           match ls with
             | nil => I
             | cons tr' rest =>
               conj (nat_tree_ind' tr') (list_nat_tree_ind rest)
           end) ls)
    end.

(** The anonymous recursion provided by [fix] is nested in the definition.*)

End nat_tree_ind'.

(** Before testing the induction principle, we'll define some list
helpers:*)

Section map.
  Variable T T' : Set.
  Variable F : T -> T'.

  Fixpoint map (ls : list T) : list T' :=
    match ls with
      | nil => nil
      | cons h t => cons (F h) (map t)
    end.
End map.

Fixpoint sum (ls : list nat) : nat :=
  match ls with
    | nil => O
    | cons h t => plus h (sum t)
  end.

Fixpoint ntsize (tr : nat_tree) : nat :=
  match tr with
    | NNode' _ trs => S (sum (map ntsize trs))
  end.

Fixpoint ntsplice (tr1 tr2 : nat_tree) : nat_tree :=
  match tr1 with
    | NNode' n nil => NNode' n (cons tr2 nil)
    | NNode' n (cons tr trs)=> NNode' n (cons (ntsplice tr tr2) trs)
  end.

(** We can now prove an arbitrary theorem about tree size:*)

Lemma plus_S: forall n1 n2 : nat,
      plus n1 (S n2) = S (plus n1 n2).
Proof. induction n1; crush. Qed.

Theorem ntsize_ntsplice: forall tr1 tr2 : nat_tree,
        ntsize (ntsplice tr1 tr2) = plus (ntsize tr2) (ntsize tr1).
Proof.
  Hint Rewrite plus_S.
  induction tr1 using nat_tree_ind'; crush.

(** This results in one remaining subgoal: a case analysis will see us
through:*)

  destruct ls; crush.

(** However, there is a more effective means of automating the proof:*)
  Restart.
  Hint Extern 1 (ntsize (match ?LS with nil => _
                            | cons _ _ => _ end) = _) =>
                destruct LS; crush.
  induction tr1 using nat_tree_ind'; crush.
Qed.

(** The hint registers a conclusion expected in the proof. Unification
variables (prefixed with ?) refer to bound variables in a tactic. The
hint makes the proof more readable by explaining the process by which
variables are selected for case analysis.*)

(** ** Manual Proofs about Constructors

Stepping through some manual proofs will help understand how tactics
like discriminate and injection operate. Here is a proof that would be
suitable for discriminate:*)

Theorem true_neq_false: true <> false.
Proof.

(** First, one step of reduction:*)

  red.

(** This gives us
[[
1 subgoals, subgoal 1 (ID 1880)
  
  ============================
   true = false -> False
]]
*)

  intro H.

(**
[[
1 subgoals, subgoal 1 (ID 1881)
  
  H : true = false
  ============================
   False
]]
*)

  Definition toProp (b : bool) := if b then True else False.
  change (toProp false).


(**
[[
1 subgoals, subgoal 1 (ID 1885)
  
  H : true = false
  ============================
   toProp false
]]
*)

  rewrite <- H.
(**
[[
1 subgoals, subgoal 1 (ID 1886)
  
  H : true = false
  ============================
   toProp true
]]
*)

  simpl.

(**
[[
1 subgoals, subgoal 1 (ID 1887)
  
  H : true = false
  ============================
   True
]]
*)

  trivial.
Qed.

(** It is also worthwhile to step through the following (but that
won't be done here):*)

Theorem S_inj': forall n m : nat,
        S n = S m -> n = m.
Proof.
  intros n m H.
  change (pred (S n) = pred (S m)).
  rewrite H.
  reflexivity.
Qed.

(** [injection] can do this style of using type-specific functions.*)

Theorem S_inj'': forall n m : nat,
        S n = S m -> n = m.
Proof.
  intros n m H.
  injection H.
  crush.
Qed.

(** A few carefully chosen rules enable desired reasoning patterns,
minimising the complexity of proof checking.*)
