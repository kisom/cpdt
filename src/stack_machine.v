(** * Chapter 2: Some Quick Examples

The chapter will explore a fully-certified compiler (more than one, actually)
to stack machines.*)

Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.

(** ** Arithmetic Expressions over Natural Numbers

Let's start with the syntax of the source language.*)

Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
  | Const : nat -> exp
  | Binop : binop -> exp -> exp -> exp.

(**
The type of arithemtic expressions:

- A constant is built form a number
- A binary operation is built from an operator

We can express what programs mean:
*)

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

(**
Coq is built around a calculus of inductive constructions (CIC),
itself an extension of the older calculus of constructions (COC). CIC
has properties like _strong normalisation_ (every program and proof
term terminates) and _relative consistency_. Gallina covers terms
between [:=] and the period; Ltac is the DSL of proofs; and commands
like [Inductive] are part of the Vernacular (queries/requests to the
Coq system).

Here we have a simple definition of the meaning of an expression:
*)

Fixpoint expDenote (e : exp) : nat :=
  match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

(** _Note_: [Eval] is a command expressing a reduction strategy.*)

Eval compute in expDenote (Const 42).
Eval compute in expDenote (Binop Plus (Const 2) (Const 2)).

(** ** Target Language
We need to be able to compile source programs onto simple stack machines:*)

Inductive instr : Set :=
  | iConst : nat -> instr
  | iBinop : binop -> instr.
Definition prog := list instr.
Definition stack := list nat.

(**
Instructions push constants onto the stack or pop two arguments, apply
a binary operator, and push result onto the stack. Programs are lists
of instructions, and stacks are lists of numbers.

We can denote optional stack instructions s.t. [None] denotes stack
underflow and [Some s'] when the result is a new stack [s'].*)

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
    | iConst n => Some (n :: s)
    | iBinop b => match s with
                    | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
                    | _ => None
                  end
    end.

(** Now, [progDenote] can be used to step through a whole program.*)

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
    | nil => Some s
    | i :: p' => match instrDenote i s with
                   | None => None
                   | Some s' => progDenote p' s'
                 end
  end.

(** ** Translation: Defining the Compiler *)

Fixpoint compile (e : exp) : prog :=
  match e with
    | Const n => iConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.
Eval simpl in compile (Binop Plus (Const 2) (Const 2)).
Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))).

(** ** Translation Correctness

We can prove the compiler is implemented correctly through
[Theorem]s. A first pass might look like 

[Theorem compiler_correct: forall e,
         progDenote (compile e) nil =
         Some (expDenote e :: nil).]

However, it turns out to be more effective to approach by
"strengthening the induction hypothesis": proving an auxilliary lemma
(via [Lemma], technically a synonym of [Theorem], but conventionally
used for less important theorems supporting some main theorem). *)

Lemma compile_correct': forall e p s,
  progDenote (compile e ++ p) s = progDenote p (expDenote e::s).

(** We _could_ prove this by: *)

Proof.
  induction e.
  intros.
  unfold compile.
  unfold expDenote.
  unfold progDenote at 1.
  simpl.
  fold progDenote.
  reflexivity.

  (** subgoal 2*)
  intros.
  unfold compile.
  fold compile.
  unfold expDenote.
  fold expDenote.

(**

At this point, we'll use the _associative law of list concatenation_,
available as [app_assoc_reverse]:

[Theorem app_assoc_reverse: forall (A : type) (l m n : list A),]

[        (l ++ m) ++ n = l ++ m ++ n.]

Returning to the proof:
*)

  rewrite app_assoc_reverse.
  rewrite IHe2.
  rewrite app_assoc_reverse.
  rewrite IHe1.
  unfold progDenote at 1.
  simpl.
  fold progDenote.
  reflexivity.

(** But this is long and tedious, so: *)

Abort.

Lemma compile_correct': forall e s p,
  progDenote (compile e ++ p) s =
  progDenote p (expDenote e :: s).
Proof.
  induction e;

  (** [t1 ; t2] runs t1, then t2 on each remaining subgoal. *)

  crush.

  (** [crush] is included with the CPDT library.*)

Qed.

(** Proof scripts (series of Ltac programs) are a foundation of
serious, complex proofs. [Qed] uses the result of the script to
generate a proof term; we need only trust that the proof-term checker
is correct -- rendering the use of proof scripts immaterial.

Now to prove the compiler:*)

Theorem compile_correct: forall e,
  progDenote (compile e) nil =
  Some (expDenote e :: nil).
Proof.
  intros.
  rewrite (app_nil_end (compile e)).
  rewrite compile_correct'.
  reflexivity.
Qed.

(** [app_nil_end] is a theorem defined as

[Theorem app_nil_end: forall (A : Type) (l : list A),]

[        l = l ++ nil.]

*)

(** ** Typed Expressions

We can strengthen our new language through the use of static typing.*)

Inductive type : Set := Nat | Bool.

(** This includes an expanded set of binary operators: *)

Inductive tbinop : type -> type -> type -> Set :=
  | TPlus : tbinop Nat Nat Nat
  | TTimes: tbinop Nat Nat Nat
  | TEq   : forall t, tbinop t t Bool
  | TLe   : tbinop Nat Nat Bool.

(** [tbinop] is an indexed type family: [tbinop t1 t2 t] is a binary
operator whose operands have typed [t1] and [t2], and whose result has
the type [t].*)

(** In Coq, types may be arbitrary Gallina terms.*)

(** Now we can define a typed expression family:*)

Inductive texp : type -> Set :=
  | TNConst : nat -> texp Nat
  | TBConst : bool -> texp Bool
  | TBinop  : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

(** Matching types of our language into Coq types.*)

Definition typeDenote (t : type): Set :=
  match t with
    | Bool => bool
    | Nat  => nat
  end.

(** Interpreting binary operators: *)

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
           :typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
    | TPlus    => plus
    | TTimes   => mult
    | TEq Nat  => beq_nat
    | TEq Bool => eqb
    | TLe      => leb
  end.

(** [tbinop] is an indexed type, and its indices become additional
arguments, meaning that a dependent pattern match (where types are
considered) is required. This is done similarly for the typed
expression definition:*)

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

(** ** Target Language

In addition to stack underflow, there is the additional complication
of stack slots with natural numbers in place of boolean values, and
vice-versa. Indexed type families allow us to avoid the need to reason
about these potential failures, as the type system can be used to
prevent these scenarios from occurring:*)

Definition tstack := list type.

(** Any typed stack _must_ have exactly as many elements of the
correct types:*)

Inductive tinstr : tstack -> tstack -> Set :=
  | TiNConst : forall s, nat  -> tinstr s (Nat :: s)
  | TiBConst : forall s, bool -> tinstr s (Bool :: s)
  | TiBinop  : forall arg1 arg2 res s,
               tbinop arg1 arg2 res
               -> tinstr (arg1 :: arg2 :: s) (res :: s).

(** Stack machine programs must be a similar inductive family:*)

Inductive tprog : tstack -> tstack -> Set :=
  | TNil  : forall s, tprog s s
  | TCons : forall s1 s2 s3,
            tinstr s1 s2
            -> tprog s2 s3
            -> tprog s1 s3.

(** We also need to define the semantics of a stack at runtime.*)

Fixpoint vstack (ts : tstack): Set :=
  match ts with
    | nil => unit
    | t :: ts' => typeDenote t * vstack ts'
  end%type.

(** The type annotation at the end causes the entire match to be
treated as a type, and therefore [*] to be interpreted as a Cartesian
product. This invocation of [type] has no relation to our
[Inductive].*)

Definition tinstrDenote ts ts' (i : tinstr ts ts')
           :vstack ts -> vstack ts' :=
  match i with
    | TiNConst _ n => fun s => (n, s)
    | TiBConst _ b => fun s => (b, s)
    | TiBinop _ _ _ _ b => fun s =>
        let '(arg1, (arg2, s')) := s in
            ((tbinopDenote b) arg1 arg2, s')
  end.

(** An anonymous function is used to bind the stack as a rsult of how
the Coq type checker works.

Program definition is straightforward.*)

Fixpoint tprogDenote ts ts' (p : tprog ts ts')
         :vstack ts -> vstack ts' :=
  match p with
    | TNil _ => fun s => s
    | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

(** It's useful to be able to concatenate two programs:*)

Fixpoint tconcat ts ts' ts'' (p : tprog ts ts')
         :tprog ts' ts'' -> tprog ts ts'' :=
  match p with
    | TNil _ => fun p' => p'
    | TCons _ _ _ i p1 => fun p' => TCons i (tconcat p1 p')
  end.

(** Compilation is done similarly:*)

Fixpoint tcompile t (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
    | TNConst n => TCons (TiNConst _ n) (TNil _)
    | TBConst b => TCons (TiBConst _ b) (TNil _)
    | TBinop _ _ _ b e1 e2 => tconcat (tcompile e2 _)
        (tconcat (tcompile e1 _) (TCons (TiBinop _ b) (TNil _)))
  end.

Eval simpl in tprogDenote
  (tcompile
    (TBinop (TEq Nat)
            (TBinop TPlus (TNConst 2) (TNConst 2))
            (TNConst 4))
    nil) tt. (** <<(* tt => unit *)>> *)

(** ** Translation Correctness.

Again, the core theorem will need to be strengthened; an alternative
approach will be taken to illustrate different tactics. The key
theorem is stated thus:*)

Theorem tcompile_correct: forall t (e : texp t),
        tprogDenote (tcompile e nil) tt =
        (texpDenote e, tt).
Abort.

(** First, it will be useful to prove a lemma regarding [tconcat].*)

Lemma tconcat_correct: forall ts ts' ts'' (p : tprog ts ts')
      (p' : tprog ts' ts'') (s : vstack ts),
      tprogDenote (tconcat p p') s =
      tprogDenote p' (tprogDenote p s).
Proof. induction p; crush. Qed.
Hint Rewrite tconcat_correct.

(** [Hint Rewrite tconcat_correct] is required to alert [crush] to
this proof's existence.*)

Lemma tcompile_correct': forall t (e : texp t) ts (s : vstack ts),
      tprogDenote (tcompile e ts) s =
      (texpDenote e, s).
Proof. induction e; crush. Qed.
Hint Rewrite tcompile_correct'.

(** Now we can prove our key theorem: *)

Theorem tcompile_correct: forall t (e : texp t),
        tprogDenote (tcompile e nil) tt =
        (texpDenote e, tt).
Proof. crush. Qed.

(** We could extract this, for example as OCaml source code, and be
presented with a certified compiler for our new language.*)

Extraction tcompile.

(**
<<
let rec tcompile t e ts =
  match e with
  | TNConst n ->
    TCons (ts, (Cons (Nat, ts)), (Cons (Nat, ts)), (TiNConst (ts, n)), (TNil
      (Cons (Nat, ts))))
  | TBConst b ->
    TCons (ts, (Cons (Bool, ts)), (Cons (Bool, ts)), (TiBConst (ts, b)),
      (TNil (Cons (Bool, ts))))
  | TBinop (t1, t2, t0, b, e1, e2) ->
    tconcat ts (Cons (t2, ts)) (Cons (t0, ts)) (tcompile t2 e2 ts)
      (tconcat (Cons (t2, ts)) (Cons (t1, (Cons (t2, ts)))) (Cons (t0, ts))
        (tcompile t1 e1 (Cons (t2, ts))) (TCons ((Cons (t1, (Cons (t2,
        ts)))), (Cons (t0, ts)), (Cons (t0, ts)), (TiBinop (t1, t2, t0, ts,
        b)), (TNil (Cons (t0, ts))))))
>>
*)