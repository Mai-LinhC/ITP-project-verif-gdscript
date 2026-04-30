(** * CS-428: Interactive Theorem Proving, Spring 2026 - Lab 7 *)

(** This lab revisits lab 6 using small-step semantics. The language is
    simplified: no function calls ([AssignCall]) and no environment ([phi])
    parameter. *)

From Stdlib Require Export Arith NArith.
From Stdlib Require Export Program.Equality.
Require Import Lab07Map.
From Stdlib Require Export String.

Arguments N.add : simpl nomatch.
Arguments N.sub : simpl nomatch.
Arguments N.mul : simpl nomatch.
Arguments N.div : simpl nomatch.
Arguments N.shiftl : simpl nomatch.
Arguments N.shiftr : simpl nomatch.

Declare Scope var_scope.

Notation var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.
Infix "==v" := var_eq (no associativity, at level 50).
Infix "==n" := Nat.eq_dec (no associativity, at level 50).
String Notation var string_of_list_byte list_byte_of_string: var_scope.

Open Scope var_scope.

(** ** Language definition *)

(** We define a simple imperative language with binary operators.
    Unlike lab 6, there are no function calls. *)

Inductive BinopName :=
| LogAnd
| Eq
| ShiftLeft
| ShiftRight
| Times
| Divide
| Plus
| Minus
| Modulo.

Inductive expr :=
| Const : nat -> expr
| Var : var -> expr
| Binop : BinopName -> expr -> expr -> expr.

Inductive cmd :=
| Skip : cmd
| Assign : var -> expr -> cmd
| Sequence : cmd -> cmd -> cmd
| If : expr -> cmd -> cmd -> cmd
| While : expr -> cmd -> cmd
| Assert : expr -> cmd.

Declare Scope expr.
Delimit Scope expr with expr.

Coercion Const : nat >-> expr.
Coercion Var : var >-> expr.

(** The coercions defined in the previous section make programs easier to write by
    allowing to write [x] for [Var x] and [n] for [Const n], but they can be
    confusing when reading programs or proving properties, so the following line
    turns them off: *)

Set Printing Coercions.

Infix "&" := (Binop LogAnd) (at level 80) : expr.
Infix "==" := (Binop Eq) (at level 70) : expr.
Infix ">>" := (Binop ShiftRight) (at level 60) : expr.
Infix "<<" := (Binop ShiftLeft) (at level 60) : expr.
Infix "+" := (Binop Plus) (at level 50, left associativity) : expr.
Infix "-" := (Binop Minus) (at level 50, left associativity) : expr.
Infix "*" := (Binop Times) (at level 40, left associativity) : expr.
Infix "/" := (Binop Divide) (at level 40, left associativity) : expr.
Infix "mod" := (Binop Modulo) (at level 40) : expr.

Notation "x <- e" :=
  (Assign x e%expr)
    (at level 75).
Infix ";;" :=
  Sequence (at level 76).
Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
  (If e%expr then_ else_)
    (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" :=
  (While e%expr body)
    (at level 75).

Example Times3Plus1Body :=
  ("n" <- "n" * 3 + 1).

Example FactBody :=
  ("f" <- 1;;
    while "n" loop
      "f" <- "f" * "n";;
      "n" <- "n" - 1
    done).

(** ** Semantics *)

(** Our first step is to give a meaning to the language constructs.
    Let's start with an interpreter for binary operators and expressions. *)
Definition interp_binop (b: BinopName) (n1 n2: nat) :=
  match b with
  | LogAnd => Nat.land n1 n2
  | Eq => if n1 =? n2 then 1 else 0
  | Plus => n1 + n2
  | Minus => n1 - n2
  | Times => n1 * n2
  | Divide => n1 / n2
  | ShiftLeft => Nat.shiftl n1 n2
  | ShiftRight => Nat.shiftr n1 n2
  | Modulo => Nat.modulo n1 n2
  end.

(** For expressions, we'll use an interpreter to implement the following rules:

                 n1 = n2
              ------------
               ⟦n2⟧ᵥ = n1

       (x ↦ a) ∈ v         x ∉ v
      --------------     ----------
         ⟦x⟧ᵥ = a         ⟦x⟧ᵥ = 0

               ⟦e1⟧ᵥ = a1
               ⟦e2⟧ᵥ = a2
         a = interp_binop b a1 a2
      -----------------------------
          ⟦Binop b e1 e2⟧ᵥ = a
*)
Definition valuation := fmap var nat.

Fixpoint interp_arith (e: expr) (v: valuation) {struct e}: nat :=
  match e with
  | Const n => n
  | Var x => match v $? x with Some a => a | None => 0 end
  | Binop b e1 e2 => interp_binop b (interp_arith e1 v) (interp_arith e2 v)
  end.

Arguments interp_binop _ !_ !_ /.
Arguments Nat.shiftl : simpl nomatch.
Arguments Nat.shiftr : simpl nomatch.
Arguments Nat.land : simpl nomatch.
Arguments Nat.lor : simpl nomatch.
Arguments interp_arith !_ _ /.

(** *** Big-step semantics *)

(** We define big-step semantics, which we'll prove to be equivalent to the
    small-step semantics.  Note that there are no [phi] parameter and no
    [EvalAssignCall], since there are no function calls. *)

Inductive eval : valuation -> cmd -> valuation -> Prop :=
| EvalSkip : forall v,
    eval v Skip v
| EvalAssign : forall v x e,
    eval v (Assign x e) (v $+ (x, interp_arith e v))
| EvalSequence : forall v c1 v1 c2 v2,
    eval v c1 v1 ->
    eval v1 c2 v2 ->
    eval v (Sequence c1 c2) v2
| EvalIfTrue : forall v e c1 c2 v',
    interp_arith e v <> 0 ->
    eval v c1 v' ->
    eval v (If e c1 c2) v'
| EvalIfFalse : forall v e c1 c2 v',
    interp_arith e v = 0 ->
    eval v c2 v' ->
    eval v (If e c1 c2) v'
| EvalWhileTrue : forall v e body v' v'',
    interp_arith e v <> 0 ->
    eval v body v' ->
    eval v' (While e body) v'' ->
    eval v (While e body) v''
| EvalWhileFalse : forall v e body,
    interp_arith e v = 0 ->
    eval v (While e body) v
| EvalAssert : forall v e,
    interp_arith e v <> 0 ->
    eval v (Assert e) v.

(** *** Small-step semantics *)

(** We now define the small-step semantics for the language.  Each step reduces
    a (valuation, cmd) pair by one computation step. *)

Inductive step : valuation * cmd -> valuation * cmd -> Prop :=
| StepAssign : forall v x e,
    step (v, Assign x e) (v $+ (x, interp_arith e v), Skip)
| StepSeq1 : forall v c1 c2 v' c1',
    step (v, c1) (v', c1') ->
    step (v, Sequence c1 c2) (v', Sequence c1' c2)
| StepSeq2 : forall v c2,
    step (v, Sequence Skip c2) (v, c2)
| StepIfTrue : forall v e thn els,
    interp_arith e v <> 0 ->
    step (v, If e thn els) (v, thn)
| StepIfFalse : forall v e thn els,
    interp_arith e v = 0 ->
    step (v, If e thn els) (v, els)
| StepWhileTrue : forall v e body,
    interp_arith e v <> 0 ->
    step (v, While e body) (v, Sequence body (While e body))
| StepWhileFalse : forall v e body,
    interp_arith e v = 0 ->
    step (v, While e body) (v, Skip)
| StepAssertTrue : forall v e,
    interp_arith e v <> 0 ->
    step (v, Assert e) (v, Skip).

(** The multi-step relation, which we denote by [step*], is the transitive
    reflexive closure of [step]. *)

Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z,
    R x y ->
    trc R y z ->
    trc R x z.

Notation "'step*'" := (trc step).
