From Stdlib Require Import String.
From Stdlib Require Export NArith Arith.
Require Import Lab07Map.

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
| Var : string -> expr
| Binop : BinopName -> expr -> expr -> expr.

Inductive stmt :=
    | varDeclStmt: string -> expr -> stmt 
    | ifStmt: expr -> stmt -> stmt -> stmt
    (* | forStmt *)
    | whileStmt: expr -> stmt -> stmt
    (*TODO | matchStmt *)
    (* | flowStmt *)
    | assignmentStmt: string -> expr -> stmt
    (* | exprStmt *)
    (* | assertStmt *)
    | awaitStmt: string -> stmt
    (* | preloadStmt *)
    (* | "breakpoint" stmtEnd *)
    (* | "pass" stmtEnd *)
    | sequence: stmt -> stmt -> stmt
    | assignCallMethodStmt: string -> string -> list expr -> stmt
    | emitSignalStmt: string -> option stmt -> list expr -> stmt
    | skip: stmt
.

Inductive topLevelDecl :=
    | classVarDecl: string -> expr -> topLevelDecl
    (* | constDecl: string -> expr -> topLevelDecl *)
    | signalDecl: string -> list string -> topLevelDecl
    (* | enumDecl *)
    | methodDecl: string -> list string -> string -> stmt -> topLevelDecl
    | readyDecl: stmt -> topLevelDecl
    | processDecl: stmt -> topLevelDecl 
    (* | constructorDecl *)
    (* | innerClass *)
    (* | "tool" *)
    | SequenceDecl: topLevelDecl -> topLevelDecl -> topLevelDecl
    | EndDecl: topLevelDecl
.

Inductive assignment:=
 | varAss (n: nat)
 | methodAss (args: list string) (ret: string) (body: stmt)
 | signAss (args: list string)
.

Definition valuation := fmap string assignment.

Notation "'topVar' x = e":= (classVarDecl x e) (at level 75).
(* Notation "'const' x = e" := (constDecl x e)(at level 75). *)
Notation "'ready():' b" := (readyDecl b)(at level 75). 
Notation "'process():' b" := (processDecl b)(at level 75).

Notation "'var' x = e":= (varDeclStmt x e) (at level 75).
Notation "'when' e 'then' then_ 'else' else_ 'done'" := (ifStmt e then_ else_)(at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" := (whileStmt e body)(at level 75).
Notation "x <- e" := (assignmentStmt x e) (at level 75).
Notation "'await' x" := (awaitStmt x)(at level 75).

Infix ";;" := sequence (at level 76).
Infix ";;;" := SequenceDecl (at level 76).

Infix "&" := (Binop LogAnd) (at level 80) : expr.
Infix "==" := (Binop Eq) (at level 70) : expr.
Infix ">>" := (Binop ShiftRight) (at level 60) : expr.
Infix "<<" := (Binop ShiftLeft) (at level 60) : expr.
Infix "+" := (Binop Plus) (at level 50, left associativity) : expr.
Infix "-" := (Binop Minus) (at level 50, left associativity) : expr.
Infix "*" := (Binop Times) (at level 40, left associativity) : expr.
Infix "/" := (Binop Divide) (at level 40, left associativity) : expr.
Infix "mod" := (Binop Modulo) (at level 40) : expr.

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

  Fixpoint interp (e: expr) (v: valuation) {struct e}: nat :=
  match e with
  | Const n => n
  | Var x => match v $? x with Some a =>
        match a with
        | varAss n => n
        | methodAss args ret body => 0
        | signAss args => 0
        end
   | None => 0 end
  | Binop b e1 e2 => interp_binop b (interp e1 v) (interp e2 v)
  end.

Fixpoint runStmt (fuel: nat) (v1: valuation) (st: stmt) (v2: valuation): Prop :=
     match fuel with
    | O => False
    | S fuel' => 
        match st with
        | varDeclStmt s e => exists n, n = interp e v1  /\ v2 = (v1 $+ (s, varAss n))
        | ifStmt e s1 s2 => (exists r, r = interp e v1 /\ r <> 0 /\ runStmt fuel' v1 s1 v2) \/
            (0 = interp e v1 /\ runStmt fuel' v1 s2 v2)
        | whileStmt e s => (exists r vmid, r = interp e v1 /\ r <> 0 /\ runStmt fuel' v1 s vmid 
            /\ runStmt fuel' vmid st v2) \/ (0 = interp e v1 /\ v1 = v2)
        | assignmentStmt s e => exists n, n = interp e v1 /\ v2 = (v1 $+ (s, varAss n))
            /\ v1 $? s <> None
        | awaitStmt s => False
        | sequence s1 s2 => exists vmid, runStmt fuel' v1 s1 vmid /\ runStmt fuel' vmid s2 v2
        | assignCallMethodStmt s ret args => False
        | emitSignalStmt s opt_callback args => False
        | skip => v1 = v2
        end
    end.


Fixpoint run (fuel: nat) (v1: valuation) (d: topLevelDecl) (v2: valuation): Prop:=
    match fuel with
    | O => False
    | S fuel' =>
        match d with
        | classVarDecl s e => exists n, n = interp e v1  /\ v2 = (v1 $+ (s, varAss n))
        | signalDecl s l => v2 = (v1 $+  (s, signAss l))
        | methodDecl s l ret st => v2 = (v1 $+ (s, methodAss l ret st))
        | readyDecl st => stmt -> exists v', runStmt fuel' v1 st v' /\ v' = v2
        | processDecl st => stmt ->  exists v', runStmt fuel' v1 st v'  /\ run fuel' v' d v2   
        | SequenceDecl d1 d2 => exists vmid, run fuel' v1 d1 vmid /\ run fuel' vmid d2 v2 
        | EndDecl => v1 = v2
        end 
    end.