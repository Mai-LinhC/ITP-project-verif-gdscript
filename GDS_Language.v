From Stdlib Require Import String.
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
    | callMethodStmt: string -> string -> list expr -> stmt
    | emitSignalStmt: string -> option stmt -> list expr -> stmt
    | done: stmt
.

Inductive topLevelDecl :=
    | classVarDecl: string -> expr -> topLevelDecl
    | constDecl: string -> expr -> topLevelDecl
    | signalDecl: string -> list string -> topLevelDecl
    (* | enumDecl *)
    | methodDecl: string -> list string -> stmt -> topLevelDecl
    | readyDecl: stmt -> topLevelDecl
    | processDecl: stmt -> topLevelDecl 
    (* | constructorDecl *)
    (* | innerClass *)
    (* | "tool" *)
    | SequenceDecl: topLevelDecl -> topLevelDecl -> topLevelDecl
    | EndDecl: topLevelDecl
.

Inductive assignement:=
 | varAss (n: nat)
 | methodAss (args: list string) (body: stmt)
.

Definition valuation := fmap string assignement.

Notation "'topVar' x = e":= (classVarDecl x e) (at level 75).
Notation "'const' x = e" := (constDecl x e)(at level 75).
Notation "'ready():' b" := (readyDecl b)(at level 75). 
Notation "'process():' b" := (processDecl b)(at level 75).

Notation "'var' x = e":= (varDeclStmt x e) (at level 75).
Notation "'when' e 'then' then_ 'else' else_ 'done'" := (ifStmt e then_ else_)(at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" := (whileStmt e body)(at level 75).
Notation "x <- e" := (assignmentStmt x e) (at level 75).
Notation "'await' x" := (awaitStmt x)(at level 75).

Infix ";;" := sequence (at level 76).
Infix ";;;" := SequenceDecl (at level 76).

