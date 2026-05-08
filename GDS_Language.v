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

    (* return variable name, method name, valuation number, args *)
    | assignCallMethodStmt: string -> string -> nat -> list expr -> stmt

    (* signal name, callback function if needed (name * valuation_number), args of signal *)
    | emitSignalStmt: string -> option (string * nat) -> list expr -> stmt
    | skip: stmt
.

Inductive topLevelDecl :=
    | classVarDecl: string -> expr -> topLevelDecl
    (* | constDecl: string -> expr -> topLevelDecl *)
    (* | signalDecl: string -> list string -> topLevelDecl removed because useless*)
    (* | enumDecl *)
    
    (* method name, arguments, return name, body *)
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
 | waitAss (pn: nat) (body: stmt)
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
        | waitAss n st => 0
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
        | awaitStmt sig_name => v1 = v2
        | sequence s1 s2 => match s1 with
            (*If we want to await a signal, we check if it has been emitted yet or no. If yes, we continue as a normal Seq,
            else, we add a waiting assignment to the valuation with the body of the Seq, which will be checked when the signal is emitted*)
            | awaitStmt sig_name => (exists r, (interp (Var sig_name) v1) = r /\ r <> 0 /\ runStmt fuel' v1 s2 v2 ) \/ 
            ((interp (Var sig_name) v1 = 0) /\ v2 = (v1 $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2)))
            | _ => exists vmid, runStmt fuel' v1 s1 vmid /\ runStmt fuel' vmid s2 v2
            end
        | assignCallMethodStmt ret s n args => False (*TODO*)
        (*If callback is Some, assignCallMethodStmt in garbage return variable with args.
        If None, do nothing. In both cases, set the signal to true in valuation to show it has been emitted.
        Check if a function is waiting for the signal. If so, call it after the callback but before resuming execution*)
        | emitSignalStmt sig_name opt_callback args => exists vmid vmid', vmid = (v1 $+ (sig_name, varAss 1)) /\
            match opt_callback with
                | Some (f, n) => runStmt fuel' vmid (assignCallMethodStmt "garb" f n args) vmid'
                | None => vmid = vmid'
                end /\ match vmid' $? ("waiting_" ++ sig_name)%string with
                    | Some (waitAss _ b) => runStmt fuel' vmid' b v2
                    | _ => vmid' = v2
                    end
        | skip => v1 = v2
        end
    end.


Fixpoint run (fuel: nat) (v1: valuation) (d: topLevelDecl) (v2: valuation): Prop:=
    match fuel with
    | O => False
    | S fuel' =>
        match d with
        | classVarDecl s e => exists n, n = interp e v1  /\ v2 = (v1 $+ (s, varAss n))
        | methodDecl s l ret st => v2 = (v1 $+ (s, methodAss l ret st))
        | readyDecl st => (*stmt ->*) runStmt fuel' v1 st v2 (*TODO: voir cette histoire de stmt -> *)
        | processDecl st => (* stmt ->  *) exists v', runStmt fuel' v1 st v'  /\ run fuel' v' d v2   
        | SequenceDecl d1 d2 => exists vmid, run fuel' v1 d1 vmid /\ run fuel' vmid d2 v2 
        | EndDecl => v1 = v2
        end 
    end.


Fixpoint runStmtDual (fuel: nat) (v1: valuation * valuation) (st: stmt) (v2: valuation * valuation): Prop :=
     match fuel with
    | O => False
    | S fuel' => match interp (Var "current") (fst v1) with
        | 1 =>  match st with
            | varDeclStmt s e => exists n, n = interp e (fst v1)  /\ v2 = (((fst v1) $+ (s, varAss n)), snd v1)
            | ifStmt e s1 s2 => (exists r, r = interp e (fst v1) /\ r <> 0 /\ runStmtDual fuel' v1 s1 v2) \/
                (0 = interp e (fst v1) /\ runStmtDual fuel' v1 s2 v2)
            | whileStmt e s => (exists r vmid, r = interp e (fst v1) /\ r <> 0 /\ runStmtDual fuel' v1 s vmid 
                /\ runStmtDual fuel' vmid st v2) \/ (0 = interp e (fst v1) /\ v1 = v2)
            | assignmentStmt s e => exists n, n = interp e (fst v1) /\ v2 = ((fst v1) $+ (s, varAss n), snd v1)
                /\ (fst v1) $? s <> None
            | awaitStmt sig_name => v1 = v2
            | sequence s1 s2 => match s1 with
                | awaitStmt sig_name => (exists r, (interp (Var sig_name) (fst v1)) = r  /\ r <> 0 /\ runStmtDual fuel' v1 s2 v2 ) \/ 
                ((interp (Var sig_name) (fst v1) = 0) /\ v2 = (((fst v1) $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2)), ((snd v1) $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2))))
                | _ => exists vmid, runStmtDual fuel' v1 s1 vmid /\ runStmtDual fuel' vmid s2 v2
                end
            | assignCallMethodStmt ret s n args => False
            | emitSignalStmt sig_name opt_callback args => exists vmid vmid', vmid = (((fst v1) $+ (sig_name, varAss 1)), ((snd v1) $+ (sig_name, varAss 1))) /\
                match opt_callback with
                    | Some (f, n) => runStmtDual fuel' vmid (assignCallMethodStmt "garb" f n args) vmid'
                    | None => vmid = vmid'
                    end /\ match (fst vmid') $? ("waiting_" ++ sig_name)%string with
                        | Some (waitAss n b) => 
                        (*Set current to 2 if n = 2 else leave it like that, then runStmt of the body, and switch back current to 1*)
                            match n with
                                | 2 => exists vswitch vreturn, vswitch = (((fst vmid') $+ (("current")%string, varAss 2)), snd vmid') /\ runStmtDual fuel' vswitch b vreturn
                                /\ v2 = (((fst vreturn) $+ (("current")%string, varAss 1)), snd vreturn)
                                | _ => runStmtDual fuel' vmid' b v2
                                end
                        | _ => vmid' = v2
                        end
            | skip => v1 = v2
            end
        | 2 => match st with
            | varDeclStmt s e => exists n, n = interp e (snd v1)  /\ v2 = (fst v1, ((snd v1) $+ (s, varAss n)))
            | ifStmt e s1 s2 => (exists r, r = interp e (snd v1) /\ r <> 0 /\ runStmtDual fuel' v1 s1 v2) \/
                (0 = interp e (snd v1) /\ runStmtDual fuel' v1 s2 v2)
            | whileStmt e s => (exists r vmid, r = interp e (snd v1) /\ r <> 0 /\ runStmtDual fuel' v1 s vmid 
                /\ runStmtDual fuel' vmid st v2) \/ (0 = interp e (snd v1) /\ v1 = v2)
            | assignmentStmt s e => exists n, n = interp e (snd v1) /\ v2 = (fst v1, (snd v1) $+ (s, varAss n))
                /\ (snd v1) $? s <> None
            | awaitStmt sig_name => v1 = v2
            | sequence s1 s2 => match s1 with
                | awaitStmt sig_name => (exists r, (interp (Var sig_name) (fst v1)) = r  /\ r <> 0 /\ runStmtDual fuel' v1 s2 v2 ) \/ 
                ((interp (Var sig_name) (fst v1) = 0) /\ v2 = (((fst v1) $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2)), ((snd v1) $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2))))
                | _ => exists vmid, runStmtDual fuel' v1 s1 vmid /\ runStmtDual fuel' vmid s2 v2
                end
            | assignCallMethodStmt ret s n args => False (*The n is the program number of the program containing the fuction, refering to the index of the valuation to read to get the function*)
            | emitSignalStmt sig_name opt_callback args => exists vmid vmid', vmid = (((fst v1) $+ (sig_name, varAss 1)), ((snd v1) $+ (sig_name, varAss 1))) /\
                match opt_callback with
                    | Some (f, n) => runStmtDual fuel' vmid (assignCallMethodStmt "garb" f n args) vmid'
                    | None => vmid = vmid'
                    end /\ match (fst vmid') $? ("waiting_" ++ sig_name)%string with
                        | Some (waitAss n b) => 
                        (*Set current to 1 if n = 1 else leave it like that, then runStmt of the body, and switch back current to 2*)
                            match n with
                                | 1 => exists vswitch vreturn, vswitch = (((fst vmid') $+ (("current")%string, varAss 1)), snd vmid') /\ runStmtDual fuel' vswitch b vreturn
                                /\ v2 = (((fst vreturn) $+ (("current")%string, varAss 2)), snd vreturn)
                                | _ => runStmtDual fuel' vmid' b v2
                                end
                        | _ => vmid' = v2
                        end
            | skip => v1 = v2
            end
        | _ => False
        end
    end.

(*NOTE / TODO : A chaque fois on écrit les waiting et les emitted dans les deux valuations mais en pratique on lit toujours dans la 1
Aussi, on peut pas avoir 2 signaux du même nom dans deux programmes différents, mais ça y'a pas le choix sauf en mettant des nombres random*)

    (*On suppose que quand on runDual 2 programmes, on donne une valuation qui contient déjà une entrée pour "current", qui est 1 si on run A, et 2 si on run B*)
Fixpoint runDual (fuel: nat) (v1: valuation * valuation) (dA: topLevelDecl) (dB: topLevelDecl) (v2: valuation * valuation): Prop:=
    match fuel with
    | O => False
    | S fuel' =>
        (*Arbitrary choice to put current in fst and not snd*)
        match interp (Var "current") (fst v1) with
        | 1 => match dA with
            | classVarDecl s e => exists n, n = interp e (fst v1)  /\ v2 = (((fst v1) $+ (s, varAss n)), snd v1)
            | methodDecl s l ret st => v2 = (((fst v1) $+ (s, methodAss l ret st)), snd v1)
            | readyDecl st => runStmtDual fuel' v1 st v2
            | processDecl st1 => match dB with
                | processDecl st2 => exists vmid vmid', runStmtDual fuel' v1 st1 vmid /\ runStmtDual fuel' vmid st2 vmid' /\ runDual fuel' vmid' dA dB v2 (*runStmt process A puis B, puis run infini*)
                | EndDecl => run fuel' (fst v1) dA (fst v2) (*runStmt process A, puis run infini*)(*Quid de snd v2, si B await A dans son ready, il faut pouvoir l'appeler avec la bonne valuation*)
                | _ => exists vmid, vmid = (((fst v1) $+ (("current")%string, varAss 2)), snd v1) /\ runDual fuel' vmid dA dB v2
                end
            | SequenceDecl d1 d2 => exists vmid, runDual fuel' v1 d1 dB vmid /\ runDual fuel' vmid d2 dB v2
            | EndDecl => match dB with (*If B process : runStmt B + run B infini, else juste run B infini*)
                                        (*If B EndDecl, v1 = v2 pour finir l'execution*)
                | processDecl st2 => exists vmid vmid', vmid = (((fst v1) $+ (("current")%string, varAss 2)), snd v1) /\ runStmtDual fuel' vmid st2 vmid' /\ runDual fuel' vmid' dA dB v2
                | EndDecl => v1 = v2
                | _ => exists vmid, vmid = (((fst v1) $+ (("current")%string, varAss 2)), snd v1) /\ runDual fuel' vmid dA dB v2
                end 
        
            end 
        | 2 => match dB with
            | classVarDecl s e => exists n, n = interp e (snd v1)  /\ v2 = (fst v1, ((snd v1) $+ (s, varAss n)))
            | methodDecl s l ret st => v2 = (fst v1, ((snd v1) $+ (s, methodAss l ret st)))
            | readyDecl st => runStmtDual fuel' v1 st v2
            | processDecl st => exists vmid, vmid = (((fst v1) $+ (("current")%string, varAss 1)), snd v1) /\ runDual fuel' vmid dA dB v2
            | SequenceDecl d1 d2 => exists vmid, runDual fuel' v1 dA d1 vmid /\ runDual fuel' vmid dA d2 v2 
            | EndDecl => exists vmid, vmid = (((fst v1) $+ (("current")%string, varAss 1)), snd v1) /\ runDual fuel' vmid dA dB v2
            end 
        | _ => False
        end
    end.