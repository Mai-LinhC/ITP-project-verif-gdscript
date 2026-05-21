From Stdlib Require Import String.
From Stdlib Require Export NArith Arith.
From Stdlib Require Import List.
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

    (* optional return variable name, method name, args *)
    | assignCallMethodStmt: option string -> string -> list expr -> stmt

    (* signal name, callback function if needed (name * valuation_number), args of signal *)
    | emitSignalStmt: string -> option (string * nat) -> list expr -> stmt
    | skip: stmt
.

Inductive topLevelDecl :=
    | classVarDecl: string -> expr -> topLevelDecl
    (* | constDecl: string -> expr -> topLevelDecl *)
    (* | signalDecl: string -> list string -> topLevelDecl removed because useless*)
    (* | enumDecl *)
    
    (* method name, arguments, optional return name, body *)
    | methodDecl: string -> list string -> option string -> stmt -> topLevelDecl
    | readyDecl: stmt -> topLevelDecl
    | processDecl: stmt -> topLevelDecl 
    (* | constructorDecl *)
    (* | innerClass *)
    (* | "tool" *)
    | SequenceDecl: topLevelDecl -> topLevelDecl -> topLevelDecl
    | EndDecl: topLevelDecl
.

Inductive assignment :=
 | varAss (n: nat)
 | methodAss (args: list string) (ret: option string) (body: stmt)
 | waitAss (pn: nat) (body: stmt)
.

Definition valuation := fmap string assignment.

Notation "'topVar' x := e":= (classVarDecl x e) (at level 75).
(* Notation "'const' x = e" := (constDecl x e)(at level 75). *)
Notation "'ready():' b" := (readyDecl b)(at level 75). 
Notation "'process():' b" := (processDecl b)(at level 75).

Notation "'var' x := e":= (varDeclStmt x e) (at level 75).
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

  Fixpoint interp (e: expr) (v: valuation) {struct e}: option nat :=
  match e with
  | Const n => Some n
  | Var x => match v $? x with Some a =>
        match a with
        | varAss n => Some n
        | methodAss args ret body => None
        | waitAss n st => None
        end
   | None => None end
  | Binop b e1 e2 => match (interp e1 v), (interp e2 v) with
    | Some n1, Some n2 => Some (interp_binop b n1 n2)
    | _, _ => None
    end
  end.

  Fixpoint interp2 (e: expr) (vg: valuation) (vl: valuation) {struct e}: option nat :=
    match e with
    | Const n => Some n
    | Var x => match vl $? x with 
    | Some a =>
        match a with
        | varAss n => Some n
        | methodAss args ret body => None
        | waitAss n st => None
        end
    | None => match vg $? x with 
        | Some a =>
            match a with
            | varAss n => Some n
            | methodAss args ret body => None
            | waitAss n st => None
            end
        | None => None
        end
    end
  | Binop b e1 e2 => match (interp2 e1 vg vl), (interp2 e2 vg vl) with
    | Some n1, Some n2 => Some (interp_binop b n1 n2)
    | _, _ => None
    end
  end.


Fixpoint runStmtP (fuel: nat) (vg1: valuation) (vl1: valuation) (st: stmt): option (valuation * valuation) :=
    match fuel with
    | O => None
    | S fuel' =>
        match st with
        | varDeclStmt name e => match interp2 e vg1 vl1 with
                                | Some n => Some (vg1, (vl1 $+ (name, varAss n)))
                                | None => None
                                end
        | ifStmt e s1 s2 => match interp2 e vg1 vl1 with
                            | Some 0 => runStmtP fuel' vg1 vl1 s2
                            | Some _n => runStmtP fuel' vg1 vl1 s1
                            | None => None
                            end
        | whileStmt e s => match interp2 e vg1 vl1 with
                            | Some 0 => Some (vg1, vl1)
                            | Some _n => match (runStmtP fuel' vg1 vl1 s) with
                                | Some (vgmid, vlmid) => runStmtP fuel' vgmid vlmid st
                                | None => None
                                end
                            | None => None
                            end
        | assignmentStmt name e => match vl1 $? name with
                                | Some _ => match interp2 e vg1 vl1 with
                                    | Some n => Some (vg1, (vl1 $+ (name, varAss n)))
                                    | None => None
                                    end
                                | None => match vg1 $? name with
                                    | Some _ => match interp2 e vg1 vl1 with
                                        | Some n => Some (vg1 $+ (name, varAss n), vl1)
                                        | None => None
                                        end
                                    | None => None
                                    end
                                end
        | awaitStmt sig_name => Some (vg1, vl1)
        | sequence s1 s2 => match s1 with
            | awaitStmt sig_name => match interp (Var sig_name) vg1 with
                | Some 0 | None => Some (vg1 $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2), vl1)
                | Some _n => runStmtP fuel' vg1 vl1 s2
                end
            | _ => match runStmtP fuel' vg1 vl1 s1 with
                | Some (vgmid, vlmid) => runStmtP fuel' vgmid vlmid s2
                | None => None
                end
            end
        | assignCallMethodStmt ret method_name args => match vg1 $? method_name with
            | Some (methodAss name_args found_ret found_body) => match 
                (runStmtP fuel' vg1 
                (fold_left 
                    (fun (acc: valuation) (arg_argname: expr * string) => 
                        match interp2 (fst arg_argname) vg1 vl1 with
                        | Some n => (acc $+ ((snd arg_argname), varAss n))
                        (*If we give an argument that isn't defined, it is not added to the valuation.
                        this might not be the correct behavior (would be better if the whole runStmt returned None. TODO: investigate)*)
                        | None => acc
                        end
                    ) 
                    (combine args name_args) ($0)) 
                found_body) with
                | Some (vgmid, vlmid) => match ret, found_ret with
                    | Some s_ret, Some s_found_ret => match interp (Var s_found_ret) vlmid with
                        | Some r => match runStmtP fuel' vgmid vl1 (assignmentStmt s_ret (Const r)) with
                            | Some (vg2, vl2) => Some (vg2, vl2)
                            | None => Some (vgmid, vl1 $+ (s_ret, varAss r))
                            end
                        | None => None 
                        end
                    | Some _, None => None
                    | None, _ => Some (vgmid, vl1)
                    end
                | None => None
                end
            | _ => None
            end
        | emitSignalStmt sig_name opt_callback args => let vgmid := (vg1 $+ (sig_name, varAss 1)) in match opt_callback with
            | Some (f, _n) => match runStmtP fuel' vgmid vl1 (assignCallMethodStmt None f args) with
                | Some (vgmid', vlmid') => match vgmid' $? ("waiting_" ++ sig_name)%string with
                    | Some (waitAss _ body) => runStmtP fuel' vgmid' vlmid' body
                    | _ => Some (vgmid', vlmid')
                    end
                | None => None
                end
            | None => match vgmid $? ("waiting_" ++ sig_name)%string with
                | Some (waitAss _ body) => runStmtP fuel' vgmid vl1 body
                | _ => Some (vgmid, vl1)
                end
            end
        | skip => Some (vg1, vl1)
        end
    end.

Fixpoint runP (fuel: nat) (v: valuation) (d: topLevelDecl) : option valuation :=
    match fuel with
    | O => None
    | S fuel' =>
        match d with
        | classVarDecl name e => match (interp e v) with
                                | Some n => Some (v $+ (name, varAss n))
                                | None => None
                                end
        | methodDecl name args ret body => Some (v $+ (name, methodAss args ret body))
        | readyDecl body => match (runStmtP fuel' v ($0) body) with
            | Some (vg2, vl2) => Some vg2
            | None => None
            end
        | processDecl body => match runStmtP fuel' v $0 body with
            | Some (vgmid, vlmid) => runP fuel' vgmid d
            | None => None
            end
        | SequenceDecl d1 d2 => match runP fuel' v d1 with
            | Some vmid => runP fuel' vmid d2
            | None => None
            end
        | EndDecl => Some v
        end
    end.
(* 
Fixpoint runStmt (fuel: nat) (vg1: valuation) (vl1: valuation) (st: stmt) (vg2: valuation) (vl2: valuation): Prop :=
    match fuel with
    | O => False
    | S fuel' => 
        match st with
        (* check what we're gonna write with interp2 and assign local var *)
        | varDeclStmt s e => exists n, n = interp2 e vg1 vl1  /\ vl2 = (vl1 $+ (s, varAss n)) /\ vg2 = vg1
        | ifStmt e s1 s2 => (exists r, r = interp2 e vg1 vl1 /\ r <> 0 /\ runStmt fuel' vg1 vl1 s1 vg2 vl2) \/
            (0 = interp2 e vg1 vl1 /\ runStmt fuel' vg1 vl1 s2 vg2 vl2)
        | whileStmt e s => (exists r vgmid vlmid, r = interp2 e vg1 vl1 /\ r <> 0 /\ runStmt fuel' vg1 vl1 s vgmid vlmid
            /\ runStmt fuel' vgmid vlmid st vg2 vl2) \/ (0 = interp2 e vg1 vl1 /\ vg1 = vg2 /\ vl1 = vl2)
        (*Check local val, if exists, reassign, else check global, if exists reassign, else crash (prop is false)*)
        | assignmentStmt s e => (vl1 $? s <> None /\ exists n, n = interp2 e vg1 vl1 /\ vl2 = (vl1 $+ (s, varAss n)) /\ vg1 = vg2) \/
            (vg1 $? s <> None /\ vl1 $? s = None /\ exists n, n = interp2 e vg1 vl1 /\ vg2 = (vg1 $+ (s, varAss n)) /\ vl1 = vl2)
        (*We check awaits in Seqs, so if we reach this case, it is either the only instruction in the program or the last one, either way it does nothing*)
        | awaitStmt sig_name => vg1 = vg2 /\ vl1 = vl2
        | sequence s1 s2 => match s1 with
            (*If we want to await a signal, we check if it has been emitted yet or no. If yes, we continue as a normal Seq,
            else, we add a waiting assignment to the valuation with the body of the Seq, which will be checked when the signal is emitted*)
            | awaitStmt sig_name => (exists r, (interp (Var sig_name) vg1) = r /\ r <> 0 /\ runStmt fuel' vg1 vl1 s2 vg2 vl2) \/ 
            ((interp (Var sig_name) vg1 = 0) /\ vg2 = (vg1 $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2)) /\ vl1 = vl2)
            | _ => exists vgmid vlmid, runStmt fuel' vg1 vl1 s1 vgmid vlmid /\ runStmt fuel' vgmid vlmid s2 vg2 vl2
            end
        | assignCallMethodStmt ret method_name args =>
            exists name_args found_ret found_body, vg1 $? method_name = 
            Some (methodAss name_args found_ret found_body) /\
                exists vlmid vgmid,
                runStmt fuel' vg1 
                (fold_left 
                    (fun (acc: valuation) (arg_argname: expr * string) => 
                        (acc $+ ((snd arg_argname), varAss (interp2 (fst arg_argname) vg1 vl1)))
                    ) 
                    (combine args name_args) ($0)) 
                found_body vgmid vlmid
                /\ match ret, found_ret with
                    | Some s_ret, Some s_found_ret => 
                        (exists r, interp (Var s_found_ret) vlmid = r 
                        /\ 
                        ((runStmt fuel' vgmid vl1 (assignmentStmt s_ret (Const r)) vg2 vl2) (* if already defined (locally or globally), reassign to new value r *)
                        \/
                        vl1 $? s_ret = None /\ vgmid $? s_ret = None /\ (vl2 = vl1 $+ (s_ret, varAss r) /\ vgmid = vg2 (* otw, new val *)
                        )))
                    | Some _, None => False
                    | None, _ => vl2 = vl1 /\ vg2 = vgmid
                    end
        (*If callback is Some, assignCallMethodStmt in garbage return variable with args.
        If None, do nothing. In both cases, set the signal to true in valuation to show it has been emitted.
        Check if a function is waiting for the signal. If so, call it after the callback but before resuming execution*)
        | emitSignalStmt sig_name opt_callback args => exists vgmid vgmid' vlmid', vgmid = (vg1 $+ (sig_name, varAss 1)) /\
            match opt_callback with
                | Some (f, n) => runStmt fuel' vgmid vl1 (assignCallMethodStmt None f args) vgmid' vlmid'
                | None => vgmid = vgmid' /\ vl1 = vlmid'
                end /\ match vgmid' $? ("waiting_" ++ sig_name)%string with
                    | Some (waitAss _ b) => runStmt fuel' vgmid' vlmid' b vg2 vl2
                    | _ => vgmid' = vg2 /\ vlmid' = vl2
                    end
        | skip => vg1 = vg2 /\ vl1 = vl2
        end
    end.


Fixpoint run (fuel: nat) (v1: valuation) (d: topLevelDecl) (v2: valuation): Prop:=
    match fuel with
    | O => False
    | S fuel' =>
        match d with
        | classVarDecl s e => exists n, n = interp e v1  /\ v2 = (v1 $+ (s, varAss n))
        | methodDecl s l ret st => v2 = (v1 $+ (s, methodAss l ret st))
        | readyDecl st => (*stmt ->*) exists vl2, runStmt fuel' v1 ($0) st v2 vl2 (*TODO: voir cette histoire de stmt -> *)
        | processDecl st => (* stmt ->  *) exists v' vl2, runStmt fuel' v1 $0 st v' vl2  /\ run fuel' v' d v2   
        | SequenceDecl d1 d2 => exists vmid, run fuel' v1 d1 vmid /\ run fuel' vmid d2 v2 
        | EndDecl => v1 = v2
        end 
    end.


Fixpoint runStmtDual (fuel: nat) (vg1: valuation * valuation) (vl1: valuation) (st: stmt) (vg2: valuation * valuation) (vl2: valuation): Prop :=
     match fuel with
    | O => False
    | S fuel' => match interp (Var "current") (fst vg1) with
        | 1 =>  match st with
            | varDeclStmt s e => exists n, n = interp2 e (fst vg1) vl1  /\ vl2 = (vl1 $+ (s, varAss n)) /\ vg1 = vg2 
            | ifStmt e s1 s2 => (exists r, r = interp2 e (fst vg1) vl1 /\ r <> 0 /\ runStmtDual fuel' vg1 vl1 s1 vg2 vl2) \/
                (0 = interp2 e (fst vg1) vl1 /\ runStmtDual fuel' vg1 vl1 s2 vg2 vl2)
            | whileStmt e s => (exists r vgmid vlmid, r = interp2 e (fst vg1) vl1 /\ r <> 0 /\ runStmtDual fuel' vg1 vl1 s vgmid vlmid 
                /\ runStmtDual fuel' vgmid vlmid st vg2 vl2) \/ (0 = interp2 e (fst vg1) vl1 /\ vg1 = vg2 /\ vl1 = vl2)
            (*Check local val, if exists, reassign, else check global, if exists reassign, else crash (prop is false)*)
            | assignmentStmt s e => (vl1 $? s <> None /\ exists n, n = interp2 e (fst vg1) vl1 /\ vl2 = (vl1 $+ (s, varAss n)) /\ vg1 = vg2) \/
                ((fst vg1) $? s <> None /\ vl1 $? s = None /\ exists n, n = interp2 e (fst vg1) vl1 /\ vg2 = ((fst vg1) $+ (s, varAss n), snd vg1) /\ vl1 = vl2)
            | awaitStmt sig_name => vg1 = vg2 /\ vl1 = vl2
            | sequence s1 s2 => match s1 with
                | awaitStmt sig_name => (exists r, (interp (Var sig_name) (fst vg1)) = r  /\ r <> 0 /\ runStmtDual fuel' vg1 vl1 s2 vg2 vl2) \/ 
                ((interp (Var sig_name) (fst vg1) = 0) /\ vg2 = (((fst vg1) $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2)), ((snd vg1) $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2)))
                /\ vl1 = vl2)
                | _ => exists vgmid vlmid, runStmtDual fuel' vg1 vl1 s1 vgmid vlmid /\ runStmtDual fuel' vgmid vlmid s2 vg2 vl2
                end
            | assignCallMethodStmt ret method_name args =>
                match (fst vg1) $? method_name with 
                | Some (methodAss name_args found_ret found_body) => 
                    exists vlmid,
                    runStmtDual fuel' vg1
                    (fold_left 
                        (fun (acc: valuation) (arg_argname: expr * string) => 
                            (acc $+ ((snd arg_argname), varAss (interp2 (fst arg_argname) (fst vg1) vl1)))
                        ) 
                        (combine args name_args) ($0)) 
                    found_body vg2 vlmid
                    /\ match ret, found_ret with
                        | Some s_ret, Some s_found_ret =>  (exists r, interp (Var s_found_ret) vlmid = r /\ vl2 = vl1 $+ (s_ret, varAss r))
                        | Some _, None => False
                        | None, _ => vl2 = vlmid
                        end    
                | _ => False
                end
            | emitSignalStmt sig_name opt_callback args => exists vgmid vgmid' vlmid', vgmid = (((fst vg1) $+ (sig_name, varAss 1)), ((snd vg1) $+ (sig_name, varAss 1))) /\
                match opt_callback with
                    (*Context switch if n = 2*)
                    | Some (f, n) =>  match n with
                        | 2 => exists vgswitch vgreturn vldump, vgswitch = (((fst vgmid) $+ (("current")%string, varAss 2)), snd vgmid) /\ runStmtDual fuel' vgswitch ($0) (assignCallMethodStmt None f args) vgreturn vldump
                        /\ vgmid' = (((fst vgreturn) $+ (("current")%string, varAss 1)), snd vgreturn) /\ vl1 = vlmid'
                        | _ => runStmtDual fuel' vgmid vl1 (assignCallMethodStmt None f args) vgmid' vlmid'
                        end
                    | None => vgmid = vgmid' /\ vl1 = vlmid'
                    end /\ match (fst vgmid') $? ("waiting_" ++ sig_name)%string with
                        | Some (waitAss n b) => 
                        (*Set current to 2 if n = 2 else leave it like that, then runStmt of the body, and switch back current to 1*)
                            match n with
                                | 2 => exists vgswitch vgreturn vldump, vgswitch = (((fst vgmid') $+ (("current")%string, varAss 2)), snd vgmid') /\ runStmtDual fuel' vgswitch ($0) b vgreturn vldump
                                /\ vg2 = (((fst vgreturn) $+ (("current")%string, varAss 1)), snd vgreturn) /\ vlmid' = vl2
                                | _ => runStmtDual fuel' vgmid' vlmid' b vg2 vl2
                                end
                        | _ => vgmid' = vg2 /\ vlmid' = vl2
                        end
            | skip => vg1 = vg2 /\ vl1 = vl2
            end
        | 2 => match st with
            | varDeclStmt s e => exists n, n = interp2 e (snd vg1) vl1  /\ vl2 = (vl1 $+ (s, varAss n)) /\ vg1 = vg2
            | ifStmt e s1 s2 => (exists r, r = interp2 e (snd vg1) vl1 /\ r <> 0 /\ runStmtDual fuel' vg1 vl1 s1 vg2 vl2) \/
                (0 = interp2 e (snd vg1) vl1 /\ runStmtDual fuel' vg1 vl1 s2 vg2 vl2)
            | whileStmt e s => (exists r vgmid vlmid, r = interp2 e (snd vg1) vl1 /\ r <> 0 /\ runStmtDual fuel' vg1 vl1 s vgmid vlmid 
                /\ runStmtDual fuel' vgmid vlmid st vg2 vl2) \/ (0 = interp2 e (snd vg1) vl1 /\ vg1 = vg2 /\ vl1 = vl2)
            | assignmentStmt s e => (vl1 $? s <> None /\ exists n, n = interp2 e (snd vg1) vl1 /\ vl2 = (vl1 $+ (s, varAss n)) /\ vg1 = vg2) \/
                ((snd vg1) $? s <> None /\ vl1 $? s = None /\ exists n, n = interp2 e (snd vg1) vl1 /\ vg2 = (fst vg1, (snd vg1) $+ (s, varAss n)) /\ vl1 = vl2)
            | awaitStmt sig_name => vg1 = vg2 /\ vl1 = vl2
            | sequence s1 s2 => match s1 with
                | awaitStmt sig_name => (exists r, (interp (Var sig_name) (fst vg1)) = r  /\ r <> 0 /\ runStmtDual fuel' vg1 vl1 s2 vg2 vl2 ) \/ 
                ((interp (Var sig_name) (fst vg1) = 0) /\ vg2 = (((fst vg1) $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2)), ((snd vg1) $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2))))
                | _ => exists vgmid vlmid, runStmtDual fuel' vg1 vl1 s1 vgmid vlmid /\ runStmtDual fuel' vgmid vlmid s2 vg2 vl2
                end
            (*The n is the program number of the program containing the fuction, refering to the index of the valuation to read to get the function*)
            (*Note : We could just context switch before *)
            | assignCallMethodStmt ret method_name args =>
                match (snd vg1) $? method_name with 
                | Some (methodAss name_args found_ret found_body) => 
                    exists vlmid,
                    runStmtDual fuel' vg1
                    (fold_left 
                        (fun (acc: valuation) (arg_argname: expr * string) => 
                            (acc $+ ((snd arg_argname), varAss (interp2 (fst arg_argname) (snd vg1) vl1)))
                        ) 
                        (combine args name_args) ($0)) 
                    found_body vg2 vlmid
                    /\ match ret, found_ret with
                        | Some s_ret, Some s_found_ret =>  (exists r, interp (Var s_found_ret) vlmid = r /\ vl2 = vl1 $+ (s_ret, varAss r))
                        | Some _, None => False
                        | None, _ => vl2 = vlmid
                        end
                | _ => False
                end
            | emitSignalStmt sig_name opt_callback args => exists vgmid vgmid' vlmid', vgmid = (((fst vg1) $+ (sig_name, varAss 1)), ((snd vg1) $+ (sig_name, varAss 1))) /\
                match opt_callback with
                    | Some (f, n) =>  match n with
                        | 1 => exists vgswitch vgreturn vldump, vgswitch = (((fst vgmid) $+ (("current")%string, varAss 1)), snd vgmid) /\ runStmtDual fuel' vgswitch ($0) (assignCallMethodStmt None f args) vgreturn vldump
                        /\ vgmid' = (((fst vgreturn) $+ (("current")%string, varAss 2)), snd vgreturn)
                        | _ => runStmtDual fuel' vgmid vl1 (assignCallMethodStmt None f args) vgmid' vlmid'
                        end
                    | None => vgmid = vgmid' /\ vl1 = vlmid'
                    end /\ match (fst vgmid') $? ("waiting_" ++ sig_name)%string with
                        | Some (waitAss n b) => 
                        (*Set current to 1 if n = 1 else leave it like that, then runStmt of the body, and switch back current to 2*)
                            match n with
                                | 1 => exists vgswitch vgreturn vldump, vgswitch = (((fst vgmid') $+ (("current")%string, varAss 1)), snd vgmid') /\ runStmtDual fuel' vgswitch ($0) b vgreturn vldump
                                /\ vg2 = (((fst vgreturn) $+ (("current")%string, varAss 2)), snd vgreturn) /\ vlmid' = vl2
                                | _ => runStmtDual fuel' vgmid' vlmid' b vg2 vl2
                                end
                        | _ => vgmid' = vg2 /\ vlmid' = vl2
                        end
            | skip => vg1 = vg2 /\ vl1 = vl2
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
            | readyDecl st => exists vl2, runStmtDual fuel' v1 ($0) st v2 vl2
            | processDecl st1 => match dB with
                | processDecl st2 => exists vmid vmid' vl2 vl2', runStmtDual fuel' v1 ($0) st1 vmid vl2 /\ runStmtDual fuel' vmid ($0) st2 vmid' vl2' /\ runDual fuel' vmid' dA dB v2 (*runStmt process A puis B, puis run infini*)
                | EndDecl => run fuel' (fst v1) dA (fst v2) (*runStmt process A, puis run infini*)(*Quid de snd v2, si B await A dans son ready, il faut pouvoir l'appeler avec la bonne valuation*)
                | _ => exists vmid, vmid = (((fst v1) $+ (("current")%string, varAss 2)), snd v1) /\ runDual fuel' vmid dA dB v2
                end
            | SequenceDecl d1 d2 => exists vmid, runDual fuel' v1 d1 dB vmid /\ runDual fuel' vmid d2 dB v2
            | EndDecl => match dB with (*If B process : runStmt B + run B infini, else juste run B infini*)
                                        (*If B EndDecl, v1 = v2 pour finir l'execution*)
                | processDecl st2 => exists vmid vmid' vl2, vmid = (((fst v1) $+ (("current")%string, varAss 2)), snd v1) /\ runStmtDual fuel' vmid ($0) st2 vmid' vl2 /\ runDual fuel' vmid' dA dB v2
                | EndDecl => v1 = v2
                | _ => exists vmid, vmid = (((fst v1) $+ (("current")%string, varAss 2)), snd v1) /\ runDual fuel' vmid dA dB v2
                end 
        
            end 
        | 2 => match dB with
            | classVarDecl s e => exists n, n = interp e (snd v1)  /\ v2 = (fst v1, ((snd v1) $+ (s, varAss n)))
            | methodDecl s l ret st => v2 = (fst v1, ((snd v1) $+ (s, methodAss l ret st)))
            | readyDecl st => exists vl2, runStmtDual fuel' v1 ($0) st v2 vl2
            | processDecl st => exists vmid, vmid = (((fst v1) $+ (("current")%string, varAss 1)), snd v1) /\ runDual fuel' vmid dA dB v2
            | SequenceDecl d1 d2 => exists vmid, runDual fuel' v1 dA d1 vmid /\ runDual fuel' vmid dA d2 v2 
            | EndDecl => exists vmid, vmid = (((fst v1) $+ (("current")%string, varAss 1)), snd v1) /\ runDual fuel' vmid dA dB v2
            end 
        | _ => False
        end
    end. *)