From Stdlib Require Import String.
From Stdlib Require Export NArith Arith.
From Stdlib Require Import List.
Require Import CompMap.

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

Infix ";;" := sequence (at level 76, right associativity).
Infix ";;;" := SequenceDecl (at level 76, right associativity).

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


Fixpoint runStmt (fuel: nat) (vg: valuation) (vl: valuation) (st: stmt): option (valuation * valuation) :=
    match fuel with
    | O => None
    | S fuel' =>
        match st with
        (*Interp expression, then assign it in local val*)
        | varDeclStmt name e => match interp2 e vg vl with
                                | Some n => Some (vg, (vl $+ (name, varAss n)))
                                | None => None
                                end
        (*If expr is >= 1, run s1, elsif 0 run s2, else crash*)
        | ifStmt e s1 s2 => match interp2 e vg vl with
                            | Some 0 => runStmt fuel' vg vl s2
                            | Some _n => runStmt fuel' vg vl s1
                            | None => None
                            end
        (*While e <> 0, run s, else skip*)
        | whileStmt e s => match interp2 e vg vl with
                            | Some 0 => Some (vg, vl)
                            | Some _n => match (runStmt fuel' vg vl s) with
                                | Some (vgmid, vlmid) => runStmt fuel' vgmid vlmid st
                                | None => None
                                end
                            | None => None
                            end
        (*If name defined in local, reassign it with value of e, else do the same for global, else crash*)
        | assignmentStmt name e => match vl $? name with
                                | Some _ => match interp2 e vg vl with
                                    | Some n => Some (vg, (vl $+ (name, varAss n)))
                                    | None => None
                                    end
                                | None => match vg $? name with
                                    | Some _ => match interp2 e vg vl with
                                        | Some n => Some (vg $+ (name, varAss n), vl)
                                        | None => None
                                        end
                                    | None => None
                                    end
                                end
        (*Skip, await is checked in sequence, because await as last instruction does nothing anyways*)
        | awaitStmt sig_name => Some (vg, vl)
        (*If s1 is await:
             check if the waited signal has been emitted. 
                If so just run s2
                else add waiting s2 to global valuation then skip, 
        else just run s1 then s2*)
        | sequence s1 s2 => match s1 with
            | awaitStmt sig_name => match interp (Var sig_name) vg with
                | Some 0 | None => Some (vg $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2), vl)
                | Some _n => runStmt fuel' vg vl s2
                end
            | _ => match runStmt fuel' vg vl s1 with
                | Some (vgmid, vlmid) => runStmt fuel' vgmid vlmid s2
                | None => None
                end
            end
        (*Get method, match arguments to parameters. If we want to assign the return value, read it in the local var of the executed func, then assign it*)
        | assignCallMethodStmt ret method_name args => match vg $? method_name with
            | Some (methodAss name_args found_ret found_body) => match 
                (runStmt fuel' vg 
                (fold_left 
                    (fun (acc: valuation) (arg_argname: expr * string) => 
                        match interp2 (fst arg_argname) vg vl with
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
                        | Some r => match runStmt fuel' vgmid vl (assignmentStmt s_ret (Const r)) with
                            | Some (vg2, vl2) => Some (vg2, vl2)
                            | None => Some (vgmid, vl $+ (s_ret, varAss r))
                            end
                        | None => None 
                        end
                    (*Assigning void to a var*)
                    | Some _, None => None
                    (*Not reading the return of a non-void func*)
                    | None, _ => Some (vgmid, vl)
                    end
                | None => None
                end
            | _ => None
            end
        (*Mark signal as emitted, check for callback (if exists, call this function with args of signal), then check for awaiting body (if exists, call this function)*)
        | emitSignalStmt sig_name opt_callback args => let vgmid := (vg $+ (sig_name, varAss 1)) in match opt_callback with
            | Some (f, _n) => match runStmt fuel' vgmid vl (assignCallMethodStmt None f args) with
                | Some (vgmid', vlmid') => match vgmid' $? ("waiting_" ++ sig_name)%string with
                    (*Here we do a mini context switch for the local val*)
                    | Some (waitAss _ body) => match runStmt fuel' vgmid' $0 body with
                        | Some (vg2, vl2) => Some (vg2, vlmid')
                        | None => None
                        end
                    | _ => Some (vgmid', vlmid')
                    end
                | None => None
                end
            | None => match vgmid $? ("waiting_" ++ sig_name)%string with
                | Some (waitAss _ body) => runStmt fuel' vgmid vl body
                | _ => Some (vgmid, vl)
                end
            end
        | skip => Some (vg, vl)
        end
    end.

Arguments runStmt _ _ _ _ : simpl never.


Definition stmtFuel := 20.


Fixpoint run (fuel: nat) (v: valuation) (d: topLevelDecl) : option valuation :=
    match fuel with
    | O => None
    | S fuel' =>
        match d with
        (*Same as for runStmt*)
        | classVarDecl name e => match (interp e v) with
                                | Some n => Some (v $+ (name, varAss n))
                                | None => None
                                end
        (*Just add method to valuation*)
        | methodDecl name args ret body => Some (v $+ (name, methodAss args ret body))
        (*Run the ready func once*)
        | readyDecl body => match (runStmt stmtFuel v ($0) body) with
            | Some (vg2, vl2) => Some vg2
            | None => None
            end
        (*Run until no fuel remaining*)
        | processDecl body => if (Nat.eqb fuel' 1) then Some v else match runStmt stmtFuel v $0 body with
            | Some (vgmid, vlmid) => run fuel' vgmid d
            | None => None
            end
        (*Run d1 then d2*)
        | SequenceDecl d1 d2 => match run fuel' v d1 with
            | Some vmid => run fuel' vmid d2
            | None => None
            end
        | EndDecl => Some v
        end
    end.

Arguments run _ _ _  : simpl never.



Fixpoint runStmtDual (fuel: nat) (vg : valuation * valuation) (vl: valuation) (st: stmt) : option((valuation * valuation) * valuation) :=
    match fuel with
    | O => None
    | S fuel' => match interp (Var "current") (fst vg) with
        | Some 1 => match st with
            | varDeclStmt name e => match interp2 e (fst vg) vl with
                | Some n => Some (vg, vl $+ (name, varAss n))
                | None => None
                end
            | ifStmt e s1 s2 => match interp2 e (fst vg) vl with
                | Some 0 => runStmtDual fuel' vg vl s2
                | Some _n => runStmtDual fuel' vg vl s1
                | None => None
                end
            | whileStmt e s => match interp2 e (fst vg) vl with
                | Some 0 => Some (vg, vl)
                | Some _n => match runStmtDual fuel' vg vl s with
                    | Some (vgmid, vlmid) => runStmtDual fuel' vgmid vlmid st
                    | None => None
                    end
                | None => None
                end
            | assignmentStmt name e => match vl $? name with
                | Some _ => match interp2 e (fst vg) vl with
                    | Some n => Some (vg, vl $+ (name, varAss n))
                    | None => None
                    end
                | None => match (fst vg) $? name with 
                    | Some _ => match interp2 e (fst vg) vl with
                        | Some n => Some (((fst vg) $+ (name, varAss n), snd vg), vl)
                        | None => None
                        end
                    | None => None
                    end
                end
            | await sig_name => Some (vg, vl)
            | sequence s1 s2 => match s1 with
                | awaitStmt sig_name => match interp (Var sig_name) (fst vg) with
                    (*Here, we add "waiting" to fst and snd of vg, but fst is probably sufficient*)
                    | Some 0 | None => Some (((fst vg) $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2), (snd vg) $+ (("waiting_" ++ sig_name)%string, waitAss 1 s2)), vl)
                    | Some _n => runStmtDual fuel' vg vl s2
                    end
                | _ => match runStmtDual fuel' vg vl s1 with
                    | Some (vgmid, vlmid) => runStmtDual fuel' vgmid vlmid s2
                    | None => None
                    end
                end
            | assignCallMethodStmt ret method_name args => match (fst vg) $? method_name with
                | Some (methodAss name_args found_ret found_body) => match
                    (runStmtDual fuel' vg
                    (fold_left
                        (fun (acc: valuation) (arg_argname: expr * string) =>
                            match interp2 (fst arg_argname) (fst vg) vl with
                                | Some n => (acc $+ (snd arg_argname, varAss n))
                                | None => acc
                                end
                                )
                                (combine args name_args) $0)
                                found_body) with
                        | Some (vgmid, vlmid) => match ret, found_ret with
                            | Some s_ret, Some s_found_ret => match interp (Var s_found_ret) vlmid with
                                | Some r => match runStmtDual fuel' vgmid vl (assignmentStmt s_ret (Const r)) with
                                    | Some (vg2, vl2) => Some (vg2, vl2)
                                    | None => Some (vgmid, vl $+ (s_ret, varAss r))
                                    end
                                | None => None
                                end
                            (*Assigning void to a var*)
                            | Some _, None => None
                            (*Not reading the return of a non-void func*)
                            | None, _ => Some (vgmid, vl)
                            end
                        | None => None
                        end
                | _ => None
                end
            | emitSignalStmt sig_name opt_callback args => let vgmid := ((fst vg) $+ (sig_name, varAss 1), (snd vg) $+ (sig_name, varAss 1)) in match opt_callback with
            (*Context switch if n = 2*)
                | Some (f, 1) => match runStmtDual fuel' vgmid vl (assignCallMethodStmt None f args) with
                    | Some (vgmid', vlmid') => match (fst vgmid') $? ("waiting_" ++ sig_name)%string with
                        (*Context switch if 2*)
                        | Some (waitAss 1 body) => match runStmtDual fuel' vgmid' $0 body with
                            | Some (vg2, vl2) => Some (vg2, vlmid')
                            | None => None
                            end
                        (*Double checking: here we want to set current to 2, call body with an empty local val, set current to 1 again and return that new global val with the old local one*)
                        | Some (waitAss 2 body) => let vgswitch := ((fst vgmid') $+ (("current")%string, varAss 2), snd vgmid') in match runStmtDual fuel' vgswitch $0 body with
                            | Some (vg2, vl2) => Some (((fst vg2) $+ (("current")%string, varAss 1) , snd vg2), vlmid')
                            | None => None
                            end
                        | _ => Some (vgmid', vlmid')
                        end
                    | None => None
                    end
                (*NB: there is a world where this is wrong because we context switch but still keep the same local val, which we return later after switching back*)
                | Some (f, 2) => let vgswitch := ((fst vgmid) $+ (("current")%string, varAss 2), snd vgmid) in match runStmtDual fuel' vgswitch vl (assignCallMethodStmt None f args) with
                    | Some (vgmid', vlmid') => match (fst vgmid') $? ("waiting_" ++ sig_name)%string with
                        (*Already switched, so stay in current if two or switch back if 1*)
                        | Some (waitAss 1 body) => let vgswitch' := ((fst vgmid') $+ (("current")%string, varAss 1), snd vgmid') in match runStmtDual fuel' vgswitch' $0 body with
                            | Some (vg2, vl2) => Some (vg2, vlmid')
                            | None => None
                            end
                        | Some (waitAss 2 body) => match runStmtDual fuel' vgmid' $0 body with
                            | Some (vg2, vl2) => Some (((fst vg2) $+ (("current")%string, varAss 1) , snd vg2), vlmid')
                            | None => None
                            end
                        (*Switch back*)
                        | _ => Some (((fst vgmid') $+ (("current")%string, varAss 1) , snd vgmid'), vlmid')
                        end
                    | None => None
                    end
                | None => match (fst vgmid) $? ("waiting_" ++ sig_name)%string with
                    (*Context switch if 2*)
                    | Some (waitAss 1 body) => match runStmtDual fuel' vgmid $0 body with
                        | Some (vg2, vl2) => Some (vg2, vl)
                        | None => None
                        end
                    | Some (waitAss 2 body) => let vgswitch := ((fst vgmid) $+ (("current")%string, varAss 2), snd vgmid) in match runStmtDual fuel' vgswitch $0 body with
                        | Some (vg2, vl2) => Some (((fst vg2) $+ (("current")%string, varAss 1) , snd vg2), vl)
                        | None => None
                        end
                    | _ => Some (vgmid, vl)
                    end
                | _ => None
                end
            | skip => Some (vg, vl)
            end
        | Some 2 => match st with
            | varDeclStmt name e => match interp2 e (snd vg) vl with
                | Some n => Some (vg, vl $+ (name, varAss n))
                | None => None
                end
            | ifStmt e s1 s2 => match interp2 e (snd vg) vl with
                | Some 0 => runStmtDual fuel' vg vl s2
                | Some _n => runStmtDual fuel' vg vl s1
                | None => None
                end
            | whileStmt e s => match interp2 e (snd vg) vl with
                | Some 0 => Some (vg, vl)
                | Some _n => match runStmtDual fuel' vg vl s with
                    | Some (vgmid, vlmid) => runStmtDual fuel' vgmid vlmid st
                    | None => None
                    end
                | None => None
                end
            | assignmentStmt name e => match vl $? name with
                | Some _ => match interp2 e (snd vg) vl with
                    | Some n => Some (vg, vl $+ (name, varAss n))
                    | None => None
                    end
                | None => match (snd vg) $? name with 
                    | Some _ => match interp2 e (snd vg) vl with
                        | Some n => Some ((fst vg, (snd vg) $+ (name, varAss n)), vl)
                        | None => None
                        end
                    | None => None
                    end
                end
            | await sig_name => Some (vg, vl)
            | sequence s1 s2 => match s1 with
                | awaitStmt sig_name => match interp (Var sig_name) (fst vg) with
                    (*Here, we add "waiting" to fst and snd of vg, but fst is probably sufficient*)
                    | Some 0 | None => Some (((fst vg) $+ (("waiting_" ++ sig_name)%string, waitAss 2 s2), (snd vg) $+ (("waiting_" ++ sig_name)%string, waitAss 2 s2)), vl)
                    | Some _n => runStmtDual fuel' vg vl s2
                    end
                | _ => match runStmtDual fuel' vg vl s1 with
                    | Some (vgmid, vlmid) => runStmtDual fuel' vgmid vlmid s2
                    | None => None
                    end
                end
            | assignCallMethodStmt ret method_name args => match (snd vg) $? method_name with
                | Some (methodAss name_args found_ret found_body) => match
                    (runStmtDual fuel' vg
                    (fold_left
                        (fun (acc: valuation) (arg_argname: expr * string) =>
                            match interp2 (fst arg_argname) (snd vg) vl with
                                | Some n => (acc $+ (snd arg_argname, varAss n))
                                | None => acc
                                end
                                )
                                (combine args name_args) $0)
                                found_body) with
                        | Some (vgmid, vlmid) => match ret, found_ret with
                            | Some s_ret, Some s_found_ret => match interp (Var s_found_ret) vlmid with
                                | Some r => match runStmtDual fuel' vgmid vl (assignmentStmt s_ret (Const r)) with
                                    | Some (vg2, vl2) => Some (vg2, vl2)
                                    | None => Some (vgmid, vl $+ (s_ret, varAss r))
                                    end
                                | None => None
                                end
                            (*Assigning void to a var*)
                            | Some _, None => None
                            (*Not reading the return of a non-void func*)
                            | None, _ => Some (vgmid, vl)
                            end
                        | None => None
                        end
                | _ => None
                end
            | emitSignalStmt sig_name opt_callback args => let vgmid := ((fst vg) $+ (sig_name, varAss 1), (snd vg) $+ (sig_name, varAss 1)) in match opt_callback with
            (*Context switch if n = 1*)
                (*NB: there is a world where this is wrong because we context switch but still keep the same local val, which we return later after switching back*)
                | Some (f, 1) => let vgswitch := ((fst vgmid) $+ (("current")%string, varAss 1), snd vgmid) in match runStmtDual fuel' vgswitch vl (assignCallMethodStmt None f args) with
                    | Some (vgmid', vlmid') => match (fst vgmid') $? ("waiting_" ++ sig_name)%string with
                        (*Already switched, so stay in current if 1 or switch back if 2*)
                        | Some (waitAss 1 body) => match runStmtDual fuel' vgmid' $0 body with
                            | Some (vg2, vl2) => Some (((fst vg2) $+ (("current")%string, varAss 2) , snd vg2), vlmid')
                            | None => None
                            end
                        | Some (waitAss 2 body) => let vgswitch' := ((fst vgmid') $+ (("current")%string, varAss 2), snd vgmid') in match runStmtDual fuel' vgswitch' $0 body with
                            | Some (vg2, vl2) => Some (vg2, vlmid')
                            | None => None
                            end
                        (*Switch back*)
                        | _ => Some (((fst vgmid') $+ (("current")%string, varAss 2) , snd vgmid'), vlmid')
                        end
                    | None => None
                    end
                | Some (f, 2) => match runStmtDual fuel' vgmid vl (assignCallMethodStmt None f args) with
                    | Some (vgmid', vlmid') => match (fst vgmid') $? ("waiting_" ++ sig_name)%string with
                        (*Context switch if 1*)
                        (*Double checking: here we want to set current to 1, call body with an empty local val, set current to 2 again and return that new global val with the old local one*)
                        | Some (waitAss 1 body) => let vgswitch := ((fst vgmid') $+ (("current")%string, varAss 1), snd vgmid') in match runStmtDual fuel' vgswitch $0 body with
                            | Some (vg2, vl2) => Some (((fst vg2) $+ (("current")%string, varAss 2) , snd vg2), vlmid')
                            | None => None
                            end
                        | Some (waitAss 2 body) => match runStmtDual fuel' vgmid' $0 body with
                            | Some (vg2, vl2) => Some (vg2, vlmid')
                            | None => None
                            end
                        | _ => Some (vgmid', vlmid')
                        end
                    | None => None
                    end
                | None => match (fst vgmid) $? ("waiting_" ++ sig_name)%string with
                    (*Context switch if 1*)
                    | Some (waitAss 1 body) => let vgswitch := ((fst vgmid) $+ (("current")%string, varAss 1), snd vgmid) in match runStmtDual fuel' vgswitch $0 body with
                        | Some (vg2, vl2) => Some (((fst vg2) $+ (("current")%string, varAss 2) , snd vg2), vl)
                        | None => None
                        end
                    | Some (waitAss 2 body) => match runStmtDual fuel' vgmid $0 body with
                        | Some (vg2, vl2) => Some (vg2, vl)
                        | None => None
                        end
                    | _ => Some (vgmid, vl)
                    end
                | _ => None
                end
            | skip => Some (vg, vl)
            end
        | _ => None
        end
    end.

Arguments runStmtDual _ _ _ _ : simpl never.


(*For this to be correct, the initial val should have current as 1 in fst v*)
Fixpoint runDual (fuel: nat) (v : valuation * valuation) (d: topLevelDecl * topLevelDecl) : option (valuation * valuation) :=
    match fuel with
    | O => None
    | S fuel' => match interp (Var "current") (fst v) with
        | Some 1 => match fst d with
            | classVarDecl name e => match interp e (fst v) with
                | Some n => Some ((fst v) $+ (name, varAss n), snd v)
                | None => None
                end
            | methodDecl name args ret body => Some ((fst v) $+ (name, methodAss args ret body), snd v)
            | readyDecl body => match (runStmtDual stmtFuel v $0 body) with
                | Some (vg2, vl2) => Some vg2
                | None => None
                end
            | processDecl bodyA => if (Nat.eqb fuel' 1) then Some v else match snd d with
                (*Run both processes one after the other until no fuel, in which case we return the last val*)
                | processDecl bodyB => match runStmtDual stmtFuel v $0 bodyA with
                    | Some (vgmid, vlmid) => let vgswitch := ((fst vgmid) $+ (("current")%string, varAss 2), snd vgmid) in match runStmtDual stmtFuel vgswitch $0 bodyB with
                        | Some (vg2, vl2) => let vgswitch' := ((fst vg2) $+ (("current")%string, varAss 1), snd vg2) in runDual fuel' vgswitch' d
                        | None => None
                        end
                    | None => None
                    end
                (*B is over, but might still be waiting or have a function callback in a signal of A, runStmt prog A then rerun*)
                | EndDecl => match runStmtDual stmtFuel v $0 bodyA with
                    | Some (vgmid, vlmid) => runDual fuel' vgmid d
                    | None => None
                    end
                (*If B is not over but not process, switch and rerun*)
                | _ => let vgswitch := (((fst v) $+ (("current")%string, varAss 2)), snd v) in runDual fuel' vgswitch d
                end
            | SequenceDecl d1 d2 => match runDual fuel' v (d1, snd d) with
                | Some vmid => runDual fuel' vmid (d2, snd d)
                | None => None
                end
            (*If B process, runStmt B then rerun. If B = endDecl, done. Else, just run B*)
            | EndDecl => match snd d with
                | processDecl bodyB => if (Nat.eqb fuel' 1) then Some v 
                else let vgswitch := (((fst v) $+ (("current")%string, varAss 2)), snd v) in match runStmtDual stmtFuel vgswitch $0 bodyB with
                    | Some (vg2, vl2) => let vgswitch' := ((fst vg2) $+ (("current")%string, varAss 1), snd vg2) in runDual fuel' vgswitch' d
                    | None => None
                    end
                | EndDecl => Some v
                | _ => let vgswitch := (((fst v) $+ (("current")%string, varAss 2)), snd v) in runDual fuel' vgswitch d
                end
            end
        | Some 2 => match snd d with
            | classVarDecl name e => match interp e (snd v) with
                | Some n => Some (fst v, (snd v) $+ (name, varAss n))
                | None => None
                end
            | methodDecl name args ret body => Some (fst v, (snd v) $+ (name, methodAss args ret body))
            | readyDecl body => match (runStmtDual stmtFuel v $0 body) with
                | Some (vg2, vl2) => Some vg2
                | None => None
                end
            (*Switch and rerun*)
            | processDecl _ => let vgswitch := (((fst v) $+ (("current")%string, varAss 1)), snd v) in runDual fuel' vgswitch d
            | SequenceDecl d1 d2 => match runDual fuel' v (fst d, d1) with
                | Some vmid => runDual fuel' vmid (fst d, d2)
                | None => None
                end
            (*Switch and rerun*)
            | EndDecl => let vgswitch := (((fst v) $+ (("current")%string, varAss 1)), snd v) in runDual fuel' vgswitch d
            end
        | _ => None
        end
    end.

Arguments runDual _ _ _ : simpl never.
