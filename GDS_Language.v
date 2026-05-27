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
             add waiting s2 to global valuation then skip, 
        else just run s1 then s2*)
        | sequence s1 s2 => match s1 with
            | awaitStmt sig_name => Some (vg $+ (sig_name, waitAss 1 s2), vl)
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
        (*Check for callback (if exists, call this function with args of signal), then check for awaiting body (if exists, call this function)*)
        | emitSignalStmt sig_name opt_callback args => match opt_callback with
            | Some (f, _n) => match runStmt fuel' vg vl (assignCallMethodStmt None f args) with
                | Some (vgmid, vlmid) => match vgmid $? sig_name with
                    (*Here we do a mini context switch for the local val*)
                    | Some (waitAss _ body) => match runStmt fuel' vgmid $0 body with
                        | Some (vg2, vl2) => Some (vg2 $- sig_name, vlmid)
                        | None => None
                        end
                    | _ => Some (vgmid, vlmid)
                    end
                | None => None
                end
            | None => match vg $? sig_name with
                | Some (waitAss _ body) => runStmt fuel' vg vl body
                | _ => Some (vg, vl)
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

Record dual_state := {
  current : nat;
  signal_state : valuation;
  vgA : valuation;
  vgB: valuation;
}.


Fixpoint runStmtDual (fuel: nat) (ds: dual_state) (vl: valuation) (st: stmt) : option((dual_state) * valuation) :=
    match fuel with
    | O => None
    | S fuel' => match current ds with
        | 1 => match st with
            | varDeclStmt name e => match interp2 e (vgA ds) vl with
                | Some n => Some (ds, vl $+ (name, varAss n))
                | None => None
                end
            | ifStmt e s1 s2 => match interp2 e (vgA ds) vl with
                | Some 0 => runStmtDual fuel' ds vl s2
                | Some _n => runStmtDual fuel' ds vl s1
                | None => None
                end
            | whileStmt e s => match interp2 e (vgA ds) vl with
                | Some 0 => Some (ds, vl)
                | Some _n => match runStmtDual fuel' ds vl s with
                    | Some (dsmid, vlmid) => runStmtDual fuel' dsmid vlmid st
                    | None => None
                    end
                | None => None
                end
            | assignmentStmt name e => match vl $? name with
                | Some _ => match interp2 e (vgA ds) vl with
                    | Some n => Some (ds, vl $+ (name, varAss n))
                    | None => None
                    end
                | None => match (vgA ds) $? name with 
                    | Some _ => match interp2 e (vgA ds) vl with
                        | Some n => Some (({| current := current ds; signal_state := signal_state ds; vgA := (vgA ds) $+ (name, varAss n); vgB := vgB ds |}), vl)
                        | None => None
                        end
                    | None => None
                    end
                end
            | await sig_name => Some (ds, vl)
            | sequence s1 s2 => match s1 with
                | awaitStmt sig_name => Some ({| current := current ds; signal_state := signal_state ds $+ (sig_name, waitAss 1 s2); vgA := vgA ds; vgB := vgB ds |}, vl)
                | _ => match runStmtDual fuel' ds vl s1 with
                    | Some (dsmid, vlmid) => runStmtDual fuel' dsmid vlmid s2
                    | None => None
                    end
                end
            | assignCallMethodStmt ret method_name args => match (vgA ds) $? method_name with
                | Some (methodAss name_args found_ret found_body) => let newLocal :=  (fold_left
                        (fun (acc: valuation) (arg_argname: expr * string) =>
                            match interp2 (fst arg_argname) (vgA ds) vl with
                                | Some n => (acc $+ (snd arg_argname, varAss n))
                                | None => acc
                                end
                                )
                                (combine args name_args) $0) in match
                    (runStmtDual fuel' ds newLocal found_body) with
                        | Some (dsmid, vlmid) => match ret, found_ret with
                            | Some s_ret, Some s_found_ret => match interp (Var s_found_ret) vlmid with
                                | Some r => match runStmtDual fuel' dsmid vl (assignmentStmt s_ret (Const r)) with
                                    | Some (ds2, vl2) => Some (ds2, vl2)
                                    | None => Some (dsmid, vl $+ (s_ret, varAss r))
                                    end
                                | None => None
                                end
                            (*Assigning void to a var*)
                            | Some _, None => None
                            (*Not reading the return of a non-void func*)
                            | None, _ => Some (dsmid, vl)
                            end
                        | None => None
                        end
                | _ => None
                end
            | emitSignalStmt sig_name opt_callback args => match opt_callback with
            (*Context switch if n = 2*)
                | Some (f, 1) => match runStmtDual fuel' ds vl (assignCallMethodStmt None f args) with
                    (*Check for waiting bodies*)
                    | Some (dsmid, vlmid) => match (signal_state dsmid) $? sig_name with
                        (*Context switch if 2*)
                        | Some (waitAss 1 body) => match runStmtDual fuel' {|current := 1; signal_state := signal_state dsmid $- sig_name; vgA := vgA dsmid; vgB := vgB dsmid |} $0 body with
                            | Some (ds2, vl2) => Some ({|current := 1; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |}, vlmid)
                            | None => None
                            end
                        (*Double checking: here we want to set current to 2, call body with an empty local val, set current to 1 again and return that new global val with the old local one*)
                        | Some (waitAss 2 body) => match runStmtDual fuel' {|current := 2; signal_state := signal_state dsmid $- sig_name; vgA := vgA dsmid; vgB := vgB dsmid |} $0 body with
                            | Some (ds2, vl2) => Some ({|current := 1; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |}, vlmid)
                            | None => None
                            end
                        | _ => Some (dsmid, vlmid)
                        end
                    | None => None
                    end
                (*NB: there is a world where this is wrong because we context switch but still keep the same local val, which we return later after switching back*)
                | Some (f, 2) => match runStmtDual fuel' {|current := 2; signal_state := signal_state ds; vgA := vgA ds; vgB := vgB ds |} vl (assignCallMethodStmt None f args) with
                    | Some (dsmid, vlmid) => match (signal_state dsmid) $? sig_name with
                        (*Already switched, so stay in current if 2 or switch back if 1*)
                        | Some (waitAss 1 body) => match runStmtDual fuel' {|current := 1; signal_state := signal_state dsmid $- sig_name; vgA := vgA dsmid; vgB := vgB dsmid |} $0 body with
                            | Some (ds2, vl2) => Some ({|current := 1; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |}, vlmid)
                            | None => None
                            end
                        | Some (waitAss 2 body) => match runStmtDual fuel' {|current := 2; signal_state := signal_state dsmid $- sig_name; vgA := vgA dsmid; vgB := vgB dsmid |} $0 body with
                            | Some (ds2, vl2) => Some ({|current := 1; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |}, vlmid)
                            | None => None
                            end
                        (*Switch back*)
                        | _ => Some ({|current := 1; signal_state := signal_state dsmid; vgA := vgA dsmid; vgB := vgB dsmid |}, vlmid)
                        end
                    | None => None
                    end
                | None => match (signal_state ds) $? sig_name with
                    (*Context switch if 2*)
                    | Some (waitAss 1 body) => match runStmtDual fuel' {|current := 1; signal_state := signal_state ds $- sig_name; vgA := vgA ds; vgB := vgB ds |} $0 body with
                        | Some (ds2, vl2) => Some ({|current := 1; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |}, vl)
                        | None => None
                        end
                    | Some (waitAss 2 body) => match runStmtDual fuel' {|current := 2; signal_state := signal_state ds $- sig_name; vgA := vgA ds; vgB := vgB ds |} $0 body with
                        | Some (ds2, vl2) => Some ({|current := 1; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |}, vl)
                        | None => None
                        end
                    | _ => Some (ds, vl)
                    end
                | _ => None
                end
            | skip => Some (ds, vl)
            end
        | 2 => match st with
            | varDeclStmt name e => match interp2 e (vgB ds) vl with
                | Some n => Some (ds, vl $+ (name, varAss n))
                | None => None
                end
            | ifStmt e s1 s2 => match interp2 e (vgB ds) vl with
                | Some 0 => runStmtDual fuel' ds vl s2
                | Some _n => runStmtDual fuel' ds vl s1
                | None => None
                end
            | whileStmt e s => match interp2 e (vgB ds) vl with
                | Some 0 => Some (ds, vl)
                | Some _n => match runStmtDual fuel' ds vl s with
                    | Some (dsmid, vlmid) => runStmtDual fuel' dsmid vlmid st
                    | None => None
                    end
                | None => None
                end
            | assignmentStmt name e => match vl $? name with
                | Some _ => match interp2 e (vgB ds) vl with
                    | Some n => Some (ds, vl $+ (name, varAss n))
                    | None => None
                    end
                | None => match (vgB ds) $? name with 
                    | Some _ => match interp2 e (vgB ds) vl with
                        | Some n => Some ({|current := current ds; signal_state := signal_state ds; vgA := vgA ds; vgB := (vgB ds $+ (name, varAss n)) |}, vl)
                        | None => None
                        end
                    | None => None
                    end
                end
            | await sig_name => Some (ds, vl)
            | sequence s1 s2 => match s1 with
                | awaitStmt sig_name => Some ({|current := current ds; signal_state := signal_state ds $+ (sig_name, waitAss 2 s2); vgA := vgA ds; vgB := vgB ds |}, vl)
                | _ => match runStmtDual fuel' ds vl s1 with
                    | Some (dsmid, vlmid) => runStmtDual fuel' dsmid vlmid s2
                    | None => None
                    end
                end
            | assignCallMethodStmt ret method_name args => match (vgB ds) $? method_name with
                | Some (methodAss name_args found_ret found_body) => let newLocal :=  (fold_left
                        (fun (acc: valuation) (arg_argname: expr * string) =>
                            match interp2 (fst arg_argname) (vgB ds) vl with
                                | Some n => (acc $+ (snd arg_argname, varAss n))
                                | None => acc
                                end
                                )
                                (combine args name_args) $0) in
                match (runStmtDual fuel' ds newLocal found_body) with
                        | Some (dsmid, vlmid) => match ret, found_ret with
                            | Some s_ret, Some s_found_ret => match interp (Var s_found_ret) vlmid with
                                | Some r => match runStmtDual fuel' dsmid vl (assignmentStmt s_ret (Const r)) with
                                    | Some (dsmid2, vl2) => Some (dsmid2, vl2)
                                    | None => Some (dsmid, vl $+ (s_ret, varAss r))
                                    end
                                | None => None
                                end
                            (*Assigning void to a var*)
                            | Some _, None => None
                            (*Not reading the return of a non-void func*)
                            | None, _ => Some (dsmid, vl)
                            end
                        | None => None
                        end
                | _ => None
                end
            | emitSignalStmt sig_name opt_callback args => match opt_callback with
            (*Context switch if n = 1*)
                (*NB: there is a world where this is wrong because we context switch but still keep the same local val, which we return later after switching back*)
                | Some (f, 1) => match runStmtDual fuel' {|current := 1; signal_state := signal_state ds; vgA := vgA ds; vgB := vgB ds |} vl (assignCallMethodStmt None f args) with
                    | Some (dsmid, vlimd) => match (signal_state dsmid) $? sig_name with
                        (*Already switched, so stay in current if 1 or switch back if 2*)
                        | Some (waitAss 1 body) => match runStmtDual fuel' {|current := 1; signal_state := signal_state dsmid $- sig_name; vgA := vgA dsmid; vgB := vgB dsmid |} $0 body with
                            | Some (ds2, vl2) => Some ({|current := 2; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |}, vlimd)
                            | None => None
                            end
                        | Some (waitAss 2 body) => match runStmtDual fuel' {|current := 2; signal_state := signal_state dsmid $- sig_name; vgA := vgA dsmid; vgB := vgB dsmid |} $0 body with
                            | Some (ds2, vl2) => Some ({|current := 2; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |}, vlimd)
                            | None => None
                            end
                        (*Switch back*)
                        | _ => Some ({|current := 2; signal_state := signal_state dsmid; vgA := vgA dsmid; vgB := vgB dsmid |}, vlimd)
                        end
                    | None => None
                    end
                | Some (f, 2) => match runStmtDual fuel' ds vl (assignCallMethodStmt None f args) with
                    | Some (dsmid, vlimd) => match (signal_state dsmid) $? sig_name with
                        (*Context switch if 1*)
                        (*Double checking: here we want to set current to 1, call body with an empty local val, set current to 2 again and return that new global val with the old local one*)
                        | Some (waitAss 1 body) => match runStmtDual fuel' {|current := 1; signal_state := signal_state dsmid $- sig_name; vgA := vgA dsmid; vgB := vgB dsmid |} $0 body with
                            | Some (ds2, vl2) => Some ({|current := 2; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |}, vlimd)
                            | None => None
                            end
                        | Some (waitAss 2 body) => match runStmtDual fuel' {|current := 2; signal_state := signal_state dsmid $- sig_name; vgA := vgA dsmid; vgB := vgB dsmid |} $0 body with
                            | Some (ds2, vl2) => Some ({|current := 2; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |}, vlimd)
                            | None => None
                            end
                        | _ => Some (dsmid, vlimd)
                        end
                    | None => None
                    end
                | None => match (signal_state ds) $? sig_name with
                    (*Context switch if 1*)
                    | Some (waitAss 1 body) => match runStmtDual fuel' {|current := 1; signal_state := signal_state ds $- sig_name; vgA := vgA ds; vgB := vgB ds |} $0 body with
                        | Some (ds2, vl2) => Some ({|current := 2; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |}, vl)
                        | None => None
                        end
                    | Some (waitAss 2 body) => match runStmtDual fuel' {|current := 2; signal_state := signal_state ds $- sig_name; vgA := vgA ds; vgB := vgB ds |} $0 body with
                        | Some (ds2, vl2) => Some ({|current := 2; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |}, vl)
                        | None => None
                        end
                    | _ => Some (ds, vl)
                    end
                | _ => None
                end
            | skip => Some (ds, vl)
            end
        | _ => None
        end
    end.

Arguments runStmtDual _ _ _ _ : simpl never.


(*Init phase of a program: var declarations, method declarations and ready execution*)
Fixpoint initProg (fuel: nat) (ds: dual_state) (d: topLevelDecl) : option (dual_state * option stmt) :=
    match fuel with
    | O => None
    | S fuel' => match current ds with
        | 1 => match d with
            | classVarDecl name e => match interp e (vgA ds) with
                | Some n => Some ({|current := 1; signal_state := signal_state ds; vgA := vgA ds $+ (name, varAss n); vgB := vgB ds |}, None)
                | None => None
                end
            | methodDecl name args ret body => Some ({|current := 1; signal_state := signal_state ds; vgA := vgA ds $+ (name, methodAss args ret body); vgB := vgB ds |}, None)
            | readyDecl body => match runStmtDual stmtFuel ds $0 body with
                | Some (ds2, vl2) => Some (ds2, None)
                | None => None
                end
            | processDecl body => Some (ds, Some body)
            | SequenceDecl d1 d2 => match initProg fuel' ds d1 with
                | Some (dsA, pA) => match initProg fuel' dsA d2 with
                    | Some (dsB, pB) => Some (dsB, match pA with
                        | Some bodyA => Some bodyA
                        | None => pB
                        end)
                    | None => None
                    end
                | None => None
                end
            | EndDecl => Some (ds, None)
            end
        | 2 => match d with
            | classVarDecl name e => match interp e (vgB ds) with
                | Some n => Some ({|current := 2; signal_state := signal_state ds; vgA := vgA ds; vgB := vgB ds $+ (name, varAss n) |}, None)
                | None => None
                end
            | methodDecl name args ret body => Some ({|current := 2; signal_state := signal_state ds; vgA := vgA ds; vgB := vgB ds $+ (name, methodAss args ret body) |}, None)
            | readyDecl body => match runStmtDual stmtFuel ds $0 body with
                | Some (ds2, vl2) => Some (ds2, None)
                | None => None
                end
            | processDecl body => Some (ds, Some body)
            | SequenceDecl d1 d2 => match initProg fuel' ds d1 with
                | Some (dsA, pA) => match initProg fuel' dsA d2 with
                    | Some (dsB, pB) => Some (dsB, match pA with
                        | Some bodyA => Some bodyA
                        | None => pB
                        end)
                    | None => None
                    end
                | None => None
                end
            | EndDecl => Some (ds, None)
            end
        | _ => None
        end
    end.

Arguments initProg _ _ _ : simpl never.

Fixpoint runProcessesDual (fuel: nat) (ds: dual_state) (pA pB: option stmt) : option dual_state :=
    match fuel with
    | O => None
    | S fuel' => if Nat.eqb fuel' 1 then Some ds else match pA, pB with
        (*Run both processes one after the other until no fuel, in which case we return the last val*)
        | Some bodyA, Some bodyB => match runStmtDual stmtFuel ds $0 bodyA with
            | Some (dsmid, vlmid) => match runStmtDual stmtFuel {|current := 2; signal_state := signal_state dsmid; vgA := vgA dsmid; vgB := vgB dsmid |} $0 bodyB with
                | Some (ds2, vl2) => runProcessesDual fuel' {|current := 1; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |} (Some bodyA) (Some bodyB)
                | None => None
                end
            | None => None
            end
        (*If one process is None but the other isn't, we still want to run the other process until no fuel left*)
        | Some bodyA, None => match runStmtDual stmtFuel ds $0 bodyA with
            | Some (ds2, vl2) => runProcessesDual fuel' {|current := 1; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |} (Some bodyA) None
            | None => None
            end
        | None, Some bodyB => match runStmtDual stmtFuel {|current := 2; signal_state := signal_state ds; vgA := vgA ds; vgB := vgB ds |} $0 bodyB with
            | Some (ds2, vl2) => runProcessesDual fuel' {|current := 1; signal_state := signal_state ds2; vgA := vgA ds2; vgB := vgB ds2 |} None (Some bodyB)
            | None => None
            end
        (*If no processes, done*)
        | None, None => Some ds
        end
    end.

Arguments runProcessesDual _ _ _ _ : simpl never.

Definition runDual (fuel: nat) (ds : dual_state) (d: topLevelDecl * topLevelDecl) : option (dual_state) :=
    match initProg fuel ds (fst d) with
    | Some (dsA, pA) => match initProg fuel ({|current := 2; signal_state := signal_state dsA; vgA := vgA dsA; vgB := vgB dsA |}) (snd d) with
        | Some (dsB, pB) => runProcessesDual fuel {|current := 1; signal_state := signal_state dsB; vgA := vgA dsB; vgB := vgB dsB |} pA pB
        | None => None
        end
    | None => None
    end.

Arguments runDual _ _ _ : simpl never.