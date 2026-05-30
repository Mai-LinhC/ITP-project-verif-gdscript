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
    | whileStmt: expr -> stmt -> stmt
    | assignmentStmt: string -> expr -> stmt
    | awaitStmt: string -> stmt
    | sequence: stmt -> stmt -> stmt

    (* optional return variable name, method name, args *)
    | assignCallMethodStmt: option string -> string -> list expr -> stmt

    (* signal name, callback function if needed (name * valuation_number), args of signal *)
    | emitSignalStmt: string -> option (string * nat) -> list expr -> stmt
    | skip: stmt
.

Inductive topLevelDecl :=
    | classVarDecl: string -> expr -> topLevelDecl
    (* | constDecl: string -> expr -> topLevelDecl easy to add but useless for our project*)
    (* | signalDecl: string -> list string -> topLevelDecl : removed because we handle signals differently
    could be interesting to add in the future to better match Godot's way of doing it*)
    
    (* method name, arguments, optional return name, body *)
    | methodDecl: string -> list string -> option string -> stmt -> topLevelDecl
    | readyDecl: stmt -> topLevelDecl
    | processDecl: stmt -> topLevelDecl 
    | SequenceDecl: topLevelDecl -> topLevelDecl -> topLevelDecl
    | EndDecl: topLevelDecl.

Inductive assignment :=
 | varAss (n: nat)
 | methodAss (args: list string) (ret: option string) (body: stmt).

Inductive waiting :=
| waitAss (pn: nat) (body: stmt).

Definition valuation := fmap string assignment.

Definition waitings := fifo_map string waiting.

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
Declare Scope expr.
Infix "&" := (Binop LogAnd) (at level 80) : expr.
Infix "==" := (Binop Eq) (at level 70) : expr.
Infix ">>" := (Binop ShiftRight) (at level 60) : expr.
Infix "<<" := (Binop ShiftLeft) (at level 60) : expr.
Infix "+" := (Binop Plus) (at level 50, left associativity) : expr.
Infix "-" := (Binop Minus) (at level 50, left associativity) : expr.
Infix "*" := (Binop Times) (at level 40, left associativity) : expr.
Infix "/" := (Binop Divide) (at level 40, left associativity) : expr.
Infix "mod" := (Binop Modulo) (at level 40) : expr.


Definition option_bind {A B : Type}
  (x : option A) (f : A -> option B) : option B :=
  match x with
  | Some a => f a
  | None => None
  end.

Notation "x >>= f" := (option_bind x f) (at level 50, left associativity).


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
    | Var x => (v $? x) >>= 
        (fun a => match a with
            | varAss n => Some n
            | _ => None
            end)
    | Binop b e1 e2 => match (interp e1 v), (interp e2 v) with
        | Some n1, Some n2 => Some (interp_binop b n1 n2)
        | _, _ => None
        end
     end.

    (*Interp in local then global*)
  Fixpoint interp2 (e: expr) (vg: valuation) (vl: valuation) {struct e}: option nat :=
    match e with
    | Const n => Some n
    | Var x => match vl $? x with 
        | Some a =>
            match a with
            | varAss n => Some n
            | _ => None
            end
        | None => (vg $? x) >>= 
            (fun a => match a with
                | varAss n => Some n
                | _ => None
                end)
        end
    | Binop b e1 e2 => match (interp2 e1 vg vl), (interp2 e2 vg vl) with
        | Some n1, Some n2 => Some (interp_binop b n1 n2)
        | _, _ => None
        end
    end.

Record mono_state := {
    vg: valuation; (*Global valuation of the node*)
    sig_state: waitings; (*Map from signal name to list of waiting bodies*)
}.

(*Creates a valuation that binds the argument names to the value of the arguments in the input valuations*)
Definition unifyArgs (vg vl: valuation) (args: list expr) (name_args: list string) : option valuation :=
(fold_left
    (fun (opt_acc: option valuation) (arg_argname: expr * string) => opt_acc >>= 
            (fun acc => (interp2 (fst arg_argname) vg vl) >>= 
                (fun n => Some (acc $+ (snd arg_argname, varAss n)))
            )
    ) (combine args name_args) (Some $0)).


(*Used to evaluate arguments with the correct valuation before passing them to a function*)
Definition evalArgs (vg vl: valuation) (args: list expr) : option (list expr) :=
    (fold_right
        (fun (e: expr) (opt_acc: option (list expr)) => opt_acc >>= 
            (fun acc => (interp2 e vg vl) >>= (fun n => Some (Const n :: acc)))
        ) (Some nil) args).


Fixpoint runStmt (fuel: nat) (ms: mono_state) (vl: valuation) (st: stmt): option (mono_state * valuation) :=
    match fuel with
    | O => None
    | S fuel' =>
        match st with
        (*if not already defined, interp expression, then assign it in local val*)
        | varDeclStmt name e => match (vl $? name) with
            | Some _ => None (*If name already defined in local, crash*)
            | None => (interp2 e (vg ms) vl) >>= (fun n => Some (ms, vl $+ (name, varAss n)))   
            end
        (* If expr is >= 1 then run s1 else if expr is 0 then run s2 else crash *)
        | ifStmt e s1 s2 => match interp2 e (vg ms) vl with
                            | Some 0 => runStmt fuel' ms vl s2
                            | Some _n => runStmt fuel' ms vl s1
                            | None => None
                            end
        (* While e <> 0, run s, else skip *)
        | whileStmt e s => match interp2 e (vg ms) vl with
                            | Some 0 => Some (ms, vl)
                            | Some _n => (runStmt fuel' ms vl s) >>= 
                                (fun '(msmid, vlmid) => runStmt fuel' msmid vlmid st)
                            | None => None
                            end
        (*If name defined in local, reassign it with value of e, else do the same for global, else crash *)
        | assignmentStmt name e => match vl $? name with
                                | Some _ => (interp2 e (vg ms) vl) >>= 
                                    (fun n => Some (ms, (vl $+ (name, varAss n))))
                                | None => (vg ms $? name) >>= 
                                    (fun _ => (interp2 e (vg ms) vl) >>= 
                                        (fun n => Some ({|vg:= vg ms $+ (name, varAss n); sig_state:= sig_state ms|}, vl))
                                    )
                                end
        (*Skip, await is checked in sequence, because await as last instruction does nothing anyways*)
        | awaitStmt sig_name => Some (ms, vl)
        (*If s1 is await:
             add (waiting s2) to global valuation then skip, 
        else just run s1 then s2*)
        | sequence s1 s2 => match s1 with
            | awaitStmt sig_name => Some ({|vg:= vg ms; sig_state:= sig_state ms $F+ (sig_name, waitAss 1 s2)|}, vl)
            | _ => (runStmt fuel' ms vl s1) >>=
                (fun '(msmid, vlmid) => runStmt fuel' msmid vlmid s2)
            end
        (*Get method, match arguments to parameters. If we want to assign the return value, read it in the local var of the executed func, then assign it*)
        | assignCallMethodStmt ret method_name args => match vg ms $? method_name with
            | Some (methodAss name_args found_ret found_body) => (unifyArgs (vg ms) vl args name_args) >>= 
                (fun newLocal => (runStmt fuel' ms newLocal found_body) >>=
                    (fun '(msmid, vlmid) => match ret, found_ret with
                        | Some s_ret, Some s_found_ret => (interp (Var s_found_ret) vlmid) >>=
                            fun r => match runStmt fuel' msmid vl (assignmentStmt s_ret (Const r)) with
                                | Some (ms2, vl2) => Some (ms2, vl2)
                                | None => Some (msmid, vl $+ (s_ret, varAss r))
                                end
                        (*Assigning void to a var*)
                        | Some _, None => None
                        (*Not reading the return of a non-void func*)
                        | None, _ => Some (msmid, vl)
                        end
                    )
                )
            | _ => None
            end
        (*Check for callback (if exists, call this function with args of signal), then check for awaiting bodies (if exist, run them then resume)*)
        | emitSignalStmt sig_name opt_callback args => match opt_callback with
            | Some (f, _n) => (runStmt fuel' ms vl (assignCallMethodStmt None f args)) >>=
                (fun '(msmid, vlmid) => match (sig_state msmid) $F? sig_name with
                    | nil => Some (msmid, vlmid)
                    (*Run every waiting body in order*)
                    | l => fold_left
                        (fun (acc : option (mono_state * valuation)) (w : waiting) =>
                            match acc, w with
                            | Some (ms_acc, vl_acc), waitAss _ body =>
                                (runStmt fuel' {| vg := vg ms_acc; sig_state := sig_state ms_acc $F- sig_name |} $0 body) >>=
                                    (fun '(ms2, _vl2) => Some (ms2, vl_acc))
                            | None, _ => None
                            end)
                        l (Some (msmid, vlmid))
                    end)
            | None => match (sig_state ms) $F? sig_name with
                | nil => Some (ms, vl)
                | l => fold_left
                        (fun (acc : option (mono_state * valuation)) (w : waiting) =>
                            match acc, w with
                            | Some (ms_acc, vl_acc), waitAss _ body =>
                                (runStmt fuel' {| vg := vg ms_acc; sig_state := sig_state ms_acc $F- sig_name |} $0 body) >>=
                                    (fun '(ms2, _vl2) => Some (ms2, vl_acc))
                            | None, _ => None
                            end)
                        l (Some (ms, vl))
                end
            end
        | skip => Some (ms, vl)
        end
    end.

Arguments runStmt _ _ _ _ : simpl never.


Definition stmtFuel := 20. (*NB: This value should be big enough to run every statement we use in proofs. Otherwise increase it*)


(*NB: This function assumes the input program has its (optional) process function defined at the end. 
runDual fixes this assumption. It would be relatively easy to fix here as well but we didn't do it because runDual with EndDecl as program 2 
is already equivalent to this fixpoint*)
Fixpoint run (fuel: nat) (ms: mono_state) (d: topLevelDecl) : option mono_state :=
    match fuel with
    | O => None
    | S fuel' =>
        match d with
        (*Same as for runStmt*)
        | classVarDecl name e => match vg ms $? name with
            | Some _ => None
            | None => interp2 e (vg ms) $0 >>=
                (fun n => Some ({|vg := (vg ms) $+ (name, varAss n); sig_state := sig_state ms|}))
            end
        (*Just add method to valuation*)
        | methodDecl name args ret body => Some ({|vg := (vg ms) $+ (name, methodAss args ret body); sig_state := sig_state ms|})
        (*Run the ready func once*)
        | readyDecl body => (runStmt stmtFuel ms ($0) body) >>=
            (fun '(ms2, vl2) => Some ms2)
        (*Run until no fuel remaining*)
        | processDecl body => if (Nat.eqb fuel' 1) then Some ms else (runStmt stmtFuel ms $0 body) >>=
            (fun '(msmid, vlmid) => run fuel' msmid d)
        (*Run d1 then d2*)
        | SequenceDecl d1 d2 => (run fuel' ms d1) >>=
            (fun vmid => run fuel' vmid d2)
        | EndDecl => Some ms
        end
    end.

Arguments run _ _ _  : simpl never.

Record dual_state := {
  current : nat; (*Context we are in, defining which global valuation to read and update*)
  signal_state : waitings; (*Map from signal name to list of awaiting bodies and their context*)
  vgA : valuation; (*Global valuation of the first program*)
  vgB: valuation; (*Global valuation of the second program*)
}.

Definition set_current (n : nat) (ds : dual_state) : dual_state :=
  {| current := n;
     signal_state := signal_state ds;
     vgA := vgA ds;
     vgB := vgB ds |}.


Fixpoint runStmtDual (fuel: nat) (ds: dual_state) (vl: valuation) (st: stmt) : option((dual_state) * valuation) :=
    match fuel with
    | O => None
    | S fuel' => match current ds with
        | 1 => match st with
            (*if not already defined, interp expression, then assign it in local val*)
            | varDeclStmt name e => match (vl $? name) with
                | Some _ => None (*If name already defined in local, crash*)
                | None => (interp2 e (vgA ds) vl) >>=
                    (fun n => Some (ds, vl $+ (name, varAss n)))
                end
             (* If expr is >= 1 then run s1 else if expr is 0 then run s2 else crash *)
            | ifStmt e s1 s2 => match interp2 e (vgA ds) vl with
                | Some 0 => runStmtDual fuel' ds vl s2
                | Some _n => runStmtDual fuel' ds vl s1
                | None => None
                end
            (* While e <> 0, run s, else skip *)
            | whileStmt e s => match interp2 e (vgA ds) vl with
                | Some 0 => Some (ds, vl)
                | Some _n => (runStmtDual fuel' ds vl s) >>=
                    (fun '(dsmid, vlmid) => runStmtDual fuel' dsmid vlmid st)
                | None => None
                end
            (*If name defined in local, reassign it with value of e, else do the same for global, else crash *)
            | assignmentStmt name e => match vl $? name with
                | Some _ => (interp2 e (vgA ds) vl) >>=
                    (fun n => Some (ds, vl $+ (name, varAss n)))
                | None => ((vgA ds) $? name) >>= 
                    (fun _ => interp2 e (vgA ds) vl >>=
                        (fun n => Some (({| current := current ds; signal_state := signal_state ds; vgA := (vgA ds) $+ (name, varAss n); vgB := vgB ds |}), vl)))
                end
            (*Skip, await is checked in sequence, because await as last instruction does nothing anyways*)
            | await sig_name => Some (ds, vl)
            (*If s1 is await:
                add (waiting s2) to global valuation then skip, 
             else just run s1 then s2*)
            | sequence s1 s2 => match s1 with
                | awaitStmt sig_name => Some ({| current := current ds; signal_state := signal_state ds $F+ (sig_name, waitAss 1 s2); vgA := vgA ds; vgB := vgB ds |}, vl)
                | _ => (runStmtDual fuel' ds vl s1) >>=
                    (fun '(dsmid, vlmid) => runStmtDual fuel' dsmid vlmid s2)
                end
            (*Get method, match arguments to parameters. If we want to assign the return value, read it in the local var of the executed func, then assign it*)
            | assignCallMethodStmt ret method_name args => match (vgA ds) $? method_name with
                | Some (methodAss name_args found_ret found_body) => unifyArgs (vgA ds) vl args name_args >>=
                    (fun newLocal => (runStmtDual fuel' ds newLocal found_body) >>=
                        (fun '(dsmid, vlmid) => match ret, found_ret with
                            | Some s_ret, Some s_found_ret => (interp (Var s_found_ret) vlmid) >>=
                                (fun r => match runStmtDual fuel' dsmid vl (assignmentStmt s_ret (Const r)) with
                                    | Some (ds2, vl2) => Some (ds2, vl2)
                                    | None => Some (dsmid, vl $+ (s_ret, varAss r))
                                    end)
                            (*Assigning void to a var*)
                            | Some _, None => None
                            (*Not reading the return of a non-void func*)
                            | None, _ => Some (dsmid, vl)
                            end
                        )
                    )
                | _ => None
                end
            (*Check for callback (if exists, call this function with args of signal in the correct context),
             then check for awaiting bodies (if exist, run them in the correct context then resume)*)
            | emitSignalStmt sig_name opt_callback args => match opt_callback with
            (*Context switch if n = 2*)
                | Some (f, 1) => (evalArgs (vgA ds) vl args) >>=
                    (fun newArgs => (runStmtDual fuel' ds vl (assignCallMethodStmt None f newArgs)) >>=
                        (*Check for waiting bodies*)
                        (fun '(dsmid, vlmid) => match (signal_state dsmid) $F? sig_name with
                            | nil => Some (dsmid, vlmid)
                            | l => fold_left
                                (fun (acc : option (dual_state * valuation)) (w : waiting) =>
                                    match acc, w with
                                    | Some (ds_acc, vl_acc), waitAss 1 body =>
                                        (runStmtDual fuel' {| current := 1; signal_state := signal_state ds_acc $F- sig_name; vgA := vgA ds_acc; vgB := vgB ds_acc |} $0 body) >>=
                                            (fun '(ds2, _vl2) => Some (set_current 1 ds2, vl_acc))
                                    | Some (ds_acc, vl_acc), waitAss 2 body =>
                                        (runStmtDual fuel' {| current := 2; signal_state := signal_state ds_acc $F- sig_name; vgA := vgA ds_acc; vgB := vgB ds_acc |} $0 body) >>=
                                            (fun '(ds2, _vl2) => Some (set_current 1 ds2, vl_acc))
                                    | _, _ => None
                                    end)
                                l (Some (dsmid, vlmid))
                            end
                        )
                    )
                | Some (f, 2) => (evalArgs (vgA ds) vl args) >>=
                    (fun newArgs => (runStmtDual fuel' (set_current 2 ds) vl (assignCallMethodStmt None f newArgs)) >>=
                        (fun '(dsmid, vlmid) => match (signal_state dsmid) $F? sig_name with
                            (*Switch back if no waiting*)
                            | nil => Some (set_current 1 dsmid, vlmid)
                            | l => fold_left
                                (fun (acc : option (dual_state * valuation)) (w : waiting) =>
                                    match acc, w with
                                    | Some (ds_acc, vl_acc), waitAss 1 body =>
                                        (runStmtDual fuel' {| current := 1; signal_state := signal_state ds_acc $F- sig_name; vgA := vgA ds_acc; vgB := vgB ds_acc |} $0 body) >>=
                                            (fun '(ds2, _vl2) => Some (set_current 1 ds2, vl_acc))
                                    | Some (ds_acc, vl_acc), waitAss 2 body =>
                                        (runStmtDual fuel' {| current := 2; signal_state := signal_state ds_acc $F- sig_name; vgA := vgA ds_acc; vgB := vgB ds_acc |} $0 body) >>=
                                            (fun '(ds2, _vl2) => Some (set_current 1 ds2, vl_acc))
                                    | _, _ => None
                                    end)
                                l (Some (set_current 1 dsmid, vlmid))
                            end
                        )
                    )
                | None => match (signal_state ds) $F? sig_name with
                    | nil => Some (ds, vl)
                    | l => fold_left
                        (fun (acc : option (dual_state * valuation)) (w : waiting) =>
                            match acc, w with
                            | Some (ds_acc, vl_acc), waitAss 1 body =>
                                (runStmtDual fuel' {| current := 1; signal_state := signal_state ds_acc $F- sig_name; vgA := vgA ds_acc; vgB := vgB ds_acc |} $0 body) >>=
                                    (fun '(ds2, _vl2) => Some (set_current 1 ds2, vl_acc))
                            | Some (ds_acc, vl_acc), waitAss 2 body =>
                                (runStmtDual fuel' {| current := 2; signal_state := signal_state ds_acc $F- sig_name; vgA := vgA ds_acc; vgB := vgB ds_acc |} $0 body) >>=
                                    (fun '(ds2, _vl2) => Some (set_current 1 ds2, vl_acc))
                            | _, _ => None
                            end)
                        l (Some (ds, vl))
                    end
                | _ => None
                end
            | skip => Some (ds, vl)
            end
        | 2 => match st with
            | varDeclStmt name e => match (vl $? name) with
                | Some _ => None (*If name already defined in local, crash*)
                | None => (interp2 e (vgB ds) vl) >>=
                    (fun n => Some (ds, vl $+ (name, varAss n)))
                end
            | ifStmt e s1 s2 => match interp2 e (vgB ds) vl with
                | Some 0 => runStmtDual fuel' ds vl s2
                | Some _n => runStmtDual fuel' ds vl s1
                | None => None
                end
            | whileStmt e s => match interp2 e (vgB ds) vl with
                | Some 0 => Some (ds, vl)
                | Some _n => (runStmtDual fuel' ds vl s) >>=
                    (fun '(dsmid, vlmid) => runStmtDual fuel' dsmid vlmid st)
                | None => None
                end
            | assignmentStmt name e => match vl $? name with
                | Some _ => (interp2 e (vgB ds) vl) >>=
                    (fun n => Some (ds, vl $+ (name, varAss n)))
                | None => ((vgB ds) $? name) >>= 
                    (fun _ => (interp2 e (vgB ds) vl) >>=
                        (fun n => Some ({|current := current ds; signal_state := signal_state ds; vgA := vgA ds; vgB := (vgB ds $+ (name, varAss n)) |}, vl))
                    )
                end
            | await sig_name => Some (ds, vl)
            | sequence s1 s2 => match s1 with
                | awaitStmt sig_name => Some ({|current := current ds; signal_state := signal_state ds $F+ (sig_name, waitAss 2 s2); vgA := vgA ds; vgB := vgB ds |}, vl)
                | _ => (runStmtDual fuel' ds vl s1) >>=
                    (fun '(dsmid, vlmid) => runStmtDual fuel' dsmid vlmid s2)
                end
            | assignCallMethodStmt ret method_name args => match (vgB ds) $? method_name with
                | Some (methodAss name_args found_ret found_body) => (unifyArgs (vgB ds) vl args name_args) >>=
                    (fun newLocal => (runStmtDual fuel' ds newLocal found_body) >>=
                        (fun '(dsmid, vlmid) => match ret, found_ret with
                            | Some s_ret, Some s_found_ret => (interp (Var s_found_ret) vlmid) >>=
                                (fun r => match runStmtDual fuel' dsmid vl (assignmentStmt s_ret (Const r)) with
                                    | Some (dsmid2, vl2) => Some (dsmid2, vl2)
                                    | None => Some (dsmid, vl $+ (s_ret, varAss r))
                                    end
                                )
                            (*Assigning void to a var*)
                            | Some _, None => None
                            (*Not reading the return of a non-void func*)
                            | None, _ => Some (dsmid, vl)
                            end
                        )
                    )
                | _ => None
                end
            | emitSignalStmt sig_name opt_callback args => match opt_callback with
            (*Context switch if n = 1*)
                | Some (f, 1) => (evalArgs (vgB ds) vl args) >>=
                    (fun newArgs => (runStmtDual fuel' (set_current 1 ds) vl (assignCallMethodStmt None f newArgs)) >>=
                        (fun '(dsmid, vlimd) => match (signal_state dsmid) $F? sig_name with
                            | nil => Some (set_current 2 dsmid, vlimd)
                            | l => fold_left
                                (fun (acc : option (dual_state * valuation)) (w : waiting) =>
                                    match acc, w with
                                    | Some (ds_acc, vl_acc), waitAss 1 body =>
                                        (runStmtDual fuel' {| current := 1; signal_state := signal_state ds_acc $F- sig_name; vgA := vgA ds_acc; vgB := vgB ds_acc |} $0 body) >>=
                                            (fun '(ds2, _vl2) => Some (set_current 2 ds2, vl_acc))
                                    | Some (ds_acc, vl_acc), waitAss 2 body =>
                                        (runStmtDual fuel' {| current := 2; signal_state := signal_state ds_acc $F- sig_name; vgA := vgA ds_acc; vgB := vgB ds_acc |} $0 body) >>=
                                            (fun '(ds2, _vl2) => Some (set_current 2 ds2, vl_acc))
                                    | _, _ => None
                                    end)
                                l (Some (set_current 2 dsmid, vlimd))
                            end
                        )
                    )
                | Some (f, 2) => (evalArgs (vgB ds) vl args) >>=
                    (fun newArgs => (runStmtDual fuel' ds vl (assignCallMethodStmt None f newArgs)) >>=
                        (fun '(dsmid, vlimd) => match (signal_state dsmid) $F? sig_name with
                            | nil => Some (dsmid, vlimd)
                            | l => fold_left
                                (fun (acc : option (dual_state * valuation)) (w : waiting) =>
                                    match acc, w with
                                    | Some (ds_acc, vl_acc), waitAss 1 body =>
                                        (runStmtDual fuel' {| current := 1; signal_state := signal_state ds_acc $F- sig_name; vgA := vgA ds_acc; vgB := vgB ds_acc |} $0 body) >>=
                                            (fun '(ds2, _vl2) => Some (set_current 2 ds2, vl_acc))
                                    | Some (ds_acc, vl_acc), waitAss 2 body =>
                                        (runStmtDual fuel' {| current := 2; signal_state := signal_state ds_acc $F- sig_name; vgA := vgA ds_acc; vgB := vgB ds_acc |} $0 body) >>=
                                            (fun '(ds2, _vl2) => Some (set_current 2 ds2, vl_acc))
                                    | _, _ => None
                                    end)
                                l (Some (dsmid, vlimd))
                            end
                        )
                    )
                | None => match (signal_state ds) $F? sig_name with
                    | nil => Some (ds, vl)
                    | l => fold_left
                        (fun (acc : option (dual_state * valuation)) (w : waiting) =>
                            match acc, w with
                            | Some (ds_acc, vl_acc), waitAss 1 body =>
                                (runStmtDual fuel' {| current := 1; signal_state := signal_state ds_acc $F- sig_name; vgA := vgA ds_acc; vgB := vgB ds_acc |} $0 body) >>=
                                    (fun '(ds2, _vl2) => Some (set_current 2 ds2, vl_acc))
                            | Some (ds_acc, vl_acc), waitAss 2 body =>
                                (runStmtDual fuel' {| current := 2; signal_state := signal_state ds_acc $F- sig_name; vgA := vgA ds_acc; vgB := vgB ds_acc |} $0 body) >>=
                                    (fun '(ds2, _vl2) => Some (set_current 2 ds2, vl_acc))
                            | _, _ => None
                            end)
                        l (Some (ds, vl))
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
            | classVarDecl name e => match vgA ds $? name with
                | Some _ => None (*If name already defined in global, crash*)
                | None => (interp e (vgA ds)) >>=
                    (fun n => Some ({|current := 1; signal_state := signal_state ds; vgA := vgA ds $+ (name, varAss n); vgB := vgB ds |}, None))
                end
            | methodDecl name args ret body => Some ({|current := 1; signal_state := signal_state ds; vgA := vgA ds $+ (name, methodAss args ret body); vgB := vgB ds |}, None)
            | readyDecl body => (runStmtDual stmtFuel ds $0 body) >>=
                (fun '(ds2, vl2) => Some (ds2, None))
            (*Return body of the process*)
            | processDecl body => Some (ds, Some body)
            | SequenceDecl d1 d2 => (initProg fuel' ds d1) >>=
                (fun '(dsA, pA) => (initProg fuel' dsA d2) >>=
                    (fun '(dsB, pB) => Some (dsB, match pA with
                        | Some bodyA => Some bodyA
                        | None => pB
                        end)
                    )
                )
            | EndDecl => Some (ds, None)
            end
        | 2 => match d with
            | classVarDecl name e => match vgB ds $? name with
                | Some _ => None (*If name already defined in global, crash*)
                | None => (interp e (vgB ds)) >>=
                    (fun n => Some ({|current := 2; signal_state := signal_state ds; vgA := vgA ds; vgB := vgB ds $+ (name, varAss n) |}, None))
                end
            | methodDecl name args ret body => Some ({|current := 2; signal_state := signal_state ds; vgA := vgA ds; vgB := vgB ds $+ (name, methodAss args ret body) |}, None)
            | readyDecl body => (runStmtDual stmtFuel ds $0 body) >>=
                (fun '(ds2, vl2) => Some (ds2, None))
            | processDecl body => Some (ds, Some body)
            (*Return the final valuation after initialization and the body of the process if any*)
            | SequenceDecl d1 d2 => (initProg fuel' ds d1) >>=
                (fun '(dsA, pA) => (initProg fuel' dsA d2) >>=
                    (fun '(dsB, pB) => Some (dsB, match pA with
                        | Some bodyA => Some bodyA
                        | None => pB
                        end)
                    )
                )
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
        | Some bodyA, Some bodyB => (runStmtDual stmtFuel ds $0 bodyA) >>=
            (fun '(dsmid, _vlmid) => (runStmtDual stmtFuel (set_current 2 dsmid) $0 bodyB) >>=
                (fun '(ds2, _vl2) => runProcessesDual fuel' (set_current 1 ds2) (Some bodyA) (Some bodyB))
            )
        (*If one process is None but the other isn't, we still want to run the other process until no fuel left*)
        | Some bodyA, None => (runStmtDual stmtFuel ds $0 bodyA) >>=
            (fun '(ds2, vl2) => runProcessesDual fuel' (set_current 1 ds2) (Some bodyA) None)
        | None, Some bodyB => (runStmtDual stmtFuel (set_current 2 ds) $0 bodyB) >>=
            (fun '(ds2, vl2) => runProcessesDual fuel' (set_current 1 ds2) None (Some bodyB))
        (*If no processes, done*)
        | None, None => Some ds
        end
    end.

Arguments runProcessesDual _ _ _ _ : simpl never.

Definition runDual (fuel: nat) (ds : dual_state) (d: topLevelDecl * topLevelDecl) : option (dual_state) :=
    (initProg fuel ds (fst d)) >>=
        (fun '(dsA, pA) => (initProg fuel (set_current 2 dsA) (snd d)) >>=
            (fun '(dsB, pB) => runProcessesDual fuel (set_current 1 dsB) pA pB)
        ).

Arguments runDual _ _ _ : simpl never.