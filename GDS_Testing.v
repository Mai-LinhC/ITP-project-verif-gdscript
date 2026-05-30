Require Import CompMap.
Require Import GDS_Language. 
From Stdlib Require Import String.
From Stdlib Require Import List.
Open Scope string_scope.
Open Scope expr.


Ltac prover := vm_compute; repeat eexists; repeat split; reflexivity.

Definition defaultStateMono : mono_state := {|vg := $0; sig_state := nil|}.


(*Using variable definitions and binary operations*)
Theorem runStmtVar :    
    exists ms2 vl2, 
    runStmt 10 defaultStateMono $0 
    ((var "a" := Const 2) ;; (var "b" := Const 3) ;; 
    (var "ret" := ((Var "a") + (Var "b"))) ;; skip) = Some (ms2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 5)).
Proof.
    prover.
Qed.


Theorem runStmtIf :
    exists ms2 vl2, 
    (runStmt 4 defaultStateMono $0 
    ((( (var "a" := Const 2 ;; var "b" := Const 3) ;; 
    when ((Var "b") - (Var "a")) 
    then (var "ret" := Const 10) 
    else (var "ret" := Const 5) done) ) ;; 
    skip)) = Some (ms2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


Theorem runStmtWhile :
    exists ms2 vl2, 
    (runStmt 10 defaultStateMono $0 
    ((((var "a" := Const 2 ;; while (Var "a") loop ("a" <- Var "a" - Const 1) done) ;; 
    var "ret" := Var "a" + Const 5) ;; skip))) = Some (ms2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 5)).
Proof.
    prover.
Qed.


Theorem runCall :
    exists ms2, (run 5 defaultStateMono 
    ((((topVar "a" := Const 9 ;;; topVar "ret" := Const 0 ) ;;;
    methodDecl "plusOne" nil (Some "dump")  (var "dump" := (Var "a" + Const 1))) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil)) ;;; EndDecl)) = Some ms2 
    /\ (vg ms2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


Theorem runCallShadowing :
    exists ms2, (run 6 defaultStateMono 
    (((topVar "a" := Const 3 ;;; topVar "ret" := Const 0 ) ;;;
    methodDecl "plusOne" nil (Some "dump") (var "a" := Const 9 ;; var "dump" := (Var "a" + Const 1))) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil) ;;; EndDecl)) = Some ms2 
    /\ ((vg ms2 $? "ret" = Some (varAss 10))  /\ (vg ms2 $? "a" = Some (varAss 3))).
Proof.
    prover.
Qed.


(*New example existential_matching assignations*)
Theorem SimpleAssign :
    exists ms2, (run 6 defaultStateMono 
    ((topVar "a" := Const 3) ;;;
    readyDecl ("a" <- Const 8 ;; skip) ;;; EndDecl)) = Some ms2 
    /\ ((vg ms2 $? "a" = Some (varAss 8))).
Proof.
    prover.
Qed.



Theorem runProcess :
    exists ms2, (run 15 defaultStateMono (
       (topVar "ret" := Const 0 ;;; processDecl(
        ((var "a" := Const 10 ;; "ret" <- Var "a") ;; skip)) ;;; 
        EndDecl) 
    )) = Some ms2
    /\ (vg ms2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


Theorem runSignal :
     exists ms2, run 15 defaultStateMono ( 
        topVar "a" := Const 0 ;;; topVar "ret" := Const 0 ;;;
        readyDecl("a" <- Const 1) ;;;
        processDecl( "a" <- Var "a" + Const 1 ;; 
        when (Var "a" == Const 3)
        then (emitSignalStmt "sig" None nil)
        else (awaitStmt "sig" ;; "ret" <- Const 10)
        done)
     ) = Some ms2
    /\ (vg ms2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


Theorem runSignalCallback :
    exists ms2, run 5 defaultStateMono (
        (topVar "ret" := Const 0 ;;; methodDecl "callback" ("a"::"b"::nil) None ("ret" <- Var "b")) ;;;
        readyDecl(emitSignalStmt "sig" (Some ("callback", 1)) (Const 5 :: Const 10 :: nil))
    ) = Some ms2 
    /\ (vg ms2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


Theorem doubleAwaitMono :
    exists ms2, run 20 defaultStateMono (
        (topVar "a" := Const 0 ;;; topVar "ret" := Const 3 ;;; topVar "ret2" := Const 1 ;;;
        readyDecl (awaitStmt "sig" ;; "ret" <- Const 10 ;; awaitStmt "sig" ;; "ret2" <- Const 5) ;;; 
        processDecl( "a" <- Var "a" + Const 1 ;; 
        when (Var "a" == Const 2)
        then (emitSignalStmt "sig" None nil)
        else (when (Var "a" == Const 5)
        then (emitSignalStmt "sig" None nil)
        else skip done)
        done);;; EndDecl)
    ) = Some ms2
    /\ (vg ms2 $? "ret" = Some (varAss 10)) /\ (vg ms2 $? "ret2" = Some (varAss 5)).
Proof.
    prover.
Qed.


Theorem awaitInProcess : 
    exists ms2, run 20 defaultStateMono (
        (topVar "a" := Const 0 ;;; topVar "b" := Const 0 ;;;
        processDecl( "b" <- Var "b" + Const 1 ;; 
        when (Var "b" == Const 4)
        then (emitSignalStmt "sig" None nil)
        else (awaitStmt "sig" ;; "a" <- Var "a" + Const 1)
        done);;; EndDecl)
    ) = Some ms2
    /\ (vg ms2 $? "a" = Some (varAss 3)).
    Proof.
        prover.
    Qed.



(*STARTING DUALS*)

Definition defaultVal: dual_state := {|current := 1; signal_state := nil; vgA := $0; vgB := $0|}.

Theorem runStmtDualVar :    
    exists ds2 vl2, 
    runStmtDual 10 defaultVal $0 
    ((var "a" := Const 2) ;; (var "b" := Const 3) ;; 
    (var "ret" := ((Var "a") + (Var "b"))) ;; skip) = Some (ds2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 5)).
Proof.
    prover.
Qed.


Theorem runStmtDualIf :
    exists ds2 vl2, 
    (runStmtDual 4 defaultVal $0 
    ((( (var "a" := Const 2 ;; var "b" := Const 3) ;; 
    when ((Var "b") - (Var "a")) 
    then (var "ret" := Const 10) 
    else (var "ret" := Const 5) done) ) ;; 
    skip)) = Some (ds2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


Theorem runStmtDualWhile :
    exists ds2 vl2, 
    (runStmtDual 6 defaultVal $0 
    ((((var "a" := Const 2 ;; while (Var "a") loop ("a" <- Var "a" - Const 1) done) ;; 
    var "ret" := Var "a" + Const 5) ;; skip))) = Some (ds2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 5)).
Proof.
    prover.
Qed.


Definition dA1 := (topVar "a" := Const 9 ;;; topVar "ret" := Const 0 ;;;
    methodDecl "plusOne" nil (Some "dump")  (var "dump" := (Var "a" + Const 1)) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil) ;;; EndDecl).


Definition dB1 := (topVar "a" := Const 3 ;;; topVar "ret" := Const 0 ;;;
    methodDecl "plusOne" nil (Some "dump")  (var "dump" := (Var "a" + Const 1));;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil) ;;; EndDecl).


(*Non interacting programs don't overlap even with duplicate names*)
Theorem RunDualProgsNoOverlap :
    exists ds2, (runDual 11 defaultVal (dA1, dB1)
    ) = Some ds2 
    /\ (vgA ds2 $? "ret" = Some (varAss 10)) /\ (vgB ds2 $? "ret" = Some (varAss 4)).
Proof.
    prover.
Qed.


Definition dA2 := (topVar "ret" := Const 3 ;;;
    readyDecl (awaitStmt "sigB" ;; "ret" <- Const 10) ;;; 
    EndDecl).

Definition dB2 := readyDecl (emitSignalStmt "sigB" None nil) ;;; EndDecl.


(*Awaiting a signal in another node*)
Theorem RunDualSimpleAwait :
    exists ds2, (runDual 10 defaultVal (dA2, dB2)
    ) = Some ds2 
    /\ (vgA ds2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


Definition dA3 := (topVar "ret" := Const 3 ;;; 
    methodDecl "func" ("a" :: nil) None ("ret" <- Var "a") ;;;
    readyDecl (awaitStmt "sigB" ;; "ret" <- (Var "ret") + Const 1) ;;; 
    EndDecl).

Definition dB3 := readyDecl (emitSignalStmt "sigB" (Some ("func", 1)) (Const 8 :: nil)) ;;; EndDecl.


(*Context switch for callback and waiting*)
Theorem RunDualEmitSignalCallbackAndAwait1 :
    exists ds2, (runDual 10 defaultVal (dA3, dB3)
    ) = Some ds2 
    /\ (vgA ds2 $? "ret" = Some (varAss 9)).
Proof.
    prover.
Qed.


Definition dA3' := (topVar "ret" := Const 3 ;;; 
    methodDecl "func" ("a" :: nil) None ("ret" <- Var "a") ;;;
    EndDecl).

Definition dB3' := (topVar "ret" := Const 0 ;;; 
    readyDecl (awaitStmt "sigB" ;; "ret" <- Const 10) ;;; 
    processDecl (emitSignalStmt "sigB" (Some ("func", 1)) (Const 8 :: nil)) ;;; 
    EndDecl).


(*Context switch for callback but not await*)
Theorem RunDualEmitSignalCallbackAndAwait2 :
    exists ds2, (runDual 10 defaultVal (dA3', dB3')
    ) = Some ds2 
    /\ (vgA ds2 $? "ret" = Some (varAss 8)) /\ (vgB ds2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.

Definition dA3'' := (topVar "ret" := Const 3 ;;; 
    methodDecl "func" ("a" :: nil) None ("ret" <- Var "a") ;;;
    processDecl (emitSignalStmt "sigA" (Some ("func", 1)) (Const 8 :: nil)) ;;; 
    EndDecl).

Definition dB3'' := (topVar "ret" := Const 0 ;;; 
    readyDecl (awaitStmt "sigA" ;; "ret" <- Const 10) ;;; 
    EndDecl).



(*Context switch for await but not callback*)
Theorem RunDualEmitSignalCallbackAndAwait3 :
    exists ds2, (runDual 10 defaultVal (dA3'', dB3'')
    ) = Some ds2 
    /\ (vgA ds2 $? "ret" = Some (varAss 8)) /\ (vgB ds2 $? "ret" = Some (varAss 10)).
Proof. 
    prover.
Qed.



(*Next: One program awaits the other, ret should be 10 if the signal is received after the first program has done two loops*)

Definition dA4 := (topVar "a" := Const 0 ;;; topVar "ret" := Const 3 ;;;
    readyDecl (awaitStmt "sigB" ;; "ret" <- Const 10) ;;; 
    processDecl( "a" <- Var "a" + Const 1 ;; 
        when (Var "a" == Const 2)
        then ("ret" <- Const 5)
        else (skip)
        done);;; EndDecl).

Definition dB4 := (topVar "a" := Const 0 ;;;
    processDecl( "a" <- Var "a" + Const 1 ;; 
        when (Var "a" == Const 4)
        then (emitSignalStmt "sigB" None nil)
        else (skip)
        done);;; EndDecl).


(*When running alone, the first program does set ret to 5*)
Lemma RunMonoAwaitForever :
    exists ms2, (run 20 defaultStateMono dA4) = Some ms2 /\ vg ms2 $? "ret" = Some (varAss 5).
Proof.
    prover.
Qed.


(*This theorem is pretty strong to show the execution order*)
Theorem RunDualProgsAwait :
    exists ds2, (runDual 14 defaultVal (dA4, dB4)
    ) = Some ds2 
    /\ (vgA ds2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


(*Now having B wait for A to check the symmetry*)

Definition dA5 := (topVar "a" := Const 0 ;;;
    processDecl( "a" <- Var "a" + Const 1 ;; 
        when (Var "a" == Const 3)
        then (emitSignalStmt "sigA" None nil)
        else (skip)
        done);;; EndDecl).

Definition dB5 := (topVar "a" := Const 0 ;;; topVar "ret" := Const 3 ;;;
    readyDecl (awaitStmt "sigA" ;; "ret" <- Const 10) ;;; 
    processDecl( "a" <- Var "a" + Const 1) ;;; EndDecl).

Theorem RunDualProgsAwaitSymmetric :
    exists ds2, (runDual 14 defaultVal (dA5, dB5)
    ) = Some ds2 
    /\ (vgB ds2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


(*B awaits A, a emits signal and has callback to function of B*)
Definition dA6 := (topVar "a" := Const 0 ;;;
    processDecl( "a" <- Var "a" + Const 1 ;; 
        when (Var "a" == Const 3)
        then (emitSignalStmt "sigA" (Some ("func", 2)) (Const 8 :: nil))
        else (skip)
        done);;; EndDecl).

Definition dB6 := (topVar "a" := Const 0 ;;; topVar "ret" := Const 3 ;;;
    methodDecl "func" ("x" :: nil) None ("a" <- Var "x") ;;;
    readyDecl (awaitStmt "sigA" ;; "ret" <- Const 10)
    ;;; EndDecl).

Theorem RunDualProgsAwaitSymmetricCallback :
    exists ds2, (runDual 14 defaultVal (dA6, dB6)
    ) = Some ds2 
    /\ (vgB ds2 $? "ret" = Some (varAss 10)) /\ (vgB ds2 $? "a" = Some (varAss 8)).
Proof.
    prover.
Qed.


(*Double await*)

Definition dA7 := (topVar "a" := Const 0 ;;;
    processDecl( "a" <- Var "a" + Const 1 ;; 
        when (Var "a" == Const 3)
        then (emitSignalStmt "sigA" None nil)
        else (when (Var "a" == Const 5)
        then (emitSignalStmt "sigA" None nil)
        else skip done)
        done);;; EndDecl).

Definition dB7 := (topVar "a" := Const 0 ;;; topVar "ret" := Const 3 ;;;
    readyDecl (awaitStmt "sigA" ;; "ret" <- Const 10 ;; awaitStmt "sigA" ;; "a" <- Const 15 ;; skip) ;;; EndDecl).


Theorem RunDualProgsDoubleAwait :
    exists ds2, (runDual 10 defaultVal (dA7, dB7)
    ) = Some ds2 
    /\ (vgB ds2 $? "ret" = Some (varAss 10)) /\ (vgB ds2 $? "a" = Some (varAss 15)).
Proof.
    prover.
Qed.


Definition dA3OOO := (
    processDecl (emitSignalStmt "sigA" (Some ("func", 1)) (Const 8 :: nil)) ;;;
    topVar "ret" := Const 3 ;;; 
    methodDecl "func" ("a" :: nil) None ("ret" <- Var "a") ;;; 
    EndDecl).

Definition dB3OOO := (
    readyDecl (awaitStmt "sigA" ;; "ret" <- Const 10) ;;;
    topVar "ret" := Const 0 ;;; 
    EndDecl).

(*Process defined as first statement instead of at the end*)
Theorem OutOfOrderRunDualEmitSignalCallbackAndAwait3 :
    exists ds2, (runDual 10 defaultVal (dA3OOO, dB3OOO)
    ) = Some ds2 
    /\ (vgA ds2 $? "ret" = Some (varAss 8)) /\ (vgB ds2 $? "ret" = Some (varAss 10)).
Proof. 
    prover.
Qed.


(*Awaiting in both processes*)

Definition dA8 := (topVar "a" := Const 0 ;;; topVar "ret" := Const 0 ;;;
    processDecl( "a" <- Var "a" + Const 1 ;; 
        when (Var "a" == Const 3)
        then (emitSignalStmt "sigA" None nil)
        else (awaitStmt "sigB" ;; "ret" <- Var "ret" + Const 1)
        done);;; EndDecl).

Definition dB8 := (topVar "a" := Const 0 ;;; topVar "ret" := Const 0 ;;;
    processDecl( "a" <- Var "a" + Const 1 ;; 
        when (Var "a" == Const 4)
        then (emitSignalStmt "sigB" None nil)
        else (awaitStmt "sigA" ;; "ret" <- Var "ret" + Const 1)
        done);;; EndDecl).

Theorem RunDualProgsDoubleAwaitSymmetric :
    exists ds2, (runDual 20 defaultVal (dA8, dB8)
    ) = Some ds2 
    /\ (vgA ds2 $? "ret" = Some (varAss 3)) /\ (vgB ds2 $? "ret" = Some (varAss 2)).
Proof.
    prover.
Qed.


(*Example of real life program*)

(*Pseudo code:

Class Player
    var health = 11
    var dead = 0 (used as a boolean)

    func takeDamage(dmg: int) -> void :
        health -= dmg
        if health == 1:
            dead = 1


Class Enemy
    var strength = 2
    var counter = 0

    func hit(bonus: int) -> void :
        emit signal "hitPlayer" (callback: player.takeDamage(strentgh + bonus))
    
    func process() -> void:
        if counter == 2 or counter == 4:
            hit(counter)
        counter +=1
*)

Definition playerClass := (topVar "health" := Const 11 ;;; topVar "dead" := Const 0 ;;;
    methodDecl "takeDamage" ("dmg" :: nil) None 
        ("health" <- Var "health" - Var "dmg" ;; 
        when (Var "health" == Const 1) then ("dead" <- Const 1) else (skip) done))
        ;;; EndDecl.

Definition enemyClass := (topVar "strength" := Const 2 ;;; topVar "counter" := Const 0 ;;;
    methodDecl "hit" ("bonus" :: nil) None
    (emitSignalStmt "hitPlayer" (Some ("takeDamage", 1)) ((Var "strength" + Var "bonus") :: nil))) ;;;
    processDecl (when (Var "counter" == Const 2) then (assignCallMethodStmt None "hit" ((Var "counter"):: nil)) else 
    (when (Var "counter" == Const 4) then (assignCallMethodStmt None "hit" ((Var "counter"):: nil)) else skip done) done ;;
    "counter" <- Var "counter" + Const 1;; skip) ;;; EndDecl.


Definition testClass1 := (readyDecl (emitSignalStmt "test" (Some ("takeDamage", 1)) (Const 10 :: nil));;; EndDecl).

Lemma subTest1 : 
    exists ds2, runDual 10 defaultVal (playerClass, testClass1) = Some ds2
    /\ (vgA ds2 $? "health" = Some (varAss 1)) /\ (vgA ds2 $? "dead" = Some (varAss 1)).
Proof.
    prover.
Qed.

Definition testClass2 := (methodDecl "hit" nil None
(emitSignalStmt "hitPlayer" (Some ("takeDamage", 1)) ((Const 10) :: nil))) ;;;
(readyDecl (assignCallMethodStmt None "hit" nil);;; EndDecl).

Lemma subTest2 : 
    exists ds2, runDual 10 defaultVal (playerClass, testClass2) = Some ds2
    /\ (vgA ds2 $? "health" = Some (varAss 1)) /\ (vgA ds2 $? "dead" = Some (varAss 1)).
Proof.
    prover.
Qed.

Definition testClass3 := 
(methodDecl "hit" ("dmg" :: nil) None
    (emitSignalStmt "hitPlayer" (Some ("takeDamage", 1)) ((Var "dmg") :: nil))) ;;;
(readyDecl (assignCallMethodStmt None "hit" (Const 10 :: nil));;; EndDecl).


Lemma subTest3 : 
    exists ds2, runDual 10 defaultVal (playerClass, testClass3) = Some ds2
    /\ (vgA ds2 $? "health" = Some (varAss 1)) /\ (vgA ds2 $? "dead" = Some (varAss 1)).
Proof.
    prover.
Qed.


Definition testClass4 := topVar "strength" := Const 10 ;;;
(methodDecl "hit" ("dmg" :: nil) None
    (emitSignalStmt "hitPlayer" (Some ("takeDamage", 1)) ((Var "dmg") :: nil))) ;;;
readyDecl (assignCallMethodStmt None "hit" (Var "strength" :: nil));;; EndDecl.


Lemma subTest4 : 
    exists ds2, runDual 10 defaultVal (playerClass, testClass4) = Some ds2
    /\ (vgA ds2 $? "health" = Some (varAss 1)) /\ (vgA ds2 $? "dead" = Some (varAss 1)).
Proof. prover. Qed.


Definition testClass5 := (topVar "strength" := Const 8 ;;; topVar "counter" := Const 2 ;;;
    methodDecl "hit" ("dmg" :: nil) None
    (emitSignalStmt "hitPlayer" (Some ("takeDamage", 1)) ((Var "strength" + Var "dmg") :: nil))) ;;; 
    readyDecl (assignCallMethodStmt None "hit" ((Var "counter") :: nil));;; EndDecl.

Lemma subTest5 : 
    exists ds2, runDual 15 defaultVal (playerClass, testClass5) = Some ds2
    /\ (vgA ds2 $? "health" = Some (varAss 1)) /\ (vgA ds2 $? "dead" = Some (varAss 1)).
Proof. prover. Qed.


(*STRONGEST EXAMPLE YET*)
Theorem actualProgram :
    exists ds2, runDual 40 defaultVal (playerClass, enemyClass) = Some ds2
     /\ (vgA ds2 $? "health" = Some (varAss 1)) /\ (vgA ds2 $? "dead" = Some (varAss 1)).
Proof.
    prover.
Qed.


(*Tests that non-compiling programs return None*)

(*Declaring the same TopVar twice*)
Theorem NonCompilingProgram1 :
    run 10 defaultStateMono (topVar "a" := Const 0 ;;; topVar "a" := Const 1 ;;; EndDecl) = None.
    Proof.
        prover.
    Qed.

(*Declaring the same local var twice*)
Theorem NonCompilingProgram2 :
    run 10 defaultStateMono (topVar "a" := Const 0 ;;; readyDecl (var "a" := Const 1 ;; var "a" := Const 2) ;;; EndDecl) = None.
    Proof.
        prover.
    Qed.

(*Reassigning a non-existent variable*)
Theorem NonCompilingProgram3 :
    run 10 defaultStateMono (readyDecl ("b" <- Const 1) ;;; EndDecl) = None.
    Proof.
        prover.
    Qed.

(*Calling a method that is not declared*)
Theorem NonCompilingProgram4 :
    run 10 defaultStateMono (topVar "a" := Const 0 ;;; readyDecl (assignCallMethodStmt None "func" (Const 1 :: nil)) ;;; EndDecl) = None.
    Proof.
        prover.
    Qed.

(*Accessing a non-existent variable*)
Theorem NonCompilingProgram5 :
    run 10 defaultStateMono (topVar "a" := Const 0 ;;; topVar "b" := Var "x" ;;; EndDecl) = None.
    Proof.
        prover.
    Qed.