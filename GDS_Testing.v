Require Import CompMap.
Require Import GDS_Language. 
From Stdlib Require Import String.
Require Import List.
Open Scope string_scope.
Open Scope expr.


Ltac prover := try repeat eexists; try repeat split; cbv; try reflexivity.


Theorem runStmtVar :    
    exists vg2 vl2, 
    runStmt 10 $0 $0 
    ((var "a" := Const 2) ;; (var "b" := Const 3) ;; 
    (var "ret" := ((Var "a") + (Var "b"))) ;; skip) = Some (vg2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 5)).
Proof.
    prover.
Qed.


Theorem runStmtIf :
    exists vg2 vl2, 
    (runStmt 4 $0 $0 
    ((( (var "a" := Const 2 ;; var "b" := Const 3) ;; 
    when ((Var "b") - (Var "a")) 
    then (var "ret" := Const 10) 
    else (var "ret" := Const 5) done) ) ;; 
    skip)) = Some (vg2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


Theorem runStmtWhile :
    exists vg2 vl2, 
    (runStmt 10 $0 $0 
    ((((var "a" := Const 2 ;; while (Var "a") loop ("a" <- Var "a" - Const 1) done) ;; 
    var "ret" := Var "a" + Const 5) ;; skip))) = Some (vg2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 5)).
Proof.
    prover.
Qed.


Theorem globalExe1 :
    exists vg2, (run 5 $0 
    ((((topVar "a" := Const 9 ;;; topVar "ret" := Const 0 ) ;;;
    methodDecl "plusOne" nil (Some "dump")  (var "dump" := (Var "a" + Const 1))) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil)) ;;; EndDecl)) = Some vg2 
    /\ (vg2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


Theorem globalExe2 :
    exists vg2, (run 6 $0 
    (((topVar "a" := Const 3 ;;; topVar "ret" := Const 0 ) ;;;
    methodDecl "plusOne" nil (Some "dump") (var "a" := Const 9 ;; var "dump" := (Var "a" + Const 1))) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil) ;;; EndDecl)) = Some vg2 
    /\ ((vg2 $? "ret" = Some (varAss 10))  /\ (vg2 $? "a" = Some (varAss 3))).
Proof.
    prover.
Qed.


(*New example existential_matching assignations*)
Theorem globalExe3 :
    exists vg2, (run 6 $0 
    ((topVar "a" := Const 3) ;;;
    readyDecl ("a" <- Const 8 ;; skip) ;;; EndDecl)) = Some vg2 
    /\ ((vg2 $? "a" = Some (varAss 8))).
Proof.
    prover.
Qed.



Theorem runProcess :
    exists v2, (run 15 $0 (
       (topVar "ret" := Const 0 ;;; processDecl(
        ((var "a" := Const 10 ;; "ret" <- Var "a") ;; skip)) ;;; 
        EndDecl) 
    )) = Some v2
    /\ (v2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


(* Warning: la preuve suivante risque d’être particulièrement longue *)
(*Update, maintenant reflexivity prouve tout ptdr*)
Theorem runSignal :
     exists v2, run 15 $0 (  (* valeur de fuel choisie au pif, potentiellement ajuster pour que le théorème soit correct *)
        topVar "a" := Const 0 ;;; topVar "ret" := Const 0 ;;;
        readyDecl("a" <- Const 1) ;;;
        processDecl( "a" <- Var "a" + Const 1 ;; 
        when (Var "a" == Const 3)
        then (emitSignalStmt "sig" None nil)
        else (awaitStmt "sig" ;; "ret" <- Const 10)
        done)
     ) = Some v2 
    /\ (v2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


Theorem runSignalCallback :
    exists v2, run 5 $0 (
        (topVar "ret" := Const 0 ;;; methodDecl "callback" ("a"::"b"::nil) None ("ret" <- Var "b")) ;;;
        readyDecl(emitSignalStmt "sig" (Some ("callback", 1)) (Const 5 :: Const 10 :: nil))
    ) = Some v2 
    /\ (v2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.



(*STARTING DUALS*)

Definition defaultVal: valuation * valuation := ($0 $+ ("current", varAss 1), $0).

Theorem runStmtDualVar :    
    exists vg2 vl2, 
    runStmtDual 10 defaultVal $0 
    ((var "a" := Const 2) ;; (var "b" := Const 3) ;; 
    (var "ret" := ((Var "a") + (Var "b"))) ;; skip) = Some (vg2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 5)).
Proof.
    prover.
Qed.


Theorem runStmtDualIf :
    exists vg2 vl2, 
    (runStmtDual 4 defaultVal $0 
    ((( (var "a" := Const 2 ;; var "b" := Const 3) ;; 
    when ((Var "b") - (Var "a")) 
    then (var "ret" := Const 10) 
    else (var "ret" := Const 5) done) ) ;; 
    skip)) = Some (vg2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


Theorem runStmtDualWhile :
    exists vg2 vl2, 
    (runStmtDual 6 defaultVal $0 
    ((((var "a" := Const 2 ;; while (Var "a") loop ("a" <- Var "a" - Const 1) done) ;; 
    var "ret" := Var "a" + Const 5) ;; skip))) = Some (vg2, vl2)
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


Theorem RunDualProgsNoOverlap :
    exists vg2, (runDual 15 defaultVal dA1 dB1
    ) = Some vg2 
    /\ (fst vg2 $? "ret" = Some (varAss 10)) /\ (snd vg2 $? "ret" = Some (varAss 4)).
Proof.
    prover.
Qed.


Definition dA2 := (topVar "ret" := Const 3 ;;;
    readyDecl (awaitStmt "sigB" ;; "ret" <- Const 10) ;;; 
    EndDecl).

Definition dB2 := readyDecl (emitSignalStmt "sigB" None nil) ;;; EndDecl.

Theorem RunDualSimpleAwait :
    exists vg2, (runDual 10 defaultVal dA2 dB2
    ) = Some vg2 
    /\ (fst vg2 $? "ret" = Some (varAss 10)).
Proof.
    prover.
Qed.


Definition dA3 := (topVar "ret" := Const 3 ;;; 
    methodDecl "func" ("a" :: nil) None ("ret" <- Var "a") ;;;
    readyDecl (awaitStmt "sigB" ;; "ret" <- Const 10) ;;; 
    EndDecl).

Definition dB3 := readyDecl (emitSignalStmt "sigB" (Some ("func", 1)) (Const 8 :: nil)) ;;; EndDecl.


(*Context switch for callback and waiting*)
Theorem RunDualEmitSignalCallbackAndAwait1 :
    exists vg2, (runDual 10 defaultVal dA2 dB2
    ) = Some vg2 
    /\ (fst vg2 $? "ret" = Some (varAss 10)).
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
    exists vg2, (runDual 10 defaultVal dA3' dB3'
    ) = Some vg2 
    /\ (fst vg2 $? "ret" = Some (varAss 8)) /\ (snd vg2 $? "ret" = Some (varAss 10)).
Proof.
    eexists; repeat split; cbv; reflexivity.
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
    exists vg2, (runDual 10 defaultVal dA3'' dB3''
    ) = Some vg2 
    /\ (fst vg2 $? "ret" = Some (varAss 8)) /\ (snd vg2 $? "ret" = Some (varAss 10)).
Proof.
    eexists; repeat split; cbv; reflexivity.
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
    exists vg2, (run 20 $0 dA4) = Some vg2 /\ vg2 $? "ret" = Some (varAss 5).
Proof.
    prover.
Qed.

(*Very strong theorem*)
Theorem RunDualProgsAwait :
    exists vg2, (runDual 14 defaultVal dA4 dB4
    ) = Some vg2 
    /\ (fst vg2 $? "ret" = Some (varAss 10)).
Proof.
    eexists; split; cbv; reflexivity.
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
    exists vg2, (runDual 14 defaultVal dA5 dB5
    ) = Some vg2 
    /\ (snd vg2 $? "ret" = Some (varAss 10)).
Proof.
    eexists; split; cbv; reflexivity.
Qed.