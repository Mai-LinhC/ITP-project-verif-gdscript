Require Import CompMap.
Require Import GDS_Language. 
From Stdlib Require Import String.
Require Import List.
Open Scope string_scope.
Open Scope expr.


Ltac inv H := inversion H; subst; clear H.
Ltac prover := try repeat eexists; try repeat split; try reflexivity.

Ltac general_match := match goal with
    | [|- _ -> _]  => intros
    | [ H: exists _,  _ |-  _ ] => destruct H
    | [ H: _ /\ _ |- _ ] => destruct H
    | [ |- _ /\ _ ] => split
    | [ H : _ \/ _ |- _ ] => destruct H
    | [H: ?a = ?a |- _ ] => clear H
    | [H: context[ (_)%nat] |- _ ] => cbv in H
    end.


Ltac existential_match := match goal with
    | [ |- _ /\ _ ] => split
    | [|- context[$0 $? _]] => rewrite lookup_empty
    | [|- context[(_ $+ (?k, ?v)) $? ?k]] => rewrite lookup_add_eq by reflexivity
    | [|- context[(_ $+ (?k1, ?v)) $? ?k2]] => rewrite lookup_add_ne by discriminate
    | [|- _ ] => subst; vm_compute; eauto; try f_equal; try discriminate; try contradiction
    end.


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

Theorem runStmtDualVar :    
    exists vg2 vl2, 
    runStmtDual 10 ($0 $+ ("current", varAss 1), $0) $0 
    ((var "a" := Const 2) ;; (var "b" := Const 3) ;; 
    (var "ret" := ((Var "a") + (Var "b"))) ;; skip) = Some (vg2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 5)).
Proof.
    prover.
Qed.


Theorem runStmtDualIf :
    exists vg2 vl2, 
    (runStmtDual 4 ($0 $+ ("current", varAss 1), $0) $0 
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
    (runStmtDual 6 ($0 $+ ("current", varAss 1), $0) $0 
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
    exists vg2, (runDual 15 ($0 $+ ("current", varAss 1), $0) dA1 dB1
    ) = Some vg2 
    /\ (fst vg2 $? "ret" = Some (varAss 10)) /\ (snd vg2 $? "ret" = Some (varAss 4)).
Proof.
    prover.
Qed.
