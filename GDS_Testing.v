Require Import Lab07Map.
Require Import GDS_Language. 
From Stdlib Require Import String.
Open Scope string_scope.
Open Scope expr.


Theorem runVar :    
    exists v2, 
    (runStmt 100 $0 $0 
    ((var "a" := Const 2) ;; (var "b" := Const 3) ;; 
    (var "ret" := ((Var "a") + (Var "b"))) ;; skip) $0 v2) 
    /\ (v2 $? "ret" = Some (varAss 5)).
Proof.
    
Admitted.