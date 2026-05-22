Require Import Lab07Map.
Require Import GDS_Language. 
From Stdlib Require Import String.
Require Import List.
Open Scope string_scope.
Open Scope expr.

  (* Ltac special_match2 := match goal with
    | [ H: exists _,  _ |-  _ ] => destruct H
    | [ H: _ /\ _ |- _ ] => destruct H
    | [ |- _ /\ _ ] => split
    | [ H : _ \/ _ |- _ ] => destruct H
    | [H: context[interp2 _ _ _] |- _ ] => simpl in H
    | [H: context[interp (Const _) _] |- _ ] => unfold interp in H
    | [ |- _ ] => subst; eauto; try discriminate
  end. *)

Ltac inv H := inversion H; subst; clear H.

Ltac general_match := match goal with
    | [|- _ -> _]  => intros
    | [ H: exists _,  _ |-  _ ] => destruct H
    | [ H: _ /\ _ |- _ ] => destruct H
    | [ |- _ /\ _ ] => split
    | [ H : _ \/ _ |- _ ] => destruct H
    | [H: ?a = ?a |- _ ] => clear H
    | [H: context[ (_)%nat] |- _ ] => cbv in H
    end.


Ltac map_match := match goal with
    | [|- (_ $+ (?k, ?v)) $? ?k = Some ?v] => rewrite lookup_add_eq by reflexivity 
    | [H: context[interp (Const _) _] |- _ ] => unfold interp in H
    | [H: context[$0 $? _] |- _] => rewrite lookup_empty in H
    | [H: context[(_ $+ (?k, ?v)) $? ?k] |- _] => rewrite lookup_add_eq in H by reflexivity
    | [H: context[(_ $+ (?k1, ?v)) $? ?k2] |- _] => rewrite lookup_add_ne in H by discriminate
    end.

Ltac run_match := match goal with
    (* | [H: run _ _ (SequenceDecl _ _) = _ |- _] => inv H
    | [H: run _ _ (classVarDecl _ (Const _)) = _ |- _] => inv H
    | [H: run _ _ (readyDecl _ ) = _ |- _] => inv H
    | [H: run _ _ (methodDecl _ _ _ _) = _ |- _] => inv H
    | [H: run _ _ EndDecl = _ |- _] => destruct H *)
    | [H: Some (?a, ?b) = Some (?c, ?d) |- _ ] => injection H as Hvg2 Hvl2
    end.

Ltac combine_match := try general_match; try map_match; try run_match; subst; eauto; try discriminate; try contradiction.


  Ltac program_match := match goal with 
    | [|- (_ $+ (?k, ?v)) $? ?k = Some ?v] => rewrite lookup_add_eq by reflexivity 
    | [ H: exists _,  _ |-  _ ] => destruct H
    | [ H: _ /\ _ |- _ ] => destruct H
    | [ |- _ /\ _ ] => split
    | [ H : _ \/ _ |- _ ] => destruct H
    (* | [H: context[interp2 _ _ _] |- _ ] => simpl in H *) (*Unsure, maybe check if this line is useful*)
    | [H: context[interp (Const _) _] |- _ ] => unfold interp in H
    | [H: context[$0 $? _] |- _] => rewrite lookup_empty in H
    | [H: context[(_ $+ (?k, ?v)) $? ?k] |- _] => rewrite lookup_add_eq in H by reflexivity
    | [H: context[(_ $+ (?k1, ?v)) $? ?k2] |- _] => rewrite lookup_add_ne in H by discriminate
    | [H: run _ _ (SequenceDecl _ _) = _ |- _] => inv H
    | [H: run _ _ (classVarDecl _ (Const _)) = _ |- _] => inv H
    | [H: run _ _ (readyDecl _ ) = _ |- _] => inv H
    | [H: run _ _ (methodDecl _ _ _ _) = _ |- _] => inv H
    | [H: run _ _ EndDecl = _ |- _] => destruct H
    | [H: ?a = ?a |- _ ] => clear H
    | [H: Some (?a, ?b) = Some (?c, ?d) |- _ ] => injection H as Hvg2 Hvl2 (*Seems to crash Rocq ?*)
    | [ |- _ ] => subst; cbv in *; eauto; try discriminate; try contradiction
  end.

Ltac existential_match := match goal with
    | [|- context[$0 $? _]] => rewrite lookup_empty
    | [|- context[(_ $+ (?k, ?v)) $? ?k]] => rewrite lookup_add_eq by reflexivity
    | [|- context[(_ $+ (?k1, ?v)) $? ?k2]] => rewrite lookup_add_ne by discriminate
    | [|- _ ] => subst; cbv in *; eauto; try f_equal; try discriminate; try contradiction
    end.


Theorem runStmtVar :    
    forall vg2 vl2, 
    runStmt 10 $0 $0 
    ((var "a" := Const 2) ;; (var "b" := Const 3) ;; 
    (var "ret" := ((Var "a") + (Var "b"))) ;; skip) = Some (vg2, vl2)
    -> (vl2 $? "ret" = Some (varAss 5)).
Proof.
    repeat combine_match.
Qed.


Theorem erunStmtVar :    
    exists vg2 vl2, 
    runStmt 10 $0 $0 
    ((var "a" := Const 2) ;; (var "b" := Const 3) ;; 
    (var "ret" := ((Var "a") + (Var "b"))) ;; skip) = Some (vg2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 5)).
Proof.
    eexists; eexists.
    split; repeat existential_match.
Qed.


Theorem runStmtIf :
    forall vg2 vl2, 
    (runStmt 10 $0 $0 
    ((( (var "a" := Const 2 ;; var "b" := Const 3) ;; 
    when ((Var "b") - (Var "a")) 
    then (var "ret" := Const 10) 
    else (var "ret" := Const 5) done) ) ;; 
    skip)) = Some (vg2, vl2)
    -> (vl2 $? "ret" = Some (varAss 10)).
Proof.
    repeat combine_match.
Qed.

Theorem erunStmtIf :
    exists vg2 vl2, 
    (runStmt 4 $0 $0 
    ((( (var "a" := Const 2 ;; var "b" := Const 3) ;; 
    when ((Var "b") - (Var "a")) 
    then (var "ret" := Const 10) 
    else (var "ret" := Const 5) done) ) ;; 
    skip)) = Some (vg2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 10)).
Proof.
    eexists; eexists.
    split; repeat existential_match.
Qed.


Theorem runStmtWhile :
    forall vg2 vl2, 
    (runStmt 10 $0 $0 
    ((((var "a" := Const 2 ;; while (Var "a") loop ("a" <- Var "a" - Const 1) done) ;; 
    var "ret" := Var "a" + Const 5) ;; skip))) = Some (vg2, vl2)
    -> (vl2 $? "ret" = Some (varAss 5)).
Proof.
    repeat combine_match.
Qed.

Theorem erunStmtWhile :
    exists vg2 vl2, 
    (runStmt 10 $0 $0 
    ((((var "a" := Const 2 ;; while (Var "a") loop ("a" <- Var "a" - Const 1) done) ;; 
    var "ret" := Var "a" + Const 5) ;; skip))) = Some (vg2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 5)).
Proof.
    eexists; eexists.
    split; repeat existential_match.
Qed.


Theorem globalExe1 :
    forall vg2, (run 5 $0 
    ((((topVar "a" := Const 9 ;;; topVar "ret" := Const 0 ) ;;;
    methodDecl "plusOne" nil (Some "dump")  (var "dump" := (Var "a" + Const 1))) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil)) ;;; EndDecl)) = Some vg2 
    -> (vg2 $? "ret" = Some (varAss 10)).
Proof.
    repeat combine_match.
    inversion H.
    combine_match.
Qed.

Theorem eglobalExe1 :
    exists vg2, (run 5 $0 
    ((((topVar "a" := Const 9 ;;; topVar "ret" := Const 0 ) ;;;
    methodDecl "plusOne" nil (Some "dump")  (var "dump" := (Var "a" + Const 1))) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil)) ;;; EndDecl)) = Some vg2 
    /\ (vg2 $? "ret" = Some (varAss 10)).
Proof.
    eexists.
    split; repeat existential_match.
Qed.

(* Theorem globalExe1 :
    forall vg2, (run 5 $0 
    ((((topVar "a" := Const 9 ;;; topVar "ret" := Const 0 ) ;;;
    methodDecl "plusOne" nil (Some "dump")  (var "dump" := (Var "a" + Const 1))) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil)) ;;; EndDecl)) = Some vg2 
    ->(vg2 $? "ret" = Some (varAss 10)).
Proof.
    intros.
    unfold run in H.
    destruct (interp (Const 9) $0) eqn:E1; [|discriminate].
    destruct (interp (Const 0) _) eqn:E2; [|discriminate].
    destruct (runStmt _ _ $0 _) eqn:E3; [|discriminate].
    simpl in E1, E2.
    injection E1 as <-.
    injection E2 as <-.
    destruct p as [vg2' vl2'].
    injection H as <-.
    inversion E3.
    destruct (($0 $+ ("a", varAss 9) $+ ("ret", varAss 0) $+ ("plusOne", methodAss nil (Some "dump") (var "dump" := Var "a" + Const 1))) $? "plusOne") eqn:Elookup.    
    -
    destruct a eqn:Ha.
        + discriminate.
        +
        assert (args = nil /\ ret = Some "dump" /\ body = (var "dump" := Var "a" + Const 1)) as [Harg [Hret Hbody]].
        {
        rewrite lookup_add_eq in Elookup by reflexivity.
        injection Elookup as [= -> -> ->].
        repeat split; reflexivity.
        } subst args ret body.
        destruct (interp2 (Var "a" + Const 1) _) eqn: E4.
            *
            rewrite lookup_add_eq in H0 by reflexivity.
            rewrite lookup_empty in H0.
            rewrite lookup_add_ne in H0 by discriminate.
            rewrite lookup_add_eq in H0 by reflexivity.
            injection H0 as [= Hvg2 Hvl2].
            subst vg2'.
            simpl in E4.
            rewrite lookup_empty in E4.
            rewrite lookup_add_ne in E4 by discriminate.
            rewrite lookup_add_ne in E4 by discriminate.
            rewrite lookup_add_eq in E4 by reflexivity.
            simpl in E4.
            injection E4 as <-.
            rewrite lookup_add_eq by reflexivity; reflexivity.

            *
            discriminate.

    +discriminate.

    -discriminate.
Qed. *)

Theorem globalExe2 :
    forall vg2, (run 7 $0 
    (((topVar "a" := Const 3 ;;; topVar "ret" := Const 0 ) ;;;
    methodDecl "plusOne" nil (Some "dump") (var "a" := Const 9 ;; var "dump" := (Var "a" + Const 1))) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil) ;;; EndDecl)) = Some vg2 
    -> ((vg2 $? "ret" = Some (varAss 10))  /\ (vg2 $? "a" = Some (varAss 3))).
Proof.
    do 2 combine_match.
    - admit.
Admitted.

Theorem eglobalExe2 :
    exists vg2, (run 6 $0 
    (((topVar "a" := Const 3 ;;; topVar "ret" := Const 0 ) ;;;
    methodDecl "plusOne" nil (Some "dump") (var "a" := Const 9 ;; var "dump" := (Var "a" + Const 1))) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil) ;;; EndDecl)) = Some vg2 
    /\ ((vg2 $? "ret" = Some (varAss 10))  /\ (vg2 $? "a" = Some (varAss 3))).
Proof.
    eexists.
    split; repeat existential_match.
Qed.


(*New example existential_matching assignations*)
Theorem eglobalExe3 :
    exists vg2, (run 6 $0 
    ((topVar "a" := Const 3) ;;;
    readyDecl ("a" <- Const 8 ;; skip) ;;; EndDecl)) = Some vg2 
    /\ ((vg2 $? "a" = Some (varAss 8))).
Proof.
    eexists.
    split; repeat existential_match.
Qed.


Definition existential_matchProg := (run 5 $0 (
       (processDecl(
        ((var "a" := Const 10 ;; var "ret" := Var "a") ;; skip)) ;;; 
        EndDecl) 
    )).

Compute existential_matchProg.


Theorem erunProcess :
    exists v2, (run 10 $0 (
       (topVar "ret" := Const 0 ;;; processDecl(
        ((var "a" := Const 10 ;; "ret" <- Var "a") ;; skip)) ;;; 
        EndDecl) 
    )) = Some v2
    /\ (v2 $? "ret" = Some (varAss 10)).
Proof.
    eexists.
    split; repeat existential_match.
Admitted.


(* Warning: la preuve suivante risque d’être particulièrement longue *)
(* Theorem runSignal :
     forall v2, run 15 $0 (  (* valeur de fuel choisie au pif, potentiellement ajuster pour que le théorème soit correct *)
        topVar "a" := Const 0 ;;; topVar "ret" := Const 0 ;;;
        readyDecl("a" <- Const 1) ;;;
        processDecl( "a" <- Var "a" + Const 1 ;; 
        when (Var "a" == Const 3)
        then (emitSignalStmt "sig" None nil)
        else (awaitStmt "sig" ;; "ret" <- Const 10)
        done)
     ) 
     v2 -> (v2 $? "ret" = Some (varAss 10)).
Proof.
Admitted. *)


(* NB: Si trop dur à prouver, on peut retirer l’argument “a” de callback_fun, mais c’est moins probant comme exemple. *)
Theorem runSignalCallback :
    exists v2, run 5 $0 (
        (topVar "ret" := Const 0 ;;; methodDecl "callback" ("a"::"b"::nil) None ("ret" <- Var "b")) ;;;
        readyDecl(emitSignalStmt "sig" (Some ("callback", 1)) (Const 5 :: Const 10 :: nil))
    ) = Some v2 
    /\ (v2 $? "ret" = Some (varAss 10)).
Proof.
    eexists.
    split; repeat existential_match.
Qed.



(*STARTING DUALS*)

Theorem erunStmtDualVar :    
    exists vg2 vl2, 
    runStmtDual 10 ($0 $+ ("current", varAss 1), $0) $0 
    ((var "a" := Const 2) ;; (var "b" := Const 3) ;; 
    (var "ret" := ((Var "a") + (Var "b"))) ;; skip) = Some (vg2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 5)).
Proof.
    eexists; eexists.
    split; repeat existential_match.
Qed.


Theorem erunStmtDualIf :
    exists vg2 vl2, 
    (runStmtDual 4 ($0 $+ ("current", varAss 1), $0) $0 
    ((( (var "a" := Const 2 ;; var "b" := Const 3) ;; 
    when ((Var "b") - (Var "a")) 
    then (var "ret" := Const 10) 
    else (var "ret" := Const 5) done) ) ;; 
    skip)) = Some (vg2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 10)).
Proof.
    eexists; eexists.
    split; repeat existential_match.
Qed.


Theorem erunStmtDualWhile :
    exists vg2 vl2, 
    (runStmtDual 6 ($0 $+ ("current", varAss 1), $0) $0 
    ((((var "a" := Const 2 ;; while (Var "a") loop ("a" <- Var "a" - Const 1) done) ;; 
    var "ret" := Var "a" + Const 5) ;; skip))) = Some (vg2, vl2)
    /\ (vl2 $? "ret" = Some (varAss 5)).
Proof.
    eexists; eexists.
    split; repeat existential_match.
Qed.


Definition dA1 := (topVar "a" := Const 9 ;;; topVar "ret" := Const 0 ;;;
    methodDecl "plusOne" nil (Some "dump")  (var "dump" := (Var "a" + Const 1)) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil) ;;; EndDecl).

Definition dB1 := (topVar "a" := Const 3 ;;; topVar "ret" := Const 0 ;;;
    methodDecl "plusOne" nil (Some "dump")  (var "dump" := (Var "a" + Const 1));;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil) ;;; EndDecl).

Theorem eRunDualProgsNoOverlap :
    exists vg2, (runDual 5 ($0 $+ ("current", varAss 1), $0) dA1 dB1
    ) = Some vg2 
    /\ (fst vg2 $? "ret" = Some (varAss 10)) /\ (snd vg2 $? "ret" = Some (varAss 4)).
Proof.
    eexists.
    repeat split; repeat existential_match.
Qed.

