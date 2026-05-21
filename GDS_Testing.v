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


  (*TODO: Probablement fausse, à changer*)
  Ltac program_match := match goal with 
    | [ H: exists _,  _ |-  _ ] => destruct H
    | [ H: _ /\ _ |- _ ] => destruct H
    | [ |- _ /\ _ ] => split
    | [ H : _ \/ _ |- _ ] => destruct H
    | [H: context[interp2 _ _ _] |- _ ] => simpl in H
    | [H: context[interp (Const _) _] |- _ ] => unfold interp in H
    | [H: context[$0 $? _] |- _] => rewrite lookup_empty in H
    | [H: runP _ _ (SequenceDecl _ _) = _ |- _] => inversion_clear H
    | [H: runP _ _ (classVarDecl _ (Const _)) = _ |- _] => inversion_clear H
    | [H: runP _ _ (readyDecl _ ) = _ |- _] => inversion_clear H
    | [H: runP _ _ (methodDecl _ _ _ _) = _ |- _] => inversion H; subst; clear H
    | [H: runP _ _ EndDecl = _ |- _] => destruct H
    | [H: ?a = ?a |- _ ] => clear H
    | [ |- _ ] => subst; eauto; try discriminate; try contradiction
  end.

  (*La def tu TH me parait ok, à vérifier*)
Theorem runVar :    
    forall vg2 vl2, 
    runStmtP 10 $0 $0 
    ((var "a" := Const 2) ;; (var "b" := Const 3) ;; 
    (var "ret" := ((Var "a") + (Var "b"))) ;; skip) = Some (vg2, vl2)
    -> (vl2 $? "ret" = Some (varAss 5)).
Proof.
    intros.
    inversion H.
    repeat program_match.
    rewrite lookup_add_ne in H1 by discriminate.
    rewrite lookup_add_eq in H1 by reflexivity.
    rewrite lookup_add_eq in H1 by reflexivity.
    injection H1 as Hvg2 Hvl2.
    subst vl2.
    rewrite lookup_add_eq by reflexivity; reflexivity.
Qed.

(*Pas encore redéfini, si preuve de RunVar réussie, redéfinir de la même manière*)
Theorem runIf :
    forall vg2 vl2, 
    (runStmtP 10 $0 $0 
    ((( (var "a" := Const 2 ;; var "b" := Const 3) ;; 
    when ((Var "b") - (Var "a")) 
    then (var "ret" := Const 10) 
    else (var "ret" := Const 5) done) ) ;; 
    skip)) = Some (vg2, vl2)
    -> (vl2 $? "ret" = Some (varAss 10)).
Proof.
    intros.
    inversion H.
    rewrite lookup_add_eq in H1 by reflexivity.
    rewrite lookup_add_ne in H1 by discriminate.
    rewrite lookup_add_eq in H1 by reflexivity.
    simpl in H1.
    injection H1 as Hvg2 Hvl2.
    subst vl2.
    rewrite lookup_add_eq by reflexivity; reflexivity.
Qed.

Theorem runWhile :
    forall vg2 vl2, 
    (runStmtP 10 $0 $0 
    ((((var "a" := Const 2 ;; while (Var "a") loop ("a" <- Var "a" - Const 1) done) ;; 
    var "ret" := Var "a" + Const 5) ;; skip))) = Some (vg2, vl2)
    -> (vl2 $? "ret" = Some (varAss 5)).
Proof.
    intros.
    inversion H.
    rewrite lookup_add_eq in H1 by reflexivity.
    rewrite lookup_add_eq in H1 by reflexivity.
    simpl in H1.
    rewrite lookup_add_eq in H1 by reflexivity.
    rewrite lookup_add_eq in H1 by reflexivity.
    injection H1 as Hvg2 Hvl2.
    subst vl2.
    rewrite lookup_add_eq by reflexivity; reflexivity.
Qed.

Theorem globalExe1 :
    forall vg2, (runP 5 $0 
    ((((topVar "a" := Const 9 ;;; topVar "ret" := Const 0 ) ;;;
    methodDecl "plusOne" nil (Some "dump")  (var "dump" := (Var "a" + Const 1))) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil)) ;;; EndDecl)) = Some vg2 
    ->(vg2 $? "ret" = Some (varAss 10)).
Proof.
    intros.
    unfold runP in H.
    destruct (interp (Const 9) $0) eqn:E1; [|discriminate].
    destruct (interp (Const 0) _) eqn:E2; [|discriminate].
    destruct (runStmtP _ _ $0 _) eqn:E3; [|discriminate].
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
Qed.

Theorem globalExe2 :
    forall vg2, (runP 10 $0 
    (((topVar "a" := Const 3 ;;; topVar "ret" := Const 0 ) ;;;
    methodDecl "plusOne" nil (Some "dump") (var "a" := Const 9 ;; var "dump" := (Var "a" + Const 1))) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil) ;;; EndDecl)) = Some vg2 
    ->((vg2 $? "ret" = Some (varAss 10))  /\ (vg2 $? "a" = Some (varAss 3))).
Proof.
Admitted.

Theorem runProcess :
    forall v2, (run 15 $0 (
       (topVar "ret" := Const 0 ;;; processDecl(
        ((var "a" := Const 10 ;; "ret" <- Var "a") ;; skip)) ;;; 
        EndDecl) 
    ) v2) 
    ->(v2 $? "ret" = Some (varAss 10)).
Proof.
Admitted.

(* Warning: la preuve suivante risque d’être particulièrement longue *)
Theorem runSignal :
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
Admitted.

(* NB: Si trop dur à prouver, on peut retirer l’argument “a” de callback_fun, mais c’est moins probant comme exemple. *)
Theorem runSignalCallback :
    forall v2, run 10 $0 (
        (topVar "ret" := Const 0 ;;; methodDecl "callback" ("a"::"b"::nil) None ("ret" <- Var "b")) ;;;
        readyDecl(emitSignalStmt "sig" (Some ("callback", 0)) (Const 5 :: Const 10 :: nil))
    ) v2 
    -> (v2 $? "ret" = Some (varAss 10)).
Proof.
Admitted.