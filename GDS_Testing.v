Require Import Lab07Map.
Require Import GDS_Language. 
From Stdlib Require Import String.
Require Import List.
Open Scope string_scope.
Open Scope expr.

Ltac special_match := match goal with
    | [ H: exists _,  _ |-  _ ] => destruct H
    | [ H: _ /\ _ |- _ ] => destruct H
    | [ |- _ /\ _ ] => split
    | [ H : _ \/ _ |- _ ] => destruct H
    | [H: context[interp2 _ _ _] |- _ ] => destruct H
    | [ |- _ ] => subst; eauto; try discriminate
  end.

  Ltac special_match2 := match goal with
    | [ H: exists _,  _ |-  _ ] => destruct H
    | [ H: _ /\ _ |- _ ] => destruct H
    | [ |- _ /\ _ ] => split
    | [ H : _ \/ _ |- _ ] => destruct H
    | [H: context[interp2 _ _ _] |- _ ] => simpl in H
    | [ |- _ ] => subst; eauto; try discriminate
  end.

Theorem runVar :    
    forall v2, 
    (runStmt 10 $0 $0 
    ((var "a" := Const 2) ;; (var "b" := Const 3) ;; 
    (var "ret" := ((Var "a") + (Var "b"))) ;; skip) $0 v2) 
    -> (v2 $? "ret" = Some (varAss 5)).
Proof.
    intros.
    inversion H.
    repeat special_match.
    inversion H1; repeat special_match.
    clear H1; clear H; inversion H0; repeat special_match.
    clear H0; inversion H; repeat special_match.
    clear H; inversion H0.
    destruct H; simpl in H; subst.
    inversion H2.
    destruct H; simpl in H; subst.
    inversion H1.
    destruct H; simpl in H.
    assert ("a" <> "b") by congruence.
    epose proof (lookup_add_ne _ _ H4) as Hlook.
    rewrite Hlook in H.
    assert ("a" = "a") by reflexivity.
    epose proof (lookup_add_eq _ _ H5) as Hlookne.
    rewrite Hlookne in H.
    assert ("b" = "b") by reflexivity.
    epose proof (lookup_add_eq _ _ H6) as Hlookeq.
    rewrite Hlookeq in H.
    simpl in H; subst.
    assert ("ret" = "ret") by reflexivity.
    epose proof (lookup_add_eq _ _ H).
    apply H3.
Qed.

Theorem runIf :
    forall v2, 
    (runStmt 10 $0 $0 
    ((( (var "a" := Const 2 ;; var "b" := Const 3) ;; 
    when ((Var "b") - (Var "a")) 
    then (var "ret" := Const 10) 
    else (var "ret" := Const 5) done) ) ;; 
    skip)
    $0 v2 )
    -> v2 $? "ret" = Some (varAss 10).
Proof.
    intros.
    inversion H; repeat special_match.
    inversion H0; repeat special_match.
    clear H0; inversion H2; repeat special_match.
    clear H2; inversion H3.
    -repeat special_match.
    clear H3; inversion H0; inversion H4.
    clear H0 H4.
    destruct H2, H3; simpl in H2, H3; subst.
    inversion H1; subst.
    inversion H6; destruct H0; simpl in H0; subst.
    assert ("ret" = "ret") by reflexivity.
    epose proof (lookup_add_eq _ _ H0).
    apply H2.
    
    -clear H3; inversion H0; inversion H4.
    clear H0 H4.
    destruct H3, H5; simpl in H3, H5; subst.
    destruct H2; simpl in H2.
    simpl in H0.
    assert ("a" <> "b") by congruence.
    epose proof (lookup_add_ne _ _ H3) as Hlookne.
    rewrite Hlookne in H0.
    assert("a" = "a") by reflexivity.
    epose proof (lookup_add_eq _ _ H4) as Hlooka.
    rewrite Hlooka in H0.
    rewrite lookup_add_eq in H0; simpl in H0.
        + discriminate H0.
        + reflexivity.
Qed.

Theorem runWhile :
    forall v2, 
    (runStmt 10 $0 $0 
    ((((var "a" := Const 2 ;; while (Var "a") loop ("a" <- Var "a" - Const 1) done) ;; 
    var "ret" := Var "a" + Const 5) ;; skip) )
    $0 v2) 
    -> (v2 $? "ret" = Some (varAss 5)).
Proof.
    intros v_res H.
    inversion_clear H; repeat special_match.
    inversion_clear H; repeat special_match.
    inversion_clear H; repeat special_match.
    inversion_clear H. destruct H3 ; simpl in H; subst.
    assert (ha: "a" = "a") by reflexivity; 
    epose proof (lookup_add_eq _ _ ha) as Hlooka.
    inversion_clear H2; [repeat special_match | do 2 special_match].
    - (* h3 = assign -> (*Check local val, if exists, reassign, else check global, if exists reassign, else crash (prop is false)*) *)
    inversion H3. 
        + (* Check local val, if exists, reassign, *)
        destruct H as [h1 [n [h3 [h4 h5]]]].
        simpl in h3.
        rewrite Hlooka in h3.
        subst.
        clear H3 H2 x4 h1.
        inversion H4. 
        -- destruct H as [inta [vgmid [vlmid [h1 [h2 [h3 h4]]]]]].
        inversion h3. 
        ++ 
            destruct H as [h1' [n [h3' [h4' h5']]]].
            simpl in h3'; rewrite (lookup_add_eq _ _ ha) in h3'; subst.
            clear h3 h1' H4 h2.
            inversion_clear h4.
            * destruct H as [inta [vgmid' [vlmid [h1 [h2 [h3 h4]]]]]].
            simpl in h1.
            rewrite (lookup_add_eq _ _ ha) in h1.
            congruence.
            * destruct H as [h [h1 h2]].
            subst.
            inversion H1. 
            destruct H as [h1 h2].
            inversion H0.
            subst. simpl.
            rewrite (lookup_add_eq _ _ ha).
            assert (hret : "ret" = "ret") by reflexivity.
            rewrite (lookup_add_eq _ _ hret).
            reflexivity.
        ++
            destruct H as [h1' [h2' h3']].
            rewrite (lookup_add_eq _ _ ha) in h2'; congruence.
        -- simpl in H. epose proof (lookup_add_eq _ _ ha) as Hlookaa; rewrite Hlookaa in H; destruct H; discriminate.
        + (* check global, knowing doesnt exist locally, if global exists reassign, *)
        destruct H as [h1 [h2 h3]].
        rewrite Hlooka in h2; congruence.
    - simpl in H.
    rewrite Hlooka in H; discriminate.
Qed.

Theorem globalExe1 :
    forall v2, (run 10 $0 
    ((((topVar "a" := Const 9 ;;; topVar "ret" := Const 0 ) ;;; topVar "dump" := Const 0) ;;;
    methodDecl "plusOne" nil (Some "dump")  ("dump" <- Var "a" + Const 1)) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil))
    v2) 
    ->(v2 $? "ret" = Some (varAss 10)).
Proof.
Admitted.

Theorem globalExe2 :
    forall v2, (run 10 $0 
    (((topVar "a" := Const 3 ;;; topVar "ret" := Const 0 ) ;;;
    methodDecl "plusOne" nil None (var "a" := Const 9 ;; "a" <- Var "a" + Const 1)) ;;;
    readyDecl (assignCallMethodStmt (Some "ret") "plusOne" nil) ;;; EndDecl)
    v2) 
    ->((v2 $? "ret" = Some (varAss 10))  /\ (v2 $? "a" = Some (varAss 3)))
.
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