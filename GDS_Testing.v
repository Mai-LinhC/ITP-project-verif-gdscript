Require Import Lab07Map.
Require Import GDS_Language. 
From Stdlib Require Import String.
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
    ((((var "a" := Const 5 ;; while (Var "a") loop ("a" <- Var "a" - Const 1) done) ;; 
    var "ret" := Var "a" + Const 2) ;; skip) )
    $0 v2) 
    -> (v2 $? "ret" = Some (varAss 2)).
Proof.
Admitted.