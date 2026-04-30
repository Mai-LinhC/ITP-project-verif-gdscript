(** * CS-428: Interactive Theorem Proving, Spring 2026 - Lab 7 *)

Require Import Lab07Signature.
Require Import Lab07Map.
Require Import Lab07Language.

From Stdlib Require Import Lia.


(** In this lab, we'll revisit program optimizations from lab 6
    using small-step semantics instead of big-step semantics.

    As in lab 6, we encourage you to try your hand at some automation.
    When decomposed into the right sequence of lemmas, most of the theorems in
    this lab have relatively short proofs.  The best way to find these lemmas is
    to approach each problem cautiously, trying to work an understanding of the
    proof before diving into long series of [inversion], [econstructor], etc.

    In general, it's also a good idea to admit lemmas until you are sure that they
    allow you to prove the complete theorem, then go back and prove the lemmas
    — but do take the time to convince yourself that your lemmas make sense, so
    that you don't waste time using incorrect lemmas. *)

Module Impl.

  (** IMPORTANT: The language we use in this lab is defined in [Lab07Language.v].
      Please read [Lab07Language.v] before you go further. *)

  (** * Part 1: Reminder on small-step semantics *)

  (** Big-step semantics, as we've seen them in lab 6, describe the
      evaluation of a program up to its final value.  This style of
      semantics works quite well for many purposes, but it has many
      shortcomings, due to the fact that the intermediate states
      during evaluation are not clearly visible.

      For one, big-step semantics do not clearly indicate why certain
      programs do not evaluate: is the program stuck in an infinite
      loop, or did the program crash?  There is no way to tell from
      a proof of [~eval] alone.

      Second, we cannot express the semantics of concurrent programs, as
      their evaluation relies on the current state of the program, which
      is implicit in big-step semantics.

      Finally, we may want to analyze the behavior of a program up to
      a certain point.  For non-terminating programs, this is not
      possible in big-step semantics, because there is no [eval] object
      to inspect.

      Small-step semantics give us a finer-grained semantics to reason
      about the intermediate states of computation, using a "small-step"
      relation [step]: *)

  Print step.

  (** [step] describes an atomic step of computation of a program,
      relating two pairs of valuation and command together.

      For example, compare the rules for [While] in big-step and
      small-semantics: *)

  Check EvalWhileTrue.
  Check StepWhileTrue.

  (** [EvalWhileTrue] requires the rest of the program to evaluate,
      while [StepWhileTrue] unfolds the loop once. *)

    Ltac mgw :=
    match goal with
    | [ H : step (_, Skip) _ |- _ ] => inversion H
    | [ |- _ ] => try reflexivity; try contradiction; subst
    end.

  (** For our simple language, [step] is deterministic: *)
  Lemma step_deterministic : forall s s1 s2,
      step s s1 ->
      step s s2 ->
      s1 = s2.
  Proof.
    intros s s1 s2 H1 H2.
    revert s2 H2.
    induction H1 ; intros s2 h2 ; inversion h2; repeat mgw.
    - assert ((v', c1') = (v'0, c1'0)) as h_eq1 by apply (IHstep (v'0, c1'0) H4).
    inversion h_eq1.
    reflexivity.
Qed.

  (** Here's an example of a program that would loop infinitely: *)
  Example infinite_loop :=
    while 1 loop Skip done.

  (** We can prove that the program does not have defined big-step
      semantics: *)
  Lemma infinite_loop_nonterminating : forall v v',
    ~ eval v infinite_loop v'.
  Proof.
    unfold infinite_loop.
    intros. intro H.
    dependent induction H; subst.
    apply IHeval2.
    reflexivity.
  Qed.

  (** We know this is because the program loops infinitely, but how can
      we formalize this? To do so, we are going to define more precise
      notions of behavior using the small-step semantics. *)

  (** We first need to iterate the [step] relation to a multi-step relation
      [step*]: *)
  Print trc.
  Check trc step.

  (** We can define a [step_terminates] predicate: a program
      [c] terminates from valuation [v] if it multi-steps to valuation [v']
      and command [Skip]: *)
  Definition step_terminates (v: valuation) (c: cmd) (v': valuation) :=
    step* (v, c) (v', Skip).

  (** Now, using small-step semantics, prove that the program never terminates: *)

  (* Lemma self_step : forall v p, step* (v, p) (v, p) -> forall v', ~ step_terminates v p v'.
  
Admitted. *)

Definition is_infinite_loop (s : valuation * cmd) : Prop :=
    match s with
    | (v, While (Const 1) Skip) => True
    | (v, Sequence Skip (While (Const 1) Skip)) => True
    | _ => False
    end.

  Lemma infinite_loop_step_invariant : forall s s',
    is_infinite_loop s ->
    step s s' ->
    is_infinite_loop s'.
  Proof.
    intros s s' Hinf Hstep.
    destruct s as [v c].
    destruct c; simpl in *; try contradiction. (* Only While and Sequence cases survive *)
    (* - Case While 1 loop Skip done
      inversion Hstep; subst.
      + (* WhileTrue branch *)
        simpl. destruct c1'. exact I.
      + (* WhileFalse branch: 1 = 0 is impossible *)
        simpl in *. lia.
    - (* Case Skip ;; While ... *)
      inversion Hstep; subst.
      + (* StepSeq1: Skip doesn't step *)
        inversion H4.
      + (* StepSeq2: Skip ;; c -> c *)
        simpl. exact I. *)
  Admitted.

  Lemma infinite_loop_nonterminating_smallstep : forall v v',
    ~ step_terminates v infinite_loop v'.
  Proof.
    unfold infinite_loop, step_terminates.
    intros v v' H.
    remember (v, while 1 loop Skip done) as s.
    remember (v', Skip) as s_end.
    dependent induction H.
    - subst; inversion Heqs_end.
    - apply IHtrc; try assumption.
    subst.
    (* need to prove false *)
    admit.
    
    (* assert (Hinf: is_infinite_loop (v, while 1 loop Skip done)) by (simpl; auto).
      (* We apply the invariant: if the first state is infinite, 
         the next one MUST be too. *)
      assert (Hy_inf: is_infinite_loop y).
      apply (infinite_loop_step_invariant) in H.
      exact H. rewrite <- Heqs in Hinf. assumption.
     
      apply IHtrc; auto.
      destruct y.
      unfold is_infinite_loop in Hy_inf.
      destruct c eqn:hc; try contradiction.

      (* Final check: is_infinite_loop (v', Skip) must be False *)
      destruct z as [ve ce]. inversion Heqs_end; subst.
      simpl in Hinf. contradiction.  *)
    (* inversion H; subst.
    inversion H0; subst; simpl in *; try lia.
    inversion H1; subst.
    inversion H2; subst.
    inversion H9.
    assert (step* (v, while 1 loop Skip done) (v, while 1 loop Skip done)). {
        eapply TrcFront.
        exact H0.
        eapply TrcFront.
        exact H2.
        apply TrcRefl.
    }
    eapply self_step. exact H4. *)

    (* dependent induction H.
    inversion H; subst; simpl in *; try lia. *)
  Admitted.

  (** Using the [step*] relation, we can now prove the equivalence
      between small-step and big-step semantics for terminating
      programs.

      Our proofs uses several lemmas on [step*] that you may want to
      prove independently before tackling both theorems. *)

  Lemma step_star_Seq1 :
    forall s1 s2 c,
    step* s1 s2 ->
    step* (fst s1, Sequence (snd s1) c) (fst s2, Sequence (snd s2) c).
  Proof.
    intros s1 s2 c H.
    induction H.
    - constructor.
    - destruct y. econstructor.
      2: { eapply IHtrc. }
      constructor. destruct x. simpl. assumption.
  Qed.


  Theorem small_big : forall v c v',
      step_terminates v c v' ->
      eval v c v'.
  Proof.

  Admitted.

  Theorem big_small : forall v c v',
      eval v c v' ->
      step_terminates v c v'.
  Proof.
    intros v c v' h.
    induction h.
    - constructor.
    - econstructor; constructor.
    - apply step_star_Seq with (c2:=c2) in IHh1.
      eapply multi_step_trans. apply IHeval1.
      econstructor. apply StepSeq2. assumption.
    - econstructor.
      { apply StepIfTrue. assumption. }
      assumption.
    - econstructor.
      { apply StepIfFalse. assumption. }
      assumption.
    - econstructor.
      { apply StepWhileTrue. assumption. }
      eapply multi_step_trans.
      2: { apply IHeval2. }
      eapply multi_step_trans.
      { apply step_star_Seq. apply IHeval1. }
      econstructor. apply StepSeq2. constructor.
    - econstructor.
      { apply StepWhileFalse. assumption. }
      constructor.
  Admitted.

  (** * Part 2: Stuckness and divergence *)

  (** One advantage of small-step semantics is that they let us
      distinguish *stuck programs* from *infinitely looping*, a
      distinction that is difficult to make using big-step semantics,
      since in big-step semantics both are represented as the absence of
      evaluation to a final value. *)

  (** To demonstrate this, we consider the command [Assert e], for which
      evaluation gets stuck when [e] evaluates to [0].
      The two lemmas below highlight the difference between these two
      modes of failure: a stuck program cannot take a step, while
      looping programs can always take a step. *)

  Lemma assert_stuck : forall v e,
    interp_arith e v = 0 -> ~ exists s, step (v, Assert e) s.
  Proof.
  Admitted.

  Lemma loop_steps : forall v,
    exists s, step (v, infinite_loop) s.
  Proof.
  Admitted.

  (** We define [stuck_assert] as an inductive predicate that holds
      whenever a command gets stuck on an [Assert]: *)

  Print stuck_assert.

  (** We also define a [trichotomy] predicate that captures that there is
      exactly one of [A], [B], and [C] that holds. *)
  Inductive trichotomy (A B C: Prop): Prop :=
  | onlyA: A -> ~ B -> ~ C -> trichotomy A B C
  | onlyB: B -> ~ A -> ~ C -> trichotomy A B C
  | onlyC: C -> ~ A -> ~ B -> trichotomy A B C.

  (** Using the two predicates above, we can prove the following trichotomy: all
      programs are either [Skip], can step, or are stuck on [Assert]. *)

  Theorem state_trichotomy : forall v c,
      trichotomy (c = Skip)
       (exists s', step (v, c) s')
       (stuck_assert v c).
  Proof.
  Admitted.

  (** You can also prove (optionally) an even stronger trichotomy result: a
      program either terminates, evaluates indefinitely, or gets stuck on an
      [Assert]. *)

  (** We start by formally defining what it means to never terminate and
      to get stuck. *)
  Definition never_terminates (v: valuation) (c: cmd) :=
    forall v' c', step* (v, c) (v', c') ->
             exists v'' c'', step (v', c') (v'', c'').

  Definition gets_stuck (v: valuation) (c: cmd) :=
    exists v' c', step* (v, c) (v', c') /\ stuck_assert v' c'.

  (** Deciding whether a program terminates in our language is very likely to be
      undecidable, due to the undecidability of the halting problem on Turing machines.
      Therefore, to prove that there is a trichotomy of program results, we will need to
      use the excluded middle: for all propositions [P], either [P] or its negation [~P] holds.

      Notice that in our case, either the program terminates, or it does not terminate, but we
      cannot decide (i.e. compute) which of the two holds! The excluded middle
      is said to have *no computational content*, and is not admissible in
      intuitionistic logic.

      This theorem is not graded, as the proof is quite long (~45 lines). If
      you're looking for a challenge, try proving this theorem! You can always
      ask the TAs for hints if you get stuck. *)
  Theorem program_result_trichotomy (EXCLUDED_MIDDLE: forall A: Prop, A \/ ~ A): forall v c,
      trichotomy (exists v', step_terminates v c v')
        (gets_stuck v c)
        (never_terminates v c).
  Proof.
  Admitted.

  (** * Part 3: Program Optimizations *)

  (** The goal of this section is to prove the correctness of two simple
      optimizations: elimination of [Skip] commands, and optimization of
      undefined behavior. *)

  (** ** Dead-code elimination *)

  (** Define the [opt_unskip] optimization as a fixpoint that
      recursively turns all sequences of commands of the form
      [Skip;; c] or [c;; Skip] into [c]. You may want to define a helper
      function [is_skip]. *)

  Fixpoint opt_unskip (c: cmd) : cmd :=
    match c with
    | Skip => Skip
    | Assign x e => Assign x e
    | Sequence c1 c2 => TODO
    | If e thn els => If e (opt_unskip thn) (opt_unskip els)
    | While e body => While e (opt_unskip body)
    | Assert e => Assert e
    end.

  (** Once you have defined [opt_unskip], the following two examples should hold
      by [reflexivity]: *)
  Example opt_unskip_test1 :
    opt_unskip (Skip;; (Skip;; Skip);; (Skip;; Skip;; Skip)) = Skip.
  Proof.
  Admitted.

  Example opt_unskip_test2 :
    opt_unskip (when 0 then (Skip;; Skip) else Skip done;;
                while 0 loop Skip;; Skip done;; Skip) =
    (when 0 then Skip else Skip done;; while 0 loop Skip done).
  Proof.
  Admitted.

  (** To prove the optimization correct in small-step semantics, we will use a
      simulation argument: we will prove that each step of the original program
      (the source) can be simulated by zero or more steps of the optimized
      program (the target).

      To do so, we will establish an invariant between the states in the
      executions of the source and the optimized programs. This invariant relates both
      the current valuation and the current command and should be enough to show
      that if there's a step in the source, there are some matching steps in the
      optimized version, and those reestablish the invariant.

      For this exercise, we provide you with the invariant between the two
      states: the valuation is the same, and if the source is running command
      [c], then the target is running [opt_unskip c]. *)

  (* Prove that each step of the original program can be matched by zero
     or more steps of the optimized program and restores the invariant. *)
  Lemma opt_unskip_sim : forall v c v' c',
      step (v, c) (v', c') ->
      step* (v, opt_unskip c) (v', opt_unskip c').
  Proof.
  Admitted.

  (** Having proved that, we can now prove our optimization correct! *)

  Theorem opt_unskip_sound : forall v c v',
      step_terminates v c v' ->
      step_terminates v (opt_unskip c) v'.
  Proof.
  Admitted.

  (** ** Undefined behavior *)

  (** In languages such as C, compilers are allowed to assume that
      *undefined behaviors* don't happen, a fact they exploit agressively
      to perform optimizations.

      Undefined behavior is often modelled as the program getting stuck,
      and it turns out our language has a way to get stuck too: [Assert]. *)

  (** The optimization we are concerned with in this section is the removal
      of some of the branches that always get stuck. Importantly, we do not
      want to remove branches that have an [Assert] but do not necessarily
      get stuck, so we will consider only the removal of branches with
      an explicit [Assert 0] command. *)

  (** Below is the definition of the [opt_ub] optimization that removes
      [Assert 0] from our programs. [opt_ub] returns [None] for commands
      that always trigger an [Assert 0] *)
  Fixpoint opt_ub (c: cmd): option cmd :=
    match c with
    | Skip => Some Skip
    | Assign x e => Some (Assign x e)
    | Sequence c1 c2 =>
        match opt_ub c1, opt_ub c2 with
        | Some c1', Some c2' => Some (Sequence c1' c2')
        | Some c1', None => None
        | _, _ => None
        end
    | If e c1 c2 =>
        match opt_ub c1, opt_ub c2 with
        | Some c1', Some c2' => Some (If e c1' c2')
        | Some c1', None => Some c1'
        | None, Some c2' => Some c2'
        | None, None => None
        end
    | While e c =>
        match opt_ub c with
        | Some c' => Some (While e c')
        | None => Some Skip
        end
    | Assert (Const 0) => None
    | Assert e => Some (Assert e)
    end.

  (** Here are a few examples to illustrate how [opt_ub] works (we encourage you
      to write some more examples): *)
  Example opt_ub_example1 :
    opt_ub (when 1 then Assert 0 else Skip done) = Some Skip.
  Proof.
    reflexivity.
  Qed.

  Example opt_ub_example2 :
    opt_ub (when 1 then (when 1 then Assert 0 else Skip done) else Assert 0 done) = Some Skip.
  Proof.
    reflexivity.
  Qed.

  Example opt_ub_example3 :
    opt_ub (when 1 then (when 1 then Assert 0 else Assert 0 done) else Assert 0 done) = None.
  Proof.
    reflexivity.
  Qed.

  (** We proceed similarly using a simulation argument: each step of
      [opt_ub c] corresponds to one or more step of [c]. *)

  (** First, we should prove that [opt_ub c = None] implies that the program
      does not terminate: *)
  Lemma opt_ub_sim_neg: forall c,
      opt_ub c = None ->
      forall v v', not (step* (v, c) (v', Skip)).
  Proof.
  Admitted.

  (** Now, we can proceed with the actual simulation proof.

      Before proceeding with the proof, take a moment to digest the statement of
      the theorem and understand how it would be used in the soundness proof. We
      suggest also that you get a good intuition (on paper) of the proof. *)
  Lemma opt_ub_sim : forall c oc c' v v',
      opt_ub c = Some oc ->
      step (v, c) (v', c') ->
      (exists oc', opt_ub c' = Some oc' /\ step* (v, oc) (v', oc'))
        \/ (opt_ub c' = None /\ forall v'', not (step* (v', c') (v'', Skip))).
  Proof.
  Admitted.

  (** Now we can prove soundness of [opt_ub]: *)
  Lemma opt_ub_sound : forall c c' v v',
      opt_ub c = Some c' ->
      step_terminates v c v' ->
      step_terminates v c' v'.
  Proof.
  Admitted.

  (** * Congratulations, you reached the end of the lab! *)

End Impl.

Module ImplCorrect : Lab07Signature.S := Impl.

(* Authors:
 * Dario Halilovic
 * Jérémy Thibault
 * Victor Deng
 * Clément Pit-Claudel
 *)
