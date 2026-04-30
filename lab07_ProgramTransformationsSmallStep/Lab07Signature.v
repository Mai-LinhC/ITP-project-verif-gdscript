(** * CS-428: Interactive Theorem Proving, Spring 2026 - Lab 7 *)

Axiom TODO : forall {A}, A.

Require Import Lab07Map Lab07Language.

(** A command is "stuck on Assert" if there is a failed Assert at the
    leftmost evaluation position (possibly nested inside Sequences). *)

Inductive stuck_assert : valuation -> cmd -> Prop :=
| SAHere : forall v e,
    interp_arith e v = 0 ->
    stuck_assert v (Assert e)
| SASeq : forall v c1 c2,
    stuck_assert v c1 ->
    stuck_assert v (Sequence c1 c2).

Module Type S.

  (** IMPORTANT: The language we use in this lab is defined in [Lab07Language.v].
      Please read [Lab07Language.v] before you go further. *)

  (** * Part 1: Introduction to small-step semantics *)

  (*[5%]*) Axiom step_deterministic : forall s s1 s2,
      step s s1 ->
      step s s2 ->
      s1 = s2.

  Example infinite_loop :=
    while 1 loop Skip done.

  Definition step_terminates (v: valuation) (c: cmd) (v': valuation) :=
    step* (v, c) (v', Skip).

  (*[10%]*) Axiom infinite_loop_nonterminating_smallstep : forall v v',
    ~ step_terminates v infinite_loop v'.

  (*[5%]*) Axiom small_big : forall v c v',
      trc step (v, c) (v', Skip) ->
      eval v c v'.
  
  (*[5%]*) Axiom big_small : forall v c v',
      eval v c v' ->
      trc step (v, c) (v', Skip).

  (** * Part 2: Stuckness and divergence *)

  (*[3%]*) Axiom assert_stuck : forall v e,
      interp_arith e v = 0 -> ~ exists s, step (v, Assert e) s.
  (*[3%]*) Axiom loop_steps : forall v,
      exists s, step (v, infinite_loop) s.

  Inductive trichotomy (A B C: Prop): Prop :=
  | onlyA: A -> ~ B -> ~ C -> trichotomy A B C
  | onlyB: B -> ~ A -> ~ C -> trichotomy A B C
  | onlyC: C -> ~ A -> ~ B -> trichotomy A B C.

  (*[9%]*) Axiom state_trichotomy : forall v c,
      trichotomy (c = Skip)
       (exists s', step (v, c) s')
       (stuck_assert v c).

  Definition never_terminates (v: valuation) (c: cmd) :=
    forall v' c', step* (v, c) (v', c') ->
             exists v'' c'', step (v', c') (v'', c'').

  Definition gets_stuck (v: valuation) (c: cmd) :=
    exists v' c', step* (v, c) (v', c') /\ stuck_assert v' c'.

  Axiom program_result_trichotomy: (forall A: Prop, A \/ ~ A) -> forall v c,
      trichotomy (exists v', step_terminates v c v')
        (gets_stuck v c)
        (never_terminates v c).

  (** * Part 3: Program Optimizations *)

  Parameter opt_unskip : cmd -> cmd.

  (*[3%]*) Axiom opt_unskip_test1 :
    opt_unskip (Skip;; (Skip;; Skip);; (Skip;; Skip;; Skip)) =
    Skip.

  (*[4%]*) Axiom opt_unskip_test2 :
    opt_unskip (when 0 then (Skip;; Skip) else Skip done;;
                while 0 loop Skip;; Skip done;; Skip) =
    (when 0 then Skip else Skip done;; while 0 loop Skip done).

  (*[15%]*) Axiom opt_unskip_sim : forall v c v' c',
      step (v, c) (v', c') ->
      step* (v, opt_unskip c) (v', opt_unskip c').

  (*[5%]*) Axiom opt_unskip_sound : forall v c v',
      step_terminates v c v' ->
      step_terminates v (opt_unskip c) v'.

  Parameter opt_ub : cmd -> option cmd.

  (*[13%]*) Axiom opt_ub_sim_neg: forall c,
      opt_ub c = None ->
      forall v v', not (step* (v, c) (v', Skip)).
  
  (*[15%]*) Axiom opt_ub_sim : forall c oc c' v v',
      opt_ub c = Some oc ->
      step (v, c) (v', c') ->
      (exists oc', opt_ub c' = Some oc' /\ step* (v, oc) (v', oc'))
        \/ (opt_ub c' = None /\ forall v'', not (step* (v', c') (v'', Skip))).

  (*[5%]*) Axiom opt_ub_sound : forall c oc v v',
      opt_ub c = Some oc ->
      step_terminates v c v' ->
      step_terminates v oc v'.

End S.

Global Arguments Nat.modulo !_ !_ /.
Global Arguments Nat.div !_ !_.
Global Arguments Nat.log2 !_ /.
