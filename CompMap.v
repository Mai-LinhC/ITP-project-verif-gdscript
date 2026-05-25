(**
    NOTE: this is an association list, so it does NOT give a canonical
    representation and does NOT satisfy fmap_ext. Use it for executable test
    theorems; if you also need extensional equality for abstract correctness
    proofs, keep Lab07Map for those (or move to a canonical map like a sorted
    list / stdpp gmap). *)

From Stdlib Require Import String List Bool.
Import ListNotations.
Set Implicit Arguments.

(* Boolean key equality, as a small typeclass so $? / $+ stay argument-free. *)
Class Eqb (A : Type) := {
  eqb : A -> A -> bool ;
  eqb_eq : forall x y, eqb x y = true <-> x = y
}.

#[export] Instance Eqb_string : Eqb string := {
  eqb := String.eqb ;
  eqb_eq := String.eqb_eq
}.

Lemma eqb_refl {A} `{Eqb A} (x : A) : eqb x x = true.
Proof. apply eqb_eq. reflexivity. Qed.

Lemma eqb_neq {A} `{Eqb A} (x y : A) : x <> y -> eqb x y = false.
Proof.
  intro Hn. destruct (eqb x y) eqn:E; [ apply eqb_eq in E; contradiction | reflexivity ].
Qed.

Definition fmap (A B : Type) := list (A * B).

Definition empty (A B : Type) : fmap A B := [].

Fixpoint lookup {A B} `{Eqb A} (m : fmap A B) (k : A) : option B :=
  match m with
  | [] => None
  | (k', v) :: m' => if eqb k k' then Some v else lookup m' k
  end.

(* Newest binding shadows older ones, so re-adding a key overrides it. *)
Definition add {A B} `{Eqb A} (m : fmap A B) (k : A) (v : B) : fmap A B :=
  (k, v) :: m.

Notation "$0" := (empty _ _).
Notation "m $+ ( k , v )" := (add m k v) (at level 50, left associativity).
Infix "$?" := lookup (at level 50, no associativity).

(* Removes EVERY binding of k. Because add shadows rather than overwrites,
   deleting only the newest binding could expose an older one, so remove
   filters out all of them. This makes (m $- k) $? k = None hold unconditionally. *)
Definition remove {A B} `{Eqb A} (m : fmap A B) (k : A) : fmap A B :=
  filter (fun p => negb (eqb k (fst p))) m.
 
Notation "m $- k" := (remove m k) (at level 50, left associativity).
 
Lemma lookup_remove_eq {A B} `{Eqb A} (m : fmap A B) (k : A) :
  (m $- k) $? k = None.
Proof.
  unfold remove. induction m as [| [k' v] m' IH]; simpl.
  - reflexivity.
  - destruct (eqb k k') eqn:E; simpl.
    + exact IH.
    + rewrite E. exact IH.
Qed.
 
Lemma lookup_remove_neq {A B} `{Eqb A} (m : fmap A B) (k j : A) :
  k <> j -> (m $- j) $? k = m $? k.
Proof.
  intro Hkj. unfold remove. induction m as [| [k' v] m' IH]; simpl.
  - reflexivity.
  - destruct (eqb j k') eqn:Ej; simpl.
    + apply eqb_eq in Ej. subst k'.
      rewrite (eqb_neq Hkj). exact IH.
    + destruct (eqb k k') eqn:Ek.
      * reflexivity.
      * exact IH.
Qed.

