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

(* Same names / shapes as the Lab07Map lemmas your tactics rewrite with. *)
Lemma lookup_empty {A B} `{Eqb A} (k : A) : (empty A B) $? k = None.
Proof. reflexivity. Qed.

Lemma lookup_add_eq {A B} `{Eqb A} (m : fmap A B) k1 k2 v :
  k1 = k2 -> (m $+ (k1, v)) $? k2 = Some v.
Proof. intros ->. simpl. rewrite eqb_refl. reflexivity. Qed.

Lemma lookup_add_ne {A B} `{Eqb A} (m : fmap A B) k k' v :
  k' <> k -> (m $+ (k, v)) $? k' = m $? k'.
Proof. intro Hne. simpl. rewrite (eqb_neq Hne). reflexivity. Qed.
