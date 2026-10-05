From Stdlib Require Import Reals List.
Import ListNotations.
Open Scope R_scope.

(* Port note. The Coquelicot version of this module imported Coquelicot and
   its Compactness library for two names only: the d-fold product type Tn and
   the coordinatewise closeness relation close_n. Coquelicot is no longer
   loaded, so both are copied here with exactly the definitions of
   Coquelicot.Compactness (Coquelicot 3.4.4), as printed by Print in the
   rocq-tools switch. The copies are convertible with the originals, so
   finite_joint_continuous below is the original text, word for word, and
   says the same thing. This module needs no MathComp library and depends
   on no axiom. *)

(* Copy of Coquelicot.Compactness.Tn: Tn n T is T * (T * ... (T * unit)),
   with n factors T. *)
Fixpoint Tn (n : nat) (T : Type) : Type :=
  match n with
  | O => unit
  | S n0 => (T * Tn n0 T)%type
  end.

(* Copy of Coquelicot.Compactness.close_n: every coordinate of x is at
   distance less than d from the same coordinate of t. *)
Fixpoint close_n (n : nat) (d : R) : Tn n R -> Tn n R -> Prop :=
  match n as n0 return (Tn n0 R -> Tn n0 R -> Prop) with
  | O => fun _ _ : Tn O R => True
  | S n0 =>
      fun x t : Tn (S n0) R =>
      let '(x1, x2) := x in
      let '(t1, t2) := t in Rabs (x1 - t1) < d /\ close_n n0 d x2 t2
  end.

Fixpoint coordinates_to_list (d : nat) : Tn d R -> list R :=
  match d as d0 return Tn d0 R -> list R with
  | O => fun _ => []
  | S k => fun z => fst z :: coordinates_to_list k (snd z)
  end.

Fixpoint coordinates_of_list (d : nat) (xs : list R) : Tn d R :=
  match d with
  | O => tt
  | S k => (hd 0 xs, coordinates_of_list k (tl xs))
  end.

Definition finite_joint_continuous (d : nat) (F : list R -> R) : Prop :=
  forall (z : Tn d R) (eps : posreal), exists delta : posreal,
    forall w : Tn d R, close_n d delta w z ->
      Rabs (F (coordinates_to_list d w) - F (coordinates_to_list d z)) < eps.
