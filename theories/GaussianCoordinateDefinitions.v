From Stdlib Require Import Reals List.
Import ListNotations.
Open Scope R_scope.

(* Joint continuity of a function of d real coordinates given as a list.
   The coordinates live in the product Tn d R, converted to and from lists
   by coordinates_to_list and coordinates_of_list.
   finite_joint_continuous d F says that F : list R -> R, on the lists of
   length d, is continuous at every point for the coordinatewise distance:
   F w is close to F z when every coordinate of w is close to the same
   coordinate of z (close_n). *)

(* Tn n T is T * (T * ... (T * unit)), with n factors T. *)
Fixpoint Tn (n : nat) (T : Type) : Type :=
  match n with
  | O => unit
  | S n0 => (T * Tn n0 T)%type
  end.

(* close_n n d x t: every coordinate of x is at distance less than d from
   the same coordinate of t. *)
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
