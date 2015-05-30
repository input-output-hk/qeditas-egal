(* Title "The Foundation: Church's Simple Type Theory with Tarski-Grothendieck Set Theory" *)
(* Author "Chad E. Brown" *)

Definition and : prop -> prop -> prop := fun A B:prop => forall P:prop, (A -> B -> P) -> P.

(* Unicode /\ "2227" *)
Infix /\ 780 left := and.

Definition iff : prop -> prop -> prop := fun (A B:prop) => (A -> B) /\ (B -> A).

(* Unicode <-> "2194" *)
Infix <-> 805 := iff.

Section Eq.

Variable A:SType.

Definition eq : A->A->prop := fun x y:A => forall Q:A->prop, Q x -> Q y.

End Eq.

Infix = 502 := eq.

(** SECTION "Extensionality Principles" **)

(** Propositional extensionality: Equivalent propositions are equal. **)

Axiom prop_ext : forall A B:prop, (A <-> B) -> A = B.

(** Functional extensionality: Equivalent functions are equal. **)
Section FE.

Variable A B:SType.

Axiom func_ext : forall (f g : A -> B), (forall x:A, f x = g x) -> f = g.

End FE.

