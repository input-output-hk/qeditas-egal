(* Title "Conditionals" *)
(* Author "Chad E. Brown" *)

(* Salt "2pYk6Gx8qDthfS2n2" *)

Section IfA.

Variable A:SType.

Definition If : prop->A->A->A := (fun p x y => some z:A, p /\ z = x \/ ~p /\ z = y).

Notation IfThenElse If.

Lemma If_correct : forall p:prop, forall x y:A,
p /\ (if p then x else y) = x \/ ~p /\ (if p then x else y) = y.
Admitted.

Theorem If_0 : forall p:prop, forall x y:A,
~ p -> (if p then x else y) = y.
Admitted.

Theorem If_1 : forall p:prop, forall x y:A,
p -> (if p then x else y) = x.
Admitted.

Theorem If_or : forall p:prop, forall x y:A, (if p then x else y) = x \/ (if p then x else y) = y.
Admitted.

Example If_eta : forall p:prop, forall x:A, (if p then x else x) = x.
Admitted.

End IfA.

Example If_True : forall p:prop, if p then p else ~p.
Admitted.

Example If_False : forall p:prop, ~if p then ~p else p.
Admitted.

Example If_not_eq : forall p:prop, (~p) = if p then False else True.
Admitted.

Example If_imp_eq : forall p q:prop, (p -> q) = if p then q else True.
Admitted.

Example If_and_eq : forall p q:prop, (p /\ q) = if p then q else False.
Admitted.

Example If_or_eq : forall p q:prop, (p \/ q) = if p then True else q.
Admitted.
