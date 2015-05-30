(* Title "A Few Basic Group Theory Results" *)
(* Author "Anonymous" *)

(* Salt "8AB52FzHiO7SVzrEhGo" *)

(** (Metalevel) Groups. Hungerford _Algebra_ Theorem 1.2 **)
Section Group.
Variable A:SType.
Variable G:A -> prop.
Variable op:A -> A -> A.
Infix * 400 left := op.
Hypothesis Gop : forall x y:A, G x -> G y -> G (x * y).
Hypothesis assoc : forall x y z:A, G x -> G y -> G z -> (x * y) * z = x * (y * z).

Theorem id_uniq : forall e e':A, G e -> G e' -> (forall x:A, G x -> e * x = x) -> (forall x:A, G x -> x * e' = x) -> e = e'.
Admitted.

Variable e:A.
Hypothesis Ge : G e.
Hypothesis idl : forall x:A, G x -> e * x = x.
Hypothesis idr : forall x:A, G x -> x * e = x.

Variable inv:A->A.
Postfix - 390 := inv.
Hypothesis Ginv : forall x:A, G x -> G (x-).
Hypothesis invl : forall x:A, G x -> x- * x = e.
Hypothesis invr : forall x:A, G x -> x * x- = e.

Theorem sqs_id : forall x:A, G x -> x * x = x -> x = e.
Admitted.

Theorem left_cancel : forall x y z:A, G x -> G y -> G z -> x * y = x * z-> y = z.
Admitted.

Theorem right_cancel : forall x y z:A, G x -> G y -> G z -> x * z = y * z -> x = y.
Admitted.

Theorem inv_uniq : forall x y:A, G x -> G y -> x * y = e -> x = y-.
Admitted.

Theorem inv_invol : forall x:A, G x -> x-- = x.
Admitted.

Theorem inv_op : forall x y:A, G x -> G y -> x- * y- = (y * x)-.
Admitted.

End Group.

