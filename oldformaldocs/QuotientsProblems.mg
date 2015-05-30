(* Title "Quotients" *)
(* Author "Chad E. Brown" *)

(* Salt "2GxJfmdu1bwYzhNYg" *)

Section QuotientsPoly1.

Variable A:SType.

Definition canonical_elt : (A->A->prop)->A->A := fun R:A->A->prop => fun x:A => some y:A, R x y.

(* Treasure "19YiGHyyqB1tw9LUmWdp2NATD3Q28ZaWzD" *)
Theorem canonical_elt_rel : forall R:A->A->prop, forall x:A, R x x -> R x (canonical_elt R x).
Admitted.

(* Treasure "1BQT8hfMVpgthxGNvQd9igsb2NwbTbDUkH" *)
Theorem canonical_elt_eq : forall R:A->A->prop, per A R -> forall x y:A, R x y -> canonical_elt R x = canonical_elt R y.
Admitted.

(* Treasure "1PB8DKmASftrzSvcvJBogwpAehT29ocxEg" *)
Theorem canonical_elt_idem : forall R:A->A->prop, per A R -> forall x:A, R x x -> canonical_elt R x = canonical_elt R (canonical_elt R x).
Admitted.

Definition quotient : (A->A->prop)->A->prop := fun R:A->A->prop => fun x:A => R x x /\ x = canonical_elt R x.

(* Treasure "18ijZZ39Axynz6VVivHtWaa1kdRrarhwDk" *)
Theorem quotient_prop1 : forall R:A->A->prop,
 forall x:A, quotient R x -> R x x.
Admitted.

(* Treasure "18sCZnfBmbtN9eRCgU9STe3fQysLedSwMQ" *)
Theorem quotient_prop2 : forall R:A->A->prop, per A R ->
 forall x y:A, quotient R x -> quotient R y -> R x y -> x = y.
Admitted.

Definition canonical_elt_def : (A->A->prop)->(A->A)->A->A := fun R:A->A->prop => fun d:A->A => fun x:A => if (R x (d x)) then (d x) else (canonical_elt R x).

(* Treasure "13ZzNKXj5Sguz1da95FFZzGpqPjyS52nHM" *)
Theorem canonical_elt_def_rel : forall R:A->A->prop, forall d:A->A, forall x:A, R x x -> R x (canonical_elt_def R d x).
Admitted.

(* Treasure "1HdG5LcTh6GYX7W6RGYzqprQQVostCdr3B" *)
Theorem canonical_elt_def_eq :
 forall R:A->A->prop, per A R ->
 forall d:A->A, (forall x y:A, R x y -> d x = d y) ->
 forall x y:A, R x y -> canonical_elt_def R d x = canonical_elt_def R d y.
Admitted.

(* Treasure "1E2K6nwut2U3vkkRcJrWUmdoPVffeHuBbN" *)
Theorem canonical_elt_def_idem :
 forall R:A->A->prop, per A R ->
 forall d:A->A, (forall x y:A, R x y -> d x = d y) ->
 forall x:A, R x x -> canonical_elt_def R d x = canonical_elt_def R d (canonical_elt_def R d x).
Admitted.

Definition quotient_def : (A->A->prop)->(A->A)->A->prop := fun R:A->A->prop => fun d:A->A => fun x:A => R x x /\ x = canonical_elt_def R d x.

(* Treasure "189qz5rBsPqq8V77qkJTvXoi5v8UgBxebM" *)
Theorem quotient_def_prop0 :
 forall R:A->A->prop, per A R ->
 forall d:A->A,
 forall x:A, R x (d x) -> x = d x -> quotient_def R d x.
Admitted.

(* Treasure "18xn7tJtqg96SigoSQ6XWvzvYFnZUVnnfk" *)
Theorem quotient_def_prop1 :
 forall R:A->A->prop,
 forall d:A->A,
 forall x:A, quotient_def R d x -> R x x.
Admitted.

(* Treasure "19C1iX5kfJZXiM3cYH5p3E2EstCPXogBgw" *)
Theorem quotient_def_prop2 :
 forall R:A->A->prop, per A R ->
 forall d:A->A, (forall x y:A, R x y -> d x = d y) ->
 forall x y:A, quotient_def R d x -> quotient_def R d y -> R x y -> x = y.
Admitted.

End QuotientsPoly1.
