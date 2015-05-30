(* Title "Exactly 1 of 2 or 3" *)
(* Author "Chad E. Brown" *)

(* Salt "2JCgFSwTWUd4YsNAm" *)

Definition exactly1of2 : prop->prop->prop := fun A B:prop =>
A /\ ~B \/ ~A /\ B.

Theorem exactly1of2_I1 : forall A B:prop, A -> ~B -> exactly1of2 A B.
Admitted.

Theorem exactly1of2_I2 : forall A B:prop, ~A -> B -> exactly1of2 A B.
Admitted.

Theorem exactly1of2_impI1 : forall A B:prop, (A -> ~B) -> (~A -> B) -> exactly1of2 A B.
Admitted.

Theorem exactly1of2_impI2 : forall A B:prop, (B -> ~A) -> (~B -> A) -> exactly1of2 A B.
Admitted.

Theorem exactly1of2_E : forall A B:prop, exactly1of2 A B ->
forall p:prop,
(A -> ~B -> p) ->
(~A -> B -> p) ->
p.
Admitted.

Theorem exactly1of2_or : forall A B:prop, exactly1of2 A B -> A \/ B.
Admitted.

Theorem exactly1of2_impn12 : forall A B:prop, exactly1of2 A B -> A -> ~B.
Admitted.

Theorem exactly1of2_impn21 : forall A B:prop, exactly1of2 A B -> B -> ~A.
Admitted.

Theorem exactly1of2_nimp12 : forall A B:prop, exactly1of2 A B -> ~A -> B.
Admitted.

Theorem exactly1of2_nimp21 : forall A B:prop, exactly1of2 A B -> ~B -> A.
Admitted.

Definition exactly1of3 : prop->prop->prop->prop := fun A B C:prop =>
exactly1of2 A B /\ ~C \/ ~A /\ ~B /\ C.

Theorem exactly1of3_I1 : forall A B C:prop, A -> ~B -> ~C -> exactly1of3 A B C.
Admitted.

Theorem exactly1of3_I2 : forall A B C:prop, ~A -> B -> ~C -> exactly1of3 A B C.
Admitted.

Theorem exactly1of3_I3 : forall A B C:prop, ~A -> ~B -> C -> exactly1of3 A B C.
Admitted.

Theorem exactly1of3_impI1 : forall A B C:prop, (A -> ~B) -> (A -> ~C) -> (B -> ~C) -> (~A -> B \/ C) -> exactly1of3 A B C.
Admitted.

Theorem exactly1of3_impI2 : forall A B C:prop, (B -> ~A) -> (B -> ~C) -> (A -> ~C) -> (~B -> A \/ C) -> exactly1of3 A B C.
Admitted.

Theorem exactly1of3_impI3 : forall A B C:prop, (C -> ~A) -> (C -> ~B) -> (A -> ~B) -> (~A -> B) -> exactly1of3 A B C.
Admitted.

Theorem exactly1of3_E : forall A B C:prop, exactly1of3 A B C ->
forall p:prop,
(A -> ~B -> ~C -> p) ->
(~A -> B -> ~C -> p) ->
(~A -> ~B -> C -> p) ->
p.
Admitted.

Theorem exactly1of3_or : forall A B C:prop, exactly1of3 A B C -> A \/ B \/ C.
Admitted.

Theorem exactly1of3_impn12 : forall A B C:prop, exactly1of3 A B C -> A -> ~B.
Admitted.

Theorem exactly1of3_impn13 : forall A B C:prop, exactly1of3 A B C -> A -> ~C.
Admitted.

Theorem exactly1of3_impn21 : forall A B C:prop, exactly1of3 A B C -> B -> ~A.
Admitted.

Theorem exactly1of3_impn23 : forall A B C:prop, exactly1of3 A B C -> B -> ~C.
Admitted.

Theorem exactly1of3_impn31 : forall A B C:prop, exactly1of3 A B C -> C -> ~A.
Admitted.

Theorem exactly1of3_impn32 : forall A B C:prop, exactly1of3 A B C -> C -> ~B.
Admitted.

Theorem exactly1of3_nimp1 : forall A B C:prop, exactly1of3 A B C -> ~A -> B \/ C.
Admitted.

Theorem exactly1of3_nimp2 : forall A B C:prop, exactly1of3 A B C -> ~B -> A \/ C.
Admitted.

Theorem exactly1of3_nimp3 : forall A B C:prop, exactly1of3 A B C -> ~C -> A \/ B.
Admitted.
