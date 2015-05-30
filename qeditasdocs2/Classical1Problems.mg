(* Title "Classical Principles in Simple Type Theory" *)
(* Author "Chad E. Brown" *)

(* Salt "2iXkDXTjL9DEMehVE" *)

(*** Diaconescu proof of excluded middle from choice. ***)
Theorem classic : forall P:prop, P \/ ~ P.
Admitted.

Theorem NNPP : forall p:prop, ~ ~ p -> p.
Admitted.

Theorem prop_deg : forall p:prop, p = True \/ p = False.
Admitted.

Theorem not_and_or_demorgan : forall A B:prop, ~(A /\ B) -> ~A \/ ~B.
Admitted.

Theorem not_and_or_demorgan_iff : forall A B:prop, ~(A /\ B) <-> ~A \/ ~B.
Admitted.

Section DeMorganQuants.

Variable A:SType.

Theorem not_all_ex_demorgan : forall P:A->prop, ~(forall x:A, P x) -> exists x:A, ~P x.
Admitted.

Theorem not_all_ex_demorgan_iff : forall P:A->prop, ~(forall x:A, P x) <-> exists x:A, ~P x.
Admitted.

End DeMorganQuants.

(*** Classical Logical Identities ***)
Theorem eq_neg_neg_id : eq (prop->prop) (fun x:prop => ~~x) (fun x:prop => x).
Admitted.

Theorem eq_true : True = (~False).
Admitted.

Theorem eq_and_nor : and = (fun (x y:prop) => ~(~x \/ ~y)).
Admitted.

Theorem eq_or_nand : or = (fun (x y:prop) => ~(~x /\ ~y)).
Admitted.

Theorem eq_or_imp : or = (fun (x y:prop) => ~ x -> y).
Admitted.

Theorem eq_and_imp : and = (fun (x y:prop) => ~ (x -> ~ y)).
Admitted.

Theorem eq_imp_or : (fun (x y:prop) => (x -> y)) = (fun (x y:prop) => (~x \/ y)).
Admitted.

Theorem eq_contrapositive : (fun (x y:prop) => (x -> y)) = (fun (x y:prop) => (~y -> ~x)).
Admitted.

Theorem eq_iff : iff = (eq prop).
Admitted.

Section EqThms.

Variable A:SType.

Theorem eq_sym_eq : (fun (x y:A) => x = y) = (fun (x y:A) => y = x).
Admitted.

Theorem eq_forall_nexists : (fun (f:A -> prop) => forall x:A, f x) = (fun (f:A -> prop) => ~exists x:A, ~f x).
Admitted.

Theorem eq_exists_nforall : (ex A) = (fun (f:A -> prop) => ~forall x:A, ~f x).
Admitted.

Theorem eq_leib2 : (fun (x y:A) => forall (p: A -> prop), ~ p x -> ~ p y) = (eq A).
Admitted.

Theorem eq_leib3 : (fun (x y:A) => forall (r: A -> A -> prop), (forall z:A, r z z) -> r x y) = (eq A).
Admitted.

Theorem eq_leib4 : (fun (x y:A) => forall (r: A -> A -> prop),~ r x y -> ~ (forall z:A, r z z)) = (eq A).
Admitted.

End EqThms.

Section Exercises.

Variable A:SType.

Example Drinker : forall d:A->prop, exists x:A, d x -> forall x:A, d x.
Admitted.

End Exercises.
