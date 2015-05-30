(* Title "Equality and Existential Quantification" *)
(* Author "Chad E. Brown" *)

(* Salt "FBjFQRGCGwP78kmG" *)

Section Poly1_eq.
Variable A:SType.

Definition eq : A -> A -> prop := fun x y => forall Q:A -> prop, Q x -> Q y.
Definition neq : A -> A -> prop := fun x y => ~eq x y.
End Poly1_eq.

Infix = 502 := eq.

(* Unicode <> "2260" *)
Infix <> 502 := neq.

Section Poly1_eqthms.
Variable A:SType.

Theorem eqE : forall x y:A, forall q:A->prop, q x -> x = y -> q y.
exact (fun x y q H1 H2 => H2 q H1).
Qed.

Theorem eqI : forall x:A, x = x.
exact (fun x q H => H).
Qed.

Theorem eq_sym : forall x y:A, x = y -> y = x.
Admitted.

Theorem eq_trans : forall x y z:A, x = y -> y = z -> x = z.
Admitted.

Theorem eqEr : forall x y:A, forall q:A->prop, q x -> y = x -> q y.
Admitted.

Theorem eq_symtrans1 : forall x y z:A, x = y -> z = y -> x = z.
Admitted.

Theorem eq_symtrans2 : forall x y z:A, y = x -> y = z -> x = z.
Admitted.

Theorem eq_trans3 : forall x0 x1 x2 x3:A, x0 = x1 -> x1 = x2 -> x2 = x3 -> x0 = x3.
Admitted.

Theorem eq_trans4 : forall x0 x1 x2 x3 x4:A, x0 = x1 -> x1 = x2 -> x2 = x3 -> x3 = x4 -> x0 = x4.
Admitted.

Theorem eq_trans5 : forall x0 x1 x2 x3 x4 x5:A, x0 = x1 -> x1 = x2 -> x2 = x3 -> x3 = x4 -> x4 = x5 -> x0 = x5.
Admitted.

Theorem neq_byprop : forall x y:A, forall P:A->prop, P x -> ~P y -> x <> y.
Admitted.

Theorem neq_sym : forall x y:A, x <> y -> y <> x.
Admitted.

End Poly1_eqthms.

Section Poly1_eq_Examples.
Variable A:SType.

Example rewrite_example_1 : forall P:A->A->prop, forall x y:A, x = y -> P x x -> P y y.
let P x y.
assume H1: x = y.
assume H2: P x x.
prove P y y.
rewrite <- H1.
prove P x x.
exact H2.
Qed.

Example rewrite_example_2 : forall P:A->A->prop, forall x y:A, x = y -> P y x -> P x y.
let P x y.
assume H1: x = y.
assume H2: P y x.
prove P x y.
rewrite H1.
prove P y y.
rewrite <- H1 at 2.
prove P y x.
exact H2.
Qed.

Example rewrite_example_3 : forall f:A->A->A, (forall x y:A, f x y = f y x) -> forall x y:A, f (f x y) y = f y (f y x).
let f.
assume H1: forall x y:A, f x y = f y x.
let x y.
prove f (f x y) y = f y (f y x).
rewrite H1.
prove f y (f x y) = f y (f y x).
rewrite H1 at 2.
prove f y (f y x) = f y (f y x).
apply (eqI A).
Qed.

End Poly1_eq_Examples.

Section Poly1_eq_Exercises.
Variable A:SType.

Example rewrite_exercise_1 : forall f:A->A->A, (forall x:A, f x x = x) -> (forall x y z:A, f (f x y) z = f x (f y z))
 -> forall x y:A, f x (f x y) = f x y.
Admitted.

Example rewrite_exercise_2 : forall f:A->A->A, forall e:A, (forall x:A, f x e = x) -> (forall x y:A, f x y = f y x)
 -> forall x:A, f x (f e x) = f x x.
Admitted.

Example rewrite_exercise_3 : forall f:A->A->A, forall z:A, (forall x:A, f x z = z) -> (forall x y:A, f x y = f y x)
 -> forall x:A, f x (f z x) = z.
Admitted.

End Poly1_eq_Exercises.

Section Poly1_exdef.
Variable A:SType.
Variable Q:A->prop.

Definition ex : prop := forall P:prop, (forall x:A, Q x -> P) -> P.
End Poly1_exdef.

(* Unicode exists "2203" *)
Binder+ exists , := ex.

Section Poly1_exthms.
Variable A:SType.

Theorem exE : forall P:A->prop, forall Q:prop, (forall x:A, P x -> Q) -> (exists x:A, P x) -> Q.
exact (fun P Q H1 H2 => H2 Q H1).
Qed.

Theorem exI : forall P:A->prop, forall x:A, P x -> exists x:A, P x.
exact (fun P x H1 Q H2 => H2 x H1).
Qed.

Example witness_example : forall x:A, exists y:A, x = y.
let x.
prove exists y:A, x = y.
witness x.
prove x = x.
exact (eqI A x).
Qed.

Theorem not_ex_all_demorgan : forall P:A->prop, (~exists x:A, P x) -> forall x:A, ~P x.
Admitted.

Theorem all_not_ex_demorgan : forall P:A->prop, (forall x:A, ~P x) -> ~exists x:A, P x.
Admitted.

Theorem not_ex_all_demorgan_iff : forall P:A->prop, (~exists x:A, P x) <-> forall x:A, ~P x.
Admitted.

Theorem ex_not_all_demorgan : forall P:A->prop, (exists x:A, ~P x) -> ~forall x:A, P x.
Admitted.

Theorem neq_byexprop : forall x y:A, (exists P:A->prop, P x /\ ~P y) -> x <> y.
Admitted.

End Poly1_exthms.

Section Poly1_exudef.
Variable A:SType.

Definition exu : (A->prop)->prop := fun P:A->prop => (exists x:A, P x) /\ (forall x y:A, P x -> P y -> eq A x y).

End Poly1_exudef.

(* Unicode exists! "2203" "0021" *)
Binder exists! , := exu.

Section Poly1_exuthms.
Variable A:SType.

Theorem exuE1 : forall P:A->prop, (exists! x:A, P x) -> exists x:A, P x.
Admitted.

Theorem exuE2 : forall P:A->prop, (exists! x:A, P x) -> forall x y:A, P x -> P y -> x = y.
Admitted.

Theorem exuI : forall P:A->prop, (exists x:A, P x) -> (forall x y:A, P x -> P y -> x = y) -> exists! x:A, P x.
Admitted.

Theorem exuEa : forall P:A->prop, (exists! x:A, P x) -> exists x:A, P x /\ forall y:A, P y -> y = x.
Admitted.

Theorem exuIa : forall P:A->prop, (exists x:A, P x /\ forall y:A, P y -> y = x) -> exists! x:A, P x.
Admitted.

End Poly1_exuthms.

Section EqExercises.

Variable A:SType.

Theorem eq_leastrefl_1 : forall x y:A, (forall r:A->A->prop, (forall z:A, r z z) -> r x y) -> x = y.
Admitted.

Theorem eq_leastrefl_2 : forall x y:A, x = y -> (forall r:A->A->prop, (forall z:A, r z z) -> r x y).
Admitted.

End EqExercises.

Section Poly1.

Variable A:SType.

Theorem exm2I : forall P:A->A->prop, forall x1 x2:A, P x1 x2 -> exists x1:A, exists x2:A, P x1 x2.
Admitted.

Theorem exm2E : forall P:A->A->prop, (exists x1:A, exists x2:A, P x1 x2)
 -> forall p:prop, (forall x1 x2:A, P x1 x2 -> p) -> p.
Admitted.

Theorem exm3I : forall P:A->A->A->prop, forall x1 x2 x3:A, P x1 x2 x3 -> exists x1:A, exists x2:A, exists x3:A, P x1 x2 x3.
Admitted.

Theorem exm3E : forall P:A->A->A->prop, (exists x1:A, exists x2:A, exists x3:A, P x1 x2 x3)
 -> forall p:prop, (forall x1 x2 x3:A, P x1 x2 x3 -> p) -> p.
Admitted.

Theorem exm4I : forall P:A->A->A->A->prop, forall x1 x2 x3 x4:A, P x1 x2 x3 x4 -> exists x1:A, exists x2:A, exists x3:A, exists x4:A, P x1 x2 x3 x4.
Admitted.

Theorem exm4E : forall P:A->A->A->A->prop, (exists x1:A, exists x2:A, exists x3:A, exists x4:A, P x1 x2 x3 x4)
 -> forall p:prop, (forall x1 x2 x3 x4:A, P x1 x2 x3 x4 -> p) -> p.
Admitted.

Theorem exm5I : forall P:A->A->A->A->A->prop, forall x1 x2 x3 x4 x5:A, P x1 x2 x3 x4 x5 -> exists x1:A, exists x2:A, exists x3:A, exists x4:A, exists x5:A, P x1 x2 x3 x4 x5.
Admitted.

Theorem exm5E : forall P:A->A->A->A->A->prop, (exists x1:A, exists x2:A, exists x3:A, exists x4:A, exists x5:A, P x1 x2 x3 x4 x5)
 -> forall p:prop, (forall x1 x2 x3 x4 x5:A, P x1 x2 x3 x4 x5 -> p) -> p.
Admitted.

Variable P:A->prop.
Variable Q:A->prop.

Theorem exandI : forall x:A, P x -> Q x -> exists x:A, P x /\ Q x.
Admitted.

Theorem exandE : (exists x:A, P x /\ Q x) -> forall p:prop, (forall x:A, P x -> Q x -> p) -> p.
Admitted.

End Poly1.

Section Poly2a.

Variable A B:SType.

Theorem ex2I : forall P:A->B->prop, forall x1:A, forall x2:B, P x1 x2 -> exists x1:A, exists x2:B, P x1 x2.
Admitted.

Theorem ex2E : forall P:A->B->prop, (exists x1:A, exists x2:B, P x1 x2)
 -> forall p:prop, (forall x1:A, forall x2:B, P x1 x2 -> p) -> p.
Admitted.

End Poly2a.

Section Poly2b.

Variable A B:SType.

Variable P:A->prop.
Variable Q:A->B->prop.
Variable R:A->B->prop.

Theorem exand2I : forall x:A, P x -> forall y:B, Q x y -> R x y -> exists x:A, P x /\ exists y:B, Q x y /\ R x y.
Admitted.

Theorem exand2E : (exists x:A, P x /\ exists y:B, Q x y /\ R x y)
 -> forall p:prop, (forall x:A, P x -> forall y:B, Q x y -> R x y -> p) -> p.
Admitted.

End Poly2b.
