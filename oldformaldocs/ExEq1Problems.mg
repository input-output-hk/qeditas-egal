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

(* Treasure "1Jj6DrsAiEgQ4AV8JzkAtFfb8Bwmj5LG2K" *)
Theorem eq_sym : forall x y:A, x = y -> y = x.
Admitted.

(* Treasure "1B8GmHi8bU3G9HW7CzYeTcXLBTAJWRYR8i" *)
Theorem eq_trans : forall x y z:A, x = y -> y = z -> x = z.
Admitted.

(* Treasure "1K8Jo1YZXRYuESuGtN9QVPoRUXf8bSXe7t" *)
Theorem eqEr : forall x y:A, forall q:A->prop, q x -> y = x -> q y.
Admitted.

(* Treasure "1NPBsFPz7BYqogqprxNMgRSfJdruPUfFwn" *)
Theorem eq_symtrans1 : forall x y z:A, x = y -> z = y -> x = z.
Admitted.

(* Treasure "1GuvKdot1TXVexnfLUd1DPkLpyXK1BopuU" *)
Theorem eq_symtrans2 : forall x y z:A, y = x -> y = z -> x = z.
Admitted.

(* Treasure "1KavmUJUYberYtgBJk49Bo9bKz4M1jBKke" *)
Theorem eq_trans3 : forall x0 x1 x2 x3:A, x0 = x1 -> x1 = x2 -> x2 = x3 -> x0 = x3.
Admitted.

(* Treasure "1DnQcL4N26oBiRm71BgRQjMdCqwbUFXwty" *)
Theorem eq_trans4 : forall x0 x1 x2 x3 x4:A, x0 = x1 -> x1 = x2 -> x2 = x3 -> x3 = x4 -> x0 = x4.
Admitted.

(* Treasure "1FKY2qA4Bw9aLVbSPF8agcuSPbBTMvenZX" *)
Theorem eq_trans5 : forall x0 x1 x2 x3 x4 x5:A, x0 = x1 -> x1 = x2 -> x2 = x3 -> x3 = x4 -> x4 = x5 -> x0 = x5.
Admitted.

(* Treasure "1DDDXvSmtq7yfSGXHsYXcG8GN3eZhudS9f" *)
Theorem neq_byprop : forall x y:A, forall P:A->prop, P x -> ~P y -> x <> y.
Admitted.

(* Treasure "12UfzGh3mcKVfbVvhXwkq9mowgWiD6SFyp" *)
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

(* Treasure "18jWBMEYymtGXv8QpwNW5hGs5C7pQ9ZtrX" *)
Example rewrite_exercise_1 : forall f:A->A->A, (forall x:A, f x x = x) -> (forall x y z:A, f (f x y) z = f x (f y z))
 -> forall x y:A, f x (f x y) = f x y.
Admitted.

(* Treasure "1Gj45nm1nitkgQxFfkBc76iFMy2VxFD8mj" *)
Example rewrite_exercise_2 : forall f:A->A->A, forall e:A, (forall x:A, f x e = x) -> (forall x y:A, f x y = f y x)
 -> forall x:A, f x (f e x) = f x x.
Admitted.

(* Treasure "1KiWjq1iFMrhgRSCNBTSLcxd7FTn4JobCs" *)
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

(* Treasure "1HeeTDKhoWgdTVm6DynYD778AdAiZXb45W" *)
Theorem not_ex_all_demorgan : forall P:A->prop, (~exists x:A, P x) -> forall x:A, ~P x.
Admitted.

(* Treasure "1C473w4HKd1Sj9nXd9GfoyCfhKjg7Q6HSd" *)
Theorem all_not_ex_demorgan : forall P:A->prop, (forall x:A, ~P x) -> ~exists x:A, P x.
Admitted.

(* Treasure "1PVhpDB4wWCh4wtyufneLHDYos4AFHHC2B" *)
Theorem not_ex_all_demorgan_iff : forall P:A->prop, (~exists x:A, P x) <-> forall x:A, ~P x.
Admitted.

(* Treasure "15KRBFwzjih3WbVwVvtWruFhKRgP71rCeb" *)
Theorem ex_not_all_demorgan : forall P:A->prop, (exists x:A, ~P x) -> ~forall x:A, P x.
Admitted.

(* Treasure "1CMHsqPsEgdM5KT3ErQdG6ucV6MyNNX382" *)
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

(* Treasure "1KSuPratJA7DRaARX3DhJbStBNqKkL1Xnu" *)
Theorem exuE1 : forall P:A->prop, (exists! x:A, P x) -> exists x:A, P x.
Admitted.

(* Treasure "16MtACqU5quss21NyVcVLK8qCAjvSqo3cd" *)
Theorem exuE2 : forall P:A->prop, (exists! x:A, P x) -> forall x y:A, P x -> P y -> x = y.
Admitted.

(* Treasure "1AMGKVgKB1YstgXSnKuCZRGL4MBQCkpgnb" *)
Theorem exuI : forall P:A->prop, (exists x:A, P x) -> (forall x y:A, P x -> P y -> x = y) -> exists! x:A, P x.
Admitted.

(* Treasure "1KxAj7j3cy17Gse9zhKZKPwqht1FoKsuW1" *)
Theorem exuEa : forall P:A->prop, (exists! x:A, P x) -> exists x:A, P x /\ forall y:A, P y -> y = x.
Admitted.

(* Treasure "1GUbgPHzuV47UbbMHmU4PrBWfML63PK7ZD" *)
Theorem exuIa : forall P:A->prop, (exists x:A, P x /\ forall y:A, P y -> y = x) -> exists! x:A, P x.
Admitted.

End Poly1_exuthms.

Section EqExercises.

Variable A:SType.

(* Treasure "124DBXsyF15PPW7ZUF9BBFZQNxg4VY3CkW" *)
Theorem eq_leastrefl_1 : forall x y:A, (forall r:A->A->prop, (forall z:A, r z z) -> r x y) -> x = y.
Admitted.

(* Treasure "1GhFfbvVr9M7Hvp7yf4818cDETddQ8aDjB" *)
Theorem eq_leastrefl_2 : forall x y:A, x = y -> (forall r:A->A->prop, (forall z:A, r z z) -> r x y).
Admitted.

End EqExercises.

Section Poly1.

Variable A:SType.

(* Treasure "1DhpPCnE2f3PinoCWaBptnheg2vPnKZMaR" *)
Theorem exm2I : forall P:A->A->prop, forall x1 x2:A, P x1 x2 -> exists x1:A, exists x2:A, P x1 x2.
Admitted.

(* Treasure "12CqTnnw8YhYYe2GS4jk3HFjCkQ3TQxkhL" *)
Theorem exm2E : forall P:A->A->prop, (exists x1:A, exists x2:A, P x1 x2)
 -> forall p:prop, (forall x1 x2:A, P x1 x2 -> p) -> p.
Admitted.

(* Treasure "1MpvLNoB3wtvGVUNHpgxp3MPJpjMFBp7Zo" *)
Theorem exm3I : forall P:A->A->A->prop, forall x1 x2 x3:A, P x1 x2 x3 -> exists x1:A, exists x2:A, exists x3:A, P x1 x2 x3.
Admitted.

(* Treasure "1AHPffUfupM2ovbBfvoq9W4hTB9uN5ka3E" *)
Theorem exm3E : forall P:A->A->A->prop, (exists x1:A, exists x2:A, exists x3:A, P x1 x2 x3)
 -> forall p:prop, (forall x1 x2 x3:A, P x1 x2 x3 -> p) -> p.
Admitted.

(* Treasure "1N7TyGakfdXXqFU6kuUWR5kG6u6h2LFZRn" *)
Theorem exm4I : forall P:A->A->A->A->prop, forall x1 x2 x3 x4:A, P x1 x2 x3 x4 -> exists x1:A, exists x2:A, exists x3:A, exists x4:A, P x1 x2 x3 x4.
Admitted.

(* Treasure "1BoPiNxperzXgZQjRKoEZBLgdSTHeTUuDy" *)
Theorem exm4E : forall P:A->A->A->A->prop, (exists x1:A, exists x2:A, exists x3:A, exists x4:A, P x1 x2 x3 x4)
 -> forall p:prop, (forall x1 x2 x3 x4:A, P x1 x2 x3 x4 -> p) -> p.
Admitted.

(* Treasure "1NyL7wiZSKa2619LkCiS9HzCas3RXZfJZm" *)
Theorem exm5I : forall P:A->A->A->A->A->prop, forall x1 x2 x3 x4 x5:A, P x1 x2 x3 x4 x5 -> exists x1:A, exists x2:A, exists x3:A, exists x4:A, exists x5:A, P x1 x2 x3 x4 x5.
Admitted.

(* Treasure "1HprUrrNYYHFvWJeovqbpdtEfnP1GuU5D7" *)
Theorem exm5E : forall P:A->A->A->A->A->prop, (exists x1:A, exists x2:A, exists x3:A, exists x4:A, exists x5:A, P x1 x2 x3 x4 x5)
 -> forall p:prop, (forall x1 x2 x3 x4 x5:A, P x1 x2 x3 x4 x5 -> p) -> p.
Admitted.

Variable P:A->prop.
Variable Q:A->prop.

(* Treasure "13wqvspfL9bmW84yh7FNj45ScNW2nLERmH" *)
Theorem exandI : forall x:A, P x -> Q x -> exists x:A, P x /\ Q x.
Admitted.

(* Treasure "1NQv1WF9n4t1rF1buW6Bs8MAmUTd36cjDh" *)
Theorem exandE : (exists x:A, P x /\ Q x) -> forall p:prop, (forall x:A, P x -> Q x -> p) -> p.
Admitted.

End Poly1.

Section Poly2a.

Variable A B:SType.

(* Treasure "1FFJBsipjnuf756bLj7c7Lb8F6MvJhD3Aw" *)
Theorem ex2I : forall P:A->B->prop, forall x1:A, forall x2:B, P x1 x2 -> exists x1:A, exists x2:B, P x1 x2.
Admitted.

(* Treasure "1Pxz4wMF883iAQjgJCSD59adtbAXQJPQLx" *)
Theorem ex2E : forall P:A->B->prop, (exists x1:A, exists x2:B, P x1 x2)
 -> forall p:prop, (forall x1:A, forall x2:B, P x1 x2 -> p) -> p.
Admitted.

End Poly2a.

Section Poly2b.

Variable A B:SType.

Variable P:A->prop.
Variable Q:A->B->prop.
Variable R:A->B->prop.

(* Treasure "17uti4aRQsK3uMu7R8Zj6G65AD7QBZgxJU" *)
Theorem exand2I : forall x:A, P x -> forall y:B, Q x y -> R x y -> exists x:A, P x /\ exists y:B, Q x y /\ R x y.
Admitted.

(* Treasure "1GXQx5iqmXaQjtL2YKGhU5PuPiuze8ERPX" *)
Theorem exand2E : (exists x:A, P x /\ exists y:B, Q x y /\ R x y)
 -> forall p:prop, (forall x:A, P x -> forall y:B, Q x y -> R x y -> p) -> p.
Admitted.

End Poly2b.
