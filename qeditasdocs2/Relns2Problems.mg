(* Title "Relations, Functions and Choice" *)
(* Author "Chad E. Brown" *)

(* Salt "4w4Ara2THhpx6TpZ" *)

Section RelnFunsPoly2.
Variable A B:SType.

Definition functionalreln : (A->B->prop)->prop := fun R => forall x:A, forall y y':B, R x y -> R x y' -> y = y'.

Definition injectivereln : (A->B->prop)->prop := fun R => forall y:B, forall x x':A, R x y -> R x' y -> x = x'.

Definition totalreln : (A->B->prop)->prop := fun R => forall x:A, exists y:B, R x y.

Definition surjectivereln : (A->B->prop)->prop := fun R => forall y:B, exists x:A, R x y.

Theorem function_functional : forall f:A->B, functionalreln (fun (x:A) (y:B) => f x = y).
Admitted.

Theorem function_total : forall f:A->B, totalreln (fun (x:A) (y:B) => f x = y).
Admitted.

Definition injective : (A->B)->prop := fun f => forall x x':A, f x = f x' -> x = x'.

Definition surjective : (A->B)->prop := fun f => forall y:B, exists x:A, f x = y.

Theorem injective_fun_reln : forall f:A->B, injective f -> injectivereln (fun (x:A) (y:B) => f x = y).
Admitted.

Theorem surjective_fun_reln : forall f:A->B, surjective f -> surjectivereln (fun (x:A) (y:B) => f x = y).
Admitted.

End RelnFunsPoly2.

(** We include an epsilon operator (Eps) as a form of the axiom of choice. **)

Section Choice.
Variable A:SType.
Parameter Eps : (A->prop)->A.
Axiom EpsR : forall P:A->prop, forall x:A, P x -> P (Eps P).
End Choice.

Binder some , := Eps.

Section ChoiceThms.
Variable A:SType.

Theorem EpsR2 : forall P:A->prop, (exists x:A, P x) -> P (some x:A, P x).
Admitted.

Theorem InhEx : exists x:A, True.
Admitted.

Theorem Inh : forall (P:prop), (forall x:A, P) -> P.
Admitted.

End ChoiceThms.

Section ChoiceExercises1.
Variable A:SType.

Theorem EpsComplR : exists e:(A->prop)->A, forall P:A->prop, (exists x:A, ~P x) -> ~P (e P).
Admitted.

End ChoiceExercises1.

Section ChoiceExercises2.
Variable A B:SType.

Theorem Skolem : forall R:A->B->prop, totalreln A B R -> exists f:A->B, forall x:A, R x (f x).
Admitted.

Theorem Eps2R : exists (e1:(A->B->prop)->A) (e2:(A->B->prop)->B), forall R:A->B->prop, (exists (x:A) (y:B), R x y) -> R (e1 R) (e2 R).
Admitted.

Theorem surj_inverse_ex : forall f:A->B, surjective A B f -> exists g:B->A, forall y:B, f (g y) = y.
Admitted.

Theorem inj_inverse_ex : forall f:A->B, injective A B f -> exists g:B->A, forall x:A, g (f x) = x.
Admitted.

End ChoiceExercises2.

Section ChoiceExercises3.
Variable A:SType.

Theorem SurjectiveCantor : ~exists g:A->A->prop, surjective A (A->prop) g.
Admitted.

Theorem InjectiveCantor : forall h:(A->prop)->A, ~injective (A->prop) A h.
Admitted.

End ChoiceExercises3.
