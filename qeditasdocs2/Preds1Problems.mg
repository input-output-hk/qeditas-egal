(* Title "Predicates and Extensionality" *)
(* Author "Chad E. Brown" *)

(* Salt "xnE3owiTuEcAVzpj" *)

Section PredPoly1.
Variable A:SType.

Definition pred_empty : A->prop := fun x:A => False.

Definition pred_full : A->prop := fun x:A => True.

Theorem pred_empty_min : forall P:A->prop, pred_empty c= P.
Admitted.

Theorem pred_full_max : forall P:A->prop, P c= pred_full.
Admitted.

Definition pred_union : (A->prop)->(A->prop)->(A->prop) :=
 fun P Q:A->prop => fun x:A => P x \/ Q x.

Definition pred_intersect : (A->prop)->(A->prop)->(A->prop) :=
 fun P Q:A->prop => fun x:A => P x /\ Q x.

Definition pred_compl : (A->prop)->(A->prop) :=
 fun P:A->prop => fun x:A => ~P x.

Theorem pred_union_ub1 : forall P Q:A->prop, P c= pred_union P Q.
Admitted.

Theorem pred_union_ub2 : forall P Q:A->prop, Q c= pred_union P Q.
Admitted.

Theorem pred_union_min : forall P Q R:A->prop, P c= R -> Q c= R -> pred_union P Q c= R.
Admitted.

Theorem pred_intersect_lb1 : forall P Q:A->prop, pred_intersect P Q c= P.
Admitted.

Theorem pred_intersect_lb2 : forall P Q:A->prop, pred_intersect P Q c= Q.
Admitted.

Theorem pred_intersect_max : forall P Q R:A->prop, R c= P -> R c= Q -> R c= pred_intersect P Q.
Admitted.

Definition bigintersect := fun (D:(A->prop)->prop) (x:A) => forall P:A->prop, D P -> P x.

Definition bigunion := fun (D:(A->prop)->prop) (x:A) => exists P:A->prop, D P /\ P x.

End PredPoly1.

(** Propositional extensionality: Equivalent propositions are equal. **)

Axiom prop_ext : forall A B:prop, (A <-> B) -> A = B.

Theorem prop_ext2 : forall A B:prop, (A -> B) -> (B -> A) -> A = B.
Admitted.

(** Functional extensionality: Equivalent functions are equal. **)
Section FE.
Variable A B:SType.
Axiom func_ext : forall (f g : A -> B), (forall x:A, f x = g x) -> f = g.
End FE.

Section PE.
Variable A:SType.

Theorem pred_ext : forall (P Q : A -> prop), P c= Q -> Q c= P -> P = Q.
Admitted.

End PE.

Section RE.
Variable A B:SType.

Theorem reln_ext : forall (R S : A -> B -> prop), R c= S -> S c= R -> R = S.
Admitted.

End RE.

(** Consequences of Extensionality **)
Section PredPoly2.

Variable A:SType.

Let E := pred_empty A.
Let C := pred_compl A.
Let I := pred_intersect A.
Let U := pred_union A.

Theorem pred_intersect_compl_empty : forall P:A->prop, I P (C P) = E.
Admitted.

Theorem pred_union_com : forall P Q:A->prop, U P Q = U Q P.
Admitted.

Theorem pred_union_asso : forall P Q R:A->prop, U P (U Q R) = U (U P Q) R.
Admitted.

Theorem pred_intersect_com : forall P Q:A->prop, I P Q = I Q P.
Admitted.

Theorem pred_intersect_asso : forall P Q R:A->prop, I P (I Q R) = I (I P Q) R.
Admitted.

Theorem pred_intersect_union_distrL : forall P Q R:A->prop, I P (U Q R) = U (I P Q) (I P R).
Admitted.

Theorem pred_intersect_union_distrR : forall P Q R:A->prop, I (U P Q) R = U (I P R) (I Q R).
Admitted.

Theorem pred_union_intersect_distrL : forall P Q R:A->prop, U P (I Q R) = I (U P Q) (U P R).
Admitted.

Theorem pred_union_intersect_distrR : forall P Q R:A->prop, U (I P Q) R = I (U P R) (U Q R).
Admitted.

End PredPoly2.
