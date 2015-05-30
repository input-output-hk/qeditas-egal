(* Title "Equality and Existential Quantification" *)
(* Author "Chad E. Brown" *)

(* Salt "FBjFQRGCGwP78kmG" *)

Require "3FEFE9FD1D796C54F5A5ECCC3DB23E61ED1B9DDC". (*** Added for Qeditas. - White, 2015 ***)

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
exact (fun x y H => H (fun y => y = x) (eqI x)).
Qed.

Theorem eq_trans : forall x y z:A, x = y -> y = z -> x = z.
exact (fun x y z H1 H2 => H2 (fun z => x = z) H1).
Qed.

Theorem eqEr : forall x y:A, forall q:A->prop, q x -> y = x -> q y.
exact (fun x y q H1 H2 => eq_sym y x H2 q H1).
Qed.

Theorem eq_symtrans1 : forall x y z:A, x = y -> z = y -> x = z.
exact (fun x y z H1 H2 => eq_trans x y z H1 (eq_sym z y H2)).
Qed.

Theorem eq_symtrans2 : forall x y z:A, y = x -> y = z -> x = z.
exact (fun x y z H1 H2 => eq_trans x y z (eq_sym y x H1) H2).
Qed.

Theorem eq_trans3 : forall x0 x1 x2 x3:A, x0 = x1 -> x1 = x2 -> x2 = x3 -> x0 = x3.
exact (fun x0 x1 x2 x3 H1 H2 H3 => eq_trans x0 x2 x3 (eq_trans x0 x1 x2 H1 H2) H3).
Qed.

Theorem eq_trans4 : forall x0 x1 x2 x3 x4:A, x0 = x1 -> x1 = x2 -> x2 = x3 -> x3 = x4 -> x0 = x4.
exact (fun x0 x1 x2 x3 x4 H1 H2 H3 H4 => eq_trans x0 x3 x4 (eq_trans3 x0 x1 x2 x3 H1 H2 H3) H4).
Qed.

Theorem eq_trans5 : forall x0 x1 x2 x3 x4 x5:A, x0 = x1 -> x1 = x2 -> x2 = x3 -> x3 = x4 -> x4 = x5 -> x0 = x5.
exact (fun x0 x1 x2 x3 x4 x5 H1 H2 H3 H4 H5 => eq_trans x0 x4 x5 (eq_trans4 x0 x1 x2 x3 x4 H1 H2 H3 H4) H5).
Qed.

Theorem neq_byprop : forall x y:A, forall P:A->prop, P x -> ~P y -> x <> y.
exact (fun (x y : A) (P : A -> prop) (H1 : P x) (H2 : ~ P y) (H3 : x = y) => H2 (H3 P H1)).
Qed.

Theorem neq_sym : forall x y:A, x <> y -> y <> x.
let x y.
assume H1: x <> y. 
assume H2: y = x. 
exact (H1 (eq_sym y x H2)).
Qed.

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
let f.
assume H1: forall x:A, f x x = x.
assume H2: forall x y z:A, f (f x y) z = f x (f y z).
let x y.
prove f x (f x y) = f x y.
rewrite <- H2.
prove f (f x x) y = f x y.
rewrite H1.
prove f x y = f x y.
apply (eqI A).
Qed.

Example rewrite_exercise_2 : forall f:A->A->A, forall e:A, (forall x:A, f x e = x) -> (forall x y:A, f x y = f y x)
 -> forall x:A, f x (f e x) = f x x.
let f e.
assume H1: forall x:A, f x e = x.
assume H2: forall x y:A, f x y = f y x.
let x.
prove f x (f e x) = f x x.
rewrite <- H2 at 2.
prove f x (f x e) = f x x.
rewrite H1.
prove f x x = f x x.
apply (eqI A).
Qed.

Example rewrite_exercise_3 : forall f:A->A->A, forall z:A, (forall x:A, f x z = z) -> (forall x y:A, f x y = f y x)
 -> forall x:A, f x (f z x) = z.
let f z.
assume H1: forall x:A, f x z = z.
assume H2: forall x y:A, f x y = f y x.
let x.
prove f x (f z x) = z.
rewrite <- H2 at 2.
prove f x (f x z) = z.
rewrite H1.
prove f x z = z.
apply H1.
Qed.

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
exact (fun P u x v => u (exI P x v)).
Qed.

Theorem all_not_ex_demorgan : forall P:A->prop, (forall x:A, ~P x) -> ~exists x:A, P x.
exact (fun P u v => v False u).
Qed.

Theorem not_ex_all_demorgan_iff : forall P:A->prop, (~exists x:A, P x) <-> forall x:A, ~P x.
exact (fun P => iffI (~exists x:A, P x) (forall x:A, ~P x) (not_ex_all_demorgan P) (all_not_ex_demorgan P)).
Qed.

Theorem ex_not_all_demorgan : forall P:A->prop, (exists x:A, ~P x) -> ~forall x:A, P x.
exact (fun P u v => u False (fun x w => w (v x))).
Qed.

Theorem neq_byexprop : forall x y:A, (exists P:A->prop, P x /\ ~P y) -> x <> y.
let x y:A.
assume H1 : exists P:A -> prop, P x /\ ~ P y.
apply H1.
let P:A->prop.
assume H2: P x /\ ~P y.
exact (H2 (x <> y) (neq_byprop A x y P)).
Qed.

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
exact (fun P => andEL (ex A P) (forall x y:A, P x -> P y -> eq A x y)).
Qed.

Theorem exuE2 : forall P:A->prop, (exists! x:A, P x) -> forall x y:A, P x -> P y -> x = y.
exact (fun P => andER (ex A P) (forall x y:A, P x -> P y -> eq A x y)).
Qed.

Theorem exuI : forall P:A->prop, (exists x:A, P x) -> (forall x y:A, P x -> P y -> x = y) -> exists! x:A, P x.
exact (fun P => andI (ex A P) (forall x y:A, P x -> P y -> eq A x y)).
Qed.

Theorem exuEa : forall P:A->prop, (exists! x:A, P x) -> exists x:A, P x /\ forall y:A, P y -> y = x.
let P. assume H1. apply H1.
prove ((exists x:A, P x) -> (forall x y:A, P x -> P y -> x = y) -> exists x:A, P x /\ forall y:A, P y -> y = x).
assume H2 H3. apply H2.
prove (forall x:A, P x -> exists x:A, P x /\ forall y:A, P y -> y = x).
let x. assume H4.
witness x. apply andI.
- exact H4.
- let y. assume H5. exact (H3 y x H5 H4).
Qed.

Theorem exuIa : forall P:A->prop, (exists x:A, P x /\ forall y:A, P y -> y = x) -> exists! x:A, P x.
exact (fun P H1 => H1 (exu A P) (fun x H2 => H2 (exu A P) (fun H3 H4 => exuI P (exI A P x H3) (fun z y H5 H6 => eq_symtrans1 A z x y (H4 z H5) (H4 y H6))))).
Qed.

End Poly1_exuthms.

Section EqExercises.

Variable A:SType.

Theorem eq_leastrefl_1 : forall x y:A, (forall r:A->A->prop, (forall z:A, r z z) -> r x y) -> x = y.
let x y. assume H1. apply (H1 (fun x y : A => x = y)). exact (eqI A).
Qed.

Theorem eq_leastrefl_2 : forall x y:A, x = y -> (forall r:A->A->prop, (forall z:A, r z z) -> r x y).
let x y. assume H1. rewrite <- H1.
let r. assume H2. apply H2.
Qed.

End EqExercises.

Section Poly1.

Variable A:SType.

Theorem exm2I : forall P:A->A->prop, forall x1 x2:A, P x1 x2 -> exists x1:A, exists x2:A, P x1 x2.
let P x1 x2.
assume u:P x1 x2.
prove exists x1:A, exists x2:A, P x1 x2.
witness x1.
prove exists x2:A, P x1 x2.
witness x2.
prove P x1 x2.
exact u.
Qed.

Theorem exm2E : forall P:A->A->prop, (exists x1:A, exists x2:A, P x1 x2)
 -> forall p:prop, (forall x1 x2:A, P x1 x2 -> p) -> p.
let P.
assume H1: exists x1:A, exists x2:A, P x1 x2.
let p.
assume Hp: forall x1 x2:A, P x1 x2 -> p.
prove p.
apply H1.
let x1.
assume H2: exists x2:A, P x1 x2.
prove p.
apply H2.
let x2.
assume H3: P x1 x2.
prove p.
exact (Hp x1 x2 H3).
Qed.

Theorem exm3I : forall P:A->A->A->prop, forall x1 x2 x3:A, P x1 x2 x3 -> exists x1:A, exists x2:A, exists x3:A, P x1 x2 x3.
let P x1 x2 x3.
assume u:P x1 x2 x3.
witness x1.
prove exists x2:A, exists x3:A, P x1 x2 x3.
exact (exm2I (P x1) x2 x3 u).
Qed.

Theorem exm3E : forall P:A->A->A->prop, (exists x1:A, exists x2:A, exists x3:A, P x1 x2 x3)
 -> forall p:prop, (forall x1 x2 x3:A, P x1 x2 x3 -> p) -> p.
let P.
assume H1: exists x1:A, exists x2:A, exists x3:A, P x1 x2 x3.
let p.
assume Hp: forall x1 x2 x3:A, P x1 x2 x3 -> p.
prove p.
apply H1.
let x1.
assume H2: exists x2:A, exists x3:A, P x1 x2 x3.
prove p.
exact (exm2E (P x1) H2 p (Hp x1)).
Qed.

Theorem exm4I : forall P:A->A->A->A->prop, forall x1 x2 x3 x4:A, P x1 x2 x3 x4 -> exists x1:A, exists x2:A, exists x3:A, exists x4:A, P x1 x2 x3 x4.
exact (fun P x1 x2 x3 x4 u => exI A (fun x1 => exists x2:A, exists x3:A, exists x4:A, P x1 x2 x3 x4) x1 (exm3I (P x1) x2 x3 x4 u)).
Qed.

Theorem exm4E : forall P:A->A->A->A->prop, (exists x1:A, exists x2:A, exists x3:A, exists x4:A, P x1 x2 x3 x4)
 -> forall p:prop, (forall x1 x2 x3 x4:A, P x1 x2 x3 x4 -> p) -> p.
exact (fun P u p H => u p (fun x1 u => exm3E (P x1) u p (H x1))).
Qed.

Theorem exm5I : forall P:A->A->A->A->A->prop, forall x1 x2 x3 x4 x5:A, P x1 x2 x3 x4 x5 -> exists x1:A, exists x2:A, exists x3:A, exists x4:A, exists x5:A, P x1 x2 x3 x4 x5.
exact (fun P x1 x2 x3 x4 x5 u => exI A (fun x1 => exists x2:A, exists x3:A, exists x4:A, exists x5:A, P x1 x2 x3 x4 x5) x1 (exm4I (P x1) x2 x3 x4 x5 u)).
Qed.

Theorem exm5E : forall P:A->A->A->A->A->prop, (exists x1:A, exists x2:A, exists x3:A, exists x4:A, exists x5:A, P x1 x2 x3 x4 x5)
 -> forall p:prop, (forall x1 x2 x3 x4 x5:A, P x1 x2 x3 x4 x5 -> p) -> p.
exact (fun P u p H => u p (fun x1 u => exm4E (P x1) u p (H x1))).
Qed.

Variable P:A->prop.
Variable Q:A->prop.

Theorem exandI : forall x:A, P x -> Q x -> exists x:A, P x /\ Q x.
exact (fun x H1 H2 => exI A (fun x => P x /\ Q x) x (andI (P x) (Q x) H1 H2)).
Qed.

Theorem exandE : (exists x:A, P x /\ Q x) -> forall p:prop, (forall x:A, P x -> Q x -> p) -> p.
exact (fun u p H => u p (fun x u => u p (H x))).
Qed.

End Poly1.

Section Poly2a.

Variable A B:SType.

Theorem ex2I : forall P:A->B->prop, forall x1:A, forall x2:B, P x1 x2 -> exists x1:A, exists x2:B, P x1 x2.
exact (fun P x1 x2 u => exI A (fun x1 => exists x2:B, P x1 x2) x1 (exI B (fun x2 => P x1 x2) x2 u)).
Qed.

Theorem ex2E : forall P:A->B->prop, (exists x1:A, exists x2:B, P x1 x2)
 -> forall p:prop, (forall x1:A, forall x2:B, P x1 x2 -> p) -> p.
exact (fun P u p H => u p (fun x1 u => u p (fun x2 u => H x1 x2 u))).
Qed.

End Poly2a.

Section Poly2b.

Variable A B:SType.

Variable P:A->prop.
Variable Q:A->B->prop.
Variable R:A->B->prop.

Theorem exand2I : forall x:A, P x -> forall y:B, Q x y -> R x y -> exists x:A, P x /\ exists y:B, Q x y /\ R x y.
exact (fun x H1 y H2 H3 => exandI A P (fun x => exists y:B, Q x y /\ R x y) x H1 (exandI B (Q x) (R x) y H2 H3)).
Qed.

Theorem exand2E : (exists x:A, P x /\ exists y:B, Q x y /\ R x y)
 -> forall p:prop, (forall x:A, P x -> forall y:B, Q x y -> R x y -> p) -> p.
exact (fun u p H => exandE A P (fun x => exists y:B, Q x y /\ R x y) u p (fun x H1 u => exandE B (Q x) (R x) u p (H x H1))).
Qed.

End Poly2b.
