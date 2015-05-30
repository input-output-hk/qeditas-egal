(* Title "Quotients" *)
(* Author "Chad E. Brown" *)

(* Salt "2GxJfmdu1bwYzhNYg" *)

(** Preamble **)
(* Unicode False "22A5" *)
Definition False : prop := forall P : prop , P.
Axiom FalseE : forall P : prop , False -> P.
Definition not : prop -> prop := fun A : prop => A -> False.
(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.
Definition and : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> B -> P) -> P.
(* Unicode /\ "2227" *)
Infix /\ 780 left  := and.
Axiom andI : forall A B : prop , A -> B -> A /\ B.
Axiom andEL : forall A B : prop , A /\ B -> A.
Axiom andER : forall A B : prop , A /\ B -> B.
Definition or : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> P) -> (B -> P) -> P.
(* Unicode \/ "2228" *)
Infix \/ 785 left  := or.
Section Poly1_eq.
Variable A : SType.
Definition eq : A -> A -> prop := fun x y => forall Q : A -> prop , Q x -> Q y.
End Poly1_eq.
Infix = 502 := eq.
Section Poly1_eqthms.
Variable A : SType.
Axiom eqI : forall x : A , x = x.
Axiom eq_sym : forall x y : A , x = y -> y = x.
End Poly1_eqthms.
Section PE.
Variable A : SType.
Axiom pred_ext : forall P Q : A -> prop , P c= Q -> Q c= P -> P = Q.
End PE.
Section RelnPoly1.
Variable A : SType.
Definition symmetric : (A -> A -> prop) -> prop := fun R => forall x y : A , R x y -> R y x.
Definition transitive : (A -> A -> prop) -> prop := fun R => forall x y z : A , R x y -> R y z -> R x z.
Definition per : (A -> A -> prop) -> prop := fun R => symmetric R /\ transitive R.
Axiom per_tra : forall R : A -> A -> prop , per R -> transitive R.
Axiom per_stra1 : forall R : A -> A -> prop , per R -> forall x y z : A , R y x -> R y z -> R x z.
Axiom per_ref1 : forall R : A -> A -> prop , per R -> forall x y : A , R x y -> R x x.
End RelnPoly1.
Section Choice.
Variable A : SType.
Parameter Eps : (A -> prop) -> A.
Axiom EpsR : forall P : A -> prop , forall x : A , P x -> P (Eps P).
End Choice.
Binder some , := Eps.
Section IfA.
Variable A : SType.
Definition If : prop -> A -> A -> A := (fun p x y => some z : A , p /\ z = x \/ ~ p /\ z = y).
Notation IfThenElse If.
Axiom If_correct : forall p : prop , forall x y : A , p /\ (if p then x else y) = x \/ ~ p /\ (if p then x else y) = y.
Axiom If_0 : forall p : prop , forall x y : A , ~ p -> (if p then x else y) = y.
Axiom If_1 : forall p : prop , forall x y : A , p -> (if p then x else y) = x.
End IfA.

(** Main Body **)

Section QuotientsPoly1.

Variable A:SType.

Definition canonical_elt : (A->A->prop)->A->A := fun R:A->A->prop => fun x:A => some y:A, R x y.

Theorem canonical_elt_rel : forall R:A->A->prop, forall x:A, R x x -> R x (canonical_elt R x).
exact (fun R x H => EpsR A (R x) x H).
Qed.

Theorem canonical_elt_eq : forall R:A->A->prop, per A R -> forall x y:A, R x y -> canonical_elt R x = canonical_elt R y.
let R.
assume H1: per A R.
let x y.
assume H2: R x y.
claim E: R x = R y.
{
  apply (pred_ext A).
  - let z. assume H3: R x z. prove R y z. exact (per_stra1 A R H1 y x z H2 H3).
  - let z. assume H3: R y z. prove R x z. exact (per_tra A R H1 x y z H2 H3).
}
prove (some z:A, R x z) = (some z:A, R y z).
rewrite <- E.
apply (eqI A).
Qed.

Theorem canonical_elt_idem : forall R:A->A->prop, per A R -> forall x:A, R x x -> canonical_elt R x = canonical_elt R (canonical_elt R x).
let R.
assume H1: per A R.
let x.
assume H2: R x x.
prove canonical_elt R x = canonical_elt R (canonical_elt R x).
apply (canonical_elt_eq R H1 x (canonical_elt R x)).
prove R x (canonical_elt R x).
exact (canonical_elt_rel R x H2).
Qed.

Definition quotient : (A->A->prop)->A->prop := fun R:A->A->prop => fun x:A => R x x /\ x = canonical_elt R x.

Theorem quotient_prop1 : forall R:A->A->prop,
 forall x:A, quotient R x -> R x x.
exact (fun R x H => andEL (R x x) (x = canonical_elt R x) H).
Qed.

Theorem quotient_prop2 : forall R:A->A->prop, per A R ->
 forall x y:A, quotient R x -> quotient R y -> R x y -> x = y.
let R.
assume H1: per A R.
let x y.
assume H2: R x x /\ x = canonical_elt R x.
assume H3: R y y /\ y = canonical_elt R y.
assume H4: R x y.
rewrite (andER (R x x) (x = canonical_elt R x) H2).
rewrite (andER (R y y) (y = canonical_elt R y) H3).
exact (canonical_elt_eq R H1 x y H4).
Qed.

Definition canonical_elt_def : (A->A->prop)->(A->A)->A->A := fun R:A->A->prop => fun d:A->A => fun x:A => if (R x (d x)) then (d x) else (canonical_elt R x).

Theorem canonical_elt_def_rel : forall R:A->A->prop, forall d:A->A, forall x:A, R x x -> R x (canonical_elt_def R d x).
let R d x.
assume H1:R x x.
prove R x (if R x (d x) then d x else canonical_elt R x).
apply (If_correct A (R x (d x)) (d x) (canonical_elt R x)).
- assume H2: R x (d x) /\ (if R x (d x) then d x else canonical_elt R x) = d x.
  apply H2.
  assume H3: R x (d x).
  assume H4: (if R x (d x) then d x else canonical_elt R x) = d x.
  rewrite H4. exact H3.
- assume H2: ~R x (d x) /\ (if R x (d x) then d x else canonical_elt R x) = canonical_elt R x.
  rewrite (andER (~R x (d x)) ((if R x (d x) then d x else canonical_elt R x) = canonical_elt R x) H2).
  prove R x (canonical_elt R x).
  exact (canonical_elt_rel R x H1).
Qed.

Theorem canonical_elt_def_eq :
 forall R:A->A->prop, per A R ->
 forall d:A->A, (forall x y:A, R x y -> d x = d y) ->
 forall x y:A, R x y -> canonical_elt_def R d x = canonical_elt_def R d y.
let R.
assume H1: per A R.
let d.
assume H2: forall x y:A, R x y -> d x = d y.
let x y.
assume H3: R x y.
apply (If_correct A (R x (d x)) (d x) (canonical_elt R x)).
- assume Hx1: R x (d x) /\ (if R x (d x) then d x else canonical_elt R x) = d x.
  apply Hx1.
  assume Hx2: R x (d x).
  assume Hx3: (if R x (d x) then d x else canonical_elt R x) = d x.
  prove ((if (R x (d x)) then (d x) else (canonical_elt R x)) = canonical_elt_def R d y).
  rewrite Hx3.
  prove (d x = canonical_elt_def R d y).
  prove (d x = (if (R y (d y)) then (d y) else (canonical_elt R y))).
  claim L1: R y (d y).
  {
    rewrite <- (H2 x y H3).
    prove R y (d x).
    exact (per_stra1 A R H1 y x (d x) H3 Hx2).
  }
  rewrite (If_1 A (R y (d y)) (d y) (canonical_elt R y) L1).
  prove d x = d y.
  exact (H2 x y H3).
- assume Hx1: ~R x (d x) /\ (if R x (d x) then d x else canonical_elt R x) = canonical_elt R x.
  apply Hx1.
  assume Hx2: ~R x (d x).
  assume Hx3: (if R x (d x) then d x else canonical_elt R x) = canonical_elt R x.
  prove (if (R x (d x)) then (d x) else (canonical_elt R x)) = canonical_elt_def R d y.
  rewrite Hx3.
  prove canonical_elt R x = canonical_elt_def R d y.
  prove canonical_elt R x = if (R y (d y)) then (d y) else (canonical_elt R y).
  claim L1: ~R y (d y).
  {
    rewrite <- (H2 x y H3).
    assume Hy1: R y (d x).
    apply Hx2.
    exact (per_tra A R H1 x y (d x) H3 Hy1).
  }
  rewrite (If_0 A (R y (d y)) (d y) (canonical_elt R y) L1).
  prove canonical_elt R x = canonical_elt R y.
  exact (canonical_elt_eq R H1 x y H3).
Qed.

Theorem canonical_elt_def_idem :
 forall R:A->A->prop, per A R ->
 forall d:A->A, (forall x y:A, R x y -> d x = d y) ->
 forall x:A, R x x -> canonical_elt_def R d x = canonical_elt_def R d (canonical_elt_def R d x).
let R.
assume H1: per A R.
let d.
assume H2: forall x y:A, R x y -> d x = d y.
let x.
assume H3: R x x.
apply (canonical_elt_def_eq R H1 d H2 x (canonical_elt_def R d x)).
prove R x (canonical_elt_def R d x).
apply canonical_elt_def_rel.
exact H3.
Qed.

Definition quotient_def : (A->A->prop)->(A->A)->A->prop := fun R:A->A->prop => fun d:A->A => fun x:A => R x x /\ x = canonical_elt_def R d x.

Theorem quotient_def_prop0 :
 forall R:A->A->prop, per A R ->
 forall d:A->A,
 forall x:A, R x (d x) -> x = d x -> quotient_def R d x.
let R.
assume H1: per A R.
let d.
let x.
assume H2: R x (d x).
assume H3: x = d x.
prove R x x /\ x = canonical_elt_def R d x.
apply andI.
- exact (per_ref1 A R H1 x (d x) H2).
- prove x = if (R x (d x)) then (d x) else (canonical_elt R x).
  rewrite (If_1 A (R x (d x)) (d x) (canonical_elt R x) H2).
  prove x = d x.
  exact H3.
Qed.

Theorem quotient_def_prop1 :
 forall R:A->A->prop,
 forall d:A->A,
 forall x:A, quotient_def R d x -> R x x.
let R d x.
assume H2: R x x /\ x = canonical_elt_def R d x.
prove R x x.
exact (andEL (R x x) (x = canonical_elt_def R d x) H2).
Qed.

Theorem quotient_def_prop2 :
 forall R:A->A->prop, per A R ->
 forall d:A->A, (forall x y:A, R x y -> d x = d y) ->
 forall x y:A, quotient_def R d x -> quotient_def R d y -> R x y -> x = y.
let R.
assume H1: per A R.
let d.
assume H2: forall x y:A, R x y -> d x = d y.
let x y.
assume Hx1: R x x /\ x = canonical_elt_def R d x.
assume Hy1: R y y /\ y = canonical_elt_def R d y.
assume H3: R x y.
rewrite (andER (R x x) (x = canonical_elt_def R d x) Hx1).
rewrite (andER (R y y) (y = canonical_elt_def R d y) Hy1).
prove canonical_elt_def R d x = canonical_elt_def R d y.
exact (canonical_elt_def_eq R H1 d H2 x y H3).
Qed.

End QuotientsPoly1.
