(* Title "Binary Relations" *)
(* Author "Chad E. Brown" *)

(* Salt "2MCsV9Ybj16WfiWJW" *)

(** Preamble **)
(* Unicode False "22A5" *)
Definition False : prop := forall P : prop , P.
(* Unicode True "22A4" *)
Definition True : prop := forall P : prop , P -> P.
Axiom TrueI : True.
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
Axiom orIL : forall A B : prop , A -> A \/ B.
Axiom orIR : forall A B : prop , B -> A \/ B.
Axiom orE : forall A B C : prop , (A -> C) -> (B -> C) -> A \/ B -> C.
Section PropN.
Variable P1 P2 P3 : prop.
Axiom and3I : P1 -> P2 -> P3 -> P1 /\ P2 /\ P3.
Axiom and3E : P1 /\ P2 /\ P3 -> (forall p : prop , (P1 -> P2 -> P3 -> p) -> p).
Axiom or3E : P1 \/ P2 \/ P3 -> (forall p : prop , (P1 -> p) -> (P2 -> p) -> (P3 -> p) -> p).
Variable P4 : prop.
Axiom and4I : P1 -> P2 -> P3 -> P4 -> P1 /\ P2 /\ P3 /\ P4.
Axiom and4E : P1 /\ P2 /\ P3 /\ P4 -> (forall p : prop , (P1 -> P2 -> P3 -> P4 -> p) -> p).
End PropN.
Section Poly1_eq.
Variable A : SType.
Definition eq : A -> A -> prop := fun x y => forall Q : A -> prop , Q x -> Q y.
Definition neq : A -> A -> prop := fun x y => ~ eq x y.
End Poly1_eq.
Infix = 502 := eq.
(* Unicode <> "2260" *)
Infix <> 502 := neq.
Section Poly1_eqthms.
Variable A : SType.
Axiom eqI : forall x : A , x = x.
Axiom eq_sym : forall x y : A , x = y -> y = x.
Axiom eq_trans : forall x y z : A , x = y -> y = z -> x = z.
End Poly1_eqthms.
Section Poly1_exdef.
Variable A : SType.
Variable Q : A -> prop.
Definition ex : prop := forall P : prop , (forall x : A , Q x -> P) -> P.
End Poly1_exdef.
(* Unicode exists "2203" *)
Binder+ exists , := ex.
Section PredPoly1.
Variable A : SType.
Definition bigintersect := fun (D : (A -> prop) -> prop) (x : A) => forall P : A -> prop , D P -> P x.
End PredPoly1.
Section PE.
Variable A : SType.
Axiom pred_ext : forall P Q : A -> prop , P c= Q -> Q c= P -> P = Q.
End PE.

(** Main Body **)

Section RelnPoly1.

Variable A:SType.

Definition reflexive : (A->A->prop)->prop := fun R => forall x:A, R x x.

Definition irreflexive : (A->A->prop)->prop := fun R => forall x:A, ~R x x.

Definition symmetric : (A->A->prop)->prop := fun R => forall x y:A, R x y -> R y x.

Definition antisymmetric : (A->A->prop)->prop := fun R => forall x y:A, R x y -> R y x -> x = y.

Definition transitive : (A->A->prop)->prop := fun R => forall x y z:A, R x y -> R y z -> R x z.

Definition eqreln : (A->A->prop)->prop := fun R => reflexive R /\ symmetric R /\ transitive R.

Definition per : (A->A->prop)->prop := fun R => symmetric R /\ transitive R.

Definition linear : (A->A->prop)->prop := fun R => forall x y:A, R x y \/ R y x.

Definition trichotomous_or : (A->A->prop)->prop := fun R => forall x y:A, R x y \/ x = y \/ R y x.

Definition partialorder : (A->A->prop)->prop := fun R => reflexive R /\ antisymmetric R /\ transitive R.

Definition totalorder : (A->A->prop)->prop := fun R => partialorder R /\ linear R.

Definition strictpartialorder : (A->A->prop)->prop := fun R => irreflexive R /\ transitive R.

Definition stricttotalorder : (A->A->prop)->prop := fun R => strictpartialorder R /\ trichotomous_or R.

Example eqreln_eq : eqreln (eq A).
prove (reflexive (eq A) /\ symmetric (eq A) /\ transitive (eq A)).
apply and3I.
- exact (eqI A).
- exact (eq_sym A).
- exact (eq_trans A).
Qed.

Example eqreln_full : eqreln (fun x y:A => True).
prove (reflexive (fun x y:A => True) /\ symmetric (fun x y:A => True) /\ transitive (fun x y:A => True)).
apply and3I.
- let x. exact TrueI.
- let x y. assume _. exact TrueI.
- let x y z. assume _ _. exact TrueI.
Qed.

Example per_empty : per (fun x y:A => False).
prove (symmetric (fun x y:A => False) /\ transitive (fun x y:A => False)).
apply andI.
- let x y. assume H:False. exact H.
- let x y z. assume H _:False. exact H.
Qed.

Theorem per_sym : forall R:A->A->prop, per R -> symmetric R.
let R. assume H1: symmetric R /\ transitive R.
exact (andEL (symmetric R) (transitive R) H1).
Qed.

Theorem per_tra : forall R:A->A->prop, per R -> transitive R.
let R. assume H1: symmetric R /\ transitive R.
exact (andER (symmetric R) (transitive R) H1).
Qed.

Theorem per_stra1 : forall R:A->A->prop, per R -> forall x y z:A, R y x -> R y z -> R x z.
let R. assume H1: symmetric R /\ transitive R.
let x y z. assume H2: R y x. assume H3: R y z.
apply H1.
assume H4: symmetric R.
assume H5: transitive R.
apply (H5 x y z).
- prove R x y. exact (H4 y x H2).
- exact H3.
Qed.

Theorem per_stra2 : forall R:A->A->prop, per R -> forall x y z:A, R x y -> R z y -> R x z.
let R. assume H1: symmetric R /\ transitive R.
let x y z. assume H2: R x y. assume H3: R z y.
apply H1.
assume H4: symmetric R.
assume H5: transitive R.
apply (H5 x y z).
- exact H2.
- prove R y z. exact (H4 z y H3).
Qed.

Theorem per_stra3 : forall R:A->A->prop, per R -> forall x y z:A, R y x -> R z y -> R x z.
let R. assume H1: symmetric R /\ transitive R.
let x y z. assume H2: R y x. assume H3: R z y.
apply H1.
assume H4: symmetric R.
assume H5: transitive R.
apply H4.
prove R z x.
exact (H5 z y x H3 H2).
Qed.

Theorem per_ref1 : forall R:A->A->prop, per R -> forall x y:A, R x y -> R x x.
let R. assume H1. apply H1.
assume H2:symmetric R.
assume H3:transitive R.
let x y. assume H4:R x y.
claim L1:R y x. { apply H2. exact H4. }
exact (H3 x y x H4 L1).
Qed.

Theorem per_ref2 : forall R:A->A->prop, per R -> forall x y:A, R x y -> R y y.
let R. assume H1. apply H1.
assume H2:symmetric R.
assume H3:transitive R.
let x y. assume H4:R x y.
claim L1:R y x. { apply H2. exact H4. }
exact (H3 y x y L1 H4).
Qed.

Theorem partialorder_strictpartialorder : forall R:A->A->prop,
  partialorder R -> strictpartialorder (fun x y => R x y /\ x <> y).
let R.
assume H1: reflexive R /\ antisymmetric R /\ transitive R.
apply (and3E (reflexive R) (antisymmetric R) (transitive R) H1).
assume H2: reflexive R.
assume H3: antisymmetric R.
assume H4: transitive R.
prove irreflexive (fun x y => R x y /\ x <> y) /\ transitive (fun x y => R x y /\ x <> y).
apply andI.
- prove irreflexive (fun x y => R x y /\ x <> y).
  let x.
  assume H5: R x x /\ x <> x.
  exact (andER (R x x) (x <> x) H5 (eqI A x)).
- prove transitive (fun x y => R x y /\ x <> y).
  let x y z.
  assume H5: R x y /\ x <> y.
  assume H6: R y z /\ y <> z.
  apply H5.
  assume H7: R x y.
  assume H8: x <> y.
  apply H6.
  assume H9: R y z.
  assume H10: y <> z.
  prove R x z /\ x <> z.
  apply andI.
  + exact (H4 x y z H7 H9).
  + prove x <> z.
    assume H11: x = z.
    claim L1: R y x.
    { rewrite H11. exact H9. }
    apply H8.
    prove x = y.
    exact (H3 x y H7 L1).
Qed.

Definition reflclos : (A->A->prop)->(A->A->prop) := fun R x y => R x y \/ x = y.

Postfix ' 400 := reflclos.

Theorem reflclos_refl : forall R:A->A->prop, reflexive (R ').
let R x.
prove R x x \/ x = x.
apply orIR.
exact (eqI A x).
Qed.

Theorem reflclos_min : forall R S:A->A->prop, R c= S -> reflexive S -> R ' c= S.
let R S.
assume H1: R c= S.
assume H2: reflexive S.
let x y.
assume H3: R x y \/ x = y.
prove S x y.
apply H3.
- assume H4: R x y.
  exact (H1 x y H4).
- assume H4: x = y.
  prove S x y.
  rewrite <- H4.
  prove S x x.
  exact (H2 x).
Qed.

Theorem strictpartialorder_partialorder_reflclos : forall R:A->A->prop, strictpartialorder R -> partialorder (R ').
let R.
assume HR: irreflexive R /\ transitive R.
apply HR.
assume HRI: irreflexive R.
assume HRT: transitive R.
prove reflexive (R ') /\ antisymmetric (R ') /\ transitive (R ').
apply and3I.
- exact (reflclos_refl R).
- let x y.
  assume H1: R x y \/ x = y.
  assume H2: R y x \/ y = x.
  prove x = y.
  apply H1.
  + assume H3: R x y.
    apply H2.
    * assume H4: R y x.
      prove False.
      claim L1: R x x.
      { exact (HRT x y x H3 H4). }
      exact (HRI x L1).
    * assume H4: y = x.
      exact (eq_sym A y x H4).
  + assume H3: x = y.
    exact H3.
- let x y z.
  assume H1: R x y \/ x = y.
  assume H2: R y z \/ y = z.
  prove R x z \/ x = z.
  apply H1.
  + assume H3: R x y.
    apply H2.
    * assume H4: R y z.
      apply orIL.
      prove R x z.
      exact (HRT x y z H3 H4).
    * assume H4: y = z.
      apply orIL.
      prove R x z.
      rewrite <- H4.
      prove R x y.
      exact H3.
  + assume H3: x = y.
    apply H2.
    * assume H4: R y z.
      apply orIL.
      prove R x z.
      rewrite H3.
      prove R y z.
      exact H4.
    * assume H4: y = z.
      apply orIR.
      prove x = z.
      exact (eq_trans A x y z H3 H4).
Qed.

Theorem stricttotalorder_totalorder_reflclos : forall R:A->A->prop,
  stricttotalorder R -> totalorder (R ').
let R.
assume HR: strictpartialorder R /\ trichotomous_or R.
apply HR.
assume HRP: strictpartialorder R.
assume HRT: trichotomous_or R.
prove partialorder (R ') /\ linear (R ').
apply andI.
- exact (strictpartialorder_partialorder_reflclos R HRP).
- let x y.
  prove R ' x y \/ R ' y x.
  prove (R x y \/ x = y) \/ (R y x \/ y = x).
  apply (or3E (R x y) (x = y) (R y x) (HRT x y)).
  + assume H1: R x y.
    apply orIL.
    apply orIL.
    exact H1.
  + assume H1: x = y.
    apply orIL.
    apply orIR.
    exact H1.
  + assume H1: R y x.
    apply orIR.
    apply orIL.
    exact H1.
Qed.

End RelnPoly1.

Section RelnPoly1b.

Variable A:SType.

Theorem partialorder_subpredq : partialorder (A -> prop) (fun X Y:A -> prop => X c= Y).
prove reflexive (A->prop) (fun X Y:A -> prop => X c= Y) /\ antisymmetric (A->prop) (fun X Y:A -> prop => X c= Y) /\ transitive (A->prop) (fun X Y:A -> prop => X c= Y).
apply and3I.
- let X x. assume H1: X x. exact H1.
- exact (pred_ext A).
- let X Y Z. assume H1: X c= Y. assume H2: Y c= Z.
  let x. assume H3:X x. exact (H2 x (H1 x H3)).
Qed.

Theorem strictpartialorder_subpred : strictpartialorder (A -> prop) (fun X Y:A -> prop => X c= Y /\ X <> Y).
exact (partialorder_strictpartialorder (A->prop) (fun X Y:A->prop => X c= Y) partialorder_subpredq).
Qed.

Variable U:(A->prop)->prop.

Hypothesis U_int : forall D:(A->prop)->prop, D c= U -> U (bigintersect A D).
Hypothesis U_sep : forall x y:A, ~(exists P:A->prop, U P /\ P x /\ ~P y) -> ~(exists P:A->prop, U P /\ P y /\ ~P x) -> x = y.
Hypothesis U_lin : forall P Q:A->prop, U P -> U Q -> P c= Q \/ Q c= P.

Let R : A->A->prop := fun x y:A => forall P:A->prop, U P -> P x -> P y.

Theorem totalorder_as_upperclosed : totalorder A R.
claim L1: forall x:A, R x = bigintersect A (fun P => U P /\ P x).
{
  let x. apply (pred_ext A).
  - let y.
    assume H1: R x y.
    prove bigintersect A (fun P => U P /\ P x) y.
    prove forall P:A->prop, U P /\ P x -> P y.
    let P.
    assume H2: U P /\ P x.
    apply H2.
    assume H3: U P.
    assume H4: P x.
    exact (H1 P H3 H4).
  - let y.
    assume H1: bigintersect A (fun P => U P /\ P x) y.
    prove R x y.
    let P.
    assume H2: U P.
    assume H3: P x.
    prove P y.
    apply (H1 P).
    prove U P /\ P x.
    exact (andI (U P) (P x) H2 H3).
}
claim L2: forall x:A, U (R x).
{
  let x.
  rewrite (L1 x).
  prove U (bigintersect A (fun P => U P /\ P x)).
  apply U_int.
  prove (fun P:A->prop => U P /\ P x) c= U.
  let P.
  assume H1: U P /\ P x.
  prove U P.
  exact (andEL (U P) (P x) H1).
}
claim L3: forall x:A, R x x.
{ exact (fun x P H1 H2 => H2). }
prove reflexive A R /\ antisymmetric A R /\ transitive A R /\ linear A R.
apply and4I.
- exact L3.
- let x y.
  assume H1: forall P:A->prop, U P -> P x -> P y.
  assume H2: forall P:A->prop, U P -> P y -> P x.
  apply (U_sep x y).
  + prove ~exists P:A->prop, U P /\ P x /\ ~P y.
    assume H3: exists P:A->prop, U P /\ P x /\ ~P y.
    apply H3.
    let P.
    assume H4: U P /\ P x /\ ~P y.
    apply (and3E (U P) (P x) (~P y) H4).
    assume H5: U P.
    assume H6: P x.
    assume H7: ~P y.
    apply H7.
    prove P y.
    exact (H1 P H5 H6).
  + prove ~exists P:A->prop, U P /\ P y /\ ~P x.
    assume H3: exists P:A->prop, U P /\ P y /\ ~P x.
    apply H3.
    let P.
    assume H4: U P /\ P y /\ ~P x.
    apply (and3E (U P) (P y) (~P x) H4).
    assume H5: U P.
    assume H6: P y.
    assume H7: ~P x.
    apply H7.
    prove P x.
    exact (H2 P H5 H6).
- let x y z.
  assume H1: forall P:A->prop, U P -> P x -> P y.
  assume H2: forall P:A->prop, U P -> P y -> P z.
  let P.
  assume H3: U P.
  assume H4: P x.
  prove P z.
  apply (H2 P H3).
  prove P y.
  exact (H1 P H3 H4).
- let x y.
  prove R x y \/ R y x.
  apply (U_lin (R x) (R y) (L2 x) (L2 y)).
  + assume H1: R x c= R y.
    apply orIR.
    prove R y x.
    exact (H1 x (L3 x)).
  + assume H1: R y c= R x.
    apply orIL.
    prove R x y.
    exact (H1 y (L3 y)).
Qed.

End RelnPoly1b.
