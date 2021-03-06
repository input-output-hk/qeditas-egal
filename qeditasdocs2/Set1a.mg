(* Title "Introduction to the Zermelo-Fraenkel Set Operators I" *)
(* Author "Chad E. Brown" *)

(* Salt "2SsTWhR3WJfSrxeRz" *)

(** Preamble **)
(* Unicode False "22A5" *)
Definition False : prop := forall P : prop , P.
Definition not : prop -> prop := fun A : prop => A -> False.
(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.
Definition and : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> B -> P) -> P.
(* Unicode /\ "2227" *)
Infix /\ 780 left  := and.
Axiom andI : forall A B : prop , A -> B -> A /\ B.
Axiom andEL : forall A B : prop , A /\ B -> A.
Axiom andER : forall A B : prop , A /\ B -> B.
Definition iff : prop -> prop -> prop := fun A B : prop => (A -> B) /\ (B -> A).
(* Unicode <-> "2194" *)
Infix <-> 805 := iff.
Axiom iffI : forall A B : prop , (A -> B) -> (B -> A) -> (A <-> B).
Axiom iffEL : forall A B : prop , (A <-> B) -> A -> B.
Axiom iffER : forall A B : prop , (A <-> B) -> B -> A.
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
End Poly1_eqthms.
Section Poly1_exdef.
Variable A : SType.
Variable Q : A -> prop.
Definition ex : prop := forall P : prop , (forall x : A , Q x -> P) -> P.
End Poly1_exdef.
(* Unicode exists "2203" *)
Binder+ exists , := ex.
Section Poly1_exthms.
Variable A : SType.
Axiom exI : forall P : A -> prop , forall x : A , P x -> exists x : A , P x.
End Poly1_exthms.
Section Poly1.
Variable A : SType.
Variable P : A -> prop.
Variable Q : A -> prop.
Axiom exandI : forall x : A , P x -> Q x -> exists x : A , P x /\ Q x.
Axiom exandE : (exists x : A , P x /\ Q x) -> forall p : prop , (forall x : A , P x -> Q x -> p) -> p.
End Poly1.

(** Main Body **)

(** membership and subset for set theory **)

(** In is the membership relation on set.  We use x :e y as notation to mean "x is a member of y" and x /:e y as notation for "x is not a member of y." **)

Parameter In:set->set->prop.

Definition nIn : set->set->prop :=
fun x X => ~In x X.

(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.

(** Subq is the subset relation on set.  We use X c= Y as notation to mean "X is a subset of Y" and X /c= Y as notation for "X is not a subset of Y." **)

Definition Subq : set->set->prop :=
fun X Y => forall x:set, x :e X -> x :e Y.

Definition nSubq : set->set->prop :=
fun X Y => ~Subq X Y.

(* Unicode /c= "2288" *)
Infix /c= 502 := nSubq.

Binder+ exists , := ex; and.
Binder exists! , := exu; and.

Theorem Subq_ref : forall X:set, X c= X.
exact (fun (X x : set) (H : x :e X) => H).
Qed.

Theorem Subq_tra : forall X Y Z:set, X c= Y -> Y c= Z -> X c= Z.
exact (fun (X Y Z : set) (H1 : X c= Y) (H2 : Y c= Z) (x : set) (H : x :e X) => (H2 x (H1 x H))).
Qed.

Theorem Subq_contra : forall X Y z:set, X c= Y -> z /:e Y -> z /:e X.
exact (fun X Y z H1 H2 H3 => H2 (H1 z H3)).
Qed.

(** Axioms and Primitives of set theory ***)
(** Two sets are equal if they have the same elements. Equivalently, we can always prove two sets are equal by proving they are subsets of each other. **)

Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X = Y.

(** Empty is the empty set. **)

(* Unicode Empty "2205" *)
Parameter Empty : set.

Axiom EmptyAx : ~exists x:set, x :e Empty.

Theorem EmptyE : forall x:set, x /:e Empty.
exact (fun x H => EmptyAx (exI set (fun x => x :e Empty) x H)).
Qed.

Theorem Subq_Empty : forall X:set, Empty c= X.
exact (fun (X x : set) (H : x :e Empty) => EmptyE x H (x :e X)).
Qed.

Theorem Empty_Subq_eq : forall X:set, X c= Empty -> X = Empty.
let X.
assume H1: X c= Empty.
apply set_ext.
- exact H1.
- exact (Subq_Empty X).
Qed.

Theorem Empty_eq : forall X:set, (forall x, x /:e X) -> X = Empty.
let X.
assume H1: forall x, x /:e X.
apply Empty_Subq_eq.
let x.
assume H2: x :e X.
prove False.
exact (H1 x H2).
Qed.

Theorem Witness_NonEmpty : forall x X:set, x :e X -> X <> Empty.
exact (fun (x X : set) (H1 : x :e X) (H2 : X = Empty) => EmptyE x (H2 (In x) H1)).
Qed.

(** Given a set X, (Union X) is the set {x | there is some Y such that x :e Y and Y :e X}. That is, Union gives the union of a set of sets. **)

(* Unicode Union "22C3" *)
Parameter Union : set->set.

Axiom UnionEq : forall X:set, forall x:set, x :e Union X <-> exists Y:set, x :e Y /\ Y :e X.

Theorem UnionE :
forall X x:set, x :e (Union X) -> exists Y:set, x :e Y /\ Y :e X.
exact (fun X x : set => iffEL (x :e Union X) (exists Y:set, x :e Y /\ Y :e X) (UnionEq X x)).
Qed.

Theorem UnionE2 :
forall X x:set, x :e (Union X) -> forall p:prop, (forall Y:set, x :e Y -> Y :e X -> p) -> p.
exact (fun X x H => exandE set (fun Y => x :e Y) (fun Y => Y :e X) (UnionE X x H)).
Qed.

Theorem UnionI :
forall X x Y:set, x :e Y -> Y :e X -> x :e (Union X).
let X x Y.
assume H1: x :e Y.
assume H2: Y :e X.
apply (UnionEq X x).
assume _ H3. apply H3.
prove exists Y:set, x :e Y /\ Y :e X.
witness Y.
apply andI.
- exact H1.
- exact H2.
Qed.

Theorem Union_Empty : Union Empty = Empty.
apply (Empty_eq (Union Empty)).
let x.
assume H1: x :e Union Empty.
apply (UnionE Empty x H1).
let Y.
assume H2: x :e Y /\ Y :e Empty.
exact (EmptyE Y (andER (x :e Y) (Y :e Empty) H2)).
Qed.

(** (Power X) is the set of all subsets of X. **)

(* Unicode Power "1D4AB" *)
Parameter Power : set->set.

Axiom PowerEq : forall X Y:set, Y :e Power X <-> Y c= X.

Theorem PowerE : forall X Y:set, Y :e Power X -> Y c= X.
exact (fun X Y : set => PowerEq X Y (Y :e Power X -> Y c= X) (fun H _ => H)).
Qed.

Theorem PowerI : forall X Y:set, Y c= X -> Y :e (Power X).
exact (fun X Y : set => PowerEq X Y (Y c= X -> Y :e Power X) (fun _ H => H)).
Qed.

Theorem Power_Subq : forall X Y:set, X c= Y -> Power X c= Power Y.
exact (fun (X Y : set) (H1 : X c= Y) (Z : set) (H2 : Z :e Power X) => PowerI Y Z (Subq_tra Z X Y (PowerE X Z H2) H1)).
Qed.

Theorem Empty_In_Power : forall X:set, Empty :e Power X.
exact (fun X : set => PowerI X Empty (Subq_Empty X)).
Qed.

Theorem Self_In_Power : forall X:set, X :e Power X.
exact (fun X : set => PowerI X X (Subq_ref X)).
Qed.

Theorem Union_Power_Subq : forall X:set, Union (Power X) c= X.
let X x.
assume H1: x :e Union (Power X).
claim L1: exists Y:set, x :e Y /\ Y :e Power X.
{ exact (UnionE (Power X) x H1). }
apply (exandE set (fun Y => x :e Y) (fun Y => Y :e Power X) L1).
let Y.
assume H2: x :e Y.
assume H3: Y :e Power X.
exact (PowerE X Y H3 x H2).
Qed.

(** Given a set X and a function F, (Repl F X) is the set {F x|x :e X}. That is, Repl allows us to form a set by
 replacing the elements x in a set X with corresponding elements F x. **)

Parameter Repl : set->(set->set)->set.
Notation Repl Repl.

Axiom ReplEq :
forall X:set, forall F:set->set, forall y:set, y :e {F x|x :e X} <-> exists x:set, x :e X /\ y = F x.

Theorem ReplE :
forall X:set, forall F:set->set, forall y:set, y :e {F x|x :e X} -> exists x:set, x :e X /\ y = F x.
exact (fun (X : set) (F : set -> set) (y : set) => iffEL (y :e Repl X (fun x : set => F x)) (exists x:set, x :e X /\ y = F x) (ReplEq X F y)).
Qed.

Theorem ReplE2 :
forall X:set, forall F:set->set, forall y:set, y :e {F x|x :e X} -> forall p:prop, (forall x:set, x :e X -> y = F x -> p) -> p.
exact (fun X F y H => exandE set (fun x => x :e X) (fun x => y = F x) (ReplE X F y H)).
Qed.

Theorem ReplI :
forall X:set, forall F:set->set, forall x:set, x :e X -> F x :e {F x|x :e X}.
let X F x.
assume H1: x :e X.
claim L1: exists z:set, z :e X /\ F x = F z.
{ exact (exandI set (fun z => z :e X) (fun z => F x = F z) x H1 (eqI set (F x))). }
exact (iffER (F x :e {F x|x :e X}) (exists z:set, z :e X /\ F x = F z) (ReplEq X F (F x)) L1).
Qed.

Theorem Repl_Empty : forall F:set -> set, {F x|x :e Empty} = Empty.
let F. apply (Empty_eq {F x|x :e Empty}).
let y.
assume H1: y :e {F x|x :e Empty}.
apply (ReplE2 Empty F y H1).
let x.
assume H2: x :e Empty.
assume _.
exact (EmptyE x H2).
Qed.
