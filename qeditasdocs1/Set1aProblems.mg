(* Title "Introduction to the Zermelo-Fraenkel Set Operators I" *)
(* Author "Chad E. Brown" *)

(* Salt "2SsTWhR3WJfSrxeRz" *)

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
Admitted.

Theorem Subq_tra : forall X Y Z:set, X c= Y -> Y c= Z -> X c= Z.
Admitted.

Theorem Subq_contra : forall X Y z:set, X c= Y -> z /:e Y -> z /:e X.
Admitted.

(** Axioms and Primitives of set theory ***)
(** Two sets are equal if they have the same elements. Equivalently, we can always prove two sets are equal by proving they are subsets of each other. **)

Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X = Y.

(** Empty is the empty set. **)

(* Unicode Empty "2205" *)
Parameter Empty : set.

Axiom EmptyAx : ~exists x:set, x :e Empty.

Theorem EmptyE : forall x:set, x /:e Empty.
Admitted.

Theorem Subq_Empty : forall X:set, Empty c= X.
Admitted.

Theorem Empty_Subq_eq : forall X:set, X c= Empty -> X = Empty.
Admitted.

Theorem Empty_eq : forall X:set, (forall x, x /:e X) -> X = Empty.
Admitted.

Theorem Witness_NonEmpty : forall x X:set, x :e X -> X <> Empty.
Admitted.

(** Given a set X, (Union X) is the set {x | there is some Y such that x :e Y and Y :e X}. That is, Union gives the union of a set of sets. **)

(* Unicode Union "22C3" *)
Parameter Union : set->set.

Axiom UnionEq : forall X:set, forall x:set, x :e Union X <-> exists Y:set, x :e Y /\ Y :e X.

Theorem UnionE :
forall X x:set, x :e (Union X) -> exists Y:set, x :e Y /\ Y :e X.
Admitted.

Theorem UnionE2 :
forall X x:set, x :e (Union X) -> forall p:prop, (forall Y:set, x :e Y -> Y :e X -> p) -> p.
Admitted.

Theorem UnionI :
forall X x Y:set, x :e Y -> Y :e X -> x :e (Union X).
Admitted.

Theorem Union_Empty : Union Empty = Empty.
Admitted.

(** (Power X) is the set of all subsets of X. **)

(* Unicode Power "1D4AB" *)
Parameter Power : set->set.

Axiom PowerEq : forall X Y:set, Y :e Power X <-> Y c= X.

Theorem PowerE : forall X Y:set, Y :e Power X -> Y c= X.
Admitted.

Theorem PowerI : forall X Y:set, Y c= X -> Y :e (Power X).
Admitted.

Theorem Power_Subq : forall X Y:set, X c= Y -> Power X c= Power Y.
Admitted.

Theorem Empty_In_Power : forall X:set, Empty :e Power X.
Admitted.

Theorem Self_In_Power : forall X:set, X :e Power X.
Admitted.

Theorem Union_Power_Subq : forall X:set, Union (Power X) c= X.
Admitted.

(** Given a set X and a function F, (Repl F X) is the set {F x|x :e X}. That is, Repl allows us to form a set by
 replacing the elements x in a set X with corresponding elements F x. **)

Parameter Repl : set->(set->set)->set.
Notation Repl Repl.

Axiom ReplEq :
forall X:set, forall F:set->set, forall y:set, y :e {F x|x :e X} <-> exists x:set, x :e X /\ y = F x.

Theorem ReplE :
forall X:set, forall F:set->set, forall y:set, y :e {F x|x :e X} -> exists x:set, x :e X /\ y = F x.
Admitted.

Theorem ReplE2 :
forall X:set, forall F:set->set, forall y:set, y :e {F x|x :e X} -> forall p:prop, (forall x:set, x :e X -> y = F x -> p) -> p.
Admitted.

Theorem ReplI :
forall X:set, forall F:set->set, forall x:set, x :e X -> F x :e {F x|x :e X}.
Admitted.

Theorem Repl_Empty : forall F:set -> set, {F x|x :e Empty} = Empty.
Admitted.
