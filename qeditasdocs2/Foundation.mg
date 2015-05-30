(* Title "The Foundation: Church's Simple Type Theory with Tarski-Grothendieck Set Theory" *)
(* Author "Chad E. Brown" *)

(* Unicode False "22A5" *)
Definition False : prop := forall P:prop, P.

(*** PARAGRAPH "We can now define the negation of a proposition $A$ using $\bot$." **)

Definition not : prop -> prop := fun A:prop => A -> False.

(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.

Definition and : prop -> prop -> prop := fun A B:prop => forall P:prop, (A -> B -> P) -> P.

(* Unicode /\ "2227" *)
Infix /\ 780 left := and.

Definition or : prop -> prop -> prop := fun (A B : prop) => forall P:prop, (A -> P) -> (B -> P) -> P.

(* Unicode \/ "2228" *)
Infix \/ 785 left := or.

Definition iff : prop -> prop -> prop := fun (A B:prop) => (A -> B) /\ (B -> A).

(* Unicode <-> "2194" *)
Infix <-> 805 := iff.

Section Eq.

Variable A:SType.

Definition eq : A->A->prop := fun x y:A => forall Q:A->prop, Q x -> Q y.

End Eq.

Infix = 502 := eq.

Section Ex.

Variable A:SType.

Definition ex : (A->prop)->prop := fun Q:A->prop => forall P:prop, (forall x:A, Q x -> P) -> P.

End Ex.

(* Unicode exists "2203" *)
Binder+ exists , := ex.

(** SECTION "Extensionality Principles" **)

(** Propositional extensionality: Equivalent propositions are equal. **)

Axiom prop_ext : forall A B:prop, (A <-> B) -> A = B.

(** Functional extensionality: Equivalent functions are equal. **)
Section FE.

Variable A B:SType.

Axiom func_ext : forall (f g : A -> B), (forall x:A, f x = g x) -> f = g.

End FE.

(** SECTION "Choice" **)

Section Choice.

Variable A:SType.

Parameter Eps : (A->prop)->A.

Axiom EpsR : forall P:A->prop, forall x:A, P x -> P (Eps (fun x => P x)).

End Choice.

Binder some , := Eps.

(** Set Theory Axioms **)

(** In is the membership relation on set.  We use x :e y as notation to mean "x is a member of y". The notation :e is fixed to In a priori. **)
Parameter In:set->set->prop.

(** Subq is the subset relation on set.  We use X c= Y as notation to mean "X is a subset of Y". The notation c= is fixed to Subq a priori. **)
Definition Subq : set->set->prop :=
fun X Y => forall x:set, x :e X -> x :e Y.

(** Two sets are equal if they have the same elements. Equivalently, we can always prove two sets are equal by proving they are subsets of each other. **)

Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X = Y.

(** Sets are formed iteratively, so we can prove properties about all sets by induction on membership.
Suppose P is a property of sets. If we can prove P holds for X from the inductive hypothesis that P holds for all member of X,
then P must hold for all sets. **)

Axiom In_ind : forall P:set->prop, (forall X:set, (forall x:set, x :e X -> P x) -> P X) -> forall X:set, P X.

(** Empty is the empty set. **)

(* Unicode Empty "2205" *)
Parameter Empty : set.

Axiom EmptyAx : ~exists x:set, x :e Empty.

(* Unicode Union "22C3" *)
Parameter Union : set->set.

Axiom UnionEq : forall X:set, forall x:set, x :e Union X <-> exists Y:set, x :e Y /\ Y :e X.

(** (Power X) is the set of all subsets of X. **)

(* Unicode Power "1D4AB" *)
Parameter Power : set->set.

Axiom PowerEq : forall X Y:set, Y :e Power X <-> Y c= X.

(** Given a set X, (Union X) is the set {x | there is some Y such that x :e Y and Y :e X}. That is, Union gives the union of a set of sets. **)

(** Given a set X and a function F, (Repl F X) is the set {F x|x :e X}. That is, Repl allows us to form a set by
 replacing the elements x in a set X with corresponding elements F x. **)

Parameter Repl : set->(set->set)->set.
Notation Repl Repl.

Axiom ReplEq :
forall X:set, forall F:set->set, forall y:set, y :e {F x|x :e X} <-> exists x:set, x :e X /\ y = F x.

(** Every set is a member of a Grothendieck universe. A Grothendieck universe is a transitive set closed under the previous
set theoretic operators. The assumption that Grothendieck universes exist is stronger than an axiom of infinity since (GrothUnivOf Empty) is infinite.
We also assume (GrothUnivOf X) is the least Grothendieck universe containing X. **)

Definition TransSet : set->prop := fun U:set => forall X:set, X :e U -> X c= U.

Definition Union_closed : set->prop := fun U:set => forall X:set, X :e U -> Union X :e U.
Definition Power_closed : set->prop := fun U:set => forall X:set, X :e U -> Power X :e U.
Definition Repl_closed : set->prop := fun U:set => forall X:set, X :e U -> forall F:set->set,
   (forall x:set, x :e X -> F x :e U) -> {F x|x :e X} :e U.
Definition ZF_closed : set->prop := fun U:set =>
   Union_closed U
/\ Power_closed U
/\ Repl_closed U.

Parameter UnivOf : set->set.

Axiom UnivOf_In : forall N:set, N :e UnivOf N.

Axiom UnivOf_TransSet : forall N:set, TransSet (UnivOf N).

Axiom UnivOf_ZF_closed : forall N:set, ZF_closed (UnivOf N).

Axiom UnivOf_Min : forall N U:set, N :e U
  -> TransSet U
  -> ZF_closed U
  -> UnivOf N c= U.
