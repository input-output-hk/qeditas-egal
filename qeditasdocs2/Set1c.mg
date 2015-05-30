(* Title "Introduction to the Zermelo-Fraenkel Set Operators III" *)
(* Author "Chad E. Brown" *)

(* Salt "2jJNJaCAtb77Cnk6Q" *)

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
Definition or : prop -> prop -> prop := fun A B : prop => forall P : prop , (A -> P) -> (B -> P) -> P.
(* Unicode \/ "2228" *)
Infix \/ 785 left  := or.
Axiom orIL : forall A B : prop , A -> A \/ B.
Axiom orIR : forall A B : prop , B -> A \/ B.
Axiom and3I : forall P1 P2 P3 : prop, P1 -> P2 -> P3 -> P1 /\ P2 /\ P3.
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
Axiom exandE : forall P Q : A -> prop , (exists x : A , P x /\ Q x) -> forall p : prop , (forall x : A , P x -> Q x -> p) -> p.
End Poly1_exthms.
Section Choice.
Variable A : SType.
Parameter Eps : (A -> prop) -> A.
Axiom EpsR : forall P : A -> prop , forall x : A , P x -> P (Eps P).
End Choice.
Binder some , := Eps.
Section ChoiceThms.
Variable A : SType.
Axiom EpsR2 : forall P : A -> prop , (exists x : A , P x) -> P (some x : A , P x).
End ChoiceThms.
Axiom classic : forall P : prop , P \/ ~ P.
Section IfA.
Variable A : SType.
Definition If : prop -> A -> A -> A := (fun p x y => some z : A , p /\ z = x \/ ~ p /\ z = y).
Notation IfThenElse If.
Axiom If_correct : forall p : prop , forall x y : A , p /\ (if p then x else y) = x \/ ~ p /\ (if p then x else y) = y.
Axiom If_0 : forall p : prop , forall x y : A , ~ p -> (if p then x else y) = y.
Axiom If_1 : forall p : prop , forall x y : A , p -> (if p then x else y) = x.
Axiom If_or : forall p : prop , forall x y : A , (if p then x else y) = x \/ (if p then x else y) = y.
Axiom If_eta : forall p : prop , forall x : A , (if p then x else x) = x.
End IfA.
Parameter In : set -> set -> prop.
Definition nIn : set -> set -> prop := fun x X => ~ In x X.
(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.
Definition Subq : set -> set -> prop := fun X Y => forall x : set , x :e X -> x :e Y.
Binder+ exists , := ex ; and.
Binder some , := Eps ; and.
Axiom set_ext : forall X Y : set , X c= Y -> Y c= X -> X = Y.
(* Unicode Empty "2205" *)
Parameter Empty : set.
Axiom EmptyE : forall x : set , x /:e Empty.
Axiom Subq_Empty : forall X : set , Empty c= X.
Axiom Empty_eq : forall X : set , (forall x , x /:e X) -> X = Empty.
(* Unicode Power "1D4AB" *)
Parameter Power : set -> set.
Axiom PowerE : forall X Y : set , Y :e Power X -> Y c= X.
Axiom PowerI : forall X Y : set , Y c= X -> Y :e (Power X).
Axiom Empty_In_Power : forall X : set , Empty :e Power X.
Axiom Self_In_Power : forall X : set , X :e Power X.
Parameter Repl : set -> (set -> set) -> set.
Notation Repl Repl.
Axiom ReplE : forall X : set , forall F : set -> set , forall y : set , y :e {F x|x :e X} -> exists x : set , x :e X /\ y = F x.
Axiom ReplE2 : forall X : set , forall F : set -> set , forall y : set , y :e {F x|x :e X} -> forall p : prop , (forall x : set , x :e X -> y = F x -> p) -> p.
Axiom ReplI : forall X : set , forall F : set -> set , forall x : set , x :e X -> F x :e {F x|x :e X}.
(* Parameter UPair MM7DGQPznayt6juAGExgMfTfAFmB3TUo5yTKCJZ37zpfyzJN *)
Parameter UPair : set -> set -> set.
Notation SetEnum2 UPair.
Axiom UPairE : forall x y z : set , x :e {y,z} -> x = y \/ x = z.
Axiom UPairI1 : forall y z : set , y :e {y,z}.
Axiom UPairI2 : forall y z : set , z :e {y,z}.
(* Parameter Sing MHQKaPMuqpPD7JYxt91FMGRr1nnP2YZ3625uoySLjwF6JjbU *)
Parameter Sing : set -> set.
Notation SetEnum1 Sing.
Axiom SingE : forall x y : set , y :e {x} -> y = x.
Axiom SingI : forall x : set , x :e {x}.

(** Main Body **)

Theorem Empty_or_ex : forall X:set, X = Empty \/ exists x:set, x :e X.
let X.
apply (classic (exists x:set, x :e X)).
- assume H1: exists x:set, x :e X. apply orIR. exact H1.
- assume H1: ~exists x:set, x :e X. apply orIL. apply set_ext.
  + let x. assume H2: x :e X.
    prove False.
    apply H1. witness x. exact H2.
  + exact (Subq_Empty X).
Qed.

Theorem Power_Sing : forall x:set, Power {x} = {Empty,{x}}.
let x. apply set_ext.
- let y.
  assume H1: y :e Power {x}.
  prove y :e {Empty,{x}}.
  apply (classic (x :e y)).
  + assume H2: x :e y.
    claim L1: y = {x}.
    {
      apply set_ext.
      - exact (PowerE {x} y H1).
      - let z. assume H3: z :e {x}.
        prove z :e y.
        rewrite (SingE x z H3).
        prove x :e y.
        exact H2.
    }
    rewrite L1.
    prove {x} :e {Empty,{x}}.
    exact (UPairI2 Empty {x}).
  + assume H2: x /:e y.
    claim L1: y = Empty.
    {
      apply Empty_eq.
      let z. assume H3: z :e y.
      claim L1a: z :e {x}.
      { exact (PowerE {x} y H1 z H3). }
      claim L1b: z = x.
      { exact (SingE x z L1a). }
      apply H2. rewrite <- L1b. exact H3.
    }
    rewrite L1.
    prove Empty :e {Empty,{x}}.
    exact (UPairI1 Empty {x}).
- let y.
  assume H1: y :e {Empty,{x}}.
  prove y :e Power {x}.
  apply (UPairE y Empty {x} H1).
  + assume H2: y = Empty.
    rewrite H2.
    prove Empty :e Power {x}.
    exact (Empty_In_Power {x}).
  + assume H2: y = {x}.
    rewrite H2.
    prove {x} :e Power {x}.
    exact (Self_In_Power {x}).
Qed.

Theorem Power_Sing_0 : Power {Empty} = {Empty,{Empty}}.
exact (Power_Sing Empty).
Qed.

Theorem Eps_set_R : forall X:set, forall P:set->prop, forall x :e X, P x -> (some x :e X, P x) :e X /\ P (some x :e X, P x).
exact (fun X P x H1 H2 => EpsR set (fun x => x :e X /\ P x) x (andI (x :e X) (P x) H1 H2)).
Qed.

Section SepSec.

Variable X:set.
Variable P:set->prop.
Let z : set := some z :e X, P z.
Let F:set->set := fun x => if P x then x else z.

Definition Sep:set
:= if (exists z :e X, P z) then {F x|x :e X} else Empty.

End SepSec.

Notation Sep Sep.

Theorem SepI:forall X:set, forall P:(set->prop), forall x:set, x :e X -> P x -> x :e {x :e X|P x}.
let X P x.
set z : set := some z :e X, P z.
set F : set->set := fun x => if P x then x else z.
assume H1: x :e X.
assume H2: P x.
claim L1: exists z :e X, P z.
{
  witness x. apply andI.
  - exact H1.
  - exact H2.
}
prove x :e {x :e X|P x}.
prove x :e if (exists z :e X, P z) then {F x|x :e X} else Empty.
(*** Note:
 Making L2 a claim and then rewriting with it succeeds, but rewrite (If_1 set (exists z :e X, P z) {F x|x :e X} Empty L1) fails.
 The reason is that when the proposition proved by (If_1 set (exists z :e X, P z) {F x|x :e X} Empty L1) is
 extracted by the code, the F x will be beta reduced to be if P x then x else z. After this beta reduction, the left hand side of the
 equation does not match the right hand side of the claim x :e if (exists z :e X, P z) then {F x|x :e X} else Empty.
 This is an example of how one must be careful using the apply and rewrite tactics and must sometimes give these
 kinds of explicit annotations, i.e., proving a beta-eta-delta equivalent claim.
 ***)
claim L2: (if (exists z :e X, P z) then {F x|x :e X} else Empty) = {F x|x :e X}.
{
  exact (If_1 set (exists z :e X, P z) {F x|x :e X} Empty L1).
}
rewrite L2.
prove x :e {F x|x :e X}.
claim L3: F x = x.
{
  prove (if P x then x else z) = x.
  exact (If_1 set (P x) x z H2).
}
rewrite <- L3.
prove F x :e {F x|x :e X}.
exact (ReplI X F x H1).
Qed.

Theorem SepE:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X /\ P x.
let X P x.
set z : set := some z :e X, P z.
set F : set->set := fun x => if P x then x else z.
apply (classic (exists z :e X, P z)).
- assume H1: exists z :e X, P z.
  prove (x :e (if (exists z :e X, P z) then {F x|x :e X} else Empty) -> x :e X /\ P x).
  claim L1: (if (exists z :e X, P z) then {F x|x :e X} else Empty) = {F x|x :e X}.
  {
    exact (If_1 set (exists z :e X, P z) {F x|x :e X} Empty H1).
  }
  rewrite L1.
  prove x :e {F x|x :e X} -> x :e X /\ P x.
  assume H2: x :e {F x|x :e X}.
  apply (ReplE2 X F x H2).
  let y.
  assume H3: y :e X.
  assume H4: x = F y.
  prove x :e X /\ P x.
  apply (classic (P y)).
  + assume H5: P y.
    claim L2: x = y.
    {
      rewrite <- (If_1 set (P y) y z H5).
      exact H4.
    }
    rewrite L2.
    prove y :e X /\ P y.
    apply andI.
    * exact H3.
    * exact H5.
  + assume H5: ~P y.
    claim L2: x = z.
    {
      rewrite <- (If_0 set (P y) y z H5).
      exact H4.
    }
    rewrite L2.
    prove z :e X /\ P z.
    exact (EpsR2 set (fun z => z :e X /\ P z) H1).
- assume H1: ~exists z :e X, P z.
  prove (x :e (if (exists z :e X, P z) then {F x|x :e X} else Empty) -> x :e X /\ P x).
  claim L1: (if (exists z :e X, P z) then {F x|x :e X} else Empty) = Empty.
  { exact (If_0 set (exists z :e X, P z) {F x|x :e X} Empty H1). }
  rewrite L1.
  prove x :e Empty -> x :e X /\ P x.
  assume H2: x :e Empty.
  prove False.
  exact (EmptyE x H2).
Qed.

Theorem SepE1:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X.
exact (fun X P x H => SepE X P x H (x :e X) (fun H _ => H)).
Qed.

Theorem SepE2:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> P x.
exact (fun X P x H => SepE X P x H (P x) (fun _ H => H)).
Qed.

Theorem Sep_Subq : forall X:set, forall P:set->prop, {x :e X|P x} c= X.
exact SepE1.
Qed.

Theorem Sep_In_Power : forall X:set, forall P:set->prop, {x :e X|P x} :e Power X.
exact (fun X P => PowerI X (Sep X P) (Sep_Subq X P)).
Qed.

Definition ReplSep : set->(set->prop)->(set->set)->set := fun X P F => {F x|x :e {z :e X|P z}}.
Notation ReplSep ReplSep.

Theorem ReplSepI: forall X:set, forall P:set->prop, forall F:set->set, forall x:set, x :e X -> P x -> F x :e {F x|x :e X, P x}.
exact (fun X P F x u v => ReplI (Sep X P) F x (SepI X P x u v)).
Qed.

Theorem ReplSepE:forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> exists x:set, x :e X /\ P x /\ y = F x.
let X P F y.
assume H1: y :e {F x|x :e {z :e X|P z}}.
apply (ReplE {z :e X|P z} F y H1).
let x.
assume H2: x :e {z :e X|P z} /\ y = F x.
apply H2.
assume H3: x :e {z :e X|P z}.
assume H4: y = F x.
apply (SepE X P x H3).
assume H5: x :e X.
assume H6: P x.
witness x.
apply and3I.
- exact H5.
- exact H6.
- exact H4.
Qed.

Theorem ReplSepE2:forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> forall p:prop, (forall x :e X, P x -> y = F x -> p) -> p.
let X P F y.
assume H1: y :e {F x|x :e X, P x}.
let p.
assume H2: forall x :e X, P x -> y = F x -> p.
prove p.
apply (exandE set (fun x => x :e X /\ P x) (fun x => y = F x) (ReplSepE X P F y H1) p).
prove forall x:set, x :e X /\ P x -> y = F x -> p.
let x.
assume H3: x :e X /\ P x.
apply H3.
exact (H2 x).
Qed.
