(* Title "Introduction to the Zermelo-Fraenkel Set Operators III" *)
(* Author "Chad E. Brown" *)

(* Salt "2jJNJaCAtb77Cnk6Q" *)

(* Treasure "1hjgWGp14aVpqQzQuukLmJgQz7Ud9R64v" *)
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

(* Treasure "1DoiVbMwFVwDM6ZaMGAk8G76LNHUoe45p1" *)
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

(* Treasure "14DYL9JnNPEspSGhbT3jQF6P7uP2s9gAdz" *)
Theorem Power_Sing_0 : Power {Empty} = {Empty,{Empty}}.
exact (Power_Sing Empty).
Qed.

(* Treasure "1JmsZ7waSLA1gFBUgjU6xCeqdosQS945pr" *)
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

(* Treasure "1FQtu81nvDBuQqwXZDvgGcncu8qWDPrL7m" *)
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

(* Treasure "1G12Ut89QYi4uGniEo2mC4o3KwZz7pjcWq" *)
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

(* Treasure "13C876Pudr84ZuQEP9Qh3JdUCy9pZyYsLm" *)
Theorem SepE1:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X.
exact (fun X P x H => SepE X P x H (x :e X) (fun H _ => H)).
Qed.

(* Treasure "18AqyZdy94FgmcyztVJ1jUD8qJ47ZHJnrr" *)
Theorem SepE2:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> P x.
exact (fun X P x H => SepE X P x H (P x) (fun _ H => H)).
Qed.

(* Treasure "15RPuU9unz3jAPJ71R2BXiEW8SvmRHEjUL" *)
Theorem Sep_Subq : forall X:set, forall P:set->prop, {x :e X|P x} c= X.
exact SepE1.
Qed.

(* Treasure "1KVAuSQbzn6oS1maSvzcqTTo8MLgggRZY9" *)
Theorem Sep_In_Power : forall X:set, forall P:set->prop, {x :e X|P x} :e Power X.
exact (fun X P => PowerI X (Sep X P) (Sep_Subq X P)).
Qed.

Definition ReplSep : set->(set->prop)->(set->set)->set := fun X P F => {F x|x :e {z :e X|P z}}.
Notation ReplSep ReplSep.

(* Treasure "1GjuK12HaYGM65ZNZAYBpNzTaLxZM3aULn" *)
Theorem ReplSepI: forall X:set, forall P:set->prop, forall F:set->set, forall x:set, x :e X -> P x -> F x :e {F x|x :e X, P x}.
exact (fun X P F x u v => ReplI (Sep X P) F x (SepI X P x u v)).
Qed.

(* Treasure "1Dyrji3hZBrVX5s5rpVh9BDkrfN244WJF6" *)
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

(* Treasure "1JcPs96Xt1SQATDDRtME6mueynAm32ZWSQ" *)
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
