(* Title "Introduction to the Zermelo-Fraenkel Set Operators III" *)
(* Author "Chad E. Brown" *)

(* Salt "2jJNJaCAtb77Cnk6Q" *)

(* Treasure "1hjgWGp14aVpqQzQuukLmJgQz7Ud9R64v" *)
Theorem Empty_or_ex : forall X:set, X = Empty \/ exists x:set, x :e X.
Admitted.

(* Treasure "1DoiVbMwFVwDM6ZaMGAk8G76LNHUoe45p1" *)
Theorem Power_Sing : forall x:set, Power {x} = {Empty,{x}}.
Admitted.

(* Treasure "14DYL9JnNPEspSGhbT3jQF6P7uP2s9gAdz" *)
Theorem Power_Sing_0 : Power {Empty} = {Empty,{Empty}}.
Admitted.

(* Treasure "1JmsZ7waSLA1gFBUgjU6xCeqdosQS945pr" *)
Theorem Eps_set_R : forall X:set, forall P:set->prop, forall x :e X, P x -> (some x :e X, P x) :e X /\ P (some x :e X, P x).
Admitted.

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
Admitted.

(* Treasure "1G12Ut89QYi4uGniEo2mC4o3KwZz7pjcWq" *)
Theorem SepE:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X /\ P x.
Admitted.

(* Treasure "13C876Pudr84ZuQEP9Qh3JdUCy9pZyYsLm" *)
Theorem SepE1:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X.
Admitted.

(* Treasure "18AqyZdy94FgmcyztVJ1jUD8qJ47ZHJnrr" *)
Theorem SepE2:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> P x.
Admitted.

(* Treasure "15RPuU9unz3jAPJ71R2BXiEW8SvmRHEjUL" *)
Theorem Sep_Subq : forall X:set, forall P:set->prop, {x :e X|P x} c= X.
Admitted.

(* Treasure "1KVAuSQbzn6oS1maSvzcqTTo8MLgggRZY9" *)
Theorem Sep_In_Power : forall X:set, forall P:set->prop, {x :e X|P x} :e Power X.
Admitted.

Definition ReplSep : set->(set->prop)->(set->set)->set := fun X P F => {F x|x :e {z :e X|P z}}.
Notation ReplSep ReplSep.

(* Treasure "1GjuK12HaYGM65ZNZAYBpNzTaLxZM3aULn" *)
Theorem ReplSepI: forall X:set, forall P:set->prop, forall F:set->set, forall x:set, x :e X -> P x -> F x :e {F x|x :e X, P x}.
Admitted.

(* Treasure "1Dyrji3hZBrVX5s5rpVh9BDkrfN244WJF6" *)
Theorem ReplSepE:forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> exists x:set, x :e X /\ P x /\ y = F x.
Admitted.

(* Treasure "1JcPs96Xt1SQATDDRtME6mueynAm32ZWSQ" *)
Theorem ReplSepE2:forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> forall p:prop, (forall x :e X, P x -> y = F x -> p) -> p.
Admitted.
