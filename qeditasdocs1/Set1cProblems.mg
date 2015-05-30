(* Title "Introduction to the Zermelo-Fraenkel Set Operators III" *)
(* Author "Chad E. Brown" *)

(* Salt "2jJNJaCAtb77Cnk6Q" *)

Theorem Empty_or_ex : forall X:set, X = Empty \/ exists x:set, x :e X.
Admitted.

Theorem Power_Sing : forall x:set, Power {x} = {Empty,{x}}.
Admitted.

Theorem Power_Sing_0 : Power {Empty} = {Empty,{Empty}}.
Admitted.

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

Theorem SepI:forall X:set, forall P:(set->prop), forall x:set, x :e X -> P x -> x :e {x :e X|P x}.
Admitted.

Theorem SepE:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X /\ P x.
Admitted.

Theorem SepE1:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X.
Admitted.

Theorem SepE2:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> P x.
Admitted.

Theorem Sep_Subq : forall X:set, forall P:set->prop, {x :e X|P x} c= X.
Admitted.

Theorem Sep_In_Power : forall X:set, forall P:set->prop, {x :e X|P x} :e Power X.
Admitted.

Definition ReplSep : set->(set->prop)->(set->set)->set := fun X P F => {F x|x :e {z :e X|P z}}.
Notation ReplSep ReplSep.

Theorem ReplSepI: forall X:set, forall P:set->prop, forall F:set->set, forall x:set, x :e X -> P x -> F x :e {F x|x :e X, P x}.
Admitted.

Theorem ReplSepE:forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> exists x:set, x :e X /\ P x /\ y = F x.
Admitted.

Theorem ReplSepE2:forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> forall p:prop, (forall x :e X, P x -> y = F x -> p) -> p.
Admitted.
