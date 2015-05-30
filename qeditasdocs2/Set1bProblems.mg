(* Title "Introduction to the Zermelo-Fraenkel Set Operators II" *)
(* Author "Chad E. Brown" *)

(* Salt "WwQk4WMPwu2ssNdv" *)

(** Given two sets y and z, (UPair y z) is {y,z}. **)

Definition UPair : set->set->set :=
fun y z => {if Empty :e X then y else z | X :e Power (Power Empty)}.

Notation SetEnum2 UPair.

Theorem UPairE :
forall x y z:set, x :e {y,z} -> x = y \/ x = z.
Admitted.

Theorem UPairI1 : forall y z:set, y :e {y,z}.
Admitted.

Theorem UPairI2 : forall y z:set, z :e {y,z}.
Admitted.

Lemma UPair_com_Subq : forall x y:set, {x,y} c= {y,x}.
Admitted.

Theorem UPair_com : forall x y:set, {x,y} = {y,x}.
Admitted.

Definition Sing : set -> set := fun x => {x,x}.
Notation SetEnum1 Sing.

Theorem SingI : forall x:set, x :e {x}. 
Admitted.

Theorem SingE : forall x y:set, y :e {x} -> y = x. 
Admitted.

Definition binunion : set -> set -> set := fun X Y => Union {X,Y}.

(* Unicode :\/: "222a" *)
Infix :\/: 345 left := binunion.

Theorem binunionI1 : forall X Y z:set, z :e X -> z :e X :\/: Y.
Admitted.

Theorem binunionI2 : forall X Y z:set, z :e Y -> z :e X :\/: Y.
Admitted.

Theorem binunionE : forall X Y z:set, z :e X :\/: Y -> z :e X \/ z :e Y.
Admitted.

Definition SetAdjoin : set->set->set := fun X y => X :\/: {y}.

Notation SetEnum Empty Sing UPair SetAdjoin.

Theorem Power_0_Sing_0 : Power Empty = {Empty}.
Admitted.

Theorem Repl_UPair : forall F:set->set, forall x y:set, {F z|z :e {x,y}} = {F x,F y}.
Admitted.

Theorem Repl_Sing : forall F:set->set, forall x:set, {F z|z :e {x}} = {F x}.
Admitted.

Lemma Repl_restr_1 : forall X:set, forall F G:set -> set, (forall x:set, x :e X -> F x = G x) -> {F x|x :e X} c= {G x|x :e X}.
Admitted.

Theorem Repl_restr : forall X:set, forall F G:set -> set, (forall x:set, x :e X -> F x = G x) -> {F x|x :e X} = {G x|x :e X}.
Admitted.

Definition famunion:set->(set->set)->set
:= fun X F => Union {F x|x :e X}.

(* Unicode \/_ "22C3" *)
(* Subscript \/_ *)
Binder \/_ , := famunion.

Theorem famunionI:forall X:set, forall F:(set->set), forall x y:set, x :e X -> y :e F x -> y :e \/_ x :e X, F x.
Admitted.

Theorem famunionE:forall X:set, forall F:(set->set), forall y:set, y :e (\/_ x :e X, F x) -> exists x :e X, y :e F x.
Admitted.

Theorem UnionEq_famunionId:forall X:set, Union X = \/_ x :e X, x.
Admitted.

Theorem ReplEq_famunion_Sing:forall X:set, forall F:(set->set), {F x|x :e X} = \/_ x :e X, {F x}.
Admitted.
