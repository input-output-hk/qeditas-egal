(* Title "Introduction to the Zermelo-Fraenkel Set Operators II" *)
(* Author "Chad E. Brown" *)

(* Salt "WwQk4WMPwu2ssNdv" *)

(** Given two sets y and z, (UPair y z) is {y,z}. **)

Definition UPair : set->set->set :=
fun y z => {if Empty :e X then y else z | X :e Power (Power Empty)}.

Notation SetEnum2 UPair.

(* Treasure "1LsZFq6KAEetFJLPH46ttFGxsHwcBvyktx" *)
Theorem UPairE :
forall x y z:set, x :e {y,z} -> x = y \/ x = z.
Admitted.

(* Treasure "17xapMwRp5RbbsGKh44hq1BBuMP7eMAAMQ" *)
Theorem UPairI1 : forall y z:set, y :e {y,z}.
Admitted.

(* Treasure "1MxAH2go6xbySB1u5dRZTYLDD81UMXn15a" *)
Theorem UPairI2 : forall y z:set, z :e {y,z}.
Admitted.

(* Treasure "1N3JVqEbi5u5nUcaFrjxJJLUpT6mTHZQ36" *)
Lemma UPair_com_Subq : forall x y:set, {x,y} c= {y,x}.
Admitted.

(* Treasure "12H3nffLmfBmaETk7yoMuNHb7gbFVi7FNX" *)
Theorem UPair_com : forall x y:set, {x,y} = {y,x}.
Admitted.

Definition Sing : set -> set := fun x => {x,x}.
Notation SetEnum1 Sing.

(* Treasure "19cy1hw2e2PKn2ahAoPkaK2JAVsWmFutj4" *)
Theorem SingI : forall x:set, x :e {x}. 
Admitted.

(* Treasure "1LfBR62qGfMJCSfSaJsxUHBbGXaxaPzFWD" *)
Theorem SingE : forall x y:set, y :e {x} -> y = x. 
Admitted.

Definition binunion : set -> set -> set := fun X Y => Union {X,Y}.

(* Unicode :\/: "222a" *)
Infix :\/: 345 left := binunion.

(* Treasure "1JHuPppgfdCXt3AWnZCMc4Jx958iq9zeWH" *)
Theorem binunionI1 : forall X Y z:set, z :e X -> z :e X :\/: Y.
Admitted.

(* Treasure "1KtkqZHR5fDvwaeRJPdDAc1RptXuf3gQiH" *)
Theorem binunionI2 : forall X Y z:set, z :e Y -> z :e X :\/: Y.
Admitted.

(* Treasure "19RyogaDJMBv64GDTCh8R8F2PW3nu54XuY" *)
Theorem binunionE : forall X Y z:set, z :e X :\/: Y -> z :e X \/ z :e Y.
Admitted.

Definition SetAdjoin : set->set->set := fun X y => X :\/: {y}.

Notation SetEnum Empty Sing UPair SetAdjoin.

(* Treasure "1HkrrPVrjvpWJZCXgqWbx2utZqMJptNWpG" *)
Theorem Power_0_Sing_0 : Power Empty = {Empty}.
Admitted.

(* Treasure "1JdxV3jP8KKpcdmDeZurZnv6ZAeQLHA6C2" *)
Theorem Repl_UPair : forall F:set->set, forall x y:set, {F z|z :e {x,y}} = {F x,F y}.
Admitted.

(* Treasure "19TH87oKNCBs5ULNiWyTkrfoFAzgr5kyjH" *)
Theorem Repl_Sing : forall F:set->set, forall x:set, {F z|z :e {x}} = {F x}.
Admitted.

(* Treasure "1AnvsP2DroVLWUMbcbuiYDyxcVzQWcaU1R" *)
Lemma Repl_restr_1 : forall X:set, forall F G:set -> set, (forall x:set, x :e X -> F x = G x) -> {F x|x :e X} c= {G x|x :e X}.
Admitted.

(* Treasure "19e4vjBh54XtUkXp6oxTK1VLGcB7N7bXf1" *)
Theorem Repl_restr : forall X:set, forall F G:set -> set, (forall x:set, x :e X -> F x = G x) -> {F x|x :e X} = {G x|x :e X}.
Admitted.

Definition famunion:set->(set->set)->set
:= fun X F => Union {F x|x :e X}.

(* Unicode \/_ "22C3" *)
(* Subscript \/_ *)
Binder \/_ , := famunion.

(* Treasure "1GyJcord2uX9UrdXbYtnzoxXXbnGE2nH4s" *)
Theorem famunionI:forall X:set, forall F:(set->set), forall x y:set, x :e X -> y :e F x -> y :e \/_ x :e X, F x.
Admitted.

(* Treasure "1NUbG5BVsbCCjmRDTYBgCo3gGVJaATvQ48" *)
Theorem famunionE:forall X:set, forall F:(set->set), forall y:set, y :e (\/_ x :e X, F x) -> exists x :e X, y :e F x.
Admitted.

(* Treasure "1HYvXdRQcwPHVb4SwfuMkZUqvFMmrmCqdY" *)
Theorem UnionEq_famunionId:forall X:set, Union X = \/_ x :e X, x.
Admitted.

(* Treasure "198U8nYqdBvE8CLaYiyVNqe4ePKNtvuV5o" *)
Theorem ReplEq_famunion_Sing:forall X:set, forall F:(set->set), {F x|x :e X} = \/_ x :e X, {F x}.
Admitted.
