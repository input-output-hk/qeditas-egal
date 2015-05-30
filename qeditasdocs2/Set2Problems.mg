(* Title "Basic Set Operations" *)
(* Author "Chad E. Brown" *)

(* Salt "cpsZu1tVzsnNo79P" *)

Theorem binunion_asso:forall X Y Z:set, X :\/: (Y :\/: Z) = (X :\/: Y) :\/: Z.
Admitted.

Lemma binunion_com_Subq:forall X Y:set, X :\/: Y c= Y :\/: X.
Admitted.

Theorem binunion_com:forall X Y:set, X :\/: Y = Y :\/: X.
Admitted.

Theorem binunion_idl:forall X:set, Empty :\/: X = X.
Admitted.

Theorem binunion_idr:forall X:set, X :\/: Empty = X.
Admitted.

Theorem binunion_idem:forall X:set, X :\/: X = X.
Admitted.

Theorem binunion_Subq_1: forall X Y:set, X c= X :\/: Y.
Admitted.

Theorem binunion_Subq_2: forall X Y:set, Y c= X :\/: Y.
Admitted.

Theorem binunion_Subq_min: forall X Y Z:set, X c= Z -> Y c= Z -> X :\/: Y c= Z.
Admitted.

Theorem Subq_binunion_eq:forall X Y, (X c= Y) = (X :\/: Y = Y).
Admitted.

Theorem binunion_nIn_I : forall X Y z:set, z /:e X -> z /:e Y -> z /:e X :\/: Y.
Admitted.

Theorem binunion_nIn_E : forall X Y z:set, z /:e X :\/: Y -> z /:e X /\ z /:e Y.
Admitted.

Definition binintersect:set->set->set
:= fun X Y => {x :e X |x :e Y}.

(* Unicode :/\: "2229" *)
Infix :/\: 340 left := binintersect.

Theorem binintersectI:forall X Y z, z :e X -> z :e Y -> z :e X :/\: Y.
Admitted.

Theorem binintersectE:forall X Y z, z :e X :/\: Y -> z :e X /\ z :e Y.
Admitted.

Theorem binintersectE1:forall X Y z, z :e X :/\: Y -> z :e X.
Admitted.

Theorem binintersectE2:forall X Y z, z :e X :/\: Y -> z :e Y.
Admitted.

Theorem binintersect_Subq_1:forall X Y:set, X :/\: Y c= X.
Admitted.

Theorem binintersect_Subq_2:forall X Y:set, X :/\: Y c= Y.
Admitted.

Theorem binintersect_Subq_max:forall X Y Z:set, Z c= X -> Z c= Y -> Z c= X :/\: Y.
Admitted.

Theorem binintersect_asso:forall X Y Z:set, X :/\: (Y :/\: Z) = (X :/\: Y) :/\: Z.
Admitted.

Lemma binintersect_com_Subq: forall X Y:set, X :/\: Y c= Y :/\: X.
Admitted.

Theorem binintersect_com: forall X Y:set, X :/\: Y = Y :/\: X.
Admitted.

Theorem binintersect_annil:forall X:set, Empty :/\: X = Empty.
Admitted.

Theorem binintersect_annir:forall X:set, X :/\: Empty = Empty.
Admitted.

Theorem binintersect_idem:forall X:set, X :/\: X = X.
Admitted.

Theorem binintersect_binunion_distr:forall X Y Z:set, X :/\: (Y :\/: Z) = X :/\: Y :\/: X :/\: Z.
Admitted.

Theorem binunion_binintersect_distr:forall X Y Z:set, X :\/: Y :/\: Z = (X :\/: Y) :/\: (X :\/: Z).
Admitted.

Theorem Subq_binintersection_eq:forall X Y:set, (X c= Y) = (X :/\: Y = X).
Admitted.

Theorem binintersect_nIn_I1 : forall X Y z:set, z /:e X -> z /:e X :/\: Y.
Admitted.

Theorem binintersect_nIn_I2 : forall X Y z:set, z /:e Y -> z /:e X :/\: Y.
Admitted.

Theorem binintersect_nIn_E : forall X Y z:set, z /:e X :/\: Y -> z /:e X \/ z /:e Y.
Admitted.

Definition setminus:set->set->set
:= fun X Y => Sep X (fun x => x /:e Y).

(* Unicode :\: "2216" *)
Infix :\: 350 := setminus.

Theorem setminusI:forall X Y z, (z :e X) -> (z /:e Y) -> z :e X :\: Y.
Admitted.

Theorem setminusE:forall X Y z, (z :e X :\: Y) -> z :e X /\ z /:e Y.
Admitted.

Theorem setminusE1:forall X Y z, (z :e X :\: Y) -> z :e X.
Admitted.

Theorem setminusE2:forall X Y z, (z :e X :\: Y) -> z /:e Y.
Admitted.

Theorem setminus_Subq:forall X Y:set, X :\: Y c= X.
Admitted.

Theorem setminus_Subq_contra:forall X Y Z:set, Z c= Y -> X :\: Y c= X :\: Z.
Admitted.

Theorem setminus_nIn_I1: forall X Y z, z /:e X -> z /:e X :\: Y.
Admitted.

Theorem setminus_nIn_I2: forall X Y z, z :e Y -> z /:e X :\: Y.
Admitted.

Theorem setminus_nIn_E: forall X Y z, z /:e X :\: Y -> z /:e X \/ z :e Y.
Admitted.

Theorem setminus_selfannih:forall X:set, (X :\: X) = Empty.
Admitted.

Theorem setminus_binintersect:forall X Y Z:set, X :\: Y :/\: Z = (X :\: Y) :\/: (X :\: Z).
Admitted.

Theorem setminus_binunion:forall X Y Z:set, X :\: Y :\/: Z = (X :\: Y) :\: Z.
Admitted.

Theorem binintersect_setminus:forall X Y Z:set, (X :/\: Y) :\: Z = X :/\: (Y :\: Z).
Admitted.

Theorem binunion_setminus:forall X Y Z:set, X :\/: Y :\: Z = (X :\: Z) :\/: (Y :\: Z).
Admitted.

Theorem setminus_setminus:forall X Y Z:set, X :\: (Y :\: Z) = (X :\: Y) :\/: (X :/\: Z).
Admitted.

Theorem setminus_annil:forall X:set, Empty :\: X = Empty.
Admitted.

Theorem setminus_idr:forall X:set, X :\: Empty = X.
Admitted.
