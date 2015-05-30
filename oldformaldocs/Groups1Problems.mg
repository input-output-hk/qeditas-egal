(* Title "A Few Basic Group Theory Results" *)
(* Author "Anonymous" *)

(* Salt "8AB52FzHiO7SVzrEhGo" *)

(** (Metalevel) Groups. Hungerford _Algebra_ Theorem 1.2 **)
Section Group.
Variable A:SType.
Variable G:A -> prop.
Variable op:A -> A -> A.
Infix * 400 left := op.
Hypothesis Gop : forall x y:A, G x -> G y -> G (x * y).
Hypothesis assoc : forall x y z:A, G x -> G y -> G z -> (x * y) * z = x * (y * z).

(* Treasure "16dPNmuuMFZPEnoqmBBD2QXQou3vGmYrNJ" *)
Theorem id_uniq : forall e e':A, G e -> G e' -> (forall x:A, G x -> e * x = x) -> (forall x:A, G x -> x * e' = x) -> e = e'.
Admitted.

Variable e:A.
Hypothesis Ge : G e.
Hypothesis idl : forall x:A, G x -> e * x = x.
Hypothesis idr : forall x:A, G x -> x * e = x.

Variable inv:A->A.
Postfix - 390 := inv.
Hypothesis Ginv : forall x:A, G x -> G (x-).
Hypothesis invl : forall x:A, G x -> x- * x = e.
Hypothesis invr : forall x:A, G x -> x * x- = e.

(* Treasure "1JiVMeYnXCJP3PWmAiDuzGnpp2LMTwpL55" *)
Theorem sqs_id : forall x:A, G x -> x * x = x -> x = e.
Admitted.

(* Treasure "1CRYSb1192DfW23671uX4FgYCg6w6xanXU" *)
Theorem left_cancel : forall x y z:A, G x -> G y -> G z -> x * y = x * z-> y = z.
Admitted.

(* Treasure "12HwcLZN52BNc8H6TNWVPadxwHz94ubYbD" *)
Theorem right_cancel : forall x y z:A, G x -> G y -> G z -> x * z = y * z -> x = y.
Admitted.

(* Treasure "13kfe3ojmxZb2Mgznrr5vuTF9PCxqkuvf2" *)
Theorem inv_uniq : forall x y:A, G x -> G y -> x * y = e -> x = y-.
Admitted.

(* Treasure "1pAWeoXxyYNazwRYo4ThV3qojLECoTQ1F" *)
Theorem inv_invol : forall x:A, G x -> x-- = x.
Admitted.

(* Treasure "165cUuWzrbLpqJXGeWAzMknnnjiBv8ZdSG" *)
Theorem inv_op : forall x y:A, G x -> G y -> x- * y- = (y * x)-.
Admitted.

End Group.

