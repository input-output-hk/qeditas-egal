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
let e e':A.
assume He: G e.
assume He': G e'.
assume Heid: forall x:A, G x -> e * x = x.
assume Heid': forall x:A, G x -> x * e' = x.
prove e = e'.
rewrite <- (Heid' e He).
prove e * e' = e'.
exact (Heid e' He').
Qed.

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
let x:A.
assume Hx: G x.
assume H1: x * x = x.
prove x = e.
rewrite <- (idl x Hx).
prove e * x = e.
rewrite <- (invl x Hx).
prove (x- * x) * x = x- * x.
rewrite (assoc (x-) x x (Ginv x Hx) Hx Hx).
prove x- * (x * x) = x- * x.
rewrite H1.
apply eqI A.
Qed.

(* Treasure "1CRYSb1192DfW23671uX4FgYCg6w6xanXU" *)
Theorem left_cancel : forall x y z:A, G x -> G y -> G z -> x * y = x * z-> y = z.
let x y z:A.
assume Hx: G x.
assume Hy: G y.
assume Hz: G z.
assume H: x * y = x * z.
prove y = z.
rewrite <- (idl y Hy).
rewrite <- (idl z Hz).
prove e * y = e * z.
rewrite <- (invl x Hx).
prove (x- * x) * y = (x- * x) * z.
rewrite (assoc (x-) x y (Ginv x Hx) Hx Hy).
rewrite (assoc (x-) x z (Ginv x Hx) Hx Hz).
prove x- * (x * y) = x- * (x * z).
rewrite H.
apply eqI A.
Qed.

(* Treasure "12HwcLZN52BNc8H6TNWVPadxwHz94ubYbD" *)
Theorem right_cancel : forall x y z:A, G x -> G y -> G z -> x * z = y * z -> x = y.
let x y z:A.
assume Hx: G x.
assume Hy: G y.
assume Hz: G z.
assume H: x * z = y * z.
prove x = y.
rewrite <- (idr x Hx).
rewrite <- (idr y Hy).
prove x * e = y * e.
rewrite <- (invr z Hz).
rewrite <- (assoc x z (z-) Hx Hz (Ginv z Hz)).
rewrite <- (assoc y z (z-) Hy Hz (Ginv z Hz)).
prove (x * z) * z- = (y * z) * z-.
rewrite H.
apply eqI A.
Qed.

(* Treasure "13kfe3ojmxZb2Mgznrr5vuTF9PCxqkuvf2" *)
Theorem inv_uniq : forall x y:A, G x -> G y -> x * y = e -> x = y-.
let x y:A.
assume Hx: G x.
assume Hy: G y.
assume H: x * y = e.
prove x = y-.
rewrite <- (idl (y-) (Ginv y Hy)).
prove x = e * y-.
rewrite <- H.
prove x = (x * y) * y-.
rewrite (assoc x y (y-) Hx Hy (Ginv y Hy)).
prove x = x * (y * y-).
rewrite (invr y Hy).
prove x = x * e.
rewrite (idr x Hx).
prove x = x.
apply eqI A.
Qed.

(* Treasure "1pAWeoXxyYNazwRYo4ThV3qojLECoTQ1F" *)
Theorem inv_invol : forall x:A, G x -> x-- = x.
let x:A.
assume Hx: G x.
rewrite <- (idr x Hx) at 2.
prove x-- = x * e.
rewrite <- (invr (x-) (Ginv x Hx)).
prove x-- = x * (x- * x--).
rewrite <- (assoc x (x-) (x--) Hx (Ginv x Hx) (Ginv (x-) (Ginv x Hx))).
prove x-- = (x * x-) * x--.
rewrite (invr x Hx).
prove x-- = e * x--.
rewrite (idl (x--) (Ginv (x-) (Ginv x Hx))).
apply eqI A.
Qed.

(* Treasure "165cUuWzrbLpqJXGeWAzMknnnjiBv8ZdSG" *)
Theorem inv_op : forall x y:A, G x -> G y -> x- * y- = (y * x)-.
let x y:A.
assume Hx: G x.
assume Hy: G y.
prove x- * y- = (y * x)-.
apply (inv_uniq (x- * y-) (y * x) (Gop (x-) (y-) (Ginv x Hx) (Ginv y Hy)) (Gop y x Hy Hx)).
prove (x- * y-) * (y * x) = e.
rewrite (assoc (x-) (y-) (y * x) (Ginv x Hx) (Ginv y Hy) (Gop y x Hy Hx)).
prove x- * (y- * (y * x)) = e.
rewrite <- (assoc (y-) y x (Ginv y Hy) Hy Hx).
prove x- * ((y- * y) * x) = e.
rewrite (invl y Hy).
prove x- * (e * x) = e.
rewrite (idl x Hx).
prove x- * x = e.
apply (invl x Hx).
Qed.

End Group.

