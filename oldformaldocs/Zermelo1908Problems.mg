(* Title "Zermelo's 1908 Proof of the Well-Ordering Theorem" *)
(* Author "Chad E. Brown" *)

(* Salt "2cgheoybPEBjBiyD2" *)

Section Zermelo1908.

Variable A:SType.

Let prime := fun (p:A -> prop) (x:A) => p x /\ x <> some x:A, p x.

Postfix ' 200 := prime.

Let C : (A -> prop) -> prop := fun p:A -> prop =>
  forall Q:(A -> prop) -> prop,
       (forall p:A->prop, Q p -> Q (p '))
    -> (forall D:(A->prop)->prop, D c= Q -> Q (bigintersect A D))
    -> Q p.

(* Treasure "16DVWqdXFX1sVRUAkzJfXC54qohfWxQe2Z" *)
Lemma C_prime : forall p:A->prop, C p -> C (p ').
Admitted.

(* Treasure "1LMwPj3CRLzEdL6e2Zvv7upYcZxmPr7hot" *)
Lemma C_int : forall D:(A->prop)->prop, D c= C -> C (bigintersect A D).
Admitted.

(* Treasure "12oevw7H6jbFaHij2Rebm67XnqFD2ZZDGC" *)
Lemma C_ind : forall Q:(A->prop)->prop,
       (forall p:A->prop, C p -> Q p -> Q (p '))
    -> (forall D:(A->prop)->prop, D c= C -> D c= Q -> Q (bigintersect A D))
    -> C c= Q.
Admitted.

Section Cp.

Variable p:A->prop.

(* Treasure "1EgHt3ZeATPNQgWGfJ6E2fJS7cWgsbNNvx" *)
Lemma C_lin : C p -> forall q:A->prop, C q -> q c= p \/ p c= q.
Admitted.

End Cp.

(* Treasure "1B932Rn2Ltpv4ddCUFnKWopKqxQEySL9dC" *)
Lemma C_Eps : forall p:A->prop, C p -> forall q:A->prop, C q -> q (some x:A, p x) -> p c= q.
Admitted.

Let clos := fun (p:A -> prop) => bigintersect A (fun q => C q /\ p c= q).

Section closp.

Variable p:A->prop.

(* Treasure "15yLhoRjQhWBv7i6Gfuri2KxFhcwVT1P3h" *)
Lemma C_clos : C (clos p).
Admitted.

(* Treasure "1GSqVJChbe6BiAdwfGuvsjDuAujYvcmM1" *)
Lemma clos_subq : forall x:A, p x -> clos p x.
Admitted.

(* Treasure "1FugT7s8ox3CKL2pPKeq1YBFzGUWm6CJYE" *)
Lemma clos_Eps : (exists x:A, p x) -> p (some x:A, clos p x).
Admitted.

End closp.

Definition ZermeloWO := fun (a:A) => clos (fun x => x = a).

Let R := ZermeloWO.

Infix <= 490 := R.

(* Treasure "15dFrugBpoAMTCYsrABSQSsTrPsZPN1wy5" *)
Lemma CR : forall a:A, C (R a).
Admitted.

(* Treasure "1JBUBhAhsXPQhuV6bjSSZ1NLE5QHEoLrs2" *)
Lemma R_ref : reflexive A R.
Admitted.

(* Treasure "1GNkZySXKSjdukVqP6Q1pA9Upu4tvWmbzL" *)
Lemma R_Eps : forall a:A, (some x:A, R a x) = a.
Admitted.

(* Treasure "1DewJze7HwmYFsFnDCm2VTysb2hYCEQ6ND" *)
Lemma R_lin : linear A R.
Admitted.

(* Treasure "1LhxeTrnx8tK6GjxFQF2Ev5kVFZUwCwHST" *)
Lemma R_tra : transitive A R.
Admitted.

(* Treasure "18BWmiMEyvqaPU3QfPPf22KR4R99FoBL2U" *)
Lemma R_antisym : antisymmetric A R.
Admitted.

(* Treasure "19gxP34ZK1A7CAN9q8jVz2ihwZeVbs1BGm" *)
Lemma R_partialorder : partialorder A R.
Admitted.

(* Treasure "1N2Btig1vdAC3pYxGoAsCauZWKZxCKLtpC" *)
Lemma R_totalorder : totalorder A R.
Admitted.

(* Treasure "1BNcwaWqnEGUz4WtZqhexuK3SN79T1Ey2m" *)
Lemma R_wo : forall p:A->prop, (exists x:A, p x) -> exists x:A, p x /\ forall y:A, p y -> x <= y.
Admitted.

Definition ZermeloWOstrict := fun (a b:A) => R a b /\ a <> b.
Let lt := ZermeloWOstrict.

Infix < 490 := lt.

(* Treasure "115K8EwLkPuWnddfnVKQcoZTw5Fu5F7dF9" *)
Lemma lt_trich : trichotomous_or A lt.
Admitted.

(* Treasure "1FtbkUfep6Pfis3abQ6RBQykaXu3ggCjYs" *)
Lemma lt_stricttotalorder : stricttotalorder A lt.
Admitted.

(* Treasure "1317wb94d46bWDNfQjHqHMBfESxkuKZ9E8" *)
Lemma lt_wo : forall (p:A -> prop), (exists x:A, p x) -> exists x:A, p x /\ forall y:A, p y /\ y <> x -> x < y.
Admitted.

(* Treasure "18iLRCWDkQuwWcHjz3pVw3YXYQi6dpmsdQ" *)
Theorem Zermelo_WO : exists r : A -> A -> prop,
    totalorder A r
 /\ (forall p:A->prop, (exists x:A, p x) -> exists x:A, p x /\ forall y:A, p y -> r x y).
Admitted.

(* Treasure "1NRqj6n7w7wcFRhcJZQ51XmqKiXxcBdTp2" *)
Theorem Zermelo_WO_strict : exists r : A -> A -> prop,
    stricttotalorder A r
 /\ (forall p:A->prop, (exists x:A, p x) -> exists x:A, p x /\ forall y:A, p y /\ y <> x -> r x y).
Admitted.

End Zermelo1908.
