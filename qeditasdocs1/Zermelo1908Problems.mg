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

Lemma C_prime : forall p:A->prop, C p -> C (p ').
Admitted.

Lemma C_int : forall D:(A->prop)->prop, D c= C -> C (bigintersect A D).
Admitted.

Lemma C_ind : forall Q:(A->prop)->prop,
       (forall p:A->prop, C p -> Q p -> Q (p '))
    -> (forall D:(A->prop)->prop, D c= C -> D c= Q -> Q (bigintersect A D))
    -> C c= Q.
Admitted.

Section Cp.

Variable p:A->prop.

Lemma C_lin : C p -> forall q:A->prop, C q -> q c= p \/ p c= q.
Admitted.

End Cp.

Lemma C_Eps : forall p:A->prop, C p -> forall q:A->prop, C q -> q (some x:A, p x) -> p c= q.
Admitted.

Let clos := fun (p:A -> prop) => bigintersect A (fun q => C q /\ p c= q).

Section closp.

Variable p:A->prop.

Lemma C_clos : C (clos p).
Admitted.

Lemma clos_subq : forall x:A, p x -> clos p x.
Admitted.

Lemma clos_Eps : (exists x:A, p x) -> p (some x:A, clos p x).
Admitted.

End closp.

Definition ZermeloWO := fun (a:A) => clos (fun x => x = a).

Let R := ZermeloWO.

Infix <= 490 := R.

Lemma CR : forall a:A, C (R a).
Admitted.

Lemma R_ref : reflexive A R.
Admitted.

Lemma R_Eps : forall a:A, (some x:A, R a x) = a.
Admitted.

Lemma R_lin : linear A R.
Admitted.

Lemma R_tra : transitive A R.
Admitted.

Lemma R_antisym : antisymmetric A R.
Admitted.

Lemma R_partialorder : partialorder A R.
Admitted.

Lemma R_totalorder : totalorder A R.
Admitted.

Lemma R_wo : forall p:A->prop, (exists x:A, p x) -> exists x:A, p x /\ forall y:A, p y -> x <= y.
Admitted.

Definition ZermeloWOstrict := fun (a b:A) => R a b /\ a <> b.
Let lt := ZermeloWOstrict.

Infix < 490 := lt.

Lemma lt_trich : trichotomous_or A lt.
Admitted.

Lemma lt_stricttotalorder : stricttotalorder A lt.
Admitted.

Lemma lt_wo : forall (p:A -> prop), (exists x:A, p x) -> exists x:A, p x /\ forall y:A, p y /\ y <> x -> x < y.
Admitted.

Theorem Zermelo_WO : exists r : A -> A -> prop,
    totalorder A r
 /\ (forall p:A->prop, (exists x:A, p x) -> exists x:A, p x /\ forall y:A, p y -> r x y).
Admitted.

Theorem Zermelo_WO_strict : exists r : A -> A -> prop,
    stricttotalorder A r
 /\ (forall p:A->prop, (exists x:A, p x) -> exists x:A, p x /\ forall y:A, p y /\ y <> x -> r x y).
Admitted.

End Zermelo1908.
