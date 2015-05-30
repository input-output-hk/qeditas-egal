(* Title "Binary Relations" *)
(* Author "Chad E. Brown" *)

(* Salt "2MCsV9Ybj16WfiWJW" *)

Section RelnPoly1.

Variable A:SType.

Definition reflexive : (A->A->prop)->prop := fun R => forall x:A, R x x.

Definition irreflexive : (A->A->prop)->prop := fun R => forall x:A, ~R x x.

Definition symmetric : (A->A->prop)->prop := fun R => forall x y:A, R x y -> R y x.

Definition antisymmetric : (A->A->prop)->prop := fun R => forall x y:A, R x y -> R y x -> x = y.

Definition transitive : (A->A->prop)->prop := fun R => forall x y z:A, R x y -> R y z -> R x z.

Definition eqreln : (A->A->prop)->prop := fun R => reflexive R /\ symmetric R /\ transitive R.

Definition per : (A->A->prop)->prop := fun R => symmetric R /\ transitive R.

Definition linear : (A->A->prop)->prop := fun R => forall x y:A, R x y \/ R y x.

Definition trichotomous_or : (A->A->prop)->prop := fun R => forall x y:A, R x y \/ x = y \/ R y x.

Definition partialorder : (A->A->prop)->prop := fun R => reflexive R /\ antisymmetric R /\ transitive R.

Definition totalorder : (A->A->prop)->prop := fun R => partialorder R /\ linear R.

Definition strictpartialorder : (A->A->prop)->prop := fun R => irreflexive R /\ transitive R.

Definition stricttotalorder : (A->A->prop)->prop := fun R => strictpartialorder R /\ trichotomous_or R.

(* Treasure "18TGbC9PpTiYs18DjwKWTvhFiALtGYxsph" *)
Example eqreln_eq : eqreln (eq A).
Admitted.

(* Treasure "162uPF12Tq5FW1BsXB4Vq1Bt3VqrrpKdE9" *)
Example eqreln_full : eqreln (fun x y:A => True).
Admitted.

(* Treasure "13aQocJcrYBix38dBTosBZYYTeiGwMn7hT" *)
Example per_empty : per (fun x y:A => False).
Admitted.

(* Treasure "164GgMyeFawAFUkqGz4uEXU7Yp37HRnZ1i" *)
Theorem per_sym : forall R:A->A->prop, per R -> symmetric R.
Admitted.

(* Treasure "1L4hyLhZp2xQnvKcdCVUHBuN39Zi5qfGFB" *)
Theorem per_tra : forall R:A->A->prop, per R -> transitive R.
Admitted.

(* Treasure "1P8grZxuBis8W3f7enirEXeDtm5HFHU1Bz" *)
Theorem per_stra1 : forall R:A->A->prop, per R -> forall x y z:A, R y x -> R y z -> R x z.
Admitted.

(* Treasure "12n3vPoFq4qMAWB3ZxcCDRyMRUXozqKdQh" *)
Theorem per_stra2 : forall R:A->A->prop, per R -> forall x y z:A, R x y -> R z y -> R x z.
Admitted.

(* Treasure "19sTzPNPz1gn7AKUrsT8qSMozNuKAWCZ5m" *)
Theorem per_stra3 : forall R:A->A->prop, per R -> forall x y z:A, R y x -> R z y -> R x z.
Admitted.

(* Treasure "17c6jB4Qy4VtbzvgMJGfA58ihve1guWBAW" *)
Theorem per_ref1 : forall R:A->A->prop, per R -> forall x y:A, R x y -> R x x.
Admitted.

(* Treasure "18KvknsdsMBS4Vicn5XkK8ukieYoSAtEm8" *)
Theorem per_ref2 : forall R:A->A->prop, per R -> forall x y:A, R x y -> R y y.
Admitted.

(* Treasure "1MhMAvCKPmsVMFHj3zJQPVM3RzSMTEvqa4" *)
Theorem partialorder_strictpartialorder : forall R:A->A->prop,
  partialorder R -> strictpartialorder (fun x y => R x y /\ x <> y).
Admitted.

Definition reflclos : (A->A->prop)->(A->A->prop) := fun R x y => R x y \/ x = y.

Postfix ' 400 := reflclos.

(* Treasure "1GkwpeV29i4PoWwpYeWyKdRw231dy1gNPq" *)
Theorem reflclos_refl : forall R:A->A->prop, reflexive (R ').
Admitted.

(* Treasure "1Afkor4MsL1jSRT1FtH62xKCGHwWNzSRA" *)
Theorem reflclos_min : forall R S:A->A->prop, R c= S -> reflexive S -> R ' c= S.
Admitted.

(* Treasure "1HA3evcnDUrejG56P9JpXo3cDaPEWbgPqW" *)
Theorem strictpartialorder_partialorder_reflclos : forall R:A->A->prop, strictpartialorder R -> partialorder (R ').
Admitted.

(* Treasure "182qvW9zryikboViW1pifyYRKgLmQ8YtDn" *)
Theorem stricttotalorder_totalorder_reflclos : forall R:A->A->prop,
  stricttotalorder R -> totalorder (R ').
Admitted.

End RelnPoly1.

Section RelnPoly1b.

Variable A:SType.

(* Treasure "1FrnvrLbhBAq61syeWb1NMuXqqK5eNXjWG" *)
Theorem partialorder_subpredq : partialorder (A -> prop) (fun X Y:A -> prop => X c= Y).
Admitted.

(* Treasure "13GxzbQ2F7QRkgBH9fmd72hXm8j2kd6DC5" *)
Theorem strictpartialorder_subpred : strictpartialorder (A -> prop) (fun X Y:A -> prop => X c= Y /\ X <> Y).
Admitted.

Variable U:(A->prop)->prop.

Hypothesis U_int : forall D:(A->prop)->prop, D c= U -> U (bigintersect A D).
Hypothesis U_sep : forall x y:A, ~(exists P:A->prop, U P /\ P x /\ ~P y) -> ~(exists P:A->prop, U P /\ P y /\ ~P x) -> x = y.
Hypothesis U_lin : forall P Q:A->prop, U P -> U Q -> P c= Q \/ Q c= P.

Let R : A->A->prop := fun x y:A => forall P:A->prop, U P -> P x -> P y.

(* Treasure "1ABdZnLd5BjrLHjR51Es2Szv6jiG1bV1Cu" *)
Theorem totalorder_as_upperclosed : totalorder A R.
Admitted.

End RelnPoly1b.
