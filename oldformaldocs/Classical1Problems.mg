(* Title "Classical Principles in Simple Type Theory" *)
(* Author "Chad E. Brown" *)

(* Salt "2iXkDXTjL9DEMehVE" *)

(*** Diaconescu proof of excluded middle from choice. ***)
(* Treasure "1vag5nNTUdWA19ggSdfvWhj7JgYPgf2VS" *)
Theorem classic : forall P:prop, P \/ ~ P.
Admitted.

(* Treasure "1NLzkHCUtdvfx5WtMtZY3TBGnwWkJ6YQnV" *)
Theorem NNPP : forall p:prop, ~ ~ p -> p.
Admitted.

(* Treasure "1DDbNtVu78UDfgDrt4Ytx53XfoqLjTWzDp" *)
Theorem prop_deg : forall p:prop, p = True \/ p = False.
Admitted.

(* Treasure "18V7Jj32N4QpFVtGCKidn9aj3idHSHgcaw" *)
Theorem not_and_or_demorgan : forall A B:prop, ~(A /\ B) -> ~A \/ ~B.
Admitted.

(* Treasure "1CeWaWvM1D6Z8KWVipRRhKbq2id6m2781C" *)
Theorem not_and_or_demorgan_iff : forall A B:prop, ~(A /\ B) <-> ~A \/ ~B.
Admitted.

Section DeMorganQuants.

Variable A:SType.

(* Treasure "16jdZABV34J27MTqhdDFgJPnbzsjXf2bP2" *)
Theorem not_all_ex_demorgan : forall P:A->prop, ~(forall x:A, P x) -> exists x:A, ~P x.
Admitted.

(* Treasure "1GRf6CeKPMo1r5ynyufVVJuNhFVwWqXFqK" *)
Theorem not_all_ex_demorgan_iff : forall P:A->prop, ~(forall x:A, P x) <-> exists x:A, ~P x.
Admitted.

End DeMorganQuants.

(*** Classical Logical Identities ***)
(* Treasure "1Fn2PSwwfbp2VhsyWfvhQ5dzu6USH4C9Ta" *)
Theorem eq_neg_neg_id : eq (prop->prop) (fun x:prop => ~~x) (fun x:prop => x).
Admitted.

(* Treasure "14gFBnBCPg3zvgYhEwPw3kT9P91UKf2V2i" *)
Theorem eq_true : True = (~False).
Admitted.

(* Treasure "1CXPPqvMNiKAG2EoTAdXLwJb8U9QAPTLFz" *)
Theorem eq_and_nor : and = (fun (x y:prop) => ~(~x \/ ~y)).
Admitted.

(* Treasure "1EnXkQRKchAf4b64opBEXMmHHb748fhoQ6" *)
Theorem eq_or_nand : or = (fun (x y:prop) => ~(~x /\ ~y)).
Admitted.

(* Treasure "1K9Uo1ibWdJpZsXfjbNMi5mgApttju86Wb" *)
Theorem eq_or_imp : or = (fun (x y:prop) => ~ x -> y).
Admitted.

(* Treasure "1JhoYo7MN5fVGYiMWr5tU7aj51so1e4n2J" *)
Theorem eq_and_imp : and = (fun (x y:prop) => ~ (x -> ~ y)).
Admitted.

(* Treasure "1P3qXcabk2Daih2BCh2NMWS14H7GpCnP8f" *)
Theorem eq_imp_or : (fun (x y:prop) => (x -> y)) = (fun (x y:prop) => (~x \/ y)).
Admitted.

(* Treasure "1B3WiPyR66LiRdKBS2sVmreqVTPgC2MtEQ" *)
Theorem eq_contrapositive : (fun (x y:prop) => (x -> y)) = (fun (x y:prop) => (~y -> ~x)).
Admitted.

(* Treasure "16SLEVfh8wPbrGHZrSjCysv2qB6eA117Dm" *)
Theorem eq_iff : iff = (eq prop).
Admitted.

Section EqThms.

Variable A:SType.

(* Treasure "1vxkdkjUmjQHGf721pnaJkJ24fkfCmT8r" *)
Theorem eq_sym_eq : (fun (x y:A) => x = y) = (fun (x y:A) => y = x).
Admitted.

(* Treasure "1D77Ln1BH2R7jzdpWVo3zszPUSuKxdggVm" *)
Theorem eq_forall_nexists : (fun (f:A -> prop) => forall x:A, f x) = (fun (f:A -> prop) => ~exists x:A, ~f x).
Admitted.

(* Treasure "19MCAHqKz5TjtepwxD8hpKS2sSwj37eFAm" *)
Theorem eq_exists_nforall : (ex A) = (fun (f:A -> prop) => ~forall x:A, ~f x).
Admitted.

(* Treasure "1NchdpXfj6TWzxkpdWvmj35m1Q3JXiQdhZ" *)
Theorem eq_leib2 : (fun (x y:A) => forall (p: A -> prop), ~ p x -> ~ p y) = (eq A).
Admitted.

(* Treasure "197mvMPAj6jdb8Mf9MPRf5tjhxQwJHLbYk" *)
Theorem eq_leib3 : (fun (x y:A) => forall (r: A -> A -> prop), (forall z:A, r z z) -> r x y) = (eq A).
Admitted.

(* Treasure "1Bhj1mjHo9x8kDCizDYH4ttpvnQTK8XPAG" *)
Theorem eq_leib4 : (fun (x y:A) => forall (r: A -> A -> prop),~ r x y -> ~ (forall z:A, r z z)) = (eq A).
Admitted.

End EqThms.

Section Exercises.

Variable A:SType.

(* Treasure "16FPEPeuxs2rkdvbY4LhSZvJ1FS9tkirSw" *)
Example Drinker : forall d:A->prop, exists x:A, d x -> forall x:A, d x.
Admitted.

End Exercises.
