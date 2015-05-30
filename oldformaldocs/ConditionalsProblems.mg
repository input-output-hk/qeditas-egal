(* Title "Conditionals" *)
(* Author "Chad E. Brown" *)

(* Salt "2pYk6Gx8qDthfS2n2" *)

Section IfA.

Variable A:SType.

Definition If : prop->A->A->A := (fun p x y => some z:A, p /\ z = x \/ ~p /\ z = y).

Notation IfThenElse If.

(* Treasure "1CTqeo85sMZdzrQfgYeMYbXQ4e7CjxoAF7" *)
Lemma If_correct : forall p:prop, forall x y:A,
p /\ (if p then x else y) = x \/ ~p /\ (if p then x else y) = y.
Admitted.

(* Treasure "1LgUML7jUMo2Siix3DfBQdNNmmg9nAPyMK" *)
Theorem If_0 : forall p:prop, forall x y:A,
~ p -> (if p then x else y) = y.
Admitted.

(* Treasure "14W7i2TTRhifKnYsZXjnhvxKVhHjC3Nzgo" *)
Theorem If_1 : forall p:prop, forall x y:A,
p -> (if p then x else y) = x.
Admitted.

(* Treasure "1HRKSpYC3VzUaEigPbLefgtdGyMXShGDzb" *)
Theorem If_or : forall p:prop, forall x y:A, (if p then x else y) = x \/ (if p then x else y) = y.
Admitted.

(* Treasure "1BGepHyjqguQC92DjQ3cRMz2mBNrZLnD48" *)
Example If_eta : forall p:prop, forall x:A, (if p then x else x) = x.
Admitted.

End IfA.

(* Treasure "13oAyV2Vfx6rDkXgNhsdTjkNhwnVR3aQYd" *)
Example If_True : forall p:prop, if p then p else ~p.
Admitted.

(* Treasure "13d9U4HBsdFDCBdzTC31BDU1Agpo4ojU8N" *)
Example If_False : forall p:prop, ~if p then ~p else p.
Admitted.

(* Treasure "1PfyJEFcGaW7uvEjTRxKeRE6bn3cZ1z3AY" *)
Example If_not_eq : forall p:prop, (~p) = if p then False else True.
Admitted.

(* Treasure "15D3XH7zqFGDdni1bYoy6gxe4VTusnAA4f" *)
Example If_imp_eq : forall p q:prop, (p -> q) = if p then q else True.
Admitted.

(* Treasure "1BdHJn721bLudgowFVyCTRpEiZ4nwYnG28" *)
Example If_and_eq : forall p q:prop, (p /\ q) = if p then q else False.
Admitted.

(* Treasure "1DNCMYjXU21GD9ch6Z8H6FmAy8FaKNpdTa" *)
Example If_or_eq : forall p q:prop, (p \/ q) = if p then True else q.
Admitted.
