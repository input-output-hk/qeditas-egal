(* Title "Predicates and Extensionality" *)
(* Author "Chad E. Brown" *)

(* Salt "xnE3owiTuEcAVzpj" *)

Section PredPoly1.
Variable A:SType.

Definition pred_empty : A->prop := fun x:A => False.

Definition pred_full : A->prop := fun x:A => True.

(* Treasure "1MKMXsiMQw5miKLz8HNEKK18VNYYRpBTZe" *)
Theorem pred_empty_min : forall P:A->prop, pred_empty c= P.
Admitted.

(* Treasure "18a9uqNqDiTJYmitN35SE3dpzt25zopp9d" *)
Theorem pred_full_max : forall P:A->prop, P c= pred_full.
Admitted.

Definition pred_union : (A->prop)->(A->prop)->(A->prop) :=
 fun P Q:A->prop => fun x:A => P x \/ Q x.

Definition pred_intersect : (A->prop)->(A->prop)->(A->prop) :=
 fun P Q:A->prop => fun x:A => P x /\ Q x.

Definition pred_compl : (A->prop)->(A->prop) :=
 fun P:A->prop => fun x:A => ~P x.

(* Treasure "1Jb6CANTBJm4ZWTRdLV9BCkadRm4Sqp6eC" *)
Theorem pred_union_ub1 : forall P Q:A->prop, P c= pred_union P Q.
Admitted.

(* Treasure "1PhzPJsqATeEEQFUjrTwGbkVd5ntFHjq8p" *)
Theorem pred_union_ub2 : forall P Q:A->prop, Q c= pred_union P Q.
Admitted.

(* Treasure "1DPs55aL5DSbRS92pQNTX5WAuZWdUPdsXQ" *)
Theorem pred_union_min : forall P Q R:A->prop, P c= R -> Q c= R -> pred_union P Q c= R.
Admitted.

(* Treasure "13wDMvdaMHyaugpVEj6JPQAeRP2nDYGhaj" *)
Theorem pred_intersect_lb1 : forall P Q:A->prop, pred_intersect P Q c= P.
Admitted.

(* Treasure "1Q2tJW4vQy35Sawpu2MK9tH7zkgyxvM52s" *)
Theorem pred_intersect_lb2 : forall P Q:A->prop, pred_intersect P Q c= Q.
Admitted.

(* Treasure "13751B3hfT2UryRZZz39k8NGtuTNpeGmqn" *)
Theorem pred_intersect_max : forall P Q R:A->prop, R c= P -> R c= Q -> R c= pred_intersect P Q.
Admitted.

Definition bigintersect := fun (D:(A->prop)->prop) (x:A) => forall P:A->prop, D P -> P x.

Definition bigunion := fun (D:(A->prop)->prop) (x:A) => exists P:A->prop, D P /\ P x.

End PredPoly1.

(** Propositional extensionality: Equivalent propositions are equal. **)

Axiom prop_ext : forall A B:prop, (A <-> B) -> A = B.

(* Treasure "1GsFMJSF7xNKgUTyWBYikS56m8tnRUhkYy" *)
Theorem prop_ext2 : forall A B:prop, (A -> B) -> (B -> A) -> A = B.
Admitted.

(** Functional extensionality: Equivalent functions are equal. **)
Section FE.
Variable A B:SType.
Axiom func_ext : forall (f g : A -> B), (forall x:A, f x = g x) -> f = g.
End FE.

Section PE.
Variable A:SType.

(* Treasure "17DrGSetpQLPeyeoy688Xcod8XUSPjYnzR" *)
Theorem pred_ext : forall (P Q : A -> prop), P c= Q -> Q c= P -> P = Q.
Admitted.

End PE.

Section RE.
Variable A B:SType.

(* Treasure "1DsEVkMddgLt8YyHKdbicsn9Z1YRE2iLNZ" *)
Theorem reln_ext : forall (R S : A -> B -> prop), R c= S -> S c= R -> R = S.
Admitted.

End RE.

(** Consequences of Extensionality **)
Section PredPoly2.

Variable A:SType.

Let E := pred_empty A.
Let C := pred_compl A.
Let I := pred_intersect A.
Let U := pred_union A.

(* Treasure "1J8sAj8RThfyHA3XRjrc5w813jsrshVoE2" *)
Theorem pred_intersect_compl_empty : forall P:A->prop, I P (C P) = E.
Admitted.

(* Treasure "1KNqUt5yBVudZxJpw7Z68eiYHLEXNznsBA" *)
Theorem pred_union_com : forall P Q:A->prop, U P Q = U Q P.
Admitted.

(* Treasure "1ETnowyT8BNYerTSJtkzaA6RtdynFoDnPi" *)
Theorem pred_union_asso : forall P Q R:A->prop, U P (U Q R) = U (U P Q) R.
Admitted.

(* Treasure "1LN4v8zdCMDfQumJVPE7BnHn5VYm6KiPmY" *)
Theorem pred_intersect_com : forall P Q:A->prop, I P Q = I Q P.
Admitted.

(* Treasure "12BAstcgUtCmRwMsEAGLzEkTRsVH2FggrA" *)
Theorem pred_intersect_asso : forall P Q R:A->prop, I P (I Q R) = I (I P Q) R.
Admitted.

(* Treasure "1McFHNBC5wFTtC68mZ7jn9J1R2Gm4qkRML" *)
Theorem pred_intersect_union_distrL : forall P Q R:A->prop, I P (U Q R) = U (I P Q) (I P R).
Admitted.

(* Treasure "18JorrPtefLoNQbk4kDRmtbSgamRPBueMx" *)
Theorem pred_intersect_union_distrR : forall P Q R:A->prop, I (U P Q) R = U (I P R) (I Q R).
Admitted.

(* Treasure "13jQ1Syr7zMAp3PdFEbb4aL8ZDUn3H4R6v" *)
Theorem pred_union_intersect_distrL : forall P Q R:A->prop, U P (I Q R) = I (U P Q) (U P R).
Admitted.

(* Treasure "162DQ8UV24crkTUyTtdVpM4i6KuaPq2iSL" *)
Theorem pred_union_intersect_distrR : forall P Q R:A->prop, U (I P Q) R = I (U P R) (U Q R).
Admitted.

End PredPoly2.
