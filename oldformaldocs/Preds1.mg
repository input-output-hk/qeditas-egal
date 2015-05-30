(* Title "Predicates and Extensionality" *)
(* Author "Chad E. Brown" *)

(* Salt "xnE3owiTuEcAVzpj" *)

Section PredPoly1.
Variable A:SType.

Definition pred_empty : A->prop := fun x:A => False.

Definition pred_full : A->prop := fun x:A => True.

(* Treasure "1MKMXsiMQw5miKLz8HNEKK18VNYYRpBTZe" *)
Theorem pred_empty_min : forall P:A->prop, pred_empty c= P.
exact (fun P x H => H (P x)).
Qed.

(* Treasure "18a9uqNqDiTJYmitN35SE3dpzt25zopp9d" *)
Theorem pred_full_max : forall P:A->prop, P c= pred_full.
exact (fun P x _ => TrueI).
Qed.

Definition pred_union : (A->prop)->(A->prop)->(A->prop) :=
 fun P Q:A->prop => fun x:A => P x \/ Q x.

Definition pred_intersect : (A->prop)->(A->prop)->(A->prop) :=
 fun P Q:A->prop => fun x:A => P x /\ Q x.

Definition pred_compl : (A->prop)->(A->prop) :=
 fun P:A->prop => fun x:A => ~P x.

(* Treasure "1Jb6CANTBJm4ZWTRdLV9BCkadRm4Sqp6eC" *)
Theorem pred_union_ub1 : forall P Q:A->prop, P c= pred_union P Q.
let P Q x.
assume H: P x.
prove pred_union P Q x.
prove P x \/ Q x.
apply orIL.
exact H.
Qed.

(* Treasure "1PhzPJsqATeEEQFUjrTwGbkVd5ntFHjq8p" *)
Theorem pred_union_ub2 : forall P Q:A->prop, Q c= pred_union P Q.
let P Q x.
assume H: Q x.
prove pred_union P Q x.
prove P x \/ Q x.
apply orIR.
exact H.
Qed.

(* Treasure "1DPs55aL5DSbRS92pQNTX5WAuZWdUPdsXQ" *)
Theorem pred_union_min : forall P Q R:A->prop, P c= R -> Q c= R -> pred_union P Q c= R.
let P Q R.
assume H1: P c= R.
assume H2: Q c= R.
let x.
assume H3: P x \/ Q x.
prove R x.
apply H3.
- assume H4: P x.
  exact (H1 x H4).
- assume H4: Q x.
  exact (H2 x H4).
Qed.

(* Treasure "13wDMvdaMHyaugpVEj6JPQAeRP2nDYGhaj" *)
Theorem pred_intersect_lb1 : forall P Q:A->prop, pred_intersect P Q c= P.
let P Q x.
assume H: pred_intersect P Q x.
prove P x.
exact (andEL (P x) (Q x) H).
Qed.

(* Treasure "1Q2tJW4vQy35Sawpu2MK9tH7zkgyxvM52s" *)
Theorem pred_intersect_lb2 : forall P Q:A->prop, pred_intersect P Q c= Q.
let P Q x.
assume H: pred_intersect P Q x.
prove Q x.
exact (andER (P x) (Q x) H).
Qed.

(* Treasure "13751B3hfT2UryRZZz39k8NGtuTNpeGmqn" *)
Theorem pred_intersect_max : forall P Q R:A->prop, R c= P -> R c= Q -> R c= pred_intersect P Q.
let P Q R.
assume H1: R c= P.
assume H2: R c= Q.
let x.
assume H3: R x.
prove P x /\ Q x.
apply andI.
- exact (H1 x H3).
- exact (H2 x H3).
Qed.

Definition bigintersect := fun (D:(A->prop)->prop) (x:A) => forall P:A->prop, D P -> P x.

Definition bigunion := fun (D:(A->prop)->prop) (x:A) => exists P:A->prop, D P /\ P x.

End PredPoly1.

(** Propositional extensionality: Equivalent propositions are equal. **)

Axiom prop_ext : forall A B:prop, (A <-> B) -> A = B.

(* Treasure "1GsFMJSF7xNKgUTyWBYikS56m8tnRUhkYy" *)
Theorem prop_ext2 : forall A B:prop, (A -> B) -> (B -> A) -> A = B.
exact (fun A B H1 H2 => prop_ext A B (iffI A B H1 H2)).
Qed.

(** Functional extensionality: Equivalent functions are equal. **)
Section FE.
Variable A B:SType.
Axiom func_ext : forall (f g : A -> B), (forall x:A, f x = g x) -> f = g.
End FE.

Section PE.
Variable A:SType.

(* Treasure "17DrGSetpQLPeyeoy688Xcod8XUSPjYnzR" *)
Theorem pred_ext : forall (P Q : A -> prop), P c= Q -> Q c= P -> P = Q.
exact (fun P Q HPQ HQP => func_ext A prop P Q (fun x => prop_ext2 (P x) (Q x) (HPQ x) (HQP x))).
Qed.

End PE.

Section RE.
Variable A B:SType.

(* Treasure "1DsEVkMddgLt8YyHKdbicsn9Z1YRE2iLNZ" *)
Theorem reln_ext : forall (R S : A -> B -> prop), R c= S -> S c= R -> R = S.
exact (fun R S HRS HSR => func_ext A (B->prop) R S (fun x => pred_ext B (R x) (S x) (HRS x) (HSR x))).
Qed.

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
let P.
apply (pred_ext A).
- prove I P (C P) c= E.
  let x.
  assume H1: P x /\ C P x.
  prove False.
  apply H1.
  assume H2: P x.
  assume H3: ~P x.
  exact (H3 H2).
- prove E c= I P (C P).
  exact (pred_empty_min A (I P (C P))).
Qed.

(* Treasure "1KNqUt5yBVudZxJpw7Z68eiYHLEXNznsBA" *)
Theorem pred_union_com : forall P Q:A->prop, U P Q = U Q P.
let P Q. apply (pred_ext A).
- prove U P Q c= U Q P.
  let x.
  exact (or_com_imp (P x) (Q x)).
- prove U Q P c= U P Q.
  let x.
  exact (or_com_imp (Q x) (P x)).
Qed.

(* Treasure "1ETnowyT8BNYerTSJtkzaA6RtdynFoDnPi" *)
Theorem pred_union_asso : forall P Q R:A->prop, U P (U Q R) = U (U P Q) R.
let P Q R. apply (pred_ext A).
- prove U P (U Q R) c= U (U P Q) R.
  let x.
  exact (or_asso_imp1 (P x) (Q x) (R x)).
- prove U (U P Q) R c= U P (U Q R).
  let x.
  exact (or_asso_imp2 (P x) (Q x) (R x)).
Qed.

(* Treasure "1LN4v8zdCMDfQumJVPE7BnHn5VYm6KiPmY" *)
Theorem pred_intersect_com : forall P Q:A->prop, I P Q = I Q P.
let P Q. apply (pred_ext A).
- prove I P Q c= I Q P.
  let x.
  exact (and_com_imp (P x) (Q x)).
- prove I Q P c= I P Q.
  let x.
  exact (and_com_imp (Q x) (P x)).
Qed.

(* Treasure "12BAstcgUtCmRwMsEAGLzEkTRsVH2FggrA" *)
Theorem pred_intersect_asso : forall P Q R:A->prop, I P (I Q R) = I (I P Q) R.
let P Q R. apply (pred_ext A).
- prove I P (I Q R) c= I (I P Q) R.
  let x.
  exact (and_asso_imp1 (P x) (Q x) (R x)).
- prove I (I P Q) R c= I P (I Q R).
  let x.
  exact (and_asso_imp2 (P x) (Q x) (R x)).
Qed.

(* Treasure "1McFHNBC5wFTtC68mZ7jn9J1R2Gm4qkRML" *)
Theorem pred_intersect_union_distrL : forall P Q R:A->prop, I P (U Q R) = U (I P Q) (I P R).
let P Q R. apply (pred_ext A).
- prove I P (U Q R) c= U (I P Q) (I P R).
  let x.
  exact (and_or_distrL_imp1 (P x) (Q x) (R x)).
- prove U (I P Q) (I P R) c= I P (U Q R).
  let x.
  exact (and_or_distrL_imp2 (P x) (Q x) (R x)).
Qed.

(* Treasure "18JorrPtefLoNQbk4kDRmtbSgamRPBueMx" *)
Theorem pred_intersect_union_distrR : forall P Q R:A->prop, I (U P Q) R = U (I P R) (I Q R).
let P Q R.
rewrite pred_intersect_com.
prove I R (U P Q) = U (I P R) (I Q R).
rewrite pred_intersect_union_distrL.
prove U (I R P) (I R Q) = U (I P R) (I Q R).
rewrite pred_intersect_com.
prove U (I P R) (I R Q) = U (I P R) (I Q R).
rewrite pred_intersect_com at 2.
prove U (I P R) (I Q R) = U (I P R) (I Q R).
exact (eqI (A->prop) (U (I P R) (I Q R))).
Qed.

(* Treasure "13jQ1Syr7zMAp3PdFEbb4aL8ZDUn3H4R6v" *)
Theorem pred_union_intersect_distrL : forall P Q R:A->prop, U P (I Q R) = I (U P Q) (U P R).
let P Q R. apply (pred_ext A).
- prove U P (I Q R) c= I (U P Q) (U P R).
  let x.
  exact (or_and_distrL_imp1 (P x) (Q x) (R x)).
- prove I (U P Q) (U P R) c= U P (I Q R).
  let x.
  exact (or_and_distrL_imp2 (P x) (Q x) (R x)).
Qed.

(* Treasure "162DQ8UV24crkTUyTtdVpM4i6KuaPq2iSL" *)
Theorem pred_union_intersect_distrR : forall P Q R:A->prop, U (I P Q) R = I (U P R) (U Q R).
let P Q R.
claim L1: U (I P Q) R = U R (I P Q).
{ apply pred_union_com. }
claim L2: U R (I P Q) = I (U R P) (U R Q).
{ apply pred_union_intersect_distrL. }
claim L3: I (U R P) (U R Q) = I (U P R) (U Q R).
{
  rewrite pred_union_com.
  rewrite pred_union_com at 2.
  exact (eqI (A->prop) (I (U P R) (U Q R))).
}
exact (eq_trans3 (A->prop)
                 (U (I P Q) R)
                 (U R (I P Q))
                 (I (U R P) (U R Q))
                 (I (U P R) (U Q R))
                 L1 L2 L3).
Qed.

End PredPoly2.
