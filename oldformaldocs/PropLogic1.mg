(* Title "Second-Order Propositional Logic" *)
(* Author "Chad E. Brown" *)

(* Salt "2mKw8BowAYq5vP9o5" *)

(*** Definitions of logical constants. ***)

Section BasicSystemExercises1.

Variable A:prop.

Example imp_refl : A -> A.
exact (fun H => H).
Qed.

Variable B:prop.

Example imp_revap : A -> (A -> B) -> B.
exact (fun H1 H2 => H2 H1).
Qed.

Example imp_dup : (A -> A -> B) -> (A -> B).
exact (fun H1 H2 => H1 H2 H2).
Qed.

Variable C:prop.
Example imp_trans : (A -> B) -> (B -> C) -> A -> C.
exact (fun H1 H2 H3 => H2 (H1 H3)).
Qed.

End BasicSystemExercises1.

(*** Russell-Prawitz Definitions of false, true, negation, conjunction, disjunction and existential quantification. ***)

(* Unicode False "22A5" *)
Definition False : prop := forall P:prop, P.

Theorem FalseE : forall P : prop, False -> P.
exact (fun P H => H P).
Qed.

(* Unicode True "22A4" *)
Definition True : prop := forall P:prop, P -> P.

Theorem TrueI : True.
exact (fun P p => p).
Qed.

Definition not : prop->prop := fun A:prop => A -> False.

(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.

Theorem notI : forall A:prop, (A -> False) -> ~A.
exact (fun A H a => H a).
Qed.

Theorem notE : forall A:prop, ~A -> A -> False.
exact (fun A H a => H a).
Qed.

Theorem notE2 : forall A p:prop, ~A -> A -> p.
let A p.
assume H1: ~A.
assume H2: A.
prove p.
prove False.
exact (H1 H2).
Qed.

Section BasicLogicExercises0.

Variable A:prop.

Example dnegI : A -> ~~A.
exact (fun H1 H2 => H2 H1).
Qed.

Example imp_false_dup : (A -> A -> False) -> A -> False.
exact (fun (H : A -> A -> False) (x : A) => H x x).
Qed.

Example imp_neg_neg : (A -> ~A) -> ~A.
exact imp_false_dup.
Qed.

Example imp_circuit : (A -> ~A) -> (~A -> A) -> False.
assume H1:A -> ~A.
assume H2:~A -> A.
claim L1:(A -> False) -> False.
{ assume H3:A -> False.
  prove False.
  apply H3.
  prove A.
  exact (H2 H3). }
apply L1.
prove A -> False.
prove ~A.
exact (imp_neg_neg H1).
Qed.

End BasicLogicExercises0.

Theorem contrapositive : forall A B:prop, (A -> B) -> ~B -> ~A.
let A B. assume u: A -> B. assume v: ~B. assume w:A.
prove False.
apply v.
prove B.
apply u.
prove A.
exact w.
Qed.

Definition and : prop->prop->prop := fun A B:prop => forall P:prop, (A -> B -> P) -> P.

(* Unicode /\ "2227" *)
Infix /\ 780 left := and.

Theorem andI : forall (A B : prop), A -> B -> A /\ B.
exact (fun A B a b P H => H a b).
Qed.

Theorem andEL : forall (A B : prop), A /\ B -> A.
exact (fun A B H => H A (fun a b => a)).
Qed.

Theorem andER : forall (A B : prop), A /\ B -> B.
exact (fun A B H => H B (fun a b => b)).
Qed.

Definition or : prop->prop->prop := fun (A B : prop) => forall P:prop, (A -> P) -> (B -> P) -> P.

(* Unicode \/ "2228" *)
Infix \/ 785 left := or.

Theorem orIL : forall (A B : prop), A -> A \/ B.
exact (fun A B a P H1 H2 => H1 a).
Qed.

Theorem orIR : forall (A B : prop), B -> A \/ B.
exact (fun A B b P H1 H2 => H2 b).
Qed.

Theorem orE : forall (A B C:prop), (A -> C) -> (B -> C) -> A \/ B -> C.
exact (fun A B C H1 H2 H3 => H3 C H1 H2).
Qed.

Section BasicLogicExercises1.

Variable A:prop.

(* Treasure "1FLJn2Ju9iyBohvdWKP3PkQeYS3PcA9pAa" *)
Theorem and_id_I : A -> A /\ A.
exact (fun H : A => andI A A H H).
Qed.

(* Treasure "12PT9TmUauucQUR3SejgjS3v9DuFXGNBAY" *)
Theorem and_id_E : A /\ A -> A.
exact (andEL A A).
Qed.

(* Treasure "1Gik1CFJTejEZ6Epqjtz8sfsNkA27yaHoR" *)
Theorem or_id_I : A -> A \/ A.
exact (orIL A A).
Qed.

(* Treasure "1PmJ1f1CXvMZcuWUFFBaQnX4z8nKYTPLKG" *)
Theorem or_id_E : A \/ A -> A.
exact (fun H : A \/ A => H A (imp_refl A) (imp_refl A)).
Qed.

Variable B:prop.

(* Treasure "1DpGcJse61w1KcHVfvPQU2Pc4m3H4UHZR5" *)
Theorem and_com_imp : A /\ B -> B /\ A.
assume H:A /\ B.
apply H.
assume H1 H2.
exact (andI B A H2 H1).
Qed.

(* Treasure "1DtQbL5crRDRkwDmCYQhvrvGzLPb3FVBc2" *)
Theorem or_com_imp : A \/ B -> B \/ A.
exact (fun H : A \/ B => H (B \/ A) (orIR B A) (orIL B A)).
Qed.

(* Treasure "1HM1yDPPK9w2D6hfnigKFRvoTevx1bJJPe" *)
Theorem or_not_and_demorgan : ~A \/ ~B -> ~(A /\ B).
assume u v.
prove False.
apply v.
assume a:A.
assume b:B.
prove False.
apply u.
- assume w : ~A. prove False. exact (w a).
- assume w : ~B. prove False. exact (w b).
Qed.

Theorem not_or_and_demorgan : ~(A \/ B) -> ~A /\ ~B.
assume u : ~(A \/ B).
apply andI.
- prove ~A. assume a:A. exact (u (orIL A B a)).
- prove ~B. assume b:B. exact (u (orIR A B b)).
Qed.

(* Treasure "184A9a2ncJpzosV5wQUU3jbPd3xFih965Z" *)
Theorem and_not_or_demorgan : ~A /\ ~B -> ~(A \/ B).
assume u:~A /\ ~B.
assume v:A \/ B.
apply u.
assume na nb.
apply v.
- exact (fun a => na a).
- exact (fun b => nb b).
Qed.

Variable C:prop.

Theorem and_asso_imp1 : A /\ (B /\ C) -> (A /\ B) /\ C.
assume H : A /\ (B /\ C).
apply H.
assume H1 : A.
assume H2 : B /\ C.
apply H2.
assume H3 : B.
assume H4 : C.
prove (A /\ B) /\ C.
apply andI.
- apply andI.
  + exact H1.
  + exact H3.
- exact H4.
Qed.

(* Treasure "1HkDuKhC3sWDGXw8RqptfbGC9BLD4xuizp" *)
Theorem and_asso_imp2 : (A /\ B) /\ C -> A /\ (B /\ C).
assume H : A /\ B /\ C.
apply H.
assume H1:A/\B.
assume H2:C.
apply H1.
assume H3:A.
assume H4:B.
prove A /\ (B /\ C).
exact (andI A (B /\ C) H3 (andI B C H4 H2)).
Qed.

(* Treasure "1MJZhgzkzX4MR1wVHsnzBegb7jZrX3EmGH" *)
Theorem or_asso_imp1 : A \/ (B \/ C) -> (A \/ B) \/ C.
assume H1:A\/(B\/C).
prove (A \/ B) \/ C.
apply H1.
- assume H2:A. apply orIL. apply orIL. exact H2.
- assume H2:B\/C. apply H2.
  + assume H3:B. apply orIL. apply orIR. exact H3.
  + assume H3:C. apply orIR. exact H3.
Qed.

Theorem or_asso_imp2 : (A \/ B) \/ C -> A \/ (B \/ C).
assume H1: A \/ B \/ C.
apply H1.
- assume H2: A \/ B.
  prove A \/ (B \/ C).
  apply H2.
  + assume H3: A.
    prove A \/ (B \/ C).
    apply orIL.
    prove A.
    exact H3.
  + assume H3: B.
    prove A \/ (B \/ C).
    apply orIR.
    prove B \/ C.
    apply orIL.
    prove B.
    exact H3.
- assume H2: C.
  prove A \/ (B \/ C).
  apply orIR.
  prove B \/ C.
  apply orIR.
  prove C.
  exact H2.
Qed.

(* Treasure "1PbWCQsgmEnjwaufyJBgMGSY8ndR5JPaWT" *)
Theorem and_or_distrL_imp1 : A /\ (B \/ C) -> A /\ B \/ A /\ C.
assume H1: A /\ (B \/ C).
apply H1.
assume H2: A.
assume H3: B \/ C.
prove A /\ B \/ A /\ C.
apply H3.
- assume H4: B.
  prove A /\ B \/ A /\ C.
  apply orIL.
  prove A /\ B.
  exact (andI A B H2 H4).
- assume H4: C.
  prove A /\ B \/ A /\ C.
  apply orIR.
  prove A /\ C.
  exact (andI A C H2 H4).
Qed.

(* Treasure "13nAxocJeEoTNfNrfZUnCnEkeGVNbLygbf" *)
Theorem and_or_distrL_imp2 : A /\ B \/ A /\ C -> A /\ (B \/ C).
assume H1: A /\ B \/ A /\ C.
apply H1.
- assume H2 : A /\ B. prove A /\ (B \/ C). apply H2.
  assume H3: A.
  assume H4: B.
  exact (andI A (B \/ C) H3 (orIL B C H4)).
- assume H2 : A /\ C. prove A /\ (B \/ C). apply H2.
  assume H3: A.
  assume H4: C.
  exact (andI A (B \/ C) H3 (orIR B C H4)).
Qed.

(* Treasure "1BAT7VMFkqsKmrukpoLxsNwc8fUUHo59Wh" *)
Theorem and_or_distrR_imp1 : (A \/ B) /\ C -> A /\ C \/ B /\ C.
assume H1:(A \/ B) /\ C.
prove A /\ C \/ B /\ C.
apply H1.
assume H2:A \/ B. assume H3:C. apply H2.
- assume H4:A. apply orIL.
  prove A /\ C.
  apply andI.
  + exact H4.
  + exact H3.
- assume H4:B. apply orIR.
  prove B /\ C.
  apply andI.
  + exact H4.
  + exact H3.
Qed.

(* Treasure "16DNgUKqFZrTqbBm8vYcV6W1L1PzSJLCpQ" *)
Theorem and_or_distrR_imp2 : A /\ C \/ B /\ C -> (A \/ B) /\ C.
assume H1 : A /\ C \/ B /\ C.
apply H1.
- assume H2 : A /\ C.
  apply H2.
  assume H3: A.
  assume H4: C.
  prove (A \/ B) /\ C.
  apply andI.
  + prove A \/ B. apply orIL. exact H3.
  + prove C. exact H4.
- assume H2 : B /\ C.
  apply H2.
  assume H3: B.
  assume H4: C.
  prove (A \/ B) /\ C.
  apply andI.
  + prove A \/ B. apply orIR. exact H3.
  + prove C. exact H4.
Qed.

(* Treasure "1AXvKaS5CM6AGfm9igYymkK6pSzXoW9J9u" *)
Theorem or_and_distrL_imp1 : A \/ B /\ C -> (A \/ B) /\ (A \/ C).
assume H1 : A \/ B /\ C.
apply H1.
- assume H2 : A.
  apply andI.
  + prove A \/ B. apply orIL. exact H2.
  + prove A \/ C. apply orIL. exact H2.
- assume H2 : B /\ C.
  apply H2.
  assume H3: B.
  assume H4: C.
  apply andI.
  + prove A \/ B. apply orIR. exact H3.
  + prove A \/ C. apply orIR. exact H4.
Qed.

(* Treasure "1KQTsCRzCFpiTeGW6gq6tgyzQShSvRM2h4" *)
Theorem or_and_distrL_imp2 : (A \/ B) /\ (A \/ C) -> A \/ B /\ C.
assume H1 : (A \/ B) /\ (A \/ C).
apply H1.
assume H2: A \/ B.
assume H3: A \/ C.
apply H2.
- assume H4: A. apply orIL. exact H4.
- assume H4: B. apply H3.
  + assume H5: A. apply orIL. exact H5.
  + assume H5: C. apply orIR. apply andI.
    * exact H4.
    * exact H5.
Qed.

(* Treasure "16eYSiDwNmyE97vdrFFXAf6WfuuWiaXGNF" *)
Theorem or_and_distrR_imp1 : A /\ B \/ C -> (A \/ C) /\ (B \/ C).
assume H1 : A /\ B \/ C.
apply H1.
- assume H2: A /\ B.
  apply H2.
  assume H3: A.
  assume H4: B.
  apply andI.
  + prove A \/ C. apply orIL. exact H3.
  + prove B \/ C. apply orIL. exact H4.
- assume H2: C.
  apply andI.
  + prove A \/ C. apply orIR. exact H2.
  + prove B \/ C. apply orIR. exact H2.
Qed.

(* Treasure "1CXUa2i9JcgRy3hucrfwy6zm5iSmGZ9jB2" *)
Theorem or_and_distrR_imp2 : (A \/ C) /\ (B \/ C) -> A /\ B \/ C.
assume H1 : (A \/ C) /\ (B \/ C).
apply H1.
assume H2 : A \/ C.
assume H3 : B \/ C.
apply H2.
- assume H4: A.
  apply H3.
  + assume H5: B. apply orIL. apply andI.
    * exact H4.
    * exact H5.
  + assume H5: C. apply orIR. exact H5.
- assume H4: C. apply orIR. exact H4.
Qed.

End BasicLogicExercises1.

Definition iff : prop->prop->prop := fun (A B:prop) => (A -> B) /\ (B -> A).

(* Unicode <-> "2194" *)
Infix <-> 805 := iff.

Theorem iffEL : forall A B:prop, (A <-> B) -> A -> B.
exact (fun A B => andEL (A -> B) (B -> A)).
Qed.

Theorem iffER : forall A B:prop, (A <-> B) -> B -> A.
exact (fun A B => andER (A -> B) (B -> A)).
Qed.

Theorem iffI : forall A B:prop, (A -> B) -> (B -> A) -> (A <-> B).
exact (fun A B => andI (A -> B) (B -> A)).
Qed.

Section BasicLogicExercises2.

Variable A:prop.

Theorem iff_refl : A <-> A.
exact (andI (A -> A) (A -> A) (fun H : A => H) (fun H : A => H)).
Qed.

(* Treasure "1AwhJ7PuAjM6UK2qFDW9CuNXTHZV6oo379" *)
Theorem iff_circuit : ~(A <-> ~A).
exact (fun H1 : A <-> ~ A => H1 False (imp_circuit A)).
Qed.

Theorem and_id_iff : A /\ A <-> A.
exact (iffI (A /\ A) A (and_id_E A) (and_id_I A)).
Qed.

(* Treasure "14sduWJd3noNmLPmhS1wp7drG8Nf6bZ9L3" *)
Theorem or_id_iff : A \/ A <-> A.
exact (iffI (A \/ A) A (or_id_E A) (or_id_I A)).
Qed.

Variable B:prop.

(* Treasure "1AZUG9vfWrpMf4RexwiRWt86v544fvfSZn" *)
Theorem iff_com_sym : (A <-> B) <-> (B <-> A).
apply iffI.
- assume H1: (A -> B) /\ (B -> A).
  apply H1.
  assume H2: A -> B.
  assume H3: B -> A.
  exact (iffI B A H3 H2).
- assume H1: (B -> A) /\ (A -> B).
  apply H1.
  assume H2: B -> A.
  assume H3: A -> B.
  exact (iffI A B H3 H2).
Qed.

Theorem and_com_iff : A /\ B <-> B /\ A.
exact (iffI (A /\ B) (B /\ A) (and_com_imp A B) (and_com_imp B A)).
Qed.

(* Treasure "155Hm6C1acaep5KgH9DPaLnWYED4kDdtxV" *)
Theorem or_com_iff : A \/ B <-> B \/ A.
exact (iffI (A \/ B) (B \/ A) (or_com_imp A B) (or_com_imp B A)).
Qed.

(* Treasure "14ACnW7NFpnPpT6tQ9FD6E1U9SCUFgsBDA" *)
Theorem not_or_and_demorgan_iff : ~(A \/ B) <-> ~A /\ ~B.
exact (iffI (~(A \/ B)) (~A /\ ~B) (not_or_and_demorgan A B) (and_not_or_demorgan A B)).
Qed.

Variable C:prop.

Theorem iff_trans : (A <-> B) -> (B <-> C) -> (A <-> C).
assume H1: A <-> B.
assume H2: B <-> C.
apply H1.
assume H3: A -> B.
assume H4: B -> A.
apply H2.
assume H5: B -> C.
assume H6: C -> B.
exact (iffI A C (imp_trans A B C H3 H5) (imp_trans C B A H6 H4)).
Qed.

Theorem and_asso_iff : A /\ (B /\ C) <-> (A /\ B) /\ C.
exact (iffI (A /\ (B /\ C)) (A /\ B /\ C) (and_asso_imp1 A B C)
  (and_asso_imp2 A B C)).
Qed.

(* Treasure "12fYUBmMZatbx75J2fEgfpaPP9YdZokUqU" *)
Theorem or_asso_iff : A \/ (B \/ C) <-> (A \/ B) \/ C.
exact (iffI (A \/ (B \/ C)) (A \/ B \/ C) (or_asso_imp1 A B C)
  (or_asso_imp2 A B C)).
Qed.

Theorem and_or_distrL_iff: A /\ (B \/ C) <-> A /\ B \/ A /\ C.
exact (iffI (A /\ (B \/ C)) (A /\ B \/ A /\ C) (and_or_distrL_imp1 A B C) (and_or_distrL_imp2 A B C)).
Qed.

Theorem and_or_distrR_iff: (A \/ B) /\ C <-> A /\ C \/ B /\ C.
exact (iffI ((A \/ B) /\ C) (A /\ C \/ B /\ C) (and_or_distrR_imp1 A B C) (and_or_distrR_imp2 A B C)).
Qed.

(* Treasure "16mRD3FU2LQC879bSbN3HGvD1PsfRnevrr" *)
Theorem or_and_distrL_iff: A \/ B /\ C <-> (A \/ B) /\ (A \/ C).
exact (iffI (A \/ B /\ C) ((A \/ B) /\ (A \/ C)) (or_and_distrL_imp1 A B C) (or_and_distrL_imp2 A B C)).
Qed.

(* Treasure "1NzF4euQqcie7VG1tUPCLoeb68EvzwhjwZ" *)
Theorem or_and_distrR_iff: A /\ B \/ C <-> (A \/ C) /\ (B \/ C).
exact (iffI (A /\ B \/ C) ((A \/ C) /\ (B \/ C)) (or_and_distrR_imp1 A B C) (or_and_distrR_imp2 A B C)).
Qed.

End BasicLogicExercises2.

Section PropN.

Variable P1 P2 P3:prop.

Theorem and3I : P1 -> P2 -> P3 -> P1 /\ P2 /\ P3.
exact (fun H1 H2 H3 => andI (P1 /\ P2) P3 (andI P1 P2 H1 H2) H3).
Qed.

Theorem and3E : P1 /\ P2 /\ P3 -> (forall p:prop, (P1 -> P2 -> P3 -> p) -> p).
exact (fun u p H => u p (fun u u3 => u p (fun u1 u2 => H u1 u2 u3))).
Qed.

Theorem or3I1 : P1 -> P1 \/ P2 \/ P3.
exact (fun u => orIL (P1 \/ P2) P3 (orIL P1 P2 u)).
Qed.

(* Treasure "19o8GRX4nURVNbtiyFpdaHQ35kQVXMuh2s" *)
Theorem or3I2 : P2 -> P1 \/ P2 \/ P3.
exact (fun u => orIL (P1 \/ P2) P3 (orIR P1 P2 u)).
Qed.

(* Treasure "15XyodERu1M2QCXSDUBvmE3MYeLDwBcpGN" *)
Theorem or3I3 : P3 -> P1 \/ P2 \/ P3.
exact (orIR (P1 \/ P2) P3).
Qed.

Theorem or3E : P1 \/ P2 \/ P3 -> (forall p:prop, (P1 -> p) -> (P2 -> p) -> (P3 -> p) -> p).
exact (fun u p H1 H2 H3 => u p (fun u => u p H1 H2) H3).
Qed.

Variable P4:prop.

(* Treasure "14jX1CmATLPKoZwMT8ofF7wkPwRgkEANqe" *)
Theorem and4I : P1 -> P2 -> P3 -> P4 -> P1 /\ P2 /\ P3 /\ P4.
exact (fun H1 H2 H3 H4 => andI (P1 /\ P2 /\ P3) P4 (and3I H1 H2 H3) H4).
Qed.

(* Treasure "1DpSQhpXeUqy6VXoNZ1jtGimb2aagJoBBD" *)
Theorem and4E : P1 /\ P2 /\ P3 /\ P4 -> (forall p:prop, (P1 -> P2 -> P3 -> P4 -> p) -> p).
exact (fun u p H => u p (fun u u4 => and3E u p (fun u1 u2 u3 => H u1 u2 u3 u4))).
Qed.

(* Treasure "16saLSHPLPY9BPgp27WgtERUDt46gkuS76" *)
Theorem or4I1 : P1 -> P1 \/ P2 \/ P3 \/ P4.
exact (fun u => orIL (P1 \/ P2 \/ P3) P4 (or3I1 u)).
Qed.

(* Treasure "15psbe2RZk1m6ZYw84YnmVTFtb8MBaLznK" *)
Theorem or4I2 : P2 -> P1 \/ P2 \/ P3 \/ P4.
exact (fun u => orIL (P1 \/ P2 \/ P3) P4 (or3I2 u)).
Qed.

(* Treasure "1Bfh2UD3fk1muJkC9AATsSXjachM9XVYkC" *)
Theorem or4I3 : P3 -> P1 \/ P2 \/ P3 \/ P4.
exact (fun u => orIL (P1 \/ P2 \/ P3) P4 (or3I3 u)).
Qed.

(* Treasure "1JbmKijassNmtg5W3MPTzv3wT6H4iinEXG" *)
Theorem or4I4 : P4 -> P1 \/ P2 \/ P3 \/ P4.
exact (orIR (P1 \/ P2 \/ P3) P4).
Qed.

(* Treasure "1959LfXEUPE2D1C3Pf1sWXh4Bndwmi8Pgr" *)
Theorem or4E : P1 \/ P2 \/ P3 \/ P4 -> (forall p:prop, (P1 -> p) -> (P2 -> p) -> (P3 -> p) -> (P4 -> p) -> p).
exact (fun u p H1 H2 H3 H4 => u p (fun u => or3E u p H1 H2 H3) H4).
Qed.

Variable P5:prop.

Theorem and5I : P1 -> P2 -> P3 -> P4 -> P5 -> P1 /\ P2 /\ P3 /\ P4 /\ P5.
exact (fun H1 H2 H3 H4 H5 => andI (P1 /\ P2 /\ P3 /\ P4) P5 (and4I H1 H2 H3 H4) H5).
Qed.

Theorem and5E : P1 /\ P2 /\ P3 /\ P4 /\ P5 -> (forall p:prop, (P1 -> P2 -> P3 -> P4 -> P5 -> p) -> p).
exact (fun u p H => u p (fun u u5 => and4E u p (fun u1 u2 u3 u4 => H u1 u2 u3 u4 u5))).
Qed.

Theorem or5I1 : P1 -> P1 \/ P2 \/ P3 \/ P4 \/ P5.
exact (fun u => orIL (P1 \/ P2 \/ P3 \/ P4) P5 (or4I1 u)).
Qed.

Theorem or5I2 : P2 -> P1 \/ P2 \/ P3 \/ P4 \/ P5.
exact (fun u => orIL (P1 \/ P2 \/ P3 \/ P4) P5 (or4I2 u)).
Qed.

Theorem or5I3 : P3 -> P1 \/ P2 \/ P3 \/ P4 \/ P5.
exact (fun u => orIL (P1 \/ P2 \/ P3 \/ P4) P5 (or4I3 u)).
Qed.

Theorem or5I4 : P4 -> P1 \/ P2 \/ P3 \/ P4 \/ P5.
exact (fun u => orIL (P1 \/ P2 \/ P3 \/ P4) P5 (or4I4 u)).
Qed.

Theorem or5I5 : P5 -> P1 \/ P2 \/ P3 \/ P4 \/ P5.
exact (orIR (P1 \/ P2 \/ P3 \/ P4) P5).
Qed.

Theorem or5E : P1 \/ P2 \/ P3 \/ P4 \/ P5 -> (forall p:prop, (P1 -> p) -> (P2 -> p) -> (P3 -> p) -> (P4 -> p) -> (P5 -> p) -> p).
exact (fun u p H1 H2 H3 H4 H5 => u p (fun u => or4E u p H1 H2 H3 H4) H5).
Qed.

End PropN.
