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
let p.
assume H1: C p.
let Q.
assume H2: forall p:A->prop, Q p -> Q (p ').
assume H3: forall D:(A->prop)->prop, D c= Q -> Q (bigintersect A D).
prove Q (p ').
apply H2.
prove Q p.
exact (H1 Q H2 H3).
Qed.

(* Treasure "1LMwPj3CRLzEdL6e2Zvv7upYcZxmPr7hot" *)
Lemma C_int : forall D:(A->prop)->prop, D c= C -> C (bigintersect A D).
let D.
assume H1: D c= C.
let Q.
assume H2: forall p:A->prop, Q p -> Q (p ').
assume H3: forall D:(A->prop)->prop, D c= Q -> Q (bigintersect A D).
prove Q (bigintersect A D).
apply H3.
prove D c= Q.
let p.
assume H4:D p.
prove Q p.
exact (H1 p H4 Q H2 H3).
Qed.

(* Treasure "12oevw7H6jbFaHij2Rebm67XnqFD2ZZDGC" *)
Lemma C_ind : forall Q:(A->prop)->prop,
       (forall p:A->prop, C p -> Q p -> Q (p '))
    -> (forall D:(A->prop)->prop, D c= C -> D c= Q -> Q (bigintersect A D))
    -> C c= Q.
let Q.
assume H1: forall p:A->prop, C p -> Q p -> Q (p ').
assume H2: forall D:(A->prop)->prop, D c= C -> D c= Q -> Q (bigintersect A D).
let p.
assume H3: C p.
claim L1:C p /\ Q p.
{
  apply H3.
  - prove forall q:A->prop, C q /\ Q q -> C (q ') /\ Q (q ').
    let q. assume H4: C q /\ Q q. apply H4. assume H5: C q. assume H6: Q q. apply andI.
    + prove (C (q ')). apply (C_prime q). exact H5.
    + prove (Q (q ')). exact (H1 q H5 H6).
  - prove forall D:(A->prop)->prop, (forall q:A->prop, D q -> C q /\ Q q) -> C (bigintersect A D) /\ Q (bigintersect A D).
    let D. assume H4: (forall q:A->prop, D q -> C q /\ Q q). apply andI.
    + prove (C (bigintersect A D)). apply (C_int D). let q. assume H5. apply (H4 q H5). assume H6 _. exact H6.
    + prove (Q (bigintersect A D)). apply (H2 D).
      * prove (D c= C). let q. assume H5. apply (H4 q H5). assume H6 _. exact H6.
      * prove (D c= Q). let q. assume H5. apply (H4 q H5). assume _ H6. exact H6.
}
apply L1.
assume _.
assume H4:Q p.
exact H4.
Qed.

Section Cp.

Variable p:A->prop.

(* Treasure "1EgHt3ZeATPNQgWGfJ6E2fJS7cWgsbNNvx" *)
Lemma C_lin : C p -> forall q:A->prop, C q -> q c= p \/ p c= q.
assume Hp:C p.
prove ((fun p:A->prop => forall q:A->prop, C q -> q c= p \/ p c= q) p).
apply (Hp (fun p => forall q:A->prop, C q -> q c= p \/ p c= q)).
- let p. 
  assume IHp: forall q:A->prop, C q -> q c= p \/ p c= q.
  prove forall q:A->prop, C q -> q c= p ' \/ p ' c= q.
  prove forall q:A->prop, C q -> (fun q:A->prop => q c= p ' \/ p ' c= q) q.
  apply (C_ind (fun q => q c= p ' \/ p ' c= q)).
  + let q.
    assume Hq:C q.
    assume IHq: q c= p ' \/ p ' c= q.
    prove q ' c= p ' \/ p ' c= q '.
    apply IHq.
    * assume IHq1: q c= p '. apply orIL. prove q ' c= p '.
      let x.
      assume H1: q x /\ x <> some x:A, q x.
      prove p ' x. apply IHq1.
      prove q x.
      exact (andEL (q x) (x <> some x:A, q x) H1).
    * { assume IHq2: p ' c= q.
        apply (IHp (q ') (C_prime q Hq)).
	- assume IHp1: q ' c= p.
          apply (classic (p ' (some x:A, q x))).
          + assume H2: p ' (some x:A, q x).
            apply (classic (q ' (some x:A, p x))).
            * { assume H3: q ' (some x:A, p x).
                claim L1: (some x:A, p x) <> (some x:A, q x).
                {
                   exact (andER (q (some x:A, p x)) ((some x:A, p x) <> (some x:A, q x)) H3).
		}
                claim L2: p <> q.
                {
                   assume H4: p = q. apply L1. rewrite <- H4. apply (eqI A).
                }
                apply L2.
                prove p = q.
		apply (pred_ext A).
		- prove p c= q.
                  let x. assume H4: p x.
                  prove q x.
		  apply (classic (x = some x:A, p x)).
		  + assume H5: x = some x:A, p x. rewrite H5. exact (andEL (q (some x:A, p x)) ((some x:A, p x) <> (some x:A, q x)) H3).
		  + assume H5: x <> some x:A, p x. apply IHq2. exact (andI (p x) (x <> (some x:A, p x)) H4 H5).
		- prove q c= p.
                  let x. assume H4: q x.
                  prove p x.
		  apply (classic (x = some x:A, q x)).
		  + assume H5: x = some x:A, q x. rewrite H5. exact (andEL (p (some x:A, q x)) ((some x:A, q x) <> (some x:A, p x)) H2).
		  + assume H5: x <> some x:A, q x. apply IHp1. exact (andI (q x) (x <> (some x:A, q x)) H4 H5).
              }
            * { assume H3: ~ q ' (some x:A, p x).
                apply orIL. prove q ' c= p '.
                let x.
   	        assume H4: q ' x.
	        prove p x /\ x <> some x:A, p x.
                apply andI.
	        - apply IHp1. exact H4.
	        - assume H5: x = some x:A, p x. apply H3. rewrite <- H5. exact H4.
              }
          + assume H2: ~ p ' (some x:A, q x).
            apply orIR. prove p ' c= q '.
            let x.
	    assume H3: p ' x.
	    prove q x /\ x <> some x:A, q x.
            apply andI.
	    * apply IHq2. exact H3.
	    * assume H4: x = some x:A, q x. apply H2. rewrite <- H4. exact H3.
	- assume IHp2: p c= q '.
          apply orIR. prove p ' c= q '.
          let x.
          assume H2: p x /\ x <> some x:A, p x.
          prove q ' x. apply IHp2. exact (andEL (p x) (x <> some x:A, p x) H2).
      }
  + let E.
    assume HE: forall q:A->prop, E q -> C q.
    assume IHE: forall q:A->prop, E q -> q c= p ' \/ p ' c= q.
    prove bigintersect A E c= p ' \/ p ' c= bigintersect A E.
    apply (classic (exists q:A->prop, E q /\ q c= p ')).
    * assume H1: exists q:A->prop, E q /\ q c= p '.
      apply orIL.
      prove bigintersect A E c= p '.
      apply H1. let q. assume H2: E q /\ q c= p '. apply H2.
      assume H3: E q.
      assume H4: q c= p '.
      let x. assume H5: bigintersect A E x. prove p ' x. apply H4. prove q x. exact (H5 q H3).
    * { assume H1: ~exists q:A->prop, E q /\ q c= p '.
        apply orIR.
        prove p ' c= bigintersect A E.
        let x. assume H2: p ' x. let q. assume H3: E q. prove q x.
        apply (IHE q H3).
        - assume IHE1: q c= p '. apply H1. witness q. exact (andI (E q) (q c= p ') H3 IHE1).
        - assume IHE2: p ' c= q. exact (IHE2 x H2).
      }
- let D.
  assume IHD: forall p:A->prop, D p -> forall q:A->prop, C q -> q c= p \/ p c= q.
  prove forall q:A->prop, C q -> q c= bigintersect A D \/ bigintersect A D c= q.
  let q. assume Hq:C q.
  apply (classic (exists p:A->prop, D p /\ p c= q)).
  + assume H1: exists p:A->prop, D p /\ p c= q.
    apply orIR.
    prove bigintersect A D c= q.
    apply H1. let p. assume H2: D p /\ p c= q. apply H2.
    assume H3: D p.
    assume H4: p c= q.
    let x. assume H5: bigintersect A D x. prove q x. apply H4. prove p x. exact (H5 p H3).
  + assume H1: ~exists p:A->prop, D p /\ p c= q.
    apply orIL.
    prove q c= bigintersect A D.
    let x. assume H2: q x. let p. assume H3: D p. prove p x.
    apply (IHD p H3 q Hq).
    * assume IHD1: q c= p. exact (IHD1 x H2).
    * assume IHD2: p c= q. apply H1. witness p. exact (andI (D p) (p c= q) H3 IHD2).
Qed.

End Cp.

(* Treasure "1B932Rn2Ltpv4ddCUFnKWopKqxQEySL9dC" *)
Lemma C_Eps : forall p:A->prop, C p -> forall q:A->prop, C q -> q (some x:A, p x) -> p c= q.
let p. assume Hp:C p. let q. assume Hq: C q. assume H1: q (some x:A, p x).
apply (C_lin (p ') (C_prime p Hp) q Hq).
- assume H2: q c= p '.
  claim L1: p ' (some x:A, p x).
  {
    apply H2. exact H1.
  }
  claim L2:((some x:A, p x) <> (some x:A, p x)).
  {
    exact (andER (p (some x:A, p x)) ((some x:A, p x) <> (some x:A, p x)) L1).
  }
  apply L2. apply (eqI A).
- assume H2: p ' c= q.
  prove p c= q.
  let x. assume H3: p x.
  prove q x.
  apply (classic (x = some x:A, p x)).
  + assume H4: x = some x:A, p x. rewrite H4. exact H1.
  + assume H4: x <> some x:A, p x. apply H2. prove (p x /\ x <> some x:A, p x). apply andI.
    * exact H3.
    * exact H4.
Qed.

Let clos := fun (p:A -> prop) => bigintersect A (fun q => C q /\ p c= q).

Section closp.

Variable p:A->prop.

(* Treasure "15yLhoRjQhWBv7i6Gfuri2KxFhcwVT1P3h" *)
Lemma C_clos : C (clos p).
prove (C (bigintersect A (fun q:A->prop => C q /\ p c= q))).
apply (C_int (fun q:A->prop => C q /\ p c= q)).
prove (fun q:A->prop => C q /\ p c= q) c= C.
let q. assume H1: C q /\ p c= q. exact (andEL (C q) (p c= q) H1).
Qed.

(* Treasure "1GSqVJChbe6BiAdwfGuvsjDuAujYvcmM1" *)
Lemma clos_subq : forall x:A, p x -> clos p x.
let x. assume H1: p x. let q. assume H2: C q /\ p c= q. prove q x.
exact (andER (C q) (p c= q) H2 x H1).
Qed.

(* Treasure "1FugT7s8ox3CKL2pPKeq1YBFzGUWm6CJYE" *)
Lemma clos_Eps : (exists x:A, p x) -> p (some x:A, clos p x).
assume H1. apply NNPP. assume H2: ~p (some x:A, clos p x).
set q := (clos p) '.
claim L1: ~ q (some x:A, clos p x).
{
  assume H3: clos p (some x:A, clos p x) /\ (some x:A, clos p x) <> (some x:A, clos p x).
  apply (andER (clos p (some x:A, clos p x)) ((some x:A, clos p x) <> (some x:A, clos p x)) H3).
  apply (eqI A).
}
claim L2: C q.
{
  prove C ((clos p) ').
  apply (C_prime (clos p)).
  prove C (clos p).
  apply C_clos.
}
claim L3: p c= q.
{
  let x. assume H3: p x.
  prove (clos p x /\ x <> some x:A, clos p x). apply andI.
  - exact (clos_subq x H3).
  - assume H4: x = some x:A, clos p x.
    apply H2.
    prove p (some x:A, clos p x).
    rewrite <- H4. exact H3.
}
claim L4: clos p c= q.
{
  let x. assume H3: clos p x.
  exact (H3 q (andI (C q) (p c= q) L2 L3)).
}
claim L5: exists x:A, clos p x.
{
  apply H1.
  let x. assume H3: p x.
  prove exists x:A, clos p x.
  witness x.
  prove clos p x.
  apply (clos_subq x).
  prove p x.
  exact H3.
}
claim L6: clos p (some x:A, clos p x).
{
  exact (EpsR2 A (clos p) L5).
}
exact (L1 (L4 (some x:A, clos p x) L6)).
Qed.

End closp.

Definition ZermeloWO := fun (a:A) => clos (fun x => x = a).

Let R := ZermeloWO.

Infix <= 490 := R.

(* Treasure "15dFrugBpoAMTCYsrABSQSsTrPsZPN1wy5" *)
Lemma CR : forall a:A, C (R a).
let a. exact (C_clos (fun x => x = a)).
Qed.

(* Treasure "1JBUBhAhsXPQhuV6bjSSZ1NLE5QHEoLrs2" *)
Lemma R_ref : reflexive A R.
let a.
prove (a <= a).
prove clos (fun x => x = a) a.
apply (clos_subq (fun x => x = a) a).
prove a = a.
exact (eqI A a).
Qed.

(* Treasure "1GNkZySXKSjdukVqP6Q1pA9Upu4tvWmbzL" *)
Lemma R_Eps : forall a:A, (some x:A, R a x) = a.
let a.
claim L1: exists x:A, x = a.
{
  witness a.
  exact (eqI A a).
}
exact (clos_Eps (fun x => x = a) L1).
Qed.

(* Treasure "1DewJze7HwmYFsFnDCm2VTysb2hYCEQ6ND" *)
Lemma R_lin : linear A R.
let a b.
prove a <= b \/ b <= a.
apply (C_lin (R a) (CR a) (R b) (CR b)).
- assume H1: R b c= R a.
  apply orIL.
  prove R a b.
  apply (H1 b).
  exact (R_ref b).
- assume H1: R a c= R b.
  apply orIR.
  prove R b a.
  apply (H1 a).
  exact (R_ref a).
Qed.

(* Treasure "1LhxeTrnx8tK6GjxFQF2Ev5kVFZUwCwHST" *)
Lemma R_tra : transitive A R.
let a b c. assume H1: a <= b. assume H2: b <= c.
prove clos (fun x => x = a) c.
let p. assume H3: C p /\ (fun x:A => x = a) c= p.
prove p c.
claim L1: (fun x:A => x = b) c= p.
{
  let x. assume H4: x = b.
  prove p x.
  rewrite H4.
  prove p b.
  exact (H1 p H3).
}
claim L2: C p /\ (fun x:A => x = b) c= p.
{
  apply andI.
  - exact (andEL (C p) ((fun x:A => x = a) c= p) H3).
  - exact L1.
}
exact (H2 p L2).
Qed.

(* Treasure "18BWmiMEyvqaPU3QfPPf22KR4R99FoBL2U" *)
Lemma R_antisym : antisymmetric A R.
let a b. assume H1: a <= b. assume H2: b <= a.
prove a = b.
rewrite <- (R_Eps a).
rewrite <- (R_Eps b).
prove (some x:A, R a x) = (some x:A, R b x).
claim L1: R a = R b.
{
  apply (pred_ext A).
  - prove R a c= R b.
    let c. assume H3:R a c. prove R b c. exact (R_tra b a c H2 H3).
  - prove R b c= R a.
    let c. assume H3:R b c. prove R a c. exact (R_tra a b c H1 H3).
}
rewrite L1.
apply (eqI A).
Qed.

(* Treasure "19gxP34ZK1A7CAN9q8jVz2ihwZeVbs1BGm" *)
Lemma R_partialorder : partialorder A R.
prove reflexive A R /\ antisymmetric A R /\ transitive A R.
apply and3I.
- exact R_ref.
- exact R_antisym.
- exact R_tra.
Qed.

(* Treasure "1N2Btig1vdAC3pYxGoAsCauZWKZxCKLtpC" *)
Lemma R_totalorder : totalorder A R.
prove partialorder A R /\ linear A R.
apply andI.
- exact R_partialorder.
- exact R_lin.
Qed.

(* Treasure "1BNcwaWqnEGUz4WtZqhexuK3SN79T1Ey2m" *)
Lemma R_wo : forall p:A->prop, (exists x:A, p x) -> exists x:A, p x /\ forall y:A, p y -> x <= y.
let p. assume H1: exists x:A, p x.
set z := some x:A, clos p x.
witness z. apply andI.
- prove p z.
  exact (clos_Eps p H1).
- prove forall y:A, p y -> z <= y.
  let y. assume H2: p y.
  prove (clos (fun x:A => x = z) y).
  let q. assume H3: C q /\ (fun x:A => x = z) c= q.
  apply H3. assume H4: C q. assume H5: (fun x:A => x = z) c= q.
  claim L1: q z.
  {
    exact (H5 z (eqI A z)).
  }
  claim L2: clos p c= q.
  {
    exact (C_Eps (clos p) (C_clos p) q H4 L1).
  }
  prove q y.
  apply L2.
  prove clos p y.
  exact (clos_subq p y H2).
Qed.

Definition ZermeloWOstrict := fun (a b:A) => R a b /\ a <> b.
Let lt := ZermeloWOstrict.

Infix < 490 := lt.

(* Treasure "115K8EwLkPuWnddfnVKQcoZTw5Fu5F7dF9" *)
Lemma lt_trich : trichotomous_or A lt.
let a b.
prove (a < b \/ a = b \/ b < a).
apply (classic (a = b)).
- assume H1: a = b. apply or3I2. exact H1.
- assume H1: a <> b.
  apply (R_lin a b).
  + assume H2: a <= b. apply or3I1. prove a <= b /\ a <> b. apply andI.
    * exact H2.
    * exact H1.
  + assume H2: b <= a. apply or3I3. prove b <= a /\ b <> a. apply andI.
    * exact H2.
    * apply (neq_sym A). exact H1.
Qed.

(* Treasure "1FtbkUfep6Pfis3abQ6RBQykaXu3ggCjYs" *)
Lemma lt_stricttotalorder : stricttotalorder A lt.
prove strictpartialorder A lt /\ trichotomous_or A lt.
apply andI.
- prove strictpartialorder A (fun a b => R a b /\ a <> b).
  apply (partialorder_strictpartialorder A R).
  prove partialorder A R.
  exact R_partialorder.
- exact lt_trich.
Qed.

(* Treasure "1317wb94d46bWDNfQjHqHMBfESxkuKZ9E8" *)
Lemma lt_wo : forall (p:A -> prop), (exists x:A, p x) -> exists x:A, p x /\ forall y:A, p y /\ y <> x -> x < y.
let p. assume H1.
apply (R_wo p H1).
let x. assume H1: p x /\ forall y:A, p y -> x <= y.
apply H1. assume H2 H3.
witness x. apply andI.
- exact H2.
- let y. assume H4. apply H4. assume H5 H6.
  prove x <= y /\ x <> y.
  apply andI.
  + exact (H3 y H5).
  + apply (neq_sym A). exact H6.
Qed.

(* Treasure "18iLRCWDkQuwWcHjz3pVw3YXYQi6dpmsdQ" *)
Theorem Zermelo_WO : exists r : A -> A -> prop,
    totalorder A r
 /\ (forall p:A->prop, (exists x:A, p x) -> exists x:A, p x /\ forall y:A, p y -> r x y).
witness R.
apply andI.
- exact R_totalorder.
- exact R_wo.
Qed.

(* Treasure "1NRqj6n7w7wcFRhcJZQ51XmqKiXxcBdTp2" *)
Theorem Zermelo_WO_strict : exists r : A -> A -> prop,
    stricttotalorder A r
 /\ (forall p:A->prop, (exists x:A, p x) -> exists x:A, p x /\ forall y:A, p y /\ y <> x -> r x y).
witness lt. apply andI.
- exact lt_stricttotalorder.
- exact lt_wo.
Qed.

End Zermelo1908.
