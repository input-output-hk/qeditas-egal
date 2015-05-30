(* Title "Classical Principles in Simple Type Theory" *)
(* Author "Chad E. Brown" *)

(* Salt "2iXkDXTjL9DEMehVE" *)

(*** Diaconescu proof of excluded middle from choice. ***)
(* Treasure "1vag5nNTUdWA19ggSdfvWhj7JgYPgf2VS" *)
Theorem classic : forall P:prop, P \/ ~ P.
let P:prop.
set p1 := fun x : prop => x \/ P.
set p2 := fun x : prop => ~x \/ P.
claim L1:p1 True.
{ prove (True \/ P). apply orIL. exact TrueI. }
claim L2:(some x:prop, p1 x) \/ P.
{ exact (EpsR prop p1 True L1). }
claim L3:p2 False.
{ prove ~False \/ P. apply orIL. assume H. exact H. }
claim L4:~(some x:prop, p2 x) \/ P.
{ exact (EpsR prop p2 False L3). }
apply L2.
- assume H1:(some x:prop, p1 x).
  apply L4.
  + assume H2:~(some x:prop, p2 x).
    prove P \/ ~ P.
    apply orIR.
    prove ~ P.
    assume H3 : P.
    claim L5:p1 = p2.
    {
      apply (pred_ext prop).
      - prove (p1 c= p2).
        let x. assume H4.
        prove (~x \/ P).
        apply orIR.
	prove P.
        exact H3.
      - prove (p2 c= p1).
        let x. assume H4.
        prove (x \/ P).
        apply orIR.
	prove P.
        exact H3.
    }
    apply H2. rewrite <- L5. exact H1.
  + assume H2:P.
    prove P \/ ~ P.
    apply orIL.
    prove P.
    exact H2.
- assume H1:P.
    prove P \/ ~ P.
    apply orIL.
    prove P.
    exact H1.
Qed.

(* Treasure "1NLzkHCUtdvfx5WtMtZY3TBGnwWkJ6YQnV" *)
Theorem NNPP : forall p:prop, ~ ~ p -> p.
let p. assume H1: ~ ~ p.
apply (classic p).
- assume H2: p. exact H2.
- assume H2: ~ p. exact (H1 H2 p).
Qed.

(* Treasure "1DDbNtVu78UDfgDrt4Ytx53XfoqLjTWzDp" *)
Theorem prop_deg : forall p:prop, p = True \/ p = False.
let p. apply (classic p).
- assume H1: p. apply orIL.
  apply prop_ext2 p.
  + assume H2. exact TrueI.
  + assume H2. exact H1.
- assume H1: ~ p. apply orIR. apply prop_ext2.
  + assume H2: p. exact (H1 H2).
  + assume H2: False. exact (H2 p).
Qed.

(* Treasure "18V7Jj32N4QpFVtGCKidn9aj3idHSHgcaw" *)
Theorem not_and_or_demorgan : forall A B:prop, ~(A /\ B) -> ~A \/ ~B.
let A B. assume u:~(A /\ B).
apply (classic A).
- assume a:A. apply (classic B).
  + assume b:B. apply u. apply andI.
    * exact a.
    * exact b.
  + assume v:~B. apply orIR. exact v.
- assume v:~A. apply orIL. exact v.
Qed.

(* Treasure "1CeWaWvM1D6Z8KWVipRRhKbq2id6m2781C" *)
Theorem not_and_or_demorgan_iff : forall A B:prop, ~(A /\ B) <-> ~A \/ ~B.
let A B.
apply iffI.
- exact (not_and_or_demorgan A B).
- exact (or_not_and_demorgan A B).
Qed.

Section DeMorganQuants.

Variable A:SType.

(* Treasure "16jdZABV34J27MTqhdDFgJPnbzsjXf2bP2" *)
Theorem not_all_ex_demorgan : forall P:A->prop, ~(forall x:A, P x) -> exists x:A, ~P x.
let P.
assume u:~forall x:A, P x.
apply NNPP.
assume v:~exists x:A, ~P x.
apply u. let x. apply NNPP.
assume w:~P x. 
exact (not_ex_all_demorgan A (fun x => ~P x) v x w).
Qed.

(* Treasure "1GRf6CeKPMo1r5ynyufVVJuNhFVwWqXFqK" *)
Theorem not_all_ex_demorgan_iff : forall P:A->prop, ~(forall x:A, P x) <-> exists x:A, ~P x.
let P.
apply iffI.
- exact (not_all_ex_demorgan P).
- exact (ex_not_all_demorgan A P).
Qed.

End DeMorganQuants.

(*** Classical Logical Identities ***)
(* Treasure "1Fn2PSwwfbp2VhsyWfvhQ5dzu6USH4C9Ta" *)
Theorem eq_neg_neg_id : eq (prop->prop) (fun x:prop => ~~x) (fun x:prop => x).
apply (pred_ext prop (fun x => ~~x) (fun x => x)).
- apply NNPP.
- apply dnegI.
Qed.

(* Treasure "14gFBnBCPg3zvgYhEwPw3kT9P91UKf2V2i" *)
Theorem eq_true : True = (~False).
exact (prop_ext2 True (~ False) (fun (_ : True) (H : False) => H) (fun _ : ~ False => TrueI)).
Qed.

(* Treasure "1CXPPqvMNiKAG2EoTAdXLwJb8U9QAPTLFz" *)
Theorem eq_and_nor : and = (fun (x y:prop) => ~(~x \/ ~y)).
apply (reln_ext prop prop and (fun (x y:prop) => ~(~x \/ ~y))).
- let x y.
  assume H1: x /\ y.
  assume H2: ~x \/ ~y.
  prove False.
  apply H1. assume H3: x. assume H4: y.
  apply H2.
  + assume H5: ~x. exact (H5 H3).
  + assume H5: ~y. exact (H5 H4).
- let x y.
  assume H1: ~(~x \/ ~y).
  prove (x /\ y).
  apply (classic x).
  + assume H2: x. apply (classic y).
    * { assume H3: y. apply andI.
        - exact H2.
        - exact H3.
      }
    * assume H3: ~y. apply H1. apply orIR. exact H3.
  + assume H2: ~x. apply H1. apply orIL. exact H2.
Qed.

(* Treasure "1EnXkQRKchAf4b64opBEXMmHHb748fhoQ6" *)
Theorem eq_or_nand : or = (fun (x y:prop) => ~(~x /\ ~y)).
apply (reln_ext prop prop).
- let x y.
  assume H1: x \/ y.
  assume H2: ~x /\ ~y.
  apply H2. assume H3 H4. exact (H1 False H3 H4).
- let x y.
  assume H1:~(~x /\ ~y).
  apply (classic x).
  + assume H2: x. apply orIL. exact H2.
  + assume H2: ~x. apply (classic y).
    * assume H3: y. apply orIR. exact H3.
    * assume H3: ~y. apply H1. exact (andI (~x) (~y) H2 H3).
Qed.

(* Treasure "1K9Uo1ibWdJpZsXfjbNMi5mgApttju86Wb" *)
Theorem eq_or_imp : or = (fun (x y:prop) => ~ x -> y).
apply (reln_ext prop prop).
- let x y.
  assume H1: x \/ y.
  assume H2: ~x.
  prove y.
  apply H1.
  + assume H3: x. exact (H2 H3 y).
  + assume H3: y. exact H3.
- let x y.
  assume H1:~x -> y.
  apply (classic x).
  + assume H2: x. apply orIL. exact H2.
  + assume H2: ~x. apply orIR. exact (H1 H2).
Qed.

(* Treasure "1JhoYo7MN5fVGYiMWr5tU7aj51so1e4n2J" *)
Theorem eq_and_imp : and = (fun (x y:prop) => ~ (x -> ~ y)).
apply (reln_ext prop prop).
- let x y.
  assume H1: x /\ y.
  assume H2: x -> ~y.
  apply H1. assume H3: x. assume H4: y.
  exact (H2 H3 H4).
- let x y.
  assume H1:~(x -> ~y).
  apply (classic x).
  + assume H2: x. apply (classic y).
    * assume H3: y. exact (andI x y H2 H3).
    * assume H3: ~y. apply H1. assume _. exact H3.
  + assume H2: ~x. apply H1. assume H3: x. apply (H2 H3).
Qed.

(* Treasure "1P3qXcabk2Daih2BCh2NMWS14H7GpCnP8f" *)
Theorem eq_imp_or : (fun (x y:prop) => (x -> y)) = (fun (x y:prop) => (~x \/ y)).
apply (reln_ext prop prop).
- let x y.
  assume H1: x -> y.
  prove ~x \/ y.
  apply (classic x).
  + assume H2: x. apply orIR. exact (H1 H2).
  + assume H2: ~x. apply orIL. exact H2.
- let x y.
  assume H1: ~x \/ y.
  apply H1.
  + assume H2: ~x. assume H3: x. apply (H2 H3).
  + assume H2: y. assume _. exact H2.
Qed.

(* Treasure "1B3WiPyR66LiRdKBS2sVmreqVTPgC2MtEQ" *)
Theorem eq_contrapositive : (fun (x y:prop) => (x -> y)) = (fun (x y:prop) => (~y -> ~x)).
apply (reln_ext prop prop).
- exact contrapositive.
- let x y.
  assume H1: ~y -> ~x.
  assume H2: x.
  apply NNPP.
  assume H3: ~y.
  exact (H1 H3 H2).
Qed.

(* Treasure "16SLEVfh8wPbrGHZrSjCysv2qB6eA117Dm" *)
Theorem eq_iff : iff = (eq prop).
apply (reln_ext prop prop).
- let x y.
  prove (x <-> y) -> x = y.
  apply prop_ext.
- let x y.
  assume H1: x = y.
  prove x <-> y.
  rewrite <- H1.
  prove x <-> x.
  prove ((x -> x) /\ (x -> x)).
  apply andI.
  + assume H2: x. exact H2.
  + assume H2: x. exact H2.
Qed.

Section EqThms.

Variable A:SType.

(* Treasure "1vxkdkjUmjQHGf721pnaJkJ24fkfCmT8r" *)
Theorem eq_sym_eq : (fun (x y:A) => x = y) = (fun (x y:A) => y = x).
exact (reln_ext A A (eq A) (fun s t : A => t = s) (eq_sym A) (fun x y => eq_sym A y x)).
Qed.

(* Treasure "1D77Ln1BH2R7jzdpWVo3zszPUSuKxdggVm" *)
Theorem eq_forall_nexists : (fun (f:A -> prop) => forall x:A, f x) = (fun (f:A -> prop) => ~exists x:A, ~f x).
apply (pred_ext (A -> prop)).
- let f:A->prop. assume u: forall x:A, f x. assume v: exists x:A, ~f x.
  apply v.
  let x:A. assume w: ~f x.
  exact w (u x).
- let f:A->prop. assume u: ~exists x:A, ~f x. let x:A.
  apply NNPP.
  assume v: ~f x.
  apply u.
  witness x.
  exact v.
Qed.

(* Treasure "19MCAHqKz5TjtepwxD8hpKS2sSwj37eFAm" *)
Theorem eq_exists_nforall : (ex A) = (fun (f:A -> prop) => ~forall x:A, ~f x).
apply (pred_ext (A -> prop)).
- let f:A->prop. assume u: exists x:A, f x. assume v: forall x:A, ~f x.
  apply u. let x. assume w: f x. exact v x w.
- let f:A->prop. assume u: ~forall x:A, ~f x.
  apply NNPP.
  assume v:~exists x:A, f x.
  apply u. let x. assume w:f x. apply v. witness x. exact w.
Qed.

(* Treasure "1NchdpXfj6TWzxkpdWvmj35m1Q3JXiQdhZ" *)
Theorem eq_leib2 : (fun (x y:A) => forall (p: A -> prop), ~ p x -> ~ p y) = (eq A).
apply (reln_ext A A).
- let x y. assume H1: forall p:A->prop, ~p x -> ~p y.
  prove x = y.
  apply NNPP.
  prove ~ (x <> y).
  apply (H1 (fun z => x <> z)).
  prove ~ ~ (x = x).
  apply dnegI. apply (eqI A).
- let x y. assume H1: x = y. let p. assume H2: ~p x.
  prove ~p y. rewrite <- H1. exact H2.
Qed.

(* Treasure "197mvMPAj6jdb8Mf9MPRf5tjhxQwJHLbYk" *)
Theorem eq_leib3 : (fun (x y:A) => forall (r: A -> A -> prop), (forall z:A, r z z) -> r x y) = (eq A).
apply (reln_ext A A).
- exact (eq_leastrefl_1 A).
- exact (eq_leastrefl_2 A).
Qed. 

(* Treasure "1Bhj1mjHo9x8kDCizDYH4ttpvnQTK8XPAG" *)
Theorem eq_leib4 : (fun (x y:A) => forall (r: A -> A -> prop),~ r x y -> ~ (forall z:A, r z z)) = (eq A).
prove ((fun x y:A => forall r:A->A->prop, ((fun p q:prop => ~q -> ~p) (forall z:A, r z z) (r x y))) = (eq A)).
rewrite <- eq_contrapositive.
exact eq_leib3.
Qed.

End EqThms.

Section Exercises.

Variable A:SType.

(* Treasure "16FPEPeuxs2rkdvbY4LhSZvJ1FS9tkirSw" *)
Example Drinker : forall d:A->prop, exists x:A, d x -> forall x:A, d x.
let d.
prove (ex A (fun x => d x -> forall x:A, d x)).
rewrite (eq_exists_nforall A).
prove ~forall x:A, ~(d x -> forall x:A, d x).
assume H1: forall x:A, ~(d x -> forall x:A, d x).
apply (H1 (some x:A, True)).
prove d (some x:A, True) -> forall x:A, d x.
assume _.
prove ((fun (f:A -> prop) => forall x:A, f x) d).
rewrite (eq_forall_nexists A).
prove ~exists x:A, ~d x.
assume H2: exists x:A, ~d x.
apply H2.
let x.
assume H3: ~d x.
apply (H1 x).
prove d x -> forall x:A, d x.
assume H4: d x.
prove False.
exact (H3 H4).
Qed.

End Exercises.
