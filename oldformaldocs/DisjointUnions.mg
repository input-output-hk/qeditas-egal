(* Title "Disjoint Unions" *)
(* Author "Chad E. Brown" *)

(* Salt "3HmtMxzQo7ZHzs1du" *)

(*** Injection of set into itself that will correspond to x |-> (1,x) after pairing is defined. ***)
Definition Inj1 : set -> set := In_rec (fun X f => {0} :\/: {f x|x :e X}).

(* Treasure "1HLkfW5thtfXVwKkkhtRJDitG45kK3MQD8" *)
Theorem Inj1_eq : forall X:set, Inj1 X = {0} :\/: {Inj1 x|x :e X}.
claim L1: forall X:set, forall g h:set->set, (forall x :e X, g x = h x)
                         -> {0} :\/: {g x|x :e X} = {0} :\/: {h x|x :e X}.
{
  let X g h.
   assume H: forall x :e X, g x = h x.
   claim L1a: {g x|x :e X} = {h x|x :e X}.
   {
     exact (Repl_restr X g h H).
   }
   prove {0} :\/: {g x|x :e X} = {0} :\/: {h x|x :e X}.
   rewrite L1a.
   apply (eqI set).
}
exact (In_rec_eq (fun X f => {0} :\/: {f x|x :e X}) L1).
Qed.

(* Treasure "1A6S9UY8oeS4PkTuB1r31DZQP8HDUhRKcr" *)
Theorem Inj1I1 : forall X:set, 0 :e Inj1 X.
let X.
rewrite (Inj1_eq X).
prove 0 :e {0} :\/: {Inj1 x|x :e X}.
apply binunionI1.
apply SingI.
Qed.

(* Treasure "1CudP163WnT32jWcWQb9aMbRFxmABDmyFz" *)
Theorem Inj1I2 : forall X x:set, x :e X -> Inj1 x :e Inj1 X.
let X x.
assume H: x :e X.
rewrite (Inj1_eq X).
prove Inj1 x :e {0} :\/: {Inj1 x|x :e X}.
apply binunionI2.
exact (ReplI X Inj1 x H).
Qed.

(* Treasure "18pmbnh5i6HZzCDfXTxGjAd25ULSqzPHii" *)
Theorem Inj1E : forall X y:set, y :e Inj1 X -> y = 0 \/ exists x :e X, y = Inj1 x.
let X y.
rewrite (Inj1_eq X).
assume H1: y :e {0} :\/: {Inj1 x|x :e X}.
prove y = 0 \/ exists x :e X, y = Inj1 x.
apply (binunionE {0} {Inj1 x|x :e X} y H1).
- assume H2: y :e {0}.
  apply orIL.
  exact (SingE 0 y H2).
- assume H2: y :e {Inj1 x|x :e X}.
  apply orIR.
  prove exists x :e X, y = Inj1 x.
  exact (ReplE X Inj1 y H2).
Qed.

(* Treasure "1P23aisnDCUcqHfQH5rAm1bwvW2GtvL6sU" *)
Theorem Inj1NE1 : forall x:set, Inj1 x <> 0.
let x.
assume H1: Inj1 x = 0.
apply (EmptyE 0).
prove 0 :e 0.
rewrite <- H1 at 2.
prove 0 :e Inj1 x.
exact (Inj1I1 x).
Qed.

(* Treasure "1HrtXSZEfTTbmZ4fzTYJpmA62ibLdF1VwQ" *)
Theorem Inj1NE2 : forall x:set, Inj1 x /:e {0}.
let x.
assume H1: Inj1 x :e {0}.
exact (Inj1NE1 x (SingE 0 (Inj1 x) H1)).
Qed.

(*** Injection of set into itself that will correspond to x |-> (0,x) after pairing is defined. ***)
Definition Inj0 : set -> set := fun X => {Inj1 x|x :e X}.

(* Treasure "13TQfEqNYkvdRsXGeKirZCrJVbYapZPqxS" *)
Theorem Inj0I : forall X x:set, x :e X -> Inj1 x :e Inj0 X.
exact (fun X x H => ReplI X Inj1 x H).
Qed.

(* Treasure "1KFmGQymRZPGx17jCQYagL5JNU29hMdRTV" *)
Theorem Inj0E : forall X y:set, y :e Inj0 X -> exists x:set, x :e X /\ y = Inj1 x.
exact (fun X y H => ReplE X Inj1 y H).
Qed.

(*** Unj : Left inverse of Inj1 and Inj0 ***)
Definition Unj : set -> set := In_rec (fun X f => {f x|x :e X :\: {0}}).

(* Treasure "17s8QQsa5jdfpScDvLv15RabX4PmUUGf52" *)
Theorem Unj_eq : forall X:set, Unj X = {Unj x|x :e X :\: {0}}.
claim L1: forall X:set, forall g h:set->set, (forall x :e X, g x = h x) -> {g x|x :e X :\: {0}} = {h x|x :e X :\: {0}}.
{
  let X g h.
  assume H1: forall x :e X, g x = h x.
  prove {g x|x :e X :\: {0}} = {h x|x :e X :\: {0}}.
  apply (Repl_restr (X :\: {0}) g h).
  let x.
  assume H2: x :e X :\: {0}.
  prove g x = h x.
  apply H1.
  prove x :e X.
  exact (setminusE1 X {0} x H2).
}
exact (In_rec_eq (fun X f => {f x|x :e X :\: {0}}) L1).
Qed.

(* Treasure "15EwYeGp7qwrzAifPVLy3HpzWJi5Gzp6Sq" *)
Theorem Unj_Inj1_eq : forall X:set, Unj (Inj1 X) = X.
apply In_ind.
let X.
assume IH: forall x :e X, Unj (Inj1 x) = x.
prove Unj (Inj1 X) = X.
rewrite Unj_eq.
prove {Unj x|x :e Inj1 X :\: {0}} = X.
apply set_ext.
- prove {Unj x|x :e Inj1 X :\: {0}} c= X.
  let x.
  assume H1: x :e {Unj x|x :e Inj1 X :\: {0}}.
  prove x :e X.
  apply (ReplE2 (Inj1 X :\: {0}) Unj x H1).
  let y.
  assume H2: y :e Inj1 X :\: {0}.
  assume H3: x = Unj y.
  rewrite H3.
  prove Unj y :e X.
  apply (setminusE (Inj1 X) {0} y H2).
  assume H4: y :e Inj1 X.
  assume H5: y /:e {0}.
  apply (Inj1E X y H4).
  + assume H6: y = 0.
    prove False.
    apply H5.
    rewrite H6.
    prove 0 :e {0}.
    apply SingI.
  + assume H6: exists x :e X, y = Inj1 x.
    apply (exandE set (fun x => x :e X) (fun x => y = Inj1 x) H6).
    let z.
    assume H7: z :e X.
    assume H8: y = Inj1 z.
    rewrite H8.
    prove Unj (Inj1 z) :e X.
    rewrite (IH z H7).
    prove z :e X.
    exact H7.
- prove X c= {Unj x|x :e Inj1 X :\: {0}}.
  let x.
  assume H1: x :e X.
  prove x :e {Unj x|x :e Inj1 X :\: {0}}.
  rewrite <- (IH x H1).
  prove Unj (Inj1 x) :e {Unj x|x :e Inj1 X :\: {0}}.
  apply (ReplI (Inj1 X :\: {0}) Unj).
  prove Inj1 x :e Inj1 X :\: {0}.
  apply setminusI.
  + exact (Inj1I2 X x H1).
  + prove Inj1 x /:e {0}.
    exact (Inj1NE2 x).
Qed.

(* Treasure "12M6AD6kpAeArzATizcW9ihrdSAkF3bU33" *)
Theorem Inj1_inj : forall X Y:set, Inj1 X = Inj1 Y -> X = Y.
let X Y.
assume H1: Inj1 X = Inj1 Y.
prove X = Y.
rewrite <- (Unj_Inj1_eq X).
rewrite <- (Unj_Inj1_eq Y).
rewrite H1.
apply (eqI set).
Qed.

(* Treasure "1K2iDYBWjXJWfHqCmzucJGdVmea8HKqpg7" *)
Theorem Unj_Inj0_eq : forall X:set, Unj (Inj0 X) = X.
let X.
rewrite (Unj_eq (Inj0 X)).
prove {Unj x|x :e Inj0 X :\: {0}} = X.
apply set_ext.
- prove {Unj x|x :e Inj0 X :\: {0}} c= X.
  let x.
  assume H1: x :e {Unj x|x :e Inj0 X :\: {0}}.
  prove x :e X.
  apply (ReplE2 (Inj0 X :\: {0}) Unj x H1).
  let y.
  assume H2: y :e Inj0 X :\: {0}.
  assume H3: x = Unj y.
  apply (setminusE (Inj0 X) {0} y H2).
  assume H4: y :e {Inj1 x|x :e X}.
  assume H5: y /:e {0}.
  apply (ReplE2 X Inj1 y H4).
  let z.
  assume H6: z :e X.
  assume H7: y = Inj1 z.
  claim L1: x = z.
  {
    rewrite H3.
    prove Unj y = z.
    rewrite H7.
    prove Unj (Inj1 z) = z.
    exact (Unj_Inj1_eq z).
  }
  prove x :e X.
  rewrite L1.
  prove z :e X.
  exact H6.
- prove X c= {Unj x|x :e Inj0 X :\: {0}}.
  let x.
  assume H1: x :e X.
  prove x :e {Unj x|x :e Inj0 X :\: {0}}.
  rewrite <- (Unj_Inj1_eq x).
  prove Unj (Inj1 x) :e {Unj x|x :e Inj0 X :\: {0}}.
  apply (ReplI (Inj0 X :\: {0}) Unj).
  prove Inj1 x :e Inj0 X :\: {0}.
  apply setminusI.
  + prove Inj1 x :e {Inj1 x|x :e X}.
    apply ReplI.
    exact H1.
  + prove Inj1 x /:e {0}.
    exact (Inj1NE2 x).
Qed.

(* Treasure "12r21GbQHLRo2FCg4FDqoa4h9BaUSEKvhv" *)
Theorem Inj0_inj : forall X Y:set, Inj0 X = Inj0 Y -> X = Y.
let X Y.
assume H1: Inj0 X = Inj0 Y.
prove X = Y.
rewrite <- (Unj_Inj0_eq X).
rewrite <- (Unj_Inj0_eq Y).
rewrite H1.
apply (eqI set).
Qed.

(* Treasure "1D2UGPdmGbFUPiXmWEwcjkZzykhH9afAWe" *)
Theorem Inj0_0 : Inj0 0 = 0.
exact (Repl_Empty Inj1).
Qed.

(* Treasure "19ZzdtFoChgrwEHngpJTSCdhBvDZnJtjDE" *)
Theorem Inj0_Inj1_neq : forall X Y:set, Inj0 X <> Inj1 Y.
let X Y.
assume H1 : Inj0 X = Inj1 Y.
claim L1: 0 :e Inj1 Y.
{ exact (Inj1I1 Y). }
claim L2: 0 :e Inj0 X.
{ rewrite H1. exact L1. }
apply (Inj0E X 0 L2).
let x.
assume H2: x :e X /\ 0 = Inj1 x.
exact (Inj1NE1 x (eq_sym set 0 (Inj1 x) (andER (x :e X) (0 = Inj1 x) H2))).
Qed.

(*** setsum ***)
Definition setsum : set -> set -> set := fun X Y => {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.

(* Unicode :+: "002b" *)
Infix :+: 450 left := setsum.

(* Treasure "1Lq3DVZuTM8xJy6b7zWkkSBZK9EG6bTBaC" *)
Theorem Inj0_setsum : forall X Y x:set, x :e X -> Inj0 x :e X :+: Y.
let X Y x.
assume H: x :e X.
prove Inj0 x :e {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.
apply binunionI1.
prove Inj0 x :e {Inj0 x|x :e X}.
apply ReplI.
exact H.
Qed.

(* Treasure "18ehfuaMKoafSybBroShCrHDMmpf5iqumG" *)
Theorem Inj1_setsum : forall X Y y:set, y :e Y -> Inj1 y :e X :+: Y.
let X Y y.
assume H: y :e Y.
prove Inj1 y :e {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.
apply binunionI2.
prove Inj1 y :e {Inj1 y|y :e Y}.
apply ReplI.
exact H.
Qed.

(* Treasure "15SMGdRG9ei4J4cZSXCiQm3sRQQ98MrLcd" *)
Theorem setsum_Inj_inv : forall X Y z:set, z :e X :+: Y -> (exists x :e X, z = Inj0 x) \/ (exists y :e Y, z = Inj1 y).
let X Y z.
assume H1 : z :e {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.
apply (binunionE {Inj0 x|x :e X} {Inj1 y|y :e Y} z H1).
- assume H2: z :e {Inj0 x|x :e X}.
  apply orIL.
  exact (ReplE X Inj0 z H2).
- assume H2: z :e {Inj1 y|y :e Y}.
  apply orIR.
  exact (ReplE Y Inj1 z H2).
Qed.

(* Treasure "16jSPndFXwe29nb2hkzSiEUv5G5u1QUXfH" *)
Theorem Inj0_setsum_0L : forall X:set, 0 :+: X = Inj0 X.
let X. apply set_ext.
- let z.
  assume H1: z :e 0 :+: X.
  prove z :e Inj0 X.
  apply (setsum_Inj_inv 0 X z H1).
  + assume H2: exists x :e 0, z = Inj0 x.
    apply (exandE set (fun x => x :e 0) (fun x => z = Inj0 x) H2).
    let x.
    assume H3: x :e 0.
    prove False.
    exact (EmptyE x H3).
  + assume H2: exists x :e X, z = Inj1 x.
    apply (exandE set (fun x => x :e X) (fun x => z = Inj1 x) H2).
    let x.
    assume H3: x :e X.
    assume H4: z = Inj1 x.
    rewrite H4.
    prove Inj1 x :e Inj0 X.
    exact (Inj0I X x H3).
- let z.
  assume H1: z :e Inj0 X.
  prove z :e 0 :+: X.
  apply (exandE set (fun x => x :e X) (fun x => z = Inj1 x) (Inj0E X z H1)).
  let x.
  assume H2: x :e X.
  assume H3: z = Inj1 x.
  rewrite H3.
  prove Inj1 x :e 0 :+: X.
  apply Inj1_setsum.
  exact H2.
Qed.

(* Treasure "1KTsqNADcSsqdK1SWPbisBmKzo4VwSq4uH" *)
Theorem Inj1_setsum_1L : forall X:set, 1 :+: X = Inj1 X.
let X. apply set_ext.
- let z.
  assume H1: z :e 1 :+: X.
  prove z :e Inj1 X.
  apply (setsum_Inj_inv 1 X z H1).
  + assume H2: exists x :e 1, z = Inj0 x.
    apply (exandE set (fun x => x :e 1) (fun x => z = Inj0 x) H2).
    let x.
    assume H3: x :e 1.
    assume H4: z = Inj0 x.
    rewrite H4.
    prove Inj0 x :e Inj1 X.
    claim L1: x = 0.
    { exact (SingE 0 x (Subq_1_Sing0 x H3)). }
    rewrite L1.
    prove Inj0 0 :e Inj1 X.
    rewrite Inj0_0.
    prove 0 :e Inj1 X.
    exact (Inj1I1 X).
  + assume H2: exists x :e X, z = Inj1 x.
    apply (exandE set (fun x => x :e X) (fun x => z = Inj1 x) H2).
    let x.
    assume H3: x :e X.
    assume H4: z = Inj1 x.
    rewrite H4.
    prove Inj1 x :e Inj1 X.
    exact (Inj1I2 X x H3).
- let z.
  assume H1: z :e Inj1 X.
  prove z :e 1 :+: X.
  apply (Inj1E X z H1).
  + assume H2: z = 0.
    rewrite H2.
    prove 0 :e 1 :+: X.
    rewrite <- Inj0_0 at 1. (*** This is a little tricky. Recall that 1 is notation for ordsucc 0, so without "at 1" this hidden 0 would also be rewritten. ***)
    prove Inj0 0 :e 1 :+: X.
    apply Inj0_setsum.
    prove 0 :e 1.
    exact In_0_1.
  + assume H2: exists x :e X, z = Inj1 x.
    apply (exandE set (fun x => x :e X) (fun x => z = Inj1 x) H2).
    let x.
    assume H2: x :e X.
    assume H3: z = Inj1 x.
    rewrite H3.
    prove Inj1 x :e 1 :+: X.
    apply Inj1_setsum.
    exact H2.
Qed.

(* Treasure "1DqLEbpzUZG8BpQNdjKq5hSpAobp7vcfPQ" *)
Theorem nat_setsum1_ordsucc : forall n:set, nat_p n -> 1 :+: n = ordsucc n.
claim L: forall n:set, nat_p n -> Inj1 n = ordsucc n.
{
  apply nat_complete_ind.
  let n.
  assume Hn: nat_p n.
  assume IHn: forall m :e n, Inj1 m = ordsucc m.
  prove Inj1 n = ordsucc n.
  apply set_ext.
  - prove Inj1 n c= ordsucc n.
    let z.
    assume H1: z :e Inj1 n.
    prove z :e ordsucc n.
    apply (Inj1E n z H1).
    + assume H2: z = 0.
      rewrite H2.
      prove 0 :e ordsucc n.
      exact (nat_0_in_ordsucc n Hn).
    + assume H2: exists m :e n, z = Inj1 m.
      apply (exandE set (fun m => m :e n) (fun m => z = Inj1 m) H2).
      let m.
      assume H3: m :e n.
      assume H4: z = Inj1 m.
      rewrite H4.
      prove Inj1 m :e ordsucc n.
      rewrite (IHn m H3).
      prove ordsucc m :e ordsucc n.
      exact (nat_ordsucc_in_ordsucc n Hn m H3).
  - prove ordsucc n c= Inj1 n.
    let m.
    assume H1: m :e ordsucc n.
    prove m :e Inj1 n.
    apply (ordsuccE n m H1).
    + assume H2: m :e n.
      apply (nat_inv m (nat_p_trans n Hn m H2)).
      * assume H3: m = 0.
        rewrite H3.
        prove 0 :e Inj1 n.
        exact (Inj1I1 n).
      * assume H3: exists k, nat_p k /\ m = ordsucc k.
        apply (exandE set nat_p (fun k => m = ordsucc k) H3).
        let k.
        assume H4: nat_p k.
        assume H5: m = ordsucc k.
        rewrite H5.
        prove ordsucc k :e Inj1 n.
        claim L1: k :e m.
        {
          rewrite H5.
  	  exact (ordsuccI2 k).
        }
        claim L2: k :e n.
        { exact (nat_trans n Hn m H2 k L1). }
        rewrite <- (IHn k L2).
        prove Inj1 k :e Inj1 n.
        exact (Inj1I2 n k L2).
    + assume H2: m = n.
      rewrite H2.
      prove n :e Inj1 n.
      apply (nat_inv n Hn).
      * assume H3: n = 0.
        rewrite H3 at 1.
        prove 0 :e Inj1 n.
        exact (Inj1I1 n).
      * assume H3: exists k, nat_p k /\ n = ordsucc k.
        apply (exandE set nat_p (fun k => n = ordsucc k) H3).
        let k.
        assume H4: nat_p k.
        assume H5: n = ordsucc k.
        rewrite H5 at 1.
        prove ordsucc k :e Inj1 n.
        claim L1: k :e n.
        {
          rewrite H5.
	  exact (ordsuccI2 k).
        }
        rewrite <- (IHn k L1).
        prove Inj1 k :e Inj1 n.
        exact (Inj1I2 n k L1).
}
let n.
assume Hn: nat_p n.
prove 1 :+: n = ordsucc n.
rewrite Inj1_setsum_1L.
prove Inj1 n = ordsucc n.
exact (L n Hn).
Qed.

(* Treasure "18tibKdygPRy3DF5TywgVFjTQLqw35qAq4" *)
Theorem setsum_0_0 : 0 :+: 0 = 0.
rewrite (Inj0_setsum_0L 0).
prove Inj0 0 = 0.
exact Inj0_0.
Qed.

(* Treasure "18ymN25HDWrSKUXjbCQUyTQQkaovPRGLfz" *)
Theorem setsum_1_0_1 : 1 :+: 0 = 1.
exact (nat_setsum1_ordsucc 0 nat_0).
Qed.

(* Treasure "18k1tppKmE66N2TRDCDEvsxuhmPVBReoqc" *)
Theorem setsum_1_1_2 : 1 :+: 1 = 2.
exact (nat_setsum1_ordsucc 1 nat_1).
Qed.

(* Treasure "1NYdPh3ynqCNJGmdhFdvpw9CDBt5uFUdZa" *)
Theorem setsum_mon : forall X Y W Z, X c= W -> Y c= Z -> X :+: Y c= W :+: Z.
let X Y W Z.
assume H1: X c= W.
assume H2: Y c= Z.
let u.
assume H3: u :e X :+: Y.
prove u :e W :+: Z.
apply (setsum_Inj_inv X Y u H3).
- assume H4: exists x :e X, u = Inj0 x.
  apply (exandE set (fun x => x :e X) (fun x => u = Inj0 x) H4).
  let x.
  assume H5: x :e X.
  assume H6: u = Inj0 x.
  rewrite H6.
  prove Inj0 x :e W :+: Z.
  apply Inj0_setsum.
  exact (H1 x H5).
- assume H4: exists y :e Y, u = Inj1 y.
  apply (exandE set (fun y => y :e Y) (fun y => u = Inj1 y) H4).
  let y.
  assume H5: y :e Y.
  assume H6: u = Inj1 y.
  rewrite H6.
  prove Inj1 y :e W :+: Z.
  apply Inj1_setsum.
  exact (H2 y H5).
Qed.
