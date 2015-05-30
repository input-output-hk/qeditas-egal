(* Title "Introduction to Ordinals" *)
(* Author "Chad E. Brown" *)

(* Salt "tgrf8cu2HQz7s5oc" *)

(* Unicode alpha "3b1" *)
(* Unicode beta "3b2" *)
(* Unicode gamma "3b3" *)
(* Unicode delta "3b4" *)

Definition TransSet : set->prop := fun U:set => forall x :e U, x c= U.

Definition ordinal : set->prop := fun (alpha:set) => TransSet alpha /\ forall beta :e alpha, TransSet beta.

(* Treasure "1EojmGk6nJKJZ5wNxmK1fqaxrKPq3ujadM" *)
Theorem ordinal_TransSet : forall alpha:set, ordinal alpha -> TransSet alpha.
exact (fun alpha H => andEL (TransSet alpha) (forall beta :e alpha, TransSet beta) H).
Qed.

(* Treasure "1AwwFxbJgHNtz5pfQhMeBfEADuVUaWK5rC" *)
Theorem ordinal_In_TransSet : forall alpha:set, ordinal alpha -> forall beta :e alpha, TransSet beta.
exact (fun alpha H => andER (TransSet alpha) (forall beta :e alpha, TransSet beta) H).
Qed.

(* Treasure "1CbQVEDG5Rrsxz5TmzH6XBMtcekcLzxi2T" *)
Theorem ordinal_Empty : ordinal Empty.
prove TransSet Empty /\ forall x :e Empty, TransSet x.
apply andI.
- let x.
  assume Hx: x :e Empty.
  prove False.
  exact (EmptyE x Hx).
- let x.
  assume Hx: x :e Empty.
  prove False.
  exact (EmptyE x Hx).
Qed.

(* Treasure "1KVzQHmEg1Ci9D6yKoMHsCGPqpouCqrbc2" *)
Theorem ordinal_Hered : forall alpha:set, ordinal alpha -> forall beta :e alpha, ordinal beta.
let alpha.
assume H1: TransSet alpha /\ forall x :e alpha, TransSet x.
let beta.
assume H2: beta :e alpha.
prove TransSet beta /\ forall x :e beta, TransSet x.
apply H1.
assume H3: TransSet alpha.
assume H4: forall x :e alpha, TransSet x.
apply andI.
- exact (H4 beta H2).
- prove forall x :e beta, TransSet x.
  let x.
  assume Hx: x :e beta.
  claim L1: x :e alpha.
  { exact (H3 beta H2 x Hx). }
  prove TransSet x.
  exact (H4 x L1).
Qed.

(* Treasure "16BcE3SvvUugf2s7hHU4QWAUDTdTGgVSSK" *)
Theorem ordinal_ind : forall p:set->prop, 
(forall alpha, ordinal alpha -> (forall beta :e alpha, p beta) -> p alpha)
->
forall alpha, ordinal alpha -> p alpha.
let p.
assume H1: forall alpha, ordinal alpha -> (forall beta :e alpha, p beta) -> p alpha.
apply In_ind.
let alpha.
assume IH: forall beta :e alpha, ordinal beta -> p beta.
assume H2: ordinal alpha.
prove p alpha.
apply (H1 alpha H2).
let beta.
assume H3: beta :e alpha.
prove p beta.
apply (IH beta H3).
prove ordinal beta.
exact (ordinal_Hered alpha H2 beta H3).
Qed.

(* Treasure "162KmhTK6ScFBnk4Dvd9jiiHf8nJqgiWXD" *)
Theorem TransSet_ordsucc : forall X:set, TransSet X -> TransSet (ordsucc X).
let X.
assume H1: TransSet X.
let x.
assume H2: x :e ordsucc X.
let y.
assume H3: y :e x.
prove y :e ordsucc X.
apply (ordsuccE X x H2).
- assume H4: x :e X.
  apply ordsuccI1.
  prove y :e X.
  exact (H1 x H4 y H3).
- assume H4: x = X.
  apply ordsuccI1.
  prove y :e X.
  rewrite <- H4.
  prove y :e x.
  exact H3.
Qed.

(* Treasure "1AmSq7wUzSUEWjExYma9QYR8qUP5n2Hj64" *)
Theorem ordinal_ordsucc : forall alpha:set, ordinal alpha -> ordinal (ordsucc alpha).
let alpha.
assume H1: TransSet alpha /\ forall beta :e alpha, TransSet beta.
apply H1.
assume H2: TransSet alpha.
assume H3: forall beta :e alpha, TransSet beta.
prove TransSet (ordsucc alpha) /\ forall beta :e ordsucc alpha, TransSet beta.
apply andI.
- exact (TransSet_ordsucc alpha H2).
- let beta.
  assume H4: beta :e ordsucc alpha.
  prove TransSet beta.
  apply (ordsuccE alpha beta H4).
  + assume H5: beta :e alpha.
    exact (H3 beta H5).
  + assume H5: beta = alpha.
    rewrite H5.
    exact H2.
Qed.

(* Treasure "1AgCLMqynP5KDaF1gSHdzjMZX7mjiHN1dN" *)
Theorem nat_p_ordinal : forall n:set, nat_p n -> ordinal n.
apply nat_ind.
- prove ordinal 0.
  exact ordinal_Empty.
- let n.
  assume Hn: nat_p n.
  assume IHn: ordinal n.
  prove ordinal (ordsucc n).
  exact (ordinal_ordsucc n IHn).
Qed.

(* Treasure "1Chj5ger4G6WFuiCbqfWmmuKBZUPrH8u6d" *)
Theorem omega_TransSet : TransSet omega.
let n.
assume Hn: n :e omega.
let m.
assume Hm: m :e n.
prove m :e omega.
apply nat_p_omega.
prove nat_p m.
apply (nat_p_trans n).
- prove nat_p n. exact (omega_nat_p n Hn).
- prove m :e n. exact Hm.
Qed.

(* Treasure "13D4LgCj56ETthUqcPcvEbP1amvRrqSUgK" *)
Theorem omega_ordinal : ordinal omega.
prove TransSet omega /\ forall n :e omega, TransSet n.
apply andI.
- exact omega_TransSet.
- let n.
  assume Hn: n :e omega.
  prove TransSet n.
  apply ordinal_TransSet.
  prove ordinal n.
  apply nat_p_ordinal.
  prove nat_p n.
  exact (omega_nat_p n Hn).
Qed.

(* Treasure "1A2P9cem1AQQbMwonSAuW6hCrgwTsQXxVW" *)
Theorem TransSet_ordsucc_In_Subq : forall X:set, TransSet X -> forall x :e X, ordsucc x c= X.
let X.
assume H1: TransSet X.
let x.
assume H2: x :e X.
let y.
assume H3: y :e ordsucc x.
prove y :e X.
apply (ordsuccE x y H3).
- assume H4: y :e x.
  exact (H1 x H2 y H4).
- assume H4: y = x.
  rewrite H4.
  prove x :e X.
  exact H2.
Qed.

(* Treasure "1Lzy1bmgxqw3KCBxtR6rXsgck8v2uaRhgR" *)
Theorem ordinal_ordsucc_In_Subq : forall alpha, ordinal alpha -> forall beta :e alpha, ordsucc beta c= alpha.
let alpha.
assume H: ordinal alpha.
exact (TransSet_ordsucc_In_Subq alpha (ordinal_TransSet alpha H)).
Qed.

(* Treasure "1Es7PU3HBZvWGrFUbPuoC718dCmBHYHqwm" *)
Theorem ordinal_trichotomy_or : forall alpha beta:set, ordinal alpha -> ordinal beta -> alpha :e beta \/ alpha = beta \/ beta :e alpha.
apply In_ind.
let alpha.
assume IHalpha: forall gamma :e alpha, forall beta:set, ordinal gamma -> ordinal beta -> gamma :e beta \/ gamma = beta \/ beta :e gamma.
prove forall beta:set, ordinal alpha -> ordinal beta -> alpha :e beta \/ alpha = beta \/ beta :e alpha.
apply In_ind.
let beta.
assume IHbeta: forall delta :e beta, ordinal alpha -> ordinal delta -> alpha :e delta \/ alpha = delta \/ delta :e alpha.
assume Halpha : ordinal alpha.
assume Hbeta : ordinal beta.
prove alpha :e beta \/ alpha = beta \/ beta :e alpha.
apply (classic (alpha :e beta)).
- assume H1: alpha :e beta.
  apply or3I1.
  exact H1.
- assume H1: alpha /:e beta.
  apply (classic (beta :e alpha)).
  + assume H2: beta :e alpha.
    apply or3I3.
    exact H2.
  + assume H2: beta /:e alpha.
    apply or3I2.
    prove alpha = beta.
    apply set_ext.
    * { prove alpha c= beta.
        let gamma.
	assume H3: gamma :e alpha.
	prove gamma :e beta.
	claim Lgamma: ordinal gamma.
	{ exact (ordinal_Hered alpha Halpha gamma H3). }
	apply (or3E (gamma :e beta) (gamma = beta) (beta :e gamma) (IHalpha gamma H3 beta Lgamma Hbeta)).
	- assume H4: gamma :e beta.
	  exact H4.
        - assume H4: gamma = beta.
          prove False.
          apply H2.
          prove beta :e alpha.
	  rewrite <- H4.
	  exact H3.
        - assume H4: beta :e gamma.
          prove False.
          apply H2.
          prove beta :e alpha.
          exact (ordinal_TransSet alpha Halpha gamma H3 beta H4).
      }
    * { prove beta c= alpha.
        let delta.
	assume H3: delta :e beta.
	prove delta :e alpha.
	claim Ldelta: ordinal delta.
	{ exact (ordinal_Hered beta Hbeta delta H3). }
	apply (or3E (alpha :e delta) (alpha = delta) (delta :e alpha) (IHbeta delta H3 Halpha Ldelta)).
        - assume H4: alpha :e delta.
          prove False.
          apply H1.
          prove alpha :e beta.
          exact (ordinal_TransSet beta Hbeta delta H3 alpha H4).
        - assume H4: alpha = delta.
          prove False.
          apply H1.
          prove alpha :e beta.
	  rewrite H4.
	  exact H3.
	- assume H4: delta :e alpha.
	  exact H4.
      }
Qed.    

(* Treasure "1zLABNcEyk91BzSAUQqh5k1vUY7AWtHUv" *)
Theorem ordinal_trichotomy : forall alpha beta:set,
 ordinal alpha -> ordinal beta -> exactly1of3 (alpha :e beta) (alpha = beta) (beta :e alpha).
let alpha beta.
assume H1: ordinal alpha.
assume H2: ordinal beta.
apply (or3E (alpha :e beta) (alpha = beta) (beta :e alpha) (ordinal_trichotomy_or alpha beta H1 H2)).
- assume H3: alpha :e beta.
  apply exactly1of3_I1.
  + prove alpha :e beta.
    exact H3.
  + prove alpha <> beta.
    assume H4: alpha = beta.
    apply (In_irref alpha).
    prove alpha :e alpha.
    rewrite H4 at 2.
    exact H3.
  + prove beta /:e alpha.
    assume H4: beta :e alpha.
    exact (In_no2cycle alpha beta H3 H4).
- assume H3: alpha = beta.
  apply exactly1of3_I2.
  + prove alpha /:e beta.
    rewrite H3.
    apply In_irref.
  + prove alpha = beta.
    exact H3.
  + prove beta /:e alpha.
    rewrite H3.
    apply In_irref.
- assume H3: beta :e alpha.
  apply exactly1of3_I3.
  + prove alpha /:e beta.
    assume H4: alpha :e beta.
    exact (In_no2cycle alpha beta H4 H3).
  + prove alpha <> beta.
    assume H4: alpha = beta.
    apply (In_irref alpha).
    prove alpha :e alpha.
    rewrite H4 at 1.
    exact H3.
  + prove beta :e alpha.
    exact H3.
Qed.

(* Treasure "135E8xcgLnkiy7kQbWRroRvBdoiVTttyKe" *)
Theorem ordinal_In_Or_Subq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha :e beta \/ beta c= alpha.
let alpha beta.
assume H1: ordinal alpha.
assume H2: ordinal beta.
apply (or3E (alpha :e beta) (alpha = beta) (beta :e alpha) (ordinal_trichotomy_or alpha beta H1 H2)).
- assume H3: alpha :e beta.
  apply orIL.
  exact H3.
- assume H3: alpha = beta.
  apply orIR.
  rewrite H3.
  apply Subq_ref.
- assume H3: beta :e alpha.
  apply orIR.
  exact (ordinal_TransSet alpha H1 beta H3).
Qed.

(* Treasure "1G8TVsrLW2SdMWm4rCx1abKjD4vZWXdyvV" *)
Theorem ordinal_linear : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta \/ beta c= alpha.
let alpha beta.
assume H1: ordinal alpha.
assume H2: ordinal beta.
apply (ordinal_In_Or_Subq alpha beta H1 H2).
- assume H3: alpha :e beta.
  apply orIL.
  exact (ordinal_TransSet beta H2 alpha H3).
- assume H3: beta c= alpha.
  apply orIR.
  exact H3.
Qed.
