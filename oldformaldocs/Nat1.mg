(* Title "Natural Numbers as Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "2nPDtwmgvfam3ctmf" *)

Definition ordsucc : set->set := fun x:set => x :\/: {x}.

(* Treasure "14528YYu71mjAqo7uj3Gg53PH1V3ANDqFg" *)
Lemma ordsuccI1 : forall x:set, x c= ordsucc x.
exact (fun (x y : set) (H1 : y :e x) => binunionI1 x {x} y H1).
Qed.

(* Treasure "1UAKapMLELUMkvRGExwgtZsfYwE2NKwco" *)
Lemma ordsuccI2 : forall x:set, x :e ordsucc x.
exact (fun x : set => binunionI2 x {x} x (SingI x)).
Qed.

(* Treasure "19kkPsDw52F5UhvBnBUXtsH194qFtxmfrp" *)
Lemma ordsuccE : forall x y:set, y :e ordsucc x -> y :e x \/ y = x.
let x y.
assume H1: y :e x :\/: {x}.
apply (binunionE x {x} y H1).
- assume H2: y :e x. apply orIL. exact H2.
- assume H2: y :e {x}. apply orIR. exact (SingE x y H2).
Qed.

Notation Nat Empty ordsucc.

(* Treasure "1H4MWygv6BDq6AjyVRXTNfUhFpF8KohYJF" *)
Lemma neq_0_ordsucc : forall a:set, 0 <> ordsucc a.
let a.
assume H1: 0 = ordsucc a.
claim L1: a /:e ordsucc a.
{ rewrite <- H1. exact (EmptyE a). }
exact (L1 (ordsuccI2 a)).
Qed.

(* Treasure "1JrLZCvBQZquz445kqr6LrW6VNcLq1WXXS" *)
Lemma neq_ordsucc_0 : forall a:set, ordsucc a <> 0.
exact (fun (a : set) (H1 : ordsucc a = 0) => neq_0_ordsucc a (eq_sym set (ordsucc a) 0 H1)).
Qed.

(* Treasure "1DgeuVcy68vTCeHFGqT5kWPyqBoPJzQUkL" *)
Lemma ordsucc_inj : forall a b:set, ordsucc a = ordsucc b -> a = b.
let a b.
assume H1: ordsucc a = ordsucc b.
claim L1: a :e ordsucc b.
{
  rewrite <- H1.
  exact (ordsuccI2 a).
}
apply (ordsuccE b a L1).
- assume H2: a :e b.
  claim L2: b :e ordsucc a.
  {
    rewrite H1.
    exact (ordsuccI2 b).
  }
  apply (ordsuccE a b L2).
  + assume H3: b :e a. prove False. exact (In_no2cycle a b H2 H3).
  + assume H3: b = a. apply (eq_sym set). exact H3.
- assume H2: a = b. exact H2.
Qed.

(* Treasure "1KZxs7zzJmJsHoVMfQ7JfBQHRskiyba5wn" *)
Lemma ordsucc_inj_contra : forall a b:set, a <> b -> ordsucc a <> ordsucc b.
exact (fun a b H1 H2 => H1 (ordsucc_inj a b H2)).
Qed.

(* Treasure "17GE5PyhStd1k1V5CeWDqAogHMnKtRX1EX" *)
Lemma In_0_1 : 0 :e 1.
exact (ordsuccI2 0).
Qed.

(* Treasure "1LyZwJKWeutbi15ZNV1oNQMTiVXn18Bf85" *)
Lemma In_1_2 : 1 :e 2.
exact (ordsuccI2 1).
Qed.

(* Treasure "1LrdnY31c8r1SkhtWSXWxL5cQJiatM5Zrh" *)
Lemma In_0_2 : 0 :e 2.
exact (ordsuccI1 1 0 In_0_1).
Qed.

(* Treasure "1LDCKeG3s7omaBNMDVbbQfiVssubuLd4oL" *)
Lemma neq_0_1 : 0 <> 1.
exact (neq_0_ordsucc 0).
Qed.

(* Treasure "16ND8FARaTMCgeusMZZ7fJAgS9Nad1eEGN" *)
Lemma neq_1_0 : 1 <> 0.
exact (neq_ordsucc_0 0).
Qed.

(* Treasure "157CrqYPEngKir83nK7DReZewBJabBcEXx" *)
Lemma neq_0_2 : 0 <> 2.
exact (neq_0_ordsucc 1).
Qed.

(* Treasure "1HP9swtgZygS4Dm4Ptfof2iX6YQJyfPFFw" *)
Lemma neq_2_0 : 2 <> 0.
exact (neq_ordsucc_0 1).
Qed.

(* Treasure "1HD8qJ2kzAPicPs18rrriLDn4qqQ2HztK2" *)
Lemma neq_1_2 : 1 <> 2.
exact (ordsucc_inj_contra 0 1 neq_0_1).
Qed.

(* Treasure "186YPhJfg9QivL6TridqKJeCAn3Q7ghWr2" *)
Lemma neq_2_1 : 2 <> 1.
exact (ordsucc_inj_contra 1 0 neq_1_0).
Qed.

(* Treasure "18wG8WfTEHmMD9vDMDrn6KnmQ9ER4JuY2P" *)
Lemma nIn_0_0 : 0 /:e 0.
exact (EmptyE 0).
Qed.

(* Treasure "1Fo1zE52VJr9tZeYLGR98Tv9dcDkqbCuJV" *)
Lemma nIn_1_0 : 1 /:e 0.
exact (EmptyE 1).
Qed.

(* Treasure "1H8CbsaRjqw5Uv3VwtP2eTz38sy6fRDyqW" *)
Lemma nIn_2_0 : 2 /:e 0.
exact (EmptyE 2).
Qed.

(* Treasure "19o8ZRYFgmgczs3Ar5x5ehSTgtjYDBTsoG" *)
Lemma nIn_1_1 : 1 /:e 1.
exact (In_irref 1).
Qed.

(* Treasure "19VQ8gvF7XR15YcPmivrFqFpSLP6ZgN4zS" *)
Lemma nIn_2_1 : 2 /:e 1.
exact (fun H => ordsuccE 0 2 H False (EmptyE 2) neq_2_0).
Qed.

(* Treasure "1LHeNQkxp4nADcrvebZQVZjVhipYUiHBLw" *)
Lemma nIn_2_2 : 2 /:e 2.
exact (In_irref 2).
Qed.

(* Treasure "1HBeVXgvSsY4RQbp46ejr22sVZg2wyEMmC" *)
Lemma Subq_0_0 : 0 c= 0.
exact (Subq_Empty 0).
Qed.

(* Treasure "1AuRhLoPW29WR4p3F6zzciFckx4UgiSsad" *)
Lemma Subq_0_1 : 0 c= 1.
exact (Subq_Empty 1).
Qed.

(* Treasure "1KL1GpS8CdhNP852FnWQoB1K2UhasLW6sx" *)
Lemma Subq_0_2 : 0 c= 2.
exact (Subq_Empty 2).
Qed.

(* Treasure "113VURtBdttJ1TwUw2FymPFU542oDvTCPh" *)
Lemma nSubq_1_0 : 1 /c= 0.
exact (fun H => nIn_0_0 (H 0 In_0_1)).
Qed.

(* Treasure "1BYoZQfD6PszgumSoN7Wi4Y6eHjwHmpCg1" *)
Lemma Subq_1_1 : 1 c= 1.
exact (Subq_ref 1).
Qed.

(* Treasure "1Att6etUUgXWe4sU8Fo5EZnfaNYDA54f59" *)
Lemma Subq_1_2 : 1 c= 2.
exact (ordsuccI1 1).
Qed.

(* Treasure "1H2on33EjMTHKY8EZiwk58454hqyPFxyoV" *)
Lemma nSubq_2_0 : 2 /c= 0.
exact (fun H => nIn_0_0 (H 0 In_0_2)).
Qed.

(* Treasure "1i7ikGCKENzqnBb5donsszp2vnvG97zYs" *)
Lemma nSubq_2_1 : 2 /c= 1.
exact (fun H => nIn_1_1 (H 1 In_1_2)).
Qed.

(* Treasure "1Li6u6A7oLbiSB2U78UhuF6Rnjx3JKewox" *)
Lemma Subq_2_2 : 2 c= 2.
exact (Subq_ref 2).
Qed.

(* Treasure "1JubG6HHTfBBB6QaB8z3WK1sA1BWQgEoS1" *)
Lemma Subq_1_Sing0 : 1 c= {0}.
let x.
assume H1: x :e 1.
prove x :e {0}.
apply (ordsuccE 0 x H1).
- assume H2: x :e 0.
  prove False.
  exact (EmptyE x H2).
- assume H2: x = 0.
  rewrite H2.
  prove 0 :e {0}.
  exact (SingI 0).
Qed.

(* Treasure "1EEFX3b3wyj8CEWS6HKHqX356XYTvMggWG" *)
Lemma Subq_Sing0_1 : {0} c= 1.
exact (fun x H1 => SingE 0 x H1 (fun s : set => x :e ordsucc s) (ordsuccI2 x)).
Qed.

(* Treasure "1CS1HyBY5dm2zvfM4sxz3nx2MqXDXy71fB" *)
Lemma eq_1_Sing0 : 1 = {0}.
exact (set_ext 1 (Sing 0) Subq_1_Sing0 Subq_Sing0_1).
Qed.

(* Treasure "19qbj94ZReU1kMkbCxsjtvdXKH8t8VdTAR" *)
Lemma Subq_2_UPair01 : 2 c= {0,1}.
let x.
assume H1: x :e 2.
apply (ordsuccE 1 x H1).
- assume H2: x :e 1.
  claim L1: x = 0.
  { exact (SingE 0 x (Subq_1_Sing0 x H2)). }
  prove x :e {0,1}.
  rewrite L1.
  prove 0 :e {0,1}.
  exact (UPairI1 0 1).
- assume H2: x = 1.
  prove x :e {0,1}.
  rewrite H2.
  prove 1 :e {0,1}.
  exact (UPairI2 0 1).
Qed.

(* Treasure "1DfvqprW2hbAXt73k7VqH5bECoi67GeAYq" *)
Lemma Subq_UPair01_2 : {0,1} c= 2.
let x.
assume H1: x :e {0,1}.
apply (UPairE x 0 1 H1).
- assume H2: x = 0.
  prove x :e 2.
  rewrite H2.
  prove 0 :e 2.
  exact In_0_2.
- assume H2: x = 1.
  prove x :e 2.
  rewrite H2.
  prove 1 :e 2.
  exact In_1_2.
Qed.

(* Treasure "1AuNLuytgf6ajzxYEh8MNxArVbguUmYAYE" *)
Lemma eq_2_UPair01 : 2 = {0,1}.
exact (set_ext 2 {0, 1} Subq_2_UPair01 Subq_UPair01_2).
Qed.

Definition nat_p : set->prop := fun n:set => forall p:set->prop, p 0 -> (forall x:set, p x -> p (ordsucc x)) -> p n.

(* Treasure "1AL4KfdaEcRckWUnVhUaCxpiutHazY9PVc" *)
Lemma nat_0 : nat_p 0.
exact (fun p H _ => H).
Qed.

(* Treasure "1DrrQ4UvWsNAsDgVXGpEo1DRwD4v5Btv6v" *)
Lemma nat_ordsucc : forall n:set, nat_p n -> nat_p (ordsucc n).
exact (fun n H1 p H2 H3 => H3 n (H1 p H2 H3)).
Qed.

(* Treasure "1B6a82GhT7ks8B9QkFRcFrpoLSspYztPzt" *)
Lemma nat_1 : nat_p 1.
exact (nat_ordsucc 0 nat_0).
Qed.

(* Treasure "1HSRtv9CXm7FJ6aN2wMmyqEe124L3d5Lqg" *)
Lemma nat_2 : nat_p 2.
exact (nat_ordsucc 1 nat_1).
Qed.

(* Treasure "1Ha5CXjXYf4LsLjsTvsi1qjhqGffRwqeBH" *)
Lemma nat_0_in_ordsucc : forall n, nat_p n -> 0 :e ordsucc n.
let n.
assume H1: nat_p n.
apply (H1 (fun n => 0 :e ordsucc n)).
- prove 0 :e ordsucc 0.
  exact In_0_1.
- let n.
  assume IH: 0 :e ordsucc n.
  prove 0 :e ordsucc (ordsucc n).
  exact (ordsuccI1 (ordsucc n) 0 IH).
Qed.

(* Treasure "1KvorejuY1XHFh3i4kTHpVenTJsENkDk2v" *)
Lemma nat_ordsucc_in_ordsucc : forall n, nat_p n -> forall m :e n, ordsucc m :e ordsucc n.
let n.
assume H1: nat_p n.
apply (H1 (fun n => forall m :e n, ordsucc m :e ordsucc n)).
- prove forall m :e 0, ordsucc m :e ordsucc 0.
  let m.
  assume Hm: m :e 0.
  prove False.
  exact (EmptyE m Hm).
- let n.
  assume IH: forall m :e n, ordsucc m :e ordsucc n.
  prove forall m :e ordsucc n, ordsucc m :e ordsucc (ordsucc n).
  let m.
  assume H2: m :e ordsucc n.
  prove ordsucc m :e ordsucc (ordsucc n).
  apply (ordsuccE n m H2).
  + assume H3: m :e n.
    claim L1: ordsucc m :e ordsucc n.
    { exact (IH m H3). }
    exact (ordsuccI1 (ordsucc n) (ordsucc m) L1).
  + assume H3: m = n.
    rewrite H3.
    prove ordsucc n :e ordsucc (ordsucc n).
    exact (ordsuccI2 (ordsucc n)).
Qed.

(* Treasure "15wy96wCYTsxNpMtPmFJnPHEFJhowr8X7M" *)
Lemma nat_ind : forall p:set->prop, p 0 -> (forall n, nat_p n -> p n -> p (ordsucc n)) -> forall n, nat_p n -> p n.
let p.
assume H1: p 0.
assume H2: forall n, nat_p n -> p n -> p (ordsucc n).
claim L1: nat_p 0 /\ p 0.
{
  exact (andI (nat_p 0) (p 0) nat_0 H1).
}
claim L2: forall n, nat_p n /\ p n -> nat_p (ordsucc n) /\ p (ordsucc n).
{
  let n.
  assume H3: nat_p n /\ p n.
  apply H3.
  assume H4: nat_p n.
  assume H5: p n.
  apply andI.
  - prove nat_p (ordsucc n).
    exact (nat_ordsucc n H4).
  - prove p (ordsucc n).
    exact (H2 n H4 H5).
}
let n.
assume H3: nat_p n.
claim L3: nat_p n /\ p n.
{ exact (H3 (fun n => nat_p n /\ p n) L1 L2). }
exact (andER (nat_p n) (p n) L3).
Qed.

(* Treasure "1LtVn242MfTmQhA72sHXtNJqjv9LfxAa4K" *)
Lemma nat_inv : forall n, nat_p n -> n = 0 \/ exists x, nat_p x /\ n = ordsucc x.
apply nat_ind.
- prove 0 = 0 \/ exists x, nat_p x /\ 0 = ordsucc x.
  apply orIL.
  apply (eqI set).
- let n.
  assume H1 _.
  prove ordsucc n = 0 \/ exists x, nat_p x /\ ordsucc n = ordsucc x.
  apply orIR.
  witness n.
  apply andI.
  + exact H1.
  + apply (eqI set).
Qed.

(* Treasure "1Fcqbvkn2vG5i8u1E4x3C1wbrs5Vskg5ii" *)
Lemma nat_complete_ind : forall p:set->prop, (forall n, nat_p n -> (forall m :e n, p m) -> p n) -> forall n, nat_p n -> p n.
let p.
assume H1: forall n, nat_p n -> (forall m :e n, p m) -> p n.
claim L1: forall n:set, nat_p n -> forall m :e n, p m.
{
  apply nat_ind.
  - prove forall m :e 0, p m.
    let m.
    assume Hm: m :e 0.
    prove False.
    exact (EmptyE m Hm).
  - let n.
    assume Hn: nat_p n.
    assume IHn: forall m :e n, p m.
    prove forall m :e ordsucc n, p m.
    let m.
    assume Hm: m :e ordsucc n.
    prove p m.
    apply (ordsuccE n m Hm).
    + assume H2: m :e n.
      exact (IHn m H2).
    + assume H2: m = n.
      prove p m.
      rewrite H2.
      prove p n.
      exact (H1 n Hn IHn).
}
prove forall n, nat_p n -> p n.
exact (fun n Hn => H1 n Hn (L1 n Hn)).
Qed.

(* Treasure "1Hph3FZa6wszjLJNVVeUaPhp9AJxPoCJZQ" *)
Lemma nat_p_trans : forall n, nat_p n -> forall m :e n, nat_p m.
apply nat_ind.
- prove forall m :e 0, nat_p m.
  let m.
  assume Hm: m :e 0.
  prove False.
  exact (EmptyE m Hm).
- let n.
  assume Hn: nat_p n.
  assume IHn: forall m :e n, nat_p m.
  prove forall m :e ordsucc n, nat_p m.
  let m.
  assume Hm: m :e ordsucc n.
  apply (ordsuccE n m Hm).
  + assume H1: m :e n.
    exact (IHn m H1).
  + assume H1: m = n.
    rewrite H1.
    exact Hn.
Qed.

(* Treasure "1Chi9W7CsUBFHVSDNxafY1W3vZbNVgGdMg" *)
Lemma nat_trans : forall n, nat_p n -> forall m :e n, m c= n.
apply nat_ind.
- prove forall m :e 0, m c= 0.
  let m.
  assume Hm: m :e 0.
  prove False.
  exact (EmptyE m Hm).
- let n.
  assume Hn: nat_p n.
  assume IHn: forall m :e n, m c= n.
  prove forall m :e ordsucc n, m c= ordsucc n.
  let m.
  assume Hm: m :e ordsucc n.
  apply (ordsuccE n m Hm).
  + assume H1: m :e n.
    prove m c= ordsucc n.
    apply (Subq_tra m n (ordsucc n)).
    * exact (IHn m H1).
    * exact (ordsuccI1 n).
  + assume H1: m = n.
    prove m c= ordsucc n.
    rewrite H1.
    prove n c= ordsucc n.
    exact (ordsuccI1 n).
Qed.

(* Treasure "14mbwbH9ZrmEDkFfq761JntojRGUUABznC" *)
Lemma nat_ordsucc_trans : forall n, nat_p n -> forall m :e ordsucc n, m c= n.
let n.
assume Hn: nat_p n.
let m.
assume Hm: m :e ordsucc n.
let k.
assume Hk: k :e m.
prove k :e n.
apply (ordsuccE n m Hm).
- assume H1: m :e n.
  exact (nat_trans n Hn m H1 k Hk).
- assume H1: m = n.
  rewrite <- H1.
  exact Hk.
Qed.

(* Treasure "1Kbw5WDH6R562UJ2QzeCRgmV33SNHpordP" *)
Lemma Union_ordsucc_eq : forall n, nat_p n -> Union (ordsucc n) = n.
apply nat_complete_ind.
let n.
assume Hn: nat_p n.
assume IHn: forall m :e n, Union (ordsucc m) = m.
prove Union (ordsucc n) = n.
apply set_ext.
- let m.
  assume Hm: m :e Union (ordsucc n).
  apply (UnionE2 (ordsucc n) m Hm).
  let k.
  assume H1: m :e k.
  assume H2: k :e ordsucc n.
  prove m :e n.
  exact (nat_ordsucc_trans n Hn k H2 m H1).
- let m.
  assume Hm: m :e n.
  prove m :e Union (ordsucc n).
  apply (UnionI (ordsucc n) m n).
  + exact Hm.
  + exact (ordsuccI2 n).
Qed.
