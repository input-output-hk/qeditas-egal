(* Title "Natural Numbers as Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "2nPDtwmgvfam3ctmf" *)

Definition ordsucc : set->set := fun x:set => x :\/: {x}.

(* Treasure "14528YYu71mjAqo7uj3Gg53PH1V3ANDqFg" *)
Lemma ordsuccI1 : forall x:set, x c= ordsucc x.
Admitted.

(* Treasure "1UAKapMLELUMkvRGExwgtZsfYwE2NKwco" *)
Lemma ordsuccI2 : forall x:set, x :e ordsucc x.
Admitted.

(* Treasure "19kkPsDw52F5UhvBnBUXtsH194qFtxmfrp" *)
Lemma ordsuccE : forall x y:set, y :e ordsucc x -> y :e x \/ y = x.
Admitted.

Notation Nat Empty ordsucc.

(* Treasure "1H4MWygv6BDq6AjyVRXTNfUhFpF8KohYJF" *)
Lemma neq_0_ordsucc : forall a:set, 0 <> ordsucc a.
Admitted.

(* Treasure "1JrLZCvBQZquz445kqr6LrW6VNcLq1WXXS" *)
Lemma neq_ordsucc_0 : forall a:set, ordsucc a <> 0.
Admitted.

(* Treasure "1DgeuVcy68vTCeHFGqT5kWPyqBoPJzQUkL" *)
Lemma ordsucc_inj : forall a b:set, ordsucc a = ordsucc b -> a = b.
Admitted.

(* Treasure "1KZxs7zzJmJsHoVMfQ7JfBQHRskiyba5wn" *)
Lemma ordsucc_inj_contra : forall a b:set, a <> b -> ordsucc a <> ordsucc b.
Admitted.

(* Treasure "17GE5PyhStd1k1V5CeWDqAogHMnKtRX1EX" *)
Lemma In_0_1 : 0 :e 1.
Admitted.

(* Treasure "1LyZwJKWeutbi15ZNV1oNQMTiVXn18Bf85" *)
Lemma In_1_2 : 1 :e 2.
Admitted.

(* Treasure "1LrdnY31c8r1SkhtWSXWxL5cQJiatM5Zrh" *)
Lemma In_0_2 : 0 :e 2.
Admitted.

(* Treasure "1LDCKeG3s7omaBNMDVbbQfiVssubuLd4oL" *)
Lemma neq_0_1 : 0 <> 1.
Admitted.

(* Treasure "16ND8FARaTMCgeusMZZ7fJAgS9Nad1eEGN" *)
Lemma neq_1_0 : 1 <> 0.
Admitted.

(* Treasure "157CrqYPEngKir83nK7DReZewBJabBcEXx" *)
Lemma neq_0_2 : 0 <> 2.
Admitted.

(* Treasure "1HP9swtgZygS4Dm4Ptfof2iX6YQJyfPFFw" *)
Lemma neq_2_0 : 2 <> 0.
Admitted.

(* Treasure "1HD8qJ2kzAPicPs18rrriLDn4qqQ2HztK2" *)
Lemma neq_1_2 : 1 <> 2.
Admitted.

(* Treasure "186YPhJfg9QivL6TridqKJeCAn3Q7ghWr2" *)
Lemma neq_2_1 : 2 <> 1.
Admitted.

(* Treasure "18wG8WfTEHmMD9vDMDrn6KnmQ9ER4JuY2P" *)
Lemma nIn_0_0 : 0 /:e 0.
Admitted.

(* Treasure "1Fo1zE52VJr9tZeYLGR98Tv9dcDkqbCuJV" *)
Lemma nIn_1_0 : 1 /:e 0.
Admitted.

(* Treasure "1H8CbsaRjqw5Uv3VwtP2eTz38sy6fRDyqW" *)
Lemma nIn_2_0 : 2 /:e 0.
Admitted.

(* Treasure "19o8ZRYFgmgczs3Ar5x5ehSTgtjYDBTsoG" *)
Lemma nIn_1_1 : 1 /:e 1.
Admitted.

(* Treasure "19VQ8gvF7XR15YcPmivrFqFpSLP6ZgN4zS" *)
Lemma nIn_2_1 : 2 /:e 1.
Admitted.

(* Treasure "1LHeNQkxp4nADcrvebZQVZjVhipYUiHBLw" *)
Lemma nIn_2_2 : 2 /:e 2.
Admitted.

(* Treasure "1HBeVXgvSsY4RQbp46ejr22sVZg2wyEMmC" *)
Lemma Subq_0_0 : 0 c= 0.
Admitted.

(* Treasure "1AuRhLoPW29WR4p3F6zzciFckx4UgiSsad" *)
Lemma Subq_0_1 : 0 c= 1.
Admitted.

(* Treasure "1KL1GpS8CdhNP852FnWQoB1K2UhasLW6sx" *)
Lemma Subq_0_2 : 0 c= 2.
Admitted.

(* Treasure "113VURtBdttJ1TwUw2FymPFU542oDvTCPh" *)
Lemma nSubq_1_0 : 1 /c= 0.
Admitted.

(* Treasure "1BYoZQfD6PszgumSoN7Wi4Y6eHjwHmpCg1" *)
Lemma Subq_1_1 : 1 c= 1.
Admitted.

(* Treasure "1Att6etUUgXWe4sU8Fo5EZnfaNYDA54f59" *)
Lemma Subq_1_2 : 1 c= 2.
Admitted.

(* Treasure "1H2on33EjMTHKY8EZiwk58454hqyPFxyoV" *)
Lemma nSubq_2_0 : 2 /c= 0.
Admitted.

(* Treasure "1i7ikGCKENzqnBb5donsszp2vnvG97zYs" *)
Lemma nSubq_2_1 : 2 /c= 1.
Admitted.

(* Treasure "1Li6u6A7oLbiSB2U78UhuF6Rnjx3JKewox" *)
Lemma Subq_2_2 : 2 c= 2.
Admitted.

(* Treasure "1JubG6HHTfBBB6QaB8z3WK1sA1BWQgEoS1" *)
Lemma Subq_1_Sing0 : 1 c= {0}.
Admitted.

(* Treasure "1EEFX3b3wyj8CEWS6HKHqX356XYTvMggWG" *)
Lemma Subq_Sing0_1 : {0} c= 1.
Admitted.

(* Treasure "1CS1HyBY5dm2zvfM4sxz3nx2MqXDXy71fB" *)
Lemma eq_1_Sing0 : 1 = {0}.
Admitted.

(* Treasure "19qbj94ZReU1kMkbCxsjtvdXKH8t8VdTAR" *)
Lemma Subq_2_UPair01 : 2 c= {0,1}.
Admitted.

(* Treasure "1DfvqprW2hbAXt73k7VqH5bECoi67GeAYq" *)
Lemma Subq_UPair01_2 : {0,1} c= 2.
Admitted.

(* Treasure "1AuNLuytgf6ajzxYEh8MNxArVbguUmYAYE" *)
Lemma eq_2_UPair01 : 2 = {0,1}.
Admitted.

Definition nat_p : set->prop := fun n:set => forall p:set->prop, p 0 -> (forall x:set, p x -> p (ordsucc x)) -> p n.

(* Treasure "1AL4KfdaEcRckWUnVhUaCxpiutHazY9PVc" *)
Lemma nat_0 : nat_p 0.
Admitted.

(* Treasure "1DrrQ4UvWsNAsDgVXGpEo1DRwD4v5Btv6v" *)
Lemma nat_ordsucc : forall n:set, nat_p n -> nat_p (ordsucc n).
Admitted.

(* Treasure "1B6a82GhT7ks8B9QkFRcFrpoLSspYztPzt" *)
Lemma nat_1 : nat_p 1.
Admitted.

(* Treasure "1HSRtv9CXm7FJ6aN2wMmyqEe124L3d5Lqg" *)
Lemma nat_2 : nat_p 2.
Admitted.

(* Treasure "1Ha5CXjXYf4LsLjsTvsi1qjhqGffRwqeBH" *)
Lemma nat_0_in_ordsucc : forall n, nat_p n -> 0 :e ordsucc n.
Admitted.

(* Treasure "1KvorejuY1XHFh3i4kTHpVenTJsENkDk2v" *)
Lemma nat_ordsucc_in_ordsucc : forall n, nat_p n -> forall m :e n, ordsucc m :e ordsucc n.
Admitted.

(* Treasure "15wy96wCYTsxNpMtPmFJnPHEFJhowr8X7M" *)
Lemma nat_ind : forall p:set->prop, p 0 -> (forall n, nat_p n -> p n -> p (ordsucc n)) -> forall n, nat_p n -> p n.
Admitted.

(* Treasure "1LtVn242MfTmQhA72sHXtNJqjv9LfxAa4K" *)
Lemma nat_inv : forall n, nat_p n -> n = 0 \/ exists x, nat_p x /\ n = ordsucc x.
Admitted.

(* Treasure "1Fcqbvkn2vG5i8u1E4x3C1wbrs5Vskg5ii" *)
Lemma nat_complete_ind : forall p:set->prop, (forall n, nat_p n -> (forall m :e n, p m) -> p n) -> forall n, nat_p n -> p n.
Admitted.

(* Treasure "1Hph3FZa6wszjLJNVVeUaPhp9AJxPoCJZQ" *)
Lemma nat_p_trans : forall n, nat_p n -> forall m :e n, nat_p m.
Admitted.

(* Treasure "1Chi9W7CsUBFHVSDNxafY1W3vZbNVgGdMg" *)
Lemma nat_trans : forall n, nat_p n -> forall m :e n, m c= n.
Admitted.

(* Treasure "14mbwbH9ZrmEDkFfq761JntojRGUUABznC" *)
Lemma nat_ordsucc_trans : forall n, nat_p n -> forall m :e ordsucc n, m c= n.
Admitted.

(* Treasure "1Kbw5WDH6R562UJ2QzeCRgmV33SNHpordP" *)
Lemma Union_ordsucc_eq : forall n, nat_p n -> Union (ordsucc n) = n.
Admitted.
