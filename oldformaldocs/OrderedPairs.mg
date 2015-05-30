(* Title "Ordered Pairs as Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "3KhxsZskpyxtXKgXx" *)

Definition pair : set -> set -> set := fun X Y => X :+: Y.

(* Treasure "1H9PSjcgfa7APtz9kDrxbaKUbAHjScqUeV" *)
Theorem pair_0_0 : pair 0 0 = 0.
prove 0 :+: 0 = 0.
exact setsum_0_0.
Qed.

(* Treasure "135QpZFUEv1zXV9GjKrwqYQb7kqqAeFwem" *)
Theorem pair_1_0_1 : pair 1 0 = 1.
prove 1 :+: 0 = 1.
exact setsum_1_0_1.
Qed.

(* Treasure "1R1qb8fxLbXdAPNP7xBeZ91hncJUzi6rq" *)
Theorem pair_1_1_2 : pair 1 1 = 2.
prove 1 :+: 1 = 2.
exact setsum_1_1_2.
Qed.

(* Treasure "14ww5UUj75xL5uEGzho9oaLWdH28wHdW5r" *)
Theorem nat_pair1_ordsucc : forall n:set, nat_p n -> pair 1 n = ordsucc n.
prove forall n:set, nat_p n -> 1 :+: n = ordsucc n.
exact nat_setsum1_ordsucc.
Qed.

Definition proj0 : set -> set := fun Z => {Unj z|z :e Z, exists x:set, Inj0 x = z}.

Definition proj1 : set -> set := fun Z => {Unj z|z :e Z, exists y:set, Inj1 y = z}.

(* Treasure "12XGYjMN9peSq6VErLQ5H3vDiN8o9EY6eu" *)
Theorem Inj0_pair_0_eq : Inj0 = pair 0.
apply (func_ext set set).
let x.
apply (eq_sym set).
prove 0 :+: x = Inj0 x.
exact (Inj0_setsum_0L x).
Qed.

(* Treasure "1DQae3qEDd2YQRSTd48bXTESvKNQ55VRU3" *)
Theorem Inj1_pair_1_eq : Inj1 = pair 1.
apply (func_ext set set).
let x.
apply (eq_sym set).
prove 1 :+: x = Inj1 x.
exact (Inj1_setsum_1L x).
Qed.

(* Treasure "19WmxEXL1KbokmxadvHjcZVTC2KrWiRvaZ" *)
Theorem pairI0 : forall X Y x, x :e X -> pair 0 x :e pair X Y.
rewrite <- Inj0_pair_0_eq.
exact Inj0_setsum.
Qed.

(* Treasure "15fQLBxAgidiKwibM8RmWJ4NDYrUU1cYnF" *)
Theorem pairI1 : forall X Y y, y :e Y -> pair 1 y :e pair X Y.
rewrite <- Inj1_pair_1_eq.
exact Inj1_setsum.
Qed.

(* Treasure "17ohZRPZmuSBGeBpwAHfqVZoEjXRPCU1DP" *)
Theorem pairE : forall X Y z, z :e pair X Y -> (exists x :e X, z = pair 0 x) \/ (exists y :e Y, z = pair 1 y).
rewrite <- Inj0_pair_0_eq.
rewrite <- Inj1_pair_1_eq.
exact setsum_Inj_inv.
Qed.

(* Treasure "1AZQuseAXHznLPZtVmewAwgN2wP4J1nfc9" *)
Theorem pairE0 : forall X Y x, pair 0 x :e pair X Y -> x :e X.
let X Y x.
assume H1: pair 0 x :e pair X Y.
prove x :e X.
apply (pairE X Y (pair 0 x) H1).
- rewrite <- Inj0_pair_0_eq.
  assume H2: exists x' :e X, Inj0 x = Inj0 x'.
  apply (exandE set (fun x' => x' :e X) (fun x' => Inj0 x = Inj0 x') H2).
  let x'.
  assume H3: x' :e X.
  assume H4: Inj0 x = Inj0 x'.
  prove x :e X.
  rewrite (Inj0_inj x x' H4).
  prove x' :e X.
  exact H3.
- rewrite <- Inj0_pair_0_eq.
  rewrite <- Inj1_pair_1_eq.
  assume H2: exists y :e Y, Inj0 x = Inj1 y.
  prove False.
  apply (exandE set (fun y => y :e Y) (fun y => Inj0 x = Inj1 y) H2).
  let y.
  assume _.
  assume H3: Inj0 x = Inj1 y.
  exact (Inj0_Inj1_neq x y H3).
Qed.

(* Treasure "1JHteYLnxoJMGS1fELR7PftnYzkfJ9k8DK" *)
Theorem pairE1 : forall X Y y, pair 1 y :e pair X Y -> y :e Y.
let X Y y.
assume H1: pair 1 y :e pair X Y.
prove y :e Y.
apply (pairE X Y (pair 1 y) H1).
- rewrite <- Inj0_pair_0_eq.
  rewrite <- Inj1_pair_1_eq.
  assume H2: exists x :e X, Inj1 y = Inj0 x.
  prove False.
  apply (exandE set (fun x => x :e X) (fun x => Inj1 y = Inj0 x) H2).
  let x.
  assume _.
  assume H3: Inj1 y = Inj0 x.
  apply (Inj0_Inj1_neq x y).
  apply (eq_sym set).
  exact H3.
- rewrite <- Inj1_pair_1_eq.
  assume H2: exists y' :e Y, Inj1 y = Inj1 y'.
  apply (exandE set (fun y' => y' :e Y) (fun y' => Inj1 y = Inj1 y') H2).
  let y'.
  assume H3: y' :e Y.
  assume H4: Inj1 y = Inj1 y'.
  prove y :e Y.
  rewrite (Inj1_inj y y' H4).
  prove y' :e Y.
  exact H3.
Qed.

(* Treasure "1DPwe7t8W78dMEbv9eyZkNpPPdR3D9hyTo" *)
Theorem pairEq : forall X Y z, z :e pair X Y <-> (exists x :e X, z = pair 0 x) \/ (exists y :e Y, z = pair 1 y).
let X Y z. apply iffI.
- exact (pairE X Y z).
- rewrite <- Inj0_pair_0_eq.
  rewrite <- Inj1_pair_1_eq.
  assume H1: (exists x, x :e X /\ z = Inj0 x) \/ (exists y, y :e Y /\ z = Inj1 y).
  prove z :e pair X Y.
  prove z :e X :+: Y.
  apply H1.
  + assume H2: exists x :e X, z = Inj0 x.
    apply (exandE set (fun x => x :e X) (fun x => z = Inj0 x) H2).
    let x.
    assume H3: x :e X.
    assume H4: z = Inj0 x.
    rewrite H4.
    prove Inj0 x :e X :+: Y.
    exact (Inj0_setsum X Y x H3).
  + assume H2: exists y :e Y, z = Inj1 y.
    apply (exandE set (fun y => y :e Y) (fun y => z = Inj1 y) H2).
    let y.
    assume H3: y :e Y.
    assume H4: z = Inj1 y.
    rewrite H4.
    prove Inj1 y :e X :+: Y.
    exact (Inj1_setsum X Y y H3).
Qed.

(* Treasure "1BWWTbT9oD7nTEqc8Yo68NCQic6XXVzbrr" *)
Theorem pairSubq : forall X Y W Z, X c= W -> Y c= Z -> pair X Y c= pair W Z.
let X Y W Z.
assume H1: X c= W.
assume H2: Y c= Z.
let u.
assume H3: u :e pair X Y.
apply (pairE X Y u H3).
- assume H4: exists x :e X, u = pair 0 x.
  apply (exandE set (fun x => x :e X) (fun x => u = pair 0 x) H4).
  let x.
  assume H5: x :e X.
  assume H6: u = pair 0 x.
  prove u :e pair W Z.
  rewrite H6.
  prove pair 0 x :e pair W Z.
  apply pairI0.
  prove x :e W.
  exact (H1 x H5).
- assume H4: exists y :e Y, u = pair 1 y.
  apply (exandE set (fun y => y :e Y) (fun y => u = pair 1 y) H4).
  let y.
  assume H5: y :e Y.
  assume H6: u = pair 1 y.
  prove u :e pair W Z.
  rewrite H6.
  prove pair 1 y :e pair W Z.
  apply pairI1.
  prove y :e Z.
  exact (H2 y H5).
Qed.

(* Treasure "1GsCXRS8FPuuphSNm8EkKqGGiYHK4uDuj8" *)
Theorem proj0I : forall w u:set, pair 0 u :e w -> u :e proj0 w.
rewrite <- Inj0_pair_0_eq.
let w u.
assume H1: Inj0 u :e w.
prove u :e {Unj z|z :e w, exists x:set, Inj0 x = z}.
rewrite <- (Unj_Inj0_eq u).
prove Unj (Inj0 u) :e {Unj z|z :e w, exists x:set, Inj0 x = z}.
apply (ReplSepI w (fun z => exists x:set, Inj0 x = z) Unj (Inj0 u)).
- prove Inj0 u :e w.
  exact H1.
- prove exists x, Inj0 x = Inj0 u.
  witness u.
  apply (eqI set).
Qed.

(* Treasure "1CZjBLDQpCuPKv7r6LyQyoXar3C6LFNtY4" *)
Theorem proj0E : forall w u:set, u :e proj0 w -> pair 0 u :e w.
let w u.
assume H1: u :e {Unj z|z :e w, exists x:set, Inj0 x = z}.
rewrite <- Inj0_pair_0_eq.
prove Inj0 u :e w.
apply (ReplSepE2 w (fun z => exists x:set, Inj0 x = z) Unj u H1).
let z.
assume H2: z :e w.
assume H3: exists x, Inj0 x = z.
assume H4: u = Unj z.
apply H3.
let x.
assume H5: Inj0 x = z.
prove Inj0 u :e w.
rewrite H4.
prove Inj0 (Unj z) :e w.
rewrite <- H5.
prove Inj0 (Unj (Inj0 x)) :e w.
rewrite Unj_Inj0_eq.
prove Inj0 x :e w.
rewrite H5.
exact H2.
Qed.

(* Treasure "1Mxa5pHgc6nkgXBKKPkc7QXdNLTfMuuphc" *)
Theorem proj1I : forall w u:set, pair 1 u :e w -> u :e proj1 w.
rewrite <- Inj1_pair_1_eq.
let w u.
assume H1: Inj1 u :e w.
prove u :e {Unj z|z :e w, exists y:set, Inj1 y = z}.
rewrite <- (Unj_Inj1_eq u).
prove Unj (Inj1 u) :e {Unj z|z :e w, exists y:set, Inj1 y = z}.
apply (ReplSepI w (fun z => exists y:set, Inj1 y = z) Unj (Inj1 u)).
- prove Inj1 u :e w.
  exact H1.
- prove exists y, Inj1 y = Inj1 u.
  witness u.
  apply (eqI set).
Qed.

(* Treasure "17SRU45xGRAEuVTXHf8QFTr5Qa1TG2fsFu" *)
Theorem proj1E : forall w u:set, u :e proj1 w -> pair 1 u :e w.
let w u.
assume H1: u :e {Unj z|z :e w, exists y:set, Inj1 y = z}.
rewrite <- Inj1_pair_1_eq.
prove Inj1 u :e w.
apply (ReplSepE2 w (fun z => exists y:set, Inj1 y = z) Unj u H1).
let z.
assume H2: z :e w.
assume H3: exists y, Inj1 y = z.
assume H4: u = Unj z.
apply H3.
let y.
assume H5: Inj1 y = z.
prove Inj1 u :e w.
rewrite H4.
prove Inj1 (Unj z) :e w.
rewrite <- H5.
prove Inj1 (Unj (Inj1 y)) :e w.
rewrite Unj_Inj1_eq.
prove Inj1 y :e w.
rewrite H5.
exact H2.
Qed.

(* Treasure "16fziJuTeJ98hrdYxVisbAqX3QYhiVtRmF" *)
Theorem proj0_pair_eq : forall X Y:set, proj0 (pair X Y) = X.
let X Y. apply set_ext.
- prove proj0 (pair X Y) c= X.
  let u.
  assume H1: u :e proj0 (pair X Y).
  prove u :e X.
  apply (pairE0 X Y u).
  prove pair 0 u :e pair X Y.
  exact (proj0E (pair X Y) u H1).
- prove X c= proj0 (pair X Y).
  let u.
  assume H1: u :e X.
  prove u :e proj0 (pair X Y).
  apply proj0I.
  prove pair 0 u :e pair X Y.
  apply pairI0.
  prove u :e X.
  exact H1.
Qed.

(* Treasure "1AURU8Ea1E82HjRypsQ3cbCWwfQP8VoneX" *)
Theorem proj1_pair_eq : forall X Y:set, proj1 (pair X Y) = Y.
let X Y. apply set_ext.
- prove proj1 (pair X Y) c= Y.
  let u.
  assume H1: u :e proj1 (pair X Y).
  prove u :e Y.
  apply (pairE1 X Y u).
  prove pair 1 u :e pair X Y.
  exact (proj1E (pair X Y) u H1).
- prove Y c= proj1 (pair X Y).
  let u.
  assume H1: u :e Y.
  prove u :e proj1 (pair X Y).
  apply proj1I.
  prove pair 1 u :e pair X Y.
  apply pairI1.
  prove u :e Y.
  exact H1.
Qed.

(* Treasure "17LUmAvonQ29ADanGaTLZR8m8jYLUyCiub" *)
Theorem pair_inj : forall x y w z:set, pair x y = pair w z -> x = w /\ y = z.
let x y w z.
assume H1: pair x y = pair w z.
prove x = w /\ y = z.
apply andI.
- prove x = w.
  rewrite <- (proj0_pair_eq x y).
  rewrite <- (proj0_pair_eq w z).
  prove proj0 (pair x y) = proj0 (pair w z).
  rewrite H1.
  prove proj0 (pair w z) = proj0 (pair w z).
  apply (eqI set).
- prove y = z.
  rewrite <- (proj1_pair_eq x y).
  rewrite <- (proj1_pair_eq w z).
  prove proj1 (pair x y) = proj1 (pair w z).
  rewrite H1.
  prove proj1 (pair w z) = proj1 (pair w z).
  apply (eqI set).
Qed.

(* Treasure "13Kn7VYCAekh3TEyFtZmDTfFaGMniNan98" *)
Theorem pair_eta_Subq_proj : forall w, pair (proj0 w) (proj1 w) c= w.
let w u.
assume H1: u :e pair (proj0 w) (proj1 w).
apply (pairE (proj0 w) (proj1 w) u H1).
- assume H2: exists x :e proj0 w, u = pair 0 x.
  apply (exandE set (fun x => x :e proj0 w) (fun x => u = pair 0 x) H2).
  let x.
  assume H3: x :e proj0 w.
  assume H4: u = pair 0 x.
  prove u :e w.
  rewrite H4.
  prove pair 0 x :e w.
  exact (proj0E w x H3).
- assume H2: exists y :e proj1 w, u = pair 1 y.
  apply (exandE set (fun y => y :e proj1 w) (fun y => u = pair 1 y) H2).
  let y.
  assume H3: y :e proj1 w.
  assume H4: u = pair 1 y.
  prove u :e w.
  rewrite H4.
  prove pair 1 y :e w.
  exact (proj1E w y H3).
Qed.
