(* Title "Ordered Pairs as Sets" *)
(* Author "Chad E. Brown" *)

(* Salt "3KhxsZskpyxtXKgXx" *)

Definition pair : set -> set -> set := fun X Y => X :+: Y.

(* Treasure "1H9PSjcgfa7APtz9kDrxbaKUbAHjScqUeV" *)
Theorem pair_0_0 : pair 0 0 = 0.
Admitted.

(* Treasure "135QpZFUEv1zXV9GjKrwqYQb7kqqAeFwem" *)
Theorem pair_1_0_1 : pair 1 0 = 1.
Admitted.

(* Treasure "1R1qb8fxLbXdAPNP7xBeZ91hncJUzi6rq" *)
Theorem pair_1_1_2 : pair 1 1 = 2.
Admitted.

(* Treasure "14ww5UUj75xL5uEGzho9oaLWdH28wHdW5r" *)
Theorem nat_pair1_ordsucc : forall n:set, nat_p n -> pair 1 n = ordsucc n.
Admitted.

Definition proj0 : set -> set := fun Z => {Unj z|z :e Z, exists x:set, Inj0 x = z}.

Definition proj1 : set -> set := fun Z => {Unj z|z :e Z, exists y:set, Inj1 y = z}.

(* Treasure "12XGYjMN9peSq6VErLQ5H3vDiN8o9EY6eu" *)
Theorem Inj0_pair_0_eq : Inj0 = pair 0.
Admitted.

(* Treasure "1DQae3qEDd2YQRSTd48bXTESvKNQ55VRU3" *)
Theorem Inj1_pair_1_eq : Inj1 = pair 1.
Admitted.

(* Treasure "19WmxEXL1KbokmxadvHjcZVTC2KrWiRvaZ" *)
Theorem pairI0 : forall X Y x, x :e X -> pair 0 x :e pair X Y.
Admitted.

(* Treasure "15fQLBxAgidiKwibM8RmWJ4NDYrUU1cYnF" *)
Theorem pairI1 : forall X Y y, y :e Y -> pair 1 y :e pair X Y.
Admitted.

(* Treasure "17ohZRPZmuSBGeBpwAHfqVZoEjXRPCU1DP" *)
Theorem pairE : forall X Y z, z :e pair X Y -> (exists x :e X, z = pair 0 x) \/ (exists y :e Y, z = pair 1 y).
Admitted.

(* Treasure "1AZQuseAXHznLPZtVmewAwgN2wP4J1nfc9" *)
Theorem pairE0 : forall X Y x, pair 0 x :e pair X Y -> x :e X.
Admitted.

(* Treasure "1JHteYLnxoJMGS1fELR7PftnYzkfJ9k8DK" *)
Theorem pairE1 : forall X Y y, pair 1 y :e pair X Y -> y :e Y.
Admitted.

(* Treasure "1DPwe7t8W78dMEbv9eyZkNpPPdR3D9hyTo" *)
Theorem pairEq : forall X Y z, z :e pair X Y <-> (exists x :e X, z = pair 0 x) \/ (exists y :e Y, z = pair 1 y).
Admitted.

(* Treasure "1BWWTbT9oD7nTEqc8Yo68NCQic6XXVzbrr" *)
Theorem pairSubq : forall X Y W Z, X c= W -> Y c= Z -> pair X Y c= pair W Z.
Admitted.

(* Treasure "1GsCXRS8FPuuphSNm8EkKqGGiYHK4uDuj8" *)
Theorem proj0I : forall w u:set, pair 0 u :e w -> u :e proj0 w.
Admitted.

(* Treasure "1CZjBLDQpCuPKv7r6LyQyoXar3C6LFNtY4" *)
Theorem proj0E : forall w u:set, u :e proj0 w -> pair 0 u :e w.
Admitted.

(* Treasure "1Mxa5pHgc6nkgXBKKPkc7QXdNLTfMuuphc" *)
Theorem proj1I : forall w u:set, pair 1 u :e w -> u :e proj1 w.
Admitted.

(* Treasure "17SRU45xGRAEuVTXHf8QFTr5Qa1TG2fsFu" *)
Theorem proj1E : forall w u:set, u :e proj1 w -> pair 1 u :e w.
Admitted.

(* Treasure "16fziJuTeJ98hrdYxVisbAqX3QYhiVtRmF" *)
Theorem proj0_pair_eq : forall X Y:set, proj0 (pair X Y) = X.
Admitted.

(* Treasure "1AURU8Ea1E82HjRypsQ3cbCWwfQP8VoneX" *)
Theorem proj1_pair_eq : forall X Y:set, proj1 (pair X Y) = Y.
Admitted.

(* Treasure "17LUmAvonQ29ADanGaTLZR8m8jYLUyCiub" *)
Theorem pair_inj : forall x y w z:set, pair x y = pair w z -> x = w /\ y = z.
Admitted.

(* Treasure "13Kn7VYCAekh3TEyFtZmDTfFaGMniNan98" *)
Theorem pair_eta_Subq_proj : forall w, pair (proj0 w) (proj1 w) c= w.
Admitted.
