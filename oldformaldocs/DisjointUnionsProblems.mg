(* Title "Disjoint Unions" *)
(* Author "Chad E. Brown" *)

(* Salt "3HmtMxzQo7ZHzs1du" *)

(*** Injection of set into itself that will correspond to x |-> (1,x) after pairing is defined. ***)
Definition Inj1 : set -> set := In_rec (fun X f => {0} :\/: {f x|x :e X}).

(* Treasure "1HLkfW5thtfXVwKkkhtRJDitG45kK3MQD8" *)
Theorem Inj1_eq : forall X:set, Inj1 X = {0} :\/: {Inj1 x|x :e X}.
Admitted.

(* Treasure "1A6S9UY8oeS4PkTuB1r31DZQP8HDUhRKcr" *)
Theorem Inj1I1 : forall X:set, 0 :e Inj1 X.
Admitted.

(* Treasure "1CudP163WnT32jWcWQb9aMbRFxmABDmyFz" *)
Theorem Inj1I2 : forall X x:set, x :e X -> Inj1 x :e Inj1 X.
Admitted.

(* Treasure "18pmbnh5i6HZzCDfXTxGjAd25ULSqzPHii" *)
Theorem Inj1E : forall X y:set, y :e Inj1 X -> y = 0 \/ exists x :e X, y = Inj1 x.
Admitted.

(* Treasure "1P23aisnDCUcqHfQH5rAm1bwvW2GtvL6sU" *)
Theorem Inj1NE1 : forall x:set, Inj1 x <> 0.
Admitted.

(* Treasure "1HrtXSZEfTTbmZ4fzTYJpmA62ibLdF1VwQ" *)
Theorem Inj1NE2 : forall x:set, Inj1 x /:e {0}.
Admitted.

(*** Injection of set into itself that will correspond to x |-> (0,x) after pairing is defined. ***)
Definition Inj0 : set -> set := fun X => {Inj1 x|x :e X}.

(* Treasure "13TQfEqNYkvdRsXGeKirZCrJVbYapZPqxS" *)
Theorem Inj0I : forall X x:set, x :e X -> Inj1 x :e Inj0 X.
Admitted.

(* Treasure "1KFmGQymRZPGx17jCQYagL5JNU29hMdRTV" *)
Theorem Inj0E : forall X y:set, y :e Inj0 X -> exists x:set, x :e X /\ y = Inj1 x.
Admitted.

(*** Unj : Left inverse of Inj1 and Inj0 ***)
Definition Unj : set -> set := In_rec (fun X f => {f x|x :e X :\: {0}}).

(* Treasure "17s8QQsa5jdfpScDvLv15RabX4PmUUGf52" *)
Theorem Unj_eq : forall X:set, Unj X = {Unj x|x :e X :\: {0}}.
Admitted.

(* Treasure "15EwYeGp7qwrzAifPVLy3HpzWJi5Gzp6Sq" *)
Theorem Unj_Inj1_eq : forall X:set, Unj (Inj1 X) = X.
Admitted.

(* Treasure "12M6AD6kpAeArzATizcW9ihrdSAkF3bU33" *)
Theorem Inj1_inj : forall X Y:set, Inj1 X = Inj1 Y -> X = Y.
Admitted.

(* Treasure "1K2iDYBWjXJWfHqCmzucJGdVmea8HKqpg7" *)
Theorem Unj_Inj0_eq : forall X:set, Unj (Inj0 X) = X.
Admitted.

(* Treasure "12r21GbQHLRo2FCg4FDqoa4h9BaUSEKvhv" *)
Theorem Inj0_inj : forall X Y:set, Inj0 X = Inj0 Y -> X = Y.
Admitted.

(* Treasure "1D2UGPdmGbFUPiXmWEwcjkZzykhH9afAWe" *)
Theorem Inj0_0 : Inj0 0 = 0.
Admitted.

(* Treasure "19ZzdtFoChgrwEHngpJTSCdhBvDZnJtjDE" *)
Theorem Inj0_Inj1_neq : forall X Y:set, Inj0 X <> Inj1 Y.
Admitted.

(*** setsum ***)
Definition setsum : set -> set -> set := fun X Y => {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.

(* Unicode :+: "002b" *)
Infix :+: 450 left := setsum.

(* Treasure "1Lq3DVZuTM8xJy6b7zWkkSBZK9EG6bTBaC" *)
Theorem Inj0_setsum : forall X Y x:set, x :e X -> Inj0 x :e X :+: Y.
Admitted.

(* Treasure "18ehfuaMKoafSybBroShCrHDMmpf5iqumG" *)
Theorem Inj1_setsum : forall X Y y:set, y :e Y -> Inj1 y :e X :+: Y.
Admitted.

(* Treasure "15SMGdRG9ei4J4cZSXCiQm3sRQQ98MrLcd" *)
Theorem setsum_Inj_inv : forall X Y z:set, z :e X :+: Y -> (exists x :e X, z = Inj0 x) \/ (exists y :e Y, z = Inj1 y).
Admitted.

(* Treasure "16jSPndFXwe29nb2hkzSiEUv5G5u1QUXfH" *)
Theorem Inj0_setsum_0L : forall X:set, 0 :+: X = Inj0 X.
Admitted.

(* Treasure "1KTsqNADcSsqdK1SWPbisBmKzo4VwSq4uH" *)
Theorem Inj1_setsum_1L : forall X:set, 1 :+: X = Inj1 X.
Admitted.

(* Treasure "1DqLEbpzUZG8BpQNdjKq5hSpAobp7vcfPQ" *)
Theorem nat_setsum1_ordsucc : forall n:set, nat_p n -> 1 :+: n = ordsucc n.
Admitted.

(* Treasure "18tibKdygPRy3DF5TywgVFjTQLqw35qAq4" *)
Theorem setsum_0_0 : 0 :+: 0 = 0.
Admitted.

(* Treasure "18ymN25HDWrSKUXjbCQUyTQQkaovPRGLfz" *)
Theorem setsum_1_0_1 : 1 :+: 0 = 1.
Admitted.

(* Treasure "18k1tppKmE66N2TRDCDEvsxuhmPVBReoqc" *)
Theorem setsum_1_1_2 : 1 :+: 1 = 2.
Admitted.

(* Treasure "1NYdPh3ynqCNJGmdhFdvpw9CDBt5uFUdZa" *)
Theorem setsum_mon : forall X Y W Z, X c= W -> Y c= Z -> X :+: Y c= W :+: Z.
Admitted.
