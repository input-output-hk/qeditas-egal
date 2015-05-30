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
Admitted.

(* Treasure "1AwwFxbJgHNtz5pfQhMeBfEADuVUaWK5rC" *)
Theorem ordinal_In_TransSet : forall alpha:set, ordinal alpha -> forall beta :e alpha, TransSet beta.
Admitted.

(* Treasure "1CbQVEDG5Rrsxz5TmzH6XBMtcekcLzxi2T" *)
Theorem ordinal_Empty : ordinal Empty.
Admitted.

(* Treasure "1KVzQHmEg1Ci9D6yKoMHsCGPqpouCqrbc2" *)
Theorem ordinal_Hered : forall alpha:set, ordinal alpha -> forall beta :e alpha, ordinal beta.
Admitted.

(* Treasure "16BcE3SvvUugf2s7hHU4QWAUDTdTGgVSSK" *)
Theorem ordinal_ind : forall p:set->prop, 
(forall alpha, ordinal alpha -> (forall beta :e alpha, p beta) -> p alpha)
->
forall alpha, ordinal alpha -> p alpha.
Admitted.

(* Treasure "162KmhTK6ScFBnk4Dvd9jiiHf8nJqgiWXD" *)
Theorem TransSet_ordsucc : forall X:set, TransSet X -> TransSet (ordsucc X).
Admitted.

(* Treasure "1AmSq7wUzSUEWjExYma9QYR8qUP5n2Hj64" *)
Theorem ordinal_ordsucc : forall alpha:set, ordinal alpha -> ordinal (ordsucc alpha).
Admitted.

(* Treasure "1AgCLMqynP5KDaF1gSHdzjMZX7mjiHN1dN" *)
Theorem nat_p_ordinal : forall n:set, nat_p n -> ordinal n.
Admitted.

(* Treasure "1Chj5ger4G6WFuiCbqfWmmuKBZUPrH8u6d" *)
Theorem omega_TransSet : TransSet omega.
Admitted.

(* Treasure "13D4LgCj56ETthUqcPcvEbP1amvRrqSUgK" *)
Theorem omega_ordinal : ordinal omega.
Admitted.

(* Treasure "1A2P9cem1AQQbMwonSAuW6hCrgwTsQXxVW" *)
Theorem TransSet_ordsucc_In_Subq : forall X:set, TransSet X -> forall x :e X, ordsucc x c= X.
Admitted.

(* Treasure "1Lzy1bmgxqw3KCBxtR6rXsgck8v2uaRhgR" *)
Theorem ordinal_ordsucc_In_Subq : forall alpha, ordinal alpha -> forall beta :e alpha, ordsucc beta c= alpha.
Admitted.

(* Treasure "1Es7PU3HBZvWGrFUbPuoC718dCmBHYHqwm" *)
Theorem ordinal_trichotomy_or : forall alpha beta:set, ordinal alpha -> ordinal beta -> alpha :e beta \/ alpha = beta \/ beta :e alpha.
Admitted.

(* Treasure "1zLABNcEyk91BzSAUQqh5k1vUY7AWtHUv" *)
Theorem ordinal_trichotomy : forall alpha beta:set,
 ordinal alpha -> ordinal beta -> exactly1of3 (alpha :e beta) (alpha = beta) (beta :e alpha).
Admitted.

(* Treasure "135E8xcgLnkiy7kQbWRroRvBdoiVTttyKe" *)
Theorem ordinal_In_Or_Subq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha :e beta \/ beta c= alpha.
Admitted.

(* Treasure "1G8TVsrLW2SdMWm4rCx1abKjD4vZWXdyvV" *)
Theorem ordinal_linear : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta \/ beta c= alpha.
Admitted.
