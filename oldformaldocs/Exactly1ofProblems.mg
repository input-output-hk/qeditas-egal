(* Title "Exactly 1 of 2 or 3" *)
(* Author "Chad E. Brown" *)

(* Salt "2JCgFSwTWUd4YsNAm" *)

Definition exactly1of2 : prop->prop->prop := fun A B:prop =>
A /\ ~B \/ ~A /\ B.

(* Treasure "1Ngk5hUcUanPpfYJGtUYrJftYz4UbcsDYk" *)
Theorem exactly1of2_I1 : forall A B:prop, A -> ~B -> exactly1of2 A B.
Admitted.

(* Treasure "17ENfuWW6dJaAys8T6CHn5EJ8q7MCFNNqP" *)
Theorem exactly1of2_I2 : forall A B:prop, ~A -> B -> exactly1of2 A B.
Admitted.

(* Treasure "15m5C8CXMKn9b5sNWMDubGVKEffJ7izgPu" *)
Theorem exactly1of2_impI1 : forall A B:prop, (A -> ~B) -> (~A -> B) -> exactly1of2 A B.
Admitted.

(* Treasure "1D4ctW1X4JFj1jrvgs7ENYY61J5Hsybk3W" *)
Theorem exactly1of2_impI2 : forall A B:prop, (B -> ~A) -> (~B -> A) -> exactly1of2 A B.
Admitted.

(* Treasure "1AzUH2iw45WQH16AxXNRT41Yy4HJPiSRL3" *)
Theorem exactly1of2_E : forall A B:prop, exactly1of2 A B ->
forall p:prop,
(A -> ~B -> p) ->
(~A -> B -> p) ->
p.
Admitted.

(* Treasure "1JVuL5cX39gfdBqy899hjyA4sPv6Tn1X25" *)
Theorem exactly1of2_or : forall A B:prop, exactly1of2 A B -> A \/ B.
Admitted.

(* Treasure "18UPERQby1AhssjPm1LXkRPBBdqcYuFNhk" *)
Theorem exactly1of2_impn12 : forall A B:prop, exactly1of2 A B -> A -> ~B.
Admitted.

(* Treasure "1DqBixBaTDcuubBDXXbt27jg8p7SLoLQT" *)
Theorem exactly1of2_impn21 : forall A B:prop, exactly1of2 A B -> B -> ~A.
Admitted.

(* Treasure "1NjrKaziAavHY8sCgT2Usjn7uS8J1GwFfT" *)
Theorem exactly1of2_nimp12 : forall A B:prop, exactly1of2 A B -> ~A -> B.
Admitted.

(* Treasure "1MZTr9RVajcVz1MrU1Dx8wXDGbvAEgmEAQ" *)
Theorem exactly1of2_nimp21 : forall A B:prop, exactly1of2 A B -> ~B -> A.
Admitted.

Definition exactly1of3 : prop->prop->prop->prop := fun A B C:prop =>
exactly1of2 A B /\ ~C \/ ~A /\ ~B /\ C.

(* Treasure "1Kxio1Ld88ZEw9hjfpnxKpicgcrTSLtM2H" *)
Theorem exactly1of3_I1 : forall A B C:prop, A -> ~B -> ~C -> exactly1of3 A B C.
Admitted.

(* Treasure "19GPpKJpct4jR2BcsjGsyremY3HCHUUmE6" *)
Theorem exactly1of3_I2 : forall A B C:prop, ~A -> B -> ~C -> exactly1of3 A B C.
Admitted.

(* Treasure "1CxWsnwRjbXQ9pV9kSMYFoC8dnGRECSXay" *)
Theorem exactly1of3_I3 : forall A B C:prop, ~A -> ~B -> C -> exactly1of3 A B C.
Admitted.

(* Treasure "1JhFJvUbsBdjjncfHUn3ykT3zLxV7PWsPx" *)
Theorem exactly1of3_impI1 : forall A B C:prop, (A -> ~B) -> (A -> ~C) -> (B -> ~C) -> (~A -> B \/ C) -> exactly1of3 A B C.
Admitted.

(* Treasure "1HCTnn8g2eVphqk4r9khm3kLc3FYd4fu3Q" *)
Theorem exactly1of3_impI2 : forall A B C:prop, (B -> ~A) -> (B -> ~C) -> (A -> ~C) -> (~B -> A \/ C) -> exactly1of3 A B C.
Admitted.

(* Treasure "1PeM82JknSSUhGvqrUh1FawhhMTjXQQQAh" *)
Theorem exactly1of3_impI3 : forall A B C:prop, (C -> ~A) -> (C -> ~B) -> (A -> ~B) -> (~A -> B) -> exactly1of3 A B C.
Admitted.

(* Treasure "1D5NWJfPbedMJWhho4Y4F9dPvXqSSqKd4f" *)
Theorem exactly1of3_E : forall A B C:prop, exactly1of3 A B C ->
forall p:prop,
(A -> ~B -> ~C -> p) ->
(~A -> B -> ~C -> p) ->
(~A -> ~B -> C -> p) ->
p.
Admitted.

(* Treasure "19Aguc33xHmCPpirKYV48aDE6Gt7T9ib4a" *)
Theorem exactly1of3_or : forall A B C:prop, exactly1of3 A B C -> A \/ B \/ C.
Admitted.

(* Treasure "1MpMHDuoBnaZWoQJJUyJWJea6FGUqR2pub" *)
Theorem exactly1of3_impn12 : forall A B C:prop, exactly1of3 A B C -> A -> ~B.
Admitted.

(* Treasure "1PMKeXzDodWQvokG5BRxEX7k33q4AtDNzF" *)
Theorem exactly1of3_impn13 : forall A B C:prop, exactly1of3 A B C -> A -> ~C.
Admitted.

(* Treasure "1LtsfzKweJFfCjS8JoM7ENDb6TkopHcCo" *)
Theorem exactly1of3_impn21 : forall A B C:prop, exactly1of3 A B C -> B -> ~A.
Admitted.

(* Treasure "1Q456gCpsXMsHPiWPzm9xXBp7S5P4uRQvW" *)
Theorem exactly1of3_impn23 : forall A B C:prop, exactly1of3 A B C -> B -> ~C.
Admitted.

(* Treasure "1BRnbVbafPB2wE8fRHfWVAqHm2dGyVYois" *)
Theorem exactly1of3_impn31 : forall A B C:prop, exactly1of3 A B C -> C -> ~A.
Admitted.

(* Treasure "1Djrh6uPrgzTG18DPAXnmGZwkxR36Kyek" *)
Theorem exactly1of3_impn32 : forall A B C:prop, exactly1of3 A B C -> C -> ~B.
Admitted.

(* Treasure "1AwZvXQG375RMowwTMSewCdVh7ZLZhCpZ" *)
Theorem exactly1of3_nimp1 : forall A B C:prop, exactly1of3 A B C -> ~A -> B \/ C.
Admitted.

(* Treasure "18j5JxBGLBNDS4Ye7Fq6ahsMRvCxfNaqip" *)
Theorem exactly1of3_nimp2 : forall A B C:prop, exactly1of3 A B C -> ~B -> A \/ C.
Admitted.

(* Treasure "1MxWFrrEidB9NvueJNwtsaPcS5Nuth12NP" *)
Theorem exactly1of3_nimp3 : forall A B C:prop, exactly1of3 A B C -> ~C -> A \/ B.
Admitted.
