(* Title "Basic Set Operations" *)
(* Author "Chad E. Brown" *)

(* Salt "cpsZu1tVzsnNo79P" *)

(* Treasure "1FAXHyauGA43yffrZc8NCD7XSPhGeyhSS7" *)
Theorem binunion_asso:forall X Y Z:set, X :\/: (Y :\/: Z) = (X :\/: Y) :\/: Z.
Admitted.

(* Treasure "16tAsKR8ReeYiAnE7YL1FBq4JZFEBUJdYW" *)
Lemma binunion_com_Subq:forall X Y:set, X :\/: Y c= Y :\/: X.
Admitted.

(* Treasure "1BjCxS2wSTzjNfDfimqdEhdKGfoCtS88UT" *)
Theorem binunion_com:forall X Y:set, X :\/: Y = Y :\/: X.
Admitted.

(* Treasure "15is2jrcPrUbCBaYjRmKf1MX1K5gZWP2vn" *)
Theorem binunion_idl:forall X:set, Empty :\/: X = X.
Admitted.

(* Treasure "14HY65Y2tcEQV7nznLc7byJEr5zreTYBpB" *)
Theorem binunion_idr:forall X:set, X :\/: Empty = X.
Admitted.

(* Treasure "15NEwaEgcv4NRFo72R44j2dg8EvoCPfzuQ" *)
Theorem binunion_idem:forall X:set, X :\/: X = X.
Admitted.

(* Treasure "1KzskJgDHJgnPE92xQduBbf5vj2vWYEWqs" *)
Theorem binunion_Subq_1: forall X Y:set, X c= X :\/: Y.
Admitted.

(* Treasure "1M7fGdoHnewfBYLdszmkeruNMr8JCwxCLZ" *)
Theorem binunion_Subq_2: forall X Y:set, Y c= X :\/: Y.
Admitted.

(* Treasure "12sd19Qn3M6Tn4F2WisoF7fiB9tdW8pqC2" *)
Theorem binunion_Subq_min: forall X Y Z:set, X c= Z -> Y c= Z -> X :\/: Y c= Z.
Admitted.

(* Treasure "1KjYfZzvvPsNcNegCjNZLvek6x2SeNtdzk" *)
Theorem Subq_binunion_eq:forall X Y, (X c= Y) = (X :\/: Y = Y).
Admitted.

(* Treasure "1G2AXb9jVynX77J3ryJU5tfMWe49i5u4Ax" *)
Theorem binunion_nIn_I : forall X Y z:set, z /:e X -> z /:e Y -> z /:e X :\/: Y.
Admitted.

(* Treasure "18s1FfoZWLPv3w6Kew2mwfg6tS9wumjR4m" *)
Theorem binunion_nIn_E : forall X Y z:set, z /:e X :\/: Y -> z /:e X /\ z /:e Y.
Admitted.

Definition binintersect:set->set->set
:= fun X Y => {x :e X |x :e Y}.

(* Unicode :/\: "2229" *)
Infix :/\: 340 left := binintersect.

(* Treasure "19vbaw2jpKHz96xUTgBLh8Fi8UMquW7ArR" *)
Theorem binintersectI:forall X Y z, z :e X -> z :e Y -> z :e X :/\: Y.
Admitted.

(* Treasure "1Ed72QQVsnbTnfX4uugz47ZPhnrKk8N9kA" *)
Theorem binintersectE:forall X Y z, z :e X :/\: Y -> z :e X /\ z :e Y.
Admitted.

(* Treasure "1FBJHd2KwUkt2J6jBUWp1ioNNy3FvGgkF7" *)
Theorem binintersectE1:forall X Y z, z :e X :/\: Y -> z :e X.
Admitted.

(* Treasure "1Bfr7Noah7VP8veWpHCsYYUAZms6hfX9UJ" *)
Theorem binintersectE2:forall X Y z, z :e X :/\: Y -> z :e Y.
Admitted.

(* Treasure "17yKg7a8pXus5gYGarypnJy46P5uesP7X2" *)
Theorem binintersect_Subq_1:forall X Y:set, X :/\: Y c= X.
Admitted.

(* Treasure "1Cfs35CETziaAq66LtK8RfAZVZ8RSkcsUH" *)
Theorem binintersect_Subq_2:forall X Y:set, X :/\: Y c= Y.
Admitted.

(* Treasure "1Ao1G24ZZk2tn9x1FpJDajFZBj7Tsb5vCY" *)
Theorem binintersect_Subq_max:forall X Y Z:set, Z c= X -> Z c= Y -> Z c= X :/\: Y.
Admitted.

(* Treasure "1AUt4SchvjZywUxDyzSHhB4SDCppYczvmv" *)
Theorem binintersect_asso:forall X Y Z:set, X :/\: (Y :/\: Z) = (X :/\: Y) :/\: Z.
Admitted.

(* Treasure "1LTXzfhr5c6s2ck6XyZ37V6ucBRMzduMua" *)
Lemma binintersect_com_Subq: forall X Y:set, X :/\: Y c= Y :/\: X.
Admitted.

(* Treasure "1HcDGV7tDUKLuA6ppNyUqFusQyQY2W1gMn" *)
Theorem binintersect_com: forall X Y:set, X :/\: Y = Y :/\: X.
Admitted.

(* Treasure "1CdUYQwG4fFtqJgLb27HWrhWrsWo2qgtDV" *)
Theorem binintersect_annil:forall X:set, Empty :/\: X = Empty.
Admitted.

(* Treasure "1NSsYkcZ8rkNyz4NsKK2GN7ZtM7wkRxoRr" *)
Theorem binintersect_annir:forall X:set, X :/\: Empty = Empty.
Admitted.

(* Treasure "1GGWxHZF7KLF8rt4FrNQBqSTApS2VkGcFC" *)
Theorem binintersect_idem:forall X:set, X :/\: X = X.
Admitted.

(* Treasure "1Kse6Q2gsFHBjth3NogdURHNKK3oa5C5Ee" *)
Theorem binintersect_binunion_distr:forall X Y Z:set, X :/\: (Y :\/: Z) = X :/\: Y :\/: X :/\: Z.
Admitted.

(* Treasure "15pXmfRFgXTgQY5yBiiabc1dcK5e3eS18g" *)
Theorem binunion_binintersect_distr:forall X Y Z:set, X :\/: Y :/\: Z = (X :\/: Y) :/\: (X :\/: Z).
Admitted.

(* Treasure "1Bmj8L82Ys6Uhz1mFx4ZfoocHWcY9UErm" *)
Theorem Subq_binintersection_eq:forall X Y:set, (X c= Y) = (X :/\: Y = X).
Admitted.

(* Treasure "1wMd3W1dzqTPZthXTxLFkKwuMm1KUGmcw" *)
Theorem binintersect_nIn_I1 : forall X Y z:set, z /:e X -> z /:e X :/\: Y.
Admitted.

(* Treasure "14pt37zPvN2eVGzfK24a3gX2c8G43whMKY" *)
Theorem binintersect_nIn_I2 : forall X Y z:set, z /:e Y -> z /:e X :/\: Y.
Admitted.

(* Treasure "1FRTFyvMmnYVbrFq2jg91qYN9DMkJ2oWPf" *)
Theorem binintersect_nIn_E : forall X Y z:set, z /:e X :/\: Y -> z /:e X \/ z /:e Y.
Admitted.

Definition setminus:set->set->set
:= fun X Y => Sep X (fun x => x /:e Y).

(* Unicode :\: "2216" *)
Infix :\: 350 := setminus.

(* Treasure "1CV1jEfaZxHXgM74c3CbiNsbZMQiEXt5rV" *)
Theorem setminusI:forall X Y z, (z :e X) -> (z /:e Y) -> z :e X :\: Y.
Admitted.

(* Treasure "1LJENy1W9C9J82ac7cKMpJysi2ciN2xazG" *)
Theorem setminusE:forall X Y z, (z :e X :\: Y) -> z :e X /\ z /:e Y.
Admitted.

(* Treasure "1LPESc4TH92KKZxTh8LwUmLtoCw6oCijzq" *)
Theorem setminusE1:forall X Y z, (z :e X :\: Y) -> z :e X.
Admitted.

(* Treasure "1E9ekP6F4txohhA6WSBsfo2tpSe8CXXUzk" *)
Theorem setminusE2:forall X Y z, (z :e X :\: Y) -> z /:e Y.
Admitted.

(* Treasure "1CuY3wr3wiizfvgvZ9SEc3hCsVQ3is7vCp" *)
Theorem setminus_Subq:forall X Y:set, X :\: Y c= X.
Admitted.

(* Treasure "15w7abucBfiMpmM1axGcehHkNZ6HrcRvBU" *)
Theorem setminus_Subq_contra:forall X Y Z:set, Z c= Y -> X :\: Y c= X :\: Z.
Admitted.

(* Treasure "1EtP9fpwesxXtaFiLYxd4GLPe5Do7iLswE" *)
Theorem setminus_nIn_I1: forall X Y z, z /:e X -> z /:e X :\: Y.
Admitted.

(* Treasure "1LLktJ5AKCrEDQdzv56zoJkuobyKscXWh8" *)
Theorem setminus_nIn_I2: forall X Y z, z :e Y -> z /:e X :\: Y.
Admitted.

(* Treasure "17oVb9Fish8sS9uA1ut6Kx4rqRFiEM65Ks" *)
Theorem setminus_nIn_E: forall X Y z, z /:e X :\: Y -> z /:e X \/ z :e Y.
Admitted.

(* Treasure "1FzVrBobCj47CtedsXEFpYWxbUDmTfDDNS" *)
Theorem setminus_selfannih:forall X:set, (X :\: X) = Empty.
Admitted.

(* Treasure "13Xcff8j388o12geyrzRYzPPinVVdvgvzy" *)
Theorem setminus_binintersect:forall X Y Z:set, X :\: Y :/\: Z = (X :\: Y) :\/: (X :\: Z).
Admitted.

(* Treasure "19VMRaaaNyWyTDwSw7b8xzG11NZeoDm1TA" *)
Theorem setminus_binunion:forall X Y Z:set, X :\: Y :\/: Z = (X :\: Y) :\: Z.
Admitted.

(* Treasure "17be9AXEJm5y7SouidTrYJ5SJLga6sH422" *)
Theorem binintersect_setminus:forall X Y Z:set, (X :/\: Y) :\: Z = X :/\: (Y :\: Z).
Admitted.

(* Treasure "1ApFQkdFfTySowyHEcpHugF5Lf2B3kUyBC" *)
Theorem binunion_setminus:forall X Y Z:set, X :\/: Y :\: Z = (X :\: Z) :\/: (Y :\: Z).
Admitted.

(* Treasure "1KSm1nJCFSfXNruLZKDdpgFaBRcvXmk5Ex" *)
Theorem setminus_setminus:forall X Y Z:set, X :\: (Y :\: Z) = (X :\: Y) :\/: (X :/\: Z).
Admitted.

(* Treasure "1Eua9anWdhx1uT5ymmASNB9d6TDRgxAZFA" *)
Theorem setminus_annil:forall X:set, Empty :\: X = Empty.
Admitted.

(* Treasure "15Sn21n7ryrv4yN2acweLXzJUAD9m8j6ys" *)
Theorem setminus_idr:forall X:set, X :\: Empty = X.
Admitted.
