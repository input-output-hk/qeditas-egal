(* Title "Socrates Introductory Example" *)
(* Author "Chad E. Brown" *)

Section Socrates.

Variable A:SType.
Variable Man:A->prop.
Variable Mortal:A->prop.
Hypothesis ManMortal: forall x:A, Man x -> Mortal x.
Variable Socrates:A.
Hypothesis SocratesMan: Man Socrates.
(* Treasure "1CQpAnWKx8qKN5ciVLvahsDu7Lun19Wh88" *)
Theorem SocratesMortal: Mortal Socrates.
Admitted.

End Socrates.

