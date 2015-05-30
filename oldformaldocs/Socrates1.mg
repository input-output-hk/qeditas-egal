(* Title "Socrates Introductory Example" *)
(* Author "Chad E. Brown" *)

Section Socrates.

Variable A:SType.
Variable Man:A->prop.
Variable Mortal:A->prop.
Hypothesis ManMortal: forall x:A, Man x -> Mortal x.
Variable Socrates:A.
Hypothesis SocratesMan: Man Socrates.
Theorem SocratesMortal: Mortal Socrates.
exact ManMortal Socrates SocratesMan.
Qed.

End Socrates.

