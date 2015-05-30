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
exact ManMortal Socrates SocratesMan.
Qed.

End Socrates.

(**
 All elephants are pink.
 Nellie is an elephant, therefore Nellie is pink.
 - Destiny of the Daleks (Doctor Who, 1979)
 **)
Section Nellie.

Variable A:SType.
Variable Elephant:A->prop.
Variable Pink:A->prop.
Hypothesis ElephantsPink: forall x:A, Elephant x -> Pink x.
Variable Nellie:A.
Hypothesis NellieElephant: Elephant Nellie.
(* Treasure "1CQpAnWKx8qKN5ciVLvahsDu7Lun19Wh88" *)
Theorem NelliePink: Pink Nellie.
exact ElephantsPink Nellie NellieElephant.
Qed.

End Nellie.

