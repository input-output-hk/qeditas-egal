(* Copyright (c) 2014 Chad E Brown *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(*** File: interpret.mli ***)
(*** Chad E Brown ***)
(*** Feb 2014 ***)

open Syntax

val verbosity : int ref
val proving : (string * int * tm * string) option ref
val prooffun :  (pf list -> pf) ref
val deltaset : string list ref
type pfstatetype =
  | PfStateGoal of tm * (string * (tp * tm option)) list * (string * tm) list
  | PfStateSep of int * bool
val pfstate : pfstatetype list ref

val fal : string ref
val eqPoly : string ref
val eqsymPoly : string ref
val eqsymPolyknown : bool ref
val eqSet : string ref
val conj : string ref
val disj : string ref
val expoly : string ref
val expolyI : string ref
val expolyIknown : bool ref
val setIn : string option ref
val setSubeq : string option ref
val setPow : string option ref
val setimplop : string option ref
val setlam : string option ref
val replop : string option ref
val sepop : string option ref
val replsepop : string option ref
val nat0 : string option ref
val natS : string option ref

val ifop : string option ref

val setenuml : string option list ref
val setenumadj : string option ref
val set_setenuml_n : int -> string -> unit

val extract_tp : atree -> string list -> tp
val extract_tm : atree
 -> ((string * int) * tp) list -> (string, ptp) Hashtbl.t -> (string * (string list -> (string * (tp * tm option)) list -> tm)) list -> string list -> (string * (tp * tm option)) list
 -> tm * tp
val check_tm : atree -> tp
 -> ((string * int) * tp) list -> (string, ptp) Hashtbl.t -> (string * (string list -> (string * (tp * tm option)) list -> tm)) list -> string list -> (string * (tp * tm option)) list
 -> tm
val extract_pf : atree
 -> ((string * int) * tp) list -> ((string * int) * tm) list
 -> (string, ptp) Hashtbl.t -> (string,ptm) Hashtbl.t
 -> (string * (string list -> (string * (tp * tm option)) list -> tm)) list
 -> (string * (string list -> (string * (tp * tm option)) list -> (string * tm) list -> pf)) list
 -> string list -> (string * (tp * tm option)) list -> (string * tm) list
 -> pf * tm
val check_pf : atree -> tm
 -> ((string * int) * tp) list -> ((string * int) * tm) list
 -> (string, ptp) Hashtbl.t -> (string,ptm) Hashtbl.t
 -> (string * (string list -> (string * (tp * tm option)) list -> tm)) list
 -> (string * (string list -> (string * (tp * tm option)) list -> (string * tm) list -> pf)) list
 -> string list -> (string * (tp * tm option)) list -> (string * tm) list
 -> pf
