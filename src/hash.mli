(* Copyright (c) 2014 Chad E Brown *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(*** Chad E Brown ***)
(*** August 2013 ***)

open Big_int

val sha256 : string -> big_int
val sha256file : string -> string

