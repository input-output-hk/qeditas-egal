(* Copyright (c) 2014 Chad E Brown *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(* Code for BIP0032 (HD Wallets) *)
(* https://en.bitcoin.it/wiki/BIP_0032 *)

open Big_int
open Secp256k1

exception Invalid

val compr : big_int * big_int -> big_int
val comprpubkey : big_int -> big_int
val big_int_of_hex_r : string -> int -> int -> big_int -> big_int
val big_int_of_hex : string -> big_int
val ripemd160num : big_int -> int -> big_int
val sha256num : big_int -> int -> big_int
val sha512num : big_int -> int -> big_int
val ckd : big_int -> big_int -> int32 -> big_int * big_int
val ckd' : big_int * big_int -> big_int -> int32 -> big_int * big_int * big_int
val master : string -> big_int * big_int
val masterhex : string -> big_int * big_int
val external_chain_privkeys : big_int -> big_int -> int32 -> int32 -> int -> big_int list * int32
val internal_chain_privkeys : big_int -> big_int -> int32 -> int32 -> int -> big_int list * int32
val external_chain_pubkeys : big_int * big_int -> big_int -> int32 -> int32 -> int -> (big_int * big_int) list * int32
val internal_chain_pubkeys : big_int * big_int -> big_int -> int32 -> int32 -> int -> (big_int * big_int) list * int32
val base58 : big_int -> string
val frombase58 : string -> big_int
val genwif : big_int -> big_int -> string
val btcwif : big_int -> string
val ltcwif : big_int -> string
val ftcwif : big_int -> string
val privkeyfromwif : string -> big_int
val genaddr : big_int * big_int -> big_int -> string
val btcaddr : big_int * big_int -> string
val ltcaddr : big_int * big_int -> string
val ftcaddr : big_int * big_int -> string
val btcfrombase58 : string -> string * string
val ltcfrombase58 : string -> string * string
val ftcfrombase58 : string -> string * string
val saltval : big_int option ref
val salt : string -> string

