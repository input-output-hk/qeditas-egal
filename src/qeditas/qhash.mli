(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Qsha256

type hashval = int32 * int32 * int32 * int32 * int32

val hash160 : string -> hashval

type addr
type payaddr
type termaddr
type docaddr

val payaddr_addr : payaddr -> addr
val termaddr_addr : termaddr -> addr
val docaddr_addr : docaddr -> addr

val payaddr_p : addr -> bool
val p2pkhaddr_p : addr -> bool
val p2shaddr_p : addr -> bool
val termaddr_p : addr -> bool
val docaddr_p : addr -> bool

val hashval_bitseq : hashval -> bool list
val addr_bitseq : addr -> bool list

val hashval_hexstring : hashval -> string
val hexstring_hashval : string -> hashval
val printhashval : hashval -> unit
val hashint32 : int32 -> hashval
val hashint64 : int64 -> hashval
val hashaddr : addr -> hashval
val hashpayaddr : payaddr -> hashval
val hashtermaddr : termaddr -> hashval
val hashdocaddr : docaddr -> hashval
val hashpair : hashval -> hashval -> hashval
val hashpubkey : md256 -> md256 -> hashval
val hashpubkeyc : int -> md256 -> hashval
val hashtag : hashval -> int32 -> hashval
val hashlist : hashval list -> hashval
val hashfold : ('a -> hashval) -> 'a list -> hashval
val ohashlist : hashval list -> hashval option
val hashopair : hashval option -> hashval option -> hashval option
val hashopair1 : hashval -> hashval option -> hashval
val hashopair2 : hashval option -> hashval -> hashval

val hashval_rev : hashval -> hashval

val seo_hashval : (int -> int -> 'a -> 'a) -> hashval -> 'a -> 'a
val sei_hashval : (int -> 'a -> int * 'a) -> 'a -> hashval * 'a
