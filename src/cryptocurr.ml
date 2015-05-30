(* Copyright (c) 2014 Chad E Brown *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(* Code for BIP0032 (HD Wallets) *)
(* https://en.bitcoin.it/wiki/BIP_0032 *)
(* Chad E. Brown, ported from Krona Rev's Lisp code: https://github.com/kronarev/bip0032sbcl *)
(* This contains much more code than is actually needed by Egal at the moment, but it might be useful later. *)

open Big_int
open Secp256k1

exception Invalid

(* Computing compressed public keys *)

(* x,y : 256 bit ints giving a public key as a point on the elliptic curve *)
(* return compressed public key as a 258 bit int *)
let compr (x,y) =
  if oddp y then
    or_big_int (big_int_of_string "347376267711948586270712955026063723559809953996921692118372752023739388919808") x
  else
    or_big_int (big_int_of_string "231584178474632390847141970017375815706539969331281128078915168015826259279872") x

(* k : 256 bit int, private key *)
(* return corresponding compressed public key as a 258 bit int *)
let comprpubkey k =
  match smulp k _g with
  | None -> raise (Failure "Bad private key")
  | Some(x,y) -> compr(x,y)

(* Hash functions (relying on openssl) *)
(* Set the values of *openssl* in config.ml *)
let rec big_int_to_bytelist n nlen r =
  if nlen > 0 then
    big_int_to_bytelist (shift_right_towards_zero_big_int n 8) (nlen - 1) (int_of_big_int (mod_big_int n (big_int_of_string "256"))::r)
  else
    r

let int_of_hexchar c =
  match c with
  | '0' -> 0
  | '1' -> 1
  | '2' -> 2
  | '3' -> 3
  | '4' -> 4
  | '5' -> 5
  | '6' -> 6
  | '7' -> 7
  | '8' -> 8
  | '9' -> 9
  | 'A' -> 10
  | 'B' -> 11
  | 'C' -> 12
  | 'D' -> 13
  | 'E' -> 14
  | 'F' -> 15
  | 'a' -> 10
  | 'b' -> 11
  | 'c' -> 12
  | 'd' -> 13
  | 'e' -> 14
  | 'f' -> 15
  | _ -> raise (Failure "non hex char")

let rec big_int_of_hex_r h i j r =
  if i < j then
    big_int_of_hex_r h (i + 1) j (add_int_big_int (int_of_hexchar (String.get h i)) (shift_left_big_int r 4))
  else
    r

let big_int_of_hex h = big_int_of_hex_r h 0 (String.length h) zero_big_int

(* n is a number with nlen bytes. Return the 20 bit number given by ripemd160 *)
let ripemd160num n nlen =
  let (myout,myin,myerr) = Unix.open_process_full (String.concat " " [Config.openssl_exec;"dgst";"-ripemd160"]) [| |] in
  List.iter (fun b -> output_byte myin b) (big_int_to_bytelist n nlen []);
  close_out myin;
  let l = input_line myout in
  let ll = String.length l in
  ignore (Unix.close_process_full (myout,myin,myerr));
  if ll < 40 then
    raise (Failure ("bad openssl ripemd160 output: " ^ l))
  else
    big_int_of_hex_r l (ll - 40) ll zero_big_int

(* n is a number with nlen bytes. Return the 256 bit number given by sha256 *)
let sha256num n nlen =
  let (myout,myin,myerr) = Unix.open_process_full (String.concat " " [Config.openssl_exec;"dgst";"-sha256"]) [| |] in
  List.iter (fun b -> output_byte myin b) (big_int_to_bytelist n nlen []);
  close_out myin;
  let l = input_line myout in
  let ll = String.length l in
  ignore (Unix.close_process_full (myout,myin,myerr));
  if ll < 64 then
    raise (Failure ("bad openssl sha256 output: " ^ l))
  else
    big_int_of_hex_r l (ll - 64) ll zero_big_int

(* n is a number with nlen bytes. Return the 512 bit number given by sha512 *)
let sha512num n nlen =
  let (myout,myin,myerr) = Unix.open_process_full (String.concat " " [Config.openssl_exec;"dgst";"-sha512"]) [| |] in
  List.iter (fun b -> output_byte myin b) (big_int_to_bytelist n nlen []);
  close_out myin;
  let l = input_line myout in
  let ll = String.length l in
  ignore (Unix.close_process_full (myout,myin,myerr));
  if ll < 128 then
    raise (Failure ("bad openssl sha512 output: " ^ l))
  else
    big_int_of_hex_r l (ll - 128) ll zero_big_int

(* HMAC-SHA512 *)
(* keybytes : list of bytes (int) *)
(* data : big_int *)
(* datalen : int *)
(* datalen is number of bytes in data *)
(* return 512 bit int *)
let hmac_sha512b keybytes data datalen =
  let keybytesr = ref keybytes in
  let okpad = ref zero_big_int in
  let ikpad = ref zero_big_int in
  begin
    for i = 0 to 127 do
      match !keybytesr with
      | (k::kl) ->
	  okpad := add_int_big_int (k lxor 92) (shift_left_big_int !okpad 8);
	  ikpad := add_int_big_int (k lxor 54) (shift_left_big_int !ikpad 8);
	  keybytesr := kl
      | [] ->
	  okpad := add_int_big_int 92 (shift_left_big_int !okpad 8);
	  ikpad := add_int_big_int 54 (shift_left_big_int !ikpad 8)
    done;
    sha512num (or_big_int
		 (shift_left_big_int !okpad 512)
		 (sha512num
		    (or_big_int
		       (shift_left_big_int !ikpad (8 * datalen))
		       data)
		    (128 + datalen)))
      192
  end

(* for a general key and data *)
(* key data : big_int *)
(* keylen datalen : ints *)
(* keylen is number of bytes in key *)
(* datalen is number of bytes in data *)
(* return 512 bit int *)
let hmac_sha512a key keylen data datalen =
  hmac_sha512b (big_int_to_bytelist key keylen []) data datalen

(* key: 256 bit, data: 296 bit (1 + 32 + 4 bytes) *)
(* return 512 bit int *)
let hmac_sha512 key data =
  hmac_sha512a key 32 data 37

let split512 bi =
  let bil = shift_right_towards_zero_big_int bi 256 in
  let bir = and_big_int bi (big_int_of_string "115792089237316195423570985008687907853269984665640564039457584007913129639935") in
  (bil,bir)

(* Private Child Key Derivation *)
(* https://en.bitcoin.it/wiki/BIP_0032#Private_child_key_derivation *)
(* kpar,cpar : 256 bit ints, the extended private key *)
(* i : int32 *)
(* returns (ki,ci) *)
(*   where ki is the private key of child i and ci is the chain code of child i *)
(*   -- that is, (ki,ci) is the extended private key of child i *)
(* or raise Invalid *)
let ckd kpar cpar i =
  let bi =
    begin
      if (i < 0l) then (* most significant bit is set, use private derivation *)
        hmac_sha512 cpar (or_big_int (shift_left_big_int kpar 32) (or_big_int (big_int_of_string "2147483648") (big_int_of_int32 (Int32.logand i 2147483647l))))
      else
	hmac_sha512 cpar (or_big_int (shift_left_big_int (comprpubkey kpar) 32) (big_int_of_int32 i))
    end
  in
  let (bil,bir) = split512 bi in
  let ki = mod_big_int (add_big_int bil kpar) _n in
  if gt_big_int ki zero_big_int && lt_big_int bil _n then
    (ki,bir)
  else
    raise Invalid

(* Public Child Key Derivation *)
(* https://en.bitcoin.it/wiki/BIP_0032#Public_child_key_derivation *)
(* xKpar,yKpar,cpar : 256 bit ints, the extended public key *)
(* i : 32 bit int, which public child to compute *)
(* (xKpar,yKpar) : public key of parent as a point on the curve. *)
(* return xKi yKi ci *)
(*   where (xKi,yKi) is the public key of child i and ci is the chain code of child i *)
(*   -- that is, (xKi,yKi,ci) is the extended public key of child i *)
(* or raise Invalid *)
let ckd' (xKpar,yKpar) cpar i =
  if (i < 0l) then
    raise Invalid (* most significant bit is set, error since should be computing public derivation *)
  else
    begin
      let bi = hmac_sha512 cpar (or_big_int (shift_left_big_int (compr (xKpar,yKpar)) 32) (big_int_of_int32 i)) in
      let (bil,bir) = split512 bi in
      match addp (smulp bil _g) (Some(xKpar,yKpar)) with
      | Some(xKi,yKi) -> (xKi,yKi,bir)
      | None -> raise Invalid
    end

let rec big_int_of_ascii s i e r =
  if i < e then
    big_int_of_ascii s (i + 1) e (add_int_big_int (Char.code (String.get s i)) (shift_left_big_int r 8))
  else
    r

(* https://en.bitcoin.it/wiki/BIP_0032#Master_key_generation *)
(* s : seed string *)
(* return two values: I_L master secret key and I_R master chain code *)
let master s =
  let m = hmac_sha512a (big_int_of_string "20553497488036055671688750436") 12 (big_int_of_ascii s 0 (String.length s) zero_big_int) (String.length s) in
  split512 m

let masterhex s =
  let m = hmac_sha512a (big_int_of_string "20553497488036055671688750436") 12 (big_int_of_hex s) ((String.length s) lsr 1) in
  split512 m

(* https://en.bitcoin.it/wiki/BIP_0032#Specification:_Wallet_structure *)

(* priv,c : extended private key *)
(* i:int32 kstart,klen : int *)
(* Return the <=klen private keys (usually klen private keys, unless some are invalid) *)
(* The private keys are the ones with indices kstart,...,kstart+klen-1 from the external chain of account i with *)
(* extended private key priv,c. *)
let external_chain_privkeys priv c i kstart klen =
  let (privi,ci) = ckd priv c i in
  let (priv0,c0) = ckd privi ci 0l in
  let k = ref kstart in
  let r = ref [] in
  let rl = ref 0 in
  while (!rl < klen) do
    try
      let (privk,_) = ckd priv0 c0 !k in
      r := privk::!r;
      incr rl;
      k := Int32.add !k 1l
    with Invalid -> k := Int32.add !k 1l
  done;
  (List.rev !r,!k)

(* priv,c : extended private key *)
(* i:int32 kstart,klen : int *)
(* Return the <=klen private keys (usually klen private keys, unless some are invalid) *)
(* The private keys are the ones with indices kstart,...,kstart+klen-1 from the internal chain of account i with *)
(* extended private key priv,c. *)
let internal_chain_privkeys priv c i kstart klen =
  let (privi,ci) = ckd priv c i in
  let (priv1,c1) = ckd privi ci 1l in
  let k = ref kstart in
  let r = ref [] in
  let rl = ref 0 in
  while (!rl < klen) do
    try
      let (privk,_) = ckd priv1 c1 !k in
      r := privk::!r;
      incr rl;
      k := Int32.add !k 1l
    with Invalid -> k := Int32.add !k 1l
  done;
  (List.rev !r,!k)

(* x,y,c : extended public key *)
(* i,kstart,klen : int *)
(* Return the <=klen public keys (usually klen public keys, unless some are invalid) *)
(* The public keys are the ones with indices kstart,...,kstart+klen-1 from the external chain of account i with *)
(* extended public key x,y,c. *)
let external_chain_pubkeys (x,y) c i kstart klen =
  if (i < 0l) then (* most significant bit is set, error since such accounts require the extended private key *)
    raise Invalid
  else
  let (xi,yi,ci) = ckd' (x,y) c i in
  let (x0,y0,c0) = ckd' (xi,yi) ci 0l in
  let k = ref kstart in
  let r = ref [] in
  let rl = ref 0 in
  while (!rl < klen) do
    try
      let (xk,yk,_) = ckd' (x0,y0) c0 !k in
      r := (xk,yk)::!r;
      incr rl;
      k := Int32.add !k 1l
    with Invalid -> k := Int32.add !k 1l
  done;
  (List.rev !r,!k)

(* x,y,c : extended public key *)
(* i,kstart,klen : int *)
(* Return the <=klen public keys (usually klen public keys, unless some are invalid) *)
(* The public keys are the ones with indices kstart,...,kstart+klen-1 from the internal chain of account i with *)
(* extended public key x,y,c. *)
let internal_chain_pubkeys (x,y) c i kstart klen =
  if (i < 0l) then (* most significant bit is set, error since such accounts require the extended private key *)
    raise Invalid
  else
  let (xi,yi,ci) = ckd' (x,y) c i in
  let (x1,y1,c1) = ckd' (xi,yi) ci 1l in
  let k = ref kstart in
  let r = ref [] in
  let rl = ref 0 in
  while (!rl < klen) do
    try
      let (xk,yk,_) = ckd' (x1,y1) c1 !k in
      r := (xk,yk)::!r;
      incr rl;
      k := Int32.add !k 1l
    with Invalid -> k := Int32.add !k 1l
  done;
  (List.rev !r,!k)

(* base58 representation *)
let _base58strs = ["1";"2";"3";"4";"5";"6";"7";"8";"9";"A";"B";"C";"D";"E";"F";"G";"H";"J";"K";"L";"M";"N";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"]

(* c : big_int *)
(* return base58 string representation of c *)
let rec base58_rec c r =
  if gt_big_int c zero_big_int then
    let (q,m) = quomod_big_int c (big_int_of_string "58") in
    base58_rec q ((List.nth _base58strs (int_of_big_int m)) ^ r)
  else
    r

let base58 c = base58_rec c ""

let base58char_int c =
   match c with
   | '1' -> 0
   | '2' -> 1
   | '3' -> 2
   | '4' -> 3
   | '5' -> 4
   | '6' -> 5
   | '7' -> 6
   | '8' -> 7
   | '9' -> 8
   | 'A' -> 9
   | 'B' -> 10
   | 'C' -> 11
   | 'D' -> 12
   | 'E' -> 13
   | 'F' -> 14
   | 'G' -> 15
   | 'H' -> 16
   | 'J' -> 17
   | 'K' -> 18
   | 'L' -> 19
   | 'M' -> 20
   | 'N' -> 21
   | 'P' -> 22
   | 'Q' -> 23
   | 'R' -> 24
   | 'S' -> 25
   | 'T' -> 26
   | 'U' -> 27
   | 'V' -> 28
   | 'W' -> 29
   | 'X' -> 30
   | 'Y' -> 31
   | 'Z' -> 32
   | 'a' -> 33
   | 'b' -> 34
   | 'c' -> 35
   | 'd' -> 36
   | 'e' -> 37
   | 'f' -> 38
   | 'g' -> 39
   | 'h' -> 40
   | 'i' -> 41
   | 'j' -> 42
   | 'k' -> 43
   | 'm' -> 44
   | 'n' -> 45
   | 'o' -> 46
   | 'p' -> 47
   | 'q' -> 48
   | 'r' -> 49
   | 's' -> 50
   | 't' -> 51
   | 'u' -> 52
   | 'v' -> 53
   | 'w' -> 54
   | 'x' -> 55
   | 'y' -> 56
   | 'z' -> 57
   | _ -> raise (Failure "bad base58 char")

(* s : base58 string *)
(* return int representation of s *)
let rec frombase58_rec s i sl r =
  if i < sl then
    frombase58_rec s (i + 1) sl (add_int_big_int (base58char_int (String.get s i)) (mult_int_big_int 58 r))
  else
    r

let frombase58 s = frombase58_rec s 0 (String.length s) zero_big_int

(* Computation of Wallet Import Formats for Private Keys *)

(* generic wif from private key with prefix depending on the coin *)
(* k : private key, big_int *)
(* pre : prefix byte, int *)
(* return string, base58 *)
let genwif k pre =
  let k1 = or_big_int pre k in
  let sh1 = sha256num k1 33 in
  let sh2 = sha256num sh1 32 in
  let sh24 = shift_right_towards_zero_big_int sh2 224 in
  let c = or_big_int (shift_left_big_int k1 32) sh24 in
  base58 c

(* btc private key in wallet import format, btc prefix is #x80. *)
(* k : private key, big_int *)
(* return string, base58 btc wif *)
let btcwif k = genwif k (shift_left_big_int (big_int_of_int 128) 256)

(* ltc private key in wallet import format, ltc prefix is #xb0, otherwise the process is the same as btcwif *)
(* k : private key, big_int *)
(* return string, base58 ltc wif *)
let ltcwif k = genwif k (shift_left_big_int (big_int_of_int 176) 256)

(* ftc private key in wallet import format, ftc prefix is #x8e, otherwise the process is the same as btcwif *)
(* k : private key, big_int *)
(* return string, base58 ftc wif *)
let ftcwif k = genwif k (shift_left_big_int (big_int_of_int 142) 256)

(* w : wif (of btc, ltc, ftc), base58 string *)
(* return private key, big_int *)
(* Note: This doesn't check that the input was a valid wif string. *)
let privkeyfromwif w =
  and_big_int (shift_right_towards_zero_big_int (frombase58 w) 32)
    (big_int_of_string "115792089237316195423570985008687907853269984665640564039457584007913129639935")

(* Computation of addresses *)

(* Helper function to count the leading 0 bytes. btcaddr uses this. *)
let count0bytes n nlen =
  let rec count0bytes_rec bl r =
  match bl with
  | (b::br) when b = 0 -> count0bytes_rec br (r + 1)
  | _ -> r
  in
  count0bytes_rec (big_int_to_bytelist n nlen []) 0

let big4pre = shift_left_big_int (big_int_of_string "4") 512

(* (x,y) : public key (as a nonzero point on the elliptic curve) *)
(* returns btc address, base58 string *)
let btcaddr (x,y) =
  let pub = or_big_int (or_big_int big4pre (shift_left_big_int x 256)) y in
  let sh1 = sha256num pub 65 in
  let rm1 = ripemd160num sh1 32 in
  let c0 = count0bytes rm1 21 in
  let sh2 = sha256num rm1 21 in
  let sh3 = sha256num sh2 32 in
  let sh34 = shift_right_towards_zero_big_int sh3 224 in
  let a = or_big_int (shift_left_big_int rm1 32) sh34 in
  ((String.make c0 '1') ^ (base58 a))

(* generic address computation which works for ltc and ftc *)
(* (x,y) : public key (as point on the elliptic curve) *)
(* pre : prefix byte *)
let genaddr (x,y) pre =
  let pub = or_big_int (or_big_int big4pre (shift_left_big_int x 256)) y in
  let sh1 = sha256num pub 65 in
  let rm1 = ripemd160num sh1 32 in
  let rm2 = or_big_int pre rm1 in
  let sh2 = sha256num rm2 21 in
  let sh3 = sha256num sh2 32 in
  let sh34 = shift_right_towards_zero_big_int sh3 224 in
  let a = or_big_int (shift_left_big_int rm2 32) sh34 in
  base58 a

(* (x,y) : public key (as point on the elliptic curve) *)
(* return ltc address, base58 string *)
(* the first byte is #x30 for LTC *)
let ltcaddr (x,y) = genaddr (x,y) (shift_left_big_int (big_int_of_int 48) 160)

(* (x,y) : public key (as point on the elliptic curve) *)
(* return ftc address, base58 string *)
(* the first byte is #x0e for FTC *)
let ftcaddr (x,y) = genaddr (x,y) (shift_left_big_int (big_int_of_int 14) 160)

let saltval : big_int option ref = ref None

let salt1 n =
  match !saltval with
  | None -> n
  | Some m ->
      shift_right_towards_zero_big_int (sha512num (or_big_int m n) 64) 256

let salt x =
  match !saltval with
  | None -> x
  | Some m ->
      let n = frombase58 x in
      base58 (shift_right_towards_zero_big_int (sha512num (or_big_int m n) 64) 256)

let btcfrombase58 k =
  let privkey = salt1 (frombase58 k) in
  if (gt_big_int privkey zero_big_int && lt_big_int privkey _n) then
    match smulp privkey _g with
    | Some(x,y) -> (btcwif privkey,btcaddr (x,y))
    | None -> raise Invalid
  else
    raise Invalid

let ltcfrombase58 k =
  let privkey = salt1 (frombase58 k) in
  if (gt_big_int privkey zero_big_int && lt_big_int privkey _n) then
    match smulp privkey _g with
    | Some(x,y) -> (ltcwif privkey,ltcaddr (x,y))
    | None -> raise Invalid
  else
    raise Invalid

let ftcfrombase58 k =
  let privkey = salt1 (frombase58 k) in
  if (gt_big_int privkey zero_big_int && lt_big_int privkey _n) then
    match smulp privkey _g with
    | Some(x,y) -> (ftcwif privkey,ftcaddr (x,y))
    | None -> raise Invalid
  else
    raise Invalid

