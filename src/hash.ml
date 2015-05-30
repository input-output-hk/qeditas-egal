(* Copyright (c) 2014 Chad E Brown *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(*** Chad E Brown ***)
(*** August 2013 ***)

open Big_int
open Cryptocurr

let sha256 s =
  let (myout,myin,myerr) = Unix.open_process_full (String.concat " " [Config.openssl_exec;"dgst";"-sha256"]) [| |] in
  String.iter (fun c -> output_byte myin (Char.code c)) s;
  close_out myin;
  let l = input_line myout in
  let ll = String.length l in
  ignore (Unix.close_process_full (myout,myin,myerr));
  if ll < 64 then
    raise (Failure ("bad openssl sha256 output: " ^ l))
  else
    big_int_of_hex_r l (ll - 64) ll Big_int.zero_big_int

let sha256file f =
  let (myout,myin,myerr) = Unix.open_process_full (String.concat " " [Config.openssl_exec;"dgst";"-sha256";f]) [| |] in
  close_out myin;
  let l = input_line myout in
  let ll = String.length l in
  ignore (Unix.close_process_full (myout,myin,myerr));
  if ll < 64 then
    raise (Failure ("bad openssl sha256 output: " ^ l))
  else
    String.sub l (ll-64) 64
