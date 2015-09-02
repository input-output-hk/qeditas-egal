(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(*** Much of this code is a modification of the code for types, terms and proofs in the
     original Egal (see syntax.ml). The main difference is Qeditas provides explicit
     support for type variables. ***)

open Qser
open Qhash

(*** TpVar x is the de Bruijn index x as a type variable with corresponding binder TpAll. ***)
type tp = TpVar of int | Prop | Base of int | Ar of tp * tp | TpAll of tp

type tm =
  | DB of int
  | TmH of hashval
  | Prim of int
  | Ap of tm * tm
  | Lam of tp * tm
  | Imp of tm * tm
  | All of tp * tm
  | TTpAp of tm * tp
  | TTpLam of tm
  | TTpAll of tm

type pf =
  | Gpa of hashval
  | Hyp of int
  | Known of hashval
  | PTmAp of pf * tm
  | PPfAp of pf * pf
  | PLam of tm * pf
  | TLam of tp * pf
  | PTpAp of pf * tp
  | PTpLam of pf

type theoryitem =
  | ThyPrim of tp
  | ThyDef of tp * tm
  | ThyAxiom of tm

type theoryspec = theoryitem list

type theory = tp list * hashval list

type signaitem =
  | SignaSigna of hashval
  | SignaParam of hashval * tp
  | SignaDef of tp * tm
  | SignaKnown of tm

type signaspec = signaitem list

type gsigna = (hashval * tp * tm option) list * (hashval * tm) list

type signa = hashval list * gsigna

type docitem =
  | DocSigna of hashval
  | DocParam of hashval * tp
  | DocDef of tp * tm
  | DocKnown of tm
  | DocConj of tm
  | DocPfOf of tm * pf

type doc = docitem list

(** ** pdoc: partical doc, approximating a doc with enough information to compute the hashroot **)
type pdoc =
  | PDocNil
  | PDocHash of hashval
  | PDocSigna of hashval * pdoc
  | PDocParam of hashval * tp * pdoc
  | PDocParamHash of hashval * pdoc
  | PDocDef of tp * tm * pdoc
  | PDocDefHash of hashval * pdoc
  | PDocKnown of tm * pdoc
  | PDocConj of tm * pdoc
  | PDocPfOf of tm * pf * pdoc
  | PDocPfOfHash of hashval * pdoc

(** * serialization code ***)

(** ** tp serialization ***)

let rec seo_tp o m c =
  match m with
  | Ar(m0,m1) -> (*** 00 ***)
      let c = o 2 0 c in
      let c = seo_tp o m0 c in
      let c = seo_tp o m1 c in
      c
  | Prop -> (*** 01 ***)
      o 2 1 c
  | Base(x) when x < 65536 -> (*** 10 ***)
      let c = o 2 2 c in
      seo_varintb o x c
  | Base(_) -> raise (Failure("Invalid base type"))
  | TpVar(x) when x < 65536 -> (*** 11 0 x ***)
      let c = o 3 3 c in
      let c = seo_varintb o x c in
      c
  | TpVar(_) -> raise (Failure("Invalid type variable"))
  | TpAll(a) -> (*** 11 1 ***)
      let c = o 3 7 c in
      let c = seo_tp o a c in
      c

let tp_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_tp seosb m (c,None));
  Buffer.contents c

let hashtp m = hashtag (hash160 (tp_to_str m)) 64l

let rec sei_tp i c =
  let (b,c) = i 2 c in
  if b = 0 then
    let (m0,c) = sei_tp i c in
    let (m1,c) = sei_tp i c in
    (Ar(m0,m1),c)
  else if b = 1 then
    (Prop,c)
  else if b = 2 then
    let (x,c) = sei_varintb i c in
    (Base(x),c)
  else
    let (y,c) = i 1 c in
    if y = 0 then
      let (x,c) = sei_varintb i c in
      (TpVar(x),c)
    else
      let (m0,c) = sei_tp i c in
      (TpAll(m0),c)

let str_to_tp c = let (m,_) = sei_tp seis (c,String.length c,None,0,0) in m

(** ** tp list serialization ***)
let seo_tpl o al c = seo_list seo_tp o al c
let sei_tpl i c = sei_list sei_tp i c

let tpl_to_str al =
  let c = Buffer.create 1000 in
  seosbf (seo_tpl seosb al (c,None));
  Buffer.contents c

let hashtpl al =
  if al = [] then
    None
  else
    Some(hashtag (hash160 (tpl_to_str al)) 65l)

(** ** tm serialization ***)
let rec seo_tm o m c =
  match m with
  | TmH(h) -> (*** 000 ***)
      let c = o 3 0 c in
      let c = seo_hashval o h c in
      c
  | DB(x) when x >= 0 && x <= 65535 -> (*** 001 ***)
      let c = o 3 1 c in
      seo_varintb o x c
  | DB(x) ->
      Printf.printf "De Bruijn index %d is not short.n" x;
      raise (Failure "seo_tm - de Bruijn out of bounds");
  | Prim(x) when x >= 0 && x <= 65535 -> (*** 010 ***)
      let c = o 3 2 c in
      let c = seo_varintb o x c in
      c
  | Prim(x) ->
      Printf.printf "Prim num %d is not short.n" x;
      raise (Failure "seo_tm - Prim out of bounds");
  | Ap(m0,m1) -> (*** 011 ***)
      let c = o 3 3 c in
      let c = seo_tm o m0 c in
      let c = seo_tm o m1 c in
      c
  | Lam(m0,m1) -> (*** 100 ***)
      let c = o 3 4 c in
      let c = seo_tp o m0 c in
      let c = seo_tm o m1 c in
      c
  | Imp(m0,m1) -> (*** 101 ***)
      let c = o 3 5 c in
      let c = seo_tm o m0 c in
      let c = seo_tm o m1 c in
      c
  | All(m0,m1) -> (*** 110 ***)
      let c = o 3 6 c in
      let c = seo_tp o m0 c in
      let c = seo_tm o m1 c in
      c
  | TTpAp(m0,a) -> (*** 111 0 ***)
      let c = o 4 7 c in
      let c = seo_tm o m0 c in
      let c = seo_tp o a c in
      c
  | TTpLam(m0) -> (*** 111 1 0 ***)
      let c = o 5 15 c in
      let c = seo_tm o m0 c in
      c
  | TTpAll(m0) -> (*** 111 1 1 ***)
      let c = o 5 31 c in
      let c = seo_tm o m0 c in
      c

let tm_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_tm seosb m (c,None));
  Buffer.contents c

let hashtm m = hashtag (hash160 (tm_to_str m)) 66l

let rec sei_tm i c =
  let (x,c) = i 3 c in
  if x = 0 then
    let (h,c) = sei_hashval i c in
    (TmH(h),c)
  else if x = 1 then
    let (z,c) = sei_varintb i c in
    (DB(z),c)
  else if x = 2 then
    let (z,c) = sei_varintb i c in
    (Prim(z),c)
  else if x = 3 then
    let (m0,c) = sei_tm i c in
    let (m1,c) = sei_tm i c in
    (Ap(m0,m1),c)
  else if x = 4 then
    let (m0,c) = sei_tp i c in
    let (m1,c) = sei_tm i c in
    (Lam(m0,m1),c)
  else if x = 5 then
    let (m0,c) = sei_tm i c in
    let (m1,c) = sei_tm i c in
    (Imp(m0,m1),c)
  else if x = 6 then
    let (m0,c) = sei_tp i c in
    let (m1,c) = sei_tm i c in
    (All(m0,m1),c)
  else
    let (y,c) = i 1 c in
    if y = 0 then
      let (m0,c) = sei_tm i c in
      let (a,c) = sei_tp i c in
      (TTpAp(m0,a),c)
    else
      let (y,c) = i 1 c in
      if y = 0 then
	let (m0,c) = sei_tm i c in
	(TTpLam(m0),c)
      else
	let (m0,c) = sei_tm i c in
	(TTpAll(m0),c)

let str_to_tm c = let (m,_) = sei_tm seis (c,String.length c,None,0,0) in m

(** ** pf serialization ***)
let rec seo_pf o m c =
  match m with
  | Gpa(h) -> (*** 000 ***)
      let c = o 3 0 c in
      seo_hashval o h c
  | Hyp(x) when x >= 0 && x <= 65535 -> (*** 001 ***)
      let c = o 3 1 c in
      seo_varintb o x c
  | Hyp(x) ->
      Printf.printf "Hypothesis index %d is not short.n" x;
      raise (Failure "seo_pf - Hypothesis out of bounds");
  | Known(h) -> (*** 010 ***)
      let c = o 3 2 c in
      let c = seo_hashval o h c in
      c
  | PTmAp(m0,m1) -> (*** 011 ***)
      let c = o 3 3 c in
      let c = seo_pf o m0 c in
      let c = seo_tm o m1 c in
      c
  | PPfAp(m0,m1) -> (*** 100 ***)
      let c = o 3 4 c in
      let c = seo_pf o m0 c in
      let c = seo_pf o m1 c in
      c
  | PLam(m0,m1) -> (*** 101 ***)
      let c = o 3 5 c in
      let c = seo_tm o m0 c in
      let c = seo_pf o m1 c in
      c
  | TLam(m0,m1) -> (*** 110 ***)
      let c = o 3 6 c in
      let c = seo_tp o m0 c in
      let c = seo_pf o m1 c in
      c
  | PTpAp(d,a) -> (*** 111 0 ***)
      let c = o 4 7 c in
      let c = seo_pf o d c in
      let c = seo_tp o a c in
      c
  | PTpLam(d) -> (*** 111 1 ***)
      let c = o 4 15 c in
      let c = seo_pf o d c in
      c

let pf_to_str m =
  let c = Buffer.create 1000 in
  seosbf (seo_pf seosb m (c,None));
  Buffer.contents c

let hashpf m = hashtag (hash160 (pf_to_str m)) 67l

let rec sei_pf i c =
  let (x,c) = i 3 c in
  if x = 0 then
    let (h,c) = sei_hashval i c in
    (Gpa(h),c)
  else if x = 1 then
    let (z,c) = sei_varintb i c in
    (Hyp(z),c)
  else if x = 2 then
    let (z,c) = sei_hashval i c in
    (Known(z),c)
  else if x = 3 then
    let (m0,c) = sei_pf i c in
    let (m1,c) = sei_tm i c in
    (PTmAp(m0,m1),c)
  else if x = 4 then
    let (m0,c) = sei_pf i c in
    let (m1,c) = sei_pf i c in
    (PPfAp(m0,m1),c)
  else if x = 5 then
    let (m0,c) = sei_tm i c in
    let (m1,c) = sei_pf i c in
    (PLam(m0,m1),c)
  else if x = 6 then
    let (m0,c) = sei_tp i c in
    let (m1,c) = sei_pf i c in
    (TLam(m0,m1),c)
  else
    let (y,c) = i 1 c in
    if y = 0 then
      let (d,c) = sei_pf i c in
      let (a,c) = sei_tp i c in
      (PTpAp(d,a),c)
    else
      let (d,c) = sei_pf i c in
      (PTpLam(d),c)

let str_to_pf c = let (m,_) = sei_pf seis (c,String.length c,None,0,0) in m

(** ** theoryspec serialization ***)
let seo_theoryitem o m c =
  match m with
  | ThyPrim(a) ->
      let c = o 1 0 c in
      let c = o 1 0 c in
      seo_tp o a c
  | ThyDef(a,m) ->
      let c = o 1 0 c in
      let c = o 1 1 c in
      let c = seo_tp o a c in
      seo_tm o m c
  | ThyAxiom(m) ->
      let c = o 1 1 c in
      seo_tm o m c

let sei_theoryitem i c =
  let (b,c) = i 1 c in
  if b = 0 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (a,c) = sei_tp i c in
      (ThyPrim(a),c)
    else
      let (a,c) = sei_tp i c in
      let (m,c) = sei_tm i c in
      (ThyDef(a,m),c)
  else
    let (m,c) = sei_tm i c in
    (ThyAxiom(m),c)

let seo_theoryspec o dl c = seo_list seo_theoryitem o dl c
let sei_theoryspec i c = sei_list sei_theoryitem i c

(** ** signaspec serialization ***)
let seo_signaitem o m c =
  match m with
  | SignaSigna(h) -> (** 00 **)
      let c = o 2 0 c in
      seo_hashval o h c
  | SignaParam(h,a) -> (** 01 **)
      let c = o 2 1 c in
      let c = seo_hashval o h c in
      seo_tp o a c
  | SignaDef(a,m) -> (** 10 **)
      let c = o 2 2 c in
      let c = seo_tp o a c in
      seo_tm o m c
  | SignaKnown(m) -> (** 11 **)
      let c = o 2 3 c in
      seo_tm o m c

let sei_signaitem i c =
  let (b,c) = i 2 c in
  if b = 0 then
    let (h,c) = sei_hashval i c in
    (SignaSigna(h),c)
  else if b = 1 then
    let (h,c) = sei_hashval i c in
    let (a,c) = sei_tp i c in
    (SignaParam(h,a),c)
  else if b = 2 then
    let (a,c) = sei_tp i c in
    let (m,c) = sei_tm i c in
    (SignaDef(a,m),c)
  else
    let (m,c) = sei_tm i c in
    (SignaKnown(m),c)

let seo_signaspec o dl c = seo_list seo_signaitem o dl c
let sei_signaspec i c = sei_list sei_signaitem i c

(** ** doc serialization ***)
let seo_docitem o m c =
  match m with
  | DocSigna(h) -> (** 00 0 **)
      let c = o 3 0 c in
      seo_hashval o h c
  | DocParam(h,a) -> (** 00 1 **)
      let c = o 3 4 c in
      let c = seo_hashval o h c in
      seo_tp o a c
  | DocDef(a,m) -> (** 01 **)
      let c = o 2 1 c in
      let c = seo_tp o a c in
      seo_tm o m c
  | DocKnown(m) -> (** 10 0 **)
      let c = o 3 2 c in
      seo_tm o m c
  | DocConj(m) -> (** 10 1 **)
      let c = o 3 6 c in
      seo_tm o m c
  | DocPfOf(m,d) -> (** 11 **)
      let c = o 2 3 c in
      let c = seo_tm o m c in
      seo_pf o d c

let sei_docitem i c =
  let (b,c) = i 2 c in
  if b = 0 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (h,c) = sei_hashval i c in
      (DocSigna(h),c)
    else
      let (h,c) = sei_hashval i c in
      let (a,c) = sei_tp i c in
      (DocParam(h,a),c)
  else if b = 1 then
    let (a,c) = sei_tp i c in
    let (m,c) = sei_tm i c in
    (DocDef(a,m),c)
  else if b = 2 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (m,c) = sei_tm i c in
      (DocKnown(m),c)
    else
      let (m,c) = sei_tm i c in
      (DocConj(m),c)
  else
    let (m,c) = sei_tm i c in
    let (d,c) = sei_pf i c in
    (DocPfOf(m,d),c)

let seo_doc o dl c = seo_list seo_docitem o dl c
let sei_doc i c = sei_list sei_docitem i c

(** ** pdoc serialization ***)
let rec seo_pdoc o dl c =
  match dl with
  | PDocNil -> (** 00 0 **)
      o 3 0 c
  | PDocHash(h) -> (** 00 1 **)
      let c = o 3 4 c in
      let c = seo_hashval o h c in
      c
  | PDocSigna(h,dr) -> (** 01 0 **)
      let c = o 3 1 c in
      let c = seo_hashval o h c in
      seo_pdoc o dr c
  | PDocParam(h,a,dr) -> (** 01 1 **)
      let c = o 3 5 c in
      let c = seo_hashval o h c in
      let c = seo_tp o a c in
      seo_pdoc o dr c
  | PDocParamHash(h,dr) -> (** 10 0 **)
      let c = o 3 2 c in
      let c = seo_hashval o h c in
      seo_pdoc o dr c
  | PDocDef(a,m,dr) -> (** 10 1 0 **)
      let c = o 4 6 c in
      let c = seo_tp o a c in
      let c = seo_tm o m c in
      seo_pdoc o dr c
  | PDocDefHash(h,dr) -> (** 10 1 1 **)
      let c = o 4 14 c in
      let c = seo_hashval o h c in
      seo_pdoc o dr c
  | PDocKnown(m,dr) -> (** 11 00 **)
      let c = o 4 3 c in
      let c = seo_tm o m c in
      seo_pdoc o dr c
  | PDocConj(m,dr) -> (** 11 01 **)
      let c = o 4 7 c in
      let c = seo_tm o m c in
      seo_pdoc o dr c
  | PDocPfOf(m,d,dr) -> (** 11 10 **)
      let c = o 4 11 c in
      let c = seo_tm o m c in
      let c = seo_pf o d c in
      seo_pdoc o dr c
  | PDocPfOfHash(h,dr) -> (** 11 11 **)
      let c = o 4 15 c in
      let c = seo_hashval o h c in
      seo_pdoc o dr c

let rec sei_pdoc i c =
  let (b,c) = i 2 c in
  if b = 0 then
    let (b,c) = i 1 c in
    if b = 0 then
      (PDocNil,c)
    else
      let (h,c) = sei_hashval i c in
      (PDocHash(h),c)
  else if b = 1 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (h,c) = sei_hashval i c in
      let (dr,c) = sei_pdoc i c in
      (PDocSigna(h,dr),c)
    else
      let (h,c) = sei_hashval i c in
      let (a,c) = sei_tp i c in
      let (dr,c) = sei_pdoc i c in
      (PDocParam(h,a,dr),c)
  else if b = 2 then
    let (b,c) = i 1 c in
    if b = 0 then
      let (h,c) = sei_hashval i c in
      let (dr,c) = sei_pdoc i c in
      (PDocParamHash(h,dr),c)
    else
      let (b,c) = i 1 c in
      if b = 0 then
	let (a,c) = sei_tp i c in
	let (m,c) = sei_tm i c in
	let (dr,c) = sei_pdoc i c in
	(PDocDef(a,m,dr),c)
      else
      let (h,c) = sei_hashval i c in
      let (dr,c) = sei_pdoc i c in
      (PDocDefHash(h,dr),c)
  else
    let (b,c) = i 2 c in
    if b = 0 then
      let (m,c) = sei_tm i c in
      let (dr,c) = sei_pdoc i c in
      (PDocKnown(m,dr),c)
    else if b = 1 then
      let (m,c) = sei_tm i c in
      let (dr,c) = sei_pdoc i c in
      (PDocConj(m,dr),c)
    else if b = 2 then
      let (m,c) = sei_tm i c in
      let (d,c) = sei_pf i c in
      let (dr,c) = sei_pdoc i c in
      (PDocPfOf(m,d,dr),c)
    else
      let (h,c) = sei_hashval i c in
      let (dr,c) = sei_pdoc i c in
      (PDocPfOfHash(h,dr),c)

(** ** serialization of theories ***)
let seo_theory o (al,kl) c =
  let c = seo_tpl o al c in
  seo_list seo_hashval o kl c

let sei_theory i c =
  let (al,c) = sei_tpl i c in
  let (kl,c) = sei_list sei_hashval i c in
  ((al,kl),c)

let theory_to_str thy =
  let c = Buffer.create 1000 in
  seosbf (seo_theory seosb thy (c,None));
  Buffer.contents c

let str_to_theory c = let (m,_) = sei_theory seis (c,String.length c,None,0,0) in m

(** * computation of hash roots ***)
let rec tm_hashroot m =
  match m with
  | TmH(h) -> h
  | Prim(x) -> hashtag (hashint32 (Int32.of_int x)) 96l
  | DB(x) -> hashtag (hashint32 (Int32.of_int x)) 97l
  | Ap(m,n) -> hashtag (hashpair (tm_hashroot m) (tm_hashroot n)) 98l
  | Lam(a,m) -> hashtag (hashpair (hashtp a) (tm_hashroot m)) 99l
  | Imp(m,n) -> hashtag (hashpair (tm_hashroot m) (tm_hashroot n)) 100l
  | All(a,m) -> hashtag (hashpair (hashtp a) (tm_hashroot m)) 101l
  | TTpAp(m,a) -> hashtag (hashpair (tm_hashroot m) (hashtp a)) 102l
  | TTpLam(m) -> hashtag (tm_hashroot m) 103l
  | TTpAll(m) -> hashtag (tm_hashroot m) 104l

let rec pf_hashroot d =
  match d with
  | Gpa(h) -> h
  | Known(h) -> hashtag h 128l
  | Hyp(x) -> hashtag (hashint32 (Int32.of_int x)) 129l
  | PTmAp(d,m) -> hashtag (hashpair (pf_hashroot d) (tm_hashroot m)) 130l
  | PPfAp(d,e) -> hashtag (hashpair (pf_hashroot d) (pf_hashroot e)) 131l
  | PLam(m,d) -> hashtag (hashpair (tm_hashroot m) (pf_hashroot d)) 132l
  | TLam(a,d) -> hashtag (hashpair (hashtp a) (pf_hashroot d)) 133l
  | PTpAp(d,a) -> hashtag (hashpair (pf_hashroot d) (hashtp a)) 134l
  | PTpLam(d) -> hashtag (pf_hashroot d) 135l

let rec theoryspec_hashroot thy =
  match thy with
  | [] -> None
  | ThyPrim(a)::thy -> Some(hashopair1 (hashtag (hashtp a) 160l) (theoryspec_hashroot thy))
  | ThyDef(a,m)::thy -> Some(hashopair1 (hashtag (hashpair (hashtp a) (hashtm m)) 161l) (theoryspec_hashroot thy))
  | ThyAxiom(m)::thy -> Some(hashopair1 (hashtag (hashtm m) 162l) (theoryspec_hashroot thy))

let rec signaspec_hashroot s =
  match s with
  | [] -> hashint32 110l
  | SignaSigna(h)::r -> hashtag (hashpair h (signaspec_hashroot r)) 164l
  | SignaParam(h,a)::r -> hashtag (hashpair (hashpair h (hashtp a)) (signaspec_hashroot r)) 165l
  | SignaDef(a,m)::r -> hashtag (hashpair (hashpair (hashtp a) (tm_hashroot m)) (signaspec_hashroot r)) 166l
  | SignaKnown(m)::r -> hashtag (hashpair (tm_hashroot m) (signaspec_hashroot r)) 167l

let rec docitem_hashroot d =
  match d with
  | DocSigna(h) -> hashtag h 172l
  | DocParam(h,a) -> hashtag (hashpair h (hashtp a)) 173l
  | DocDef(a,m) -> hashtag (hashpair (hashtp a) (tm_hashroot m)) 174l
  | DocKnown(m) -> hashtag (tm_hashroot m) 175l
  | DocConj(m) -> hashtag (tm_hashroot m) 176l
  | DocPfOf(m,d) -> hashtag (hashpair (tm_hashroot m) (pf_hashroot d)) 177l

let rec doc_hashroot dl =
  match dl with
  | [] -> hashint32 180l
  | d::dr -> hashtag (hashpair (docitem_hashroot d) (doc_hashroot dr)) 181l

let rec pdoc_hashroot dl =
  match dl with
  | PDocNil -> hashint32 180l
  | PDocHash(h) -> h
  | PDocSigna(h,dr) ->
      hashtag (hashpair (hashtag h 172l)
		 (pdoc_hashroot dr)) 181l
  | PDocParam(h,a,dr) ->
      hashtag (hashpair (hashtag (hashpair h (hashtp a)) 173l)
		 (pdoc_hashroot dr)) 181l
  | PDocParamHash(h,dr) ->
      hashtag (hashpair (hashtag h 173l)
		 (pdoc_hashroot dr)) 181l
  | PDocDef(a,m,dr) ->
      hashtag (hashpair (hashtag (hashpair (hashtp a) (tm_hashroot m)) 174l)
		 (pdoc_hashroot dr)) 181l
  | PDocDefHash(h,dr) ->
      hashtag (hashpair (hashtag h 174l)
		 (pdoc_hashroot dr)) 181l
  | PDocKnown(m,dr) ->
      hashtag (hashpair (hashtag (tm_hashroot m) 175l)
		 (pdoc_hashroot dr)) 181l
  | PDocConj(m,dr) ->
      hashtag (hashpair (hashtag (tm_hashroot m) 176l)
		 (pdoc_hashroot dr)) 181l
  | PDocPfOf(m,d,dr) ->
      hashtag (hashpair (hashtag (hashpair (tm_hashroot m) (pf_hashroot d)) 177l)
		 (pdoc_hashroot dr)) 181l
  | PDocPfOfHash(h,dr) ->
      hashtag (hashpair (hashtag h 177l)
		 (pdoc_hashroot dr)) 181l

(** * conversion of theoryspec to theory and signaspec to signa **)
let rec theoryspec_primtps_r dl =
  match dl with
  | [] -> []
  | ThyPrim(a)::dr -> a::theoryspec_primtps_r dr
  | _::dr -> theoryspec_primtps_r dr
  
let theoryspec_primtps dl = List.rev (theoryspec_primtps_r dl)

let rec theoryspec_hashedaxioms dl =
  match dl with
  | [] -> []
  | ThyAxiom(m)::dr -> tm_hashroot m::theoryspec_hashedaxioms dr
  | _::dr -> theoryspec_hashedaxioms dr

let theoryspec_theory thy = (theoryspec_primtps thy,theoryspec_hashedaxioms thy)

let hashtheory (al,kl) =
  hashopair
    (ohashlist (List.map hashtp al))
    (ohashlist kl)

let rec signaspec_signas s =
  match s with
  | [] -> []
  | SignaSigna(h)::r -> h::signaspec_signas r
  | _::r -> signaspec_signas r

let rec signaspec_trms s =
  match s with
  | [] -> []
  | SignaParam(h,a)::r -> (h,a,None)::signaspec_trms r
  | SignaDef(a,m)::r -> (tm_hashroot m,a,Some(m))::signaspec_trms r
  | _::r -> signaspec_trms r

let rec signaspec_knowns s =
  match s with
  | [] -> []
  | SignaKnown(p)::r -> (tm_hashroot p,p)::signaspec_knowns r
  | _::r -> signaspec_knowns r

let signaspec_signa s = (signaspec_signas s,(signaspec_trms s,signaspec_knowns s))

let hashgsigna (tl,kl) =
  hashpair
    (hashlist
       (List.map (fun z ->
	 match z with
	 | (h,a,None) -> hashtag (hashpair h (hashtp a)) 160l
	 | (h,a,Some(m)) -> hashtag (hashpair h (hashpair (hashtp a) (hashtm m))) 161l)
	  tl))
    (hashlist (List.map (fun (k,p) -> (hashpair k (hashtm p))) kl))

let hashsigna (sl,(tl,kl)) = hashpair (hashlist sl) (hashgsigna (tl,kl))

(** * operations (substitution, shift, normalization) ***)

let rec tpshift i j a =
  match a with
  | TpVar(k) when k < i -> TpVar(k)
  | TpVar(k) -> TpVar(k+j)
  | Ar(a1,a2) -> Ar(tpshift i j a1,tpshift i j a2)
  | TpAll(a) -> TpAll(tpshift (i+1) j a)
  | _ -> a

(*** The shift and substitution operations are only valid if TmH only abbreviates
 closed terms (terms with no DBs and no TpVars).
 ***)
let rec tmshift i j m =
  match m with
  | DB(k) when k < i -> DB(k)
  | DB(k) -> DB(k+j)
  | Ap(m1,m2) -> Ap(tmshift i j m1,tmshift i j m2)
  | Lam(a1,m1) -> Lam(a1,tmshift (i+1) j m1)
  | Imp(m1,m2) -> Imp(tmshift i j m1,tmshift i j m2)
  | All(a1,m1) -> All(a1,tmshift (i+1) j m1)
  | TTpAp(m1,a1) -> TTpAp(tmshift i j m1,a1)
  | TTpLam(m1) -> TTpLam(tmshift i j m1)
  | TTpAll(m1) -> TTpAll(tmshift i j m1)
  | _ -> m

let rec tmtpshift i j m =
  match m with
  | DB(k) when k < i -> DB(k)
  | DB(k) -> DB(k+j)
  | Ap(m1,m2) -> Ap(tmtpshift i j m1,tmtpshift i j m2)
  | Lam(a1,m1) -> Lam(a1,tmtpshift i j m1)
  | Imp(m1,m2) -> Imp(tmtpshift i j m1,tmtpshift i j m2)
  | All(a1,m1) -> All(a1,tmtpshift i j m1)
  | TTpAp(m1,a1) -> TTpAp(tmtpshift i j m1,tpshift i j a1)
  | TTpLam(m1) -> TTpLam(tmtpshift (i+1) j m1)
  | TTpAll(m1) -> TTpAll(tmtpshift (i+1) j m1)
  | _ -> m

(*** Similar to the tm case, pf shift and subst operations are only valid when Gpa and TmH
  abbreviate closed pfs and tms, respectively.
 ***)
let rec pfshift i j d =
  match d with
  | Hyp(k) when k < i -> Hyp(k)
  | Hyp(k) -> Hyp(k+j)
  | PTmAp(d1,m2) -> PTmAp(pfshift i j d1,m2)
  | PPfAp(d1,d2) -> PPfAp(pfshift i j d1,pfshift i j d2)
  | PLam(m1,d1) -> PLam(m1,pfshift (i+1) j d1)
  | TLam(a1,d1) -> TLam(a1,pfshift i j d1)
  | PTpAp(d1,a1) -> PTpAp(pfshift i j d1,a1)
  | PTpLam(d1) -> PTpLam(pfshift i j d1)
  | _ -> d

let rec pftmshift i j d =
  match d with
  | PTmAp(d1,m2) -> PTmAp(pftmshift i j d1,tmshift i j m2)
  | PPfAp(d1,d2) -> PPfAp(pftmshift i j d1,pftmshift i j d2)
  | PLam(m1,d1) -> PLam(tmshift i j m1,pftmshift i j d1)
  | TLam(a1,d1) -> TLam(a1,pftmshift (i+1) j d1)
  | PTpAp(d1,a1) -> PTpAp(pftmshift i j d1,a1)
  | PTpLam(d1) -> PTpLam(pftmshift i j d1)
  | _ -> d

let rec pftpshift i j d =
  match d with
  | PTmAp(d1,m2) -> PTmAp(pftpshift i j d1,tmtpshift i j m2)
  | PPfAp(d1,d2) -> PPfAp(pftpshift i j d1,pftpshift i j d2)
  | PLam(m1,d1) -> PLam(tmtpshift i j m1,pftpshift i j d1)
  | TLam(a1,d1) -> TLam(tpshift i j a1,pftpshift i j d1)
  | PTpAp(d1,a1) -> PTpAp(pftpshift i j d1,tpshift i j a1)
  | PTpLam(d1) -> PTpLam(pftpshift (i+1) j d1)
  | _ -> d

let rec tpsubst a j b =
  match a with
  | TpVar(i) when i = j && j = 0 -> b
  | TpVar(i) when i = j -> tpshift 0 j b
  | TpVar(i) when i > j -> TpVar(i-1)
  | Ar(a1,a2) -> Ar(tpsubst a1 j b,tpsubst a2 j b)
  | TpAll(a1) -> TpAll(tpsubst a1 (j+1) b)
  | _ -> a

let rec tmtpsubst m j b =
  match m with
  | Ap(m1,m2) -> Ap(tmtpsubst m1 j b,tmtpsubst m2 j b)
  | Lam(a1,m1) -> Lam(tpsubst a1 j b,tmtpsubst m1 j b)
  | Imp(m1,m2) -> Imp(tmtpsubst m1 j b,tmtpsubst m2 j b)
  | All(a1,m1) -> All(tpsubst a1 j b,tmtpsubst m1 j b)
  | TTpAp(m,a) -> TTpAp(tmtpsubst m j b,tpsubst a j b)
  | TTpLam(m) -> TTpLam(tmtpsubst m (j+1) b)
  | TTpAll(m) -> TTpAll(tmtpsubst m (j+1) b)
  | _ -> m

let rec pftpsubst d j b =
  match d with
  | PTmAp(d1,m1) -> PTmAp(pftpsubst d1 j b,tmtpsubst m1 j b)
  | PPfAp(d1,d2) -> PPfAp(pftpsubst d1 j b,pftpsubst d2 j b)
  | PLam(m1,d1) -> PLam(tmtpsubst m1 j b,pftpsubst d1 j b)
  | TLam(a1,d1) -> TLam(tpsubst a1 j b,pftpsubst d1 j b)
  | PTpAp(d1,a) -> PTpAp(pftpsubst d1 j b,tpsubst a j b)
  | PTpLam(d1) -> PTpLam(pftpsubst d1 (j+1) b)
  | _ -> d

let rec tmsubst m j n =
  match m with
  | DB(i) when i = j && j = 0 -> n
  | DB(i) when i = j -> tmshift 0 j n
  | DB(i) when i > j -> DB(i-1)
  | Ap(m1,m2) -> Ap(tmsubst m1 j n,tmsubst m2 j n)
  | Lam(a,m1) -> Lam(a,tmsubst m1 (j+1) n)
  | Imp(m1,m2) -> Imp(tmsubst m1 j n,tmsubst m2 j n)
  | All(a,m1) -> All(a,tmsubst m1 (j+1) n)
  | _ -> m

let rec free_in_tm_p m j =
  match m with
  | DB(i) when i = j -> true
  | Ap(m1,m2) -> free_in_tm_p m1 j || free_in_tm_p m2 j
  | Lam(a,m1) -> free_in_tm_p m1 (j+1)
  | Imp(m1,m2) -> free_in_tm_p m1 j || free_in_tm_p m2 j
  | All(a,m1) -> free_in_tm_p m1 (j+1)
  | _ -> false

let rec free_tpvar_in_tp_p a j =
  match a with
  | TpVar(i) when i = j -> true
  | Ar(a1,a2) -> free_tpvar_in_tp_p a1 j || free_tpvar_in_tp_p a2 j
  | TpAll(a) -> free_tpvar_in_tp_p a (j+1)
  | _ -> false

let rec free_tpvar_in_tm_p m j =
  match m with
  | Ap(m1,m2) -> free_tpvar_in_tm_p m1 j || free_tpvar_in_tm_p m2 j
  | Lam(a,m1) -> free_tpvar_in_tp_p a j || free_tpvar_in_tm_p m1 j
  | Imp(m1,m2) -> free_tpvar_in_tm_p m1 j || free_tpvar_in_tm_p m2 j
  | All(a,m1) -> free_tpvar_in_tp_p a j || free_tpvar_in_tm_p m1 j
  | TTpAp(m1,a) -> free_tpvar_in_tm_p m1 j || free_tpvar_in_tp_p a j
  | TTpLam(m1) -> free_tpvar_in_tm_p m1 (j+1)
  | TTpAll(m1) -> free_tpvar_in_tm_p m1 (j+1)
  | _ -> false

let beta_count = ref (Some 1000000)

exception BetaLimit

let beta_count_check () =
  match !beta_count with
  | None -> ()
  | Some b when b > 0 ->
      beta_count := Some (b-1)
  | _ ->
      raise BetaLimit

let rec tm_beta_eta_norm_1 m =
  match m with
  | Ap(m1,m2) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      let (m2r,m2b) = tm_beta_eta_norm_1 m2 in
      begin
	match m1r with
	| Lam(a,m) ->
	    beta_count_check ();
	    (tmsubst m 0 m2r,false) (*** beta ***)
	| _ -> (Ap(m1r,m2r),m1b && m2b)
      end
  | Lam(a,m1) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      begin
	match m1r with
	| Ap(m1f,DB(0)) when not (free_in_tm_p m1f 0) -> (tmshift 0 (-1) m1f,false) (*** eta ***)
	| _ -> (Lam(a,m1r),m1b)
      end
  | TTpAp(m1,a) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      begin
	match m1r with
	| TTpLam(m) ->
	    beta_count_check ();
	    (tmtpsubst m 0 a,false) (*** type level beta ***)
	| _ -> (TTpAp(m1r,a),m1b)
      end
  | TTpLam(m1) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      begin
	match m1r with
	| TTpAp(m1f,TpVar(0)) when not (free_tpvar_in_tm_p m1f 0) -> (tmtpshift 0 (-1) m1f,false) (*** type level eta ***)
	| _ -> (TTpLam(m1r),m1b)
      end
  | Imp(m1,m2) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      let (m2r,m2b) = tm_beta_eta_norm_1 m2 in
      (Imp(m1r,m2r),m1b && m2b)
  | All(a,m1) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      (All(a,m1r),m1b)
  | TTpAll(m1) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      (TTpAll(m1r),m1b)
  | _ -> (m,true)

let rec tm_beta_eta_norm m =
  let (mr,mb) = tm_beta_eta_norm_1 m in
  if mb then
    mr
  else
    tm_beta_eta_norm mr

let rec pf_beta_eta_norm d =
  match d with
  | PTmAp(d,m) -> PTmAp(pf_beta_eta_norm d,tm_beta_eta_norm m)
  | PPfAp(d1,d2) -> PPfAp(pf_beta_eta_norm d1,pf_beta_eta_norm d2)
  | PLam(m,d) -> PLam(tm_beta_eta_norm m,pf_beta_eta_norm d)
  | TLam(a,d) -> TLam(a,pf_beta_eta_norm d)
  | PTpAp(d,a) -> PTpAp(pf_beta_eta_norm d,a)
  | PTpLam(d) -> PTpLam(pf_beta_eta_norm d)
  | _ -> d

