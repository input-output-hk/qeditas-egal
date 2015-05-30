(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(* Convert Egal representations of types, terms and proofs into Qeditas representations. ***)
open Syntax

(***
 sigdelta is a hash table for looking up Egal terms corresponding to strings/hashes.
 sigtmof is a hash table for looking up the types of Egal terms corresponding to strings/hashes.
 They are here instead of in egalqedtheory.ml and egalqeddoc.ml so that the conversion functions
 can use it.
 ***)
let sigdelta : (string,ptm) Hashtbl.t = Hashtbl.create 1000;; 
let sigtmof : (string,ptp) Hashtbl.t  = Hashtbl.create 1000;;

(*** eqtmh and eqknh relate strings (Egal hash values) to Qeditas hashvalues ***)
let eqtmh : (string,Qhash.hashval) Hashtbl.t = Hashtbl.create 1000;;
let eqknh : (string,Qhash.hashval) Hashtbl.t = Hashtbl.create 1000;;

let eqtmhfile = ref "egaltoqedtmh";;
let eqknhfile = ref "egaltoqedknh";;

let deftmh = ref [];;
let paramtmh = ref [];;

let load_eqtmh () =
  let f = open_in !eqtmhfile in
  try
    while true do
      let h = input_line f in
      let qh = input_line f in
      Hashtbl.add eqtmh h (Qhash.hexstring_hashval qh)
    done
  with
  | End_of_file -> ()

let load_eqknh () =
  let f = open_in !eqknhfile in
  try
    while true do
      let h = input_line f in
      let qh = input_line f in
      Hashtbl.add eqknh h (Qhash.hexstring_hashval qh)
    done
  with
  | End_of_file -> ()

let new_eqtmh h qh =
  Hashtbl.add eqtmh h qh;
  let c = open_out_gen [Open_creat;Open_append] 0o640 !eqtmhfile in
  output_string c h;
  output_char c '\n';
  output_string c (Qhash.hashval_hexstring qh);
  output_char c '\n';
  close_out c

let new_eqknh h qh =
  Hashtbl.add eqknh h qh;
  let c = open_out_gen [Open_creat;Open_append] 0o640 !eqknhfile in
  output_string c h;
  output_char c '\n';
  output_string c (Qhash.hashval_hexstring qh);
  output_char c '\n';
  close_out c

(* Output Qeditas docs *)
(* Convert Egal representations of types, terms and proofs into Qeditas representations. ***)
let rec tp_to_qtp i a =
  match a with
  | Prop -> Qsyntax.Prop
  | Set -> Qsyntax.Base(0)
  | Ar(a,b) -> Qsyntax.Ar(tp_to_qtp i a,tp_to_qtp i b)
  | TpVar(x) ->
      let y = i-x-1 in
      Qsyntax.TpVar(y)

let rec ptp_to_qtp i j a =
  if j < i then
    Qsyntax.TpAll(ptp_to_qtp i (j+1) a)
  else
    tp_to_qtp i a

let rec tm_to_qtm i m =
  match m with
  | DB(i) -> Qsyntax.DB(i)
  | TmH(h) ->
      if List.mem h !deftmh then
	begin
	  try
	    let qh = Hashtbl.find eqtmh h in
	    Qsyntax.TmH(qh)
	  with Not_found ->
	    let (j,n) = Hashtbl.find sigdelta h in
	    let qn = ptm_to_qtm_lam j 0 n in
	    let qnn = Qsyntax.tm_beta_eta_norm qn in
	    let qh = Qsyntax.tm_hashroot qnn in
	    new_eqtmh h qh;
	    Qsyntax.TmH(qh)
	end
      else if List.mem h !paramtmh then
	begin
	  try
	    let qh = Hashtbl.find eqtmh h in
	    Qsyntax.TmH(qh)
	  with Not_found ->
	    raise (Failure("Do not know Qeditas hash for param " ^ h))
	end
      else
	begin
	  let (j,n) = Hashtbl.find sigdelta h in
	  let qn = ptm_to_qtm_lam j 0 n in
	  qn
	end
  | Prim(i) -> Qsyntax.Prim(i)
  | TpAp(m1,a) ->
      Qsyntax.TTpAp(tm_to_qtm i m1,tp_to_qtp i a)
  | Ap(m1,m2) ->
      Qsyntax.Ap(tm_to_qtm i m1,tm_to_qtm i m2)
  | Lam(a,m1) ->
      Qsyntax.Lam(tp_to_qtp i a,tm_to_qtm i m1)
  | Imp(m1,m2) ->
      Qsyntax.Imp(tm_to_qtm i m1,tm_to_qtm i m2)
  | All(a,m1) ->
      Qsyntax.All(tp_to_qtp i a,tm_to_qtm i m1)
and ptm_to_qtm_lam i j m =
  if j < i then
    Qsyntax.TTpLam(ptm_to_qtm_lam i (j+1) m)
  else
    tm_to_qtm i m

let rec ptm_to_qtm_all i j m =
  if j < i then
    Qsyntax.TTpAll(ptm_to_qtm_all i (j+1) m)
  else
    tm_to_qtm i m

let rec pf_to_qpf i d =
  match d with
  | Hyp(k) -> Qsyntax.Hyp(k)
  | Known(h) ->
      begin
	try
	  let qh = Hashtbl.find eqknh h in
	  Qsyntax.Known(qh)
	with Not_found ->
	  try
	    let (i,n) = Hashtbl.find sigdelta h in
	    let qn = ptm_to_qtm_all i 0 n in
	    let qnn = Qsyntax.tm_beta_eta_norm qn in
	    let qh = Qsyntax.tm_hashroot qnn in
	    new_eqknh h qh;
	    Qsyntax.Known(qh)
	  with Not_found ->
	    raise (Failure("Do not know the Qeditas hashroot corresponding to " ^ h))
      end
  | PTpAp(d1,a) -> Qsyntax.PTpAp(pf_to_qpf i d1,tp_to_qtp i a)
  | PTmAp(d1,m) -> Qsyntax.PTmAp(pf_to_qpf i d1,tm_to_qtm i m)
  | PPfAp(d1,d2) -> Qsyntax.PPfAp(pf_to_qpf i d1,pf_to_qpf i d2)
  | PLam(p,d1) -> Qsyntax.PLam(tm_to_qtm i p,pf_to_qpf i d1)
  | TLam(a,d1) -> Qsyntax.TLam(tp_to_qtp i a,pf_to_qpf i d1)

let rec ppf_to_qpf i j d =
  if j < i then
    Qsyntax.PTpLam(ppf_to_qpf i (j+1) d)
  else
    pf_to_qpf i d

let tm_to_qtm_n i m =
  Qsyntax.tm_beta_eta_norm (tm_to_qtm i m)

let ptm_to_qtm_lam_n i j m =
  let qm = ptm_to_qtm_lam i j m in
  let qn = Qsyntax.tm_beta_eta_norm qm in
  let h = ptm_id (i,m) sigtmof sigdelta in
  if not (Hashtbl.mem eqtmh h) then
    begin
      let qh = Qsyntax.tm_hashroot qn in
      new_eqtmh h qh
    end;
  qn

let ptm_to_qtm_all_n i j m =
  let qm = ptm_to_qtm_all i j m in
  let qn = Qsyntax.tm_beta_eta_norm qm in
  let h = ptm_id (i,m) sigtmof sigdelta in
  if not (Hashtbl.mem eqknh h) then
    begin
      let qh = Qsyntax.tm_hashroot qn in
      new_eqknh h qh
    end;
  qn

let pf_to_qpf_n i d =
  Qsyntax.pf_beta_eta_norm (pf_to_qpf i d)

let ppf_to_qpf_n i j d =
  Qsyntax.pf_beta_eta_norm (ppf_to_qpf i j d)


