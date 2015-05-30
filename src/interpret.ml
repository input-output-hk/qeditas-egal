(* Copyright (c) 2014 Chad E Brown *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(*** File: interpret.ml ***)
(*** Chad E Brown ***)
(*** Feb 2014 ***)

open Syntax
open Parser

let verbosity = ref 1
let proving : (string * int * tm * string) option ref = ref None
let prooffun : (pf list -> pf) ref = ref (fun _ -> raise (Failure "Bug. Proof construction function has not been set"))
let deltaset : string list ref = ref []
type pfstatetype =
  | PfStateGoal of tm * (string * (tp * tm option)) list * (string * tm) list
  | PfStateSep of int * bool
let pfstate : pfstatetype list ref = ref []

(*** The hash ids for the following will be added as we bootstrap, allowing us to make sense of more term syntax as we go. ***)
let fal : string ref = ref "";;
let eqPoly : string ref = ref "";;
let eqsymPoly : string ref = ref "";;
let eqsymPolyknown : bool ref = ref false;;
let eqSet : string ref = ref "";;
let conj : string ref = ref "";;
let disj : string ref = ref "";;
let expoly : string ref = ref "";;
let expolyI : string ref = ref "";;
let expolyIknown : bool ref = ref false;;
let setIn : string option ref = ref None;;
let setSubeq : string option ref = ref None;;
let setPow : string option ref = ref None;;
let setimplop : string option ref = ref None;;
let setlam : string option ref = ref None;;
let replop : string option ref = ref None;;
let sepop : string option ref = ref None;;
let replsepop : string option ref = ref None;;

let setenuml : string option list ref = ref [];;
let setenumadj : string option ref = ref None;;

let rec set_setenuml_r i h sel =
  if i > 0 then
    begin
      match sel with
      | [] -> None::set_setenuml_r (i-1) h []
      | (z::ser) -> z::set_setenuml_r (i-1) h ser
    end
  else
    begin
      match sel with
      | [] -> [Some h]
      | (_::ser) -> Some h::ser
    end

let set_setenuml_n i h =
  setenuml := set_setenuml_r i h !setenuml

let nat0 : string option ref = ref None
let natS : string option ref = ref None

let rec tm_buildnat_r hS n r =
  if n > 0 then
    tm_buildnat_r hS (n-1) (Ap(TmH(hS),r))
  else
    r

let tm_buildnat h0 hS n =
  tm_buildnat_r hS n (TmH(h0))

(*** Hash id for polymorphic if operator: ***)
let ifop : string option ref = ref None

let rec cxtmdb cxtm =
  match cxtm with
  | [] -> []
  | (_,(a,None))::cxtmr -> a::cxtmdb cxtmr
  | (_,(_,Some(_)))::cxtmr -> cxtmdb cxtmr

let cxpfdb cxpf = List.map (fun (_,p) -> p) cxpf

let rec extract_tp a tvl =
  match a with
  | Na "prop" -> Prop
  | Na "set" -> Set
  | Na x ->
      begin
	try
	  let i = position tvl x in
	  TpVar i
	with Not_found -> raise (Failure (x ^ " is not a tp"))
      end
  | Info(InfNam "->",a1,a2) -> Ar(extract_tp a1 tvl,extract_tp a2 tvl)
  | _ ->
      if !verbosity > 3 then (output_ltree stdout (atree_to_ltree a); Printf.printf " is not a type.\n"; flush stdout);
      raise (Failure ("Not a tp"))

let multbvarsp bvl =
  match bvl with
  | [([y],_)] -> false
  | _ -> true

let rec invert_mtupletp_n a c n =
  if a = c then
    n
  else
    match a with
    | Ar(c1,b) when c1 = c -> invert_mtupletp_n b c (1+n)
    | _ -> raise Not_found

let invert_mtupletp a =
  match a with
  | (Ar(b,c)) -> (c,invert_mtupletp_n b c 0)
  | _ -> raise Not_found

(***
 extract_tm returns tm * tp or raises an exception
 check_tm returns a tm or raises an exception
 ***)
let rec extract_tm a poly sgtmof sgtm cxtp cxtm =
  match a with
  | Na(x) ->
      begin
	try
	  let (atm,atp) = tmtplookup cxtm x in
	  if (!verbosity > 19) then (Printf.printf "Found %s in ctx as %s\n" x (tm_to_str atm); flush stdout);
	  (atm,atp)
	with Not_found ->
	  try
	    if (!verbosity > 19) then (Printf.printf "about to lookup in sgtm %s\n" x; flush stdout);
	    let m = List.assoc x sgtm cxtp cxtm in
	    if (!verbosity > 19) then (Printf.printf "looked up in sg %s\nand found %s\n" x (tm_to_str m); flush stdout);
	    (m,extr_tpoftm sgtmof (cxtmdb cxtm) m)
	  with Not_found ->
	    raise (Failure("Unknown term " ^ x ^ " -- it might be a proof in the position where a term is expected"))
      end
  | Implop(Na(x),a1) when List.mem_assoc (x,1) poly ->
      let xa = List.assoc (x,1) poly in
      let a1tp = extract_tp a1 cxtp in
      let xd = List.assoc x sgtm cxtp cxtm in
      (TpAp(xd,a1tp),tpsubst xa [a1tp])
  | Implop(Implop(Na(x),a1),a2) when List.mem_assoc (x,2) poly ->
      let xa = List.assoc (x,2) poly in
      let a1tp = extract_tp a1 cxtp in
      let a2tp = extract_tp a2 cxtp in
      let xd = List.assoc x sgtm cxtp cxtm in
      (TpAp(TpAp(xd,a1tp),a2tp),tpsubst xa [a1tp;a2tp])
  | Implop(Implop(Implop(Na(x),a1),a2),a3) when List.mem_assoc (x,3) poly ->
      let xa = List.assoc (x,3) poly in
      let a1tp = extract_tp a1 cxtp in
      let a2tp = extract_tp a2 cxtp in
      let a3tp = extract_tp a3 cxtp in
      let xd = List.assoc x sgtm cxtp cxtm in
      (TpAp(TpAp(TpAp(xd,a1tp),a2tp),a3tp),tpsubst xa [a1tp;a2tp;a3tp])
  | Implop(a1,a2) ->
      let (n1,n1tp) = extract_tm a1 poly sgtmof sgtm cxtp cxtm in
      begin
	match n1tp with
	| Ar(b1,b2) ->
	    let n2 = check_tm a2 b1 poly sgtmof sgtm cxtp cxtm in
	    (Ap(n1,n2),b2)
	| Set ->
	    begin
	      match !setimplop with
	      | None -> raise (Failure("An implicit operator was used on a set before declared."))
	      | Some(oph) ->
		  let n2 = check_tm a2 Set poly sgtmof sgtm cxtp cxtm in
		  (Ap(Ap(TmH(oph),n1),n2),Set)
	    end
	| _ -> raise (Failure("Non-function applied to an argument"))
      end
  | Info(InfNam("->"),a1,a2) ->
      let n1 = check_tm a1 Prop poly sgtmof sgtm cxtp cxtm in
      let n2 = check_tm a2 Prop poly sgtmof sgtm cxtp cxtm in
      (Imp(n1,n2),Prop)
  | Bi("fun",bvl,a1) ->
      extract_tm_lam bvl a1 poly sgtmof sgtm cxtp cxtm
  | Bi("forall",bvl,a1) ->
      (check_tm_all bvl a1 poly sgtmof sgtm cxtp cxtm,Prop)
(*** With user declared binders, split into several different cases:
 Look up x in bindersem to get (plus,a,bo) where a is an atree and bo is an optional atree.
 Extract the term atm and type atp from a.
 Below alpha, beta and gamma are monomorphic.
 Consider the cases for atp:
 1. If atp is (?0->prop)->?0 (e.g., Eps/some), then there must be 1 bound variable and a Tp or Set ascription. ?0 is replaced by the ascripted Tp or Set.
    [There are actually two cases based on whether or not a connective is given.]
 2. If atp is (?0->beta)->beta (e.g., ex/exists pre In) and bo is None, then there can be many bound variables, but they must all be ascribed Tps
    (or, if None, then the ascription is assumed to be Tp set) and
    the resulting term will be the beta atm[?0:=tp1] (fun x1:tp1 => ... atm[?0:=tpn] (fun xn:tpn => body) ... )
 3. If atp is (?0->prop)->prop (e.g., ex/exists post In) and bo is Some btm of type prop->prop->prop (e.g., and), then
    there can be many variables and they must all either be ascribed to Tp, Set, or Subeq, or if no ascription is given it is assumed to be Tp set.
    Variables ascribed with Tps are handled as in the case above, and for variables ascribed with Set or Subeq,
    the connective given by btm is use to conjoin the body with a corresponding :e prop or c= prop.
In the remaining cases, atp is monomorphic (no TpVars):
 4. If atp is (alpha->beta)->beta and bo is None, then there can be many bound variables, but they must all be ascribed Tps matching alpha or without ascription.
    The resulting term will be atm (fun x1 => ... atm (fun xn => body) ...)
 5. If atp is (set->prop)->prop and bo is Some btm of type prop->prop->prop, then there can be many bound variables,
    and each is either unascribed, has Tp set, or has a Set or Subeq ascription.
    The resulting term will be atm (fun x1 => [btm x1:e/co..] ... atm (fun xn => [btm xn:e/co..] body) ...)
 6. If atp is set->(set->beta)->beta and bo is None, then there can be many variables and each must be ascribed a Set or Subeq.
    The resulting term will be atm A1 (fun x1 => ... atm An (fun xn => body) ...)
    where Ai is either the i'th Set ascr or is Power Ai' where Ai' is the i'th Subeq ascr.
 7. If atp is (alpha->beta)->gamma, then there must be a single variable with either no ascription or a Tp ascription maching alpha.
    The resulting term will be atm (fun x:alpha => body) of type gamma.
 Other possibilities are errors.
 ***)
  | Bi(x,[],a1) -> raise (Failure("Binder " ^ x ^ " should bind at least one variable."))
  | Bi(x,bvl,body) ->
      begin
	try
	  let (plus,xb,xco) = Hashtbl.find bindersem x in
	  match xb with
	  | Na(xbn) when List.mem_assoc (xbn,1) poly ->
	      begin
		let bindop = List.assoc xbn sgtm cxtp cxtm in
		let bindoptp = List.assoc (xbn,1) poly in
		match (bindoptp,xco) with
		| (Ar(Ar(TpVar 0,Prop),TpVar 0),None) -> (*** Case 1 ***)
		    begin
		      match bvl with
		      | [([y],Some (AscTp,ya))] ->
			  let ytp = extract_tp ya cxtp in
			  let bodytm = check_tm body Prop poly sgtmof sgtm cxtp ((y,(ytp,None))::cxtm) in
			  (Ap(TpAp(bindop,ytp),Lam(ytp,bodytm)),ytp)
		      | _ -> raise (Failure(x ^ " should only bind one variable and that variable should be ascribed a type."))
		    end
		| (Ar(Ar(TpVar 0,Prop),TpVar 0),Some xc) -> (*** Case 1 ***)
		    begin
		      match bvl with
		      | [([y],Some (AscTp,ya))] ->
			  let ytp = extract_tp ya cxtp in
			  let bodytm = check_tm body Prop poly sgtmof sgtm cxtp ((y,(ytp,None))::cxtm) in
			  (Ap(TpAp(bindop,ytp),Lam(ytp,bodytm)),ytp)
		      | [([y],Some (AscSet,ya))] ->
			  begin
			    match !setIn with
			    | None -> raise (Failure(":e not declared"))
			    | Some sIn ->
				let c = check_tm xc (Ar(Prop,Ar(Prop,Prop))) poly sgtmof sgtm cxtp cxtm in
				let yatm = check_tm ya Set poly sgtmof sgtm cxtp cxtm in
				let bodytm = check_tm body Prop poly sgtmof sgtm cxtp ((y,(Set,None))::cxtm) in
				(Ap(TpAp(bindop,Set),Lam(Set,Ap(Ap(c,Ap(Ap(TmH(sIn),DB(0)),tmshift 0 1 yatm)),bodytm))),Set)
			  end
		      | [([y],Some (AscSubeq,ya))] ->
			  begin
			    match !setSubeq with
			    | None -> raise (Failure("c= not declared"))
			    | Some sSubeq ->
				let c = check_tm xc (Ar(Prop,Ar(Prop,Prop))) poly sgtmof sgtm cxtp cxtm in
				let yatm = check_tm ya Set poly sgtmof sgtm cxtp cxtm in
				let bodytm = check_tm body Prop poly sgtmof sgtm cxtp ((y,(Set,None))::cxtm) in
				(Ap(TpAp(bindop,Set),Lam(Set,Ap(Ap(c,Ap(Ap(TmH(sSubeq),DB(0)),tmshift 0 1 yatm)),bodytm))),Set)
			  end
		      | _ -> raise (Failure(x ^ " should only bind one variable."))
		    end
		| (Ar(Ar(TpVar 0,beta),beta2),None) when notpvarsp beta && beta = beta2 -> (*** Case 2 ***)
		    if not plus && multbvarsp bvl then raise (Failure(x ^ " can only bind one variable"));
		    let m = check_tm_bind2 x bindop beta bvl body poly sgtmof sgtm cxtp cxtm in
		    (m,beta)
		| (Ar(Ar(TpVar 0,Prop),Prop),Some xc) -> (*** Case 3 ***)
		    if not plus && multbvarsp bvl then raise (Failure(x ^ " can only bind one variable"));
		    let c = check_tm xc (Ar(Prop,Ar(Prop,Prop))) poly sgtmof sgtm cxtp cxtm in
		    let m = check_tm_bind3 x bindop c bvl body poly sgtmof sgtm cxtp cxtm in
		    (m,Prop)
		| _ -> raise (Failure("The binder " ^ x ^ " cannot be used in this way."))
	      end
	  | _ -> (*** monomorphic ***)
	      begin
		let (bindop,bindoptp) = extract_tm xb poly sgtmof sgtm cxtp cxtm in
		match (bindoptp,xco) with
		| (Ar(Ar(alpha,beta),beta2),None) when notpvarsp alpha && notpvarsp beta && beta = beta2 -> (*** Case 4 ***)
		    if not plus && multbvarsp bvl then raise (Failure(x ^ " can only bind one variable"));
		    let m = check_tm_bind4 x bindop alpha beta bvl body poly sgtmof sgtm cxtp cxtm in
		    (m,beta)
		| (Ar(Ar(Set,Prop),Prop),Some xc) -> (*** Case 5 ***)
		    if not plus && multbvarsp bvl then raise (Failure(x ^ " can only bind one variable"));
		    let c = check_tm xc (Ar(Prop,Ar(Prop,Prop))) poly sgtmof sgtm cxtp cxtm in
		    let m = check_tm_bind5 x bindop c bvl body poly sgtmof sgtm cxtp cxtm in
		    (m,Prop)
		| (Ar(Set,Ar(Ar(Set,beta),beta2)),None) when notpvarsp beta && beta = beta2 -> (*** Case 6 ***)
		    if not plus && multbvarsp bvl then raise (Failure(x ^ " can only bind one variable"));
		    let m = check_tm_bind6 x bindop beta bvl body poly sgtmof sgtm cxtp cxtm in
		    (m,beta)
		| (Ar(Ar(alpha,beta),gamma),None) when notpvarsp alpha && notpvarsp beta && notpvarsp gamma -> (*** Case 7 ***)
		    begin
		      match bvl with
		      | [([y],None)] ->
			  let bodytm = check_tm body beta poly sgtmof sgtm cxtp ((y,(alpha,None))::cxtm) in
			  (Ap(bindop,Lam(alpha,bodytm)),gamma)
		      | [([y],Some (AscTp,ya))] ->
			  let ytp = extract_tp ya cxtp in
			  if ytp = alpha then
			    let bodytm = check_tm body beta poly sgtmof sgtm cxtp ((y,(alpha,None))::cxtm) in
			    (Ap(bindop,Lam(alpha,bodytm)),gamma)
			  else
			    raise (Failure(x ^ " must bind one variable with type " ^ tp_to_str alpha))
		      | _ -> raise (Failure(x ^ " should only bind one variable which has type " ^ tp_to_str alpha))
		    end
		| _ -> raise (Failure("The binder " ^ x ^ " cannot be used in this way."))
	      end
	with Not_found ->
	  raise (Failure("Unknown binder " ^ x ^ " -- bug"))
      end
  | Info(InfNam(x),a1,a2) ->
      let xs = Hashtbl.find infixsem x in
      begin
	try
	  match xs with
	  | Na xo ->
	      begin
		match List.assoc (xo,1) poly with (*** intended for =, but could handle similar polymorphic infix operators; I'm not inclined to make it too general though ***)
		| Ar(TpVar 0,Ar(TpVar 0,rtp)) ->
		    let (a1tm,a1tp) = extract_tm a1 poly sgtmof sgtm cxtp cxtm in
		    let a2tm = check_tm a2 a1tp poly sgtmof sgtm cxtp cxtm in
		    let xd = List.assoc xo sgtm cxtp cxtm in
		    (Ap(Ap(TpAp(xd,a1tp),a1tm),a2tm),tpsubst rtp [a1tp])
		| _ -> raise (Failure(x ^ " has an inappropriate type to be a polymorphic infix operator; expected ?0 -> ?0 -> ..."))
	      end
	  | _ -> raise Not_found
	with Not_found ->
	  let (n,ntp) = extract_tm xs poly sgtmof sgtm cxtp cxtm in
	  begin
	    match ntp with
	    | Ar(a1tp,Ar(a2tp,rtp)) ->
		let a1tm = check_tm a1 a1tp poly sgtmof sgtm cxtp cxtm in
		let a2tm = check_tm a2 a2tp poly sgtmof sgtm cxtp cxtm in
		(Ap(Ap(n,a1tm),a2tm),rtp)
	    | _ -> raise (Failure (x ^ " does not have the type of something expecting two arguments"))
	  end
      end
  | Info(InfSet(InfMem),a1,a2) ->
      begin
	match !setIn with
	| None -> raise (Failure(":e not declared"))
	| Some sIn ->
	    let a1tm = check_tm a1 Set poly sgtmof sgtm cxtp cxtm in
	    let a2tm = check_tm a2 Set poly sgtmof sgtm cxtp cxtm in
	    (Ap(Ap(TmH(sIn),a1tm),a2tm),Prop)
      end
  | Info(InfSet(InfSubq),a1,a2) ->
      let (a1tm,a1tp) = extract_tm a1 poly sgtmof sgtm cxtp cxtm in
      begin
	let (argtpl,rtp) = tp_args_rtp a1tp in
	match rtp with
	| Prop ->
	    let a2tm = check_tm a2 a1tp poly sgtmof sgtm cxtp cxtm in
	    (mk_forall_tm argtpl (fun a b -> Imp(a,b)) a1tm a2tm,Prop)
	| Set ->
	    begin
	      match !setSubeq with
	      | None -> raise (Failure("c= not declared for sets (yet)"))
	      | Some sSubeq ->
		  let a2tm = check_tm a2 a1tp poly sgtmof sgtm cxtp cxtm in
		  (mk_forall_tm argtpl (fun a b -> Ap(Ap(TmH(sSubeq),a),b)) a1tm a2tm,Prop)
	    end
	| _ -> raise (Failure("c= cannot be used with type " ^ tp_to_str a1tp))
      end
  | Posto(x,a1) ->
      let xs = Hashtbl.find postfixsem x in
      let (n,ntp) = extract_tm xs poly sgtmof sgtm cxtp cxtm in
      begin
	match ntp with
	| Ar(a1tp,rtp) ->
	    let a1tm = check_tm a1 a1tp poly sgtmof sgtm cxtp cxtm in
	    (Ap(n,a1tm),rtp)
	| _ -> raise (Failure (x ^ " does not have the type of something expecting two arguments"))
      end
  | Preo(x,a1) ->
      let xs = Hashtbl.find prefixsem x in
      let (n,ntp) = extract_tm xs poly sgtmof sgtm cxtp cxtm in
      begin
	match ntp with
	| Ar(a1tp,rtp) ->
	    let a1tm = check_tm a1 a1tp poly sgtmof sgtm cxtp cxtm in
	    (Ap(n,a1tm),rtp)
	| _ -> raise (Failure (x ^ " does not have the type of something expecting two arguments"))
      end
  | MTuple(a,bl) ->
      let l = 1 + List.length bl in
      let (n,ntp) = extract_tm a poly sgtmof sgtm cxtp cxtm in
      let ml = List.map (fun b -> check_tm b ntp poly sgtmof sgtm cxtp cxtm) bl in
      let rec mtupletpaux i r =
	if i > 0 then
	  mtupletpaux (i-1) (Ar(ntp,r))
	else
	  r
      in
      let ltp = mtupletpaux l ntp in
      let rec mtupleconstrap i r =
	if i > 0 then
	  mtupleconstrap (i-1) (Ap(r,DB(i)))
	else
	  r
      in
      let rec mtupleconstr i =
	if i > 0 then
	  Lam(ntp,mtupleconstr (i-1))
	else
	  Lam(Ar(ltp,ntp),mtupleconstrap l (DB(0)))
      in
      let r = List.fold_left (fun r m -> Ap(r,m)) (mtupleconstr l) (n::ml) in
      (r,Ar(ltp,ntp))
  | Rep(x,InfMem,a,b) ->
      begin
	match !replop with
	| Some rop ->
	    let atm = check_tm a Set poly sgtmof sgtm cxtp ((x,(Set,None))::cxtm) in
	    let btm = check_tm b Set poly sgtmof sgtm cxtp cxtm in
	    (Ap(Ap(TmH(rop),btm),Lam(Set,atm)),Set)
	| None -> raise (Failure("{..|x :e ..} notation can only be used after Notation Repl is declared"))
      end
  | Rep(x,InfSubq,a,b) ->
      begin
	match (!replop,!setPow) with
	| (Some rop,Some sPow) ->
	    let atm = check_tm a Set poly sgtmof sgtm cxtp ((x,(Set,None))::cxtm) in
	    let btm = check_tm b Set poly sgtmof sgtm cxtp cxtm in
	    (Ap(Ap(TmH(rop),Ap(TmH(sPow),btm)),Lam(Set,atm)),Set)
	| (None,_) -> raise (Failure("{..|x c= ..} notation can only be used after Notation Repl is declared"))
	| (_,None) -> raise (Failure("{..|x c= ..} notation can only be used after Power is declared"))
      end
  | Sep(x,InfMem,a,b) ->
      begin
	match !sepop with
	| Some sop ->
	    let atm = check_tm a Set poly sgtmof sgtm cxtp cxtm in
	    let btm = check_tm b Prop poly sgtmof sgtm cxtp ((x,(Set,None))::cxtm) in
	    (Ap(Ap(TmH(sop),atm),Lam(Set,btm)),Set)
	| None -> raise (Failure("{x :e .. | ..} notation can only be used after Notation Sep is declared"))
      end
  | Sep(x,InfSubq,a,b) ->
      begin
	match (!sepop,!setPow) with
	| (Some sop,Some sPow) ->
	    let atm = check_tm a Set poly sgtmof sgtm cxtp cxtm in
	    let btm = check_tm b Prop poly sgtmof sgtm cxtp ((x,(Set,None))::cxtm) in
	    (Ap(Ap(TmH(sop),Ap(TmH(sPow),atm)),Lam(Set,btm)),Set)
	| (None,_) -> raise (Failure("{x c= .. | ..} notation can only be used after Notation Sep is declared"))
	| (_,None) -> raise (Failure("{x c= .. | ..} notation can only be used after Power is declared"))
      end
  | SepRep(x,InfMem,a,b,c) ->
      begin
	match !replsepop with
	| Some rsop ->
	    let atm = check_tm a Set poly sgtmof sgtm cxtp ((x,(Set,None))::cxtm) in
	    let btm = check_tm b Set poly sgtmof sgtm cxtp cxtm in
	    let ctm = check_tm c Prop poly sgtmof sgtm cxtp ((x,(Set,None))::cxtm) in
	    (Ap(Ap(Ap(TmH(rsop),btm),Lam(Set,ctm)),Lam(Set,atm)),Set)
	| None -> raise (Failure("{.. |x :e .., ..} notation can only be used after Notation SepRepl is declared"))
      end
  | SepRep(x,InfSubq,a,b,c) ->
      begin
	match (!replsepop,!setPow) with
	| (Some rsop,Some sPow) ->
	    let atm = check_tm a Set poly sgtmof sgtm cxtp ((x,(Set,None))::cxtm) in
	    let btm = check_tm b Set poly sgtmof sgtm cxtp cxtm in
	    let ctm = check_tm c Prop poly sgtmof sgtm cxtp ((x,(Set,None))::cxtm) in
	    (Ap(Ap(Ap(TmH(rsop),Ap(TmH(sPow),btm)),Lam(Set,ctm)),Lam(Set,atm)),Set)
	| (None,_) -> raise (Failure("{.. |x c= .., ..} notation can only be used after Notation SepRepl is declared"))
	| (_,None) -> raise (Failure("{.. |x c= .., ..} notation can only be used after Power is declared"))
      end
  | LeM(x,xl,a,b) ->
      begin
	let (atm,atp) = extract_tm a poly sgtmof sgtm cxtp cxtm in
	try
	  let (xtp,n) = invert_mtupletp atp in
	  if n = 1+List.length xl then
	    let rec nlam n m =
	      if n > 0 then
		nlam (n-1) (Lam(xtp,m))
	      else
		m
	    in
	    let i = ref (-1) in
	    let ncxtm = List.map (fun x -> incr i; (x,(xtp,Some (Ap(atm,nlam n (DB(!i))))))) (List.rev (x::xl)) in
	    extract_tm b poly sgtmof sgtm cxtp (ncxtm @ cxtm)
	  else
	    raise (Failure("The term in 'let [...] := <term>' has type of an " ^ string_of_int n ^ "-metatuple while " ^ (string_of_int (1+List.length xl)) ^ " variables were given."))
	with Not_found ->
	  raise (Failure("The term in 'let [...] := <term>' has type " ^ tp_to_str atp ^ " which is not a meta-tuple type"))
      end
  | IfThenElse(a,b,c) ->
      begin
	match !ifop with
	| Some iop ->
	    let atm = check_tm a Prop poly sgtmof sgtm cxtp cxtm in
	    let (btm,btp) = extract_tm b poly sgtmof sgtm cxtp cxtm in
	    let ctm = check_tm c btp poly sgtmof sgtm cxtp cxtm in
	    (Ap(Ap(Ap(TpAp(TmH(iop),btp),atm),btm),ctm),btp)
	| None ->
	    raise (Failure("if ... then ... else ... cannot be used until Notation for IfThenElse has been declared."))
      end
  | SetEnum(al) ->
      let n = List.length al in
      begin
	match (!setenumadj) with
	| Some seadj ->
	    let atml = List.map (fun a -> check_tm a Set poly sgtmof sgtm cxtp cxtm) al in
            let rec senr i rtml =
	      begin
		try
		  match List.nth !setenuml i with
		  | None -> raise (Failure("nth"))
		  | Some(sei) -> mk_gen_ap (TmH(sei)) (List.rev rtml)
		with Failure("nth") ->
		  if i > 0 then
		    begin
		      match rtml with
		      | (rtm::rtmr) -> Ap(Ap(TmH(seadj),senr (i-1) rtmr),rtm)
		      | [] -> raise (Failure("Should never happen since i should be |rtml|"))
		    end
		  else
		    raise (Failure("There is no way to interpret {}, which is surprising."))
	      end
	    in
	    (senr n (List.rev atml),Set)
	| None ->
	    begin
	      try
		match List.nth !setenuml n with
		| None -> raise (Failure("nth"))
		| Some(sen) ->
		    let atml = List.map (fun a -> check_tm a Set poly sgtmof sgtm cxtp cxtm) al in
		    (mk_gen_ap (TmH(sen)) atml,Set)
	      with Failure("nth") -> raise (Failure("No notation has been declared for {...,...} with " ^ (string_of_int n) ^ " elements"))
	    end
      end
  | Nu(false,n,None,None) -> (** Nat (nonnegative integer) **)
      let n = int_of_string n in
      begin
	match (!nat0,!natS) with
	| (Some h0,Some hS) ->
	    (tm_buildnat h0 hS n,Set)
	| _ -> raise (Failure("A notation for natural numbers has not been declared"))
      end
  | Tuple(a,b,cl) -> (*** I'm commiting to (fun i :e X => if i = 0 then a else if i = 1 then b else ...) here in the code. - Chad, Feb 26 2014 ***)
      begin
	match (!eqSet,!ifop,!setlam,!nat0,!natS) with
	| (eop,Some iop,Some slam,Some h0,Some hS) ->
	    let n = 2+List.length cl in
	    let rec mk_tuple_body i xi xs =
	      let xitm = check_tm xi Set poly sgtmof sgtm cxtp cxtm in
	      match xs with
	      | [] -> tmshift 0 1 xitm
	      | (xj::xr) ->
		  Ap(Ap(Ap(TpAp(TmH(iop),Set),Ap(Ap(TmH(eop),DB(0)),tm_buildnat h0 hS i)),tmshift 0 1 xitm),mk_tuple_body (i+1) xj xr)
	    in
	    (Ap(Ap(TmH(slam),tm_buildnat h0 hS n),Lam(Set,mk_tuple_body 0 a (b::cl))),Set)
	| _ -> raise (Failure("Tuples cannot be used until natural numbers, if-then-else and set-level lambdas have been declared."))
      end
  | _ ->
      if (!verbosity > 3) then (Printf.printf "Could not compute a term corresponding to "; output_ltree stdout (atree_to_ltree a); Printf.printf "\n"; flush stdout);
      raise (Failure "Ill-formed term")
and check_tm a mtp poly sgtmof sgtm cxtp cxtm =
  match a with
  | Bi("fun",bvl,a1) ->
      check_tm_lam mtp bvl a1 poly sgtmof sgtm cxtp cxtm
  | _ ->
      let (n,ntp) = extract_tm a poly sgtmof sgtm cxtp cxtm in
      if ntp = mtp then
	n
      else
	raise (Failure("Type Error found " ^ (tp_to_str ntp) ^ " expected " ^ (tp_to_str mtp)))
and check_tm_all bvl body poly sgtmof sgtm cxtp cxtm =
  match bvl with
  | [] -> check_tm body Prop poly sgtmof sgtm cxtp cxtm
  | ([],_)::bvr -> check_tm_all bvr body poly sgtmof sgtm cxtp cxtm
  | (xl,None)::bvr -> (*** if no ascription is given, assume it is Set ***)
      let n = check_tm_all bvr body poly sgtmof sgtm cxtp ((List.map (fun x -> (x,(Set,None))) (List.rev xl)) @ cxtm) in
      List.fold_right (fun x n1 -> All(Set,n1)) xl n
  | (xl,Some(AscTp,a1))::bvr ->
      let a1tp = extract_tp a1 cxtp in
      let n = check_tm_all bvr body poly sgtmof sgtm cxtp ((List.map (fun x -> (x,(a1tp,None))) (List.rev xl)) @ cxtm) in
      List.fold_right (fun x n1 -> All(a1tp,n1)) xl n
  | (xl,Some(AscSet,a1))::bvr ->
      begin
	match !setIn with
	| None -> raise (Failure(":e not declared"))
	| Some sIn ->
	    let a1s = check_tm a1 Set poly sgtmof sgtm cxtp cxtm in
	    let n = check_tm_all bvr body poly sgtmof sgtm cxtp ((List.map (fun x -> (x,(Set,None))) (List.rev xl)) @ cxtm) in
	    let sh = ref (1+(List.length xl)) in
	    List.fold_right (fun x n1 -> decr sh; All(Set,Imp(Ap(Ap(TmH(sIn),DB(0)),tmshift 0 !sh a1s),n1))) xl n
      end
  | (xl,Some(AscSubeq,a1))::bvr ->
      begin
	match !setSubeq with
	| None -> raise (Failure("c= not declared"))
	| Some sSubeq ->
	    let a1s = check_tm a1 Set poly sgtmof sgtm cxtp cxtm in
	    let n = check_tm_all bvr body poly sgtmof sgtm cxtp ((List.map (fun x -> (x,(Set,None))) (List.rev xl)) @ cxtm) in
	    let sh = ref (1+(List.length xl)) in
	    List.fold_right (fun x n1 -> decr sh; All(Set,Imp(Ap(Ap(TmH(sSubeq),DB(0)),tmshift 0 !sh a1s),n1))) xl n
      end
and extract_tm_lam bvl body poly sgtmof sgtm cxtp cxtm =
  match bvl with
  | [] -> extract_tm body poly sgtmof sgtm cxtp cxtm
  | ([],_)::bvr -> extract_tm_lam bvr body poly sgtmof sgtm cxtp cxtm
  | (x::_,None)::_ -> raise (Failure ("Could not infer type of lambda bound variable " ^ x))
  | (xl,Some(AscTp,a1))::bvr ->
      let a1tp = extract_tp a1 cxtp in
      let (n,ntp) = extract_tm_lam bvr body poly sgtmof sgtm cxtp ((List.map (fun x -> (x,(a1tp,None))) (List.rev xl)) @ cxtm) in
      (List.fold_right (fun x n1 -> Lam(a1tp,n1)) xl n,List.fold_right (fun x n1tp -> Ar(a1tp,n1tp)) xl ntp)
  | (xl,Some(AscSet,a1))::bvr ->
      begin
	match !setlam with
	| None -> raise (Failure("Set level lambdas have not been declared"))
	| Some slam ->
	    let a1s = check_tm a1 Set poly sgtmof sgtm cxtp cxtm in
	    let n = check_tm_lam Set bvr body poly sgtmof sgtm cxtp ((List.map (fun x -> (x,(Set,None))) (List.rev xl)) @ cxtm) in
	    (List.fold_right (fun x n1 -> Ap(Ap(TmH(slam),a1s),Lam(Set,n1))) xl n,Set)
      end
  | (xl,Some(AscSubeq,a1))::bvr ->
      begin
	match (!setlam,!setPow) with
	| (None,_) -> raise (Failure("Set level lambdas have not been declared"))
	| (_,None) -> raise (Failure("Set level lambdas can only be used with c= when power sets are declared"))
	| (Some slam,Some sPow) ->
	    let a1s = check_tm a1 Set poly sgtmof sgtm cxtp cxtm in
	    let n = check_tm_lam Set bvr body poly sgtmof sgtm cxtp ((List.map (fun x -> (x,(Set,None))) (List.rev xl)) @ cxtm) in
	    (List.fold_right (fun x n1 -> Ap(Ap(TmH(slam),Ap(TmH(sPow),a1s)),Lam(Set,n1))) xl n,Set)
      end
and check_tm_lam btp bvl body poly sgtmof sgtm cxtp cxtm =
  match bvl with
  | [] -> check_tm body btp poly sgtmof sgtm cxtp cxtm
  | ([],_)::bvr -> check_tm_lam btp bvr body poly sgtmof sgtm cxtp cxtm
  | (x::xr,None)::bvr ->
      begin
	match btp with
	| Ar(b1,b2) ->
	    let n = check_tm_lam b2 ((xr,None)::bvr) body poly sgtmof sgtm cxtp ((x,(b1,None))::cxtm) in
	    Lam(b1,n)
	| _ ->
	    raise (Failure "fun expected to be of non-functional type")
      end
  | (x::xr,Some(AscTp,a1))::bvr ->
      begin
	let a1tp = extract_tp a1 cxtp in (*** It's wasteful to recompute this for each bound variable. I should write an auxiliary function. A similar remark holds for the other cases below. ***)
	match btp with
	| Ar(b1,b2) ->
	    if b1 = a1tp then
	      let n = check_tm_lam b2 ((xr,None)::bvr) body poly sgtmof sgtm cxtp ((x,(b1,None))::cxtm) in
	      Lam(b1,n)
	    else
	      raise (Failure ("domain of fun is expected to be " ^ (tp_to_str b1) ^ " but given as " ^ (tp_to_str a1tp)))
	| _ ->
	    raise (Failure "fun expected to be of non-functional type")
      end
  | (x::xr,Some(AscSet,a1))::bvr ->
      if btp = Set then
	begin
	  match !setlam with
	  | None -> raise (Failure("Set level lambdas have not been declared"))
	  | Some slam ->
	      let a1s = check_tm a1 Set poly sgtmof sgtm cxtp cxtm in
	      let n = check_tm_lam Set ((xr,None)::bvr) body poly sgtmof sgtm cxtp ((x,(Set,None))::cxtm) in
	      Ap(Ap(TmH(slam),a1s),Lam(Set,n))
	end
      else
	raise (Failure "Set level lambda expected to have to be of non-Set type")
  | (x::xr,Some(AscSubeq,a1))::bvr ->
      if btp = Set then
	begin
	  match (!setlam,!setPow) with
	  | (None,_) -> raise (Failure("Set level lambdas have not been declared"))
	  | (_,None) -> raise (Failure("Set level lambdas can only be used with c= when power sets are declared"))
	  | (Some slam,Some sPow) ->
	      let a1s = check_tm a1 Set poly sgtmof sgtm cxtp cxtm in
	      let n = check_tm_lam Set ((xr,None)::bvr) body poly sgtmof sgtm cxtp ((x,(Set,None))::cxtm) in
	      Ap(Ap(TmH(slam),Ap(TmH(sPow),a1s)),Lam(Set,n))
	end
      else
	raise (Failure "Set level lambda expected to have to be of non-Set type")
and check_tm_bind2 x bindop beta bvl body poly sgtmof sgtm cxtp cxtm =
  match bvl with
  | [] ->
      let m = check_tm body beta poly sgtmof sgtm cxtp cxtm in
      m
  | ([],_)::bvr -> raise (Failure("Empty list of variables to be bound with " ^ x))
  | (yl,None)::bvr -> (*** assume Set if no ascription is given ***)
      check_tm_bind2b x bindop beta yl Set bvr body poly sgtmof sgtm cxtp cxtm
  | (yl,Some(AscTp,ya))::bvr ->
      let ytp = extract_tp ya cxtp in
      check_tm_bind2b x bindop beta yl ytp bvr body poly sgtmof sgtm cxtp cxtm
  | (_,Some(AscSet,_))::_ -> raise (Failure("Variables bound with " ^ x ^ " must be ascribed a type (using :) not a set"))
  | (_,Some(AscSubeq,_))::_ -> raise (Failure("Variables bound with " ^ x ^ " must be ascribed a type (using :) not a set"))
and check_tm_bind2b x bindop beta yl ytp bvl body poly sgtmof sgtm cxtp cxtm =
  match yl with
  | [] -> check_tm_bind2 x bindop beta bvl body poly sgtmof sgtm cxtp cxtm
  | y::yr ->
      let m = check_tm_bind2b x (tmshift 0 1 bindop) beta yr ytp bvl body poly sgtmof sgtm cxtp ((y,(ytp,None))::cxtm) in
      Ap(TpAp(bindop,ytp),Lam(ytp,m))
and check_tm_bind3 x bindop c bvl body poly sgtmof sgtm cxtp cxtm =
  match bvl with
  | [] ->
      let m = check_tm body Prop poly sgtmof sgtm cxtp cxtm in
      m
  | ([],_)::bvr -> raise (Failure("Empty list of variables to be bound with " ^ x))
  | (yl,None)::bvr -> (*** if no type is ascribed, assume it is set ***)
      check_tm_bind3b x bindop c yl Set bvr body poly sgtmof sgtm cxtp cxtm
  | (yl,Some(AscTp,ya))::bvr ->
      let ytp = extract_tp ya cxtp in
      check_tm_bind3b x bindop c yl ytp bvr body poly sgtmof sgtm cxtp cxtm
  | (yl,Some(AscSet,ya))::bvr ->
      begin
	match !setIn with
	| None -> raise (Failure("Cannot ascribe a variable with :e since :e is not (yet) declared"))
	| Some sIn ->
	    let yset = check_tm ya Set poly sgtmof sgtm cxtp cxtm in
	    check_tm_bind3c x bindop (TmH(sIn)) c yl yset bvr body poly sgtmof sgtm cxtp cxtm
      end
  | (yl,Some(AscSubeq,ya))::bvr ->
      begin
	match !setSubeq with
	| None -> raise (Failure("Cannot ascribe a variable with c= since c= is not (yet) declared"))
	| Some sSubeq ->
	    let yset = check_tm ya Set poly sgtmof sgtm cxtp cxtm in
	    check_tm_bind3c x bindop (TmH(sSubeq)) c yl yset bvr body poly sgtmof sgtm cxtp cxtm
      end
and check_tm_bind3b x bindop c yl ytp bvl body poly sgtmof sgtm cxtp cxtm =
  match yl with
  | [] -> check_tm_bind3 x bindop c bvl body poly sgtmof sgtm cxtp cxtm
  | y::yr ->
      let m = check_tm_bind3b x (tmshift 0 1 bindop) c yr ytp bvl body poly sgtmof sgtm cxtp ((y,(ytp,None))::cxtm) in
      Ap(TpAp(bindop,ytp),Lam(ytp,m))
and check_tm_bind3c x bindop r c yl yset bvl body poly sgtmof sgtm cxtp cxtm =
  match yl with
  | [] -> check_tm_bind3 x bindop c bvl body poly sgtmof sgtm cxtp cxtm
  | y::yr ->
      let yset = tmshift 0 1 yset in
      let m = check_tm_bind3c x (tmshift 0 1 bindop) r (tmshift 0 1 c) yr yset bvl body poly sgtmof sgtm cxtp ((y,(Set,None))::cxtm) in
      Ap(TpAp(bindop,Set),Lam(Set,Ap(Ap(c,Ap(Ap(r,DB(0)),yset)),m)))
and check_tm_bind4 x bindop alpha beta bvl body poly sgtmof sgtm cxtp cxtm =
  match bvl with
  | [] ->
      let m = check_tm body beta poly sgtmof sgtm cxtp cxtm in
      m
  | ([],_)::bvr -> raise (Failure("Empty list of variables to be bound with " ^ x))
  | (yl,Some(AscTp,ya))::bvr ->
      let ytp = extract_tp ya cxtp in
      if ytp = alpha then
	check_tm_bind4b x bindop alpha beta yl bvr body poly sgtmof sgtm cxtp cxtm
      else
	raise (Failure("Variables bound with " ^ x ^ " must have type " ^ tp_to_str alpha))
  | (yl,None)::bvr ->
      check_tm_bind4b x bindop alpha beta yl bvr body poly sgtmof sgtm cxtp cxtm
  | (_,Some(AscSet,_))::_ -> raise (Failure("Variables bound with " ^ x ^ " cannot be ascribed with :e"))
  | (_,Some(AscSubeq,_))::_ -> raise (Failure("Variables bound with " ^ x ^ " cannot be ascribed with c="))
and check_tm_bind4b x bindop alpha beta yl bvl body poly sgtmof sgtm cxtp cxtm =
  match yl with
  | [] -> check_tm_bind4 x bindop alpha beta bvl body poly sgtmof sgtm cxtp cxtm
  | y::yr ->
      let m = check_tm_bind4b x (tmshift 0 1 bindop) alpha beta yr bvl body poly sgtmof sgtm cxtp ((y,(alpha,None))::cxtm) in
      Ap(bindop,Lam(alpha,m))
and check_tm_bind5 x bindop c bvl body poly sgtmof sgtm cxtp cxtm =
  match bvl with
  | [] ->
      let m = check_tm body Prop poly sgtmof sgtm cxtp cxtm in
      m
  | ([],_)::bvr -> raise (Failure("Empty list of variables to be bound with " ^ x))
  | (yl,None)::bvr ->
      check_tm_bind5b x bindop c yl bvr body poly sgtmof sgtm cxtp cxtm
  | (yl,Some(AscTp,ya))::bvr ->
      let ytp = extract_tp ya cxtp in
      if ytp = Set then
	check_tm_bind5b x bindop c yl bvr body poly sgtmof sgtm cxtp cxtm
      else
	raise (Failure("Variables bound with " ^ x ^ " must be of type set"))
  | (yl,Some(AscSet,ya))::bvr ->
      begin
	match !setIn with
	| None -> raise (Failure("Cannot ascribe a variable with :e since :e is not (yet) declared"))
	| Some sIn ->
	    let yset = check_tm ya Set poly sgtmof sgtm cxtp cxtm in
	    check_tm_bind5c x bindop (TmH(sIn)) c yl yset bvr body poly sgtmof sgtm cxtp cxtm
      end
  | (yl,Some(AscSubeq,ya))::bvr ->
      begin
	match !setSubeq with
	| None -> raise (Failure("Cannot ascribe a variable with c= since c= is not (yet) declared"))
	| Some sSubeq ->
	    let yset = check_tm ya Set poly sgtmof sgtm cxtp cxtm in
	    check_tm_bind5c x bindop (TmH(sSubeq)) c yl yset bvr body poly sgtmof sgtm cxtp cxtm
      end
and check_tm_bind5b x bindop c yl bvl body poly sgtmof sgtm cxtp cxtm =
  match yl with
  | [] -> check_tm_bind5 x bindop c bvl body poly sgtmof sgtm cxtp cxtm
  | y::yr ->
      let m = check_tm_bind5b x (tmshift 0 1 bindop) c yr bvl body poly sgtmof sgtm cxtp ((y,(Set,None))::cxtm) in
      Ap(bindop,Lam(Set,m))
and check_tm_bind5c x bindop r c yl yset bvl body poly sgtmof sgtm cxtp cxtm =
  match yl with
  | [] -> check_tm_bind5 x bindop c bvl body poly sgtmof sgtm cxtp cxtm
  | y::yr ->
      let yset = tmshift 0 1 yset in
      let m = check_tm_bind5c x (tmshift 0 1 bindop) r (tmshift 0 1 c) yr yset bvl body poly sgtmof sgtm cxtp ((y,(Set,None))::cxtm) in
      Ap(bindop,Lam(Set,Ap(Ap(c,Ap(Ap(r,DB(0)),yset)),m)))
and check_tm_bind6 x bindop beta bvl body poly sgtmof sgtm cxtp cxtm =
  match bvl with
  | [] ->
      let m = check_tm body beta poly sgtmof sgtm cxtp cxtm in
      m
  | ([],_)::bvr -> raise (Failure("Empty list of variables to be bound with " ^ x))
  | (_,None)::_ ->
      raise (Failure("Variables bound by " ^ x ^ " must be ascribed a set with :e or c="))
  | (_,Some(AscTp,_))::_ ->
      raise (Failure("Variables bound by " ^ x ^ " must be ascribed a set with :e or c="))
  | (yl,Some(AscSet,ya))::bvr ->
      begin
	let yset = check_tm ya Set poly sgtmof sgtm cxtp cxtm in
	check_tm_bind6b x bindop beta yl yset bvr body poly sgtmof sgtm cxtp cxtm
      end
  | (yl,Some(AscSubeq,ya))::bvr ->
      begin
	match !setPow with
	| None -> raise (Failure("Cannot ascribe a " ^ x ^ " bound variable with c= since Power is not (yet) declared"))
	| Some sPow ->
	    let yset = check_tm ya Set poly sgtmof sgtm cxtp cxtm in
	    check_tm_bind6c x bindop beta (TmH(sPow)) yl yset bvr body poly sgtmof sgtm cxtp cxtm
      end
and check_tm_bind6b x bindop beta yl yset bvl body poly sgtmof sgtm cxtp cxtm =
  match yl with
  | [] -> check_tm_bind6 x bindop beta bvl body poly sgtmof sgtm cxtp cxtm
  | y::yr ->
      let m = check_tm_bind6b x (tmshift 0 1 bindop) beta yr (tmshift 0 1 yset) bvl body poly sgtmof sgtm cxtp ((y,(Set,None))::cxtm) in
      Ap(Ap(bindop,yset),Lam(Set,m))
and check_tm_bind6c x bindop beta p yl yset bvl body poly sgtmof sgtm cxtp cxtm =
  match yl with
  | [] -> check_tm_bind6 x bindop beta bvl body poly sgtmof sgtm cxtp cxtm
  | y::yr ->
      let m = check_tm_bind6c x (tmshift 0 1 bindop) beta p yr (tmshift 0 1 yset) bvl body poly sgtmof sgtm cxtp ((y,(Set,None))::cxtm) in
      Ap(Ap(bindop,Ap(p,yset)),Lam(Set,m))

let rec extract_pf a polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf =
  match a with
  | Na(x) ->
      begin
	try
	  let (apf,atm) = pfproplookup cxpf x in
	  if (!verbosity > 19) then (Printf.printf "Found %s in hyp ctx as pf of %s\n" x (tm_to_str atm); flush stdout);
	  (apf,atm)
	with Not_found ->
	  try
	    if (!verbosity > 19) then (Printf.printf "about to lookup in sgpf %s\n" x; flush stdout);
	    let d = List.assoc x sgpf cxtp cxtm cxpf in
	    let (p,dl) = extr_propofpf sgdelta sgtmof (cxtmdb cxtm) (cxpfdb cxpf) d !deltaset in
	    deltaset := dl;
	    (d,p)
	  with Not_found ->
	    raise (Failure("Unknown proof " ^ x ^ " -- it might be a term in a position where a proof is expected"))
      end
  | Implop(Na(x),a1) when List.mem_assoc (x,1) polyp ->
      let xa = List.assoc (x,1) polyp in
      let a1tp = extract_tp a1 cxtp in
      let xd = List.assoc x sgpf cxtp cxtm cxpf in
      (PTpAp(xd,a1tp),tmtpsubst xa [a1tp])
  | Implop(Implop(Na(x),a1),a2) when List.mem_assoc (x,2) polyp ->
      let xa = List.assoc (x,2) polyp in
      let a1tp = extract_tp a1 cxtp in
      let a2tp = extract_tp a2 cxtp in
      let xd = List.assoc x sgpf cxtp cxtm cxpf in
      (PTpAp(PTpAp(xd,a1tp),a2tp),tmtpsubst xa [a1tp;a2tp])
  | Implop(Implop(Implop(Na(x),a1),a2),a3) when List.mem_assoc (x,3) polyp ->
      let xa = List.assoc (x,3) polyp in
      let a1tp = extract_tp a1 cxtp in
      let a2tp = extract_tp a2 cxtp in
      let a3tp = extract_tp a3 cxtp in
      let xd = List.assoc x sgpf cxtp cxtm cxpf in
      (PTpAp(PTpAp(PTpAp(xd,a1tp),a2tp),a3tp),tmtpsubst xa [a1tp;a2tp;a3tp])
  | Implop(a1,a2) ->
      let (a1pf,a1tm) = extract_pf a1 polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf in
      begin
	let (p,dl) = headnorm a1tm sgdelta !deltaset in
	deltaset := dl;
	match p with
	| Imp(p1,p2) ->
	    let d1 = check_pf a2 p1 polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf in
	    (PPfAp(a1pf,d1),p2)
	| All(b1,p2) ->
	    let m1 = check_tm a2 b1 polyt sgtmof sgtm cxtp cxtm in
	    (PTmAp(a1pf,m1),tmsubst p2 0 m1)
	| _ -> raise (Failure("Proof term applied like a function but is not a proof of an implication or universal quantifier: " ^ (tm_to_str p)))
      end
  | Bi("fun",bvl,a1) ->
      extract_pf_lam bvl a1 polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf
  | Le(x,None,b,body) ->
      begin
	try
	  let (btm,btp) = extract_tm b polyt sgtmof sgtm cxtp cxtm in
	  extract_pf body polyt polyp sgtmof sgdelta sgtm sgpf cxtp ((x,(btp,Some btm))::cxtm) cxpf
	with Failure _ ->
	  let (bpf,btm) = extract_pf b polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf in
	  let (bodypf,bodytm) = extract_pf body polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm ((x,btm)::cxpf) in
	  (PPfAp(PLam(btm,bodypf),bpf),bodytm)
      end
  | Le(x,Some(AscTp,a),b,body) ->
      begin
	try
	  let atp = extract_tp a cxtp in
	  let btm = check_tm b atp polyt sgtmof sgtm cxtp cxtm in
	  extract_pf body polyt polyp sgtmof sgdelta sgtm sgpf cxtp ((x,(atp,Some btm))::cxtm) cxpf
	with Failure _ ->
	  let atm = check_tm a Prop polyt sgtmof sgtm cxtp cxtm in
	  let bpf = check_pf b atm polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf in
	  let (bodypf,bodytm) = extract_pf body polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm ((x,atm)::cxpf) in
	  (PPfAp(PLam(atm,bodypf),bpf),bodytm)
      end
  | Le(x,Some(_,a),b,body) ->
      raise (Failure("let variables in proof terms cannot be ascribed with :e or c="))
  | LeM(x,xl,a,b) ->
      begin
	let (atm,atp) = extract_tm a polyt sgtmof sgtm cxtp cxtm in
	try
	  let (xtp,n) = invert_mtupletp atp in
	  if n = 1+List.length xl then
	    let rec nlam n m =
	      if n > 0 then
		nlam (n-1) (Lam(xtp,m))
	      else
		m
	    in
	    let i = ref (-1) in
	    let ncxtm = List.map (fun x -> incr i; (x,(xtp,Some (Ap(atm,nlam n (DB(!i))))))) (List.rev (x::xl)) in
	    extract_pf b polyt polyp sgtmof sgdelta sgtm sgpf cxtp (ncxtm @ cxtm) cxpf
	  else
	    raise (Failure("The term in 'let [...] := <term>' has type of an " ^ string_of_int n ^ "-metatuple while " ^ (string_of_int (1+List.length xl)) ^ " variables were given."))
	with Not_found ->
	  raise (Failure("The term in 'let [...] := <term>' has type " ^ tp_to_str atp ^ " which is not a meta-tuple type"))
      end
  | _ -> raise (Failure("Unknown proof term construct"))
and extract_pf_lam bvl body polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf =
  match bvl with
  | [] -> extract_pf body polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf
  | ([],_)::bvr -> extract_pf_lam bvr body polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf
  | (x::xr,None)::bvr -> raise (Failure("Cannot infer the type or prop for the proof level lambda bound variable " ^ x))
  | (x::xr,Some(AscTp,b1))::bvr ->
      begin
	try
	  let b1tp = extract_tp b1 cxtp in
	  let (d1,p1) = extract_pf_lam ((xr,Some(AscTp,b1))::bvr) body polyt polyp sgtmof sgdelta sgtm sgpf cxtp ((x,(b1tp,None))::cxtm) (List.map (fun (y,q) -> (y,tmshift 0 1 q)) cxpf) in
	  (TLam(b1tp,d1),All(b1tp,p1))
	with Failure(_) ->
	  let b1tm = check_tm b1 Prop polyt sgtmof sgtm cxtp cxtm in
	  let (d1,p1) = extract_pf_lam ((xr,None)::bvr) body polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm ((x,b1tm)::cxpf) in
	  (PLam(b1tm,d1),Imp(b1tm,p1))
      end
  | (x::xr,Some(AscSet,a1))::bvr ->
      raise (Failure(":e ascriptions are not allowed for proof level lambdas (for now)"))
  | (x::xr,Some(AscSubeq,a1))::bvr ->
      raise (Failure("c= ascriptions are not allowed for proof level lambdas (for now)"))
and check_pf a p polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf =
  match a with
  | Bi("fun",bvl,a1) ->
      check_pf_lam p bvl a1 polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf
  | _ ->
      let (d,dtm) = extract_pf a polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf in
      begin
	match conv p dtm sgdelta !deltaset with
	| Some(dl) -> deltaset := dl; d
	| None ->
	    raise (Failure("Proof term proves " ^ (tm_to_str dtm) ^ " but expected to prove " ^ (tm_to_str p)))
      end
and check_pf_lam p bvl body polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf =
  match bvl with
  | [] -> check_pf body p polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf
  | ([],_)::bvr -> check_pf_lam p bvr body polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm cxpf
  | (x::xr,None)::bvr ->
      begin
	if !verbosity > 49 then (Printf.printf "pre headnorm p = %s\n" (tm_to_str p); flush stdout);
	let (p,dl) = headnorm p sgdelta !deltaset in
	if !verbosity > 49 then (Printf.printf "post headnorm p = %s\n" (tm_to_str p); flush stdout);
	deltaset := dl;
	match p with
	| Imp(p1,p2) ->
	    let d1 = check_pf_lam p2 ((xr,None)::bvr) body polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm ((x,p1)::cxpf) in
	    PLam(p1,d1)
	| All(a1,p2) ->
	    let d1 = check_pf_lam p2 ((xr,None)::bvr) body polyt polyp sgtmof sgdelta sgtm sgpf cxtp ((x,(a1,None))::cxtm) (List.map (fun (y,q) -> (y,tmshift 0 1 q)) cxpf) in
	    TLam(a1,d1)
	| _ -> raise (Failure("Lambda in proof term is expected to prove something other than an implication or universal quantifier: " ^ (tm_to_str p)))
      end
  | (x::xr,Some(AscTp,b1))::bvr -> 
      begin
	let (p,dl) = headnorm p sgdelta !deltaset in
	deltaset := dl;
	match p with
	| Imp(p1,p2) ->
	    let q1 = check_tm b1 Prop polyt sgtmof sgtm cxtp cxtm in
	    begin
	      match conv q1 p1 sgdelta !deltaset with
	      | Some(dl) ->
		  deltaset := dl;
		  let d1 = check_pf_lam p2 ((xr,None)::bvr) body polyt polyp sgtmof sgdelta sgtm sgpf cxtp cxtm ((x,q1)::cxpf) in
		  PLam(q1,d1)
	      | None ->
		  raise (Failure("Lambda bound variable " ^ x ^ " in proof term ascribed prop " ^ (tm_to_str q1) ^ " but expected " ^ (tm_to_str p1)))
	    end
	| All(a1,p2) ->
	    let b1tp = extract_tp b1 cxtp in (*** It's wasteful to recompute this for each bound variable. I should write an auxiliary function. A similar remark holds for the other cases below. ***)
	    if b1tp = a1 then
	      let d1 = check_pf_lam p2 ((xr,Some(AscTp,b1))::bvr) body polyt polyp sgtmof sgdelta sgtm sgpf cxtp ((x,(a1,None))::cxtm) (List.map (fun (y,q) -> (y,tmshift 0 1 q)) cxpf) in
	      TLam(a1,d1)
	    else
	      raise (Failure("Lambda bound variable " ^ x ^ " in proof term ascribed type " ^ (tp_to_str b1tp) ^ " but expected " ^ (tp_to_str a1)))
	| _ -> raise (Failure("Lambda in proof term is expected to prove something other than an implication or universal quantifier: " ^ (tm_to_str p)))
      end
  | (x::xr,Some(AscSet,a1))::bvr ->
      raise (Failure(":e ascriptions are not allowed for proof level lambdas (for now)"))
  | (x::xr,Some(AscSubeq,a1))::bvr ->
      raise (Failure("c= ascriptions are not allowed for proof level lambdas (for now)"))

