(* Copyright (c) 2014 Chad E Brown *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(*** File: mgcheck.ml ***)
(*** Author: Chad E Brown ***)
(*** Date: Jan 21 2014 ***)

open Syntax
open Parser
open Big_int
open Interpret

let reporteachitem : bool ref = ref false
let reportids : bool ref = ref true
let reportpfcomplexity : bool ref = ref false
let webout : bool ref = ref false
let ajax : bool ref = ref false
let ajaxactive : bool ref = ref false
let ajaxpffile : string ref = ref ""
let sqlout : bool ref = ref false
let sqltermout : bool ref = ref false
let presentationonly : bool ref = ref false
let mainfilehash : string option ref = ref None
let solvesproblemfile : string option ref = ref None
let checksigfile : string option ref = ref None

let thmsasexercises : bool ref = ref false
let exercises : string list ref = ref []

let admits : bool ref = ref false

let indoutfile : string option ref = ref None;;
let indextms : (string,tp) Hashtbl.t = Hashtbl.create 1000;;
let indexknowns : (string,unit) Hashtbl.t = Hashtbl.create 1000;;

(*** White 2015, moved the hashes of hardcoded Egal axioms into a separate file "axioms.ml" ***)
(*** The identifiers are different depending on whether or not polyexpand is set, so this command line argument is searched for. ***)
Axioms.initializeknowns indexknowns (List.mem "-polyexpand" (Array.to_list Sys.argv));;

let combsigtm sgtmloc secstack =
  (List.concat
     (List.map (fun l -> List.map (fun (x,m,a,n,b) -> (x,(n,b))) l)
	(sgtmloc::(List.map (fun (_,_,_,stl,_) -> stl) secstack))))

exception AdmittedPf

let rec map_for f i n =
  if i <= n then
    (f i::map_for f (i+1) n)
  else
    [];;

let rec split_list n l =
  if n > 0 then
    match l with
    | (a::r) ->
      let (l1,l2) = split_list (n-1) r in
      (a::l1,l2)
    | [] -> ([],[])
  else
    ([],l)

let read_indexfile c =
  let tl = ref (TokStrRest(Lexer.token,Lexing.from_channel c)) in
  lineno := 1;
  charno := 0;
  try
    while true do
      let (iitem,tr) = parse_indexitem !tl in
      tl := tr;
      match iitem with
      | IndexTm(h,a) ->
	  if not (valid_id_p h) then raise (Failure(h ^ " in index file is not a valid id"));
	  let a = ltree_to_atree a in
	  let atp = extract_tp a [] in
	  begin
	    try
	      let itp = Hashtbl.find indextms h in
	      if itp <> atp then raise (Failure("Mismatch in indexed type assignment for " ^ h))
	    with Not_found ->
	      Hashtbl.add indextms h atp
	  end
      | IndexKnown(h) ->
	  if not (valid_id_p h) then raise (Failure(h ^ " in index file is not a valid id"));
	  if not (Hashtbl.mem indexknowns h) then
	    Hashtbl.add indexknowns h ()
    done
  with
  | Lexer.Eof ->
      ()
  | Failure(x) ->
      if !webout then
	begin
          Printf.printf "AF%d:%d\n"  !lineno !charno;
	  Printf.printf "<div class='documentfail'>Failure reading index file at line %d char %d: %s</div>" !lineno !charno x; flush stdout;
	  exit 1
	end
      else if !ajax then
	begin
	  Printf.printf "f\n" (*** this indicates a fundamental problem, not a problem with the ajax input ***)
	end
      else
	begin
	  Printf.printf "Failure reading index file at line %d char %d: %s\n" !lineno !charno x; flush stdout;
	  exit 1
	end

let html = ref None;;
let inchan = ref None;; (*** This is a possible second channel for reading the input file currently used to record a literal copy of the text of proofs ***)
let inchanline = ref 1;;
let inchanchar = ref 0;;
let includingsigfile = ref false;;
let includedsigfiles = ref [];;
let sigoutfile = ref None;;
let sigtmh : (string,string) Hashtbl.t  = Hashtbl.create 1000;;
let sigknh : (string,string) Hashtbl.t  = Hashtbl.create 1000;;
let sigtmof : (string,ptp) Hashtbl.t  = Hashtbl.create 1000;;
let sigdelta : (string,ptm) Hashtbl.t = Hashtbl.create 1000;;
let sigtm = ref [];;
let sigpf = ref [];;
let polytm = ref [];;
let polypf = ref [];;
let futurepolytm = ref [];;
let futurepolypf = ref [];;
let handlepolysnow () =
  polytm := !futurepolytm @ !polytm;
  polypf := !futurepolypf @ !polypf;
  futurepolytm := [];
  futurepolypf := [];;
let pushpolytm a = futurepolytm := a::!futurepolytm;;
let pushpolypf a = futurepolypf := a::!futurepolypf;;
(*** special cases so that the certain tactics get activated ***)
let activate_special_knowns h =
  if h = !expolyI then
    begin
      expolyIknown := true;
      if !verbosity > 50 then (Printf.printf "Activated expolyI, so that witness tactic can now be used.\n"; flush stdout);
    end
  else if h = !eqsymPoly then
    begin
      eqsymPolyknown := true;
      if !verbosity > 50 then (Printf.printf "Activated eqsymPoly, so that rewrite tactic can now be used without <-.\n"; flush stdout);
    end;;
(*** I could make this more general, but I won't for now. ***)
let extract_exclaim m =
  match m with
  | Ap(TpAp(TmH(e),etp),ep) when e = !expoly -> (etp,ep)
  | _ -> raise Not_found

(*** Output docitems to the signature file, changing theorems to axioms ***)
let outtosigfile soc ditem =
  let outc s = output_char soc s in
  let outs s = output_string soc s in
  let outi i = Printf.fprintf soc "%d" i in
  let outl a = output_ltree soc a in
  let outasckd asck =
    begin
      match asck with
      | AscTp -> outs " : ";
      | AscSet -> outs " :e ";
      | AscSubeq -> outs " c= ";
    end;		    
  in
  begin
    match ditem with
    | Section(x) ->
	outs ("Section " ^ x ^ ".\n")
    | End(x) ->
	outs ("End " ^ x ^ ".\n")
    | VarDecl(xl,asck,a) ->
	outs "Variable";
	List.iter (fun x -> outc ' '; outs x) xl;
	outasckd asck;
	outl a;
	outc '.';
	outc '\n';
    | HypDecl(x,a) ->
	outs ("Hypothesis " ^ x ^ " : ");
	outl a;
	outc '.';
	outc '\n';
    | LetDecl(x,None,b) ->
	outs ("Let " ^ x ^ " := ");
	outl b;
	outc '.';
	outc '\n';
    | LetDecl(x,Some(asck,a),b) ->
	outs "Let ";
	outs x;
	outasckd asck;
	outl a;
	outs " := ";
	outl b;
	outc '.';
	outc '\n';
    | PostInfixDecl(x,a,p,Postfix) ->
	outs "Postfix ";
	outs x;
	outc ' ';
	outi p;
	outs " := ";
	outl a;
	outs ".\n";
    | PostInfixDecl(x,a,p,InfixNone) ->
	outs "Infix ";
	outs x;
	outc ' ';
	outi p;
	outs " := ";
	outl a;
	outs ".\n";
    | PostInfixDecl(x,a,p,InfixLeft) ->
	outs "Infix ";
	outs x;
	outc ' ';
	outi p;
	outs " left ";
	outs " := ";
	outl a;
	outs ".\n";
    | PostInfixDecl(x,a,p,InfixRight) ->
	outs "Infix ";
	outs x;
	outc ' ';
	outi p;
	outs " right ";
	outs " := ";
	outl a;
	outs ".\n";
    | PrefixDecl(x,a,p) ->
	outs "Prefix ";
	outs x;
	outc ' ';
	outi p;
	outs " := ";
	outl a;
	outs ".\n";
    | BinderDecl(plus,comma,x,a,bo) ->
	outs "Binder";
	if plus then outs "+ " else outc ' ';
	outs x;
	if comma then outs " , := " else outs " => := ";
	outl a;
	begin
	  match bo with
	  | Some(b) -> outs " ; "; outl b
	  | None -> ()
	end;
	outs ".\n"
    | UnicodeDecl(x,yl) ->
	outs "(* Unicode ";
	outs x;
	List.iter (fun y ->
	  outs " \"";
	  outs y;
	  outs "\"")
	  yl;
	outs " *)\n"
    | SubscriptDecl(x) ->
	outs "(* Subscript ";
	outs x;
	outs " *)\n"
    | SuperscriptDecl(x) ->
	outs "(* Superscript ";
	outs x;
	outs " *)\n"
    | NotationDecl(x,yl) ->
	outs "Notation ";
	outs x;
	List.iter (fun y -> outc ' '; outs y) yl;
	outs ".\n";
    | ParamHash(x,h) ->
	outs "(* Parameter ";
	outs x;
	outc ' ';
	outs h;
	outs "*)\n";
    | ParamDecl(x,a) ->
	outs "Parameter ";
	outs x;
	outs " : ";
	outl a;
	outs ".\n";
    | DefDecl(x,None,b) ->
	outs "Definition ";
	outs x;
	outs " := ";
	outl b;
	outs ".\n";
    | DefDecl(x,Some a,b) ->
	outs "Definition ";
	outs x;
	outs " : ";
	outl a;
	outs " := ";
	outl b;
	outs ".\n";
    | AxDecl(x,a) ->
	outs "Axiom ";
	outs x;
	outs " : ";
	outl a;
	outs ".\n";
    | ThmDecl(_,x,a) -> (*** Theorems are axioms in the signature. ***)
	outs "Axiom ";
	outs x;
	outs " : ";
	outl a;
	outs ".\n";
    | _ -> ()
  end

let skip_to_line_char c li1 ch1 li2 ch2 =
  try
    while (!li1 < li2) do
      ch1 := 0;
      let z = input_char c in
      if z = '\n' then incr li1;
    done;
    while (!ch1 < ch2) do
      ignore (input_char c);
      incr ch1
    done
  with End_of_file -> () (*** this probably shouldn't happen, but if it does, just stop reading the file ***)

let buffer_to_line_char c b li1 ch1 li2 ch2 =
  try
    while (!li1 < li2) do
      ch1 := 0;
      let z = input_char c in
      Buffer.add_char b z;
      if z = '\n' then incr li1;
    done;
    while (!ch1 < ch2) do
      let z = input_char c in
      Buffer.add_char b z;
      incr ch1
    done
  with End_of_file -> () (*** this probably shouldn't happen, but if it does, just stop reading the file ***)

let ctxtp = ref []
let ctxtm = ref []
let ctxpf = ref []
let tparclos = ref (fun a -> a)
let tmallclos = ref (fun m -> m)
let tmlamclos = ref (fun m -> m)
let pflamclos = ref (fun d -> d)
let aptmloc = ref (fun m cxtp cxtm -> m)
let appfloc = ref (fun d cxtp cxtm cxpf -> d)
let secstack = ref []
let popfn = ref (fun () -> ())

let laststructaction = ref 0;;

let evaluate_docitem_1 ditem =
  begin
    match !sigoutfile with
    | Some soc -> outtosigfile soc ditem
    | None -> ()
  end;
  match ditem with
  | RequireDecl(x) -> () (*** Requires are for Qeditas and are ignored by Egal. - Bill White, May 2015 ***)
  | Author(x,yl) ->
      authors := !authors @ (x::yl);
      begin
	List.iter
	  (fun z ->
	    if !sqlout then
	      begin
		match !mainfilehash with
		| Some docsha ->
		    if not !presentationonly then (Printf.printf "INSERT INTO `docauthor` (`docsha`,`docauthorname`) VALUES ('%s',\"%s\");\n" docsha (String.escaped z));
		| None -> ()
	      end)
	  (x::yl);
      end
  | Title(x) ->
      begin
	match !title with
	| None -> title := Some(x);
	    if !sqlout then
	      begin
		match !mainfilehash with
		| Some docsha ->
		    if not !presentationonly then (Printf.printf "INSERT INTO `doc` (`docsha`,`docname`,`doctitle`,`dockind`,`docreleaseorder`,`docreleasedate`,`docstatus`) VALUES ('%s','%s',\"%s\",'putkind',1,'putrdate','s');\n" docsha Sys.argv.((Array.length Sys.argv) - 1) (String.escaped x));
		| None -> ()
	      end;
	| Some _ -> raise (Failure("Title can only be declared once"))
      end
  | ShowProofTerms(b) -> showproofterms := b
  | Salt(x) -> salt := Some x
  | Treasure(x) ->
      treasure := Some x;
  | Section(x) ->
      begin
	secstack := (x,!popfn,!aptmloc,!appfloc,!sigtm,!sigpf)::!secstack;
	popfn := (fun () -> ());
      end
  | End(x) ->
      begin
	match !secstack with
	| ((y,f,atl,apl,st,sp)::cs) when x = y ->
	    begin
	      !popfn ();
	      popfn := f;
	      aptmloc := atl;
	      appfloc := apl;
	      sigtm := st;
	      sigpf := sp;
	      secstack := cs
	    end
	| ((y,f,atl,apl,stl,spl)::_) -> raise (Failure("Section " ^ y ^ " cannot be ended with End " ^ x))
	| [] -> raise (Failure("No Section To End"))
      end
  | VarDecl(xl,AscTp,NaL "SType") -> (** Type variable **)
      begin
	match (!ctxtp,!ctxtm,!ctxpf) with
	| ([],[],[]) ->
	    ctxtp := xl;
	    if (List.length !ctxtp > 3) then raise (Failure "More than 3 type variables are not allowed.");
	    List.iter (fun x ->
	      let prevaptmloc = !aptmloc in
	      let prevappfloc = !appfloc in
	      aptmloc := (fun m cxtp cxtm -> TpAp(prevaptmloc m cxtp cxtm,tplookup cxtp x));
	      appfloc := (fun d cxtp cxtm cxpf -> PTpAp(prevappfloc d cxtp cxtm cxpf,tplookup cxtp x)))
	      xl;
	    let popfnnow = !popfn in
	    popfn := (fun () -> handlepolysnow (); ctxtp := []; popfnnow ())
	| _ ->
	    raise (Failure "Type variables can only be declared when the context is empty.")
      end
  | VarDecl(xl,AscTp,a) -> (** Ordinary variable **)
      let a = ltree_to_atree a in
      let atp = extract_tp a !ctxtp in
      let prevctxtm = !ctxtm in
      let prevctxpf = !ctxpf in
      let prevtparclos = !tparclos in
      let prevtmallclos = !tmallclos in
      let prevtmlamclos = !tmlamclos in
      let prevpflamclos = !pflamclos in
      ctxtm := (List.map (fun x -> (x,(atp,None))) (List.rev xl)) @ prevctxtm;
      let xln = List.length xl in
      ctxpf := (List.map (fun (y,p) -> (y,tmshift 0 xln p)) prevctxpf); (*** shift the hyp context to account for the fresh vars on the var context ***)
      List.iter (fun x ->
	let prevaptmloc = !aptmloc in
	let prevappfloc = !appfloc in
	aptmloc := (fun m cxtp cxtm -> Ap(prevaptmloc m cxtp cxtm,tmlookup cxtm x));
	appfloc := (fun d cxtp cxtm cxpf -> PTmAp(prevappfloc d cxtp cxtm cxpf,tmlookup cxtm x)))
	xl;
      tparclos := (fun a -> prevtparclos (List.fold_right (fun x b -> Ar(atp,b)) xl a));
      tmallclos := (fun m -> prevtmallclos (List.fold_right (fun x n -> All(atp,n)) xl m));
      tmlamclos := (fun m -> prevtmlamclos (List.fold_right (fun x n -> Lam(atp,n)) xl m));
      pflamclos := (fun d -> prevpflamclos (List.fold_right (fun x e -> TLam(atp,e)) xl d));
      let popfnnow = !popfn in
      popfn := (fun () -> ctxtm := prevctxtm; ctxpf := prevctxpf; tparclos := prevtparclos; tmallclos := prevtmallclos; tmlamclos := prevtmlamclos; pflamclos := prevpflamclos; popfnnow ())
  | VarDecl(xl,AscSet,a) -> (** Variable/Hyp combo, I might allow this later **)
      raise (Failure("Variables must be ascribed a type, not a set"))
  | VarDecl(xl,AscSubeq,a) -> (** Variable/Hyp combo, I might allow this later **)
      raise (Failure("Variables must be ascribed a type, not a set"))
  | HypDecl(x,a) -> (** declare a hypothesis, put into ctxpf, add removal to popfn, update appfloc **)
      let a = ltree_to_atree a in
      let atm = check_tm a Prop !polytm sigtmof !sigtm !ctxtp !ctxtm in
      let prevappfloc = !appfloc in
      let prevtmallclos = !tmallclos in
      let prevpflamclos = !pflamclos in
      let prevctxpf = !ctxpf in
      ctxpf := (x,atm)::prevctxpf;
      appfloc := (fun d cxtp cxtm cxpf -> PPfAp(prevappfloc d cxtp cxtm cxpf,pflookup cxpf x));
      tmallclos := (fun m -> prevtmallclos (Imp(atm,m)));
      pflamclos := (fun d -> prevpflamclos (PLam(atm,d)));
      let popfnnow = !popfn in
      popfn := (fun () -> ctxpf := prevctxpf; tmallclos := prevtmallclos; pflamclos := prevpflamclos; popfnnow ())
  | LetDecl(x,None,b) -> (** add (x,atp[extracted from btm],btm) to ctxtm, add removal to popfn **)
      (*** Note: Let variables do not correspond to de Bruijn indices. There need be no shifting of hypotheses. ***)
      let b = ltree_to_atree b in
      let (btm,btp) = extract_tm b !polytm sigtmof !sigtm !ctxtp !ctxtm in
      let prevctxtm = !ctxtm in
      ctxtm := (x,(btp,Some btm))::prevctxtm;
      let popfnnow = !popfn in
      popfn := (fun () -> ctxtm := prevctxtm; popfnnow ())
  | LetDecl(x,Some (AscTp,a),b) -> (** add (x,atp,btm) to ctxtm, add removal to popfn **)
      let a = ltree_to_atree a in
      let b = ltree_to_atree b in
      let btp = extract_tp a !ctxtp in
      let btm = check_tm b btp !polytm sigtmof !sigtm !ctxtp !ctxtm in
      let prevctxtm = !ctxtm in
      ctxtm := (x,(btp,Some btm))::prevctxtm;
      let popfnnow = !popfn in
      popfn := (fun () -> ctxtm := prevctxtm; popfnnow ())
  | LetDecl(x,Some (_,a),b) -> (*** I doubt I will allow this later since it would require finding a proof that b is in the set a ***)
      raise (Failure("Lets must be ascribed a type, not a set"))
  | PostInfixDecl(x,a,p,pic) ->
      let a = ltree_to_atree a in
      popfn := declare_postinfix x a p pic !popfn
  | PrefixDecl(x,a,p) ->
      let a = ltree_to_atree a in
      popfn := declare_prefix x a p !popfn
  | BinderDecl(plus,comma,x,a,bo) ->
      let a = ltree_to_atree a in
      let bo = (match bo with Some(b) -> Some(ltree_to_atree b) | None -> None) in
      popfn := declare_binder plus comma x a bo !popfn
  | UnicodeDecl(x,ul) ->
      Hashtbl.add unicode x ul; (*** just associate x with ul forever - not contained within a section ***)
  | SubscriptDecl(x) -> Hashtbl.add subscript x () (*** escapes sections, only use this when it should be permanent ***)
  | SuperscriptDecl(x) -> Hashtbl.add superscript x () (*** escapes sections, only use this when it should be permanent ***)
  | NotationDecl(x,yl) ->
      begin
	match x with
	| "IfThenElse" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (1,Ar(Prop,Ar(TpVar(0),Ar(TpVar(0),TpVar(0))))) ->
			  ifop := Some(h)
		      | _ -> raise (Failure("IfThenElse Notation should be given a polymorphic name of type prop->?0->?0->?0"))
		    with Not_found -> raise (Failure("IfThenElse Notation should be given a polymorphic name of type prop->?0->?0->?0"))
		  end
  	      | _ -> raise (Failure("IfThenElse Notation should be given a polymorphic name of type prop->?0->?0->?0"))
	    end
	| "Repl" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Ar(Ar(Set,Set),Set))) ->
			  replop := Some(h)
		      | _ -> raise (Failure("Repl Notation should be given a parameter or definition name of type set->(set->set)->set"))
		    with Not_found -> raise (Failure("Repl Notation should be given a parameter or definition name of type set->(set->set)->set"))
		  end
  	      | _ -> raise (Failure("Repl Notation should be given a parameter or definition name of type set->(set->set)->set"))
	    end
	| "Sep" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Ar(Ar(Set,Prop),Set))) ->
			  sepop := Some(h)
		      | _ -> raise (Failure("Repl Notation should be given a parameter or definition name of type set->(set->set)->set"))
		    with Not_found -> raise (Failure("Repl Notation should be given a parameter or definition name of type set->(set->set)->set"))
		  end
  	      | _ -> raise (Failure("Repl Notation should be given a parameter or definition name of type set->(set->set)->set"))
	    end
	| "ReplSep" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Ar(Ar(Set,Prop),Ar(Ar(Set,Set),Set)))) ->
			  replsepop := Some(h)
		      | _ -> raise (Failure("ReplSep Notation should be given a parameter or definition name of type set->(set->prop)->(set->set)->set"))
		    with Not_found -> raise (Failure("ReplSep Notation should be given a parameter or definition name of type set->(set->prop)->(set->set)->set"))
		  end
  	      | _ -> raise (Failure("ReplSep Notation should be given a parameter or definition name of type set->(set->prop)->(set->set)->set"))
	    end
	| "SetEnum" ->
	    begin
	      if List.length yl <= 1 then
		raise (Failure("SetEnum should be given at least n>=2 names: constructors for the first n-1 cases and finally constructor for adjoining to a set"))
	      else
		let rec f i yl ztp =
		  match yl with
		  | [y] ->
		      begin
			try
			  let h = Hashtbl.find sigtmh y in
			  match Hashtbl.find sigtmof h with
			  | (0,Ar(Set,Ar(Set,Set))) ->
			      setenumadj := Some(h)
			  | _ -> raise (Failure("The last name in the SetEnum Notation should be given a parameter or definition name of type set->set->set"))
			with Not_found -> raise (Failure("The last name in the SetEnum Notation should be given a parameter or definition name of type set->set->set"))
		      end
		  | (y::yr) ->
		      begin
			try
			  let h = Hashtbl.find sigtmh y in
			  match Hashtbl.find sigtmof h with
			  | (0,htp) ->
			      if htp = ztp then
				setenuml := Some(h)::!setenuml
			      else
				begin
				  Printf.printf "y = %s h = %s\nhtp = %s\nztp = %s\n" y h (tp_to_str htp) (tp_to_str ztp); flush stdout;
				  raise (Failure("Name " ^ string_of_int i ^ " in the SetEnum Notation should be given a parameter or definition name of type " ^ tp_to_str ztp))
				end
			  | _ -> raise (Failure("Name " ^ string_of_int i ^ " in the SetEnum Notation should be given a parameter or definition name of type " ^ tp_to_str ztp))
			with Not_found -> raise (Failure("Name " ^ string_of_int i ^ " in the SetEnum Notation should be given a parameter or definition name of type " ^ tp_to_str ztp))
		      end;
		      f (i+1) yr (Ar(Set,ztp))
		  | [] -> raise (Failure("SetEnum should be given at least n>=2 names: constructors for the first n-1 cases and finally constructor for adjoining to a set"))
		in
		setenuml := [];
		f 0 yl Set;
		setenuml := List.rev !setenuml
	    end
	| "SetEnum0" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Set) ->
			  set_setenuml_n 0 h
		      | _ -> raise (Failure("SetEnum0 Notation should be given a parameter or definition name of type set"))
		    with Not_found -> raise (Failure("SetEnum0 Notation should be given a parameter or definition name of type set"))
		  end
  	      | _ -> raise (Failure("SetEnum0 Notation should be given a parameter or definition name of type set"))
	    end
	| "SetEnum1" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Set)) ->
			  set_setenuml_n 1 h
		      | _ -> raise (Failure("SetEnum1 Notation should be given a parameter or definition name of type set->set"))
		    with Not_found -> raise (Failure("SetEnum1 Notation should be given a parameter or definition name of type set->set"))
		  end
  	      | _ -> raise (Failure("SetEnum1 Notation should be given a parameter or definition name of type set->set"))
	    end
	| "SetEnum2" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Ar(Set,Set))) ->
			  set_setenuml_n 2 h;
		      | _ -> raise (Failure("SetEnum2 Notation should be given a parameter or definition name of type set->set->set"))
		    with Not_found -> raise (Failure("SetEnum2 Notation should be given a parameter or definition name of type set->set->set"))
		  end
  	      | _ -> raise (Failure("SetEnum2 Notation should be given a parameter or definition name of type set->set->set"))
	    end
	| "Nat" ->
	    begin
	      match yl with
	      | [y0;yS] ->
		  begin
		    try
		      let h0 = Hashtbl.find sigtmh y0 in
		      let hS = Hashtbl.find sigtmh yS in
		      match (Hashtbl.find sigtmof h0,Hashtbl.find sigtmof hS) with
		      | ((0,Set),(0,Ar(Set,Set))) ->
			  nat0 := Some(h0);
			  natS := Some(hS)
		      | _ -> raise (Failure("Nat Notation should be given a name of type set (for 0) and a name of type set->set (for successor)"))
		    with Not_found -> raise (Failure("Nat Notation should be given a name of type set (for 0) and a name of type set->set (for successor)"))
		  end
	      | _ -> raise (Failure("Nat Notation should be given a name of type set (for 0) and a name of type set->set (for successor)"))
	    end
	| "SetLam" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Ar(Ar(Set,Set),Set))) ->
			  setlam := Some h
		      | _ -> raise (Failure("SetLam Notation should be given a name of type set->(set->set)->set"))
		    with Not_found -> raise (Failure("SetLam Notation should be given a name of type set->(set->set)->set"))
		  end
	      | _ -> raise (Failure("SetLam Notation should be given a name of type set->(set->set)->set"))
	    end
	| "SetImplicitOp" ->
	    begin
	      match yl with
	      | [y] ->
		  begin
		    try
		      let h = Hashtbl.find sigtmh y in
		      match Hashtbl.find sigtmof h with
		      | (0,Ar(Set,Ar(Set,Set))) ->
			  setimplop := Some h
		      | _ -> raise (Failure("SetAp Notation should be given a name of type set->set->set"))
		    with Not_found -> raise (Failure("SetAp Notation should be given a name of type set->set->set"))
		  end
	      | _ -> raise (Failure("SetAp Notation should be given a name of type set->set->set"))
	    end
	| _ -> raise (Failure("Unknown Notation " ^ x))
      end
  | ParamHash(x,h) ->
      if (!verbosity > 9) then (Printf.printf "ParamHash %s %s\n" x h; flush stdout);
      begin
	try
	  let (xj,(xi,_)) = primname x in
	  let xh = ptm_id (xi,Prim xj) sigtmof sigdelta in
	  if (h <> xh) then raise (Failure(x ^ " is the name of a built-in primitive and must have the id " ^ xh))
	with Not_found ->
	  if Hashtbl.mem sigtmh x then
	    raise (Failure(x ^ " is already assigned an id"))
	  else
	    if valid_id_p h then
	      Hashtbl.add sigtmh x h
	    else
	      raise (Failure(x ^ " is assigned an invalid id"))
      end
  | ParamDecl(x,a) ->
      if !reporteachitem then (Printf.printf "++ %s\n" x; flush stdout);
      let a = ltree_to_atree a in
      if List.mem_assoc x !sigtm || List.mem_assoc x !sigpf || List.mem x !ctxtp || List.mem_assoc x !ctxtm || List.mem_assoc x !ctxpf then
	raise (Failure(x ^ " has already been used."));
      if (!verbosity > 9) then (Printf.printf "Param %s : " x; output_ltree stdout (atree_to_ltree a); Printf.printf "\n"; flush stdout);
      let i = List.length !ctxtp in
      let atp = extract_tp a !ctxtp in
      if (!verbosity > 19) then Printf.printf "i = %d\natp = %s\n" i (tp_to_str atp);
      let agtp = !tparclos atp in
      begin
	try
	  let (xj,(xi,xtp)) = primname x in
	  if (xi,xtp) <> (i,agtp) then raise (Failure(x ^ " is the name of a built-in primitive which does not have the given type."));
	  let mp = match i with 0 -> Prim xj | 1 -> TpAp(Prim xj,TpVar 0) | 2 -> TpAp(TpAp(Prim xj,TpVar 0),TpVar 1) | 3 -> TpAp(TpAp(TpAp(Prim xj,TpVar 0),TpVar 1),TpVar 2) | _ -> raise (Failure("It is forbidden to have more than 3 type variables.")) in
	  let xhv = ptm_id (xi,mp) sigtmof sigdelta in
	  begin
	    if !sqlout then
	      begin
		match !mainfilehash with
		| Some docsha ->
		    if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`,`termprimitive`) VALUES ('%s','%s',%d,true);\n" xhv (stp_html_string agtp) i;
		    if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'p');\n" xhv docsha (String.escaped x));
		| None -> ()
	      end
	  end;
	  if !verbosity > 3 then (Printf.printf "%s has id %s\n" x xhv; flush stdout);
	  if (x = "Power") then setPow := Some xhv;
	  if (x = "In") then (*** As soon as In is declared, declare the id's corresponding to :e and c= ***)
	    begin
	      setIn := Some xhv;
	      let subhv = ptm_id (0,Lam(Set,Lam(Set,All(Set,Imp(Ap(Ap(TmH(xhv),DB(0)),DB(2)),Ap(Ap(TmH(xhv),DB(0)),DB(1))))))) sigtmof sigdelta in
	      setSubeq := Some subhv
	    end;
	  Hashtbl.add sigtmh x xhv;
	  Hashtbl.add sigtmof xhv (i,agtp);
	  if i > 0 then (*** x will look polymorphic with i types after the appropriate section is ended ***)
	    pushpolytm ((x,i),agtp);
	  if i = 0 && not (Hashtbl.mem indextms xhv) then Hashtbl.add indextms xhv xtp; (*** since this is a primitive, it doesn't really need to be indexed. However, indexing it will allow me to use parameters with different names for the primitives if I want. ***)
	  let m = TmH xhv in
	  sigtm := (x,!aptmloc m)::!sigtm;
	  secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,(x,atl m)::st,sp)) !secstack
	with Not_found ->
	  begin
	    if (i > 0) then raise (Failure(x ^ " must be defined. The only polymorphic parameter allowed are built-in primitives."));
	    if List.mem_assoc x !sigtm || List.mem_assoc x !sigpf || List.mem x !ctxtp || List.mem_assoc x !ctxtm || List.mem_assoc x !ctxpf then
	      raise (Failure(x ^ " has already been used."))
	    else
	      try
		let xhv = Hashtbl.find sigtmh x in
		begin
		  if !sqlout then
		    begin
		      match !mainfilehash with
		      | Some docsha ->
			  if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" xhv (stp_html_string agtp) i;
			  if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'p');\n" xhv docsha (String.escaped x));
		      | None -> ()
		    end
		end;
		begin
		  try
		    if (x = "Subq") then
		      begin
			match !setSubeq with
			| Some subhv ->
			    if xhv <> subhv then
			      raise (Failure("Subq can only be used to mean fun X Y:set => forall x:set, x :e X -> x :e Y"))
			| None ->
			    raise (Failure("Subq can only be used after In is declared and then only to mean fun X Y:set => forall x:set, x :e X -> x :e Y"))
		      end;
		    let itp = Hashtbl.find indextms xhv in
		    if agtp <> itp then raise (Failure("The id " ^ xhv ^ " associated with the parameter " ^ x ^ " has is indexed to have the type " ^ tp_to_str itp ^ " not " ^ tp_to_str agtp));
		    Hashtbl.add sigtmof xhv (i,agtp);
		    let m = TmH xhv in
		    sigtm := (x,!aptmloc m)::!sigtm;
		    secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,(x,atl m)::st,sp)) !secstack
		  with Not_found ->
		    raise (Failure("The given id " ^ xhv ^ " for " ^ x ^ " is not a known index for a term."))
		end
   	      with Not_found ->
		raise (Failure("Unknown id for " ^ x))
	  end
      end
  | DefDecl(x,None,b) ->
      if !reporteachitem then (Printf.printf "++ %s\n" x; flush stdout);
      let b = ltree_to_atree b in
      if List.mem_assoc x !sigtm || List.mem_assoc x !sigpf || List.mem x !ctxtp || List.mem_assoc x !ctxtm || List.mem_assoc x !ctxpf then
	raise (Failure(x ^ " has already been used."))
      else
	begin
	  if (!verbosity > 9) then (Printf.printf "Def %s := " x; output_ltree stdout (atree_to_ltree b); Printf.printf "\n"; flush stdout);
	  let i = List.length !ctxtp in
	  let (btm,btp) = extract_tm b !polytm sigtmof !sigtm !ctxtp !ctxtm in
	  if (!verbosity > 9) then (Printf.printf "Def %s := " x; output_ltree stdout (atree_to_ltree b); Printf.printf "\n"; flush stdout);
	  let bgtm = !tmlamclos btm in
	  let bgtp = !tparclos btp in
	  let xhv = ptm_id (i,bgtm) sigtmof sigdelta in
	  begin
	    if !sqlout then
	      begin
		match !mainfilehash with
		| Some docsha ->
		    if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" xhv (stp_html_string bgtp) i;
		    if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'d');\n" xhv docsha (String.escaped x));
		| None -> ()
	      end
	  end;
	  if (x = "Subq") then
	    begin
	      match !setSubeq with
	      | Some subhv ->
		  if xhv <> subhv then
		    raise (Failure("Subq can only be used to mean fun X Y:set => forall x:set, x :e X -> x :e Y"))
	      | None ->
		  raise (Failure("Subq can only be used after In is declared and then only to mean fun X Y:set => forall x:set, x :e X -> x :e Y"))
	    end;
	  if (!verbosity > 3) then (Printf.printf "%s := %s was assigned id %s\n" x (tm_to_str bgtm) xhv; flush stdout);
	  if !reporteachitem then (Printf.printf "%s was assigned id %s\n" x xhv; flush stdout);
	  if i > 0 then (*** x will look polymorphic with i types after the appropriate section is ended ***)
	    pushpolytm ((x,i),bgtp);
	  begin
	    try
	      let xhv2 = Hashtbl.find sigtmh x in
	      if xhv <> xhv2 then raise (Failure(x ^ " was explicitly assigned id " ^ xhv2 ^ " but this does not match its computed id " ^ xhv))
	    with Not_found -> ()
	  end;
	  Hashtbl.add sigtmh x xhv;
	  Hashtbl.add sigtmof xhv (i,bgtp);
	  if i = 0 then
	    begin
	      try
		let itp = Hashtbl.find indextms xhv in
		if bgtp <> itp then raise (Failure("The id " ^ xhv ^ " associated with the definition of " ^ x ^ " has is indexed to have the type " ^ tp_to_str itp ^ " not " ^ tp_to_str bgtp ^ ". This indicates some fundamental bug since it would presumably imply a hash collision."));
	      with Not_found ->
		Hashtbl.add indextms xhv bgtp
	    end;
	  let m = TmH xhv in
	  sigtm := (x,!aptmloc m)::!sigtm;
	  secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,(x,atl m)::st,sp)) !secstack;
	  if (!verbosity > 19) then (Printf.printf "i = %d\nbtm = %s\nbtp = %s\n" i (tm_to_str btm) (tp_to_str btp); flush stdout);
	end
  | DefDecl(x,Some a,b) ->
      if !reporteachitem then (Printf.printf "++ %s\n" x; flush stdout);
      let a = ltree_to_atree a in
      let b = ltree_to_atree b in
      if List.mem_assoc x !sigtm || List.mem_assoc x !sigpf || List.mem x !ctxtp || List.mem_assoc x !ctxtm || List.mem_assoc x !ctxpf then
	raise (Failure(x ^ " has already been used."))
      else
	begin
	  if (!verbosity > 9) then (Printf.printf "Def %s : " x; output_ltree stdout (atree_to_ltree a); Printf.printf "\n := "; output_ltree stdout (atree_to_ltree b); Printf.printf "\n"; flush stdout);
	  let i = List.length !ctxtp in
	  let atp = extract_tp a !ctxtp in
	  let btm = check_tm b atp !polytm sigtmof !sigtm !ctxtp !ctxtm in
	  if (!verbosity > 9) then (Printf.printf "Def %s := " x; output_ltree stdout (atree_to_ltree b); Printf.printf "\n"; flush stdout);
	  let bgtm = !tmlamclos btm in
	  let agtp = !tparclos atp in
	  let xhv = ptm_id (i,bgtm) sigtmof sigdelta in
	  begin
	    if !sqlout then
	      begin
		match !mainfilehash with
		| Some docsha ->
		    if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" xhv (stp_html_string agtp) i;
		    if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'d');\n" xhv docsha (String.escaped x));
		| None -> ()
	      end
	  end;
	  if (x = "Subq") then
	    begin
	      match !setSubeq with
	      | Some subhv ->
		  if xhv <> subhv then
		    raise (Failure("Subq can only be used to mean fun X Y:set => forall x:set, x :e X -> x :e Y"))
	      | None ->
		  raise (Failure("Subq can only be used after In is declared and then only to mean fun X Y:set => forall x:set, x :e X -> x :e Y"))
	    end;
	  if (!verbosity > 3) then (Printf.printf "%s := %s was assigned id %s\n" x (tm_to_str bgtm) xhv; flush stdout);
	  if !reporteachitem then (Printf.printf "%s was assigned id %s\n" x xhv; flush stdout);
	  if i > 0 then (*** x will look polymorphic with i types after the appropriate section is ended ***)
	    pushpolytm ((x,i),agtp);
	  begin
	    try
	      let xhv2 = Hashtbl.find sigtmh x in
	      if xhv <> xhv2 then raise (Failure(x ^ " was explicitly assigned id " ^ xhv2 ^ " but this does not match its computed id " ^ xhv))
	    with Not_found -> ()
	  end;
	  Hashtbl.add sigtmh x xhv;
	  Hashtbl.add sigtmof xhv (i,agtp);
	  if i = 0 then
	    begin
	      try
		let itp = Hashtbl.find indextms xhv in
		if agtp <> itp then raise (Failure("The id " ^ xhv ^ " associated with the definition of " ^ x ^ " has is indexed to have the type " ^ tp_to_str itp ^ " not " ^ tp_to_str agtp ^ ". This indicates some fundamental bug since it would presumably imply a hash collision."));
	      with Not_found ->
		Hashtbl.add indextms xhv agtp
	    end;
	  let m = TmH xhv in
	  sigtm := (x,!aptmloc m)::!sigtm;
	  secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,(x,atl m)::st,sp)) !secstack;
	  if (!verbosity > 19) then (Printf.printf "i = %d\nbtm = %s\nbtp = %s\n" i (tm_to_str btm) (tp_to_str atp); flush stdout);
	end
  | AxDecl(x,a) ->
      if !reporteachitem then (Printf.printf "++ %s\n" x; flush stdout);
      let a = ltree_to_atree a in
      if List.mem_assoc x !sigtm || List.mem_assoc x !sigpf || List.mem x !ctxtp || List.mem_assoc x !ctxtm || List.mem_assoc x !ctxpf then
	raise (Failure(x ^ " has already been used."));
      let i = List.length !ctxtp in
      let atm = check_tm a Prop !polytm sigtmof !sigtm !ctxtp !ctxtm in
      let agtm = !tmallclos atm in
      let ahv = ptm_id (i,agtm) sigtmof sigdelta in
      Hashtbl.add sigknh x ahv;
      activate_special_knowns ahv;
      begin
	if !sqlout then
	  begin
	    match !mainfilehash with
	    | Some docsha ->
		if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" ahv (stp_html_string Prop) i;
		if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'a');\n" ahv docsha (String.escaped x));
	    | None -> ()
	  end
      end;
      sigpf := (x,!appfloc (Known(ahv)))::!sigpf;
      if i > 0 then (*** x will look polymorphic with i types after the appropriate section is ended ***)
	pushpolypf ((x,i),agtm);
      if not (Hashtbl.mem indexknowns ahv) then raise (Failure("The id " ^ ahv ^ " for the proposition for axiom " ^ x ^ " is not indexed as previously known"));
      secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,st,(x,apl (Known(ahv)))::sp)) !secstack;
      if (!verbosity > 3) then (Printf.printf "Proposition of Axiom %s : %s was assigned id %s\n" x (tm_to_str agtm) ahv; flush stdout);
      if !reporteachitem then (Printf.printf "%s was assigned id %s\n" x ahv; flush stdout);
      ()
  | ThmDecl(c,x,a) ->
      let a = ltree_to_atree a in
      if List.mem_assoc x !sigtm || List.mem_assoc x !sigpf || List.mem x !ctxtp || List.mem_assoc x !ctxtm || List.mem_assoc x !ctxpf then
	raise (Failure(x ^ " has already been used."));
      if !includingsigfile then raise (Failure("Included signature file includes a theorem (" ^ x ^ "), but should only include axioms."));
      let i = List.length !ctxtp in
      let atm = check_tm a Prop !polytm sigtmof !sigtm !ctxtp !ctxtm in
      let agtm = !tmallclos atm in
      let ahv = ptm_id (i,agtm) sigtmof sigdelta in
      Hashtbl.add sigknh x ahv;
      if !reporteachitem then (Printf.printf "++ %s\nHASH %s\n" x ahv; flush stdout);
      if !sqlout then
	begin
	  match !treasure with
	  | Some(traddr) ->
	      begin
		match !mainfilehash with
		| Some docsha ->
		    if not !presentationonly then (Printf.printf "INSERT INTO `treasuretermdoc` (`treasureaddress`,`propid`,`docsha`,`thmdocname`) VALUES ('%s','%s','%s','%s');\n" traddr ahv docsha x);
		| None -> ()
	      end
	  | None -> ()
	end;
      if !verbosity > 5 && Hashtbl.mem indexknowns ahv then (Printf.printf "Warning: The id %s for the proposition for theorem %s is already known.\n" ahv x; flush stdout);
      if (!verbosity > 3) then (Printf.printf "Proposition of %s %s : %s was assigned id %s\n" c x (tm_to_str agtm) ahv; flush stdout);
      if !reporteachitem then (Printf.printf "%s was assigned id %s\n" x ahv; flush stdout);
      let currpflamclos = !pflamclos in
      deltaset := [];
      proving := Some (x,i,agtm,ahv);
      prooffun := (fun dl -> match dl with [d] -> currpflamclos d | _ -> raise (Failure("Bug with proof construction")));
      pfstate := [PfStateGoal(atm,!ctxtm,!ctxpf)];
      laststructaction := -1

let evaluate_docitem ditem =
  evaluate_docitem_1 ditem;
  match !html with
  | Some hc ->
      begin
	if !thmsasexercises then
	  begin
	    match ditem with
	    | ThmDecl(_,x,_) ->
		begin
		  try
		    let h = Hashtbl.find sigknh x in
		    Printf.fprintf hc "\n$x%s\n" h
		  with Not_found -> ()
		end
	    | _ -> ()
	  end;
	output_docitem_html hc ditem sigtmh sigknh;
	match ditem with
	| ThmDecl(_,x,_) ->
	    begin
	      match !inchan with
	      | Some(c) ->
		  begin
		    try
		      let h = Hashtbl.find sigknh x in
		      currtmid := h
		    with Not_found -> ()
		  end;
		  pflinestart := !lineno;
		  pfcharstart := !charno;
		  skip_to_line_char c inchanline inchanchar !lineno !charno;
	      | None -> ()
	    end
	| _ -> ()
      end
  | None -> ()

let rec structure_pfstate i goal1 pfstl =
  match pfstl with
  | (PfStateGoal(claim2,cxtm2,cxpf2)::pfstr) ->
      (PfStateSep(i,true)::goal1::structure_pfstate i (PfStateGoal(claim2,cxtm2,cxpf2)) pfstr)
  | pfstr ->
      (PfStateSep(i,true)::goal1::PfStateSep(i,false)::pfstr)

let print_pfstate () =
  List.iter
    (fun p ->
      match p with
      | PfStateSep(j,true) -> Printf.printf "PfStateSep(%d,true)\n" j
      | PfStateSep(j,false) -> Printf.printf "PfStateSep(%d,false)\n" j
      | PfStateGoal(claim1,_,_) -> Printf.printf "PfStateGoal(%s,_,_)\n" (tm_to_str claim1)
      )
    !pfstate

let evaluate_pftac_1 pitem thmname i gpgtm gphv =
  match pitem with
  | PfStruct i when i < 4 ->
      if !verbosity > 19 then (Printf.printf "pfstruct %d\nLength of pfstate stack: %d\n" i (List.length !pfstate); print_pfstate (); flush stdout);
      begin
	match !pfstate with
	| PfStateSep(j,true)::pfstr ->
	    if i = j then
	      begin
		laststructaction := 2;
		pfstate := pfstr;
		if !verbosity > 19 then (Printf.printf "pfstruct %d pop\nLength of pfstate stack: %d\n" i (List.length !pfstate); flush stdout);
	      end
	    else
	      raise (Failure("Previous subproof not completed"))
	| PfStateSep(j,false)::pfstr ->
	    raise (Failure("Proof structuring bug"))
	| [] ->
	    raise (Failure("No claim to prove here"))
	| PfStateGoal(claim1,cxtm1,cxpf1)::PfStateGoal(claim2,cxtm2,cxpf2)::pfstr ->
	    laststructaction := 1;
	    pfstate := PfStateGoal(claim1,cxtm1,cxpf1)::structure_pfstate i (PfStateGoal(claim2,cxtm2,cxpf2)) pfstr;
	    if !verbosity > 19 then (Printf.printf "pfstruct %d push\nLength of pfstate stack: %d\n" i (List.length !pfstate); flush stdout);
	| PfStateGoal(claim1,cxtm1,cxpf1)::pfstr ->
	    raise (Failure("Inappropriate place for this proof structuring symbol since there is only one goal"))
      end
  | PfStruct 4 ->
      begin
	match !pfstate with
	| PfStateSep _::pfstr ->
	    raise (Failure("A subproof cannot be started here"))
	| [] ->
	    raise (Failure("No claim to prove here"))
	| PfStateGoal(claim1,cxtm1,cxpf1)::pfstr ->
	    pfstate := PfStateGoal(claim1,cxtm1,cxpf1)::PfStateSep(5,true)::pfstr
      end
  | PfStruct 5 ->
      begin
	match !pfstate with
	| PfStateSep(j,_)::pfstr ->
	    if j = 5 then
	      pfstate := pfstr
	    else
	      raise (Failure("Previous subproof not completed"))
	| [] ->
	    raise (Failure("Not proving a goal"))
	| _ -> raise (Failure("Subproof not completed"))
      end
  | Exact(d) ->
      laststructaction := 0;
      let d = ltree_to_atree d in
      begin
	match !pfstate with
	| PfStateGoal(claimtm,cxtm,cxpf)::pfstr ->
	    let dpf = check_pf d claimtm !polytm !polypf sigtmof sigdelta !sigtm !sigpf !ctxtp cxtm cxpf in
	    let currprooffun = !prooffun in
	    prooffun := (fun dl -> currprooffun (dpf::dl));
	    pfstate := pfstr
	| _ ->
	    raise (Failure("No current claim"))
      end
  | LetTac(xl,None) ->
      laststructaction := 0;
      begin
	match !pfstate with
	| PfStateGoal(claimtm,cxtm,cxpf)::pfstr ->
	    let rec let_tac_None_r xs claimtm cxtm cxpf =
	      match xs with
	      | [] ->
		  pfstate := PfStateGoal(claimtm,cxtm,cxpf)::pfstr
	      | (x::xr) ->
		  match claimtm with
		  | All(a,body) -> (*** If it's already an All, then don't call headnorm since headnorm will at least beta eta normalize and change the structure. ***)
		      let currprooffun = !prooffun in
		      prooffun := (fun dl -> match dl with d::dr -> currprooffun (TLam(a,d)::dr) | _ -> raise (Failure("proof reconstruction problem")));
		      let_tac_None_r xr body ((x,(a,None))::cxtm) (List.map (fun (y,q) -> (y,tmshift 0 1 q)) cxpf)
		  | _ -> (*** If it's not an All, then call headnorm and try to expose an All. ***)
		      let (p,dl) = headnorm claimtm sigdelta !deltaset in
		      match p with
		      | All(a,body) ->
			  let currprooffun = !prooffun in
			  prooffun := (fun dl -> match dl with d::dr -> currprooffun (TLam(a,d)::dr) | _ -> raise (Failure("proof reconstruction problem")));
			  let_tac_None_r xr body ((x,(a,None))::cxtm) (List.map (fun (y,q) -> (y,tmshift 0 1 q)) cxpf)
		      | _ ->
			  raise (Failure("let tactic used with " ^ x ^ " when claim is not a universal quantifier"))
	    in
	    let_tac_None_r xl claimtm cxtm cxpf
	| _ ->
	    raise (Failure("No current claim"))
      end
  | LetTac(xl,Some b) ->
      laststructaction := 0;
      let b = ltree_to_atree b in
      let btp = extract_tp b !ctxtp in
      begin
	match !pfstate with
	| PfStateGoal(claimtm,cxtm,cxpf)::pfstr ->
	    let rec let_tac_Some_r xs claimtm cxtm cxpf =
	      match xs with
	      | [] ->
		  pfstate := PfStateGoal(claimtm,cxtm,cxpf)::pfstr
	      | (x::xr) ->
		  match claimtm with
		  | All(a,body) -> (*** If it's already an All, then don't call headnorm since headnorm will at least beta eta normalize and change the structure. ***)
		      if a = btp then
			let currprooffun = !prooffun in
			prooffun := (fun dl -> match dl with d::dr -> currprooffun (TLam(a,d)::dr) | _ -> raise (Failure("proof reconstruction problem")));
			let_tac_Some_r xr body ((x,(a,None))::cxtm) (List.map (fun (y,q) -> (y,tmshift 0 1 q)) cxpf)
		      else
			raise (Failure(x ^ " ascribe type " ^ (tp_to_str btp) ^ " but the claim is universally quantified over type " ^ (tp_to_str a)))
		  | _ -> (*** If it's not an All, then call headnorm and try to expose an All. ***)
		      let (p,dl) = headnorm claimtm sigdelta !deltaset in
		      match p with
		      | All(a,body) ->
			  if a = btp then
			    let currprooffun = !prooffun in
			    prooffun := (fun dl -> match dl with d::dr -> currprooffun (TLam(a,d)::dr) | _ -> raise (Failure("proof reconstruction problem")));
			    let_tac_Some_r xr body ((x,(a,None))::cxtm) (List.map (fun (y,q) -> (y,tmshift 0 1 q)) cxpf)
			  else
			    raise (Failure(x ^ " ascribe type " ^ (tp_to_str btp) ^ " but the claim is universally quantified over type " ^ (tp_to_str a)))
		      | _ ->
			  raise (Failure("let tactic used with " ^ x ^ " when claim is not a universal quantifier"))
	    in
	    let_tac_Some_r xl claimtm cxtm cxpf
	| _ ->
	    raise (Failure("No current claim"))
      end
  | AssumeTac(xl,None) ->
      laststructaction := 0;
      begin
	match !pfstate with
	| PfStateGoal(claimtm,cxtm,cxpf)::pfstr ->
	    let rec assume_tac_None_r xs claimtm cxtm cxpf =
	      match xs with
	      | [] ->
		  pfstate := PfStateGoal(claimtm,cxtm,cxpf)::pfstr
	      | (x::xr) ->
		  match claimtm with
		  | Imp(p1,p2) -> (*** If it's already an Imp, then don't call headnorm since headnorm will at least beta eta normalize and change the structure. ***)
		      let currprooffun = !prooffun in
		      prooffun := (fun dl -> match dl with d::dr -> currprooffun (PLam(p1,d)::dr) | _ -> raise (Failure("proof reconstruction problem")));
		      assume_tac_None_r xr p2 cxtm ((x,p1)::cxpf)
		  | _ -> (*** If it's not an All, then call headnorm and try to expose an All. ***)
		      let (p,dl) = headnorm claimtm sigdelta !deltaset in
		      match p with
		      | Imp(p1,p2) ->
			  let currprooffun = !prooffun in
			  prooffun := (fun dl -> match dl with d::dr -> currprooffun (PLam(p1,d)::dr) | _ -> raise (Failure("proof reconstruction problem")));
			  assume_tac_None_r xr p2 cxtm ((x,p1)::cxpf)
		      | _ ->
			  raise (Failure("assume tactic used with " ^ x ^ " when claim is not an implication"))
	    in
	    assume_tac_None_r xl claimtm cxtm cxpf
	| _ ->
	    raise (Failure("No current claim"))
      end
  | AssumeTac(xl,Some b) ->
      laststructaction := 0;
      let b = ltree_to_atree b in
      begin
	match !pfstate with
	| PfStateGoal(claimtm,cxtm,cxpf)::pfstr ->
	    let btm = check_tm b Prop !polytm sigtmof !sigtm !ctxtp cxtm in
	    let rec assume_tac_Some_r xs claimtm cxtm cxpf =
	      match xs with
	      | [] ->
		  pfstate := PfStateGoal(claimtm,cxtm,cxpf)::pfstr
	      | (x::xr) ->
		  match claimtm with
		  | Imp(p1,p2) -> (*** If it's already an Imp, then don't call headnorm since headnorm will at least beta eta normalize and change the structure. ***)
		      begin
			match conv p1 btm sigdelta !deltaset with
			| Some(dl) ->
			    deltaset := dl;
			    let currprooffun = !prooffun in
			    prooffun := (fun dl -> match dl with d::dr -> currprooffun (PLam(btm,d)::dr) | _ -> raise (Failure("proof reconstruction problem")));
			    assume_tac_Some_r xr p2 cxtm ((x,btm)::cxpf)
			| None ->
			    raise (Failure(x ^ " ascribed prop " ^ (tm_to_str btm) ^ " but the antecendent of the claim is " ^ (tm_to_str p1)))
		      end
		  | _ -> (*** If it's not an Imp, then call headnorm and try to expose an Imp. ***)
		      let (p,dl) = headnorm claimtm sigdelta !deltaset in
		      match p with
		      | Imp(p1,p2) ->
			  begin
			    match conv p1 btm sigdelta !deltaset with
			    | Some(dl) ->
				deltaset := dl;
				let currprooffun = !prooffun in
				prooffun := (fun dl -> match dl with d::dr -> currprooffun (PLam(btm,d)::dr) | _ -> raise (Failure("proof reconstruction problem")));
				assume_tac_Some_r xr p2 cxtm ((x,btm)::cxpf)
			    | None ->
				raise (Failure(x ^ " ascribed prop " ^ (tm_to_str btm) ^ " but the antecendent of the claim is " ^ (tm_to_str p1)))
			  end
		      | _ ->
			  raise (Failure("assume tactic used with " ^ x ^ " when claim is not an implication"))
	    in
	    assume_tac_Some_r xl claimtm cxtm cxpf
	| _ ->
	    raise (Failure("No current claim"))
      end
  | SetTac(x,None,b) ->
      laststructaction := 0;
      let b = ltree_to_atree b in
      begin
	match !pfstate with
	| PfStateGoal(claimtm,cxtm,cxpf)::pfstr ->
	    let (btm,btp) = extract_tm b !polytm sigtmof !sigtm !ctxtp cxtm in
	    pfstate := (PfStateGoal(claimtm,(x,(btp,Some(btm)))::cxtm,cxpf))::pfstr
	| _ ->
	    raise (Failure("set tactic cannot be used when there is no claim"))
      end
  | SetTac(x,Some(a),b) ->
      let a = ltree_to_atree a in
      let b = ltree_to_atree b in
      begin
	match !pfstate with
	| PfStateGoal(claimtm,cxtm,cxpf)::pfstr ->
	    let atp = extract_tp a !ctxtp in
	    let btm = check_tm b atp !polytm sigtmof !sigtm !ctxtp cxtm in
	    pfstate := (PfStateGoal(claimtm,(x,(atp,Some(btm)))::cxtm,cxpf))::pfstr
	| _ ->
	    raise (Failure("set tactic cannot be used when there is no claim"))
      end
  | ApplyTac(a) ->
      laststructaction := 0;
      let a = ltree_to_atree a in
      if !verbosity > 19 then (Printf.printf "apply tactic begin\nLength of pfstate stack: %d\n" (List.length !pfstate); flush stdout);
      begin
	match !pfstate with
	| PfStateGoal(claimtm,cxtm,cxpf)::pfstr ->
	    let (apf,atm) = extract_pf a !polytm !polypf sigtmof sigdelta !sigtm !sigpf !ctxtp cxtm cxpf in
	    let sigma =
	      begin
		let i = ref 0 in
		List.iter (fun (_,(_,d)) -> match d with None -> incr i | _ -> ()) cxtm;
		map_for (fun j -> MDB j) 0 (!i-1)
	      end
	    in
	    let rec foapplyf p n margs subclaims apff =
	      try
		if !verbosity > 19 then (Printf.printf "about to call pattern_match with %s\n" (mtm_to_str p); flush stdout);
		let theta = pattern_match sigdelta p claimtm (fun _ -> raise Not_found) in
		if !verbosity > 19 then (Printf.printf "after pattern_match\n"; flush stdout);
		let ml = List.map (fun m -> mtm_to_tm (mtm_msub theta m)) margs in
		(*** The next code reverses the subclaims (so earliest arguments are to be proven first) and also grounds them from mtm to tm simultaneously ***)
		let subclaimtms = ref [] in
		List.iter
		  (fun c ->
		    let c1 = mtm_msub theta c in
		    let c2 = mtm_to_tm c1 in
		    subclaimtms := c2::!subclaimtms)
		  subclaims;
		(!subclaimtms,apff ml)
	      with MatchFail ->
		match p with
		| MImp(p1,p2) ->
		    foapplyf p2 n margs (p1::subclaims) (fun ml dl -> match dl with d::dr -> PPfAp(apff ml dr,d) | _ -> raise (Failure("proof reconstruction problem")))
		| MAll(a1,p2) ->
		    begin
		      match mtm_minap_db p2 0 with
		      | None -> (*** special case: no occurrence, use Eps _:a1, False ***)
			  let defelt = Ap(TpAp(Prim(0),a1),Lam(a1,All(Prop,DB(0)))) in
			  foapplyf p2 n margs subclaims (fun ml dl -> match dl with d::dr -> PTmAp(apff ml dr,defelt) | _ -> raise (Failure("proof reconstruction problem")))
		      | Some(l) when l = 0 -> (*** simple case, like a FO var ***)
			  foapplyf (mtm_ssub (MVar(n,sigma)::sigma) p2) (n+1) (MVar(n,sigma)::margs) subclaims (fun ml dl -> match ml with m::mr -> PTmAp(apff mr dl,m) | _ -> raise (Failure("proof reconstruction problem")))
		      | Some(l) -> (*** otherwise, move l arguments into the context of the metavar so that the higher-order pattern case is handled ***)
			  let sigmal = (map_for (fun j -> MDB j) 0 (l-1)) @ (List.map (mtm_shift 0 l) sigma) in
			  let rec lmvnr l a m =
			    if l > 0 then
			      begin
				match a with
				| Ar(a1,a2) -> MLam(a1,lmvnr (l-1) a2 m)
				| _ -> raise (Failure("Type Error found while attempting apply tactic"))
			      end
			    else
			      m
			  in
			  let lmvn = lmvnr l a1 (MVar(n,sigmal)) in
			  let p3 = mtm_ssub (lmvn::sigma) p2 in
			  let p4 = mtm_betared_if p3 (fun q _ -> mtm_lammvar_p q) in
			  foapplyf p4 (n+1) (lmvn::margs) subclaims (fun ml dl -> match ml with m::mr -> PTmAp(apff mr dl,m) | _ -> raise (Failure("proof reconstruction problem")))
		    end
		| _ ->
		    begin
		      let p1 = mtm_betared_if p (fun _ _ -> true) in (*** try to beta reduce ***)
		      if p = p1 then (*** there were no beta reductions ***)
			let (p2,del) = mheadnorm p sigdelta !deltaset in (*** try to delta expand some heads ***)
			if p = p2 then (*** no delta expansions ***)
			  raise Not_found (*** give up and fail ***)
			else
			  begin
			    deltaset := del;
			    foapplyf p2 n margs subclaims apff
			  end
		      else
			foapplyf p1 n margs subclaims apff
		    end
	    in
	    begin
	      try
		if !verbosity > 19 then (Printf.printf "Proof term given with apply proves %s\n" (tm_to_str atm); flush stdout);
		let (subclaims,apff) = foapplyf (tm_to_mtm atm) 0 [] [] (fun ml dl -> apf) in
		let nsubs = List.length subclaims in
		let currprooffun = !prooffun in
		prooffun := (fun dl -> let (dl1,dl2) = split_list nsubs dl in currprooffun (apff (List.rev dl1)::dl2));
		pfstate := (List.map (fun c -> PfStateGoal(c,cxtm,cxpf)) subclaims) @ pfstr;
		if !verbosity > 19 then (Printf.printf "here nach apply\nLength of pfstate stack: %d\n" (List.length !pfstate); flush stdout);
	      with Not_found ->
		raise (Failure("apply does not match the current claim"))
	    end
	| _ ->
	    raise (Failure("apply tactic cannot be used when there is no claim"))
      end
  | ClaimTac(x,a) ->
      laststructaction := 0;
      let a = ltree_to_atree a in
      begin
	match !pfstate with
	| PfStateGoal(claimtm,cxtm,cxpf)::pfstr ->
	    let atm = check_tm a Prop !polytm sigtmof !sigtm !ctxtp cxtm in
	    pfstate := (PfStateGoal(atm,cxtm,cxpf))::(PfStateGoal(claimtm,cxtm,(x,atm)::cxpf))::pfstr;
	    let currprooffun = !prooffun in
	    prooffun := (fun dl -> match dl with d1::d2::dr -> currprooffun (PPfAp(PLam(atm,d2),d1)::dr) | _ -> raise (Failure("proof reconstruction problem")))
	| _ ->
	    raise (Failure("claim tactic cannot be used when there is no claim"))
      end
  | ProveTac(a,[]) ->
      laststructaction := 0;
      let a = ltree_to_atree a in
      begin
	match !pfstate with
	| PfStateGoal(claimtm,cxtm,cxpf)::pfstr ->
	    let atm = check_tm a Prop !polytm sigtmof !sigtm !ctxtp cxtm in
	    begin
	      match conv claimtm atm sigdelta !deltaset with
	      | Some(dl) ->
		  deltaset := dl;
		  pfstate := (PfStateGoal(atm,cxtm,cxpf))::pfstr
	      | None ->
		  match conv (All(Prop,DB(0))) atm sigdelta !deltaset with (*** or if prove False, then use FalseE ***)
		  | Some(del) ->
		      deltaset := del;
		      let currprooffun = !prooffun in
		      prooffun := (fun dl -> match dl with d1::dr -> currprooffun (PTmAp(d1,claimtm)::dr) | _ -> raise (Failure("proof reconstruction problem")));
		      pfstate := (PfStateGoal(atm,cxtm,cxpf))::pfstr
		  | None ->
		      raise (Failure("Proposition given with prove tactic does not match the current claim.\n" ^ tm_to_str claimtm ^ "\n" ^ tm_to_str atm))
	    end
	| _ ->
	    raise (Failure("prove tactic cannot be used when there is no claim"))
      end
  | ProveTac(a,bl) ->
      laststructaction := 0;
      raise (Failure("prove tactic can currently only be used with one proposition"))
  | CasesTac(a,xbll) ->
      laststructaction := 0;
      raise (Failure("cases tactic is not yet implemented"))
  | WitnessTac(a) ->
      laststructaction := 0;
      let a = ltree_to_atree a in
      if not !expolyIknown then
	raise (Failure("witness tactic cannot be used until the introduction lemma for existentials is known"))
      else
	begin
	  match !pfstate with
	  | PfStateGoal(claimtm,cxtm,cxpf)::pfstr ->
	      begin
		try
		  let (etp,ep) = extract_exclaim claimtm in
		  let atm = check_tm a etp !polytm sigtmof !sigtm !ctxtp cxtm in
		  let epatm =
		    begin
		      match ep with
		      | Lam(_,epbody) -> tmsubst epbody 0 atm
		      | _ -> Ap(ep,atm)
		    end
		  in
		  if !verbosity > 50 then (Printf.printf "witness tactic with etp = %s\n and ep = %s\n and atm = %s\n and epatm = %s\n" (tp_to_str etp) (tm_to_str ep) (tm_to_str atm) (tm_to_str epatm); flush stdout);
		  pfstate := (PfStateGoal(epatm,cxtm,cxpf)::pfstr);
		  let currprooffun = !prooffun in
		  prooffun := (fun dl -> match dl with d1::dr -> currprooffun (PPfAp(PTmAp(PTmAp(PTpAp(Known(!expolyI),etp),ep),atm),d1)::dr) | _ -> raise (Failure("proof reconstruction problem")))
		with Not_found ->
		  raise (Failure("witness tactic can only be used when claim is existential"))
	      end
	  | _ ->
	      raise (Failure("witness tactic cannot be used when there is no claim"))
	end
  | RewriteTac(sym,a,posl) -> (*** rewrite from right to left, which is actually the direction that does not use symmetry given the definition of Leibniz equality. ***)
      laststructaction := 0;
      let a = ltree_to_atree a in
      if !verbosity > 19 then (Printf.printf "rewrite tactic begin\nLength of pfstate stack: %d\n" (List.length !pfstate); flush stdout);
      if (not sym) && (not !eqsymPolyknown) then raise (Failure("rewrite tactic cannot be used without <- until symmetry of equality is known."));
      begin
	match !pfstate with
	| PfStateGoal(claimtm,cxtm,cxpf)::pfstr ->
	    let (apf,atm) = extract_pf a !polytm !polypf sigtmof sigdelta !sigtm !sigpf !ctxtp cxtm cxpf in
	    let sigma =
	      begin
		let i = ref 0 in
		List.iter (fun (_,(_,d)) -> match d with None -> incr i | _ -> ()) cxtm;
		map_for (fun j -> MDB j) 0 (!i-1)
	      end
	    in
	    let inpos i = match posl with [] -> true | _ -> List.mem i posl in
	    let posr = ref 0 in
	    let rec forewritef4 z etmi mtm =
	      if !verbosity > 79 then (Printf.printf "forewritef4: %d\n etmi: %s\n mtm: %s\n" z (tm_to_str etmi) (tm_to_str mtm); flush stdout);
	      if mtm = etmi then
		begin
		  incr posr;
		  if inpos !posr then
		    DB(z)
		  else
		    forewritef5 z etmi mtm
		end
	      else
		forewritef5 z etmi mtm
	    and forewritef5 z etmi mtm =
	      if !verbosity > 79 then (Printf.printf "forewritef5: %d\n etmi: %s\n mtm: %s\n" z (tm_to_str etmi) (tm_to_str mtm); flush stdout);
	      match mtm with
	      | Ap(m1,m2) ->
		  let m1b = forewritef4 z etmi m1 in
		  let m2b = forewritef4 z etmi m2 in
		  Ap(m1b,m2b)
	      | Imp(m1,m2) ->
		  let m1b = forewritef4 z etmi m1 in
		  let m2b = forewritef4 z etmi m2 in
		  Imp(m1b,m2b)
	      | Lam(a1,m1) -> Lam(a1,forewritef4 (z+1) (tmshift 0 1 etmi) m1)
	      | All(a1,m1) -> All(a1,forewritef4 (z+1) (tmshift 0 1 etmi) m1)
	      | DB(j) when j >= z -> DB(j+1)
	      | _ -> mtm
	    in
	    let rec forewritef2 z n etp etm mtm =
	      if !verbosity > 79 then (Printf.printf "forewritef2: %d %d\n etm: %s\n mtm: %s\n" z n (mtm_to_str etm) (tm_to_str mtm); flush stdout);
	      begin
		try
		  begin
		    if !verbosity > 19 then (Printf.printf "rewrite: about to call pattern_match with\n    %s\n =? %s\n" (mtm_to_str etm) (tm_to_str mtm); flush stdout);
		    let theta = pattern_match sigdelta etm mtm (fun _ -> raise Not_found) in
		    if !verbosity > 19 then (Printf.printf "after pattern_match %d\n" !posr; flush stdout);
		    try
		      begin
			for i = 0 to n-1 do
			  let _ = theta i in ()
			done;
			incr posr;
			if inpos !posr then
			  begin
			    (*** the instantiation to use ***)
			    (DB(z),theta)
			  end
			else
			  forewritef3 z n etp etm mtm
		      end
		    with Not_found ->
		      forewritef3 z n etp etm mtm
		  end
		with MatchFail ->
		  forewritef3 z n etp etm mtm
	      end
	    and forewritef3 z n etp etm mtm =
	      if !verbosity > 79 then (Printf.printf "forewritef3: %d %d\n etm: %s\n mtm: %s\n" z n (mtm_to_str etm) (tm_to_str mtm); flush stdout);
	      match mtm with
	      | Ap(m1,m2) ->
		  begin
		    try
		      let (leibp1,theta) = forewritef2 z n etp etm m1 in
		      let leibp2 = forewritef4 z (mtm_to_tm (mtm_msub theta etm)) m2 in
		      (Ap(leibp1,leibp2),theta)
		    with Not_found ->
		      let (leibp2,theta) = forewritef2 z n etp etm m2 in
		      (Ap(tmshift z 1 m1,leibp2),theta)
		  end
	      | Imp(m1,m2) ->
		  begin
		    try
		      let (leibp1,theta) = forewritef2 z n etp etm m1 in
		      let leibp2 = forewritef4 z (mtm_to_tm (mtm_msub theta etm)) m2 in
		      (Imp(leibp1,leibp2),theta)
		    with Not_found ->
		      let (leibp2,theta) = forewritef2 z n etp etm m2 in
		      (Imp(tmshift z 1 m1,leibp2),theta)
		  end
	      | Lam(a1,m1) ->
		  let (leibp1,theta) = forewritef2 (z+1) n etp (mtm_shift 0 1 etm) m1 in
		  (Lam(a1,leibp1),theta)
	      | All(a1,m1) ->
		  let (leibp1,theta) = forewritef2 (z+1) n etp (mtm_shift 0 1 etm) m1 in
		  (All(a1,leibp1),theta)
	      | _ -> raise Not_found
	    in
	    let destruct_leibeq p =
	      match p with
	      | MAp(MAp(MTpAp(MTmH(e),etp),ltm),rtm) when e = !eqPoly -> (etp,ltm,rtm) (*** recognize it before delta expanding ***)
	      | MAll(Ar(etp,Prop),MImp(MAp(MDB(0),shltm),MAp(MDB(0),shrtm))) -> (*** also need to recognize delta expanded version to avoid confusion ***)
		  begin
		    try
		      let ltm = mtm_shift 0 (-1) shltm in
		      let rtm = mtm_shift 0 (-1) shrtm in
		      (etp,ltm,rtm)
		    with NegDB -> raise Not_found
		  end
	      | _ ->
		  raise Not_found
	    in
	    let rec forewritef p n margs subclaims apff =
	      if !verbosity > 19 then (Printf.printf "forewritef p : %s\n" (mtm_to_str p); flush stdout);
	      begin
		try
		  let (etp,ltm,rtm) = destruct_leibeq p in
		  begin
		    try
		      let tm1 = if sym then rtm else ltm in
		      let tm2 = if sym then ltm else rtm in
		      let (leibq,theta) = forewritef2 0 n etp tm1 claimtm in
		      if !verbosity > 90 then (Printf.printf "leibq: %s\n" (tm_to_str leibq); flush stdout);
		      let tm2i = mtm_to_tm (mtm_msub theta tm2) in
		      let ml = List.map (fun m -> mtm_to_tm (mtm_msub theta m)) margs in
		      let subclaimtms = ref [] in
		      List.iter
			(fun c ->
			  let c1 = mtm_msub theta c in
			  let c2 = mtm_to_tm c1 in
			  subclaimtms := c2::!subclaimtms)
			subclaims;
		      let apffm =
			if sym then (*** OK, this is a little confusing, but if sym is true, then we're rewriting as <- and do not need to use the eqsymPoly theorem in the proof. Otherwise, we do. ***)
			  (fun dl ->
			    match dl with
			      d::dr ->
				let epf = apff ml dr in
				PPfAp(PTmAp(epf,Lam(etp,leibq)),d)
			    | _ -> raise (Failure("proof reconstruction problem")))
			else
			  let tm1i = mtm_to_tm (mtm_msub theta tm1) in (*** I only need to compute this instance if I need to send it to eqsymPoly ***)
			  (fun dl ->
			    match dl with
			      d::dr ->
				let epf = apff ml dr in
				let epf2 = PPfAp(PTmAp(PTmAp(PTpAp(Known(!eqsymPoly),etp),tm1i),tm2i),epf) in
				PPfAp(PTmAp(epf2,Lam(etp,leibq)),d)
			    | _ -> raise (Failure("proof reconstruction problem")))
		      in
		      (tmsubst leibq 0 tm2i::!subclaimtms,apffm)
		    with Not_found ->
		      raise (Failure("rewrite tactic failed"))
		  end
		with Not_found ->
		  match p with
		  | MImp(p1,p2) ->
		      forewritef p2 n margs (p1::subclaims) (fun ml dl -> match dl with d::dr -> PPfAp(apff ml dr,d) | _ -> raise (Failure("proof reconstruction problem")))
		  | MAll(a1,p2) ->
		      begin
			match mtm_minap_db p2 0 with
			| None -> (*** special case: no occurrence, use Eps _:a1, False ***)
			    let defelt = Ap(TpAp(Prim(0),a1),Lam(a1,All(Prop,DB(0)))) in
			    forewritef p2 n margs subclaims (fun ml dl -> match dl with d::dr -> PTmAp(apff ml dr,defelt) | _ -> raise (Failure("proof reconstruction problem")))
			| Some(l) when l = 0 -> (*** simple case, like a FO var ***)
			    forewritef (mtm_ssub (MVar(n,sigma)::sigma) p2) (n+1) (MVar(n,sigma)::margs) subclaims (fun ml dl -> match ml with m::mr -> PTmAp(apff mr dl,m) | _ -> raise (Failure("proof reconstruction problem")))
			| Some(l) -> (*** otherwise, move l arguments into the context of the metavar so that the higher-order pattern case is handled ***)
			    let sigmal = (map_for (fun j -> MDB j) 0 (l-1)) @ (List.map (mtm_shift 0 l) sigma) in
			    let rec lmvnr l a m =
			      if l > 0 then
				begin
				  match a with
				  | Ar(a1,a2) -> MLam(a1,lmvnr (l-1) a2 m)
				  | _ -> raise (Failure("Type Error found while attempting apply tactic"))
				end
			      else
				m
			    in
			    let lmvn = lmvnr l a1 (MVar(n,sigmal)) in
			    let p3 = mtm_ssub (lmvn::sigma) p2 in
			    let p4 = mtm_betared_if p3 (fun q _ -> mtm_lammvar_p q) in
			    forewritef p4 (n+1) (lmvn::margs) subclaims (fun ml dl -> match ml with m::mr -> PTmAp(apff mr dl,m) | _ -> raise (Failure("proof reconstruction problem")))
		      end
		  | _ ->
		      begin
			let p1 = mtm_betared_if p (fun _ _ -> true) in (*** try to beta reduce ***)
			if p = p1 then (*** there were no beta reductions ***)
			  let (p2,del) = mheadnorm p sigdelta !deltaset in (*** try to delta expand some heads ***)
			  if p = p2 then
			    begin
			      if !verbosity > 19 then (Printf.printf "p : %s\n" (mtm_to_str p); flush stdout);
			      raise (Failure("rewrite tactic given a proof of a non-equation"))
			    end
			  else
			    begin
			      deltaset := del;
			      forewritef p2 n margs subclaims apff
			    end
			else
			  forewritef p1 n margs subclaims apff
		      end
	      end
	    in
	    begin
	      try
		if !verbosity > 19 then (Printf.printf "Proof term given with rewrite proves %s\n" (tm_to_str atm); flush stdout);
		let (subclaims,apff) = forewritef (tm_to_mtm atm) 0 [] [] (fun ml dl -> apf) in
		let nsubs = List.length subclaims in
		let currprooffun = !prooffun in
		prooffun := (fun dl -> match dl with d::dr -> let (dl1,dl2) = split_list (nsubs-1) dr in currprooffun (apff (d::(List.rev dl1))::dl2) | [] -> raise (Failure("proof reconstruction problem")));
		pfstate := (List.map (fun c -> PfStateGoal(c,cxtm,cxpf)) subclaims) @ pfstr;
		if !verbosity > 19 then (Printf.printf "here nach apply\nLength of pfstate stack: %d\n" (List.length !pfstate); flush stdout);
	      with Not_found ->
		raise (Failure("rewrite tactic failed"))
	    end
	| _ ->
	    raise (Failure("rewrite tactic cannot be used when there is no claim"))
      end
  | Qed ->
      begin
	if !pfstate = [] then
	  begin
	    try
	      if !verbosity > 19 then (Printf.printf "Qed start\n"; flush stdout);
	      if not (Hashtbl.mem indexknowns gphv) then Hashtbl.add indexknowns gphv ();
	      activate_special_knowns gphv;
	      sigpf := (thmname,!appfloc (Known(gphv)))::!sigpf;
	      if i > 0 then (*** x will look polymorphic with i types after the appropriate section is ended ***)
		pushpolypf ((thmname,i),gpgtm);
	      secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,st,(thmname,apl (Known(gphv)))::sp)) !secstack;
	      proving := None;
	      let dgpf = !prooffun [] in
	      if (!verbosity > 19) then (Printf.printf "Double checking:\n%s\n%s\n" (pf_to_str dgpf) (tm_to_str gpgtm); flush stdout);
	      match check_propofpf sigdelta sigtmof [] [] dgpf gpgtm !deltaset with
	      | None ->
		  if (!verbosity > 19) then (Printf.printf "Proof doesn't doublecheck!\n%s\n" (pf_to_str dgpf); flush stdout);
		  raise (Failure("Proof doesn't prove the proposition."))
	      | Some(dl) ->
		  deltaset := dl;
		  if (!verbosity > 19) then (Printf.printf "Delta Set:"; List.iter (fun h -> Printf.printf " %s" h) dl; Printf.printf "\n"; flush stdout);
		  let dhv = ppf_id (i,dgpf) sigtmof sigdelta in
		  if (!verbosity > 3) then (Printf.printf "Proof %s\n of %s was assigned id %s\n" (pf_to_str dgpf) thmname dhv; flush stdout);
		  if (!reportpfcomplexity) then (Printf.printf "(PFCOMPLEXITY \"%s\" \"%s\" \"%s\" %d)\n" thmname gphv dhv (pf_complexity dgpf); flush stdout);
		  begin
		    if !sqlout then
		      begin
			match !mainfilehash with
			| Some docsha ->
			    if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" gphv (stp_html_string Prop) i;
			    if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'T');\n" gphv docsha (String.escaped thmname));
			    if !sqltermout then Printf.printf "INSERT INTO `proppf` (`propid`,`pfid`) VALUES ('%s','%s');\n" gphv dhv;
			    if not !presentationonly then
			      begin
				Printf.printf "INSERT INTO `proppfdoc` (`propid`,`pfid`,`docsha`) VALUES ('%s','%s',\"%s\");\n" gphv dhv docsha;
				List.iter
				  (fun d ->
				    Printf.printf "INSERT INTO `proppfdocdelta` (`propid`,`pfid`,`docsha`,`termid`) VALUES ('%s','%s','%s','%s');\n" gphv dhv docsha d)
				  !deltaset
			      end
			| None -> ()
		      end
		  end;
		  begin
		    match !treasure with
		    | Some(traddr) ->
			begin
			  let privkey = id_to_btcprivkey dhv in
			  match Secp256k1.smulp privkey Secp256k1._g with
			  | Some(pubkeyx,pubkeyy) ->
			      let privkeywif = Cryptocurr.btcwif privkey in
			      let addr = Cryptocurr.btcaddr (pubkeyx,pubkeyy) in
			      if !verbosity > 5 then (Printf.printf "BTC private key and address for proof of %s with current salt:\n%s\n%s\n" thmname privkeywif addr; flush stdout);
			      if addr = traddr then
				begin
				  begin
				    if !sqlout then
				      begin
					match !mainfilehash with
					| Some docsha ->
					    if not !presentationonly then (Printf.printf "INSERT INTO `treasuretermdoc` (`treasureaddress`,`propid`,`docsha`,`thmdocname`) VALUES ('%s','%s','%s',\"%s\");\n" addr gphv docsha (String.escaped thmname))
					| None -> ()
				      end
				  end;
				  if !verbosity > 0 then
				    begin
				      if !webout then
					begin
					  Printf.printf "<div class='treasurefound'>Your proof of %s corresponds to the declared treasure at <a href='https://blockchain.info/address/%s'>%s</a>.<br/>The private key to claim the treasure is %s.<br/>For more information about how to claim the treasure, see <a href='treasure.php'>here</a>.</div>" thmname addr addr privkeywif;
					end
				      else if !ajax then
					begin
					  if !ajaxactive then
					    begin
					      Printf.printf "T %s %s$" addr privkeywif
					    end
					end
				      else
					begin
					  Printf.printf "The proof of %s corresponds to the declared treasure at %s.\nThe private key to claim the treasure is %s\n" thmname addr privkeywif;
					  flush stdout
					end
				    end
				end
			      else
				begin
				  if !webout then
				    begin
				      Printf.printf "<div class='treasurenotfound'>Your proof of %s is correct, but does not correspond to the declared treasure.</div>" thmname;
				    end
				  else if !ajax then
				    begin
				      if !ajaxactive then
					begin
					  Printf.printf "S$"
					end
				    end
				  else
				    raise (Failure("The proof of " ^ thmname ^ " does not correspond to the declared treasure."))
				end
			  | None ->
			      if !verbosity > 0 then
				begin
				  if !webout then
				    begin
				      Printf.printf "<div class='treasurenotfound'>Your proof of %s is correct, but does not correspond to a treasure.</div>" thmname;
				    end
				  else if !ajax then
				    begin
				      if !ajaxactive then
					begin
					  Printf.printf "S$"
					end
				    end
				  else
				    (Printf.printf "The proof of %s does not correspond to a treasure.\n" thmname; flush stdout)
				end
			end;
			treasure := None
		    | None ->
			if (!ajax && !ajaxactive) then Printf.printf "s$";
			if !verbosity > 5 || !verbosity > 0 && List.mem thmname !exercises then
			  begin
			    let privkey = id_to_btcprivkey dhv in
			    match Secp256k1.smulp privkey Secp256k1._g with
			    | Some(pubkeyx,pubkeyy) ->
				let privkeywif = Cryptocurr.btcwif privkey in
				let addr = Cryptocurr.btcaddr (pubkeyx,pubkeyy) in
				Printf.printf "*** With current salt, a treasure could be buried underneath the proof of %s at %s to be redeemed with private key %s.\n" thmname addr privkeywif; flush stdout;
				Printf.printf "(TREASURE \"%s\" \"%s\" \"%s\")\n" thmname addr privkeywif; flush stdout
			    | None ->
				Printf.printf "*** With current salt, no treasure can be buried underneath the proof of %s. Very unusual (but possible) case!\n" thmname; flush stdout		
			  end
		  end
	    with AdmittedPf ->
	      if (!verbosity > 9) then (Printf.printf "Theorem %s admitted\n" thmname; flush stdout);
	      if (!ajax && !ajaxactive) then (Printf.printf "I$"; exit 1);
	      begin
		if !sqlout then
		  begin
		    match !mainfilehash with
		    | Some docsha ->
			if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" gphv (stp_html_string Prop) i;
			if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'t');\n" gphv docsha (String.escaped thmname));
		    | None -> ()
		  end
	      end;
	      treasure := None;
	  end
	else
	  raise (Failure("Proof of " ^ thmname ^ " is incomplete"))
      end
  | Admitted ->
      begin
	if i > 0 then (*** x will look polymorphic with i types after the appropriate section is ended ***)
	  pushpolypf ((thmname,i),gpgtm);
	activate_special_knowns gphv;
	sigpf := (thmname,!appfloc (Known(gphv)))::!sigpf;
	secstack := List.map (fun (y,f,atl,apl,st,sp) -> (y,f,atl,apl,st,(thmname,apl (Known(gphv)))::sp)) !secstack;
	proving := None;
	pfstate := [];
	treasure := None;
	admits := true;
	begin
	  if !sqlout then
	    begin
	      match !mainfilehash with
	      | Some docsha ->
		  if !sqltermout then Printf.printf "INSERT INTO `term` (`termid`,`termtp`,`termpoly`) VALUES ('%s','%s',%d);\n" gphv (stp_html_string Prop) i;
		  if not !presentationonly then (Printf.printf "INSERT INTO `termdoc` (`termid`,`docsha`,`termdocname`,`termdockind`) VALUES ('%s','%s',\"%s\",'t');\n" gphv docsha (String.escaped thmname));
	      | None -> ()
	    end
	end;
      end
  | Admit ->
      begin
	match !pfstate with
	| (pfst::pfstr) ->
	    pfstate := pfstr;
	    admits := true;
	    prooffun := (fun _ -> raise AdmittedPf)
	| [] -> raise (Failure("No goal to admit"))
      end
  | _ ->
      raise (Failure("Unknown proof tactic"))

let rec evaluate_pftac_2 () =
  match !pfstate with
  | PfStateSep(j,false)::pfstr ->
      begin
	match !html with
	| Some hc -> output_pftacitem_html hc (PfStruct(j)) sigtmh sigknh 3
	| None -> ()
      end;
      pfstate := pfstr;
      evaluate_pftac_2 ()
  | _ -> ()

let evaluate_pftac pitem thmname i gpgtm gphv =
  if !verbosity > 19 then (Printf.printf "pre1 pfstruct %d\nLength of pfstate stack: %d\n" i (List.length !pfstate); print_pfstate (); flush stdout);
  evaluate_pftac_1 pitem thmname i gpgtm gphv;
  begin
    match !html with
    | Some hc ->
	if pitem = Qed || pitem = Admitted then
	  begin
	    match !inchan with
	    | Some(c) -> buffer_to_line_char c pftext inchanline inchanchar !lineno !charno
	    | None -> ()
	  end;
	output_pftacitem_html hc pitem sigtmh sigknh !laststructaction
    | None -> ()
  end;
  if !verbosity > 19 then (Printf.printf "pre2 pfstruct %d\nLength of pfstate stack: %d\n" i (List.length !pfstate); print_pfstate (); flush stdout);
  evaluate_pftac_2 ()

let init_env () =
  ctxtp := [];
  ctxtm := [];
  ctxpf := [];
  tparclos := (fun a -> a);
  tmallclos := (fun m -> m);
  tmlamclos := (fun m -> m);
  pflamclos := (fun d -> d);
  aptmloc := (fun m cxtp cxtm -> m);
  appfloc := (fun d cxtp cxtm cxpf -> d);
  secstack := [];
  popfn := (fun () -> ())
	
(*** Function for checking if a file solves a problem file in addition to checking the solution file for correctness. ***)
let mgchecksolves probc solnc =
  init_env ();
  let ptl = ref (TokStrRest(Lexer.token,Lexing.from_channel probc)) in
  let stl = ref (TokStrRest(Lexer.token,Lexing.from_channel solnc)) in
  let currentthm = ref "" in
  let inadmitted = ref false in
  let linenop = ref 1 in
  let charnop = ref 0 in
  let linenos = ref 1 in
  let charnos = ref 0 in
  try
    while true do
      match !proving with
      | None ->
	  begin
	    lineno := !linenop;
	    charno := !charnop;
	    let (pditem,ptr) =
	      try
		parse_docitem !ptl
	      with Lexer.Eof ->
		let _ = parse_docitem !stl in
		raise (Failure("Problem file ended prematurely"))
	    in
	    linenop := !lineno;
	    charnop := !charno;
	    lineno := !linenos;
	    charno := !charnos;
	    authors := [];
	    title := None;
	    let (sditem,str) =
	      try
		parse_docitem !stl
	      with Lexer.Eof ->
		raise (Failure("Solution file ended prematurely"))
	    in
	    linenos := !lineno;
	    charnos := !charno;
	    ptl := ptr;
	    stl := str;
	    evaluate_docitem sditem;
	    if pditem <> sditem then
	      raise (Failure("Solution document differs from problem document at line " ^ (string_of_int !linenop) ^ " and char " ^ (string_of_int !charnop) ^ " / line " ^ (string_of_int !linenos) ^ " and char " ^ (string_of_int !charnos)));
	    match sditem with
	    | ThmDecl(_,x,_) -> currentthm := x
	    | _ -> ()
	  end
      | Some (thmname,i,gpgtm,gphv) -> (*** reading a proof in the solution file ***)
	  begin
	    if !inadmitted then
	      begin
		lineno := !linenos;
		charno := !charnos;
		let (spftac,str) =
		  try
		    parse_pftacitem !stl
		  with Lexer.Eof ->
		    raise (Failure("Solution file ended prematurely"))
		in
		stl := str;
		linenos := !lineno;
		charnos := !charno;
		evaluate_pftac spftac thmname i gpgtm gphv;
		if spftac = Qed then
		  inadmitted := false
		else if spftac = Admit || spftac = Admitted then
		  raise (Failure("Incomplete proof in solution file"))
	      end
	    else
	      begin
		lineno := !linenop;
		charno := !charnop;
		let (ppftac,ptr) =
		  try
		    parse_pftacitem !ptl
		  with Lexer.Eof ->
		    let _ = parse_pftacitem !stl in
		    raise (Failure("Problem file ended prematurely"))
		in
		linenop := !lineno;
		charnop := !charno;
		lineno := !linenos;
		charno := !charnos;
		let (spftac,str) =
		  try
		    parse_pftacitem !stl
		  with Lexer.Eof ->
		    raise (Failure("Solution file ended prematurely"))
		in
		linenos := !lineno;
		charnos := !charno;
		ptl := ptr;
		stl := str;
		evaluate_pftac spftac thmname i gpgtm gphv;
		if spftac = Admit || spftac = Admitted then
		  raise (Failure("Incomplete proof in solution file"));
		if ppftac <> spftac then
		  begin
		    if ppftac = Admitted then
		      begin
			exercises := !currentthm :: !exercises;
			if spftac <> Qed then
			  inadmitted := true
		      end
		    else
		      raise (Failure("Solution document differs from problem document in proof at line " ^ (string_of_int !linenop) ^ " and char " ^ (string_of_int !charnop) ^ " / line " ^ (string_of_int !linenos) ^ " and char " ^ (string_of_int !charnos)))
		  end
	      end
	  end
    done
  with
  | Lexer.Eof ->
      ()
  | ParsingError(x,l1,c1,l2,c2) ->
      if !webout then
	begin
          Printf.printf "AS%d:%d:%d:%d\n"  l1 c1 l2 c2;
	  Printf.printf "<div class='documentfail'>Syntax error between line %d char %d and line %d char %d:<br/>%s</div>" l1 c1 l2 c2 x;
	  exit 1
	end
      else
	begin
	  Printf.printf "Syntax error between line %d char %d and line %d char %d:\n%s\n" l1 c1 l2 c2 x;
	  exit 1
	end
  | Failure(x) ->
      if !webout then
	begin
          Printf.printf "AF%d:%d\n"  !lineno !charno;
	  Printf.printf "<div class='documentfail'>Failure at line %d char %d: %s</div>" !lineno !charno x; flush stdout;
	  exit 1
	end
      else
	begin
	  Printf.printf "Failure at line %d char %d: %s\n" !lineno !charno x; flush stdout;
	  exit 1
	end

exception CheckSigOK

(*** Function for checking if a file implements a signature. (It is also order sensitive, just to make this code simpler.) ***)
let mgchecksig sigc solnc =
  init_env ();
  let sigtl = ref (TokStrRest(Lexer.token,Lexing.from_channel sigc)) in
  let stl = ref (TokStrRest(Lexer.token,Lexing.from_channel solnc)) in
  let linenop = ref 1 in
  let charnop = ref 0 in
  let linenos = ref 1 in
  let charnos = ref 0 in
  let psigh : (string,string) Hashtbl.t = Hashtbl.create 10 in
  let bufferedsigditem : docitem option ref = ref None in
  try
    while true do
      match !proving with
      | None ->
	  begin
	    lineno := !linenop;
	    charno := !charnop;
	    let (pditem,sigtr) =
	      begin
		match !bufferedsigditem with
		| Some(pditem) -> bufferedsigditem := None; (pditem,!sigtl)
		| None ->
		    try
		      parse_docitem !sigtl
		    with Lexer.Eof -> (*** OK, it implements the signature. (Don't check that the rest of the main file is OK.) ***)
		      raise CheckSigOK
	      end
	    in
	    linenop := !lineno;
	    charnop := !charno;
	    match pditem with
	    | ParamHash(x,h) ->
		Hashtbl.add psigh x h
	    | _ ->
		begin
		  lineno := !linenos;
		  charno := !charnos;
		  authors := [];
		  title := None;
		  let (sditem,str) =
		    try
		      parse_docitem !stl
		    with Lexer.Eof ->
		      raise (Failure("Main file ended before signature was implemented, signature is at line " ^ string_of_int !linenop ^ " char " ^ string_of_int !charnop))
		  in
		  linenos := !lineno;
		  charnos := !charno;
		  sigtl := sigtr;
		  stl := str;
		  evaluate_docitem sditem;
		  if pditem <> sditem then
		    begin
		      match (pditem,sditem) with
		      | (AxDecl(y,ya),ThmDecl(_,x,xa)) when y = x ->
			  if ya <> xa then
			    raise (Failure("Mismatch with " ^ x))
		      | (ParamDecl(y,ya),DefDecl(x,_,_)) when y = x ->
			  begin
			    try
			      let xh = Hashtbl.find sigtmh x in
			      begin
				try
				  let yh = Hashtbl.find psigh y in
				  if xh <> yh then
				    raise (Failure("Mismatch with " ^ x))
				with Not_found ->
				  raise (Failure("Could not find id of " ^ y ^ " in the signature"))
			      end
			    with Not_found ->
			      raise (Failure("Could not find id of " ^ x ^ " -- impossible!"))
			  end
		      | _ -> bufferedsigditem := Some pditem (*** wait until it is reached ***)
		    end
		end
	  end
      | Some (thmname,i,gpgtm,gphv) -> (*** reading a proof in the main file; signature file is ignored here ***)
	  begin
	    lineno := !linenos;
	    charno := !charnos;
	    let (spftac,str) =
	      try
		parse_pftacitem !stl
	      with Lexer.Eof ->
		    raise (Failure("Main file ended prematurely"))
	    in
	    stl := str;
	    linenos := !lineno;
	    charnos := !charno;
	    evaluate_pftac spftac thmname i gpgtm gphv;
	    if spftac = Admit || spftac = Admitted then
	      raise (Failure("Incomplete proof in main file"))
	  end
    done
  with
  | Lexer.Eof ->
      ()
  | ParsingError(x,l1,c1,l2,c2) ->
      if !webout then
	begin
          Printf.printf "AS%d:%d:%d:%d\n"  l1 c1 l2 c2;
	  Printf.printf "<div class='documentfail'>Syntax error between line %d char %d and line %d char %d:<br/>%s</div>" l1 c1 l2 c2 x;
	  exit 1
	end
      else
	begin
	  Printf.printf "Syntax error between line %d char %d and line %d char %d:\n%s\n" l1 c1 l2 c2 x;
	  exit 1
	end
  | Failure(x) ->
      if !webout then
	begin
          Printf.printf "AF%d:%d\n"  !lineno !charno;
	  Printf.printf "<div class='documentfail'>Failure at line %d char %d: %s</div>" !lineno !charno x; flush stdout;
	  exit 1
	end
      else
	begin
	  Printf.printf "Failure at line %d char %d: %s\n" !lineno !charno x; flush stdout;
	  exit 1
	end

let mgcheck_ajax c =
  let tl = ref (TokStrRest(Lexer.token,Lexing.from_channel c)) in
  lineno := 1;
  charno := 0;
  verbosity := 1;
  try
    while true do
      if !verbosity > 59 then (Printf.printf "Main Loop Start\n"; flush stdout);
      match !proving with
      | None ->
	  ignore (parse_docitem !tl); (*** hopefully this raises End_of_file ***)
	  raise (Failure("The content must not continue beyond the proof."))
      | Some (thmname,i,gpgtm,gphv) -> (*** reading a proof ***)
	  let (pitem,tr) = parse_pftacitem !tl in
	  tl := tr;
	  evaluate_pftac pitem thmname i gpgtm gphv
    done
  with
  | Lexer.Eof ->
      begin
	match !proving with
	| None -> () (* OK *)
	| Some(thmname,i,gpgtm,gphv) -> (* pretend there is a Qed at the end *)
	    try
	      evaluate_pftac Qed thmname i gpgtm gphv
	    with
	    | Failure(x) ->
		Printf.printf "F %d %d$%s" !lineno !charno x
	    | ParsingError(x,l1,c1,l2,c2) ->
		Printf.printf "E %d %d %d %d$%s" l1 c1 l2 c2 x
      end
  | Failure(x) ->
      Printf.printf "F %d %d$%s" !lineno !charno x
  | ParsingError(x,l1,c1,l2,c2) ->
      Printf.printf "E %d %d %d %d$%s" l1 c1 l2 c2 x

(*** Main function for checking a file ***)
let mgcheck c =
  init_env ();
  let tl = ref (TokStrRest(Lexer.token,Lexing.from_channel c)) in
  lineno := 1;
  charno := 0;
  try
    while true do
      if !verbosity > 59 then (Printf.printf "Main Loop Start\n"; flush stdout);
      match !proving with
      | None ->
	  let (ditem,tr) = parse_docitem !tl in
	  tl := tr;
	  evaluate_docitem ditem
      | Some (thmname,i,gpgtm,gphv) -> (*** reading a proof ***)
	  let (pitem,tr) = parse_pftacitem !tl in
	  tl := tr;
	  evaluate_pftac pitem thmname i gpgtm gphv
    done
  with
  | Lexer.Eof ->
    begin
      if !ajax then (*** we should be expecting a proof which can be read from the given proof file ***)
	if not !includingsigfile then
	  begin
	    ajaxactive := true;
	    let ca = open_in !ajaxpffile in
	    mgcheck_ajax ca
	  end
      else
	if (!verbosity > 9) then (Printf.printf "done.\n"; flush stdout)
    end
  | ParsingError(x,l1,c1,l2,c2) ->
      if !webout then
	begin
          Printf.printf "AS%d:%d:%d:%d\n"  l1 c1 l2 c2;
	  Printf.printf "<div class='documentfail'>Syntax error between line %d char %d and line %d char %d:<br/>%s</div>" l1 c1 l2 c2 x;
	  exit 1
	end
      else if !ajax then
	begin
	  Printf.printf "f\n"; (*** this indicates a fundamental problem, not a problem with the ajax input ***)
	  exit 1
	end
      else
	begin
	  Printf.printf "Syntax error between line %d char %d and line %d char %d:\n%s\n" l1 c1 l2 c2 x;
	  exit 1
	end
  | Failure(x) ->
      if !webout then
	begin
          Printf.printf "AF%d:%d\n"  !lineno !charno;
	  Printf.printf "<div class='documentfail'>Failure at line %d char %d: %s</div>" !lineno !charno x; flush stdout;
	  exit 1
	end
      else if !ajax then
	begin
	  Printf.printf "f\n"; (*** this indicates a fundamental problem, not a problem with the ajax input ***)
	  exit 1
	end
      else
	begin
	  Printf.printf "Failure at line %d char %d: %s\n" !lineno !charno x; flush stdout;
	  exit 1
	end

let rec sql_docpresentation docsha c i =
  try
    let l = input_line c in
    sql_docpresentation_0 docsha c l i
  with End_of_file -> ()
and sql_docpresentation_0 docsha c l i =
  if String.length l > 0 && l.[0] = '$' then
    begin
      if String.length l > 1 then
	if l.[1] = 'x' then
	  begin
	    Printf.printf "INSERT INTO `docpresentationpart` (`docsha`,`docpresentationpartno`,`docpresentationpartexercise`) VALUES ('%s',%d,'%s');\n" docsha i (String.sub l 2 (String.length l - 2));
	    if not !presentationonly then (Printf.printf "INSERT INTO `docexercise` (`docsha`,`termid`) VALUES ('%s','%s');\n" docsha (String.sub l 2 (String.length l - 2)));
	  end
	else
	  Printf.printf "INSERT INTO `docpresentationpart` (`docsha`,`docpresentationpartno`,`docpresentationparttreasure`) VALUES ('%s',%d,'%s');\n" docsha i (String.sub l 1 (String.length l - 1));
      sql_docpresentation docsha c (i+10)
    end
  else
    begin
      Printf.printf "INSERT INTO `docpresentationpart` (`docsha`,`docpresentationpartno`,`docpresentationparttext`) VALUES ('%s',%d,'" docsha i;
      try
	sql_docpresentation_1 docsha c l (i+10)
      with End_of_file ->
	Printf.printf "');\n";
    end
and sql_docpresentation_1 docsha c l i =
  if String.length l > 0 && l.[0] = '$' then
    begin
      Printf.printf "');\n";
      sql_docpresentation_0 docsha c l i
    end
  else
    begin
      for j = 0 to String.length l - 1 do
	let z = l.[j] in
	if z = '\'' then
	  (output_char stdout z; output_char stdout z)
	else if z = '\\' then
	  (output_char stdout '\\'; output_char stdout '\\')
	else
	  output_char stdout z
      done;
      output_char stdout '\n';
      let l = input_line c in
      sql_docpresentation_1 docsha c l i
    end

let preset_ptm_id (m:ptm) : string =
  let h = ptm_id m sigtmof sigdelta in
  Hashtbl.add sigdelta h m;
  h

(*** "main" ***)
let _ =
  (*** There are some global names I need before getting started to make the proof tactics work, so they are precomputed here. ***)
  fal := preset_ptm_id (0,All(Prop,DB(0)));
  eqPoly := preset_ptm_id (1,Lam(TpVar(0),Lam(TpVar(0),All(Ar(TpVar(0),Prop),Imp(Ap(DB(0),DB(2)),Ap(DB(0),DB(1)))))));
  eqsymPoly := preset_ptm_id (1,All(TpVar(0),All(TpVar(0),Imp(Ap(Ap(TpAp(TmH(!eqPoly),TpVar(0)),DB(1)),DB(0)),Ap(Ap(TpAp(TmH(!eqPoly),TpVar(0)),DB(0)),DB(1))))));
  eqSet := preset_ptm_id (0,Lam(Set,Lam(Set,All(Ar(Set,Prop),Imp(Ap(DB(0),DB(2)),Ap(DB(0),DB(1)))))));
  conj := preset_ptm_id (0,Lam(Prop,Lam(Prop,All(Prop,Imp(Imp(DB(2),Imp(DB(1),DB(0))),DB(0))))));
  disj := preset_ptm_id (0,Lam(Prop,Lam(Prop,All(Prop,Imp(Imp(DB(2),DB(0)),Imp(Imp(DB(1),DB(0)),DB(0)))))));
  expoly := preset_ptm_id (1,Lam(Ar(TpVar(0),Prop),All(Prop,Imp(All(TpVar(0),Imp(Ap(DB(2),DB(0)),DB(1))),DB(0)))));
  expolyI := preset_ptm_id (1,All(Ar(TpVar(0),Prop),All(TpVar(0),Imp(Ap(DB(1),DB(0)),Ap(TpAp(TmH(!expoly),TpVar(0)),DB(1))))));
  let i = Array.length Sys.argv in
  if i = 1 then
    mgcheck stdin (*** if no arguments are given, read and check from stdin ***)
  else (*** otherwise, assume the last argument is the main file from which to read and check ***)
    begin
      (*** Process command line arguments including reading signature input files ***)
      let j = ref 0 in
      while (!j < i - 2) do
	incr j;
	if Sys.argv.(!j) = "-I" then
	  begin
	    match !html with
	    | Some(_) -> raise (Failure("-I must come before -html"))
	    | None -> includingsigfile := true
	  end
	else if Sys.argv.(!j) = "-s" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		incr j;
		match !sigoutfile with
		| Some _ -> raise (Failure("Cannot use -s twice"))
		| None -> sigoutfile := Some (open_out (Sys.argv.(!j)))
	      end
	    else
	      raise (Failure("Expected -s <outsigfilename>"))
	  end
	else if Sys.argv.(!j) = "-checksig" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		incr j;
		checksigfile := Some (Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -checksig <sigfilename>"))
	  end
	else if Sys.argv.(!j) = "-indout" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		incr j;
		match !indoutfile with
		| Some _ -> raise (Failure("Cannot use -indout twice"))
		| None -> indoutfile := Some (Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -indout <indoutfilename>"))
	  end
	else if Sys.argv.(!j) = "-ind" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		incr j;
		let c = open_in (Sys.argv.(!j)) in
		read_indexfile c;
		close_in c;
	      end
	    else
	      raise (Failure("Expected -ind <indexfilename>"))
	  end
	else if Sys.argv.(!j) = "-solves" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		incr j;
		solvesproblemfile := Some (Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -solves <indexfilename>"))
	  end
	else if Sys.argv.(!j) = "-reportpfcomplexity" then
	  begin
	    includingsigfile := false;
	    reportpfcomplexity := true
	  end
	else if Sys.argv.(!j) = "-reporteachitem" then
	  begin
	    includingsigfile := false;
	    reporteachitem := true
	  end
	else if Sys.argv.(!j) = "-polyexpand" then (*** This is needed to check the original "treasure hunt" documents from 2014. ***)
	  begin
	    polyexpand := true;
	  end
	else if Sys.argv.(!j) = "-webout" then
	  begin
	    includingsigfile := false;
	    webout := true;
	  end
	else if Sys.argv.(!j) = "-ajax" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		ajax := true;
		incr j;
		ajaxpffile := Sys.argv.(!j);
		verbosity := 0;
	      end
	    else
	      raise (Failure("Expected -ajax <pffile>"))
	  end
	else if Sys.argv.(!j) = "-sqltermout" then (*** this should only be used when -sqlout is already being used ***)
	  begin
	    includingsigfile := false;
	    sqltermout := true;
	  end
	else if Sys.argv.(!j) = "-presentationonly" then
	  begin
	    includingsigfile := false;
	    presentationonly := true;
	  end
	else if Sys.argv.(!j) = "-sqlout" then
	  begin
	    verbosity := 0;
	    includingsigfile := false;
	    sqlout := true;
	    let docsha = Hash.sha256file (Sys.argv.(i-1)) in
	    mainfilehash := Some docsha;
	    if not !presentationonly then Printf.printf "INSERT INTO `docpurchaseinfo` (`docsha`,`docpurchaseinfotext`) VALUES ('%s','insert purchase info');\n" docsha;
	    begin (*** see if html info was already generated and if so include it here; Note: I may have modified the html by hand so be careful. ***)
	      try
		let htmlfile =
		  if Filename.check_suffix (Sys.argv.(i-1)) ".mg" then
		    (Filename.chop_suffix (Sys.argv.(i-1)) ".mg") ^ ".html"
		  else if Filename.check_suffix (Sys.argv.(i-1)) ".mgs" then
		    (Filename.chop_suffix (Sys.argv.(i-1)) ".mgs") ^ ".html"
		  else
		    raise Not_found
		in
		if Sys.file_exists htmlfile then
		  begin
		    let c = open_in htmlfile in
		    sql_docpresentation docsha c 1;
		    close_in c
		  end
	      with Not_found -> ()
	    end;
	    begin
	      let sc = ref 0 in
	      List.iter
		(fun x ->
		  begin
		    incr sc;
		    let xsha = Hash.sha256file x in
		    if not !presentationonly then (Printf.printf "INSERT INTO `docpreamble` (`docsha`,`docpreamblesha`,`docpreambleord`,`docpreamblename`) VALUES ('%s','%s',%d,'%s');\n" docsha xsha !sc (Filename.basename x));
		  end) (List.rev !includedsigfiles);
	    end;
	    let c = open_in (Sys.argv.(i-1)) in
	    let lno = ref 0 in
	    try
	      while true do
		incr lno;
		let l = input_line c in
		if not !presentationonly then (Printf.printf "INSERT INTO `docformalline` (`docsha`,`docformallineno`,`docformallinetext`) VALUES ('%s',%d,\"%s\");\n" docsha !lno (String.escaped l));
	      done
	    with End_of_file -> close_in c
	  end
	else if Sys.argv.(!j) = "-thmsasexercises" then
	  begin
	    verbosity := 0;
	    includingsigfile := false;
	    thmsasexercises := true;
	  end
	else if Sys.argv.(!j) = "-v" then
	  begin
	    if !j < i-2 then
	      begin
		incr j;
		verbosity := int_of_string (Sys.argv.(!j))
	      end
	    else
	      raise (Failure("Expected -v <verbositynumber>"))
	  end
	else if Sys.argv.(!j) = "-html" then
	  begin
	    includingsigfile := false;
	    if !j < i-2 then
	      begin
		incr j;
		let filehash = Hash.sha256file (Sys.argv.(i-1)) in
		let c = open_out (Sys.argv.(!j)) in
		Printf.fprintf c "<input type='hidden' id='mainfilehash' value='%s'/>\n" filehash;
		html := Some c
	      end
	    else
	      raise (Failure("Expected -html <htmloutfilename>"))
	  end
	else if !includingsigfile then
	  let c = open_in (Sys.argv.(!j)) in
	  mgcheck c;
	  title := None;
	  authors := [];
	  includedsigfiles := Sys.argv.(!j)::!includedsigfiles
	else
	  raise (Failure("Cannot understand command line argument " ^ (Sys.argv.(!j))))
      done;
      includingsigfile := false;
      let checkfile () =
	let c = open_in (Sys.argv.(i-1)) in
	begin
	  match !html with
	  | Some(_) ->
	      inchan := Some (open_in (Sys.argv.(i-1))) (*** This is a second channel for reading the input file currently used to record a literal copy of the text of proofs ***)
	  | None ->
	      ()
	end;
	mgcheck c;
	close_in c;
	begin
	  match !sigoutfile with
	  | Some(soc) -> close_out soc
	  | None -> ()
	end;
	begin
	  match !inchan with
	  | Some(c) -> close_in c
	  | None -> ()
	end;
      in
      begin
	match !solvesproblemfile,!checksigfile with
	| None,None -> checkfile ()
	| Some probf,None ->
	    let p = open_in probf in
	    let c = open_in (Sys.argv.(i-1)) in
	    mgchecksolves p c;
	    close_in c;
	    close_in p;
	    if !verbosity > 1 then (Printf.printf "%s completely solves %s\n" Sys.argv.(i-1) probf; flush stdout);
	| None,Some checksigf ->
	    let p = open_in checksigf in
	    let c = open_in (Sys.argv.(i-1)) in
	    begin
	      try
		mgchecksig p c;
		close_in c;
		close_in p;
	      with CheckSigOK ->
		close_in c;
		close_in p;
	    end;
	    if !verbosity > 1 then (Printf.printf "%s implements the signature %s\n" Sys.argv.(i-1) checksigf; flush stdout);
	| Some probf,Some checksigf -> raise (Failure("Cannot check a sig file and verify a solution to a problem file at the same time.\nThat is, do not use -checksig and -solves together."))
      end
    end;
  begin
    match !html with
    | Some hc ->
	close_out hc
    | None -> ()
  end;
  if !webout then
    begin
      Printf.printf "<div class='documentcorrect'>The document in its current form is correct.</div>\n";
    end;
  if (!reportids) then
    begin
      match !indoutfile with
      | Some(f) ->
	  let c = open_out f in
	  Hashtbl.iter (fun h a -> Printf.fprintf c "%s %s.\n" h (tp_to_str a)) indextms;
	  Hashtbl.iter (fun x _ -> Printf.fprintf c "Known %s.\n" x) indexknowns;
	  close_out c
      | None ->
	  ()
    end
;;
