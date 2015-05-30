(* Copyright (c) 2014 Chad E Brown *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(*** File: syntax.ml ***)
(*** Chad E. Brown ***)
(*** Jan 18 2014 ***)

open Big_int

let currtmid : string ref = ref ""
let thmcount : int ref = ref 0
let pflinestart : int ref = ref 0
let pfcharstart : int ref = ref 0
let pftext : Buffer.t = Buffer.create 10000
(***
 If polyexpand is true, it expands polymorphic definitions when the type arguments are closed before computing hash identifiers.
 Otherwise, polymorphic definitions are not expanded when computing hash identifiers.
 Note that this changes the identifiers of many terms.
 ***)
let polyexpand : bool ref = ref false

type tp = TpVar of int | Prop | Set | Ar of tp * tp

let rec notpvarsp a =
  match a with
  | TpVar _ -> false
  | Ar(a1,a2) -> notpvarsp a1 && notpvarsp a2
  | _ -> true

(*** assume number of type variables is between 0 and 3 ***)
type ptp = int * tp

let primname x =
  match x with
  | "Eps" -> (0,(1,Ar(Ar(TpVar 0,Prop),TpVar 0)))
  | "In" -> (1,(0,Ar(Set,Ar(Set,Prop))))
  | "Empty" -> (2,(0,Set))
  | "Union" -> (3,(0,Ar(Set,Set)))
  | "Power" -> (4,(0,Ar(Set,Set)))
  | "Repl" -> (5,(0,Ar(Set,Ar(Ar(Set,Set),Set))))
  | "UnivOf" -> (6,(0,Ar(Set,Set)))
  | _ -> raise Not_found

type tm =
  | DB of int
  | TmH of string
  | Prim of int
  | TpAp of tm * tp
  | Ap of tm * tm
  | Lam of tp * tm
  | Imp of tm * tm
  | All of tp * tm

type ptm = int * tm

type pf =
  | Hyp of int
  | Known of string
  | PTpAp of pf * tp
  | PTmAp of pf * tm
  | PPfAp of pf * pf
  | PLam of tm * pf
  | TLam of tp * pf

type ppf = int * pf

type setinfixop = InfMem | InfSubq

type infixop =
  | InfSet of setinfixop
  | InfNam of string

type asckind = AscTp | AscSet | AscSubeq

type atree =
  | Na of string
  | Nu of bool * string * string option * string option
  | Le of string * (asckind * atree) option * atree * atree
  | LeM of string * string list * atree * atree
  | Bi of string * (string list * (asckind * atree) option) list * atree
  | Preo of string * atree
  | Posto of string * atree
  | Info of infixop * atree * atree
  | Implop of atree * atree
  | Sep of string * setinfixop * atree * atree
  | Rep of string * setinfixop * atree * atree
  | SepRep of string * setinfixop * atree * atree * atree
  | SetEnum of atree list
  | MTuple of atree * atree list
  | Tuple of atree * atree * atree list
  | IfThenElse of atree * atree * atree

type ltree =
  | NaL of string
  | NuL of bool * string * string option * string option
  | LeL of string * (asckind * ltree) option * ltree * ltree
  | LeML of string * string list * ltree * ltree
  | BiL of string * string * (string list * (asckind * ltree) option) list * ltree
  | PreoL of string * ltree
  | PostoL of string * ltree
  | InfoL of infixop * ltree * ltree
  | ImplopL of ltree * ltree
  | SepL of string * setinfixop * ltree * ltree
  | RepL of string * setinfixop * ltree * ltree
  | SepRepL of string * setinfixop * ltree * ltree * ltree
  | SetEnumL of ltree list
  | MTupleL of ltree * ltree list
  | ParenL of ltree * ltree list
  | IfThenElseL of ltree * ltree * ltree

let rec binderishp (a:ltree) : bool =
  match a with
  | BiL(_) -> true
  | LeL(_) -> true
  | LeML(_) -> true
  | IfThenElseL(_) -> true
  | PreoL(x,a) -> binderishp a
  | InfoL(i,a,b) -> binderishp b
  | _ -> false

let setinfixop_string i =
  match i with
  | InfMem -> ":e"
  | InfSubq -> "c="

let asckind_string i =
  match i with
  | AscTp -> ":"
  | AscSet -> ":e"
  | AscSubeq -> "c="

let rec output_ltree ch a =
  match a with
  | NaL(x) -> output_string ch x
  | NuL(b,x,None,None) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
      end
  | NuL(b,x,Some y,None) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch '.';
	output_string ch y;
      end
  | NuL(b,x,None,Some z) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch 'E';
	output_string ch z;
      end
  | NuL(b,x,Some y,Some z) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch '.';
	output_string ch y;
	output_char ch 'E';
	output_string ch z;
      end
  | LeL(x,None,a,c) ->
      output_string ch "let ";
      output_string ch x;
      output_string ch " := ";
      output_ltree ch a;
      output_string ch " in ";
      output_ltree ch c
  | LeL(x,Some (i,b),a,c) ->
      output_string ch "let ";
      output_string ch x;
      output_char ch ' ';
      output_string ch (asckind_string i);
      output_char ch ' ';
      output_ltree ch b;
      output_string ch " := ";
      output_ltree ch a;
      output_string ch " in ";
      output_ltree ch c
  | LeML(x,xl,a,c) ->
      output_string ch "let [";
      output_string ch x;
      List.iter (fun y -> output_char ch ','; output_string ch y) xl;
      output_string ch "] := ";
      output_ltree ch a;
      output_string ch " in ";
      output_ltree ch c
  | BiL(x,m,[(xl,None)],c) ->
      output_string ch x;
      List.iter (fun y -> output_char ch ' '; output_string ch y) xl;
      output_char ch ' ';
      output_string ch m;
      output_char ch ' ';
      output_ltree ch c
  | BiL(x,m,[(xl,Some(i,b))],c) ->
      output_string ch x;
      List.iter (fun y -> output_char ch ' '; output_string ch y) xl;
      output_char ch ' ';
      output_string ch (asckind_string i);
      output_char ch ' ';
      output_ltree ch b;
      output_char ch ' ';
      output_string ch m;
      output_char ch ' ';
      output_ltree ch c
  | BiL(x,m,vll,c) ->
      output_string ch x;
      List.iter
	(fun vl ->
	  output_string ch " (";
	  let nfst = ref false in
	  begin
	    match vl with
	    | (xl,None) ->
		List.iter (fun y -> if !nfst then output_char ch ' '; nfst := true; output_string ch y) xl;
	    | (xl,Some(AscTp,b)) ->
		List.iter (fun y -> if !nfst then output_char ch ' '; nfst := true; output_string ch y) xl;
		output_string ch " : ";
		output_ltree ch b
	    | (xl,Some(AscSet,b)) ->
		List.iter (fun y -> if !nfst then output_char ch ' '; nfst := true; output_string ch y) xl;
		output_string ch " :e ";
		output_ltree ch b
	    | (xl,Some(AscSubeq,b)) ->
		List.iter (fun y -> if !nfst then output_char ch ' '; nfst := true; output_string ch y) xl;
		output_string ch " c= ";
		output_ltree ch b
	  end;
	  output_char ch ')';
	  )
	vll;
      output_char ch ' ';
      output_string ch m;
      output_char ch ' ';
      output_ltree ch c
  | PreoL(x,a) ->
      output_string ch x;
      output_char ch ' ';
      output_ltree ch a
  | PostoL(x,a) ->
      output_ltree ch a;
      output_char ch ' ';
      output_string ch x
  | InfoL(InfSet i,a,b) ->
      output_ltree ch a;
      output_char ch ' ';
      output_string ch (setinfixop_string i);
      output_char ch ' ';
      output_ltree ch b
  | InfoL(InfNam x,a,b) ->
      output_ltree ch a;
      output_char ch ' ';
      output_string ch x;
      output_char ch ' ';
      output_ltree ch b
  | ImplopL(a,b) ->
      output_ltree ch a;
      output_char ch ' ';
      output_ltree ch b
  | SepL(x,i,a,b) ->
      output_char ch '{';
      output_string ch x;
      output_char ch ' ';
      output_string ch (setinfixop_string i);
      output_char ch ' ';
      output_ltree ch a;
      output_char ch '|';
      output_ltree ch b;
      output_char ch '}';
  | RepL(x,i,a,b) ->
      output_char ch '{';
      output_ltree ch a;
      output_char ch '|';
      output_string ch x;
      output_char ch ' ';
      output_string ch (setinfixop_string i);
      output_char ch ' ';
      output_ltree ch b;
      output_char ch '}';
  | SepRepL(x,i,a,b,c) ->
      output_char ch '{';
      output_ltree ch a;
      output_char ch '|';
      output_string ch x;
      output_char ch ' ';
      output_string ch (setinfixop_string i);
      output_char ch ' ';
      output_ltree ch b;
      output_char ch ',';
      output_ltree ch c;
      output_char ch '}';
  | SetEnumL(al) ->
      begin
	output_char ch '{';
	match al with
	| [] -> output_char ch '}';
	| (a::bl) ->
	    output_ltree ch a;
	    List.iter (fun b -> output_char ch ','; output_ltree ch b) bl;
	    output_char ch '}';
      end
  | MTupleL(a,bl) ->
      output_char ch '[';
      output_ltree ch a;
      List.iter (fun b -> output_char ch ','; output_ltree ch b) bl;
      output_char ch ']';
  | ParenL(a,bl) ->
      output_char ch '(';
      output_ltree ch a;
      List.iter (fun b -> output_char ch ','; output_ltree ch b) bl;
      output_char ch ')';
  | IfThenElseL(a,b,c) ->
      output_string ch "if ";
      output_ltree ch a;
      output_string ch " then ";
      output_ltree ch b;
      output_string ch " else ";
      output_ltree ch c

let rec ltree_to_atree a =
  match a with
  | NaL(x) -> Na(x)
  | NuL(b,x,y,z) -> Nu(b,x,y,z)
  | LeL(x,None,a,c) -> Le(x,None,ltree_to_atree a,ltree_to_atree c)
  | LeL(x,Some(i,b),a,c) -> Le(x,Some(i,ltree_to_atree b),ltree_to_atree a,ltree_to_atree c)
  | LeML(x,xl,a,c) -> LeM(x,xl,ltree_to_atree a,ltree_to_atree c)
  | BiL(x,m,vll,c) ->
      let vlla = List.map
	  (fun (xl,o) ->
	    match o with
	    | None -> (xl,None)
	    | Some(i,b) -> (xl,Some(i,ltree_to_atree b)))
	  vll
      in
      Bi(x,vlla,ltree_to_atree c)
  | PreoL(x,a) -> Preo(x,ltree_to_atree a)
  | PostoL(x,a) -> Posto(x,ltree_to_atree a)
  | InfoL(x,a,b) -> Info(x,ltree_to_atree a,ltree_to_atree b)
  | ImplopL(a,b) -> Implop(ltree_to_atree a,ltree_to_atree b)
  | SepL(x,i,a,b) -> Sep(x,i,ltree_to_atree a,ltree_to_atree b)
  | RepL(x,i,a,b) -> Rep(x,i,ltree_to_atree a,ltree_to_atree b)
  | SepRepL(x,i,a,b,c) -> SepRep(x,i,ltree_to_atree a,ltree_to_atree b,ltree_to_atree c)
  | SetEnumL(al) -> SetEnum(List.map ltree_to_atree al)
  | MTupleL(a,bl) -> MTuple(ltree_to_atree a,List.map ltree_to_atree bl)
  | ParenL(a,[]) -> ltree_to_atree a
  | ParenL(a,b::cl) -> Tuple(ltree_to_atree a,ltree_to_atree b,List.map ltree_to_atree cl)
  | IfThenElseL(a,b,c) -> IfThenElse(ltree_to_atree a,ltree_to_atree b,ltree_to_atree c)

type picase = Postfix | InfixNone | InfixLeft | InfixRight

type docitem =
  | Author of string * string list
  | Title of string
  | Salt of string
  | Treasure of string
  | ShowProofTerms of bool
  | Section of string
  | End of string
  | VarDecl of string list * asckind * ltree
  | LetDecl of string * (asckind * ltree) option * ltree
  | HypDecl of string * ltree
  | PostInfixDecl of string * ltree * int * picase
  | PrefixDecl of string * ltree * int
  | BinderDecl of bool * bool * string * ltree * ltree option
  | NotationDecl of string * string list
  | UnicodeDecl of string * string list
  | SubscriptDecl of string
  | SuperscriptDecl of string
  | RequireDecl of string
  | ParamDecl of string * ltree
  | DefDecl of string * ltree option * ltree
  | ParamHash of string * string
  | AxDecl of string * ltree
  | ThmDecl of string * string * ltree

type pftacitem =
  | PfStruct of int
  | Exact of ltree
  | LetTac of string list * ltree option
  | AssumeTac of string list * ltree option
  | SetTac of string * ltree option * ltree
  | ApplyTac of ltree
  | ClaimTac of string * ltree
  | ProveTac of ltree * ltree list
  | CasesTac of ltree * (string * ltree) list list
  | WitnessTac of ltree
  | RewriteTac of bool * ltree * int list
  | Qed
  | Admitted
  | Admit

type docorpftacitem =
  | DocItem : docitem -> docorpftacitem
  | PfTacItem : pftacitem -> docorpftacitem

type doc = (string * string) list * docorpftacitem list

(*** DocPromise(hashofdocyettobepublished,[...listofhashesofpropositionsprovenindocyettobepublished...]) ***)
type formalmetablockitem =
  | Doc of doc
  | DocPromise of string * string list

type formalmetablock = formalmetablockitem list

let rec tp_to_str m =
  match m with
  | TpVar(i) -> "?" ^ string_of_int i
  | Prop -> "prop"
  | Set -> "set"
  | Ar(m1,m2) -> "(" ^ tp_to_str m1 ^ " -> " ^ tp_to_str m2 ^ ")"

let rec tm_to_str m =
  match m with
  | DB(i) -> "_" ^ string_of_int i
  | TmH(h) -> "#" ^ h
  | Prim(i) -> "\"" ^ string_of_int i ^ "\""
  | TpAp(m1,m2) -> "(" ^ tm_to_str m1 ^ " " ^ tp_to_str m2 ^ ")"
  | Ap(m1,m2) -> "(" ^ tm_to_str m1 ^ " " ^ tm_to_str m2 ^ ")"
  | Lam(m1,m2) -> "(fun _:" ^ tp_to_str m1 ^ " => " ^ tm_to_str m2 ^ ")"
  | Imp(m1,m2) -> "(" ^ tm_to_str m1 ^ " -> " ^ tm_to_str m2 ^ ")"
  | All(m1,m2) -> "(forall _:" ^ tp_to_str m1 ^ ", " ^ tm_to_str m2 ^ ")"

let rec pf_to_str m =
  match m with
  | Hyp(i) -> "__" ^ string_of_int i
  | Known(h) -> "##" ^ h
  | PTpAp(m1,m2) -> "(" ^ pf_to_str m1 ^ " " ^ tp_to_str m2 ^ ")"
  | PTmAp(m1,m2) -> "(" ^ pf_to_str m1 ^ " " ^ tm_to_str m2 ^ ")"
  | PPfAp(m1,m2) -> "(" ^ pf_to_str m1 ^ " " ^ pf_to_str m2 ^ ")"
  | PLam(m1,m2) -> "(fun _:" ^ tm_to_str m1 ^ " => " ^ pf_to_str m2 ^ ")"
  | TLam(m1,m2) -> "(fun _:" ^ tp_to_str m1 ^ " => " ^ pf_to_str m2 ^ ")"

(*** serialization code ***)
let hex_char h =
  List.nth ['0';'1';'2';'3';'4';'5';'6';'7';'8';'9';'A';'B';'C';'D';'E';'F'] h

let output_byte_sb c by =
  Buffer.add_char c (char_of_int by)

let flush_bits_sb (c,byio) =
  match byio with
  | Some (by,i) ->
      output_byte_sb c by
  | None -> ()

let output_bit_sb b (c,byio) =
  match byio with
  | Some (by,i) -> 
      if (i >= 7) then
	begin
	  output_byte_sb c ((b lsl 7) lor by);
	  (c,None)
	end
      else
	(c,Some (((b lsl i) lor by),i+1))
  | None ->
      (c,Some(b,1))

let output_bits_byte_sb bs i =
  let bsr = ref bs in
  let ir = ref i in
  for j = 0 to 7 do
    bsr := output_bit_sb (!ir mod 2) (!bsr);
    ir := !ir lsr 1;
  done;
  !bsr

let output_bits_int16_sb bs i =
  let bsr = ref bs in
  let ir = ref i in
  for j = 0 to 15 do
    bsr := output_bit_sb (!ir mod 2) (!bsr);
    ir := !ir lsr 1;
  done;
  !bsr

let output_bits_int32_sb bs i =
  let bsr = ref bs in
  let ir = ref i in
  for j = 0 to 31 do
    bsr := output_bit_sb (Int32.to_int (Int32.logand !ir 1l)) (!bsr);
    ir := Int32.shift_right_logical !ir 1;
  done;
  !bsr

let output_bits_int64_sb bs i =
  let bsr = ref bs in
  let ir = ref i in
  for j = 0 to 63 do
    bsr := output_bit_sb (Int64.to_int (Int64.logand !ir 1L)) (!bsr);
    ir := Int64.shift_right_logical !ir 1;
  done;
  !bsr

(*** assume big_int's are 256-bit ***)
let output_bits_big_int_sb bs i =
  let bsr = ref bs in
  let ir = ref i in
  for j = 0 to 255 do
     let b = if (eq_big_int (and_big_int zero_big_int unit_big_int) zero_big_int) then 0 else 1 in
     bsr := output_bit_sb b (!bsr);
     ir := shift_right_towards_zero_big_int !ir 1
  done;
  !bsr

let output_bits_string_sb bs s =
  let bsr = ref bs in
  for j = 0 to (String.length s) - 1 do
    bsr := output_bits_byte_sb !bsr (int_of_char (String.get s j));
  done;
  output_bits_byte_sb (!bsr) 0

let output_byte_nat c by =
  match (!c) with
  | (n,i) when by = 0 -> c := (n,i+8)
  | (n,i) when i < 32 -> c := (Int64.logor n (Int64.shift_left (Int64.of_int by) i),i+8)
  | _ -> raise Exit (*** Refute if it's >= 2^32 ***)

let flush_bits_nat (c,byio) =
  match byio with
  | Some (by,i) ->
      output_byte_nat c by
  | None -> ()

let output_bit_nat b (c,byio) =
  match byio with
  | Some (by,i) -> 
      if (i >= 7) then
	begin
	  output_byte_nat c ((b lsl 7) lor by);
	  (c,None)
	end
      else
	(c,Some (((b lsl i) lor by),i+1))
  | None ->
      (c,Some(b,1))

let destruct_bitstream_s (c,n,i,j) =
  if (j >= 0 && i >= 0 && i < n) then
    let by = int_of_char (String.get c i) in
    let b = (by lsr j) mod 2 in
    if (j < 7) then
      (b,(c,n,i,j+1))
    else
      (b,(c,n,i+1,0))
  else
    raise Not_found

let input_bits_s_byte bs =
  let bsr = ref bs in
  let ir = ref 0 in
  for j = 0 to 7 do
    let (b,bs) = destruct_bitstream_s (!bsr) in
    bsr := bs;
    ir := (b lsl j) lor !ir;
  done;
  (!ir,!bsr)

let input_bits_s_int16 bs =
  let bsr = ref bs in
  let ir = ref 0 in
  for j = 0 to 15 do
    let (b,bs) = destruct_bitstream_s (!bsr) in
    bsr := bs;
    ir := (b lsl j) lor !ir;
  done;
  (!ir,!bsr)

let input_bits_s_int32 bs =
  let bsr = ref bs in
  let ir = ref 0l in
  for j = 0 to 31 do
    let (b,bs) = destruct_bitstream_s (!bsr) in
    bsr := bs;
    ir := Int32.logor (Int32.shift_left (Int32.of_int b) j) !ir;
  done;
  (!ir,!bsr)

let input_bits_s_int64 bs =
  let bsr = ref bs in
  let ir = ref 0L in
  for j = 0 to 63 do
    let (b,bs) = destruct_bitstream_s (!bsr) in
    bsr := bs;
    ir := Int64.logor (Int64.shift_left (Int64.of_int b) j) !ir;
  done;
  (!ir,!bsr)

(*** assume big_int's are 256-bit ***)
let input_bits_s_big_int bs =
  let bsr = ref bs in
  let ir = ref zero_big_int in
  for j = 0 to 255 do
    let (b,bs) = destruct_bitstream_s (!bsr) in
    bsr := bs;
    ir := or_big_int (shift_left_big_int (big_int_of_int b) j) !ir
  done;
  (!ir,!bsr)

let input_bits_s_string bs =
  let bsr = ref bs in
  let s = Buffer.create 20 in
  let cont = ref true in
  while !cont do
    let (b,bs) = input_bits_s_byte (!bsr) in
    bsr := bs;
    if (b = 0) then
      cont := false
    else
      Buffer.add_char s (char_of_int b)
  done;
  (Buffer.contents s,!bsr)

let destruct_bitstream_s (c,n,i,j) =
  if (j >= 0 && i >= 0 && i < n) then
    let by = int_of_char (String.get c i) in
    let b = (by lsr j) mod 2 in
    if (j < 7) then
      (b,(c,n,i,j+1))
    else
      (b,(c,n,i+1,0))
  else
    raise Not_found

let rec output_tp_sb_rec bs m =
  match m with
  | TpVar(0) -> (*** 00 00 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      bs
  | TpVar(1) -> (*** 00 01 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 1 bs in
      bs
  | TpVar(2) -> (*** 00 10 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 0 bs in
      bs
  | TpVar(3) -> (*** 00 11 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 1 bs in
      bs
  | TpVar(m0) -> raise (Failure("Invalid type variable"))
  | Prop -> (*** 01 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 1 bs in
      bs
  | Set -> (*** 10 ***)
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 0 bs in
      bs
  | Ar(m0,m1) -> (*** 11 ***)
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_tp_sb_rec bs m0 in
      let bs = output_tp_sb_rec bs m1 in
      bs

let output_tp_sb c m = flush_bits_sb (output_tp_sb_rec (c,None) m)

let tp_to_ser m =
  let c = Buffer.create 1000 in
  output_tp_sb c m;
  Buffer.contents c

(*** i assumed to be 0,1,2 or 3; at most 3 type variables. ***)
let ptp_to_ser (i,m) =
     if (i < 0 || i > 3) then raise (Failure "Polymorphic types must have at most 3 type variables");
     let c = Buffer.create 1000 in
     let bs1 = output_bit_sb (i mod 2) (c,None) in
     let bs2 = output_bit_sb (if i > 1 then 1 else 0) bs1 in
     flush_bits_sb (output_tp_sb_rec bs2 m);
     Buffer.contents c

let rec input_tp_s_rec bs =
  let (b,bs) = destruct_bitstream_s bs in
  if b = 0 then
    let (b,bs) = destruct_bitstream_s bs in
    if b = 0 then
      let (b,bs) = destruct_bitstream_s bs in
      if b = 0 then
	let (b,bs) = destruct_bitstream_s bs in
	if b = 0 then
	  (TpVar(0),bs)
	else
	  (TpVar(1),bs)
      else
	let (b,bs) = destruct_bitstream_s bs in
	if b = 0 then
	  (TpVar(2),bs)
	else
	  (TpVar(3),bs)
    else
      (Prop,bs)
  else
    let (b,bs) = destruct_bitstream_s bs in
    if b = 0 then
      (Set,bs)
    else
      let (m0,bs) = input_tp_s_rec bs in
      let (m1,bs) = input_tp_s_rec bs in
      (Ar(m0,m1),bs)

let input_tp_s c = let (m,_) = input_tp_s_rec (c,String.length c,0,0) in m

let ser_to_tp mc =
  input_tp_s mc

let ser_to_ptp c =
  let (b0,bs1) = destruct_bitstream_s (c,String.length c,0,0) in
  let (b1,bs2) = destruct_bitstream_s bs1 in
  let (m,_) = input_tp_s_rec bs2 in (b1 * 2 + b0,m)

let rec output_tm_sb_rec bs m =
  match m with
  | DB(m0) -> (*** 000 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      if ((m0 < 0) || (m0 > 65535)) then (Printf.printf "De Bruijn index %d is not short.n" m0; raise (Failure "output_tm_sb - de Bruijn out of bounds"));
      let bs = output_bits_int16_sb bs m0 in
      bs
  | TmH(m0) -> (*** 001 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_bits_string_sb bs m0 in
      bs
  | Prim(m0) -> (*** 010 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 0 bs in
      if ((m0 < 0) || (m0 > 65535)) then (Printf.printf "Prim num %d is not short.n" m0; raise (Failure "output_tm_sb - de Bruijn out of bounds"));
      let bs = output_bits_int16_sb bs m0 in
      bs
  | TpAp(m0,m1) -> (*** 011 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_tm_sb_rec bs m0 in
      let bs = output_tp_sb_rec bs m1 in
      bs
  | Ap(m0,m1) -> (*** 100 ***)
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_tm_sb_rec bs m0 in
      let bs = output_tm_sb_rec bs m1 in
      bs
  | Lam(m0,m1) -> (*** 101 ***)
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_tp_sb_rec bs m0 in
      let bs = output_tm_sb_rec bs m1 in
      bs
  | Imp(m0,m1) -> (*** 110 ***)
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_tm_sb_rec bs m0 in
      let bs = output_tm_sb_rec bs m1 in
      bs
  | All(m0,m1) -> (*** 111 ***)
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_tp_sb_rec bs m0 in
      let bs = output_tm_sb_rec bs m1 in
      bs

let output_tm_sb c m = flush_bits_sb (output_tm_sb_rec (c,None) m)

let tm_to_ser m =
  let c = Buffer.create 1000 in
  output_tm_sb c m;
  Buffer.contents c

let ptm_to_ser (i,m) =
     if (i < 0 || i > 3) then raise (Failure "Polymorphic terms must have at most 3 type variables");
     let c = Buffer.create 1000 in
     let bs1 = output_bit_sb (i mod 2) (c,None) in
     let bs2 = output_bit_sb (if i > 1 then 1 else 0) bs1 in
     flush_bits_sb (output_tm_sb_rec bs2 m);
     Buffer.contents c

let rec input_tm_s_rec bs =
  let (b,bs) = destruct_bitstream_s bs in
  if b = 0 then
    let (b,bs) = destruct_bitstream_s bs in
    if b = 0 then
      let (b,bs) = destruct_bitstream_s bs in
      if b = 0 then
        let (m0,bs) = input_bits_s_int16 bs in
        (DB(m0),bs)
      else
        let (m0,bs) = input_bits_s_string bs in
        (TmH(m0),bs)
    else
      let (b,bs) = destruct_bitstream_s bs in
      if b = 0 then
        let (m0,bs) = input_bits_s_int16 bs in
        (Prim(m0),bs)
      else
        let (m0,bs) = input_tm_s_rec bs in
        let (m1,bs) = input_tp_s_rec bs in
        (TpAp(m0,m1),bs)
  else
    let (b,bs) = destruct_bitstream_s bs in
    if b = 0 then
      let (b,bs) = destruct_bitstream_s bs in
      if b = 0 then
        let (m0,bs) = input_tm_s_rec bs in
        let (m1,bs) = input_tm_s_rec bs in
        (Ap(m0,m1),bs)
      else
        let (m0,bs) = input_tp_s_rec bs in
        let (m1,bs) = input_tm_s_rec bs in
        (Lam(m0,m1),bs)
    else
      let (b,bs) = destruct_bitstream_s bs in
      if b = 0 then
        let (m0,bs) = input_tm_s_rec bs in
        let (m1,bs) = input_tm_s_rec bs in
        (Imp(m0,m1),bs)
      else
        let (m0,bs) = input_tp_s_rec bs in
        let (m1,bs) = input_tm_s_rec bs in
        (All(m0,m1),bs)

let input_tm_s c = let (m,_) = input_tm_s_rec (c,String.length c,0,0) in m

let ser_to_tm mc =
  input_tm_s mc

let ser_to_ptm c =
  let (b0,bs1) = destruct_bitstream_s (c,String.length c,0,0) in
  let (b1,bs2) = destruct_bitstream_s bs1 in
  let (m,_) = input_tm_s_rec bs2 in (b1 * 2 + b0,m)

let rec output_pf_sb_rec bs m =
  match m with
  | Hyp(m0) -> (*** 000 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      if ((m0 < 0) || (m0 > 65535)) then (Printf.printf "De Bruijn index %d is not short.n" m0; raise (Failure "output_pf_sb - de Bruijn out of bounds"));
      let bs = output_bits_int16_sb bs m0 in
      bs
  | Known(m0) -> (*** 001 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_bits_string_sb bs m0 in
      bs
  | PTpAp(m0,m1) -> (*** 010 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_pf_sb_rec bs m0 in
      let bs = output_tp_sb_rec bs m1 in
      bs
  | PTmAp(m0,m1) -> (*** 011 ***)
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_pf_sb_rec bs m0 in
      let bs = output_tm_sb_rec bs m1 in
      bs
  | PPfAp(m0,m1) -> (*** 100 ***)
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_pf_sb_rec bs m0 in
      let bs = output_pf_sb_rec bs m1 in
      bs
  | TLam(m0,m1) -> (*** 101 ***)
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_tp_sb_rec bs m0 in
      let bs = output_pf_sb_rec bs m1 in
      bs
  | PLam(m0,m1) -> (*** 110 ***)
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 1 bs in
      let bs = output_bit_sb 0 bs in
      let bs = output_tm_sb_rec bs m0 in
      let bs = output_pf_sb_rec bs m1 in
      bs

let output_pf_sb c m = flush_bits_sb (output_pf_sb_rec (c,None) m)

let pf_to_ser m =
  let c = Buffer.create 1000 in
  output_pf_sb c m;
  Buffer.contents c

let ppf_to_ser (i,m) =
     if (i < 0 || i > 3) then raise (Failure "Polymorphic proofs must have at most 3 type variables");
     let c = Buffer.create 1000 in
     let bs1 = output_bit_sb (i mod 2) (c,None) in
     let bs2 = output_bit_sb (if i > 1 then 1 else 0) bs1 in
     flush_bits_sb (output_pf_sb_rec bs2 m);
     Buffer.contents c

(***
let rec input_pf_rec bs =
  let (b,bs) = destruct_bitstream bs in
  if b = 0 then
    let (b,bs) = destruct_bitstream bs in
    if b = 0 then
      let (b,bs) = destruct_bitstream bs in
      if b = 0 then
        let (m0,bs) = input_bits_int16 bs in
        (Hyp(m0),bs)
      else
        let (m0,bs) = input_bits_string bs in
        (Known(m0),bs)
    else
      let (b,bs) = destruct_bitstream bs in
      if b = 0 then
        let (m0,bs) = input_pf_rec bs in
        let (m1,bs) = input_tp_rec bs in
        (PTpAp(m0,m1),bs)
      else
        let (m0,bs) = input_pf_rec bs in
        let (m1,bs) = input_tm_rec bs in
        (PTmAp(m0,m1),bs)
  else
    let (b,bs) = destruct_bitstream bs in
    if b = 0 then
      let (b,bs) = destruct_bitstream bs in
      if b = 0 then
        let (m0,bs) = input_pf_rec bs in
        let (m1,bs) = input_pf_rec bs in
        (PPfAp(m0,m1),bs)
      else
        let (m0,bs) = input_tp_rec bs in
        let (m1,bs) = input_pf_rec bs in
        (TLam(m0,m1),bs)
    else
      let (b,bs) = destruct_bitstream bs in
      if b = 0 then
        let (m0,bs) = input_tm_rec bs in
        let (m1,bs) = input_pf_rec bs in
        (PLam(m0,m1),bs)
      else
	raise (Failure("Not a serialization of a pf"))

let input_pf c = let (m,_) = input_pf_rec (c,None) in m

let rec input_pf_and_ser_rec bs buf =
  let (b,bs) = destruct_bitstream_w_buf bs buf in
  if b = 0 then
    let (b,bs) = destruct_bitstream_w_buf bs buf in
    if b = 0 then
      let (b,bs) = destruct_bitstream_w_buf bs buf in
      if b = 0 then
        let (m0,bs) = input_bits_int16_w_buf bs buf in
        (Hyp(m0),bs)
      else
        let (m0,bs) = input_bits_string_w_buf bs buf in
        (Known(m0),bs)
    else
      let (b,bs) = destruct_bitstream_w_buf bs buf in
      if b = 0 then
        let (m0,bs) = input_pf_and_ser_rec bs buf in
        let (m1,bs) = input_tp_and_ser_rec bs buf in
        (PTpAp(m0,m1),bs)
      else
        let (m0,bs) = input_pf_and_ser_rec bs buf in
        let (m1,bs) = input_tm_and_ser_rec bs buf in
        (PTmAp(m0,m1),bs)
  else
    let (b,bs) = destruct_bitstream_w_buf bs buf in
    if b = 0 then
      let (b,bs) = destruct_bitstream_w_buf bs buf in
      if b = 0 then
        let (m0,bs) = input_pf_and_ser_rec bs buf in
        let (m1,bs) = input_pf_and_ser_rec bs buf in
        (PPfAp(m0,m1),bs)
      else
        let (m0,bs) = input_tp_and_ser_rec bs buf in
        let (m1,bs) = input_pf_and_ser_rec bs buf in
        (TLam(m0,m1),bs)
    else
      let (b,bs) = destruct_bitstream_w_buf bs buf in
      if b = 0 then
        let (m0,bs) = input_tm_and_ser_rec bs buf in
        let (m1,bs) = input_pf_and_ser_rec bs buf in
        (PLam(m0,m1),bs)
      else
	raise (Failure("Not a serialization of a pf"))

let input_pf_and_ser c =
  let buf = Buffer.create 1000 in
  let (m,_) = input_pf_and_ser_rec (c,None) buf in
  (m,Buffer.contents buf)
***)

let rec input_pf_s_rec bs =
  let (b,bs) = destruct_bitstream_s bs in
  if b = 0 then
    let (b,bs) = destruct_bitstream_s bs in
    if b = 0 then
      let (b,bs) = destruct_bitstream_s bs in
      if b = 0 then
        let (m0,bs) = input_bits_s_int16 bs in
        (Hyp(m0),bs)
      else
        let (m0,bs) = input_bits_s_string bs in
        (Known(m0),bs)
    else
      let (b,bs) = destruct_bitstream_s bs in
      if b = 0 then
        let (m0,bs) = input_pf_s_rec bs in
        let (m1,bs) = input_tp_s_rec bs in
        (PTpAp(m0,m1),bs)
      else
        let (m0,bs) = input_pf_s_rec bs in
        let (m1,bs) = input_tm_s_rec bs in
        (PTmAp(m0,m1),bs)
  else
    let (b,bs) = destruct_bitstream_s bs in
    if b = 0 then
      let (b,bs) = destruct_bitstream_s bs in
      if b = 0 then
        let (m0,bs) = input_pf_s_rec bs in
        let (m1,bs) = input_pf_s_rec bs in
        (PPfAp(m0,m1),bs)
      else
        let (m0,bs) = input_tp_s_rec bs in
        let (m1,bs) = input_pf_s_rec bs in
        (TLam(m0,m1),bs)
    else
      let (b,bs) = destruct_bitstream_s bs in
      if b = 0 then
        let (m0,bs) = input_tm_s_rec bs in
        let (m1,bs) = input_pf_s_rec bs in
        (PLam(m0,m1),bs)
      else
	raise (Failure("Not a serialization of a pf"))

let input_pf_s c = let (m,_) = input_pf_s_rec (c,String.length c,0,0) in m

let ser_to_pf mc =
  input_pf_s mc

let ser_to_ppf c =
  let (b0,bs1) = destruct_bitstream_s (c,String.length c,0,0) in
  let (b1,bs2) = destruct_bitstream_s bs1 in
  let (m,_) = input_pf_s_rec bs2 in (b1 * 2 + b0,m)

(*** position function ***)
let rec position_rec l x i =
match l with
| (y::r) when x = y -> i
| (y::r) -> position_rec r x (i+1)
| [] -> raise Not_found

let position l x = position_rec l x 0

let tplookup ctxtp x =
  TpVar (position ctxtp x)

exception NegDB

let rec tmshift i j m =
  match m with
  | DB(k) when k < i -> DB(k)
  | DB(k) ->
      let l = k + j in
      if l >= i then DB(l) else raise NegDB
  | TpAp(m1,a) -> TpAp(tmshift i j m1,a)
  | Ap(m1,m2) -> Ap(tmshift i j m1,tmshift i j m2)
  | Lam(a1,m1) -> Lam(a1,tmshift (i+1) j m1)
  | Imp(m1,m2) -> Imp(tmshift i j m1,tmshift i j m2)
  | All(a1,m1) -> All(a1,tmshift (i+1) j m1)
  | _ -> m

let rec tmtplookup_rec ctxtm x i =
  match ctxtm with
  | ((y,(a,None))::_) when y = x -> (DB i,a)
  | ((y,(a,Some(m)))::_) when y = x && i = 0 -> (m,a)
  | ((y,(a,Some(m)))::_) when y = x -> (tmshift 0 i m,a)
  | ((_,(_,None))::r) -> tmtplookup_rec r x (i+1) (*** Shift for variables ***)
  | ((_,(_,Some(_)))::r) -> tmtplookup_rec r x i (*** Do not shift for lets ***)
  | [] -> raise Not_found

let tmtplookup ctxtm x =
  tmtplookup_rec ctxtm x 0

let tmlookup ctxtm x =
  let (n,_) = tmtplookup_rec ctxtm x 0 in n

let rec pfshift i j d =
  match d with
  | Hyp(k) when k < i -> Hyp(k)
  | Hyp(k) -> let l = k+j in if l >= i then Hyp(k+j) else raise NegDB
  | PTpAp(d1,a) -> PTpAp(pfshift i j d1,a)
  | PTmAp(d1,m2) -> PTmAp(pfshift i j d1,m2)
  | PPfAp(d1,d2) -> PPfAp(pfshift i j d1,pfshift i j d2)
  | PLam(m1,d1) -> PLam(m1,pfshift (i+1) j d1)
  | TLam(a1,d1) -> TLam(a1,pfshift i j d1)
  | _ -> d

let rec pftmshift i j d =
  match d with
  | Hyp(k) -> Hyp(k)
  | PTpAp(d1,a) -> PTpAp(pftmshift i j d1,a)
  | PTmAp(d1,m2) -> PTmAp(pftmshift i j d1,tmshift i j m2)
  | PPfAp(d1,d2) -> PPfAp(pftmshift i j d1,pftmshift i j d2)
  | PLam(m1,d1) -> PLam(tmshift i j m1,pftmshift i j d1)
  | TLam(a1,d1) -> TLam(a1,pftmshift (i+1) j d1)
  | _ -> d

let rec pflookup_rec ctxpf x i =
  match ctxpf with
  | ((y,m)::_) when y = x -> Hyp i
  | (_::r) -> pflookup_rec r x (i+1)
  | [] -> raise Not_found

let pflookup ctxpf x = pflookup_rec ctxpf x 0

let rec pfproplookup_rec ctxpf x i =
  match ctxpf with
  | ((y,m)::_) when y = x -> (Hyp i,m)
  | (_::r) -> pfproplookup_rec r x (i+1)
  | [] -> raise Not_found

let pfproplookup ctxpf x = pfproplookup_rec ctxpf x 0

let rec tp_closed_p a =
  match a with
  | Ar(a1,a2) -> tp_closed_p a1 && tp_closed_p a2
  | TpVar _ -> false
  | _ -> true

let rec tpsubst a cl =
  match a with
  | TpVar i -> List.nth cl i
  | Set -> Set
  | Prop -> Prop
  | Ar(a,b) -> Ar(tpsubst a cl,tpsubst b cl)

let rec tmtpsubst m cl =
  match m with
  | TpAp(m1,a1) -> TpAp(tmtpsubst m1 cl,tpsubst a1 cl)
  | Ap(m1,m2) -> Ap(tmtpsubst m1 cl,tmtpsubst m2 cl)
  | Lam(a1,m1) -> Lam(tpsubst a1 cl,tmtpsubst m1 cl)
  | Imp(m1,m2) -> Imp(tmtpsubst m1 cl,tmtpsubst m2 cl)
  | All(a1,m1) -> All(tpsubst a1 cl,tmtpsubst m1 cl)
  | _ -> m

let rec pftpsubst d cl =
  match d with
  | PTpAp(d1,a1) -> PTpAp(pftpsubst d1 cl,tpsubst a1 cl)
  | PTmAp(d1,m1) -> PTmAp(pftpsubst d1 cl,tmtpsubst m1 cl)
  | PPfAp(d1,d2) -> PPfAp(pftpsubst d1 cl,pftpsubst d2 cl)
  | PLam(m1,d1) -> PLam(tmtpsubst m1 cl,pftpsubst d1 cl)
  | TLam(a1,d1) -> TLam(tpsubst a1 cl,pftpsubst d1 cl)
  | _ -> d

let rec tmsubst m j n =
  match m with
  | DB(i) when i = j && j = 0 -> n
  | DB(i) when i = j -> tmshift 0 j n
  | DB(i) when i > j -> DB(i-1)
  | TpAp(m1,a) -> TpAp(tmsubst m1 j n,a) (*** This could be omitted since it should always be TmH applied to <= 3 type variables, and so will contain no de Bruijns. ***)
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
  | TpAp(m1,a) -> false (*** invariant: m1 is closed ***)
  | _ -> false

let beta_count = ref (Some 1000000)

let beta_count_check () =
  match !beta_count with
  | None -> ()
  | Some b when b > 0 ->
      beta_count := Some (b-1)
  | _ ->
      raise (Failure("Resource Bound Reached -- Too many beta reductions"))

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
  | Imp(m1,m2) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      let (m2r,m2b) = tm_beta_eta_norm_1 m2 in
      (Imp(m1r,m2r),m1b && m2b)
  | All(a,m1) ->
      let (m1r,m1b) = tm_beta_eta_norm_1 m1 in
      (All(a,m1r),m1b)
  | TpAp(m1,a1) -> (m,true) (*** invariant: polydefs are gone, so m1 is either Prim(0) or TmH(h) where h is the id of Prim(0). No reduction here. ***)
  | _ -> (m,true)

let rec tm_beta_eta_norm m =
  let (mr,mb) = tm_beta_eta_norm_1 m in
  if mb then
    mr
  else
    tm_beta_eta_norm mr

let tpofprim i =
  match i with
  | 0 -> Ar(Ar(TpVar 0,Prop),TpVar 0)
  | 1 -> Ar(Set,Ar(Set,Prop))
  | 2 -> Set
  | 3 -> Ar(Set,Set)
  | 4 -> Ar(Set,Set)
  | 5 -> Ar(Set,Ar(Ar(Set,Set),Set))
  | 6 -> Ar(Set,Set)
  | _ -> raise Not_found

let rec extr_tpoftm sgtmof cxtm m =
  match m with
  | DB i -> List.nth cxtm i
  | TpAp(Prim 0,a) -> Ar(Ar(a,Prop),a)
  | TpAp(TpAp(TpAp(TmH h,a),b),c) ->
      begin
	match Hashtbl.find sgtmof h with
	| (3,d) -> tpsubst d [a;b;c]
	| (i,_) -> raise (Failure(h ^ " applied to 3 types, but expected to be applied to " ^ (string_of_int i)))
      end
  | TpAp(TpAp(TmH h,a),b) ->
      begin
	match Hashtbl.find sgtmof h with
	| (2,d) -> tpsubst d [a;b]
	| (i,_) -> raise (Failure(h ^ " applied to 2 types, but expected to be applied to " ^ (string_of_int i)))
      end
  | TpAp(TmH h,a) ->
      begin
	match Hashtbl.find sgtmof h with
	| (1,d) -> tpsubst d [a]
	| (i,_) -> raise (Failure(h ^ " applied to 1 type, but expected to be applied to " ^ (string_of_int i)))
      end
  | TmH h ->
      begin
	match Hashtbl.find sgtmof h with
	| (0,d) -> d
	| (i,_) -> raise (Failure(h ^ " applied to no types, but expected to be applied to " ^ (string_of_int i)))
      end
  | Prim 0 -> raise (Failure("The polymorphic primitive Eps applied to no types, but expected to be applied to 1"))
  | Prim i -> tpofprim i
  | TpAp(_,_) -> raise (Failure("Nonprefix polymorphism in term"))
  | Ap(m1,m2) ->
      begin
	match extr_tpoftm sgtmof cxtm m1 with
	| Ar(a,b) -> (check_tpoftm sgtmof cxtm m2 a; b)
	| _ -> raise (Failure("Type Error: Nonfunction applied to an argument."))
      end
  | Lam(a,m) -> Ar(a,extr_tpoftm sgtmof (a::cxtm) m)
  | Imp(m1,m2) -> (check_tpoftm sgtmof cxtm m1 Prop; check_tpoftm sgtmof cxtm m2 Prop; Prop)
  | All(a,m) -> (check_tpoftm sgtmof (a::cxtm) m Prop; Prop)
and check_tpoftm sgtmof cxtm m a =
  let b = extr_tpoftm sgtmof cxtm m in
  if a = b then
    ()
  else
    raise (Failure("Type Error: Found " ^ tp_to_str b ^ "\nbut expected " ^ tp_to_str a))

let rec tm_head_args_r m args =
  match m with
  | Ap(m1,m2) -> tm_head_args_r m1 (m2::args)
  | _ -> (m,args)

let tm_head_args m =
  tm_head_args_r m []

(*** assume m is beta eta normal and not a Lam, and args are all beta eta normal ***)
let rec tm_app_beta_eta_norm2 m args =
  match args with
  | (n::argr) -> tm_app_beta_eta_norm2 (Ap(m,n)) argr
  | _ -> m

(*** assume m is beta eta normal already and args are all beta eta normal ***)
let rec tm_app_beta_eta_norm m args =
  match (m,args) with
  | (Lam(_,m1),n::argr) ->
      tm_app_beta_eta_norm (tm_beta_eta_norm (tmsubst m1 0 n)) argr
  | _ ->
      tm_app_beta_eta_norm2 m args

let defp sdel h =
  match h with
  | TmH(c) -> Hashtbl.mem sdel c
  | TpAp(TmH(c),_) -> Hashtbl.mem sdel c
  | TpAp(TpAp(TmH(c),_),_) -> Hashtbl.mem sdel c
  | TpAp(TpAp(TpAp(TmH(c),_),_),_) -> Hashtbl.mem sdel c
  | _ -> false

let deltap dl h =
  match h with
  | TmH(c) -> List.mem c dl
  | TpAp(TmH(c),_) -> true
  | TpAp(TpAp(TmH(c),_),_) -> true
  | TpAp(TpAp(TpAp(TmH(c),_),_),_) -> true
  | _ -> false

(*** assume all defs are beta eta normal ***)
let delta_exp sdel h args =
  try
    match h with
    | TmH(c) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 0 then
	    tm_app_beta_eta_norm m args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to none."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to none."))
	end
    | TpAp(TmH(c),a1) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 1 then
	    tm_app_beta_eta_norm (tmtpsubst m [a1]) args
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 1."))
	end
    | TpAp(TpAp(TmH(c),a1),a2) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 2 then
	    tm_app_beta_eta_norm (tmtpsubst m [a1;a2]) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to 2."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 2."))
	end
    | TpAp(TpAp(TpAp(TmH(c),a1),a2),a3) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 3 then
	    tm_app_beta_eta_norm (tmtpsubst m [a1;a2;a3]) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to 3."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 3."))
	end
    | _ -> raise Not_found
  with Not_found ->
    (*** By checking with defp above before delta_exp is called, I should know that this doesn't happen. **)
    raise (Failure("delta_exp called with an inappropriate head. Bug"))

let delta_cons h dl =
  match h with
  | TmH(c) -> (c::dl)
  | _ -> dl

let rec headnorm1 m sdel dl =
  match m with
  | Lam(_,_) -> (m,dl)
  | Imp(_,_) -> (m,dl)
  | All(_,_) -> (m,dl)
  | _ ->
      let (mh,margs) = tm_head_args m in
      if defp sdel mh then
	headnorm1 (delta_exp sdel mh margs) sdel (delta_cons mh dl)
      else
	(m,dl)

let headnorm m sdel dl = headnorm1 (tm_beta_eta_norm m) sdel dl

(*** conv2 assumes m and n are beta-eta normal ***)
let rec conv2 m n sdel dl =
  match (m,n) with
  | (Lam(a1,m1),Lam(b1,n1)) ->
      if a1 = b1 then
	conv2 m1 n1 sdel dl
      else
	None
  | (All(a1,m1),All(b1,n1)) ->
      if a1 = b1 then
	conv2 m1 n1 sdel dl
      else
	None
  | (Imp(m1,m2),Imp(n1,n2)) ->
      convl [m1;m2] [n1;n2] sdel dl
  | (Lam(_,_),All(_,_)) -> None
  | (Lam(_,_),Imp(_,_)) -> None
  | (All(_,_),Lam(_,_)) -> None
  | (All(_,_),Imp(_,_)) -> None
  | (Imp(_,_),All(_,_)) -> None
  | (Imp(_,_),Lam(_,_)) -> None
  | (_,Lam(_,_)) ->
      let (mh,margs) = tm_head_args m in
      if defp sdel mh then
	conv2 (delta_exp sdel mh margs) n sdel (delta_cons mh dl)
      else
	None
  | (_,All(_,_)) ->
      let (mh,margs) = tm_head_args m in
      if defp sdel mh then
	conv2 (delta_exp sdel mh margs) n sdel (delta_cons mh dl)
      else
	None
  | (_,Imp(_,_)) ->
      let (mh,margs) = tm_head_args m in
      if defp sdel mh then
	conv2 (delta_exp sdel mh margs) n sdel (delta_cons mh dl)
      else
	None
  | (Lam(_,_),_) ->
      let (nh,nargs) = tm_head_args n in
      if defp sdel nh then
	conv2 m (delta_exp sdel nh nargs) sdel (delta_cons nh dl)
      else
	None
  | (All(_,_),_) ->
      let (nh,nargs) = tm_head_args n in
      if defp sdel nh then
	conv2 m (delta_exp sdel nh nargs) sdel (delta_cons nh dl)
      else
	None
  | (Imp(_,_),_) ->
      let (nh,nargs) = tm_head_args n in
      if defp sdel nh then
	conv2 m (delta_exp sdel nh nargs) sdel (delta_cons nh dl)
      else
	None
  | _ ->
      let (mh,margs) = tm_head_args m in
      if defp sdel mh then
	if deltap dl mh then
	  conv2 (delta_exp sdel mh margs) n sdel dl
	else
	  begin
	    match convrigid1 mh margs n sdel dl with
	    | Some(dl) -> Some(dl)
	    | None -> (*** try delta expanding mh ***)
		conv2 (delta_exp sdel mh margs) n sdel (delta_cons mh dl)
	  end
      else
	convrigid1 mh margs n sdel dl
and convrigid1 mh margs n sdel dl =
  let (nh,nargs) = tm_head_args n in
  if defp sdel nh then
    if deltap dl nh then
      convrigid1 mh margs (delta_exp sdel nh nargs) sdel dl
    else
      begin
	match convrigid2 mh margs nh nargs sdel dl with
	| Some(dl) -> Some(dl)
	| None -> (*** try delta expanding nh ***)
	    convrigid1 mh margs (delta_exp sdel nh nargs) sdel (delta_cons nh dl)
      end
  else
    convrigid2 mh margs nh nargs sdel dl
and convrigid2 mh margs nh nargs sdel dl =
  if mh = nh then
    convl margs nargs sdel dl
  else
    None
and convl ml nl sdel dl =
  match (ml,nl) with
  | ([],[]) -> Some(dl)
  | (m::mr,n::nr) ->
      begin
	match conv2 m n sdel dl with
	| Some(dl) -> convl mr nr sdel dl
	| None -> None
      end
  | _ -> None

let conv m n sdel dl =
  conv2 (tm_beta_eta_norm m) (tm_beta_eta_norm n) sdel dl

let rec extr_propofpf sgdelta sgtmof cxtm cxpf d dl =
  match d with
  | Hyp j -> (List.nth cxpf j,dl)
  | PTpAp(PTpAp(PTpAp(Known(h),a1),a2),a3) ->
      begin
	try
	  match Hashtbl.find sgdelta h with
	  | (i,p) ->
	      if i = 3 then
		(tmtpsubst p [a1;a2;a3],dl)
	      else if i = 1 then
		raise (Failure(h ^ " requires 1 type but was given none"))
	      else
		raise (Failure(h ^ " requires " ^ (string_of_int i) ^ " types but was given 3"))
	with Not_found -> raise (Failure(h ^ " should be known, but is not known")) 
      end
  | PTpAp(PTpAp(Known(h),a1),a2) ->
      begin
	try
	  match Hashtbl.find sgdelta h with
	  | (i,p) ->
	      if i = 2 then
		(tmtpsubst p [a1;a2],dl)
	      else if i = 1 then
		raise (Failure(h ^ " requires 1 type but was given none"))
	      else
		raise (Failure(h ^ " requires " ^ (string_of_int i) ^ " types but was given 2"))
	with Not_found -> raise (Failure(h ^ " should be known, but is not known")) 
      end
  | PTpAp(Known(h),a1) ->
      begin
	try
	  match Hashtbl.find sgdelta h with
	  | (i,p) ->
	      if i = 1 then
		(tmtpsubst p [a1],dl)
	      else
		raise (Failure(h ^ " requires " ^ (string_of_int i) ^ " types but was given 1"))
	with Not_found -> raise (Failure(h ^ " should be known, but is not known")) 
      end
  | Known(h) ->
      begin
	try
	  match Hashtbl.find sgdelta h with
	  | (i,p) ->
	      if i = 0 then
		(p,dl)
	      else if i = 1 then
		raise (Failure(h ^ " requires 1 type but was given none"))
	      else
		raise (Failure(h ^ " requires " ^ (string_of_int i) ^ " types but was given none"))
	with Not_found -> raise (Failure(h ^ " should be known, but is not known")) 
      end
  | PTmAp(d1,m) ->
      begin
	let (q,dl) = extr_propofpf sgdelta sgtmof cxtm cxpf d1 dl in
	match headnorm q sgdelta dl with
	| (All(a,p),dl) ->
	    if extr_tpoftm sgtmof cxtm m = a then
	      (tmsubst p 0 m,dl)
	    else
	      raise (Failure("Proof term for a universally quantified proposition applied to a term of the wrong type"))
	| _ ->
	    raise (Failure("Proof term does not prove a universally quantified proposition but is applied to a term"))
      end
  | PPfAp(d1,d2) ->
      begin
	let (q,dl) = extr_propofpf sgdelta sgtmof cxtm cxpf d1 dl in
	match headnorm q sgdelta dl with
	| (Imp(p1,p2),dl) ->
	    begin
	      match check_propofpf sgdelta sgtmof cxtm cxpf d2 p1 dl with
	      | Some(dl) -> (p2,dl)
	      | None ->
		  raise (Failure("Proof term for an implication applied to a proof term for the wrong proposition"))
	    end
	| _ ->
	    raise (Failure("Proof term does not prove an implication but is applied to a proof term"))
      end
  | TLam(a,d1) ->
      let (q,dl) = extr_propofpf sgdelta sgtmof (a::cxtm) (List.map (fun q -> tmshift 0 1 q) cxpf) d1 dl in
      (All(a,q),dl)
  | PLam(p,d1) ->
      let (q,dl) = extr_propofpf sgdelta sgtmof cxtm (p::cxpf) d1 dl in
      (Imp(p,q),dl)
  | _ -> raise (Failure("Ill-formed Proof Term"))
and check_propofpf sgdelta sgtmof cxtm cxpf d p dl =
  let (q,dl) = extr_propofpf sgdelta sgtmof cxtm cxpf d dl in
  conv q p sgdelta dl


exception MatchFail

type mtm =
  | MVar of int * mtm list
  | MDB of int
  | MTmH of string
  | MPrim of int
  | MTpAp of mtm * tp
  | MAp of mtm * mtm
  | MLam of tp * mtm
  | MImp of mtm * mtm
  | MAll of tp * mtm

let rec mtm_to_str m =
  match m with
  | MVar(x,[]) -> "?" ^ string_of_int x
  | MVar(x,(n::sigma)) -> "?" ^ string_of_int x ^ "[" ^ (mtm_to_str n) ^ (List.fold_right (fun n r -> "," ^ (mtm_to_str n) ^ r) sigma "]")
  | MDB(i) -> "_" ^ string_of_int i
  | MTmH(h) -> "#" ^ h
  | MPrim(i) -> "\"" ^ string_of_int i ^ "\""
  | MTpAp(m1,m2) -> "(" ^ mtm_to_str m1 ^ " " ^ tp_to_str m2 ^ ")"
  | MAp(m1,m2) -> "(" ^ mtm_to_str m1 ^ " " ^ mtm_to_str m2 ^ ")"
  | MLam(m1,m2) -> "(fun _:" ^ tp_to_str m1 ^ " => " ^ mtm_to_str m2 ^ ")"
  | MImp(m1,m2) -> "(" ^ mtm_to_str m1 ^ " -> " ^ mtm_to_str m2 ^ ")"
  | MAll(m1,m2) -> "(forall _:" ^ tp_to_str m1 ^ ", " ^ mtm_to_str m2 ^ ")"

let rec tm_to_mtm q =
  match q with
  | DB i -> MDB i
  | TmH h -> MTmH h
  | Prim i -> MPrim i
  | TpAp(q1,a) -> MTpAp(tm_to_mtm q1,a)
  | Ap(q1,q2) -> MAp(tm_to_mtm q1,tm_to_mtm q2)
  | Imp(q1,q2) -> MImp(tm_to_mtm q1,tm_to_mtm q2)
  | Lam(a,q1) -> MLam(a,tm_to_mtm q1)
  | All(a,q1) -> MAll(a,tm_to_mtm q1)

let rec mtm_to_tm q =
  match q with
  | MVar(_,_) -> raise Not_found
  | MDB i -> DB i
  | MTmH h -> TmH h
  | MPrim i -> Prim i
  | MTpAp(q1,a) -> TpAp(mtm_to_tm q1,a)
  | MAp(q1,q2) -> Ap(mtm_to_tm q1,mtm_to_tm q2)
  | MImp(q1,q2) -> Imp(mtm_to_tm q1,mtm_to_tm q2)
  | MLam(a,q1) -> Lam(a,mtm_to_tm q1)
  | MAll(a,q1) -> All(a,mtm_to_tm q1)

let rec mtm_shift i j m =
  match m with
  | MVar(x,sigma) -> MVar(x,List.map (mtm_shift i j) sigma)
  | MDB(k) when k < i -> MDB(k)
  | MDB(k) ->
      let l = k + j in
      if l >= i then MDB(l) else raise NegDB
  | MTpAp(m1,a) -> MTpAp(mtm_shift i j m1,a)
  | MAp(m1,m2) -> MAp(mtm_shift i j m1,mtm_shift i j m2)
  | MLam(a1,m1) -> MLam(a1,mtm_shift (i+1) j m1)
  | MImp(m1,m2) -> MImp(mtm_shift i j m1,mtm_shift i j m2)
  | MAll(a1,m1) -> MAll(a1,mtm_shift (i+1) j m1)
  | _ -> m

let rec mtm_subst m j n =
  match m with
  | MVar(x,sigma) -> MVar(x,List.map (fun m -> mtm_subst m j n) sigma)
  | MDB(i) when i = j && j = 0 -> n
  | MDB(i) when i = j -> mtm_shift 0 j n
  | MDB(i) when i > j -> MDB(i-1)
  | MTpAp(m1,a) -> MTpAp(mtm_subst m1 j n,a) (*** This could be omitted since it should always be TmH applied to <= 3 type variables, and so will contain no de Bruijns. ***)
  | MAp(m1,m2) -> MAp(mtm_subst m1 j n,mtm_subst m2 j n)
  | MLam(a1,m1) -> MLam(a1,mtm_subst m1 (j+1) n)
  | MImp(m1,m2) -> MImp(mtm_subst m1 j n,mtm_subst m2 j n)
  | MAll(a1,m1) -> MAll(a1,mtm_subst m1 (j+1) n)
  | _ -> m

let rec mtm_ssub tau q =
  match q with
  | MVar(x,sigma) -> MVar(x,List.map (mtm_ssub tau) sigma)
  | MDB i -> List.nth tau i
  | MTmH h -> MTmH h
  | MPrim i -> MPrim i
  | MTpAp(q1,a) -> MTpAp(mtm_ssub tau q1,a)
  | MAp(q1,q2) -> MAp(mtm_ssub tau q1,mtm_ssub tau q2)
  | MImp(q1,q2) -> MImp(mtm_ssub tau q1,mtm_ssub tau q2)
  | MLam(a,q1) -> MLam(a,mtm_ssub (MDB 0::List.map (mtm_shift 0 1) tau) q1)
  | MAll(a,q1) -> MAll(a,mtm_ssub (MDB 0::List.map (mtm_shift 0 1) tau) q1)

let rec mtm_msub theta q =
  match q with
  | MVar(x,sigma) ->
      begin
	let thetasigma = List.map (mtm_msub theta) sigma in
	try
	  let m = theta x in
	  mtm_ssub thetasigma m
	with Not_found -> MVar(x,thetasigma)
      end
  | MTpAp(q1,a) -> MTpAp(mtm_msub theta q1,a)
  | MAp(q1,q2) -> MAp(mtm_msub theta q1,mtm_msub theta q2)
  | MImp(q1,q2) -> MImp(mtm_msub theta q1,mtm_msub theta q2)
  | MLam(a,q1) -> MLam(a,mtm_msub theta q1)
  | MAll(a,q1) -> MAll(a,mtm_msub theta q1)
  | _ -> q

let op_min r z =
  match r with
  | Some(y) -> min y z
  | None -> z

let rec mtm_minap_db_r q j z r =
  match q with
  | MVar(x,sigma) ->
      mtms_minap_db_r sigma j r
  | MDB i when i = j -> Some(op_min r z)
  | MTpAp(q1,a) -> r (*** assume no DBs in q1 ***)
  | MAp(q1,q2) -> mtm_minap_db_r q1 j (z+1) (mtm_minap_db_r q2 j 0 r)
  | MImp(q1,q2) -> mtm_minap_db_r q1 j 0 (mtm_minap_db_r q2 j 0 r)
  | MLam(a,q1) -> mtm_minap_db_r q1 (j+1) 0 r
  | MAll(a,q1) -> mtm_minap_db_r q1 (j+1) 0 r
  | _ -> r
and mtms_minap_db_r sigma j r =
  match sigma with
  | [] -> r
  | (q::sigmar) -> mtms_minap_db_r sigmar j (mtm_minap_db_r q j 0 r)

let mtm_minap_db q j = mtm_minap_db_r q j 0 None

let rec mtm_lammvar_p q =
  match q with
  | MVar(_,_) -> true
  | MLam(_,q1) -> mtm_lammvar_p q1
  | _ -> false

let rec mtm_betared_if_1 q p =
  match q with
  | MVar(x,sigma) ->
      let (sigmar,sigmab) = mtms_betared_if_1 sigma p in
      (MVar(x,sigmar),sigmab)
  | MAp(q1,q2) ->
      let (q1r,q1b) = mtm_betared_if_1 q1 p in
      let (q2r,q2b) = mtm_betared_if_1 q2 p in
      begin
	match q1r with
	| MLam(a,qb) ->
	    if p qb q2r then
	      begin
		beta_count_check ();
		(mtm_subst qb 0 q2r,false) (*** beta, satisfying p ***)
	      end
	    else
	      (MAp(q1r,q2r),q1b && q2b)
	| _ -> (MAp(q1r,q2r),q1b && q2b)
      end
  | MLam(a,q1) ->
      let (q1r,q1b) = mtm_betared_if_1 q1 p in
      (MLam(a,q1r),q1b)
  | MImp(q1,q2) ->
      let (q1r,q1b) = mtm_betared_if_1 q1 p in
      let (q2r,q2b) = mtm_betared_if_1 q2 p in
      (MImp(q1r,q2r),q1b && q2b)
  | MAll(a,q1) ->
      let (q1r,q1b) = mtm_betared_if_1 q1 p in
      (MAll(a,q1r),q1b)
  | MTpAp(_,_) -> (q,true) (*** invariant should imply no betas are in here ***)
  | _ -> (q,true)
and mtms_betared_if_1 sigma p =
  match sigma with
  | [] -> ([],true)
  | (q::sigmar) ->
      let (qr,qb) = mtm_betared_if_1 q p in
      let (sigmarr,sigmarb) = mtms_betared_if_1 sigmar p in
      (qr::sigmarr,qb && sigmarb)

let rec mtm_betared_if q p =
  let (qr,qb) = mtm_betared_if_1 q p in
  if qb then
    qr
  else
    mtm_betared_if qr p

let rec pattern_invert k sigma q =
  match q with
  | DB i when i < k -> MDB i
  | DB i ->
      let j = position sigma (MDB (i-k)) in
      MDB (j+k)
  | TmH h -> MTmH h
  | Prim i -> MPrim i
  | TpAp(q1,a) -> MTpAp(pattern_invert k sigma q1,a)
  | Ap(q1,q2) -> MAp(pattern_invert k sigma q1,pattern_invert k sigma q2)
  | Imp(q1,q2) -> MImp(pattern_invert k sigma q1,pattern_invert k sigma q2)
  | Lam(a,q1) -> MLam(a,pattern_invert (k+1) sigma q1)
  | All(a,q1) -> MAll(a,pattern_invert (k+1) sigma q1)

let rec pattern_match sdel p q theta =
  match (p,q) with
  | (MVar(x,sigma),_) ->
      begin
	try
	  let m = mtm_ssub sigma (theta x) in
	  pattern_match sdel m q theta
	with Not_found ->
	  try
	    let m = pattern_invert 0 sigma q in
	    (fun y -> if x = y then m else theta y)
	  with Not_found -> raise MatchFail
      end
  | (MDB i,DB j) when i = j -> theta
  | (MPrim i,Prim j) when i = j -> theta
  | (MTmH h,TmH k) when h = k -> theta
  | (MTpAp(MTmH h,a1),TpAp(TmH k,b1)) when h = k && a1 = b1 -> theta
  | (MTpAp(MTpAp(MTmH h,a1),a2),TpAp(TpAp(TmH k,b1),b2)) when h = k && a1 = b1 && a2 = b2 -> theta
  | (MTpAp(MTpAp(MTpAp(MTmH h,a1),a2),a3),TpAp(TpAp(TpAp(TmH k,b1),b2),b3)) when h = k && a1 = b1 && a2 = b2 && a3 = b3 -> theta
  | (MAp(p1,p2),Ap(q1,q2)) ->
      let theta = pattern_match sdel p1 q1 theta in
      pattern_match sdel p2 q2 theta
  | (MImp(p1,p2),Imp(q1,q2)) ->
      let theta = pattern_match sdel p1 q1 theta in
      pattern_match sdel p2 q2 theta
  | (MLam(a1,p1),Lam(b1,q1)) when a1 = b1 ->
      pattern_match sdel p1 q1 theta
  | (MAll(a1,p1),All(b1,q1)) when a1 = b1 ->
      pattern_match sdel p1 q1 theta
  | (_,_) ->
      begin
	try
	  let p1 = mtm_to_tm p in
	  match conv p1 q sdel [] with
	  | Some(_) -> theta
	  | None -> raise MatchFail
	with Not_found -> raise MatchFail
      end

let rec mtm_app_red2 m args =
  match args with
  | (n::argr) -> mtm_app_red2 (MAp(m,n)) argr
  | _ -> m

let rec mtm_app_red m args =
  match (m,args) with
  | (MLam(_,m1),n::argr) ->
      mtm_app_red (mtm_subst m1 0 n) argr
  | _ ->
      mtm_app_red2 m args

let mdefp sdel h =
  match h with
  | MTmH(c) -> Hashtbl.mem sdel c
  | MTpAp(MTmH(c),_) -> Hashtbl.mem sdel c
  | MTpAp(MTpAp(MTmH(c),_),_) -> Hashtbl.mem sdel c
  | MTpAp(MTpAp(MTpAp(MTmH(c),_),_),_) -> Hashtbl.mem sdel c
  | _ -> false

(*** assume all defs are beta eta normal ***)
let mdelta_exp sdel h args =
  try
    match h with
    | MTmH(c) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 0 then
	    mtm_app_red (tm_to_mtm m) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to none."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to none."))
	end
    | MTpAp(MTmH(c),a1) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 1 then
	    mtm_app_red (tm_to_mtm (tmtpsubst m [a1])) args
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 1."))
	end
    | MTpAp(MTpAp(MTmH(c),a1),a2) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 2 then
	    mtm_app_red (tm_to_mtm (tmtpsubst m [a1;a2])) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to 2."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 2."))
	end
    | MTpAp(MTpAp(MTpAp(MTmH(c),a1),a2),a3) ->
	begin
	  let (i,m) = Hashtbl.find sdel c in
	  if i = 3 then
	    mtm_app_red (tm_to_mtm (tmtpsubst m [a1;a2;a3])) args
	  else if i = 1 then
	    raise (Failure(c ^ " should be applied to 1 type, but is applied to 3."))
	  else
	    raise (Failure(c ^ " should be applied to " ^ (string_of_int i) ^ " types, but is applied to 3."))
	end
    | _ -> raise Not_found
  with Not_found ->
    raise (Failure("mdelta_exp called with an inappropriate head. Bug"))

let rec mtm_head_args_r m args =
  match m with
  | MAp(m1,m2) -> mtm_head_args_r m1 (m2::args)
  | _ -> (m,args)

let mtm_head_args m =
  mtm_head_args_r m []

let mdelta_cons h dl =
  match h with
  | MTmH(c) -> (c::dl)
  | _ -> dl

let rec mheadnorm1 m sdel dl =
  match m with
  | MLam(_,_) -> (m,dl)
  | MImp(_,_) -> (m,dl)
  | MAll(_,_) -> (m,dl)
  | _ ->
      let (mh,margs) = mtm_head_args m in
      if mdefp sdel mh then
	mheadnorm1 (mdelta_exp sdel mh margs) sdel (mdelta_cons mh dl)
      else
	(m,dl)

let mheadnorm m sdel dl = mheadnorm1 m sdel dl

let first16bigint = big_int_of_int 65535

let checksum h =
  let v = ref h in
  let c = ref 0 in
  for j = 0 to 15 do
    c := !c + (int_of_big_int (and_big_int !v first16bigint));
    v := shift_right_towards_zero_big_int !v 16
  done;
  !c land 65535

let big203 = big_int_of_int 203
let big203pre = shift_left_big_int big203 272

let hash_w_checksum a =
  let h = Hash.sha256 a in
  Cryptocurr.base58 (or_big_int big203pre (or_big_int (shift_left_big_int h 16) (big_int_of_int (checksum h))))

let valid_id_p h =
  let h = Cryptocurr.frombase58 h in
  let p = (shift_right_towards_zero_big_int h 272) in
  if eq_big_int p big203 then
    let c = checksum (shift_right_towards_zero_big_int h 16) in
    c = (int_of_big_int (and_big_int h first16bigint))
  else
    false

let tp_id a =
  let c = Buffer.create 1000 in
  let bs0 = output_bits_byte_sb (c,None) 1 in (*** prefix byte so that types, terms and proofs will have different ids ***)
  flush_bits_sb (output_tp_sb_rec bs0 a);
  let s = Buffer.contents c in
  hash_w_checksum s

let ptp_id (i,a) =
  let c = Buffer.create 1000 in
  let bs0 = output_bits_byte_sb (c,None) 2 in (*** prefix byte so that types, terms and proofs will have different ids ***)
  let bs1 = output_bit_sb (i mod 2) bs0 in
  let bs2 = output_bit_sb (if i > 1 then 1 else 0) bs1 in
  flush_bits_sb (output_tp_sb_rec bs2 a);
  let s = Buffer.contents c in
  hash_w_checksum s

let tm_id_1 m =
  let c = Buffer.create 1000 in
  let bs0 = output_bits_byte_sb (c,None) 3 in (*** prefix byte so that types, terms and proofs will have different ids ***)
  flush_bits_sb (output_tm_sb_rec bs0 m);
  let s = Buffer.contents c in
  hash_w_checksum s

let ptm_id_1 (i,m) =
  let c = Buffer.create 1000 in
  let bs0 = output_bits_byte_sb (c,None) 4 in (*** prefix byte so that types, terms and proofs will have different ids ***)
  let bs1 = output_bit_sb (i mod 2) bs0 in
  let bs2 = output_bit_sb (if i > 1 then 1 else 0) bs1 in
  flush_bits_sb (output_tm_sb_rec bs2 m);
  let s = Buffer.contents c in
  hash_w_checksum s

(***
 m : tm,
 vl list of dangling de Bruijns,
 o boolean (true if has a type var, false ow),
 nf normalizing function (tm_beta_eta_norm if normal not guaranteed already, id if we know m is already normal)
 ***)
let hash_if_closed m vl o sof sdel nf =
  match (vl,o) with
  | ([],false) ->
      begin
	let m = nf m in
	match m with
	| TmH h -> (TmH h,[],false)
	| _ ->
	    let h = tm_id_1 m in
	    let a = extr_tpoftm sof [] m in
	    Hashtbl.add sof h (0,a);
	    Hashtbl.add sdel h (0,m);
	    (TmH h,[],false)
      end
  | _ -> (m,vl,o)

let rec tm_pack m sof sdel nf =
  match m with
  | DB(i) -> (m,[i],false)
  | TmH(h) -> (m,[],false)
  | Prim(0) -> raise (Failure("Eps without type encountered"))
  | Prim(i) ->
      let h = tm_id_1 m in
      let a = extr_tpoftm sof [] m in
      Hashtbl.add sof h (0,a);
      Hashtbl.add sdel h (0,m);
      (TmH h,[],false)
  | TpAp(Prim(0),a) -> (*** Eps ***)
      hash_if_closed (TpAp(Prim(0),a)) [] (not (tp_closed_p a)) sof sdel nf
  | TpAp(TpAp(TpAp(TmH(h),a1),a2),a3) ->
      begin
	try
	  let (j,d) = Hashtbl.find sdel h in
	  if j <> 3 then raise (Failure("#" ^ h ^ " applied to 3 types instead of " ^ (string_of_int j)));
	  (*** Egal originally reduced this if all the types are closed and this is needed for the old documents to check.
	       To produce Qeditas documents these should not be expanded.
	       The boolean polyexpand controls this.
	   ***)
          if !polyexpand && tp_closed_p a1 && tp_closed_p a2 && tp_closed_p a3 then (*** If all the types are closed, then expand and pack ***)
            let m = tmtpsubst d [a1;a2;a3] in
            tm_pack m sof sdel nf
          else (*** Otherwise, stick with the id of the poly def and consider it open ***)
            (m,[],true)
	with Not_found ->
	  raise (Failure("Unknown poly term " ^ h))
      end
  | TpAp(TpAp(TmH(h),a1),a2) ->
      begin
	try
	  let (j,d) = Hashtbl.find sdel h in
	  if j <> 2 then raise (Failure("#" ^ h ^ " applied to 2 types instead of " ^ (string_of_int j)));
	  if !polyexpand && tp_closed_p a1 && tp_closed_p a2 then (*** If all the types are closed, then expand and pack ***)
	    let m = tmtpsubst d [a1;a2] in
	    tm_pack m sof sdel nf
	  else (*** Otherwise, stick with the id of the poly def and consider it open ***)
	    (m,[],true)
	with Not_found ->
	  raise (Failure("Unknown poly term " ^ h))
      end
  | TpAp(TmH(h),a1) ->
      begin
	try
	  let (j,d) = Hashtbl.find sdel h in
	  if j <> 1 then raise (Failure("#" ^ h ^ " applied to 1 type instead of " ^ (string_of_int j)));
	  if !polyexpand && tp_closed_p a1 then (*** If all the types are closed, then expand and pack ***)
	    let m = tmtpsubst d [a1] in
	    tm_pack m sof sdel nf
	  else (*** Otherwise, stick with the id of the poly def and consider it open ***)
	    (m,[],true)
	with Not_found ->
	  raise (Failure("Unknown poly term " ^ h))
      end
  | TpAp(_,_) -> raise (Failure("Illegal polymorphism"))
  | Ap(m1,m2) ->
      let (m1p,m1il,m1o) = tm_pack m1 sof sdel nf in
      let (m2p,m2il,m2o) = tm_pack m2 sof sdel nf in
      hash_if_closed (Ap(m1p,m2p)) (m1il @ m2il) (m1o || m2o) sof sdel nf
  | Lam(a,m1) ->
      let (m1p,m1il,m1o) = tm_pack m1 sof sdel nf in
      hash_if_closed (Lam(a,m1p)) (List.map (fun i -> i - 1) (List.filter (fun i -> i > 0) m1il)) (m1o || (not (tp_closed_p a))) sof sdel nf
  | Imp(m1,m2) ->
      let (m1p,m1il,m1o) = tm_pack m1 sof sdel nf in
      let (m2p,m2il,m2o) = tm_pack m2 sof sdel nf in
      hash_if_closed (Imp(m1p,m2p)) (m1il @ m2il) (m1o || m2o) sof sdel nf
  | All(a,m1) ->
      let (m1p,m1il,m1o) = tm_pack m1 sof sdel nf in
      hash_if_closed (All(a,m1p)) (List.map (fun i -> i - 1) (List.filter (fun i -> i > 0) m1il)) (m1o || (not (tp_closed_p a))) sof sdel nf

let tm_pack_full m sof sdel =
  let (m2,vl,o) = tm_pack m sof sdel tm_beta_eta_norm in
  let m3 = tm_beta_eta_norm m2 in
  tm_pack m3 sof sdel (fun m -> m)

let rec tm_id m sof sdel = 
  let (m4,vl,o) = tm_pack_full m sof sdel in
  match m4 with
  | TmH h ->
      h
  | _ ->
      match (vl,o) with
      | (_::_,_) -> raise (Failure("Term cannot be given an id since it is open"))
      | ([],true) -> raise (Failure("Term cannot be given an id since it has a type variable"))
      | _ -> raise (Failure("There's a bug. A closed term was not properly packed."))

let ptm_id (i,m) sof sdel =
  let (m2,vl,o) = tm_pack m sof sdel tm_beta_eta_norm in
  let m3 = tm_beta_eta_norm m2 in
  let (m4,vl,_) = tm_pack m3 sof sdel (fun m -> m) in
  match vl with
  | (_::_) -> raise (Failure("Term cannot be given an id since it is open"))
  | _ ->
      match m4 with
      | TmH h when i = 0 -> (*** If it's fully packed, return id h ***)
	  h
      | TpAp(TmH h,TpVar 0) when i = 1 -> (*** If it's fully packed, return id h ***)
	  h
      | TpAp(TpAp(TmH h,TpVar 0),TpVar 1) when i = 2 -> (*** If it's fully packed, return id h ***)
	  h
      | TpAp(TpAp(TpAp(TmH h,TpVar 0),TpVar 1),TpVar 2) when i = 3 -> (*** If it's fully packed, return id h ***)
	  h
      | _ -> (*** otherwise compute id using the number of type var args, as if it's TypeLam...m4 ***)
	  let h = ptm_id_1 (i,m4) in
	  let a = extr_tpoftm sof [] m4 in
	  Hashtbl.add sof h (i,a);
	  Hashtbl.add sdel h (i,m4);
	  h

let pf_id_1 d =
  let c = Buffer.create 1000 in
  let bs0 = output_bits_byte_sb (c,None) 5 in (*** prefix byte so that types, terms and proofs will have different ids ***)
  flush_bits_sb (output_pf_sb_rec bs0 d);
  let s = Buffer.contents c in
  hash_w_checksum s

let ppf_id_1 (i,d) =
  let c = Buffer.create 1000 in
  let bs0 = output_bits_byte_sb (c,None) 6 in (*** prefix byte so that types, terms and proofs will have different ids ***)
  let bs1 = output_bit_sb (i mod 2) bs0 in
  let bs2 = output_bit_sb (if i > 1 then 1 else 0) bs1 in
  flush_bits_sb (output_pf_sb_rec bs2 d);
  let s = Buffer.contents c in
  hash_w_checksum s

let rec pf_pack_full d sof sdel =
  match d with
  | PTpAp(d1,a1) -> PTpAp(pf_pack_full d1 sof sdel,a1)
  | PTmAp(d1,m1) -> PTmAp(pf_pack_full d1 sof sdel,let (n1,_,_) = tm_pack_full m1 sof sdel in n1)
  | PPfAp(d1,d2) -> PPfAp(pf_pack_full d1 sof sdel,pf_pack_full d2 sof sdel)
  | PLam(m1,d1) -> PLam((let (n1,_,_) = tm_pack_full m1 sof sdel in n1),pf_pack_full d1 sof sdel)
  | TLam(a1,d1) -> TLam(a1,pf_pack_full d1 sof sdel)
  | _ -> d

let pf_id d sof sdel =
  let d2 = pf_pack_full d sof sdel in
  pf_id_1 d2

let ppf_id (i,d) sof sdel =
  let d2 = pf_pack_full d sof sdel in
  ppf_id_1 (i,d2)

let rec tp_args_rtp a =
  match a with
  | Ar(a1,a2) ->
      let (argtpl,rtp) = tp_args_rtp a2 in
      (a1::argtpl,rtp)
  | _ -> ([],a)

let gen_lam_body m =
  match m with
  | Lam(_,mb) -> mb
  | _ -> Ap(tmshift 0 1 m,DB(0))

let rec mk_forall_tm argtpl f m n =
  match argtpl with
  | (a::argtpr) ->
      let mb = gen_lam_body m in
      let nb = gen_lam_body n in
      All(a,mk_forall_tm argtpr f mb nb)
  | [] -> f m n

let rec mk_gen_ap m nl =
  match nl with
  | (n::nr) -> mk_gen_ap (Ap(m,n)) nr
  | [] -> m

let unicode : (string,string list) Hashtbl.t = Hashtbl.create 100;;
let subscript : (string,unit) Hashtbl.t = Hashtbl.create 100;;
let superscript : (string,unit) Hashtbl.t = Hashtbl.create 100;;

begin
  Hashtbl.add unicode "->" ["2192"];
  Hashtbl.add unicode "fun" ["3bb"];
  Hashtbl.add unicode "forall" ["2200"];
end

let authors : string list ref = ref []
let title : string option ref = ref None
let signature : string option ref = ref None
let showproofterms : bool ref = ref false
let salt : string option ref = ref None
let treasure : string option ref = ref None

let id_to_btcprivkey h =
  match !salt with
  | Some s -> Hash.sha256(s ^ h)
  | None -> Hash.sha256(h)

(*** code for measuring complexity of tms and pfs -- not necessary ***)
let rec rem_dups_r ml rl =
  match ml with
  | [] -> rl
  | (m::mr) ->
      if List.mem m rl then
	rem_dups_r mr rl
      else
	rem_dups_r mr (m::rl)

let rem_dups ml = rem_dups_r ml []

let rec tm_info m =
  match m with
  | Lam(a,m) ->
      let (hs,ltps,atps,aps,imps) = tm_info m in
      (hs,a::ltps,atps,aps,imps)
  | All(a,m) -> 
      let (hs,ltps,atps,aps,imps) = tm_info m in
      (hs,ltps,a::atps,aps,imps)
  | Ap(m1,m2) ->
      let (hs1,ltps1,atps1,aps1,imps1) = tm_info m1 in
      let (hs2,ltps2,atps2,aps2,imps2) = tm_info m2 in
      (hs1 @ hs2,ltps1 @ ltps2,atps1 @ atps2,1+aps1+aps2,imps1+imps2)
  | Imp(m1,m2) ->
      let (hs1,ltps1,atps1,aps1,imps1) = tm_info m1 in
      let (hs2,ltps2,atps2,aps2,imps2) = tm_info m2 in
      (hs1 @ hs2,ltps1 @ ltps2,atps1 @ atps2,aps1+aps2,1+imps1+imps2)
  | TmH(h) -> ([h],[],[],0,0)
  | TpAp(TmH(h),_) -> ([h],[],[],0,0)
  | TpAp(TpAp(TmH(h),_),_) -> ([h],[],[],0,0)
  | TpAp(TpAp(TpAp(TmH(h),_),_),_) -> ([h],[],[],0,0)
  | _ -> ([],[],[],0,0)

let rec pf_info d =
  match d with
  | Known(h) -> ([h],[],[],0,[],[])
  | PTpAp(Known(h),_) -> ([h],[],[],0,[],[])
  | PTpAp(PTpAp(Known(h),_),_) -> ([h],[],[],0,[],[])
  | PTpAp(PTpAp(PTpAp(Known(h),_),_),_) -> ([h],[],[],0,[],[])
  | TLam(a,d) ->
      let (kl,tlams,insts,mps,plams,pbetas) = pf_info d in
      (kl,a::tlams,insts,mps,plams,pbetas)
  | PTmAp(d,m) ->
      let (kl,tlams,insts,mps,plams,pbetas) = pf_info d in
      (kl,tlams,m::insts,mps,plams,pbetas)
  | PPfAp(d1,d2) ->
      let (kl1,tlams1,insts1,mps1,plams1,pbetas1) = pf_info d1 in
      let (kl2,tlams2,insts2,mps2,plams2,pbetas2) = pf_info d2 in
      begin
	match d1 with
	| PLam(m,d) ->
	    (kl1 @ kl2,tlams1 @ tlams2,insts1 @ insts2,1+mps1+mps2,plams1 @ plams2,m::(pbetas1 @ pbetas2))
	| _ ->
	    (kl1 @ kl2,tlams1 @ tlams2,insts1 @ insts2,1+mps1+mps2,plams1 @ plams2,pbetas1 @ pbetas2)
      end
  | PLam(m,d) ->
      let (kl,tlams,insts,mps,plams,pbetas) = pf_info d in
      (kl,tlams,insts,mps,m::plams,pbetas)
  | _ -> ([],[],[],0,[],[])

let pf_complexity d =
  let (kl,tlams,insts,mps,plams,pbetas) = pf_info d in
  let kl2 = rem_dups kl in
  let tlams2 = rem_dups tlams in
  let insts2 = rem_dups insts in
  let plams2 = rem_dups plams in
  let pbetas2 = rem_dups pbetas in
  let complexity = ref (5 * mps) in
  complexity := !complexity + 10 * (List.length kl2) + List.length kl;
  complexity := !complexity + 10 * (List.length tlams2) + List.length tlams;
  List.iter
    (fun m ->
      let (hs,ltps,atps,aps,imps) = tm_info m in
      complexity := !complexity + List.length hs + List.length ltps + List.length atps + aps + imps
      )
    plams2;
  complexity := !complexity + List.length plams;
  List.iter
    (fun m ->
      let (hs,ltps,atps,aps,imps) = tm_info m in
      let hs2 = rem_dups hs in
      let ltps2 = rem_dups ltps in
      let atps2 = rem_dups atps in
      complexity := !complexity + 100 * (List.length ltps2); (** number of lambdas in the instantiations **)
      complexity := !complexity + 5 * (List.length hs2 + List.length atps2) + 10 * (List.length ltps) + List.length hs + List.length atps)
    insts2;
  complexity := !complexity + 10 * List.length insts;
  List.iter
    (fun m ->
      let (hs,ltps,atps,aps,imps) = tm_info m in
      let hs2 = rem_dups hs in
      let ltps2 = rem_dups ltps in
      let atps2 = rem_dups atps in
      complexity := !complexity + 70 * (List.length ltps2);
      complexity := !complexity + 3 * (List.length hs2 + List.length atps2) + 7 * (List.length ltps) + List.length hs + List.length atps)
    pbetas2;
  !complexity

let output_unicode_html ch u =
  output_string ch "&#x";
  output_string ch u;
  output_char ch ';'

let output_name_html ch x =
  try
    let ul = Hashtbl.find unicode x in
    List.iter (fun u -> output_unicode_html ch u) ul
  with Not_found ->
    output_string ch x

let output_asckind_html ch k =
  match k with
  | AscTp -> output_string ch " : "
  | AscSet -> output_string ch " &#x2208; "
  | AscSubeq -> output_string ch " &#x2286; "

let output_setinfixop_html ch k =
  match k with
  | InfMem -> output_string ch " &#x2208; "
  | InfSubq -> output_string ch " &#x2286; "

let output_infixop_html ch i =
  match i with
  | InfNam(x) -> output_name_html ch x
  | InfSet(k) -> output_setinfixop_html ch k

let output_midtok_html ch m =
  if m = "," then
    output_string ch ", "
  else if m = "=>" then
    output_string ch " &#x21d2; "
  else
    output_string ch m

let output_names_html ch xl =
  match xl with
  | [] -> ()
  | (x::yl) ->
      output_name_html ch x;
      List.iter
	(fun y ->
	  output_char ch ' ';
	  output_string ch y;
	)
	yl

let rec output_comma_names_html ch xl =
  match xl with
  | [] -> ()
  | [x] ->
      output_name_html ch x;
  | [x;y] ->
      output_name_html ch x;
      output_string ch " and ";
      output_name_html ch y;
  | (x::yl) ->
      output_name_html ch x;
      output_string ch ", ";
      output_comma_names_html ch yl

(*** <a> causes css problems in combination with <span> for some reason, so only call this if it's declaring the name (not inside an lterm).
    Eh, it also insists on screwing up the font. I've just changed all anchors to have the math friendly font. How annoying. ***)
let output_name_whrefa_html ch x stmh sknh =
  begin
    try
      let hid = Hashtbl.find stmh x in
      output_string ch "<a classname='anamelink' href='term.php?h="; 
      output_string ch hid;
      output_string ch "'>";
      output_name_html ch x;
      output_string ch "</a>";
    with Not_found ->
      try
	let hid = Hashtbl.find sknh x in
	output_string ch "<a classname='anamelink' href='term.php?h="; 
	output_string ch hid;
	output_string ch "'>";
	output_name_html ch x;
	output_string ch "</a>";
      with Not_found ->
	output_name_html ch x
  end

(*** <a> causes css problems in combination with <span> for some reason, so I usually call this and use a span for links ***)
let output_name_whref_html ch x stmh sknh =
  begin
    try
      let hid = Hashtbl.find stmh x in
      output_string ch "<span class='namelink' onclick=\"location.href='term.php?h="; 
      output_string ch hid;
      output_string ch "';\">";
      output_name_html ch x;
      output_string ch "</span>";
    with Not_found ->
      try
	let hid = Hashtbl.find sknh x in
	output_string ch "<span class='namelink' onclick=\"location.href='term.php?h=";
	output_string ch hid;
	output_string ch "';\">";
	output_name_html ch x;
	output_string ch "</span>";
      with Not_found ->
	output_name_html ch x
  end

let rec output_ltree_html ch a stmh sknh =
  output_string ch "<span class='ltree'>";
  output_ltree_html_c ch a stmh sknh;
  output_string ch "</span>"
and output_ltree_html_c ch a stmh sknh =
  match a with
  | NaL(x) ->
      output_name_whref_html ch x stmh sknh
  | NuL(b,x,None,None) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
      end
  | NuL(b,x,Some y,None) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch '.';
	output_string ch y;
      end
  | NuL(b,x,None,Some z) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch 'E';
	output_string ch z;
      end
  | NuL(b,x,Some y,Some z) ->
      begin
	if b then output_char ch '-';
	output_string ch x;
	output_char ch '.';
	output_string ch y;
	output_char ch 'E';
	output_string ch z;
      end
  | LeL(x,None,a,c) ->
      begin
	output_string ch "<span class='keyword'>let</span> ";
	output_string ch x;
	output_string ch  " &#x2254; ";
	output_ltree_html ch a stmh sknh;
	output_string ch " <span class='keyword'>in</span> ";
	output_ltree_html ch c stmh sknh;
      end
  | LeL(x,Some(i,b),a,c) ->
      begin
	output_string ch "<span class='keyword'>let</span> ";
	output_string ch x;
	output_asckind_html ch i;
	output_ltree_html ch b stmh sknh;
	output_string ch  " &#x2254; ";
	output_ltree_html ch a stmh sknh;
	output_string ch " <span class='keyword'>in</span> ";
	output_ltree_html ch c stmh sknh;
      end
  | LeML(x,yl,a,c) ->
      begin
	output_string ch "<span class='keyword'>let</span> [";
	output_string ch x;
	List.iter
	  (fun y ->
	    output_char ch ',';
	    output_string ch y;
	    )
	  yl;
	output_string ch  "] := ";
	output_ltree_html ch a stmh sknh;
	output_string ch  " in ";
	output_ltree_html ch c stmh sknh;
      end
  | BiL(x,m,[(xl,o)],c) ->
      let subp = Hashtbl.mem subscript x in
      let supp = Hashtbl.mem superscript x in
      output_name_html ch x;
      if subp then output_string ch "<sub>" else if supp then output_string ch "<sup>" else if not (Hashtbl.mem unicode x) then output_string ch " ";
      output_names_html ch xl;
      begin
	match o with
	| None -> ()
	| Some(i,b) ->
	    output_asckind_html ch i;
	    output_ltree_html ch b stmh sknh
      end;
      if subp then
	output_string ch "</sub>"
      else if supp then
	output_string ch "</sup>"
      else
	begin
	  output_midtok_html ch m;
	  output_string ch " "
	end;
      output_ltree_html ch c stmh sknh
  | BiL(x,m,vll,c) ->
      let subp = Hashtbl.mem subscript x in
      let supp = Hashtbl.mem superscript x in
      output_name_html ch x;
      if subp then output_string ch "<sub>" else if supp then output_string ch "<sup>";
      List.iter
	(fun (xl,o) ->
	  output_char ch '(';
	  output_names_html ch xl;
	  begin
	    match o with
	    | None -> ()
	    | Some(i,b) ->
		output_asckind_html ch i;
		output_ltree_html ch b stmh sknh
	  end;
	  output_char ch ')';
	)
	vll;
      if subp then
	output_string ch "</sub>"
      else if supp then
	output_string ch "</sup>"
      else
	output_midtok_html ch m;
      output_ltree_html ch c stmh sknh
  | PreoL(x,a) ->
      output_name_html ch x;
      output_char ch ' ';
      output_ltree_html ch a stmh sknh
  | PostoL(x,a) ->
      output_ltree_html ch a stmh sknh;
      output_char ch ' ';
      output_name_html ch x
  | InfoL(x,a,b) ->
      begin
	if match x with InfNam(y) -> Hashtbl.mem subscript y | _ -> false then
	  begin
	    output_ltree_html ch a stmh sknh;
	    output_string ch "<sub>";
	    output_ltree_html ch b stmh sknh;
	    output_string ch "</sub>";
	  end
	else if match x with InfNam(y) -> Hashtbl.mem superscript y | _ -> false then
	  begin
	    output_ltree_html ch a stmh sknh;
	    output_string ch "<sup>";
	    output_ltree_html ch b stmh sknh;
	    output_string ch "</sup>";
	  end
	else
	  begin
	    output_ltree_html ch a stmh sknh;
	    output_char ch ' ';
	    output_infixop_html ch x;
	    output_char ch ' ';
	    output_ltree_html ch b stmh sknh
	  end
      end
  | ImplopL(a,b) ->
      output_ltree_html ch a stmh sknh;
      output_char ch ' ';
      output_ltree_html ch b stmh sknh
  | SepL(x,i,a,b) ->
      output_char ch '{';
      output_name_html ch x;
      output_setinfixop_html ch i;
      output_ltree_html ch a stmh sknh;
      output_char ch '|';
      output_ltree_html ch b stmh sknh;
      output_char ch '}';
  | RepL(x,i,a,b) ->
      output_char ch '{';
      output_ltree_html ch a stmh sknh;
      output_char ch '|';
      output_name_html ch x;
      output_setinfixop_html ch i;
      output_ltree_html ch b stmh sknh;
      output_char ch '}';
  | SepRepL(x,i,a,b,c) ->
      output_char ch '{';
      output_ltree_html ch a stmh sknh;
      output_char ch '|';
      output_name_html ch x;
      output_setinfixop_html ch i;
      output_ltree_html ch b stmh sknh;
      output_string ch ", ";
      output_ltree_html ch c stmh sknh;
      output_char ch '}';
  | SetEnumL([]) ->
      output_char ch '{';
      output_char ch '}';
  | SetEnumL(a::bl) ->
      output_char ch '{';
      output_ltree_html ch a stmh sknh;
	List.iter
	  (fun b ->
	    output_char ch ',';
	    output_ltree_html ch b stmh sknh;
	    )
	  bl;
      output_char ch '}';
  | MTupleL(a,bl) ->
      output_char ch '[';
      output_ltree_html ch a stmh sknh;
      List.iter
	(fun b ->
	  output_char ch ',';
	  output_ltree_html ch b stmh sknh;
	)
	bl;
      output_char ch ']';
  | ParenL(a,[]) ->
      output_char ch '(';
      output_ltree_html ch a stmh sknh;
      output_char ch ')';
  | ParenL(a,b::cl) ->
      output_char ch '(';
      output_ltree_html ch a stmh sknh;
      List.iter
	(fun c ->
	  output_char ch ',';
	  output_ltree_html ch c stmh sknh;
	)
	(b::cl);
      output_char ch ')';
  | IfThenElseL(a,b,c) ->
      output_string ch "<span class='keyword'>if</span> ";
      output_ltree_html ch a stmh sknh;
      output_string ch " <span class='keyword'>then</span> ";
      output_ltree_html ch b stmh sknh;
      output_string ch " <span class='keyword'>else</span> ";
      output_ltree_html ch c stmh sknh

let url_friendly_name x =
  let y = Buffer.create 100 in
  for i = 0 to (String.length x) - 1 do
    let c = x.[i] in
    let co = Char.code c in
    if (co >= 48 && co <= 57 || co >= 65 && co <= 90 || co >= 97 && co <= 122) then
      Buffer.add_char y c
    else
      begin
	Buffer.add_char y '_';
	Buffer.add_char y (hex_char ((co lsr 4) mod 16));
	Buffer.add_char y (hex_char (co mod 16));
      end
  done;
  Buffer.contents y

let output_docitem_html ch ditem stmh sknh =
  match ditem with
  | Author(x,yl) -> ()
  | Title(x) -> ()
  | Salt(x) -> ()
  | Treasure(x) ->
      Printf.fprintf ch "\n$%s\n" x;
  | ShowProofTerms(_) -> ()
  | Section(_) -> output_string ch "<div class='formalsection'>";
  | End(_) -> output_string ch "</div>\n";
  | VarDecl(xl,i,a) ->
      output_string ch "<div class='vardecl'><span class='docitemkeyword'>Variable</span> <span class='ltree'>";
      List.iter
	(fun x ->
	  output_char ch ' ';
	  output_string ch x;
	)
	xl;
      output_asckind_html ch i;
      output_ltree_html ch a stmh sknh;
      output_string ch "</span></div>\n";
  | LetDecl(x,None,b) ->
      output_string ch "\n$\n";
      output_string ch "<div class='letdecl'><span class='docitemkeyword'>Let</span> <span class='ltree'>";
      output_string ch x;
      output_string ch " &#x225d; ";
      output_ltree_html ch b stmh sknh;
      output_string ch "</span></div>\n";
  | LetDecl(x,Some(i,a),b) ->
      output_string ch "\n$\n";
      output_string ch "<div class='letdecl'><span class='docitemkeyword'>Let</span> <span class='ltree'>";
      output_string ch x;
      output_string ch " ";
      output_asckind_html ch i;
      output_ltree_html ch a stmh sknh;
      output_string ch " &#x225d; ";
      output_ltree_html ch b stmh sknh;
      output_string ch "</span></div>\n";
  | HypDecl(x,b) ->
      output_string ch "\n$\n";
      output_string ch "<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>";
      output_string ch x;
      output_string ch " : ";
      output_ltree_html ch b stmh sknh;
      output_string ch "</span></div>\n";
  | PostInfixDecl(x,b,p,InfixNone) ->
      output_string ch "\n$\n";
      output_string ch "<div class='infixdecl'><b>Notation</b>. We use <span class='ltree'>";
      output_name_html ch x;
      output_string ch "</span> as an infix operator with priority ";
      output_string ch (string_of_int p);
      output_string ch " and no associativity";
      output_string ch " corresponding to applying term <span class='ltree'>";
      output_ltree_html ch b stmh sknh;
      output_string ch "</span>.</div>\n";
  | PostInfixDecl(x,b,p,InfixLeft) ->
      output_string ch "\n$\n";
      output_string ch "<div class='infixdecl'><b>Notation</b>. We use <span class='ltree'>";
      output_name_html ch x;
      output_string ch "</span> as an infix operator with priority ";
      output_string ch (string_of_int p);
      output_string ch " and which associates to the left";
      output_string ch " corresponding to applying term <span class='ltree'>";
      output_ltree_html ch b stmh sknh;
      output_string ch "</span>.</div>\n";
  | PostInfixDecl(x,b,p,InfixRight) ->
      output_string ch "\n$\n";
      output_string ch "<div class='infixdecl'><b>Notation</b>. We use <span class='ltree'>";
      output_name_html ch x;
      output_string ch "</span> as an infix operator with priority ";
      output_string ch (string_of_int p);
      output_string ch " and which associates to the right";
      output_string ch " corresponding to applying term <span class='ltree'>";
      output_ltree_html ch b stmh sknh;
      output_string ch "</span>.</div>\n";
  | PostInfixDecl(x,b,p,Postfix) ->
      output_string ch "\n$\n";
      output_string ch "<div class='postfixdecl'><b>Notation</b>. We use <span class='ltree'>";
      output_name_html ch x;
      output_string ch "</span> as a postfix operator with priority ";
      output_string ch (string_of_int p);
      output_string ch " corresponding to applying term <span class='ltree'>";
      output_ltree_html ch b stmh sknh;
      output_string ch "</span>.";
      output_string ch "</div>\n";
  | PrefixDecl(x,b,p) ->
      output_string ch "\n$\n";
      output_string ch "<div class='prefixdecl'><b>Notation</b>. We use <span class='ltree'>";
      output_name_html ch x;
      output_string ch "</span> as a prefix operator with priority ";
      output_string ch (string_of_int p);
      output_string ch " corresponding to applying term <span class='ltree'>";
      output_ltree_html ch b stmh sknh;
      output_string ch "</span>.";
      output_string ch "</div>\n";
  | BinderDecl(plus,comma,x,a,None) ->
      output_string ch "\n$\n";
      output_string ch "<div class='binderdecl'><b>Notation</b>. We use <span class='ltree'>";
      output_name_html ch x;
      if plus then
	output_string ch " <i>x</i>...<i>y</i> [possibly with ascriptions] "
      else
	output_string ch " <i>x</i> [possibly with ascriptions] ";
      if comma then
	output_string ch " , <i>B</i> "
      else
	output_string ch " &#x21d2; <i>B</i>";
      output_string ch "</span> as a binder notation corresponding to a term constructed using <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span>.</div>\n";
  | BinderDecl(plus,comma,x,a,Some(b)) ->
      output_string ch "\n$\n";
      output_string ch "<div class='binderdecl'><b>Notation</b>. We use <span class='ltree'>";
      output_name_html ch x;
      if plus then
	output_string ch " <i>x</i>...<i>y</i> [possibly with ascriptions] "
      else
	output_string ch " <i>x</i> [possibly with ascriptions] ";
      if comma then
	output_string ch " , <i>B</i> "
      else
	output_string ch " &#x21d2; <i>B</i> ";
      output_string ch "</span> as a binder notation corresponding to a term constructed using <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span> and handling  &#x2208; or &#x2286; ascriptions using <span class='ltree'>";
      output_ltree_html ch b stmh sknh;
      output_string ch "</span>.</div>\n";
  | NotationDecl(x,yl) ->
      output_string ch "\n$\n";
      output_string ch "<div class='notationdecl'><b>Notation</b>. ";
      begin
	match x with
	| "IfThenElse" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'><span class='keyword'>if</span> <i>cond</i> <span class='keyword'>then</span> <i>T</i> <span class='keyword'>else</span> <i>E</i></span> is notation corresponding to <span class='ltree'>";
		  output_string ch y;
		  output_string ch " <i>type</i> <i>cond</i> <i>T</i> <i>E</i></span> where <span class='ltree'><i>type</i></span> is the inferred type of <span class='ltree'><i>T</i></span>."
	      | _ ->
		  raise (Failure("Bad IfThenElse notation"))
	    end
	| "Repl" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>{<i>B</i>| <i>x</i> &#x2208; <i>A</i>}</span> is notation for <span class='ltree'>";
		  output_name_whref_html ch y stmh sknh;
		  output_string ch " <i>A</i> (&#x03bb; <i>x</i> . <i>B</i>)</span>."
	      | _ ->
		  raise (Failure("Bad Repl notation"))
	    end
	| "Sep" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>{<i>x</i> &#x2208; <i>A</i> | <i>B</i>}</span> is notation for <span class='ltree'>";
		  output_name_whref_html ch y stmh sknh;
		  output_string ch " <i>A</i> (&#x03bb; <i>x</i> . <i>B</i>)</span>."
	      | _ ->
		  raise (Failure("Bad Sep notation"))
	    end
	| "ReplSep" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>{<i>B</i>| <i>x</i> &#x2208; <i>A</i>, <i>C</i>}</span> is notation for <span class='ltree'>";
		  output_name_whref_html ch y stmh sknh;
		  output_string ch " <i>A</i> (&#x03bb; <i>x</i> . <i>C</i>) (&#x03bb; <i>x</i> . <i>B</i>)</span>."
	      | _ ->
		  raise (Failure("Bad ReplSep notation"))
	    end
	| "SetEnum" ->
	    begin
	      output_string ch "We now use the set enumeration notation <span class='ltree'>{...,...,...}</span> in general. ";
	      let rec setenum_notation_expl_r i z yl =
		match yl with
		| [] ->
		    output_string ch "  If more than ";
		    if i = 1 then
		      output_string ch " element is "
		    else
		      output_string ch " elements are ";
		    output_string ch " given, then <span class='ltree'>";
		    output_name_whref_html ch z stmh sknh;
		    output_string ch "</span> is used to reduce to the case with one fewer elements."
		| (y::yr) ->
		    output_string ch "  If ";
		    output_string ch (string_of_int i);
		    if i = 1 then
		      output_string ch " element is "
		    else
		      output_string ch " elements are ";
		    output_string ch " given, then <span class='ltree'>";
		    output_name_whref_html ch z stmh sknh;
		    output_string ch "</span> is used to form the corresponding term.";
		    setenum_notation_expl_r (i+1) y yr
	      in
	      match yl with
	      | (y::yr) ->
		  setenum_notation_expl_r 0 y yr
	      | _ ->
		  raise (Failure("Bad SetEnum notation"))
	    end
	| "SetEnum0" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>{}</span> is notation for <span class='ltree'>";
		  output_name_whref_html ch y stmh sknh;
		  output_string ch "</span>.";
	      | _ ->
		  raise (Failure("Bad SetEnum0 notation"))
	    end
	| "SetEnum1" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>{<i>x</i>}</span> is notation for <span class='ltree'>";
		  output_name_whref_html ch y stmh sknh;
		  output_string ch " <i>x</i></span>.";
	      | _ ->
		  raise (Failure("Bad SetEnum1 notation"))
	    end
	| "SetEnum2" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>{<i>x</i>,<i>y</i>}</span> is notation for <span class='ltree'>";
		  output_name_whref_html ch y stmh sknh;
		  output_string ch " <i>x</i> <i>y</i></span>.";
	      | _ ->
		  raise (Failure("Bad SetEnum2 notation"))
	    end
	| "Nat" ->
	    begin
	      match yl with
	      | [y0;yS] ->
		  output_string ch "Natural numbers 0,1,2,... are notation for the terms formed using <span class='ltree'>";
		  output_name_whref_html ch y0 stmh sknh;
		  output_string ch "</span> as 0 and forming successors with <span class='ltree'>";
		  output_name_whref_html ch yS stmh sknh;
		  output_string ch "</span>."
	      | _ ->
		  raise (Failure("Bad Nat notation"))
	    end
	| "SetLam" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "<span class='ltree'>&#x03bb; <i>x</i> &#x2208; <i>A</i> &#x21d2; <i>B</i></span> is notation for the set <span class='ltree'>";
		  output_name_whref_html ch y stmh sknh;
		  output_string ch " <i>A</i> (&#x03bb; <i>x</i> : set &#x21d2; <i>B</i>)</span>.";
	      | _ ->
		  raise (Failure("Bad SetLam notation"))
	    end
	| "SetImplicitOp" ->
	    begin
	      match yl with
	      | [y] ->
		  output_string ch "When <span class='ltree'><i>x</i></span> is a set, a term <span class='ltree'><i>x</i> <i>y</i></span> is notation for <span class='ltree'>";
		  output_name_whref_html ch y stmh sknh;
		  output_string ch " <i>x</i> <i>y</i></span>.";
	      | _ ->
		  raise (Failure("Bad SetImplicitOp notation"))
	    end
	| _ -> raise (Failure("Unknown notation " ^ x))
      end;
      output_string ch "</div>\n";
  | UnicodeDecl(x,ul) -> ()
  | SuperscriptDecl(x) -> (*** I should say something about notation here, but at the moment it would need to be "If x is a binder, then we write its bound variables as a superscript. If x is an infix operator, then we omit the operator and write the second argument as a superscript." ***)
      ()
  | SubscriptDecl(x) -> (*** I should say something about notation here, but at the moment it would need to be "If x is a binder, then we write its bound variables as a subscript. If x is an infix operator, then we omit the operator and write the second argument as a subscript." ***)
      ()
  | RequireDecl(x) ->
      output_string ch "\nRequire \n";
      output_string ch x;
      output_string ch "<br/>\n";
  | ParamDecl(x,a) ->
      output_string ch "\n$\n";
      output_string ch "<a name='";
      output_string ch (url_friendly_name x);
      output_string ch x;
      output_string ch "'/>";
      output_string ch "<div class='paramdecl'><b>Primitive</b>. The name <span class='ltree'>";
      output_name_whrefa_html ch x stmh sknh;
      output_string ch "</span> is a term of type <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span>.</div>\n";
      begin
	if x = "In" then
	  begin
	    output_string ch "<div class='infixdecl'><b>Notation</b>. We use <span class='ltree'>&#x2208;</span>";
	    output_string ch "</span> as an infix operator with priority 500";
	    output_string ch " and no associativity";
	    output_string ch " corresponding to applying term <span class='ltree'>";
	    output_name_whrefa_html ch x stmh sknh;
	    output_string ch "</span>. Furthermore, we may write <span class='ltree'>&#x2200; <I>x</I> &#x2208; <I>A</I>, <I>B</I></span> to mean <span class='ltree'>&#x2200; <I>x</I> : ";
	    output_name_whrefa_html ch "set" stmh sknh;
	    output_string ch ", <I>x</I> &#x2208; <I>A</I> &#x2192; <I>B</I></span>.</div>\n";
	  end
      end;
      begin
	if x = "Subq" then
	  begin
	    output_string ch "<div class='infixdecl'><b>Notation</b>. We use <span class='ltree'>&#x2286;</span>";
	    output_string ch "</span> as an infix operator with priority 500";
	    output_string ch " and no associativity";
	    output_string ch " corresponding to applying term <span class='ltree'>";
	    output_name_whrefa_html ch x stmh sknh;
	    output_string ch "</span>. Furthermore, we may write <span class='ltree'>&#x2200; <I>x</I> &#x2286; <I>A</I>, <I>B</I></span> to mean <span class='ltree'>&#x2200; <I>x</I> : ";
	    output_name_whrefa_html ch "set" stmh sknh;
	    output_string ch ", <I>x</I> &#x2286; <I>A</I> &#x2192; <I>B</I></span>.</div>\n";
	  end
      end
  | ParamHash(x,h) -> ()
  | DefDecl(x,None,a) ->
      output_string ch "\n$\n";
      output_string ch "<a name='";
      output_string ch (url_friendly_name x);
      output_string ch "'/>";
      output_string ch "<div class='defdecl'><b>Definition.</b> We define <span class='ltree'>";
      output_name_whrefa_html ch x stmh sknh;
      output_string ch "</span> to be <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span>.</div>\n";
      begin
	if x = "Subq" then
	  begin
	    output_string ch "<div class='infixdecl'><b>Notation</b>. We use <span class='ltree'>&#x2286;</span>";
	    output_string ch "</span> as an infix operator with priority 500";
	    output_string ch " and no associativity";
	    output_string ch " corresponding to applying term <span class='ltree'>";
	    output_name_whrefa_html ch x stmh sknh;
	    output_string ch "</span>. Furthermore, we may write <span class='ltree'>&#x2200; <I>x</I> &#x2286; <I>A</I>, <I>B</I></span> to mean <span class='ltree'>&#x2200; <I>x</I> : ";
	    output_name_whrefa_html ch "set" stmh sknh;
	    output_string ch ", <I>x</I> &#x2286; <I>A</I> &#x2192; <I>B</I></span>.</div>\n";
	  end
      end
  | DefDecl(x,Some b,a) ->
      output_string ch "\n$\n";
      output_string ch "<a name='";
      output_string ch (url_friendly_name x);
      output_string ch "'/>";
      output_string ch "<div class='defdecl'><b>Definition.</b> We define <span class='ltree'>";
      output_name_whrefa_html ch x stmh sknh;
      output_string ch "</span> to be <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span> of type <span class='ltree'>";
      output_ltree_html ch b stmh sknh;
      output_string ch "</span>.</div>\n";
      begin
	if x = "Subq" then
	  begin
	    output_string ch "<div class='infixdecl'><b>Notation</b>. We use <span class='ltree'>&#x2286;</span>";
	    output_string ch "</span> as an infix operator with priority 500";
	    output_string ch " and no associativity";
	    output_string ch " corresponding to applying term <span class='ltree'>";
	    output_name_whrefa_html ch x stmh sknh;
	    output_string ch "</span>. Furthermore, we may write <span class='ltree'>&#x2200; <I>x</I> &#x2286; <I>A</I>, <I>B</I></span> to mean <span class='ltree'>&#x2200; <I>x</I> : ";
	    output_name_whrefa_html ch "set" stmh sknh;
	    output_string ch ", <I>x</I> &#x2286; <I>A</I> &#x2192; <I>B</I></span>.</div>\n";
	  end
      end
  | AxDecl(x,a) ->
      output_string ch "\n$\n";
      output_string ch "<a name='";
      output_string ch (url_friendly_name x);
      output_string ch "'/>";
      output_string ch "<div class='axdecl'><b>Axiom.</b> (<span class='ltree'>";
      output_name_whrefa_html ch x stmh sknh;
      output_string ch "</span>) We take the following as an axiom:\n<div class='axiomprop'><span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span></div></div>\n";
  | ThmDecl(c,x,a) ->
      output_string ch "\n$\n";
      output_string ch "<a name='";
      output_string ch (url_friendly_name x);
      output_string ch "'/>";
      output_string ch "<div class='thmandproof'><div class='thmdecl'><b>";
      output_string ch c;
      output_string ch ".</b> (<span class='ltree'>";
      output_name_whrefa_html ch x stmh sknh;
      output_string ch "</span>) The following is provable: <div class='thmprop'><span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span></div></div>\n";
      incr thmcount;
      Buffer.reset pftext;
      Printf.fprintf ch "<div id='pf%d' class='proof'><div class='proofpres' onclick='g(this)'><b>Proof:</b><br/>" !thmcount

let text_row_col txt =
  let nli = ref 1 in
  let nch = ref 0 in
  let maxch = ref 0 in
  for i = 0 to String.length txt - 1 do
    let c = txt.[i] in
    if c = '\n' then
      (incr nli; nch := 0)
    else
      (incr nch; maxch := max !maxch !nch)
  done;
  (!nli,!maxch)

let output_pftacitem_html ch pftac stmh sknh laststructact =
  match pftac with
  | PfStruct i when i < 4 ->
      if laststructact = 1 then
	output_string ch "<div class='subproof'>"
      else if laststructact = 2 then
	output_string ch "</div>\n<div class='subproof'>"
      else if laststructact = 3 then
	output_string ch "</div>\n";
  | PfStruct 4 -> output_string ch "<div class='subproof'>";
  | PfStruct 5 -> output_string ch "</div>";
  | PfStruct _ -> ()
  | Exact(a) ->
      output_string ch "<div class='exact'>An <span class='pftackeyword'>exact</span> proof term for the current goal is <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span>.</div>\n"
  | LetTac(xl,None) ->
      output_string ch "<div class='lettac'><span class='pftackeyword'>Let</span> <span class='ltree'>";
      output_comma_names_html ch xl;
      output_string ch "</span> be given.</div>\n"
  | LetTac(xl,Some a) ->
      output_string ch "<div class='lettac'><span class='pftackeyword'>Let</span> <span class='ltree'>";
      output_comma_names_html ch xl;
      output_string ch "</span> of type <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span> be given.</div>\n"
  | SetTac(x,None,a) ->
      output_string ch "<div class='settac'><span class='pftackeyword'>Set</span> <span class='ltree'>";
      output_string ch x;
      output_string ch "</span> to be the term <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span>.</div>\n"
  | SetTac(x,Some(b),a) ->
      output_string ch "<div class='settac'><span class='pftackeyword'>Set</span> <span class='ltree'>";
      output_string ch x;
      output_string ch "</span> to be the term <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span> of type <span class='ltree'>";
      output_ltree_html ch b stmh sknh;
      output_string ch "</span>.</div>\n"
  | AssumeTac(xl,None) ->
      output_string ch "<div class='assumetac'><span class='pftackeyword'>Assume</span> <span class='ltree'>";
      output_names_html ch xl;
      output_string ch "</span>.</div>\n"
  | AssumeTac(xl,Some a) ->
      output_string ch "<div class='assumetac'><span class='pftackeyword'>Assume</span> <span class='ltree'>";
      output_names_html ch xl;
      output_string ch "</span>: <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span>.</div>\n"
  | ApplyTac(a) ->
      output_string ch "<div class='applytac'><span class='pftackeyword'>Apply</span> <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span> to the current goal.</div>\n"
  | ClaimTac(x,a) ->
      output_string ch "<div class='claimtac'>We prove the intermediate <span class='pftackeyword'>claim</span> <span class='ltree'>";
      output_name_html ch x;
      output_string ch "</span>: <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span>.</div>\n"
  | ProveTac(a,bl) ->
      output_string ch "<div class='provetac'>We will <span class='pftackeyword'>prove</span> ";
      output_ltree_html ch a stmh sknh;
      List.iter (fun b ->
	output_string ch ", <span class='ltree'>";
	output_ltree_html ch b stmh sknh;
	output_string ch "</span>")
	bl;
      output_string ch ".</div>\n"
  | CasesTac(a,cl) ->
      raise (Failure("Cases tactic not yet implemented"))
  | WitnessTac(a) ->
      output_string ch "<div class='witnesstac'>We use <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span> to <span class='pftackeyword'>witness</span> the existential quantifier.</div>\n";
  | RewriteTac(s,a,il) ->
      output_string ch "<div class='rewritetac'><span class='pftackeyword'>rewrite</span> the current goal using <span class='ltree'>";
      output_ltree_html ch a stmh sknh;
      output_string ch "</span>";
      if s then
	output_string ch " (from right to left)"
      else
	output_string ch " (from left to right)";
      begin
	match il with
	| [] -> ()
	| [i] ->
	    output_string ch " at position ";
	    output_string ch (string_of_int i);
	| (i::j::kl) ->
	    output_string ch " at positions ";
	    let rec posl i j kl =
	      match kl with
	      | k::kr ->
		  output_string ch (string_of_int i);
		  output_string ch ", ";
		  posl j k kr
	      | [] ->
		  output_string ch (string_of_int i);
		  output_string ch " and ";
		  output_string ch (string_of_int j)
	    in
	    posl i j kl
      end;
      output_string ch ".</div>\n"
  | Qed ->
      output_string ch "&#x220e;\n";
      Printf.fprintf ch "</div><div id='pf%dcode' class='proofcodehidden'>\n" !thmcount;
      Printf.fprintf ch "<input type='hidden' id='pf%dcodeline' value='%d'/><input type='hidden' id='pf%dcodechar' value='%d'/>\n" !thmcount !pflinestart !thmcount !pfcharstart;
      if (String.length !currtmid > 0) then (Printf.fprintf ch "<input type='hidden' id='pf%dcodetmid' value='%s'/>\n" !thmcount !currtmid; currtmid := "");
      let pftxt = Buffer.contents pftext in
      let (rowcount,colcount) = text_row_col pftxt in
      Printf.fprintf ch "<textarea id='pf%dcodetext' rows=%d cols=%d>%s</textarea><br/><input type='button' value='Recheck' onclick='h(this)'/>\n" !thmcount rowcount colcount pftxt;
      Printf.fprintf ch "<div id='pf%dcoderesp' class='proofcoderesp'/></div>" !thmcount;
      output_string ch "</div></div></div>\n"
  | Admitted ->
      if laststructact < 0 then
	begin
	  output_string ch "<div class='admitted'>The proof is left to the reader.</div>\n";
	  Printf.fprintf ch "</div><div id='pf%dcode' class='proofcodehidden'>\n" !thmcount;
	  Printf.fprintf ch "<input type='hidden' id='pf%dcodeline' value='%d'/><input type='hidden' id='pf%dcodechar' value='%d'/>\n" !thmcount !pflinestart !thmcount !pfcharstart;
	  if (String.length !currtmid > 0) then (Printf.fprintf ch "<input type='hidden' id='pf%dcodetmid' value='%s'/>\n" !thmcount !currtmid; currtmid := "");
	  Printf.fprintf ch "<textarea id='pf%dcodetext' rows=5 cols=80></textarea><br/><input type='button' value='Check' onclick='h(this)'/>\n" !thmcount; (*** just leave this one blank instead of just putting 'Admitted' ***)
	  Printf.fprintf ch "<div id='pf%dcoderesp' class='proofcoderesp'/></div>" !thmcount;
	  output_string ch "</div></div></div>\n"
	end
      else
	begin
	  output_string ch "<div class='admitted'>The rest of the proof is left to the reader.</div>\n";
	  Printf.fprintf ch "</div><div id='pf%dcode' class='proofcodehidden'>\n" !thmcount;
	  Printf.fprintf ch "<input type='hidden' id='pf%dcodeline' value='%d'/><input type='hidden' id='pf%dcodechar' value='%d'/>\n" !thmcount !pflinestart !thmcount !pfcharstart;
	  if (String.length !currtmid > 0) then (Printf.fprintf ch "<input type='hidden' id='pf%dcodetmid' value='%s'/>\n" !thmcount !currtmid; currtmid := "");
	  let pftxt = Buffer.contents pftext in
	  let (rowcount,colcount) = text_row_col pftxt in
	  Printf.fprintf ch "<textarea id='pf%dcodetext' rows=%d cols=%d>%s</textarea><br/><input type='button' value='Check' onclick='h(this)'/>\n" !thmcount rowcount colcount pftxt;
	  Printf.fprintf ch "<div id='pf%dcoderesp' class='proofcoderesp'/></div>" !thmcount;
	  output_string ch "</div></div></div>\n"
	end
  | Admit ->
      output_string ch "<div class='admit'>The rest of this subproof is left to the reader.</div>"

let rec stp_html_string_1 a p =
  match a with
  | TpVar 0 -> "&#x3b1;"
  | TpVar 1 -> "&#x3b2;"
  | TpVar 2 -> "&#x3b3;"
  | TpVar i -> raise (Failure("bad type var"))
  | Set -> "set"
  | Prop -> "prop"
  | Ar(b,c) when p -> "(" ^ stp_html_string_1 b true ^ " &#x2192; " ^ stp_html_string_1 c false ^ ")"
  | Ar(b,c) -> stp_html_string_1 b true ^ " &#x2192; " ^ stp_html_string_1 c false
      
let stp_html_string a = stp_html_string_1 a false
