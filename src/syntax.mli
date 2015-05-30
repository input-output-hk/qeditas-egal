(* Copyright (c) 2014 Chad E Brown *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(*** File: syntax.ml ***)
(*** Chad E. Brown ***)
(*** Jan 18 2014 ***)

open Big_int

val currtmid : string ref
val thmcount : int ref
val pflinestart : int ref
val pfcharstart : int ref
val pftext : Buffer.t
val polyexpand : bool ref

type tp = TpVar of int | Prop | Set | Ar of tp * tp

val notpvarsp : tp -> bool

(*** assume number of type variables is between 0 and 3 ***)
type ptp = int * tp

val primname : string -> int * ptp

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

open Big_int

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

val binderishp : ltree -> bool

val output_ltree : out_channel -> ltree -> unit

val ltree_to_atree : ltree -> atree

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

val tp_to_str : tp -> string
val tm_to_str : tm -> string
val pf_to_str : pf -> string

val tp_to_ser : tp -> string
val ser_to_tp : string -> tp
val ptp_to_ser : ptp -> string
val ser_to_ptp : string -> ptp
(***
val output_tp:out_channel -> tp -> unit
val input_tp:in_channel -> tp
val input_tp_and_ser:in_channel -> tp * string
***)
val tm_to_ser : tm -> string
val ser_to_tm : string -> tm
val ptm_to_ser : ptm -> string
val ser_to_ptm : string -> ptm
(***
val output_tm:out_channel -> tm -> unit
val input_tm:in_channel -> tm
val input_tm_and_ser:in_channel -> tm * string
***)
val pf_to_ser : pf -> string
val ser_to_pf : string -> pf
val ppf_to_ser : ppf -> string
val ser_to_ppf : string -> ppf
(***
val output_pf:out_channel -> pf -> unit
val input_pf:in_channel -> pf
val input_pf_and_ser:in_channel -> pf * string
***)

val position : 'a list -> 'a -> int

val tpsubst : tp -> tp list -> tp
val tmtpsubst : tm -> tp list -> tm
val pftpsubst : pf -> tp list -> pf

val tplookup : string list -> string -> tp
val tmlookup : (string * (tp * tm option)) list -> string -> tm
val tmtplookup : (string * (tp * tm option)) list -> string -> tm * tp
val pflookup : (string * tm) list -> string -> pf
val pfproplookup : (string * tm) list -> string -> pf * tm

val beta_count : int option ref
val beta_count_check : unit -> unit

exception NegDB
val tmshift : int -> int -> tm -> tm
val pfshift : int -> int -> pf -> pf
val pftmshift : int -> int -> pf -> pf
val tmsubst : tm -> int -> tm -> tm
(***
val tmssub : tm -> (int -> tm) -> tm
***)

val extr_tpoftm : (string,ptp) Hashtbl.t -> tp list -> tm -> tp
val check_tpoftm : (string,ptp) Hashtbl.t -> tp list -> tm -> tp -> unit

val extr_propofpf : (string,ptm) Hashtbl.t -> (string,ptp) Hashtbl.t -> tp list -> tm list -> pf -> string list -> tm * string list
val check_propofpf : (string,ptm) Hashtbl.t -> (string,ptp) Hashtbl.t -> tp list -> tm list -> pf -> tm -> string list -> string list option

(*** conv m n del returns None if m and n are not convertible and returns Some(dl) where dl is a list of global definitions that were expanded if they are convertible ***)
val conv : tm -> tm -> (string,ptm) Hashtbl.t -> string list -> string list option
val headnorm : tm -> (string,ptm) Hashtbl.t -> string list -> tm * string list
val tm_beta_eta_norm : tm -> tm

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

val mtm_to_str : mtm -> string
val tm_to_mtm : tm -> mtm
val mtm_to_tm : mtm -> tm
val mtm_shift : int -> int -> mtm -> mtm
val mtm_ssub : mtm list -> mtm -> mtm
val mtm_msub : (int -> mtm) -> mtm -> mtm
val mtm_minap_db : mtm -> int -> int option
val mtm_lammvar_p : mtm -> bool
val mtm_betared_if : mtm -> (mtm -> mtm -> bool) -> mtm
val pattern_match : (string,ptm) Hashtbl.t -> mtm -> tm -> (int -> mtm) -> (int -> mtm)
val mheadnorm : mtm -> (string,ptm) Hashtbl.t -> string list -> mtm * string list

val valid_id_p : string -> bool

val tp_id : tp -> string
val ptp_id : ptp -> string
val tm_id : tm -> (string,ptp) Hashtbl.t -> (string,ptm) Hashtbl.t -> string
val ptm_id : ptm -> (string,ptp) Hashtbl.t -> (string,ptm) Hashtbl.t -> string
val pf_id : pf -> (string,ptp) Hashtbl.t -> (string,ptm) Hashtbl.t -> string
val ppf_id : ppf -> (string,ptp) Hashtbl.t -> (string,ptm) Hashtbl.t -> string

val tp_args_rtp : tp -> tp list * tp
val mk_forall_tm : tp list -> (tm -> tm -> tm) -> tm -> tm -> tm
val mk_gen_ap : tm -> tm list -> tm

val unicode : (string,string list) Hashtbl.t
val subscript : (string,unit) Hashtbl.t
val superscript : (string,unit) Hashtbl.t
val authors : string list ref
val title : string option ref
val signature : string option ref
val showproofterms : bool ref
val salt : string option ref
val treasure : string option ref

val id_to_btcprivkey : string -> big_int

val pf_complexity : pf -> int

val output_ltree_html : out_channel -> ltree -> (string,string) Hashtbl.t -> (string,string) Hashtbl.t -> unit
val output_docitem_html : out_channel -> docitem -> (string,string) Hashtbl.t -> (string,string) Hashtbl.t -> unit
val output_pftacitem_html : out_channel -> pftacitem -> (string,string) Hashtbl.t -> (string,string) Hashtbl.t -> int -> unit

val stp_html_string : tp -> string

val flush_bits_sb : Buffer.t * (int * 'a) option -> unit
val output_bit_sb : int -> Buffer.t * (int * int) option -> Buffer.t * (int * int) option
