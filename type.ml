(*
    Copyright (C) 2018 Richard Bornat
     
        richard@bornat.me.uk

    This file is part of Qtpi, an interpreter for Gay and Nagarajan's CQP.

    Qtpi is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    Qtpi is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Qtpi in the file LICENSE; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
    (or look at http://www.gnu.org).
*)

open Settings
open Sourcepos
open Name
open Stringutils
open Listutils
open Functionutils
open Instance

exception Error of sourcepos * string

type _type = tnode instance

(* at present I can't find any simpler way to distinguish singleton Qubit and multiple Qubits than to have two types. *)
(* string is now [char], as in Miranda, but the parser still recognises the string word *)

and tnode =
  | Unit
  | Num
  | Bool
  | Char
  | Bit
  | Sxnum
  | Qubit    
  | Qubits    
  | Qstate
  | Bra
  | Ket
  | Gate                            (* arity is no longer a static property, because of multiplication *)
  | Matrix                          (* Gate is a square unitary Matrix; matrices can be calculated *)
  | Unknown of unknown         
  | Known   of uname                (* knowns start with '\'', which doesn't appear in parseable names *)
  | Poly    of uname list * _type   (* oh dear this could be Poly of Poly ... would that be ok? *)
(*| Range   of int * int *)
  | List    of _type
  | Tuple   of _type list
  | Channel of _type                (* cos if it's _type list, as in tuple, then typechecking is harder *)
  | Fun     of _type * _type
  | Process of _type list

and unknown = uname * _type option ref (* unknowns start with '?', which doesn't appear in parseable names *)
and uname = string * ukind             

and 'a typedinstance = 'a tinst instance

and 'a tinst = {toptr: _type option ref; tinst: 'a}

and ukind = 
  | UnkAll              (* anything *)
  | UnkEq               (* equality: can't have qubit, qstate, channel, function, process (or value containing etc.) *)
  | UnkClass of bool    (* classical: can't have qubit or value containing qubit.
                           boolean says whether is alt (true) or functional (false) restriction
                         *)
  | UnkComm             (* simply a qubit, or classical *)


let twrap opt tinst = {toptr=ref opt; tinst=tinst}
let tadorn pos = adorn pos <.> twrap None

let tinst x = x.inst.tinst
let toptr x = x.inst.toptr

let type_of_typedinstance x =
  match !(toptr x) with
  | Some t -> t
  | None   -> raise (Error (x.pos, "(Type.type_of_typedinstance) typecheck didn't mark something"))

type typedname = name typedinstance

let name_of_typedname = tinst

let string_of_typedname n = string_of_name (tinst n) 

let type_of_typedname n = 
  try type_of_typedinstance n
  with _ -> raise (Error (n.pos, Printf.sprintf "(Type.type_of_typedname) typecheck didn't mark %s" (string_of_typedname n)))

let processprio = 0 (* lower than tuple, channel, function *)
let funprio = 1     (* lower than tuple *)
let chanprio = 2
let primaryprio = 10

let typeprio t = 
  match t.inst with  
  | Num 
  | Bool
  | Char
  | Bit         
  | Unit
  | Sxnum
  | Qubit   
  | Qubits   
  | Qstate
  | Bra
  | Ket
  | Gate     
  | Matrix
  | Unknown _ 
  | Known   _ 
(*| Range   _ *) 
  | Poly    _       -> primaryprio
  | List    _       -> primaryprio
  | Tuple   _       -> primaryprio
  | Channel _       -> chanprio
  | Fun     _       -> funprio
  | Process _       -> processprio
  
let delist = function
  | []  -> Unit
  | [t] -> t.inst
  | ts  -> Tuple ts

let relist t =
  match t.inst with
  | Unit     -> [] 
  | Tuple ts -> ts
  | _        -> [t]
  
let rec string_of_type t = string_of_tnode t.inst

and string_of_tnode = function
  | Num              -> "num"
  | Bit              -> "bit"
  | Char             -> "char"
  | Bool             -> "bool"
  | Unit             -> "()"
  | Sxnum            -> "sxnum"
  | Qubit             -> "qubit" 
  | Qubits            -> "qubits" 
  | Qstate           -> "qstate"
  | Bra              -> "bra"
  | Ket              -> "ket"
  | Gate             -> "gate"
  | Matrix           -> "matrix"
  | Unknown (_, {contents=Some t})   
                     -> string_of_type t
  | Unknown (n, _)   -> (*"Unknown " ^*) "?" ^ string_of_uname n
  | Known   n        -> (*"Known " ^*) "'" ^ string_of_uname n
  | Poly    (ns,ut)  -> let nstrings = List.map string_of_uname ns in
                        Printf.sprintf "forall %s.%s" (String.concat "," nstrings) (string_of_type ut)
(*| Range   (l,h)    -> Printf.sprintf "%s..%s" (string_of_int l) (string_of_int h) *)
  | List    t        -> if t.inst=Char then "string" else Printf.sprintf "[%s]" (string_of_type t)
  | Tuple   ts       -> "(" ^ string_of_list string_of_type "," ts ^ ")"
  | Channel t        -> Printf.sprintf "^%s" (possbracket false chanprio t)
  | Fun     (t1,t2)  -> Printf.sprintf "%s→%s"
                                       (possbracket true funprio t1)
                                       (possbracket false funprio t2)
  | Process ts       -> Printf.sprintf "%s process" (string_of_tnode (delist ts))

and string_of_uname (n,k) = (* unknowns are transparent *)
  (match k with
  | UnkEq      -> "'"
  | UnkAll     -> "*"
  | UnkComm    -> "^"
  |UnkClass _  -> "") ^ n 

and possbracket ifeq supprio t = 
  possbracket' ifeq supprio (typeprio t) (string_of_type t)
  
and possbracket' ifeq supprio subprio substring =
  if subprio<supprio || (ifeq && subprio=supprio) 
  then Printf.sprintf "(%s)" substring
  else substring

(* we need exists and I don't know what else. Should have had it ages ago *)
let exists : (_type -> bool) -> _type -> bool = fun p t ->
  let optp t = if p t then Some () else None in
  let rec ee : _type -> bool = fun t ->
    match optp t with
    | Some _ -> true
    | _      -> match t.inst with
                | Unit
                | Num
                | Bool
                | Char
                | Bit
                | Sxnum
                | Qubit    
                | Qubits    
                | Qstate
                | Bra
                | Ket
                | Gate                            
                | Matrix                          
                | Unknown _          
                | Known   _                 
                | Poly    _         -> false  
                | List    t     
                | Channel t         -> ee t             
                | Tuple   ts    
                | Process ts        -> List.exists ee ts
                | Fun     (t1,t2)   -> List.exists ee [t1;t2]
  in
  ee t
  
module OrderedUname = struct type t = uname 
                        let compare (n1,_) (n2,_) = Stdlib.compare n1 n2 
                        let to_string = string_of_uname
                      end
module UnameSet = MySet.Make(OrderedUname)

let rec freetvs t = 
  let rec _freetvs s t = 
    match t.inst with
    | Num
    | Bool
    | Char
    | Bit 
    | Unit
    | Sxnum
    | Qubit               
    | Qubits               
    | Qstate
    | Bra
    | Ket
  (*| Range   _ *)
    | Gate            
    | Matrix                -> s
    | Unknown (_, {contents=Some t'})    
                            -> _freetvs s t'      
    | Unknown (u, _)        -> UnameSet.add u s      
    | Known   u             -> UnameSet.add u s 
    | Poly    (us,t)        -> let vs = freetvs t in UnameSet.union s (UnameSet.diff vs (UnameSet.of_list us))
    | Channel t   
    | List    t             -> _freetvs s t  
    | Process ts   
    | Tuple   ts            -> List.fold_left _freetvs s ts
    | Fun     (t1,t2)       -> _freetvs (_freetvs s t1) t2
  in
  _freetvs UnameSet.empty t

let freeunknowns t = 
  let rec _freeuks s t = 
    match t.inst with
    | Num
    | Bool
    | Char
    | Bit 
    | Unit
    | Sxnum
    | Qubit     
    | Qubits     
    | Qstate
    | Bra
    | Ket
  (*| Range   _ *)
    | Gate            
    | Matrix          -> s
    | Unknown (_, {contents=Some t'})    
                      -> _freeuks s t'      
    | Unknown (u, _)  -> UnameSet.add u s      
    | Known   _       -> s 
    | Poly    (ns,t)  -> raise (Invalid_argument ("freeunknowns " ^ string_of_type t))
    | Channel t   
    | List    t       -> _freeuks s t  
    | Process ts   
    | Tuple   ts      -> List.fold_left _freeuks s ts
    | Fun     (t1,t2) -> _freeuks (_freeuks s t1) t2
  in
  _freeuks UnameSet.empty t

let kind_of_uname (n,k) = k

let string_of_ukind = function
  | UnkAll       -> "(any type)"
  | UnkEq        -> "(equality type)"
  | UnkClass b   -> "(classical type" ^ (if b then " from alt" else "") ^ ")"
  | UnkComm      -> "(qubit or classical)"
  
let new_unknown = (* hide the count *)
  (let ucount = ref 0 in
   let new_unknown uk = 
     let n = !ucount in
     ucount := n+1;
     (string_of_int n, uk), ref None
   in
   new_unknown
  )

(* 
   Eq(ality)       < Class(ical)     (because Class includes functions)
   Class(ical)     < Comm(unication) (because Comm includes single qubits)
   Comm(unication) < All             (because All allows qubits in lists and tuples, heaven forbid)
   
   We require that functional values are classical, and so cannot have free qubit variables.
   This means restrictions on function definitions, 
   and restrictions on partial applications -- f q is non-classical if q is a qubit.
   
   But library functions can take non-classical arguments (at least show and qstate), so 
   function calls can take non-classical arguments.
 *)
 
let kind_includes k1 k2 =
  if k1=k2 then true else
  match k1, k2 with
  | UnkAll       , _                -> true
  | _            , UnkAll           -> false
  | UnkComm      , _                -> true
  | _            , UnkComm          -> false
  | UnkClass true, UnkClass false   -> false (* has to be the other way round *) 
  | UnkClass _   , _                -> true
  | _                               -> false
  
(* a service to the parser *)
let uname_of_string s =
  let rest () = String.sub s 1 (String.length s - 1) in
  match s.[1] with
  | '\'' -> rest (), UnkEq
  | '*'  -> rest (), UnkAll
  | '^'  -> rest (), UnkComm
  | _    -> s, UnkClass false


let result_type pos pars ft =
  let bad () = raise (Can'tHappen (Printf.sprintf "%s: result_type (%d) %s"
                                                  (string_of_sourcepos pos)
                                                  (List.length pars)
                                                  (string_of_type ft)
                                  )
                     )
  in
  let rec rt pars t =
    match pars, t.inst with
    | []     , _           -> t
    | _::pars, Fun (ta,tr) -> rt pars tr
    | _                    -> bad ()
  in
  match ft.inst with
  | Poly (_,t) -> rt pars t
  | _          -> rt pars ft
  
(* not very clever this: ought to go 'a, 'b, 'c etc. *)
(* but it's too hard to fix, so sorry *)
(* and it's inefficient, but it doesn't matter *)
let generalise t0 = 
  let rec unknown_to_known t = 
   let replace tnode = {pos=t.pos; inst=tnode} in
   match t.inst with
    | Num
    | Bool
    | Char
    | Bit
    | Unit
    | Sxnum
    | Qubit     
    | Qubits     
    | Qstate
    | Bra
    | Ket
  (*| Range   _ *)
    | Gate              
    | Matrix            -> t
    | Unknown (_, {contents=Some t'})  
                        -> replace (unknown_to_known t').inst  
    | Unknown (u, _)    -> (* let n' = String.concat "" ["'"; String.sub n 1 (String.length n - 1)] in *)
                           replace (Known u)
    | Known   _         -> t
    | Poly    _         -> raise (Invalid_argument ("Type.generalise polytype " ^ string_of_type t0))
    | List    t         -> replace (List (unknown_to_known t))  
    | Channel t         -> replace (Channel (unknown_to_known t))
    | Process ts        -> replace (Process (List.map unknown_to_known ts))
    | Tuple   ts        -> replace (Tuple (List.map unknown_to_known ts))
    | Fun     (t1,t2)   -> replace (Fun (unknown_to_known t1, unknown_to_known t2))
  in
  let t = unknown_to_known t0 in
  let nset = freetvs t in
  if UnameSet.is_empty nset then t 
  else adorn t.pos (Poly(UnameSet.elements nset,t))

let instantiate t =
  let rec rename assoc t = 
    let replace tnode = {pos=t.pos; inst=tnode} in
    match t.inst with
    | Num
    | Bool
    | Char
    | Bit
    | Unit
    | Sxnum
    | Qubit     
    | Qubits     
    | Qstate
    | Bra
    | Ket
  (*| Range   _ *)
    | Gate            
    | Matrix          -> t
    | Known u         -> replace (let u' = assoc<@>u in Unknown u') 
    | Unknown _       
    | Poly    _       -> raise (Invalid_argument ("Type.rename " ^ string_of_type t))
    | List    t       -> replace (List (rename assoc t))   
    | Channel t       -> replace (Channel (rename assoc t))
    | Process ts      -> replace (Process (List.map (rename assoc) ts))
    | Tuple   ts      -> replace (Tuple (List.map (rename assoc) ts))
    | Fun     (t1,t2) -> replace (Fun (rename assoc t1, rename assoc t2))
  in
  match t.inst with
  | Poly (ns, t)  -> let newns = List.map (fun n -> new_unknown (kind_of_uname n)) ns in
                     (try rename (zip ns newns) t
                      with Zip -> raise (Invalid_argument ("Type.instantiate " ^ string_of_type t))
                     )
  | _             -> t

(* a service to compilation of monitor processes *)
let rec is_classical t =
  let is_cu k = (match k with UnkClass _ |  UnkEq -> true | _ -> false) in
  match t.inst with
  | Qubit                  
  | Qubits           -> false            
  | Unit          
  | Num 
  | Bool
  | Char
  | Bit
  | Sxnum
  | Bra
  | Ket
  | Gate            
  | Matrix          -> true
  | Qstate          -> true    (* really *)
  (* | Range   _ *)
  | Unknown (_, {contents=Some t})    
                      -> is_classical t       
  | Unknown ((_, k), _) -> is_cu k      
  | Known   (_, k)     (* can happen in Poly ... *)       
                    -> is_cu k
  | Poly    (_, t)  -> is_classical t 
  | List    t       -> is_classical t 
  | Channel t       -> is_classical t
  | Tuple   ts      -> List.for_all is_classical ts
  | Fun     (t1,t2) -> true (* yes *)
                     
  | Process _       -> true (* yes? *)

(* a service to compilation of 'compare' and 'show' *)
let is_just_polytype t =
  match t.inst with
  | Unknown _       
  | Known   _         
  | Poly    _   -> true
  | _           -> false
                     
let is_polytype = exists is_just_polytype