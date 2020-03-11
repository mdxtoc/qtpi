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

and tnode =
  | Unit
  | Num
  | Bool
  | Char
  | String
  | Bit 
  | Qbit
  | Qstate
  | Bra
  | Ket
  | Gate                            (* arity is no longer a static property, because of multiplication *)
  | Matrix                          (* Gate is a square unitary Matrix; matrices can be calculated *)
  | Unknown of unknown          
  | Known   of name                 (* knowns start with '\'', which doesn't appear in parseable names *)
  | OneOf   of unknown * _type list (* constrained unknown, for overloading *)
                                    (* and the typechecker won't work unless those are straightforward types:
                                       no unknowns, no OneOfs.
                                     *)
                                    (* at the moment OneOf is used for Num and Gate and Matrix in arithmetic operations.
                                       This simpifies the treatment in typecheck and resource. If it gets
                                       used more, I shall have to think again.
                                     *)
  | Poly    of name list * _type    (* oh dear this could be Poly of Poly ... would that be ok? *)
(*| Range   of int * int *)
  | List    of _type
  | Tuple   of _type list
  | Channel of _type                (* cos if it's _type list, as in tuple, then typechecking is harder *)
  | Fun     of _type * _type
  | Process of _type list

and unknown = name * _type option ref (* unknowns start with '?', which doesn't appear in parseable names *)

and 'a typedinstance = 'a tinst instance

and 'a tinst = {toptr: _type option ref; tinst: 'a}

let twrap opt tinst = {toptr=ref opt; tinst=tinst}
let tadorn pos = adorn pos <.> twrap None

let tinst x = x.inst.tinst
let toptr x = x.inst.toptr

let type_of_typedinstance x =
  match !(toptr x) with
  | Some t -> t
  | None   -> raise (Error (x.pos, "(Type.type_of_typedinstance) typecheck didn't mark something"))

type typedname = name typedinstance

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
  | String
  | Bit           
  | Unit          
  | Qbit
  | Qstate
  | Bra
  | Ket
  | Gate     
  | Matrix
  | Unknown _ 
  | Known   _ 
  | OneOf   _
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
  | String           -> "string"
  | Bool             -> "bool"
  | Unit             -> "()"
  | Qbit             -> "qbit"
  | Qstate           -> "qstate"
  | Bra              -> "bra"
  | Ket              -> "ket"
  | Gate             -> "gate"
  | Matrix           -> "matrix"
  | Unknown (_, {contents=Some t})        -> string_of_type t
  | Unknown u                             -> (*"Unknown " ^*) string_of_unknown u
  | OneOf   ((_, {contents=Some t}), _)   -> string_of_type t
  | OneOf   (u,ts)                        -> (*"OneOf "^*) string_of_unknown u ^ "<" ^ bracketed_string_of_list string_of_type ts
  | Known   n        -> (*"Known " ^*) string_of_name n
  | Poly    (ns,ut)  -> let nstrings = List.map string_of_name ns in
                        Printf.sprintf "forall %s.%s" (String.concat "," nstrings) (string_of_type ut)
(*| Range   (l,h)    -> Printf.sprintf "%s..%s" (string_of_int l) (string_of_int h) *)
  | List    t        -> Printf.sprintf "[%s]" (string_of_type t)
  | Tuple   ts       -> "(" ^ string_of_list string_of_type "," ts ^ ")"
  | Channel t        -> Printf.sprintf "^%s" (possbracket false chanprio t)
  | Fun     (t1,t2)  -> Printf.sprintf "%s->%s"
                                       (possbracket true funprio t1)
                                       (possbracket false funprio t2)
  | Process ts       -> Printf.sprintf "%s process" (string_of_tnode (delist ts))

and string_of_unknown = function    (* unknowns are transparent *)
  | n, _                 -> string_of_name n

and possbracket ifeq supprio t = 
  possbracket' ifeq supprio (typeprio t) (string_of_type t)
  
and possbracket' ifeq supprio subprio substring =
  if subprio<supprio || (ifeq && subprio=supprio) 
  then Printf.sprintf "(%s)" substring
  else substring

let rec freetvs t = 
  let rec _freetvs s t = 
    match t.inst with
    | Num
    | Bool
    | Char
    | String
    | Bit 
    | Unit
    | Qbit 
    | Qstate
    | Bra
    | Ket
  (*| Range   _ *)
    | Gate            
    | Matrix                -> s
    | Unknown (_, {contents=Some t'})    
                            -> _freetvs s t'      
    | Unknown (n, _)        -> NameSet.add n s      
    | Known   n             -> NameSet.add n s 
    | OneOf   ((n, _), _)   -> NameSet.add n s
    | Poly    (ns,t)        -> let vs = freetvs t in NameSet.union s (NameSet.diff vs (NameSet.of_list ns))
    | Channel t   
    | List    t             -> _freetvs s t  
    | Process ts   
    | Tuple   ts            -> List.fold_left _freetvs s ts
    | Fun     (t1,t2)       -> _freetvs (_freetvs s t1) t2
  in
  _freetvs NameSet.empty t

module OrderedUnknown = struct type t = unknown let compare (n1,_) (n2,_) = Stdlib.compare n1 n2 let to_string = string_of_unknown end
module UnknownSet = MySet.Make(OrderedUnknown)

let freeunknowns t = 
  let rec _freeuks s t = 
    match t.inst with
    | Num
    | Bool
    | Char
    | String
    | Bit 
    | Unit
    | Qbit 
    | Qstate
    | Bra
    | Ket
  (*| Range   _ *)
    | Gate            
    | Matrix          -> s
    | Unknown (_, {contents=Some t'})    
                      -> _freeuks s t'      
    | Unknown u       -> UnknownSet.add u s      
    | Known   n       -> s 
    | OneOf   (u, _)  -> UnknownSet.add u s
    | Poly    (ns,t)  -> raise (Invalid_argument ("freeunknowns " ^ string_of_type t))
    | Channel t   
    | List    t       -> _freeuks s t  
    | Process ts   
    | Tuple   ts      -> List.fold_left _freeuks s ts
    | Fun     (t1,t2) -> _freeuks (_freeuks s t1) t2
  in
  _freeuks UnknownSet.empty t

type unknownkind = 
  | UnkAll       (* anything *)
  | UnkEq        (* equality: can't have qbit, qstate, channel, function, process (or value containing etc.) *)
  | UnkClass     (* classical: can't have qbit or value containing *)
  | UnkComm      (* simply a qbit, or classical *)

let string_of_unknownkind = function
  | UnkAll       -> "(any type)"
  | UnkEq        -> "(equality type)"
  | UnkClass     -> "(classical type)"
  | UnkComm      -> "(qbit or classical)"
  
let new_unknown = (* hide the reference *)
  (let ucount = ref 0 in
   let new_unknown uk = 
     let n = !ucount in
     ucount := n+1;
     (match uk with
     | UnkEq        -> "?'"
     | UnkClass     -> "?"
     | UnkComm      -> "?^"
     | UnkAll       -> "?*"
     ) ^ string_of_int n, 
     ref None
   in
   new_unknown
  )

(* 
   Eq(ality)       < Class(ical)     (because Class includes functions)
   Class(ical)     < Comm(unication) (because Comm includes single qbits)
   Comm(unication) < All             (because All allows qbits in lists and tuples, heaven forbid)
   
   We require that functional values are classical, and so cannot have free qbit variables.
   This means restrictions on function definitions, 
   and restrictions on partial applications -- f q is non-classical if q is a qbit.
   
   But I think functions can take non-classical arguments.
 *)
 
let kind_of_unknown n = 
  match n.[1] with
  | '\'' -> UnkEq
  | '*'  -> UnkAll
  | '^'  -> UnkComm
  | _    -> UnkClass

let kind_includes k1 k2 =
  if k1=k2 then true else
  match k1, k2 with
  | UnkAll    , _       -> true
  | _      , UnkAll     -> false
  | UnkComm, _       -> true
  | _      , UnkComm -> false
  | UnkClass, _      -> true
  | _                -> false
  
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
    | String
    | Bit 
    | Unit
    | Qbit 
    | Qstate
    | Bra
    | Ket
  (*| Range   _ *)
    | Gate              
    | Matrix            -> t
    | Unknown (n, {contents=Some t'})  
                        -> replace (unknown_to_known t').inst  
    | Unknown (n, _)    -> let n' = String.concat "" ["'"; String.sub n 1 (String.length n - 1)] in
                           replace (Known n')
    | Known   _         -> t
    | OneOf ((n, {contents=Some t'}),_)  
                        -> replace (unknown_to_known t').inst 
    | OneOf (_, ts)     -> raise (Error (t0.pos, Printf.sprintf "Cannot generalise type %s: ambiguity between %s" 
                                                                    (string_of_type t0)
                                                                    (Stringutils.phrase (List.map string_of_type ts))
                                        )
                                 )
    | Poly    _         -> raise (Invalid_argument ("Type.generalise polytype " ^ string_of_type t0))
    | List    t         -> replace (List (unknown_to_known t))  
    | Channel t         -> replace (Channel (unknown_to_known t))
    | Process ts        -> replace (Process (List.map unknown_to_known ts))
    | Tuple   ts        -> replace (Tuple (List.map unknown_to_known ts))
    | Fun     (t1,t2)   -> replace (Fun (unknown_to_known t1, unknown_to_known t2))
  in
  let t = unknown_to_known t0 in
  let nset = freetvs t in
  if NameSet.is_empty nset then t 
  else adorn t.pos (Poly(NameSet.elements nset,t))

let instantiate t =
  let rec rename assoc t = 
    let replace tnode = {pos=t.pos; inst=tnode} in
    match t.inst with
    | Num
    | Bool
    | Char
    | String
    | Bit 
    | Unit
    | Qbit 
    | Qstate
    | Bra
    | Ket
  (*| Range   _ *)
    | Gate            
    | Matrix          -> t
    | Known n         -> replace (let n' = assoc<@>n in Unknown n') 
    | Unknown _       
    | Poly    _       -> raise (Invalid_argument ("Type.rename " ^ string_of_type t))
    | OneOf   _       -> t (* I think *)
    | List    t       -> replace (List (rename assoc t))   
    | Channel t       -> replace (Channel (rename assoc t))
    | Process ts      -> replace (Process (List.map (rename assoc) ts))
    | Tuple   ts      -> replace (Tuple (List.map (rename assoc) ts))
    | Fun     (t1,t2) -> replace (Fun (rename assoc t1, rename assoc t2))
  in
  match t.inst with
  | Poly (ns, t)  -> let newns = List.map (fun n -> new_unknown (kind_of_unknown n)) ns in
                     (try rename (zip ns newns) t
                      with Zip -> raise (Invalid_argument ("Type.instantiate " ^ string_of_type t))
                     )
  | _             -> t

(* a service to compilation of monitor processes *)
let rec is_classical t =
  match t.inst with
  | Qbit            -> false            
  | Unit          
  | Num 
  | Bool
  | Char
  | String
  | Bit 
  | Bra
  | Ket
  | Gate            
  | Matrix          -> true
  | Qstate          -> true    (* really *)
  (* | Range   _ *)
  | Unknown (_, {contents=Some t})    
                    -> is_classical t       
  | Unknown (n, _)  -> let k = kind_of_unknown n in
                       k=UnkClass || k=UnkEq      
  | Known   n          (* can happen in Poly ... *)       
                    -> let k = kind_of_unknown n in
                       k=UnkClass || k=UnkEq
  | Poly    (ns, t) -> is_classical t 
  | OneOf   ((_, {contents=Some t}), _) -> is_classical t 
  | OneOf   (_, ts) -> List.for_all is_classical ts
  | List    t       -> is_classical t 
  | Channel t       -> is_classical t
  | Tuple   ts      -> List.for_all is_classical ts
  | Fun     (t1,t2) -> true (* yes *)
                     
  | Process _       -> true (* yes? *)

