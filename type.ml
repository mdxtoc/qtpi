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
open Instance

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
  | Basisv
  | Gate    of int              (* arity *)
  | Unknown of unknown          
  | Known   of name             (* knowns start with '\'', which doesn't appear in parseable names *)
  | Poly    of name list * _type
(*| Range   of int * int *)
  | List    of _type
  | Tuple   of _type list
  | Channel of _type            (* cos if it's _type list, as in tuple, then typechecking is harder *)
  | Fun     of _type * _type
  | Process of _type list

and unknown = name * _type option ref (* unknowns start with '?', which doesn't appear in parseable names *)

let processprio = 0 (* lower than tuple, channel, function *)
let funprio = 1     (* lower than tuple *)
let chanprio = 2
let tupleprio = 3
let listprio = 4
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
  | Basisv
  | Gate    _
  | Unknown _ 
  | Known   _ 
(*| Range   _ *) 
  | Poly    _       -> primaryprio
  | List    _       -> listprio
  | Tuple   _       -> tupleprio
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
  | Unit             -> "unit"
  | Qbit             -> "qbit"
  | Qstate           -> "qstate"
  | Basisv           -> "basisv"
  | Gate    i        -> Printf.sprintf "gate(%d)" i
  | Unknown u        -> (*"Unknown " ^*) string_of_unknown u
  | Known   n        -> (*"Known " ^*) string_of_name n
  | Poly    (ns,ut)  -> let nstrings = List.map string_of_name ns in
                        Printf.sprintf "forall %s.%s" (String.concat "," nstrings) (string_of_type ut)
(*| Range   (l,h)    -> Printf.sprintf "%s..%s" (string_of_int l) (string_of_int h) *)
  | List    t        -> Printf.sprintf "%s list" (possbracket false listprio t)
  | Tuple   ts       -> string_of_typelist true tupleprio ts
  | Channel t        -> Printf.sprintf "^%s" (possbracket false chanprio t)
  | Fun     (t1,t2)  -> Printf.sprintf "%s->%s"
                                       (possbracket true funprio t1)
                                       (possbracket false funprio t2)
  | Process ts       -> Printf.sprintf "%s process" (string_of_tnode (delist ts))

and string_of_unknown = function    (* unknowns are transparent *)
  | _, {contents=Some t} -> string_of_type t
  | n, _                 -> string_of_name n

and string_of_typelist ifeq supprio = function
  | [t] -> string_of_type t
  | ts  -> String.concat "*" (List.map (possbracket true tupleprio) ts)

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
    | Basisv
  (*| Range   _ *)
    | Gate    _       -> s
    | Unknown (_, {contents=Some t'})    
                      -> _freetvs s t'      
    | Unknown (n, _)  -> NameSet.add n s      
    | Known   n       -> NameSet.add n s 
    | Poly    (ns,t)  -> let vs = freetvs t in NameSet.union s (NameSet.diff vs (NameSet.of_list ns))
    | Channel t   
    | List    t       -> _freetvs s t  
    | Process ts   
    | Tuple   ts      -> List.fold_left _freetvs s ts
    | Fun     (t1,t2) -> _freetvs (_freetvs s t1) t2
  in
  _freetvs NameSet.empty t

module OrderedUnknown = struct type t = unknown let compare (n1,_) (n2,_) = Pervasives.compare n1 n2 let to_string = string_of_unknown end
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
    | Basisv
  (*| Range   _ *)
    | Gate    _       -> s
    | Unknown (_, {contents=Some t'})    
                      -> _freeuks s t'      
    | Unknown u       -> UnknownSet.add u s      
    | Known   n       -> s 
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
let generalise t = 
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
    | Basisv
  (*| Range   _ *)
    | Gate    _         -> t
    | Unknown (n, {contents=Some t'})  
                        -> replace (unknown_to_known t').inst  
    | Unknown (n, _)    -> let n' = String.concat "" ["'"; String.sub n 1 (String.length n - 1)] in
                           replace (Known n')
    | Known   _         -> t
    | Poly    _         -> raise (Invalid_argument ("Type.generalise " ^ string_of_type t))
    | List    t         -> replace (List (unknown_to_known t))  
    | Channel t         -> replace (Channel (unknown_to_known t))
    | Process ts        -> replace (Process (List.map unknown_to_known ts))
    | Tuple   ts        -> replace (Tuple (List.map unknown_to_known ts))
    | Fun     (t1,t2)   -> replace (Fun (unknown_to_known t1, unknown_to_known t2))
  in
  let t = unknown_to_known t in
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
    | Basisv
  (*| Range   _ *)
    | Gate    _       -> t
    | Known n         -> replace (let n' = assoc<@>n in Unknown n') 
    | Unknown _       
    | Poly    _       -> raise (Invalid_argument ("Type.rename " ^ string_of_type t))
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
