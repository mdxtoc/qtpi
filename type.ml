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
    along with Qtpi; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
    (or look at http://www.gnu.org).
*)

open Settings
open Name
open Stringutils
open Listutils

type _type = 
  | Int
  | Bool
  | Bit 
  | Unit
  | Qbit
  | TypeVar of name (* unknown name starts with '?', which doesn't appear in parseable names *)
  | Univ of name list * _type
  | Range of int * int
  | List of _type
  | Tuple of _type list
  | Channel of _type        (* cos if it's _type list then typechecking is harder *)
  | Fun of _type * _type
  | Process of _type list
  
let processprio = 0 (* lower than tuple, channel, function *)
let funprio = 1     (* lower than tuple *)
let chanprio = 2
let tupleprio = 3
let listprio = 4
let primaryprio = 10

let typeprio t = 
  match t with  
  | Int 
  | Bool
  | Bit           
  | Unit          
  | Qbit            
  | TypeVar _ 
  | Univ    _        
  | Range   _       -> primaryprio
  | List    _       -> listprio
  | Tuple   _       -> tupleprio
  | Channel _       -> chanprio
  | Fun     _       -> funprio
  | Process _       -> processprio
  
let delist = function
  | []  -> Unit
  | [t] -> t
  | ts  -> Tuple ts

let relist = function
  | Unit     -> [] 
  | Tuple ts -> ts
  | t        -> [t]

let rec string_of_type t = match t with
  | Int             -> "int"
  | Bit             -> "bit"
  | Bool            -> "bool"
  | Unit            -> "unit"
  | Qbit            -> "qbit"
  | TypeVar  n     -> string_of_typevar n
  | Univ    (ns,ut) -> let nstrings = List.map string_of_typevar ns in
                       Printf.sprintf "forall %s.%s" (String.concat "," nstrings) (string_of_type ut)
  | Range   (l,h)   -> Printf.sprintf "%s..%s" (string_of_int l) (string_of_int h)
  | List    t       -> Printf.sprintf "%s list" (possbracket false listprio t)
  | Tuple   ts      -> string_of_typelist true tupleprio ts
  | Channel t       -> Printf.sprintf "^%s" (possbracket false chanprio t)
  | Fun     (t1,t2) -> Printf.sprintf "%s->%s"
                                      (possbracket true funprio t1)
                                      (possbracket false funprio t2)
  | Process ts      -> Printf.sprintf "%s process" (string_of_typelist false processprio ts)

and string_of_typevar n =
  if starts_with n "?" then string_of_name n else "'" ^ string_of_name n
  
and string_of_typelist ifeq supprio = function
  | [t] -> possbracket ifeq supprio t
  | ts  -> let substring = String.concat "*" (List.map (possbracket true tupleprio) ts) in
           possbracket' ifeq supprio tupleprio substring

and possbracket ifeq supprio t = 
  possbracket' ifeq supprio (typeprio t) (string_of_type t)
  
and possbracket' ifeq supprio subprio substring =
  if subprio<supprio || (ifeq && subprio=supprio) 
  then Printf.sprintf "(%s)" substring
  else substring

let rec frees t = _frees NameSet.empty t

and _frees s = function
  | Int
  | Bool
  | Bit 
  | Unit
  | Qbit        
  | Range _     -> s
  | TypeVar (n) -> NameSet.add n s 
  | Univ (ns,t) -> let vs = frees t in NameSet.union s (NameSet.diff vs (NameSet.of_list ns))
  | Channel t   
  | List    t   -> _frees s t  
  | Process ts   
  | Tuple ts    -> List.fold_left _frees s ts
  | Fun (t1,t2) -> _frees (_frees s t1) t2

let rec rename assoc t = 
  match t with
  | Int
  | Bool
  | Bit 
  | Unit
  | Qbit        
  | Range _     -> t
  | TypeVar (n) -> TypeVar (assoc<@>n) 
  | Univ (ns,t) -> raise (Invalid_argument ("Type.rename " ^ string_of_type t))
  | List    t   -> List (rename assoc t)   
  | Channel t  -> Channel (rename assoc t)
  | Process ts  -> Process (List.map (rename assoc) ts)
  | Tuple ts    -> Tuple (List.map (rename assoc) ts)
  | Fun (t1,t2) -> Fun (rename assoc t1, rename assoc t2)

let instantiate t =
  match t with
  | Univ (ns, t) -> let newns = List.map (fun _ -> new_unknown_name ()) ns in
                    (try rename (zip ns newns) t
                     with _ -> raise (Invalid_argument ("Type.instantiate " ^ string_of_type t))
                    )
  | _            -> t
