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

open Stringutils
open Functionutils
open Optionutils
open Listutils
open Name
open Sourcepos
open Instance
open Type
open Pattern
open Basisv
open Printpriority

exception Error of string

type expr = einst instance

and einst = {etype: _type option ref; enode: enode}

and enode = 
  | EUnit
  | EVar of name
  | EInt of int
  | EBool of bool
  | EChar of char
  | EString of string
  | EBit of bool        (* 1=true *)
  | EBasisv of basisv
  | EGate of ugate
  | EMinus of expr
  | ENot of expr
  | ETuple of expr list
  | ENil
  | ECons of expr * expr
  | EAppend of expr * expr
  | ECond of expr * expr * expr
  | EMatch of expr * ematch list
  | EApp of expr * expr
  | EArith of expr * arithop * expr
  | ECompare of expr * compareop * expr
  | EBoolArith of expr * boolop * expr
  | ELambda of pattern list * expr
  | EWhere of edecl

and ugate = ugnode instance

and ugnode =
  | GH
  | GI
  | GX
  | GY
  | GZ
  | GCnot
  | GPhi of expr

and arithop =
  | Plus
  | Minus
  | Times
  | Div
  | Mod
  
and compareop =
  | Lt
  | Leq
  | Eq
  | Neq
  | Geq
  | Gt
  
and boolop =
  | And
  | Or
  | Implies
  | Iff

and ematch = pattern * expr

and edecl =  
  | EDPat of expr * pattern* _type option * expr
  | EDFun of expr * name instance * pattern list * _type option * expr 

let ewrap opt enode = {etype=ref opt; enode=enode}

let eadorn pos = adorn pos <.> ewrap None

let rec is_nilterminated e =
  match e.inst.enode with
  | ENil        -> true
  | ECons (_,e) -> is_nilterminated e
  | _           -> false
  
let rec list_of_expr e =
  match e.inst.enode with
  | ENil          -> Some []    
  | ECons (hd,tl) -> list_of_expr tl &~~ (fun es -> Some (hd::es)) 
  | _             -> None
  
let tupleprio               =  NonAssoc, -10

let boolprio = function 
  | Implies                 -> Right   , 10
  | Iff                     -> Left    , 20 
  | Or                      -> Assoc   , 40
  | And                     -> Assoc   , 60

let compprio _              =  NonAssoc, 100

let arithprio = function
  | Plus                    -> Assoc   , 200
  | Minus                   -> Left    , 200
  | Times                   -> Assoc   , 210
  | Div | Mod               -> Left    , 210

let consprio                =  Right,    300
let unaryprio               =  NonAssoc, 400
let lambdaprio              =  NonAssoc, 500
let appprio                 =  Left    , 600
let whereprio               =  Left    , 700
let abitlessthanprimaryprio =  NonAssoc, 900
let primaryprio             =  NonAssoc, 1000

(* let string_of_prio = bracketed_string_of_pair string_of_prioritydir string_of_int *)

let rec exprprio e = 
  match e.inst.enode with 
  | EUnit                   
  | ENil
  | EVar        _   
  | EInt        _
  | EBool       _
  | EChar       _
  | EString     _
  | EBit        _ 
  | EBasisv     _
  | EGate       _
  | ECond       _           
  | EMatch      _           -> primaryprio
  | EMinus      _           
  | ENot        _           -> unaryprio
  | EApp        _           -> appprio
  | ECons       _           -> if is_nilterminated e then primaryprio else consprio
  | EArith      (_,op,_)    -> arithprio op
  | ECompare    (_,op,_)    -> compprio op
  | EBoolArith  (_,op,_)    -> boolprio op
  | EAppend     _           -> Left, 150    (* a temporary guess *)
  | ETuple      _           -> tupleprio
  | ELambda     _           -> lambdaprio
  | EWhere      _           -> whereprio

let is_primary e = exprprio e = primaryprio

let rec string_of_primary e =
  let bad () =
    raise (Error ("string_of_primary (" ^ string_of_expr e ^ ")"))
  in
  match e.inst.enode with
  | EUnit           -> "()"
  | ENil            -> "[]"
  | EVar x          -> string_of_name x
  | EBit b          -> if b then "0b1" else "0b0"
  | EBasisv bv      -> string_of_basisv bv
  | EGate ug        -> string_of_ugate ug
  | EInt i          -> string_of_int i
  | EBool b         -> if b then "true" else "false"
  | EChar c         -> Printf.sprintf "'%s'" (Char.escaped c)
  | EString s       -> Printf.sprintf "\"%s\"" (String.escaped s)
  | ECons (hd,tl)   -> (* if it ends in nil, print as constant. Otherwise error *)
                       (match list_of_expr e with
                        | Some es -> bracketed_string_of_list string_of_expr es
                        | None    -> bad ()
                       )
  | EMatch (e, ems) -> Printf.sprintf "match %s.%s hctam" (string_of_expr e) (string_of_list string_of_ematch "<+>" ems)
  | ECond (c,e1,e2) -> Printf.sprintf "if %s then %s else %s fi"
                                      (string_of_expr c)
                                      (string_of_expr e1)
                                      (string_of_expr e2)
  | _                -> bad ()
  
and bracketed_string_of_expr e = Printf.sprintf "(%s)" (string_of_expr e)

and string_of_binary_expr left right opstr opprio =
  let lprio = exprprio left in
  let leftf = bracket_left lprio opprio in
  let rprio = exprprio right in
  let rightf = bracket_right opprio rprio in
  leftf left^opstr^rightf right

and bracket_left lprio fprio = if mustbracket_left lprio fprio then bracketed_string_of_expr 
                                                               else string_of_expr

and bracket_right fprio rprio = if mustbracket_right fprio rprio then bracketed_string_of_expr
                                                                 else string_of_expr

and bracket_nonassoc supprio e = if mustbracket_nonassoc supprio (exprprio e) then bracketed_string_of_expr e
                                                                 else string_of_expr e                                                
and string_of_expr e = 
  match e.inst.enode with 
  | EUnit       
  | ENil
  | EVar        _
  | EBit        _
  | EBasisv     _
  | EGate       _
  | EInt        _
  | EBool       _
  | EChar       _
  | EString     _ 
  | ECond       _                   
  | EMatch      _                   -> string_of_primary e
  | EApp       (e1,e2)              -> string_of_binary_expr e1 e2 " " appprio
  | EMinus e                        -> Printf.sprintf "-%s" (bracket_nonassoc unaryprio e)
  | ENot   e                        -> Printf.sprintf "not %s" (bracket_nonassoc unaryprio e)
  | ECons      (hd,tl)              -> if is_nilterminated e then string_of_primary e
                                       else string_of_binary_expr hd tl "::" consprio
  | ETuple es                       -> commasep (List.map (bracket_nonassoc tupleprio) es)
  | EArith      (left, op, right)   -> string_of_binary_expr left right (string_of_arithop   op) (arithprio op)
  | ECompare    (left, op, right)   -> string_of_binary_expr left right (string_of_compareop op) (compprio op)
  | EBoolArith  (left, op, right)   -> string_of_binary_expr left right (string_of_boolop    op) (boolprio op)
  | EAppend     (left, right)       -> string_of_binary_expr left right "@"                      (exprprio e)
  | ELambda     (pats, expr)        -> Printf.sprintf "lam %s.%s" (string_of_list string_of_fparam " " pats) (string_of_expr expr)
  | EWhere      ed                  -> string_of_edecl ed
  
and string_of_edecl = 
  let sot = function
    | Some t -> Printf.sprintf " :%s" (string_of_type t)
    | None   -> ""
  in
  function
  | EDPat (e,wpat,wtype,we)         -> Printf.sprintf "(%s where %s%s=%s)" 
                                              (string_of_expr e) 
                                              (string_of_pattern wpat) 
                                              (sot wtype)
                                              (string_of_expr we)
  | EDFun (e,wfn,wfpats,wtype, we)  -> Printf.sprintf "(%s where %s %s%s = %s)"
                                                      (string_of_expr e)
                                                      (string_of_name wfn.inst)
                                                      (String.concat " " (List.map string_of_fparam wfpats))
                                                      (sot wtype)
                                                      (string_of_expr we)

and string_of_arithop = function
  | Plus    -> "+"
  | Minus   -> "-"
  | Times   -> "*"
  | Div     -> "/"
  | Mod     -> "%"
  
and string_of_compareop = function
  | Lt  -> "<"
  | Leq -> "<="
  | Eq  -> "="
  | Neq -> "<>"
  | Geq -> ">="
  | Gt  -> ">"

and string_of_boolop = function
  | And     -> "&&"
  | Or      -> "||"
  | Implies -> "=>"
  | Iff     -> "<=>"

and string_of_ugate ug = 
  match ug.inst with
  | GH              -> "_H"  
  | GI              -> "_I"
  | GX              -> "_X"
  | GY              -> "_Y"
  | GZ              -> "_Z"
  | GCnot           -> "_CNot"
  | GPhi (e)        -> Printf.sprintf "_Phi(%s)" (string_of_expr e)

and string_of_ematch (pat,e) =
  Printf.sprintf "%s.%s" (string_of_pattern pat) (string_of_expr e)

let arity_of_ugate ug =
  match ug.inst with
  | GH
  | GI
  | GX
  | GY
  | GZ
  | GPhi _  -> 1
  | GCnot   -> 2

let delist = function
  | []  -> EUnit
  | [e] -> e.inst.enode
  | es  -> ETuple es
  
let relist e = 
  match e.inst.enode with
  | EUnit     -> []
  | ETuple es -> es
  | _         -> [e]
  