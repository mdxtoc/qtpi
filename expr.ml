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
open Name
open Sourcepos
open Instance
open Type

exception Error of string

type expr = einst instance

and einst = {etype: _type option ref; enode: enode}

and enode = 
  | EUnit
  | EVar of name
  | EInt of int
  | EBool of bool
  | EBit of bool        (* 1=true *)
  | EMinus of expr
  | ETuple of expr list
  | EList of expr list
  | ECond of expr * expr * expr
  | EApp of expr * expr
  | EArith of expr * arithop * expr
  | ECompare of expr * compareop * expr
  | EBoolArith of expr * boolop * expr
  | EAppend of expr * expr
  | EBitCombine of expr * expr

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
  
let ewrap opt enode = {etype=ref opt; enode=enode}
  
type prioritydir = Left | Right | Assoc | NonAssoc

let string_of_prioritydir = function
  | Left     -> "Left"
  | Right    -> "Right"
  | Assoc    -> "Assoc"
  | NonAssoc -> "NonAssoc"
  
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

let unaryprio               =  NonAssoc, 400
let appprio                 =  Left,     500
let primaryprio             =  NonAssoc, 1000
let abitlessthanprimaryprio =  NonAssoc, 900

(* let string_of_prio = bracketed_string_of_pair string_of_prioritydir string_of_int *)

let mustbracket_left (lassoc,lprio) (supassoc, supprio) =
  lprio<supprio || (lprio=supprio && match supassoc with | Left | Assoc -> false |_ -> true)

let mustbracket_right (supassoc, supprio) (rassoc,rprio) =
  supprio>rprio || (supprio=rprio && match supassoc with | Right | Assoc -> false |_ -> true)

let mustbracket_nonassoc (_,supprio) (_,subprio) = subprio <= supprio

let rec exprprio e = 
  match e.inst.enode with 
  | EUnit                   
  | EVar        _   
  | EInt        _
  | EBool       _
  | EBit        _   
  | EList       _
  | ECond       _           -> primaryprio
  | EMinus      _           -> unaryprio
  | EApp       _            -> appprio
  | EArith      (_,op,_)    -> arithprio op
  | ECompare    (_,op,_)    -> compprio op
  | EBoolArith  (_,op,_)    -> boolprio op
  | EAppend     _           -> Left, 150    (* a temporary guess *)
  | EBitCombine     _       -> Left, 155    (* a temporary guess *)
  | ETuple      _           -> tupleprio

let is_primary e = exprprio e = primaryprio

let rec string_of_primary e =
  match e.inst.enode with
  | EUnit           -> "()"
  | EVar x          -> string_of_name x
  | EBit b          -> if b then "0b1" else "0b0"
  | EInt i          -> string_of_int i
  | EBool b         -> if b then "true" else "false"
  | EList es        -> Printf.sprintf "[%s]"
                                      (commasep (List.map string_of_expr es))
  | ECond (c,e1,e2) -> Printf.sprintf "if %s then %s else %s fi"
                                      (string_of_expr c)
                                      (string_of_expr e1)
                                      (string_of_expr e2)
  | _                -> raise (Error ("string_of_primary (" ^ string_of_expr e ^ ")"))
  
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
  | EVar        _
  | EBit        _
  | EInt        _
  | EBool       _
  | EList       _
  | ECond       _                   -> string_of_primary e
  | EApp       (e1,e2)              -> string_of_binary_expr e1 e2 (if exprprio e2 = primaryprio then " " else "") appprio
  | EMinus e                        -> Printf.sprintf "-%s" (bracket_nonassoc unaryprio e)
  | ETuple es                       -> commasep (List.map (bracket_nonassoc tupleprio) es)
  | EArith      (left, op, right)   -> string_of_binary_expr left right (string_of_arithop   op) (arithprio op)
  | ECompare    (left, op, right)   -> string_of_binary_expr left right (string_of_compareop op) (compprio op)
  | EBoolArith  (left, op, right)   -> string_of_binary_expr left right (string_of_boolop    op) (boolprio op)
  | EAppend     (left, right)       -> string_of_binary_expr left right "@"                      (exprprio e)
  | EBitCombine (left, right)       -> string_of_binary_expr left right "++"                     (exprprio e)

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

  