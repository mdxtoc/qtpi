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
open Tupleutils
open Name
open Sourcepos
open Instance
open Type
open Pattern
open Basisv
open Printpriority

exception Error of sourcepos * string

type expr = einst instance

and einst = {etype: _type option ref; enode: enode}

and enode = 
  | EUnit
  | EVar of name
  | ENum of Number.num
  | EBool of bool
  | EChar of char
  | EString of string
  | EBit of bool        (* 1=true *)
  | EBasisv of basisv
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
  | EWhere of expr * edecl

and arithop =
  | Plus
  | Minus
  | Times
  | TensorP
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

and edecl = edeclnode instance

and edeclnode = 
  | EDPat of pattern * _type option * expr
  | EDFun of name instance * pattern list * _type option ref * expr 

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
  | TensorP                 -> Left    , 205
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
  | ENum        _
  | EBool       _
  | EChar       _
  | EString     _
  | EBit        _ 
  | EBasisv     _
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
    raise (Error (e.pos, "string_of_primary (" ^ string_of_expr e ^ ")"))
  in
  match e.inst.enode with
  | EUnit           -> "()"
  | ENil            -> "[]"
  | EVar x          -> string_of_name x
  | EBit b          -> if b then "0b1" else "0b0"
  | EBasisv bv      -> string_of_basisv bv
  | ENum n          -> Number.string_of_num n
  | EBool b         -> if b then "true" else "false"
  | EChar c         -> Printf.sprintf "'%s'" (Char.escaped c)
  | EString s       -> Printf.sprintf "\"%s\"" (String.escaped s)
  | ECons (hd,tl)   -> (* if it ends in nil, print as constant. Otherwise error *)
                       (match list_of_expr e with
                        | Some es -> bracketed_string_of_list string_of_expr es
                        | None    -> bad ()
                       )
  | EMatch (e, ems) -> Printf.sprintf "(match %s.%s)" (string_of_expr e) (string_of_list string_of_ematch "<+>" ems)
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
  | ENum        _
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
  | EWhere      (e, ed)             -> Printf.sprintf "(%s where %s)" (string_of_expr e) (string_of_edecl ed)
  
and string_of_edecl edecl = 
  let sot = function
    | Some t -> Printf.sprintf " :%s" (string_of_type t)
    | None   -> ""
  in
  match edecl.inst with
  | EDPat (pat,topt,e)       -> Printf.sprintf "%s%s=%s" 
                                               (string_of_pattern pat) 
                                               (sot topt)
                                               (string_of_expr e)
  | EDFun (fn,pats,toptr, e)  -> Printf.sprintf "%s %s%s = %s"
                                               (string_of_name fn.inst)
                                               (String.concat " " (List.map string_of_fparam pats))
                                               (sot !toptr)
                                               (string_of_expr e)

and string_of_arithop = function
  | Plus    -> "+"
  | Minus   -> "-"
  | Times   -> "*"
  | TensorP -> "><"
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

and string_of_ematch (pat,e) =
  Printf.sprintf "%s.%s" (string_of_pattern pat) (string_of_expr e)

let delist = function
  | []  -> EUnit
  | [e] -> e.inst.enode
  | es  -> ETuple es
  
let relist e = 
  match e.inst.enode with
  | EUnit     -> []
  | ETuple es -> es
  | _         -> [e]
  
let type_of_expr e =
  match !(e.inst.etype) with
  | Some t -> t
  | None   -> raise (Error (e.pos, Printf.sprintf "typecheck didn't mark expr %s" (string_of_expr e)))
  
(* this is parameterised to allow various kinds of sets. Well, a few anyway: sets of names / types / source locations. More? *)

let frees_fun (s_exclude: NameSet.t -> 't -> 't) (s_add: name -> expr -> 't -> 't) (s_union: 't -> 't -> 't) (s_empty: 't) : expr -> 't =
  let rec frees e =
    let rec _frees s e =
      match e.inst.enode with
      | EVar        n          -> s_add n e s
      | EUnit  
      | ENum        _ 
      | EBool       _ 
      | EChar       _ 
      | EString     _ 
      | EBit        _ 
      | EBasisv     _ 
      | ENil                   -> s
      | EMinus      e 
      | ENot        e          -> _frees s e
      | ETuple      es         -> List.fold_left _frees s es
      | ECons       (e1,e2)
      | EAppend     (e1,e2) 
      | EApp        (e1,e2)    -> List.fold_left _frees s [e1;e2]
      | ECond       (e1,e2,e3) -> List.fold_left _frees s [e1;e2;e3]
      | EMatch      (e,ems)    -> (let ss = List.map (fun (pat,e) -> _frees_pats [pat] e) ems in
                                   let s' = List.fold_left s_union s_empty ss in
                                   s_union s s'
                                  )
      | EArith      (e1,_,e2) 
      | ECompare    (e1,_,e2) 
      | EBoolArith  (e1,_,e2)  -> List.fold_left _frees s [e1;e2]
      | ELambda     (pats,e)   -> s_union s (_frees_pats pats e)
      | EWhere      (e,edecl)  -> (match edecl.inst with
                                   | EDPat (pat,_,e')      -> let s = _frees s e' in            (* frees of e' (pat irrelevant) *)
                                                              let s' = _frees_pats [pat] e in   (* frees of e - binders of pat) *)
                                                              s_union s s'
                                   | EDFun (fn,pats, _,e') -> let s' = _frees_pats pats e' in   (* frees of e' - binders of pats *)
                                                              let s'' = _frees_pats pats e in   (* frees of e - binders of pats *)
                                                              s_exclude (NameSet.singleton (fn.inst)) (s_union s (s_union s' s''))
                                                                                              (* frees of the lot - function name *)
                                  )
  
    and _frees_pats pats e =
      let s = frees e in 
      s_exclude (names_of_pats pats) s
  
    in 
      _frees s_empty e
  in
  frees

let frees = frees_fun (fun nset s -> NameSet.diff s nset)
                      (fun n _ s -> NameSet.add n s)
                      NameSet.union
                      NameSet.empty
