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
open Instance
open Sourcepos
open Listutils
open Functionutils
open Instance
open Name
open Type
open Basisv
open Printpriority

type pattern = pnode typedinstance

and pnode =
  | PatAny
  | PatName of name
  | PatUnit
  | PatNil
  | PatInt of int
  | PatBit of bool (* as EBit *)
  | PatBool of bool
  | PatChar of char
  | PatString of string
  | PatBasisv of basisv
  | PatCons of pattern * pattern
  | PatTuple of pattern list

let constprio = NonAssoc, 10
let listprio  = Right   , 6
let tupleprio = NonAssoc, 3 (* it's the comma priority, really *)

let patprio p =
  match tinst p with
  | PatAny
  | PatName     _
  | PatUnit
  | PatNil
  | PatInt      _
  | PatBit      _
  | PatBool     _
  | PatChar     _
  | PatBasisv   _
  | PatString   _   -> constprio
  | PatTuple    _   -> constprio (* now tuples must be bracketed *)
  | PatCons     _   -> listprio

let mbl = revargs mustbracket_left
let mbr = mustbracket_right
let mbn = mustbracket_nonassoc

let rec string_of_pattern p =
  let rec sp p =
    let pn = tinst p in
    match !(toptr p), pn with 
    | Some t, PatCons  _
    | Some t, PatTuple _ -> "(" ^ spnode pn ^ "):" ^ string_of_type t
    | Some t, _          -> spnode pn ^ ":" ^ string_of_type t
    | None  , _          -> spnode pn
  and spnode = function
    | PatAny            -> "_"
    | PatName   n       -> string_of_name n
    | PatCons   (ph,pt) -> Printf.sprintf "%s::%s" (spb (mbl listprio) ph) (spb (mbr listprio) pt)
    | PatUnit           -> "()"
    | PatNil            -> "[]"
    | PatBit    b       -> if b then "0b1" else "0b0"
    | PatTuple  ps      -> string_of_list (spb (mbn tupleprio)) "," ps
    | PatInt    i       -> string_of_int i
    | PatBool   b       -> string_of_bool b
    | PatChar   c       -> Printf.sprintf "'%s'" (Char.escaped c)
    | PatString s       -> Printf.sprintf "\"%s\"" (String.escaped s)
    | PatBasisv bv      -> string_of_basisv bv
  and spb mb p =
    let s = sp p in
    if mb (patprio p) then "(" ^ s ^ ")" else s
  in 
  sp p

let string_of_fparam pat =
  match tinst pat, !(toptr pat) with
  | PatUnit   , None
  | PatName _ , None
  | PatAny    , None -> string_of_pattern pat
  | _                -> "(" ^ string_of_pattern pat ^ ")"

let delist = function
  | []      -> PatUnit
  | [p]     -> tinst p
  | ps      -> PatTuple ps

let name_of_qpat pat = 
  match tinst pat with
  | PatName n -> Some n
  | PatAny    -> None
  | _         -> raise (Can'tHappen (string_of_sourcepos pat.pos ^ " name_of_qpat " ^ string_of_pattern pat))
  
let qpat_binds pat = 
  match name_of_qpat pat with
  | Some _ -> true
  | None   -> false
  
let names_of_pattern =
  let rec nps set p =
    match tinst p with
    | PatAny
    | PatUnit
    | PatNil
    | PatInt    _
    | PatBit    _
    | PatBool   _
    | PatChar   _
    | PatString _
    | PatBasisv _       -> set
    | PatName   n       -> NameSet.add n set 
    | PatCons   (ph,pt) -> nps (nps set ph) pt
    | PatTuple  ps      -> List.fold_left nps set ps
  in
  nps NameSet.empty
  
let frees = names_of_pattern
  
let names_of_pats pats = 
  List.fold_left NameSet.union NameSet.empty (List.map names_of_pattern pats) 
