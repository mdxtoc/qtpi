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

open Instance
open Listutils
open Functionutils
open Instance
open Name
open Type
open Basisv
open Printpriority

type pattern = pinst instance

and pinst = {ptype: _type option ref; pnode: pnode} 

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
  | PatGate of gatepat
  | PatCons of pattern * pattern
  | PatTuple of pattern list

and gatepat = gpnode instance

and gpnode =
  | PatH
  | PatI
  | PatX
  | PatY
  | PatZ
  | PatCnot
  | PatPhi of pattern 
  
let nGatepat = 7  (* for matchchecker *)

let constprio = NonAssoc, 10
let tupleprio = NonAssoc, 6
let listprio  = Right   , 3

let patprio p =
  match p.inst.pnode with
  | PatAny
  | PatName     _
  | PatUnit
  | PatNil
  | PatInt      _
  | PatBit      _
  | PatBool     _
  | PatChar     _
  | PatBasisv   _
  | PatGate     _
  | PatString   _   -> constprio
  | PatTuple    _   -> tupleprio
  | PatCons     _   -> listprio

let pwrap topt p = {ptype=ref topt; pnode=p}
let padorn pos topt p = adorn pos (pwrap topt p)

let mbl = revargs mustbracket_left
let mbr = mustbracket_right
let mbn = mustbracket_nonassoc

let rec string_of_pattern p =
  let rec sp p =
    let {pnode=pn; ptype=tor} = p.inst in
    match !tor, pn with 
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
    | PatGate   g       -> string_of_gatepat g
  and spb mb p =
    let s = sp p in
    if mb (patprio p) then "(" ^ s ^ ")" else s
  in 
  sp p

and string_of_gatepat g =
  match g.inst with 
  | PatH        -> "_H"
  | PatI        -> "_I"
  | PatX        -> "_X"
  | PatY        -> "_Y"
  | PatZ        -> "_Z"
  | PatCnot     -> "_Cnot"
  | PatPhi p    -> Printf.sprintf "_Phi(%s)" (string_of_pattern p)
  
let delist = function
  | []      -> PatUnit
  | [p]     -> p.inst.pnode
  | ps      -> PatTuple ps
