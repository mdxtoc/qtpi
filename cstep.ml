(*
    Copyright (C) 2018-20 Richard Bornat
     
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
open Stringutils
open Optionutils
open Instance
open Name
open Vt
open Cbasics
open Type
open Param

type ciostep = ciostumble instance

and ciostumble = (* type needed for tracing. Sorry *)
  | CRead of cexpr * _type * rtenv cpattern
  | CWrite of cexpr * _type * cexpr                                     (* argument cexpr can, of course, be a tuple *)
  
type cqstep = cqstumble instance

and cqstumble =
  | CMeasure of bool * cexpr * cexpr option * rtenv cpattern    (* plural, qbit, basis gate, cpattern *)
  | CThrough of bool * cexpr list * cexpr                       (* plural, qbits, gate *)
  
let string_of_ciostep ciostep =
  match ciostep.inst with
  | CRead (ce,tpat,pat)         -> Printf.sprintf "%s?(%s:%s)"
                                          (string_of_cexpr ce)
                                          (string_of_cpattern pat)
                                          (string_of_type tpat)
  | CWrite (ce,te,e)            -> Printf.sprintf "%s!(%s:%s)"
                                          (string_of_cexpr ce)
                                          (string_of_cexpr e)
                                          (string_of_type te)

let string_of_cqstep cqstep =
  match cqstep.inst with
  | CMeasure (plural,e,gopt,p)   -> Printf.sprintf "%s%s%s(%s)"
                                          (string_of_cexpr e)
                                          (if plural then "⌢⃫" else "⌢̸")
                                          (((fun g -> "[" ^ string_of_cexpr g ^ "]") ||~~ "") gopt)
                                          (string_of_cpattern p)
  | CThrough (plural,es,ge)      -> Printf.sprintf "%s%s%s"
                                          (commasep (List.map string_of_cexpr es))
                                          (if plural then ">>>" else ">>")
                                          (string_of_cexpr ge)
