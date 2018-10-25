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
open Stringutils
open Instance
open Name
open Expr
open Type
open Pattern
open Param

type iostep = iostumble instance

and iostumble =
  | Read of expr * pattern
  | Write of expr * expr            (* argument expr can, of course, be a tuple *)
  
type qstep = qstumble instance

and qstumble =
  | Measure of expr * expr list * param  (* qbit, gates, param *)
  | Ugatestep of expr list * expr
  
let string_of_iostep iostep =
  match iostep.inst with
  | Read (ce,pat)       -> Printf.sprintf "%s?(%s)"
                                          (string_of_expr ce)
                                          (string_of_pattern pat)
  | Write (ce,e)        -> Printf.sprintf "%s!%s"
                                          (string_of_expr ce)
                                          (string_of_expr e)
let string_of_qstep qstep =
  match qstep.inst with
  | Measure (e,gs,p)       -> Printf.sprintf "%s=?%s(%s)"
                                          (string_of_expr e)
                                          (match gs with
                                           | []   -> ""
                                           | _    -> Listutils.bracketed_string_of_list string_of_expr gs
                                          )
                                          (string_of_param p)
  | Ugatestep (es,u)    -> Printf.sprintf "%s>>%s"
                                          (commasep (List.map string_of_expr es))
                                          (string_of_expr u)
