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
open Param

type iostep = iostumble instance

and iostumble =
  | Read of expr * param list
  | Write of expr * expr list
  
type qstep = qstumble instance

and qstumble =
  | Measure of expr * param
  | Ugatestep of expr list * expr
  
let string_of_iostep iostep =
  match iostep.inst with
  | Read (e,params)     -> Printf.sprintf "%s?(%s)"
                                          (string_of_expr e)
                                          (commasep (List.map string_of_param params))
  | Write (e,es)        -> Printf.sprintf "%s!%s"
                                          (string_of_expr e)
                                          (commasep (List.map string_of_expr es))
let string_of_qstep qstep =
  match qstep.inst with
  | Measure (e,p)       -> Printf.sprintf "%s?%c(%s)"
                                          (string_of_expr e)
                                          '?'
                                          (string_of_param p)
  | Ugatestep (es,u)    -> Printf.sprintf "%s>>%s"
                                          (commasep (List.map string_of_expr es))
                                          (string_of_expr u)
