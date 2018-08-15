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
open Name
open Process
open Expr
open Pattern
open Param

type def = 
  | Processdef of name instance * param list * process
  | Functiondef of name instance * pattern list * expr 

let rec string_of_def = function
  | Processdef  (pn,params,proc) -> Printf.sprintf "proc %s(%s) = %s"
                                       (string_of_name pn.inst)
                                       (String.concat "," (List.map string_of_param params))
                                       (string_of_process proc)
  | Functiondef (fn,params,expr) -> Printf.sprintf "fun %s %s = %s"
                                       (string_of_name fn.inst)
                                       (String.concat " " (List.map string_of_fparam params))
                                       (string_of_expr expr)

and string_of_fparam pat =
  let {pnode=pn; ptype=tor} = pat.inst in
  match pn, !tor with
  | PatName _ , None
  | PatAny    , None -> string_of_pattern pat
  | _                -> "(" ^ string_of_pattern pat ^ ")"
  