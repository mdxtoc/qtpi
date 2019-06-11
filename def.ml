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
open Type

(* to deal honestly with Hindley-Milner typechecking, a program is now a sequence of 
   _groups_ of mutually-recursive function definitions and single process definitions.
   Real Soon Now we will have Miranda-style type definitions in the functiondefs
 *)
type def = 
  | Processdef of name instance * param list * (process * process option) 
  | Functiondefs of fdef list
  | Letdef of pattern * expr
  
and fdef = name instance * pattern list * _type option ref * expr 

let rec string_of_def = function
  | Processdef (pn,params,(proc, monopt)) -> Printf.sprintf "proc %s(%s) = %s"
                                        (string_of_name pn.inst)
                                        (String.concat "," (List.map string_of_param params))
                                        (string_of_process proc ^ 
                                          (match monopt with 
                                           | Some mon -> " with " ^ string_of_process mon
                                           | None     -> ""
                                          )
                                        )
  | Functiondefs fdefs          ->  "fun " ^ Listutils.string_of_list string_of_fdef "\n" fdefs
  | Letdef (pat, e)             ->  Printf.sprintf "let %s = %s" 
                                                   (string_of_pattern pat) 
                                                   (string_of_expr e)
  
and string_of_fdef (fn,pats,toptr,expr) =
  Printf.sprintf "%s %s%s = %s"
  (string_of_name fn.inst)
  (String.concat " " (List.map string_of_fparam pats))
  (match !toptr with
   | Some t -> Printf.sprintf " :%s" (string_of_type t)
   | None   -> ""
  )
  (string_of_expr expr)
