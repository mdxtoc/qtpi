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
    along with Qtpi; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
    (or look at http://www.gnu.org).
*)

open Stringutils
open Listutils
open Name
open Type
open Expr
open Step
open Param

type process = 
  | Terminate
  | Call of name * expr list
  | WithNew of param list * process
  | WithQbit of qspec list * process
  | WithLet of letspec * process
  | WithStep of step * process
  | Cond of expr * process * process
  | Par of process list

and qspec = param * basisv_e option

and letspec = param * expr

and basisv =
  | BVzero
  | BVone
  | BVplus
  | BVminus

and basisv_e =
  | BVe of basisv
  | BVcond of expr * basisv_e * basisv_e
  
let rec string_of_process = 
  let trailing_sop p =
    let s = string_of_process p in
    match p with
    | Par _ -> Printf.sprintf "(%s)" s
    | _     -> s
  in
  function
  | Terminate             -> "_0"
  | Call (p,es)           -> Printf.sprintf "%s(%s)"
                                            (string_of_name p)
                                            (string_of_list string_of_expr "," es)
  | WithNew (params,p)    -> Printf.sprintf "(new %s)%s"
                                            (commasep (List.map string_of_param params))
                                            (trailing_sop p)
  | WithQbit (xs,p)       -> Printf.sprintf "(newq %s)%s"
                                            (commasep (List.map string_of_qspec xs))
                                            (trailing_sop p)
  | WithLet (x,p)        -> Printf.sprintf "(let %s)%s"
                                            (string_of_letspec x)
                                            (trailing_sop p)
  | WithStep (s,p)        -> Printf.sprintf "%s.%s"
                                            (string_of_step s)
                                            (trailing_sop p)
  | Par (ps)              -> Printf.sprintf "%s" (String.concat "|" (List.map string_of_process ps))
  | Cond (e,p1,p2)        -> Printf.sprintf "if %s then %s else %s fi"
                                            (string_of_expr e)
                                            (string_of_process p1)
                                            (string_of_process p2)
and string_of_qspec (p, vopt) =
  Printf.sprintf "%s%s" 
                 (string_of_param p)
                 (match vopt with
                  | None    -> ""
                  | Some bv -> Printf.sprintf "=%s" (string_of_basisv_e bv)
                 )

and string_of_letspec (p,e) =
  Printf.sprintf "%s=%s"
  				 (string_of_param p)
  				 (string_of_expr e)
  				 
and string_of_basisv bv =
  match bv with
  | BVzero				-> "|0>"
  | BVone				-> "|1>"
  | BVplus				-> "|+>"
  | BVminus				-> "|->"
  
and string_of_basisv_e bve = 
  match bve with
  | BVe bv					-> string_of_basisv bv
  | BVcond (e,bve1,bve2)	-> Printf.sprintf "if %s then %s else %s fi"
  										  	  (string_of_expr e)
  										  	  (string_of_basisv_e bve1)
  										  	  (string_of_basisv_e bve2)
  