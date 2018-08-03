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
open Listutils
open Tupleutils
open Instance
open Name
open Type
open Expr
open Step
open Pattern
open Param

type process = procnode instance

and procnode =
  | Terminate
  | Call of name instance * expr list
  | WithNew of param list * process
  | WithQbit of qspec list * process
  | WithLet of letspec * process
  | WithQstep of qstep * process
  | WithExpr of expr * process
  | Cond of expr * process * process
  | PMatch of expr * (pattern * process) list
  | GSum of (iostep * process) list
  | Par of process list

and qspec = param * expr option

and letspec = pattern * expr

let rec string_of_process proc = 
  match proc.inst with
  | Terminate             -> "_0"
  | Call (p,es)           -> Printf.sprintf "%s(%s)"
                                            (string_of_name p.inst)
                                            (string_of_list string_of_expr "," es)
  | WithNew (params,p)    -> Printf.sprintf "(new %s)%s"
                                            (commasep (List.map string_of_param params))
                                            (trailing_sop p)
  | WithQbit (qs,p)       -> Printf.sprintf "(newq %s)%s"
                                            (commasep (List.map string_of_qspec qs))
                                            (trailing_sop p)
  | WithLet (lsc,p)       -> Printf.sprintf "(let %s)%s"
                                            (string_of_letspec lsc)
                                            (trailing_sop p)
  | WithQstep (q,p)       -> Printf.sprintf "%s.%s"
                                            (string_of_qstep q)
                                            (trailing_sop p)
  | WithExpr (e,p)        -> Printf.sprintf "{%s}.%s" 
                                            (string_of_expr e) 
                                            (trailing_sop p)
  | GSum gs               -> String.concat "+" (List.map (string_of_pair string_of_iostep string_of_process ".") gs)
  | Par  ps               -> String.concat "|" (List.map string_of_process ps)
  | Cond (e,p1,p2)        -> Printf.sprintf "if %s then %s else %s fi"
                                            (string_of_expr e)
                                            (string_of_process p1)
                                            (string_of_process p2)
  | PMatch (e,pms)        -> Printf.sprintf "match %s.%s hctam" (string_of_expr e) (string_of_list string_of_procmatch "<+>" pms)

and trailing_sop p =
  let s = string_of_process p in
  match p.inst with
  | GSum   [_]
  | Par    [_] -> s
  | GSum   _
  | Par    _   -> "(" ^ s ^ ")"
  | _          -> s        

and short_string_of_process proc = 
  match proc.inst with
  | Terminate             -> "_0"
  | Call (p,es)           -> Printf.sprintf "%s(%s)"
                                            (string_of_name p.inst)
                                            (string_of_list string_of_expr "," es)
  | WithNew (params,p)    -> Printf.sprintf "(new %s) ..."
                                            (commasep (List.map string_of_param params))
  | WithQbit (xs,p)       -> Printf.sprintf "(newq %s) ..."
                                            (commasep (List.map string_of_qspec xs))
  | WithLet (lsc,p)       -> Printf.sprintf "(let %s) ..."
                                            (string_of_letspec lsc)
  | WithQstep (q,p)       -> Printf.sprintf "%s. ..."
                                            (string_of_qstep q)
  | WithExpr (e,p)        -> Printf.sprintf "%s; ..."
                                            (string_of_expr e)
  | GSum gs               -> let sf (g,p) = Printf.sprintf "%s. ..." (string_of_iostep g) in
                             String.concat "+" (List.map sf gs)
  | Par  ps               -> String.concat "|" (List.map short_string_of_process ps)
  | Cond (e,p1,p2)        -> Printf.sprintf "if %s then %s else %s fi"
                                            (string_of_expr e)
                                            (short_string_of_process p1)
                                            (short_string_of_process p2)
  | PMatch (e,pms)        -> Printf.sprintf "match %s.%s hctam" (string_of_expr e) (string_of_list short_string_of_procmatch "<+>" pms)

and string_of_qspec (p, eopt) =
  Printf.sprintf "%s%s" 
                 (string_of_param p)
                 (match eopt with
                  | None      -> ""
                  | Some bve  -> Printf.sprintf "=%s" (string_of_expr bve)
                 )

and string_of_letspec (pat,e) =
  Printf.sprintf "%s=%s"
  				 (string_of_pattern pat)
  				 (string_of_expr e)
  				 
and string_of_procmatch (pat,proc) =
  Printf.sprintf "%s.%s" (string_of_pattern pat) (trailing_sop proc)
  
and short_string_of_procmatch (pat, _) = Printf.sprintf "%s. ..." (string_of_pattern pat)
