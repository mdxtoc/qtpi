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

open Stringutils
open Listutils
open Tupleutils
open Optionutils
open Functionutils
open Sourcepos
open Instance
open Name
open Type
open Vt
open Cbasics
open Cstep
open Param

type cprocess = cprocnode instance

and cprocnode =
  | CTerminate
  | CGoOnAs of int * cexpr list                                 (* GoOnAs: homage to Laski *)
  | CWithNew of (bool * int list) * cprocess                    (* bool is traced *)
  | CWithQbit of bool * cqspec list * cprocess                  (* false: newq; true: newqs *)
  | CWithLet of cletspec * cprocess
  | CWithProc of int * cpdecl * cprocess
  | CWithQstep of cqstep * cprocess
  | CJoinQs of int list * int * cprocess
  | CSplitQs of int * csplitspec list * cprocess
  | CCond of cexpr * cprocess * cprocess
  | CPMatch of cexpr * (rtenv * cprocess) cpattern
  | CGSum of (ciostep * cprocess) list
  | CPar of cprocess list
  | CSpawn of cprocess list * cprocess                          (* CPar when all but one are CGoOnAs *)

and cqspec = int * cexpr option

and cletspec = rtenv cpattern * cexpr

and csplitspec = int * cexpr option

and cpdecl = name * (rtenv -> vt list -> procname * rtenv * cprocess)   (* name is for diagnostics, procname for tracing *)

and procname = name * (int * int) ref                           (* activity count, invocation count -- for computing process name in tracing *)

let name_of_procname : procname -> name = fst
let ref_of_procname : procname -> (int * int) ref = snd

let string_of_procname (n,_) = string_of_name n

let long_string_of_procname (n,r) = Printf.sprintf "%s%s" (string_of_name n) (bracketed_string_of_pair string_of_int string_of_int !r)

let name_of_csplitspec csplitspec = name_of_param (fst csplitspec)

let cheadpos pos pinst = match pinst with 
                         | CTerminate
                         | CGoOnAs     _
                         | CPar        _
                         | CSpawn      _
                         | CPMatch     _
                         | CCond       _         -> pos
                         | CGSum       [(_,p)]   -> spdiff pos p.pos
                         | CGSum       _         -> pos
                         | CWithNew    (_, p) 
                         | CWithQbit   (_, _, p) 
                         | CWithLet    (_, p) 
                         | CWithProc   (_, _, p)
                         | CWithQstep  (_, p)
                         | CJoinQs     (_, _, p) 
                         | CSplitQs    (_, _, p) -> spdiff pos p.pos

let procadorn pos pinst = adorn (cheadpos pos pinst) pinst 

let csteppos cprocess = cheadpos cprocess.pos cprocess.inst

let rec so_cp proc = 
  match proc.inst with
  | CTerminate             -> "_0"
  | CGoOnAs (i,es)         -> Printf.sprintf "%d(%s)" i (string_of_list string_of_cexpr "," es)
  | CWithNew ((traced,is),p) 
                          -> Printf.sprintf "(%s %s).%s"
                                            (if traced then "newuntraced" else "new")
                                            (commasep (List.map string_of_int is))
                                            (trailing_csop p)
  | CWithQbit (plural,qs,p) -> Printf.sprintf "(%s %s).%s"
                                            (if plural then "newqs" else "newq")
                                            (commasep (List.map string_of_cqspec qs))
                                            (trailing_csop p)
  | CWithLet (lsc,p)       -> Printf.sprintf "(let %s).%s"
                                            (string_of_cletspec lsc)
                                            (trailing_csop p)
  | CWithProc (i,cpdecl,p)  -> Printf.sprintf "(withproc %d,%s).%s"
                                            i
                                            (string_of_cpdecl cpdecl)
                                            (trailing_csop p)
  | CWithQstep (q,p)       -> Printf.sprintf "%s.%s"
                                            (string_of_cqstep q)
                                            (trailing_csop p)
  | CJoinQs    (qs,q,p)    -> Printf.sprintf "(joinqs %s→%s).%s"
                                            (string_of_list string_of_int "," qs)
                                            (string_of_int q)
                                            (trailing_csop p)
  | CSplitQs   (q,qs,p)    -> Printf.sprintf "(splitqs %s→%s).%s"
                                            (string_of_int q)
                                            (string_of_list string_of_csplitspec "," qs)
                                            (trailing_csop p)
  | CGSum [g]              -> string_of_pair string_of_ciostep so_cp "." g
  | CGSum gs               -> "<+> " ^ String.concat " <+> " (List.map (string_of_pair string_of_ciostep so_cp ".") gs)
  | CPar  [p]              -> so_cp p
  | CPar  ps               -> "| " ^ String.concat " | " (List.map so_cp ps)
  | CSpawn (ps,p)          -> so_cp (adorn proc.pos (CPar(p::ps)))
  | CCond (e,p1,p2)        -> Printf.sprintf "if %s then %s else %s fi"
                                            (string_of_cexpr e)
                                            (so_cp p1)
                                            (so_cp p2)
  | CPMatch (e,pms)        -> Printf.sprintf "(match %s.%s)" (string_of_cexpr e) (string_of_cpattern pms)

and trailing_csop p =
  let s = so_cp p in
  match p.inst with
  | CGSum   [_]
  | CPar    [_] -> s
  | CGSum   _
  | CPar    _   
  | CSpawn  _   -> "(" ^ s ^ ")"
  | _           -> s        

and short_so_cp proc = 
  match proc.inst with
  | CTerminate             -> "_0"
  | CGoOnAs (i,es)         -> Printf.sprintf "%d(%s)" i (string_of_list string_of_cexpr "," es)
  | CWithNew ((traced,is),p)    
                          -> Printf.sprintf "(%s %s) ..."
                                            (if traced then "new" else "newuntraced")
                                            (commasep (List.map string_of_int is))
  | CWithQbit (plural,xs,p) -> Printf.sprintf "(%s %s) ..."
                                            (if plural then "newqs" else "newq")
                                            (commasep (List.map string_of_cqspec xs))
  | CWithLet (lsc,p)       -> Printf.sprintf "(let %s) ..."
                                            (string_of_cletspec lsc)
  | CWithProc (i,cpdecl,p)    -> Printf.sprintf "(withproc %d %s). ..."
                                            i
                                            (short_string_of_cpdecl cpdecl)
  | CWithQstep (q,p)       -> Printf.sprintf "%s. ..."
                                            (string_of_cqstep q)
  | CJoinQs    (qs,q,p)    -> Printf.sprintf "(joinqs %s→%s) ..."
                                            (string_of_list string_of_int "," qs)
                                            (string_of_int q)
  | CSplitQs   (q,qs,p)    -> Printf.sprintf "(splitqs %s→%s) ..."
                                            (string_of_int q)
                                            (string_of_list string_of_csplitspec "," qs)
  | CGSum [i,p]            -> Printf.sprintf "%s. .." (string_of_ciostep i) 
  | CGSum gs               -> let sf (g,p) = Printf.sprintf "%s. .." (string_of_ciostep g) in
                             "<+> " ^ String.concat " <+> " (List.map sf gs)
  | CPar  [p]              -> short_so_cp p 
  | CPar  ps               -> "| " ^ String.concat " | " (List.map short_so_cp ps) 
  | CSpawn (ps,p)          -> short_so_cp (adorn proc.pos (CPar(p::ps)))
  | CCond (e,p1,p2)        -> Printf.sprintf "if %s then %s else %s fi"
                                            (string_of_cexpr e)
                                            (short_so_cp p1)
                                            (short_so_cp p2)
  | CPMatch (e,pms)        -> Printf.sprintf "(match %s.%s)" (string_of_cexpr e) (short_string_of_cpattern pms)

and string_of_cqspec (i, eopt) =
  Printf.sprintf "%s%s" 
                 (string_of_int i)
                 (match eopt with
                  | None      -> ""
                  | Some bve  -> Printf.sprintf "=%s" (string_of_cexpr bve)
                 )

and string_of_cletspec (pat,e) =
  Printf.sprintf "%s=%s"
  				 (string_of_cpattern pat)
  				 (string_of_cexpr e)
  				 
and string_of_csplitspec (i, eopt) =
  Printf.sprintf "%s%s" 
                 (string_of_int i)
                 (match eopt with
                  | None    -> ""
                  | Some e  -> Printf.sprintf "(%s)" (string_of_cexpr e)
                 )

and string_of_cpdecl (name, f) =
  Printf.sprintf "(%s,<fun>)" (string_of_name name)
  
and short_string_of_cpdecl (name, f) = string_of_cpdecl (name, f)
  
let string_of_cprocess proc = Printf.sprintf "%s: %s" (string_of_sourcepos (csteppos proc)) (so_cp proc)

let short_string_of_cprocess proc = Printf.sprintf "%s: %s" (string_of_sourcepos (csteppos proc)) (short_so_cp proc)

