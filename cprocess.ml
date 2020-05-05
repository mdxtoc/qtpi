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
open Cbasics
open Cstep
open Param

type cprocess = cprocnode instance

and cprocnode =
  | CTerminate
  | CGoOnAs of typedname * cexpr list             (* GoOnAs: homage to Laski *)
  | CWithNew of (bool * param list) * cprocess    (* bool is traced *)
  | CWithQbit of bool * cqspec list * cprocess     (* false: newq; true: newqs *)
  | CWithLet of cletspec * cprocess
  | CWithProc of cpdecl * cprocess
  | CWithQstep of cqstep * cprocess
  | CJoinQs of typedname list * param * cprocess
  | CSplitQs of typedname * csplitspec list * cprocess
  | CTestPoint of name instance * cprocess        (* not typedname in this case ... *)
  | CIter of env cpattern * cexpr * cprocess * cprocess  (* [ pat<-cexpr:cprocess].cprocess *)
  | CCond of cexpr * cprocess * cprocess
  | CPMatch of cexpr * (env * cprocess) cpattern
  | CGSum of (ciostep * cprocess) list
  | CPar of cprocess list

and cqspec = param * cexpr option

and cletspec = env cpattern * cexpr

and csplitspec = param * cexpr option

and cpdecl = bool * typedname * param list * cprocess   (* bool for recursion:
                                                                   false -- proc pn = tau(params).proc 
                                                                   true  -- proc pn(params) = proc
                                                       *)

let name_of_csplitspec csplitspec = name_of_param (fst csplitspec)

let cheadpos pos pinst = match pinst with 
                         | CTerminate
                         | CGoOnAs     _
                         | CPar        _
                         | CGSum       _
                         | CPMatch     _
                         | CCond       _         -> pos
                         | CWithNew    (_, p) 
                         | CWithQbit   (_, _, p) 
                         | CWithLet    (_, p) 
                         | CWithProc   (_, p)
                         | CWithQstep  (_, p)
                         | CTestPoint  (_, p)    
                         | CJoinQs     (_, _, p) 
                         | CSplitQs    (_, _, p)
                         | CIter    (_, _, _, p) -> spdiff pos p.pos

let procadorn pos pinst = adorn (cheadpos pos pinst) pinst 

let csteppos cprocess = cheadpos cprocess.pos cprocess.inst

let rec so_cp proc = 
  match proc.inst with
  | CTerminate             -> "_0"
  | CGoOnAs (pn,es)        -> Printf.sprintf "%s(%s)"
                                            (string_of_name (tinst pn))
                                            (string_of_list string_of_cexpr "," es)
  | CWithNew ((traced,params),p) 
                          -> Printf.sprintf "(%s %s)%s"
                                            (if traced then "newuntraced" else "new")
                                            (commasep (List.map string_of_param params))
                                            (trailing_csop p)
  | CWithQbit (plural,qs,p) -> Printf.sprintf "(%s %s)%s"
                                            (if plural then "newqs" else "newq")
                                            (commasep (List.map string_of_cqspec qs))
                                            (trailing_csop p)
  | CWithLet (lsc,p)       -> Printf.sprintf "(let %s)%s"
                                            (string_of_cletspec lsc)
                                            (trailing_csop p)
  | CWithProc (cpdecl,p)    -> Printf.sprintf "(proc %s)%s"
                                            (string_of_cpdecl cpdecl)
                                            (trailing_csop p)
  | CWithQstep (q,p)       -> Printf.sprintf "%s.%s"
                                            (string_of_cqstep q)
                                            (trailing_csop p)
  | CJoinQs    (qs,q,p)    -> Printf.sprintf "(joinqs %s→%s)%s"
                                            (string_of_list string_of_typedname "," qs)
                                            (string_of_param q)
                                            (trailing_csop p)
  | CSplitQs   (q,qs,p)    -> Printf.sprintf "(splitqs %s→%s)%s"
                                            (string_of_typedname q)
                                            (string_of_list string_of_csplitspec "," qs)
                                            (trailing_csop p)
  | CTestPoint (n,p)       -> Printf.sprintf "⁁%s %s"
                                            (string_of_name n.inst)
                                            (trailing_csop p)
  | CIter (pat, e, proc, p)
                          -> Printf.sprintf "[%s<-%s:%s] . %s"
                                            (string_of_cpattern pat)
                                            (string_of_cexpr e)
                                            (so_cp proc)
                                            (trailing_csop p)
  | CGSum [g]              -> string_of_pair string_of_ciostep so_cp "." g
  | CGSum gs               -> "+ " ^ String.concat " <+> " (List.map (string_of_pair string_of_ciostep so_cp ".") gs)
  | CPar  [p]              -> so_cp p
  | CPar  ps               -> "| " ^ String.concat " | " (List.map so_cp ps)
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
  | CPar    _   -> "(" ^ s ^ ")"
  | _          -> s        

and short_so_cp proc = 
  match proc.inst with
  | CTerminate             -> "_0"
  | CGoOnAs (pn,es)        -> Printf.sprintf "%s(%s)"
                                            (string_of_name (tinst pn))
                                            (string_of_list string_of_cexpr "," es)
  | CWithNew ((traced,params),p)    
                          -> Printf.sprintf "(%s %s) ..."
                                            (if traced then "new" else "newuntraced")
                                            (commasep (List.map string_of_param params))
  | CWithQbit (plural,xs,p) -> Printf.sprintf "(%s %s) ..."
                                            (if plural then "newqs" else "newq")
                                            (commasep (List.map string_of_cqspec xs))
  | CWithLet (lsc,p)       -> Printf.sprintf "(let %s) ..."
                                            (string_of_cletspec lsc)
  | CWithProc (cpdecl,p)    -> Printf.sprintf "(proc %s) ..."
                                            (string_of_cpdecl cpdecl)
  | CWithQstep (q,p)       -> Printf.sprintf "%s. ..."
                                            (string_of_cqstep q)
  | CJoinQs    (qs,q,p)    -> Printf.sprintf "(joinqs %s→%s) ..."
                                            (string_of_list string_of_param "," qs)
                                            (string_of_param q)
  | CSplitQs   (q,qs,p)    -> Printf.sprintf "(splitqs %s→%s) ..."
                                            (string_of_typedname q)
                                            (string_of_list string_of_csplitspec "," qs)
  | CTestPoint (n,p)       -> Printf.sprintf "⁁%s ..."
                                            (string_of_name n.inst)
  | CIter (pat, e, proc, p)
                          -> Printf.sprintf "[%s<-%s:..] . .."
                                            (string_of_cpattern pat)
                                            (string_of_cexpr e)
  | CGSum [i,p]            -> Printf.sprintf "%s. .." (string_of_ciostep i) 
  | CGSum gs               -> let sf (g,p) = Printf.sprintf "%s. .." (string_of_ciostep g) in
                             "+ " ^ String.concat " <+> " (List.map sf gs)
  | CPar  [p]              -> short_so_cp p 
  | CPar  ps               -> "| " ^ String.concat " | " (List.map short_so_cp ps) 
  | CCond (e,p1,p2)        -> Printf.sprintf "if %s then %s else %s fi"
                                            (string_of_cexpr e)
                                            (short_so_cp p1)
                                            (short_so_cp p2)
  | CPMatch (e,pms)        -> Printf.sprintf "(match %s.%s)" (string_of_cexpr e) (short_string_of_cpattern pms)

and string_of_cqspec (p, eopt) =
  Printf.sprintf "%s%s" 
                 (string_of_param p)
                 (match eopt with
                  | None      -> ""
                  | Some bve  -> Printf.sprintf "=%s" (string_of_cexpr bve)
                 )

and string_of_cletspec (pat,e) =
  Printf.sprintf "%s=%s"
  				 (string_of_cpattern pat)
  				 (string_of_cexpr e)
  				 
and string_of_csplitspec (p, eopt) =
  Printf.sprintf "%s%s" 
                 (string_of_param p)
                 (match eopt with
                  | None    -> ""
                  | Some e  -> Printf.sprintf "(%s)" (string_of_cexpr e)
                 )

and string_of_cpdecl (recb, pn, params, proc) =
  if recb then
    Printf.sprintf "%s(%s) = %s"
                    (match !(toptr pn) with 
                     | None -> tinst pn 
                     | Some t -> Printf.sprintf "(%s:%s)" (string_of_name (tinst pn)) (string_of_type t)
                    )
                    (string_of_params params)
                    (so_cp proc)
  else
    Printf.sprintf "%s%s = tau(%s).%s"
                    (string_of_name (tinst pn))
                    (match !(toptr pn) with None -> "" | Some t -> ":" ^ string_of_type t)
                    (string_of_params params)
                    (so_cp proc)
  
(* 
   and string_of_cprocmatch (pat,proc) =
     Printf.sprintf "%s.%s" (string_of_cpattern pat) (trailing_csop proc)
  
   and short_string_of_cprocmatch (pat, _) = Printf.sprintf "%s. ..." (string_of_cpattern pat)
 *)

let string_of_cprocess proc = Printf.sprintf "%s: %s" (string_of_sourcepos (csteppos proc)) (so_cp proc)

let short_string_of_cprocess proc = Printf.sprintf "%s: %s" (string_of_sourcepos (csteppos proc)) (short_so_cp proc)

