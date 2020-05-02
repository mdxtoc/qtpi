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
open Optionutils
open Functionutils
open Sourcepos
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
  | GoOnAs of typedname * expr list             (* GoOnAs: homage to Laski *)
  | WithNew of (bool * param list) * process    (* bool is traced *)
  | WithQbit of bool * qspec list * process     (* false: newq; true: newqs *)
  | WithLet of letspec * process
  | WithProc of pdecl * process
  | WithQstep of qstep * process
  | JoinQs of typedname list * param * process
  | SplitQs of typedname * splitspec list * process
  | TestPoint of name instance * process        (* not typedname in this case ... *)
  | Iter of pattern * expr * process * process  (* [ pat<-expr:process].process *)
  | Cond of expr * process * process
  | PMatch of expr * (pattern * process) list
  | GSum of (iostep * process) list
  | Par of process list

and qspec = param * expr option

and letspec = pattern * expr

and splitspec = param * expr option

and pdecl = bool * typedname * param list * process   (* bool for recursion:
                                                                   false -- proc pn = tau(params).proc 
                                                                   true  -- proc pn(params) = proc
                                                       *)

let name_of_splitspec = name_of_param <.> fst

let headpos pos pinst = match pinst with 
                      | Terminate
                      | GoOnAs     _
                      | Par        _
                      | GSum       _
                      | PMatch     _
                      | Cond       _         -> pos
                      | WithNew    (_, p) 
                      | WithQbit   (_, _, p) 
                      | WithLet    (_, p) 
                      | WithProc   (_, p)
                      | WithQstep  (_, p)
                      | TestPoint  (_, p)    
                      | JoinQs     (_, _, p) 
                      | SplitQs    (_, _, p)
                      | Iter    (_, _, _, p) -> spdiff pos p.pos

let procadorn pos pinst = adorn (headpos pos pinst) pinst 

let steppos process = headpos process.pos process.inst

let rec string_of_process proc = 
  match proc.inst with
  | Terminate             -> "_0"
  | GoOnAs (pn,es)        -> Printf.sprintf "%s(%s)"
                                            (string_of_name (tinst pn))
                                            (string_of_list string_of_expr "," es)
  | WithNew ((traced,params),p) 
                          -> Printf.sprintf "(%s %s)%s"
                                            (if traced then "newuntraced" else "new")
                                            (commasep (List.map string_of_param params))
                                            (trailing_sop p)
  | WithQbit (plural,qs,p) -> Printf.sprintf "(%s %s)%s"
                                            (if plural then "newqs" else "newq")
                                            (commasep (List.map string_of_qspec qs))
                                            (trailing_sop p)
  | WithLet (lsc,p)       -> Printf.sprintf "(let %s)%s"
                                            (string_of_letspec lsc)
                                            (trailing_sop p)
  | WithProc (pdecl,p)    -> Printf.sprintf "(proc %s)%s"
                                            (string_of_pdecl pdecl)
                                            (trailing_sop p)
  | WithQstep (q,p)       -> Printf.sprintf "%s.%s"
                                            (string_of_qstep q)
                                            (trailing_sop p)
  | JoinQs    (qs,q,p)    -> Printf.sprintf "(joinqs %s→%s)%s"
                                            (string_of_list string_of_typedname "," qs)
                                            (string_of_param q)
                                            (trailing_sop p)
  | SplitQs   (q,qs,p)    -> Printf.sprintf "(splitqs %s→%s)%s"
                                            (string_of_typedname q)
                                            (string_of_list string_of_splitspec "," qs)
                                            (trailing_sop p)
  | TestPoint (n,p)       -> Printf.sprintf "⁁%s %s"
                                            (string_of_name n.inst)
                                            (trailing_sop p)
  | Iter (pat, e, proc, p)
                          -> Printf.sprintf "[%s<-%s:%s] . %s"
                                            (string_of_pattern pat)
                                            (string_of_expr e)
                                            (string_of_process proc)
                                            (trailing_sop p)
  | GSum [g]              -> string_of_pair string_of_iostep string_of_process "." g
  | GSum gs               -> "+ " ^ String.concat " <+> " (List.map (string_of_pair string_of_iostep string_of_process ".") gs)
  | Par  [p]              -> string_of_process p
  | Par  ps               -> "| " ^ String.concat " | " (List.map string_of_process ps)
  | Cond (e,p1,p2)        -> Printf.sprintf "if %s then %s else %s fi"
                                            (string_of_expr e)
                                            (string_of_process p1)
                                            (string_of_process p2)
  | PMatch (e,pms)        -> Printf.sprintf "(match %s.%s)" (string_of_expr e) (string_of_list string_of_procmatch "<+>" pms)

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
  | GoOnAs (pn,es)        -> Printf.sprintf "%s(%s)"
                                            (string_of_name (tinst pn))
                                            (string_of_list string_of_expr "," es)
  | WithNew ((traced,params),p)    
                          -> Printf.sprintf "(%s %s) ..."
                                            (if traced then "newuntraced" else "new")
                                            (commasep (List.map string_of_param params))
  | WithQbit (plural,xs,p) -> Printf.sprintf "(%s %s) ..."
                                            (if plural then "newqs" else "newq")
                                            (commasep (List.map string_of_qspec xs))
  | WithLet (lsc,p)       -> Printf.sprintf "(let %s) ..."
                                            (string_of_letspec lsc)
  | WithProc (pdecl,p)    -> Printf.sprintf "(proc %s) ..."
                                            (string_of_pdecl pdecl)
  | WithQstep (q,p)       -> Printf.sprintf "%s. ..."
                                            (string_of_qstep q)
  | JoinQs    (qs,q,p)    -> Printf.sprintf "(joinqs %s→%s) ..."
                                            (string_of_list string_of_param "," qs)
                                            (string_of_param q)
  | SplitQs   (q,qs,p)    -> Printf.sprintf "(splitqs %s→%s) ..."
                                            (string_of_typedname q)
                                            (string_of_list string_of_splitspec "," qs)
  | TestPoint (n,p)       -> Printf.sprintf "⁁%s ..."
                                            (string_of_name n.inst)
  | Iter (pat, e, proc, p)
                          -> Printf.sprintf "[%s<-%s:..] . .."
                                            (string_of_pattern pat)
                                            (string_of_expr e)
  | GSum [i,p]            -> Printf.sprintf "%s. .." (string_of_iostep i) 
  | GSum gs               -> let sf (g,p) = Printf.sprintf "%s. .." (string_of_iostep g) in
                             "+ " ^ String.concat " <+> " (List.map sf gs)
  | Par  [p]              -> short_string_of_process p 
  | Par  ps               -> "| " ^ String.concat " | " (List.map short_string_of_process ps) 
  | Cond (e,p1,p2)        -> Printf.sprintf "if %s then %s else %s fi"
                                            (string_of_expr e)
                                            (short_string_of_process p1)
                                            (short_string_of_process p2)
  | PMatch (e,pms)        -> Printf.sprintf "(match %s.%s)" (string_of_expr e) (string_of_list short_string_of_procmatch "<+>" pms)

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
  				 
and string_of_splitspec (p, eopt) =
  Printf.sprintf "%s%s" 
                 (string_of_param p)
                 (match eopt with
                  | None    -> ""
                  | Some e  -> Printf.sprintf "(%s)" (string_of_expr e)
                 )

and string_of_pdecl (recb, pn, params, proc) =
  if recb then
    Printf.sprintf "%s(%s) = %s"
                    (match !(toptr pn) with 
                     | None -> tinst pn 
                     | Some t -> Printf.sprintf "(%s:%s)" (string_of_name (tinst pn)) (string_of_type t)
                    )
                    (string_of_params params)
                    (string_of_process proc)
  else
    Printf.sprintf "%s%s = tau(%s).%s"
                    (string_of_name (tinst pn))
                    (match !(toptr pn) with None -> "" | Some t -> ":" ^ string_of_type t)
                    (string_of_params params)
                    (string_of_process proc)
  
and string_of_procmatch (pat,proc) =
  Printf.sprintf "%s.%s" (string_of_pattern pat) (trailing_sop proc)
  
and short_string_of_procmatch (pat, _) = Printf.sprintf "%s. ..." (string_of_pattern pat)

(* I wish OCaml didn't force this ... *)
let _GoOnAs n es    = GoOnAs (n,es)
let _WithNew bpars p = WithNew (bpars,p)
let _WithQbit b qs p  = WithQbit (b,qs,p)
let _WithLet l p    = WithLet (l,p)
let _WithProc pd p  = WithProc (pd,p)
let _WithQstep q p  = WithQstep (q,p)  
let _JoinQs qs q p  = JoinQs (qs,q,p)
let _SplitQs q qs p = SplitQs (q,qs,p)
let _TestPoint ni p = TestPoint (ni,p)
let _Iter pat e proc p = Iter (pat,e,proc,p)
let _Cond e p1 p2   = Cond (e,p1,p2)
let _PMatch e pms   = PMatch (e,pms)
let _GSum iops      = GSum iops
let _Par ps         = Par ps

(* traversing a process and modifying it: None if no change, Some f' if it changes. 
   Here optf gives two results: Some r means r is the answer; None means recurse.
   (The original, in Arsenic, from which this is copied had three answers:
    Some (Some r) meant r is the answer; Some None meant ignore this node; None meant recurse.)
 *)

let optmap optf proc =
  let take1 c x = Some {proc with inst = c x} in
  let take2 c (p1,p2) = Some {proc with inst = c p1 p2} in
  let rec trav proc =
    match optf proc with
    | Some result -> Some result
    | _           -> match proc.inst with 
                     | Terminate
                     | GoOnAs     _          -> None
                     | WithNew  (bps, p)     -> trav p &~~ take1 (_WithNew bps)
                     | WithQbit (b, qs, p)   -> trav p &~~ take1 (_WithQbit b qs)
                     | WithLet  (l, p)      -> trav p &~~ take1 (_WithLet l)
                     | WithProc (pd, p)     -> trav p &~~ take1 (_WithProc pd) (* note we don't look at pd *)
                     | WithQstep (q, p)     -> trav p &~~ take1 (_WithQstep q)
                     | JoinQs (qs, q, p)    -> trav p &~~ take1 (_JoinQs qs q)
                     | SplitQs (q, qs, p)   -> trav p &~~ take1 (_SplitQs q qs)
                     | TestPoint (tp, p)    -> trav p &~~ take1 (_TestPoint tp)
                     | Iter (pat,e,proc,p) -> trav2 proc p &~~ take2 (fun proc p -> Iter(pat,e,proc,p))
                     | Cond (e, p1, p2)     -> trav2 p1 p2 &~~ take2 (_Cond e)
                     | PMatch (e, pms)      -> Optionutils.optmap_any (fun (pat,p) -> trav p &~~ (_Some <.> (fun p -> pat,p))) pms 
                                               &~~ take1 (_PMatch e)
                     | GSum iops            -> Optionutils.optmap_any (fun (io,p) -> trav p &~~ (_Some <.> (fun p -> io,p))) iops 
                                               &~~ take1 _GSum          
                     | Par procs            -> Optionutils.optmap_any trav procs &~~ take1 _Par
    and trav2 p1 p2 = optionpair_either trav p1 trav p2
    in
    trav proc
    
let map optf = optmap optf ||~ id

let rec frees proc =
  let paramset params = NameSet.of_list (names_of_params params) in
  let nsu = NameSet.union in
  let nsd = NameSet.diff in
  let nsus = List.fold_left nsu NameSet.empty in
  let free_es = nsus <.> List.map Expr.frees in
  match proc.inst with
  | Terminate               -> NameSet.empty
  | GoOnAs (pn, es)         -> NameSet.add (tinst pn) (free_es es)
  | WithNew ((_,pars), p)   -> NameSet.diff (frees p) (paramset pars)
  | WithQbit (_,qspecs, p)  -> let qs, optes = List.split qspecs in
                               let qset = paramset qs in
                               let ff_opte set = function
                                 | Some e -> nsu set (Expr.frees e) 
                                 | None   -> set
                               in
                               nsus [List.fold_left ff_opte NameSet.empty optes; nsd (frees p) qset]
  | WithLet ((pat, e), p) -> nsu (Expr.frees e) (nsd (frees p) (Pattern.frees pat))
  | WithProc (pd, p)      -> let (brec, pn, params, proc) = pd in
                             let pdfrees = nsd (frees proc) (paramset params) in
                             if brec then
                               NameSet.remove (tinst pn) (NameSet.union pdfrees (frees p))
                             else
                               nsd pdfrees (NameSet.remove (tinst pn) (frees p))
  | WithQstep (qstep,p)   -> (match qstep.inst with
                              | Measure (_,qe,optbe,pat) -> let qset = Expr.frees qe in
                                                            let bset = match optbe with
                                                                       | Some be -> nsu qset (Expr.frees be)
                                                                       | None    -> qset
                                                            in
                                                            nsu bset (nsd (frees p) (Pattern.frees pat))
                              | Through (_, qes, ge)     -> nsu (free_es (ge::qes)) (frees p)
                             )
  | JoinQs (qs,q,p)       -> let qset = paramset qs in
                             nsu qset (NameSet.remove (name_of_param q) (frees p)) 
  | SplitQs (q,qs,p)      -> NameSet.add (name_of_typedname q) 
                                         (List.fold_left (fun set -> (revargs NameSet.remove) set <.> name_of_splitspec) (frees p) qs)
  | TestPoint (tpn,p)     -> (* tpn not included *) frees p
  | Iter (pat,e,proc,p)   -> let pset = nsd (frees proc) (Pattern.frees pat) in
                             nsus [pset; Expr.frees e; frees p]
  | Cond (e, p1, p2)      -> nsus [Expr.frees e; frees p1; frees p2]
  | PMatch (e, pps)       -> let frees_pp (pat, proc) = nsd (frees proc) (Pattern.frees pat) in
                             nsu (Expr.frees e) (nsus (List.map frees_pp pps))
  | GSum iops             -> let frees_iop (iostep, p) =
                               let pset = frees p in
                               match iostep.inst with
                               | Read (e, pat)  -> nsu (Expr.frees e) (nsd pset (Pattern.frees pat))
                               | Write (ce, ve) -> nsu pset (free_es [ce;ve])
                             in
                             nsus (List.map frees_iop iops)
  | Par ps                -> nsus (List.map frees ps)

(* fold (left) over a process. optp x p delivers Some x' when it knows, None when it doesn't. *)

let optfold (optp: 'a -> process -> 'a option) x =
  let rec ofold x p =
    optp x p |~~ (fun () -> 
      match p.inst with
        | Terminate 
        | GoOnAs      _          -> None
        | WithNew   (_,p) 
        | WithQbit  (_,_,p)
        | WithLet   (_,p)
        | WithProc  (_,p)          (* note we don't go into pdecl *) 
        | WithQstep (_,p)
        | TestPoint (_,p)        
        | JoinQs    (_,_,p)      
        | SplitQs   (_,_,p)      -> ofold x p
        | Iter      (_,_,proc,p) -> Optionutils.optfold ofold x [proc;p]
        | Cond      (e,p1,p2)    -> Optionutils.optfold ofold x [p1;p2]
        | PMatch    (e,pms)      -> Optionutils.optfold ofold x (List.map snd pms)
        | GSum      iops         -> Optionutils.optfold ofold x (List.map snd iops)
        | Par       ps           -> Optionutils.optfold ofold x ps
    )
  in
  ofold x 

let fold optp x p = (revargs (optfold optp) p ||~ id) x

(* find all the monitor processes inserted in a process -- as (lab,pos) for convenience of typechecker *)
let called_mons proc =
  let rec find_lps tps =
    let rec tpn tps p =
      match p.inst with
      | TestPoint (lab, p) -> Some (find_lps ((lab.inst,lab.pos)::tps) p) (* includes position *)
      | _                  -> None
    in
    fold tpn tps
  in
  find_lps [] proc

