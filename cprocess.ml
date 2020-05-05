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

let rec string_of_cprocess proc = 
  match proc.inst with
  | CTerminate             -> "_0"
  | CGoOnAs (pn,es)        -> Printf.sprintf "%s(%s)"
                                            (string_of_name (tinst pn))
                                            (string_of_list string_of_cexpr "," es)
  | CWithNew ((traced,params),p) 
                          -> Printf.sprintf "(%s %s)%s"
                                            (if traced then "newuntraced" else "new")
                                            (commasep (List.map string_of_param params))
                                            (trailing_sop p)
  | CWithQbit (plural,qs,p) -> Printf.sprintf "(%s %s)%s"
                                            (if plural then "newqs" else "newq")
                                            (commasep (List.map string_of_cqspec qs))
                                            (trailing_sop p)
  | CWithLet (lsc,p)       -> Printf.sprintf "(let %s)%s"
                                            (string_of_cletspec lsc)
                                            (trailing_sop p)
  | CWithProc (cpdecl,p)    -> Printf.sprintf "(proc %s)%s"
                                            (string_of_cpdecl cpdecl)
                                            (trailing_sop p)
  | CWithQstep (q,p)       -> Printf.sprintf "%s.%s"
                                            (string_of_cqstep q)
                                            (trailing_sop p)
  | CJoinQs    (qs,q,p)    -> Printf.sprintf "(joinqs %s→%s)%s"
                                            (string_of_list string_of_typedname "," qs)
                                            (string_of_param q)
                                            (trailing_sop p)
  | CSplitQs   (q,qs,p)    -> Printf.sprintf "(splitqs %s→%s)%s"
                                            (string_of_typedname q)
                                            (string_of_list string_of_csplitspec "," qs)
                                            (trailing_sop p)
  | CTestPoint (n,p)       -> Printf.sprintf "⁁%s %s"
                                            (string_of_name n.inst)
                                            (trailing_sop p)
  | CIter (pat, e, proc, p)
                          -> Printf.sprintf "[%s<-%s:%s] . %s"
                                            (string_of_cpattern pat)
                                            (string_of_cexpr e)
                                            (string_of_cprocess proc)
                                            (trailing_sop p)
  | CGSum [g]              -> string_of_pair string_of_ciostep string_of_cprocess "." g
  | CGSum gs               -> "+ " ^ String.concat " <+> " (List.map (string_of_pair string_of_ciostep string_of_cprocess ".") gs)
  | CPar  [p]              -> string_of_cprocess p
  | CPar  ps               -> "| " ^ String.concat " | " (List.map string_of_cprocess ps)
  | CCond (e,p1,p2)        -> Printf.sprintf "if %s then %s else %s fi"
                                            (string_of_cexpr e)
                                            (string_of_cprocess p1)
                                            (string_of_cprocess p2)
  | CPMatch (e,pms)        -> Printf.sprintf "(match %s.%s)" (string_of_cexpr e) (string_of_cpattern pms)

and trailing_sop p =
  let s = string_of_cprocess p in
  match p.inst with
  | CGSum   [_]
  | CPar    [_] -> s
  | CGSum   _
  | CPar    _   -> "(" ^ s ^ ")"
  | _          -> s        

and short_string_of_cprocess proc = 
  match proc.inst with
  | CTerminate             -> "_0"
  | CGoOnAs (pn,es)        -> Printf.sprintf "%s(%s)"
                                            (string_of_name (tinst pn))
                                            (string_of_list string_of_cexpr "," es)
  | CWithNew ((traced,params),p)    
                          -> Printf.sprintf "(%s %s) ..."
                                            (if traced then "newuntraced" else "new")
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
  | CPar  [p]              -> short_string_of_cprocess p 
  | CPar  ps               -> "| " ^ String.concat " | " (List.map short_string_of_cprocess ps) 
  | CCond (e,p1,p2)        -> Printf.sprintf "if %s then %s else %s fi"
                                            (string_of_cexpr e)
                                            (short_string_of_cprocess p1)
                                            (short_string_of_cprocess p2)
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
                    (string_of_cprocess proc)
  else
    Printf.sprintf "%s%s = tau(%s).%s"
                    (string_of_name (tinst pn))
                    (match !(toptr pn) with None -> "" | Some t -> ":" ^ string_of_type t)
                    (string_of_params params)
                    (string_of_cprocess proc)
  
(* 
   and string_of_cprocmatch (pat,proc) =
     Printf.sprintf "%s.%s" (string_of_cpattern pat) (trailing_sop proc)
  
   and short_string_of_cprocmatch (pat, _) = Printf.sprintf "%s. ..." (string_of_cpattern pat)
 *)

(* I hope I don't need any of this ...
   (* I wish OCaml didn't force this ... *)
   let _GoOnAs n es    = CGoOnAs (n,es)
   let _WithNew bpars p = CWithNew (bpars,p)
   let _WithQbit b qs p  = CWithQbit (b,qs,p)
   let _WithLet l p    = CWithLet (l,p)
   let _WithProc pd p  = CWithProc (pd,p)
   let _WithQstep q p  = CWithQstep (q,p)  
   let _JoinQs qs q p  = CJoinQs (qs,q,p)
   let _SplitQs q qs p = CSplitQs (q,qs,p)
   let _TestPoint ni p = CTestPoint (ni,p)
   let _Iter pat e proc p = CIter (pat,e,proc,p)
   let _Cond e p1 p2   = CCond (e,p1,p2)
   let _PMatch e pms   = CPMatch (e,pms)
   let _GSum iops      = CGSum iops
   let _Par ps         = CPar ps

   (* traversing a cprocess and modifying it: None if no change, Some f' if it changes. 
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
                        | CTerminate
                        | CGoOnAs     _          -> None
                        | CWithNew  (bps, p)     -> trav p &~~ take1 (_WithNew bps)
                        | CWithQbit (b, qs, p)   -> trav p &~~ take1 (_WithQbit b qs)
                        | CWithLet  (l, p)      -> trav p &~~ take1 (_WithLet l)
                        | CWithProc (pd, p)     -> trav p &~~ take1 (_WithProc pd) (* note we don't look at pd *)
                        | CWithQstep (q, p)     -> trav p &~~ take1 (_WithQstep q)
                        | CJoinQs (qs, q, p)    -> trav p &~~ take1 (_JoinQs qs q)
                        | CSplitQs (q, qs, p)   -> trav p &~~ take1 (_SplitQs q qs)
                        | CTestPoint (tp, p)    -> trav p &~~ take1 (_TestPoint tp)
                        | CIter (pat,e,proc,p) -> trav2 proc p &~~ take2 (fun proc p -> CIter(pat,e,proc,p))
                        | CCond (e, p1, p2)     -> trav2 p1 p2 &~~ take2 (_Cond e)
                        | CPMatch (e, pms)      -> Optionutils.optmap_any (fun (pat,p) -> trav p &~~ (_Some <.> (fun p -> pat,p))) pms 
                                                  &~~ take1 (_PMatch e)
                        | CGSum iops            -> Optionutils.optmap_any (fun (io,p) -> trav p &~~ (_Some <.> (fun p -> io,p))) iops 
                                                  &~~ take1 _GSum          
                        | CPar procs            -> Optionutils.optmap_any trav procs &~~ take1 _Par
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
     | CTerminate               -> NameSet.empty
     | CGoOnAs (pn, es)         -> NameSet.add (tinst pn) (free_es es)
     | CWithNew ((_,pars), p)   -> NameSet.diff (frees p) (paramset pars)
     | CWithQbit (_,qspecs, p)  -> let qs, optes = List.split qspecs in
                                  let qset = paramset qs in
                                  let ff_opte set = function
                                    | Some e -> nsu set (Expr.frees e) 
                                    | None   -> set
                                  in
                                  nsus [List.fold_left ff_opte NameSet.empty optes; nsd (frees p) qset]
     | CWithLet ((pat, e), p) -> nsu (Expr.frees e) (nsd (frees p) (Pattern.frees pat))
     | CWithProc (pd, p)      -> let (brec, pn, params, proc) = pd in
                                let pdfrees = nsd (frees proc) (paramset params) in
                                if brec then
                                  NameSet.remove (tinst pn) (NameSet.union pdfrees (frees p))
                                else
                                  nsd pdfrees (NameSet.remove (tinst pn) (frees p))
     | CWithQstep (cqstep,p)   -> (match cqstep.inst with
                                 | CMeasure (_,qe,optbe,pat) -> let qset = Expr.frees qe in
                                                               let bset = match optbe with
                                                                          | Some be -> nsu qset (Expr.frees be)
                                                                          | None    -> qset
                                                               in
                                                               nsu bset (nsd (frees p) (Pattern.frees pat))
                                 | CThrough (_, qes, ge)     -> nsu (free_es (ge::qes)) (frees p)
                                )
     | CJoinQs (qs,q,p)       -> let qset = paramset qs in
                                nsu qset (NameSet.remove (name_of_param q) (frees p)) 
     | CSplitQs (q,qs,p)      -> NameSet.add (name_of_typedname q) 
                                            (List.fold_left (fun set -> (revargs NameSet.remove) set <.> name_of_csplitspec) (frees p) qs)
     | CTestPoint (tpn,p)     -> (* tpn not included *) frees p
     | CIter (pat,e,proc,p)   -> let pset = nsd (frees proc) (Pattern.frees pat) in
                                nsus [pset; Expr.frees e; frees p]
     | CCond (e, p1, p2)      -> nsus [Expr.frees e; frees p1; frees p2]
     | CPMatch (e, pps)       -> let frees_pp (pat, proc) = nsd (frees proc) (Pattern.frees pat) in
                                nsu (Expr.frees e) (nsus (List.map frees_pp pps))
     | CGSum iops             -> let frees_iop (ciostep, p) =
                                  let pset = frees p in
                                  match ciostep.inst with
                                  | CRead (e, pat)  -> nsu (Expr.frees e) (nsd pset (Pattern.frees pat))
                                  | CWrite (ce, ve) -> nsu pset (free_es [ce;ve])
                                in
                                nsus (List.map frees_iop iops)
     | CPar ps                -> nsus (List.map frees ps)

   (* fold (left) over a cprocess. optp x p delivers Some x' when it knows, None when it doesn't. *)

   let optfold (optp: 'a -> cprocess -> 'a option) x =
     let rec ofold x p =
       optp x p |~~ (fun () -> 
         match p.inst with
           | CTerminate 
           | CGoOnAs      _          -> None
           | CWithNew   (_,p) 
           | CWithQbit  (_,_,p)
           | CWithLet   (_,p)
           | CWithProc  (_,p)          (* note we don't go into cpdecl *) 
           | CWithQstep (_,p)
           | CTestPoint (_,p)        
           | CJoinQs    (_,_,p)      
           | CSplitQs   (_,_,p)      -> ofold x p
           | CIter      (_,_,proc,p) -> Optionutils.optfold ofold x [proc;p]
           | CCond      (e,p1,p2)    -> Optionutils.optfold ofold x [p1;p2]
           | CPMatch    (e,pms)      -> Optionutils.optfold ofold x (List.map snd pms)
           | CGSum      iops         -> Optionutils.optfold ofold x (List.map snd iops)
           | CPar       ps           -> Optionutils.optfold ofold x ps
       )
     in
     ofold x 

   let fold optp x p = (revargs (optfold optp) p ||~ id) x

   (* find all the monitor processes inserted in a cprocess -- as (lab,pos) for convenience of typechecker *)
   let called_mons proc =
     let rec find_lps tps =
       let rec tpn tps p =
         match p.inst with
         | CTestPoint (lab, p) -> Some (find_lps ((lab.inst,lab.pos)::tps) p) (* includes position *)
         | _                  -> None
       in
       fold tpn tps
     in
     find_lps [] proc
 *)

