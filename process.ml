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
  | GoOnAs of name instance * expr list * expr list (* GoOnAs: homage to Laski *)
  | WithNew of param list * process
  | WithQbit of qspec list * process
  | WithLet of letspec * process
  | WithQstep of qstep * process
  | TestPoint of name instance * process
  | Iter of param list * process * expr * process
  | Cond of expr * process * process
  | PMatch of expr * (pattern * process) list
  | GSum of (iostep * process) list
  | Par of process list

and qspec = param * expr option

and letspec = pattern * expr

let rec string_of_process proc = 
  match proc.inst with
  | Terminate             -> "_0"
  | GoOnAs (p,es,mes)     -> Printf.sprintf "%s(%s)%s"
                                            (string_of_name p.inst)
                                            (string_of_list string_of_expr "," es)
                                            (if mes=[] then "" else "/^(" ^ string_of_list string_of_expr "," mes ^ ")")
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
  | TestPoint (n,p)       -> Printf.sprintf "/^%s %s"
                                            (string_of_name n.inst)
                                            (trailing_sop p)
  | Iter (params, proc, e, p)
                          -> Printf.sprintf ".* (%s) (%s) %s . %s"
                                            (commasep (List.map string_of_param params))
                                            (string_of_process proc)
                                            (string_of_expr e)
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
  | GoOnAs (p,es,mes)     -> Printf.sprintf "%s(%s)%s"
                                            (string_of_name p.inst)
                                            (string_of_list string_of_expr "," es)
                                            (if mes=[] then "" else "/^(" ^ string_of_list string_of_expr "," mes ^ ")")
  | WithNew (params,p)    -> Printf.sprintf "(new %s) ..."
                                            (commasep (List.map string_of_param params))
  | WithQbit (xs,p)       -> Printf.sprintf "(newq %s) ..."
                                            (commasep (List.map string_of_qspec xs))
  | WithLet (lsc,p)       -> Printf.sprintf "(let %s) ..."
                                            (string_of_letspec lsc)
  | WithQstep (q,p)       -> Printf.sprintf "%s. ..."
                                            (string_of_qstep q)
  | TestPoint (n,p)       -> Printf.sprintf "/^%s ..."
                                            (string_of_name n.inst)
  | Iter (params, proc, e, p)
                          -> Printf.sprintf ".* (%s) (..) %s . .."
                                            (commasep (List.map string_of_param params))
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
  				 
and string_of_procmatch (pat,proc) =
  Printf.sprintf "%s.%s" (string_of_pattern pat) (trailing_sop proc)
  
and short_string_of_procmatch (pat, _) = Printf.sprintf "%s. ..." (string_of_pattern pat)

(* I wish OCaml didn't force this ... *)
let _GoOnAs n es mes  = GoOnAs (n,es,mes)
let _WithNew pars p = WithNew (pars,p)
let _WithQbit qs p  = WithQbit (qs,p)
let _WithLet l p    = WithLet (l,p)
let _WithQstep q p  = WithQstep (q,p)  
let _TestPoint ni p = TestPoint (ni,p)
let _Iter pars proc e p = Iter (pars,proc,e,p)
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
                     | WithNew  (ps, p)     -> trav p &~~ take1 (_WithNew ps)
                     | WithQbit (qs, p)     -> trav p &~~ take1 (_WithQbit qs)
                     | WithLet  (l, p)      -> trav p &~~ take1 (_WithLet l)
                     | WithQstep (q, p)     -> trav p &~~ take1 (_WithQstep q)
                     | TestPoint (tp, p)    -> trav p &~~ take1 (_TestPoint tp)
                     | Iter (pars,proc,e,p) -> trav2 proc p &~~ take2 (fun proc p -> Iter(pars,proc,e,p))
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
  let rec ff set p =
    match p.inst with
    | Terminate -> set
    | GoOnAs (pn, es, mes)    -> NameSet.add pn.inst (ff_es (ff_es set es) mes)
    | WithNew (pars, p)     -> NameSet.diff (ff set p) (NameSet.of_list (strip_params pars))
    | WithQbit (qspecs, p)  -> let qs, optes = List.split qspecs in
                               let qset = NameSet.of_list (strip_params qs) in
                               let ff_opte set = function
                                 | Some e -> NameSet.union set (Expr.frees e) 
                                 | None   -> set
                               in
                               NameSet.union (List.fold_left ff_opte NameSet.empty optes) 
                                             (NameSet.diff (ff set p) qset)
    | WithLet ((pat, e), p) -> NameSet.union (Expr.frees e) (NameSet.diff (ff set p) (Pattern.frees pat))
    | WithQstep (qstep,p)   -> (match qstep.inst with
                                | Measure (qe,optbe,pat) -> let qset = Expr.frees qe in
                                                            let bset = match optbe with
                                                                       | Some be -> NameSet.union qset (Expr.frees be)
                                                                       | None    -> qset
                                                            in
                                                            NameSet.diff (ff bset p) (Pattern.frees pat)
                                | Ugatestep (qes, ge)    -> ff (ff_es set (ge::qes)) p
                               )
    | TestPoint (tpn,p)     -> (* tpn not included *) ff set p
    | Iter (pars,proc,e,p)  -> let set = NameSet.diff (ff set proc) (NameSet.of_list (strip_params pars)) in
                               NameSet.union (Expr.frees e) (ff set p)
    | Cond (e, p1, p2)      -> NameSet.union (Expr.frees e) (ff (ff set p1) p2)
    | PMatch (e, pps)       -> let ff_pp set (pat, proc) = NameSet.diff (ff set proc) (Pattern.frees pat) in
                               NameSet.union (Expr.frees e) (List.fold_left ff_pp set pps)
    | GSum iops             -> let ff_iop set (iostep, proc) =
                                 let pset = ff set p in
                                 match iostep.inst with
                                 | Read (e, pat)  -> NameSet.union (Expr.frees e) (NameSet.diff pset (Pattern.frees pat))
                                 | Write (ce, ve) -> NameSet.union pset (ff_es NameSet.empty [ce;ve])
                               in
                               List.fold_left ff_iop set iops
    | Par ps                -> List.fold_left ff set ps
  and ff_es set es = List.fold_left NameSet.union set (List.map Expr.frees es)
  in
  ff NameSet.empty proc

(* fold (left) over a process. optp x p delivers Some x' when it knows, None when it doesn't. *)

let optfold (optp: 'a -> process -> 'a option) x =
  let rec ofold x p =
    optp x p |~~ (fun () -> 
      match p.inst with
        | Terminate 
        | GoOnAs      _           -> None
        | WithNew   (_,p) 
        | WithQbit  (_,p)
        | WithLet   (_,p)
        | WithQstep (_,p)
        | TestPoint (_,p)       -> ofold x p
        | Iter      (_,proc,_,p)-> Optionutils.optfold ofold x [proc;p]
        | Cond      (e,p1,p2)   -> Optionutils.optfold ofold x [p1;p2]
        | PMatch    (e,pms)     -> Optionutils.optfold ofold x (List.map snd pms)
        | GSum      iops        -> Optionutils.optfold ofold x (List.map snd iops)
        | Par       ps          -> Optionutils.optfold ofold x ps
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

