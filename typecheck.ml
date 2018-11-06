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
open Sourcepos
open Name
open Type
open Listutils
open Optionutils
open Functionutils
open Tupleutils
open Expr
open Instance
open Def
open Param
open Process
open Step
open Pattern

exception TypeUnifyError of _type * _type
exception Error of sourcepos * string
exception Undeclared of sourcepos * name
exception Disaster of string

(* converting to NameMap rather than assoc list for type contexts, 
   because resourcing needs a map of all typevars, obvs.
   
   Have to play games to get assoc list behaviour, allowing a binding to be over-ridden 
   with <@++> and then restored with <@-->.
 *)
type typecxt         = {tpushes: (name*_type option) list; tmap: _type NameMap.t}

let string_of_typecxt cxt = 
  Printf.sprintf "(%s,%s)" 
                 (bracketed_string_of_list (string_of_pair string_of_name (string_of_option string_of_type) ":") cxt.tpushes)
                 (NameMap.to_string string_of_type cxt.tmap)

let new_cxt tmap = {tpushes=[]; tmap=tmap}

let (<@>) cxt n      = NameMap.find n cxt.tmap       
let (<@+>) cxt (n,t) = {cxt with tmap=NameMap.add n t cxt.tmap}      
let (<@->) cxt n     = {cxt with tmap=NameMap.remove n cxt.tmap}     
let (<@?>) cxt n     = NameMap.mem n cxt.tmap        

let (<@++>) cxt (n,t) = (* push binding *)
  let oldt = try Some (cxt <@> n) with Not_found -> None in
  {(cxt <@+> (n,t)) with tpushes=(n,oldt)::cxt.tpushes}
  
let (<@-->) cxt n = (* pop binding *)
  match cxt.tpushes with
  | (n',Some t)::tpushes when n'=n -> {(cxt <@+> (n,t)) with tpushes=tpushes}
  | (n',None  )::tpushes when n'=n -> {(cxt <@-> n    ) with tpushes=tpushes}
  | _                              -> raise (Disaster (Printf.sprintf "(<@-->) %s %s"
                                                                      (string_of_typecxt cxt)
                                                                      (string_of_name n)
                                                      )
                                            )

let new_TypeVar () = TypeVar (new_unknown_name ())
let ntv pos = adorn pos (new_TypeVar ())

let rec eval cxt n =
  try Some (evaltype cxt (cxt <@> n)) with Not_found -> None

and evaltype cxt t = 
  let adorn tnode = {pos=t.pos; inst=tnode} in
  match t.inst with
  | Unit
  | Int
  | Bool
  | Char
  | String
  | Bit 
  | Basisv
  | Gate    _       
  | Qbit            -> t
  | TypeVar n       -> (try evaltype cxt (cxt <@> string_of_name n) with Not_found -> t)
  | Univ (ns,t')    -> let cxt = List.fold_left (fun cxt n -> cxt <@-> (string_of_name n)) cxt ns in
                       adorn (Univ (ns,evaltype cxt t'))
  (* | Range _         -> t *)
  | List t          -> adorn (List (evaltype cxt t))
  | Tuple ts        -> adorn (Tuple (List.map (evaltype cxt) ts))
  | Channel t       -> adorn (Channel (evaltype cxt t))
  | Fun (t1,t2)     -> adorn (Fun (evaltype cxt t1, evaltype cxt t2))
  | Process ts      -> adorn (Process (List.map (evaltype cxt) ts))

let rec rewrite_expr cxt e =
  match !(e.inst.etype) with
  | Some t -> 
      (e.inst.etype := Some (evaltype cxt t);
       match e.inst.enode with
       | EUnit
       | ENil
       | EVar        _
       | EInt        _
       | EBool       _
       | EChar       _
       | EString     _
       | EBit        _          
       | EBasisv     _          -> ()
       | EGate       ug         -> (match ug.inst with
                                    | UG_H | UG_FG | UG_I | UG_X | UG_Y | UG_Z | UG_Cnot 
                                                    -> ()
                                    | UG_Phi e      -> rewrite_expr cxt e
                                   )
       | EMinus      e          
       | ENot        e          -> rewrite_expr cxt e
       | ETuple      es         -> List.iter (rewrite_expr cxt) es
       | ECond       (e1,e2,e3) -> List.iter (rewrite_expr cxt) [e1;e2;e3]
       | EMatch      (e,ems)    -> rewrite_expr cxt e; 
                                   List.iter (fun (pat,e) -> rewrite_pattern cxt pat; rewrite_expr cxt e) ems
       | ECons       (e1,e2)
       | EApp        (e1,e2)     
       | EAppend     (e1,e2)    -> List.iter (rewrite_expr cxt) [e1;e2]
       | EArith      (e1,_,e2)   
       | ECompare    (e1,_,e2)   
       | EBoolArith  (e1,_,e2)  -> List.iter (rewrite_expr cxt) [e1;e2]
       | ELambda     (pats, e)  -> List.iter (rewrite_pattern cxt) pats; rewrite_expr cxt e
       | EWhere      (e,ed)     -> rewrite_expr cxt e; rewrite_edecl cxt ed
      )
  | None   -> raise (Error (e.pos,
                            Printf.sprintf "** Disaster: typecheck didn't mark %s"
                                           (string_of_expr e)
                           )
                    )

and rewrite_edecl cxt = function
  | EDPat (wpat,_,we)        -> rewrite_pattern cxt wpat; rewrite_expr cxt we
  | EDFun (wfn,wfpats,_, we) -> rewrite_fparams cxt wfpats; rewrite_expr cxt we

and rewrite_fparams cxt = List.iter (rewrite_pattern cxt)

and rewrite_pattern cxt p =
  match !(p.inst.ptype) with
  | Some t -> 
      (p.inst.ptype := Some (evaltype cxt t);
       match p.inst.pnode with
       | PatAny
       | PatName    _
       | PatUnit
       | PatNil
       | PatBit     _
       | PatInt     _
       | PatBool    _
       | PatChar    _
       | PatString  _
       | PatBasisv  _
       | PatGate    _       -> ()
       | PatCons    (ph,pt) -> List.iter (rewrite_pattern cxt) [ph;pt]
       | PatTuple   ps      -> List.iter (rewrite_pattern cxt) ps
       
      )
  | None   -> raise (Error (p.pos,
                            Printf.sprintf "** Disaster: typecheck didn't mark %s"
                                           (string_of_pattern p)
                           )
                    )

let rewrite_param cxt {inst=n,rt} =
  match !rt with
  | Some t -> rt := Some (evaltype cxt t)
  | _      -> ()
  
let rewrite_params cxt = List.iter (rewrite_param cxt)

let rewrite_qstep cxt qstep = 
  match qstep.inst with
  | Measure   (e,ges,pattern) -> rewrite_expr cxt e; List.iter (rewrite_expr cxt) ges;
                                 rewrite_pattern cxt pattern
  | Ugatestep (es, ug)        -> List.iter (rewrite_expr cxt) es; rewrite_expr cxt ug

let rewrite_iostep cxt iostep = 
  match iostep.inst with
  | Read      (ce,pat)    -> rewrite_expr cxt ce; rewrite_pattern cxt pat
  | Write     (ce,e)      -> rewrite_expr cxt ce; rewrite_expr cxt e 

let rec rewrite_process cxt proc = 
  match proc.inst with
  | Terminate               -> ()
  | Call      (n,es)        -> List.iter (rewrite_expr cxt) es
  | WithNew   (params, p)   -> rewrite_params cxt params; rewrite_process cxt p
  | WithQbit  (qss, p)      -> List.iter (rewrite_param cxt <.> fst) qss; rewrite_process cxt p
  | WithLet  ((pat,e), p)   -> rewrite_pattern cxt pat; rewrite_expr cxt e; rewrite_process cxt p
  | WithQstep (qstep, p)    -> rewrite_qstep cxt qstep; rewrite_process cxt p
  | WithExpr (e,p)          -> rewrite_expr cxt e; rewrite_process cxt p
  | Cond     (e, p1, p2)    -> rewrite_expr cxt e; rewrite_process cxt p1; rewrite_process cxt p2
  | PMatch    (e,pms)       -> rewrite_expr cxt e; 
                               List.iter (fun (pat,proc) -> rewrite_pattern cxt pat; rewrite_process cxt proc) pms
  | GSum     gs             -> let rewrite_g (iostep, proc) =
                                 rewrite_iostep cxt iostep; rewrite_process cxt proc
                               in
                               List.iter (rewrite_g) gs
  | Par      ps             -> List.iter (rewrite_process cxt) ps

let rewrite_def cxt = function
  | Processdef (n, params, proc) ->
      rewrite_params cxt params; rewrite_process cxt proc
  | Functiondef (n, pats, _, expr) ->
      rewrite_fparams cxt pats; rewrite_expr cxt expr
  
(* useful in error messages *)
let pickdiff cxt t t1 t2 = 
  let t = evaltype cxt t in
  let t1 = evaltype cxt t1 in
  let t2 = evaltype cxt t2 in
  if t=t1 then t2 else t1
  
let rec unifytypes cxt t1 t2 = 
  let t1 = evaltype cxt t1 in
  let t2 = evaltype cxt t2 in
  let exn = TypeUnifyError (t1,t2) in 
  match t1.inst, t2.inst with
  | TypeVar n1      , TypeVar n2        -> if n1=n2 then cxt else cxt <@+> (n1,t2)
  | TypeVar n1      , _                 -> if canunifytype n1 cxt t2 then cxt <@+> (n1,t2) else raise exn
  | _               , TypeVar n2        -> if canunifytype n2 cxt t1 then cxt <@+> (n2,t1) else raise exn
  | Tuple t1s       , Tuple t2s             
  | Process t1s     , Process t2s       -> unifylists exn cxt t1s t2s 
  | Channel t1      , Channel t2        
  | List t1         , List t2           -> (try unifytypes cxt t1 t2 with _ -> raise exn)
  | Fun (t1a,t1b)   , Fun (t2a,t2b)     -> unifylists exn cxt [t1a;t1b] [t2a;t2b]
  (* | Range (i,j)     , Range (m,n)       -> (* presuming t2 is the context ... *)
                                           if m<=i && j<=n then cxt else raise exn *)
  | _                                   -> if t1.inst=t2.inst then cxt else raise exn

and unifypair cxt (t1,t2) = unifytypes cxt t1 t2

and unifylists exn cxt t1s t2s = 
  let pairs = try List.combine t1s t2s with Invalid_argument _ -> raise exn in
  List.fold_left unifypair cxt pairs

(* canunify checks that a type doesn't contain TypeVar n *)  
and canunifytype n cxt t = 
  match t.inst with
  | Int
  | Bool
  | Char
  | String
  | Bit 
  | Unit
  | Qbit 
  | Basisv   
  (* | Range   _ *)
  | Gate    _       -> true
  | TypeVar n'      -> (match eval cxt n' with
                        | None    -> n<>n'
                        | Some t' -> canunifytype n cxt t'
                       )
  | Process ts       
  | Tuple ts        -> List.for_all (canunifytype n cxt) ts
  | Fun (t1,t2)     -> canunifytype n cxt t1 && canunifytype n cxt t2
  | Channel t      
  | List t          -> canunifytype n cxt t
  | Univ (ns,t)     -> List.mem n ns || canunifytype n cxt t
  
(* when you think you have a complete type context, simplify it with evalcxt. 
   Once threw away TypeVars: now it just shortens lookups. 
 *)
let evalcxt cxt = 
  let tpushes = List.map (fun (n,t) -> n, t &~~ (_Some <.> evaltype cxt)) cxt.tpushes in
  let tmap = NameMap.map (evaltype cxt) cxt.tmap in
  {tpushes=tpushes; tmap=tmap}

let short_string_of_typecxt cxt = 
  let cxt = evalcxt cxt in
  let tmap = NameMap.filter (fun n t -> not (Stringutils.starts_with n "?")) cxt.tmap in
  string_of_typecxt {cxt with tmap=tmap}

(* *************************** typechecker starts here ********************************* *)

let rec typecheck_pats tc cxt t pxs =
   if !verbose then 
     Printf.printf "typecheck_pats ... %s (%s) %s\n\n"
                   (short_string_of_typecxt cxt)
                   (string_of_type t)
                   (bracketed_string_of_list (string_of_pair string_of_pattern (fun _ -> "") "") pxs);
   List.fold_left (fun cxt (pat, x) -> assigntype_pat ((revargs tc) x) cxt t pat) cxt pxs
   
and assigntype_pat contn cxt t p =
  if !verbose then
    Printf.printf "assigntype_pat ... %s (%s) (%s)\n\n"
                  (short_string_of_typecxt cxt)
                  (string_of_type t)
                  (string_of_pattern p);
  let cxt = match !(p.inst.ptype) with
            | Some pt -> unifytypes cxt t pt
            | None    -> p.inst.ptype := Some t; cxt
  in
  try match p.inst.pnode with
      | PatAny          -> contn cxt
      | PatName n       -> let cxt = contn (cxt<@++>(n,t)) in cxt<@-->n
      | PatUnit         -> contn (unifytypes cxt t (adorn p.pos Unit))
      | PatNil          -> let vt = ntv p.pos in
                           let lt = adorn p.pos (List vt) in
                           contn (unifytypes cxt t lt)
      | PatInt _        -> contn (unifytypes cxt t (adorn p.pos Int))
      | PatBit _        -> contn (unifytypes cxt t (adorn p.pos Bit))
      | PatBool _       -> contn (unifytypes cxt t (adorn p.pos Bool))
      | PatChar _       -> contn (unifytypes cxt t (adorn p.pos Char))
      | PatString _     -> contn (unifytypes cxt t (adorn p.pos String))
      | PatBasisv _     -> contn (unifytypes cxt t (adorn p.pos Basisv))
      | PatGate pg      -> (match pg.inst with
                            | PatH| PatFG | PatI | PatX | PatY | PatZ 
                                                    -> contn (unifytypes cxt t (adorn p.pos (Gate (1))))
                            | PatCnot               -> contn (unifytypes cxt t (adorn p.pos (Gate (2))))
                            | PatPhi p              -> let pt = adorn p.pos Int in
                                                       let cxt = unifytypes cxt t (adorn p.pos (Gate(1))) in
                                                       assigntype_pat contn cxt pt p
                           ) 
      | PatCons (ph,pt) -> let vt = ntv ph.pos in
                           let lt = adorn p.pos (List vt) in
                           let cf cxt = 
                             assigntype_pat contn cxt t pt
                           in
                           let cxt = unifytypes cxt t lt in
                           assigntype_pat cf cxt vt ph
      | PatTuple ps     -> let ts = List.map (fun p -> ntv p.pos) ps in
                           let cxt = unifytypes cxt t (adorn p.pos (Tuple ts)) in
                           let rec tc cxt = function
                             | (p,t)::pts -> assigntype_pat ((revargs tc) pts) cxt t p
                             | []         -> contn cxt
                           in
                           tc cxt (zip ps ts)
  with TypeUnifyError _ -> raise (Error (p.pos,
                                         Printf.sprintf "cannot assign type %s to pattern %s"
                                                        (string_of_type (evaltype cxt t))
                                                        (string_of_pattern p)
                                        )
                                 )

;; (* to give typecheck_pats and assigntype_pat a universal type *)

let rec assigntype_name pos cxt t n =
  match eval cxt n with
  | Some t' -> 
      let t' = Type.instantiate t' in
      (try unifytypes cxt t t' 
       with TypeUnifyError(t1,t2) -> 
         raise (Error (pos,
                       Printf.sprintf "(unifying types %s and %s for %s): can't (sub-)unify %s and %s"
                                      (string_of_type (evaltype cxt t))
                                      (string_of_type (evaltype cxt t'))
                                      (string_of_name n)
                                      (string_of_type (evaltype cxt t1))
                                      (string_of_type (evaltype cxt t2))
                      )
               )
      )
  | None    -> raise (Undeclared (pos, n))

and assigntype_expr cxt t e =
  if !verbose then
    Printf.printf "assigntype_expr %s (%s) (%s)\n\n"
                  (short_string_of_typecxt cxt)
                  (string_of_type (evaltype cxt t))
                  (string_of_expr e);
  e.inst.etype := Some t; (* for rewriting later *)
  let utaf cxt = uncurry2 (assigntype_expr cxt) in
  try 
    let unary cxt tout tin e = 
       let cxt = unifytypes cxt t tout in
       try assigntype_expr cxt tin e 
       with TypeUnifyError (t1,t2) -> 
         raise (Error(e.pos,
                      Printf.sprintf "%s should be %s but is actually %s"
                                     (string_of_expr e)
                                     (string_of_type (evaltype cxt tin))
                                     (string_of_type (pickdiff cxt tin t1 t2))
                     )
                )
     in
     let binary cxt tout tin1 tin2 f1 f2 =
       let cxt = unary cxt tout tin1 f1 in
       unary cxt tout tin2 f2
     in
     let ternary cxt tout tin1 tin2 tin3 f1 f2 f3 =
       let cxt = binary cxt tout tin1 tin2 f1 f2 in
       unary cxt tout tin3 f3
     in
     match e.inst.enode with
     | EUnit                -> unifytypes cxt t (adorn_x e Unit)
     | ENil                 -> unifytypes cxt t (adorn_x e (List (ntv e.pos)))
     | EInt i               -> (match (evaltype cxt t).inst with 
                                | Bit              -> if i=0||i=1 then cxt
                                                      else unifytypes cxt t (adorn_x e Int)
                                (* | Range (j,k) as t -> if j<=i && i<=k then cxt 
                                                      else unifytypes cxt (adorn_x e t) (adorn_x e Int) *)
                                | t                -> unifytypes cxt (adorn_x e t) (adorn_x e Int)
                               )
     | EBool _              -> unifytypes cxt t (adorn_x e Bool)
     | EChar _              -> unifytypes cxt t (adorn_x e Char)
     | EString _            -> unifytypes cxt t (adorn_x e String)
     | EBit b               -> (match (evaltype cxt t).inst with 
                                | Int              -> cxt
                                (* | Range (j,k) as t -> let i = if b then 1 else 0 in
                                                      if j<=i && i<=k then cxt 
                                                      else unifytypes cxt (adorn_x e t) (adorn_x e Bit) *)
                                | t                -> unifytypes cxt (adorn_x e t) (adorn_x e Bit)
                               )
     | EBasisv _            -> unifytypes cxt t (adorn_x e Basisv)
     | EGate   ug           -> let cxt = match ug.inst with
                                         | UG_H | UG_FG | UG_I | UG_X | UG_Y | UG_Z | UG_Cnot 
                                                        -> cxt
                                         | UG_Phi e       -> assigntype_expr cxt (adorn_x e (* Range (0,3) *)Int) e
                               in
                               unifytypes cxt t (adorn_x e (Gate(arity_of_ugate ug)))
     | EVar    n            -> assigntype_name e.pos cxt t n
     | EApp    (e1,e2)      -> let atype = ntv e2.pos in
                               let ftype = adorn_x e1 (Fun (atype, t)) in
                               let cxt = assigntype_expr cxt ftype e1 in 
                               assigntype_expr cxt atype e2
     | EMinus  e            -> unary cxt (adorn_x e Int) (adorn_x e Int) e
     | ENot    e            -> unary cxt (adorn_x e Bool) (adorn_x e Bool) e
     | ETuple  es           -> let ts = List.map (fun e -> ntv e.pos) es in
                               let tes = List.combine ts es in
                               let cxt' = List.fold_left utaf cxt tes in
                               unifytypes cxt' t (adorn_x e (Tuple ts))
     | ECons   (hd,tl)      -> let t' = ntv e.pos in
                               let cxt = assigntype_expr cxt t' hd in
                               let t'' = (adorn_x e (List t')) in
                               let cxt = assigntype_expr cxt t'' tl in
                               unifytypes cxt t t''
     | EMatch (e,ems)       -> let et = ntv e.pos in
                               let cxt = assigntype_expr cxt et e in
                               let tc cxt e = 
                                 assigntype_expr cxt t e
                               in
                               typecheck_pats tc cxt et ems
     | ECond  (c,e1,e2)     -> ternary cxt t (adorn_x c Bool) t t c e1 e2
     | EArith (e1,_,e2)     -> binary cxt (adorn_x e Int)  (adorn_x e1 Int)  (adorn_x e2 Int)  e1 e2
     | ECompare (e1,op,e2)  -> (match op with 
                                   | Eq | Neq ->
                                       let t = ntv e1.pos in
                                       binary cxt (adorn_x e Bool) t t e1 e2
                                   | _ ->
                                       binary cxt (adorn_x e Bool) (adorn_x e1 Int) (adorn_x e2 Int)  e1 e2
                                  )
     | EBoolArith (e1,_,e2) -> binary cxt (adorn_x e Bool)  (adorn_x e1 Bool)  (adorn_x e2 Bool)  e1 e2
     | EAppend (e1,e2)      -> let t' = adorn_x e (List (ntv e.pos)) in
                               let cxt = assigntype_expr cxt t' e1 in
                               let cxt = assigntype_expr cxt t' e2 in
                               unifytypes cxt t t'
     | ELambda (pats, e)    -> check_distinct_fparams pats; assigntype_fun cxt t pats e
     | EWhere  (e, ed)      -> assigntype_edecl cxt t e ed
  with 
  | TypeUnifyError (t1,t2)  -> raise (Error (e.pos,
                                             Printf.sprintf "%s appears to be type %s, but in context should be %s"
                                                            (string_of_expr e) 
                                                            (string_of_type (evaltype cxt t2))
                                                            (string_of_type (evaltype cxt t1))
                                            )
                                     )
  
and assigntype_edecl cxt t e = function
  | EDPat (wpat,wtopt,we)        -> let wt = ntv we.pos in
                                    let cxt = assigntype_expr cxt wt we in
                                    assigntype_pat (fun cxt -> assigntype_expr cxt t e) cxt wt wpat
  | EDFun (wfn,wfpats,wtopt, we) -> ok_funname wfn;
                                    check_distinct_fparams wfpats;
                                    let tf = inventtype_fun wfpats wtopt we in
                                    let cxt = cxt <@++> (wfn.inst,tf) in
                                    let cxt = assigntype_fun cxt tf wfpats we in
                                    let cxt = assigntype_expr cxt t e in
                                    cxt <@--> wfn.inst

and inventtype_fun pats topt e = 
  let rec itf set = function
  | pat::pats'  -> let set, ta = inventtype_pat set pat in
                   let set, tr = itf set pats' in
                   set, adorn (pos_of_instances pats) (Fun (ta,tr))
  | []          -> (match topt with 
                    | None   -> set, ntv e.pos 
                    | Some t -> NameSet.union set (Type.frees t), t
                   )
  and inventtype_pat set pat =
    match !(pat.inst.ptype) with
      | Some t -> NameSet.union set (Type.frees t), t
      | None   -> match pat.inst.pnode with
                  | PatName _ 
                  | PatAny          -> set, ntv pat.pos
                  | PatUnit         -> set, adorn pat.pos Unit
                  | PatTuple pats   -> let itp (set, ts) pat = 
                                         let set, t = inventtype_pat set pat in
                                         set, t::ts
                                       in
                                       let set, ts = List.fold_left itp (set,[]) pats in
                                       set, adorn pat.pos (Tuple (List.rev ts))
                  | _               -> raise (Can'tHappen (Printf.sprintf "inventtype_pat %s" (string_of_pattern pat)))
  in 
  let set, t = itf NameSet.empty pats in
  if NameSet.is_empty set then t else adorn t.pos (Univ (NameSet.elements set, t))
  
and check_distinct_fparams pats =
  let rec cdfp set pat =
    match pat.inst.pnode with
    | PatName   n -> if NameSet.mem n set then
                       raise (Error (pat.pos,
                                     Printf.sprintf "repeated parameter %s" n
                                    )
                             )
                     else NameSet.add n set
    | PatAny      
    | PatUnit     -> set
    | PatTuple ps -> List.fold_left cdfp set ps
    | _           -> raise (Can'tHappen (Printf.sprintf "check_distinct_fparams %s" (string_of_pattern pat)))
  in
  ignore (List.fold_left cdfp NameSet.empty pats)
  
and assigntype_fun cxt t pats e =
  match pats with
  | pat::pats'  -> let ta = ntv pat.pos in
                   let tr = ntv (pos_of_instances pats') in
                   let tf = adorn (pos_of_instances pats) (Fun (ta,tr)) in
                   let cxt = unifytypes cxt t tf in
                   let contn cxt () = assigntype_fun cxt tr pats' e in
                   typecheck_pats contn cxt ta [pat,()]
  | []          -> assigntype_expr cxt t e
  
and ok_procname n = 
  let c = Stringutils.first n.inst in
  if not ('A' <= c && c <= 'Z') then raise (Error (n.pos, "process name " ^ string_of_name n.inst ^ " should start with upper case"))

and ok_funname n =
  let c = Stringutils.first n.inst in
  if not ('a' <= c && c <= 'z') then raise (Error (n.pos, "function name " ^ string_of_name n.inst ^ " should start with lower case"))

let check_distinct params =
  let check set {inst=n,_} =
    if NameSet.mem n set then 
      raise (Error (pos_of_instances params, 
                    Printf.sprintf "non-distinct parameters (%s)"
                                   (string_of_list string_of_param "," params)
                   )
            )
    else NameSet.add n set
  in
  let _ = List.fold_left check NameSet.empty params in
  ()

let strip_procparams s cxt params = 
  if !verbose then
    Printf.printf "before strip_procparams %s (%s)\n%s\n\n" s (string_of_params params) (short_string_of_typecxt cxt);
  let cxt = List.fold_left (fun cxt p -> cxt<@-->(strip_param p)) cxt (List.rev params) in
  if !verbose then
    Printf.printf "after strip_procparams %s\n\n" (short_string_of_typecxt cxt); 
  cxt

let rec do_procparams s cxt params proc =
  if !verbose then
    Printf.printf "do_procparams %s" (string_of_list string_of_param "," params);
  let process_param {pos=pos; inst=n,rt} = n, fix_paramtype pos rt in
  let cxt = List.fold_left (fun cxt param -> cxt <@++> process_param param) cxt params in
  if !verbose then
    Printf.printf " -> %s\n" (string_of_list string_of_param "," params);
  let cxt = typecheck_process cxt proc in
  strip_procparams s cxt params

and fix_paramtype pos rt =
  match !rt with
  | Some t -> t
  | None   -> let t = ntv pos in rt := Some t; t
  
and unify_paramtype cxt rt t =
  match !rt with
  | Some t' ->               unifytypes cxt t t'
  | None    -> rt := Some t; cxt
  
and typecheck_process cxt p =
  if !verbose then
    Printf.printf "typecheck_process ... %s\n" (short_string_of_process p);
  match p.inst with
  | Terminate     -> cxt
  | Call (n,args) -> 
      ok_procname n;
      let ts = 
        (try let t = evaltype cxt (cxt<@>n.inst) in
             match t.inst with
             | Process ts -> ts
             | _          -> raise (Error (n.pos, string_of_name n.inst ^ " used as process name, but declared as " ^ string_of_type t))
         with _ -> raise (Error (n.pos, "undefined process " ^ string_of_name n.inst))
        )
      in
      let ets = try zip args ts
                with Zip -> 
                       raise (Error (p.pos,
                                     Printf.sprintf "%s: should have %d arguments"
                                                    (string_of_process p)
                                                    (List.length ts)
                                    )
                             )
      in
      List.fold_left (fun cxt (e,t) -> assigntype_expr cxt t e) cxt ets
  | WithNew (params, proc) ->
      (* all the params have to be channels *)
      let cxt = 
        List.fold_left (fun cxt {pos=pos; inst=n,rt} -> 
                          unify_paramtype cxt rt (adorn pos (Channel (ntv pos))) 
                       )
                       cxt
                       params
      in
      check_distinct params;
      do_procparams "WithNew" cxt params proc
  | WithQbit (qss,proc) ->
      let typecheck_qspec cxt ({pos=pos; inst=n,rt}, bvopt) =
        let cxt = unify_paramtype cxt rt (adorn pos Qbit) in
        match bvopt with
        | Some bve -> assigntype_expr cxt (adorn bve.pos Basisv) bve
        | None     -> cxt
      in
      let cxt = List.fold_left typecheck_qspec cxt qss in
      let params = List.map fst qss in
      check_distinct params;
      do_procparams "WithQbit" cxt params proc
  | WithLet ((pat,e),proc) ->
      let t = ntv e.pos in
      let cxt = assigntype_expr cxt t e in
      assigntype_pat (fun cxt -> typecheck_process cxt proc) cxt t pat
  | WithQstep (qstep,proc) ->
      (match qstep.inst with
       | Measure (e, ges, pat) ->
           let cxt = assigntype_expr cxt (adorn e.pos Qbit) e in
           let cxt = List.fold_left (fun cxt ge -> assigntype_expr cxt (adorn ge.pos (Gate 1)) ge) cxt ges in
           assigntype_pat (fun cxt -> typecheck_process cxt proc) cxt (adorn pat.pos Bit) pat
       | Ugatestep (es, uge) ->
           let cxt = List.fold_left (fun cxt e -> assigntype_expr cxt (adorn e.pos Qbit) e) cxt es in
           let arity = List.length es in
           let cxt = assigntype_expr cxt (adorn uge.pos (Gate(arity))) uge in
           typecheck_process cxt proc
      )
  | WithExpr (e, proc) ->
      let cxt = assigntype_expr cxt (adorn e.pos Unit) e in
      typecheck_process cxt proc
  | GSum gs ->
      let check_g cxt (iostep,proc) =
        match iostep.inst with
         | Read (ce, pat) ->
             let t = ntv ce.pos in
             let cxt = assigntype_expr cxt (adorn ce.pos (Channel t)) ce in
             assigntype_pat (fun cxt -> typecheck_process cxt proc) cxt t pat
         | Write (ce, e) ->
             let t = ntv ce.pos in 
             let cxt = assigntype_expr cxt (adorn ce.pos (Channel t)) ce in
             let cxt = assigntype_expr cxt t e in
             typecheck_process cxt proc
      in
      List.fold_left check_g cxt gs
  | Cond (e,p1,p2) ->
      let cxt = assigntype_expr cxt (adorn e.pos Bool) e in
      let cxt = typecheck_process cxt p1 in
      typecheck_process cxt p2
  | PMatch (e,pms)  -> let et = ntv e.pos in
                       let cxt = assigntype_expr cxt et e in
                       typecheck_pats typecheck_process cxt et pms
  | Par (ps)        -> List.fold_left typecheck_process cxt ps

and typecheck_def cxt def =
  if !verbose then
    Printf.printf "typecheck_def %s %s\n\n" 
                   (short_string_of_typecxt cxt)
                   (string_of_def def);
  let cxt =
    match def with 
      | Processdef (pn,params,proc) -> 
          let env_types = match (cxt<@>pn.inst).inst with
                          | Process ts -> ts
                          | _          -> raise (Can'tHappen (Printf.sprintf "%s not a process name"
                                                                             (string_of_name pn.inst)
                                                             )
                                                )
          in
          check_distinct params;
          let cxt = do_procparams "processdef" cxt params proc in
          let cxt = evalcxt cxt in
          let tps = zip env_types params in
          List.fold_left (fun cxt (t,{inst=n,rt}) -> unifytypes cxt t (_The !rt)) cxt tps
      | Functiondef (fn,pats,topt,expr) -> 
          let env_type = let t = cxt<@>fn.inst in
                         match t.inst with
                         | Fun  _
                         | Univ _ -> t
                         | _     -> raise (Can'tHappen (Printf.sprintf "%s not a function name"
                                                                       (string_of_name fn.inst)
                                                       )
                                          )
          in
          evalcxt (assigntype_fun cxt (Type.instantiate env_type) pats expr)
  in
  if !verbose then
    (rewrite_def cxt def;
     Printf.printf "after typecheck_def, def = %s\n\ncxt = %s\n\n" 
                   (string_of_def def) 
                   (short_string_of_typecxt cxt)
    );
   cxt
      
let make_library_cxt () =
  let knownassoc = List.map (fun (n,t,_) -> n, generalise (Parseutils.parse_typestring t)) !Interpret.knowns in
  let cxt = new_cxt (NameMap.of_assoc knownassoc) in
  if cxt <@?> "dispose" then cxt else cxt <@+> ("dispose",adorn dummy_spos (Channel (adorn dummy_spos Qbit)))

      
let typecheck defs =
  try push_verbose !verbose_typecheck (fun () ->
        let cxt = make_library_cxt () in
        let header_type cxt = function
          | Processdef (pn,ps,_) ->
              ok_procname pn;
              let process_param param = 
                let n,rt = param.inst in
                match !rt with
                | None   -> ntv param.pos
                | Some t -> if (match t.inst with Univ _ -> true | _ -> false) ||
                               not (NameSet.is_empty (Type.frees t)) 
                            then raise (Error (t.pos,
                                               Printf.sprintf "Error in %s: process parameter cannot be given a universal type"
                                                              (string_of_param param)
                                              )
                                       );
                            t
              in
              let process_params = List.map process_param in
              if cxt<@?>pn.inst 
              then raise (Error (pn.pos,
                                 Printf.sprintf "there is a previous definition of %s" 
                                                (string_of_name pn.inst)
                                )
                         )
              else cxt <@+> (pn.inst, (adorn pn.pos (Process (process_params ps))))
          | Functiondef (fn,pats,topt,e) ->
              ok_funname fn;
              check_distinct_fparams pats;
              let t = inventtype_fun pats topt e in
              cxt <@+> (fn.inst, t)
        in
        let cxt = List.fold_left header_type cxt defs in
        let cxt = List.fold_left typecheck_def cxt defs in
        List.iter (rewrite_def cxt) defs;
        if !verbose then 
          Printf.printf "typechecked\n\ncxt =\n%s\n\ndefs=\n%s\n\n" 
                        (short_string_of_typecxt cxt)
                        (string_of_list string_of_def "\n\n" defs)
        else
        if !typereport then 
          Printf.printf "fully typed program =\n%s\n\n" (string_of_list string_of_def "\n\n" defs);
      )
  with Undeclared (pos, n) -> raise (Error (pos,
                                            Printf.sprintf "undeclared %s"
                                                           (string_of_name n)
                                           )
                                    )
