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
  | _                                 -> raise (Disaster (Printf.sprintf "(<@-->) %s %s"
                                                                         (string_of_typecxt cxt)
                                                                         (string_of_name n)
                                                         )
                                               )

let new_Unknown pos uk = adorn pos (Unknown (new_unknown uk))
let ntv pos = new_Unknown pos UKall

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
  | Qbit            
  | Qstate          -> t
  | Unknown n       -> (try evaltype cxt (cxt <@>n) with Not_found -> t)
  | Known n         -> t
  | Poly (ns,t')    -> let cxt' = List.fold_left (fun cxt n -> cxt <@->n) cxt ns in
                       adorn (Poly (ns,evaltype cxt' t'))
(*| Range _         -> t *)
  | List t          -> adorn (List (evaltype cxt t))
  | Tuple ts        -> adorn (Tuple (List.map (evaltype cxt) ts))
  | Channel t       -> adorn (Channel (evaltype cxt t))
  | Fun (t1,t2)     -> adorn (Fun (evaltype cxt t1, evaltype cxt t2))
  | Process ts      -> adorn (Process (List.map (evaltype cxt) ts))

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

(* ***************************** rewriting stuff ********************************* *)

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
                                    | UG_H | UG_F | UG_G | UG_I | UG_X | UG_Y | UG_Z | UG_Cnot 
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
  | Cond     (e, p1, p2)    -> rewrite_expr cxt e; rewrite_process cxt p1; rewrite_process cxt p2
  | PMatch    (e,pms)       -> rewrite_expr cxt e; 
                               List.iter (fun (pat,proc) -> rewrite_pattern cxt pat; rewrite_process cxt proc) pms
  | GSum     gs             -> let rewrite_g (iostep, proc) =
                                 rewrite_iostep cxt iostep; rewrite_process cxt proc
                               in
                               List.iter (rewrite_g) gs
  | Par      ps             -> List.iter (rewrite_process cxt) ps

let rewrite_def cxt def = 
  match def with
  | Processdef  (n, params, proc) ->
      rewrite_params cxt params; rewrite_process cxt proc
  | Functiondefs fdefs            ->
      let rewrite_fdef (n, pats, toptr, expr) =
        let nt = (try evaltype cxt (cxt <@>n.inst) 
                  with Not_found -> raise (Can'tHappen (Printf.sprintf "%s: %s not in cxt %s"
                                                                       (string_of_sourcepos n.pos)
                                                                       (string_of_name n.inst)
                                                                       (string_of_typecxt cxt)
                                                       )
                                          )
                 )
        in
        let doit cxt rt = rewrite_fparams cxt pats; rewrite_expr cxt expr; toptr := Some (evaltype cxt rt) in
        (* let freeprimetvs t = let set = freetvs t in NameSet.filter (fun n -> Stringutils.starts_with n "'") set in
        let freeset = NameMap.fold (fun n t set -> NameSet.union set (freeprimetvs t)) cxt.tmap NameSet.empty in
        if not (NameSet.is_empty freeset) then 
          raise (Can'tHappen (string_of_sourcepos n.pos ^": cxt=" ^ string_of_typecxt cxt ^ "\nfrees " ^ NameSet.to_string freeset)); *)
        doit cxt (result_type n.pos pats nt)
      in
      List.iter rewrite_fdef fdefs
      
(* ********************************************** unification stuff ******************************** *)

(* useful in error messages *)
let pickdiff cxt t t1 t2 = 
  let t = evaltype cxt t in
  let t1 = evaltype cxt t1 in
  let t2 = evaltype cxt t2 in
  if t=t1 then t2 else t1
  
let rec unifytypes cxt t1 t2 = 
  let t1 = evaltype cxt t1 in
  let t2 = evaltype cxt t2 in
  if !verbose then
    Printf.printf "unifytypes %s (%s) (%s)\n\n"
                  (short_string_of_typecxt cxt)
                  (string_of_type t1)
                  (string_of_type t2);
  let exn = TypeUnifyError (t1,t2) in
  let ut n t =
    let kind = kind_of_unknown n in
    (if kind=UKall then cxt else force_kind kind cxt t) <@+> (n,t)
  in
  match t1.inst, t2.inst with
  | Unknown n1      , Unknown n2        -> if n1=n2 then cxt 
                                           else cxt <@+> (if kind_includes (kind_of_unknown n1) (kind_of_unknown n2) 
                                                          then (n1,t2) 
                                                          else (n2,t1)
                                                         )
  | Unknown n1      , _                 -> if canunifytype n1 cxt t2 then ut n1 t2 else raise exn
  | _               , Unknown n2        -> if canunifytype n2 cxt t1 then ut n2 t1 else raise exn
  | Tuple t1s       , Tuple t2s             
  | Process t1s     , Process t2s       -> unifylists exn cxt t1s t2s 
  | Channel t1      , Channel t2        
  | List t1         , List t2           -> (* (try *)unifytypes cxt t1 t2(* with _ -> raise exn)*)
  | Fun (t1a,t1b)   , Fun (t2a,t2b)     -> unifylists exn cxt [t1a;t1b] [t2a;t2b]
(*| Range (i,j)     , Range (m,n)       -> if m<=i && j<=n then cxt else raise exn *)
  | _                                   -> if t1.inst=t2.inst then cxt else raise exn

and unifypair cxt (t1,t2) = unifytypes cxt t1 t2

and unifylists exn cxt t1s t2s = 
  let pairs = try List.combine t1s t2s with Invalid_argument _ -> raise exn in
  List.fold_left unifypair cxt pairs

(* canunify checks that a type doesn't contain Unknown n; also that equnknowns don't get unified with qbits, functions and such;
   and now also that channel types are qbit or classical and that classicals are classical. ISWIM
 *)  
and canunifytype n cxt t =
  let bad () = 
    let s = match kind_of_unknown n with
            | UKclass -> "a classical type"
            | UKeq    -> "an equality type"
            | UKchan  -> "suitable for a channel"
            | UKall   -> " (whoops: can't happen)"
    in
    raise (Error (t.pos, string_of_type t ^ " is not " ^ s))
  in
  let rec check kind t = 
    let rec cu t = 
      match kind, t.inst with
      | _       , Unknown n'  -> (match eval cxt n' with
                                  | None    -> n<>n'
                                  | Some t' -> cu t'
                                 )
      | _       , Known n'    -> kind_includes kind (kind_of_unknown n')
      | _       , Unit
      | _       , Int
      | _       , Bool
      | _       , Char
      | _       , String
      | _       , Bit 
      | _       , Basisv   
   (* | _       , Range   _ *)
      | _       , Gate    _   -> true
     
      | UKchan  , Qbit        -> true
      | UKchan  , Channel t'  -> cu t'
      | UKchan  , _           -> check UKclass t
      
      | UKeq    , Qbit        
      | UKeq    , Qstate      
      | UKeq    , Channel _   
      | UKeq    , Fun     _   
      | UKeq    , Poly    _      (* Poly types are function types *)
      | UKeq    , Process _   -> bad ()
      
      | UKclass, Qbit        -> bad ()
      
      | UKall   , Qbit        -> true
      | _       , Qstate      -> true
      | _       , Tuple ts    -> List.for_all cu ts
      | _       , Fun (t1,t2) -> check UKall t1 && check UKall t2 (* only the TypeVars matter *)
      | _       , Process ts  -> List.for_all (check UKall) ts
      | _       , List t      -> cu t
      | _       , Channel t   -> check UKchan t                (* why not? *)
      | _       , Poly (ns,t) -> true                           (* Poly types have no free variables *) 
    in
    cu t
  in
  check (kind_of_unknown n) t

(* force_kind unifies the unknowns in t with appropriate unknowns *)  
and force_kind kind cxt t =
  let rec fk cxt t =
    match t.inst with
    | Unknown n'      -> (match eval cxt n' with
                          | None    -> if kind_includes kind (kind_of_unknown n') then cxt else
                                       (let n'' = new_Unknown t.pos kind in cxt <@+> (n',n''))
                          | Some t' -> fk cxt t'
                         )
    | Tuple ts        -> List.fold_left fk cxt ts
    | List t          -> fk cxt t
    | Int
    | Bool
    | Char
    | String
    | Bit 
    | Unit
    | Basisv   
    | Known   _
 (* | Range   _ *)
    | Gate    _       
    | Qbit            
    | Qstate          
    | Fun _           
    | Process _       
    | Channel _       
    | Poly _          -> cxt 
  in
  fk cxt t
  
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
                            | PatH| PatF | PatG | PatI | PatX | PatY | PatZ 
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

;; (* to give typecheck_pats and assigntype_pat a polytype *)

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
                                         | UG_H | UG_F | UG_G | UG_I | UG_X | UG_Y | UG_Z | UG_Cnot 
                                                        -> cxt
                                         | UG_Phi e       -> assigntype_expr cxt (adorn_x e (* Range (0,3) *)Int) e
                               in
                               unifytypes cxt t (adorn_x e (Gate(arity_of_ugate ug)))
     | EVar    n            -> assigntype_name e.pos cxt t n
     | EApp    (e1,e2)      -> let atype = ntv e2.pos in
                               let rtype = new_Unknown e.pos UKclass in
                               let ftype = adorn_x e1 (Fun (atype, rtype)) in
                               let cxt = unifytypes cxt rtype t in
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
                               let tc cxt e = assigntype_expr cxt t e in
                               typecheck_pats tc cxt et ems
     | ECond  (c,e1,e2)     -> ternary cxt t (adorn_x c Bool) t t c e1 e2
     | EArith (e1,_,e2)     -> binary cxt (adorn_x e Int)  (adorn_x e1 Int)  (adorn_x e2 Int)  e1 e2
     | ECompare (e1,op,e2)  -> (match op with 
                                   | Eq | Neq ->
                                       let t = new_Unknown e1.pos UKeq in
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
  | EDFun (wfn,wfpats,wtoptr,we) -> ok_funname wfn;
                                    check_distinct_fparams wfpats;
                                    let tf, tr = inventtype_fun wfpats !wtoptr we in
                                    let cxt = cxt <@++> (wfn.inst,tf) in
                                    let cxt = assigntype_fun cxt tf wfpats we in
                                    let rt = new_Unknown we.pos UKclass in
                                    let cxt = unifytypes cxt rt tr in
                                    let cxt = assigntype_expr cxt t e in
                                    wtoptr := Some tr;
                                    cxt <@--> wfn.inst

and inventtype_fun pats topt e = 
  let rec itf = function
  | pat::pats'  -> let ta = inventtype_pat pat in
                   let tr, trall = itf pats' in
                   adorn (pos_of_instances pats) (Fun (ta,tr)), trall
  | []          -> let tr = match topt with 
                            | None   -> new_Unknown e.pos UKclass
                            | Some t -> t
                    in tr, tr
  and inventtype_pat pat =
    match !(pat.inst.ptype) with
      | Some t -> t
      | None   -> match pat.inst.pnode with
                  | PatName _ 
                  | PatAny          -> ntv pat.pos
                  | PatUnit         -> adorn pat.pos Unit
                  | PatTuple pats   -> let itp ts pat = inventtype_pat pat :: ts in
                                       let ts = List.fold_left itp [] pats in
                                       adorn pat.pos (Tuple (List.rev ts))
                  | _               -> raise (Can'tHappen (Printf.sprintf "inventtype_pat %s" (string_of_pattern pat)))
  in 
  let t, tr = itf pats in
  let vs = NameSet.union (freetvs t) (freetvs tr) in
  (* change the knowns to new unknowns *)
  let assoc = List.map (fun v -> v, new_Unknown dummy_spos (kind_of_unknown v)) (NameSet.elements vs) in
  Type.rewrite assoc t, Type.rewrite assoc tr
  
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
  if !verbose then
    Printf.printf "assigntype_fun %s (%s) [%s] (%s)\n\n"
                  (short_string_of_typecxt cxt)
                  (string_of_type (evaltype cxt t))
                  (string_of_list string_of_fparam " " pats)
                  (string_of_expr e);
  match pats with
  | pat::pats'  -> let ta = ntv pat.pos in
                   let tr = new_Unknown (pos_of_instances pats') UKclass in
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
                          unify_paramtype cxt rt (adorn pos (Channel (new_Unknown pos UKchan))) 
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

and typecheck_pdef cxt def =
  let cxt =
    match def with 
      | Processdef (pn,params,proc) -> 
          if !verbose then
            Printf.printf "typecheck_pdef %s\n  %s\n\n" 
                           (short_string_of_typecxt cxt)
                           (string_of_def def);
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
          let r = List.fold_left (fun cxt (t,{inst=n,rt}) -> unifytypes cxt t (_The !rt)) cxt tps in
          if !verbose then
            (rewrite_def cxt def;
             Printf.printf "after typecheck_def, def = %s\n\ncxt = %s\n\n" 
                           (string_of_def def) 
                           (short_string_of_typecxt cxt)
            );
          r
      | Functiondefs _ -> cxt
   in
   cxt
      
let make_library_cxt () =
  let knownassoc = List.map (fun (n,t,_) -> n, generalise (Parseutils.parse_typestring t)) !Interpret.knowns in
  let cxt = new_cxt (NameMap.of_assoc knownassoc) in
  let typ = adorn dummy_spos in
  let cxt = if cxt <@?> "dispose" then cxt else cxt <@+> ("dispose", typ (Channel (typ Qbit))) in
  let cxt = if cxt <@?> "out"     then cxt else cxt <@+> ("out"    , typ (Channel (typ (List (typ String))))) in
  let cxt = if cxt <@?> "outq"    then cxt else cxt <@+> ("outq"   , typ (Channel (typ Qstate))) in
  let cxt = if cxt <@?> "in"      then cxt else cxt <@+> ("in"     , typ (Channel (typ String))) in
  cxt

let typecheck_fdefs cxt = function
  | Processdef   _     -> cxt
  | Functiondefs fdefs -> 
      let precxt cxt (fn,pats,toptr,e) =
        ok_funname fn;
        check_distinct_fparams pats;
        let t, rt = inventtype_fun pats !toptr e in
        toptr := Some rt;
        cxt <@+> (fn.inst, t)
      in
      let fns = List.map (fun (fn,_,_,_) -> fn) fdefs in
      let rec check_unique_fns = function
        | fn::fns -> List.iter (fun fn' -> if fn.inst=fn'.inst then raise (Error (fn'.pos, "duplicate function definition"))) fns;
                     check_unique_fns fns
        | []      -> ()
      in
      check_unique_fns fns;
      let cxt = List.fold_left precxt cxt fdefs in
      let tc_fdef cxt (fn,pats,topt,expr) = 
        let env_type = cxt<@>fn.inst in
        (* force classical result type *)
        let rt = result_type fn.pos pats env_type in
        let rtv = new_Unknown rt.pos UKclass in
        let cxt = unifytypes cxt rtv rt in
        evalcxt (assigntype_fun cxt (Type.instantiate env_type) pats expr)
      in
      let cxt = List.fold_left tc_fdef cxt fdefs in
      let postcxt cxt fn =  
        let t = evaltype cxt (cxt<@>fn.inst) in
        cxt <@+> (fn.inst, generalise t)
      in
      List.fold_left postcxt cxt fns
      
let precheck_pdef cxt = function
  | Processdef   (pn,ps,_) -> 
      ok_procname pn;
      let process_param param = 
        let n,rt = param.inst in
        let unknown = new_unknown UKchan in
        match !rt with
        | None   -> adorn param.pos (Unknown unknown)
        | Some t -> if (match t.inst with Poly _ -> true | _ -> false) ||
                       not (NameSet.is_empty (Type.freetvs t)) 
                    then raise (Error (t.pos, "process parameter cannot be given a polytype or an unknown type"))
                    else
                    if not (canunifytype unknown cxt t) 
                    then raise (Error (t.pos, "parameter type must be qbit, ^qbit or classical"))
                    else t
      in
      let process_params = List.map process_param in
      if cxt<@?>pn.inst 
      then raise (Error (pn.pos,
                         Printf.sprintf "there is a previous definition of %s" 
                                        (string_of_name pn.inst)
                        )
                 )
      else cxt <@+> (pn.inst, (adorn pn.pos (Process (process_params ps))))
  | Functiondefs _         -> cxt

let typecheck defs =
  try push_verbose !verbose_typecheck (fun () ->
        let cxt = make_library_cxt () in
        (* put the process names in cxt *)
        let cxt = List.fold_left precheck_pdef cxt defs in
        (* do the function defs in order and in groups *)
        let cxt = List.fold_left typecheck_fdefs cxt defs in
        (* do the process defs *)
        let cxt = List.fold_left typecheck_pdef cxt defs in
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
