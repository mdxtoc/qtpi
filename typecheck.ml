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
open Number

exception TypeUnifyError of _type * _type
exception Error of sourcepos * string
exception Undeclared of sourcepos * name
exception Disaster of string

(* Back to assoc lists. Maps seem to be overkill, now that unknowns are not in the context *)

type typecxt         = (name * _type) list

let string_of_typecxt = 
   bracketed_string_of_list (string_of_pair string_of_name string_of_type "->")

let new_cxt cxt = cxt

let (<@>)  = Listutils.(<@>)       
let (<@+>) = Listutils.(<@+>)       
let (<@->) = Listutils.(<@->)       
let (<@?>) = Listutils.(<@?>)       

let new_Unknown pos uk = adorn pos (Unknown (new_unknown uk))
let ntv pos = new_Unknown pos UnkAll
let newclasstv pos = new_Unknown pos (if !Settings.resourcecheck then UnkClass else UnkAll)
let commU = if !Settings.resourcecheck then UnkComm else UnkAll
let newcommtv pos = new_Unknown pos commU

let rec eval cxt n =
  try Some (evaltype (cxt <@> n)) with Not_found -> None

and evaltype t = 
  let adorn tnode = {pos=t.pos; inst=tnode} in
  let evu = function
    | (_, {contents=Some t}) -> evaltype t
    | _                      -> t
  in
  match t.inst with
  | Unit
  | Num
  | Bool
  | Char
  | String
  | Bit 
  | Basisv
  | Gate            
  | Qbit            
  | Qstate          -> t
  | Unknown u       -> evu u 
  | Known n         -> t
  | OneOf (u, _)    -> evu u
  | Poly (ns,t')    -> adorn (Poly (ns,evaltype t'))
(*| Range _         -> t *)
  | List t          -> adorn (List (evaltype t))
  | Tuple ts        -> adorn (Tuple (List.map evaltype ts))
  | Channel t       -> adorn (Channel (evaltype t))
  | Fun (t1,t2)     -> adorn (Fun (evaltype t1, evaltype t2))
  | Process ts      -> adorn (Process (List.map evaltype ts))

(* when you think you have a complete type context, simplify it with evalcxt. 
   Once threw away TypeVars: now it just shortens lookups. 
 *)
let evalcxt = List.map (fun (n,t) -> n, evaltype t)

let short_string_of_typecxt = string_of_typecxt

(* ***************************** rewriting stuff ********************************* *)

let rec rewrite_expr cxt e =
  match !(e.inst.etype) with
  | Some t -> 
      (e.inst.etype := Some (evaltype t);
       match e.inst.enode with
       | EUnit
       | ENil
       | EVar        _
       | ENum        _
       | EBool       _
       | EChar       _
       | EString     _
       | EBit        _          
       | EBasisv     _          -> ()
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

and rewrite_edecl cxt edecl = 
  match edecl.inst with
  | EDPat (wpat,_,we)        -> rewrite_pattern cxt wpat; rewrite_expr cxt we
  | EDFun (wfn,wfpats,_, we) -> rewrite_fparams cxt wfpats; rewrite_expr cxt we

and rewrite_fparams cxt = List.iter (rewrite_pattern cxt)

and rewrite_pattern cxt p =
  match !(p.inst.ptype) with
  | Some t -> 
      (p.inst.ptype := Some (evaltype t);
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
       | PatBasisv  _       -> ()
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
  | Some t -> rt := Some (evaltype t)
  | _      -> ()
  
let rewrite_params cxt = List.iter (rewrite_param cxt)

let rewrite_qstep cxt qstep = 
  match qstep.inst with
  | Measure   (e,gopt,pattern)  -> rewrite_expr cxt e; (rewrite_expr cxt ||~~ ()) gopt; rewrite_pattern cxt pattern
  | Ugatestep (es, ug)          -> List.iter (rewrite_expr cxt) es; rewrite_expr cxt ug

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
  | Processdef  (n, params, (proc, None)) ->
      rewrite_params cxt params; rewrite_process cxt proc
  | Processdef  (n, params, (proc, Some _)) ->
      raise (Error (n.pos, "cannot rewrite_def process with monitor"))
  | Functiondefs fdefs            ->
      let rewrite_fdef (n, pats, toptr, expr) =
        let nt = (try evaltype (cxt <@>n.inst) 
                  with Not_found -> raise (Can'tHappen (Printf.sprintf "%s: %s not in cxt %s"
                                                                       (string_of_sourcepos n.pos)
                                                                       (string_of_name n.inst)
                                                                       (string_of_typecxt cxt)
                                                       )
                                          )
                 )
        in
        let doit cxt rt = rewrite_fparams cxt pats; rewrite_expr cxt expr; toptr := Some (evaltype rt) in
        doit cxt (result_type n.pos pats nt)
      in
      List.iter rewrite_fdef fdefs
  | Letdef (pat, e)                ->  
      rewrite_pattern cxt pat; rewrite_expr cxt e
     
(* ********************************************** unification stuff ******************************** *)

(* useful in error messages *)
let pickdiff t t1 t2 = 
  let t = evaltype t in
  let t1 = evaltype t1 in
  let t2 = evaltype t2 in
  if t=t1 then t2 else t1
  
let rec unifytypes t1 t2 = 
  let t1 = evaltype t1 in
  let t2 = evaltype t2 in
  if !verbose then
    (Printf.printf "unifytypes %s %s\n\n"
                  (Type.string_of_type t1)
                  (Type.string_of_type t2); flush stdout);
  let exn = TypeUnifyError (t1,t2) in
  let ut n r t =
    let kind = kind_of_unknown n in
    r:=Some t; if kind=UnkAll then () else force_kind kind t
  in
  (* because of evaltype above, Unknowns must be ref None *)
  match t1.inst, t2.inst with
  | Unknown (n1,r1)     , Unknown (n2,r2)       -> if n1<>n2 then
                                                     (if kind_includes (kind_of_unknown n1) (kind_of_unknown n2) 
                                                      then r1:=Some t2 
                                                      else r2:=Some t1
                                                     )
  | Unknown (n1,r1)     , OneOf (_,ts)          -> if List.for_all (canunifytype n1) ts then ut n1 r1 t2 else raise exn (* I think *)
  | OneOf (_,ts)        , Unknown (n2,r2)       -> if List.for_all (canunifytype n2) ts then ut n2 r2 t1 else raise exn (* I think *)
  | Unknown (n1,r1)     , _                     -> if canunifytype n1 t2 then ut n1 r1 t2 else raise exn
  | _                   , Unknown (n2,r2)       -> if canunifytype n2 t1 then ut n2 r2 t1 else raise exn
  | OneOf ((n1,r1),t1s)  , OneOf ((n2,r2),t2s)  -> if n1<>n2 then
                                                     (if List.for_all (fun t2 -> List.exists (fun t1 -> t1.inst=t2.inst) t1s) t2s
                                                       then ut n1 r1 t2 else 
                                                      if List.for_all (fun t1 -> List.exists (fun t2 -> t1.inst=t2.inst) t2s) t1s
                                                       then ut n2 r2 t1 else 
                                                      raise exn
                                                     ) 
  | OneOf ((n1,r1),t1s)  , _                    -> if List.exists (fun t1 -> t1.inst=t2.inst) t1s then ut n1 r1 t2 else raise exn
  | _                   , OneOf ((n2,r2),t2s)   -> if List.exists (fun t2 -> t1.inst=t2.inst) t2s then ut n2 r2 t1 else raise exn
  | Tuple t1s           , Tuple t2s             
  | Process t1s         , Process t2s           -> unifylists exn t1s t2s 
  | Channel t1          , Channel t2        
  | List t1             , List t2               -> (* (try *)unifytypes t1 t2(* with _ -> raise exn)*)
  | Fun (t1a,t1b)       , Fun (t2a,t2b)         -> unifylists exn [t1a;t1b] [t2a;t2b]
(*| Range (i,j)         , Range (m,n)           -> if m<=i && j<=n then () else raise exn *)
  | _                                           -> if t1.inst=t2.inst then () else raise exn

and unifypair (t1,t2) = unifytypes t1 t2

and unifylists exn t1s t2s = 
  let pairs = try List.combine t1s t2s with Invalid_argument _ -> raise exn in
  List.iter unifypair pairs

(* canunify checks that a type doesn't contain Unknown n; also that equnknowns don't get unified with qbits, functions and such;
   and now also that channel types are qbit or classical and that classicals are classical. ISWIM
 *)  
and canunifytype n t =
  let bad prefix = 
    let s = match kind_of_unknown n with
            | UnkClass -> "a classical type"
            | UnkEq    -> "an equality type"
            | UnkComm  -> "qbit or classical"
            | UnkAll   -> " (whoops: can't happen)"
    in
    raise (Error (t.pos, string_of_type t ^ " is not " ^ prefix ^ s))
  in
  let rec check kind t = 
    let rec cu t = 
      match kind, t.inst with
      | _       , Unknown (_, {contents=Some t'}) -> cu t'
      | _       , Unknown (n',_) -> n<>n' (* ignore kind: we shall force it later *)
      | _       , Known n'       -> kind_includes kind (kind_of_unknown n')
      
      (* try OneOf one at a time: they must all be ok *)
      | _       , OneOf ((_, {contents=Some t'}), _) -> cu t'
      | _       , OneOf ((n',_), ts) -> n<>n' && List.for_all cu ts
      
      (* everybody takes the basic ones *)
      | _       , Unit
      | _       , Num
      | _       , Bool
      | _       , Char
      | _       , String
      | _       , Bit 
      | _       , Basisv   
   (* | _       , Range   _ *)
      | _       , Gate          -> true
     
      (* Unkall takes anything *)
      | UnkAll  , _             -> true
      
      (* there remain Comm, Class, Eq *)
      (* Comm takes Qbit or otherwise behaves as Class *)
      | UnkComm , Qbit          -> true
      | UnkComm , _             -> check (if !Settings.resourcecheck then UnkClass else UnkAll) t
      
      (* there remain Class and Eq *)
      (* neither allows Qbit *)
      |_        , Qbit          -> bad ""
      (* Eq doesn't allow several things *)
      | UnkEq   , Qstate      
      | UnkEq   , Channel _   
      | UnkEq   , Fun     _   
      | UnkEq   , Poly    _        (* Poly types are function types *)
      | UnkEq   , Process _     -> bad ""

      (* but Class does *)
      | UnkClass, Qstate      
      | UnkClass, Fun     _        (* check the classical free-variable condition later *)
      | UnkClass, Poly    _     -> true
      
      (* otherwise some recursions *)
      | _       , Tuple ts      -> List.for_all cu ts
      | _       , Process ts    -> List.for_all (check commU) ts
      | _       , List t        -> cu t
      | _       , Channel t     -> (try check commU t with Error _ -> bad "channel of ")                    
    in
    cu t
  in
  check (kind_of_unknown n) t

(* force_kind unifies the unknowns in t with appropriate unknowns *)  
and force_kind kind t =
  let rec fk t =
    match t.inst with
    | Unknown (n,{contents=Some t'})    
                    -> fk t'
    | Unknown (n,r) -> if kind_includes kind (kind_of_unknown n) 
                       then () 
                       else (let u' = new_Unknown t.pos kind in r:=Some u')
    | OneOf ((n,{contents=Some t'}), _)  -> fk t'
    | OneOf ((n,r),ts)                   -> List.iter fk ts
    | Tuple ts      -> List.iter fk ts
    | List t        -> fk t
    | Num
    | Bool
    | Char
    | String
    | Bit 
    | Unit
    | Basisv   
    | Known   _
 (* | Range   _ *)
    | Gate           
    | Qbit            
    | Qstate          
    | Fun _           
    | Process _       
    | Channel _       
    | Poly _        -> () 
  in
  fk t
  
(* *************************** typechecker starts here ********************************* *)

let rec typecheck_pats tc cxt t pxs : unit =
   if !verbose then 
     Printf.printf "typecheck_pats ... %s (%s) %s\n\n"
                   (short_string_of_typecxt cxt)
                   (string_of_type t)
                   (bracketed_string_of_list (string_of_pair string_of_pattern (fun _ -> "") "") pxs);
   List.iter (fun (pat, x) -> assigntype_pat ((revargs tc) x) cxt t pat) pxs
   
and assigntype_pat contn cxt t p : unit =
  if !verbose then
    Printf.printf "assigntype_pat ... %s (%s) (%s)\n\n"
                  (short_string_of_typecxt cxt)
                  (string_of_type t)
                  (string_of_pattern p);
  (match !(p.inst.ptype) with
   | Some pt -> unifytypes t pt
   | None    -> p.inst.ptype := Some t
  );
  try match p.inst.pnode with
      | PatAny          -> contn cxt
      | PatName n       -> contn (cxt <@+> (n,t)) 
      | PatUnit         -> unifytypes t (adorn p.pos Unit); contn cxt
      | PatNil          -> let vt = ntv p.pos in
                           let lt = adorn p.pos (List vt) in
                           unifytypes t lt; contn cxt
      | PatInt _        -> unifytypes t (adorn p.pos Num); contn cxt
      | PatBit _        -> unifytypes t (adorn p.pos Bit); contn cxt
      | PatBool _       -> unifytypes t (adorn p.pos Bool); contn cxt
      | PatChar _       -> unifytypes t (adorn p.pos Char); contn cxt
      | PatString _     -> unifytypes t (adorn p.pos String); contn cxt
      | PatBasisv _     -> unifytypes t (adorn p.pos Basisv); contn cxt
      | PatCons (ph,pt) -> let vt = ntv ph.pos in
                           let lt = adorn p.pos (List vt) in
                           let cf cxt = 
                             assigntype_pat contn cxt t pt
                           in
                           unifytypes t lt;
                           assigntype_pat cf cxt vt ph
      | PatTuple ps     -> let ts = List.map (fun p -> ntv p.pos) ps in
                           unifytypes t (adorn p.pos (Tuple ts));
                           let rec tc cxt = function
                             | (p,t)::pts -> assigntype_pat ((revargs tc) pts) cxt t p
                             | []         -> contn cxt
                           in
                           tc cxt (zip ps ts)
  with TypeUnifyError _ -> raise (Error (p.pos,
                                         Printf.sprintf "cannot assign type %s to pattern %s"
                                                        (string_of_type (evaltype t))
                                                        (string_of_pattern p)
                                        )
                                 )

;; (* to give typecheck_pats and assigntype_pat a polytype *)

let rec assigntype_name pos cxt t n =
  match eval cxt n with
  | Some t' -> 
      let t' = Type.instantiate t' in
      (try unifytypes t t' 
       with 
       | TypeUnifyError(t1,t2) -> 
           raise (Error (pos,
                         Printf.sprintf "(unifying types %s and %s for %s): can't (sub-)unify %s and %s"
                                        (string_of_type (evaltype t))
                                        (string_of_type (evaltype t'))
                                        (string_of_name n)
                                        (string_of_type (evaltype t1))
                                        (string_of_type (evaltype t2))
                        )
                 )
       | Error (_, s) -> raise (Error (pos, s))
      )
  | None    -> raise (Undeclared (pos, n))

and assigntype_expr cxt t e =
  if !verbose then
    Printf.printf "assigntype_expr %s (%s) (%s)\n\n"
                  (short_string_of_typecxt cxt)
                  (string_of_type (evaltype t))
                  (string_of_expr e);
  e.inst.etype := Some t; (* for rewriting later *)
  let utaf cxt = uncurry2 (assigntype_expr cxt) in
  try 
    let unary cxt tout tin e = 
       unifytypes t tout;
       try assigntype_expr cxt tin e 
       with TypeUnifyError (t1,t2) -> 
         raise (Error(e.pos,
                      Printf.sprintf "%s should be %s but is actually %s"
                                     (string_of_expr e)
                                     (string_of_type (evaltype tin))
                                     (string_of_type (pickdiff tin t1 t2))
                     )
                )
     in
     let binary cxt tout tin1 tin2 f1 f2 =
       unary cxt tout tin1 f1;
       unary cxt tout tin2 f2
     in
     let ternary cxt tout tin1 tin2 tin3 f1 f2 f3 =
       binary cxt tout tin1 tin2 f1 f2;
       unary cxt tout tin3 f3
     in
     match e.inst.enode with
     | EUnit                -> unifytypes t (adorn_x e Unit)
     | ENil                 -> unifytypes t (adorn_x e (List (ntv e.pos)))
     | ENum i               -> (* no longer is Bit a subtype of Num
                                (match (evaltype t).inst with 
                                 | Bit              -> if i=/zero||i=/one then ()
                                                       else unifytypes t (adorn_x e Num)
                                 (* | Range (j,k) as t -> if j<=i && i<=k then () 
                                                       else unifytypes (adorn_x e t) (adorn_x e Num) *)
                                 | t                -> unifytypes (adorn_x e t) (adorn_x e Num)
                                )
                                *)
                               unifytypes t (adorn_x e Num) 
     | EBool _              -> unifytypes t (adorn_x e Bool)
     | EChar _              -> unifytypes t (adorn_x e Char)
     | EString _            -> unifytypes t (adorn_x e String)
     | EBit b               -> (* no longer is Bit a subtype of Num
                                (match (evaltype t).inst with 
                                 | Num              -> ()
                                 (* | Range (j,k) as t -> let i = if b then 1 else 0 in
                                                       if j<=i && i<=k then cxt 
                                                       else unifytypes (adorn_x e t) (adorn_x e Bit) *)
                                 | t                -> unifytypes (adorn_x e t) (adorn_x e Bit)
                                )
                                *)
                               unifytypes t (adorn_x e Bit) 
     | EBasisv _            -> unifytypes t (adorn_x e Basisv)
     | EVar    n            -> assigntype_name e.pos cxt t n
     | EApp    (e1,e2)      -> let atype = ntv e2.pos in (* arguments can be non-classical: loophole for libraries *)
                               let rtype = newclasstv e.pos in (* result always classical *)
                               let ftype = adorn_x e1 (Fun (atype, rtype)) in
                               let _ = unifytypes rtype t in
                               let _ = assigntype_expr cxt ftype e1 in 
                               assigntype_expr cxt atype e2
     | EMinus  e            -> unary cxt (adorn_x e Num) (adorn_x e Num) e
     | ENot    e            -> unary cxt (adorn_x e Bool) (adorn_x e Bool) e
     | ETuple  es           -> let ts = List.map (fun e -> ntv e.pos) es in
                               let tes = List.combine ts es in
                               let _ = List.iter (utaf cxt) tes in
                               unifytypes t (adorn_x e (Tuple ts))
     | ECons   (hd,tl)      -> let t' = ntv e.pos in
                               let _ = assigntype_expr cxt t' hd in
                               let t'' = (adorn_x e (List t')) in
                               let _ = assigntype_expr cxt t'' tl in
                               unifytypes t t''
     | EMatch (e,ems)       -> let et = ntv e.pos in
                               let _ = assigntype_expr cxt et e in
                               let tc cxt e = assigntype_expr cxt t e in
                               let _ = typecheck_pats tc cxt et ems in
                               ()
     | ECond  (c,e1,e2)     -> ternary cxt t (adorn_x c Bool) t t c e1 e2
     | EArith (e1,op,e2)    -> let tnode = 
                                 match op with
                                 | Times   -> OneOf(new_unknown UnkEq, [adorn_x e Num; adorn_x e Gate]) 
                                 | TensorP -> Gate
                                 | _       -> Num 
                               in
                               binary cxt (adorn_x e tnode) (adorn_x e1 tnode) (adorn_x e2 tnode) e1 e2
     | ECompare (e1,op,e2)  -> (match op with 
                                   | Eq | Neq ->
                                       let t = new_Unknown e1.pos UnkEq in
                                       binary cxt (adorn_x e Bool) t t e1 e2
                                   | _ ->
                                       binary cxt (adorn_x e Bool) (adorn_x e1 Num) (adorn_x e2 Num) e1 e2
                                  )
     | EBoolArith (e1,_,e2) -> binary cxt (adorn_x e Bool) (adorn_x e1 Bool) (adorn_x e2 Bool) e1 e2
     | EAppend (e1,e2)      -> let t' = adorn_x e (List (newclasstv e.pos)) in (* append has to deal in classical lists *)
                               let _ = assigntype_expr cxt t' e1 in
                               let _ = assigntype_expr cxt t' e2 in
                               unifytypes t t'
     | ELambda (pats, e)    -> check_distinct_fparams pats; assigntype_fun cxt t pats e
     | EWhere  (e, ed)      -> assigntype_edecl cxt t e ed
  with 
  | TypeUnifyError (t1,t2)  -> raise (Error (e.pos,
                                             Printf.sprintf "%s appears to be type %s, but in context should be %s"
                                                            (string_of_expr e) 
                                                            (string_of_type (evaltype t2))
                                                            (string_of_type (evaltype t1))
                                            )
                                     )
  
and assigntype_edecl cxt t e ed = 
  match ed.inst with
  | EDPat (wpat,wtopt,we)        -> let wt = ntv we.pos in
                                    let _ = assigntype_expr cxt wt we in
                                    assigntype_pat (fun cxt -> assigntype_expr cxt t e) cxt wt wpat
  | EDFun (wfn,wfpats,wtoptr,we) -> ok_funname wfn;
                                    check_distinct_fparams wfpats;
                                    let tf, tr = read_funtype wfpats wtoptr we in
                                    let cxt = cxt <@+> (wfn.inst,tf) in
                                    let _ = assigntype_fun cxt tf wfpats we in
                                    let rt = newclasstv we.pos in
                                    let _ = unifytypes rt tr in
                                    let cxt = (cxt <@-> wfn.inst) <@+> (wfn.inst, generalise tf) in
                                    assigntype_expr cxt t e

and read_funtype pats toptr e = 
  (* with mutually-recursive function definitions, read_funtype gets called more than once.
     So the first on the scene gets to fill in the unknowns.
     (Well actually it's only called once per definition, at present, but it does no harm.)
   *)
  let rec itf = function
  | pat::pats'  -> let ta = inventtype_pat pat in
                   let tr, trall = itf pats' in
                   adorn (pos_of_instances pats) (Fun (ta,tr)), trall
  | []          -> let tr = match !toptr with 
                            | None   -> let t = newclasstv e.pos in toptr := Some t; t (* result must be classical *)
                            | Some t -> t
                   in tr, tr
  and inventtype_pat pat =
    let f = match pat.inst.pnode with
            | PatName _ 
            | PatAny          -> (fun () -> ntv pat.pos)            (* note this is UnkAll -- any type of argument. Hmmm. *)
            | PatUnit         -> (fun () -> adorn pat.pos Unit)
            | PatTuple pats   -> let itp ts pat = inventtype_pat pat :: ts in
                                 let ts = List.fold_left itp [] pats in
                                 (fun () -> adorn pat.pos (Tuple (List.rev ts)))
            | _               -> raise (Can'tHappen (Printf.sprintf "inventtype_pat %s" (string_of_pattern pat)))
    in
    match !(pat.inst.ptype) with
    | Some t -> t   (* not all that work for nothing: the PatNames have been typed *)
    | None   -> let t = f () in pat.inst.ptype := Some t; t
  in 
  itf pats
  
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
                  (string_of_type (evaltype t))
                  (string_of_list string_of_fparam " " pats)
                  (string_of_expr e);
  match pats with
  | pat::pats'  -> let ta = newclasstv pat.pos in (* function arguments must be classical *)
                   let tr = newclasstv (pos_of_instances pats') in
                   let tf = adorn (pos_of_instances pats) (Fun (ta,tr)) in
                   let _ = unifytypes t tf in
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

(* let strip_procparams s cxt params = 
     if !verbose then
       Printf.printf "before strip_procparams %s (%s)\n%s\n\n" s (string_of_params params) (short_string_of_typecxt cxt);
     let cxt = List.fold_left (fun cxt p -> cxt<@-->(strip_param p)) cxt (List.rev params) in
     if !verbose then
       Printf.printf "after strip_procparams %s\n\n" (short_string_of_typecxt cxt); 
     cxt
 *)
 
let rec do_procparams s cxt params proc =
  if !verbose then
    Printf.printf "do_procparams %s" (string_of_list string_of_param "," params);
  let process_param {pos=pos; inst=n,rt} = n, fix_paramtype pos rt in
  let cxt = List.fold_left (fun cxt param -> cxt <@+> process_param param) cxt params in
  if !verbose then
    Printf.printf " -> %s\n" (string_of_list string_of_param "," params);
  typecheck_process cxt proc

and fix_paramtype pos rt =
  match !rt with
  | Some t -> t
  | None   -> let t = newcommtv pos in rt := Some t; t (* process params are, like messages, qbits or classical *)
  
and unify_paramtype rt t =
  match !rt with
  | Some t' -> unifytypes t t'
  | None    -> rt := Some t
  
and typecheck_process cxt p =
  if !verbose then
    Printf.printf "typecheck_process ... %s\n" (short_string_of_process p);
  match p.inst with
  | Terminate     -> ()
  | Call (n,args) -> 
      ok_procname n;
      let ts = 
        (try let t = evaltype (cxt<@>n.inst) in
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
      List.iter (fun (e,t) -> assigntype_expr cxt t e) ets
  | WithNew (params, proc) ->
      (* all the params have to be channels *)
      let _ = 
        List.iter (fun {pos=pos; inst=n,rt} -> 
                     unify_paramtype rt (adorn pos (Channel (newcommtv pos))) 
                  )
                  params
      in
      check_distinct params;
      do_procparams "WithNew" cxt params proc
  | WithQbit (qss,proc) ->
      let typecheck_qspec cxt ({pos=pos; inst=n,rt}, bvopt) =
        let _ = unify_paramtype rt (adorn pos Qbit) in
        match bvopt with
        | Some bve -> assigntype_expr cxt (adorn bve.pos Basisv) bve
        | None     -> ()
      in
      let _ = List.iter (typecheck_qspec cxt) qss in
      let params = List.map fst qss in
      check_distinct params;
      do_procparams "WithQbit" cxt params proc
  | WithLet ((pat,e),proc) ->
      typecheck_letspec (fun cxt -> typecheck_process cxt proc) cxt pat e
  | WithQstep (qstep,proc) ->
      (match qstep.inst with
       | Measure (e, gopt, pat) ->
           let _ = assigntype_expr cxt (adorn e.pos Qbit) e in
           let _ = ((fun ge -> assigntype_expr cxt (adorn ge.pos Gate) ge) ||~~ ()) gopt in
           assigntype_pat (fun cxt -> typecheck_process cxt proc) cxt (adorn pat.pos Bit) pat
       | Ugatestep (es, uge) ->
           let _ = List.iter (fun e -> assigntype_expr cxt (adorn e.pos Qbit) e) es in
           let _ = assigntype_expr cxt (adorn uge.pos Gate) uge in
           typecheck_process cxt proc
      )
  | GSum gs ->
      let check_g (iostep,proc) =
        match iostep.inst with
         | Read (ce, pat) ->
             let t = newcommtv ce.pos in
             let _ = assigntype_expr cxt (adorn ce.pos (Channel t)) ce in
             assigntype_pat (fun cxt -> typecheck_process cxt proc) cxt t pat
         | Write (ce, e) ->
             let t = newcommtv ce.pos in 
             let _ = assigntype_expr cxt (adorn ce.pos (Channel t)) ce in
             let _ = assigntype_expr cxt t e in
             typecheck_process cxt proc
      in
      List.iter check_g gs
  | Cond (e,p1,p2) ->
      let _ = assigntype_expr cxt (adorn e.pos Bool) e in
      let _ = typecheck_process cxt p1 in
      typecheck_process cxt p2
  | PMatch (e,pms)  -> let et = newclasstv e.pos in
                       let _ = assigntype_expr cxt et e in
                       typecheck_pats typecheck_process cxt et pms
  | Par (ps)        -> List.iter (typecheck_process cxt) ps

and typecheck_pdef cxt def =
  match def with 
  | Processdef (pn,params,(proc, None)) -> 
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
      let _ = do_procparams "processdef" cxt params proc in
      let cxt = evalcxt cxt in
      let tps = zip env_types params in
      let _ = List.iter (fun (t,{inst=n,rt}) -> unifytypes t (_The !rt)) tps in
      if !verbose then
        (rewrite_def cxt def;
         Printf.printf "after typecheck_def, def = %s\n\ncxt = %s\n\n" 
                       (string_of_def def) 
                       (short_string_of_typecxt cxt)
        )
  | Processdef (pn,params,(proc, Some _)) -> 
      raise (Error (pn.pos, "cannot typecheck process with monitor"))  
  | Functiondefs _ 
  | Letdef       _ -> ()
      
and typecheck_letspec contn cxt pat e =
  let t = newclasstv e.pos in
  let _ = assigntype_expr cxt t e in
  let t = generalise t in
  assigntype_pat contn cxt t pat

let make_library_cxt () =
  let knownassoc = List.map (fun (n,t,_) -> n, generalise (Parseutils.parse_typestring t)) !Interpret.knowns in
  let cxt = new_cxt knownassoc in
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
        let t, rt = read_funtype pats toptr e in
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
        let rtv = newclasstv rt.pos in
        let _ = unifytypes rtv rt in
        assigntype_fun cxt (Type.instantiate env_type) pats expr;
        evalcxt cxt
      in
      let cxt = List.fold_left tc_fdef cxt fdefs in
      let postcxt cxt fn =  
        let t = evaltype (cxt<@>fn.inst) in
        (cxt <@-> fn.inst) <@+> (fn.inst, generalise t)
      in
      List.fold_left postcxt cxt fns
  | Letdef (pat, e) ->
      (* sneaky use of reference to allow typecheck_letspec to return unit *)
      let cref = ref cxt in
      let contn cxt = cref := cxt in
      typecheck_letspec contn cxt pat e;
      !cref
      
let precheck_pdef cxt = function
  | Processdef   (pn,ps,_) -> 
      ok_procname pn;
      let process_param param = 
        let n,rt = param.inst in
        let unknown = new_unknown commU in
        match !rt with
        | None   -> adorn param.pos (Unknown unknown)
        | Some t -> if (match t.inst with Poly _ -> true | _ -> false) ||
                       not (NameSet.is_empty (Type.freetvs t)) 
                    then raise (Error (t.pos, "process parameter cannot be given a polytype or an unknown type"))
                    else
                    if not (canunifytype (fst unknown) t) 
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
  | Functiondefs _         
  | Letdef       _         -> cxt

let typecheck defs =
  try push_verbose !verbose_typecheck (fun () ->
        let cxt = make_library_cxt () in
        (* put the process names in cxt *)
        let cxt = List.fold_left precheck_pdef cxt defs in
        (* do the function defs in order and in groups *)
        let cxt = List.fold_left typecheck_fdefs cxt defs in
        (* do the process defs *)
        let _ = List.iter (typecheck_pdef cxt) defs in
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
