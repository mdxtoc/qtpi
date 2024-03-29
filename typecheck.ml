(*
    Copyright (C) 2018-2020 Richard Bornat
     
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
      
(* now, in 03/2022, I decree that tuples and lists can't hold qubits. RB *)

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
open Monenv

exception TypeUnifyError of _type * _type
exception Error of sourcepos * string
exception Undeclared of sourcepos * name
exception Disaster of string

(* Back to assoc lists. Maps seem to be overkill, now that unknowns are not in the context *)

type typecxt = _type monenv

let string_of_typeassoc = string_of_monassoc "->" string_of_type

let string_of_typecxt = string_of_monenv "->" string_of_type

let new_Unknown pos uk = adorn pos (Unknown (new_unknown uk))
let ntv pos = new_Unknown pos UnkAll
let newclasstv ischan pos = new_Unknown pos (if !Settings.resourcecheck then UnkClass ischan else UnkAll)
let commU = if !Settings.resourcecheck then UnkComm else UnkAll
let classU = if !Settings.resourcecheck then UnkClass false else UnkAll (* a functional restriction for Tuple and List *)
let newcommtv pos = new_Unknown pos commU
let neweqtv pos = new_Unknown pos UnkEq

let rec eval cxt n =
  try Some (evaltype (cxt<@>n)) with Not_found -> None

and evaltype t = 
  let adorn = Instance.adorn t.pos in
  let evu = function
    | (_, {contents=Some t}) -> evaltype t
    | _                      -> t
  in
  match t.inst with
  | Unit
  | Num
  | Bool
  | Char
  | Sxnum 
  | Bit 
  | Bra
  | Ket
  | Gate
  | Matrix
  | Qubit                    
  | Qubits                    
  | Qstate          -> t
  | Unknown u       -> evu u 
  | Known n         -> t
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
let evalassoc = List.map (fun (n,t) -> n, evaltype t)

let evalcxt (local, usemon, mon, global) = 
  evalassoc local, usemon, evalassoc mon, evalassoc global

let short_string_of_typecxt = string_of_typecxt

(* ***************************** rewriting stuff ********************************* *)

let rec rewrite_expr e =
  match !(toptr e) with
  | Some t -> 
      (toptr e := Some (evaltype t);
       match tinst e with
       | EUnit
       | ENil
       | ERes        _
       | EVar        _
       | ENum        _
       | EBool       _
       | EChar       _
       | EString     _
       | EBit        _ 
       | EPi    
       | EBra        _          
       | EKet        _          -> ()
       | EMinus      e          
       | ENot        e          
       | EDagger     e          -> rewrite_expr e
       | ETuple      es         -> List.iter rewrite_expr es
       | ECond       (e1,e2,e3) -> List.iter rewrite_expr [e1;e2;e3]
       | EMatch      (e,ems)    -> rewrite_expr e; 
                                   List.iter (fun (pat,e) -> rewrite_pattern pat; rewrite_expr e) ems
       | ECons       (e1,e2)
       | EJux        (e1,e2)     
       | EAppend     (e1,e2)    
       | ESub        (e1,e2)    -> List.iter rewrite_expr [e1;e2]
       | EArith      (e1,_,e2)   
       | ECompare    (e1,_,e2)   
       | EBoolArith  (e1,_,e2)  -> List.iter rewrite_expr [e1;e2]
       | ELambda     (pats, e)  -> List.iter rewrite_pattern pats; rewrite_expr e
       | EWhere      (e,ed)     -> rewrite_expr e; rewrite_edecl ed
      )
  | None   -> raise (Error (e.pos,
                            Printf.sprintf "** Disaster: typecheck didn't mark %s"
                                           (string_of_expr e)
                           )
                    )

and rewrite_edecl edecl = 
  match edecl.inst with
  | EDPat (wpat,_,we)        -> rewrite_pattern wpat; rewrite_expr we
  | EDFun (wfn,wfpats,_, we) -> rewrite_typedname wfn; rewrite_fparams wfpats; rewrite_expr we

and rewrite_fparams fps = List.iter rewrite_pattern fps

and rewrite_pattern p =
  match !(toptr p) with
  | Some t -> 
      (toptr p := Some (evaltype t);
       match tinst p with
       | PatAny
       | PatName    _
       | PatUnit
       | PatNil
       | PatBit     _
       | PatInt     _
       | PatBool    _
       | PatChar    _
       | PatString  _
       | PatBra     _
       | PatKet     _       -> ()
       | PatCons    (ph,pt) -> List.iter rewrite_pattern [ph;pt]
       | PatTuple   ps      -> List.iter rewrite_pattern ps
       
      )
  | None   -> raise (Error (p.pos,
                            Printf.sprintf "** Disaster: typecheck didn't mark %s"
                                           (string_of_pattern p)
                           )
                    )

and rewrite_param par = rewrite_typedname par

and rewrite_params params = rewrite_typednames params

and rewrite_typedname n =
  match !(toptr n) with
  | Some t -> toptr n := Some (evaltype t)
  | None   -> raise (Error (n.pos, Printf.sprintf "typechecker didn't assign type to %s" (string_of_name (tinst n))))
  
and rewrite_typednames ns = List.iter (rewrite_typedname) ns

let rewrite_qstep qstep = 
  match qstep.inst with
  | Measure (_,e,gopt,pattern)  -> rewrite_expr e; (rewrite_expr ||~~ ()) gopt; rewrite_pattern pattern
  | Through (_,es,ge,_)         -> List.iter rewrite_expr es; rewrite_expr ge

let rewrite_iostep iostep = 
  match iostep.inst with
  | Read      (ce,pat)    -> rewrite_expr ce; rewrite_pattern pat
  | Write     (ce,e)      -> rewrite_expr ce; rewrite_expr e 

let rec rewrite_process mon proc = 
  if !verbose || !verbose_typecheck then
    Printf.printf "rewrite_process ... %s:%s\n" (string_of_sourcepos proc.pos) (short_string_of_process proc);
  match proc.inst with
  | Terminate               -> ()
  | GoOnAs    (n,es)        -> rewrite_typedname n; List.iter rewrite_expr es
  | WithNew   ((_,params), p)   
                            -> rewrite_params params; rewrite_process mon p
  | WithQubit  (_,qss, p)    -> List.iter rewrite_qspec qss; rewrite_process mon p
  | WithLet   ((pat,e), p)  -> rewrite_pattern pat; rewrite_expr e; rewrite_process mon p
  | WithProc  (pdecl, p)    -> rewrite_pdecl mon pdecl; rewrite_process mon p
  | WithQstep (qstep, p)    -> rewrite_qstep qstep; rewrite_process mon p
  | TestPoint (n, p)        -> let _, mp = _The (find_monel n.inst mon) in
                               rewrite_process mon mp; (* does it need mon? Let Compile judge *)
                               rewrite_process mon p
  | JoinQs    (qs, q, p)    -> rewrite_typednames qs; rewrite_param q; rewrite_process mon p
  | SplitQs   (q, qs, p)    -> rewrite_typedname q; List.iter rewrite_splitspec qs; rewrite_process mon p
  | Iter      (pat, e, proc, p)
                            -> rewrite_pattern pat; rewrite_process mon proc;
                               rewrite_expr e; rewrite_process mon p
  | Cond     (e, p1, p2)    -> rewrite_expr e; rewrite_process mon p1; rewrite_process mon p2
  | PMatch    (e,pms)       -> rewrite_expr e; 
                               List.iter (fun (pat,proc) -> rewrite_pattern pat; rewrite_process mon proc) pms
  | GSum     gs             -> let rewrite_g (iostep, p) =
                                 rewrite_iostep iostep; rewrite_process mon p
                               in
                               List.iter (rewrite_g) gs
  | Par      ps             -> List.iter (rewrite_process mon) ps

and rewrite_qspec (qp,eopt) =
  rewrite_param qp;
  match eopt with
  | Some e -> rewrite_expr e
  | None   -> ()
  
and rewrite_splitspec spec = rewrite_qspec spec

and rewrite_pdecl mon (_, pn, params, proc) =
  rewrite_typedname pn; rewrite_params params; rewrite_process mon proc

let rewrite_pdef (pn, params, proc, mon) = 
  rewrite_typedname pn;
  rewrite_params params; rewrite_process mon proc
  (* and we don't rewrite unused monprocs *)

let rewrite_def def = 
  match def with
  | Processdefs pdefs  -> List.iter (rewrite_pdef) pdefs
  | Functiondefs fdefs ->
      let rewrite_fdef (fn, pats, toptr, expr) =
        rewrite_typedname fn;
        let nt = type_of_typedname fn in
        rewrite_fparams pats; rewrite_expr expr; toptr := Some (evaltype (result_type fn.pos pats nt))
      in
      List.iter rewrite_fdef fdefs
  | Letdef (pat, e)                ->  
      rewrite_pattern pat; rewrite_expr e
     
(* ********************************************** unification stuff ******************************** *)

let explain_ukind = function
  | UnkClass true  -> "the classical type of a value received in a guarded alt"
  | UnkClass false -> "a classical type"
  | UnkEq          -> "an equality type"
  | UnkComm        -> "channel of (qubit or qubits or classical)"
  | UnkAll         -> "any type"

let explain_uname (n,k as u) =
  Printf.sprintf "?%s is %s" (string_of_uname u) (explain_ukind k) 
  
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
    let kind = kind_of_uname n in
    r:=Some t; if kind=UnkAll then () else force_kind kind t
  in
  (* because of evaltype above, Unknowns must be ref None *)
  match t1.inst, t2.inst with
  | Unknown (n1,r1)     , Unknown (n2,r2)       -> if n1<>n2 then
                                                     (if kind_includes (kind_of_uname n1) (kind_of_uname n2) 
                                                      then r1:=Some t2 
                                                      else r2:=Some t1
                                                     )
  | Unknown (n1,r1)     , _                     -> if canunifytype n1 t2 then ut n1 r1 t2 else raise exn
  | _                   , Unknown (n2,r2)       -> if canunifytype n2 t1 then ut n2 r2 t1 else raise exn
  | Tuple t1s           , Tuple t2s             
  | Process t1s         , Process t2s           -> unifylists exn t1s t2s 
  | Channel t1          , Channel t2        
  | List t1             , List t2               -> (* (try *)
                                                   unifytypes t1 t2 (* look carefully: no try, no with *)
                                                   (* with _ -> raise exn)*)
  | Fun (t1a,t1b)       , Fun (t2a,t2b)         -> unifylists exn [t1a;t1b] [t2a;t2b]
(*| Range (i,j)         , Range (m,n)           -> if m<=i && j<=n then () else raise exn *)
  | _                                           -> if t1.inst=t2.inst then () else raise exn

and unifypair (t1,t2) = unifytypes t1 t2

and unifylists exn t1s t2s = 
  let pairs = try List.combine t1s t2s with Invalid_argument _ -> raise exn in
  List.iter unifypair pairs

(* canunify checks that a type doesn't contain Unknown n; also that equnknowns don't get unified with qubits, functions and such;
   and now also that channel types are qubit or classical and that classicals are classical. ISWIM
 *)  
and canunifytype n t =
  let bad () = 
    let s = match kind_of_uname n with
            | UnkClass _ -> "a classical type"
            | UnkEq      -> "an equality type"
            | UnkComm    -> "channel of (qubit or qubits or classical)"
            | UnkAll     -> " (whoops: can't happen)"
    in
    raise (Error (t.pos, match kind_of_uname n with
                         | UnkClass true -> "channel in alt cannot carry non-classical values"
                         | _             -> string_of_type t ^ " is not " ^ s))
  in
  let rec check kind t = 
    let rec cu t = 
      match kind, t.inst with
      | _       , Unknown (_, {contents=Some t'}) -> cu t'
      | _       , Unknown (n',_) -> n<>n' (* ignore kind: we shall force it later *)
      | _       , Known n'       -> kind_includes kind (kind_of_uname n')
      
      (* everybody takes the basic ones *)
      | _       , Unit
      | _       , Num
      | _       , Bool
      | _       , Char
      | _       , Sxnum
      | _       , Bit 
      | _       , Bra
      | _       , Ket
   (* | _       , Range   _ *)
      | _       , Gate          
      | _       , Matrix        -> true
     
      (* Unkall takes anything *)
      | UnkAll  , _             -> true
      
      (* there remain Comm, Class, Eq *)
      (* Comm takes Qubit or Qubits or otherwise behaves as Class *)
      | UnkComm , Qubit          -> true
      | UnkComm , Qubits         -> true
      | UnkComm , _             -> check (if !Settings.resourcecheck then UnkClass false else UnkAll) t  (* false because not an alt-read ... *)
      
      (* there remain Class and Eq *)
      (* neither allows Qubit or Qubits *)
      |_        , Qubit          -> bad ()
      |_        , Qubits         -> bad ()
      (* Eq doesn't allow several things *)
      | UnkEq   , Qstate      
      | UnkEq   , Channel _   
      | UnkEq   , Fun     _   
      | UnkEq   , Poly    _        (* Poly types are function types *)
      | UnkEq   , Process _     -> bad ()

      (* but Class does *)
      | UnkClass _, Qstate      
      | UnkClass _, Fun     _        (* check the classical free-variable condition later *)
      | UnkClass _, Poly    _     -> true
      
      (* otherwise some recursions *)
      | _       , Tuple ts      -> List.for_all (check classU) ts
      | _       , Process ts    -> List.for_all (check commU) ts
      | _       , List t        -> check classU t
      | _       , Channel t     -> (try check commU t 
                                    with Error (pos, _) as error -> 
                                           (* if it's complaining about t and t is not itself a channel, complain.
                                              Otherwise pass on the error
                                            *)
                                           if pos=t.pos && (match t.inst with Channel _ -> false | _ -> true)
                                           then bad () else raise error
                                   )                 
    in
    cu t
  in
  check (kind_of_uname n) t

(* force_kind unifies the unknowns in t with appropriate unknowns *)  
and force_kind kind t =
  let rec fk t =
    match t.inst with
    | Unknown (n,{contents=Some t'})    
                    -> fk t'
    | Unknown (n,r) -> if kind_includes kind (kind_of_uname n) 
                       then () 
                       else (let u' = new_Unknown t.pos kind in r:=Some u')
    | Tuple ts      -> List.iter fk ts
    | List t        -> fk t
    | Num
    | Bool
    | Char
    | Sxnum
    | Bit 
    | Unit
    | Bra
    | Ket
    | Known   _
 (* | Range   _ *)
    | Gate   
    | Matrix
    | Qubit            
    | Qubits           
    | Qstate          
    | Fun _           
    | Process _       
    | Channel _       
    | Poly _        -> () 
  in
  fk t

(* *************************** typechecker starts here ********************************* *)

let force_type pos t t' = (* force t to be t' -- t' determined by stuff at position pos *)
  try unifytypes t t' with _ ->
     let t = evaltype t in
     let t' = evaltype t' in
     let tvs = UnameSet.elements (freetvs t) @ UnameSet.elements (freetvs t') in
     let explain_tvs () = 
       Printf.sprintf " (where %s)" (Stringutils.phrase (List.map explain_uname tvs))
     in
     raise (Error (pos, Printf.sprintf "should be type %s; type %s doesn't fit%s"
                                       (string_of_type (evaltype t'))
                                       (string_of_type (evaltype t))
                                       (if tvs=[] then "" else explain_tvs ())
                  )
           )

let make_toptr x t =
  match !(toptr x) with
     | Some pt -> force_type x.pos pt t
     | None    -> toptr x := Some t
;;

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
  make_toptr p t;
  try match tinst p with
      | PatAny          -> contn cxt
      | PatName n       -> contn (cxt <@+> (n,t)) 
      | PatUnit         -> force_type p.pos t (adorn p.pos Unit); contn cxt
      | PatNil          -> let vt = newclasstv false p.pos in
                           let lt = adorn p.pos (List vt) in
                           force_type p.pos t lt; contn cxt
      | PatInt _        -> force_type p.pos t (adorn p.pos Num); contn cxt
      | PatBit _        -> force_type p.pos t (adorn p.pos Bit); contn cxt
      | PatBool _       -> force_type p.pos t (adorn p.pos Bool); contn cxt
      | PatChar _       -> force_type p.pos t (adorn p.pos Char); contn cxt
      | PatString _     -> force_type p.pos t (adorn p.pos (List (adorn p.pos Char))); contn cxt
      | PatBra _        -> force_type p.pos t (adorn p.pos Bra); contn cxt
      | PatKet _        -> force_type p.pos t (adorn p.pos Ket); contn cxt
      | PatCons (ph,pt) -> let vt = newclasstv false ph.pos in
                           let lt = adorn p.pos (List vt) in
                           let cf cxt = 
                             assigntype_pat contn cxt t pt
                           in
                           force_type p.pos t lt;
                           assigntype_pat cf cxt vt ph
      | PatTuple ps     -> let ts = List.map (fun p -> ntv p.pos) ps in
                           force_type p.pos t (adorn p.pos (Tuple ts));
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
      (try force_type pos t' t 
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
  make_toptr e t;
  let utaf cxt = uncurry2 (assigntype_expr cxt) in
  try 
    let unary cxt tout tin e = 
       force_type e.pos t tout;
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
     let ovld_warn opstring ee t =
       warning e.pos (Printf.sprintf "overloaded %s: in the absence of type information, \
                                       %s is assumed to be type %s"
                                          opstring
                                          (string_of_expr ee)
                                          (string_of_type t)
                    )

     in
     let ovld_warn2 opstring e1 e2 t =
       warning e.pos (Printf.sprintf "overloaded %s: in the absence of type information, \
                                        %s and %s are assumed to be type %s"
                                           opstring
                                           (string_of_expr e1)
                                           (string_of_expr e2)
                                           (string_of_type t)
                     )
     in
     match tinst e with
     | EUnit                -> force_type e.pos t (adorn_x e Unit)
     | ENil                 -> force_type e.pos t (adorn_x e (List (newclasstv false e.pos)))
     | ERes w               -> (let ft = 
                                  match w with
                                  | ResShow false -> adorn_x e (Fun (ntv e.pos, adorn_x e (List (adorn_x e Char))))
                                  | ResShow true  -> adorn_x e (Fun (ntv e.pos, adorn_x e Qstate))
                                  | ResCompare    -> let ct = neweqtv e.pos in
                                                     adorn_x e (Fun (ct,
                                                                     adorn_x e (Fun (ct, adorn_x e Num))
                                                                    )
                                                               )
                                in
                                force_type e.pos t ft
                               )
     | ENum i               -> (* no longer is Bit a subtype of Num
                                (match (evaltype t).inst with 
                                 | Bit              -> if i=/zero||i=/one then ()
                                                       else force_type e.pos t (adorn_x e Num)
                                 (* | Range (j,k) as t -> if j<=i && i<=k then () 
                                                       else force_type e.pos (adorn_x e t) (adorn_x e Num) *)
                                 | t                -> force_type e.pos (adorn_x e t) (adorn_x e Num)
                                )
                                *)
                               force_type e.pos t (adorn_x e Num) 
     | EBool _              -> force_type e.pos t (adorn_x e Bool)
     | EChar _              -> force_type e.pos t (adorn_x e Char)
     | EString _            -> force_type e.pos t (adorn_x e (List (adorn_x e Char)))
     | EBit b               -> (* no longer is Bit a subtype of Num
                                (match (evaltype t).inst with 
                                 | Num              -> ()
                                 (* | Range (j,k) as t -> let i = if b then 1 else 0 in
                                                       if j<=i && i<=k then cxt 
                                                       else force_type e.pos (adorn_x e t) (adorn_x e Bit) *)
                                 | t                -> force_type e.pos (adorn_x e t) (adorn_x e Bit)
                                )
                                *)
                               force_type e.pos t (adorn_x e Bit) 
     | EPi                  -> force_type e.pos t (adorn_x e Num)
     | EBra    _            -> force_type e.pos t (adorn_x e Bra)
     | EKet    _            -> force_type e.pos t (adorn_x e Ket)
     | EVar    n            -> assigntype_name e.pos cxt t n
     | EJux    (e1,e2)      -> let atype = ntv e2.pos in (* arguments can be non-classical: loophole for libraries *)
                               let rtype = newclasstv false e.pos in (* result always classical *)
                               let ftype = adorn_x e1 (Fun (atype, rtype)) in
                               let _ = force_type e.pos rtype t in
                               let _ = assigntype_expr cxt ftype e1 in 
                               assigntype_expr cxt atype e2
     | EMinus  e            -> (* even this is overloaded now, because of sxnum and angle -- and matrix, why not? *)
                               (let te = neweqtv e.pos in (* uniform overloading *)
                                unary cxt te te e;
                                let te = evaltype te in
                                let bad () = raise (Error (e.pos, Printf.sprintf "overloaded %s can be num->num, sxnum->sxnum, angle-> angle or matrix->matrix -- \
                                                                                  here we have %s->%s"
                                                                                        ("unary " ^ Expr.string_of_uminus)
                                                                                        (string_of_type te)
                                                                                        (string_of_type te)
                                                          )
                                                   )
                                in    
                                match te.inst with
                                | Num      
                                | Sxnum     
                                | Matrix    -> ()
                                | Unknown _ -> let t = adorn e.pos Num in
                                               ovld_warn ("unary " ^ Expr.string_of_uminus) e t;
                                               force_type e.pos te t
                                | _         -> bad()
                               )
     | ENot    e            -> unary cxt (adorn_x e Bool) (adorn_x e Bool) e
     | EDagger e            -> (* a little overloaded *)
                               (let te, tout = neweqtv e.pos, neweqtv e.pos in
                                unary cxt te tout e;
                                let te, tout = evaltype te, evaltype tout in
                                let bad () = raise (Error (e.pos, Printf.sprintf "overloaded † can be gate->gate or matrix->matrix: \
                                                                                  here we have %s->%s"
                                                                                        (string_of_type te)
                                                                                        (string_of_type tout)
                                                                            )
                                                                     )
                                in    
                                match te.inst, tout.inst with
                                | Gate     , _
                                | _        , Gate
                                | Matrix   , _
                                | _        , Matrix     -> (try force_type e.pos te tout with _ -> bad ())
                                | Unknown _, Unknown _  -> 
                                      raise (Error (e.pos, Printf.sprintf "overloaded † can be gate->gate or matrix->matrix: \
                                                                           cannot deduce type (use some type constraints)"
                                                   )
                                            )
                                | _                     -> bad()
                               )
     | ETuple  es           -> let ts = List.map (fun e -> ntv e.pos) es in
                               let tes = List.combine ts es in
                               let _ = List.iter (utaf cxt) tes in
                               force_type e.pos t (adorn_x e (Tuple ts))
     | ECons   (hd,tl)      -> let t' = newclasstv false e.pos in
                               let _ = assigntype_expr cxt t' hd in
                               let t'' = (adorn_x e (List t')) in
                               let _ = assigntype_expr cxt t'' tl in
                               force_type e.pos t t''
     | EMatch (e,ems)       -> let et = ntv e.pos in
                               let _ = assigntype_expr cxt et e in
                               let tc cxt e = assigntype_expr cxt t e in
                               let _ = typecheck_pats tc cxt et ems in
                               ()
     | ECond  (c,e1,e2)     -> ternary cxt t (adorn_x c Bool) t t c e1 e2
     | EArith (e1,op,e2)    -> (* lots and lots of overloading *)
                               (let tn1, tn2, tnout = 
                                  match op with
                                  | Plus
                                  | Minus       
                                  | TensorProd  -> let t = Unknown (new_unknown UnkEq) in t, t, t (* uniform overloading *)
                                  | Div         
                                  | TensorPower -> let t = Unknown (new_unknown UnkEq) in t, Num, t
                                  | Times       -> Unknown (new_unknown UnkEq), Unknown (new_unknown UnkEq), Unknown (new_unknown UnkEq)
                                  | Mod
                                  | Power       -> Num , Num , Num 
                                in
                                let t1, t2, tout = adorn_x e tn1, adorn_x e tn2, adorn_x e tnout in
                                (* arithmetic is massively overloaded. We hope to deal with some of the cases ... *)
                                binary cxt tout t1 t2 e1 e2;
                                let t1, t2, tout = evaltype t1, evaltype t2, evaltype tout in
                                
                                let bad () =
                                  match t1.inst, t2.inst with
                                  | Unknown _, Unknown _-> 
                                      raise (Error (e.pos, Printf.sprintf "overloaded %s: cannot deduce type of %s or %s (use some type constraints)"
                                                                            (string_of_arithop op)
                                                                            (string_of_expr e1)
                                                                            (string_of_expr e2)
                                                   )
                                            )
                                  | _                   ->
                                      raise (Error (e.pos, Printf.sprintf "overloaded %s: we have %s -> %s -> %s"
                                                                        (string_of_arithop op)
                                                                        (string_of_type t1)
                                                                        (string_of_type t2)
                                                                        (string_of_type tout)
                                                   )
                                            )
                                in
                                let ovld_warn = ovld_warn (string_of_arithop op) in
                                let ovld_warn2 = ovld_warn2 (string_of_arithop op) in
                                match op with
                                | Times       -> 
                                    (* we currently have the following
                                         Num    -> Num    -> Num   
                                         Sxnum  -> Sxnum  -> Sxnum   
                                         Gate   -> Gate   -> Gate
                                         Matrix -> Matrix -> Matrix
                                         Gate   -> Ket    -> Ket
                                         Ket    -> Bra    -> Matrix
                                         Bra    -> Ket    -> Sxnum
                                         Sxnum  -> Matrix -> Matrix
                                         Matrix -> Sxnum  -> Matrix
                                    ( -- Matrix -> Ket    -> Ket   -- not unless Ket can be un-normalised ...)
                                     *)
                                    (match t1.inst, t2.inst, tout.inst with
                                     | Num      , _        , _ 
                                     | _        , Num      , _ 
                                     | _        , _        , Num
                                     | Sxnum    , Sxnum    , _ 
                                     | Sxnum    , _        , Sxnum    
                                     | _        , Sxnum    , Sxnum    
                                     | Gate     , Gate     , _    
                                     | Matrix   , Matrix   , _    
                                     | Gate     , _        , Gate
                                     | Matrix   , _        , Matrix   
                                     | _        , Gate     , Gate      -> (try force_type e.pos t1 tout; force_type e.pos t2 tout
                                                                           with _ -> bad ()
                                                                          )

                                     | Gate     , Ket      , _         -> (try force_type e.pos t2 tout
                                                                           with _ -> bad ()
                                                                          )
                                     
                                     | Ket      , Bra      , _         -> (try force_type e.pos tout (adorn_x e Matrix)
                                                                           with _ -> bad ()
                                                                          )
                                     | Bra      , Ket      , _         -> (try force_type e.pos tout (adorn_x e Sxnum)
                                                                           with _ -> bad ()
                                                                          )
                                     | Matrix   , Sxnum    , _         
                                     | Sxnum    , Matrix   , _         -> (try force_type e.pos tout (adorn_x e Matrix)
                                                                           with _ -> bad ()
                                                                          )

                                     | _        , Matrix   , Matrix    -> (try force_type e.pos t1 tout; force_type e.pos t2 tout;
                                                                               ovld_warn e1 t2
                                                                           with _ -> bad ()
                                                                          )                                       
                                     
                                     | _                               -> bad ()
                                    )
                                | TensorProd  -> 
                                    (* we currently have the following
                                         Bra    -> Bra    -> Bra
                                         Ket    -> Ket    -> Ket
                                         Gate   -> Gate   -> Gate
                                         Matrix -> Matrix -> Matrix
                                      -- so it's uniform
                                     *)
                                    (match t1.inst with
                                     | Bra       
                                     | Ket      
                                     | Gate         
                                     | Matrix    -> ()
                                     | Unknown _ -> raise (Error (e.pos, Printf.sprintf "overloaded %s: cannot deduce type of %s or %s"
                                                                                           (string_of_arithop op)
                                                                                           (string_of_expr e1)
                                                                                           (string_of_expr e2)
                                                                  )
                                                           )       
                                     | _         -> bad ()
                                    )
                                | TensorPower ->
                                    (* we currently have the following
                                         Bra    -> Num    -> Bra
                                         Ket    -> Num    -> Ket
                                         Gate   -> Num    -> Gate
                                         Matrix -> Num    -> Matrix
                                      -- also uniform
                                     *)
                                    (match t1.inst with
                                     | Bra                       
                                     | Ket                        
                                     | Gate                       
                                     | Matrix    -> ()  
                                     | Unknown _ -> 
                                         raise (Error (e.pos, Printf.sprintf "overloaded %s: cannot deduce type of %s"
                                                                               (string_of_arithop op)
                                                                               (string_of_expr e1)
                                                      )
                                               )
                                     
                                     | _         -> bad ()
                                    )
                                | Plus
                                | Minus       ->
                                    (* we currently have the following 
                                         Num    -> Num    -> Num   
                                         Sxnum  -> Sxnum  -> Sxnum   
                                         Matrix -> Matrix -> Matrix
                                       -- nothing with Bra or Ket, because we want to keep them normalised. Hmm.
                                       
                                       Note this is uniform overloading (all the same shape), so t1, t2, tout are the same.
                                       See above. We assume Num -> Num -> Num if forced.
                                     *)
                                    (match t1.inst with
                                     | Num      
                                     | Sxnum     
                                     | Matrix    -> ()
                                     | Unknown _ -> let t = adorn e.pos Num in
                                                    ovld_warn2 e1 e2 t; 
                                                    force_type e.pos t1 t
                                     | _         -> bad ()
                                    )
                                | Div            ->
                                   (* no longer overloaded, because Angle is no more *)
                                    (match t1.inst with
                                     | Num       -> ()
                                     | Unknown _ -> let t = adorn e.pos Num in
                                                    ovld_warn e1 t; 
                                                    force_type e.pos t1 t
                                     | _         -> bad ()
                                    )
                                | Mod
                                | Power          -> ()  (* Num -> Num -> Num -- see above *)
                               )
     | ECompare (e1,op,e2)  -> (match op with 
                                   | Eq | Neq ->
                                       let t = new_Unknown e1.pos UnkEq in
                                       binary cxt (adorn_x e Bool) t t e1 e2
                                   | _ ->
                                       binary cxt (adorn_x e Bool) (adorn_x e1 Num) (adorn_x e2 Num) e1 e2
                                  )
     | EBoolArith (e1,_,e2) -> binary cxt (adorn_x e Bool) (adorn_x e1 Bool) (adorn_x e2 Bool) e1 e2
     | ESub (e1,e2)         -> binary cxt (adorn_x e Qubit) (adorn_x e1 Qubits) (adorn_x e2 Num) e1 e2
     | EAppend (e1,e2)      -> let t' = adorn_x e (List (newclasstv false e.pos)) in 
                               let _ = assigntype_expr cxt t' e1 in
                               let _ = assigntype_expr cxt t' e2 in
                               force_type e.pos t t'
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
                                    (match wtopt, !(toptr wpat) with
                                     | Some wt', Some ot -> force_type e.pos wt' ot
                                     | _                 -> ()
                                    );
                                    assigntype_pat (fun cxt -> assigntype_expr cxt t e) cxt wt wpat
  | EDFun (wfn,wfpats,wtoptr,we) -> ok_funname wfn;
                                    check_distinct_fparams wfpats;
                                    let tf, tr = read_funtype wfpats wtoptr we in
                                    assigntype_typedname tf wfn;
                                    let cxt = cxt <@+> (tinst wfn,tf) in
                                    let _ = assigntype_fun cxt tf wfpats we in
                                    let rt = newclasstv false we.pos in
                                    let _ = force_type e.pos rt tr in
                                    let cxt = (cxt <@-> tinst wfn) <@+> (tinst wfn, generalise tf) in
                                    assigntype_expr cxt t e

and assigntype_typedname t n =
  make_toptr n t
  
and assigntype_param t n = assigntype_typedname t n
  
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
                            | None   -> let t = newclasstv false e.pos in toptr := Some t; t (* result must be classical *)
                            | Some t -> t
                   in tr, tr
  and inventtype_pat pat =
    let f = match tinst pat with
            | PatName _ 
            | PatAny          -> (fun () -> ntv pat.pos)            (* note this is UnkAll -- any type of argument. Hmmm. *)
            | PatUnit         -> (fun () -> adorn pat.pos Unit)
            | PatTuple pats   -> let itp ts pat = inventtype_pat pat :: ts in
                                 let ts = List.fold_left itp [] pats in
                                 (fun () -> adorn pat.pos (Tuple (List.rev ts)))
            | _               -> raise (Can'tHappen (Printf.sprintf "inventtype_pat %s" (string_of_pattern pat)))
    in
    match !(Type.toptr pat) with
    | Some t -> t   (* not all that work for nothing: the PatNames have been typed *)
    | None   -> let t = f () in Type.toptr pat := Some t; t
  in 
  itf pats
  
and check_distinct_fparams pats =
  let rec cdfp set pat =
    match tinst pat with
    | PatName   n -> if NameSet.mem n set then
                       raise (Error (pat.pos, Printf.sprintf "repeated parameter %s" n))
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
  | pat::pats'  -> let ta = newclasstv false pat.pos in (* function arguments must be classical *)
                   let tr = newclasstv false (pos_of_instances pats') in
                   let tf = adorn (pos_of_instances pats) (Fun (ta,tr)) in
                   let _ = force_type e.pos t tf in
                   let contn cxt () = assigntype_fun cxt tr pats' e in
                   typecheck_pats contn cxt ta [pat,()]
  | []          -> assigntype_expr cxt t e
  
and ok_procname pn = 
  let n = tinst pn in
  let c = Stringutils.first n in
  if not ('A' <= c && c <= 'Z') then raise (Error (pn.pos, "process name " ^ string_of_name n ^ " should start with upper case"))

and ok_funname n =
  let c = Stringutils.first (tinst n) in
  if not ('a' <= c && c <= 'z') then raise (Error (n.pos, "function name " ^ string_of_name (tinst n) ^ " should start with lower case"))

let check_distinct_params params =
  let check set param =
    let n = name_of_param param in
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

(* monitor labels must be unique in the monitor, should be referred to in the process *)
let check_monlabels proc mon =
  let rec check_unique = 
    let rec cu lab = function
    | (l,(pos,_)) :: mon -> if lab = l then raise (Error (pos, "repeated monitor label"))
                                       else cu lab mon
    | []                 -> ()
    in
    function | (lab,_) :: mon -> cu lab mon; check_unique mon
             | []             -> ()
  in
  check_unique mon;
  let tpns = Process.called_mons proc in
  (* question 1: is any logging process called twice? *)
  (* it's ok to find just the first occurrence: this is not run from a card reader *)
  let rec checktpns = function
    | (lab1,pos1)::(lab2,pos2)::_
        when lab1=lab2              ->
            raise (Settings.Error (Printf.sprintf "Logging process %s called twice, at %s and %s"
                                                    lab1
                                                    (string_of_sourcepos pos1)
                                                    (string_of_sourcepos pos2)
                                  )
                  )
    | _::tpns                          -> checktpns tpns
    | []                               -> ()
  in
  checktpns (List.sort Stdlib.compare tpns);
  (* question 2: is any logging process not called? *)
  let tpnset = NameSet.of_list (List.map fst tpns) in
  List.iter (fun (lab,(pos,_)) -> 
               if not (NameSet.mem lab tpnset) then
                 warning pos "this logging process is unused. \
                              It isn't inserted anywhere, so it can't be type, match or resource checked";
              flush stderr
            ) 
            mon

(* let strip_procparams s cxt params = 
     if !verbose then
       Printf.printf "before strip_procparams %s (%s)\n%s\n\n" s (string_of_params params) (short_string_of_typecxt cxt);
     let cxt = List.fold_left (fun cxt p -> cxt<@-->(name_of_param p)) cxt (List.rev params) in
     if !verbose then
       Printf.printf "after strip_procparams %s\n\n" (short_string_of_typecxt cxt); 
     cxt
 *)

(* fnew is normally newcommtv, but in Iter it's newclasstv *)  
let fix_paramtype fnew par =
  match !(toptr par) with
  | Some t -> t
  | None   -> let t = fnew par.pos in toptr par := Some t; t (* process params are, like messages, qubit or qubits or classical *)
  
let unify_paramtype pos rt t =
  match !rt with
  | Some t' -> force_type pos t t'
  | None    -> rt := Some t
  
let process_param fnew par = name_of_param par, fix_paramtype fnew par

let rec do_procparams s fnew cxt params proc monparams mon =
  if !verbose then
    Printf.printf "do_procparams %s" (string_of_list string_of_param "," params);
  let cxt = List.fold_left (fun cxt param -> cxt <@+> process_param fnew param) cxt params in
  if !verbose then
    Printf.printf " -> %s\n" (string_of_list string_of_param "," params);
  typecheck_process mon cxt proc

and typecheck_process mon cxt p  =
  if !verbose then
    Printf.printf "typecheck_process .. %s %s:%s\n" (string_of_typecxt cxt) (string_of_sourcepos p.pos) (short_string_of_process p);
  match p.inst with
  | Terminate        -> ()
  | GoOnAs (pn,args) -> 
      let arglength = List.length args in
      ok_procname pn;
      let ts = 
        (try let t = Type.instantiate (evaltype (cxt<@>tinst pn)) in
             assigntype_typedname t pn;
             match t.inst with
             | Process ts -> if arglength <> List.length ts then
                               raise (Error (pn.pos,  Printf.sprintf "%s: should have %d arguments: this invocation provides %d"
                                                           (string_of_name (tinst pn))
                                                           (List.length ts)
                                                           arglength
                                           )
                                    );
                             ts
             | _          -> let ts = tabulate arglength (fun _ -> newcommtv p.pos) in
                             force_type p.pos t (adorn p.pos (Process ts));
                             ts
         with Not_found -> raise (Error (pn.pos, "undefined process " ^ string_of_name (tinst pn)))
        )
      in
      List.iter (fun (t,e) -> assigntype_expr cxt t e) (zip ts args)
  | WithNew ((_,params), proc) ->
      (* all the params have to be channels *)
      let _ = 
        List.iter (fun par -> 
                     unify_paramtype p.pos (toptr par) (adorn par.pos (Channel (newcommtv par.pos))) 
                  )
                  params
      in
      check_distinct_params params;
      do_procparams "WithNew" newcommtv cxt params proc [] mon
  | WithQubit (plural,qss,proc) -> 
      let tqnode = if plural then Qubits else Qubit in
      let typecheck_qspec cxt (par, kopt) =
        let _ = unify_paramtype p.pos (toptr par) (adorn par.pos tqnode) in
        match kopt with
        | Some k   -> assigntype_expr cxt (adorn k.pos Ket) k
        | None     -> ()
      in
      let _ = List.iter (typecheck_qspec cxt) qss in
      let params = List.map fst qss in
      check_distinct_params params;
      do_procparams "WithQubit" ntv cxt params proc [] mon
  | WithLet ((pat,e),proc) ->
      typecheck_letspec (fun cxt -> typecheck_process mon cxt proc) cxt pat e
  | WithProc (pdecl, proc) -> typecheck_pdecl (fun cxt -> typecheck_process mon cxt proc) mon cxt pdecl
  | WithQstep (qstep,proc) ->
      (match qstep.inst with
       | Measure (plural, e, gopt, pat) -> (* no longer overloaded: plural distinguishes qubits -> [bit] from qubit -> bit *)
           let te = adorn e.pos (if plural then Qubits else Qubit) in
           let tpat = adorn pat.pos (if plural then List (adorn pat.pos Bit) else Bit) in
           let _ = assigntype_expr cxt te e in
           let _ = ((fun ge -> assigntype_expr cxt (adorn ge.pos Gate) ge) ||~~ ()) gopt in
           assigntype_pat (fun cxt -> typecheck_process mon cxt proc) cxt tpat pat
       | Through (plural, es, ge, _) -> (* no longer overloaded: plural distinguishes qubits from qubit *)
           let do_e e = 
             let te = adorn e.pos (if plural then Qubits else Qubit) in
             assigntype_expr cxt te e
           in
           let _ = List.iter do_e es in
           let _ = assigntype_expr cxt (adorn ge.pos Gate) ge in
           typecheck_process mon cxt proc
      )
  | GSum gs ->
      (* let samechan x y = 
           match tinst x, tinst y with
           | EVar x, EVar y -> x=y
           | _                -> false
      in *)
      let is_alt = List.length gs > 1 (* && what a filthy hack
                   not (let step1 = fst (List.hd gs) in (* ok if all the alternatives _obviously_ use the same channel *)
                        List.for_all (fun (step,_) -> match step1.inst, step.inst with
                                                      | Read (ce1,_), Read (ce,_)   -> samechan ce1 ce
                                                      | Write (ce1,_), Write (ce,_) -> samechan ce1 ce
                                                      | _                           -> false
                                     )
                                     (List.tl gs)
                       ) *)
      in
      let newtv = if is_alt then newclasstv true else newcommtv in (* no quantum channels in alts: this will get a crap error message, sigh *)
      let check_g (iostep,proc) =
        match iostep.inst with
         | Read (ce, pat) ->
             let t = newtv ce.pos in
             let _ = assigntype_expr cxt (adorn ce.pos (Channel t)) ce in
             assigntype_pat (fun cxt -> typecheck_process mon cxt proc) cxt t pat
         | Write (ce, e) ->
             if is_alt then (* write guard in alt *)
               raise (Error (iostep.pos, "write guard in alt (temporary prohibition while I think of how to fix the type system)"));
             let t = newtv ce.pos in 
             let _ = assigntype_expr cxt (adorn ce.pos (Channel t)) ce in
             let _ = assigntype_expr cxt t e in
             typecheck_process mon cxt proc
      in
      List.iter check_g gs
  | JoinQs (qs,q,proc) ->
      let do_q qn = let t = try cxt<@>tinst qn with Not_found -> raise (Error (qn.pos, Printf.sprintf "undeclared %s" (string_of_typedname qn)))
                    in
                    force_type qn.pos t (adorn qn.pos Qubits);
                    assigntype_typedname t qn 
      in
      List.iter do_q qs; 
      let tq = adorn q.pos Qubits in
      assigntype_param tq q;
      typecheck_process mon (cxt<@+>(tinst q,tq)) proc
  | SplitQs (qn,sss,proc) ->
      assigntype_typedname (adorn qn.pos Qubits) qn;
      let do_splitspec cxt (qp, eopt) =
        let tq = adorn qp.pos Qubits in
        assigntype_param tq qp;
        (match eopt with
         | Some e -> assigntype_expr cxt (adorn e.pos Num) e
         | None   -> ()
        );
        cxt<@+>(tinst qp,tq)
      in
      typecheck_process mon (List.fold_left do_splitspec cxt sss) proc
  | TestPoint (n,proc) -> 
      (match find_monel n.inst mon with
       | Some (pos, monproc) -> (* typecheck the monproc in monitor context *)
                                typecheck_process [] cxt monproc
       | None                -> raise (Error (n.pos, Printf.sprintf "no monitor process labelled %s" n.inst))
      );
      typecheck_process mon cxt proc
  | Iter (pat, expr, ip, proc) -> 
      let t = newclasstv false expr.pos in
      let _ = assigntype_expr cxt (adorn expr.pos (List t)) expr in
      assigntype_pat (fun cxt -> typecheck_process mon cxt ip) cxt t pat;
      typecheck_process mon cxt proc
  | Cond (e,p1,p2) ->
      let _ = assigntype_expr cxt (adorn e.pos Bool) e in
      let _ = typecheck_process mon cxt p1 in
      typecheck_process mon cxt p2
  | PMatch (e,pms)  -> let et = newclasstv false e.pos in
                       let _ = assigntype_expr cxt et e in
                       typecheck_pats (typecheck_process mon) cxt et pms
  | Par (ps)        -> List.iter (typecheck_process mon cxt) ps
  
and typecheck_letspec contn cxt pat e =
  let t = newclasstv false e.pos in
  let _ = assigntype_expr cxt t e in
  (* Inconvenient though it may occasionally be, we can't do this mid-process ...
     let t = generalise t in
   *)
  assigntype_pat contn cxt t pat

and typecheck_pdecl contn mon cxt (brec, pn, params, proc) =
  let tparams = List.map (fix_paramtype (newclasstv false)) params in (* not newcommtv: internal processes can't take qubit arguments *)
  let tp = adorn pn.pos (Process tparams) in
  assigntype_typedname tp pn;
  let cxt = if brec then cxt<@+>(tinst pn,tp) else cxt in
  do_procparams "WithProc" newcommtv cxt params proc [] mon;
  let cxt = if brec then cxt else cxt<@+>(tinst pn,tp) in
  contn cxt

let make_library_assoc () =
  let assoc = List.map (fun (n,t,_) -> n, generalise (Parseutils.parse_typestring t)) !Library.knowns in
  let typ = adorn dummy_spos in
  let typstring = typ (List (typ Char)) in
  let assoc = if assoc <%@?> "dispose" then assoc else assoc <%@+> ("dispose", typ (Channel (typ Qubit))) in
  let assoc = if assoc <%@?> "out"     then assoc else assoc <%@+> ("out"    , typ (Channel (typ (List typstring)))) in
  let assoc = if assoc <%@?> "outq"    then assoc else assoc <%@+> ("outq"   , typ (Channel (typ Qstate))) in
  let assoc = if assoc <%@?> "in"      then assoc else assoc <%@+> ("in"     , typ (Channel typstring)) in
  assoc

let rec check_unique_ns s = function
  | (n,_)::ns -> (try let pos = ns<%@> n in raise (Error (pos, ("duplicate definition of " ^ s ^ " " ^ n)))
                  with Not_found -> check_unique_ns s ns
                 )
  | []        -> ()

let typecheck_fdefs assoc fdefs =
  let precxt assoc (fn,pats,toptr,e) =
    ok_funname fn; 
    check_distinct_fparams pats;
    let t, rt = read_funtype pats toptr e in
    toptr := Some rt; 
    if !(Type.toptr fn)=None then Type.toptr fn:=Some t;
    assoc <%@+> (tinst fn, t)
  in
  let fns = List.map (fun (fn,_,_,_) -> tinst fn, fn.pos) fdefs in
  check_unique_ns "function" fns;
  let assoc = List.fold_left precxt assoc fdefs in
  let tc_fdef assoc (fn,pats,topt,expr) = 
    let env_type = assoc<%@>tinst fn in
    (* force classical result type *)
    let rt = result_type fn.pos pats env_type in
    let rtv = newclasstv false rt.pos in
    let _ = force_type expr.pos rtv rt in
    assigntype_fun assoc (Type.instantiate env_type) pats expr;
    evalassoc assoc
  in
  let assoc = List.fold_left tc_fdef assoc fdefs in
  let postcxt assoc (fn,_) =  
    let t = evaltype (assoc<%@>fn) in
    (assoc <%@-> fn) <%@+> (fn, generalise t)
  in
  List.fold_left postcxt assoc fns

(* this is very similar to typecheck_fdefs, mutatis mutandis *)
let typecheck_pdefs assoc pdefs =     
  let precheck_pdef assoc (pn,ps,_,_) = 
      ok_procname pn;
      let process_param param = 
        let n,rt = tinst param, toptr param in
        let unknown = new_unknown commU in
        match !rt with
        | None   -> adorn param.pos (Unknown unknown)
        | Some t -> if (match t.inst with Poly _ -> true | _ -> false) ||
                       not (UnameSet.is_empty (Type.freetvs t)) 
                    then raise (Error (t.pos, "process parameter cannot be given a polytype or an unknown type"))
                    else
                    if not (canunifytype (fst unknown) t) 
                    then raise (Error (t.pos, "parameter type must be qubit, ^qubit or classical"))
                    else t
      in
      let process_params = List.map process_param in
      let t = adorn pn.pos (Process (process_params ps)) in
      toptr pn := Some t; (* I hope *)
      if assoc<%@?>tinst pn 
       then raise (Error (pn.pos,
                          Printf.sprintf "there is a previous definition of %s" 
                                         (string_of_name tinst pn)
                         )
                  );
      assoc <%@+> (tinst pn, t)
  in
  let pns = List.map (fun (pn,_,_,_) -> tinst pn, pn.pos) pdefs in
  check_unique_ns "process" pns;
  let assoc = List.fold_left precheck_pdef assoc pdefs in
  let tc_pdef assoc (pn,params,proc,mon as pdef) =
    if !verbose then
      Printf.printf "tc_pdef [%s]\n  %s\n\n" 
                     (string_of_typeassoc assoc)
                     (string_of_pdef pdef);
    let env_types = match (assoc<%@>tinst pn).inst with
                    | Process ts -> ts
                    | _          -> raise (Can'tHappen (Printf.sprintf "%s not a process name"
                                                                       (string_of_name tinst pn)
                                                       )
                                          )
    in
    check_distinct_params params;
    check_monlabels proc mon;
    let locals = List.map (process_param newcommtv) params in
    typecheck_process mon (monenv_of_lg locals (globalise assoc)) proc;
    let assoc = evalassoc assoc in
    let tps = zip env_types params in
    let _ = List.iter (fun (t, par) -> force_type par.pos t (type_of_typedname par)) tps in
    if !verbose then
      (rewrite_pdef pdef;
       Printf.printf "after tc_pdef, pdef = %s\n\nglobal_assoc = %s\n\n" 
                     (string_of_pdef pdef) 
                     (string_of_typeassoc assoc)
      );
    evalassoc assoc
  in
  let assoc = List.fold_left tc_pdef assoc pdefs in
  let postcheck assoc (n,_) =  
    let t = evaltype (assoc<%@>n) in
    (assoc <%@-> n) <%@+> (n, generalise t)
  in
  List.fold_left postcheck assoc pns

let typecheck_def assoc def =
  match def with
  | Processdefs  pdefs   -> typecheck_pdefs assoc pdefs
  | Functiondefs fdefs   -> typecheck_fdefs assoc fdefs
  | Letdef       (pat,e) ->
      (* sneaky use of reference to allow typecheck_letspec to return unit *)
      let cref = ref assoc in
      let contn cxt = cref := cxt in
      typecheck_letspec contn assoc pat e;
      evalassoc !cref

let typecheck defs =
  try push_verbose !verbose_typecheck (fun () ->
        let global_assoc = make_library_assoc () in
        let global_assoc = List.fold_left typecheck_def global_assoc defs in
        (* we check that the environment contains System as a process with a null parameter list *)
        (try let t = global_assoc<@>"System" in
             match t.inst with
             | Process []   -> ()
             | Process _    -> raise (Error (t.pos, "starting process System must have null parameter list"))
             | _            -> raise (Error (t.pos, Printf.sprintf "System value is type %s, not a process" (string_of_type t)))
         with Not_found -> raise (Error (dummy_spos, "no process called System"))
        );
        List.iter rewrite_def defs;
        if !verbose then 
          (Printf.printf "typechecked\n\ncxt =[\n]%s\n\ndefs=\n%s\n\n" 
                        (string_of_typeassoc global_assoc)
                        (string_of_list string_of_def "\n\n" defs);
           flush stdout;
          );
        if !verbose || !typereport then 
          Printf.printf "fully typed program =\n%s\n\n" (string_of_list string_of_def "\n\n" defs);
      )
  with Undeclared (pos, n) -> raise (Error (pos,
                                            Printf.sprintf "undeclared %s"
                                                           (string_of_name n)
                                           )
                                    )
