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
open Expr
open Instance
open Processdef
open Param
open Ugate
open Process
open Step

exception TypeUnifyError of _type * _type
exception TypeCheckError of sourcepos * string
exception Undeclared of sourcepos * name

(* converting to Map rather than assoc list for type contexts, 
   because resourcing needs a map of all typevars, obvs.
 *)
type typecxt         = _type NameMap.t
let (<@>) cxt n      = NameMap.find n cxt       (* is this evil? Over-riding Listutils.(<@>)?? *)
let (<@+>) cxt (n,t) = NameMap.add n t cxt      (* also evil? *)
let (<@->) cxt n     = NameMap.remove n cxt     (* also evil? *)
let (<@?>) cxt n     = NameMap.mem n cxt        (* you know, I no longer think it's evil *)

let string_of_typecxt = NameMap.to_string string_of_type

let new_TypeVar () = TypeVar (new_unknown_name ())

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
  | Qbit            -> t
  | TypeVar n       -> (try evaltype cxt (cxt <@> string_of_name n) with Not_found -> t)
  | Univ (ns,t')    -> let cxt = List.fold_left (fun cxt n -> cxt <@-> (string_of_name n)) cxt ns in
                       adorn (Univ (ns,evaltype cxt t'))
  | Range _         -> t
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
       | EVar        _
       | EInt        _
       | EBool       _
       | EChar       _
       | EString     _
       | EBit        _          
       | EBasisv     _          -> ()
       | EMinus      e          -> rewrite_expr cxt e
       | ETuple      es
       | EList       es         -> List.iter (rewrite_expr cxt) es
       | ECond       (e1,e2,e3) -> List.iter (rewrite_expr cxt) [e1;e2;e3]
       | EApp        (e1,e2)     
       | EAppend     (e1,e2)
       | EBitCombine (e1,e2)    -> List.iter (rewrite_expr cxt) [e1;e2]
       | EArith      (e1,_,e2)   
       | ECompare    (e1,_,e2)   
       | EBoolArith  (e1,_,e2)  -> List.iter (rewrite_expr cxt) [e1;e2]
      )
  | None   -> raise (TypeCheckError (e.pos,
                                     Printf.sprintf "** Disaster: typecheck didn't mark %s"
                                                    (string_of_expr e)
                                    )
                    )

let rewrite_param cxt {inst=n,rt} =
  match !rt with
  | Some t -> rt := Some (evaltype cxt t)
  | _      -> ()
  
let rewrite_params cxt = List.iter (rewrite_param cxt)

let rewrite_step cxt step = 
  match step.inst with
  | Read      (e,params)    -> rewrite_expr cxt e; rewrite_params cxt params
  | Write     (e,es)        -> rewrite_expr cxt e; List.iter (rewrite_expr cxt) es
  | Measure   (e,param)     -> rewrite_expr cxt e; rewrite_param cxt param
  | Ugatestep (es, ug)      -> List.iter (rewrite_expr cxt) es

let rec rewrite_process cxt proc = 
  match proc.inst with
  | Terminate               -> ()
  | Call      (n,es)        -> List.iter (rewrite_expr cxt) es
  | WithNew   (params, p)   -> rewrite_params cxt params; rewrite_process cxt p
  | WithQbit  (qss, p)      -> List.iter (rewrite_param cxt <.> fst) qss; rewrite_process cxt p
  | WithLet  ((param,e), p) -> rewrite_param cxt param; rewrite_expr cxt e; rewrite_process cxt p
  | WithStep (step, p)      -> rewrite_step cxt step; rewrite_process cxt p
  | Cond     (e, p1, p2)    -> rewrite_expr cxt e; rewrite_process cxt p1; rewrite_process cxt p2
  | Par      ps             -> List.iter (rewrite_process cxt) ps

let rewrite_processdef cxt (Processdef (n, params, proc)) =
  rewrite_params cxt params; rewrite_process cxt proc
  
(* useful in error messages *)
let pickdiff cxt t t1 t2 = 
  let t = evaltype cxt t in
  let t1 = evaltype cxt t1 in
  let t2 = evaltype cxt t2 in
  if t=t1 then t2 else t1
  
let rec unifytype cxt t1 t2 = 
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
  | List t1         , List t2           -> (try unifytype cxt t1 t2 with _ -> raise exn)
  | Fun (t1a,t1b)   , Fun (t2a,t2b)     -> unifylists exn cxt [t1a;t1b] [t2a;t2b]
  | Range (i,j)     , Range (m,n)       -> (* presuming t2 is the context ... *)
                                           if m<=i && j<=n then cxt else raise exn
  | _                                   -> if t1.inst=t2.inst then cxt else raise exn

and unifypair cxt (t1,t2) = unifytype cxt t1 t2

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
  | Range _         -> true
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
let evalcxt cxt = NameMap.map (evaltype cxt) cxt

let string_of_evalcxt = string_of_typecxt <.> evalcxt

let rec assign_name_type pos cxt t n =
  match eval cxt n with
  | Some t' -> 
      let t' = Type.instantiate t' in
      (try unifytype cxt t t' 
       with TypeUnifyError(t1,t2) -> 
         raise (TypeCheckError (pos,
                                Printf.sprintf "%s seems to be type %s, but in context has to be type %s"
                                               (string_of_name n)
                                               (string_of_type (evaltype cxt t2))
                                               (string_of_type (evaltype cxt t1)))
                               )
      )
  | None    -> raise (Undeclared (pos, n))

and assigntype_expr cxt t e =
  e.inst.etype := Some t; (* for rewriting later *)
  let utaf cxt = uncurry2 (assigntype_expr cxt) in
  try 
    let unary cxt tout tin e = 
       let cxt = unifytype cxt t tout in
       try assigntype_expr cxt tin e 
       with TypeUnifyError (t1,t2) -> 
         raise (TypeCheckError(e.pos,
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
     let adorn = Instance.adorn_x in
     match e.inst.enode with
     | EUnit                -> unifytype cxt t (adorn e Unit)
     | EInt i               -> (match (evaltype cxt t).inst with 
                                | Bit              -> if i=0||i=1 then cxt
                                                      else unifytype cxt t (adorn e Int)
                                | Range (j,k) as t -> if j<=i && i<=k then cxt 
                                                      else unifytype cxt (adorn e t) (adorn e Int)
                                | t                -> unifytype cxt (adorn e t) (adorn e Int)
                               )
     | EBool _              -> unifytype cxt t (adorn e Bool)
     | EChar _              -> unifytype cxt t (adorn e Char)
     | EString _            -> unifytype cxt t (adorn e String)
     | EBit b               -> (match (evaltype cxt t).inst with 
                                | Int              -> cxt
                                | Range (j,k) as t -> let i = if b then 1 else 0 in
                                                      if j<=i && i<=k then cxt 
                                                      else unifytype cxt (adorn e t) (adorn e Bit)
                                | t                -> unifytype cxt (adorn e t) (adorn e Bit)
                               )
     | EBasisv _            -> unifytype cxt t (adorn e Basisv)
     | EVar n               -> assign_name_type e.pos cxt t n
     | EApp (e1,e2)         -> let atype = adorn e2 (new_TypeVar()) in
                               let ftype = adorn e1 (Fun (atype, t)) in
                               let cxt = assigntype_expr cxt ftype e1 in 
                               assigntype_expr cxt atype e2
     | EMinus e             -> unary cxt (adorn e Int) (adorn e Int) e
     | ETuple es            -> let ts = List.map (fun e -> adorn e (new_TypeVar ())) es in
                               let tes = List.combine ts es in
                               let cxt' = List.fold_left utaf cxt tes in
                               unifytype cxt' t (adorn e (Tuple ts))
     | EList es             -> let t' = adorn e (new_TypeVar()) in
                               let cxt = List.fold_left (fun cxt -> assigntype_expr cxt t') cxt es in
                               unifytype cxt t (adorn e (List t'))
     | ECond (c,e1,e2)      -> ternary cxt t (adorn c Bool) t t c e1 e2
     | EArith (e1,_,e2)     -> binary cxt (adorn e Int)  (adorn e1 Int)  (adorn e2 Int)  e1 e2
     | ECompare (e1,op,e2)  -> (match op with 
                                   | Eq | Neq ->
                                       let t = adorn e1 (new_TypeVar ()) in
                                       binary cxt (adorn e Bool) t t e1 e2
                                   | _ ->
                                       binary cxt (adorn e Bool) (adorn e1 Int) (adorn e2 Int)  e1 e2
                                  )
     | EBoolArith (e1,_,e2) -> binary cxt (adorn e Bool)  (adorn e1 Bool)  (adorn e2 Bool)  e1 e2
     | EAppend (e1,e2)      -> let t' = adorn e (List (adorn e (new_TypeVar()))) in
                               let cxt = assigntype_expr cxt t' e1 in
                               let cxt = assigntype_expr cxt t' e2 in
                               unifytype cxt t t'
     | EBitCombine (e1, e2) -> let t' = adorn e (new_TypeVar ()) in
                               let cxt = assigntype_expr cxt t' e1 in
                               let cxt = assigntype_expr cxt (adorn e2 Bit) e2 in
                               (* if e1 is a Bit, an Int or a Range then we know what to do. 
                                * Otherwise force Int
                                *)
                               let t' = evaltype cxt t' in
                               (match t'.inst with
                                | Int         -> unifytype cxt t t'
                                | Bit         -> unifytype cxt t (adorn e (Range (0,3)))
                                | Range (j,k) -> unifytype cxt t (adorn e (Range (2*j, 2*k+1)))
                                | t1          -> let cxt = unifytype cxt t' (adorn e Int) in
                                                 unifytype cxt t (adorn e Int)
                               )
with 
  | TypeUnifyError (t1,t2)  -> raise (TypeCheckError (e.pos,
                                                      Printf.sprintf "%s appears to be type %s, but in context should be %s"
                                                                     (string_of_expr e) 
                                                                     (string_of_type (evaltype cxt t2))
                                                                     (string_of_type (evaltype cxt t1))
                                                     )
                                     )
  
let ok_procname n = 
  let c = Stringutils.first n.inst in
  if not ('A' <= c && c <= 'Z') then raise (TypeCheckError (n.pos, "process name " ^ string_of_name n.inst ^ " should start with upper case"))

let rec typecheck_ugate cxt ugate = (* arity, cxt *)
  match ugate.inst with
  | GH
  | GI
  | GX                    -> 1, cxt
  | GCnot                 -> 2, cxt 
  | GPhi (e)              -> 1, assigntype_expr cxt (adorn e.pos (Range (0,3))) e
  | GCond (e, ug1, ug2)   -> let cxt = assigntype_expr cxt (adorn e.pos Bool) e in
                             let a1, cxt = typecheck_ugate cxt ug1 in
                             let a2, cxt = typecheck_ugate cxt ug2 in
                             if a1=a2 then a1,cxt
                             else raise (TypeCheckError (ugate.pos, "arity mismatch in " ^ string_of_ugate ugate))

let check_distinct params =
  let check set {inst=n,_} =
    if NameSet.mem n set then 
      raise (TypeCheckError (pos_of_list params, 
                             Printf.sprintf "non-distinct parameters (%s)"
                                            (string_of_list string_of_param "," params)
                            )
            )
    else NameSet.add n set
  in
  let _ = List.fold_left check NameSet.empty params in
  ()

let strip_procparams s cxt params = 
  (* Printf.printf "before strip_procparams %s (%s)\n%s\n" s (string_of_params params) (string_of_typecxt cxt); *)
  let cxt = List.fold_left (fun cxt p -> cxt<@->(strip_param p)) cxt params in
  (* Printf.printf "after strip_procparams %s\n" (string_of_typecxt cxt); *)
  cxt

let rec do_procparams s cxt params proc =
  if !verbose_typecheck then
    Printf.printf "do_procparams %s" (string_of_list string_of_param "," params);
  let process_param {pos=pos; inst=n,rt} = n, fix_paramtype pos rt in
  let cxt = List.fold_left (fun cxt param -> cxt <@+> process_param param) cxt params in
  if !verbose_typecheck then
    Printf.printf " -> %s\n" (string_of_list string_of_param "," params);
  let cxt = typecheck_process cxt proc in
  strip_procparams s cxt params

and fix_paramtype pos rt =
  match !rt with
  | Some t -> t
  | None   -> let t = adorn pos (new_TypeVar()) in rt := Some t; t
  
and unify_paramtype cxt rt t =
  match !rt with
  | Some t' ->               unifytype cxt t t'
  | None    -> rt := Some t; cxt
  
and typecheck_process cxt p =
  if !verbose_typecheck then
    Printf.printf "typecheck_process ... %s\n" (short_string_of_process p);
  match p.inst with
  | Terminate     -> cxt
  | Call (n,args) -> 
      ok_procname n;
      let ts = 
        (try let t = evaltype cxt (cxt<@>n.inst) in
             match t.inst with
             | Process ts -> ts
             | _          -> raise (TypeCheckError (n.pos, string_of_name n.inst ^ " used as process name, but declared as " ^ string_of_type t))
         with _ -> raise (TypeCheckError (n.pos, "undefined process " ^ string_of_name n.inst))
        )
      in
      let ets = try zip args ts
                with Zip -> 
                       raise (TypeCheckError (p.pos,
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
                          unify_paramtype cxt rt (adorn pos (Channel (adorn pos (new_TypeVar ())))) 
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
  | WithLet ((p,e),proc) -> 
      let (n,rt) = p.inst in
      let t = fix_paramtype p.pos rt in
      let cxt = assigntype_expr cxt t e in
      do_procparams "WithLet" cxt [p] proc
  | WithStep (step,proc) ->
      (match step.inst with
       | Read (chan, params) ->
           let chants = List.map (fun param -> adorn param.pos (new_TypeVar())) params in 
           let chant = Type.delist chan.pos chants in
           let cxt = assigntype_expr cxt (adorn chan.pos (Channel chant)) chan in
           let stitch (t', {inst=n,rt}) cxt = 
             unify_paramtype cxt rt t'
           in
           let cxt = List.fold_right stitch (zip chants params) cxt in
           check_distinct params;
           do_procparams "Read" cxt params proc 
       | Write (chan, es) ->
           let chants = List.map (fun e -> adorn e.pos (new_TypeVar())) es in 
           let chant = Type.delist chan.pos chants in
           let cxt = assigntype_expr cxt (adorn chan.pos (Channel chant)) chan in
           let cxt = List.fold_left (fun cxt (t,v) -> assigntype_expr cxt t v) cxt (zip chants es) in
           typecheck_process cxt proc
       | Measure (e, param) ->
           let n,rt = param.inst in
           let cxt = assigntype_expr cxt (adorn e.pos Qbit) e in
           let cxt = unify_paramtype cxt rt (adorn param.pos Bit) in
           do_procparams "Measure" cxt [param] proc
       | Ugatestep (es, ugate) ->
           let cxt = List.fold_left (fun cxt e -> assigntype_expr cxt (adorn e.pos Qbit) e) cxt es in
           let arity, cxt = typecheck_ugate cxt ugate in
           if List.length es <> arity then 
             raise (TypeCheckError (step.pos, "arity mismatch in " ^ string_of_step step))
           ;
           typecheck_process cxt proc
      )
  | Cond (e,p1,p2) ->
      let cxt = assigntype_expr cxt (adorn e.pos Bool) e in
      let cxt = typecheck_process cxt p1 in
      typecheck_process cxt p2
  | Par (ps) -> List.fold_left typecheck_process cxt ps

let typecheck_processdef cxt (Processdef (pn,params,proc) as def) =
  let env_types = match (cxt<@>pn.inst).inst with
                  | Process ts -> ts
                  | _          -> raise (TypeCheckError (pn.pos,
                                                         Printf.sprintf "%s not a process name"
                                                                        (string_of_name pn.inst)
                                                        )
                                        )
  in
  check_distinct params;
  let cxt = do_procparams "processdef" cxt params proc in
  let cxt = evalcxt cxt in
  let tps = zip env_types params in
  let cxt = List.fold_left (fun cxt (t,{inst=n,rt}) -> unifytype cxt t (_The !rt)) cxt tps in
  if !verbose_typecheck then
    (rewrite_processdef cxt def;
     Printf.printf "after typecheck_processdef, def = %s\n\ncxt = %s\n\n" 
                   (string_of_processdef def) 
                   (string_of_typecxt cxt)
    );
  cxt

let make_cxt lib defs =
      (* lib is a list of name:type pairs; all should be process types with proper process names *)
      List.iter (fun (n,t) -> match t.inst with 
                              | Process _ -> ok_procname n 
                              | _         -> raise (TypeCheckError (t.pos,
                                                                    Printf.sprintf "error in given list: %s: %s is not a process spec"
                                                                           (string_of_name n.inst)
                                                                           (string_of_type t)
                                                           )
                                           )
                ) 
                lib;
      let lib = List.map (fun (n,t) -> n.inst, t) lib in
      let knownassoc = List.map (fun (n,t,_) -> n, generalise (Parseutils.parse_typestring t)) !Interpret.knowns in
      List.fold_left (fun cxt binding -> cxt <@+> binding) NameMap.empty (lib @ knownassoc)
      
let typecheck lib defs =
  try
      let cxt = make_cxt lib defs in
      let header_type cxt (Processdef (pn,ps,_) as def) =
        ok_procname pn;
        let process_param param = 
          let n,rt = param.inst in
          match !rt with
          | None   -> (adorn param.pos (new_TypeVar ()))
          | Some t -> if (match t.inst with Univ _ -> true | _ -> false) ||
                         not (NameSet.is_empty (Type.frees t)) 
                      then raise (TypeCheckError (t.pos,
                                                  Printf.sprintf "Error in %s: process parameter cannot be given a universal type"
                                                                 (string_of_param param)
                                                 )
                                 )
                      ;
                      (match t.inst with Process _ -> ok_procname {pos=param.pos; inst=n} | _ -> ())
                      ;
                      t
        in
        let process_params = List.map process_param in
        if cxt<@?>pn.inst 
        then raise (TypeCheckError (pn.pos,
                                    Printf.sprintf "Error in %s: previous definition of %s" 
                                                   (string_of_processdef def)
                                                   (string_of_name pn.inst)
                                   )
                   )
        else cxt <@+> (pn.inst, (adorn pn.pos (Process (process_params ps))))
      in
      let cxt = List.fold_left header_type cxt defs in
      let cxt = List.fold_left typecheck_processdef cxt defs in
      List.iter (rewrite_processdef cxt) defs;
      if !verbose || !verbose_typecheck then 
        Printf.printf "typechecked\n\ncxt =\n%s\n\ndefs=\n%s\n\n" 
                      (string_of_typecxt cxt)
                      (string_of_list string_of_processdef "\n\n" defs);
      (List.map (fun (n,t) -> n, evaltype cxt t) lib), cxt
  with Undeclared (pos, n) -> raise (TypeCheckError (pos,
                                                     Printf.sprintf "undeclared %s"
                                                                    (string_of_name n)
                                                    )
                                    )
