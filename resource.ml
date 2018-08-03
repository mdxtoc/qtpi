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

(* Resources in quantum protocols are qbits. A qbit is owned by a single process.
   Resources are received in process invocations and in reads; they are transmitted
   in process calls and in sends.
   
   The parameters of a process definition name resources. Suppose those resources
   are non-overlapping. Then if the process body distributes those resources in a
   non-overlapping way -- if the tuple expressions in its sends are non-overlapping, if 
   tuples of arguments in its process calls are non-overlapping, if the tuples of process
   calls in its parallel calls are non-overlapping -- then we shall have correct resourcing.
   
   Provided, of course, we police the use of qbits that are sent away down channels.
   
   To begin, channels take either a single qbit or a classical value. Seems to make
   practical sense. And function applications must not deliver a qbit, or a value containing
   a qbit.
   
   Good luck to us all.
 *)
 
open Settings
open Instance
open Sourcepos
open Listutils
open Optionutils
open Tupleutils
open Functionutils
open Name
open Type
open Expr
open Param
open Processdef
open Process
open Step
open Pattern
open Typecheck

exception ResourceError of sourcepos * string
exception ResourceDisaster of sourcepos * string

let rec is_resource_type t =
  match t.inst with
  | Qbit            -> true            
  | Unit          
  | Int 
  | Bool
  | Char
  | String
  | Bit 
  | Basisv
  | Gate    _
  | TypeVar _          (* can happen in Univ ... *)
  | Range   _       -> false
  | Univ (ns, t)    -> is_resource_type t 
  | List    t       -> is_resource_type t 
  | Channel t       -> false
  | Tuple   ts      -> List.exists is_resource_type ts
  | Fun     (t1,t2) -> is_resource_type t1 || is_resource_type t2
                     
  | Process _       -> false

let type_of_expr e =
  match !(e.inst.etype) with
  | Some t -> t
  | None   -> raise (ResourceDisaster (e.pos,
                                       Printf.sprintf "typecheck didn't mark %s"
                                                      (string_of_expr e)
                                      )
                    )

(* *************** phase 1: channel types and function applications (ctfa_...) *************************** *)
(* ******************************* also check that we don't compare qbits ******************************** *)

let rec ctfa_type classic t = 
  let badtype s = raise (ResourceError (t.pos,
                                        Printf.sprintf "type %s: %s"
                                                       (string_of_type t)
                                                       s
                                       )
                         )
  in
  match t.inst with
  | Qbit            -> if classic then badtype "should be classical, includes qbit" else ()
  | Unit
  | Int
  | Char
  | String
  | Bool
  | Bit 
  | Basisv
  | Gate    _
  | Range   _       -> ()
  | TypeVar n       -> (* it really doesn't matter: type variables just correspond to unused variables *)
                       ()
  | Univ    (ns, t) -> ctfa_type classic t
  | List    t       -> ctfa_type classic t
  | Tuple   ts    
  | Process ts      -> List.iter (ctfa_type classic) ts
  | Channel t       -> (match t.inst with
                        | Qbit      -> () (* always ok, even in classical channels *)
                        | _         -> try ctfa_type true t
                                       with _ -> badtype "should be a channel of qbit or a classical channel"
                       )
  | Fun  _          -> () (* function types are classical, always *)

let ctfa_def (Processdef(pn, params, proc)) =
  let ctfa_param p =
    let bad_param s = raise (ResourceError (p.pos, Printf.sprintf "parameter %s: %s"
                                                                  (string_of_param p)
                                                                  s
                                           )
                                    )
    in
    let n, tor = p.inst in
    match !tor with
    | Some t -> ctfa_type false t
    | _      -> bad_param "Disaster (typechecked type expected)"
  in
  
  let rec ctfa_proc proc =
    match proc.inst with
    | Terminate                  -> ()
    | Call      (pn', es)        -> List.iter ctfa_expr es
    | WithNew   (params, proc)   -> List.iter ctfa_param params; ctfa_proc proc
    | WithQbit  (qspecs, proc)   -> List.iter (fun (param,_) -> ctfa_param param) qspecs;
                                    ctfa_proc proc
    | WithLet   (letspec, proc)  -> let pat, e = letspec in
                                    ctfa_expr e;
                                    ctfa_proc proc
    | WithQstep (qstep, proc)    -> ctfa_qstep qstep; ctfa_proc proc
    | WithExpr  (e, proc)        -> ctfa_expr e; ctfa_proc proc
    | Cond      (ce,p1,p2)       -> ctfa_expr ce; List.iter ctfa_proc [p1;p2]
    | GSum      gs               -> let ctfa_g (iostep, proc) =
                                      ctfa_iostep iostep; ctfa_proc proc
                                    in
                                    List.iter ctfa_g gs
    | PMatch    (e,pms)          -> ctfa_expr e; List.iter (ctfa_proc <.> snd) pms
    | Par       procs            -> List.iter ctfa_proc procs
  
  and ctfa_qstep qstep =
    match qstep.inst with
    | Measure   (qe,gopt,param) -> ctfa_expr qe; 
                                   (match gopt with Some g -> ctfa_expr g | None -> ());
                                   ctfa_param param
    | Ugatestep (qes, ug)       -> List.iter ctfa_expr qes
  
  and ctfa_iostep iostep =
    (* if the channel types are right then we don't need to type-police the steps. But check the exprs for use of functions *)
    match iostep.inst with
    | Read      (ce,params) -> ctfa_expr ce; List.iter ctfa_param params
    | Write     (ce,es)     -> List.iter ctfa_expr (ce::es)
  
  and ctfa_expr e =
    match e.inst.enode with
    | EUnit
    | ENil
    | EVar       _
    | EInt       _
    | EBool      _
    | EChar      _
    | EString    _
    | EBit       _          
    | EBasisv    _          -> ()   (* constants *)
    | EGate      ug         -> (match ug.inst with
                                  | GH | GI | GX | GY | GZ | GCnot -> ()
                                  | GPhi e                         -> ctfa_expr e
                               )
    | EMinus     e          -> ctfa_expr e
    | ETuple     es         -> List.iter ctfa_expr es
    | EMatch     (e,ems)    -> ctfa_expr e; List.iter (ctfa_expr <.> snd) ems
    | ECond      (ce,e1,e2) -> if is_resource_type (type_of_expr e1) then
                                raise (ResourceError (e.pos,
                                                      "comparison of qbits, or values containing qbits, not allowed"
                                                     )
                                      )
                               else ();
                               List.iter ctfa_expr [ce;e1;e2]
    | EApp        (ea,er)   -> if is_resource_type (type_of_expr e) then
                                raise (ResourceError (e.pos,
                                                      "a function application may not deliver a qbit, or a value containing a qbit"
                                                     )
                                      )
                               else ();
                               List.iter ctfa_expr [ea; er]
    | EArith      (e1,_,e2)
    | ECompare    (e1,_,e2)
    | EBoolArith  (e1,_,e2) -> List.iter ctfa_expr [e1;e2]
    | ECons       (e1,e2)    
    | EBitCombine (e1,e2)   -> List.iter ctfa_expr [e1;e2]
    | EAppend     (e1,e2)   -> if is_resource_type (type_of_expr e) then
                                raise (ResourceError (e.pos,
                                                      "list append may not be applied to lists including qbits"
                                                     )
                                      )
                               else ();
                               List.iter ctfa_expr [e1;e2]
    
  in
  List.iter ctfa_param params;
  ctfa_proc proc
  
(* we don't need ctfa_pat *)

(* *************** phase 2: resource check (rck_...) *************************** *)

type resource =
  | RNull
  | RQbit of int                
  | RTuple of resource list
  | RList of name                   (* for stuff that hasn't been taken apart *)
  | RCons of resource * resource    (* using RNull at the end of the list ... *)
  | RMaybe of resource list         (* for dealing with conditional and match expressions, sigh ... *)
  
let rec string_of_resource r =
  match r with
  | RNull               -> "RNull"
  | RQbit  i            -> Printf.sprintf "RQbit %d" i
  | RTuple rs           -> Printf.sprintf "RTuple (%s)" (string_of_list string_of_resource "*" rs)
  | RList  n            -> Printf.sprintf "RList %s" (string_of_name n)
  | RCons  (rh,rt)      -> Printf.sprintf "RCons (%s,%s)" (string_of_resource rh) (string_of_resource rt)
  | RMaybe rs           -> Printf.sprintf "RMaybe %s" (bracketed_string_of_list string_of_resource rs)
  
module OrderedResource = struct type t = resource let compare = Pervasives.compare let to_string = string_of_resource end
module ResourceSet = MySet.Make(OrderedResource)  

module OrderedInt = struct type t = int let compare=Pervasives.compare let to_string=string_of_int end
module State = MyMap.Make(OrderedInt) (* to tell if qbits have been sent away *)

let string_of_state = State.to_string string_of_bool
let string_of_env = NameMap.to_string string_of_resource

let rec lookup renv n =
  try let r = renv <@> n in
      match r with
      | RList l -> (try lookup renv l with _ -> r)
      | _       -> r
  with Not_found -> raise (ResourceDisaster (dummy_spos, "unbound " ^ n))

let (<@>) = lookup

let newqid =
  (let qid = ref 0 in
   let newqid state =
     let q = !qid in
     qid := !qid+1;
     State.add q true state, q
   in
   newqid
  )
  
let resource_of_type state t = (* makes new resource: for use in parameter bindings *)
  let rec rt state t =
    match t.inst with
    | Int
    | Bool
    | Char
    | String
    | Bit 
    | Unit  
    | Basisv
    | Gate  _         
    | Range _         -> state, RNull
    | Qbit            -> let state, q = newqid state in state, RQbit q
    | TypeVar _       -> state, RNull  (* checked in ctfa *)
    | Univ _          -> state, RNull  (* checked in cfta *)
    | List t          -> let state, r = rt state t in
                         state, (if r=RNull then RNull else RList (new_unknown_name ()))
    | Tuple ts        -> let state, rs = List.fold_right (fun t (state,rs) -> let state, r = rt state t in state, r::rs) ts (state,[]) in
                         if List.exists (function RNull -> false | _ -> true) rs
                         then state, RTuple rs 
                         else state, RNull
    | Channel _       
    | Fun     _ 
    | Process _       -> state, RNull
  in
  rt state t

type use = 
  | Uok
  | Uarith
  | Ucompare
  | Ubool
  
let rec resources_of_resource r =
  match r with
  | RNull           -> ResourceSet.empty
  | RQbit _         -> ResourceSet.singleton r                
  | RTuple rs       -> resources_of_resourcelist rs
  | RList _         -> ResourceSet.singleton r
  | RCons  (r1,r2)  -> ResourceSet.union (resources_of_resource r1) (resources_of_resource r2)
  | RMaybe rs       -> List.fold_left (fun u r -> ResourceSet.union u (resources_of_resource r)) ResourceSet.empty rs
  
and resources_of_resourcelist rs = 
  List.fold_left (revargs ResourceSet.add) ResourceSet.empty rs
  
exception OverLap of string

  let rec rck_pat is_me contn state env pat res =
    let bad () = raise (ResourceDisaster (pat.pos,
                                          Printf.sprintf "pattern %s resource %s"
                                                         (string_of_pattern pat)
                                                         (string_of_resource res)
                                         )
                  )
    in
    if !verbose || !verbose_resource then 
      Printf.printf "rck_pat %B %s %s %s %s\n" is_me 
                                               (string_of_state state)
                                               (string_of_env env)
                                               (string_of_pattern pat)
                                               (string_of_resource res);
    match pat.inst.pnode with
    | PatAny    
    | PatUnit   
    | PatNil
    | PatInt    _ 
    | PatBit    _
    | PatBool   _
    | PatChar   _
    | PatString _
    | PatBasisv _
    | PatGate   _       -> contn state env
    | PatName   n       -> contn state (env<@+>(n,res))
    | PatCons   (ph,pt) -> let doit contn state env rh rt =
                             let tl state env = rck_pat is_me contn state env pt rt in
                             rck_pat is_me tl state env ph rh
                           in
                           (match res with
                            | RNull         -> doit contn state env RNull RNull
                            | RCons (rh,rt) -> doit contn state env rh rt
                            | RList l       -> if is_me then
                                                 raise (ResourceError (pat.pos,
                                                                       "match expressions may not be used to uncover qbits in list parameters"
                                                                      )
                                                       )
                                               else (let state, rh = resource_of_type state (_The !(ph.inst.ptype)) in
                                                     let rt = RList (new_unknown_name ()) in
                                                     let env = env<@+>(l,RCons(rh,rt)) in
                                                     doit contn state env rh rt
                                                    )
                            | _             -> bad ()
                           )
    | PatTuple ps       -> let rec rck state env = function
                             | (p,r)::prs -> rck_pat is_me (fun state env -> rck state env prs) state env p r
                             | []         -> contn state env
                           in
                           (match res with
                            | RNull     -> rck state env (List.map (fun p -> p,RNull) ps)
                            | RTuple rs -> rck state env (zip ps rs)
                            | _         -> bad ()
                           )

and rck_pats is_me rck state env re pxs =
  let rck_px (pat,x) = rck_pat is_me (fun state env -> rck state env x) state env pat re in
  List.map rck_px pxs
    
;; (* to give rck_pat and rck_pats a universal type *)

let disju ers =
  let dju set er = if not (ResourceSet.is_empty (ResourceSet.inter set er)) 
                   then raise (OverLap (Printf.sprintf "non-disjoint resources (%s)" (string_of_list ResourceSet.to_string "," ers)))
                   else ResourceSet.union set er in
  List.fold_left dju ResourceSet.empty ers

let resources_of_expr state env e =
  let rec re_env use env e =
    let rec re use e =
      let do_list use es = List.fold_right (fun e (rs, set) -> let r, used = re use e in
                                                                 r::rs, ResourceSet.union set used 
                                         )
                                         es
                                         ([],ResourceSet.empty) 
      in
      match e.inst.enode with
      | EUnit 
      | ENil
      | EInt        _              
      | EBool       _
      | EChar       _
      | EString     _
      | EBit        _         
      | EBasisv     _         -> RNull, ResourceSet.empty
      | EGate       ug        -> (match ug.inst with
                                    | GH | GI | GX | GY | GZ | GCnot -> RNull, ResourceSet.empty
                                    | GPhi e                         -> let _, used = re use e in
                                                                        RNull, used
                                 )                    
      | EMinus      e         -> re Uarith e
      | EArith      (e1,_,e2) -> let _, used = do_list Uarith   [e1;e2] in RNull, used
      | ECompare    (e1,_,e2) -> let _, used = do_list Ucompare [e1;e2] in RNull, used
      | EBoolArith  (e1,_,e2) -> let _, used = do_list Ubool    [e1;e2] in RNull, used
      | EVar        n         -> let r = env <@> n in
                                  (match r with
                                  | RNull   -> RNull, ResourceSet.empty
                                  | RQbit q -> if use<>Uok then
                                                 raise (ResourceError (e.pos,
                                                                       Printf.sprintf "use of qbit %s in %s"
                                                                                      (match use with 
                                                                                       | Uok      -> "??"
                                                                                       | Uarith   -> "arithmetic"
                                                                                       | Ucompare -> "comparison"
                                                                                       | Ubool    -> "boolean arithmetic"
                                                                                      )
                                                                                      (string_of_name n)
                                                                      )
                                                        )
                                               else
                                               if State.find q state then r, ResourceSet.singleton r
                                               else
                                                 raise (ResourceError (e.pos,
                                                                       Printf.sprintf "use of sent-away qbit %s" (string_of_name n)
                                                                      )
                                                        )
                                  | _       -> r, resources_of_resource r
                                 )
      | ETuple      es        -> let rs, used = do_list use es in RTuple rs, used
      | ECons       (hd,tl)   -> let r1, u1 = re use hd in
                                 let r2, u2 = re use tl in
                                 (try match r1, r2 with
                                  | RNull, _        (* if the hd has no resource, neither can the list *)
                                  | _    , RNull -> (* likewise the tail *)
                                                    RNull, ResourceSet.union u1 u2
                                  | _            -> RCons (r1,r2), disju [u1;u2] (* disjoint union essential *)
                                  with OverLap _ ->
                                    raise (ResourceError (e.pos,
                                                          Printf.sprintf "%s and %s share qbits"
                                                                         (string_of_expr hd)
                                                                         (string_of_expr tl)
                                                         )
                                          )
                                 )
      | EMatch      (e,ems)   -> let re, usede = re use e in
                                 let rus = rck_pats true (fun _ env -> re_env use env) state env re ems in
                                 let rs, useds = unzip rus in
                                 (match List.filter (function RNull -> false | _ -> true) rs with
                                  | []  -> RNull
                                  | [r] -> r 
                                  | rs  -> RMaybe rs
                                 ),
                                 List.fold_left ResourceSet.union usede useds
      | ECond       (ce,e1,e2)-> let _ , used0 = re Ubool ce in
                                 let r1, used1 = re use e1 in
                                 let r2, used2 = re use e2 in
                                 (match r1, r2 with
                                  | RNull, _      -> r2
                                  | _    , RNull  -> r1
                                  | _             -> if r1=r2 then r1 else RMaybe [r1;r2]
                                 ),
                                 ResourceSet.union used0 (ResourceSet.union used1 used2)
      | EApp        (e1,e2)   
      | EAppend     (e1,e2)   -> let _, used1 = re use e1 in
                                 let _, used2 = re use e2 in
                                 (* EAppend and EApp don't return resources: we checked *)
                                 RNull, ResourceSet.union used1 used2
      | EBitCombine (e1,e2)   -> let _, used = do_list Uarith   [e1;e2] in RNull, used
    in re use e
  in
  re_env Uok env e
  
let resource_of_params state params = 
  List.fold_right (fun {inst=n,toptr} (state, nrs) -> 
                     let state, r = resource_of_type state (_The !toptr) in
                     state, (n,r)::nrs 
                  ) 
                  params
                  (state,[])

let rec rck_proc state env proc = 
  let badproc s =
    raise (ResourceError (proc.pos,
                          Printf.sprintf "checking %s: %s"
                                         (short_string_of_process proc)
                                         s
                         )
          )
  in
  let rec rp state env proc =
    if !verbose || !verbose_resource then 
      Printf.printf "rp %s %s %s\n" (string_of_env env)
                                    (string_of_state state)
                                    (short_string_of_process proc);
    let r =
      (match proc.inst with
      | Terminate               -> ResourceSet.empty
      | Call (n, es)            -> (* disjoint resources in the arguments, no dead qbits used *)
                                   (try let ers = List.map (snd <.> resources_of_expr state env) es in
                                        disju ers
                                    with OverLap s -> badproc s
                                   )
      | WithNew (params, proc)  -> (* all channels, no new resource, nothing used *)
                                   let env = List.fold_left (fun env {inst=n,_} -> env <@+> (n,RNull)) env params in
                                   rp state env proc
      | WithQbit (qspecs, proc) -> (* all new qbits, nothing used *)
                                   let state, env = 
                                     List.fold_left (fun (state, env) (param,_) -> 
                                                        let (n,_) = param.inst in
                                                        let state, q = newqid state in
                                                        state, env <@+> (n,RQbit q)
                                                    ) 
                                                    (state, env) 
                                                    qspecs 
                                   in
                                   rp state env proc
      | WithLet (letspec, proc) -> (* whatever resource the expression gives us *)
                                   let pat, e = letspec in
                                   let re, usede = resources_of_expr state env e in 
                                   let used = rck_pat false (fun state env -> rp state env proc) state env pat re in
                                   ResourceSet.union used usede
      | WithQstep (qstep,proc)  -> (match qstep.inst with 
                                    | Measure (qe, bopt, param) -> 
                                        let n,_ = param.inst in
                                        let _, usedq = resources_of_expr state env qe in
                                        let usedb = match bopt with
                                                    | Some e -> snd (resources_of_expr state env e)
                                                    | None   -> ResourceSet.empty
                                        in
                                        ResourceSet.union usedq (ResourceSet.union usedb (rp state (env <@+> (n,RNull)) proc))
                                    | Ugatestep (qes, ug)    -> 
                                        (try let qers = List.map (snd <.> resources_of_expr state env) qes in
                                             let used = disju qers in
                                             ResourceSet.union (rp state env proc) used
                                         with OverLap s -> badproc s
                                        )
                                   )
      | WithExpr (e, proc)      -> let _, used = resources_of_expr state env e in
                                   ResourceSet.union used (rp state env proc)
      | Cond (ce,p1,p2)         -> (try let _, used = resources_of_expr state env ce in
                                        let prs = List.map (rp state env) [p1;p2] in
                                        List.fold_left ResourceSet.union used prs (* NOT disju, silly boy! *)
                                    with OverLap s -> badproc s
                                   )
      | PMatch (e,pms)          -> let re, usede = resources_of_expr state env e in
                                   List.fold_left ResourceSet.union usede (rck_pats false rck_proc state env re pms)
      | GSum gs                 -> let rg (iostep, proc) =
                                      match iostep.inst with 
                                      | Read (ce,params)  -> let _, used = resources_of_expr state env ce in
                                                             let state, extras = resource_of_params state params in
                                                             let env = List.fold_left (<@+>) env extras in
                                                             ResourceSet.union (rp state env proc) used
                                      | Write (ce,es)     -> (try let _, used = resources_of_expr state env ce in
                                                                  let rers = List.map (resources_of_expr state env) es in
                                                                  (* if it's a channel of qbit, then it sends away a qbit *)
                                                                  let state = 
                                                                    match (type_of_expr ce).inst, es, rers with
                                                                    | Channel {inst=Qbit}, [e], [r,rs] ->
                                                                        (match r with
                                                                         | RQbit q   -> State.add q false state
                                                                         | _         ->
                                                                            raise (ResourceError (e.pos,
                                                                                                  "ambiguous qbit-sending expression"
                                                                                                 )
                                                                                  )
                                                                        )
                                                                    | _                         -> state
                                                                  in
                                                                  let used = ResourceSet.union used (disju (List.map snd rers)) in
                                                                  ResourceSet.union (rp state env proc) used
                                                              with OverLap s -> badproc s
                                                             )
                                   in
                                   List.fold_left ResourceSet.union ResourceSet.empty (List.map rg gs)
      | Par ps                  -> (try let prs = List.map (rp state env) ps in
                                        disju prs
                                    with OverLap s -> badproc s
                                   )
      )
    in
    if !verbose || !verbose_resource then 
      Printf.printf "rp ... ... %s\n  => %s\n" (string_of_process proc) (ResourceSet.to_string r);
    r
  in
  rp state env proc
  
let rck_def env (Processdef(pn, params, proc)) = 
  let state, rparams = resource_of_params State.empty params in
  if !verbose || !verbose_resource then
    Printf.printf "\ndef %s params %s resource %s\n" 
                  (string_of_name pn.inst)
                  (bracketed_string_of_list string_of_param params)
                  (bracketed_string_of_list (string_of_pair string_of_name string_of_resource ":") rparams);
  (* here we go with the symbolic execution *)
  let _ = rck_proc state (List.fold_left (<@+>) env rparams) proc in
  ()

(* *************** main function: trigger the phases *************************** *)
let resourcecheck cxt defs = 
  (* the typecxt comes from typecheck. defs have been rewritten to mark exprs
     with their types.
     
     Let's police parameters: channels take either a single qbit or a classical value. Functions and
     applications must have nothing to do with qbits.
   *)
  
  if !verbose || !verbose_resource then Printf.printf "about to ctfa\n";
  List.iter ctfa_def defs;
  
  if !verbose || !verbose_resource then Printf.printf "about to build sysenv\n";
  let knownassoc = 
    List.map (fun (n,t,_) -> let _, r = resource_of_type State.empty (Parseutils.parse_typestring t) in
                             n, r
             ) 
             !Interpret.knowns 
  in
  let env = NameMap.of_assoc knownassoc in
  let env = if env <@?> "dispose" then env else env <@+> ("dispose",RNull) in

  if !verbose || !verbose_resource then Printf.printf "about to rck\n";
  List.iter (rck_def env) defs