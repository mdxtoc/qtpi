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
   
   Channels take either a single qbit or a classical value. This is a simplification of
   the language, and seems to suit the needs of clear description of quantum protocols. 
   
   Function applications must not deliver a qbit, or a value containing a qbit. 
   
   Functional values may not have free variables which are a qbit or a value containing
   a qbit. That's hard to assess during typechecking (or at least, the error messages
   make sense if we delay the check until now).
   
   This is all done with a symbolic execution, which made sense when I was trying to do
   resource-checking without syntactic restrictions. Now, perhaps, it's overkill, but
   it seems to work.
   
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
open Def
open Process
open Step
open Pattern

exception Error of sourcepos * string
exception Disaster of sourcepos * string

let rec is_resource_type t =
  match t.inst with
  | Qbit            -> true            
  | Unit          
  | Num 
  | Bool
  | Char
  | String
  | Bit 
  | Basisv
  | Gate            -> false
  | Qstate          -> false    (* really *)
  (* | Range   _ *)
  | Unknown (_, {contents=Some t})    
                    -> is_resource_type t       
  | Unknown (n, _)  -> let k = kind_of_unknown n in
                       k=UnkAll || k=UnkComm      
  | Known   n          (* can happen in Poly ... *)       
                    -> let k = kind_of_unknown n in
                       k=UnkAll || k=UnkComm
  | Poly    (ns, t) -> is_resource_type t 
  | OneOf   ((_, {contents=Some t}), _) -> is_resource_type t 
  | OneOf   (_, ts) -> List.exists is_resource_type ts
  | List    t       -> is_resource_type t 
  | Channel t       -> false
  | Tuple   ts      -> List.exists is_resource_type ts
  | Fun     (t1,t2) -> false (* yes *)
                     
  | Process _       -> false

let type_of_pattern p =
  match !(p.inst.ptype) with
  | Some t -> t
  | None   -> raise (Disaster (p.pos, Printf.sprintf "typecheck didn't mark pattern %s"
                                                     (string_of_pattern p)
                              )
                    )
  
(* *************** phase 1: resource check (rck_...) *************************** *)

(* with the new restrictions on process arguments, qbit-valued conditionals, bindings, 
   all this can be done _very_ simply. And will be done, when I get round to it.
 *)
 
(* by which I think I mean: an expression is classical if it uses no resource *)

(* odd, this: we have a resourceid which is null. But I can't see how to get rid of it ... *)
(* actually it would need to go over to options. But, in effect, this is a kind of option type. Sigh. *)
 
type resource =
  | RNull
  | RQbit of resourceid                
  | RTuple of resource list
  | RList of resourceid             (* for stuff that hasn't been taken apart *)
  | RCons of resource * resource    (* using RNull at the end of the list ... *)
  | RMaybe of resource list         (* for dealing with conditional and match expressions, sigh ... *)

and resourceid = sourcepos * string

type env = resource NameMap.t

let rec string_of_resource r =
  match r with
  | RNull               -> "RNull"
  | RQbit  rid          -> Printf.sprintf "RQbit %s" (string_of_resourceid rid)
  | RTuple rs           -> Printf.sprintf "RTuple (%s)" (string_of_list string_of_resource "*" rs)
  | RList  rid          -> Printf.sprintf "RList %s" (string_of_resourceid rid)
  | RCons  (rh,rt)      -> Printf.sprintf "RCons (%s,%s)" (string_of_resource rh) (string_of_resource rt)
  | RMaybe rs           -> Printf.sprintf "RMaybe %s" (bracketed_string_of_list string_of_resource rs)

and string_of_resourceid (spos, s) =
  Printf.sprintf "%s:%s" (short_string_of_sourcepos spos) s

let extendid (spos, s) s1 = spos, s^"."^s1

module OrderedResource = struct type t = resource let compare = Stdlib.compare let to_string = string_of_resource end
module ResourceSet = MySet.Make(OrderedResource)  

module OrderedRid = struct type t = resourceid let compare=Stdlib.compare let to_string=string_of_resourceid end
module State = MyMap.Make(OrderedRid) (* to tell if qbits have been sent away *)

let string_of_state = State.to_string string_of_bool
let string_of_env = NameMap.to_string string_of_resource

let (<@>)  env n     = try NameMap.find n env 
                       with Not_found -> raise (Error (dummy_spos, Printf.sprintf "looking for %s in %s"
                                                                                  (string_of_name n)
                                                                                  (string_of_env env)
                                                      )
                                               )      
let (<@+>) env (n,r) = NameMap.add n r env      
let (<@->) env n     = try NameMap.remove n env 
                       with Not_found -> raise (Error (dummy_spos, Printf.sprintf "removing %s from %s"
                                                                                  (string_of_name n)
                                                                                  (string_of_env env)
                                                      )
                                               )
let (<@?>) env n     = NameMap.mem n env 

(* option version of binding *)
let (<@@>) env n = try Some (NameMap.find n env) with _ -> None        

(* use: what a (qbit in an) expression is used for *)

type use =
  | URead       (* e.g. argument *)
  | UGate       
  | USend  
  | UMeasure
  | UPass       (* as argument in process invocation *)

let string_of_use = function
  | URead       -> "URead"       
  | UGate       -> "UGate"       
  | USend       -> "USend"       
  | UMeasure    -> "UMeasure"
  | UPass       -> "UPass"

(* qstop: things you _can't_ do with a qbit *)  

type qstop =
  | StopNowt
  | StopAllButRead
  | StopKill
  | StopUse

let string_of_qstop = function
  | StopKill       -> "StopKill"
  | StopUse        -> "StopUse"
  | StopAllButRead -> "StopAllButRead"
  | StopNowt       -> "StopNowt"

(* we stop qbit operations by attaching a qstop to an environment *)
(* stoppers are lists of (env,qstop) pairs: successive environments should be distinct.
   This enables us to control use of free qbits.
   
   We can stop all use of qbits in an environment with the stopper [(env,StopUse)] 
 *)

let string_of_stoppers = 
  bracketed_string_of_list (string_of_pair string_of_env string_of_qstop ",")
                           
let oktouse stoppers n res use =
  let police = function
    | StopKill       -> not (use=USend || (use=UMeasure && !measuredestroys) || use=UPass)
    | StopAllButRead -> use=URead
    | StopUse        -> false      (* you can't do it *)
    | StopNowt       -> true       (* you can do it *)
  in
  let rec findlevel stoppers =
    match stoppers with 
    | (env,stop)::((outer,_)::_ as more) ->
        if outer<@@>n = Some res    then findlevel more (* it's not mine *)
        else if env<@@>n = Some res then police stop    (* it's mine *)
                                    else true           (* it was yours all the time *)
    | [(env,stop)]                       ->
        if env<@@>n = Some res then police stop     (* it's mine *)
                               else true            (* it was yours all the time *)
    | []                                  ->
        true
  in
  findlevel stoppers

let nouseqbits env = [(env,StopUse)]

(* resource-checking, here we go *)                                

let newqid rid state = 
  let q = rid in
  State.add q true state, q
  
let rec resource_of_type rid state t = (* makes new resource: for use in parameter bindings *)
  if !verbose then
    Printf.printf "resource_of_type %s %s %s\n" (string_of_resourceid rid) (string_of_state state) (string_of_type t);
  match t.inst with
  | Num
  | Bool
  | Char
  | String
  | Bit 
  | Unit  
  | Basisv         
  (* | Range _ *)
  | Gate            
  | Qstate          -> state, RNull
  | Qbit            -> let state, q = newqid rid state in state, RQbit q
  | Unknown _       
  | Known   _       -> state, RNull  
  | Poly _          -> state, RNull  
  | OneOf (_, ts)   -> let srs = List.map (resource_of_type rid state) ts in
                       if List.exists (fun (_,r) -> r<>RNull) srs then
                         raise (Disaster (t.pos, "resource checker sees type " ^ string_of_type t))
                       else state, RNull
  | List t          -> let _, r = resource_of_type rid state t in
                       state, (if r=RNull then RNull else RList rid)
  | Tuple ts        -> let subrt (i,state,rs) t = 
                         let rid = extendid rid (string_of_int i) in
                         let state,r = resource_of_type rid state t in
                         (i+1,state,r::rs)
                       in
                       let _, state, rs = List.fold_left subrt (0,state,[]) ts in
                       if List.for_all (function RNull -> true | _ -> false) rs
                       then state, RNull
                       else state, RTuple (List.rev rs) 
  | Channel _       
  | Fun     _ 
  | Process _       -> state, RNull

exception OverLap of string

let rsingleton = function 
  | RNull -> ResourceSet.empty
  | r     -> ResourceSet.singleton r
  
let runion disjoint rset1 rset2 =
  let purge set =  if ResourceSet.mem RNull set then 
                     Printf.printf "** tell Richard ** runion saw %s\n" (ResourceSet.to_string set);
                   ResourceSet.remove RNull set
  in
  let rset1 = purge rset1 in
  let rset2 = purge rset2 in
  if disjoint && not (ResourceSet.is_empty (ResourceSet.inter rset1 rset2))
    then raise (OverLap (Printf.sprintf "non-disjoint resources (%s) and (%s)" 
                                        (ResourceSet.to_string rset1)
                                        (ResourceSet.to_string rset2)
                        )
               )
    else ResourceSet.union rset1 rset2

let runbind = ResourceSet.remove 
let runbind2 r (a,u) = a, runbind r u

let rec resources_of_resource disjoint r =
  let bad () = raise (OverLap (Printf.sprintf "non-disjoint resource %s" 
                                              (string_of_resource r)
                              )
                     )
  in
  match r with
  | RNull           -> ResourceSet.empty
  | RQbit _         -> rsingleton r                
  | RTuple rs       -> let rsets = List.map (resources_of_resource disjoint) rs in
                       (try List.fold_left (runion disjoint) ResourceSet.empty rsets 
                        with OverLap _ -> bad()
                       )
  | RList _         -> rsingleton r
  | RCons  (r1,r2)  -> let rset1 = resources_of_resource disjoint r1 in
                       let rset2 = resources_of_resource disjoint r2 in
                       (try runion disjoint rset1 rset2 with OverLap _ -> bad ()) 
  | RMaybe rs       -> let rsets = List.map (resources_of_resource disjoint) rs in
                       List.fold_left ResourceSet.union ResourceSet.empty rsets (* not runion -- yes *)
  
(* and in what follows *)

let disju = List.fold_left (runion true) ResourceSet.empty

(* rck_pat can be given a resource (Some res) or rely on types. In the latter case, which
   arises only in Read steps, we don't have to consider more than the range of patterns 
   that can arise in bpats -- names, underscores and tuples.
   
   To handle resource accounting properly, rck_pat must remove resource bindings it creates from 
   the resource set it returns.
 *)
 
let rec rck_pat contn unbind state env stoppers pat resopt =
  let bad () = raise (Disaster (pat.pos, Printf.sprintf "pattern %s resource %s"
                                                        (string_of_pattern pat)
                                                        (string_of_option string_of_resource resopt)
                               )
                )
  in
  if !verbose then 
    Printf.printf "rck_pat %s %s %s %s %s\n" (string_of_state state)
                                             (string_of_env env)
                                             (string_of_stoppers stoppers)
                                             (string_of_pattern pat)
                                             (string_of_option string_of_resource resopt);
  match pat.inst.pnode with
  | PatAny    
  | PatUnit   
  | PatNil
  | PatInt    _ 
  | PatBit    _
  | PatBool   _
  | PatChar   _
  | PatString _
  | PatBasisv _       -> contn state env stoppers (* no resources here *)
  | PatName   n       -> let state, res = match resopt with
                           | Some res -> state, res
                           | None     -> resource_of_type (pat.pos,n) state (type_of_pattern pat) 
                         in
                         unbind res (contn state (env<@+>(n,res)) stoppers)
  | PatCons   (ph,pt) -> let docons contn state env stoppers rh rt =
                           let tl state env stoppers = rck_pat contn unbind state env stoppers pt (Some rt) in
                           rck_pat tl unbind state env stoppers ph (Some rh)
                         in
                         (match (_The resopt) with (* this pattern is not in bpat *)
                          | RNull         -> docons contn state env stoppers RNull RNull
                          | RCons (rh,rt) -> docons contn state env stoppers rh rt
                          | RList rid     -> let state, rh = resource_of_type (extendid rid "hd") state (type_of_pattern ph) in
                                             let rt = RList (extendid rid "tl") in
                                             docons contn state env stoppers rh rt
                          | _             -> bad ()
                         )
  | PatTuple ps       -> let rec rck state env stoppers = function
                           | (p,r)::prs -> rck_pat (fun state env stoppers -> rck state env stoppers prs) unbind state env stoppers p r
                           | []         -> contn state env stoppers
                         in
                         (match resopt with
                          | Some RNull       -> rck state env stoppers (List.map (fun p -> p,Some RNull) ps)
                          | Some (RTuple rs) -> let rs = List.map _Some rs in rck state env stoppers (zip ps rs)
                          | None             -> rck state env stoppers (List.map (fun p -> p,None) ps)
                          | _                -> bad ()
                         )

and rck_pats rck unbind state env stoppers reopt pxs =
  let rck_px (pat,x) = rck_pat (fun state env stoppers -> rck state env stoppers x) unbind state env stoppers pat reopt in
  List.map rck_px pxs
    
;; (* to give rck_pat and rck_pats a polytype *)

let rec r_o_e disjoint use state env stoppers (e:Expr.expr) =
  let rec re_env use env stoppers (e:Expr.expr) =
    let rec re use (e:Expr.expr) =
      let do_list use es = List.fold_right (fun e (rs, set) -> let r, used = re use e in
                                                               r::rs, ResourceSet.union set used (* not runion - yes *)
                                           )
                                           es
                                           ([],ResourceSet.empty) 
      in
      let try_disjoint r =
        try let _ = resources_of_resource disjoint r in r
        with OverLap _ -> raise (Error (e.pos,  Printf.sprintf "non-separated expression %s"
                                                               (string_of_expr e)
                                       )
                                )
      in
      match e.inst.enode with
      | EUnit 
      | ENil
      | ENum        _              
      | EBool       _
      | EChar       _
      | EString     _
      | EBit        _         
      | EBasisv     _         -> RNull, ResourceSet.empty
      | EMinus      e         
      | ENot        e         -> re use e
      | EArith      (e1,_,e2) 
      | ECompare    (e1,_,e2) 
      | EBoolArith  (e1,_,e2) -> let rs, used = do_list URead [e1;e2] in 
                                 if List.exists (fun r -> r<>RNull) rs then
                                   raise (Error (e.pos, "cannot manipulate qbits with arith/compare/bool expressions"));
                                 RNull, used
      | EVar        n         -> let r = env <@> n in
                                  (match r with
                                  | RNull   -> RNull, ResourceSet.empty
                                  | RQbit q -> if not (oktouse stoppers n r use) then
                                                 raise (Error (e.pos, Printf.sprintf "cannot %s free qbit %s"
                                                                                      (match use with 
                                                                                       | URead      -> "use"
                                                                                       | UGate      -> "gate"
                                                                                       | USend      -> "send"
                                                                                       | UMeasure   -> "measure"
                                                                                       | UPass      -> "pass (as process argument)"
                                                                                      )
                                                                                      (string_of_name n)
                                                              )
                                                        )
                                               else
                                               if State.find q state then r, rsingleton r
                                               else
                                                 raise (Error (e.pos, Printf.sprintf "use of sent-away%s qbit %s" 
                                                                                     (if !measuredestroys then "/measured" else "")
                                                                                     (string_of_name n)
                                                              )
                                                       )
                                  | _       -> r, resources_of_resource disjoint r
                                 )
      | ETuple      es        -> let rs, used = do_list use es in
                                 if List.for_all (function RNull -> true | _ -> false) rs 
                                 then RNull, used
                                 else try_disjoint (RTuple rs), used
      | ECons       (hd,tl)   -> let r1, u1 = re use hd in
                                 let r2, u2 = re use tl in
                                 (match r1, r2 with
                                  | RNull, _        (* if the hd has no resource, neither can the list (either it has qbit or it doesn't)*)
                                  | _    , RNull -> (* likewise the tail *)
                                                    RNull
                                  | _            -> try_disjoint (RCons (r1,r2))
                                 ),
                                 ResourceSet.union u1 u2
      | EMatch      (e,ems)   -> let re, usede = re URead e in
                                 let rus = rck_pats (fun _ env stoppers -> re_env use env stoppers) runbind2 state env stoppers (Some re) ems in
                                 let rs, useds = unzip rus in
                                 (match List.filter (function RNull -> false | _ -> true) rs with
                                  | []  -> RNull
                                  | [r] -> r 
                                  | rs  -> RMaybe rs
                                 ),
                                 List.fold_left ResourceSet.union usede useds
      | ECond       (ce,e1,e2)-> let _ , used0 = re URead ce in
                                 let r1, used1 = re use e1 in
                                 let r2, used2 = re use e2 in
                                 (match r1, r2 with
                                  | RNull, _      -> r2
                                  | _    , RNull  -> r1
                                  | _             -> if r1=r2 then r1 else RMaybe [r1;r2]
                                 ),
                                 ResourceSet.union used0 (ResourceSet.union used1 used2)
      | EApp        (e1,e2)   
      | EAppend     (e1,e2)   -> let _, used1 = re URead e1 in
                                 let _, used2 = re URead e2 in
                                 (* EAppend and EApp don't return resources: we checked *)
                                 RNull, ResourceSet.union used1 used2
      | ELambda     (pats,e)  -> rck_fun state env pats e
      | EWhere      (e,ed)    -> rck_edecl use state env stoppers e ed
            
    
    and rck_edecl use state env stoppers e ed = 
      match ed.inst with
      | EDPat (wpat,_,we)        -> let wr, wused = re use we in
                                    let r, used = rck_pat (fun state env stoppers -> resources_of_expr use state env stoppers e) 
                                                          runbind2 state env stoppers wpat (Some wr) 
                                    in
                                    r, ResourceSet.union used wused
      | EDFun (wfn,wfpats,_, we) -> let env = env <@+> (wfn.inst,RNull) in (* functions aren't resource *)
                                    let wr, wused = rck_fun state env wfpats we in
                                    let r, used = resources_of_expr use state env stoppers e in
                                    r, ResourceSet.union used wused

    in re use e
  in
  re_env use env stoppers e
  
and rck_fun state env pats expr = (* note: no stoppers *)
  let stoppers = nouseqbits env in
  (* this works because we only have bpats as params *)
  let pos = pos_of_instances pats in
  rck_pat (fun state env stoppers -> resources_of_expr URead state env stoppers expr) runbind2 
          state env stoppers 
          (adorn pos (pwrap None (PatTuple pats))) (* not in the tree, so nobody should notice *)
          None
  
and resources_of_expr use = r_o_e false use
and disjoint_resources_of_expr use = r_o_e true use

and resource_of_params state params = 
  List.fold_right (fun param (state, nrs) ->
                     let n, toptr = param.inst in
                     let state, r = resource_of_type (param.pos,n) state (_The !toptr) in
                     state, (n,r)::nrs 
                  ) 
                  params
                  (state,[])

and rck_proc mon state env stoppers proc = 
  let badproc s =
    raise (Error (proc.pos, Printf.sprintf "checking %s: %s"
                                           (short_string_of_process proc)
                                           s
                 )
          )
  in
  let rec rp state env stoppers proc =
    if !verbose then 
      Printf.printf "rp %s %s %s %s\n" (string_of_env env)
                                       (string_of_state state)
                                       (string_of_stoppers stoppers)
                                       (short_string_of_process proc);
    let r =
      match proc.inst with
      | Terminate               -> ResourceSet.empty
      | GoOnAs (n, es, mes)       -> (* disjoint resources in the arguments, no dead qbits used *)
                                   let ers = List.map (snd <.> disjoint_resources_of_expr UPass state env stoppers) (es@mes) in
                                   (try disju ers with OverLap s -> badproc s)
      | WithNew (params, proc)  -> (* all channels, no new resource, nothing used *)
                                   let env = List.fold_left (fun env {inst=n,_} -> env <@+> (n,RNull)) env params in
                                   rp state env stoppers proc
      | WithQbit (qspecs, proc) -> (* all new qbits *)
                                   let do_qspec (qs, used, state, env) (param, eopt) =
                                     let _, usede = match eopt with
                                                    | Some e -> resources_of_expr URead state env stoppers e
                                                    | None   -> RNull, ResourceSet.empty
                                     in
                                     let n, _ = param.inst in
                                     let state, q = newqid (param.pos,n) state in
                                     RQbit q::qs, ResourceSet.union used usede, state, env <@+> (n,RQbit q)
                                   in
                                   let qs, used, state, env = 
                                     List.fold_left do_qspec ([], ResourceSet.empty, state, env) qspecs 
                                   in
                                   List.fold_left (revargs runbind) (ResourceSet.union used (rp state env stoppers proc)) qs
      | WithLet (letspec, proc) -> (* whatever resource the expression gives us *)
                                   let pat, e = letspec in
                                   let re, usede = resources_of_expr URead state env stoppers e in 
                                   let used = rck_pat (fun state env stoppers -> rp state env stoppers proc) 
                                                      runbind state env stoppers pat (Some re) 
                                   in
                                   (* rck_pat does the runbinding *)
                                   ResourceSet.union used usede
      | WithQstep (qstep,proc)  -> (match qstep.inst with 
                                    | Measure (qe, gopt, pattern) -> 
                                        let destroys = !measuredestroys in
                                        (* if destroys is false then qe can be ambiguously conditional *)
                                        let rq, usedq = (if destroys then disjoint_resources_of_expr else resources_of_expr) 
                                                            UMeasure state env stoppers qe 
                                        in
                                        let usedg = ((snd <.> resources_of_expr URead state env stoppers) ||~~ ResourceSet.empty) gopt in
                                        let env' = match pattern.inst.pnode with
                                                   | PatAny    -> env
                                                   | PatName n -> env <@+> (n,RNull)
                                                   | _         -> raise (Disaster (qstep.pos, string_of_qstep qstep))
                                        in
                                        let state = 
                                          match destroys, rq with
                                          | false, _       -> state
                                          | true , RQbit q -> State.add q false state
                                          | true , _       -> (* belt and braces ... *)
                                              raise (Error (qe.pos, "ambiguous qbit expression (which qbit is destroyed?)"))
                                        in
                                        ResourceSet.union usedq (ResourceSet.union usedg (rp state env' stoppers proc))
                                    | Ugatestep (qes, ug)    -> 
                                        let qers = List.map (snd <.> resources_of_expr UGate state env stoppers) qes in
                                        (try let used = disju qers in
                                             ResourceSet.union (rp state env stoppers proc) used
                                         with OverLap s -> badproc s
                                        )
                                   )
      | Iter (params, p, e, proc)                 
                                -> let state', rparams = resource_of_params state params in
                                   let pused = rp state' (List.fold_left (<@+>) env rparams) ((env,StopKill)::stoppers) p in
                                   let _, eused = resources_of_expr URead state env stoppers e in
                                   List.fold_left ResourceSet.union pused [eused; rp state env stoppers proc]
      | TestPoint (n, proc)     -> (match find_monel n.inst mon with
                                    | Some (_,monproc) -> ResourceSet.union (rp state env [(env, StopAllButRead)] monproc) 
                                                                            (rp state env stoppers proc)
                                    | None             -> raise (Can'tHappen (Printf.sprintf "%s: rck sees no monproc"
                                                                                               (string_of_sourcepos n.pos)
                                                                             )
                                                                )
                                   )
      | Cond (ce,p1,p2)         -> let _, used = resources_of_expr URead state env stoppers ce in
                                   let prs = List.map (rp state env stoppers) [p1;p2] in
                                   List.fold_left ResourceSet.union used prs (* NOT disju, silly boy! *)
      | PMatch (e,pms)          -> let re, usede = resources_of_expr URead state env stoppers e in
                                   List.fold_left ResourceSet.union usede (rck_pats (rck_proc mon) runbind state env stoppers (Some re) pms)
      | GSum gs                 -> 
          let rg (iostep, proc) =
            match iostep.inst with 
            | Read (ce,pat)  -> let _, usedce = resources_of_expr URead state env stoppers ce in
                                let used = rck_pat (fun state env stoppers -> rp state env stoppers proc) 
                                                   runbind state env stoppers pat None 
                                in
                                ResourceSet.union usedce used
            | Write (ce,e)   -> (try let _, usedce = resources_of_expr URead state env stoppers ce in
                                     let r, usede = disjoint_resources_of_expr USend state env stoppers e in
                                     (* if it's a channel of qbit, then it sends away a qbit *)
                                     let state = 
                                       match (type_of_expr ce).inst with
                                       | Channel {inst=Qbit} ->
                                           (match r with
                                            | RQbit q   -> State.add q false state
                                            | _         ->
                                               raise (Error (e.pos, "ambiguous qbit expression (which qbit is sent?)"))
                                           )
                                       | _              -> state
                                     in
                                     List.fold_left ResourceSet.union ResourceSet.empty [usedce; usede; rp state env stoppers proc]
                                 with OverLap s -> badproc s
                                )
         in
         List.fold_left ResourceSet.union ResourceSet.empty (List.map rg gs)
      | Par ps                  -> (try let prs = List.map (rp state env stoppers) ps in
                                        disju prs
                                    with OverLap s -> badproc s
                                   )
    in
    if !verbose then 
      Printf.printf "rp ... ... %s\n  => %s\n" (string_of_process proc) (ResourceSet.to_string r);
    r
  in
  rp state env stoppers proc
  
let rck_def env def =
  if !verbose then 
    Printf.printf "\nrck_def %s %s\n"
                  (string_of_env env)
                  (string_of_def def);
  match def with
  | Processdefs pdefs -> 
      let rck_pdef (pn, params, proc, monparams, mon) =
        let state, rparams = resource_of_params State.empty (params@monparams) in
        if !verbose then
          Printf.printf "\ndef %s params %s resource %s\n" 
                        (string_of_name pn.inst)
                        (bracketed_string_of_list string_of_param params)
                        (bracketed_string_of_list (string_of_pair string_of_name string_of_resource ":") rparams);
        (* here we go with the symbolic execution *)
        ignore (rck_proc mon state (List.fold_left (<@+>) env rparams) [] proc) 
      in
      List.iter rck_pdef pdefs
  | Functiondefs fdefs ->
      let rck_fdef (fn, pats, _, expr) = ignore (rck_fun State.empty env pats expr) in
      List.iter rck_fdef fdefs
  | Letdef (pat,e) -> () (* I think so: the typechecker has done the work *)
      
(* *************** phase 1: function free variables (ffv_...) *************************** *)

(* delayed until this point in the hope of better error messages *)

module OrderedNE = struct type t = name*expr 
                          let compare = Stdlib.compare 
                          let to_string = bracketed_string_of_pair string_of_name (fun e -> string_of_sourcepos (e.pos)) 
                   end
module NESet = MySet.Make(OrderedNE)

let ne_filter nset s = NESet.filter (fun (n,_) -> not (NameSet.mem n nset)) s

let frees = Expr.frees_fun ne_filter
                           (fun n e s -> NESet.add (n, e) s)
                           NESet.union
                           NESet.empty

let rec ffv_expr expr =
  match expr.inst.enode with
  | EUnit
  | EVar       _
  | ENum       _
  | EBool      _
  | EChar      _
  | EString    _
  | EBit       _
  | EBasisv    _
  | ENil                    -> ()
  | EMinus     e
  | ENot       e            -> ffv_expr e
  | ETuple     es           -> List.iter ffv_expr es  
  | ECons      (e1,e2)
  | EAppend    (e1,e2)
  | EApp       (e1,e2)      -> List.iter ffv_expr [e1;e2]
  | ECond      (e1,e2,e3)   -> List.iter ffv_expr [e1;e2;e3]
  | EMatch     (e,ems)      -> ffv_expr e; List.iter (fun (pat,e) -> ffv_expr e) ems
  | EArith     (e1, _, e2)
  | ECompare   (e1, _, e2)
  | EBoolArith (e1, _, e2)  -> List.iter ffv_expr [e1;e2]
  | ELambda    (pats, e)    -> ffv_fundef expr.pos None pats e
  | EWhere     (e, edecl)   -> (match edecl.inst with
                                | EDPat (pat, _, e)      -> ffv_expr e;
                                | EDFun (fn, pats, _, e) -> ffv_fundef edecl.pos (Some fn) pats e 
                               );
                               ffv_expr e

and ffv_fundef pos fnopt pats e =
  (* now actually we can ignore pats and fn, because both are classical anyway, but to
     keep sane, let's do this right
   *)
  let veset = frees e in
  let veset = ne_filter (names_of_pats pats) veset in
  let veset = match fnopt with
              | None -> veset
              | Some fn -> ne_filter (NameSet.singleton fn.inst) veset
  in
  let bad_veset = NESet.filter (fun (n,e) -> is_resource_type (type_of_expr e)) veset in
  if not (NESet.is_empty bad_veset) then
    (let bad_v (n,e) = Printf.sprintf "%s:%s (at %s)"
                          (string_of_name n)
                          (string_of_type (type_of_expr e))
                          (string_of_sourcepos e.pos)
     in
     let ss = List.map bad_v (NESet.elements bad_veset) in
     raise (Error (pos, Printf.sprintf "function definition has non-classical free variable(s)\n    %s"
                                          (String.concat "\n    " ss)
                  )
           )
    );
  ffv_expr e

and ffv_proc mon proc =
  match proc.inst with
  | Terminate                      -> ()
  | GoOnAs      (pn,es,mes)          -> List.iter ffv_expr es; List.iter ffv_expr mes
  | WithNew   (params, proc)       -> ffv_proc mon proc
  | WithQbit  (qspecs, proc)       -> List.iter ffv_qspec qspecs; ffv_proc mon proc
  | WithLet   (letspec, proc)      -> ffv_letspec letspec; ffv_proc mon proc
  | WithQstep (qstep, proc)        -> ffv_qstep qstep; ffv_proc mon proc
  | TestPoint (n, proc)            -> (match find_monel n.inst mon with
                                       | Some (_,monproc) -> ffv_proc [] monproc; ffv_proc mon proc
                                       | None -> raise (Can'tHappen (string_of_sourcepos n.pos ^
                                                                     ": resourcecheck ffv can't find " ^ n.inst
                                                                    )
                                                       )
                                      )
  | Iter      (params, p, e, proc) -> ffv_proc mon p; ffv_expr e; ffv_proc mon proc
  | Cond      (expr, proc1, proc2) -> ffv_expr expr; ffv_proc mon proc1; ffv_proc mon proc2
  | PMatch    (expr, patprocs)     -> ffv_expr expr; List.iter ((ffv_proc mon) <.> snd) patprocs
  | GSum      ioprocs              -> List.iter (ffv_ioproc mon) ioprocs
  | Par       procs                -> List.iter (ffv_proc mon) procs

and ffv_qspec qspec =
  match qspec with
  | param, None      -> ()
  | param, Some expr -> ffv_expr expr

and ffv_letspec (pattern, expr) = ffv_expr expr

and ffv_qstep qstep =
  match qstep.inst with
  | Measure (expr, gopt, _)  -> ffv_expr expr; (ffv_expr ||~~ ()) gopt
  | Ugatestep (exprs, ge)    -> List.iter ffv_expr exprs; ffv_expr ge
  
and ffv_ioproc mon (iostep, proc) =
  (match iostep.inst with
   | Read (expr, pat)     -> ffv_expr expr
   | Write (expr1, expr2) -> ffv_expr expr1; ffv_expr expr2
  );
  ffv_proc mon proc
  
and ffv_def def =
  if !verbose then 
    Printf.printf "\nffv_def %s\n"
                  (string_of_def def);
  match def with
  | Processdefs  pdefs -> List.iter ffv_pdef pdefs
  | Functiondefs fdefs -> List.iter ffv_fdef fdefs
  | Letdef (pat,e)     -> ffv_expr e
  
and ffv_fdef (fn, pats, _, e) = ffv_fundef fn.pos (Some fn) pats e

and ffv_pdef (pn, _, proc, _, mon) = ffv_proc mon proc

(* *************** main function: trigger the phases *************************** *)

let resourcecheck defs = 
  (* defs have been rewritten to mark exprs with their types. I hope. *)
  
  push_verbose !verbose_resource (fun () ->  
    let knownassoc = 
      List.map (fun (n,t,_) -> let _, r = resource_of_type (dummy_spos, "library_"^n) State.empty (Parseutils.parse_typestring t) in
                               n, r
               ) 
               !Interpret.knowns 
    in
    let env = NameMap.of_assoc knownassoc in
    let do_def env def =
      match def with
      | Processdefs  pdefs      -> let do_pdef env (pn, _, _, _, _) = env <@+> (pn.inst,RNull) in
                                   List.fold_left do_pdef env pdefs
      | Functiondefs fdefs      -> let do_fdef env (fn, _, _, _) = env <@+> (fn.inst,RNull) in
                                   List.fold_left do_fdef env fdefs
      | Letdef       (pat,e)    -> let ns = NameSet.elements (names_of_pattern pat) in
                                   List.fold_left (fun env n -> env <@+> (n,RNull)) env ns
    in
    let env = List.fold_left do_def env defs in
    let add_std_channel env name =
      if env <@?> name then env else env <@+> (name,RNull)
    in
    let env = add_std_channel env "dispose" in
    let env = add_std_channel env "out"     in
    let env = add_std_channel env "outq"    in
    let env = add_std_channel env "in"      in

    List.iter (rck_def env) defs;
    
    (* and then we check function defs for non-classical free variables *)
    List.iter ffv_def defs
  )