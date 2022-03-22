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

(* Resources in quantum protocols are qubits. A qubit is owned by a single process.
   Resources are received in process invocations and in reads; they are transmitted
   in process calls and in sends.
   
   The parameters of a process definition name resources. Suppose those resources
   are non-overlapping. Then if the process body distributes those resources in a
   non-overlapping way -- if the tuple expressions in its sends are non-overlapping, if 
   tuples of arguments in its process calls are non-overlapping, if the tuples of parallel 
   processes are non-overlapping -- then we shall have correct resourcing.
   
   Provided, of course, we police the use of qubits that are sent away down channels.
   
   Channels take either a single qubit or a classical value. This is a simplification of
   the language, and seems to suit the needs of clear description of quantum protocols. 
   
   Function applications must not deliver a qubit, or a value containing a qubit. 
   
   Functional values may not have free variables which are a qubit or a value containing
   a qubit. That's hard to assess during typechecking (or at least, the error messages
   make sense if we delay the check until now).
   
   This is all done with a symbolic execution, which made sense when I was trying to do
   resource-checking without syntactic restrictions. Now, perhaps, it's overkill, but
   it seems to work.
   
   Good luck to us all.
   
   Annotated 03/2022: We treat qubit collections as single qubits for resource accounting. 
   This is fine most of the time, but it is inconvenient when gating: we really must allow,
   for example, qs↓0,qs↓1,ancs↓0>>T as a gating step. 
   
   I suspect I shall have to rework this mightily ...     
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
  | Qubit                       
  | Qubits              -> true            
  | Unit          
  | Num 
  | Bool
  | Char
  | Sxnum
  | Bit 
  | Bra
  | Ket
  | Gate            
  | Matrix              -> false
  | Qstate              -> false    (* really *)
  (* | Range   _ *)
  | Unknown (_, {contents=Some t})    
                        -> is_resource_type t       
  | Unknown ((_,k), _)  -> k=UnkAll || k=UnkComm      
  | Known   (_,k)          (* can happen in Poly ... *)       
                        -> k=UnkAll || k=UnkComm
  | Poly    (ns, t)     -> false (* if Fun is false, so is Poly *)
  | List    t           -> false (* 03/2022: classical lists *) 
  | Channel t           -> false
  | Tuple   ts          -> false (* 03/2022: classical tuples *)
  | Fun     (t1,t2)     -> false (* yes *)
                     
  | Process _           -> false

  
(* *************** phase 1: resource check (rck_...) *************************** *)

(* with the new restrictions on process arguments, qubit-valued conditionals, bindings, 
   all this can be done _very_ simply. And will be done, when I get round to it.
   (And is beginning to be done, in 03/2022. First step: no Cons, List or Tuple resources.
    But still left with Maybe. Hmm.
    
    But there doesn't seem much left of this thing now. And I was so proud of it ...
   )
 *)
 
(* this is a kind of option type. *) 
type resource =
  | RNull
  | RQubit of resourceid                
  | RMaybe of resource list         (* for dealing with conditional and match expressions, sigh ... *)

and resourceid = sourcepos * string * expr option (* expr is an index *)

type env = resource NameMap.t

let rec string_of_resource r =
  match r with
  | RNull               -> "RNull"
  | RQubit  rid         -> Printf.sprintf "RQubit %s" (string_of_resourceid rid)
  | RMaybe rs           -> Printf.sprintf "RMaybe %s" (bracketed_string_of_list string_of_resource rs)

and string_of_resourceid (spos, s, ix) =
  Printf.sprintf "%s:%s%s" (short_string_of_sourcepos spos) s (match ix with 
                                                               | Some e -> Printf.sprintf "↓(%s)" (string_of_expr e)
                                                               | None   -> ""
                                                              )

let extendid (spos, s, ix) s1 = (spos, s^"."^s1, ix)

module OrderedRid = struct type t = resourceid let compare = Stdlib.compare let to_string = string_of_resourceid end
module RidSet = MySet.Make(OrderedRid)  (* for used, because it's probably not always going to be just resourceids *)  
module State = MyMap.Make(OrderedRid)   (* to tell if qubits have been sent away *)

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

(* use: what a (qubit in an) expression is used for *)

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

(* qstop: things you _can't_ do with a qubit *)  

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

(* we stop qubit operations by attaching a qstop to an environment *)
(* stoppers are lists of (env,qstop) pairs: successive environments should be distinct.
   This enables us to control use of free qubits.
   
   We can stop all use of qubits in an environment with the stopper [(env,StopUse)] 
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
    | (env,stop)::more ->
        if env<@@>n = Some res then police stop && findlevel more   (* it's mine, but it might also be restricted more *)
                               else true                            (* it was yours all the time *)
    | []               -> true
  in
  findlevel stoppers

let nousequbits env = [(env,StopUse)]

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
  | Bit 
  | Unit 
  | Sxnum
  | Bra
  | Ket
  (* | Range _ *)
  | Gate      
  | Matrix
  | Qstate          -> state, RNull
  | Qubit               (* treat singleton qubit and qubit collection each as a single resource *)
  | Qubits           -> let state, q = newqid rid state in state, RQubit q
  | Unknown _       
  | Known   _         
  | Poly    _           
  | List    _          
  | Tuple   _         
  | Channel _       
  | Fun     _ 
  | Process _       -> state, RNull

exception OverLap of string

(* maybe not needed ...
   let rsingleton = function 
     | RNull           -> RidSet.empty
     | RMaybe rs       -> RidSet.singleton r
     | RQubit rid      -> RidSet.singleton rid
 *)
  
let runion disjoint rset1 rset2 =
  if disjoint && not (RidSet.is_empty (RidSet.inter rset1 rset2))
    then raise (OverLap (Printf.sprintf "non-disjoint resources (%s) and (%s)" 
                                        (RidSet.to_string rset1)
                                        (RidSet.to_string rset2)
                        )
               )
    else RidSet.union rset1 rset2

let rec runbind r u = 
  match r with 
  | RNull      -> u
  | RQubit rid -> RidSet.remove rid u
  | RMaybe rs  -> List.fold_left (Functionutils.revargs runbind) u rs
let runbind2 r (a,u) = a, runbind r u

let rec set_of_resource disjoint r =
  match r with
  | RNull           -> RidSet.empty
  | RQubit rid      -> RidSet.singleton rid                
  | RMaybe rs       -> let rsets = List.map (set_of_resource disjoint) rs in
                       List.fold_left RidSet.union RidSet.empty rsets (* not runion -- yes *)
  
(* and in what follows *)

let disju = List.fold_left (runion true) RidSet.empty

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
  match tinst pat with
  | PatAny    
  | PatUnit   
  | PatNil
  | PatInt    _ 
  | PatBit    _
  | PatBool   _
  | PatChar   _
  | PatString _
  | PatBra    _       
  | PatKet    _       -> contn state env stoppers (* no resources here *)
  | PatName   n       -> let state, res = match resopt with
                           | Some res -> state, res
                           | None     -> resource_of_type (pat.pos,n,None) state (type_of_pattern pat) 
                         in
                         unbind res (contn state (env<@+>(n,res)) stoppers)
  | PatCons   (ph,pt) -> let docons contn state env stoppers rh rt =
                           let tl state env stoppers = rck_pat contn unbind state env stoppers pt (Some rt) in
                           rck_pat tl unbind state env stoppers ph (Some rh)
                         in
                         (match (_The resopt) with (* this pattern is not in bpat *)
                          | RNull         -> docons contn state env stoppers RNull RNull (* trust the typechecker: it's got to be RNull *)
                          | _             -> bad ()
                         )
  | PatTuple ps       -> let rec rck state env stoppers = function
                           | (p,r)::prs -> rck_pat (fun state env stoppers -> rck state env stoppers prs) unbind state env stoppers p r
                           | []         -> contn state env stoppers
                         in
                         (match resopt with
                          | Some RNull       -> rck state env stoppers (List.map (fun p -> p,Some RNull) ps)
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
                                                               r::rs, RidSet.union set used (* not runion - yes *)
                                           )
                                           es
                                           ([],RidSet.empty) 
      in
      match tinst e with
      | EUnit 
      | ENil
      | ERes        _
      | ENum        _              
      | EBool       _
      | EChar       _
      | EString     _
      | EBit        _         
      | EBra        _
      | EKet        _         -> RNull, RidSet.empty
      | EMinus      e         
      | ENot        e         
      | EDagger     e         -> re use e
      | EArith      (e1,_,e2) 
      | ECompare    (e1,_,e2) 
      | EBoolArith  (e1,_,e2) -> let rs, used = do_list URead [e1;e2] in 
                                 if List.exists (fun r -> r<>RNull) rs then
                                   raise (Error (e.pos, "cannot manipulate qubits with arith/compare/bool expressions"));
                                 RNull, used
      | EVar        n         -> let r = env <@> n in
                                 (match r with
                                  | RNull    -> RNull, RidSet.empty
                                  | RQubit q -> resources_of_q e.pos use state stoppers r (type_of_expr e) n q
                                  | _        -> r, set_of_resource disjoint r
                                 )
      | ETuple      es        -> let rs, used = do_list use es in
                                 if List.for_all (function RNull -> true | _ -> false) rs 
                                 then RNull, used
                                 else raise (Disaster (e.pos, "tuple with qubit resource"))
      | ECons       (hd,tl)   -> let r1, u1 = re use hd in
                                 let r2, u2 = re use tl in
                                 (match r1, r2 with
                                  | RNull, RNull -> RNull
                                  | _            -> raise (Disaster (e.pos, "ECons with qubit resource"))
                                 ),
                                 RidSet.union u1 u2
      | EMatch      (e,ems)   -> let re, usede = re URead e in
                                 let rus = rck_pats (fun _ env stoppers -> re_env use env stoppers) runbind2 state env stoppers (Some re) ems in
                                 let rs, useds = unzip rus in
                                 (match List.filter (function RNull -> false | _ -> true) rs with
                                  | []  -> RNull
                                  | [r] -> r 
                                  | rs  -> RMaybe rs
                                 ),
                                 List.fold_left RidSet.union usede useds
      | ECond       (ce,e1,e2)-> let _ , used0 = re URead ce in
                                 let r1, used1 = re use e1 in
                                 let r2, used2 = re use e2 in
                                 (match r1, r2 with
                                  | RNull, _      -> r2
                                  | _    , RNull  -> r1
                                  | _             -> if r1=r2 then r1 else RMaybe [r1;r2]
                                 ),
                                 ResourceSet.union used0 (ResourceSet.union used1 used2)
      | ESub        (e1,e2)   -> if use=UMeasure then
                                   raise (Error (e.pos, "measuring element of collection"));
                                 (* at present this is qubits -> num -> qubit, so e2 had better be RNull *)
                                 let r1, used1 = re URead e1 in
                                 let r2, used2 = re URead e2 in
                                 (match r2 with
                                  | RNull -> r1, ResourceSet.union used1 used2
                                  | _     -> raise (Disaster (e2.pos, Printf.sprintf "%s is resource %s" 
                                                                                     (string_of_expr e2) 
                                                                                     (string_of_resource r2)
                                                             )
                                                   )
                                 )
      | EJux        (e1,e2)   
      | EAppend     (e1,e2)   -> let _, used1 = re URead e1 in
                                 let _, used2 = re URead e2 in
                                 (* EAppend and EJux don't return resources: we checked *)
                                 RNull, ResourceSet.union used1 used2
      | ELambda     (pats,e)  -> rck_fun state env pats e
      | EWhere      (e,ed)    -> rck_edecl use state env stoppers e ed
            
    
    and rck_edecl use state env stoppers e ed = 
      match ed.inst with
      | EDPat (wpat,_,we)        -> let wr, wused = re use we in
                                    let r, used = rck_pat (fun state env stoppers -> resources_of_expr use state env stoppers e) 
                                                          runbind2 state env stoppers wpat (Some wr) 
                                    in
                                    r, RidSet.union used wused
      | EDFun (wfn,wfpats,_, we) -> let env = env <@+> (tinst wfn,RNull) in (* functions aren't resource *)
                                    let wr, wused = rck_fun state env wfpats we in
                                    let r, used = resources_of_expr use state env stoppers e in
                                    r, RidSet.union used wused

    in re use e
  in
  re_env use env stoppers e
  
and rck_fun state env pats expr = (* note: no stoppers *)
  let stoppers = nousequbits env in
  (* this works because we only have bpats as params *)
  let pos = pos_of_instances pats in
  rck_pat (fun state env stoppers -> resources_of_expr URead state env stoppers expr) runbind2 
          state env stoppers 
          (adorn pos (twrap None (PatTuple pats))) (* not in the tree, so nobody should notice *)
          None
  
and resources_of_expr use = r_o_e false use
and disjoint_resources_of_expr use = r_o_e true use

and resources_of_q pos use state stoppers r t n q =
  if not (oktouse stoppers n r use) then
    raise (Error (pos, Printf.sprintf "cannot %s free qubit %s"
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
  if State.find q state then r, set_of_resource false r (* I _think_ non-disjoint is correct here ... *)
  else
    raise (Error (pos, Printf.sprintf "use of sent-away%s%s qubit%s %s" 
                                        (if !measuredestroys then "/measured" else "")
                                        (if t.inst=Qubits then "/joined" else "")
                                        (if t.inst=Qubits then "s" else "")
                                        (string_of_name n)
                 )
          )

and resource_of_params state params = 
  List.fold_right (fun param (state, nrs) ->
                     let n, toptr = tinst param, toptr param in
                     let state, r = resource_of_type (param.pos,n,None) state (_The !toptr) in
                     state, (n,r)::nrs 
                  ) 
                  params
                  (state,[])

and rck_proc mon state env stoppers proc = 
  let rec rp state env stoppers proc =
    let badproc s =
      raise (Error (proc.pos, Printf.sprintf "checking %s: %s"
                                             (short_string_of_process proc)
                                             s
                   )
            )
    in
    if !verbose then 
      Printf.printf "rp %s %s %s %s\n" (string_of_env env)
                                       (string_of_state state)
                                       (string_of_stoppers stoppers)
                                       (short_string_of_process proc);
    let r =
      let outerproc = proc in
      match proc.inst with
      | Terminate               -> RidSet.empty
      | GoOnAs (n, es)          -> (* disjoint resources in the arguments, no dead qubits used *)
                                   let ers = List.map (snd <.> disjoint_resources_of_expr UPass state env stoppers) es in
                                   (try disju ers with OverLap s -> badproc s)
      | WithNew ((_,params), proc)  
                                -> (* all channels, no new resource, nothing used *)
                                   let env = List.fold_left (fun env param -> env <@+> (name_of_param param, RNull)) env params in
                                   rp state env stoppers proc
      | WithQubit (_,qspecs, proc) 
                                -> rqspecs state env stoppers qspecs proc
      | JoinQs (qns, qp, proc)  -> let do_q (state,used) qn = rqs state env stoppers used qn in
                                   let state, used = List.fold_left do_q (state, RidSet.empty) qns
                                   in
                                   let n = name_of_param qp in
                                   let state, q = newqid (qp.pos,n,None) state in 
                                   let r = RQubit q in
                                   runbind r (RidSet.union used (rp state (env<@+>(n,r)) stoppers proc))
      | SplitQs (qn, qspecs, proc) 
                                -> let state, used = rqs state env stoppers RidSet.empty qn in
                                   RidSet.union used (rqspecs state env stoppers qspecs proc)
      | WithLet (letspec, proc) -> (* whatever resource the expression gives us *)
                                   let pat, e = letspec in
                                   let re, usede = resources_of_expr URead state env stoppers e in 
                                   let used = rck_pat (fun state env stoppers -> rp state env stoppers proc) 
                                                      runbind state env stoppers pat (Some re) 
                                   in
                                   (* rck_pat does the runbinding *)
                                   RidSet.union used usede
      | WithProc  (pdecl, proc) -> let (brec, pn, params, p) = pdecl in
                                   let _ = rp state env ((env,StopUse)::stoppers) p in
                                   rp state env stoppers proc
      | WithQstep (qstep,proc)  -> (match qstep.inst with 
                                    | Measure (plural, qe, gopt, pattern) -> 
                                        let destroys = !measuredestroys in
                                        (* if destroys is false then qe can be ambiguously conditional *)
                                        let rq, usedq = (if destroys then disjoint_resources_of_expr else resources_of_expr) 
                                                            (if destroys then UMeasure else URead) state env stoppers qe 
                                        in
                                        let usedg = ((snd <.> resources_of_expr URead state env stoppers) ||~~ RidSet.empty) gopt in
                                        let env' = match tinst pattern with
                                                   | PatAny    -> env
                                                   | PatName n -> env <@+> (n,RNull)
                                                   | _         -> raise (Disaster (qstep.pos, string_of_qstep qstep))
                                        in
                                        let state = 
                                          match destroys, rq with
                                          | false, _        -> state
                                          | true , RQubit q -> State.add q false state
                                          | true , _        -> (* belt and braces ... *)
                                              raise (Error (qe.pos, "ambiguous qubit expression (which qubit is destroyed?)"))
                                        in
                                    | Through (_, qes, ug)    -> 
                                        RidSet.union usedq (RidSet.union usedg (rp state env' stoppers proc))
                                        let qers = List.map (snd <.> resources_of_expr UGate state env stoppers) qes in
                                        (try let used = disju qers in
                                             ResourceSet.union (rp state env stoppers proc) used
                                         with OverLap s -> badproc s
                                        )
                                   )
      | Iter (pat, e, p, proc)  -> let re, eused = resources_of_expr URead state env stoppers e in
                                   let pused state env stoppers p = rp state env ((env,StopKill)::stoppers) p in
                                   let used = rck_pat (fun state env stoppers -> pused state env stoppers p) 
                                                       runbind state env stoppers pat (Some re)
                                   in
                                   List.fold_left RidSet.union used [eused; rp state env stoppers proc]
      | TestPoint (n, proc)     -> (match find_monel n.inst mon with
                                    | Some (_,monproc) -> RidSet.union (rp state env [(env, StopAllButRead)] monproc) 
                                                                            (rp state env stoppers proc)
                                    | None             -> raise (Can'tHappen (Printf.sprintf "%s: rck sees no monproc"
                                                                                               (string_of_sourcepos n.pos)
                                                                             )
                                                                )
                                   )
      | Cond (ce,p1,p2)         -> let _, used = resources_of_expr URead state env stoppers ce in
                                   let prs = List.map (rp state env stoppers) [p1;p2] in
                                   List.fold_left RidSet.union used prs (* NOT disju, silly boy! *)
      | PMatch (e,pms)          -> let re, usede = resources_of_expr URead state env stoppers e in
                                   List.fold_left RidSet.union usede (rck_pats (rck_proc mon) runbind state env stoppers (Some re) pms)
      | GSum gs                 -> 
          let rg (iostep, proc) =
            match iostep.inst with 
            | Read (ce,pat)  -> let _, usedce = resources_of_expr URead state env stoppers ce in
                                let used = rck_pat (fun state env stoppers -> rp state env stoppers proc) 
                                                   runbind state env stoppers pat None 
                                in
                                RidSet.union usedce used
            | Write (ce,e)   -> (try let _, usedce = resources_of_expr URead state env stoppers ce in
                                     let r, usede = disjoint_resources_of_expr USend state env stoppers e in
                                     (* if it's a channel of qubit, then it sends away a qubit *)
                                     let state = 
                                       match (type_of_expr ce).inst with
                                       | Channel {inst=Qubit} ->
                                           (match r with
                                            | RQubit q   -> State.add q false state
                                            | _          ->
                                               raise (Error (e.pos, "ambiguous qubit expression (which qubit is sent?)"))
                                           )
                                       | _              -> state
                                     in
                                     List.fold_left RidSet.union RidSet.empty [usedce; usede; rp state env stoppers proc]
                                 with OverLap s -> badproc s
                                )
         in
         List.fold_left RidSet.union RidSet.empty (List.map rg gs)
      | Par ps                  -> (try let prs = List.map (rp state env stoppers) ps in
                                        disju prs
                                    with OverLap s -> badproc s
                                   )
    in
    if !verbose then 
      Printf.printf "rp ... ... %s\n  => %s\n" (string_of_process proc) (RidSet.to_string r);
    r
  
  and rqs state env stoppers used qn = 
    let n = tinst qn in
    let r = env<@>n in
    let q = match r with
            | RQubit q -> q
            | _        -> raise (Disaster (qn.pos, "not qubit/qubits resource"))
    in
    let _, u = resources_of_q qn.pos URead state stoppers r (type_of_typedname qn) n q in
    State.add q false state, RidSet.union used u

  and rqspecs state env stoppers specs proc =
    let do_spec (rs, used, state, env) (param, eopt) =
      let _, usede = match eopt with
                     | Some e -> resources_of_expr URead state env stoppers e
                     | None   -> RNull, RidSet.empty
      in
      let n = name_of_param param in
      let state, q = newqid (param.pos,n,None) state in
      let r = RQubit q in
      r::rs, RidSet.union used usede, state, env <@+> (n,r)
    in
    let rs, used, state, env = List.fold_left do_spec ([], RidSet.empty, state, env) specs in
    List.fold_left (revargs runbind) (RidSet.union used (rp state env stoppers proc)) rs
  in
  rp state env stoppers proc
  
let rck_def env def =
  if !verbose then 
    Printf.printf "\nrck_def %s %s\n"
                  (string_of_env env)
                  (string_of_def def);
  match def with
  | Processdefs pdefs -> 
      let rck_pdef (pn, params, proc, mon) =
        let state, rparams = resource_of_params State.empty params in
        if !verbose then
          Printf.printf "\ndef %s params %s resource %s\n" 
                        (string_of_name (tinst pn))
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
  match tinst expr with
  | EUnit
  | ERes       _
  | EVar       _
  | ENum       _
  | EBool      _
  | EChar      _
  | EString    _
  | EBit       _
  | EBra       _
  | EKet       _
  | ENil                    -> ()
  | EMinus     e
  | ENot       e            
  | EDagger    e            -> ffv_expr e
  | ETuple     es           -> List.iter ffv_expr es  
  | ECons      (e1,e2)
  | EAppend    (e1,e2)
  | EJux       (e1,e2)      
  | ESub       (e1,e2)      -> List.iter ffv_expr [e1;e2]
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
              | Some fn -> ne_filter (NameSet.singleton (tinst fn)) veset
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
  | GoOnAs    (pn,es)              -> List.iter ffv_expr es
  | WithNew   ((_,params), proc)   -> ffv_proc mon proc
  | WithQubit  (_,qspecs, proc)     -> List.iter ffv_qspec qspecs; ffv_proc mon proc
  | WithLet   (letspec, proc)      -> ffv_letspec letspec; ffv_proc mon proc
  | WithProc  (pdecl, proc)        -> let (_,_,_,p) = pdecl in
                                      ffv_proc mon p; ffv_proc mon proc
  | WithQstep (qstep, proc)        -> ffv_qstep qstep; ffv_proc mon proc
  | JoinQs    (_, _, proc)         -> ffv_proc mon proc
  | SplitQs   (_, qspecs, proc)    -> List.iter ffv_qspec qspecs; ffv_proc mon proc
  | TestPoint (n, proc)            -> (match find_monel n.inst mon with
                                       | Some (_,monproc) -> ffv_proc [] monproc; ffv_proc mon proc
                                       | None -> raise (Can'tHappen (string_of_sourcepos n.pos ^
                                                                     ": resourcecheck ffv can't find " ^ n.inst
                                                                    )
                                                       )
                                      )
  | Iter      (params, e, p, proc) -> ffv_proc mon p; ffv_expr e; ffv_proc mon proc
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
  | Measure (_, expr, gopt, _)  -> ffv_expr expr; (ffv_expr ||~~ ()) gopt
  | Through (_, exprs, ge)      -> List.iter ffv_expr exprs; ffv_expr ge
  
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

and ffv_pdef (pn, _, proc, mon) = ffv_proc mon proc

(* *************** main function: trigger the phases *************************** *)

let resourcecheck defs = 
  (* defs have been rewritten to mark exprs with their types. I hope. *)
  
  push_verbose !verbose_resource (fun () ->  
    let knownassoc = 
      List.map (fun (n,t,_) -> let _, r = resource_of_type (dummy_spos, "library_"^n, None) State.empty (Parseutils.parse_typestring t) in
                               n, r
               ) 
               !Library.knowns 
    in
    let env = NameMap.of_assoc knownassoc in
    let do_def env def =
      match def with
      | Processdefs  pdefs      -> let do_pdef env (pn, _, _, _) = env <@+> (tinst pn,RNull) in
                                   List.fold_left do_pdef env pdefs
      | Functiondefs fdefs      -> let do_fdef env (fn, _, _, _) = env <@+> (tinst fn,RNull) in
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