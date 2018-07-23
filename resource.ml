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
   practical sense. And functions have nothing to do with qbits, either in their types
   or in their application.
   
   Good luck to us all.
 *)
 
open Instance
open Sourcepos
open Listutils
open Optionutils
open Tupleutils
open Name
open Type
open Expr
open Param
open Processdef
open Process
open Step
open Typecheck
open Settings

exception Error of string

let (<@>)  env n     = NameMap.find n env       (* is this evil? Over-riding Listutils.(<@>)!! *)
let (<@+>) env (n,t) = NameMap.add n t env      (* also evil? *)
let (<@->) env n     = NameMap.remove n env     (* also evil? *)
let (<@?>) env n     = NameMap.mem n env        (* you know, I no longer think it's evil *)

(*
    type resource = Res of name list (* in application order, which may not be efficient, but this is a static check *) 

    let rec string_of_resource = function
      | Res []        -> "can't happen"
      | Res [n]       -> string_of_name n
      | Res [n1;n2]   -> string_of_name n1 ^ " " ^ string_of_name n2
      | Res (n :: ns) -> Printf.sprintf "%s (%s)" (string_of_name n) (string_of_resource (Res ns))

    let rec is_resource_type t =
      let bad () =
      raise (Error (Printf.sprintf "** Disaster: is_resource_type (%s)"
                                   (string_of_type t)
                   )
            )
      in
      match t with
      | Qbit            -> true            
      | Int 
      | Bool
      | Bit           
      | Unit          
      | TypeVar _       (* hmm -- should only happen if never used *)
      | Range   _       -> false
      | Univ (ns, t)    -> is_resource_type t 
      | List    t       
      | Channel t       -> is_resource_type t
      | Tuple   ts      -> List.exists is_resource_type ts
      | Fun     (t1,t2) -> if is_resource_type t1 || is_resource_type t2 then bad () else false
                         
      | Process _       -> bad ()
  
  
*)

let type_of_expr e =
  match !(e.inst.etype) with
  | Some t -> t
  | None   -> raise (Error (Printf.sprintf "** Disaster %s: typecheck didn't mark %s"
                                           (string_of_sourcepos e.pos)
                                           (string_of_expr e)
                           )
                    )

(* *************** phase 1: channel types and function applications (ctfa_...) *************************** *)

let ctfa_type pn classic t = 
  let badtype s = raise (Error (Printf.sprintf "resourcecheck in %s, type %s: %s"
                                               (string_of_name pn)
                                               (string_of_type t)
                                               s
                               )
                        )
  in
  let rec ct classic vars t =
    match t with
    | Qbit            -> if classic then badtype "should be classical, includes qbit" else ()
    | Int
    | Bool
    | Bit 
    | Unit
    | Range   _       -> ()
    | TypeVar n       -> if NameSet.mem n vars then () else badtype "Disaster (typechecker left a type variable)"
    | Univ    (ns, t) -> ct classic (addnames ns vars) t
    | List    t       -> ct classic vars t
    | Tuple   ts    
    | Process ts      -> List.iter (ct classic vars) ts
    | Channel t       -> (match t with
                          | Qbit      -> () (* always ok, even in classical channels *)
                          | _         -> try ct true vars t
                                         with _ -> badtype "should be a channel of qbit or a classical channel"
                         )
    | Fun     (t1,t2) -> ct true vars t1; ct true vars t2
  in
  ct classic NameSet.empty t

let ctfa_given (pn, t) = ctfa_type pn false t

let ctfa_def (Processdef(pn, params, proc)) =
  let ctfa_param p =
    let bad_param s = raise (Error (Printf.sprintf "resourcecheck in %s, parameter %s: %s"
                                                   (string_of_name pn)
                                                   (string_of_param p)
                                                   s
                                   )
                            )
    in
    let n, tor = p in
    match !tor with
    | Some t -> ctfa_type pn false t
    | _      -> bad_param "Disaster (typechecked type expected)"
  in
  
  let rec ctfa_proc proc =
    match proc with
    | Terminate                 -> ()
    | Call     (pn', es)        -> List.iter ctfa_expr es
    | WithNew  (params, proc)   -> List.iter ctfa_param params; ctfa_proc proc
    | WithQbit (qspecs, proc)   -> List.iter (fun (param,_) -> ctfa_param param) qspecs;
                                   ctfa_proc proc
    | WithLet  (letspec, proc)  -> let param, e = letspec in
                                   ctfa_param param; 
                                   ctfa_expr e;
                                   ctfa_proc proc
    | WithStep (step, proc)     -> ctfa_step step; ctfa_proc proc
    | Cond     (ce,p1,p2)       -> ctfa_expr ce; List.iter ctfa_proc [p1;p2]
    | Par      procs            -> List.iter ctfa_proc procs
  
  and ctfa_step step =
    (* if the channel types are right then we don't need to type-police the steps. But check the exprs for use of functions *)
    match step with
    | Read      (ce,params) -> ctfa_expr ce; List.iter ctfa_param params
    | Write     (ce,es)     -> List.iter ctfa_expr (ce::es)
    | Measure   (qe,param)  -> ctfa_expr qe; ctfa_param param
    | Ugatestep (qes, ug)   -> List.iter ctfa_expr qes
  
  and ctfa_expr e =
    match e.inst.enode with
    | EUnit
    | EVar       _
    | EInt       _
    | EBool      _
    | EBit       _          -> ()   (* constants *)
    | EMinus     e          -> ctfa_expr e
    | ETuple     es
    | EList      es         -> List.iter ctfa_expr es
    | ECond      (ce,e1,e2) -> List.iter ctfa_expr [ce;e1;e2]
    | EApp       (ef,ea)    -> List.iter (ctfa_type pn true) [type_of_expr ef; type_of_expr ea];
                               ctfa_expr ef; ctfa_expr ea
    | EArith     (e1,_,e2)
    | ECompare   (e1,_,e2)
    | EBoolArith (e1,_,e2)   -> List.iter ctfa_expr [e1;e2]
    | EAppend     (e1,e2)
    | EBitCombine (e1,e2)   -> List.iter ctfa_expr [e1;e2]
    
  in
  List.iter ctfa_param params;
  ctfa_proc proc
  
(* *************** phase 2: resource check (rck_...) *************************** *)

type resource =
  | RQbit of int * bool         (* id, present *)
  | RTuple of resource list
  (* | RList of resource           (* hmmm ... *) *)
  | RNull

let rec string_of_resource r =
  match r with
  | RQbit (i,b)         -> Printf.sprintf "RQbit(%d,%B)" i b
  | RTuple rs           -> Printf.sprintf "RTuple [%s]" (string_of_list string_of_resource ";" rs)
  | RNull               -> "RNull"
  
module OrderedResource = struct type t = resource let compare = Pervasives.compare let to_string = string_of_resource end
module ResourceSet = MySet.Make(OrderedResource)  

let newqid =
  (let qid = ref 0 in
   let newqid () =
     let r = !qid in
     qid := !qid+1;
     r
   in
   newqid
  )
  
let resource_of_type pn t =
  let badtype s = raise (Error (Printf.sprintf "resourcecheck in %s, type %s: %s"
                                               (string_of_name pn)
                                               (string_of_type t)
                                               s
                               )
                        )
  in
  let rec rt t =
    match t with
    | Int
    | Bool
    | Bit 
    | Unit            
    | Range _         -> RNull
    | Qbit            -> RQbit (newqid(), true)
    | TypeVar n       -> RNull  (* checked in ctfa *)
    | Univ (ns,t)     -> RNull  (* checked in cfta *)
    | List t          -> let r = rt t in
                         if r=RNull then RNull else badtype (string_of_resource r ^ " -- haven't decided how to resource lists yet")
    | Tuple ts        -> let rs = List.map rt ts in
                         if List.exists (function RNull -> false | _ -> true) rs
                         then RTuple rs 
                         else RNull
    | Channel _       
    | Fun     _ 
    | Process _       -> RNull
  in
  rt t

let rec resources_of_expr env e =
  let do_list = List.fold_left (fun set e -> ResourceSet.union set (resources_of_expr env e)) ResourceSet.empty in
  match e.inst.enode with
  | EUnit               
  | EInt        _              
  | EBool       _
  | EBit        _         -> ResourceSet.empty            
  | EMinus      e         -> resources_of_expr env e
  | EArith      (e1,_,e2) 
  | ECompare    (e1,_,e2)
  | EBoolArith  (e1,_,e2) -> do_list [e1;e2] 
  | EVar        n         -> (match env <@> n with
                              | RNull -> ResourceSet.empty
                              | r     -> ResourceSet.singleton r
                             )
  | ETuple      es       
  | EList       es        -> do_list es
  | ECond       (e1,e2,e3)-> do_list [e1;e2;e3]
  | EApp        (e1,e2)
  | EBitCombine (e1,e2)
  | EAppend     (e1,e2)   -> do_list [e1;e2]
  
let rparams pn params = List.map (fun (n,toptr) -> n, resource_of_type pn ( _The (!toptr))) params

exception OverLap of string

let disju ers =
  let dju set er = if not (ResourceSet.is_empty (ResourceSet.inter set er)) 
                   then raise (OverLap (Printf.sprintf "non-disjoint resources (%s)" (string_of_list ResourceSet.to_string "," ers)))
                   else ResourceSet.union set er in
  List.fold_left dju ResourceSet.empty ers

let rck_proc pn env proc = 
  let badproc s =
    raise (Error (Printf.sprintf "resourcecheck in %s, checking %s: %s"
                                               (string_of_name pn)
                                               (short_string_of_process proc)
                                               s
                 )
          )
  in
  let rec rp env proc =
    if !verbose_resource then 
      Printf.printf "rp (%s) %s\n" (NameMap.to_string string_of_resource env)
                                   (short_string_of_process proc);
    let r =
      (match proc with
      | Terminate               -> ResourceSet.empty
      | Call (n, es)            -> (* disjoint resources in the arguments *)
                                   (try let ers = List.map (resources_of_expr env) es in
                                        disju ers
                                    with OverLap s -> badproc s
                                   )
      | WithNew (params, proc)  -> (* all channels, no resource *)
                                   let env = List.fold_left (fun env (n,_) -> NameMap.add n RNull env) env params in
                                   rp env proc
      | WithQbit (qspecs, proc) -> (* all new qbits *)
                                   let env = 
                                     List.fold_left (fun env ((n,_),_) -> NameMap.add n (RQbit (newqid(),true)) env) 
                                                    env 
                                                    qspecs 
                                   in
                                   rp env proc
      | WithLet (letspec, proc) -> (* whatever resource the expression gives us *)
                                   let (n,_),e = letspec in
                                   let er = resources_of_expr env e in
                                   let res = match ResourceSet.elements er with
                                             | []    -> RNull
                                             | [res] -> res
                                             | _     -> badproc (Printf.sprintf "let binding ambiguously uses resources %s" (ResourceSet.to_string er))
                                   in
                                   ResourceSet.union (rp (NameMap.add n res env) proc) er
      | WithStep (step,proc)    -> (match step with 
                                    | Read (ce,params)  -> let used = resources_of_expr env ce in
                                                           let extras = rparams pn params in
                                                           let env = List.fold_left (<@+>) env extras in
                                                           ResourceSet.union (rp env proc) used
                                    | Write (ce,es)     -> (try let used = resources_of_expr env ce in
                                                                let ers = List.map (resources_of_expr env) es in
                                                                let used = ResourceSet.union used (disju ers) in
                                                                ResourceSet.union (rp env proc) used
                                                            with OverLap s -> badproc s
                                                           )
                                    | Measure (qe, (n,_))   -> let used = resources_of_expr env qe in
                                                               ResourceSet.union used (rp (env <@+> (n,RNull)) proc)
                                    | Ugatestep (qes, ug)   -> (try let qers = List.map (resources_of_expr env) qes in
                                                                    let used = disju qers in
                                                                    ResourceSet.union (rp env proc) used
                                                                with OverLap s -> badproc s
                                                               )
                                   )
      | Cond (ce,p1,p2)         -> (try let used = resources_of_expr env ce in
                                        let prs = List.map (rp env) [p1;p2] in
                                        ResourceSet.union used (disju prs)
                                    with OverLap s -> badproc s
                                   )
      | Par ps                  -> (try let prs = List.map (rp env) ps in
                                        disju prs
                                    with OverLap s -> badproc s
                                   )
      )
    in
    if !verbose_resource then 
      Printf.printf "rp ... %s\n  => %s\n" (string_of_process proc) (ResourceSet.to_string r);
    r
  in
  rp env proc
  
let rck_def (Processdef(pn, params, proc)) = 
  let rparams = rparams pn params in
  if !verbose_resource then
    Printf.printf "\ndef %s params %s resource %s\n" 
                  (string_of_name pn)
                  (bracketed_string_of_list string_of_param params)
                  (bracketed_string_of_list (string_of_pair string_of_name string_of_resource ":") rparams);
  (* here we go with the symbolic execution *)
  let _ = rck_proc pn (NameMap.of_assoc rparams) proc in
  ()

(* *************** main function: trigger the phases *************************** *)
let resourcecheck cxt lib defs = 
  (* the typecxt comes from typecheck. lib is from given. defs have been rewritten to mark exprs
     with their types.
     
     Let's police parameters: channels take either a single qbit or a classical value. Functions and
     applications must have nothing to do with qbits.
   *)
  List.iter ctfa_given lib;
  List.iter ctfa_def defs;
  List.iter rck_def defs