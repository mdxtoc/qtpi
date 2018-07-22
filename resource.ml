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
open Name
open Type
open Expr
open Param
open Processdef
open Process
open Step
open Typecheck

exception Error of string
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
  
  
    (* not doing fst, snd, hd, tl yet *)
    let rec resource_of_expr cxt e =
      let t = type_of_expr e in
      let do_list = List.fold_left (fun set e -> NameSet.union set (resource_of_expr cxt e)) NameSet.empty in
      if is_resource_type t then
        match e.inst.enode with
        | EUnit               
        | EInt        _              
        | EBool       _
        | EBit        _             
        | EMinus      _
        | EArith      _
        | ECompare    _
        | EBoolArith  _         -> NameSet.empty    (* because type is int or bool *)
        | EBitCombine _         -> raise (Error (Printf.sprintf "%s has resource type %s"
                                                                (string_of_expr e)
                                                                (string_of_type t)
                                                )
                                         )
        | EVar    n             -> NameSet.singleton n
        | ETuple  es           
        | EList   es            -> do_list es
        | ECond   (e1,e2,e3)    -> do_list [e1;e2;e3]
        | EApp    (f, a)        -> do_list [f;a]
        | EAppend (e1,e2)       -> do_list [e1;e2]
      else NameSet.empty
  
*)

let type_of_expr e =
  match !(e.inst.etype) with
  | Some t -> t
  | None   -> raise (Error (Printf.sprintf "** Disaster %s: typecheck didn't mark %s"
                                           (string_of_sourcepos e.pos)
                                           (string_of_expr e)
                           )
                    )

let check_type pn classic t = 
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

let rck_given (pn, t) = check_type pn false t

let rck_def (Processdef(pn, params, proc)) =
  let check_param p =
    let bad_param s = raise (Error (Printf.sprintf "resourcecheck in %s, parameter %s: %s"
                                                   (string_of_name pn)
                                                   (string_of_param p)
                                                   s
                                   )
                            )
    in
    let n, tor = p in
    match !tor with
    | Some t -> check_type pn false t
    | _      -> bad_param "Disaster (typechecked type expected)"
  in
  let rec check_proc proc =
    match proc with
    | Terminate                 -> ()
    | Call     (pn', es)        -> List.iter check_expr es
    | WithNew  (params, proc)   -> List.iter check_param params; check_proc proc
    | WithQbit (qspecs, proc)   -> List.iter (fun (param,_) -> check_param param) qspecs;
                                   check_proc proc
    | WithLet  (letspec, proc)  -> let param, e = letspec in
                                   check_param param; 
                                   check_expr e;
                                   check_proc proc
    | WithStep (step, proc)     -> check_step step; check_proc proc
    | Cond     (ce,p1,p2)       -> check_expr ce; List.iter check_proc [p1;p2]
    | Par      procs            -> List.iter check_proc procs
  and check_step step =
    (* if the channel types are right then we don't need to type-police the steps. But check the exprs for use of functions *)
    match step with
    | Read      (ce,params) -> check_expr ce; List.iter check_param params
    | Write     (ce,es)     -> List.iter check_expr (ce::es)
    | Measure   (qe,param)  -> check_expr qe; check_param param
    | Ugatestep (qes, ug)   -> List.iter check_expr qes
  and check_expr e =
    match e.inst.enode with
    | EUnit
    | EVar       _
    | EInt       _
    | EBool      _
    | EBit       _          -> ()   (* constants *)
    | EMinus     e          -> check_expr e
    | ETuple     es
    | EList      es         -> List.iter check_expr es
    | ECond      (ce,e1,e2) -> List.iter check_expr [ce;e1;e2]
    | EApp       (ef,ea)    -> List.iter (check_type pn true) [type_of_expr ef; type_of_expr ea];
                               check_expr ef; check_expr ea
    | EArith     (e1,_,e2)
    | ECompare   (e1,_,e2)
    | EBoolArith (e1,_,e2)   -> List.iter check_expr [e1;e2]
    | EAppend     (e1,e2)
    | EBitCombine (e1,e2)   -> List.iter check_expr [e1;e2]
    
  in
  List.iter check_param params;
  check_proc proc
  
let resourcecheck cxt lib defs = 
  (* the typecxt comes from typecheck. lib is from given. defs have been rewritten to mark exprs
     with their types.
     
     Let's police parameters: channels take either a single qbit or a classical value.
   *)
  List.iter rck_given lib;
  List.iter rck_def defs