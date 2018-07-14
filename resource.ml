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
   
   We can't get this exactly right, but we can apply an over-zealous check. The resources
   of a process are those names whose type includes qbit. The resources required by an
   expression are those qbits which it names. We can allow fst, snd, hd and tl, with
   their built-in meanings, to modify those resources: so the resource named by 
   snd (hd ps) is just snd (hd ps). And snd (hd ps) overlaps with hd ps and with ps, but 
   not with fst (hd ps) or with tl ps. Rresource of anything complicated, like 
   (if e then fst else snd fi) ps, is ps.
   
   It matters that the only functions we have are external: be afraid of
     lambda i . if i=0 then q1 else q2 fi
   -- which has qbit in its type, I suppose. I'll be afraid of those.
   
   Good luck to us all.
 *)
 
open Instance
open Sourcepos
open Name
open Type
open Expr
open Typecheck

exception Error of string

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
  
let type_of_expr e =
  match !(e.inst.etype) with
  | Some t -> t
  | None   -> raise (Error (Printf.sprintf "%s: typecheck didn't mark %s"
                                           (string_of_sourcepos e.pos)
                                           (string_of_expr e)
                           )
                    )
  
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
  
let resourcecheck cxt lib defs = 
  (* the typecxt comes from typecheck. lib is from given. defs have been rewritten *)
  ()