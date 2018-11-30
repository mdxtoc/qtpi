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

open Listutils
open Basisv
open Number
open Name
open Process
open Pattern

let queue_elements q = let vs = Queue.fold (fun vs v -> v::vs) [] q in
                       List.rev vs

let string_of_queue string_of_v sep q = 
  let vs = queue_elements q in
  "{" ^ string_of_list string_of_v sep vs ^ "}"

type value =
  | VUnit
  | VBit of bool
  | VNum of num
  | VBool of bool
  | VChar of char
  | VBasisv of basisv
  | VGate of ugv
  | VString of string
  | VQbit of qbit
  | VQstate of string
  | VChan of chan
  | VTuple of value list
  | VList of value list
  | VFun of (value -> value)        (* with the environment baked in for closures *)
  | VProcess of name list * process

and ugv =
  | GateH
  | GateF
  | GateG
  | GateI
  | GateX
  | GateY
  | GateZ
  | GateCnot
  | GatePhi of int

and qbit = int

(* the gsum_info in channel waiter queues is to deal with guarded sums: an offer
   to communicate is withdrawn from all guards by setting the shared boolean to false.
   The channel list is to remove a space leak (blush): clear out the dead from those channels.
   The space leak is because we keep a set stuck_chans (a set?) for diagnostic printing purposes.
 *)
 
and chan = {cname: int; stream: value Queue.t; wwaiters: (wwaiter*gsum_info) PQueue.t; rwaiters: (rwaiter*gsum_info) PQueue.t}

and gsum_info = (bool * chan list) ref

and runner = name * process * env

and rwaiter = name * pattern * process * env

and wwaiter = name * value * process * env

and env = (name * value) list (* which, experiment suggests, is more efficient than Map at runtime *)

let string_of_pqueue string_of sep pq = 
  "{" ^ string_of_list string_of sep (PQueue.elements pq) ^ "}"
;;

let rec string_of_value v =
  match v with
  | VUnit           -> "()"
  | VBit b          -> if b then "1" else "0"
  | VNum n          -> string_of_num n
  | VBool b         -> string_of_bool b
  | VBasisv bv      -> string_of_basisv bv
  | VGate ugv       -> string_of_ugv ugv
  | VChar c         -> Printf.sprintf "'%s'" (Char.escaped c)
  | VString s       -> Printf.sprintf "\"%s\"" (String.escaped s)
  | VQbit q         -> "Qbit " ^ string_of_qbit q
  | VQstate s       -> s
  | VChan c         -> "Chan " ^ string_of_chan c
  | VTuple vs       -> "(" ^ string_of_list string_of_value "," vs ^ ")"
  | VList vs        -> bracketed_string_of_list string_of_value vs
  | VFun f          -> "<function>"
  | VProcess (ns,p) -> Printf.sprintf "process (%s) %s"
                                      (string_of_list string_of_name "," ns)
                                      (string_of_process p)

and short_string_of_value v =
  match v with
  | VQbit q         -> "Qbit " ^ short_string_of_qbit q
  | VChan c         -> "Chan " ^ short_string_of_chan c
  | VTuple vs       -> "(" ^ string_of_list short_string_of_value "," vs ^ ")"
  | VList vs        -> bracketed_string_of_list short_string_of_value vs
  | VProcess (ns,p) -> Printf.sprintf "process (%s)"
                                      (string_of_list string_of_name "," ns)
  | v               -> string_of_value v
  
and string_of_chan {cname=i; stream=vs; rwaiters=rq; wwaiters=wq} =
    Printf.sprintf "%d = vs:{%s} rs:{%s} ws:{%s}"
                   i
                   (string_of_queue string_of_value "; " vs)
                   (string_of_pqueue short_string_of_rwaiter "; " rq)
                   (string_of_pqueue short_string_of_wwaiter "; " wq)

and short_string_of_chan {cname=i} =
    string_of_int i
    
and string_of_env env =
  "{" ^ string_of_assoc string_of_name string_of_value ":" ";" env ^ "}"

and short_string_of_env env =
  "{" ^  string_of_assoc string_of_name short_string_of_value  ":" ";" 
                         (List.filter (function 
                                       | _, VFun     _ 
                                       | _, VProcess _ -> false
                                       | _             -> true
                                      )
                                      env 
                         ) ^
  "}"   
  
and string_of_runner (n, proc, env) =
  Printf.sprintf "%s = (%s) %s" 
                 (string_of_name n)
                 (short_string_of_process proc)
                 (short_string_of_env env)
                 
and string_of_rwaiter ((n, pat, proc, env),gsir) = 
  Printf.sprintf "%s = (%s)%s %s%s" 
                 (string_of_name n)
                 (string_of_pattern pat)
                 (short_string_of_process proc)
                 (short_string_of_env env)
                 (if fst !gsir then "" else "[dead]")
                 
and short_string_of_rwaiter ((n, pat, proc, env),gsir) = (* infinite loop if we print the environment *)
  Printf.sprintf "%s(%s)%s" 
                 (string_of_name n)
                 (string_of_pattern pat)
                 (if fst !gsir then "" else "[dead]")
                 
and string_of_wwaiter ((n, v, proc, env),gsir) = 
  Printf.sprintf "%s = (%s)%s %s%s" 
                 (string_of_name n)
                 (string_of_value v)
                 (short_string_of_process proc)
                 (short_string_of_env env)
                 (if fst !gsir then "" else "[dead]")
                 
and short_string_of_wwaiter ((n, v, proc, env),gsir) = (* infinite loop if we print the environment *)
  Printf.sprintf "%s(%s)%s" 
                 (string_of_name n)
                 (string_of_value v)
                 (if fst !gsir then "" else "[dead]")
                 
and string_of_runnerqueue sep rq =
  string_of_pqueue string_of_runner sep rq

and string_of_ugv = function
  | GateH           -> "_H"
  | GateF           -> "_F"
  | GateG           -> "_G"
  | GateI           -> "_I"
  | GateX           -> "_X"
  | GateY           -> "_Y"
  | GateZ           -> "_Z"
  | GateCnot        -> "_Cnot"
  | GatePhi (i)     -> "_Phi(" ^ string_of_int i ^ ")"

and string_of_qbit = string_of_int

and short_string_of_qbit = string_of_int

