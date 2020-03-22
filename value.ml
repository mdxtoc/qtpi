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
open Listutils
open Functionutils
open Optionutils
open Tupleutils
open Braket
open Number
open Name
open Process
open Pattern
open Monenv
open Snum
open Vmg

exception Disaster of string
exception Error of string

let queue_elements q = let vs = Queue.fold (fun vs v -> v::vs) [] q in
                       List.rev vs

let string_of_queue string_of sep q = 
  let vs = queue_elements q in
  "{" ^ string_of_list string_of sep vs ^ "}"

type value =
  | VUnit
  | VBit of bool
  | VNum of num
  | VBool of bool
  | VChar of Uchar.t
  | VBra of snv
  | VKet of snv
  | VMatrix of matrix
  | VGate of gate
  | VString of string
  | VQbit of qbit
  | VQstate of string
  | VChan of chan
  | VTuple of value list
  | VList of value list
  | VFun of (value -> value)        (* with the environment baked in for closures *)
  | VProcess of name * env ref * name list * process

and qbit = int

(* the gsum_info in channel waiter queues is to deal with guarded sums: an offer
   to communicate is withdrawn from all guards by setting the shared boolean to false.
   The channel list is to remove a space leak (blush): clear out the dead from those channels.
   The space leak is because we keep a set stuck_chans (a set?) for diagnostic printing purposes.
 *)
 
and chan = {cname: int; traced: bool; stream: value Queue.t; wwaiters: (wwaiter*gsum_info) PQueue.t; rwaiters: (rwaiter*gsum_info) PQueue.t}

and gsum_info = (bool * chan list) ref

and runner = name * process * env

and rwaiter = name * pattern * process * env

and wwaiter = name * value * process * env

and env = value monenv (* which, experiment suggests, is more efficient than Map at runtime *)

let string_of_qbit i = "#" ^ string_of_int i

let short_string_of_qbit = string_of_qbit

(* ********************* string_of_ functions ***************************** *)

let string_of_pqueue stringof sep pq = 
  "{" ^ string_of_list stringof sep (PQueue.elements pq) ^ "}"
;;

(* so_value takes an argument optf to winnow out those things we don't want it to deal with directly *)
(* this is to allow the library function 'show' to work properly. The rest of the world can use string_of_value *)
let rec so_value optf v =
  match optf v with
  | Some s -> s
  | None   -> (match v with
               | VUnit           -> "()"
               | VBit b          -> if b then "1" else "0"
               | VNum n          -> string_of_num n
               | VBool b         -> string_of_bool b
               | VBra b          -> string_of_bra b
               | VKet k          -> string_of_ket k
               | VMatrix m       -> string_of_matrix m
               | VGate g         -> string_of_gate g
               | VChar c         -> Printf.sprintf "'%s'" (Utf8.escaped c)
               | VString s       -> Printf.sprintf "\"%s\"" (String.escaped s)
               | VQbit q         -> "Qbit " ^ string_of_qbit q
               | VQstate s       -> s
               | VChan c         -> "Chan " ^ so_chan optf c
               | VTuple vs       -> "(" ^ string_of_list (so_value optf) "," vs ^ ")"
               | VList vs        -> bracketed_string_of_list (so_value optf) vs
               | VFun f          -> "<function>"
               | VProcess (n,_,ns,p) (* don't print the env: it will be an infinite recursion *)
                                 -> Printf.sprintf "process %s .. (%s) %s"
                                                      (string_of_name n)
                                                      (string_of_list string_of_name "," ns)
                                                      (string_of_process p)
              )

and short_so_value optf v =
  match optf v with
  | Some s -> s
  | None   -> (match v with
               | VQbit q         -> "Qbit " ^ short_string_of_qbit q
               | VChan c         -> "Chan " ^ short_so_chan optf c ^ if c.traced then "" else "(untraced)"
               | VTuple vs       -> "(" ^ string_of_list (short_so_value optf) "," vs ^ ")"
               | VList vs        -> bracketed_string_of_list (short_so_value optf) vs
               | VProcess (n,_,ns,_) 
                                 -> Printf.sprintf "process %s .. (%s)"
                                                      (string_of_name n)
                                                      (string_of_list string_of_name "," ns)
               | v               -> so_value optf v
              )
  
and so_chan optf {cname=i; traced=traced; stream=vs; rwaiters=rq; wwaiters=wq} =
    Printf.sprintf "%d%s = vs:{%s} rs:{%s} ws:{%s}"
                   i
                   (if traced then "" else "(untraced)")
                   (string_of_queue (so_value optf) "; " vs)
                   (string_of_pqueue (short_so_rwaiter optf) "; " rq)
                   (string_of_pqueue (short_so_wwaiter optf) "; " wq)

and short_so_chan optf {cname=i} =
    string_of_int i
    
and so_env optf env =
  "{" ^ string_of_monenv "=" (so_value optf) env ^ "}"

and short_so_env optf = so_env optf (* <.> (Monenv.filterg (function 
                                                        | _, VFun     _ 
                                                        | _, VProcess _ -> false
                                                        | _             -> true
                                                        )
                                         ) *)
  
and so_runner optf (n, proc, env) =
  Printf.sprintf "%s = (%s) %s" 
                 (string_of_name n)
                 (short_string_of_process proc)
                 (short_so_env optf env)
                 
and so_rwaiter optf ((n, pat, proc, env),gsir) = 
  Printf.sprintf "%s = (%s)%s %s%s" 
                 (string_of_name n)
                 (string_of_pattern pat)
                 (short_string_of_process proc)
                 (short_so_env optf env)
                 (if fst !gsir then "" else "[dead]")
                 
and short_so_rwaiter optf ((n, pat, proc, env),gsir) = (* infinite loop if we print the environment *)
  Printf.sprintf "%s(%s)%s" 
                 (string_of_name n)
                 (string_of_pattern pat)
                 (if fst !gsir then "" else "[dead]")
                 
and so_wwaiter optf ((n, v, proc, env),gsir) = 
  Printf.sprintf "%s = (%s)%s %s%s" 
                 (string_of_name n)
                 (so_value optf v)
                 (short_string_of_process proc)
                 (short_so_env optf env)
                 (if fst !gsir then "" else "[dead]")
                 
and short_so_wwaiter optf ((n, v, proc, env),gsir) = (* infinite loop if we print the environment *)
  Printf.sprintf "%s(%s)%s" 
                 (string_of_name n)
                 (so_value optf v)
                 (if fst !gsir then "" else "[dead]")
                 
and so_runnerqueue optf sep rq =
  string_of_pqueue (so_runner optf) sep rq

and string_of_gate g = 
  let nameopt = if !Settings.showsymbolicgate then
                  (if g=g_I       then Some "I" else
                   if g=g_X       then Some "X" else
                   if g=g_Y       then Some "Y" else
                   if g=g_Z       then Some "Z" else
                   if g=g_H       then Some "H" else
                   if g=g_Rz      then Some "Rz" else
                   if g=g_Rx      then Some "Rx" else
                   if g=g_Cnot    then Some "Cnot" else
                   if g=g_Swap    then Some "Swap" else
                   if g=g_Toffoli then Some "T" else 
                   if g=g_Fredkin then Some "F" else 
                   None
                  )
                else None
  in
  match nameopt with 
  | Some s -> s
  | None   -> Vmg.string_of_gate g

(* ********************************************************************************************************** *)

let doptf s = None

let string_of_value = so_value doptf
let short_string_of_value = short_so_value doptf 

let string_of_env = so_env doptf
let short_string_of_env = short_so_env doptf 

let string_of_chan = so_chan doptf
let short_string_of_chan = short_so_chan doptf 

let string_of_runnerqueue = so_runnerqueue doptf

