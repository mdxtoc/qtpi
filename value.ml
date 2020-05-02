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

open Sourcepos
open Settings
open Listutils
open Functionutils
open Optionutils
open Tupleutils
open Instance
open Type
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

module OrderedPrioI = struct type prio = int
                            let compare = (~-)<..>Stdlib.compare
                     end

module Ipq = PQueue.Make (OrderedPrioI)

let queue_elements q = let vs = Queue.fold (fun vs v -> v::vs) [] q in
                       List.rev vs

let string_of_queue string_of sep q = 
  let vs = queue_elements q in
  "{" ^ string_of_list string_of sep vs ^ "}"

(* this type doesn't exist any more 
   type value =
     | VUnit
     | VBit of bool
     | VNum of num
     | VBool of bool
     | VSxnum of csnum
     | VChar of Uchar.t
     | VBra of nv
     | VKet of nv
     | VMatrix of matrix
     | VGate of gate
     | VQbit of qbit
     | VQbits of qbit list
     | VQstate of string
     | VChan of chan
     | VTuple of value list
     | VList of value list
     | VFun of (value -> value)        (* with the environment baked in for closures *)
     | VProcess of name * env ref * name list * process
 *)
(* but these do ... *)

(* I make heavy use of Obj.magic at run time. Type vt is a place holder *)
(* but to make show and compare, from the library, work at all, values come with a type
   -- which is never looked at
 *)

type vt = int (* oh no it isn't! Oh yes it is! A fake type for run-time values: see compile.ml *)

(* for the moment I'm still using an assoc list as environment *)
(* one day this will be a vt array *)
type env = vt monenv (* assoc list, experiment suggests, is more efficient than Map at runtime *)

(* at present I can't think of how to deal with singleton qbits and qbit collections than to have two kinds of value. 
   One is an int, the other an int list
 *)
type qbit = int

type procv = name * env ref * name list * process

(* the gsum_info in channel waiter queues is to deal with guarded sums: an offer
   to communicate is withdrawn from all guards by setting the shared boolean to false.
   The channel list is to remove a space leak (blush): clear out the dead from those channels.
   The space leak is because we keep a set stuck_chans (a set?) for diagnostic printing purposes.
 *)
 
type chan = {cname: int; traced: bool; stream: vt Queue.t; wwaiters: (wwaiter*gsum_info) Ipq.pq; rwaiters: (rwaiter*gsum_info) Ipq.pq}

and gsum_info = (bool * chan list) ref

and runner = name * process * env

and rwaiter = name * pattern * process * env

and wwaiter = name * vt * process * env

let string_of_vt : vt -> string = fun _ -> "?<vt>"

let string_of_qbit i = "#" ^ string_of_int i

let short_string_of_qbit = string_of_qbit

let string_of_qbits = bracketed_string_of_list string_of_qbit

let short_string_of_qbits = string_of_qbits

let string_of_bit b = if b then "1" else "0"

let queue_elements queue = Queue.fold (fun es e -> e::es) [] queue

(* *************************** conversion functions for the vt trick ********************************** *)

let to_bit     : vt -> bool         =  Obj.magic
let to_bool    : vt -> bool         =  Obj.magic
let to_bra     : vt -> nv           =  Obj.magic
let to_chan    : vt -> chan         =  Obj.magic
let to_csnum   : vt -> csnum        =  Obj.magic
let to_fun     : vt -> (vt -> vt)   =  Obj.magic
let to_gate    : vt -> gate         =  Obj.magic
let to_ket     : vt -> nv           =  Obj.magic
let to_list    : vt -> vt list      =  Obj.magic
let to_matrix  : vt -> matrix       =  Obj.magic
let to_num     : vt -> num          =  Obj.magic
let to_nv      : vt -> nv           =  Obj.magic
let to_procv   : vt -> procv        =  Obj.magic 
let to_qbit    : vt -> qbit         =  Obj.magic
let to_qbits   : vt -> qbit list    =  Obj.magic
let to_uchar   : vt -> Uchar.t      =  Obj.magic
let to_uchars  : vt -> Uchar.t list = Obj.magic
let to_unit    : vt -> unit         =  Obj.magic

let of_bit     : bool         -> vt = Obj.magic
let of_bool    : bool         -> vt = Obj.magic
let of_bra     : nv           -> vt = Obj.magic
let of_chan    : chan         -> vt = Obj.magic
let of_csnum   : csnum        -> vt = Obj.magic
let of_fun     : (vt -> vt)   -> vt = Obj.magic
let of_gate    : gate         -> vt = Obj.magic
let of_ket     : nv           -> vt = Obj.magic
let of_list    : vt list      -> vt = Obj.magic
let of_matrix  : matrix       -> vt = Obj.magic
let of_num     : num          -> vt = Obj.magic
let of_nv      : nv           -> vt = Obj.magic
let of_procv   : procv        -> vt = Obj.magic
let of_qbit    : qbit         -> vt = Obj.magic
let of_qbits   : qbit list    -> vt = Obj.magic
let of_uchar   : Uchar.t      -> vt = Obj.magic
let of_uchars  : Uchar.t list -> vt = Obj.magic
let of_tuple   : vt list      -> vt = Obj.magic
let of_unit    : unit         -> vt = Obj.magic

(* convert strings, for the library. What's hidden is a uchar list (see of_uchars) *)
let reveal_string : vt -> string = fun v -> let cs = to_uchars v in
                                            Utf8.string_of_uchars cs
let hide_string : string -> vt = fun s -> of_uchars (Utf8.uchars_of_string s)

let reveal_qstate = reveal_string
let hide_qstate = hide_string

(* convert pairs and triples, for the library. What's hidden is an n-element list (see of_tuple) *)
let reveal_pair   : vt -> 'a * 'b = fun v -> let vs = to_list v in 
                                             (Obj.magic (List.hd vs) :'a), 
                                             (Obj.magic (List.hd (List.tl vs)) :'b)
let hide_pair   : 'a * 'b -> vt = fun (a,b) -> let vs =  [(Obj.magic a :int); (Obj.magic b :int)] in
                                               of_tuple vs

let reveal_triple : vt -> 'a * 'b * 'c = fun v -> let vs = to_list v in 
                                         (Obj.magic (List.hd vs) :'a), 
                                         (Obj.magic (List.hd (List.tl vs)) :'b), 
                                         (Obj.magic (List.hd (List.tl (List.tl vs))) :'c)
let hide_triple : 'a * 'b *'c -> vt = fun (a,b,c) -> let vs = [(Obj.magic a:int); (Obj.magic b:int); (Obj.magic c:int)] in
                                                     of_tuple vs

(* convert integers, for the library. What's hidden is a num *) 
let hide_int    : int -> vt = fun i -> of_num (num_of_int i) 

(* ********************* string_of_ functions ***************************** *)

let string_of_pqueue stringof sep pq = 
  "{" ^ string_of_list stringof sep (List.map snd( Ipq.to_list pq)) ^ "}"
;;

(* so_value takes an argument optf to winnow out those things we don't want it to deal with directly *)
(* this is to allow the library function 'show' to work properly. The rest of the world can use string_of_value *)
(* Since we no longer have run-time types, it has to have a type argument t *)
let rec so_value optf t v =
  match optf t with
  | Some s -> s
  | None   -> (match t.inst with
               | Unit          -> "()"
               | Bit           -> if to_bool v then "1" else "0"
               | Num           -> string_of_num (to_num v)
               | Bool          -> string_of_bool (to_bool v)
               | Sxnum         -> string_of_csnum (to_csnum v)
               | Bra           -> string_of_bra (to_bra v)
               | Ket           -> string_of_ket (to_ket v)
               | Matrix        -> string_of_matrix (to_matrix v)
               | Gate          -> string_of_gate (to_gate v)
               | Char          -> Printf.sprintf "'%s'" (Utf8.escaped (to_uchar v))
               | Qbit          -> "Qbit " ^ string_of_qbit (to_qbit v)
               | Qbits         -> "Qbits " ^ string_of_qbits (to_qbits v)
               | Qstate        -> reveal_string v
               | Channel t     -> "Chan " ^ so_chan optf t (to_chan v)
               | Tuple ts      -> "(" ^ string_of_list (uncurry2 (so_value optf)) "," (zip ts (to_list v)) ^ ")"
               | List t        -> bracketed_string_of_list (so_value optf t) (to_list v)
               | Process ts    -> (* don't print the env: it will be an infinite recursion *)
                                  let n, env, ns, p = to_procv v in
                                  Printf.sprintf "procv %s .. (%s) %s"
                                                      (string_of_name n)
                                                      (string_of_list string_of_name "," ns)
                                                      (Process.string_of_process p)
               | Fun _         
               | Unknown _
               | Known _
               | Poly _       -> Printf.sprintf "?<vt type %s>" (string_of_type t)
              )

and short_so_value optf t v =
  match optf t with
  | Some s -> s
  | None   -> (match t.inst with
               | Qbit          -> "Qbit " ^ short_string_of_qbit (to_qbit v)
               | Qbits         -> "Qbits " ^ short_string_of_qbits (to_qbits v)
               | Channel t     -> let c = to_chan v in
                                  "Chan " ^ short_so_chan optf t c ^ if c.traced then "" else "(untraced)"
               | Tuple ts      -> "(" ^ string_of_list (uncurry2 (short_so_value optf)) "," (zip ts (to_list v)) ^ ")"
               | List t        -> bracketed_string_of_list (short_so_value optf t) (to_list v)
               | Process ts    -> let n, env, ns, p = to_procv v in
                                  Printf.sprintf "procv %s .. (%s)"
                                                      (string_of_name n)
                                                      (string_of_list string_of_name "," ns)
               | _             -> so_value optf t v
              )
  
and so_chan optf t {cname=i; traced=traced; stream=vs; rwaiters=rq; wwaiters=wq} =
    Printf.sprintf "%d%s = vs:{%s} rs:{%s} ws:{%s}"
                   i
                   (if traced then "" else "(untraced)")
                   (string_of_queue (so_value optf t) "; " vs)
                   (string_of_pqueue (short_so_rwaiter optf) "; " rq)
                   (string_of_pqueue (short_so_wwaiter optf t) "; " wq)

and short_so_chan optf t {cname=i} =
    string_of_int i
    
and so_env optf env =
  "{" ^ string_of_monenv "=" (* (so_value optf) *) string_of_vt env  ^ "}"

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
                 
and so_wwaiter optf t ((n, v, proc, env),gsir) = 
  Printf.sprintf "%s = (%s)%s %s%s" 
                 (string_of_name n)
                 (so_value optf t v)
                 (short_string_of_process proc)
                 (short_so_env optf env)
                 (if fst !gsir then "" else "[dead]")
                 
and short_so_wwaiter optf t ((n, v, proc, env),gsir) = (* infinite loop if we print the environment *)
  Printf.sprintf "%s(%s)%s" 
                 (string_of_name n)
                 (so_value optf t v)
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

let string_of_runner = so_runner doptf
let string_of_runnerqueue = so_runnerqueue doptf

