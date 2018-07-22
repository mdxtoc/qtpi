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
open Sourcepos
open Instance
open Name
open Expr
open Type
open Param
open Step
open Process
open Processdef
open Ugate
open Qsim

exception Error of sourcepos * string

type iprocess = IGiven | IDef of process

let string_of_iprocess = function
  | IGiven -> "_"
  | IDef p -> string_of_process p

let queue_elements q = let vs = Queue.fold (fun vs v -> v::vs) [] q in
                       List.rev vs

let string_of_queue string_of_v sep q = 
  let vs = queue_elements q in
  string_of_list string_of_v sep vs

module rec Types : sig
  type value =
    | VUnit
    | VInt of int
    | VBool of bool
    | VQbit of qbit
    | VChan of chan
    | VTuple of value list
    | VList of value list
    | VFun of (value -> value)        
    | VProcess of name list * iprocess

  and chan = {cname: int; stream: (value list) Queue.t; wwaiters: WWaiterQueue.t; rwaiters: RWaiterQueue.t}

  and runner = name * process * env

  and rwaiter = name * name list * process * env
  
  and wwaiter = name * value list * process * env

  and env = (name * value) list

  and stuck = name * value list
end = Types

and OrderedRWaiters : Priority_queue.Ordered = struct type t = Types.rwaiter let compare = Pervasives.compare end
and OrderedWWaiters : Priority_queue.Ordered = struct type t = Types.wwaiter let compare = Pervasives.compare end
and OrderedRunners : Priority_queue.Ordered = struct type t = Types.runner let compare = Pervasives.compare end

and RWaiterQueue : Priority_queue.PQ with type elt=Types.rwaiter = Priority_queue.Make(OrderedRWaiters)
and WWaiterQueue : Priority_queue.PQ with type elt=Types.wwaiter = Priority_queue.Make(OrderedWWaiters)
and RunnerQueue : Priority_queue.PQ with type elt=Types.runner = Priority_queue.Make(OrderedRunners)

open Types
let string_of_pqueue string_of sep es = 
  string_of_list (if !verbose_queues then (Tupleutils.string_of_pair string_of_int string_of ", ") 
                   else string_of <.> snd
                  )
                  sep
                  es
;;

let rec string_of_value = function
  | VUnit           -> "()"
  | VInt i          -> string_of_int i
  | VBool b         -> string_of_bool b
  | VQbit q         -> "Qbit " ^ string_of_qbit q
  | VChan c         -> "Chan " ^ string_of_chan c
  | VTuple vs       -> "(" ^ string_of_list string_of_value "," vs ^ ")"
  | VList vs        -> bracketed_string_of_list string_of_value vs
  | VFun f          -> "(..->..)"
  | VProcess (ns,p) -> Printf.sprintf "process (%s) %s"
                                      (string_of_list string_of_name "," ns)
                                      (string_of_iprocess p)

and short_string_of_value = function
  | VQbit q         -> "Qbit " ^ short_string_of_qbit q
  | VChan c         -> "Chan " ^ short_string_of_chan c
  | VTuple vs       -> "(" ^ string_of_list short_string_of_value "," vs ^ ")"
  | VList vs        -> "[" ^ string_of_list short_string_of_value ";" vs ^ "]"
  | VProcess (ns,p) -> Printf.sprintf "process (%s)"
                                      (string_of_list string_of_name "," ns)
  | v               -> string_of_value v
  
and string_of_chan {cname=i; stream=vs; rwaiters=rq; wwaiters=wq} =
    let string_of_qelement = function
      | [v] -> string_of_value v
      | vs  -> "(" ^ string_of_list string_of_value "," vs ^ ")"
    in
    Printf.sprintf "%d vs:{%s} rs:{%s} ws:{%s}"
                   i
                   (string_of_queue string_of_qelement "; " vs)
                   (string_of_pqueue short_string_of_rwaiter "; " (RWaiterQueue.queue rq))
                   (string_of_pqueue short_string_of_wwaiter "; " (WWaiterQueue.queue wq))

and short_string_of_chan {cname=i} =
    string_of_int i
    
and string_of_env env =
  string_of_assoc string_of_name string_of_value "->" "; " env

and short_string_of_env env =
  string_of_assoc string_of_name short_string_of_value "->" "; " 
    (List.filter (function _, VProcess _
                  |        _, VFun     _ -> false
                  | _                    -> true
                  )
                  env
    )

and string_of_runner (n, proc, env) =
  Printf.sprintf "%s = (%s) [%s]" 
                 (string_of_name n)
                 (string_of_process proc)
                 (short_string_of_env env)
                 
and string_of_rwaiter (n, vars, proc, env) = 
  Printf.sprintf "%s = (%s)%s [%s]" 
                 (string_of_name n)
                 (string_of_list string_of_name ";" vars)
                 (string_of_process proc)
                 (short_string_of_env env)
                 
and short_string_of_rwaiter (n, vars, proc, env) = (* infinite loop if we print the environment *)
  Printf.sprintf "%s(%s)" 
                 (string_of_name n)
                 (string_of_list string_of_name ";" vars)
                 
and string_of_wwaiter (n, vals, proc, env) = 
  Printf.sprintf "%s = (%s)%s [%s]" 
                 (string_of_name n)
                 (string_of_list string_of_value ";" vals)
                 (string_of_process proc)
                 (short_string_of_env env)
                 
and short_string_of_wwaiter (n, vals, proc, env) = (* infinite loop if we print the environment *)
  Printf.sprintf "%s(%s)" 
                 (string_of_name n)
                 (string_of_list string_of_value ";" vals)
                 
and string_of_stuck (n, vs) =
  Printf.sprintf "%s(%s)._"
                 (string_of_name n)
                 (string_of_list string_of_value "," vs)

and string_of_runnerqueue sep rq =
  string_of_pqueue string_of_runner sep (RunnerQueue.queue rq)
  
let miseval s v = raise (Error (dummy_spos, s ^ string_of_value v))

let unitv = function VUnit          -> ()     | v -> miseval "unitv"  v
let intv  = function VInt  i        -> i      | v -> miseval "intv"   v
let boolv = function VBool  b       -> b      | v -> miseval "boolv"  v
let listv = function VList  vs      -> vs     | v -> miseval "listv"  v
let chanv = function VChan  c       -> c      | v -> miseval "chanv"  v
let qbitv = function VQbit  q       -> q      | v -> miseval "qbitv"  v
let pairv = function VTuple [e1;e2] -> e1, e2 | v -> miseval "pairv"  v
let funv  = function VFun   f       -> f      | v -> miseval "pairv"  v

let vunit ()  = VUnit
let vint  i   = VInt   i
let vbool b   = VBool  b
let vlist vs  = VList  vs
let vchan c   = VChan  c
let vqbit q   = VQbit  q
let vpair a b = VTuple [a;b]
let vfun  f   = VFun   f

let mistyped pos thing v shouldbe =
  raise (Error (pos, Printf.sprintf "** Disaster: %s is %s, not %s" 
                                    thing 
                                    (string_of_value v)
                                    shouldbe
               )
        )

let rec evale env e =
  match e.inst.enode with
  | EUnit               -> VUnit
  | EVar n              -> (try env<@>n 
                            with Invalid_argument _ -> 
                              raise (Error (e.pos, "** Disaster: unbound " ^ string_of_name n))
                           )
  | EInt i              -> VInt i
  | EBool b             -> VBool b
  | EBit b              -> VInt (if b then 1 else 0)
  | EMinus e            -> VInt (- (intev env e))
  | ETuple es           -> VTuple (List.map (evale env) es)
  | EList es            -> VList (List.map (evale env) es)
  | ECond (c,e1,e2)     -> evale env (if boolev env c then e1 else e2)
  | EApp (f,a)          -> let fv = funev env f in
                           fv (evale env a)
  | EArith (e1,op,e2)   -> let v1 = intev env e1 in
                           let v2 = intev env e2 in
                           VInt (match op with
                                 | Plus    -> v1+v2    
                                 | Minus   -> v1-v2
                                 | Times   -> v1*v2
                                 | Div     -> v1/v2
                                 | Mod     -> v1 mod v2
                                )
  | ECompare (e1,op,e2) -> VBool (match op with
                                  | Eq  -> evale env e1 = evale env e2
                                  | Neq -> evale env e1 <> evale env e2
                                  | _   -> let v1 = intev env e1 in
                                           let v2 = intev env e2 in
                                           (match op with
                                            | Lt    -> v1<v2
                                            | Leq   -> v1<=v2
                                            | Eq    -> v1=v2  (* can't happen *)
                                            | Neq   -> v1<>v2 (* can't happen *)
                                            | Geq   -> v1>=v2
                                            | Gt    -> v1>v2
                                           )
                                 ) 
  | EBoolArith (e1,op,e2) -> let v1 = boolev env e1 in
                             let v2 = boolev env e2 in
                             VBool (match op with
                                      | And       -> v1 && v2
                                      | Or        -> v1 || v2
                                      | Implies   -> (not v1) || v2
                                      | Iff       -> v1 = v2
                                   )
  | EAppend (es, es')       -> VList (listev env es @ listev env es')
  | EBitCombine (e1, e2)    -> let v1 = intev env e1 in
                               let v2 = intev env e2 in
                               VInt (v1*2+v2)
                 
and unitev env e =
  match evale env e with
  | VUnit -> ()
  | v     -> mistyped e.pos (string_of_expr e) v "unit" 

and intev env e =
  match evale env e with
  | VInt i -> i
  | v      -> mistyped e.pos (string_of_expr e) v "an integer" 

and boolev env e = 
  match evale env e with
  | VBool b -> b
  | v       -> mistyped e.pos (string_of_expr e) v "a bool"

and listev env e = 
  match evale env e with
  | VList vs -> vs
  | v        -> mistyped e.pos (string_of_expr e) v "a list"

and chanev env e = 
  match evale env e with
  | VChan c -> c
  | v       -> mistyped e.pos (string_of_expr e) v "a channel"

and qbitev env e = 
  match evale env e with
  | VQbit q -> q
  | v       -> mistyped e.pos (string_of_expr e) v "a qbit"

and pairev env e =
  match evale env e with
  | VTuple [e1;e2] -> e1, e2
  | v              -> mistyped e.pos (string_of_expr e) v "a pair"

and funev env e = 
  match evale env e with
  | VFun f -> f
  | v      -> mistyped e.pos (string_of_expr e) v "a function"

and ugev env ug = 
  match ug with
  | GH                  -> GateH
  | GI                  -> GateI
  | GX                  -> GateX
  | GCnot               -> GateCnot
  | GPhi  e             -> GatePhi(intev env e)
  | GCond (e,ug1,ug2)   -> ugev env (if boolev env e then ug1 else ug2)

let rec interp sysenv proc =
  Qsim.init ();
  let newqbit pn n vopt = VQbit (Qsim.newqbit pn n vopt) in
  let chancount = ref 0 in
  let chanpool = ref [] in
  let newchan () = 
    let c = !chancount in 
    chancount := !chancount+1; 
    let chan = {cname=c; stream=Queue.create (); 
                         rwaiters=RWaiterQueue.create 10; (* 10 is a guess *)
                         wwaiters=WWaiterQueue.create 10; (* 10 is a guess *)
               } 
    in
    chanpool := chan::!chanpool;
    VChan chan 
  in
  let runners = RunnerQueue.create (10) in (* 10 is a guess *)
  let addrunner runner = RunnerQueue.push runners runner in
  let stucks = Queue.create () in
  let addstuck stuck = Queue.push stuck stucks in
  let rec step () =
    if RunnerQueue.is_empty runners then 
      Printf.printf "All stuck!\n channels=[\n  %s\n]\n stucks=[%s]\n qstate=%s\n\n"
                    (string_of_list string_of_chan ";\n  " (List.rev !chanpool))
                    (string_of_queue string_of_stuck "\n" stucks)
                    (string_of_qstate ())
    else
      (if !verbose || !verbose_interpret then
         Printf.printf "interpret\n runners=[\n  %s\n]\n channels=[\n  %s\n]\n stucks=[%s]\n qstate=%s\n\n"
                       (string_of_runnerqueue ";\n  " runners)
                       (string_of_list string_of_chan ";\n  " (List.rev !chanpool))
                       (string_of_queue string_of_stuck "; " stucks)
                       (string_of_qstate ());
       let runner = RunnerQueue.pop runners in
       (match runner with
        | _, Terminate, _       -> ()
        | _, Call (n, es), env  -> 
            (let vs = List.map (evale env) es in
             try (match env<@>n with
                  | VProcess (ns, IDef proc) -> let env = zip ns vs @ sysenv in
                                                addrunner (n, proc, env)
                  | VProcess (ns, IGiven)    -> addstuck (n, vs)
                  | v                        -> mistyped dummy_spos (string_of_name n) v "a process"
                 )  
             with Invalid_argument _ -> raise (Error (dummy_spos, "** Disaster: no process called " ^ string_of_name n))
            )
         
        | pn, WithNew (ps, proc), env ->
            let ps = List.map (fun (n, _) -> (n, newchan ())) ps in
            addrunner (pn, proc, (ps @ env))
        | pn, WithQbit (ps, proc), env ->
            let rec fv bv =
              match bv with
              | BVe bv                  -> bv              
              | BVcond (e, bv1, bv2)    -> fv (if boolev env e then bv1 else bv2)
            in
            let bv_eval = function
            | None      -> None
            | Some bve  -> Some (fv bve)
            in
            let ps = List.map (fun ((n,_),vopt) -> (n, newqbit pn n (bv_eval vopt))) ps in
            addrunner (pn, proc, (ps @ env))
        | pn, WithLet (((n,_),e), proc), env ->
            let env = (n, evale env e) :: env in
            addrunner (pn, proc, env)
        | pn, WithStep (step, proc), env ->
            (match step with
             | Read (e, ps) -> let c = chanev env e in
                               let ns, _ = unzip ps in
                               if not (Queue.is_empty c.stream) then (* there cannot be rwaiters ... *)
                                 (let vs = Queue.pop c.stream in
                                  let env = zip ns vs @ env in
                                  addrunner (pn, proc, env)
                                 )
                               else
                               if not (WWaiterQueue.is_empty c.wwaiters) then
                                 (let pn',vs',proc',env' = WWaiterQueue.pop c.wwaiters in
                                  addrunner (pn', proc', env');
                                  addrunner (pn, proc, (zip ns vs' @ env))
                                 )
                               else
                                 RWaiterQueue.push c.rwaiters (pn, ns, proc, env)
             | Write (e,es) -> let c = chanev env e in
                               let vs = List.map (evale env) es in
                               if not (RWaiterQueue.is_empty c.rwaiters) then (* there can be no stream *)
                                 (let pn',ns',proc',env' = RWaiterQueue.pop c.rwaiters in
                                  addrunner (pn', proc', (zip ns' vs @ env'));
                                  addrunner (pn, proc, env)
                                 )
                               else
                               if !Settings.chanbuf_limit = -1 ||               (* infinite buffers *)
                                  !Settings.chanbuf_limit>Queue.length c.stream (* buffer not full *)
                               then
                                 (Queue.push vs c.stream;
                                  addrunner (pn, proc, env)
                                 )
                               else
                                 WWaiterQueue.push c.wwaiters (pn, vs, proc, env)
             | Measure (e, (n,_))  -> let q = qbitev env e in
                                      let v = VInt (qmeasure pn q) in
                                      addrunner (pn, proc, (n,v)::env)
             | Ugatestep (es, ug)  -> let qs = List.map (qbitev env) es in
                                      let g = ugev env ug in
                                      ugstep pn qs g;
                                      addrunner (pn, proc, env)
            )
        | pn, Cond (e, p1, p2), env ->
            addrunner (pn, (if boolev env e then p1 else p2), env)
        | pn, Par ps, env ->
            List.iter (fun (i,proc) -> addrunner ((pn ^ "." ^ string_of_int i), proc, env)) (numbered ps)
       );
       step ()
      )
  in
  addrunner ("System", proc, sysenv);
  step()

let knowns = (ref [] : (name * string * value) list ref)

let know dec = knowns := dec :: !knowns

let interpret lib defs =
  Random.self_init(); (* for all kinds of random things *)
  (* make an assoc list of process defs and functions *)
  let given (n,t) assoc =
    match t with 
    | Process ts -> (n, VProcess ((List.map (fun t -> new_unknown_name()) ts), IGiven))::assoc
    | t          -> raise (Error(dummy_spos, Printf.sprintf "** cannot interpret with given %s:%s" 
                                                            (string_of_name n)
                                                            (string_of_type t)
                                )
                          )
  in
  let givenassoc = List.fold_right given lib [] in
  let knownassoc = List.map (fun (n,_,v) -> n, v) !knowns in
  let defassoc = List.map (fun (Processdef (n,params,p)) -> (n, VProcess (strip_params params, IDef p))) defs in
  let sysenv = defassoc @ givenassoc @ knownassoc in
  if !verbose || !verbose_interpret then
    Printf.printf "sysenv = [%s]\n\n" (string_of_env sysenv);
  let sysv = try sysenv <@> "System"
             with Invalid_argument _ -> raise (Error (dummy_spos, "no System process"))
  in 
  match sysv with
  | VProcess ([], IDef p) -> interp sysenv p
  | VProcess (ps, IDef _) -> raise (Error (dummy_spos, "can't interpret System with non-null parameter list"))
  | VProcess (_ , IGiven) -> raise (Error (dummy_spos, "System process in 'given' list"))
  | _                     -> raise (Error (dummy_spos, "System doesn't name a process"))
