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
    along with Qtpi; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
    (or look at http://www.gnu.org).
*)

open Settings
open Listutils
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
    | VFun of name        (* help! *)
    | VProcess of name list * iprocess

  and chan = {cname: int; stream: (value list) Queue.t; waiters: WaiterHeap.t}

  and runner = name * process * env

  and waiter = name * name list * process * env

  and env = (name * value) list

  and stuck = name * value list
end = Types

and OrderedRandomWaiters : Binary_heap.Ordered = struct type t = int*Types.waiter let compare = Pervasives.compare end
and OrderedRandomRunners : Binary_heap.Ordered = struct type t = int*Types.runner let compare = Pervasives.compare end

and WaiterHeap : Binary_heap.BH with type elt=int*Types.waiter = Binary_heap.Make(OrderedRandomWaiters)
and RunnerHeap : Binary_heap.BH with type elt=int*Types.runner = Binary_heap.Make(OrderedRandomRunners)

open Types

let rec string_of_value = function
  | VUnit           -> "()"
  | VInt i          -> string_of_int i
  | VBool b         -> string_of_bool b
  | VQbit q         -> "Qbit " ^ string_of_qbit q
  | VChan c         -> "Chan " ^ string_of_chan c
  | VTuple vs       -> "(" ^ string_of_list string_of_value "," vs ^ ")"
  | VList vs        -> "[" ^ string_of_list string_of_value ";" vs ^ "]"
  | VFun n          -> string_of_name n (* help! *)
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
  
and string_of_chan {cname=i; stream=vs; waiters=ws} =
    Printf.sprintf "%d [%s] [%s]"
                   i
                   (string_of_queue (bracketed_string_of_list string_of_value) "; " vs)
                   (short_string_of_waiterheap "; " ws)

and short_string_of_chan {cname=i; stream=vs; waiters=ws} =
    string_of_int i
    
and string_of_env env =
  string_of_assoc string_of_name string_of_value "->" "; " env

and short_string_of_env env =
  string_of_assoc string_of_name short_string_of_value "->" "; " env

and string_of_runner (n, proc, env) =
  Printf.sprintf "%s = (%s) [%s]" 
                 (string_of_name n)
                 (string_of_process proc)
                 (short_string_of_env env)
                 
and string_of_waiter (n, vars, proc, env) = 
  Printf.sprintf "%s = (%s)%s [%s]" 
                 (string_of_name n)
                 (string_of_list string_of_name ";" vars)
                 (string_of_process proc)
                 (short_string_of_env env)
                 
and short_string_of_waiter (n, vars, proc, env) = (* infinite loop if we print the environment *)
  Printf.sprintf "%s(%s)" 
                 (string_of_name n)
                 (string_of_list string_of_name ";" vars)
                 
and string_of_stuck (n, vs) =
  Printf.sprintf "%s(%s)._"
                 (string_of_name n)
                 (string_of_list string_of_value "," vs)

and string_of_waiterheap sep wh =
  let ss = WaiterHeap.fold (fun (i,w) ss -> (i,string_of_waiter w)::ss) wh [] in
  String.concat sep @@ List.rev @@ (List.map snd) @@ (List.sort Pervasives.compare) @@ ss
  
and short_string_of_waiterheap sep wh =
  let ss = WaiterHeap.fold (fun (i,w) ss -> (i,short_string_of_waiter w)::ss) wh [] in
  String.concat sep @@ List.rev @@ (List.map snd) @@ (List.sort Pervasives.compare) @@ ss
  
and string_of_runnerheap sep rh =
  let ss = RunnerHeap.fold (fun (i,r) ss -> (i,string_of_runner r)::ss) rh [] in
  String.concat sep @@ List.rev @@ (List.map snd) @@ (List.sort Pervasives.compare) @@ ss
  
let mistyped pos thing v shouldbe =
  raise (Error (pos, Printf.sprintf "** Disaster: %s is %s, not %s" 
                                    thing 
                                    (string_of_value v)
                                    shouldbe
               )
        )

let rec evale env e =
  match e.inst with
  | EUnit               -> VUnit
  | EVar n              -> (try env<@>n 
                            with Invalid_argument _ -> 
                              raise (Error (e.pos, "** Disaster: unbound " ^ string_of_name n))
                           )
  | EInt i              -> VInt i
  | EBool b             -> VBool b
  | EBit b              -> VInt (if b then 1 else 0)
  | EMinus e            -> VInt (- (intv env e))
  | ETuple es           -> VTuple (List.map (evale env) es)
  | EList es            -> VList (List.map (evale env) es)
  | ECond (c,e1,e2)     -> evale env (if boolv env c then e1 else e2)
  | EApp (f,a)          -> raise (Error (e.pos, "** Cannot (yet) deal with " ^ string_of_expr e))
  | EArith (e1,op,e2)   -> let v1 = intv env e1 in
                           let v2 = intv env e2 in
                           VInt (match op with
                                 | Plus    -> v1+v2    
                                 | Minus   -> v1-v2
                                 | Times   -> v1*v2
                                 | Div     -> v1/v2
                                 | Mod     -> v1 mod v2
                                )
  | ECompare (e1,op,e2) -> (match op with
                            | Eq  -> VBool (evale env e1 = evale env e2)
                            | Neq -> VBool (evale env e1 <> evale env e2)
                            | _   -> raise (Error (e.pos, "** Cannot (yet) deal with " ^ string_of_expr e))
                           ) 
  | EBoolArith (e1,op,e2) -> let v1 = boolv env e1 in
                             let v2 = boolv env e2 in
                             VBool (match op with
                                      | And       -> v1 && v2
                                      | Or        -> v1 || v2
                                      | Implies   -> (not v1) || v2
                                      | Iff       -> v1 = v2
                                   )
  | EAppend (es, e)         -> VList (listv env es @ [evale env e])
  | EBitCombine (e1, e2)    -> let v1 = intv env e1 in
                               let v2 = intv env e2 in
                               VInt (v1*2+v2)
                 
and unitv env e =
  match evale env e with
  | VUnit -> ()
  | v     -> mistyped e.pos (string_of_expr e) v "unit" 

and intv env e =
  match evale env e with
  | VInt i -> i
  | v      -> mistyped e.pos (string_of_expr e) v "an integer" 

and boolv env e = 
  match evale env e with
  | VBool b -> b
  | v       -> mistyped e.pos (string_of_expr e) v "a bool"

and listv env e = 
  match evale env e with
  | VList vs -> vs
  | v        -> mistyped e.pos (string_of_expr e) v "a list"

and chanv env e = 
  match evale env e with
  | VChan c -> c
  | v       -> mistyped e.pos (string_of_expr e) v "a channel"

and qbitv env e = 
  match evale env e with
  | VQbit q -> q
  | v       -> mistyped e.pos (string_of_expr e) v "a qbit"

and evalug env ug = 
  match ug with
  | GH                  -> GateH
  | GI                  -> GateI
  | GX                  -> GateX
  | GCnot               -> GateCnot
  | GPhi  e             -> GatePhi(intv env e)
  | GCond (e,ug1,ug2)   -> evalug env (if boolv env e then ug1 else ug2)

let rec interp sysenv proc =
  Qsim.init ();
  let newqbit n vopt = VQbit (Qsim.newqbit n vopt) in
  let chancount = ref 0 in
  let chanpool = ref [] in
  let newchan () = 
    let c = !chancount in 
    chancount := !chancount+1; 
    let chan = {cname=c; stream=Queue.create (); waiters=WaiterHeap.create 10} in (* 10 is a guess *)
    chanpool := chan::!chanpool;
    VChan chan 
  in
  let runners = RunnerHeap.create (10) in (* 10 is a guess *)
  let addrunner stuff = RunnerHeap.add runners (Random.bits(),stuff) in
  let stucks = Queue.create () in
  let addstuck stuck = Queue.add stuck stucks in
  let rec step () =
    if RunnerHeap.is_empty runners then 
      Printf.printf "All stuck!\n channels=[\n  %s\n]\n stucks=[%s]\n qstate=%s\n\n"
                    (string_of_list string_of_chan ";\n  " (List.rev !chanpool))
                    (string_of_queue string_of_stuck "\n" stucks)
                    (string_of_qstate ())
    else
      (if !verbose || !verbose_interpret then
         Printf.printf "interpret\n runners=[\n  %s\n]\n channels=[\n  %s\n]\n stucks=[%s]\n qstate=%s\n\n"
                       (string_of_runnerheap ";\n  " runners)
                       (string_of_list string_of_chan ";\n  " (List.rev !chanpool))
                       (string_of_queue string_of_stuck "; " stucks)
                       (string_of_qstate ());
       let _, runner = RunnerHeap.pop_maximum runners in
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
        | pn, WithQbit (ns, proc), env ->
            let ps = List.map (fun (n,vopt) -> (n, newqbit n vopt)) ns in
            addrunner (pn, proc, (ps @ env))
        | pn, WithStep (step, proc), env ->
            (match step with
             | Read (e, ps) -> let c = chanv env e in
                               let ns, _ = unzip ps in
                               if not (Queue.is_empty c.stream) then (* there cannot be waiters ... *)
                                 (let vs = Queue.pop c.stream in
                                  let env = zip ns vs @ env in
                                  addrunner (pn, proc, env)
                                 )
                               else
                                 WaiterHeap.add c.waiters (Random.bits (), (pn, ns, proc, env))
             | Write (e,es) -> let c = chanv env e in
                               let vs = List.map (evale env) es in
                               if not (WaiterHeap.is_empty c.waiters) then (* there can be no stream *)
                                 (let _,(n',ns',proc',env') = WaiterHeap.pop_maximum c.waiters in
                                  addrunner (n', proc', (zip ns' vs @ env'));
                                  addrunner (pn, proc, env)
                                 )
                               else
                                 (Queue.add vs c.stream;
                                  addrunner (pn, proc, env)
                                 )
             | Measure (e, (n,_))  -> let q = qbitv env e in
                                      let v = VInt (qmeasure q) in
                                      addrunner (pn, proc, (n,v)::env)
             | Ugatestep (es, ug)  -> let qs = List.map (qbitv env) es in
                                      let g = evalug env ug in
                                      ugstep qs g;
                                      addrunner (pn, proc, env)
             | Eval e              -> let _ = unitv env e in
                                      addrunner (pn, proc, env)
            )
        | pn, Cond (e, p1, p2), env ->
            addrunner (pn, (if boolv env e then p1 else p2), env)
        | pn, Par ps, env ->
            List.iter (fun (i,proc) -> addrunner ((pn ^ "." ^ string_of_int i), proc, env)) (numbered ps)
       );
       step ()
      )
  in
  addrunner ("System", proc, sysenv);
  step()

let interpretdefs lib defs =
  Random.self_init(); (* for all kinds of random things *)
  (* make an assoc list of process defs and functions *)
  let given (n,t) assoc =
    match t with 
    | Process ts -> (n, VProcess ((List.map (fun t -> new_unknown_name()) ts), IGiven))::assoc
    | Fun _      -> (n, VFun n)::assoc
    | t          -> raise (Error(dummy_spos, Printf.sprintf "** cannot interpret with given %s:%s" 
                                                            (string_of_name n)
                                                            (string_of_type t)
                                )
                          )
  in
  let libassoc = List.fold_right given lib [] in
  let procassoc = List.map (fun (Processdef (n,params,p)) -> (n, VProcess (strip_params params, IDef p))) defs in
  let sysenv = procassoc @ libassoc in
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
