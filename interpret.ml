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
open Sourcepos
open Instance
open Name
open Expr
open Basisv
open Pattern
open Type
open Param
open Step
open Process
open Processdef
open Qsim

exception Error of sourcepos * string
exception Disaster of sourcepos * string
exception LibraryError of string

let queue_elements q = let vs = Queue.fold (fun vs v -> v::vs) [] q in
                       List.rev vs

let string_of_queue string_of_v sep q = 
  let vs = queue_elements q in
  "{" ^ string_of_list string_of_v sep vs ^ "}"

type value =
  | VUnit
  | VInt of int
  | VBool of bool
  | VChar of char
  | VBasisv of basisv
  | VGate of Qsim.ugv
  | VString of string
  | VQbit of qbit
  | VChan of chan
  | VTuple of value list
  | VList of value list
  | VFun of (value -> value)        
  | VProcess of name list * process

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
  | VInt i          -> string_of_int i
  | VBool b         -> string_of_bool b
  | VBasisv bv      -> string_of_basisv bv
  | VGate ugv       -> string_of_ugv ugv
  | VChar c         -> Printf.sprintf "'%s'" (Char.escaped c)
  | VString s       -> Printf.sprintf "\"%s\"" (String.escaped s)
  | VQbit q         -> "Qbit " ^ string_of_qbit q
  | VChan c         -> "Chan " ^ string_of_chan c
  | VTuple vs       -> "(" ^ string_of_list string_of_value "," vs ^ ")"
  | VList vs        -> bracketed_string_of_list string_of_value vs
  | VFun f          -> "(..->..)"
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
  
let (<@>)  env n     = try Listutils.(<@>) env n 
                       with Not_found -> raise (Disaster (dummy_spos, 
                                                          Printf.sprintf "looking up %s in %s"
                                                                         (string_of_name n)
                                                                         (short_string_of_env env)
                                                         )
                                               )       
let (<@+>) = Listutils.(<@+>)      
let (<@?>) = Listutils.(<@?>)        

let miseval s v = raise (Error (dummy_spos, s ^ string_of_value v))

let unitv   = function VUnit           -> ()     | v -> miseval "unitv"    v
let bitv    = function VInt    0       -> 0  
                     | VInt    1       -> 1      | v -> miseval "bitv"     v
let intv    = function VInt    i       -> i      | v -> miseval "intv"     v
let boolv   = function VBool   b       -> b      | v -> miseval "boolv"    v
let charv   = function VChar   c       -> c      | v -> miseval "charv"    v
let stringv = function VString s       -> s      | v -> miseval "stringv"  v
let basisvv = function VBasisv bv      -> bv     | v -> miseval "basisvv"  v
let gatev   = function VGate   g       -> g      | v -> miseval "gatev"    v
let chanv   = function VChan   c       -> c      | v -> miseval "chanv"    v
let qbitv   = function VQbit   q       -> q      | v -> miseval "qbitv"    v
let pairv   = function VTuple  [e1;e2] -> e1, e2 | v -> miseval "pairv"    v
let listv   = function VList   vs      -> vs     | v -> miseval "listv"    v
let funv    = function VFun    f       -> f      | v -> miseval "funv"    v

let vunit   ()    = VUnit
let vbit    i     = VInt    (i land 1)
let vint    i     = VInt    i
let vbool   b     = VBool   b
let vchar   c     = VChar   c
let vstring s     = VString s
let vgate   g     = VGate   g
let vchan   c     = VChan   c
let vqbit   q     = VQbit   q
let vpair   (a,b) = VTuple  [a;b]
let vlist   vs    = VList   vs
let vfun    f     = VFun    f

let mistyped pos thing v shouldbe =
  raise (Error (pos, Printf.sprintf "** Disaster: %s is %s, not %s" 
                                    thing 
                                    (string_of_value v)
                                    shouldbe
               )
        )
        
(* bring out your dead: a nasty space leak plugged *)
let rec boyd pq = 
  try let _, gsir = PQueue.first pq in
      let b, _ = !gsir in
      if b then () else (PQueue.remove pq; boyd pq)
  with PQueue.Empty -> ()

;; (* to give boyd a universal type *)

(* ******************** the interpreter proper ************************* *)

(* Sestoft's naive pattern matcher, from "ML pattern match and partial evaluation".
   Modified a bit, obvs, but really the thing.
 *)

let matcher pos env pairs value =
  let sop p = "(" ^ string_of_pattern p ^ ")" in
  if !verbose || !verbose_interpret then
    Printf.printf "matcher %s %s %s\n\n" (short_string_of_env env)
                                         (bracketed_string_of_list (sop <.> fst) pairs)
                                         (string_of_value value);
  let rec fail pairs =
    match pairs with
    | []               -> None
    | (pat,rhs)::pairs -> _match env pat value [] rhs pairs
  and succeed env work rhs pairs =
    match work with
    | []                         -> if !verbose || !verbose_interpret then
                                      Printf.printf "matcher succeeds %s\n\n" (short_string_of_env env);
                                    Some (env,rhs)
    | ([]      , []      )::work -> succeed env work rhs pairs
    | (p1::pats, v1::vals)::work -> _match env p1 v1 ((pats,vals)::work) rhs pairs
    | (ps      , vs      )::_    -> raise (Disaster (pos,
                                                     Printf.sprintf "matcher succeed pats %s values %s"
                                                                    (bracketed_string_of_list sop ps)
                                                                    (bracketed_string_of_list string_of_value vs)
                                                    )
                                          )
  and _match env pat v work rhs pairs =
    if !verbose_interpret then
      Printf.printf "_match %s %s %s ...\n\n" (short_string_of_env env)
                                              (sop pat)
                                              (string_of_value v);
    let yes env = succeed env work rhs pairs in
    let no () = fail pairs in
    let maybe v v' = if v=v' then yes env else no () in
    match pat.inst.pnode, v with
    | PatAny            , _                 
    | PatUnit           , VUnit             
    | PatNil            , VList []          -> yes env
    | PatName   n       , _                 -> yes (env<@+>(n,v))
    | PatInt    i       , VInt    i'        -> maybe i i'
    | PatBit    b       , VInt    i'        -> maybe (if b then 1 else 0) i'
    | PatBool   b       , VBool   b'        -> maybe b b'
    | PatChar   c       , VChar   c'        -> maybe c c'
    | PatString s       , VString s'        -> maybe s s'
    | PatBasisv v       , VBasisv v'        -> maybe v v'
    | PatGate   pg      , VGate   vg        -> (match pg.inst, vg with
                                                | PatH    , GateH 
                                                | PatI    , GateI
                                                | PatX    , GateX
                                                | PatY    , GateY
                                                | PatZ    , GateZ
                                                | PatCnot , GateCnot  -> yes env
                                                | PatPhi p, GatePhi i -> succeed env (([p],[VInt i])::work) rhs pairs
                                                | _                   -> no ()
                                               )
    | PatCons   (ph,pt) , VList   (vh::vt)  -> succeed env (([ph;pt],[vh;VList vt])::work) rhs pairs
    | PatTuple  ps      , VTuple  vs        -> succeed env ((ps,vs)::work) rhs pairs
    | _                                     -> no () (* can happen: PNil vs ::, PCons vs [] *)
  in
  fail pairs
  
let bmatch env pat v =
  match matcher pat.pos env [pat,()] v with
  | Some (env,()) -> env
  | None          -> raise (Disaster (pat.pos,
                                      Printf.sprintf "bmatch %s %s"
                                                     (string_of_pattern pat)
                                                     (string_of_value v)
                                     )
                           )
  
let name_of_bpat pat = (* only called by dispose?(q) *)
  match pat.inst.pnode with
  | PatName n -> n
  | PatAny    -> "_"
  | _         -> "can't happen"
  
let rec evale env e =
  match e.inst.enode with
  | EUnit               -> VUnit
  | ENil                -> VList []
  | EVar n              -> (try env<@>n 
                            with Invalid_argument _ -> 
                              raise (Error (e.pos, "** Disaster: unbound " ^ string_of_name n))
                           )
  | EInt i              -> VInt i
  | EBool b             -> VBool b
  | EChar c             -> VChar c
  | EString s           -> VString s
  | EBit b              -> VInt (if b then 1 else 0)
  | EBasisv bv          -> VBasisv bv
  | EGate uge           -> VGate (ugev env uge)
  | EMinus e            -> VInt (~- (intev env e))
  | ENot   e            -> VBool (not (boolev env e))
  | ETuple es           -> VTuple (List.map (evale env) es)
  | ECons (hd,tl)       -> VList (evale env hd :: listev env tl)
  | ECond (c,e1,e2)     -> evale env (if boolev env c then e1 else e2)
  | EMatch (me,ems)     -> let v = evale env me in
                           (match matcher e.pos env ems v with
                            | Some (env, e) -> evale env e
                            | None          -> raise (Error (e.pos, Printf.sprintf "match failed against %s"
                                                                                   (string_of_value v)
                                                            )
                                                     )
                           )  
  | EApp (f,a)          -> let fv = funev env f in
                           (try fv (evale env a) with LibraryError s -> raise (Error (e.pos, s)))

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
  | EAppend (es, es')       -> VList (List.append (listev env es) (listev env es'))
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

and listev env e =
  match evale env e with
  | VList vs -> vs
  | v        -> mistyped e.pos (string_of_expr e) v "a list"

and funev env e = 
  match evale env e with
  | VFun f -> f
  | v      -> mistyped e.pos (string_of_expr e) v "a function"

and ugev env ug = 
  match ug.inst with
  | GH                  -> GateH
  | GI                  -> GateI
  | GX                  -> GateX
  | GY                  -> GateY
  | GZ                  -> GateZ
  | GCnot               -> GateCnot
  | GPhi  e             -> GatePhi(intev env e)

let mkchan c = {cname=c; stream=Queue.create (); 
                         rwaiters=PQueue.create 10; (* 10 is a guess *)
                         wwaiters=PQueue.create 10; (* 10 is a guess *)
               }

module OrderedChan = struct type t = chan 
                            let compare c1 c2 = Pervasives.compare c1.cname c2.cname
                            let to_string = string_of_chan
                     end
module ChanSet = MySet.Make (OrderedChan)

type gsum = Grw of rwaiter | Gww of wwaiter

let rec interp sysenv proc =
  Qsim.init ();
  let newqbit pn n vopt = VQbit (Qsim.newqbit pn n vopt) in
  let chancount = ref 0 in
  let stuck_chans = ref ChanSet.empty in (* no more space leak: this is for stuck channels *)
  let string_of_stuck_chans () = ChanSet.to_string !stuck_chans in
  let remember_chan c = stuck_chans := ChanSet.add c !stuck_chans in
  let maybe_forget_chan c =
    boyd c.rwaiters;
    boyd c.wwaiters;
    if Queue.is_empty c.stream && 
       PQueue.is_empty c.rwaiters &&
       PQueue.is_empty c.wwaiters
    then
      stuck_chans := ChanSet.remove c !stuck_chans
  in
  let newchan () = 
    let c = !chancount in 
    chancount := !chancount+1; 
    let chan = mkchan c in
    VChan chan 
  in
  let runners = PQueue.create (10) in (* 10 is a guess *)
  let addrunner runner = PQueue.push runners runner in
  let rec step () =
    if PQueue.is_empty runners then 
      if !verbose || !verbose_interpret || !verbose_qsim || !show_final then
        Printf.printf "All stuck!\n channels=%s\n %s\n\n"
                      (string_of_stuck_chans ())
                      (String.concat "\n " (strings_of_qsystem ()))
      else ()
    else
      (if !verbose || !verbose_interpret then
         Printf.printf "interpret\n runners=[\n  %s\n]\n channels=%s\n %s\n\n"
                       (string_of_runnerqueue ";\n  " runners)
                       (string_of_stuck_chans ())
                       (String.concat "\n " (strings_of_qsystem ()));
       let runner = PQueue.pop runners in
       PQueue.excite runners;
       let pn, rproc, env = runner in
       (match rproc.inst with
        | Terminate         -> ()
        | Call (n, es)      -> 
            (let vs = List.map (evale env) es in
             try (match env<@>n.inst with
                  | VProcess (ns, proc) -> let env = List.fold_left (<@+>) sysenv (zip ns vs) in
                                           addrunner (n.inst, proc, env)
                  | v                   -> mistyped rproc.pos (string_of_name n.inst) v "a process"
                 )  
             with Not_found -> raise (Error (dummy_spos, "** Disaster: no process called " ^ string_of_name n.inst))
            )
        | WithNew (ps, proc) ->
            let ps = List.map (fun n -> (n, newchan ())) (strip_params ps) in
            addrunner (pn, proc, (List.fold_left (<@+>) env ps))
        | WithQbit (ps, proc) ->
            let bv_eval = function
            | None      -> None
            | Some bve  -> Some (basisvv (evale env bve))
            in
            let ps = List.map (fun ({inst=n,_},vopt) -> (n, newqbit pn n (bv_eval vopt))) ps in
            addrunner (pn, proc, (List.fold_left (<@+>) env ps))
        | WithLet ((pat,e), proc) ->
            let v = evale env e in
            addrunner (pn, proc, bmatch env pat v)
        | WithQstep (qstep, proc) ->
            (match qstep.inst with
             | Measure (e, bopt, {inst=n,_}) -> let q = qbitev env e in
                                                let bvopt = bopt &~~ (fun e -> Some (gatev (evale env e))) in
                                                let v = VInt (qmeasure pn bvopt q) in
                                                addrunner (pn, proc, env <@+> (n,v))
             | Ugatestep (es, ug)            -> let qs = List.map (qbitev env) es in
                                                let g = gatev (evale env ug) in
                                                ugstep pn qs g;
                                                addrunner (pn, proc, env)
            )
        | WithExpr (e, proc)  -> let _ = evale env e in
                                 addrunner (pn, proc, env)
        | GSum ioprocs      -> 
            let withdraw chans = List.iter maybe_forget_chan chans in (* kill the space leak! *)
            let canread c pat =
              let do_match v' = Some (bmatch env pat v') in
              try if c.cname = -1 then (* reading from dispose, ho ho *)
                    let q = newqbit pn (name_of_bpat pat) None in
                    do_match q
                  else
                    let v' = Queue.pop c.stream in
                    (maybe_forget_chan c; 
                     do_match v'
                    )
              with Queue.Empty ->
              try boyd c.wwaiters; (* now the first must be alive *)
                  let (pn',v',proc',env'),gsir = PQueue.pop c.wwaiters in
                  let _, chans = !gsir in
                  gsir := false, [];
                  withdraw chans;
                  PQueue.excite c.wwaiters;
                  maybe_forget_chan c;
                  addrunner (pn', proc', env');
                  do_match v'
              with PQueue.Empty -> None
            in
            let canwrite c v =
              if c.cname = -1 then (* it's dispose *)
                 (disposeqbit pn (qbitv v); 
                  true
                 )
               else
               try boyd c.rwaiters;
                   let (pn',pat',proc',env'),gsir = PQueue.pop c.rwaiters in
                   let _, chans = !gsir in
                   gsir := false, [];
                   withdraw chans;
                   PQueue.excite c.rwaiters;
                   maybe_forget_chan c;
                   addrunner (pn', proc', bmatch env' pat' v);
                   true
               with PQueue.Empty -> 
               if !Settings.chanbuf_limit = -1 ||               (* infinite buffers *)
                  !Settings.chanbuf_limit>Queue.length c.stream (* buffer not full *)
               then
                 (Queue.push v c.stream;
                  remember_chan c;
                  true
                 )
               else false
            in
            let rec try_iosteps gsum pq = 
              try let (iostep,proc) = PQueue.pop pq in
                  match iostep.inst with
                  | Read (ce,pat) -> let c = chanev env ce in
                                     (match canread c pat with
                                      | Some env -> addrunner (pn, proc, env)
                                      | None     -> try_iosteps ((c, Grw (pn, pat, proc, env))::gsum) pq
                                     )
                  | Write (ce,e)  -> let c = chanev env ce in
                                     let v = evale env e in
                                     if canwrite c v then addrunner (pn, proc, env)
                                     else try_iosteps ((c, Gww (pn, v, proc, env))::gsum) pq
              with PQueue.Empty ->
              let cs = List.map fst gsum in
              let gsir = ref (true, cs) in
              let add_waiter = function
                | c, Grw rw -> PQueue.push c.rwaiters (rw,gsir);
                               remember_chan c
                | c, Gww ww -> PQueue.push c.wwaiters (ww,gsir);
                               remember_chan c
              in
              List.iter add_waiter gsum
            in
            let pq = PQueue.create (List.length ioprocs) in
            List.iter (PQueue.push pq) ioprocs;
            try_iosteps [] pq
        | Cond (e, p1, p2)  ->
            addrunner (pn, (if boolev env e then p1 else p2), env)
        | PMatch (e,pms)    -> let v = evale env e in
                               (match matcher rproc.pos env pms v with
                                | Some (env, proc) -> addrunner (pn, proc, env)
                                | None             -> raise (Error (rproc.pos, Printf.sprintf "match failed against %s"
                                                                                              (string_of_value v)
                                                            )
                                                     )
                               )  
        | Par ps            ->
            List.iter (fun (i,proc) -> addrunner ((pn ^ "." ^ string_of_int i), proc, env)) (numbered ps)
       );
       step ()
      )
  in
  addrunner ("System", proc, sysenv);
  step()

let knowns = (ref [] : (name * string * value) list ref)

let know dec = knowns := dec :: !knowns

let interpret defs =
  Random.self_init(); (* for all kinds of random things *)
  (* make an assoc list of process defs and functions *)
  let knownassoc = List.map (fun (n,_,v) -> n, v) !knowns in
  let defassoc = List.map (fun (Processdef (n,params,p)) -> (n.inst, VProcess (strip_params params, p))) defs in
  let sysenv = defassoc @ knownassoc in
  let sysenv = if sysenv <@?> "dispose" then sysenv else sysenv <@+> ("dispose", VChan (mkchan (-1))) in
  if !verbose || !verbose_interpret then
    Printf.printf "sysenv = %s\n\n" (string_of_env sysenv);
  let sysv = try sysenv <@> "System"
             with Invalid_argument _ -> raise (Error (dummy_spos, "no System process"))
  in 
  match sysv with
  | VProcess ([], p) -> interp sysenv p
  | VProcess (ps, _) -> raise (Error (dummy_spos, "can't interpret System with non-null parameter list"))
  | _                     -> raise (Error (dummy_spos, "System doesn't name a process"))
